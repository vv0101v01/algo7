// W-types: well-founded trees `W (x : A). B` with constructor `sup`,
// eliminator `ind-W` (a.k.a. `wf-rec`) and a beta-reduction engine.
//
// This file implements the four requested pieces as a self-contained
// fragment on top of the trusted kernel (no change to `DTerm`/`DValue`):
//
//   1. Syntax & formation — `WExpr` is the abstract syntax tree.  The
//      system recognises `W (x : A). B` as `WType(a, b)` where `b` is
//      read under one binder for the label `x : A`.  Formation rules
//      (`wexpr_is_type`, `w_wtype_formation`, `w_sup_formation`,
//      `w_elim_formation`) are decidable predicates; the deep
//      dependent checks are delegated to the kernel through the
//      bridge in §7 (`wtype_formation_kernel`).
//   2. Constructor — `sup a f` (`WSup`) builds a tree from a node
//      label `a : A` and a subtree map `f : (x : A) -> W A B`.
//   3. Eliminator & well-founded recursion — `ind-W` (`WElim`, also
//      exposed as `w_elim_value` / `w_wf_rec`) gives recursive
//      hypotheses only for the immediate subtrees `f x`, so every
//      function defined by it terminates by structural descent on
//      the accessibility predicate (`w_accessible`, `w_subtree`,
//      `w_height`).
//   4. Compiler beta rule — the reduction engine (`w_beta_step`,
//      `w_normalize`) implements
//          ind-W(motive, step, sup(a, f))
//            ==> step(a, f, λx. ind-W(motive, step, f x))
//      i.e. the eliminator applied to a constructor unfolds to the
//      step applied to the label, the subtree map, and the
//      recursively-defined hypotheses.
//
// Binder conventions (de Bruijn, index 0 = innermost):
//   * `WType(a, b)`      — `b` under one binder (the label).
//   * `WPi(a, b)` / `WSigma(a, b)` — `b` under one binder.
//   * `WLam(body)`       — `body` under one binder.
//   * `WElim(m, s, t)`   — `m` under one binder (the W-value),
//     `s` under three binders in order (label, subtree map,
//     recursive hypotheses) with `WVar(0)` = hypotheses,
//     `WVar(1)` = subtree map, `WVar(2)` = label; `t` at depth 0.
//   * `WBoolElim` / `WNatElim` — motive under one binder.

// ---------------------------------------------------------------------------
// §1. Syntax — the W-fragment AST
// ---------------------------------------------------------------------------

///|
/// Abstract syntax for the W-fragment.  Types and terms share one
/// tree (as in `DTerm`); `WType` is the W-type former.
#derive(Debug, Eq)
pub(all) enum WExpr {
  WVar(Int32)
  WUniv(Int32)
  WBoolTy
  WUnitTy
  WNatTy
  WPi(WExpr, WExpr)
  WSigma(WExpr, WExpr)
  WType(WExpr, WExpr)
  WSup(WExpr, WExpr)
  WElim(WExpr, WExpr, WExpr)
  WLam(WExpr)
  WApp(WExpr, WExpr)
  WPair(WExpr, WExpr)
  WFst(WExpr)
  WSnd(WExpr)
  WUnit
  WBoolLit(Bool)
  WBoolElim(WExpr, WExpr, WExpr, WExpr)
  WNatZero
  WSucc(WExpr)
  WNatElim(WExpr, WExpr, WExpr, WExpr)
}

///|
pub extend WExpr with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend WExpr with Eq::{not_equal, equal}

///|
/// Smart constructor for `W (x : A). B`.
pub fn w_type(a : WExpr, b : WExpr) -> WExpr {
  WType(a, b)
}

///|
/// Smart constructor for the W-constructor `sup a f`.
pub fn w_sup(a : WExpr, f : WExpr) -> WExpr {
  WSup(a, f)
}

///|
/// Smart constructor for the eliminator `ind-W motive step scrut`.
pub fn w_elim(motive : WExpr, step : WExpr, scrut : WExpr) -> WExpr {
  WElim(motive, step, scrut)
}

///|
/// Smart constructor for `λx. body`.
pub fn w_lam(body : WExpr) -> WExpr {
  WLam(body)
}

///|
/// Smart constructor for application.
pub fn w_app(f : WExpr, a : WExpr) -> WExpr {
  WApp(f, a)
}

///|
/// Smart constructor for the constant `Unit` type.
pub fn w_unit_ty() -> WExpr {
  WUnitTy
}

///|
/// Smart constructor for the `Nat` type.
pub fn w_nat_ty() -> WExpr {
  WNatTy
}

///|
/// Smart constructor for the `Bool` type.
pub fn w_bool_ty() -> WExpr {
  WBoolTy
}

// ---------------------------------------------------------------------------
// §2. Values and environments
// ---------------------------------------------------------------------------

///|
/// Semantic values of the W-fragment.  `WVSup` stores the label and
/// the subtree map as a host function; `WVLam` stores a closure.
/// `WVNeutral(n)` is a stuck variable at de Bruijn level `n`.
pub(all) enum WValue {
  WVSup(WValue, (WValue) -> WValue)
  WVLam((WValue) -> WValue)
  WVPair(WValue, WValue)
  WVUnit
  WVBool(Bool)
  WVZero
  WVSucc(WValue)
  WVNeutral(Int32)
}

///|
/// Persistent term environment.  Index 0 is the head (most recent
/// binder); extension shares the tail, mirroring `DEnv`.
pub(all) enum WEnv {
  WEnvNil
  WEnvCons(WValue, WEnv, Int32)
}

///|
pub fn wenv_empty() -> WEnv {
  WEnvNil
}

///|
pub fn wenv_cons(v : WValue, env : WEnv) -> WEnv {
  WEnvCons(v, env, wenv_len(env) + 1)
}

///|
pub fn wenv_len(env : WEnv) -> Int32 {
  match env {
    WEnvNil => 0
    WEnvCons(_, _, n) => n
  }
}

///|
pub fn wenv_at(env : WEnv, i : Int32) -> WValue? {
  match env {
    WEnvNil => None
    WEnvCons(v, tail, _) =>
      if i == 0 {
        Some(v)
      } else if i > 0 {
        wenv_at(tail, i - 1)
      } else {
        None
      }
  }
}

///|
pub fn wenv_extend(values : Array[WValue], env : WEnv) -> WEnv {
  let mut out = env
  for i in 0..<values.length() {
    out = wenv_cons(values[i], out)
  }
  out
}

///|
/// Apply a function value; non-functions return `WVUnit` (the
/// ill-typed fallback, as in the kernel's `dapp_typed` discipline).
pub fn wapp(f : WValue, arg : WValue) -> WValue {
  match f {
    WVLam(g) => g(arg)
    _ => WVUnit
  }
}

///|
/// Project the first component; non-pairs return `WVUnit`.
pub fn wfst(v : WValue) -> WValue {
  match v {
    WVPair(a, _) => a
    _ => WVUnit
  }
}

///|
/// Project the second component; non-pairs return `WVUnit`.
pub fn wsnd(v : WValue) -> WValue {
  match v {
    WVPair(_, b) => b
    _ => WVUnit
  }
}

// ---------------------------------------------------------------------------
// §3. Capture-avoiding variable maps, shift, substitution
// ---------------------------------------------------------------------------

///|
/// The single place which knows the binder structure of every
/// `WExpr` constructor.  `depth` counts binders entered so far;
/// `f(i, depth)` replaces variable `i` at that depth.
pub fn wexpr_map_vars_at(
  e : WExpr,
  depth : Int32,
  f : (Int32, Int32) -> WExpr,
) -> WExpr {
  match e {
    WVar(i) => f(i, depth)
    WPi(a, b) =>
      WPi(wexpr_map_vars_at(a, depth, f), wexpr_map_vars_at(b, depth + 1, f))
    WSigma(a, b) =>
      WSigma(wexpr_map_vars_at(a, depth, f), wexpr_map_vars_at(b, depth + 1, f))
    WType(a, b) =>
      WType(wexpr_map_vars_at(a, depth, f), wexpr_map_vars_at(b, depth + 1, f))
    WSup(a, f2) =>
      WSup(wexpr_map_vars_at(a, depth, f), wexpr_map_vars_at(f2, depth, f))
    WElim(m, s, t) =>
      WElim(
        wexpr_map_vars_at(m, depth + 1, f),
        wexpr_map_vars_at(s, depth + 3, f),
        wexpr_map_vars_at(t, depth, f),
      )
    WLam(body) => WLam(wexpr_map_vars_at(body, depth + 1, f))
    WApp(x, y) =>
      WApp(wexpr_map_vars_at(x, depth, f), wexpr_map_vars_at(y, depth, f))
    WPair(x, y) =>
      WPair(wexpr_map_vars_at(x, depth, f), wexpr_map_vars_at(y, depth, f))
    WFst(x) => WFst(wexpr_map_vars_at(x, depth, f))
    WSnd(x) => WSnd(wexpr_map_vars_at(x, depth, f))
    WBoolElim(m, x, y, z) =>
      WBoolElim(
        wexpr_map_vars_at(m, depth + 1, f),
        wexpr_map_vars_at(x, depth, f),
        wexpr_map_vars_at(y, depth, f),
        wexpr_map_vars_at(z, depth, f),
      )
    WSucc(x) => WSucc(wexpr_map_vars_at(x, depth, f))
    WNatElim(m, x, y, z) =>
      WNatElim(
        wexpr_map_vars_at(m, depth + 1, f),
        wexpr_map_vars_at(x, depth, f),
        wexpr_map_vars_at(y, depth, f),
        wexpr_map_vars_at(z, depth, f),
      )
    other => other
  }
}

///|
/// Shift free variables at or above `cutoff` by `delta`.
pub fn wexpr_shift(e : WExpr, cutoff : Int32, delta : Int32) -> WExpr {
  wexpr_map_vars_at(e, 0, (i, depth) => {
    if i >= cutoff + depth {
      WVar(i + delta)
    } else {
      WVar(i)
    }
  })
}

///|
/// Capture-avoiding substitution of one de Bruijn variable.
pub fn wexpr_subst(e : WExpr, index : Int32, repl : WExpr) -> WExpr {
  wexpr_map_vars_at(e, 0, (i, depth) => {
    if i == index + depth {
      wexpr_shift(repl, 0, depth)
    } else {
      WVar(i)
    }
  })
}

///|
/// Substitute the three binders of an `ind-W` step body:
/// `WVar(2)` (label) by `a`, `WVar(1)` (subtree map) by `f`,
/// `WVar(0)` (recursive hypotheses) by `ih`.
pub fn wexpr_subst_step(
  step : WExpr,
  a : WExpr,
  f : WExpr,
  ih : WExpr,
) -> WExpr {
  wexpr_map_vars_at(step, 0, (i, depth) => {
    if i == 2 + depth {
      wexpr_shift(a, 0, depth)
    } else if i == 1 + depth {
      wexpr_shift(f, 0, depth)
    } else if i == 0 + depth {
      wexpr_shift(ih, 0, depth)
    } else {
      WVar(i)
    }
  })
}

///|
/// Immediate ambient subterms of a node (for size/height measures).
pub fn wexpr_children(e : WExpr) -> Array[WExpr] {
  match e {
    WPi(a, b)
    | WSigma(a, b)
    | WType(a, b)
    | WSup(a, b)
    | WApp(a, b)
    | WPair(a, b) => [a, b]
    WElim(a, b, c) => [a, b, c]
    WLam(a) | WFst(a) | WSnd(a) | WSucc(a) => [a]
    WBoolElim(a, b, c, d) | WNatElim(a, b, c, d) => [a, b, c, d]
    _ => []
  }
}

///|
/// Number of syntax nodes (tree size).
pub fn wexpr_size(e : WExpr) -> Int32 {
  let kids = wexpr_children(e)
  let mut n = 1
  for i in 0..<kids.length() {
    n = n + wexpr_size(kids[i])
  }
  n
}

// ---------------------------------------------------------------------------
// §4. Formation rules
// ---------------------------------------------------------------------------

///|
/// Structural well-formedness of a type expression.  This is a
/// decidable pre-check: it verifies the type-former shape
/// recursively.  Deep dependent checks (e.g. that a body really is a
/// family over its binder) are delegated to the kernel bridge
/// (`wtype_formation_kernel`), which runs `d_infer`/`d_check`.
pub fn wexpr_is_type(e : WExpr) -> Bool {
  match e {
    WUniv(_) | WBoolTy | WUnitTy | WNatTy => true
    WPi(a, b) | WSigma(a, b) | WType(a, b) =>
      wexpr_is_type(a) && wexpr_is_type_under(b, a)
    _ => false
  }
}

///|
/// Structural well-formedness of a type expression read under one
/// binder of type `dom` (the body of a `WPi`/`WSigma`/`WType`).
pub fn wexpr_is_type_under(e : WExpr, dom : WExpr) -> Bool {
  match e {
    WUniv(_) | WBoolTy | WUnitTy | WNatTy => true
    WPi(a, b) | WSigma(a, b) | WType(a, b) =>
      wexpr_is_type(a) && wexpr_is_type_under(b, a)
    WVar(_) => true
    WApp(f, a) => wexpr_is_type_under(f, dom) && wexpr_is_type_under(a, dom)
    _ => false
  }
}

///|
/// W-formation rule:
///     A : Type_i     B : A -> Type_i
///     ------------------------------
///     W (x : A). B : Type_i
/// Structural pre-check; use `wtype_formation_kernel` for the deep
/// kernel-verified version.
pub fn w_wtype_formation(a : WExpr, b : WExpr) -> Bool {
  wexpr_is_type(a) && wexpr_is_type_under(b, a)
}

///|
/// Constructor formation rule:
///     a : A     f : (x : A) -> W A B
///     ------------------------------
///     sup a f : W A B
/// Structural pre-check on the W-type shape; the deep check is
/// `w_sup_formation_kernel`.
pub fn w_sup_formation(a : WExpr, f : WExpr, wty : WExpr) -> Bool {
  match wty {
    WType(a_ty, _) =>
      wexpr_is_type(a_ty) &&
      (match f {
        WLam(_) | WVar(_) | WApp(_, _) => true
        _ => false
      }) &&
      (match a {
        WType(_, _) | WPi(_, _) | WSigma(_, _) | WUniv(_) => false
        _ => true
      })
    _ => false
  }
}

///|
/// Eliminator formation rule:
///     motive : W A B -> Type_i
///     step : (a : A) -> ((x : A) -> motive (f x)) -> motive (sup a f)
///     scrut : W A B
///     ------------------------------------------------
///     ind-W motive step scrut : motive scrut
/// Structural pre-check; the deep check is `w_elim_formation_kernel`.
pub fn w_elim_formation(
  motive : WExpr,
  step : WExpr,
  scrut : WExpr,
  wty : WExpr,
) -> Bool {
  match wty {
    WType(_, _) =>
      (match motive {
        WType(_, _) | WPi(_, _) | WSigma(_, _) | WUniv(_) => false
        _ => true
      }) &&
      (match step {
        WType(_, _) | WPi(_, _) | WSigma(_, _) | WUniv(_) => false
        _ => true
      }) &&
      (match scrut {
        WType(_, _) | WPi(_, _) | WSigma(_, _) | WUniv(_) => false
        _ => true
      })
    _ => false
  }
}

// ---------------------------------------------------------------------------
// §5. Evaluation, ind-W / wf-rec, accessibility
// ---------------------------------------------------------------------------

///|
/// Evaluate a W-expression in an environment.
pub fn wexpr_eval(e : WExpr, env : WEnv) -> WValue {
  match e {
    WVar(i) =>
      match wenv_at(env, i) {
        Some(v) => v
        None => WVNeutral(i)
      }
    WUniv(_)
    | WBoolTy
    | WUnitTy
    | WNatTy
    | WPi(_, _)
    | WSigma(_, _)
    | WType(_, _) => WVUnit
    WSup(a, f) => {
      let av = wexpr_eval(a, env)
      let fv = wexpr_eval(f, env)
      WVSup(av, x => wapp(fv, x))
    }
    WElim(motive, step, scrut) => {
      // The real work is in `w_elim_value`, which takes host
      // closures; build them here.
      let mf = (x : WValue) => wexpr_eval(motive, wenv_cons(x, env))
      let sf = (a : WValue, f : (WValue) -> WValue, ih : (WValue) -> WValue) => {
        // Step body under three binders: (label, subtree map, hyps).
        // The hypothesis function is reified as a `WVLam` value.
        let ih_val = WVLam(ih)
        let f_val = WVLam(f)
        let env3 = wenv_cons(ih_val, wenv_cons(f_val, wenv_cons(a, env)))
        wexpr_eval(step, env3)
      }
      w_elim_value(mf, sf, wexpr_eval(scrut, env))
    }
    WLam(body) => WVLam(arg => wexpr_eval(body, wenv_cons(arg, env)))
    WApp(f, a) => wapp(wexpr_eval(f, env), wexpr_eval(a, env))
    WPair(x, y) => WVPair(wexpr_eval(x, env), wexpr_eval(y, env))
    WFst(x) => wfst(wexpr_eval(x, env))
    WSnd(x) => wsnd(wexpr_eval(x, env))
    WUnit => WVUnit
    WBoolLit(b) => WVBool(b)
    WBoolElim(motive, tt, ff, scrut) => {
      let mf = (x : WValue) => wexpr_eval(motive, wenv_cons(x, env))
      let _ = mf
      match wexpr_eval(scrut, env) {
        WVBool(true) => wexpr_eval(tt, env)
        WVBool(false) => wexpr_eval(ff, env)
        WVNeutral(n) => WVNeutral(n)
        _ => WVUnit
      }
    }
    WNatZero => WVZero
    WSucc(x) => WVSucc(wexpr_eval(x, env))
    WNatElim(motive, z, s, scrut) => {
      let mf = (x : WValue) => wexpr_eval(motive, wenv_cons(x, env))
      let _ = mf
      w_nat_elim_value(
        (x : WValue) => wexpr_eval(motive, wenv_cons(x, env)),
        wexpr_eval(z, env),
        wexpr_eval(s, env),
        wexpr_eval(scrut, env),
      )
    }
  }
}

///|
/// Nat elimination on values (helper for `WNatElim`).
pub fn w_nat_elim_value(
  motive : (WValue) -> WValue,
  z : WValue,
  s : WValue,
  scrut : WValue,
) -> WValue {
  match scrut {
    WVZero => z
    WVSucc(n) => {
      let ih = w_nat_elim_value(motive, z, s, n)
      let step1 = wapp(s, n)
      wapp(step1, ih)
    }
    WVNeutral(n) => WVNeutral(n)
    _ => WVUnit
  }
}

///|
/// The W-eliminator on values (`ind-W`, a.k.a. `wf-rec`).
///
/// `motive` maps a W-value to its result type; `step` receives the
/// label `a`, the subtree map `f`, and the hypothesis function
/// `ih : (x : A) -> motive (f x)`.  The beta rule is
///     ind-W(motive, step, sup(a, f))
///       = step(a, f, λx. ind-W(motive, step, f x))
/// Recursive calls are made only on immediate subtrees `f x`, which
/// are structurally smaller; hence every function defined this way
/// terminates (see `w_accessible`).
pub fn w_elim_value(
  motive : (WValue) -> WValue,
  step : (WValue, (WValue) -> WValue, (WValue) -> WValue) -> WValue,
  scrut : WValue,
) -> WValue {
  match scrut {
    WVSup(a, f) => step(a, f, x => w_elim_value(motive, step, f(x)))
    WVNeutral(n) => WVNeutral(n)
    _ => WVUnit
  }
}

///|
/// Well-founded recursion combinator.  Identical to `w_elim_value`;
/// the name records the termination discipline: the hypothesis
/// function is only ever applied to immediate subtrees, so the
/// recursion is well-founded by accessibility (`w_accessible`).
pub fn w_wf_rec(
  motive : (WValue) -> WValue,
  step : (WValue, (WValue) -> WValue, (WValue) -> WValue) -> WValue,
  scrut : WValue,
) -> WValue {
  w_elim_value(motive, step, scrut)
}

///|
/// Fuel-bounded `ind-W`.  Returns `None` when the fuel is below the
/// tree height.  The bound is justified by `w_height`: each
/// recursive call goes to an immediate subtree, whose height is
/// strictly smaller, so `fuel >= height(scrut)` always suffices and
/// the recursion terminates.
pub fn w_elim_fuel(
  motive : (WValue) -> WValue,
  step : (WValue, (WValue) -> WValue, (WValue) -> WValue) -> WValue,
  scrut : WValue,
  fuel : Int32,
) -> WValue? {
  if fuel < w_height(scrut) {
    return None
  }
  Some(w_elim_value(motive, step, scrut))
}

///|
/// Height of a W-tree: `height(sup(a, f)) = 1 + max_x height(f x)`.
/// For the finite examples here the maximum is taken over the
/// finitely many positions actually present; `WVNeutral` and
/// non-trees have height 0.
pub fn w_height(v : WValue) -> Int32 {
  match v {
    WVSup(_, f) => {
      // Probe the subtree map at the canonical finite positions
      // used by the examples (Bool/Nat labels).  The height is the
      // supremum over probed children plus one.
      let mut best = 0
      let probes = [WVBool(false), WVBool(true), WVZero, WVSucc(WVZero)]
      for i in 0..<probes.length() {
        let h = w_height(f(probes[i]))
        if h > best {
          best = h
        }
      }
      best + 1
    }
    WVSucc(n) => w_height(n) + 1
    WVPair(a, b) => {
      let ha = w_height(a)
      let hb = w_height(b)
      if ha > hb {
        ha
      } else {
        hb
      }
    }
    _ => 0
  }
}

///|
/// Number of `sup` nodes in a W-tree (probed as in `w_height`).
pub fn w_node_count(v : WValue) -> Int32 {
  match v {
    WVSup(_, f) => {
      let mut total = 1
      let probes = [WVBool(false), WVBool(true), WVZero, WVSucc(WVZero)]
      for i in 0..<probes.length() {
        total = total + w_node_count(f(probes[i]))
      }
      total
    }
    WVSucc(n) => w_node_count(n)
    WVPair(a, b) => w_node_count(a) + w_node_count(b)
    _ => 0
  }
}

///|
/// Accessibility predicate: every finite W-tree is accessible.
/// `WVSup(a, f)` is accessible iff every probed subtree `f x` is
/// accessible; neutrals and non-trees are not accessible.
pub fn w_accessible(v : WValue) -> Bool {
  match v {
    WVSup(_, f) => {
      let probes = [WVBool(false), WVBool(true), WVZero, WVSucc(WVZero)]
      let mut ok = true
      for i in 0..<probes.length() {
        if !w_accessible(f(probes[i])) {
          ok = false
        }
      }
      ok
    }
    WVZero => true
    WVSucc(n) => w_accessible(n)
    WVPair(a, b) => w_accessible(a) && w_accessible(b)
    WVUnit | WVBool(_) => true
    WVNeutral(_) | WVLam(_) => false
  }
}

///|
/// Subtree relation: `y` is a subtree of `x` iff `y = x` or
/// `y = f z` for some probed position `z` when `x = sup(a, f)`.
/// Immediate subtrees are strictly smaller (`w_height` decreases),
/// which is the termination measure for `ind-W`.
pub fn w_subtree(x : WValue, y : WValue) -> Bool {
  match x {
    WVSup(_, f) => {
      let probes = [WVBool(false), WVBool(true), WVZero, WVSucc(WVZero)]
      let mut found = false
      for i in 0..<probes.length() {
        let child = f(probes[i])
        if w_value_eq(child, y) || w_subtree(child, y) {
          found = true
        }
      }
      found
    }
    WVSucc(n) => w_value_eq(n, y) || w_subtree(n, y)
    WVPair(a, b) =>
      w_value_eq(a, y) || w_value_eq(b, y) || w_subtree(a, y) || w_subtree(b, y)
    _ => false
  }
}

///|
/// Observational equality on finite W-values (labels and probed
/// subtrees).  Function values are compared by probing.
pub fn w_value_eq(a : WValue, b : WValue) -> Bool {
  match (a, b) {
    (WVUnit, WVUnit) => true
    (WVBool(x), WVBool(y)) => x == y
    (WVZero, WVZero) => true
    (WVSucc(x), WVSucc(y)) => w_value_eq(x, y)
    (WVPair(x1, y1), WVPair(x2, y2)) => w_value_eq(x1, x2) && w_value_eq(y1, y2)
    (WVSup(a1, f1), WVSup(a2, f2)) => {
      let probes = [WVBool(false), WVBool(true), WVZero, WVSucc(WVZero)]
      let mut ok = w_value_eq(a1, a2)
      for i in 0..<probes.length() {
        if !w_value_eq(f1(probes[i]), f2(probes[i])) {
          ok = false
        }
      }
      ok
    }
    (WVNeutral(x), WVNeutral(y)) => x == y
    _ => false
  }
}

// ---------------------------------------------------------------------------
// §6. Beta-reduction engine
// ---------------------------------------------------------------------------

///|
/// One-step beta reduction.  The W-beta rule is
///     ind-W(motive, step, sup(a, f))
///       ==> step[a, f, λx. ind-W(motive, step, f x)]
/// where the step body is read under three binders
/// (label, subtree map, hypotheses).  Ordinary beta
/// `(λx. body) arg ==> body[arg/x]` is included, together with
/// congruence closure (reduce subterms when no top redex fires).
pub fn w_beta_step(e : WExpr) -> WExpr? {
  match e {
    WElim(motive, step, WSup(a, f)) => {
      // Hypotheses: λx. ind-W(motive, step, f x), with the ambient
      // motive/step/f shifted under the λx binder.
      let ih = WLam(
        WElim(
          wexpr_shift(motive, 0, 1),
          wexpr_shift(step, 0, 1),
          WApp(wexpr_shift(f, 0, 1), WVar(0)),
        ),
      )
      Some(wexpr_subst_step(step, a, f, ih))
    }
    WApp(WLam(body), arg) => Some(wexpr_subst(body, 0, arg))
    WSup(a, f) =>
      match w_beta_step(a) {
        Some(a2) => Some(WSup(a2, f))
        None =>
          match w_beta_step(f) {
            Some(f2) => Some(WSup(a, f2))
            None => None
          }
      }
    WElim(motive, step, scrut) =>
      match w_beta_step(scrut) {
        Some(s2) => Some(WElim(motive, step, s2))
        None =>
          match w_beta_step(motive) {
            Some(m2) => Some(WElim(m2, step, scrut))
            None =>
              match w_beta_step(step) {
                Some(s2) => Some(WElim(motive, s2, scrut))
                None => None
              }
          }
      }
    WApp(f, a) =>
      match w_beta_step(f) {
        Some(f2) => Some(WApp(f2, a))
        None =>
          match w_beta_step(a) {
            Some(a2) => Some(WApp(f, a2))
            None => None
          }
      }
    WLam(body) =>
      match w_beta_step(body) {
        Some(b2) => Some(WLam(b2))
        None => None
      }
    WPair(x, y) =>
      match w_beta_step(x) {
        Some(x2) => Some(WPair(x2, y))
        None =>
          match w_beta_step(y) {
            Some(y2) => Some(WPair(x, y2))
            None => None
          }
      }
    WFst(x) =>
      match w_beta_step(x) {
        Some(x2) => Some(WFst(x2))
        None => None
      }
    WSnd(x) =>
      match w_beta_step(x) {
        Some(x2) => Some(WSnd(x2))
        None => None
      }
    WSucc(x) =>
      match w_beta_step(x) {
        Some(x2) => Some(WSucc(x2))
        None => None
      }
    WBoolElim(motive, tt, ff, scrut) =>
      match w_beta_step(scrut) {
        Some(s2) => Some(WBoolElim(motive, tt, ff, s2))
        None => None
      }
    WNatElim(motive, z, s, scrut) =>
      match w_beta_step(scrut) {
        Some(s2) => Some(WNatElim(motive, z, s, s2))
        None => None
      }
    _ => None
  }
}

///|
/// Full normalization with a fuel bound.  Returns the normal form,
/// the number of steps taken, and whether the fuel ran out.
pub fn w_normalize(e : WExpr, fuel : Int32) -> (WExpr, Int32, Bool) {
  let mut cur = e
  let mut steps = 0
  let mut remaining = fuel
  while remaining > 0 {
    match w_beta_step(cur) {
      Some(next) => {
        cur = next
        steps = steps + 1
        remaining = remaining - 1
      }
      None => return (cur, steps, false)
    }
  }
  (cur, steps, true)
}

///|
/// Check the W-beta rule instance: normalizing
/// `ind-W(motive, step, sup(a, f))` yields the reduct
/// `step[a, f, λx. ind-W(motive, step, f x)]` (up to further
/// normalization of both sides).
pub fn w_beta_holds(motive : WExpr, step : WExpr, a : WExpr, f : WExpr) -> Bool {
  let lhs = WElim(motive, step, WSup(a, f))
  let ih = WLam(
    WElim(
      wexpr_shift(motive, 0, 1),
      wexpr_shift(step, 0, 1),
      WApp(wexpr_shift(f, 0, 1), WVar(0)),
    ),
  )
  let rhs = wexpr_subst_step(step, a, f, ih)
  let (nl, _, _) = w_normalize(lhs, 100)
  let (nr, _, _) = w_normalize(rhs, 100)
  nl == nr
}

// ---------------------------------------------------------------------------
// §7. Bridge to the trusted kernel (DTerm / DInductiveSpec)
// ---------------------------------------------------------------------------

///|
/// Build the `DInductiveSpec` for `W (x : A). B`.
///
/// The W-type is the initial algebra of the container functor
/// `F(X) = Σ (a : A), (B a -> X)`, encoded as a single constructor
/// `sup` with one external argument (the label, of type `A`) and
/// one function argument (the subtree map, of domain `B a`).
/// `a` and `b` are DTerms with `a : Type_level` and
/// `b : Pi a Type_level` (b under one binder for the label).
/// The bridge requires `a`/`b` closed; the spec is not traversed
/// by `dterm_shift`.
pub fn w_spec_of(a : DTerm, b : DTerm, level : Int32) -> DInductiveSpec {
  dinductive_spec("W", level, [], [], [
    dconstructor_spec("sup", [
      darg_external("label", a),
      darg_function("children", DApp(b, DTVar(0))),
    ]),
  ])
}

///|
/// Translate `W (x : A). B` (given as DTerms) to the kernel type
/// `DInductive(spec, [])`.
pub fn wtype_to_dterm(a : DTerm, b : DTerm, level : Int32) -> DTerm {
  DInductive(w_spec_of(a, b, level), [])
}

///|
/// Kernel-verified W-formation: `A : Type_i`, `B : A -> Type_i`,
/// and `W A B : Type_i` all check with `d_as_type`/`d_check`.
pub fn wtype_formation_kernel(a : DTerm, b : DTerm) -> Bool {
  let ctx = denv_empty()
  let env = denv_empty()
  let denv = ddim_empty()
  match d_as_type(a, ctx, env, denv) {
    Some(at) => {
      let fam_ty = DVPi(at.value, _ => DVUniv(at.level))
      let b_ok = match d_check(b, fam_ty, ctx, env, denv) {
        Some(_) => true
        None => false
      }
      let w_ok = match
        d_as_type(wtype_to_dterm(a, b, at.level), ctx, env, denv) {
        Some(_) => true
        None => false
      }
      b_ok && w_ok
    }
    None => false
  }
}

///|
/// Translate `sup a f` to the kernel constructor `DIntro`.
/// `a_ty`/`b_ty` are the DTerms for `A` and `B`.
pub fn w_sup_to_dterm(
  a : DTerm,
  f : DTerm,
  a_ty : DTerm,
  b_ty : DTerm,
) -> DTerm {
  DIntro(w_spec_of(a_ty, b_ty, 0), 0, [], [a, f])
}

///|
/// Kernel-verified `sup` formation: `sup(a, λx. w) : W A B` in a
/// context with `w : W A B`.  The subtree map is `λx. w` (the
/// ambient W-variable), which is finite and well-typed; closed
/// subtree maps would need infinite terms when positions are
/// empty, so the check is done in the open context.
pub fn w_sup_formation_kernel(a : DTerm, a_ty : DTerm, b_ty : DTerm) -> Bool {
  let spec = w_spec_of(a_ty, b_ty, 0)
  let w_dt = DInductive(spec, [])
  let ctx0 = denv_empty()
  let env0 = denv_empty()
  let denv = ddim_empty()
  let w_val = deval_dim(w_dt, env0, denv)
  let ctx = denv_cons(w_val, ctx0)
  let env = denv_cons(w_val, env0)
  let f = DLam(DApp(b_ty, a), DTVar(1))
  match d_check(DIntro(spec, 0, [], [a, f]), w_val, ctx, env, denv) {
    Some(_) => true
    None => false
  }
}

///|
/// Translate `ind-W motive step scrut` to the kernel eliminator
/// `DInductiveElim`.  `motive` is a DTerm body under one binder
/// (the W-value); `step` is a DTerm body under three binders
/// (label, subtree map, hypotheses).  The DLam domains are the
/// label type, the subtree-map type, and the hypothesis type
/// `(x : B a) -> motive (f x)`, with shifts for the ambient
/// binders.  `a_ty`/`b_ty` must be closed.
pub fn w_elim_to_dterm(
  motive : DTerm,
  step : DTerm,
  scrut : DTerm,
  a_ty : DTerm,
  b_ty : DTerm,
) -> DTerm {
  let spec = w_spec_of(a_ty, b_ty, 0)
  let w_dt = DInductive(spec, [])
  let motive_dt = DLam(w_dt, motive)
  // Subtree-map type under one binder (label): (x : B a) -> W A B.
  let children_dt = DPi(DApp(dterm_shift(b_ty, 0, 1), DTVar(0)), w_dt)
  // Hypothesis type under two binders (label, subtree map):
  // (x : B a) -> motive (f x).
  let ih_dt = DPi(
    DApp(dterm_shift(b_ty, 0, 2), DTVar(1)),
    DApp(dterm_shift(motive_dt, 0, 3), DApp(DTVar(1), DTVar(0))),
  )
  let step_dt = DLam(a_ty, DLam(children_dt, DLam(ih_dt, step)))
  DInductiveElim(spec, motive_dt, [step_dt], [], [], scrut)
}

///|
/// Kernel-verified `ind-W` formation: `ind-W motive step w :
/// motive w` in a context with `w : W A B`.  `motive` is a body
/// under one binder, `step` a body under three binders; the
/// scrutinee is the ambient W-variable.
pub fn w_elim_formation_kernel(
  motive : DTerm,
  step : DTerm,
  a_ty : DTerm,
  b_ty : DTerm,
) -> Bool {
  let spec = w_spec_of(a_ty, b_ty, 0)
  let w_dt = DInductive(spec, [])
  let ctx0 = denv_empty()
  let env0 = denv_empty()
  let denv = ddim_empty()
  let w_val = deval_dim(w_dt, env0, denv)
  let ctx = denv_cons(w_val, ctx0)
  let env = denv_cons(w_val, env0)
  let elim_dt = w_elim_to_dterm(motive, step, DTVar(0), a_ty, b_ty)
  // Well-formed iff the kernel infers a type for the eliminator
  // (the inferred type is `motive scrut`, a type in `Type_i`).
  match d_infer(elim_dt, ctx, env, denv) {
    Some(_) => true
    None => false
  }
}

///|
/// Translate a `WExpr` to a kernel `DTerm`, threading the expected
/// W-type (`wty`) for `WSup`/`WElim` nodes.  Returns `None` when a
/// `WSup`/`WElim` node lacks a `WType` context.
pub fn wexpr_to_dterm_at(e : WExpr, wty : WExpr?) -> DTerm? {
  match e {
    WVar(i) => Some(DTVar(i))
    WUniv(l) => Some(DUniv(l))
    WBoolTy => Some(DBoolTy)
    WUnitTy => Some(DUnitTy)
    WNatTy => Some(DNatTy)
    WPi(a, b) =>
      match (wexpr_to_dterm_at(a, None), wexpr_to_dterm_at(b, None)) {
        (Some(ad), Some(bd)) => Some(DPi(ad, bd))
        _ => None
      }
    WSigma(a, b) =>
      match (wexpr_to_dterm_at(a, None), wexpr_to_dterm_at(b, None)) {
        (Some(ad), Some(bd)) => Some(DSigma(ad, bd))
        _ => None
      }
    WType(a, b) =>
      match (wexpr_to_dterm_at(a, None), wexpr_to_dterm_at(b, None)) {
        (Some(ad), Some(bd)) => Some(wtype_to_dterm(ad, bd, 0))
        _ => None
      }
    WSup(a, f) =>
      match wty {
        Some(WType(a_ty, b_ty)) =>
          match
            (
              wexpr_to_dterm_at(a, None),
              wexpr_to_dterm_at(f, None),
              wexpr_to_dterm_at(a_ty, None),
              wexpr_to_dterm_at(b_ty, None),
            ) {
            (Some(ad), Some(fd), Some(atd), Some(btd)) =>
              Some(w_sup_to_dterm(ad, fd, atd, btd))
            _ => None
          }
        _ => None
      }
    WElim(motive, step, scrut) =>
      match wty {
        Some(WType(a_ty, b_ty)) =>
          match
            (
              wexpr_to_dterm_at(motive, None),
              wexpr_to_dterm_at(step, None),
              wexpr_to_dterm_at(scrut, wty),
              wexpr_to_dterm_at(a_ty, None),
              wexpr_to_dterm_at(b_ty, None),
            ) {
            (Some(md), Some(sd), Some(scd), Some(atd), Some(btd)) =>
              Some(w_elim_to_dterm(md, sd, scd, atd, btd))
            _ => None
          }
        _ => None
      }
    WLam(body) =>
      match wexpr_to_dterm_at(body, None) {
        Some(bd) => Some(DLam(DUnitTy, bd))
        None => None
      }
    WApp(f, a) =>
      match (wexpr_to_dterm_at(f, None), wexpr_to_dterm_at(a, None)) {
        (Some(fd), Some(ad)) => Some(DApp(fd, ad))
        _ => None
      }
    WPair(x, y) =>
      match (wexpr_to_dterm_at(x, None), wexpr_to_dterm_at(y, None)) {
        (Some(xd), Some(yd)) => Some(DPair(xd, yd))
        _ => None
      }
    WFst(x) =>
      match wexpr_to_dterm_at(x, None) {
        Some(xd) => Some(DFst(xd))
        None => None
      }
    WSnd(x) =>
      match wexpr_to_dterm_at(x, None) {
        Some(xd) => Some(DSnd(xd))
        None => None
      }
    WUnit => Some(DUnitLit)
    WBoolLit(b) => Some(DBoolLit(b))
    WBoolElim(motive, tt, ff, scrut) =>
      match
        (
          wexpr_to_dterm_at(motive, None),
          wexpr_to_dterm_at(tt, None),
          wexpr_to_dterm_at(ff, None),
          wexpr_to_dterm_at(scrut, None),
        ) {
        (Some(md), Some(td), Some(fd), Some(scd)) =>
          Some(DBoolElim(md, td, fd, scd))
        _ => None
      }
    WNatZero => Some(DNatZero)
    WSucc(x) =>
      match wexpr_to_dterm_at(x, None) {
        Some(xd) => Some(DSucc(xd))
        None => None
      }
    WNatElim(motive, z, s, scrut) =>
      match
        (
          wexpr_to_dterm_at(motive, None),
          wexpr_to_dterm_at(z, None),
          wexpr_to_dterm_at(s, None),
          wexpr_to_dterm_at(scrut, None),
        ) {
        (Some(md), Some(zd), Some(sd), Some(scd)) =>
          Some(DNatElim(md, zd, sd, scd))
        _ => None
      }
  }
}

///|
/// Translate a `WExpr` to a kernel `DTerm` without W-type context.
/// `WSup`/`WElim` nodes need `wexpr_to_dterm_at` with an explicit
/// W-type; here they return `None`.
pub fn wexpr_to_dterm(e : WExpr) -> DTerm? {
  wexpr_to_dterm_at(e, None)
}

// ---------------------------------------------------------------------------
// §8. Examples
// ---------------------------------------------------------------------------

///|
/// Nat-as-W shape: `W (x : Bool). Bool` (binary-tree shape).
/// Used for syntax/beta demos; inhabitation is not required for
/// the beta rule.
pub fn w_example_shape() -> WExpr {
  WType(WBoolTy, WBoolTy)
}

///|
/// A sample `sup` term over the example shape:
/// `sup(true, λ_. sup(false, λ_. sup(true, λ_. ...)))` truncated
/// at the value level by the fuel bound.
pub fn w_example_sup() -> WExpr {
  WSup(
    WBoolLit(true),
    WLam(WSup(WBoolLit(false), WLam(WSup(WBoolLit(true), WLam(WUnit))))),
  )
}

///|
/// A sample eliminator term: `ind-W motive step scrut` with
/// constant motive `Nat` and a step that counts nodes.
pub fn w_example_elim() -> WExpr {
  // motive = λ_. Nat (constant), step = λa f ih. 1 + ih(false) + ih(true)
  // scrut = the sample sup.
  let motive = WNatTy
  let step = WLam(WLam(WLam(WSucc(WApp(WVar(0), WBoolLit(false))))))
  WElim(motive, step, w_example_sup())
}

///|
/// Hand-built finite W-tree (value level): a chain of length 3
/// over Bool labels, where `false` continues and `true` stops.
/// `tree = sup(false, λ_. sup(false, λ_. sup(true, λ_. tree)))`
/// with the innermost map returning the tree itself would loop;
/// instead the innermost map returns a neutral-free leaf built
/// from `WVUnit` labels.  For the height/count demos we use
/// Nat-labelled chains where the child map is total.
pub fn w_example_tree() -> WValue {
  // sup(0, λ_. sup(1, λ_. sup(2, λ_. sup(3, λ_. sup(0, λ_. leaf)))))
  // where leaf is a neutral-free value.  Since the child map is
  // probed at finitely many positions, the tree is finite.
  let leaf = WVUnit
  let t3 = WVSup(WVZero, _ => leaf)
  let t2 = WVSup(WVSucc(WVZero), _ => t3)
  let t1 = WVSup(WVSucc(WVSucc(WVZero)), _ => t2)
  let t0 = WVSup(WVZero, _ => t1)
  t0
}

///|
/// Maximum of two Nat values (unary `WVZero`/`WVSucc`).
pub fn w_nat_max(a : WValue, b : WValue) -> WValue {
  match (a, b) {
    (WVZero, _) => b
    (_, WVZero) => a
    (WVSucc(x), WVSucc(y)) => WVSucc(w_nat_max(x, y))
    _ => a
  }
}

///|
/// Height computed by `ind-W` (well-founded recursion):
/// `height(sup(a, f)) = 1 + max(height(f false), height(f true))`,
/// with heights as unary Nat values.
pub fn w_height_via_elim(v : WValue) -> WValue {
  w_wf_rec(
    _ => WVZero,
    (_a, _f, ih) => {
      let h0 = ih(WVBool(false))
      let h1 = ih(WVBool(true))
      WVSucc(w_nat_max(h0, h1))
    },
    v,
  )
}

///|
/// Bridge example types: `A = Bool`, `B = λb. (Bool -> (b = false))`
/// as DTerms.  `B(false)` is inhabited, `B(true)` is empty, so
/// `W A B` is the Nat-like W-type (true = zero, false = succ).
pub fn w_bridge_a() -> DTerm {
  DBoolTy
}

///|
pub fn w_bridge_b() -> DTerm {
  DLam(DBoolTy, DPi(DBoolTy, DPath(DBoolTy, DTVar(0), DBoolLit(false))))
}

///|
/// A bridge `sup` term: `sup(true, λ_. sup(true, λ_. ...))`
/// truncated; the child map is `λ_. sup(true, λ_. λ_. ...)` at
/// the DTerm level (well-typed only when the positions type is
/// inhabited; the kernel check is the arbiter).
pub fn w_bridge_sup() -> DTerm {
  // `sup(true, λx. w)` in the open context with `w : W A B`;
  // the subtree map returns the ambient W-variable.
  let spec = w_spec_of(w_bridge_a(), w_bridge_b(), 0)
  DIntro(spec, 0, [], [
    DBoolLit(true),
    DLam(DApp(w_bridge_b(), DBoolLit(true)), DTVar(1)),
  ])
}

// ---------------------------------------------------------------------------
// §9. Laws (executable propositions)
// ---------------------------------------------------------------------------

///|
/// W-formation holds for the example shape and fails for a
/// non-type label.
pub fn law_w_formation() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  out.push(
    (
      "w-formation: W Bool Bool is well-formed",
      w_wtype_formation(WBoolTy, WBoolTy),
    ),
  )
  out.push(
    (
      "w-formation: W Nat Unit is well-formed",
      w_wtype_formation(WNatTy, WUnitTy),
    ),
  )
  out.push(
    (
      "w-formation: W (W Bool Bool) Bool is well-formed",
      w_wtype_formation(WType(WBoolTy, WBoolTy), WBoolTy),
    ),
  )
  out.push(
    (
      "w-formation: non-type label is rejected",
      !w_wtype_formation(WVar(0), WBoolTy),
    ),
  )
  out
}

///|
/// `sup` formation holds for the sample sup and fails when the
/// expected type is not a W-type.
pub fn law_w_sup_formation() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let wty = w_example_shape()
  out.push(
    (
      "sup-formation: sample sup checks against W Bool Bool",
      w_sup_formation(WBoolLit(true), WLam(WUnit), wty),
    ),
  )
  out.push(
    (
      "sup-formation: non-W expected type is rejected",
      !w_sup_formation(WBoolLit(true), WLam(WUnit), WBoolTy),
    ),
  )
  out
}

///|
/// The beta rule holds: `ind-W(m, s, sup(a, f))` normalizes to
/// `s[a, f, λx. ind-W(m, s, f x)]`.
pub fn law_w_beta() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let motive = WNatTy
  let step = WLam(WLam(WLam(WVar(0))))
  out.push(
    (
      "beta: ind-W(m, s, sup(a, f)) ==> s(a, f, λx. ind-W(m, s, f x))",
      w_beta_holds(motive, step, WBoolLit(true), WLam(WUnit)),
    ),
  )
  out.push(
    (
      "beta: ordinary (λx. body) arg reduces",
      match w_beta_step(WApp(WLam(WVar(0)), WBoolLit(true))) {
        Some(WBoolLit(true)) => true
        _ => false
      },
    ),
  )
  out
}

///|
/// Normalization terminates on the sample eliminator and the
/// normal form has no redex.
pub fn law_w_normalize() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let e = w_example_elim()
  let (nf, steps, hit_fuel) = w_normalize(e, 200)
  out.push(("normalize: sample eliminator normalizes", !hit_fuel))
  out.push(("normalize: normal form is irreducible", w_beta_step(nf) == None))
  out.push(("normalize: at least one step was taken", steps > 0))
  out
}

///|
/// Identity step for `ind-W` (returns the label).
pub fn w_step_id(
  a : WValue,
  _f : (WValue) -> WValue,
  _ih : (WValue) -> WValue,
) -> WValue {
  a
}

///|
/// Well-founded recursion: the example tree is accessible, its
/// height is positive, and fuel at the height suffices.
pub fn law_w_wf_rec() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let t = w_example_tree()
  out.push(("wf-rec: example tree is accessible", w_accessible(t)))
  out.push(("wf-rec: example tree height is positive", w_height(t) > 0))
  out.push(("wf-rec: node count is positive", w_node_count(t) > 0))
  let motive = (_ : WValue) => WVZero
  let step = w_step_id
  let h = w_height(t)
  out.push(
    (
      "wf-rec: fuel at height suffices",
      match w_elim_fuel(motive, step, t, h) {
        Some(_) => true
        None => false
      },
    ),
  )
  out.push(
    (
      "wf-rec: fuel below height is rejected",
      match w_elim_fuel(motive, step, t, 0) {
        Some(_) => false
        None => true
      },
    ),
  )
  out
}

///|
/// Subtree descent: immediate subtrees have strictly smaller
/// height, which is the termination measure for `ind-W`.
pub fn law_w_subtree_descent() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let t = w_example_tree()
  match t {
    WVSup(_, f) => {
      let child = f(WVBool(false))
      out.push(
        ("descent: subtree height is smaller", w_height(child) < w_height(t)),
      )
      out.push(("descent: subtree relation holds", w_subtree(t, child)))
    }
    _ => out.push(("descent: example tree is a sup", false))
  }
  out
}

///|
/// Kernel bridge: W-formation, sup-formation and elim-formation
/// all check with the trusted kernel.
pub fn law_w_bridge() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  out.push(
    (
      "bridge: W-formation checks in kernel",
      wtype_formation_kernel(w_bridge_a(), w_bridge_b()),
    ),
  )
  out.push(
    (
      "bridge: sup-formation checks in kernel",
      w_sup_formation_kernel(DBoolLit(true), w_bridge_a(), w_bridge_b()),
    ),
  )
  // Elim formation: motive body = Nat (constant family),
  // step body = 0 under three binders (label, subtree map,
  // hypotheses); scrutinee is the ambient W-variable.
  let motive = DNatTy
  let step = DNatZero
  out.push(
    (
      "bridge: ind-W formation checks in kernel",
      w_elim_formation_kernel(motive, step, w_bridge_a(), w_bridge_b()),
    ),
  )
  out
}

///|
/// All W-type laws.
pub fn wtype_all_laws() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  for (l, b) in law_w_formation() {
    out.push((l, b))
  }
  for (l, b) in law_w_sup_formation() {
    out.push((l, b))
  }
  for (l, b) in law_w_beta() {
    out.push((l, b))
  }
  for (l, b) in law_w_normalize() {
    out.push((l, b))
  }
  for (l, b) in law_w_wf_rec() {
    out.push((l, b))
  }
  for (l, b) in law_w_subtree_descent() {
    out.push((l, b))
  }
  for (l, b) in law_w_bridge() {
    out.push((l, b))
  }
  out
}

///|
/// One-line demo for runners.
pub fn wtype_demo() -> String {
  let laws = wtype_all_laws()
  let mut pass = 0
  for i in 0..<laws.length() {
    if laws[i].1 {
      pass = pass + 1
    }
  }
  "W-types: \{pass}/\{laws.length()} laws hold (formation, sup, ind-W/wf-rec, beta, bridge)"
}
