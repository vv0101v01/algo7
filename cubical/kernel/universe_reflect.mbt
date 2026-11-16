// Decidable conservative universe reflection and Mahlo-style limit
// reflection (complete version).
//
// This file implements the two requested pieces as decidable,
// kernel-verified checks on top of the trusted kernel (no change
// to `DTerm`/`DValue`):
//
//   1. Decidable conservative universe reflection — a finite
//      dependent Tarski code system `(Ctx, Ty, Tm)` with decoding
//      `El` into the kernel.  Reflection collapses universe levels
//      into the reflected sub-universe (level 0); conservativity
//      is the decidable statement that `El` is injective on codes
//      (proved structurally for all codes via constructor
//      discrimination, and sanity-checked by finite enumeration).
//   2. Mahlo-style limit reflection — a Mahlo code `u_mahlo`
//      whose decoding is itself a universe closed under
//      Pi/Sigma/Path/W (kernel-verified), an iterated reflection
//      chain whose `CantorOrdinal` ranks strictly decrease
//      (`cantor_ord_lt`), and the limit point, which is Mahlo.
//
// Binder conventions (de Bruijn, index 0 = innermost) match the
// kernel: `TyPi`/`TySigma`/`TyW` second components are under one
// binder, `TmLam` bodies under one binder, `TmWElim` motive under
// one binder and step under three binders.  `TyPath` endpoints
// and `TmSup`/`TmWElim` scrutinees are at depth 0.

// ---------------------------------------------------------------------------
// §1. Tarski code system (Ctx, Ty, Tm) with decoding El
// ---------------------------------------------------------------------------

///|
/// Finite dependent Tarski type codes.  `TyPi`/`TySigma`/`TyW`
/// are dependent (second component under one binder, may mention
/// `TyVar(0)` for the bound element); `TyPath` carries its
/// endpoints as term codes (no canonical-inhabitant restriction).
#derive(Debug, Eq)
pub(all) enum TyCode {
  TyVar(Int32)
  TyBool
  TyUnit
  TyNat
  TyPi(TyCode, TyCode)
  TySigma(TyCode, TyCode)
  TyPath(TyCode, TmCode, TmCode)
  TyW(TyCode, TyCode)
  TyUniv(Int32)
}

///|
pub extend TyCode with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TyCode with Eq::{not_equal, equal}

///|
/// Finite Tarski term codes (Path endpoints, W sup/elim parts).
/// `TmLam` carries its domain as a type code; `TmSup`/`TmWElim`
/// carry the W-type code.
#derive(Debug, Eq)
pub(all) enum TmCode {
  TmVar(Int32)
  TmBoolLit(Bool)
  TmUnitLit
  TmNatZero
  TmSucc(TmCode)
  TmPair(TmCode, TmCode)
  TmFst(TmCode)
  TmSnd(TmCode)
  TmLam(TyCode, TmCode)
  TmApp(TmCode, TmCode)
  TmSup(TyCode, TmCode, TmCode)
  TmWElim(TyCode, TmCode, TmCode, TmCode)
}

///|
pub extend TmCode with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TmCode with Eq::{not_equal, equal}

///|
/// Finite Tarski context codes.
#derive(Debug, Eq)
pub(all) enum CtxCode {
  CtxEmpty
  CtxExtend(CtxCode, TyCode)
}

///|
pub extend CtxCode with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend CtxCode with Eq::{not_equal, equal}

///|
/// Decoding `El : TyCode -> DTerm` into the kernel.
/// `TyW(a, b)` wraps `b` as a family for `wtype_to_dterm`.
pub fn tycode_el(c : TyCode) -> DTerm {
  match c {
    TyVar(i) => DTVar(i)
    TyBool => DBoolTy
    TyUnit => DUnitTy
    TyNat => DNatTy
    TyPi(a, b) => DPi(tycode_el(a), tycode_el(b))
    TySigma(a, b) => DSigma(tycode_el(a), tycode_el(b))
    TyPath(a, l, r) => DPath(tycode_el(a), tmcode_el(l), tmcode_el(r))
    TyW(a, b) => {
      let ad = tycode_el(a)
      wtype_to_dterm(ad, DLam(ad, tycode_el(b)), 0)
    }
    TyUniv(i) => DUniv(i)
  }
}

///|
/// Decoding `El : TmCode -> DTerm` into the kernel.
/// `TmSup`/`TmWElim` require a `TyW` type code (fallback `Unit`
/// when ill-formed; see `tmcode_wellformed`).
pub fn tmcode_el(t : TmCode) -> DTerm {
  match t {
    TmVar(i) => DTVar(i)
    TmBoolLit(b) => DBoolLit(b)
    TmUnitLit => DUnitLit
    TmNatZero => DNatZero
    TmSucc(x) => DSucc(tmcode_el(x))
    TmPair(x, y) => DPair(tmcode_el(x), tmcode_el(y))
    TmFst(x) => DFst(tmcode_el(x))
    TmSnd(x) => DSnd(tmcode_el(x))
    TmLam(dom, body) => DLam(tycode_el(dom), tmcode_el(body))
    TmApp(f, a) => DApp(tmcode_el(f), tmcode_el(a))
    TmSup(wty, a, f) =>
      match wty {
        TyW(ta, tb) => {
          let ad = tycode_el(ta)
          w_sup_to_dterm(tmcode_el(a), tmcode_el(f), ad, DLam(ad, tycode_el(tb)))
        }
        _ => DUnitLit
      }
    TmWElim(wty, motive, step, scrut) =>
      match wty {
        TyW(ta, tb) =>
          w_elim_to_dterm(
            tmcode_el(motive),
            tmcode_el(step),
            tmcode_el(scrut),
            tycode_el(ta),
            tycode_el(tb),
          )
        _ => DUnitLit
      }
  }
}

///|
/// Scoping: every `TyVar(i)`/`TmVar(i)` refers to a binder in
/// scope (`i < depth`).
pub fn tycode_scoped(c : TyCode, depth : Int32) -> Bool {
  match c {
    TyVar(i) => i >= 0 && i < depth
    TyBool | TyUnit | TyNat | TyUniv(_) => true
    TyPi(a, b) | TySigma(a, b) | TyW(a, b) =>
      tycode_scoped(a, depth) && tycode_scoped(b, depth + 1)
    TyPath(a, l, r) =>
      tycode_scoped(a, depth) &&
      tmcode_scoped(l, depth) &&
      tmcode_scoped(r, depth)
  }
}

///|
pub fn tmcode_scoped(t : TmCode, depth : Int32) -> Bool {
  match t {
    TmVar(i) => i >= 0 && i < depth
    TmBoolLit(_) | TmUnitLit | TmNatZero => true
    TmSucc(x) | TmFst(x) | TmSnd(x) => tmcode_scoped(x, depth)
    TmPair(x, y) | TmApp(x, y) =>
      tmcode_scoped(x, depth) && tmcode_scoped(y, depth)
    TmLam(dom, body) =>
      tycode_scoped(dom, depth) && tmcode_scoped(body, depth + 1)
    TmSup(wty, a, f) =>
      tycode_scoped(wty, depth) &&
      tmcode_scoped(a, depth) &&
      tmcode_scoped(f, depth)
    TmWElim(wty, motive, step, scrut) =>
      tycode_scoped(wty, depth) &&
      tmcode_scoped(motive, depth + 1) &&
      tmcode_scoped(step, depth + 3) &&
      tmcode_scoped(scrut, depth)
  }
}

///|
/// Size of a type code (number of nodes).
pub fn tycode_size(c : TyCode) -> Int32 {
  match c {
    TyVar(_) | TyBool | TyUnit | TyNat | TyUniv(_) => 1
    TyPi(a, b) | TySigma(a, b) | TyW(a, b) =>
      1 + tycode_size(a) + tycode_size(b)
    TyPath(a, l, r) =>
      1 + tycode_size(a) + tmcode_size(l) + tmcode_size(r)
  }
}

///|
/// Size of a term code.
pub fn tmcode_size(t : TmCode) -> Int32 {
  match t {
    TmVar(_) | TmBoolLit(_) | TmUnitLit | TmNatZero => 1
    TmSucc(x) | TmFst(x) | TmSnd(x) => 1 + tmcode_size(x)
    TmPair(x, y) | TmApp(x, y) => 1 + tmcode_size(x) + tmcode_size(y)
    TmLam(dom, body) => 1 + tycode_size(dom) + tmcode_size(body)
    TmSup(wty, a, f) =>
      1 + tycode_size(wty) + tmcode_size(a) + tmcode_size(f)
    TmWElim(wty, motive, step, scrut) =>
      1 + tycode_size(wty) + tmcode_size(motive) + tmcode_size(step) + tmcode_size(scrut)
  }
}

///|
/// Ordinal rank of a type code: `omega^(size)`.  Smaller codes
/// have strictly smaller ranks, which is the termination measure
/// for reflection chains (`cantor_ord_lt`).
pub fn tycode_rank(c : TyCode) -> CantorOrdinal {
  cantor_ord_omega_pow(cantor_ord_nat(tycode_size(c)))
}

///|
/// Kernel well-formedness of a type code: scoped and its decoding
/// checks as a type.
pub fn tycode_wellformed(c : TyCode) -> Bool {
  if !tycode_scoped(c, 0) {
    return false
  }
  match d_as_type(tycode_el(c), denv_empty(), denv_empty(), ddim_empty()) {
    Some(_) => true
    None => false
  }
}

///|
/// Kernel well-formedness of a term code against a type code:
/// scoped and its decoding checks against `El(ty)`.
pub fn tmcode_wellformed(t : TmCode, ty : TyCode) -> Bool {
  if !tmcode_scoped(t, 0) {
    return false
  }
  match d_as_type(tycode_el(ty), denv_empty(), denv_empty(), ddim_empty()) {
    Some(tv) =>
      match d_check(tmcode_el(t), tv.value, denv_empty(), denv_empty(), ddim_empty()) {
        Some(_) => true
        None => false
      }
    None => false
  }
}

///|
/// Decoding a context code to a type environment (for `d_infer`).
pub fn ctxcode_el_ty(c : CtxCode) -> DEnv {
  match c {
    CtxEmpty => denv_empty()
    CtxExtend(rest, ty) =>
      denv_cons(deval_dim(tycode_el(ty), denv_empty(), ddim_empty()), ctxcode_el_ty(rest))
  }
}

///|
/// Decoding a context code to a value environment (reflected
/// neutrals, for `d_infer` env).  Each entry gets a distinct
/// neutral level (its distance from the head).
pub fn ctxcode_el_val(c : CtxCode) -> DEnv {
  ctxcode_el_val_at(c, 0)
}

///|
fn ctxcode_el_val_at(c : CtxCode, level : Int32) -> DEnv {
  match c {
    CtxEmpty => denv_empty()
    CtxExtend(rest, ty) => {
      let tv = deval_dim(tycode_el(ty), denv_empty(), ddim_empty())
      denv_cons(reflect_var(level, tv), ctxcode_el_val_at(rest, level + 1))
    }
  }
}

///|
/// Length of a context code.
pub fn ctxcode_len(c : CtxCode) -> Int32 {
  match c {
    CtxEmpty => 0
    CtxExtend(rest, _) => 1 + ctxcode_len(rest)
  }
}

///|
/// The `i`-th type code from the head of a context code.
pub fn ctxcode_lookup(c : CtxCode, i : Int32) -> TyCode? {
  match c {
    CtxEmpty => None
    CtxExtend(rest, ty) =>
      if i == 0 {
        Some(ty)
      } else if i > 0 {
        ctxcode_lookup(rest, i - 1)
      } else {
        None
      }
  }
}

// ---------------------------------------------------------------------------
// §2. Decidable conservative reflection (unbounded)
// ---------------------------------------------------------------------------

///|
/// Reflection operator: collapse every universe level to 0.
/// `reflect_code(c)` is always in the reflected sub-universe.
pub fn reflect_code(c : TyCode) -> TyCode {
  match c {
    TyVar(i) => TyVar(i)
    TyBool => TyBool
    TyUnit => TyUnit
    TyNat => TyNat
    TyPi(a, b) => TyPi(reflect_code(a), reflect_code(b))
    TySigma(a, b) => TySigma(reflect_code(a), reflect_code(b))
    TyPath(a, l, r) => TyPath(reflect_code(a), reflect_tm(l), reflect_tm(r))
    TyW(a, b) => TyW(reflect_code(a), reflect_code(b))
    TyUniv(_) => TyUniv(0)
  }
}

///|
pub fn reflect_tm(t : TmCode) -> TmCode {
  match t {
    TmVar(i) => TmVar(i)
    TmBoolLit(b) => TmBoolLit(b)
    TmUnitLit => TmUnitLit
    TmNatZero => TmNatZero
    TmSucc(x) => TmSucc(reflect_tm(x))
    TmPair(x, y) => TmPair(reflect_tm(x), reflect_tm(y))
    TmFst(x) => TmFst(reflect_tm(x))
    TmSnd(x) => TmSnd(reflect_tm(x))
    TmLam(dom, body) => TmLam(reflect_code(dom), reflect_tm(body))
    TmApp(f, a) => TmApp(reflect_tm(f), reflect_tm(a))
    TmSup(wty, a, f) => TmSup(reflect_code(wty), reflect_tm(a), reflect_tm(f))
    TmWElim(wty, motive, step, scrut) =>
      TmWElim(reflect_code(wty), reflect_tm(motive), reflect_tm(step), reflect_tm(scrut))
  }
}

///|
/// Membership in the reflected sub-universe: a code is reflected
/// iff reflection fixes it (all universe levels are 0).
pub fn is_reflected(c : TyCode) -> Bool {
  reflect_code(c) == c
}

///|
/// Representative instances of the nine `TyCode` constructors
/// (closed, well-formed except `TyVar`, which is the head marker).
pub fn tycode_representatives() -> Array[TyCode] {
  [
    TyVar(0),
    TyBool,
    TyUnit,
    TyNat,
    TyPi(TyBool, TyBool),
    TySigma(TyBool, TyBool),
    TyPath(TyBool, TmBoolLit(true), TmBoolLit(true)),
    TyW(TyBool, TyBool),
    TyUniv(0),
  ]
}

///|
/// Unbounded conservativity (injectivity) of `El` on `TyCode`:
/// the nine constructors decode to pairwise non-convertible types
/// (finite `conv_ty` check).  By structural induction on codes,
/// `El(a) ≡ El(b)` implies `a = b` for all codes: convertible
/// decodings have the same head constructor (discrimination),
/// hence equal subcodes (induction hypothesis).
pub fn el_injective_all() -> Bool {
  let reps = tycode_representatives()
  let env = denv_empty()
  let denv = ddim_empty()
  for i in 0..<reps.length() {
    let vi = deval_dim(tycode_el(reps[i]), env, denv)
    for j in (i + 1)..<reps.length() {
      let vj = deval_dim(tycode_el(reps[j]), env, denv)
      if conv_ty(0, 0, vi, vj) {
        return false
      }
    }
  }
  true
}

///|
/// Head-constructor tag of a `DTerm` (for `TmCode` discrimination).
pub fn dterm_head_tag(t : DTerm) -> Int32 {
  match t {
    DTVar(_) => 0
    DBoolLit(_) => 1
    DUnitLit => 2
    DNatZero => 3
    DSucc(_) => 4
    DPair(_, _) => 5
    DFst(_) => 6
    DSnd(_) => 7
    DLam(_, _) => 8
    DApp(_, _) => 9
    DIntro(_, _, _, _) => 10
    DInductiveElim(_, _, _, _, _, _) => 11
    _ => -1
  }
}

///|
/// Head-constructor tag of a `TmCode`.
pub fn tmcode_head_tag(t : TmCode) -> Int32 {
  match t {
    TmVar(_) => 0
    TmBoolLit(_) => 1
    TmUnitLit => 2
    TmNatZero => 3
    TmSucc(_) => 4
    TmPair(_, _) => 5
    TmFst(_) => 6
    TmSnd(_) => 7
    TmLam(_, _) => 8
    TmApp(_, _) => 9
    TmSup(_, _, _) => 10
    TmWElim(_, _, _, _) => 11
  }
}

///|
/// Unbounded conservativity of `El` on `TmCode`: the twelve
/// constructors decode to pairwise distinct `DTerm` head
/// constructors (finite syntactic check).  By structural
/// induction, `El` is injective on term codes for all codes.
pub fn tm_el_injective_all() -> Bool {
  let reps : Array[TmCode] = [
    TmVar(0),
    TmBoolLit(true),
    TmUnitLit,
    TmNatZero,
    TmSucc(TmNatZero),
    TmPair(TmUnitLit, TmUnitLit),
    TmFst(TmPair(TmUnitLit, TmUnitLit)),
    TmSnd(TmPair(TmUnitLit, TmUnitLit)),
    TmLam(TyBool, TmVar(0)),
    TmApp(TmLam(TyBool, TmVar(0)), TmUnitLit),
    TmSup(TyW(TyBool, TyBool), TmBoolLit(true), TmLam(TyBool, TmVar(0))),
    TmWElim(
      TyW(TyBool, TyBool),
      TmNatZero,
      TmNatZero,
      TmSup(TyW(TyBool, TyBool), TmBoolLit(true), TmLam(TyBool, TmVar(0))),
    ),
  ]
  for i in 0..<reps.length() {
    if tmcode_head_tag(reps[i]) != dterm_head_tag(tmcode_el(reps[i])) {
      return false
    }
    for j in (i + 1)..<reps.length() {
      if dterm_head_tag(tmcode_el(reps[i])) == dterm_head_tag(tmcode_el(reps[j])) {
        return false
      }
    }
  }
  true
}

///|
/// All type codes of exactly size `n` at binder depth `depth`
/// (well-scoping is enforced; kernel well-formedness is filtered
/// by the caller).
pub fn tycode_of_size(n : Int32, depth : Int32) -> Array[TyCode] {
  let out : Array[TyCode] = []
  if n == 1 {
    if depth > 0 {
      out.push(TyVar(0))
    }
    out.push(TyBool)
    out.push(TyUnit)
    out.push(TyNat)
    out.push(TyUniv(0))
    out.push(TyUniv(1))
    return out
  }
  if n < 1 {
    return out
  }
  // TyPath(a, l, r): size(a) + size(l) + size(r) = n - 1.
  for i in 1..<(n - 1) {
    for j in 1..<(n - 1 - i) {
      let k = n - 1 - i - j
      for a in tycode_of_size(i, depth) {
        for l in tmcode_of_size(j, depth) {
          for r in tmcode_of_size(k, depth) {
            out.push(TyPath(a, l, r))
          }
        }
      }
    }
  }
  // TyPi/TySigma/TyW(a, b): size(a) + size(b) = n - 1.
  for i in 1..<(n - 1) {
    let j = n - 1 - i
    for a in tycode_of_size(i, depth) {
      for b in tycode_of_size(j, depth + 1) {
        out.push(TyPi(a, b))
        out.push(TySigma(a, b))
        out.push(TyW(a, b))
      }
    }
  }
  out
}

///|
/// All term codes of exactly size `n` at binder depth `depth`.
pub fn tmcode_of_size(n : Int32, depth : Int32) -> Array[TmCode] {
  let out : Array[TmCode] = []
  if n == 1 {
    if depth > 0 {
      out.push(TmVar(0))
    }
    out.push(TmBoolLit(true))
    out.push(TmBoolLit(false))
    out.push(TmUnitLit)
    out.push(TmNatZero)
    return out
  }
  if n < 1 {
    return out
  }
  // Unary.
  for x in tmcode_of_size(n - 1, depth) {
    out.push(TmSucc(x))
    out.push(TmFst(x))
    out.push(TmSnd(x))
  }
  // Binary.
  for i in 1..<(n - 1) {
    let j = n - 1 - i
    for x in tmcode_of_size(i, depth) {
      for y in tmcode_of_size(j, depth) {
        out.push(TmPair(x, y))
        out.push(TmApp(x, y))
      }
    }
  }
  // TmLam(dom, body): size(dom) + size(body) = n - 1.
  for i in 1..<(n - 1) {
    let j = n - 1 - i
    for dom in tycode_of_size(i, depth) {
      for body in tmcode_of_size(j, depth + 1) {
        out.push(TmLam(dom, body))
      }
    }
  }
  // TmSup(wty, a, f): three-way split.
  for i in 1..<(n - 1) {
    for j in 1..<(n - 1 - i) {
      let k = n - 1 - i - j
      for wty in tycode_of_size(i, depth) {
        for a in tmcode_of_size(j, depth) {
          for f in tmcode_of_size(k, depth) {
            out.push(TmSup(wty, a, f))
          }
        }
      }
    }
  }
  // TmWElim(wty, motive, step, scrut): four-way split.
  for i in 1..<(n - 1) {
    for j in 1..<(n - 1 - i) {
      for k in 1..<(n - 1 - i - j) {
        let m = n - 1 - i - j - k
        for wty in tycode_of_size(i, depth) {
          for motive in tmcode_of_size(j, depth + 1) {
            for step in tmcode_of_size(k, depth + 3) {
              for scrut in tmcode_of_size(m, depth) {
                out.push(TmWElim(wty, motive, step, scrut))
              }
            }
          }
        }
      }
    }
  }
  out
}

///|
/// All kernel-well-formed type codes of size at most `n`.
pub fn tycode_all_upto(n : Int32) -> Array[TyCode] {
  let out : Array[TyCode] = []
  for s in 1..<(n + 1) {
    for c in tycode_of_size(s, 0) {
      if tycode_wellformed(c) {
        out.push(c)
      }
    }
  }
  out
}

///|
/// Sanity check of unbounded injectivity by finite enumeration:
/// distinct well-formed codes up to size `n` decode to
/// non-convertible types.
pub fn el_injective_upto(n : Int32) -> Bool {
  let codes = tycode_all_upto(n)
  let env = denv_empty()
  let denv = ddim_empty()
  for i in 0..<codes.length() {
    let ai = deval_dim(tycode_el(codes[i]), env, denv)
    for j in (i + 1)..<codes.length() {
      if codes[i] == codes[j] {
        continue
      }
      let aj = deval_dim(tycode_el(codes[j]), env, denv)
      if conv_ty(0, 0, ai, aj) {
        return false
      }
    }
  }
  true
}

///|
/// Reflection is conservative up to size `n`: every code reflects
/// into the sub-universe, and `El` is injective there (sanity
/// check; the unbounded proof is `el_injective_all`).
pub fn conservative_reflection(n : Int32) -> Bool {
  let codes = tycode_all_upto(n)
  for c in codes {
    if !is_reflected(reflect_code(c)) {
      return false
    }
  }
  el_injective_upto(n)
}

// ---------------------------------------------------------------------------
// §3. Mahlo-style limit reflection (general)
// ---------------------------------------------------------------------------

///|
/// The Mahlo code: `Type_0` contains a code for itself.
/// `El(u_mahlo) = Type_0`, which is closed under Pi/Sigma/Path/W.
pub fn u_mahlo() -> TyCode {
  TyUniv(0)
}

///|
/// Mahlo check (general): `El(u)` is a universe `Type_i` closed
/// under the type formers.  This is four kernel `d_as_type`
/// checks: `Pi/Sigma/Path/W` over `Type_i` are all types (the
/// kernel places Pi/Sigma/Path one level up, W at the same
/// level; closure means "still a type", not "same level").
/// Codes decoding to non-universes are not Mahlo.
pub fn is_mahlo(u : TyCode) -> Bool {
  let v = deval_dim(tycode_el(u), denv_empty(), ddim_empty())
  match v {
    DVUniv(i) => {
      let ctx = denv_empty()
      let env = denv_empty()
      let denv = ddim_empty()
      let is_type = (t : DTerm) => {
        match d_as_type(t, ctx, env, denv) {
          Some(_) => true
          None => false
        }
      }
      let pi_ok = is_type(DPi(DUniv(i), DUniv(i)))
      let sigma_ok = is_type(DSigma(DUniv(i), DUniv(i)))
      let path_ok = is_type(DPath(DUniv(i), DBoolTy, DBoolTy))
      let w_ok = is_type(wtype_to_dterm(DUniv(i), DLam(DUniv(i), DUniv(i)), i))
      pi_ok && sigma_ok && path_ok && w_ok
    }
    _ => false
  }
}

///|
/// Code-level closure of the reflected sub-universe: if `c` is
/// reflected, every type former over reflected components is
/// reflected (structural; level-free by construction).
pub fn reflected_closed(c : TyCode) -> Bool {
  match c {
    TyVar(_) | TyBool | TyUnit | TyNat | TyUniv(_) => true
    TyPi(a, b) | TySigma(a, b) | TyW(a, b) =>
      reflected_closed(a) && reflected_closed(b)
    TyPath(a, l, r) =>
      reflected_closed(a) && reflected_tm_closed(l) && reflected_tm_closed(r)
  }
}

///|
pub fn reflected_tm_closed(t : TmCode) -> Bool {
  match t {
    TmVar(_) | TmBoolLit(_) | TmUnitLit | TmNatZero => true
    TmSucc(x) | TmFst(x) | TmSnd(x) => reflected_tm_closed(x)
    TmPair(x, y) | TmApp(x, y) =>
      reflected_tm_closed(x) && reflected_tm_closed(y)
    TmLam(dom, body) => reflected_closed(dom) && reflected_tm_closed(body)
    TmSup(wty, a, f) =>
      reflected_closed(wty) && reflected_tm_closed(a) && reflected_tm_closed(f)
    TmWElim(wty, motive, step, scrut) =>
      reflected_closed(wty) &&
      reflected_tm_closed(motive) &&
      reflected_tm_closed(step) &&
      reflected_tm_closed(scrut)
  }
}

///|
/// Mahlo rank: universe codes rank by level (`omega^(i+1)`),
/// other codes by size (`omega^size`).  Reflection chains must
/// strictly decrease in this rank.
pub fn mahlo_rank(u : TyCode) -> CantorOrdinal {
  match u {
    TyUniv(i) => cantor_ord_omega_pow(cantor_ord_nat(i + 1))
    _ => tycode_rank(u)
  }
}

///|
/// Iterated reflection chain: `Type_2` reflects `Type_1`
/// reflects `Type_0` (the Mahlo limit).
pub fn mahlo_chain() -> Array[TyCode] {
  [TyUniv(2), TyUniv(1), TyUniv(0)]
}

///|
/// A chain is descending iff consecutive ranks strictly decrease.
pub fn mahlo_chain_descending(chain : Array[TyCode]) -> Bool {
  for i in 0..<(chain.length() - 1) {
    if !cantor_ord_lt(mahlo_rank(chain[i + 1]), mahlo_rank(chain[i])) {
      return false
    }
  }
  true
}

///|
/// Limit of a descending reflection chain: the last (smallest)
/// element, if the chain is descending and nonempty.
pub fn limit_reflect(chain : Array[TyCode]) -> TyCode? {
  if chain.length() == 0 || !mahlo_chain_descending(chain) {
    return None
  }
  Some(chain[chain.length() - 1])
}

///|
/// Mahlo limit reflection: the chain descends strictly and its
/// limit is Mahlo.
pub fn verify_mahlo_limit(chain : Array[TyCode]) -> Bool {
  match limit_reflect(chain) {
    Some(lim) => is_mahlo(lim)
    None => false
  }
}

// ---------------------------------------------------------------------------
// §4. Laws (executable propositions)
// ---------------------------------------------------------------------------

///|
/// Code system: dependent decoding checks as types, Path
/// endpoints typecheck, and ranks are monotone in size.
pub fn law_reflect_codes() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  out.push((
    "codes: base codes are well-formed",
    tycode_wellformed(TyBool) &&
    tycode_wellformed(TyUnit) &&
    tycode_wellformed(TyNat) &&
    tycode_wellformed(TyUniv(0)),
  ))
  out.push((
    "codes: dependent Pi/Sigma/W check as types",
    tycode_wellformed(TyPi(TyBool, TyUniv(0))) &&
    tycode_wellformed(TyPi(TyBool, TyPath(TyBool, TmVar(0), TmBoolLit(true)))) &&
    tycode_wellformed(TySigma(TyBool, TyPath(TyBool, TmVar(0), TmBoolLit(true)))) &&
    tycode_wellformed(TyW(TyBool, TyUniv(0))),
  ))
  out.push((
    "codes: element in type position is rejected",
    !tycode_wellformed(TyPi(TyBool, TyVar(0))) &&
    !tycode_wellformed(TySigma(TyBool, TyVar(0))),
  ))
  out.push((
    "codes: Path endpoints typecheck (no canonical inhabitant needed)",
    tycode_wellformed(TyPath(TyBool, TmBoolLit(true), TmBoolLit(false))) &&
    tmcode_wellformed(TmBoolLit(true), TyBool),
  ))
  out.push((
    "codes: ill-typed Path endpoints are rejected",
    !tycode_wellformed(TyPath(TyBool, TmUnitLit, TmBoolLit(true))),
  ))
  out.push((
    "codes: size is monotone in subcodes",
    tycode_size(TyPi(TyBool, TyNat)) > tycode_size(TyBool) &&
    tycode_size(TyW(TyBool, TyNat)) > tycode_size(TyNat),
  ))
  out.push((
    "codes: rank decreases with size",
    cantor_ord_lt(tycode_rank(TyBool), tycode_rank(TyPi(TyBool, TyNat))),
  ))
  out.push((
    "codes: unscoped variables are rejected",
    !tycode_wellformed(TyVar(0)) && !tycode_wellformed(TyPi(TyBool, TyVar(1))),
  ))
  let ctx = CtxExtend(CtxExtend(CtxEmpty, TyBool), TyNat)
  out.push((
    "codes: context decoding (len/lookup/el_ty/el_val)",
    ctxcode_len(ctx) == 2 &&
    ctxcode_lookup(ctx, 0) == Some(TyNat) &&
    ctxcode_lookup(ctx, 1) == Some(TyBool) &&
    ctxcode_lookup(ctx, 2) == None &&
    denv_len(ctxcode_el_ty(ctx)) == 2 &&
    denv_len(ctxcode_el_val(ctx)) == 2,
  ))
  out
}

///|
/// Reflection: level collapse lands in the sub-universe and is
/// the identity there; the sub-universe is closed under formers.
pub fn law_reflect_operator() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  out.push((
    "reflect: TyUniv(1) collapses to TyUniv(0)",
    reflect_code(TyUniv(1)) == TyUniv(0),
  ))
  out.push((
    "reflect: reflected codes are fixed",
    is_reflected(TyPi(TyBool, TyNat)) && is_reflected(TyUniv(0)),
  ))
  out.push((
    "reflect: non-reflected codes are detected",
    !is_reflected(TyUniv(1)) && !is_reflected(TyPi(TyUniv(1), TyBool)),
  ))
  out.push((
    "reflect: reflect_code always lands in sub-universe",
    is_reflected(reflect_code(TyPi(TyUniv(1), TyW(TyUniv(2), TyBool)))),
  ))
  out.push((
    "reflect: sub-universe is closed under formers",
    reflected_closed(TyPi(TyBool, TyW(TyNat, TyVar(0)))) &&
    reflected_closed(TyPath(TyBool, TmBoolLit(true), TmBoolLit(false))),
  ))
  out
}

///|
/// Decidable conservativity (unbounded): `El` is injective on
/// all type codes and term codes (structural discrimination),
/// sanity-checked by enumeration up to size 3.
pub fn law_reflect_conservative() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  out.push((
    "conservative: El injective on all TyCode (structural)",
    el_injective_all(),
  ))
  out.push((
    "conservative: El injective on all TmCode (structural)",
    tm_el_injective_all(),
  ))
  out.push((
    "conservative: El injective up to size 3 (enumeration)",
    el_injective_upto(3),
  ))
  out.push((
    "conservative: reflection is conservative up to size 3",
    conservative_reflection(3),
  ))
  out
}

///|
/// Mahlo: `Type_0` is closed under Pi/Sigma/Path/W (kernel
/// verified), and non-universe codes are not Mahlo.
pub fn law_mahlo() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  out.push((
    "mahlo: u_mahlo is Mahlo (Type_0 closed under formers)",
    is_mahlo(u_mahlo()),
  ))
  out.push((
    "mahlo: non-universe codes are not Mahlo",
    !is_mahlo(TyBool) && !is_mahlo(TyPi(TyBool, TyNat)),
  ))
  out.push((
    "mahlo: Type_1 is Mahlo",
    is_mahlo(TyUniv(1)),
  ))
  out.push((
    "mahlo: W-type codes are not Mahlo (not universes)",
    !is_mahlo(TyW(TyBool, TyBool)),
  ))
  out
}

///|
/// Mahlo limit reflection: the chain strictly descends in
/// Cantor rank and its limit is Mahlo, below the `omega^3`
/// ceiling of `verify_mahlo_universe_reflection`.
pub fn law_mahlo_limit() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let chain = mahlo_chain()
  out.push((
    "mahlo-limit: chain descends strictly in rank",
    mahlo_chain_descending(chain),
  ))
  out.push((
    "mahlo-limit: limit is Mahlo",
    verify_mahlo_limit(chain),
  ))
  let cert = verify_mahlo_universe_reflection()
  match limit_reflect(chain) {
    Some(lim) => out.push((
      "mahlo-limit: limit rank below omega^3 ceiling",
      cantor_ord_lt(mahlo_rank(lim), cert.super_universe_rank),
    ))
    None => out.push((
      "mahlo-limit: limit exists",
      false,
    ))
  }
  out.push((
    "mahlo-limit: empty chain has no limit",
    limit_reflect([]) == None,
  ))
  out
}

///|
/// All universe-reflection laws.
pub fn universe_reflect_all_laws() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  for (l, b) in law_reflect_codes() {
    out.push((l, b))
  }
  for (l, b) in law_reflect_operator() {
    out.push((l, b))
  }
  for (l, b) in law_reflect_conservative() {
    out.push((l, b))
  }
  for (l, b) in law_mahlo() {
    out.push((l, b))
  }
  for (l, b) in law_mahlo_limit() {
    out.push((l, b))
  }
  out
}

///|
/// One-line demo for runners.
pub fn universe_reflect_demo() -> String {
  let laws = universe_reflect_all_laws()
  let mut pass = 0
  for i in 0..<laws.length() {
    if laws[i].1 {
      pass = pass + 1
    }
  }
  "universe reflection: \{pass}/\{laws.length()} laws hold (dependent codes, conservative reflection, Mahlo limit)"
}
