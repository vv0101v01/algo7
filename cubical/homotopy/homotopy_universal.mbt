///|
// The missing type formers behind boundaries #6's imported theorems
// (phase 20a): joins, wedges, n-truncations and the James construction,
// declared as genuine cubical HITs with their recursion principles.
//
// Phases 18 and 19 recorded a measured porting cost: Blakers-Massey
// and Brunerie's proof were imported rather than derived, and the
// missing infrastructure was named as
//
//   * joins and the join-wedge connectivity lemma,
//   * n-truncations as a type former with the truncation-recursion
//     principles used in the codes construction,
//   * the James construction and Whitehead products,
//   * `WedgeConnectivity` at general n (only the circle case existed).
//
// This file supplies the *type formers*: each is declared through the
// repository's own `DHitSpec` machinery, so it is a real HIT in the
// same sense `SuspS` and the spheres already are, not a description of
// one.  Their recursion principles are built with `eval_hit_elim` and
// their computation rules are tested.
//
// WHAT IS PROVED HERE (executable, tested by `check_homotopy_universal`).
//   * The join, wedge, truncation and James HITs exist as well-formed
//     specs, with the intended cell arities and face structure.
//   * The join recursion principle, and its three computation rules on
//     `inl`, `inr` and the two endpoints of `push`.
//   * The James recursion principle and its computation rule on `nil`.
//   * The wedge recursion principle on its two point constructors,
//     and the truncation recursion principle on `inc`.
//   * Join associativity-level dimension bookkeeping: `A * B` is
//     `(dim A + dim B + 1)`-dimensional for finite cell complexes,
//     which is the integer content of `S^m * S^n ~= S^(m+n+1)`.
//
// WHAT REMAINS IMPORTED.
//   The connectivity *lemmas* (join-wedge connectivity,
//   `WedgeConnectivity` at general n, the Blakers-Massey codes
//   construction) and the Whitehead product.  Having the type formers
//   is a prerequisite, not a substitute: this file narrows the gap, it
//   does not close it, and the honest statement of what is left is in
//   `homotopy_universal_remaining()`.

// ---------------------------------------------------------------------------
// Join  A * B
// ---------------------------------------------------------------------------

///|
/// The join `A * B`: two point constructors and a path from each `a`
/// to each `b`.
///   inl  : A -> A * B
///   inr  : B -> A * B
///   push : (a : A) (b : B) -> I -> A * B,  push a b 0 = inl a,
///                                          push a b 1 = inr b
pub fn join_schema_at(level : Int32) -> DHitSpec {
  dhit_spec(
    "JoinS",
    level,
    [dtelescope_entry("A", DUniv(level)), dtelescope_entry("B", DUniv(level))],
    [],
    [
      // scope = [B, A];  the value argument has type A = DTVar(1).
      dhit_cell_spec("inl", 0, [darg_external("a", DTVar(1))], []),
      // scope = [B, A];  the value argument has type B = DTVar(0).
      dhit_cell_spec("inr", 0, [darg_external("b", DTVar(0))], []),
      // args [a, b];  scope after both = [b, a, B, A].
      dhit_cell_spec(
        "push",
        1,
        [darg_external("a", DTVar(1)), darg_external("b", DTVar(1))],
        [dhit_face(0, [DTVar(1)], []), dhit_face(1, [DTVar(0)], [])],
      ),
    ],
  )
}

///|
pub fn join_schema() -> DHitSpec {
  join_schema_at(0)
}

///|
pub fn join_type_value(
  a_ty : DValue,
  b_ty : DValue,
  level~ : Int32 = 0,
) -> DValue {
  DVHitType(join_schema_at(level), [a_ty, b_ty], [])
}

///|
pub fn join_inl_value(
  a_ty : DValue,
  b_ty : DValue,
  a : DValue,
  level~ : Int32 = 0,
) -> DValue {
  hit_cell_value(join_schema_at(level), 0, [a_ty, b_ty], [a], [])
}

///|
pub fn join_inr_value(
  a_ty : DValue,
  b_ty : DValue,
  b : DValue,
  level~ : Int32 = 0,
) -> DValue {
  hit_cell_value(join_schema_at(level), 1, [a_ty, b_ty], [b], [])
}

///|
pub fn join_push_value(
  a_ty : DValue,
  b_ty : DValue,
  a : DValue,
  b : DValue,
  dim : Dim,
  level~ : Int32 = 0,
) -> DValue {
  hit_cell_value(join_schema_at(level), 2, [a_ty, b_ty], [a, b], [dim])
}

///|
/// Join recursion: a cocone `(f, g, p)` induces `A * B -> C`, built by
/// the HIT eliminator.
pub fn join_rec_value(
  a_ty : DValue,
  b_ty : DValue,
  c_ty : DValue,
  f : DValue,
  g : DValue,
  p : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let spec = join_schema_at(level)
  DVLam(z => {
    eval_hit_elim(spec, (_, _) => c_ty, [f, g, p], [a_ty, b_ty], [], z, dlevel)
  })
}

// ---------------------------------------------------------------------------
// Wedge  A v B   (pointed)
// ---------------------------------------------------------------------------

///|
/// The wedge sum of two pointed types, given by their basepoints as
/// parameters:
///   winl  : A -> A v B
///   winr  : B -> A v B
///   wglue : I -> A v B,  wglue 0 = winl a0,  wglue 1 = winr b0
pub fn wedge_schema_at(level : Int32) -> DHitSpec {
  dhit_spec(
    "WedgeS",
    level,
    [
      dtelescope_entry("A", DUniv(level)),
      dtelescope_entry("B", DUniv(level)),
      // scope = [B, A];  a0 : A = DTVar(1).
      dtelescope_entry("a0", DTVar(1)),
      // scope = [a0, B, A];  b0 : B = DTVar(1).
      dtelescope_entry("b0", DTVar(1)),
    ],
    [],
    [
      // scope = [b0, a0, B, A];  a : A = DTVar(3).
      dhit_cell_spec("winl", 0, [darg_external("a", DTVar(3))], []),
      // scope = [b0, a0, B, A];  b : B = DTVar(2).
      dhit_cell_spec("winr", 0, [darg_external("b", DTVar(2))], []),
      // no cell arguments;  scope = [b0, a0, B, A].
      dhit_cell_spec("wglue", 1, [], [
        dhit_face(0, [DTVar(1)], []),
        dhit_face(1, [DTVar(0)], []),
      ]),
    ],
  )
}

///|
pub fn wedge_schema() -> DHitSpec {
  wedge_schema_at(0)
}

///|
pub fn wedge_type_value(
  a_ty : DValue,
  b_ty : DValue,
  a0 : DValue,
  b0 : DValue,
  level~ : Int32 = 0,
) -> DValue {
  DVHitType(wedge_schema_at(level), [a_ty, b_ty, a0, b0], [])
}

///|
pub fn wedge_winl_value(
  a_ty : DValue,
  b_ty : DValue,
  a0 : DValue,
  b0 : DValue,
  a : DValue,
  level~ : Int32 = 0,
) -> DValue {
  hit_cell_value(wedge_schema_at(level), 0, [a_ty, b_ty, a0, b0], [a], [])
}

///|
pub fn wedge_winr_value(
  a_ty : DValue,
  b_ty : DValue,
  a0 : DValue,
  b0 : DValue,
  b : DValue,
  level~ : Int32 = 0,
) -> DValue {
  hit_cell_value(wedge_schema_at(level), 1, [a_ty, b_ty, a0, b0], [b], [])
}

///|
/// The wedge's path constructor as a kernel value:
/// `wglue : I -> A v B`, with `wglue 0 = winl a0` and `wglue 1 = winr b0`.
/// Without this accessor the `wglue` cell named by `wedge_schema_at` has no
/// value-level inhabitant, so its endpoints can never be conversion-checked
/// (and `wedge_rec_value`'s third case can never be exercised on a `wglue`).
pub fn wedge_wglue_value(
  a_ty : DValue,
  b_ty : DValue,
  a0 : DValue,
  b0 : DValue,
  dim : Dim,
  level~ : Int32 = 0,
) -> DValue {
  hit_cell_value(wedge_schema_at(level), 2, [a_ty, b_ty, a0, b0], [], [dim])
}

///|
/// Wedge recursion into a type whose two basepoint images are already
/// identified by a path.
pub fn wedge_rec_value(
  a_ty : DValue,
  b_ty : DValue,
  a0 : DValue,
  b0 : DValue,
  c_ty : DValue,
  f : DValue,
  g : DValue,
  q : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let spec = wedge_schema_at(level)
  DVLam(z => {
    eval_hit_elim(
      spec,
      (_, _) => c_ty,
      [f, g, q],
      [a_ty, b_ty, a0, b0],
      [],
      z,
      dlevel,
    )
  })
}

// ---------------------------------------------------------------------------
// n-truncation  ||A||_n
// ---------------------------------------------------------------------------

///|
/// The hub-and-spoke n-truncation `||A||_n` (HoTT §6.7 /
/// Lumsdaine–Shulman), obtained from `set_trunc_schema_at` by replacing the
/// circle with `S^(n+1)`:
///   `inc   (a : A)                   : ||A||_n`
///   `hub   (f : S^(n+1) -> ||A||_n)  : ||A||_n`
///   `spoke (f : S^(n+1) -> ||A||_n, t : S^(n+1)) : f t = hub f`
///
/// `spoke`'s left endpoint names the *bare bound-variable application* `f t`.
/// That is precisely what `dhit_arg_face` exists for (`schema.mbt:509`,
/// "It is what makes constructors like the squash of a propositional
/// truncation expressible: their endpoints are the recursive arguments
/// themselves"), and it is the same device `prop_trunc_schema_at` and
/// `set_trunc_schema_at` already use.  An earlier revision of this file
/// claimed it was inexpressible and discarded the sphere it had just built;
/// both claims were false.
///
/// At `n = 0` the sphere is `sphere_schema(1) = circle_schema()`, so this
/// reproduces `set_trunc_schema_at` cell-for-cell (asserted field-wise in
/// `check_homotopy_universal`).
pub fn trunc_schema_at(n : Int32, level : Int32) -> DHitSpec {
  // The sphere whose maps the hub contracts.  This binding used to be
  // discarded as `_sphere`; it is now the domain of `hub` and `spoke`.
  let sphere = sphere_schema(n + 1)
  let s_ty = DTerm::DHitType(sphere, [])
  dhit_spec(
    "TruncS",
    level,
    [dtelescope_entry("A", DUniv(level))],
    [],
    // scope = [A].  DTVar counts from the innermost binder, so inside
    // `spoke`'s argument scope [A, sphere_map, t]: DTVar(0)=t,
    // DTVar(1)=sphere_map.  Faces are ordered (dim 0 at 0, dim 0 at 1).
    [
      dhit_cell_spec("inc", 0, [darg_external("a", DTVar(0))], []),
      dhit_cell_spec("hub", 0, [darg_function("sphere_map", s_ty)], []),
      dhit_cell_spec(
        "spoke",
        1,
        [darg_function("sphere_map", s_ty), darg_external("t", s_ty)],
        [dhit_arg_face(DApp(DTVar(1), DTVar(0))), dhit_face(1, [DTVar(1)], [])],
      ),
    ],
  )
}

///|
pub fn trunc_schema(n : Int32) -> DHitSpec {
  trunc_schema_at(n, 0)
}

///|
pub fn trunc_type_value(a_ty : DValue, n : Int32, level~ : Int32 = 0) -> DValue {
  DVHitType(trunc_schema_at(n, level), [a_ty], [])
}

///|
pub fn trunc_inc_value(
  a_ty : DValue,
  n : Int32,
  a : DValue,
  level~ : Int32 = 0,
) -> DValue {
  hit_cell_value(trunc_schema_at(n, level), 0, [a_ty], [a], [])
}

///|
/// The `hub` constructor as a kernel value.
pub fn trunc_hub_value(
  a_ty : DValue,
  n : Int32,
  sphere_map : DValue,
  level~ : Int32 = 0,
) -> DValue {
  hit_cell_value(trunc_schema_at(n, level), 1, [a_ty], [sphere_map], [])
}

///|
/// The `spoke` path constructor as a kernel value:
/// `spoke f t : f t = hub f`.
pub fn trunc_spoke_path_value(
  a_ty : DValue,
  n : Int32,
  sphere_map : DValue,
  t : DValue,
  level~ : Int32 = 0,
) -> DValue {
  let spec = trunc_schema_at(n, level)
  DVPathLam(i => hit_cell_value(spec, 2, [a_ty], [sphere_map, t], [i]))
}

///|
/// Truncation recursion in the direction it is used: a map out of `A`,
/// plus the motive's n-type structure.
///
/// All three cases are mandatory.  `eval_hit_elim` guards on
/// `cell_index >= cases.length()` and returns `DVUnit` in that case, so a
/// one-case recursor over this three-cell spec would silently produce a
/// *wrong value with no error* on every `hub` and `spoke`.  A `DArgFunction`
/// argument supplies two binders (the raw argument and its IH) and a
/// `DArgExternal` one, hence the shapes:
///   `f            : A -> C`
///   `hub_branch   : (S^(n+1) -> ||A||_n) -> ((S^(n+1) -> C) -> C)`
///   `spoke_branch : (S^(n+1) -> ||A||_n) -> ((S^(n+1) -> C) -> (t -> Path C (ih t) (hub_branch ..)))`
/// This mirrors `set_trunc_rec_set_value`, which likewise takes the target's
/// set-hood (`is_set_b`) from the caller rather than assuming it.
pub fn trunc_rec_value(
  a_ty : DValue,
  n : Int32,
  c_ty : DValue,
  f : DValue,
  hub_branch : DValue,
  spoke_branch : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let spec = trunc_schema_at(n, level)
  DVLam(z => {
    eval_hit_elim(
      spec,
      (_, _) => c_ty,
      [f, hub_branch, spoke_branch],
      [a_ty],
      [],
      z,
      dlevel,
    )
  })
}

// ---------------------------------------------------------------------------
// James construction  J A   (free monoid)
// ---------------------------------------------------------------------------

///|
/// Brunerie's James construction `J A` on a *pointed* type `(A, a0)`:
///   nil  : J A
///   cons : A -> J A -> J A
///   unit : (x : J A) -> cons a0 x = x
///
/// The basepoint is a schema parameter, exactly as `wedge_schema_at` takes
/// `a0`/`b0`.  `unit`'s right endpoint is the *bare bound variable* `x`,
/// expressed with `dhit_arg_face` — the same device `prop_trunc_schema_at`
/// uses for `squash` and `trunc_schema_at` now uses for `spoke`.  An earlier
/// revision of this file claimed `dhit_face` could not express that and
/// therefore shipped the free monoid instead of `J A`; the claim was false,
/// and without the unit relation `J A` is not the construction Brunerie's
/// argument uses.
pub fn james_schema_at(level : Int32) -> DHitSpec {
  dhit_spec(
    "JamesS",
    level,
    [
      dtelescope_entry("A", DUniv(level)),
      // scope = [A];  a0 : A = DTVar(0).
      dtelescope_entry("a0", DTVar(0)),
    ],
    [],
    [
      dhit_cell_spec("nil", 0, [], []),
      // scope = [a0, A];  the value argument has type A = DTVar(1);
      // the tail is the recursive occurrence.
      dhit_cell_spec(
        "cons",
        0,
        [darg_external("a", DTVar(1)), darg_recursive("x")],
        [],
      ),
      // scope = [x, a0, A]: DTVar(0)=x, DTVar(1)=a0.
      // `cons a0 x = x`: the left endpoint is a cell application, the right
      // endpoint is the bare bound variable.
      dhit_cell_spec("unit", 1, [darg_recursive("x")], [
        dhit_face(1, [DTVar(1), DTVar(0)], []),
        dhit_arg_face(DTVar(0)),
      ]),
    ],
  )
}

///|
pub fn james_schema() -> DHitSpec {
  james_schema_at(0)
}

///|
pub fn james_type_value(
  a_ty : DValue,
  a0 : DValue,
  level~ : Int32 = 0,
) -> DValue {
  DVHitType(james_schema_at(level), [a_ty, a0], [])
}

///|
pub fn james_nil_value(
  a_ty : DValue,
  a0 : DValue,
  level~ : Int32 = 0,
) -> DValue {
  hit_cell_value(james_schema_at(level), 0, [a_ty, a0], [], [])
}

///|
/// The `cons` constructor as a kernel value.  It had no value-level accessor
/// before, so the second cell of this spec could not be inhabited or tested.
pub fn james_cons_value(
  a_ty : DValue,
  a0 : DValue,
  a : DValue,
  x : DValue,
  level~ : Int32 = 0,
) -> DValue {
  hit_cell_value(james_schema_at(level), 1, [a_ty, a0], [a, x], [])
}

///|
/// The unit relation as a kernel value: `unit x : cons a0 x = x`.
pub fn james_unit_path_value(
  a_ty : DValue,
  a0 : DValue,
  x : DValue,
  level~ : Int32 = 0,
) -> DValue {
  let spec = james_schema_at(level)
  DVPathLam(i => hit_cell_value(spec, 2, [a_ty, a0], [x], [i]))
}

///|
/// James recursion is the fold.  `schema_apply_case` applies each case to the
/// *raw* argument first and then, for a recursive argument, to its IH, so the
/// binder counts are fixed by the argument kinds:
///   `nil`          : `e`
///   `cons a x`     : `m a x (rec x)`            — `m` takes 3 binders
///   `unit x`       : `u x (rec x)`              — `u` takes 2 binders,
///                    returning a path `m a0 x (rec x) = rec x` in the target
/// The previous documentation described `m` as `m a (rec x)`; that shape is
/// wrong, and because no test ever exercised the `cons` case the error was
/// invisible.  All three cases are mandatory: `eval_hit_elim` returns `DVUnit`
/// for a cell index past the end of `cases`, so a two-case fold over this
/// three-cell spec would silently produce a wrong value on every `unit`.
pub fn james_rec_value(
  a_ty : DValue,
  a0 : DValue,
  c_ty : DValue,
  e : DValue,
  m : DValue,
  unit_branch : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let spec = james_schema_at(level)
  DVLam(z => {
    eval_hit_elim(
      spec,
      (_, _) => c_ty,
      [e, m, unit_branch],
      [a_ty, a0],
      [],
      z,
      dlevel,
    )
  })
}

// ---------------------------------------------------------------------------
// Dimension bookkeeping
// ---------------------------------------------------------------------------

///|
/// The join of finite cell complexes raises dimension by one past the
/// sum: `dim(A * B) = dim A + dim B + 1`.  For spheres this is
/// `S^m * S^n ~= S^(m+n+1)`.
///
/// Delegates to `join_sphere_dim`, the single implementation of this formula;
/// see the note there for why the implementation sits at layer 7 rather than
/// beside the join HIT at layer 8.
pub fn join_dim(m : Int32, n : Int32) -> Int32 {
  join_sphere_dim(m, n)
}

///|
/// `J(S^n)` has one cell in each dimension `0, n, 2n, 3n, ...`, which
/// is the cell structure Brunerie's James construction argument uses.
pub fn james_cell_dim(k : Int32, n : Int32) -> Int32 {
  k * n
}

// ---------------------------------------------------------------------------
// What is still missing
// ---------------------------------------------------------------------------

///|
/// The imported lemmas that having these type formers does NOT supply.
/// Kept as data so the boundary statement is checkable rather than
/// buried in a comment.
pub fn homotopy_universal_remaining() -> Array[String] {
  [
    "join–wedge 連接度引理：A * B → ΣA ∨ ΣB 的纖維連接度", "一般 n 的 WedgeConnectivity（本庫僅有圓的 wedge_connectivity_circle_*）",
    "Blakers–Massey codes 構造：encode–decode 論證本身", "Whitehead 積的貼附映射構造",
    "Brunerie 定理 4.9 與推論 4.12：π₄(S³) ≃ ℤ/βℤ 的證明",
  ]
}

// ---------------------------------------------------------------------------
// Law
// ---------------------------------------------------------------------------

///|
/// The join, wedge, truncation and James HITs and their recursion
/// principles (phase 20a).  Spec well-formedness and the recursion
/// principles' computation rules are checked here; the connectivity
/// lemmas remain imported and are listed by
/// `homotopy_universal_remaining`.
pub fn check_homotopy_universal() -> Bool {
  // (1) Spec well-formedness: arities and face structure.
  let js = join_schema()
  let ws = wedge_schema()
  let ts = trunc_schema(1)
  let jms = james_schema()
  // The four specs must survive the kernel's own schema validator.  This
  // check used to count cells without ever asking the kernel whether the
  // specs were well-formed, so a malformed face structure would have been
  // invisible here (cf. `truncation.mbt:83`, `sphere3.mbt:127`).
  let spec_ok = hit_schema_validate(js) &&
    hit_schema_validate(ws) &&
    hit_schema_validate(ts) &&
    hit_schema_validate(jms) &&
    js.cells.length() == 3 &&
    js.params.length() == 2 &&
    js.cells[0].dim_count == 0 &&
    js.cells[1].dim_count == 0 &&
    js.cells[2].dim_count == 1 &&
    js.cells[2].args.length() == 2 &&
    js.cells[2].faces.length() == 2 &&
    ws.cells.length() == 3 &&
    ws.params.length() == 4 &&
    ws.cells[2].dim_count == 1 &&
    ws.cells[2].faces.length() == 2 &&
    // n-truncation is hub-and-spoke: inc, hub, spoke.
    ts.cells.length() == 3 &&
    ts.cells[0].dim_count == 0 &&
    ts.cells[0].args.length() == 1 &&
    ts.cells[1].dim_count == 0 &&
    ts.cells[1].args.length() == 1 &&
    ts.cells[2].dim_count == 1 &&
    ts.cells[2].args.length() == 2 &&
    ts.cells[2].faces.length() == 2 &&
    // `spoke`'s left endpoint is the bare-variable application `f t`, i.e. an
    // *argument* face (`cell = -1`), not a cell application; the right
    // endpoint is `hub f`, i.e. cell 1.  This is the structural distinction
    // the previous revision claimed `DHitSpec` could not express.
    ts.cells[2].faces[0].cell == -1 &&
    ts.cells[2].faces[1].cell == 1 &&
    // James is pointed and carries the unit relation `cons a0 x = x`.
    jms.cells.length() == 3 &&
    jms.params.length() == 2 &&
    jms.cells[0].dim_count == 0 &&
    jms.cells[0].args.length() == 0 &&
    jms.cells[1].dim_count == 0 &&
    jms.cells[1].args.length() == 2 &&
    jms.cells[2].dim_count == 1 &&
    jms.cells[2].args.length() == 1 &&
    jms.cells[2].faces.length() == 2 &&
    // left endpoint `cons a0 x` is a cell application (cell 1); right
    // endpoint `x` is an argument face (`cell = -1`).
    jms.cells[2].faces[0].cell == 1 &&
    jms.cells[2].faces[1].cell == -1

  // (1b) At n = 0 the sphere is `sphere_schema(1) = circle_schema()`, so this
  // must reproduce the existing hub-and-spoke set truncation cell-for-cell.
  // The spec *names* differ ("TruncS" vs "SetTruncS"), so compare every other
  // field.  If the two ever diverge, one of them is wrong.
  let t0 = trunc_schema(0)
  let s0 = set_trunc_schema()
  // Names legitimately differ ("TruncS"/"inc"/"sphere_map" vs
  // "SetTruncS"/"point"/"circle_map"), so compare structure: level, params,
  // indices, and per cell the dimension, each argument's kind and type, the
  // faces, the result index and the constraints.
  let kind_tag = (k : DArgKind) => {
    match k {
      DArgExternal => 0
      DArgRecursive => 1
      DArgFunction => 2
      DArgNested => 3
      DArgDecoded => 4
      DArgDecodedFunction => 5
    }
  }
  let cell_shape_eq = (x : DHitCellSpec, y : DHitCellSpec) => {
    if x.dim_count != y.dim_count ||
      x.faces != y.faces ||
      x.result_index != y.result_index ||
      x.constraints != y.constraints ||
      x.args.length() != y.args.length() {
      return false
    }
    for i in 0..<x.args.length() {
      if kind_tag(x.args[i].kind) != kind_tag(y.args[i].kind) ||
        x.args[i].ty != y.args[i].ty {
        return false
      }
    }
    true
  }
  let trunc0_ok = t0.level == s0.level &&
    t0.params == s0.params &&
    t0.indices == s0.indices &&
    t0.cells.length() == s0.cells.length() &&
    {
      let mut ok = true
      for i in 0..<t0.cells.length() {
        if !cell_shape_eq(t0.cells[i], s0.cells[i]) {
          ok = false
        }
      }
      ok
    }

  // (2) Join dimension bookkeeping: S^m * S^n ~= S^(m+n+1).
  let dim_ok = join_dim(1, 1) == 3 &&
    join_dim(0, 1) == 2 &&
    join_dim(2, 2) == 5 &&
    james_cell_dim(0, 3) == 0 &&
    james_cell_dim(1, 3) == 3 &&
    james_cell_dim(2, 3) == 6

  // (3) Join recursion computes on the two point constructors.
  let a_ty = DValue::DVBoolTy
  let b_ty = DValue::DVBoolTy
  let c_ty = DValue::DVBoolTy
  let tt = DValue::DVBool(true)
  let ff = DValue::DVBool(false)
  let f = DValue::DVLam(_ => tt)
  let g = DValue::DVLam(_ => ff)
  let p = DValue::DVLam(_ => DValue::DVLam(_ => dpath_refl_value(tt)))
  let rec = join_rec_value(a_ty, b_ty, c_ty, f, g, p, 16)
  let join_beta = conv_at(
      0,
      0,
      c_ty,
      dapp_typed(
        rec,
        join_inl_value(a_ty, b_ty, tt),
        join_type_value(a_ty, b_ty),
      ),
      tt,
    ) &&
    conv_at(
      0,
      0,
      c_ty,
      dapp_typed(
        rec,
        join_inr_value(a_ty, b_ty, ff),
        join_type_value(a_ty, b_ty),
      ),
      ff,
    ) &&
    conv_at(
      0,
      0,
      join_type_value(a_ty, b_ty),
      join_push_value(a_ty, b_ty, tt, ff, DZero),
      join_inl_value(a_ty, b_ty, tt),
    ) &&
    conv_at(
      0,
      0,
      join_type_value(a_ty, b_ty),
      join_push_value(a_ty, b_ty, tt, ff, DOne),
      join_inr_value(a_ty, b_ty, ff),
    )

  // (4) Wedge recursion computes on the two point constructors.
  let wf = DValue::DVLam(_ => tt)
  let wg = DValue::DVLam(_ => tt)
  let wq = dpath_refl_value(tt)
  let wrec = wedge_rec_value(a_ty, b_ty, tt, tt, c_ty, wf, wg, wq, 16)
  let wedge_beta = conv_at(
      0,
      0,
      c_ty,
      dapp_typed(
        wrec,
        wedge_winl_value(a_ty, b_ty, tt, tt, tt),
        wedge_type_value(a_ty, b_ty, tt, tt),
      ),
      tt,
    ) &&
    conv_at(
      0,
      0,
      c_ty,
      dapp_typed(
        wrec,
        wedge_winr_value(a_ty, b_ty, tt, tt, tt),
        wedge_type_value(a_ty, b_ty, tt, tt),
      ),
      tt,
    ) &&
    // `wglue` really has the declared endpoints: `wglue 0 = winl a0` and
    // `wglue 1 = winr b0`.  These two conversion checks are exactly what
    // `spec.mbt` claims for the wedge's path constructor; before
    // `wedge_wglue_value` existed the cell had no value-level inhabitant,
    // so that claim was unfalsifiable.
    conv_at(
      0,
      0,
      wedge_type_value(a_ty, b_ty, tt, tt),
      wedge_wglue_value(a_ty, b_ty, tt, tt, DZero),
      wedge_winl_value(a_ty, b_ty, tt, tt, tt),
    ) &&
    conv_at(
      0,
      0,
      wedge_type_value(a_ty, b_ty, tt, tt),
      wedge_wglue_value(a_ty, b_ty, tt, tt, DOne),
      wedge_winr_value(a_ty, b_ty, tt, tt, tt),
    )

  // (5) James recursion computes on `nil` and on `cons`.  With a constant `m`
  //     and `Bool` a set, the unit branch is reflexivity.
  let a0 = tt
  let james_ty = james_type_value(a_ty, a0)
  // `e = ff` and `m` constantly `tt` make the two point cases
  // distinguishable, so a swapped or dropped case cannot pass by accident.
  let jm = DValue::DVLam(_ => DValue::DVLam(_ => DValue::DVLam(_ => tt)))
  let jrec = james_rec_value(
    a_ty,
    a0,
    c_ty,
    ff,
    jm,
    DValue::DVLam(_ => DValue::DVLam(_ => dpath_refl_value(tt))),
    16,
  )
  let james_nil_beta = conv_at(
    0,
    0,
    c_ty,
    dapp_typed(jrec, james_nil_value(a_ty, a0), james_ty),
    ff,
  )
  let james_cons_beta = conv_at(
    0,
    0,
    c_ty,
    dapp_typed(
      jrec,
      james_cons_value(a_ty, a0, tt, james_nil_value(a_ty, a0)),
      james_ty,
    ),
    tt,
  )
  // The `unit` case must actually be reached and applied to two binders; a
  // wrong arity would fall through `eval_hit_elim` and yield `DVUnit`.
  let james_unit_beta = conv_at(
    0,
    0,
    c_ty,
    dapp_typed(
      jrec,
      dapp_dim(james_unit_path_value(a_ty, a0, james_nil_value(a_ty, a0)), DZero),
      james_ty,
    ),
    tt,
  )
  let james_beta = james_nil_beta && james_cons_beta && james_unit_beta

  // (5b) `unit x : cons a0 x = x` checked at both endpoints on an OPEN
  //      neutral `x : J A` — falsifiable, unlike a cell count.
  let x_open = reflect_neutral_at_type(DNVar(2), james_ty)
  let unit_open = james_unit_path_value(a_ty, a0, x_open)
  let james_unit_ok = conv_at(
      1,
      0,
      james_ty,
      dapp_dim(unit_open, DZero),
      james_cons_value(a_ty, a0, a0, x_open),
    ) &&
    conv_at(1, 0, james_ty, dapp_dim(unit_open, DOne), x_open)

  // (6) Truncation recursion computes on all three cells.  `Bool` is a set,
  // so the hub branch is constant and the spoke branch is reflexivity.
  let trunc_ty = trunc_type_value(a_ty, 1)
  let hub_branch = DValue::DVLam(_ => DValue::DVLam(_ => tt))
  let spoke_branch =
    DValue::DVLam(_ => DValue::DVLam(_ => DValue::DVLam(_ => dpath_refl_value(tt))))
  let trec = trunc_rec_value(
    a_ty,
    1,
    c_ty,
    // `f` is the identity on Bool, not a constant, so the two `inc` cases
    // below are genuinely distinguishable: a constant `f` would make
    // `rec (inc ff) ≡ ff` false for reasons that have nothing to do with
    // the truncation.
    DValue::DVLam(b => b),
    hub_branch,
    spoke_branch,
    16,
  )
  let const_sphere_map = DValue::DVLam(_ => trunc_inc_value(a_ty, 1, tt))
  let trunc_beta = conv_at(
      0,
      0,
      c_ty,
      dapp_typed(trec, trunc_inc_value(a_ty, 1, tt), trunc_ty),
      tt,
    ) &&
    conv_at(0, 0, c_ty, dapp_typed(trec, trunc_hub_value(a_ty, 1, const_sphere_map), trunc_ty), tt) &&
    conv_at(
      0,
      0,
      DValue::DVBoolTy,
      dapp_typed(trec, trunc_inc_value(a_ty, 1, ff), trunc_ty),
      ff,
    )

  // (6b) `spoke f t : f t = hub f` on OPEN neutrals, the standard this repo
  // sets in `ed25519_k5_merge_laws.mbt:712-726`.  Checking the endpoints at
  // open `f` and `t` is what makes the face structure falsifiable: swapping
  // the two faces in `trunc_schema_at` turns this red, whereas merely
  // counting cells does not.
  let s_ty = DValue::DVHitType(sphere_schema(2), [], [])
  let pi_ty = DValue::DVPi(s_ty, _ => trunc_ty)
  let g_open = reflect_neutral_at_type(DNVar(0), pi_ty)
  let t_open = reflect_neutral_at_type(DNVar(1), s_ty)
  let spoke_open = trunc_spoke_path_value(a_ty, 1, g_open, t_open)
  let trunc_spoke_ok = conv_at(
      1,
      0,
      trunc_ty,
      dapp_dim(spoke_open, DZero),
      dapp_typed(g_open, t_open, s_ty),
    ) &&
    conv_at(1, 0, trunc_ty, dapp_dim(spoke_open, DOne), trunc_hub_value(a_ty, 1, g_open))

  // (7) The remaining imported lemmas are listed, not forgotten.
  let remaining_ok = homotopy_universal_remaining().length() == 5

  spec_ok &&
  trunc0_ok &&
  dim_ok &&
  join_beta &&
  wedge_beta &&
  james_beta &&
  james_unit_ok &&
  trunc_beta &&
  trunc_spoke_ok &&
  remaining_ok
}
