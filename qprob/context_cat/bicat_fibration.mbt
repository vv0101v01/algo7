// ---------------------------------------------------------------------------
// qprob/context_cat/bicat_fibration.mbt
//   Stage VI-A：雙範疇各空間與子場態射、主命題之間態射與 Grothendieck 命題纖維化
// ---------------------------------------------------------------------------
// 數學結構演變（第六階 · 上篇）：
//   前五階（Stage I–V）分別在各自的代數子場與算子空間中證成了 70 條局部演化命題。
//   要將各層空間、子場與其主命題統合為單一範疇論骨架，必須依序建立兩層高階結構：
//
//   1. 【空間與子場雙範疇 `ℬ_qprob`】：
//      - 0-胞（Objects）：子場塔節點（`ℚ`, `ℚ(√d)`, `ℚ((ε))_≤M`）與五階量子空間節點
//        （`lim_← V_k`, `(𝒟, Op*(𝒟), φ)`, `ℱ_q(ℋ)`, `CCR(L²)`, `(𝒜, POVM, κ)`）；
//      - 1-態射（Horizontal 1-Cells）：子場嵌入／Galois 不動投影／標準部商同態、
//        Yosida 預解正則化、二次量子化 `Γ`/`dΓ`、離散格點塗抹嵌入、Born 矩泛函與 Naimark 等距擴張；
//      - 2-態射（Vertical 2-Cells）：兩條平行 1-態射之間的比較變換／收斂逼近元
//        （例如 Galois 平均投影 `1/2(id + σ)`、Richardson 漸近外推收斂、CPTP 通道細化），
//        嚴格滿足雙範疇 **Godement 縱橫互換律（Interchange Law）**：
//        `(β₂ ∘_h α₂) ∘_v (β₁ ∘_h α₁) == (β₂ ∘_v β₁) ∘_h (α₂ ∘_v α₁)`！
//
//   2. 【主命題纖維化 `π : ∫ Prop → ℬ_qprob`（Grothendieck Fibration）】：
//      - 每個基底 0-胞 `X` 上方懸掛其**主命題纖維偏序範疇 `Prop(X)`**，物件為該空間／子場的主命題
//        （攜帶見證不變量 `QVal` 與真值），纖維內態射為同空間內的邏輯蘊含；
//      - 沿基底 1-態射 `f : X → Y` 定義**逆變拉回函子 `f* : Prop(Y) → Prop(X)`**，
//        滿足贗函子律 `(g ∘_h f)* == f* ∘ g*` 與 `(id_X)* == id_{Prop(X)}`；
//      - 主命題之間的全空間態射 `(f, θ) : (X, P) → (Y, Q)` 由基底態射 `f : X → Y` 與纖維演繹見證
//        `θ : P ⊢_X f*(Q)` 組成；當 `P == f*(Q)` 時，`(f, id) : (X, f*Q) → (Y, Q)` 為
//        **笛卡兒提升（Cartesian Lift）**，具備唯一因式分解泛性質！

///|
/// 雙範疇 `ℬ_qprob` 的 0-胞：涵蓋代數子場塔與五階量子概率空間。
#derive(Eq)
pub(all) enum SpaceSubfieldCell0 {
  SubfieldQ
  SubfieldQuad(Int32)
  SubfieldJet(Int32)
  SpaceProjTower(Int32)
  SpaceUnbounded(Int32)
  SpaceFock(Int32, @asymptotic.QVal)
  SpaceContinuumCCR(Int32)
  SpaceNcMeasure(Int32)
}

///|
pub extend SpaceSubfieldCell0 with Eq::{not_equal, equal}

///|
/// 0-胞的可讀數學記號。
pub fn cell0_label(c : SpaceSubfieldCell0) -> String {
  match c {
    SubfieldQ => "ℚ"
    SubfieldQuad(d) => "ℚ(√\{d})"
    SubfieldJet(m) => "ℚ((ε))_≤\{m}"
    SpaceProjTower(r) => "lim_←V(rank=\{r})"
    SpaceUnbounded(d) => "Op*(𝒟_\{d})"
    SpaceFock(d, q) => "ℱ_\{@asymptotic.qv_show(q)}(ℚ^\{d})"
    SpaceContinuumCCR(deg) => "CCR(ℚ[t]_≤\{deg})"
    SpaceNcMeasure(k) => "NCMeas_≤\{k}"
  }
}

///|
/// 雙範疇 `ℬ_qprob` 的 1-態射（空間與子場之間的結構態射，支援嚴格複合路徑）。
pub(all) struct SpaceMorphism1 {
  dom : SpaceSubfieldCell0
  cod : SpaceSubfieldCell0
  steps : Array[String]
  scale_factor : @asymptotic.QVal
  preserves_order_positivity : Bool
}

///|
/// 0-胞上的恆等 1-態射 `id_X : X → X`。
pub fn bicat_id1(obj : SpaceSubfieldCell0) -> SpaceMorphism1 {
  SpaceMorphism1::{
    dom: obj,
    cod: obj,
    steps: [],
    scale_factor: @asymptotic.qv_one(),
    preserves_order_positivity: true,
  }
}

///|
/// 構造原子 1-態射 `f : dom → cod`。
pub fn bicat_atom1(
  dom : SpaceSubfieldCell0,
  cod : SpaceSubfieldCell0,
  tag : String,
  scale_factor : @asymptotic.QVal,
  preserves_order_positivity : Bool,
) -> SpaceMorphism1 {
  guard tag != "" else { abort("bicat_atom1: empty step tag") }
  SpaceMorphism1::{
    dom,
    cod,
    steps: [tag],
    scale_factor,
    preserves_order_positivity,
  }
}

///|
/// 1-態射判等。
pub fn bicat_eq1(f : SpaceMorphism1, g : SpaceMorphism1) -> Bool {
  if f.dom != g.dom ||
    f.cod != g.cod ||
    f.preserves_order_positivity != g.preserves_order_positivity ||
    !@asymptotic.qv_eq(f.scale_factor, g.scale_factor) ||
    f.steps.length() != g.steps.length() {
    return false
  }
  for i in 0..<f.steps.length() {
    if f.steps[i] != g.steps[i] {
      return false
    }
  }
  true
}

///|
/// 1-態射水平複合 `g ∘_h f : X → Z`（當 `f.cod == g.dom` 時有定義，否則回傳 `None`）。
pub fn bicat_comp1(g : SpaceMorphism1, f : SpaceMorphism1) -> SpaceMorphism1? {
  if f.cod != g.dom {
    return None
  }
  let merged : Array[String] = []
  for s in f.steps {
    merged.push(s)
  }
  for s in g.steps {
    merged.push(s)
  }
  Some(SpaceMorphism1::{
    dom: f.dom,
    cod: g.cod,
    steps: merged,
    scale_factor: @asymptotic.qv_mul(g.scale_factor, f.scale_factor),
    preserves_order_positivity: f.preserves_order_positivity &&
    g.preserves_order_positivity,
  })
}

///|
/// 在具體代數子場塔元素上執行子場 1-態射的作用：
/// - `ℚ ↪ ℚ(√d)` 嵌入 `r ↦ r + 0√d`；
/// - `ℚ(√d) → ℚ` 正規化跡投影 `a + b√d ↦ (1/2) Tr(a + b√d) = a`（在 `Fix(σ)=ℚ` 上為恆等左逆！）；
/// - `ℚ ↪ ℚ((ε))_≤M` 常數噴流嵌入與 `st : ℚ[[ε]] → ℚ` 標準部商同態。
pub fn subfield_quad_roundtrip(
  r : @asymptotic.QVal,
  d : Int32,
) -> @asymptotic.QVal {
  let emb = @asymptotic.quad_of_qv(r, d)
  @asymptotic.qv_mul(@asymptotic.qv_frac(1, 2), @asymptotic.quad_trace(emb))
}

///|
pub fn subfield_jet_roundtrip(
  r : @asymptotic.QVal,
  eps_tail : @asymptotic.QVal,
  max_order : Int32,
) -> @asymptotic.QVal? {
  let j = @asymptotic.jet_add(
    @asymptotic.jet_const(r, max_order),
    @asymptotic.jet_monomial(eps_tail, 1, max_order),
  )
  @asymptotic.jet_standard_part(j)
}

///|
/// 雙範疇 `ℬ_qprob` 的 2-態射 `α : src ⇒ tgt`（同源同匯平行 1-態射之間的自然比較／收斂變換）。
/// `defect` 度量兩條平行態射的漸近偏差或相對權重（加法群結構），複合縮放由底層 1-態射的 `scale_factor` 雙線性誘導：
/// - 垂直複合 `(β ∘_v α).defect = α.defect + β.defect`；
/// - 水平複合 `(β ∘_h α).defect = β.tgt.scale_factor · α.defect + β.defect · α.src.scale_factor`
///   （這恰是嚴格 2-範疇／雙範疇 Whiskering `g ◁ α` 與 `β ▷ f` 誘導的標準水平複合，只要平行 1-態射同調縮放，
///   即嚴格滿足 Godement 縱橫互換律！）。
pub(all) struct SpaceCell2 {
  src : SpaceMorphism1
  tgt : SpaceMorphism1
  defect : @asymptotic.QVal
  witness_tag : String
}

///|
/// 構造合法 2-態射 `α : src ⇒ tgt`（要求 `src` 與 `tgt` 平行：`dom` 與 `cod` 相同，且縮放率相容）。
pub fn bicat_make2(
  src : SpaceMorphism1,
  tgt : SpaceMorphism1,
  defect : @asymptotic.QVal,
  witness_tag : String,
) -> SpaceCell2? {
  if src.dom != tgt.dom ||
    src.cod != tgt.cod ||
    !@asymptotic.qv_eq(src.scale_factor, tgt.scale_factor) {
    return None
  }
  Some(SpaceCell2::{ src, tgt, defect, witness_tag, })
}

///|
/// 1-態射 `f` 上的恆等 2-態射 `id_f : f ⇒ f`。
pub fn bicat_id2(f : SpaceMorphism1) -> SpaceCell2 {
  SpaceCell2::{
    src: f,
    tgt: f,
    defect: @asymptotic.qv_zero(),
    witness_tag: "id2",
  }
}

///|
/// 2-態射判等（比較源／目標 1-態射與精確偏差不變量 `defect`）。
pub fn bicat_eq2(a : SpaceCell2, b : SpaceCell2) -> Bool {
  bicat_eq1(a.src, b.src) &&
  bicat_eq1(a.tgt, b.tgt) &&
  @asymptotic.qv_eq(a.defect, b.defect)
}

///|
/// 2-態射垂直複合 `β ∘_v α : f₁ ⇒ f₃`（要求 `α.tgt == β.src`）。
pub fn bicat_vcomp2(beta : SpaceCell2, alpha : SpaceCell2) -> SpaceCell2? {
  if !bicat_eq1(alpha.tgt, beta.src) {
    return None
  }
  Some(SpaceCell2::{
    src: alpha.src,
    tgt: beta.tgt,
    defect: @asymptotic.qv_add(alpha.defect, beta.defect),
    witness_tag: "\{beta.witness_tag}∘_v\{alpha.witness_tag}",
  })
}

///|
/// 2-態射水平複合 `β ∘_h α : (g₁ ∘_h f₁) ⇒ (g₂ ∘_h f₂)`（要求 `α.src.cod == β.src.dom`）。
pub fn bicat_hcomp2(beta : SpaceCell2, alpha : SpaceCell2) -> SpaceCell2? {
  guard bicat_comp1(beta.src, alpha.src) is Some(comp_src) else { return None }
  guard bicat_comp1(beta.tgt, alpha.tgt) is Some(comp_tgt) else { return None }
  let left_whisker = @asymptotic.qv_mul(beta.tgt.scale_factor, alpha.defect)
  let right_whisker = @asymptotic.qv_mul(beta.defect, alpha.src.scale_factor)
  Some(SpaceCell2::{
    src: comp_src,
    tgt: comp_tgt,
    defect: @asymptotic.qv_add(left_whisker, right_whisker),
    witness_tag: "(\{beta.witness_tag}*\{alpha.witness_tag})",
  })
}

///|
/// 檢驗雙範疇四角形 `(α₁, α₂)` 與 `(β₁, β₂)` 的 **Godement 縱橫互換律（Interchange Law）**：
/// `(β₂ ∘_h α₂) ∘_v (β₁ ∘_h α₁) == (β₂ ∘_v β₁) ∘_h (α₂ ∘_v α₁)`。
pub fn bicat_check_interchange(
  beta2 : SpaceCell2,
  beta1 : SpaceCell2,
  alpha2 : SpaceCell2,
  alpha1 : SpaceCell2,
) -> Bool {
  guard bicat_hcomp2(beta1, alpha1) is Some(h1) else { return false }
  guard bicat_hcomp2(beta2, alpha2) is Some(h2) else { return false }
  guard bicat_vcomp2(h2, h1) is Some(lhs) else { return false }
  guard bicat_vcomp2(beta2, beta1) is Some(vb) else { return false }
  guard bicat_vcomp2(alpha2, alpha1) is Some(va) else { return false }
  guard bicat_hcomp2(vb, va) is Some(rhs) else { return false }
  bicat_eq2(lhs, rhs)
}

// ---------------------------------------------------------------------------
// Grothendieck 主命題纖維化 π : ∫ Prop → ℬ_qprob 與主命題間態射
// ---------------------------------------------------------------------------

///|
/// 懸掛在基底空間／子場 `base` 上方的主命題物件 `(X, P)`：
/// - `prop_code`：主命題家族識別碼（跨層拉回時保持語意血統）；
/// - `invariant`：該空間上當場重算出的主命題特徵不變量（例如 Galois 範數、飽和下界、Catalan 矩、`L²` 對易子、自由累積量）；
/// - `strength_rank`：同一纖維內的邏輯強度階層（供纖維內演繹偏序 `P ⊢_X Q` 判定）；
/// - `holds`：主命題在該空間／子場上的實算真值。
pub(all) struct FiberPrincipalProp {
  base : SpaceSubfieldCell0
  prop_code : String
  statement : String
  invariant : @asymptotic.QVal
  strength_rank : Int32
  holds : Bool
}

///|
pub fn fiber_prop_eq(p : FiberPrincipalProp, q : FiberPrincipalProp) -> Bool {
  p.base == q.base &&
  p.prop_code == q.prop_code &&
  @asymptotic.qv_eq(p.invariant, q.invariant) &&
  p.strength_rank == q.strength_rank &&
  p.holds == q.holds
}

///|
/// 同一基底空間 `X` 內的垂直蘊含判定 `P ⊢_X Q`：
/// 要求同基底、同主命題血統（或強命題蘊含弱命題 `p.strength_rank >= q.strength_rank`）、
/// 見證不變量相容，且 Heyting 真值滿足 `p.holds ⇒ q.holds`（不可由真推出假！）。
pub fn fiber_entails_in_base(
  p : FiberPrincipalProp,
  q : FiberPrincipalProp,
) -> Bool {
  if p.base != q.base {
    return false
  }
  if p.holds && !q.holds {
    return false
  }
  p.prop_code == q.prop_code &&
  p.strength_rank >= q.strength_rank &&
  @asymptotic.qv_eq(p.invariant, q.invariant)
}

///|
/// 沿基底 1-態射 `f : X → Y` 的**逆變拉回函子 `f* : Prop(Y) → Prop(X)`**（Substitution / Reindexing）：
/// 將目標空間 `Y` 上的主命題 `Q` 沿 `f` 拉回至源空間 `X` 上的誘導主命題 `f*(Q)`。
/// 若 `f` 不保序／不保正定（`!f.preserves_order_positivity`），正定性主命題拉回後失真（`holds = false`）。
pub fn pullback_principal_prop(
  f : SpaceMorphism1,
  q_cod : FiberPrincipalProp,
) -> FiberPrincipalProp? {
  if f.cod != q_cod.base {
    return None
  }
  let pulled_inv = @asymptotic.qv_mul(f.scale_factor, q_cod.invariant)
  let pulled_holds = if f.preserves_order_positivity {
    q_cod.holds
  } else {
    false
  }
  let stmt = if f.steps.length() == 0 {
    q_cod.statement
  } else {
    let path_str = f.steps.join("∘")
    "(\{path_str})*[\{q_cod.statement}]"
  }
  Some(FiberPrincipalProp::{
    base: f.dom,
    prop_code: q_cod.prop_code,
    statement: stmt,
    invariant: pulled_inv,
    strength_rank: q_cod.strength_rank,
    holds: pulled_holds,
  })
}

///|
/// 總範疇 `∫ Prop` 中**主命題之間的態射** `(f, θ) : (X, P) → (Y, Q)`：
/// 覆蓋基底空間／子場態射 `f : X → Y`，並攜帶纖維內蘊含見證 `P ⊢_X f*(Q)`。
pub(all) struct PrincipalPropMorphism {
  src : FiberPrincipalProp
  tgt : FiberPrincipalProp
  base_map : SpaceMorphism1
  is_cartesian : Bool
}

///|
/// 構造並驗證主命題態射 `(X, P) → (Y, Q)`（僅當 `f : X → Y` 且 `P ⊢_X f*(Q)` 成立時回傳 `Some`）。
pub fn make_prop_morphism(
  src : FiberPrincipalProp,
  tgt : FiberPrincipalProp,
  base_map : SpaceMorphism1,
) -> PrincipalPropMorphism? {
  if src.base != base_map.dom || tgt.base != base_map.cod {
    return None
  }
  guard pullback_principal_prop(base_map, tgt) is Some(pulled) else {
    return None
  }
  if !fiber_entails_in_base(src, pulled) {
    return None
  }
  let cart = fiber_prop_eq(src, pulled)
  Some(PrincipalPropMorphism::{ src, tgt, base_map, is_cartesian: cart, })
}

///|
/// 主命題全空間上的恆等態射 `id_{(X,P)} : (X, P) → (X, P)`。
pub fn prop_morphism_id(p : FiberPrincipalProp) -> PrincipalPropMorphism {
  PrincipalPropMorphism::{
    src: p,
    tgt: p,
    base_map: bicat_id1(p.base),
    is_cartesian: true,
  }
}

///|
/// 主命題態射複合 `(g, φ) ∘ (f, θ) : (X, P) → (Z, R)`；
/// 笛卡兒態射在複合下封閉（Grothendieck 纖維化基本引理）。
pub fn prop_morphism_comp(
  second : PrincipalPropMorphism,
  first : PrincipalPropMorphism,
) -> PrincipalPropMorphism? {
  if !fiber_prop_eq(first.tgt, second.src) {
    return None
  }
  guard bicat_comp1(second.base_map, first.base_map) is Some(comp_base) else {
    return None
  }
  make_prop_morphism(first.src, second.tgt, comp_base)
}

///|
/// 構造沿 `f : X → Y` 對目標主命題 `Q ∈ Prop(Y)` 的**笛卡兒提升態射**
/// `Cart(f, Q) : (X, f*Q) → (Y, Q)`。
pub fn cartesian_lift_morphism(
  f : SpaceMorphism1,
  q_cod : FiberPrincipalProp,
) -> PrincipalPropMorphism? {
  guard pullback_principal_prop(f, q_cod) is Some(src_pulled) else {
    return None
  }
  make_prop_morphism(src_pulled, q_cod, f)
}

///|
/// **Grothendieck 笛卡兒提升泛性質演算法**：
/// 給定笛卡兒態射 `cart : (Y, f*R) → (Z, R)`（覆蓋 `f : Y → Z`）以及任意態射
/// `h_tot : (X, P) → (Z, R)`，若基底態射分解為 `h_tot.base_map == f ∘_h u`（`u : X → Y`），
/// 則必存在**唯一**中繼主命題態射 `u_bar : (X, P) → (Y, f*R)` 覆蓋 `u`，使得 `cart ∘ u_bar == h_tot`！
pub fn factor_through_cartesian_lift(
  h_tot : PrincipalPropMorphism,
  u : SpaceMorphism1,
  cart : PrincipalPropMorphism,
) -> PrincipalPropMorphism? {
  if !cart.is_cartesian || !fiber_prop_eq(h_tot.tgt, cart.tgt) {
    return None
  }
  guard bicat_comp1(cart.base_map, u) is Some(expected_base) else {
    return None
  }
  if !bicat_eq1(expected_base, h_tot.base_map) {
    return None
  }
  make_prop_morphism(h_tot.src, cart.src, u)
}

///|
/// 由 Stage I–V 真實算子與子場運算當場重算並建立 **8 個核心空間／子場節點的錨定主命題切面**！
pub fn canonical_principal_prop_section() -> Array[FiberPrincipalProp] {
  // 1. ℚ：有序基子場乘法逆元恆等 (2/3)·(3/2) = 1
  let q_inv_inv = @asymptotic.qv_mul(
    @asymptotic.qv_frac(2, 3),
    @asymptotic.qv_frac(3, 2),
  )
  let p_q = FiberPrincipalProp::{
    base: SubfieldQ,
    prop_code: "subfield-unit",
    statement: "ℚ 乘法單位與逆元不變量 1",
    invariant: q_inv_inv,
    strength_rank: 2,
    holds: @asymptotic.qv_eq(q_inv_inv, @asymptotic.qv_one()),
  }

  // 2. ℚ(√2)：Galois 佩爾單位 N(3 + 2√2) = 9 - 8 = 1
  let pell = @asymptotic.quad_make(
    @asymptotic.qv_int(3),
    @asymptotic.qv_int(2),
    2,
  )
  let pell_norm = @asymptotic.quad_norm(pell)
  let p_quad = FiberPrincipalProp::{
    base: SubfieldQuad(2),
    prop_code: "subfield-unit",
    statement: "ℚ(√2) Galois 範數 N(3+2√2) = 1",
    invariant: pell_norm,
    strength_rank: 2,
    holds: @asymptotic.qv_eq(pell_norm, @asymptotic.qv_one()),
  }

  // 3. ℚ((ε))_≤4：漸近噴流 (1 + 3ε)(1 + 3ε)⁻¹ 標準部 st = 1
  let j_unit = @asymptotic.jet_add(
    @asymptotic.jet_const(@asymptotic.qv_one(), 4),
    @asymptotic.jet_monomial(@asymptotic.qv_int(3), 1, 4),
  )
  let j_st = match @asymptotic.jet_inv(j_unit) {
    Some(inv_j) =>
      match @asymptotic.jet_standard_part(@asymptotic.jet_mul(j_unit, inv_j)) {
        Some(st) => st
        None => @asymptotic.qv_zero()
      }
    None => @asymptotic.qv_zero()
  }
  let p_jet = FiberPrincipalProp::{
    base: SubfieldJet(4),
    prop_code: "subfield-unit",
    statement: "ℚ((ε))_≤4 標準部商同態 st(u·u⁻¹) = 1",
    invariant: j_st,
    strength_rank: 2,
    holds: @asymptotic.qv_eq(j_st, @asymptotic.qv_one()),
  }

  // 4. lim_← V_k：Richardson 外推極限 (2N+1)/N → 2
  let rich_lim = match
    @asymptotic.richardson_extrapolate_limit([2, 4], [
      @asymptotic.qv_frac(5, 2),
      @asymptotic.qv_frac(9, 4),
    ]) {
    Some(v) => v
    None => @asymptotic.qv_zero()
  }
  let p_tower = FiberPrincipalProp::{
    base: SpaceProjTower(2),
    prop_code: "quantum-moment-4",
    statement: "射影極限 Richardson 外推無窮極限 = 2",
    invariant: rich_lim,
    strength_rank: 2,
    holds: @asymptotic.qv_eq(rich_lim, @asymptotic.qv_int(2)),
  }

  // 5. Op*(𝒟_4)：Robertson–Schrödinger 真空基態飽和 4·Var(Q)·Var(P) = 1，對齊二粒子對易能階 2
  let d = 4
  let sub = [@asymptotic.qv_one(), @asymptotic.qv_int(2), @asymptotic.qv_int(3)]
  let q_op = @unbounded.uop_jacobi_tridiag(
    Array::make(d, @asymptotic.qv_zero()),
    sub,
  )
  let p_op = @unbounded.uop_dual_momentum_tridiag(sub, d)
  let vac_amp = [
    @unbounded.qc_one(),
    @unbounded.qc_zero(),
    @unbounded.qc_zero(),
    @unbounded.qc_zero(),
  ]
  let ub_inv = match @unbounded.qstate_pure(vac_amp) {
    Some(st0) => {
      let ub = @unbounded.check_robertson_schrodinger(st0, q_op, p_op)
      if ub.holds && @asymptotic.qv_eq(ub.lhs_prod, ub.rhs_total) {
        @asymptotic.qv_mul(@asymptotic.qv_int(2), ub.lhs_prod)
      } else {
        @asymptotic.qv_zero()
      }
    }
    None => @asymptotic.qv_zero()
  }
  let p_unb = FiberPrincipalProp::{
    base: SpaceUnbounded(d),
    prop_code: "quantum-moment-4",
    statement: "Op*(𝒟_4) 真空基態 Robertson–Schrödinger 飽和 2·Var(Q)Var(P) = 2",
    invariant: ub_inv,
    strength_rank: 2,
    holds: @asymptotic.qv_eq(ub_inv, @asymptotic.qv_int(2)),
  }

  // 6. ℱ_0(ℚ¹)：全福克場算子 X = ℓ* + ℓ 的四階 Catalan 矩 m_4 = C_2 = 2
  let z0 = @asymptotic.qv_zero()
  let z1 = @asymptotic.qv_one()
  let vac = @fock.fock_vacuum(1)
  let mut cur = vac
  for _ in 0..<4 {
    cur = @fock.fock_add(
      @fock.fock_create_left([z1], cur),
      @fock.fock_annihilate_q(z0, [z1], cur),
    )
  }
  let m4_free = @fock.fock_inner_q(z0, vac, cur)
  let p_fock = FiberPrincipalProp::{
    base: SpaceFock(1, z0),
    prop_code: "quantum-moment-4",
    statement: "ℱ_0(ℚ¹) 半圓場四階真空矩 ⟨Ω,(ℓ*+ℓ)⁴Ω⟩ = C₂ = 2",
    invariant: m4_free,
    strength_rank: 2,
    holds: @asymptotic.qv_eq(m4_free, @asymptotic.qv_int(2)),
  }

  // 7. CCR(ℚ[t])：連續玻色場雙模塗抹對易能量 ⟨√2·1, √2·1⟩ = ∫_0^1 2 dt = 2
  let wave = @ccr_field.ContinuumTestFn::{
    t_start: z0,
    t_end: z1,
    coeffs: [@asymptotic.qv_int(2)],
  }
  let unit_wave = @ccr_field.ContinuumTestFn::{
    t_start: z0,
    t_end: z1,
    coeffs: [z1],
  }
  let ccr_comm = @ccr_field.continuum_l2_inner(unit_wave, wave)
  let p_ccr = FiberPrincipalProp::{
    base: SpaceContinuumCCR(0),
    prop_code: "quantum-moment-4",
    statement: "CCR(L²[0,1]) 連續創生湮滅對易子 [A(1), A†(2)] = 2",
    invariant: ccr_comm,
    strength_rank: 2,
    holds: @asymptotic.qv_eq(ccr_comm, @asymptotic.qv_int(2)),
  }

  // 8. NCMeas_≤4：半圓律四階矩 m_4 = 2（自由累積量 κ_2 = 1, κ_4 = 0）
  let semi_m = @nc_measure.free_cumulants_to_moments([z0, z1, z0, z0])
  let p_nc = FiberPrincipalProp::{
    base: SpaceNcMeasure(4),
    prop_code: "quantum-moment-4",
    statement: "NCMeas_≤4 半圓律非交叉四階矩 m₄ = 2 (κ₄ = 0)",
    invariant: semi_m[4],
    strength_rank: 2,
    holds: @asymptotic.qv_eq(semi_m[4], @asymptotic.qv_int(2)),
  }

  [p_q, p_quad, p_jet, p_tower, p_unb, p_fock, p_ccr, p_nc]
}
