// ---------------------------------------------------------------------------
// qprob/ccr_field/continuum_field.mbt — 連續創生與湮滅算子場、Wick 正規序與量子隨機微積分
// ---------------------------------------------------------------------------
// 數學結構演變（第四階）：
//   在第三階，單粒子空間 `ℋ` 為有限維離散模態。當我們將單粒子空間提升為連續區間 `[0, T]` 上的
//   平方可積測試函數空間 `L²([0, T], dt)` 時：
//     1. 逐點算子值分佈 `[a(s), a†(t)] = δ(s − t)` 在一點 `s = t` 發散（不是真正的希爾伯特算子），
//        必須經過測試函數塗抹（Smearing）成為算子場泛函：
//          `A(g) = ∫_0^T g(t) a(t) dt`，`A†(f) = ∫_0^T f(t) a†(t) dt`，
//        此時對易子收斂為精確連續 `L²` 內積：`[A(g), A†(f)] = ∫_0^T g(t) f(t) dt · I`！
//     2. 將連續區間等分為 `N` 個步長 `Δt = T/N` 的格點離散場 `[a_j, a†_k] = δ_{jk}`，
//        取無窮細分漸近極限 `N → ∞`（直接調用第一階的 Richardson 外推器！），
//        離散 Riemann 場對易子零誤差收斂至精確連續積分內積！
//     3. 在算子場代數中，非正規序乘積的真空期望值由 **Wick 正規序展開演算法** 化約為真空對縮併和；
//     4. 對指數相干態／Weyl 位移算子 `W(f) = exp(A†(f) − A(f))`，導出 **BCH–Weyl 辛對易律**：
//          `W(f) W(g) = exp(−(i/2) Im⟨f, g⟩) W(f + g)`；
//     5. 進一步令測試函數取指示函數 `1_{[0, t]}`，即湧現 **Hudson–Parthasarathy 量子隨機過程**
//        `(A_t, A†_t, Λ_t)` 與量子 Itô 乘法表：`dA_t · dA†_t = dt`（其餘二階微元乘積除 `dΛ` 耦合外為 0）！

///|
/// 連續區間 `[a, b]` 上的精確多項式測試函數 `f(t) = Σ_{k=0}^m coeffs[k] t^k ∈ ℚ[t]`。
/// 多項式在 `L²([a, b], dt)` 中稠密，且一切連續積分內積皆為精確有理數，零數值求積誤差！
pub(all) struct ContinuumTestFn {
  t_start : @asymptotic.QVal
  t_end : @asymptotic.QVal
  coeffs : Array[@asymptotic.QVal]
}

///|
pub fn test_fn_eval(
  f : ContinuumTestFn,
  t : @asymptotic.QVal,
) -> @asymptotic.QVal {
  let mut acc = @asymptotic.qv_zero()
  let mut i = f.coeffs.length() - 1
  while i >= 0 {
    acc = @asymptotic.qv_add(@asymptotic.qv_mul(acc, t), f.coeffs[i])
    i = i - 1
  }
  acc
}

///|
fn assert_same_interval(f : ContinuumTestFn, g : ContinuumTestFn) -> Unit {
  guard @asymptotic.qv_eq(f.t_start, g.t_start) &&
    @asymptotic.qv_eq(f.t_end, g.t_end) else {
    abort("ContinuumTestFn: interval mismatch")
  }
}

///|
pub fn test_fn_add(f : ContinuumTestFn, g : ContinuumTestFn) -> ContinuumTestFn {
  assert_same_interval(f, g)
  let len = if f.coeffs.length() > g.coeffs.length() {
    f.coeffs.length()
  } else {
    g.coeffs.length()
  }
  let cs = Array::make(len, @asymptotic.qv_zero())
  for i in 0..<len {
    let a = if i < f.coeffs.length() {
      f.coeffs[i]
    } else {
      @asymptotic.qv_zero()
    }
    let b = if i < g.coeffs.length() {
      g.coeffs[i]
    } else {
      @asymptotic.qv_zero()
    }
    cs[i] = @asymptotic.qv_add(a, b)
  }
  ContinuumTestFn::{ t_start: f.t_start, t_end: f.t_end, coeffs: cs, }
}

///|
pub fn test_fn_scale(
  c : @asymptotic.QVal,
  f : ContinuumTestFn,
) -> ContinuumTestFn {
  ContinuumTestFn::{
    t_start: f.t_start,
    t_end: f.t_end,
    coeffs: [
      for x in f.coeffs => @asymptotic.qv_mul(c, x)
    ],
  }
}

///|
/// 精確連續積分 `∫_{t_start}^{t_end} p(t) dt`（由原函數 `Σ c_k / (k+1) · (b^{k+1} − a^{k+1})` 精確計算）。
pub fn poly_definite_integral(
  coeffs : Array[@asymptotic.QVal],
  a : @asymptotic.QVal,
  b : @asymptotic.QVal,
) -> @asymptotic.QVal {
  let mut sum = @asymptotic.qv_zero()
  for k in 0..<coeffs.length() {
    if !@asymptotic.qv_is_zero(coeffs[k]) {
      let deg1 = k + 1
      let diff = @asymptotic.qv_sub(
        @asymptotic.qv_pow(b, deg1),
        @asymptotic.qv_pow(a, deg1),
      )
      let term = @asymptotic.qv_div(
        @asymptotic.qv_mul(coeffs[k], diff),
        @asymptotic.qv_int(deg1),
      )
      sum = @asymptotic.qv_add(sum, term)
    }
  }
  sum
}

///|
/// 連續 `L²([a, b], dt)` 內積 `⟨g, f⟩_{L²} = ∫_a^b g(t) f(t) dt = [A(g), A†(f)]`。
pub fn continuum_l2_inner(
  g : ContinuumTestFn,
  f : ContinuumTestFn,
) -> @asymptotic.QVal {
  assert_same_interval(g, f)
  if g.coeffs.length() == 0 || f.coeffs.length() == 0 {
    return @asymptotic.qv_zero()
  }
  let prod_len = g.coeffs.length() + f.coeffs.length() - 1
  let prod = Array::make(prod_len, @asymptotic.qv_zero())
  for i in 0..<g.coeffs.length() {
    for j in 0..<f.coeffs.length() {
      prod[i + j] = @asymptotic.qv_add(
        prod[i + j],
        @asymptotic.qv_mul(g.coeffs[i], f.coeffs[j]),
      )
    }
  }
  poly_definite_integral(prod, g.t_start, g.t_end)
}

///|
/// 將連續區間等分為 `N` 個離散格點，構造塗抹波包 `f` 在全量子福克空間單粒子扇區 `ℚ^N` 的離散向量
/// `v_k = f(t_k) · Δt`（配合單位權重對偶基底 `u_k = g(t_k)`），透過 `@fock` 的玻色對易關係
/// `[ℓ_1(u), ℓ*_1(v)]|Ω⟩` 實算離散場對易子！
pub fn fock_lattice_bosonic_commutator(
  g : ContinuumTestFn,
  f : ContinuumTestFn,
  n_sites : Int32,
) -> @asymptotic.QVal {
  assert_same_interval(g, f)
  if n_sites <= 0 {
    return @asymptotic.qv_zero()
  }
  let span = @asymptotic.qv_sub(g.t_end, g.t_start)
  let dt = @asymptotic.qv_div(span, @asymptotic.qv_int(n_sites))
  let u_vec : Array[@asymptotic.QVal] = []
  let v_vec : Array[@asymptotic.QVal] = []
  for k in 0..<n_sites {
    let tk = @asymptotic.qv_add(
      g.t_start,
      @asymptotic.qv_mul(@asymptotic.qv_int(k), dt),
    )
    u_vec.push(test_fn_eval(g, tk))
    v_vec.push(@asymptotic.qv_mul(test_fn_eval(f, tk), dt))
  }
  let vac = @fock.fock_vacuum(n_sites)
  let q1 = @asymptotic.qv_one()
  let acted = @fock.fock_annihilate_q(
    q1,
    u_vec,
    @fock.fock_create_left(v_vec, vac),
  )
  @fock.fock_inner_q(q1, vac, acted)
}

// ---------------------------------------------------------------------------
// 演算法 4.A：連續算子場的 Wick 正規序展開器（Normal-Ordering Engine）
// ---------------------------------------------------------------------------
// 算子場字母：`FieldFactor` 為 `Create(f)`（即 `A†(f)`）或 `Annihilate(g)`（即 `A(g)`）。
// 正規序項 `WickTerm`：所有創生算子居左 `A†(f_1)...A†(f_p)`、所有湮滅算子居右 `A(g_1)...A(g_q)`，
// 乘上標量係數 `coeff`（來自連續對易縮併 `⟨g, f⟩_{L²}`）。
// 定理：任何正規序項若含至少一個湮滅算子（`q > 0`）或至少一個創生算子（`p > 0`），
// 夾在真空態 `⟨Ω | : ⋯ : | Ω⟩` 中必恆等於 0！因此真空期望值**精確等於純常數項（`p = q = 0`）係數**！

///|
pub(all) enum FieldFactor {
  Create(ContinuumTestFn)
  Annihilate(ContinuumTestFn)
}

///|
pub(all) struct WickNormalTerm {
  coeff : @asymptotic.QVal
  creators : Array[ContinuumTestFn]
  annihilators : Array[ContinuumTestFn]
}

///|
/// 將單個場算子左乘入一個已正規序項：
/// - 若左乘 `A†(f)`：直接置於最左端，仍保持正規序！
/// - 若左乘 `A(g)` 於 `A†(f_0) ... A†(f_{p-1}) A(h_0)...`：
///   利用 Leibniz 導子恆等式 `[A(g), A†(f_0)...A†(f_{p-1})] = Σ_{r=0}^{p-1} ⟨g, f_r⟩ A†(f_0)...Â†(f_r)...A†(f_{p-1})`，
///   拆分為 1 個純正規序項 + `p` 個縮併降階正規序項！
fn wick_prepend_factor(
  fac : FieldFactor,
  term : WickNormalTerm,
) -> Array[WickNormalTerm] {
  match fac {
    Create(f) => {
      let nc : Array[ContinuumTestFn] = [f]
      for x in term.creators {
        nc.push(x)
      }
      [
        WickNormalTerm::{
          coeff: term.coeff,
          creators: nc,
          annihilators: term.annihilators,
        },
      ]
    }
    Annihilate(g) => {
      let out : Array[WickNormalTerm] = []
      // 1. 穿過全部創生算子到達右側湮滅區
      let na : Array[ContinuumTestFn] = [g]
      for y in term.annihilators {
        na.push(y)
      }
      out.push(WickNormalTerm::{
        coeff: term.coeff,
        creators: term.creators,
        annihilators: na,
      })
      // 2. 與第 r 個創生算子縮併 ⟨g, f_r⟩_{L²}
      let p = term.creators.length()
      for r in 0..<p {
        let contraction = continuum_l2_inner(g, term.creators[r])
        if !@asymptotic.qv_is_zero(contraction) {
          let rem_c : Array[ContinuumTestFn] = []
          for idx in 0..<p {
            if idx != r {
              rem_c.push(term.creators[idx])
            }
          }
          out.push(WickNormalTerm::{
            coeff: @asymptotic.qv_mul(term.coeff, contraction),
            creators: rem_c,
            annihilators: term.annihilators,
          })
        }
      }
      out
    }
  }
}

///|
/// 演算法 4.A：將任意連續創生／湮滅場乘積串列完全展開為 Wick 正規序和！
pub fn wick_normal_order(factors : Array[FieldFactor]) -> Array[WickNormalTerm] {
  let mut terms : Array[WickNormalTerm] = [
    WickNormalTerm::{
      coeff: @asymptotic.qv_one(),
      creators: [],
      annihilators: [],
    },
  ]
  let mut idx = factors.length() - 1
  while idx >= 0 {
    let next_terms : Array[WickNormalTerm] = []
    for t in terms {
      for nt in wick_prepend_factor(factors[idx], t) {
        if !@asymptotic.qv_is_zero(nt.coeff) {
          next_terms.push(nt)
        }
      }
    }
    terms = next_terms
    idx = idx - 1
  }
  terms
}

///|
/// 由 Wick 正規序展開直接讀取任意連續場乘積的精確真空期望值 `⟨Ω | F_0 ⋯ F_{m-1} | Ω⟩`：
/// 等於所有 `creators == [] && annihilators == []` 完全縮併項的係數總和。
pub fn wick_vacuum_expectation(
  factors : Array[FieldFactor],
) -> @asymptotic.QVal {
  let normal_terms = wick_normal_order(factors)
  let mut v_exp = @asymptotic.qv_zero()
  for t in normal_terms {
    if t.creators.length() == 0 && t.annihilators.length() == 0 {
      v_exp = @asymptotic.qv_add(v_exp, t.coeff)
    }
  }
  v_exp
}

// ---------------------------------------------------------------------------
// Weyl CCR 指數場代數（辛形式）與 Hudson–Parthasarathy 量子 Itô 代數
// ---------------------------------------------------------------------------

///|
/// 複相空間測試函數 `f_re(t) + i f_im(t) ∈ L²([a, b], ℂ)`，用於非退化 Weyl 辛形式。
pub(all) struct ComplexFieldFn {
  re : ContinuumTestFn
  im : ContinuumTestFn
}

///|
/// 複 `L²` Hermitian 內積（物理慣例左共軛線性）：`⟨f, g⟩ = ∫ conj(f(t)) g(t) dt`。
pub fn complex_field_inner(
  f : ComplexFieldFn,
  g : ComplexFieldFn,
) -> @unbounded.QComplex {
  let re_part = @asymptotic.qv_add(
    continuum_l2_inner(f.re, g.re),
    continuum_l2_inner(f.im, g.im),
  )
  let im_part = @asymptotic.qv_sub(
    continuum_l2_inner(f.re, g.im),
    continuum_l2_inner(f.im, g.re),
  )
  @unbounded.qc_make(re_part, im_part)
}

///|
/// 標準連續場辛形式 `σ(f, g) = Im⟨f, g⟩ = ∫ (f_re g_im − f_im g_re) dt`：
/// 決定 Weyl 位移算子乘法上同調相位 `W(f) W(g) = exp(−(i/2) σ(f, g)) W(f + g)`！
pub fn weyl_symplectic_form(
  f : ComplexFieldFn,
  g : ComplexFieldFn,
) -> @asymptotic.QVal {
  complex_field_inner(f, g).im
}

///|
/// Hudson–Parthasarathy 量子隨機微積分基本微元：`dt`、`dA_t`（湮滅微元）、`dA†_t`（創生微元）、`dΛ_t`（規範／保數微元）。
#derive(Eq)
pub(all) enum QuantumItoDiff {
  ZeroDiff
  Dt
  DA
  DADag
  DLambda
}

///|
pub extend QuantumItoDiff with Eq::{not_equal, equal}

///|
/// 量子 Itô 乘法表（Hudson–Parthasarathy 定理）：
///   `dA · dA† = dt`、`dA · dΛ = dA`、`dΛ · dA† = dA†`、`dΛ · dΛ = dΛ`，其餘二階微元乘積全為 0！
/// 這使得二階量子隨機微分形成一個嚴格結合（Associative）但非交換的微元代數！
pub fn quantum_ito_mul(
  x : QuantumItoDiff,
  y : QuantumItoDiff,
) -> QuantumItoDiff {
  match (x, y) {
    (DA, DADag) => Dt
    (DA, DLambda) => DA
    (DLambda, DADag) => DADag
    (DLambda, DLambda) => DLambda
    _ => ZeroDiff
  }
}

///|
/// 量子隨機微分線性組合 `c_t dt + c_a dA + c_ad dA† + c_l dΛ`。
pub(all) struct QuantumSdeIncrement {
  c_dt : @unbounded.QComplex
  c_da : @unbounded.QComplex
  c_dadag : @unbounded.QComplex
  c_dlambda : @unbounded.QComplex
}

///|
pub fn qsde_adjoint(dx : QuantumSdeIncrement) -> QuantumSdeIncrement {
  QuantumSdeIncrement::{
    c_dt: @unbounded.qc_conj(dx.c_dt),
    c_da: @unbounded.qc_conj(dx.c_dadag),
    c_dadag: @unbounded.qc_conj(dx.c_da),
    c_dlambda: @unbounded.qc_conj(dx.c_dlambda),
  }
}

///|
/// 計算兩個量子隨機微分增量的 Itô 二次變差乘積 `dX · dY`！
pub fn qsde_ito_product(
  dx : QuantumSdeIncrement,
  dy : QuantumSdeIncrement,
) -> QuantumSdeIncrement {
  // dA * dA† -> dt
  let dt_term = @unbounded.qc_mul(dx.c_da, dy.c_dadag)
  // dA * dΛ -> dA
  let da_term = @unbounded.qc_mul(dx.c_da, dy.c_dlambda)
  // dΛ * dA† -> dA†
  let dadag_term = @unbounded.qc_mul(dx.c_dlambda, dy.c_dadag)
  // dΛ * dΛ -> dΛ
  let dlam_term = @unbounded.qc_mul(dx.c_dlambda, dy.c_dlambda)
  QuantumSdeIncrement::{
    c_dt: dt_term,
    c_da: da_term,
    c_dadag: dadag_term,
    c_dlambda: dlam_term,
  }
}

///|
pub fn qsde_add(
  a : QuantumSdeIncrement,
  b : QuantumSdeIncrement,
) -> QuantumSdeIncrement {
  QuantumSdeIncrement::{
    c_dt: @unbounded.qc_add(a.c_dt, b.c_dt),
    c_da: @unbounded.qc_add(a.c_da, b.c_da),
    c_dadag: @unbounded.qc_add(a.c_dadag, b.c_dadag),
    c_dlambda: @unbounded.qc_add(a.c_dlambda, b.c_dlambda),
  }
}

///|
pub fn qsde_eq(a : QuantumSdeIncrement, b : QuantumSdeIncrement) -> Bool {
  a.c_dt == b.c_dt &&
  a.c_da == b.c_da &&
  a.c_dadag == b.c_dadag &&
  a.c_dlambda == b.c_dlambda
}
