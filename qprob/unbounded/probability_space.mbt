// ---------------------------------------------------------------------------
// qprob/unbounded/probability_space.mbt — 無界算子概率空間 (𝒟, Op*(𝒟), φ)
// ---------------------------------------------------------------------------
// 數學結構演變（第二階）：
//   在第一階的歸納／射影極限空間之上，一旦引入量子粒子數算子 `N|n⟩ = n|n⟩` 或位置／動量算子
//   `Q = a + a†`，算子範數隨截斷維度 `d → ∞` 無界增長（`‖N_d‖ = d − 1 → ∞`）。
//   因此有界 C*-代數 `ℬ(ℋ)` 不再封閉，必須抽象出 **Schwartz 型稠密不變定義域 `𝒟 = ∪_k V_k`**
//   與其上的 **無界 *-代數 `Op*(𝒟)`**：
//     1. 每個無界算子攜帶顯式的多項式成長階 `growth_deg`（`‖A|n⟩‖ ≤ C (1+n)^k`），
//        由於 `𝒟` 對任意多項式權重快速衰減，無界算子複合 `A ∘ B` 在 `𝒟` 上處處有定義！
//     2. 非交換量子態 `φ`（密度算子／正規化正線性泛函）滿足正定性 `φ(A*A) ≥ 0`；
//     3. 由此自然導出：
//        - [定理 2.1] GNS 構造與非交換 Cauchy–Schwarz 不等式 `|φ(A*B)|² ≤ φ(A*A)φ(B*B)`；
//        - [定理 2.2] Robertson–Schrödinger 無界算子不確定性原理
//          `Var_φ(A)·Var_φ(B) ≥ (1/4)|φ([A,B])|² + (1/4)|φ({A−μ_A, B−μ_B})|²`；
//        - [定理 2.3] Yosida 有界預解逼近 `A_λ = λ A (λ I + A)⁻¹`：將無界正自伴算子正則化為
//          範數 `≤ λ` 的有界算子，並在 `λ → ∞`（`ε = λ⁻¹ → 0⁺`）漸近極限逐點收斂回 `A`！
//        - [演算法 2.A] 精確 Rutishauser–Stieltjes 矩問題 → 連分數 → Jacobi 三對角無界算子重構！

///|
/// 複有理數 `re + i · im ∈ ℚ(i)`，供自伴算子、反自伴交換子 `[Q, P] = i I` 與 Schrödinger 協方差使用。
#derive(Eq)
pub(all) struct QComplex {
  re : @asymptotic.QVal
  im : @asymptotic.QVal
}

///|
pub extend QComplex with Eq::{not_equal, equal}

///|
pub fn qc_zero() -> QComplex {
  QComplex::{ re: @asymptotic.qv_zero(), im: @asymptotic.qv_zero(), }
}

///|
pub fn qc_one() -> QComplex {
  QComplex::{ re: @asymptotic.qv_one(), im: @asymptotic.qv_zero(), }
}

///|
pub fn qc_i() -> QComplex {
  QComplex::{ re: @asymptotic.qv_zero(), im: @asymptotic.qv_one(), }
}

///|
pub fn qc_real(r : @asymptotic.QVal) -> QComplex {
  QComplex::{ re: r, im: @asymptotic.qv_zero(), }
}

///|
pub fn qc_make(re : @asymptotic.QVal, im : @asymptotic.QVal) -> QComplex {
  QComplex::{ re, im, }
}

///|
pub fn qc_conj(z : QComplex) -> QComplex {
  QComplex::{ re: z.re, im: @asymptotic.qv_neg(z.im), }
}

///|
pub fn qc_add(a : QComplex, b : QComplex) -> QComplex {
  QComplex::{
    re: @asymptotic.qv_add(a.re, b.re),
    im: @asymptotic.qv_add(a.im, b.im),
  }
}

///|
pub fn qc_neg(z : QComplex) -> QComplex {
  QComplex::{ re: @asymptotic.qv_neg(z.re), im: @asymptotic.qv_neg(z.im), }
}

///|
pub fn qc_mul(a : QComplex, b : QComplex) -> QComplex {
  QComplex::{
    re: @asymptotic.qv_sub(
      @asymptotic.qv_mul(a.re, b.re),
      @asymptotic.qv_mul(a.im, b.im),
    ),
    im: @asymptotic.qv_add(
      @asymptotic.qv_mul(a.re, b.im),
      @asymptotic.qv_mul(a.im, b.re),
    ),
  }
}

///|
/// 模平方 `|z|² = re² + im² ∈ ℚ_{\ge 0}`。
pub fn qc_norm_sq(z : QComplex) -> @asymptotic.QVal {
  @asymptotic.qv_add(
    @asymptotic.qv_mul(z.re, z.re),
    @asymptotic.qv_mul(z.im, z.im),
  )
}

///|
/// 稠密定義域截斷上的無界算子表示（`dim × dim` 複有理矩陣 + Sobolev 多項式成長階 `growth_deg`）。
/// 當 `growth_deg > 0` 時，算子範數隨截斷維度 `dim → ∞` 以 `O(dim^{growth_deg})` 發散。
pub(all) struct UnboundedOp {
  dim : Int32
  growth_deg : Int32
  entries : Array[QComplex]
}

///|
pub fn uop_zero(dim : Int32) -> UnboundedOp {
  guard dim >= 0 else { abort("uop_zero: negative dim") }
  UnboundedOp::{
    dim,
    growth_deg: 0,
    entries: Array::make(dim * dim, qc_zero()),
  }
}

///|
pub fn uop_identity(dim : Int32) -> UnboundedOp {
  guard dim >= 0 else { abort("uop_identity: negative dim") }
  let es = Array::make(dim * dim, qc_zero())
  for i in 0..<dim {
    es[i * dim + i] = qc_one()
  }
  UnboundedOp::{ dim, growth_deg: 0, entries: es, }
}

///|
pub fn uop_scale(c : QComplex, a : UnboundedOp) -> UnboundedOp {
  let g = if c == qc_zero() { 0 } else { a.growth_deg }
  UnboundedOp::{
    dim: a.dim,
    growth_deg: g,
    entries: [
      for x in a.entries => qc_mul(c, x)
    ],
  }
}

///|
pub fn uop_add(a : UnboundedOp, b : UnboundedOp) -> UnboundedOp {
  guard a.dim == b.dim && a.entries.length() == b.entries.length() else {
    abort("uop_add: dimension mismatch")
  }
  let g = if a.growth_deg > b.growth_deg { a.growth_deg } else { b.growth_deg }
  UnboundedOp::{
    dim: a.dim,
    growth_deg: g,
    entries: [
      for k in 0..<a.entries.length() => qc_add(a.entries[k], b.entries[k])
    ],
  }
}

///|
pub fn uop_sub(a : UnboundedOp, b : UnboundedOp) -> UnboundedOp {
  guard a.dim == b.dim && a.entries.length() == b.entries.length() else {
    abort("uop_sub: dimension mismatch")
  }
  uop_add(a, UnboundedOp::{
    dim: b.dim,
    growth_deg: b.growth_deg,
    entries: [
      for x in b.entries => qc_neg(x)
    ],
  })
}

///|
/// 形式伴隨 `A†`（共軛轉置）；在稠密不變核 `𝒟` 上與閉伴隨限制一致。
pub fn uop_adjoint(a : UnboundedOp) -> UnboundedOp {
  let d = a.dim
  guard a.entries.length() == d * d else {
    abort("uop_adjoint: malformed entries")
  }
  let es = Array::make(d * d, qc_zero())
  for r in 0..<d {
    for c in 0..<d {
      es[c * d + r] = qc_conj(a.entries[r * d + c])
    }
  }
  UnboundedOp::{ dim: d, growth_deg: a.growth_deg, entries: es, }
}

///|
/// 無界算子在共同不變稠密核 `𝒟` 上的複合 `A · B`，多項式成長階相加 `deg(AB) = deg(A) + deg(B)`。
pub fn uop_mul(a : UnboundedOp, b : UnboundedOp) -> UnboundedOp {
  let d = a.dim
  guard d == b.dim && a.entries.length() == d * d && b.entries.length() == d * d else {
    abort("uop_mul: dimension mismatch")
  }
  let es = Array::make(d * d, qc_zero())
  for r in 0..<d {
    for k in 0..<d {
      let ark = a.entries[r * d + k]
      if ark != qc_zero() {
        for c in 0..<d {
          let idx = r * d + c
          es[idx] = qc_add(es[idx], qc_mul(ark, b.entries[k * d + c]))
        }
      }
    }
  }
  UnboundedOp::{ dim: d, growth_deg: a.growth_deg + b.growth_deg, entries: es, }
}

///|
pub fn uop_eq(a : UnboundedOp, b : UnboundedOp) -> Bool {
  if a.dim != b.dim || a.entries.length() != b.entries.length() {
    return false
  }
  for k in 0..<a.entries.length() {
    if a.entries[k] != b.entries[k] {
      return false
    }
  }
  true
}

///|
pub fn uop_is_self_adjoint(a : UnboundedOp) -> Bool {
  uop_eq(a, uop_adjoint(a))
}

///|
/// 交換子 `[A, B] = A B − B A`。
pub fn uop_commutator(a : UnboundedOp, b : UnboundedOp) -> UnboundedOp {
  uop_sub(uop_mul(a, b), uop_mul(b, a))
}

///|
/// 反交換子 `{A, B} = A B + B A`。
pub fn uop_anticommutator(a : UnboundedOp, b : UnboundedOp) -> UnboundedOp {
  uop_add(uop_mul(a, b), uop_mul(b, a))
}

///|
/// 標準無界粒子數算子 `N|n⟩ = n|n⟩`（`0 ≤ n < dim`，成長階 1）。
pub fn uop_number_op(dim : Int32) -> UnboundedOp {
  let es = Array::make(dim * dim, qc_zero())
  for n in 0..<dim {
    es[n * dim + n] = qc_real(@asymptotic.qv_int(n))
  }
  UnboundedOp::{ dim, growth_deg: 1, entries: es, }
}

///|
/// 截斷玻色場對偶正交分量（未帶 √，採精確整係數 Jacobi 自伴實現或標準對稱加權）：
/// 給定實次對角權重 `b_0, ..., b_{dim-2}` 與對角勢 `a_0, ..., a_{dim-1}`，
/// 構造對稱 Jacobi 三對角無界算子 `J`（自伴）與其共軛反對稱夥伴 `K = i [N, J]`（乘 `i` 後自伴）。
pub fn uop_jacobi_tridiag(
  diag : Array[@asymptotic.QVal],
  subdiag : Array[@asymptotic.QVal],
) -> UnboundedOp {
  let d = diag.length()
  let es = Array::make(d * d, qc_zero())
  for i in 0..<d {
    es[i * d + i] = qc_real(diag[i])
  }
  for i in 0..<(d - 1) {
    if i < subdiag.length() {
      let w = qc_real(subdiag[i])
      es[i * d + (i + 1)] = w
      es[(i + 1) * d + i] = w
    }
  }
  UnboundedOp::{ dim: d, growth_deg: 1, entries: es, }
}

///|
/// 與 Jacobi 算子對偶的動量型自伴三對角算子 `P_J`：次對角為 `± i · subdiag[k]`。
pub fn uop_dual_momentum_tridiag(
  subdiag : Array[@asymptotic.QVal],
  dim : Int32,
) -> UnboundedOp {
  let es = Array::make(dim * dim, qc_zero())
  for k in 0..<(dim - 1) {
    if k < subdiag.length() {
      // <k| P |k+1> = -i w_k, <k+1| P |k> = +i w_k  => P† = P
      es[k * dim + (k + 1)] = QComplex::{
        re: @asymptotic.qv_zero(),
        im: @asymptotic.qv_neg(subdiag[k]),
      }
      es[(k + 1) * dim + k] = QComplex::{
        re: @asymptotic.qv_zero(),
        im: subdiag[k],
      }
    }
  }
  UnboundedOp::{ dim, growth_deg: 1, entries: es, }
}

// ---------------------------------------------------------------------------
// 量子概率態 φ : Op*(𝒟) → ℚ(i)（由快速衰減密度矩陣 ρ 誘導：φ(A) = Tr(ρ A)）
// ---------------------------------------------------------------------------

///|
/// 量子概率態（正規化 Hermitian 正定密度算子 `ρ`：`Tr(ρ) = 1`）。
pub(all) struct QuantumProbState {
  dim : Int32
  rho : UnboundedOp
}

///|
/// 由純態向量 `|ψ⟩ ∈ 𝒟`（不必預先正規化，只要範數平方 > 0）構造純量子概率態 `ρ = |ψ⟩⟨ψ| / ⟨ψ|ψ⟩`。
pub fn qstate_pure(psi : Array[QComplex]) -> QuantumProbState? {
  let d = psi.length()
  let mut norm2 = @asymptotic.qv_zero()
  for z in psi {
    norm2 = @asymptotic.qv_add(norm2, qc_norm_sq(z))
  }
  guard @asymptotic.qv_inv(norm2) is Some(inv_n2) else { return None }
  let es = Array::make(d * d, qc_zero())
  for r in 0..<d {
    for c in 0..<d {
      let prod = qc_mul(psi[r], qc_conj(psi[c]))
      es[r * d + c] = qc_mul(prod, qc_real(inv_n2))
    }
  }
  Some(QuantumProbState::{
    dim: d,
    rho: UnboundedOp::{ dim: d, growth_deg: 0, entries: es, },
  })
}

///|
/// 由非負有理權重 `w_0, ..., w_{d-1}`（總和 > 0）構造對角混合 Gibbs／熱態 `ρ = diag(w_n) / Z`。
pub fn qstate_diagonal_gibbs(
  weights : Array[@asymptotic.QVal],
) -> QuantumProbState? {
  let d = weights.length()
  let mut z_part = @asymptotic.qv_zero()
  for w in weights {
    if @asymptotic.qv_lt(w, @asymptotic.qv_zero()) {
      return None
    }
    z_part = @asymptotic.qv_add(z_part, w)
  }
  guard @asymptotic.qv_inv(z_part) is Some(inv_z) else { return None }
  let es = Array::make(d * d, qc_zero())
  for i in 0..<d {
    es[i * d + i] = qc_real(@asymptotic.qv_mul(weights[i], inv_z))
  }
  Some(QuantumProbState::{
    dim: d,
    rho: UnboundedOp::{ dim: d, growth_deg: 0, entries: es, },
  })
}

///|
/// 量子期望值泛函 `φ(A) = Tr(ρ A)`。
pub fn qstate_expect(st : QuantumProbState, a : UnboundedOp) -> QComplex {
  let prod = uop_mul(st.rho, a)
  let mut tr = qc_zero()
  for i in 0..<prod.dim {
    tr = qc_add(tr, prod.entries[i * prod.dim + i])
  }
  tr
}

///|
fn uop_center(st : QuantumProbState, a : UnboundedOp) -> UnboundedOp {
  uop_sub(a, uop_scale(qstate_expect(st, a), uop_identity(a.dim)))
}

///|
/// 自伴觀測量 `A = A†` 的量子變異數 `Var_φ(A) = φ((A − φ(A)I)²) ∈ ℚ_{\ge 0}`。
pub fn qstate_variance(
  st : QuantumProbState,
  a : UnboundedOp,
) -> @asymptotic.QVal {
  let centered = uop_center(st, a)
  qstate_expect(st, uop_mul(centered, centered)).re
}

///|
/// Robertson–Schrödinger 不確定性不等式檢驗報告：
/// 左式 `LHS = Var_φ(A) · Var_φ(B)`，
/// 右式 `RHS = (1/4)|φ([A,B])|² + (1/4)|φ({A_0, B_0})|²`（其中 `A_0 = A − φ(A)I`）。
pub(all) struct UncertaintyBound {
  lhs_prod : @asymptotic.QVal
  commutator_term : @asymptotic.QVal
  covariance_term : @asymptotic.QVal
  rhs_total : @asymptotic.QVal
  holds : Bool
}

///|
pub fn check_robertson_schrodinger(
  st : QuantumProbState,
  a : UnboundedOp,
  b : UnboundedOp,
) -> UncertaintyBound {
  let va = qstate_variance(st, a)
  let vb = qstate_variance(st, b)
  let lhs = @asymptotic.qv_mul(va, vb)
  let q_quarter = @asymptotic.qv_frac(1, 4)
  let comm_exp = qstate_expect(st, uop_commutator(a, b))
  let comm_term = @asymptotic.qv_mul(q_quarter, qc_norm_sq(comm_exp))
  let a0 = uop_center(st, a)
  let b0 = uop_center(st, b)
  let anti_exp = qstate_expect(st, uop_anticommutator(a0, b0))
  let cov_term = @asymptotic.qv_mul(q_quarter, qc_norm_sq(anti_exp))
  let rhs = @asymptotic.qv_add(comm_term, cov_term)
  UncertaintyBound::{
    lhs_prod: lhs,
    commutator_term: comm_term,
    covariance_term: cov_term,
    rhs_total: rhs,
    holds: @asymptotic.qv_le(rhs, lhs),
  }
}

// ---------------------------------------------------------------------------
// 定理 2.3 & 演算法 2.A：Yosida 有界預解正則化與 Stieltjes–Lanczos 矩重構
// ---------------------------------------------------------------------------

///|
/// 對角非負無界自伴算子 `A = diag(λ_0, ..., λ_{d-1})`（`λ_n ≥ 0`）的
/// Yosida 有界逼近算子 `A_γ = γ A (γ I + A)⁻¹`（`γ > 0`）：
/// 1. 每個特徵值變為 `γ λ_n / (γ + λ_n) < γ`（有界算子，範數嚴格受 `γ` 控制，`growth_deg = 0`）；
/// 2. 當 `γ → +∞` 時，以 `A - A_γ = A² (γ I + A)⁻¹ = O(γ⁻¹)` 單調收斂回無界算子 `A`！
pub fn yosida_diagonal_approximant(
  spectrum : Array[@asymptotic.QVal],
  gamma : @asymptotic.QVal,
) -> UnboundedOp? {
  if @asymptotic.qv_le(gamma, @asymptotic.qv_zero()) {
    return None
  }
  let d = spectrum.length()
  let es = Array::make(d * d, qc_zero())
  for n in 0..<d {
    let lam = spectrum[n]
    if @asymptotic.qv_lt(lam, @asymptotic.qv_zero()) {
      return None
    }
    let denom = @asymptotic.qv_add(gamma, lam)
    guard @asymptotic.qv_inv(denom) is Some(inv_d) else { return None }
    let bounded_eig = @asymptotic.qv_mul(@asymptotic.qv_mul(gamma, lam), inv_d)
    es[n * d + n] = qc_real(bounded_eig)
  }
  Some(UnboundedOp::{ dim: d, growth_deg: 0, entries: es, })
}

///|
/// 演算法 2.A（Favard–Chebyshev–Lanczos 正交多項式三對角重構演算法）：
/// 給定無界實自伴隨機變數的前 `2M` 個精確矩 `m_k = φ(X^k)`（`k = 0 .. 2M - 1`，`m_0 = 1`），
/// 透過 Hankel 矩內積 `⟨p, q⟩_m = Σ c_i d_j m_{i+j}` 執行精確三項遞迴正交化：
///   `x P_k(x) = P_{k+1}(x) + α_k P_k(x) + β_k P_{k-1}(x)`
/// 重構唯一的典範 Jacobi 三對角係數 `(α_0..α_{M-1}, β_1..β_{M-1})`（其中 `β_k = ‖P_k‖² / ‖P_{k-1}‖² > 0`）。
/// 若矩序列不滿足嚴格正定（Hamburger 退化或非正測度），精確攔截並回傳 `None`！
pub(all) struct JacobiMomentReconstruction {
  alphas : Array[@asymptotic.QVal]
  betas : Array[@asymptotic.QVal]
}

///|
fn poly_moment_inner(
  p : Array[@asymptotic.QVal],
  q : Array[@asymptotic.QVal],
  moments : Array[@asymptotic.QVal],
) -> @asymptotic.QVal {
  let mut sum = @asymptotic.qv_zero()
  for i in 0..<p.length() {
    for j in 0..<q.length() {
      let prod = @asymptotic.qv_mul(p[i], q[j])
      sum = @asymptotic.qv_add(sum, @asymptotic.qv_mul(prod, moments[i + j]))
    }
  }
  sum
}

///|
fn poly_shift_x(p : Array[@asymptotic.QVal]) -> Array[@asymptotic.QVal] {
  let out = Array::make(p.length() + 1, @asymptotic.qv_zero())
  for i in 0..<p.length() {
    out[i + 1] = p[i]
  }
  out
}

///|
pub fn reconstruct_jacobi_from_moments(
  moments : Array[@asymptotic.QVal],
  order : Int32,
) -> JacobiMomentReconstruction? {
  if order <= 0 || moments.length() < 2 * order {
    return None
  }
  if !@asymptotic.qv_eq(moments[0], @asymptotic.qv_one()) {
    return None
  }
  let alphas : Array[@asymptotic.QVal] = []
  let betas : Array[@asymptotic.QVal] = []
  let mut p_prev : Array[@asymptotic.QVal] = []
  let mut p_cur : Array[@asymptotic.QVal] = [@asymptotic.qv_one()]
  let mut norm_prev = @asymptotic.qv_one()
  for k in 0..<order {
    let norm_cur = poly_moment_inner(p_cur, p_cur, moments)
    if @asymptotic.qv_le(norm_cur, @asymptotic.qv_zero()) {
      return None
    }
    guard @asymptotic.qv_inv(norm_cur) is Some(inv_nc) else { return None }
    let xp = poly_shift_x(p_cur)
    let alpha_k = @asymptotic.qv_mul(
      poly_moment_inner(xp, p_cur, moments),
      inv_nc,
    )
    alphas.push(alpha_k)
    if k > 0 {
      guard @asymptotic.qv_inv(norm_prev) is Some(inv_np) else { return None }
      let beta_k = @asymptotic.qv_mul(norm_cur, inv_np)
      if @asymptotic.qv_le(beta_k, @asymptotic.qv_zero()) {
        return None
      }
      betas.push(beta_k)
    }
    if k + 1 < order {
      // P_{k+1} = x P_k - alpha_k P_k - (k > 0 ? beta_k P_{k-1} : 0)
      let next_p = Array::make(xp.length(), @asymptotic.qv_zero())
      for i in 0..<xp.length() {
        next_p[i] = xp[i]
      }
      for i in 0..<p_cur.length() {
        next_p[i] = @asymptotic.qv_sub(
          next_p[i],
          @asymptotic.qv_mul(alpha_k, p_cur[i]),
        )
      }
      if k > 0 {
        let bk = betas[betas.length() - 1]
        for i in 0..<p_prev.length() {
          next_p[i] = @asymptotic.qv_sub(
            next_p[i],
            @asymptotic.qv_mul(bk, p_prev[i]),
          )
        }
      }
      p_prev = p_cur
      p_cur = next_p
      norm_prev = norm_cur
    }
  }
  Some(JacobiMomentReconstruction::{ alphas, betas, })
}
