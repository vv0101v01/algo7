// ---------------------------------------------------------------------------
// qprob/nc_measure/noncommutative_measure.mbt — 非交換隨機分佈、正算子值測度（POVM）與自由累積量
// ---------------------------------------------------------------------------
// 數學結構演變（第五階 — 全系統統合頂點）：
//   在第一至第四階中，我們依次建立了：
//     L0 無窮漸近極限空間 → L1 無界算子概率空間 → L2 全量子福克空間 → L3 連續創生湮滅算子場。
//   現在，當場算子或觀測量互不交換時，古典 Kolmogorov σ-代數與聯合機率測度不再存在！
//   我們將整個機率測度論提升為 **非交換隨機分佈與量子測度空間**：
//     1. **正算子值測度（POVM / Noncommutative Operator-Valued Measure）**：
//        事件不再是布爾冪集，而是滿足正定性 `E_k ≥ 0`（表示為 `M_k† M_k` Kraus 算子平方）與
//        完備性分解 `Σ_k E_k = I` 的算子測度族！對任意密度態 `ρ`，誘導 Born 機率測度 `p_k = Tr(ρ E_k)`。
//        當 `E_j E_k = δ_{jk} E_k` 時退化為投影值譜測度（PVM）；一般 POVM 經由 **Naimark 擴張定理**
//        等距嵌入高維環境希爾伯特空間 `ℋ ⊗ ℂ^K` 上的正交 PVM！
//     2. **非交換隨機分佈與自由累積量演算法（Voiculescu–Speicher Free Cumulants）**：
//        在非交換空間 `(𝒜, φ)` 中，經典配分格 `Π(n)` 被替換為 **非交叉配分格 `NC(n)`**（大小為 Catalan 數 `C_n`）！
//        矩-累積量方程 `m_n = Σ_{π ∈ NC(n)} ∏_{B ∈ π} κ_{|B|}` 透過非交叉遞迴 Möbius 反演，給出自由累積量 `κ_n`：
//          - Wigner 半圓分佈（第三階全福克場 `ℓ* + ℓ` 的真空分佈！）滿足 `κ_2 = 1`，且所有高階 `κ_n = 0 (n ≠ 2)`！
//          - 自由中心極限定理（Free CLT）：`N` 個自由獨立同分佈中心化變數標準化和 `S_N = (X_1 + ... + X_N)/√N`
//            的第 `n` 階自由累積量為 `κ_n(S_N) = N^{1 - n/2} κ_n(X)`；當 `N → ∞`（第一階漸近極限！），
//            所有 `n ≥ 3` 的累積量以 `O(N^{-(n-2)/2})` 湮滅，矩序列精確收斂至半圓律 Catalan 矩！
//          - 自由 Poisson（Marchenko–Pastur，率 `λ`）分佈的所有階自由累積量恆為 `κ_n = λ`！
//     3. **完全正保跡量子通道（CPTP Quantum Markov Measure Kernel）**：
//        Kraus 表示 `Φ(ρ) = Σ_a K_a ρ K_a†`（`Σ_a K_a† K_a = I`）實現非交換隨機轉移核。

///|
/// 以 Kraus 測度平方根 `M_k` 表示的正算子值測度（POVM）：每個效應算子 `E_k = M_k† M_k` 自動半正定！
pub(all) struct PovmMeasure {
  dim : Int32
  kraus_roots : Array[@unbounded.UnboundedOp]
}

///|
/// 計算第 `k` 個 POVM 效應算子 `E_k = M_k† M_k`。
pub fn povm_effect(povm : PovmMeasure, idx : Int32) -> @unbounded.UnboundedOp {
  guard idx >= 0 && idx < povm.kraus_roots.length() else {
    abort("povm_effect: index out of range")
  }
  let mk = povm.kraus_roots[idx]
  @unbounded.uop_mul(@unbounded.uop_adjoint(mk), mk)
}

///|
/// 檢查 POVM 完備性公理：`Σ_{k=0}^{K-1} M_k† M_k == I_{dim}`。
pub fn povm_is_complete(povm : PovmMeasure) -> Bool {
  if povm.dim <= 0 || povm.kraus_roots.length() == 0 {
    return false
  }
  let mut sum = @unbounded.uop_zero(povm.dim)
  for k in 0..<povm.kraus_roots.length() {
    if povm.kraus_roots[k].dim != povm.dim {
      return false
    }
    sum = @unbounded.uop_add(sum, povm_effect(povm, k))
  }
  @unbounded.uop_eq(sum, @unbounded.uop_identity(povm.dim))
}

///|
/// 檢查是否為正交投影值測度（PVM）：對所有 `j, k`，`E_j E_k = δ_{jk} E_k`。
pub fn povm_is_projective(povm : PovmMeasure) -> Bool {
  let k_cnt = povm.kraus_roots.length()
  let zero_op = @unbounded.uop_zero(povm.dim)
  for j in 0..<k_cnt {
    let ej = povm_effect(povm, j)
    for k in 0..<k_cnt {
      let ek = povm_effect(povm, k)
      let prod = @unbounded.uop_mul(ej, ek)
      let expected = if j == k { ek } else { zero_op }
      if !@unbounded.uop_eq(prod, expected) {
        return false
      }
    }
  }
  true
}

///|
/// Born 量子測度律：將非交換 POVM 與量子態 `st` 配對，生成古典離散機率分佈 `p_k = Tr(ρ E_k) ∈ ℚ_{\ge 0}`。
pub fn povm_born_probabilities(
  povm : PovmMeasure,
  st : @unbounded.QuantumProbState,
) -> Array[@asymptotic.QVal] {
  [
    for k in 0..<povm.kraus_roots.length() => {
      @unbounded.qstate_expect(st, povm_effect(povm, k)).re
    }
  ]
}

// ---------------------------------------------------------------------------
// 演算法 5.A：Naimark 算子測度擴張演算法（Naimark Dilation to Orthogonal PVM）
// ---------------------------------------------------------------------------
// 給定 `d` 維空間上的 `K` 結果完備 POVM `{M_0, ..., M_{K-1}}`（`Σ M_k† M_k = I_d`），
// 構造等距嵌入 `V : ℂ^d → ℂ^{K·d}`（分塊行矩陣 `[M_0; M_1; ...; M_{K-1}]`，滿足 `V† V = I_d`），
// 以及擴張空間 `ℂ^{K·d}` 上的分塊對角正交投影族 `P_k = |k⟩⟨k| ⊗ I_d`：
//   1. `{P_0, ..., P_{K-1}}` 在 `ℂ^{K·d}` 上嚴格正交（`P_j P_k = δ_{jk} P_k`）且完備（`Σ P_k = I_{Kd}`）；
//   2. 壓縮恆等式：`V† P_k V == M_k† M_k = E_k` 對每個結果 `k` 精確成立！

///|
/// 驗證 Naimark 等距擴張壓縮恆等式 `V† P_k V = E_k` 與 `V† V = I_d`，並回傳擴張維度 `K · d`。
pub fn verify_naimark_dilation(povm : PovmMeasure) -> (Int32, Bool) {
  let d = povm.dim
  let k_cnt = povm.kraus_roots.length()
  let big_d = k_cnt * d
  if !povm_is_complete(povm) {
    return (big_d, false)
  }
  // 構造 V (big_d × d) 與 V† (d × big_d)
  let v_mat = Array::make(big_d * d, @unbounded.qc_zero())
  for k in 0..<k_cnt {
    let mk = povm.kraus_roots[k]
    for r in 0..<d {
      for c in 0..<d {
        v_mat[(k * d + r) * d + c] = mk.entries[r * d + c]
      }
    }
  }
  // 檢查 V† V == I_d
  let mut iso_ok = true
  for r in 0..<d {
    for c in 0..<d {
      let mut acc = @unbounded.qc_zero()
      for row in 0..<big_d {
        acc = @unbounded.qc_add(
          acc,
          @unbounded.qc_mul(
            @unbounded.qc_conj(v_mat[row * d + r]),
            v_mat[row * d + c],
          ),
        )
      }
      let exp = if r == c { @unbounded.qc_one() } else { @unbounded.qc_zero() }
      if acc != exp {
        iso_ok = false
      }
    }
  }
  // 檢查對每個 k，壓縮 V† P_k V（只對 row ∈ [k*d .. (k+1)*d) 求和）精確等於 E_k
  let mut comp_ok = true
  for k in 0..<k_cnt {
    let ek = povm_effect(povm, k)
    for r in 0..<d {
      for c in 0..<d {
        let mut acc = @unbounded.qc_zero()
        for sub_r in 0..<d {
          let row = k * d + sub_r
          acc = @unbounded.qc_add(
            acc,
            @unbounded.qc_mul(
              @unbounded.qc_conj(v_mat[row * d + r]),
              v_mat[row * d + c],
            ),
          )
        }
        if acc != ek.entries[r * d + c] {
          comp_ok = false
        }
      }
    }
  }
  (big_d, iso_ok && comp_ok)
}

// ---------------------------------------------------------------------------
// 演算法 5.B：非交叉配分格 NC(n) 與 Speicher 矩 ↔ 自由累積量轉換演算法
// ---------------------------------------------------------------------------
// 單變量非交換分佈的矩序列 `m_1, m_2, ..., m_N`（約定 `m_0 = 1`）與自由累積量 `κ_1, ..., κ_N`
// 滿足 Voiculescu R-變換等價的遞迴卷積恆等式（按包含首元素 `1` 的非交叉塊大小 `s` 分類！）：
//   `m_n = Σ_{s=1}^n κ_s · Σ_{i_1 + ... + i_s = n - s, i_r ≥ 0} m_{i_1} · m_{i_2} · ... · m_{i_s}`
// 反解出 `κ_n`（因為唯一包含 `s = n` 的項是 `κ_n · m_0^n = κ_n`！）：
//   `κ_n = m_n − Σ_{s=1}^{n-1} κ_s · (m^{* s})_{n - s}`
// 此動態規劃在 `O(N³)` 精確有理算術內完成矩與自由累積量的雙向無損互轉，
// 同時代數地證明了非交叉配分計數與 Lagrange 反演！

///|
/// 計算序列 `m[0..=max_deg]`（`m[0] = 1`）的 `s` 重 Cauchy 卷積冪 `(m^{* s})[0..=max_deg]`。
fn moment_conv_power(
  m : Array[@asymptotic.QVal],
  s : Int32,
  max_deg : Int32,
) -> Array[@asymptotic.QVal] {
  let mut cur = Array::make(max_deg + 1, @asymptotic.qv_zero())
  cur[0] = @asymptotic.qv_one()
  for _ in 0..<s {
    let nxt = Array::make(max_deg + 1, @asymptotic.qv_zero())
    for i in 0..<(max_deg + 1) {
      if !@asymptotic.qv_is_zero(cur[i]) {
        for j in 0..<(max_deg + 1 - i) {
          nxt[i + j] = @asymptotic.qv_add(
            nxt[i + j],
            @asymptotic.qv_mul(cur[i], m[j]),
          )
        }
      }
    }
    cur = nxt
  }
  cur
}

///|
/// 演算法 5.B（正向）：由正規化矩序列 `moments = [m_0=1, m_1, ..., m_N]` 精確計算自由累積量 `[κ_1, ..., κ_N]`！
pub fn moments_to_free_cumulants(
  moments : Array[@asymptotic.QVal],
) -> Array[@asymptotic.QVal] {
  if moments.length() <= 1 {
    return []
  }
  guard @asymptotic.qv_eq(moments[0], @asymptotic.qv_one()) else {
    abort("moments_to_free_cumulants: moments[0] must equal 1")
  }
  let max_n = moments.length() - 1
  // 遞推維護 Cauchy 卷積冪 (m^{* s})，免除重複呼叫 moment_conv_power
  let convs : Array[Array[@asymptotic.QVal]] = [
    Array::make(max_n + 1, @asymptotic.qv_zero()),
  ]
  convs[0][0] = @asymptotic.qv_one()
  for s in 1..<(max_n + 1) {
    let prev = convs[s - 1]
    let nxt = Array::make(max_n + 1, @asymptotic.qv_zero())
    for i in 0..<(max_n + 1) {
      if !@asymptotic.qv_is_zero(prev[i]) {
        for j in 0..<(max_n + 1 - i) {
          nxt[i + j] = @asymptotic.qv_add(
            nxt[i + j],
            @asymptotic.qv_mul(prev[i], moments[j]),
          )
        }
      }
    }
    convs.push(nxt)
  }
  let kappas = Array::make(max_n, @asymptotic.qv_zero())
  for n in 1..<(max_n + 1) {
    let mut sub_sum = @asymptotic.qv_zero()
    for s in 1..<n {
      let term = @asymptotic.qv_mul(kappas[s - 1], convs[s][n - s])
      sub_sum = @asymptotic.qv_add(sub_sum, term)
    }
    kappas[n - 1] = @asymptotic.qv_sub(moments[n], sub_sum)
  }
  kappas
}

///|
/// 演算法 5.B（逆向）：由自由累積量 `kappas = [κ_1, ..., κ_N]` 精確合成矩序列 `[m_0=1, m_1, ..., m_N]`！
pub fn free_cumulants_to_moments(
  kappas : Array[@asymptotic.QVal],
) -> Array[@asymptotic.QVal] {
  let max_n = kappas.length()
  let m = Array::make(max_n + 1, @asymptotic.qv_zero())
  m[0] = @asymptotic.qv_one()
  for n in 1..<(max_n + 1) {
    let mut acc = @asymptotic.qv_zero()
    for s in 1..<(n + 1) {
      let ks = kappas[s - 1]
      if !@asymptotic.qv_is_zero(ks) {
        // 只需用到 m[0 .. n - s]，皆已在更小階算出！
        let cp = moment_conv_power(m, s, n - s)
        acc = @asymptotic.qv_add(acc, @asymptotic.qv_mul(ks, cp[n - s]))
      }
    }
    m[n] = acc
  }
  m
}

///|
/// 自由加性卷積 `μ ⊞ ν`（Voiculescu Free Additive Convolution）：
/// 若非交換隨機變數 `X, Y` 自由獨立，則 `X + Y` 的各階自由累積量精確可加：`κ_n(X + Y) = κ_n(X) + κ_n(Y)`！
/// 本函式輸入 `X` 與 `Y` 的矩序列，透過「矩 → 自由累積量相加 → 矩」計算 `X + Y` 的精確自由卷積矩序列！
pub fn free_additive_convolution_moments(
  m_x : Array[@asymptotic.QVal],
  m_y : Array[@asymptotic.QVal],
) -> Array[@asymptotic.QVal] {
  let kx = moments_to_free_cumulants(m_x)
  let ky = moments_to_free_cumulants(m_y)
  let n = if kx.length() < ky.length() { kx.length() } else { ky.length() }
  let k_sum = [ for i in 0..<n => @asymptotic.qv_add(kx[i], ky[i]) ]
  free_cumulants_to_moments(k_sum)
}

///|
/// 計算 `N` 個自由獨立同分佈中心化變數（`κ_1 = 0, κ_2 = 1`）標準化和
/// `S_N = (X_1 + ... + X_N) / √N` 的精確矩序列（利用偶／奇冪次有理縮放：
/// 對中心化對稱分佈奇數累積量為 0，偶數階 `2m` 累積量縮放因子為 `N · (N^{-1/2})^{2m} = N^{1 - m} ∈ ℚ`！
/// 對一般含三階累積量 `κ_3` 的情形，`κ_4` 縮放為 `N^{-1}`、`κ_6` 為 `N^{-2}`；此處支援任意偶累積量精確縮放，
/// 若針對 `N = r²` 完全平方數，連奇數階 `N^{1 - n/2} = r^{2 - n}` 亦全部為精確有理數！）。
pub fn free_clt_scaled_moments(
  base_moments : Array[@asymptotic.QVal],
  sqrt_n : Int32,
) -> Array[@asymptotic.QVal] {
  if sqrt_n <= 0 {
    return []
  }
  let kx = moments_to_free_cumulants(base_moments)
  // N = sqrt_n², 縮放因子 N · (1 / sqrt_n)^deg = sqrt_n^{2 - deg}（對任意奇偶 deg 皆為精確有理數！）
  let r_val = @asymptotic.qv_int(sqrt_n)
  let k_scaled : Array[@asymptotic.QVal] = []
  for idx in 0..<kx.length() {
    let deg = idx + 1
    if deg == 1 {
      // 中心化後 κ_1 = 0
      k_scaled.push(@asymptotic.qv_zero())
    } else if deg == 2 {
      k_scaled.push(kx[idx])
    } else {
      let inv_pow = @asymptotic.qv_pow(r_val, deg - 2)
      k_scaled.push(@asymptotic.qv_div(kx[idx], inv_pow))
    }
  }
  free_cumulants_to_moments(k_scaled)
}

// ---------------------------------------------------------------------------
// 古典累積量（Classical Cumulants on All Partitions Π(n)）對照：證明非交換自由性 ≠ 張量古典獨立！
//   m_n = Σ_{s=1}^n C(n-1, s-1) c_s m_{n-s}
// ---------------------------------------------------------------------------

///|
fn binom_q(n : Int32, k : Int32) -> @asymptotic.QVal {
  if k < 0 || k > n {
    return @asymptotic.qv_zero()
  }
  let mut num = 1N
  let mut den = 1N
  for i in 0..<k {
    num = num * BigInt::from_int(n - i)
    den = den * BigInt::from_int(i + 1)
  }
  @asymptotic.qv_make(num, den)
}

///|
/// 古典累積量遞迴：`c_n = m_n − Σ_{s=1}^{n-1} C(n-1, s-1) c_s m_{n-s}`（高斯分佈滿足 `c_{n≥3} = 0`）。
pub fn moments_to_classical_cumulants(
  moments : Array[@asymptotic.QVal],
) -> Array[@asymptotic.QVal] {
  if moments.length() <= 1 {
    return []
  }
  guard @asymptotic.qv_eq(moments[0], @asymptotic.qv_one()) else {
    abort("moments_to_classical_cumulants: moments[0] must equal 1")
  }
  let max_n = moments.length() - 1
  let cs = Array::make(max_n, @asymptotic.qv_zero())
  for n in 1..<(max_n + 1) {
    let mut sub_s = @asymptotic.qv_zero()
    for s in 1..<n {
      let term = @asymptotic.qv_mul(
        binom_q(n - 1, s - 1),
        @asymptotic.qv_mul(cs[s - 1], moments[n - s]),
      )
      sub_s = @asymptotic.qv_add(sub_s, term)
    }
    cs[n - 1] = @asymptotic.qv_sub(moments[n], sub_s)
  }
  cs
}

// ---------------------------------------------------------------------------
// 完全正保跡量子通道（CPTP Quantum Markov Kernel）Φ(ρ) = Σ_a K_a ρ K_a†
// ---------------------------------------------------------------------------

///|
/// 施加 Kraus 量子通道 `Φ(ρ) = Σ_a K_a ρ K_a†` 於量子概率態，保跡且保正定！
pub fn apply_cptp_channel(
  kraus_ops : Array[@unbounded.UnboundedOp],
  st : @unbounded.QuantumProbState,
) -> @unbounded.QuantumProbState? {
  let povm_dual = PovmMeasure::{ dim: st.dim, kraus_roots: kraus_ops, }
  if !povm_is_complete(povm_dual) {
    return None
  }
  let mut out_rho = @unbounded.uop_zero(st.dim)
  for k in kraus_ops {
    let term = @unbounded.uop_mul(
      k,
      @unbounded.uop_mul(st.rho, @unbounded.uop_adjoint(k)),
    )
    out_rho = @unbounded.uop_add(out_rho, term)
  }
  Some(@unbounded.QuantumProbState::{ dim: st.dim, rho: out_rho, })
}
