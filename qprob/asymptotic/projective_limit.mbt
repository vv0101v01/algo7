// ---------------------------------------------------------------------------
// qprob/asymptotic/projective_limit.mbt — 無窮漸近極限空間與加速收斂演算法
// ---------------------------------------------------------------------------
// 數學結構演變（第一階）：
//   有限截斷空間序列 `(V_k, π_{k,k+1})`
//     ──► 射影極限空間 `lim_← V_k`（相容執行緒 `π_{k,k+1}(x_{k+1}) = x_k`）
//     ──► 歸納極限空間 `lim_→ V_k`（嵌入等價類 `ι_{k,k+1}(x_k) ~ x_{k+1}`）
//     ──► Cauchy-漸近極限商空間 `𝒜 / ℐ_0`（有界漸近序列模無窮小理想）
//   由此導出：
//     - [定理 1.1] 射影相容性與 Mittag-Leffler 滿射判準；
//     - [定理 1.2] 標準部函子 `st : ℚ[[ε]] → ℚ` 是保序環同態且核恰為無窮小理想；
//     - [演算法 1.A] 精確 Neville–Richardson 多項式漸近外推（消除 `O(N^{-1})..O(N^{-m})`）；
//     - [演算法 1.B] 精確 Shanks–Aitken `Δ²` 非線性序列變換（對一階幾何暫態一步精確命中極限）；
//     - [演算法 1.C] Cesàro 算術平均極限與振盪序列正則化。

///|
/// 射影系（Inverse / Projective System）：
/// 第 `k` 層維度為 `dims[k]`，投射矩陣 `maps[k]` 將 `V_{k+1}` 線性映至 `V_k`
/// （大小 `dims[k] × dims[k+1]`，row-major）。
pub(all) struct ProjectiveTower {
  dims : Array[Int32]
  maps : Array[Array[QVal]]
}

///|
/// 矩陣乘向量（`rows × cols` 作用於長度 `cols` 的向量）。
pub fn qmat_vec_mul(
  mat : Array[QVal],
  rows : Int32,
  cols : Int32,
  vec : Array[QVal],
) -> Array[QVal] {
  guard rows >= 0 &&
    cols >= 0 &&
    mat.length() == rows * cols &&
    vec.length() == cols else {
    abort("qmat_vec_mul: dimension mismatch")
  }
  qmat_mul(mat, rows, cols, vec, 1)
}

///|
/// 矩陣乘法 `(r × m) · (m × c) = (r × c)`。
pub fn qmat_mul(
  a : Array[QVal],
  r : Int32,
  m : Int32,
  b : Array[QVal],
  c : Int32,
) -> Array[QVal] {
  guard r >= 0 && m >= 0 && c >= 0 && a.length() == r * m && b.length() == m * c else {
    abort("qmat_mul: dimension mismatch")
  }
  let out = Array::make(r * c, qv_zero())
  for i in 0..<r {
    for k in 0..<m {
      let aik = a[i * m + k]
      if !qv_is_zero(aik) {
        for j in 0..<c {
          let idx = i * c + j
          out[idx] = qv_add(out[idx], qv_mul(aik, b[k * c + j]))
        }
      }
    }
  }
  out
}

///|
/// 精確有理矩陣秩（高斯消元行階梯形），供 Mittag-Leffler 滿射與算子核維數計算。
pub fn qmat_rank(mat : Array[QVal], rows : Int32, cols : Int32) -> Int32 {
  guard rows >= 0 && cols >= 0 && mat.length() == rows * cols else {
    abort("qmat_rank: dimension mismatch")
  }
  let work = [ for x in mat => x ]
  let mut rank = 0
  let mut col = 0
  while rank < rows && col < cols {
    let mut pivot = -1
    for r in rank..<rows {
      if !qv_is_zero(work[r * cols + col]) {
        pivot = r
        break
      }
    }
    if pivot < 0 {
      col = col + 1
      continue
    }
    if pivot != rank {
      for j in col..<cols {
        let tmp = work[rank * cols + j]
        work[rank * cols + j] = work[pivot * cols + j]
        work[pivot * cols + j] = tmp
      }
    }
    guard qv_inv(work[rank * cols + col]) is Some(inv_p) else {
      col = col + 1
      continue
    }
    for j in col..<cols {
      work[rank * cols + j] = qv_mul(work[rank * cols + j], inv_p)
    }
    for r in (rank + 1)..<rows {
      let factor = work[r * cols + col]
      if !qv_is_zero(factor) {
        for j in col..<cols {
          work[r * cols + j] = qv_sub(
            work[r * cols + j],
            qv_mul(factor, work[rank * cols + j]),
          )
        }
      }
    }
    rank = rank + 1
    col = col + 1
  }
  rank
}

///|
/// 標準截斷射影塔：`V_k = ℚ^{dims[k]}`，`π_{k,k+1}` 保留前 `dims[k]` 個座標（Fock 截斷原型）。
pub fn tower_canonical_truncation(dims : Array[Int32]) -> ProjectiveTower {
  let maps : Array[Array[QVal]] = []
  for k in 0..<(dims.length() - 1) {
    let r = dims[k]
    let c = dims[k + 1]
    let m = Array::make(r * c, qv_zero())
    for i in 0..<r {
      if i < c {
        m[i * c + i] = qv_one()
      }
    }
    maps.push(m)
  }
  ProjectiveTower::{ dims, maps, }
}

///|
/// 檢查序列 `thread[k] ∈ V_k` 是否屬於射影極限 `lim_← V_k`：
/// 對所有 `k`，必須滿足相容性方程 `π_{k,k+1}(thread[k+1]) = thread[k]`。
pub fn tower_is_coherent_thread(
  tower : ProjectiveTower,
  thread : Array[Array[QVal]],
) -> Bool {
  if thread.length() != tower.dims.length() {
    return false
  }
  for k in 0..<tower.dims.length() {
    if thread[k].length() != tower.dims[k] {
      return false
    }
  }
  for k in 0..<tower.maps.length() {
    let projected = qmat_vec_mul(
      tower.maps[k],
      tower.dims[k],
      tower.dims[k + 1],
      thread[k + 1],
    )
    if !qv_vec_eq(projected, thread[k]) {
      return false
    }
  }
  true
}

///|
/// 計算複合轉移映射 `π_{i, j} = π_{i, i+1} ∘ ... ∘ π_{j-1, j} : V_j → V_i`（`0 ≤ i ≤ j < tower.dims.length()`）。
pub fn tower_transition(
  tower : ProjectiveTower,
  i : Int32,
  j : Int32,
) -> Array[QVal] {
  guard i >= 0 &&
    j >= i &&
    j < tower.dims.length() &&
    tower.maps.length() + 1 == tower.dims.length() else {
    abort("tower_transition: invalid level range")
  }
  if i == j {
    let d = tower.dims[i]
    let id = Array::make(d * d, qv_zero())
    for k in 0..<d {
      id[k * d + k] = qv_one()
    }
    return id
  }
  let mut cur = tower.maps[j - 1]
  let mut cur_rows = tower.dims[j - 1]
  let cols = tower.dims[j]
  let mut step = j - 2
  while step >= i {
    cur = qmat_mul(tower.maps[step], tower.dims[step], cur_rows, cur, cols)
    cur_rows = tower.dims[step]
    step = step - 1
  }
  cur
}

///|
/// Mittag-Leffler 穩定性檢驗：對第 `i` 層，序列 `Im(π_{i,j}) ⊆ V_i` 的維度隨 `j ≥ i` 單調遞減並穩定；
/// 回傳穩定像維度 `dim(∩_{j≥i} Im(π_{i,j}))`。當每一層投射皆滿射時，穩定維度恆等於 `dims[i]`（`R¹lim = 0`）。
pub fn tower_mittag_leffler_stable_rank(
  tower : ProjectiveTower,
  level : Int32,
) -> Int32 {
  let top = tower.dims.length() - 1
  let trans = tower_transition(tower, level, top)
  qmat_rank(trans, tower.dims[level], tower.dims[top])
}

// ---------------------------------------------------------------------------
// 演算法 1.A：精確 Richardson / Neville 漸近極限外推器
// ---------------------------------------------------------------------------
// 設序列在尺度 `N_i > 0`（步長 `h_i = 1 / N_i`）具有漸近展開：
//   A(N) = L + c_1 N^{-1} + c_2 N^{-2} + ... + c_m N^{-m} + O(N^{-(m+1)})
// 給定 `m + 1` 個不同尺度 `(N_0, A(N_0)), ..., (N_m, A(N_m))`，
// Neville 算法在 `h = 0` 處插值，精確消去全部前 `m` 階漸近誤差，一步給出極限 `L`！

///|
/// 精確 Neville–Richardson `h → 0` 漸近極限外推表；回傳最高階外推極限值。
pub fn richardson_extrapolate_limit(
  scales : Array[Int32],
  samples : Array[QVal],
) -> QVal? {
  let m = scales.length()
  if m == 0 || m != samples.length() {
    return None
  }
  let hs : Array[QVal] = []
  for s in scales {
    if s <= 0 {
      return None
    }
    hs.push(qv_frac(1, s))
  }
  let tbl = [ for v in samples => v ]
  for span in 1..<m {
    for i in 0..<(m - span) {
      let hi = hs[i]
      let hj = hs[i + span]
      let denom = qv_sub(hi, hj)
      guard qv_inv(denom) is Some(inv_d) else { return None }
      // T_{i, span}(0) = (h_i * T_{i+1, span-1} - h_{i+span} * T_{i, span-1}) / (h_i - h_{i+span})
      let num = qv_sub(qv_mul(hi, tbl[i + 1]), qv_mul(hj, tbl[i]))
      tbl[i] = qv_mul(num, inv_d)
    }
  }
  Some(tbl[0])
}

// ---------------------------------------------------------------------------
// 演算法 1.B：精確 Shanks–Aitken Δ² 與 Wynn ε-算法（Padé–Hankel 漸近加速）
// ---------------------------------------------------------------------------
// 1. 對單指數暫態 `s_n = L + α · r^n`（`r ≠ 1`），單步 Aitken `Δ²` 在任意三點精確命中 `L`。
// 2. 對一般 `K` 模態指數暫態 `s_n = L + Σ_{j=1}^K α_j r_j^n`，必須使用真正的 **Wynn ε-算法**
//    `ε_{-1}^{(n)} = 0`, `ε_0^{(n)} = s_n`,
//    `ε_{k+1}^{(n)} = ε_{k-1}^{(n+1)} + 1 / (ε_k^{(n+1)} - ε_k^{(n)})`！
//    定理（Shanks–Wynn）：`ε_{2K}^{(n)}` 在 `2K + 1` 個樣本點上**零誤差代數命中極限 `L`**！

///|
/// 單步 Aitken `Δ²` 加速變換（等價於 `ε_2^{(n)}`）：將長度 `k ≥ 3` 的序列壓縮為長度 `k - 2`。
pub fn shanks_aitken_step(seq : Array[QVal]) -> Array[QVal] {
  if seq.length() < 3 {
    return []
  }
  let out : Array[QVal] = []
  for n in 0..<(seq.length() - 2) {
    let s0 = seq[n]
    let s1 = seq[n + 1]
    let s2 = seq[n + 2]
    let d1 = qv_sub(s1, s0)
    let d2 = qv_add(qv_sub(s2, qv_add(s1, s1)), s0)
    match qv_inv(d2) {
      None => out.push(s2)
      Some(inv_d2) => out.push(qv_sub(s0, qv_mul(qv_mul(d1, d1), inv_d2)))
    }
  }
  out
}

///|
/// 精確 Wynn ε-算法菱形表：輸入長度 `2K + 1` 的序列，計算偶數列極限估計 `ε_{2K}^{(0)}`！
/// 對任意 `K` 模態幾何暫態和 `L + Σ_{j=1}^K α_j r_j^n` 實現**精確零誤差消去**！
pub fn wynn_epsilon_limit(seq : Array[QVal]) -> QVal? {
  let m = seq.length()
  if m == 0 {
    return None
  }
  if m == 1 {
    return Some(seq[0])
  }
  let mut eps_prev = Array::make(m + 1, qv_zero())
  let mut eps_cur = [ for x in seq => x ]
  let mut best_even = seq[m - 1]
  let mut k = 0
  while eps_cur.length() >= 2 {
    let next_len = eps_cur.length() - 1
    let eps_next = Array::make(next_len, qv_zero())
    for n in 0..<next_len {
      let diff = qv_sub(eps_cur[n + 1], eps_cur[n])
      guard qv_inv(diff) is Some(inv_diff) else { return None }
      eps_next[n] = qv_add(eps_prev[n + 1], inv_diff)
    }
    eps_prev = eps_cur
    eps_cur = eps_next
    k = k + 1
    if k % 2 == 0 {
      best_even = eps_cur[eps_cur.length() - 1]
    }
  }
  Some(best_even)
}

// ---------------------------------------------------------------------------
// 演算法 1.C：Cesàro 算術平均極限算子（消除有界振盪暫態）
// ---------------------------------------------------------------------------

///|
/// 計算序列前 `N` 項的精確 Cesàro 算術平均 `(1/N) Σ_{k=0}^{N-1} s_k`。
pub fn cesaro_mean(seq : Array[QVal]) -> QVal? {
  let n = seq.length()
  if n == 0 {
    return None
  }
  let mut sum = qv_zero()
  for x in seq {
    sum = qv_add(sum, x)
  }
  Some(qv_div(sum, qv_int(n)))
}
