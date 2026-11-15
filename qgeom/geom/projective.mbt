// ---------------------------------------------------------------------------
// qgeom/geom — 平移射影（translation-projective geometry）
// ---------------------------------------------------------------------------
// 仿射平移 `x ↦ x + t` 不是「射影變換」的自由選擇，而是**被強制的**：
// 它唯一的射影提升是齊次矩陣
//
//     M(t) = [[ I_n , t ],
//             [ 0   , 1 ]]
//
// 這支矩陣把無窮遠超平面 w = 0 送到自己（`proj_translation_keeps_infinity`），
// 在仿射圖 w = 1 上就是平移，且是拋物元素（`(M(t) − I)² = 0`、det = 1、
// 無限階）。交比是射影不變量，因此在 M(t) 下不變——而且因為它是用 2×2
// 行列式寫的，對任意 det ≠ 0 的分式線性映射都不變。
//
// 全部運算在 QQ 上精確進行：沒有「差不多等於」。

///|
/// 齊次座標是否代表零向量（零向量不是射影點）。
pub fn proj_is_zero(p : Array[@core.QQ]) -> Bool {
  let mut i = 0
  while i < p.length() {
    if !(@core.qq_is_zero(p[i])) {
      return false
    }
    i = i + 1
  }
  true
}

///|
/// 投影相等：存在 λ ≠ 0 使 p = λq。用交叉相乘判定，不需要先算 λ。
pub fn proj_eq(p : Array[@core.QQ], q : Array[@core.QQ]) -> Bool {
  if p.length() != q.length() {
    return false
  }
  if @core.qq_list_eq(p, q) {
    return true
  }
  // 找出兩邊各自的第一個非零分量，檢查全部交叉乘積
  let mut i = 0
  while i < p.length() {
    let mut j = 0
    while j < p.length() {
      if !(@core.qq_eq(
        @core.qq_mul(p[i], q[j]),
        @core.qq_mul(q[i], p[j]),
      )) {
        return false
      }
      j = j + 1
    }
    i = i + 1
  }
  true
}

///|
/// 仿射點 `x`（n 維）↦ 齊次點 `[x : 1]`。
pub fn proj_of_affine(x : Array[@core.QQ]) -> Array[@core.QQ] {
  let out : Array[@core.QQ] = []
  let mut i = 0
  while i < x.length() {
    out.push(x[i])
    i = i + 1
  }
  out.push(@core.qq_one())
  out
}

///|
/// 齊次點在仿射圖 `w = 1` 上的座標；`w = 0`（無窮遠）回傳 `None`。
pub fn proj_to_affine(p : Array[@core.QQ]) -> Array[@core.QQ]? {
  let n = p.length()
  if n < 2 {
    return None
  }
  let w = p[n - 1]
  if @core.qq_is_zero(w) {
    return None
  }
  let inv_w = @core.qq_div(@core.qq_one(), w)
  let out : Array[@core.QQ] = @core.qvec_zero(n - 1)
  let mut i = 0
  while i < n - 1 {
    out[i] = @core.qq_mul(p[i], inv_w)
    i = i + 1
  }
  Some(out)
}

///|
/// 平移的射影提升 `M(t) = [[I_n, t], [0, 1]]`（`(n+1) × (n+1)`）。
pub fn proj_translation_matrix(t : Array[@core.QQ]) -> Array[Array[@core.QQ]] {
  let n = t.length()
  let m = @core.qmat_zero(n + 1, n + 1)
  let mut i = 0
  while i < n {
    m[i][i] = @core.qq_one()
    m[i][n] = t[i]
    i = i + 1
  }
  m[n][n] = @core.qq_one()
  m
}

///|
/// 齊次線性作用 `p ↦ M·p`。
pub fn proj_apply(
  m : Array[Array[@core.QQ]],
  p : Array[@core.QQ],
) -> Array[@core.QQ]? {
  @core.qmat_vec(m, p)
}

///|
/// 二階行列式 `det2([a₀,a₁],[b₀,b₁])`：交比的基本積木。
pub fn proj_det2(a : Array[@core.QQ], b : Array[@core.QQ]) -> @core.QQ {
  @core.qq_sub(
    @core.qq_mul(a[0], b[1]),
    @core.qq_mul(a[1], b[0]),
  )
}

///|
/// 交比 `(a,b;c,d) = det(a,c)·det(b,d) / (det(a,d)·det(b,c))`。
/// 分母有意義時才有定義；分母為零（三點重合）回傳 `None`。
pub fn proj_cross_ratio(
  a : Array[@core.QQ],
  b : Array[@core.QQ],
  c : Array[@core.QQ],
  d : Array[@core.QQ],
) -> @core.QQ? {
  let ac = proj_det2(a, c)
  let bd = proj_det2(b, d)
  let ad = proj_det2(a, d)
  let bc = proj_det2(b, c)
  let den = @core.qq_mul(ad, bc)
  if @core.qq_is_zero(den) {
    return None
  }
  Some(@core.qq_div(@core.qq_mul(ac, bd), den))
}

///|
/// 分式線性（Möbius）矩陣 `[[α, β], [γ, δ]]`，作用於齊次點。
pub fn proj_mobius(
  alpha : @core.QQ,
  beta : @core.QQ,
  gamma : @core.QQ,
  delta : @core.QQ,
) -> Array[Array[@core.QQ]] {
  let m = @core.qmat_zero(2, 2)
  m[0][0] = alpha
  m[0][1] = beta
  m[1][0] = gamma
  m[1][1] = delta
  m
}

///|
/// 交比在分式線性映射下的像：`(Ma, Mb; Mc, Md)`。
pub fn proj_cross_ratio_image(
  m : Array[Array[@core.QQ]],
  a : Array[@core.QQ],
  b : Array[@core.QQ],
  c : Array[@core.QQ],
  d : Array[@core.QQ],
) -> @core.QQ? {
  let ma = match proj_apply(m, a) {
    Some(x) => x
    None => return None
  }
  let mb = match proj_apply(m, b) {
    Some(x) => x
    None => return None
  }
  let mc = match proj_apply(m, c) {
    Some(x) => x
    None => return None
  }
  let md = match proj_apply(m, d) {
    Some(x) => x
    None => return None
  }
  proj_cross_ratio(ma, mb, mc, md)
}

///|
/// 矩陣減單位矩陣。
pub fn proj_mat_minus_identity(m : Array[Array[@core.QQ]]) -> Array[Array[@core.QQ]] {
  let n = @core.qmat_rows(m)
  let id = @core.qmat_identity(n)
  @core.qmat_sub(m, id)
}

///|
/// 矩陣的 `k` 次方（`k ≥ 1`；`k = 0` 給單位矩陣）。
pub fn proj_mat_pow(m : Array[Array[@core.QQ]], k : Int32) -> Array[Array[@core.QQ]] {
  let n = @core.qmat_rows(m)
  let mut out = @core.qmat_identity(n)
  let mut step = 0
  while step < k {
    out = @core.qmat_mul_unchecked(out, m)
    step = step + 1
  }
  out
}

///|
/// 平移矩陣的轉置反矩陣 `M(t)^{-ᵗ} = [[I, 0], [−tᵗ, 1]]`（用於關聯性保持）。
pub fn proj_translation_inverse_transpose(
  t : Array[@core.QQ],
) -> Array[Array[@core.QQ]] {
  let n = t.length()
  let m = @core.qmat_zero(n + 1, n + 1)
  let mut i = 0
  while i < n {
    m[i][i] = @core.qq_one()
    m[n][i] = @core.qq_neg(t[i])
    i = i + 1
  }
  m[n][n] = @core.qq_one()
  m
}

///|
/// 齊次線性方程 `Lᵗp = 0` 是否成立（點 `p` 在超平面／直線 `L` 上）。
pub fn proj_incident(line : Array[@core.QQ], p : Array[@core.QQ]) -> Bool {
  @core.qq_is_zero(@core.qvec_dot(line, p))
}
