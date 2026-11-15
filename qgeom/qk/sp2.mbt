// ---------------------------------------------------------------------------
// qgeom/qk/sp2 — 四元數凱勒流形的「曲率張量群空間」：sp(2) 與其 Cartan 分解
// ---------------------------------------------------------------------------
// 四元數凱勒流形（quaternionic Kähler）的核心代數事實是：
// 它的曲率算子落在 `sp(1) ⊕ sp(n)` 裡，而 `sp(1)` 的部分就是三個
// 相容複結構 I、J、K 的「群空間」。最小模型是四元數射影線
//
//     HP¹ = Sp(2) / (Sp(1) × Sp(1)) ≅ S⁴,
//
// 這裡把它完全算出來：
//
//   * `sp(2) = {X : X† = −X}`（四元數 2×2 矩陣，實維數 10）；
//   * Cartan 分解 `sp(2) = k ⊕ m`，`k = sp(1) ⊕ sp(1)`（分塊對角，6 維）、
//     `m`（分塊非對角，4 維，就是切空間 `H`）；
//   * 曲率 `R(X,Y)Z = −[[X,Y],Z]`（對稱空間公式），它落在 `m` 裡，
//     而且**作為算子它屬於 k**——這就是「曲率張量群空間」的可計算內容；
//   * `k` 的兩個 `sp(1)` 因子在 `m ≅ H` 上分別是左乘與右乘虛四元數，
//     於是 I、J、K 滿足 `I² = J² = K² = IJK = −1`。
//
// 全部用精確有理數與四元數計算，沒有一條定律是「相信課本」。

///|
/// 四元數 2×2 矩陣的 Hamilton 交換子 `[X,Y] = XY − YX`。
pub fn sp2_bracket(
  x : Array[Array[@core.Quat]],
  y : Array[Array[@core.Quat]],
) -> Array[Array[@core.Quat]] {
  let xy = @core.qm_mul_unchecked(x, y)
  let yx = @core.qm_mul_unchecked(y, x)
  @core.qm_sub(xy, yx)
}

///|
/// `X†`（共軛轉置）是否等於 `−X`：`X ∈ sp(2)` 的判據。
pub fn sp2_is_skew(x : Array[Array[@core.Quat]]) -> Bool {
  @core.qm_eq(@core.qm_conj_transpose(x), @core.qm_neg(x))
}

///|
/// 把四元數 2×2 矩陣攤成 16 個 QQ 分量（實座標），用於「是否落在子空間」的判定。
pub fn sp2_flatten(m : Array[Array[@core.Quat]]) -> Array[@core.QQ] {
  let out : Array[@core.QQ] = Array::make(16, @core.qq_zero())
  let mut i = 0
  while i < 2 {
    let mut j = 0
    while j < 2 {
      let q = m[i][j]
      out[(i * 2 + j) * 4] = q.re
      out[(i * 2 + j) * 4 + 1] = q.qi
      out[(i * 2 + j) * 4 + 2] = q.qj
      out[(i * 2 + j) * 4 + 3] = q.qk
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
/// `sp(2)` 的 10 個基底元素：
/// `sp(1)_L = span{X₁,X₂,X₃}`、`sp(1)_R = span{Y₁,Y₂,Y₃}`、`m = span{M₀..M₃}`。
/// 寫法：`X_a = diag(σ_a, 0)`、`Y_a = diag(0, σ_a)`、`M_b = [[0, b], [−conj(b), 0]]`。
pub fn sp2_basis() -> Array[Array[Array[@core.Quat]]] {
  let out : Array[Array[Array[@core.Quat]]] = []
  // sp(1)_L
  let mut a = 1
  while a <= 3 {
    let m = @core.qm_zero(2, 2)
    m[0][0] = @core.quat_basis(a)
    out.push(m)
    a = a + 1
  }
  // sp(1)_R
  a = 1
  while a <= 3 {
    let m = @core.qm_zero(2, 2)
    m[1][1] = @core.quat_basis(a)
    out.push(m)
    a = a + 1
  }
  // m：M_b = [[0, b], [−conj(b), 0]]
  a = 0
  while a <= 3 {
    let b = @core.quat_basis(a)
    let m = @core.qm_zero(2, 2)
    m[0][1] = b
    m[1][0] = @core.quat_neg(@core.quat_conj(b))
    out.push(m)
    a = a + 1
  }
  out
}

///|
/// `k = sp(1) ⊕ sp(1)` 的 6 個基底（分塊對角）。
pub fn sp2_k_basis() -> Array[Array[Array[@core.Quat]]] {
  let all = sp2_basis()
  let out : Array[Array[Array[@core.Quat]]] = []
  let mut i = 0
  while i < 6 {
    out.push(all[i])
    i = i + 1
  }
  out
}

///|
/// `m` 的 4 個基底（分塊非對角，切空間）。
pub fn sp2_m_basis() -> Array[Array[Array[@core.Quat]]] {
  let all = sp2_basis()
  let out : Array[Array[Array[@core.Quat]]] = []
  let mut i = 6
  while i < 10 {
    out.push(all[i])
    i = i + 1
  }
  out
}

///|
/// 在給定基底下的座標（以 16 維實向量攤平求解）；不在張成空間裡回傳 `None`。
pub fn sp2_coords(
  basis : Array[Array[Array[@core.Quat]]],
  x : Array[Array[@core.Quat]],
) -> Array[@core.QQ]? {
  let flat : Array[Array[@core.QQ]] = []
  let mut i = 0
  while i < basis.length() {
    flat.push(sp2_flatten(basis[i]))
    i = i + 1
  }
  @core.qmat_span_coords(flat, sp2_flatten(x))
}

///|
/// 四元數矩陣的 Hermitian 內積實部（`sp(2)` 上的 Killing 型替代：正定、Ad-不變的
/// 實內積在 `X† = −X` 上就是 `−Re tr(XY)`，這裡直接用正定版本 `Re tr(X†Y)`）。
pub fn sp2_inner(
  x : Array[Array[@core.Quat]],
  y : Array[Array[@core.Quat]],
) -> @core.QQ {
  @core.qm_hermitian_re(x, y)
}

///|
/// 對稱空間曲率 `R(X,Y)Z = −[[X,Y],Z]`。
pub fn sp2_curvature(
  x : Array[Array[@core.Quat]],
  y : Array[Array[@core.Quat]],
  z : Array[Array[@core.Quat]],
) -> Array[Array[@core.Quat]] {
  @core.qm_neg(sp2_bracket(sp2_bracket(x, y), z))
}

///|
/// 把 `m ≅ H` 的識別寫出來：`M_b ↔ b`（讀出右上角那個四元數）。
pub fn sp2_m_of_quat(b : @core.Quat) -> Array[Array[@core.Quat]] {
  let m = @core.qm_zero(2, 2)
  m[0][1] = b
  m[1][0] = @core.quat_neg(@core.quat_conj(b))
  m
}

///|
/// 左乘虛四元數 `L_u(v) = u·v`（`u` 為虛單位）：四元數凱勒結構的 `I`、`J`、`K`。
pub fn sp2_left_mul(u : @core.Quat, v : @core.Quat) -> @core.Quat {
  @core.quat_mul(u, v)
}

///|
/// 右乘 `R_u(v) = v·u`。
pub fn sp2_right_mul(u : @core.Quat, v : @core.Quat) -> @core.Quat {
  @core.quat_mul(v, u)
}
