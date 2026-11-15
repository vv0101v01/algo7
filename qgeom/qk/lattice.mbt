// ---------------------------------------------------------------------------
// qgeom/qk/lattice — 雙射緊緻四元雅可比簇（bijective compact quaternionic torus）
// ---------------------------------------------------------------------------
// 一個複環面是 `C^g / Λ`；四元數的類比是 `H^g / Λ`（實維數 `4g`）。
// 「緊緻」不是形容詞：它來自 `Λ` 是**秩 4g 的格子**，而四元數結構
// `I, J, K` 必須把格子送到自己（否則 `I` 根本下降不到商空間）。
//
// 「雙射」在這裡是三個可判定的條件：
//   * `I, J, K` 是**整數**矩陣（格子不變）；
//   * `det = 1`（單模 ⇒ 把 `Z^{4g}` 雙射到自己）；
//   * `Iᵗ δ I = δ`（恆等張量不變）——於是 `I` 是格子的自同構。
//
// 「恆等張量幾何矩陣」則是極化形式 `Ω`：整數、反對稱、單模，且在
// `Sp(2g, Z)` 的分塊生成元下不變（`Θ(Mx, My) = Θ(x, y)`，逐個基底對檢查）。
//
// 這一支只用 `qgeom/core` 的精確代數：沒有任何浮點近似。

///|
/// 左乘虛單位的 4×4 實矩陣：`I = L(i)`、`J = L(j)`、`K = L(k)`（`j = 1, 2, 3`）。
pub fn ql_structure(j : Int32) -> Array[Array[@core.QQ]] {
  @core.quat_left_mat(@core.quat_basis(j))
}

///|
/// 矩陣的每個元素是否都是整數。
pub fn ql_is_integral(m : Array[Array[@core.QQ]]) -> Bool {
  let mut i = 0
  while i < @core.qmat_rows(m) {
    let mut j = 0
    while j < @core.qmat_cols(m) {
      if m[i][j].den != 1N {
        return false
      }
      j = j + 1
    }
    i = i + 1
  }
  true
}

///|
/// 極化形式 `Ω = dx₀∧dx₁ + dx₂∧dx₃`（4×4，整數、反對稱、單模）。
pub fn ql_polarization(g : Int32) -> Array[Array[@core.QQ]] {
  let n = 4 * g
  let out = @core.qmat_zero(n, n)
  let mut b = 0
  while b < g {
    let off = 4 * b
    out[off][off + 1] = @core.qq_one()
    out[off + 1][off] = @core.qq_int(-1)
    out[off + 2][off + 3] = @core.qq_one()
    out[off + 3][off + 2] = @core.qq_int(-1)
    b = b + 1
  }
  out
}

///|
/// 形式求值 `Ω(X, Y) = Xᵗ Ω Y`。
pub fn ql_form(
  omega : Array[Array[@core.QQ]],
  x : Array[@core.QQ],
  y : Array[@core.QQ],
) -> @core.QQ {
  let wx = @core.qmat_vec_unchecked(omega, y)
  @core.qvec_dot(x, wx)
}

///|
/// 四元數 Hermitian 形式 `h(X,Y) = ⟨X,Y⟩ + i⟨IX,Y⟩ + j⟨JX,Y⟩ + k⟨KX,Y⟩`。
///
/// 這就是四元數的 `conj(X)·Y` 展開：實部是歐氏度量，三個虛部是三個
/// 「Kähler 形式」`ω_a(X,Y) = ⟨aX, Y⟩`。`a = I` 的那一個正好等於極化形式
/// `Ω(X,Y) = ⟨IX, Y⟩`——這件事在 `law_qk_identity_tensor` 裡當場核對。
pub fn ql_hermitian(x : Array[@core.QQ], y : Array[@core.QQ]) -> @core.Quat {
  let real = @core.qvec_dot(x, y)
  let ix = @core.qmat_vec_unchecked(ql_structure(1), x)
  let jx = @core.qmat_vec_unchecked(ql_structure(2), x)
  let kx = @core.qmat_vec_unchecked(ql_structure(3), x)
  @core.quat_make(
    real,
    @core.qvec_dot(ix, y),
    @core.qvec_dot(jx, y),
    @core.qvec_dot(kx, y),
  )
}

///|
/// `I` 作用在向量上（`Ω(X,Y) = ⟨IX, Y⟩` 的核對用）。
pub fn ql_I(x : Array[@core.QQ]) -> Array[@core.QQ] {
  @core.qmat_vec_unchecked(ql_structure(1), x)
}

///|
/// 分塊對角 `diag(a, b)`（`a`、`b` 同尺寸）。
pub fn ql_block_diag(
  a : Array[Array[@core.QQ]],
  b : Array[Array[@core.QQ]],
) -> Array[Array[@core.QQ]] {
  let na = @core.qmat_rows(a)
  let nb = @core.qmat_rows(b)
  let out = @core.qmat_zero(na + nb, na + nb)
  let mut i = 0
  while i < na {
    let mut j = 0
    while j < na {
      out[i][j] = a[i][j]
      j = j + 1
    }
    i = i + 1
  }
  i = 0
  while i < nb {
    let mut j = 0
    while j < nb {
      out[na + i][na + j] = b[i][j]
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
/// `g` 個副本的 `4×4` 結構矩陣分塊對角（`H^g` 上的 `I, J, K`）。
pub fn ql_structure_g(j : Int32, g : Int32) -> Array[Array[@core.QQ]] {
  let block = ql_structure(j)
  let mut out = block
  let mut b = 1
  while b < g {
    out = ql_block_diag(out, block)
    b = b + 1
  }
  out
}

///|
/// `Sp(2g, Z)` 的分塊生成元：`diag(A, B)`，`A, B ∈ SL(2, Z)`。
pub fn ql_symplectic_generator(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[@core.QQ]] {
  ql_block_diag(@core.qmat_from_int(a), @core.qmat_from_int(b))
}

///|
/// `SL(2, Z)` 的四個常用元素：`S`、`T`、`T⁻¹`、`ST`。
pub fn ql_sl2z_samples() -> Array[Array[Array[Int32]]] {
  [[[0, 1], [-1, 0]], [[1, 1], [0, 1]], [[1, -1], [0, 1]], [[1, 1], [-1, 0]]]
}

///|
/// 一個格點盒子 `[−r, r]^{n}` 的所有整數點（以 QQ 向量表示）。
pub fn ql_box_points(n : Int32, r : Int32) -> Array[Array[@core.QQ]] {
  let out : Array[Array[@core.QQ]] = []
  let side = 2 * r + 1
  let total = {
    let mut s = 1
    let mut i = 0
    while i < n {
      s = s * side
      i = i + 1
    }
    s
  }
  let mut lin = 0
  while lin < total {
    let v : Array[@core.QQ] = Array::make(n, @core.qq_zero())
    let mut rem = lin
    let mut i = 0
    while i < n {
      let digit = rem % side
      v[i] = @core.qq_int(digit - r)
      rem = rem / side
      i = i + 1
    }
    out.push(v)
    lin = lin + 1
  }
  out
}

///|
/// 布林向量比較（點是否相同）。
pub fn ql_pt_eq(a : Array[@core.QQ], b : Array[@core.QQ]) -> Bool {
  @core.qq_list_eq(a, b)
}
