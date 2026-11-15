// ---------------------------------------------------------------------------
// qgeom/core — 四元數 H（係數在 QQ 上）
// ---------------------------------------------------------------------------
// 這裡的四元數是定義在精確有理數體上的 Hurwitz 四元數：`i² = j² = k² = ijk = -1`。
// 每個代數性質都不是引用課本，而是在 `law_quaternion_ring` 裡用具體元素重算：
// 結合律、分配律、非交換見證、共軛反自同構、範數的乘法性、無零因子，
// 以及左正則表示是同態（`L(a)L(b) = L(ab)`）。
//
// `quat_left_mat`／`quat_right_mat` 把四元數變成 QQ 上的 4×4 矩陣；四元數凱勒
// 流形的 I/J/K 結構與「雙射緊緻四元雅可比簇」的整數週期矩陣都由此長出來。

///|
/// 四元數 `re + i·i + j·j + k·k`（欄位名稱用 `qi`/`qj`/`qk`，避免與單位元同名）。
pub(all) struct Quat {
  re : QQ
  qi : QQ
  qj : QQ
  qk : QQ
}

///|
pub fn quat_make(re : QQ, qi : QQ, qj : QQ, qk : QQ) -> Quat {
  Quat::{ re: re, qi: qi, qj: qj, qk: qk }
}

///|
pub fn quat_of_int(a : Int32, b : Int32, c : Int32, d : Int32) -> Quat {
  quat_make(qq_int(a), qq_int(b), qq_int(c), qq_int(d))
}

///|
pub fn quat_of_qq(a : QQ) -> Quat {
  quat_make(a, qq_zero(), qq_zero(), qq_zero())
}

///|
pub fn quat_zero() -> Quat {
  quat_of_int(0, 0, 0, 0)
}

///|
pub fn quat_one() -> Quat {
  quat_of_int(1, 0, 0, 0)
}

///|
pub fn quat_i() -> Quat {
  quat_of_int(0, 1, 0, 0)
}

///|
pub fn quat_j() -> Quat {
  quat_of_int(0, 0, 1, 0)
}

///|
pub fn quat_k() -> Quat {
  quat_of_int(0, 0, 0, 1)
}

///|
pub fn quat_add(a : Quat, b : Quat) -> Quat {
  quat_make(
    qq_add(a.re, b.re),
    qq_add(a.qi, b.qi),
    qq_add(a.qj, b.qj),
    qq_add(a.qk, b.qk),
  )
}

///|
pub fn quat_sub(a : Quat, b : Quat) -> Quat {
  quat_make(
    qq_sub(a.re, b.re),
    qq_sub(a.qi, b.qi),
    qq_sub(a.qj, b.qj),
    qq_sub(a.qk, b.qk),
  )
}

///|
pub fn quat_neg(a : Quat) -> Quat {
  quat_make(qq_neg(a.re), qq_neg(a.qi), qq_neg(a.qj), qq_neg(a.qk))
}

///|
pub fn quat_scale(s : QQ, a : Quat) -> Quat {
  quat_make(
    qq_mul(s, a.re),
    qq_mul(s, a.qi),
    qq_mul(s, a.qj),
    qq_mul(s, a.qk),
  )
}

///|
/// Hamilton 乘法。
pub fn quat_mul(a : Quat, b : Quat) -> Quat {
  let re = qq_sub(
    qq_sub(qq_mul(a.re, b.re), qq_mul(a.qi, b.qi)),
    qq_add(qq_mul(a.qj, b.qj), qq_mul(a.qk, b.qk)),
  )
  let qi = qq_add(
    qq_add(qq_mul(a.re, b.qi), qq_mul(a.qi, b.re)),
    qq_sub(qq_mul(a.qj, b.qk), qq_mul(a.qk, b.qj)),
  )
  let qj = qq_add(
    qq_sub(qq_mul(a.re, b.qj), qq_mul(a.qi, b.qk)),
    qq_add(qq_mul(a.qj, b.re), qq_mul(a.qk, b.qi)),
  )
  let qk = qq_add(
    qq_add(qq_mul(a.re, b.qk), qq_mul(a.qi, b.qj)),
    qq_add(qq_sub(qq_zero(), qq_mul(a.qj, b.qi)), qq_mul(a.qk, b.re)),
  )
  quat_make(re, qi, qj, qk)
}

///|
pub fn quat_conj(a : Quat) -> Quat {
  quat_make(a.re, qq_neg(a.qi), qq_neg(a.qj), qq_neg(a.qk))
}

///|
/// 範數平方 `N(a) = a·ā = re² + i² + j² + k²`（Lagrange 四平方恆等式的左邊）。
pub fn quat_norm(a : Quat) -> QQ {
  qq_add(
    qq_add(qq_mul(a.re, a.re), qq_mul(a.qi, a.qi)),
    qq_add(qq_mul(a.qj, a.qj), qq_mul(a.qk, a.qk)),
  )
}

///|
pub fn quat_eq(a : Quat, b : Quat) -> Bool {
  qq_eq(a.re, b.re) && qq_eq(a.qi, b.qi) && qq_eq(a.qj, b.qj) && qq_eq(a.qk, b.qk)
}

///|
pub fn quat_is_zero(a : Quat) -> Bool {
  qq_is_zero(quat_norm(a))
}

///|
/// 乘法反元素 `ā / N(a)`；只有零沒有反元素。
pub fn quat_inv(a : Quat) -> Quat? {
  let n = quat_norm(a)
  if qq_is_zero(n) {
    None
  } else {
    let inv_n = qq_div(qq_one(), n)
    Some(quat_scale(inv_n, quat_conj(a)))
  }
}

///|
/// 實部（四元數的「純量部分」）；對四元數矩陣的跡取實部時用到。
pub fn quat_re(a : Quat) -> QQ {
  a.re
}

///|
pub fn quat_show(a : Quat) -> String {
  "(" +
  qq_show(a.re) +
  "," +
  qq_show(a.qi) +
  "," +
  qq_show(a.qj) +
  "," +
  qq_show(a.qk) +
  ")"
}

// ---------------------------------------------------------------------------
// 左／右正則表示：四元數 ↪ QQ 上的 4×4 矩陣
// ---------------------------------------------------------------------------

///|
/// 單位元 `e_j`（`j = 0..3` 對應 `1, i, j, k`）。
pub fn quat_basis(j : Int32) -> Quat {
  if j == 0 {
    quat_one()
  } else if j == 1 {
    quat_i()
  } else if j == 2 {
    quat_j()
  } else {
    quat_k()
  }
}

///|
/// 把四元數寫成 4 維列向量 `[re, i, j, k]`。
pub fn quat_to_vec(a : Quat) -> Array[QQ] {
  [a.re, a.qi, a.qj, a.qk]
}

///|
/// 左乘表示 `L(q)`：第 `j` 欄是 `q·e_j` 的分量。`L(q)·x` 等於 `q·x`。
pub fn quat_left_mat(q : Quat) -> Array[Array[QQ]] {
  let out = qmat_zero(4, 4)
  let mut j = 0
  while j < 4 {
    let col = quat_to_vec(quat_mul(q, quat_basis(j)))
    let mut i = 0
    while i < 4 {
      out[i][j] = col[i]
      i = i + 1
    }
    j = j + 1
  }
  out
}

///|
/// 右乘表示 `R(q)`：`R(q)·x` 等於 `x·q`。
pub fn quat_right_mat(q : Quat) -> Array[Array[QQ]] {
  let out = qmat_zero(4, 4)
  let mut j = 0
  while j < 4 {
    let col = quat_to_vec(quat_mul(quat_basis(j), q))
    let mut i = 0
    while i < 4 {
      out[i][j] = col[i]
      i = i + 1
    }
    j = j + 1
  }
  out
}

// ---------------------------------------------------------------------------
// 四元數矩陣（用於超對稱代數與 sp(n) 模型）
// ---------------------------------------------------------------------------

///|
pub fn qm_zero(r : Int32, c : Int32) -> Array[Array[Quat]] {
  let out : Array[Array[Quat]] = Array::make(r, Array::make(0, quat_zero()))
  let mut i = 0
  while i < r {
    out[i] = Array::make(c, quat_zero())
    i = i + 1
  }
  out
}

///|
pub fn qm_rows(m : Array[Array[Quat]]) -> Int32 {
  m.length()
}

///|
pub fn qm_cols(m : Array[Array[Quat]]) -> Int32 {
  if m.length() == 0 {
    0
  } else {
    m[0].length()
  }
}

///|
pub fn qm_add(a : Array[Array[Quat]], b : Array[Array[Quat]]) -> Array[Array[Quat]] {
  let out = qm_zero(qm_rows(a), qm_cols(a))
  let mut i = 0
  while i < qm_rows(a) {
    let mut j = 0
    while j < qm_cols(a) {
      out[i][j] = quat_add(a[i][j], b[i][j])
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
pub fn qm_sub(a : Array[Array[Quat]], b : Array[Array[Quat]]) -> Array[Array[Quat]] {
  let out = qm_zero(qm_rows(a), qm_cols(a))
  let mut i = 0
  while i < qm_rows(a) {
    let mut j = 0
    while j < qm_cols(a) {
      out[i][j] = quat_sub(a[i][j], b[i][j])
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
pub fn qm_neg(a : Array[Array[Quat]]) -> Array[Array[Quat]] {
  let out = qm_zero(qm_rows(a), qm_cols(a))
  let mut i = 0
  while i < qm_rows(a) {
    let mut j = 0
    while j < qm_cols(a) {
      out[i][j] = quat_neg(a[i][j])
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
/// 四元數矩陣乘法（維度不符回傳 `None`）。
pub fn qm_mul(a : Array[Array[Quat]], b : Array[Array[Quat]]) -> Array[Array[Quat]]? {
  if qm_cols(a) != qm_rows(b) {
    return None
  }
  let out = qm_zero(qm_rows(a), qm_cols(b))
  let mut i = 0
  while i < qm_rows(a) {
    let mut j = 0
    while j < qm_cols(b) {
      let mut acc = quat_zero()
      let mut k = 0
      while k < qm_cols(a) {
        acc = quat_add(acc, quat_mul(a[i][k], b[k][j]))
        k = k + 1
      }
      out[i][j] = acc
      j = j + 1
    }
    i = i + 1
  }
  Some(out)
}

///|
pub fn qm_mul_unchecked(a : Array[Array[Quat]], b : Array[Array[Quat]]) -> Array[Array[Quat]] {
  match qm_mul(a, b) {
    Some(m) => m
    None => qm_zero(qm_rows(a), qm_cols(b))
  }
}

///|
/// 共軛轉置 `X†`（四元數矩陣的伴隨）。
pub fn qm_conj_transpose(a : Array[Array[Quat]]) -> Array[Array[Quat]] {
  let out = qm_zero(qm_cols(a), qm_rows(a))
  let mut i = 0
  while i < qm_rows(a) {
    let mut j = 0
    while j < qm_cols(a) {
      out[j][i] = quat_conj(a[i][j])
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
pub fn qm_eq(a : Array[Array[Quat]], b : Array[Array[Quat]]) -> Bool {
  if qm_rows(a) != qm_rows(b) || qm_cols(a) != qm_cols(b) {
    return false
  }
  let mut i = 0
  while i < qm_rows(a) {
    let mut j = 0
    while j < qm_cols(a) {
      if !(quat_eq(a[i][j], b[i][j])) {
        return false
      }
      j = j + 1
    }
    i = i + 1
  }
  true
}

///|
pub fn qm_trace(a : Array[Array[Quat]]) -> Quat {
  let n = if qm_rows(a) < qm_cols(a) { qm_rows(a) } else { qm_cols(a) }
  let mut acc = quat_zero()
  let mut i = 0
  while i < n {
    acc = quat_add(acc, a[i][i])
    i = i + 1
  }
  acc
}

///|
/// 四元數矩陣的 Hermitian 內積的實部 `Σ_ij Re(conj(X_ij)·Y_ij)`：
/// 正定、對稱、實值。超對稱頂點的對偶配對就用它。
pub fn qm_hermitian_re(a : Array[Array[Quat]], b : Array[Array[Quat]]) -> QQ {
  let mut acc = qq_zero()
  let mut i = 0
  while i < qm_rows(a) {
    let mut j = 0
    while j < qm_cols(a) {
      acc = qq_add(acc, quat_re(quat_mul(quat_conj(a[i][j]), b[i][j])))
      j = j + 1
    }
    i = i + 1
  }
  acc
}
