// ---------------------------------------------------------------------------
// qgeom/core — QQ 上的精確線性代數（向量、矩陣、秩、行列式、座標解）
// ---------------------------------------------------------------------------
// 只實作整個聯邦真正會用到的部分：矩陣乘、轉置、秩（精確高斯消去）、
// 行列式（同一支消去法的乘積形式）、跡、以及在給定生成向量下求座標
// （李代數結構常數、對偶配對、張量積滿射性都靠它）。
//
// 全部是精確運算：`qmat_rank` 回傳的是「精確秩」，沒有 eps、沒有隨機取樣。

///|
pub fn qmat_rows(m : Array[Array[QQ]]) -> Int32 {
  m.length()
}

///|
pub fn qmat_cols(m : Array[Array[QQ]]) -> Int32 {
  if m.length() == 0 {
    0
  } else {
    m[0].length()
  }
}

///|
pub fn qmat_zero(r : Int32, c : Int32) -> Array[Array[QQ]] {
  let out : Array[Array[QQ]] = Array::make(r, Array::make(0, qq_zero()))
  let mut i = 0
  while i < r {
    out[i] = Array::make(c, qq_zero())
    i = i + 1
  }
  out
}

///|
pub fn qmat_identity(n : Int32) -> Array[Array[QQ]] {
  let out = qmat_zero(n, n)
  let mut i = 0
  while i < n {
    out[i][i] = qq_one()
    i = i + 1
  }
  out
}

///|
pub fn qmat_from_int(rows : Array[Array[Int32]]) -> Array[Array[QQ]] {
  let out : Array[Array[QQ]] = Array::make(rows.length(), Array::make(0, qq_zero()))
  let mut i = 0
  while i < rows.length() {
    let row = rows[i]
    let new_row : Array[QQ] = Array::make(row.length(), qq_zero())
    let mut j = 0
    while j < row.length() {
      new_row[j] = qq_int(row[j])
      j = j + 1
    }
    out[i] = new_row
    i = i + 1
  }
  out
}

///|
pub fn qmat_copy(m : Array[Array[QQ]]) -> Array[Array[QQ]] {
  let out : Array[Array[QQ]] = Array::make(m.length(), Array::make(0, qq_zero()))
  let mut i = 0
  while i < m.length() {
    let row = m[i]
    let new_row : Array[QQ] = Array::make(row.length(), qq_zero())
    let mut j = 0
    while j < row.length() {
      new_row[j] = row[j]
      j = j + 1
    }
    out[i] = new_row
    i = i + 1
  }
  out
}

///|
pub fn qmat_add(a : Array[Array[QQ]], b : Array[Array[QQ]]) -> Array[Array[QQ]] {
  let r = qmat_rows(a)
  let c = qmat_cols(a)
  let out = qmat_zero(r, c)
  let mut i = 0
  while i < r {
    let mut j = 0
    while j < c {
      out[i][j] = qq_add(a[i][j], b[i][j])
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
pub fn qmat_sub(a : Array[Array[QQ]], b : Array[Array[QQ]]) -> Array[Array[QQ]] {
  let r = qmat_rows(a)
  let c = qmat_cols(a)
  let out = qmat_zero(r, c)
  let mut i = 0
  while i < r {
    let mut j = 0
    while j < c {
      out[i][j] = qq_sub(a[i][j], b[i][j])
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
pub fn qmat_scale(s : QQ, a : Array[Array[QQ]]) -> Array[Array[QQ]] {
  let out = qmat_zero(qmat_rows(a), qmat_cols(a))
  let mut i = 0
  while i < qmat_rows(a) {
    let mut j = 0
    while j < qmat_cols(a) {
      out[i][j] = qq_mul(s, a[i][j])
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
pub fn qmat_transpose(a : Array[Array[QQ]]) -> Array[Array[QQ]] {
  let r = qmat_rows(a)
  let c = qmat_cols(a)
  let out = qmat_zero(c, r)
  let mut i = 0
  while i < r {
    let mut j = 0
    while j < c {
      out[j][i] = a[i][j]
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
pub fn qmat_is_square(a : Array[Array[QQ]]) -> Bool {
  qmat_rows(a) == qmat_cols(a)
}

///|
pub fn qmat_eq(a : Array[Array[QQ]], b : Array[Array[QQ]]) -> Bool {
  if qmat_rows(a) != qmat_rows(b) || qmat_cols(a) != qmat_cols(b) {
    return false
  }
  let mut i = 0
  while i < qmat_rows(a) {
    if !(qq_list_eq(a[i], b[i])) {
      return false
    }
    i = i + 1
  }
  true
}

///|
/// 矩陣乘；維度不合回傳 `None`（而不是悄悄補零）。
pub fn qmat_mul(a : Array[Array[QQ]], b : Array[Array[QQ]]) -> Array[Array[QQ]]? {
  if qmat_cols(a) != qmat_rows(b) {
    return None
  }
  let r = qmat_rows(a)
  let c = qmat_cols(b)
  let n = qmat_cols(a)
  let out = qmat_zero(r, c)
  let mut i = 0
  while i < r {
    let mut j = 0
    while j < c {
      let mut acc = qq_zero()
      let mut k = 0
      while k < n {
        acc = qq_add(acc, qq_mul(a[i][k], b[k][j]))
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
/// 矩陣乘（呼叫端已知維度相符；維度不符時回傳零矩陣並由呼叫端的守衛擋下）。
pub fn qmat_mul_unchecked(a : Array[Array[QQ]], b : Array[Array[QQ]]) -> Array[Array[QQ]] {
  match qmat_mul(a, b) {
    Some(m) => m
    None => qmat_zero(qmat_rows(a), qmat_cols(b))
  }
}

///|
/// 矩陣與向量的乘積（向量視為行向量）。
pub fn qmat_vec(a : Array[Array[QQ]], v : Array[QQ]) -> Array[QQ]? {
  if qmat_cols(a) != v.length() {
    return None
  }
  let out : Array[QQ] = Array::make(qmat_rows(a), qq_zero())
  let mut i = 0
  while i < qmat_rows(a) {
    let mut acc = qq_zero()
    let mut j = 0
    while j < qmat_cols(a) {
      acc = qq_add(acc, qq_mul(a[i][j], v[j]))
      j = j + 1
    }
    out[i] = acc
    i = i + 1
  }
  Some(out)
}

///|
pub fn qmat_vec_unchecked(a : Array[Array[QQ]], v : Array[QQ]) -> Array[QQ] {
  match qmat_vec(a, v) {
    Some(x) => x
    None => Array::make(qmat_rows(a), qq_zero())
  }
}

///|
pub fn qvec_zero(n : Int32) -> Array[QQ] {
  Array::make(n, qq_zero())
}

///|
/// 內積（正定，對稱）。
pub fn qvec_dot(a : Array[QQ], b : Array[QQ]) -> QQ {
  let mut acc = qq_zero()
  let mut i = 0
  while i < a.length() {
    acc = qq_add(acc, qq_mul(a[i], b[i]))
    i = i + 1
  }
  acc
}

///|
/// 是否為零矩陣。
pub fn qmat_is_zero_matrix(m : Array[Array[QQ]]) -> Bool {
  let mut i = 0
  while i < qmat_rows(m) {
    let mut j = 0
    while j < qmat_cols(m) {
      if !(qq_is_zero(m[i][j])) {
        return false
      }
      j = j + 1
    }
    i = i + 1
  }
  true
}

///|
/// 精確秩：複製一份做高斯消去，原矩陣不動。
pub fn qmat_rank(m : Array[Array[QQ]]) -> Int32 {
  let rows = qmat_rows(m)
  let cols = qmat_cols(m)
  let work = qmat_copy(m)
  let mut rank = 0
  let mut r = 0
  let mut c = 0
  while c < cols && r < rows {
    // 找這一欄的第一個非零樞軸
    let mut piv = -1
    let mut k = r
    while k < rows {
      if piv < 0 && !(qq_is_zero(work[k][c])) {
        piv = k
      }
      k = k + 1
    }
    if piv < 0 {
      c = c + 1
    } else {
      if piv != r {
        let tmp = work[piv]
        work[piv] = work[r]
        work[r] = tmp
      }
      let pivot = work[r][c]
      let mut j = c
      while j < cols {
        work[r][j] = qq_div(work[r][j], pivot)
        j = j + 1
      }
      let mut i2 = 0
      while i2 < rows {
        if i2 != r {
          let factor = work[i2][c]
          if !(qq_is_zero(factor)) {
            let mut j2 = c
            while j2 < cols {
              work[i2][j2] = qq_sub(work[i2][j2], qq_mul(factor, work[r][j2]))
              j2 = j2 + 1
            }
          }
        }
        i2 = i2 + 1
      }
      rank = rank + 1
      r = r + 1
      c = c + 1
    }
  }
  rank
}

///|
/// 零度（核的維數）＝ 行數 − 秩。
pub fn qmat_nullity(m : Array[Array[QQ]]) -> Int32 {
  qmat_cols(m) - qmat_rank(m)
}

///|
/// 精確行列式（非方陣回傳 `None`）：帶樞軸交換的高斯消去，乘積形式。
pub fn qmat_det(m : Array[Array[QQ]]) -> QQ? {
  if !(qmat_is_square(m)) {
    return None
  }
  let n = qmat_rows(m)
  let work = qmat_copy(m)
  let mut det = qq_one()
  let mut c = 0
  while c < n {
    let mut piv = -1
    let mut k = c
    while k < n {
      if piv < 0 && !(qq_is_zero(work[k][c])) {
        piv = k
      }
      k = k + 1
    }
    if piv < 0 {
      return Some(qq_zero())
    }
    if piv != c {
      let tmp = work[piv]
      work[piv] = work[c]
      work[c] = tmp
      det = qq_neg(det)
    }
    let pivot = work[c][c]
    det = qq_mul(det, pivot)
    let mut i = c + 1
    while i < n {
      let factor = qq_div(work[i][c], pivot)
      let mut j = c
      while j < n {
        work[i][j] = qq_sub(work[i][j], qq_mul(factor, work[c][j]))
        j = j + 1
      }
      i = i + 1
    }
    c = c + 1
  }
  Some(det)
}

///|
/// 把 `x` 寫成生成組 `basis` 的線性組合，回傳係數；不在張成空間裡回傳 `None`。
/// 這是「結構常數」與「曲率張量群空間分解」的判定工具。
pub fn qmat_span_coords(basis : Array[Array[QQ]], x : Array[QQ]) -> Array[QQ]? {
  let k = basis.length()
  if k == 0 {
    return None
  }
  let rows = x.length()
  // 增廣矩陣：每個 basis 向量一欄，最後一欄是 x。
  let aug = qmat_zero(rows, k + 1)
  let mut i = 0
  while i < rows {
    let mut j = 0
    while j < k {
      aug[i][j] = basis[j][i]
      j = j + 1
    }
    aug[i][k] = x[i]
    i = i + 1
  }
  // 對列做 RREF，追蹤哪個原始變數是樞軸。
  let pivot_col = Array::make(k, -1)
  let mut rank = 0
  let mut r = 0
  let mut c = 0
  while c < k && r < rows {
    let mut piv = -1
    let mut kk = r
    while kk < rows {
      if piv < 0 && !(qq_is_zero(aug[kk][c])) {
        piv = kk
      }
      kk = kk + 1
    }
    if piv < 0 {
      c = c + 1
    } else {
      if piv != r {
        let tmp = aug[piv]
        aug[piv] = aug[r]
        aug[r] = tmp
      }
      let pivot = aug[r][c]
      let mut j = 0
      while j <= k {
        aug[r][j] = qq_div(aug[r][j], pivot)
        j = j + 1
      }
      let mut i2 = 0
      while i2 < rows {
        if i2 != r {
          let factor = aug[i2][c]
          if !(qq_is_zero(factor)) {
            let mut j2 = 0
            while j2 <= k {
              aug[i2][j2] = qq_sub(aug[i2][j2], qq_mul(factor, aug[r][j2]))
              j2 = j2 + 1
            }
          }
        }
        i2 = i2 + 1
      }
      pivot_col[r] = c
      rank = rank + 1
      r = r + 1
      c = c + 1
    }
  }
  // 一致性：任何「係數全零但常數非零」的列 ⇒ 不在張成空間裡。
  let mut rr = 0
  while rr < rows {
    let mut all_zero = true
    let mut j = 0
    while j < k {
      if !(qq_is_zero(aug[rr][j])) {
        all_zero = false
      }
      j = j + 1
    }
    if all_zero && !(qq_is_zero(aug[rr][k])) {
      return None
    }
    rr = rr + 1
  }
  let out = qvec_zero(k)
  let mut p = 0
  while p < rank {
    out[pivot_col[p]] = aug[p][k]
    p = p + 1
  }
  Some(out)
}
