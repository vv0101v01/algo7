// ---------------------------------------------------------------------------
// qgeom/core — 精確有理數 QQ（BigInt 分子／分母，唯一正規形）
// ---------------------------------------------------------------------------
// 整個 qgeom 聯邦不需要任何浮點數：四元數、軸向張量、曲率張量、週期矩陣的
// 每個等式都是「有理數相等」或「整數相等」。這裡的有理數永遠保持正規形
// （分母 > 0、gcd = 1、零寫成 0/1），因此 `qq_eq` 是結構比較而不是交叉相乘，
// 而 `qq_inv` 只有在分子為零時才回傳 `None`（真正的不存在，不是約定值）。
//
// 除掉「除零」這一條以外，這是一個特徵 0 的體：交換、結合、分配、單位、
// 反元素全都在 `law_rational_field` 裡當場重算，而不是引用文字。

///|
/// 精確有理數。正規形：`den > 0`、`gcd(num, den) = 1`、零為 `0/1`。
pub(all) struct QQ {
  num : BigInt
  den : BigInt
}

///|
fn qq_big_abs(x : BigInt) -> BigInt {
  if x < 0N {
    -x
  } else {
    x
  }
}

///|
/// 非負最大公因數；`gcd(0, 0)` 定義為 0（`qq_make` 在此之前就攔下零）。
pub fn qq_gcd(a : BigInt, b : BigInt) -> BigInt {
  let mut x = qq_big_abs(a)
  let mut y = qq_big_abs(b)
  while y != 0N {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
/// 由任意一對 BigInt 造出正規形有理數。分母為 0 的傳統全約定：回傳 0
/// （與 `algebra/core` 的 `Rat` 一致），但**任何需要真正除法的位置**
/// 都走 `qq_inv`／`qq_div` 的選項型介面。
pub fn qq_make(n : BigInt, d : BigInt) -> QQ {
  if n == 0N || d == 0N {
    return QQ::{ num: 0N, den: 1N }
  }
  let g = qq_gcd(n, d)
  let nn = n / g
  let dd = d / g
  if dd < 0N {
    QQ::{ num: -nn, den: -dd }
  } else {
    QQ::{ num: nn, den: dd }
  }
}

///|
pub fn qq_int(n : Int32) -> QQ {
  qq_make(BigInt::from_int(n), 1N)
}

///|
pub fn qq_frac(n : Int32, d : Int32) -> QQ {
  qq_make(BigInt::from_int(n), BigInt::from_int(d))
}

///|
pub fn qq_zero() -> QQ {
  QQ::{ num: 0N, den: 1N }
}

///|
pub fn qq_one() -> QQ {
  QQ::{ num: 1N, den: 1N }
}

///|
pub fn qq_neg(a : QQ) -> QQ {
  QQ::{ num: -a.num, den: a.den }
}

///|
pub fn qq_add(a : QQ, b : QQ) -> QQ {
  qq_make(a.num * b.den + b.num * a.den, a.den * b.den)
}

///|
pub fn qq_sub(a : QQ, b : QQ) -> QQ {
  qq_make(a.num * b.den - b.num * a.den, a.den * b.den)
}

///|
pub fn qq_mul(a : QQ, b : QQ) -> QQ {
  qq_make(a.num * b.num, a.den * b.den)
}

///|
/// 乘法反元素；零沒有反元素，所以是選項型而不是約定值。
pub fn qq_inv(a : QQ) -> QQ? {
  if a.num == 0N {
    None
  } else {
    Some(qq_make(a.den, a.num))
  }
}

///|
/// 總函數除法：`b = 0` 時回傳 0（全約定）。需要區分時用 `qq_inv`。
pub fn qq_div(a : QQ, b : QQ) -> QQ {
  if b.num == 0N {
    qq_zero()
  } else {
    qq_make(a.num * b.den, a.den * b.num)
  }
}

///|
/// 正規形讓等值判定退化成兩個 BigInt 的結構比較。
pub fn qq_eq(a : QQ, b : QQ) -> Bool {
  a.num == b.num && a.den == b.den
}

///|
pub fn qq_is_zero(a : QQ) -> Bool {
  a.num == 0N
}

///|
pub fn qq_cmp(a : QQ, b : QQ) -> Int32 {
  let l = a.num * b.den
  let r = b.num * a.den
  if l < r {
    -1
  } else if l == r {
    0
  } else {
    1
  }
}

///|
pub fn qq_lt(a : QQ, b : QQ) -> Bool {
  qq_cmp(a, b) < 0
}

///|
pub fn qq_half() -> QQ {
  qq_frac(1, 2)
}

///|
/// 非負整數次方（`k = 0` 給 1）。
pub fn qq_pow(a : QQ, k : Int32) -> QQ {
  let mut out = qq_one()
  let mut i = 0
  while i < k {
    out = qq_mul(out, a)
    i = i + 1
  }
  out
}

///|
/// 顯示用（`num/den` 或整數 `num`）；只用於報告標籤，不參與任何判定。
pub fn qq_show(a : QQ) -> String {
  if a.den == 1N {
    a.num.to_string()
  } else {
    a.num.to_string() + "/" + a.den.to_string()
  }
}

///|
/// 有理數列（`Array[QQ]`）的相等判定，向量與矩陣層都用到。
pub fn qq_list_eq(a : Array[QQ], b : Array[QQ]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let mut i = 0
  while i < a.length() {
    if !(qq_eq(a[i], b[i])) {
      return false
    }
    i = i + 1
  }
  true
}
