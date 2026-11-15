// ---------------------------------------------------------------------------
// qprob/asymptotic/subfield.mbt — 精確有序體鏈：ℚ ⊂ ℚ(√d) ⊂ ℚ((ε))_≤M
// ---------------------------------------------------------------------------
// 量子概率與漸近極限的底層數域：
// 1. 精確正規形有理數 `QVal`（分母 > 0、gcd = 1、零為 0/1）；
// 2. 二次擴張子場 `QuadField(d)`（`a + b√d`）與嵌入射 `qval_to_quad`；
// 3. 截斷超實漸近子場 `AsymJet`（`Σ_{k=-p}^{M-p} c_k ε^k`，`ε → 0⁺` 無窮小、
//    `ε⁻¹ → +∞` 無窮大），具備精確字典序（非阿基米德有序體截斷）與主部擷取。

///|
/// 命題記錄輔助：全 `qprob` 子聯邦統一入口。
pub fn chk(out : Array[(String, Bool)], label : String, cond : Bool) -> Unit {
  out.push((label, cond))
}

///|
/// 精確有理數（唯一正規形：`den > 0`、`gcd(|num|, den) = 1`）。
#derive(Eq)
pub(all) struct QVal {
  num : BigInt
  den : BigInt
}

///|
pub extend QVal with Eq::{not_equal, equal}

///|
fn big_abs(x : BigInt) -> BigInt {
  if x < 0N {
    -x
  } else {
    x
  }
}

///|
/// 非負最大公因數。
pub fn qv_gcd(a : BigInt, b : BigInt) -> BigInt {
  let mut x = big_abs(a)
  let mut y = big_abs(b)
  while y != 0N {
    let r = x % y
    x = y
    y = r
  }
  x
}

///|
/// 正規化構造有理數；分母為 0 時回傳 0/1，嚴格反元素走 `qv_inv`。
pub fn qv_make(n : BigInt, d : BigInt) -> QVal {
  if n == 0N || d == 0N {
    return QVal::{ num: 0N, den: 1N, }
  }
  let g = qv_gcd(n, d)
  let nn = n / g
  let dd = d / g
  if dd < 0N {
    QVal::{ num: -nn, den: -dd, }
  } else {
    QVal::{ num: nn, den: dd, }
  }
}

///|
pub fn qv_zero() -> QVal {
  QVal::{ num: 0N, den: 1N, }
}

///|
pub fn qv_one() -> QVal {
  QVal::{ num: 1N, den: 1N, }
}

///|
pub fn qv_int(n : Int32) -> QVal {
  qv_make(BigInt::from_int(n), 1N)
}

///|
pub fn qv_frac(n : Int32, d : Int32) -> QVal {
  qv_make(BigInt::from_int(n), BigInt::from_int(d))
}

///|
pub fn qv_eq(a : QVal, b : QVal) -> Bool {
  a.num == b.num && a.den == b.den
}

///|
pub fn qv_is_zero(a : QVal) -> Bool {
  a.num == 0N
}

///|
pub fn qv_neg(a : QVal) -> QVal {
  QVal::{ num: -a.num, den: a.den, }
}

///|
pub fn qv_add(a : QVal, b : QVal) -> QVal {
  qv_make(a.num * b.den + b.num * a.den, a.den * b.den)
}

///|
pub fn qv_sub(a : QVal, b : QVal) -> QVal {
  qv_add(a, qv_neg(b))
}

///|
pub fn qv_mul(a : QVal, b : QVal) -> QVal {
  qv_make(a.num * b.num, a.den * b.den)
}

///|
/// 選項型乘法反元素：`0` 精確回傳 `None`。
pub fn qv_inv(a : QVal) -> QVal? {
  if a.num == 0N {
    None
  } else {
    Some(qv_make(a.den, a.num))
  }
}

///|
/// 全函數除法（`b = 0` 約定回傳 `0`）。
pub fn qv_div(a : QVal, b : QVal) -> QVal {
  guard qv_inv(b) is Some(inv_b) else { return qv_zero() }
  qv_mul(a, inv_b)
}

///|
/// 整數次冪（支援 `exp < 0` 取逆後平方求冪，`0` 的負次冪約定回傳 `0`）。
pub fn qv_pow(a : QVal, exp : Int32) -> QVal {
  if exp == 0 {
    return qv_one()
  }
  let (base, abs_e) = if exp > 0 {
    (a, exp)
  } else {
    guard qv_inv(a) is Some(inv_a) else { return qv_zero() }
    (inv_a, -exp)
  }
  let mut acc = qv_one()
  let mut cur = base
  let mut e = abs_e
  while e > 0 {
    if e % 2 == 1 {
      acc = qv_mul(acc, cur)
    }
    e = e / 2
    if e > 0 {
      cur = qv_mul(cur, cur)
    }
  }
  acc
}

///|
pub fn qv_cmp(a : QVal, b : QVal) -> Int32 {
  let lhs = a.num * b.den
  let rhs = b.num * a.den
  if lhs < rhs {
    -1
  } else if lhs == rhs {
    0
  } else {
    1
  }
}

///|
pub fn qv_lt(a : QVal, b : QVal) -> Bool {
  qv_cmp(a, b) < 0
}

///|
pub fn qv_le(a : QVal, b : QVal) -> Bool {
  qv_cmp(a, b) <= 0
}

///|
pub fn qv_show(a : QVal) -> String {
  if a.den == 1N {
    a.num.to_string()
  } else {
    "\{a.num}/\{a.den}"
  }
}

///|
/// 數字左補空白對齊（供定律總表編號輸出共用）。
pub fn pad_left_int(n : Int32, width : Int32) -> String {
  let mut s = "\{n}"
  while s.length() < width {
    s = " " + s
  }
  s
}

///|
pub fn ints_show(xs : Array[Int32]) -> String {
  let sb = StringBuilder()
  sb.write_string("[")
  for i in 0..<xs.length() {
    if i > 0 {
      sb.write_string(", ")
    }
    sb.write_string(xs[i].to_string())
  }
  sb.write_string("]")
  sb.to_string()
}

///|
pub fn qv_vec_eq(xs : Array[QVal], ys : Array[QVal]) -> Bool {
  if xs.length() != ys.length() {
    return false
  }
  for i in 0..<xs.length() {
    if !qv_eq(xs[i], ys[i]) {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// 2. 二次代數子場 QuadElem = a + b√d（d 無平方因子、非 0 非 1）
// ---------------------------------------------------------------------------

///|
/// 二次擴張域 `ℚ(√rad)` 的元素 `re + surd · √rad`。
pub(all) struct QuadElem {
  re : QVal
  surd : QVal
  rad : Int32
}

///|
pub fn quad_of_qv(x : QVal, rad : Int32) -> QuadElem {
  QuadElem::{ re: x, surd: qv_zero(), rad, }
}

///|
pub fn quad_make(re : QVal, surd : QVal, rad : Int32) -> QuadElem {
  QuadElem::{ re, surd, rad, }
}

///|
pub fn quad_eq(x : QuadElem, y : QuadElem) -> Bool {
  x.rad == y.rad && qv_eq(x.re, y.re) && qv_eq(x.surd, y.surd)
}

///|
pub fn quad_in_base_subfield(x : QuadElem) -> Bool {
  qv_is_zero(x.surd)
}

///|
pub fn quad_conj(x : QuadElem) -> QuadElem {
  QuadElem::{ re: x.re, surd: qv_neg(x.surd), rad: x.rad, }
}

///|
/// 域範數 `N(a + b√d) = a² − d·b² ∈ ℚ`。
pub fn quad_norm(x : QuadElem) -> QVal {
  qv_sub(qv_mul(x.re, x.re), qv_mul(qv_int(x.rad), qv_mul(x.surd, x.surd)))
}

///|
/// 域跡 `Tr(a + b√d) = 2a ∈ ℚ`。
pub fn quad_trace(x : QuadElem) -> QVal {
  qv_add(x.re, x.re)
}

///|
pub fn quad_add(x : QuadElem, y : QuadElem) -> QuadElem {
  guard x.rad == y.rad else { abort("quad_add: radical mismatch") }
  QuadElem::{
    re: qv_add(x.re, y.re),
    surd: qv_add(x.surd, y.surd),
    rad: x.rad,
  }
}

///|
pub fn quad_sub(x : QuadElem, y : QuadElem) -> QuadElem {
  guard x.rad == y.rad else { abort("quad_sub: radical mismatch") }
  quad_add(x, QuadElem::{ re: qv_neg(y.re), surd: qv_neg(y.surd), rad: y.rad, })
}

///|
pub fn quad_mul(x : QuadElem, y : QuadElem) -> QuadElem {
  guard x.rad == y.rad else { abort("quad_mul: radical mismatch") }
  let d = qv_int(x.rad)
  let r = qv_add(qv_mul(x.re, y.re), qv_mul(d, qv_mul(x.surd, y.surd)))
  let s = qv_add(qv_mul(x.re, y.surd), qv_mul(x.surd, y.re))
  QuadElem::{ re: r, surd: s, rad: x.rad, }
}

///|
/// 二次域反元素 `(a - b√d) / (a² - d b²)`；範數為 0 時回傳 `None`。
pub fn quad_inv(x : QuadElem) -> QuadElem? {
  guard qv_inv(quad_norm(x)) is Some(inv_n) else { return None }
  let c = quad_conj(x)
  Some(QuadElem::{
    re: qv_mul(c.re, inv_n),
    surd: qv_mul(c.surd, inv_n),
    rad: x.rad,
  })
}

// ---------------------------------------------------------------------------
// 3. 漸近 Laurent 噴流子場 AsymJet：c_{v} ε^v + c_{v+1} ε^{v+1} + ...
//    其中 ε → 0⁺（即 n = ε⁻¹ → +∞）。
//    非阿基米德序：由最低階非零項的符號決定，滿足 0 < ε^2 < ε < q（∀q ∈ ℚ⁺）。
// ---------------------------------------------------------------------------

///|
/// 漸近展開噴流：表示 `Σ_{i=0}^{coeffs.length()-1} coeffs[i] · ε^{min_exp + i}`，
/// 截斷至 `ε^cutoff`（包含 `cutoff` 階）。
pub(all) struct AsymJet {
  min_exp : Int32
  cutoff : Int32
  coeffs : Array[QVal]
}

///|
/// 將係數陣列修剪掉前導零，保持正規表示。
pub fn jet_normalize(
  min_exp : Int32,
  cutoff : Int32,
  raw : Array[QVal],
) -> AsymJet {
  if cutoff < min_exp {
    return AsymJet::{ min_exp: 0, cutoff, coeffs: [], }
  }
  let mut first = 0
  while first < raw.length() && qv_is_zero(raw[first]) {
    first = first + 1
  }
  let new_min = min_exp + first
  if first >= raw.length() || new_min > cutoff {
    return AsymJet::{ min_exp: 0, cutoff, coeffs: [], }
  }
  let max_len = cutoff - new_min + 1
  let out : Array[QVal] = []
  let mut k = 0
  while k < max_len && first + k < raw.length() {
    out.push(raw[first + k])
    k = k + 1
  }
  while out.length() > 0 && qv_is_zero(out[out.length() - 1]) {
    let _ = out.pop()
  }
  if out.length() == 0 {
    AsymJet::{ min_exp: 0, cutoff, coeffs: [], }
  } else {
    AsymJet::{ min_exp: new_min, cutoff, coeffs: out, }
  }
}

///|
pub fn jet_zero(cutoff : Int32) -> AsymJet {
  AsymJet::{ min_exp: 0, cutoff, coeffs: [], }
}

///|
/// 常數子場嵌入：`q ∈ ℚ ↪ q · ε^0 ∈ ℚ((ε))_≤cutoff`。
pub fn jet_const(q : QVal, cutoff : Int32) -> AsymJet {
  jet_normalize(0, cutoff, [q])
}

///|
/// 單項式 `c · ε^exp`。`exp < 0` 為無窮大階 `(ε⁻¹)^{|exp|}`，`exp > 0` 為無窮小階。
pub fn jet_monomial(c : QVal, exp : Int32, cutoff : Int32) -> AsymJet {
  jet_normalize(exp, cutoff, [c])
}

///|
/// 讀取 `ε^exp` 的係數。
pub fn jet_coeff(j : AsymJet, exp : Int32) -> QVal {
  if j.coeffs.length() == 0 {
    return qv_zero()
  }
  let idx = exp - j.min_exp
  if idx < 0 || idx >= j.coeffs.length() {
    qv_zero()
  } else {
    j.coeffs[idx]
  }
}

///|
pub fn jet_is_zero(j : AsymJet) -> Bool {
  j.coeffs.length() == 0
}

///|
/// 賦值階 `val(f) = min { k | c_k ≠ 0 }`；零元素回傳 `None`。
pub fn jet_valuation(j : AsymJet) -> Int32? {
  if j.coeffs.length() == 0 {
    None
  } else {
    Some(j.min_exp)
  }
}

///|
/// 有界元素判定（屬於賦值環 `ℚ[[ε]]`：`val(f) ≥ 0`）。
pub fn jet_is_bounded(j : AsymJet) -> Bool {
  j.coeffs.length() == 0 || j.min_exp >= 0
}

///|
/// 無窮小理想判定（屬於極大理想 `ε·ℚ[[ε]]`：`val(f) ≥ 1`）。
pub fn jet_is_infinitesimal(j : AsymJet) -> Bool {
  j.coeffs.length() == 0 || j.min_exp >= 1
}

///|
/// 標準部映射（Standard Part / 漸近極限 `lim_{ε→0⁺} f(ε)`）：
/// - 若存在負冪項（無窮大發散），回傳 `None`；
/// - 若有界（`val ≥ 0`），消去全部 `ε^k (k ≥ 1)` 無窮小項，回傳常數項 `c_0 ∈ ℚ`。
/// 這正是 `ℚ[[ε]] / (ε) ≅ ℚ` 的商同態！
pub fn jet_standard_part(j : AsymJet) -> QVal? {
  if !jet_is_bounded(j) {
    None
  } else {
    Some(jet_coeff(j, 0))
  }
}

///|
pub fn jet_eq(a : AsymJet, b : AsymJet) -> Bool {
  let c = if a.cutoff < b.cutoff { a.cutoff } else { b.cutoff }
  if a.coeffs.length() == 0 && b.coeffs.length() == 0 {
    return true
  }
  let lo_a = if a.coeffs.length() == 0 { 0 } else { a.min_exp }
  let lo_b = if b.coeffs.length() == 0 { 0 } else { b.min_exp }
  let lo = if lo_a < lo_b { lo_a } else { lo_b }
  for e in lo..<(c + 1) {
    if !qv_eq(jet_coeff(a, e), jet_coeff(b, e)) {
      return false
    }
  }
  true
}

///|
pub fn jet_add(a : AsymJet, b : AsymJet) -> AsymJet {
  let c = if a.cutoff < b.cutoff { a.cutoff } else { b.cutoff }
  if a.coeffs.length() == 0 && b.coeffs.length() == 0 {
    return jet_zero(c)
  }
  let lo = if a.coeffs.length() == 0 {
    b.min_exp
  } else if b.coeffs.length() == 0 {
    a.min_exp
  } else if a.min_exp < b.min_exp {
    a.min_exp
  } else {
    b.min_exp
  }
  let raw = [
    for e in lo..<(c + 1) => qv_add(jet_coeff(a, e), jet_coeff(b, e))
  ]
  jet_normalize(lo, c, raw)
}

///|
pub fn jet_sub(a : AsymJet, b : AsymJet) -> AsymJet {
  let neg_b = AsymJet::{
    min_exp: b.min_exp,
    cutoff: b.cutoff,
    coeffs: [
      for x in b.coeffs => qv_neg(x)
    ],
  }
  jet_add(a, neg_b)
}

///|
pub fn jet_mul(a : AsymJet, b : AsymJet) -> AsymJet {
  let c = if a.cutoff < b.cutoff { a.cutoff } else { b.cutoff }
  if a.coeffs.length() == 0 || b.coeffs.length() == 0 {
    return jet_zero(c)
  }
  let lo = a.min_exp + b.min_exp
  if lo > c {
    return jet_zero(c)
  }
  let len = c - lo + 1
  let raw = Array::make(len, qv_zero())
  for i in 0..<a.coeffs.length() {
    for j in 0..<b.coeffs.length() {
      let exp = a.min_exp + i + b.min_exp + j
      if exp <= c {
        let idx = exp - lo
        raw[idx] = qv_add(raw[idx], qv_mul(a.coeffs[i], b.coeffs[j]))
      }
    }
  }
  jet_normalize(lo, c, raw)
}

///|
/// 截斷 Laurent 級數反元素：若 `a = c_v ε^v (1 + u)`（`c_v ≠ 0`），
/// 用精確長除法在 `ℚ((ε))` 中計算 `a⁻¹` 至 `ε^cutoff` 階，使得 `a · a⁻¹ ≡ 1 (mod ε^{cutoff+1})`。
pub fn jet_inv(a : AsymJet) -> AsymJet? {
  if a.coeffs.length() == 0 {
    return None
  }
  let v = a.min_exp
  guard qv_inv(a.coeffs[0]) is Some(inv_c0) else { return None }
  let inv_min = -v
  if inv_min > a.cutoff {
    return Some(jet_zero(a.cutoff))
  }
  let len = a.cutoff - inv_min + 1
  let b = Array::make(len, qv_zero())
  b[0] = inv_c0
  for k in 1..<len {
    let mut sum = qv_zero()
    let mut i = 1
    while i <= k && i < a.coeffs.length() {
      sum = qv_add(sum, qv_mul(a.coeffs[i], b[k - i]))
      i = i + 1
    }
    b[k] = qv_neg(qv_mul(inv_c0, sum))
  }
  Some(jet_normalize(inv_min, a.cutoff, b))
}

///|
/// 非阿基米德漸近序（`ε → 0⁺`）：比較 `a - b` 最低次非零項的符號。
pub fn jet_cmp(a : AsymJet, b : AsymJet) -> Int32 {
  let diff = jet_sub(a, b)
  if diff.coeffs.length() == 0 {
    0
  } else {
    qv_cmp(diff.coeffs[0], qv_zero())
  }
}
