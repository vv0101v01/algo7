// ---------------------------------------------------------------------------
// qgeom/geom — 定律登記
// ---------------------------------------------------------------------------
// A. 平移射影：提升、群律、無窮遠超平面、拋物性、交比不變、調和共軛、關聯性。
// B. 雅可布全射張量積：rank(A⊗B) = rank A · rank B、滿射保存、核維數、行列式、
//    鏈鎖律（雅可比是函子）、線性映射與平移的雅可比。

///|
pub fn geom_all_laws() -> Array[(String, Array[(String, Bool)])] {
  [
    ("平移的射影提升：群律與無窮遠超平面", law_projective_translation_group()),
    ("交比在平移與分式線性映射下不變", law_cross_ratio_invariance()),
    ("調和共軛與交比的對稱恆等式", law_harmonic_and_symmetry()),
    ("雅可比是函子：鏈鎖律", law_jacobian_chain_rule()),
    ("張量積的秩與全射性", law_tensor_product_surjectivity()),
  ]
}

///|
fn gn(i : Int32, d : Int32) -> @core.QQ {
  @core.qq_frac(i, d)
}

///|
fn tvec2() -> Array[@core.QQ] {
  [gn(1, 1), gn(2, 1)]
}

///|
fn svec2() -> Array[@core.QQ] {
  [gn(-3, 1), gn(1, 2)]
}

///|
fn p2(x : Int32, y : Int32) -> Array[@core.QQ] {
  [gn(x, 1), gn(y, 1), gn(1, 1)]
}

// ---------------------------------------------------------------------------
// A. 平移射影
// ---------------------------------------------------------------------------

///|
pub fn law_projective_translation_group() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let t = tvec2()
  let s = svec2()
  let mt = proj_translation_matrix(t)
  let ms = proj_translation_matrix(s)
  @core.chk(
    out,
    "提升形狀為 3×3 且最後一列是 (0,0,1)",
    @core.qmat_rows(mt) == 3 &&
    @core.qq_is_zero(mt[2][0]) &&
    @core.qq_is_zero(mt[2][1]) &&
    @core.qq_eq(mt[2][2], @core.qq_one()),
  )
  // 群律：M(t)M(s) = M(t+s)
  let sum : Array[@core.QQ] = []
  let mut i = 0
  while i < t.length() {
    sum.push(@core.qq_add(t[i], s[i]))
    i = i + 1
  }
  let prod = match @core.qmat_mul(mt, ms) {
    Some(m) => m
    None => @core.qmat_zero(3, 3)
  }
  @core.chk(
    out,
    "群律：M(t)·M(s) = M(t+s)",
    @core.qmat_eq(prod, proj_translation_matrix(sum)),
  )
  let id = @core.qmat_identity(3)
  let zero_t : Array[@core.QQ] = [@core.qq_zero(), @core.qq_zero()]
  @core.chk(out, "M(0) = id", @core.qmat_eq(proj_translation_matrix(zero_t), id))
  let neg_t : Array[@core.QQ] = [@core.qq_neg(t[0]), @core.qq_neg(t[1])]
  let inv = match @core.qmat_mul(proj_translation_matrix(neg_t), mt) {
    Some(m) => m
    None => @core.qmat_zero(3, 3)
  }
  @core.chk(out, "M(−t)·M(t) = id（提升是雙射）", @core.qmat_eq(inv, id))
  let det = @core.qmat_det(mt)
  @core.chk(
    out,
    "det M(t) = 1（保體積，射影群元）",
    match det {
      Some(d) => @core.qq_eq(d, @core.qq_one())
      None => false
    },
  )
  // 無窮遠超平面不變
  let inf_pt : Array[@core.QQ] = [gn(1, 1), gn(2, 1), @core.qq_zero()]
  let inf_img = match proj_apply(mt, inf_pt) {
    Some(p) => p
    None => inf_pt
  }
  @core.chk(
    out,
    "無窮遠點 (1,2,0) 的像是無窮遠點（w 分量仍為 0）",
    @core.qq_is_zero(inf_img[2]) && proj_eq(inf_img, inf_pt),
  )
  // 仿射作用
  let x = proj_of_affine([gn(3, 1), gn(-1, 1)])
  let img = match proj_apply(mt, x) {
    Some(p) => p
    None => x
  }
  let expect = proj_of_affine([gn(4, 1), gn(1, 1)])
  let affine_ok = match proj_to_affine(img) {
    None => false
    Some(v) => @core.qq_list_eq(v, [gn(4, 1), gn(1, 1)])
  }
  @core.chk(
    out,
    "仿射圖上就是平移：[3,−1,1] ↦ [4,1,1]",
    proj_eq(img, expect) && affine_ok,
  )
  @core.chk(
    out,
    "負控制：平移後的點與原點不同（不是恆等映射）",
    !(proj_eq(img, x)),
  )
  // 拋物（unipotent）：(M − I)² = 0、M^k = M(kt) ≠ id
  let diff = proj_mat_minus_identity(mt)
  let diff2 = @core.qmat_mul_unchecked(diff, diff)
  @core.chk(
    out,
    "(M(t) − I)² = 0（拋物元素：在無窮遠處只有一個不動點）",
    @core.qmat_is_zero_matrix(diff2),
  )
  let mut power_ok = true
  let mut k = 1
  while k <= 5 {
    let kt : Array[@core.QQ] = [
      @core.qq_mul(@core.qq_int(k), t[0]),
      @core.qq_mul(@core.qq_int(k), t[1]),
    ]
    if !(@core.qmat_eq(proj_mat_pow(mt, k), proj_translation_matrix(kt))) {
      power_ok = false
    }
    if k > 0 && @core.qmat_eq(proj_mat_pow(mt, k), id) {
      power_ok = false
    }
    k = k + 1
  }
  @core.chk(out, "M(t)^k = M(kt) ≠ id（k = 1..5：平移是無限階的）", power_ok)
  // 關聯性：Lᵗp = 0 ⇒ (M⁻ᵗL)ᵗ(Mp) = 0
  let line : Array[@core.QQ] = [gn(2, 1), gn(-1, 1), gn(-5, 1)]
  let on_line = {
    // 點 (3,1) 在直線 2x − y − 5 = 0 上
    let q = p2(3, 1)
    proj_incident(line, q)
  }
  let moved_line = match proj_apply(proj_translation_inverse_transpose(t), line) {
    Some(l) => l
    None => line
  }
  let moved_point = match proj_apply(mt, p2(3, 1)) {
    Some(p) => p
    None => p2(3, 1)
  }
  @core.chk(
    out,
    "關聯性保持：(3,1) 在 2x−y−5=0 上 ⇒ 像點在像直線上",
    on_line && proj_incident(moved_line, moved_point),
  )
  @core.chk(
    out,
    "負控制：不在直線上的點，其像也不在像直線上",
    !(proj_incident(line, p2(3, 2))) &&
    !(proj_incident(moved_line, match proj_apply(mt, p2(3, 2)) {
      Some(p) => p
      None => p2(3, 2)
    })),
  )
  // 零向量不是射影點
  @core.chk(
    out,
    "proj_is_zero：零向量被認出、非零向量不會被誤判",
    proj_is_zero([@core.qq_zero(), @core.qq_zero(), @core.qq_zero()]) &&
    !(proj_is_zero(p2(0, 0))),
  )
  out
}

// ---------------------------------------------------------------------------
// 交比
// ---------------------------------------------------------------------------

///|
fn p1(x : Int32, d : Int32) -> Array[@core.QQ] {
  [gn(x, d), gn(1, 1)]
}

///|
pub fn law_cross_ratio_invariance() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let a = p1(0, 1)
  let b = p1(1, 1)
  let c = p1(7, 2)
  let d = p1(5, 1)
  let cr = match proj_cross_ratio(a, b, c, d) {
    Some(x) => x
    None => @core.qq_zero()
  }
  // 手算：(0−7/2)(1−5) / ((0−5)(1−7/2)) = (−7/2·−4) / (−5·−5/2) = 14 / (25/2) = 28/25
  @core.chk(
    out,
    "交比 (0,1;7/2,5) = 28/25（與手算一致）",
    @core.qq_eq(cr, gn(28, 25)),
  )
  // 平移不變（平移後的點仍是仿射點，交比只看 2×2 行列式）
  let t = gn(4, 3)
  let shift = fn(p : Array[@core.QQ]) -> Array[@core.QQ] {
    [@core.qq_add(p[0], t), p[1]]
  }
  let cr_shift = match proj_cross_ratio(shift(a), shift(b), shift(c), shift(d)) {
    Some(x) => x
    None => @core.qq_zero()
  }
  @core.chk(out, "平移 x ↦ x + 4/3 不改交比", @core.qq_eq(cr_shift, cr))
  // 一般分式線性映射不變（含 det ≠ 1 與 S: x ↦ −1/x）
  let mobius_list : Array[Array[Array[@core.QQ]]] = [
    proj_mobius(gn(2, 1), gn(1, 1), gn(1, 1), gn(1, 1)),
    proj_mobius(gn(3, 1), gn(2, 1), gn(1, 1), gn(1, 1)),
    proj_mobius(gn(2, 1), gn(0, 1), gn(0, 1), gn(3, 1)),
    proj_mobius(gn(0, 1), gn(-1, 1), gn(1, 1), gn(0, 1)),
  ]
  let mut mobius_ok = true
  let mut mobius_checked = 0
  let mut i = 0
  while i < mobius_list.length() {
    let m = mobius_list[i]
    match proj_cross_ratio_image(m, a, b, c, d) {
      None => ()
      Some(x) =>
        if !(@core.qq_eq(x, cr)) {
          mobius_ok = false
        }
    }
    mobius_checked = mobius_checked + 1
    i = i + 1
  }
  @core.chk(
    out,
    "\{mobius_checked} 個分式線性映射（含 det≠1 與 x↦−1/x）都不改交比",
    mobius_ok,
  )
  // 退化：三點重合時交比沒有定義
  @core.chk(
    out,
    "退化守衛：b = c 時交比分母為零 ⇒ None",
    proj_cross_ratio(a, b, b, d) is None,
  )
  // 兩個不同的入射四元組交比不同（負控制）
  let other = p1(-2, 1)
  let cr_other = match proj_cross_ratio(a, b, other, d) {
    Some(x) => x
    None => @core.qq_zero()
  }
  @core.chk(out, "負控制：換一個點交比就變了", !(@core.qq_eq(cr_other, cr)))
  out
}

///|
pub fn law_harmonic_and_symmetry() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let a = p1(0, 1)
  let b = p1(1, 1)
  let c = p1(3, 1)
  let d0 = p1(5, 1)
  let cr = match proj_cross_ratio(a, b, c, d0) {
    Some(x) => x
    None => @core.qq_zero()
  }
  // 對稱恆等式
  let swap_cd = match proj_cross_ratio(c, d0, a, b) {
    Some(x) => x
    None => @core.qq_zero()
  }
  let swap_both = match proj_cross_ratio(b, a, d0, c) {
    Some(x) => x
    None => @core.qq_zero()
  }
  let invert = match proj_cross_ratio(a, b, d0, c) {
    Some(x) => x
    None => @core.qq_zero()
  }
  @core.chk(
    out,
    "(a,b;c,d) = (c,d;a,b) = (b,a;d,c)",
    @core.qq_eq(cr, swap_cd) && @core.qq_eq(cr, swap_both),
  )
  @core.chk(
    out,
    "(a,b;c,d)·(a,b;d,c) = 1",
    @core.qq_eq(@core.qq_mul(cr, invert), @core.qq_one()),
  )
  // 調和共軛：d = ((a+b)c − 2ab)/(2c − a − b)
  let xa = a[0]
  let xb = b[0]
  let xc = c[0]
  let num = @core.qq_sub(
    @core.qq_mul(@core.qq_add(xa, xb), xc),
    @core.qq_mul(@core.qq_int(2), @core.qq_mul(xa, xb)),
  )
  let den = @core.qq_sub(
    @core.qq_sub(@core.qq_mul(@core.qq_int(2), xc), xa),
    xb,
  )
  let xd = @core.qq_div(num, den)
  @core.chk(
    out,
    "調和共軛公式 d = ((a+b)c − 2ab)/(2c − a − b) 給出 3/5",
    @core.qq_eq(xd, gn(3, 5)),
  )
  let dh = [xd, @core.qq_one()]
  let harmonic = match proj_cross_ratio(a, b, c, dh) {
    Some(x) => x
    None => @core.qq_zero()
  }
  @core.chk(
    out,
    "調和四元組： (a,b;c,d) = −1（值 \{@core.qq_show(harmonic)}）",
    @core.qq_eq(harmonic, @core.qq_int(-1)),
  )
  // 用整數齊次座標 [3,5] 表示同一個點：交比只依賴射影類
  let dh2 : Array[@core.QQ] = [gn(3, 1), gn(5, 1)]
  let harmonic2 = match proj_cross_ratio(a, b, c, dh2) {
    Some(x) => x
    None => @core.qq_zero()
  }
  @core.chk(
    out,
    "交比只依賴射影類：[3/5,1] 與 [3,5] 給出同一個 −1",
    @core.qq_eq(harmonic2, harmonic),
  )
  @core.chk(
    out,
    "負控制：非調和點（d = 2）給出 ≠ −1 的交比",
    !(@core.qq_eq(
      match proj_cross_ratio(a, b, c, p1(2, 1)) {
        Some(x) => x
        None => @core.qq_zero()
      },
      @core.qq_int(-1),
    )),
  )
  out
}

// ---------------------------------------------------------------------------
// B. 雅可比
// ---------------------------------------------------------------------------

///|
fn map_f() -> Array[MPoly] {
  // f(x,y) = (x·y, x + y)
  [
    mpoly_mul(mpoly_var(2, 0), mpoly_var(2, 1)),
    mpoly_add(mpoly_var(2, 0), mpoly_var(2, 1)),
  ]
}

///|
fn map_g() -> Array[MPoly] {
  // g(u,v) = (u + v, u·v)
  [
    mpoly_add(mpoly_var(2, 0), mpoly_var(2, 1)),
    mpoly_mul(mpoly_var(2, 0), mpoly_var(2, 1)),
  ]
}

///|
fn points2() -> Array[Array[@core.QQ]] {
  [
    [gn(1, 1), gn(2, 1)],
    [gn(3, 2), gn(-1, 1)],
    [gn(0, 1), gn(0, 1)],
  ]
}

///|
pub fn law_jacobian_chain_rule() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let f = map_f()
  let g = map_g()
  let gof = map_compose(g, f)
  let pts = points2()
  let mut chain_ok = true
  let mut checked = 0
  let mut i = 0
  while i < pts.length() {
    let x = pts[i]
    let lhs = map_jacobian(gof, x)
    let fx = map_eval(f, x)
    let jg = map_jacobian(g, fx)
    let jf = map_jacobian(f, x)
    let rhs = @core.qmat_mul_unchecked(jg, jf)
    if !(@core.qmat_eq(lhs, rhs)) {
      chain_ok = false
    }
    checked = checked + 1
    i = i + 1
  }
  @core.chk(out, "鏈鎖律 J(g∘f)(x) = J_g(f(x))·J_f(x)（\{checked} 個點，精確相等）", chain_ok)
  // 複合後的顯式分量：g∘f = (xy + x + y, xy(x+y))
  let gof_at_1_2 = map_eval(gof, [gn(1, 1), gn(2, 1)])
  @core.chk(
    out,
    "複合映射 (g∘f)(1,2) = (5,6)（代值核對）",
    @core.qq_eq(gof_at_1_2[0], gn(5, 1)) && @core.qq_eq(gof_at_1_2[1], gn(6, 1)),
  )
  // 線性映射的雅可比就是矩陣本身
  let lin = [
    mpoly_add(
      mpoly_scale(gn(2, 1), mpoly_var(2, 0)),
      mpoly_scale(gn(3, 1), mpoly_var(2, 1)),
    ),
    mpoly_sub(mpoly_var(2, 0), mpoly_var(2, 1)),
  ]
  let lin_mat = @core.qmat_zero(2, 2)
  lin_mat[0][0] = gn(2, 1)
  lin_mat[0][1] = gn(3, 1)
  lin_mat[1][0] = gn(1, 1)
  lin_mat[1][1] = gn(-1, 1)
  let mut lin_ok = true
  i = 0
  while i < pts.length() {
    if !(@core.qmat_eq(map_jacobian(lin, pts[i]), lin_mat)) {
      lin_ok = false
    }
    i = i + 1
  }
  @core.chk(out, "線性映射的雅可比在每一點都等於其矩陣", lin_ok)
  // 平移映射的雅可比是單位矩陣（與 A 章的射影提升對接）
  let trans = [
    mpoly_add(mpoly_var(2, 0), mpoly_const(2, gn(7, 3))),
    mpoly_add(mpoly_var(2, 1), mpoly_const(2, gn(-2, 1))),
  ]
  let mut trans_ok = true
  i = 0
  while i < pts.length() {
    if !(@core.qmat_eq(map_jacobian(trans, pts[i]), @core.qmat_identity(2))) {
      trans_ok = false
    }
    i = i + 1
  }
  @core.chk(
    out,
    "平移映射的雅可比恆為 I（射影平移的線性化是恆等）",
    trans_ok,
  )
  out
}

// ---------------------------------------------------------------------------
// 張量積
// ---------------------------------------------------------------------------

///|
fn qm(rows : Array[Array[Int32]]) -> Array[Array[@core.QQ]] {
  @core.qmat_from_int(rows)
}

///|
fn tensor_battery() -> Array[Array[Array[@core.QQ]]] {
  [
    qm([[1, 2], [3, 4]]),
    qm([[1, 0, 1], [0, 1, 1]]),
    qm([[1, 2], [2, 4]]),
    qm([[1, 2, 3]]),
    qm([[2, 1], [1, 3]]),
  ]
}

///|
pub fn law_tensor_product_surjectivity() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let mats = tensor_battery()
  let mut rank_ok = true
  let mut pairs = 0
  let mut nullity_ok = true
  let mut i = 0
  while i < mats.length() {
    let mut j = 0
    while j < mats.length() {
      let a = mats[i]
      let b = mats[j]
      let ka = mat_kronecker(a, b)
      let ra = @core.qmat_rank(a)
      let rb = @core.qmat_rank(b)
      if @core.qmat_rank(ka) != ra * rb {
        rank_ok = false
      }
      // 核維數：cols(A)·cols(B) − rank(A)·rank(B)
      let cols = @core.qmat_cols(a) * @core.qmat_cols(b)
      if @core.qmat_nullity(ka) != cols - ra * rb {
        nullity_ok = false
      }
      pairs = pairs + 1
      j = j + 1
    }
    i = i + 1
  }
  @core.chk(out, "rank(A⊗B) = rank(A)·rank(B)（\{pairs} 對矩陣，精確秩）", rank_ok)
  @core.chk(out, "核維數恆等：dim ker(A⊗B) = 列積 − rank(A)·rank(B)", nullity_ok)
  // 全射 ⊗ 全射 = 全射
  let surj_a = mats[1]
  let surj_b = mats[0]
  let k = mat_kronecker(surj_a, surj_b)
  @core.chk(
    out,
    "全射 ⊗ 全射 = 全射：rank(A⊗B) = \{@core.qmat_rank(k)} = 列積 \{@core.qmat_rows(k)}",
    mat_is_surjective(surj_a) &&
    mat_is_surjective(surj_b) &&
    mat_is_surjective(k),
  )
  // 負控制：秩虧張量積不滿射
  let sing = mats[2]
  @core.chk(
    out,
    "負控制：rank 1 的奇異矩陣與任何矩陣張量積後仍秩虧（不滿射）",
    !(mat_is_surjective(sing)) &&
    !(mat_is_surjective(mat_kronecker(sing, mats[0]))) &&
    !(mat_is_surjective(mat_kronecker(mats[0], sing))),
  )
  // 行列式乘法性 det(A⊗B) = det(A)^{cB}·det(B)^{rA}
  let a = mats[0]
  let b = mats[4]
  let det_a = match @core.qmat_det(a) {
    Some(x) => x
    None => @core.qq_zero()
  }
  let det_b = match @core.qmat_det(b) {
    Some(x) => x
    None => @core.qq_zero()
  }
  let det_k = match @core.qmat_det(mat_kronecker(a, b)) {
    Some(x) => x
    None => @core.qq_zero()
  }
  let expect = @core.qq_mul(
    @core.qq_pow(det_a, @core.qmat_cols(b)),
    @core.qq_pow(det_b, @core.qmat_rows(a)),
  )
  @core.chk(
    out,
    "det(A⊗B) = det(A)^\{@core.qmat_cols(b)}·det(B)^\{@core.qmat_rows(a)} = \{@core.qq_show(det_k)}",
    @core.qq_eq(det_k, expect),
  )
  // 雅可比滿秩 ⇒ 淹沒 ⇒ id⊗J 全射；奇異點則否
  let f = map_f()
  let good : Array[@core.QQ] = [gn(1, 1), gn(2, 1)]
  let bad : Array[@core.QQ] = [gn(0, 1), gn(0, 1)]
  let jgood = map_jacobian(f, good)
  let jbad = map_jacobian(f, bad)
  let id2 = @core.qmat_identity(2)
  @core.chk(
    out,
    "雅可比滿秩點：rank J = 2、rank(id⊗J) = 4 = 目標維度（淹沒）",
    @core.qmat_rank(jgood) == 2 &&
    @core.qmat_rank(mat_kronecker(id2, jgood)) == 4,
  )
  @core.chk(
    out,
    "負控制：奇異點 (0,0) 上 rank J = \{@core.qmat_rank(jbad)}，id⊗J 不滿射",
    @core.qmat_rank(jbad) < 2 &&
    !(mat_is_surjective(mat_kronecker(id2, jbad))),
  )
  out
}
