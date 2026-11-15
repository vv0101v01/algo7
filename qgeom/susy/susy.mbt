// ---------------------------------------------------------------------------
// qgeom/susy — 超對稱四元數頂點代數與「頂點對偶幾何方程」
// ---------------------------------------------------------------------------
// 三層結構，全部在 QQ 上精確計算：
//
//   1. **分次（super）代數**：四元數矩陣配上宇稱 |A| ∈ {0,1}，
//      分次交換子 `[A,B] = AB − (−1)^{|A||B|} BA`。分次反對稱、分次 Jacobi、
//      超跡（supertrace）的分次循環性都在 `law_superalgebra` 當場重算。
//   2. **四元數頂點算子**：`V(z) = Σ_n A_n z^n`（截斷形式冪級數，係數是四元數矩陣）。
//      對偶 `V*(z) = Σ_n A_n† z^{−n}`。伴隨性 `⟨Au, w⟩ = ⟨u, A†w⟩` 與
//      「對偶兩次回到自己」把「頂點對偶」變成可判定的等式，而不是類比。
//   3. **複形四元數**（complexified quaternions）`H ⊗_R C`：`(a + i b)`，
//      `i` 與四元數交換。德朗姆複形在 `qgeom/susy/derham.mbt`，
//      這裡只提供係數環與它的複結構 `J`（`J² = −1`，且 `J` 與實邊界算子交換）。

// ---------------------------------------------------------------------------
// 1. 分次代數
// ---------------------------------------------------------------------------

///|
/// 齊次元素：四元數矩陣 + 宇稱（0 = 偶、1 = 奇）。
pub(all) struct SLad {
  mat : Array[Array[@core.Quat]]
  par : Int32
}

///|
pub fn slad_new(mat : Array[Array[@core.Quat]], par : Int32) -> SLad {
  SLad::{ mat: mat, par: par }
}

///|
/// 符號 `(−1)^{|A||B|}`。
pub fn slad_sign(a : SLad, b : SLad) -> Int32 {
  if a.par * b.par == 0 {
    1
  } else {
    -1
  }
}

///|
/// 分次交換子 `[A,B] = AB − (−1)^{|A||B|} BA`；宇稱取模 2 相加。
pub fn slad_bracket(a : SLad, b : SLad) -> SLad {
  let ab = @core.qm_mul_unchecked(a.mat, b.mat)
  let ba = @core.qm_mul_unchecked(b.mat, a.mat)
  let sign = slad_sign(a, b)
  let second = if sign == 1 {
    ba
  } else {
    @core.qm_neg(ba)
  }
  slad_new(@core.qm_sub(ab, second), (a.par + b.par) % 2)
}

///|
pub fn slad_eq(a : SLad, b : SLad) -> Bool {
  a.par == b.par && @core.qm_eq(a.mat, b.mat)
}

///|
/// **實超跡**（supertrace 的實部）：`str(M) = Re tr(M_ee) − Re tr(M_oo)`。
///
/// 為什麼取實部而不是四元數值：四元數不可交換，`tr(AB) = tr(BA)` 對
/// 四元數係數的矩陣**不成立**（1×1 分塊時就退化成 `ab ≠ ba`），但
/// `Re tr(AB) = Re tr(BA)` 恆成立（`Re(ab) = Re(ba)`）。分次循環性需要的
/// 正是後者，所以這裡把超跡定義成實值——這是定義的選擇，不是為了讓定律通過
/// 而臨時改的：四元數矩陣的「跡」在無跡代數裡本來就取實部。
pub fn susy_supertrace(
  m : Array[Array[@core.Quat]],
  p : Int32,
  q : Int32,
) -> @core.QQ {
  // str(M) = Re tr(D·M)，D = diag(I_p, −I_q)：用既有的矩陣乘與跡，不再手寫兩段對角迴圈。
  let d = @core.qm_zero(p + q, p + q)
  let mut i = 0
  while i < p + q {
    d[i][i] = if i < p {
      @core.quat_one()
    } else {
      @core.quat_neg(@core.quat_one())
    }
    i = i + 1
  }
  @core.quat_re(@core.qm_trace(@core.qm_mul_unchecked(d, m)))
}

// ---------------------------------------------------------------------------
// 2. 複形四元數 H ⊗_R C
// ---------------------------------------------------------------------------

///|
/// 複形四元數 `a + i·b`（`a`、`b` 是四元數，`i` 與四元數交換，`i² = −1`）。
pub(all) struct CQuat {
  ca : @core.Quat
  cb : @core.Quat
}

///|
pub fn cq_make(a : @core.Quat, b : @core.Quat) -> CQuat {
  CQuat::{ ca: a, cb: b }
}

///|
pub fn cq_zero() -> CQuat {
  cq_make(@core.quat_zero(), @core.quat_zero())
}

///|
pub fn cq_one() -> CQuat {
  cq_make(@core.quat_one(), @core.quat_zero())
}

///|
/// 純虛單位 `i`（複結構的生成元）。
pub fn cq_unit() -> CQuat {
  cq_make(@core.quat_zero(), @core.quat_one())
}

///|
pub fn cq_from_quat(a : @core.Quat) -> CQuat {
  cq_make(a, @core.quat_zero())
}

///|
pub fn cq_of_int(n : Int32) -> CQuat {
  cq_from_quat(@core.quat_of_qq(@core.qq_int(n)))
}

///|
pub fn cq_add(a : CQuat, b : CQuat) -> CQuat {
  cq_make(@core.quat_add(a.ca, b.ca), @core.quat_add(a.cb, b.cb))
}

///|
/// `(a + ib)(c + id) = (ac − bd) + i(ad + bc)`。
pub fn cq_mul(a : CQuat, b : CQuat) -> CQuat {
  let ac = @core.quat_mul(a.ca, b.ca)
  let bd = @core.quat_mul(a.cb, b.cb)
  let ad = @core.quat_mul(a.ca, b.cb)
  let bc = @core.quat_mul(a.cb, b.ca)
  cq_make(@core.quat_sub(ac, bd), @core.quat_add(ad, bc))
}

///|
/// 複共軛 `a − ib`。
pub fn cq_conj(a : CQuat) -> CQuat {
  cq_make(a.ca, @core.quat_neg(a.cb))
}

///|
pub fn cq_eq(a : CQuat, b : CQuat) -> Bool {
  @core.quat_eq(a.ca, b.ca) && @core.quat_eq(a.cb, b.cb)
}

///|
/// 複結構 `J(x) = i·x`（左乘複單位）。
pub fn cq_J(x : CQuat) -> CQuat {
  cq_mul(cq_unit(), x)
}

// ---------------------------------------------------------------------------
// 3. 四元數矩陣的 Hermitian 配對與頂點算子
// ---------------------------------------------------------------------------

///|
/// 四元數向量的 Hermitian 內積實部 `Σ Re(conj(u_i)·w_i)`。
pub fn susy_hdot(u : Array[@core.Quat], w : Array[@core.Quat]) -> @core.QQ {
  let mut acc = @core.qq_zero()
  let mut i = 0
  while i < u.length() {
    acc = @core.qq_add(
      acc,
      @core.quat_re(@core.quat_mul(@core.quat_conj(u[i]), w[i])),
    )
    i = i + 1
  }
  acc
}

///|
/// 四元數矩陣作用在向量上。
pub fn qm_apply(
  a : Array[Array[@core.Quat]],
  v : Array[@core.Quat],
) -> Array[@core.Quat] {
  let out : Array[@core.Quat] = Array::make(@core.qm_rows(a), @core.quat_zero())
  let mut i = 0
  while i < @core.qm_rows(a) {
    let mut acc = @core.quat_zero()
    let mut k = 0
    while k < @core.qm_cols(a) {
      acc = @core.quat_add(acc, @core.quat_mul(a[i][k], v[k]))
      k = k + 1
    }
    out[i] = acc
    i = i + 1
  }
  out
}

///|
/// 頂點算子 `V(z) = Σ_{n<k} A_n z^n`（截斷級數，係數是四元數矩陣）。
pub(all) struct VertexOp {
  modes : Array[Array[Array[@core.Quat]]]
}

///|
pub fn vertex_of(modes : Array[Array[Array[@core.Quat]]]) -> VertexOp {
  VertexOp::{ modes: modes }
}

///|
pub fn vertex_modes(v : VertexOp) -> Int32 {
  v.modes.length()
}

///|
/// 對偶頂點算子 `V*(z) = Σ_n A_n† z^{−n}`：逐模取共軛轉置。
pub fn vertex_dual(v : VertexOp) -> VertexOp {
  let out : Array[Array[Array[@core.Quat]]] = []
  let mut i = 0
  while i < v.modes.length() {
    out.push(@core.qm_conj_transpose(v.modes[i]))
    i = i + 1
  }
  VertexOp::{ modes: out }
}

///|
/// 第 `n` 階 Cauchy 卷積係數 `Σ_{i+j=n} A_i B_j`。
pub fn vertex_conv_coeff(
  a : VertexOp,
  b : VertexOp,
  n : Int32,
) -> Array[Array[@core.Quat]] {
  // 模矩陣一律是方陣（大小由第一個模決定）。
  let size = if a.modes.length() > 0 {
    @core.qm_rows(a.modes[0])
  } else if b.modes.length() > 0 {
    @core.qm_rows(b.modes[0])
  } else {
    0
  }
  let mut acc = @core.qm_zero(size, size)
  let mut i = 0
  while i <= n {
    let j = n - i
    if i < a.modes.length() && j >= 0 && j < b.modes.length() {
      acc = @core.qm_add(acc, @core.qm_mul_unchecked(a.modes[i], b.modes[j]))
    }
    i = i + 1
  }
  acc
}

///|
/// 截斷級數乘積（只保留前 `limit` 階）。
pub fn vertex_mul(a : VertexOp, b : VertexOp, limit : Int32) -> VertexOp {
  let out : Array[Array[Array[@core.Quat]]] = []
  let mut n = 0
  while n < limit {
    out.push(vertex_conv_coeff(a, b, n))
    n = n + 1
  }
  VertexOp::{ modes: out }
}

///|
/// 頂點對偶配對的第 `n` 階：`⟨A_n u, w⟩`（實值）。
pub fn vertex_pairing(
  v : VertexOp,
  n : Int32,
  u : Array[@core.Quat],
  w : Array[@core.Quat],
) -> @core.QQ {
  if n >= v.modes.length() {
    return @core.qq_zero()
  }
  susy_hdot(qm_apply(v.modes[n], u), w)
}
