# `qprob/unbounded/` — 無界算子概率空間與矩問題重構（Stage II · Layer 1）

> **架構位置**：套件 `qprob-unbounded`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 1**，`depends_on: [qprob-asymptotic]`。
> **規模**：2 個 `.mbt` 檔、**906 行**、4 章、**12 條命題**（編號 `[022]–[033]`，含 3 條負控制）。

---

## 1. 數學結構定位與演變動因

當第一階射影極限的截斷維度 $d \to \infty$ 時，量子諧振子粒子數算子 $N|n\rangle = n|n\rangle$ 與正則位置／動量算子 $Q, P$ 的算子範數發散（$\|N_d\| = d-1 \to \infty$），傳統有界 $C^*$-代數 $\mathcal{B}(\mathcal{H})$ 不再對無界生成元封閉。

本套件抽象出**共同不變稠密核 $\mathcal{D}$ 上的無界 $^*$-代數概率空間 $(\mathcal{D}, \mathrm{Op}^*(\mathcal{D}), \varphi)$**：
* 每個算子顯式追蹤 Sobolev 多項式成長階 `growth_deg`（$\|A|n\rangle\| \le C(1+n)^k$），確保複合 $A \circ B$ 在快速衰減核 $\mathcal{D}$ 上處處良構且滿足成長階次可加性 $\deg(AB) = \deg(A) + \deg(B)$；
* 量子概率態 $\varphi(A) = \operatorname{Tr}(\rho A)$ 在無界觀測量上誘導非交換期望、協方差、Yosida 預解正則化與 Stieltjes–Hamburger 矩重構。

---

## 2. 檔案與職責

| 檔案 | 行數 | 核心型別與公開介面 |
|---|---:|---|
| `probability_space.mbt` | 543 | 高斯有理複數 `QComplex`、無界算子 `UnboundedOp`（零算子、中心化、伴隨、複合、交換子、反交換子、粒子數與對偶 Jacobi 算子）、量子概率態 `QuantumProbState`（純態與 Gibbs 混合態）、`check_robertson_schrodinger`、`yosida_diagonal_approximant`、`reconstruct_jacobi_from_moments` |
| `laws.mbt` | 363 | 4 章 / **12 條命題**（`unbounded_all_laws`） |

---

## 3. 核心演算法記錄與簡介

| 演算法函式 | 輸入 → 輸出 | 數學原理與複雜度簡介 |
|---|---|---|
| `uop_mul` / `uop_scale` | `(UnboundedOp, UnboundedOp) -> UnboundedOp` | 複有理矩陣複合並累加非零算子的多項式成長階 `a.growth_deg + b.growth_deg`；若任一算子為零或純量為 `0`，自動收斂 `growth_deg = 0`。 |
| `qstate_pure` / `qstate_diagonal_gibbs` | `Array[QComplex] -> QuantumProbState?` / `Array[QVal] -> QuantumProbState?` | 由未正規化態向量 $|\psi\rangle$ 構造投影密度矩陣 $|\psi\rangle\langle\psi|/\|\psi\|^2$，或由非負 Boltzmann 權重構造混合態 $\operatorname{diag}(w_n)/Z$；零範數或負權重嚴格回傳 `None`。 |
| `check_robertson_schrodinger` | `(QuantumProbState, UnboundedOp, UnboundedOp) -> UncertaintyBound` | 以共用中心化算子 $A_0 = A - \varphi(A)I$ 精確計算變異數乘積 $\operatorname{Var}_\varphi(A)\operatorname{Var}_\varphi(B)$、交換子下界 $\frac{1}{4}|\varphi([A,B])|^2$ 與反交換協方差項 $\frac{1}{4}|\varphi(\{A_0,B_0\})|^2$，回傳完整不等式證書。 |
| `yosida_diagonal_approximant` | `(Array[QVal], QVal) -> UnboundedOp?` | 對非負無界自伴譜 $\{\lambda_n \ge 0\}$ 與正則化參數 $\gamma > 0$，構造有界預解逼近 $A_\gamma = \gamma A (\gamma I + A)^{-1} = \operatorname{diag}\!\big(\frac{\gamma \lambda_n}{\gamma + \lambda_n}\big)$（`growth_deg = 0`，範數嚴格 $< \gamma$），負特徵值輸入回傳 `None`。 |
| `reconstruct_jacobi_from_moments` | `(Array[QVal], Int32) -> JacobiMomentReconstruction?` | **Favard–Chebyshev–Lanczos 正交多項式三項遞迴演算法**：僅由前 $2n$ 階矩序列 $\{m_0,\dots,m_{2n-1}\}$ 透過單一線性矩泛函 $\mathcal{L}(x^k)=m_k$ 遞迴正交化 $P_{k+1}(x) = (x-\alpha_k)P_k(x) - \beta_k P_{k-1}(x)$，精確反演出無界 Jacobi 三對角算子係數 $(\alpha_k, \beta_k)$；一旦偵測到平方範數 $h_k \le 0$（違反 Hankel 正定性），立即回傳 `None`。 |

---

## 4. 定理與命題記錄（`[022]–[033]`）

| 編號 | 定理／命題 | 實算見證與負控制 |
|---:|---|---|
| `[022]–[025]` | **無界 $^*$-代數反自同構、Lie–Jacobi 恆等式與 Dirac 對易子** | $(Q_J P_J)^\dagger = P_J^\dagger Q_J^\dagger$，$\deg(Q_J P_J)=2$；$[[N,Q_J],P_J]+\text{cyc}=0$；$i[Q_J,P_J]$ 自伴而 $[Q_J,P_J]\neq 0$。 |
| `[026]–[027]` | **GNS Cauchy–Schwarz 定理與非正態攔截** | $50$ 對無界算子全滿足 $|\varphi(X^\dagger Y)|^2 \le \varphi(X^\dagger X)\varphi(Y^\dagger Y)$；負權重泛函與零態向量回傳 `None`。 |
| `[028]–[029]` | **Robertson–Schrödinger 無界不確定性原理與基態飽和** | 真空態 $|0\rangle$ 精確飽和 $\operatorname{Var}(Q)\operatorname{Var}(P) = 1 = \frac{1}{4}|\langle[Q,P]\rangle|^2$；相干疊加態與 Gibbs 混合態在非零協方差項下嚴格成立。 |
| `[030]` | **Yosida 有界預解正則化收斂定理** | $\|A_\gamma\| < \gamma$（有界階 $0$），且隨 $\gamma = 10, 20, 40$ 單調上升逼近無界粒子數期望 $\varphi(N)$。 |
| `[031]–[033]` | **Favard–Hermite 與 Poisson–Charlier 矩重構定理** | 高斯雙階乘矩 $[1,0,1,0,3,0,15,0]$ 反演出 $\alpha=[0,0,0,0],\ \beta=[1,2,3]$（自然湧現玻色福克權重！）；Poisson Bell 矩 $[1,1,2,5,15,52]$ 反演出 $\alpha=[1,2,3],\ \beta=[1,2]$；非正定偽矩 $[1,0,-1,0]$ 被攔截。 |
