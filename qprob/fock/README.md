# `qprob/fock/` — 全量子福克空間與 q-變形三統計分裂（Stage III · Layer 2）

> **架構位置**：套件 `qprob-fock`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 2**，`depends_on: [qprob-asymptotic, qprob-unbounded]`。
> **規模**：2 個 `.mbt` 檔、**776 行**、4 章、**13 條命題**（編號 `[034]–[046]`，含 2 條負控制）。

---

## 1. 數學結構定位與演變動因

第二階的 Favard 矩重構揭示：古典高斯矩給出線性增長的 Jacobi 次對角權重 $\beta_k = k$，而常數權重 $\beta_k = 1$ 則對應非交換自由概率的半圓律。要同時在單一希爾伯特空間框架下解釋這兩種統計以及費米 Pauli 不相容原理，必須構造單粒子空間 $\mathcal{H} = \mathbb{Q}^d$ 上的**全量子（Boltzmann）福克空間**與 **Bożejko–Speicher $q$-變形內積核**：
$$\mathcal{F}_0(\mathcal{H}) = \bigoplus_{n=0}^{\infty} \mathcal{H}^{\otimes n}, \qquad \langle e_{i_1}\otimes\dots\otimes e_{i_n},\, e_{j_1}\otimes\dots\otimes e_{j_n}\rangle_q = \sum_{\sigma \in S_n} q^{\mathrm{inv}(\sigma)} \prod_{k=1}^n \delta_{i_k, j_{\sigma(k)}}$$

當 $q \in [-1, 1]$ 連續變化時，Gram 核 $\mathcal{N}_q$ 的商空間維度在同一套演算法下自動分裂出三大量子統計：
* **$q = 0$（自由／Boltzmann 統計）**：無交換縮併，Cuntz–Toeplitz 等距代數 $\ell_i \ell_j^* = \delta_{ij} I$，場算子 $\ell^* + \ell$ 真空矩即 Catalan 半圓律；
* **$q = +1$（玻色 CCR 統計）**：全對稱張量商 $\mathrm{Sym}^n(\mathbb{Q}^d)$，維度 $\binom{d+n-1}{n}$；
* **$q = -1$（費米 CAR 統計）**：全反對稱外代數 $\Lambda^n(\mathbb{Q}^d)$，維度 $\binom{d}{n}$，當 $n > d$ 時核全空間坍縮為 $0$（Pauli 不相容定理）；
* **$|q| > 1$（超界負控制）**：出現負範數幽靈態，證明 Bożejko–Speicher 正定界 $|q|\le 1$ 緊緻不可放寬。

---

## 2. 檔案與職責

| 檔案 | 行數 | 核心型別與公開介面 |
|---|---:|---|
| `full_fock.mbt` | 435 | 張量基底詞 `FockWord`、稀疏正規形全福克態 `FullFockVec`、左創生 `fock_create_left`、$q$-變形左湮滅 `fock_annihilate_q`、置換枚舉與逆序數 `perm_inversions`、$q$-內積 `fock_inner_q`、扇區 Gram 矩陣 `fock_q_gram_matrix`、二次量子化函子 `fock_gamma` / `fock_dgamma` |
| `laws.mbt` | 341 | 4 章 / **13 條命題**（`fock_all_laws`） |

---

## 3. 核心演算法記錄與簡介

| 演算法函式 | 輸入 → 輸出 | 數學原理與複雜度簡介 |
|---|---|---|
| `fock_normalize` | `(Int32, Array[(FockWord, QVal)]) -> FullFockVec` | 將稀疏張量詞按長度與字典序正規排序、合併同基底詞係數並剔除零項，確保全福克向量具有唯一典範表示。 |
| `fock_create_left` / `fock_annihilate_q` | `(Array[QVal], FullFockVec) -> FullFockVec` | `fock_create_left` 在張量詞最左側張量乘入單粒子向量 $\ell^*(f)|w\rangle = f \otimes |w\rangle$；`fock_annihilate_q` 依 Leibniz $q$-規則計算 $\ell_q(g)(e_{i_1}\otimes\dots\otimes e_{i_n}) = \sum_{k=1}^n q^{k-1}\langle g, e_{i_k}\rangle e_{i_1}\otimes\dots\widehat{e_{i_k}}\dots\otimes e_{i_n}$，在真空 $|\Omega\rangle$ 上嚴格為 $0$。 |
| `symmetric_group_perms` / `perm_inversions` | `Int32 -> Array[Array[Int32]]` / `Array[Int32] -> Int32` | 生成對稱群 $S_n$ 全部 $n!$ 個置換並精確計算逆序對數 $\mathrm{inv}(\sigma) = |\{(a<b) : \sigma(a) > \sigma(b)\}|$。 |
| `fock_inner_q` / `fock_q_gram_matrix` | `(QVal, Int32, Int32) -> (Int32, Array[QVal])` | 在 $n$ 粒子扇區全部 $d^n$ 個正交張量詞上構造 $d^n \times d^n$ 的 Bożejko–Speicher $q$-Gram 矩陣，結合 `@asymptotic.qmat_rank` 精確算出物理商希爾伯特空間維度 $\dim \mathcal{F}_q^{(n)}(\mathbb{Q}^d) = \operatorname{rank}(G_q^{(n)})$。 |
| `fock_gamma` / `fock_dgamma` | `(Array[QVal], Int32, FullFockVec) -> FullFockVec` | **乘法二次量子化** $\Gamma(T)(v_1\otimes\dots\otimes v_n) = Tv_1 \otimes \dots \otimes Tv_n$（保持 $|\Omega\rangle$ 不變）與**微商二次量子化** $d\Gamma(H)(v_1\otimes\dots\otimes v_n) = \sum_{k=1}^n v_1\otimes\dots\otimes Hv_k\otimes\dots\otimes v_n$（消滅 $|\Omega\rangle$）。 |

---

## 4. 定理與命題記錄（`[034]–[046]`）

| 編號 | 定理／命題 | 實算見證與負控制 |
|---:|---|---|
| `[034]–[037]` | **Cuntz–Toeplitz 等距恆等式、真空餘投影與半圓律矩定理** | $\ell_i \ell_j^* = \delta_{ij}I$，$I - \sum_i \ell_i^*\ell_i = |\Omega\rangle\langle\Omega|$；場算子 $(\ell^*+\ell)^k$ 真空矩算出 Catalan 數 $[1,0,1,0,2,0,5,0,14]$ 並經 Favard 重構出 $\beta=[1,1,1]$；詞序非交換 $e_0\otimes e_1 \perp e_1\otimes e_0$。 |
| `[038]–[039]` | **普適 $q$-對易關係與 Bożejko–Speicher 伴隨定理** | 在 $q \in \{-1, -\frac{1}{2}, 0, \frac{1}{2}, 1\}$ 全數滿足 $\ell_q(g)\ell^*(f) - q\ell^*(f)\ell_q(g) = \langle g,f\rangle I$ 與 $80$ 對態上的伴隨恆等式 $\langle \ell^*(f)u, v\rangle_q = \langle u, \ell_q(f)v\rangle_q$。 |
| `[040]–[043]` | **三統計維度分裂與 $|q|\le 1$ 緊緻界定理** | $d=2,\ n=0..3$ 扇區 Gram 秩實算：$q=0,\frac{1}{2} \Rightarrow [1,2,4,8]$；$q=+1 \Rightarrow [1,2,3,4]$；$q=-1 \Rightarrow [1,2,1,0]$（3 費米子坍縮為 $0$）；$q=2$ 單重態範數平方 $=-2 < 0$。 |
| `[044]–[046]` | **二次量子化函子律與 Lie 代數同態** | $\Gamma(AB)=\Gamma(A)\Gamma(B)$，$\Gamma(I)=I$，$[d\Gamma(A), d\Gamma(B)] = d\Gamma([A,B])$，且 $d\Gamma(I)|\Psi_3\rangle = 3|\Psi_3\rangle$。 |
