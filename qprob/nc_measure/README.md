# `qprob/nc_measure/` — 非交換隨機分佈、POVM 算子測度與自由累積量統合（Stage V · Layer 4）

> **架構位置**：套件 `qprob-nc-measure`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 4**，`depends_on: [qprob-asymptotic, qprob-unbounded, qprob-fock, qprob-ccr-field]`。
> **規模**：2 個 `.mbt` 檔、**792 行**、4 章、**13 條命題**（編號 `[058]–[070]`，含 2 條負控制）。

---

## 1. 數學結構定位與演變動因

在非交換量子場與有限維量子系統中，不對易觀測量不存在古典 Kolmogorov 聯合 $\sigma$-代數機率測度。因此古典概率測度在第五階分裂並升華為兩個緊密對偶的非交換測度結構：
1. **正算子值測度（POVM）與 Naimark 等距擴張**：一般量子量測由滿足 $\sum_{k=0}^{K-1} M_k^\dagger M_k = I$ 的非正交、非對易效應算子族 $E_k = M_k^\dagger M_k$ 描述（Born 機率 $p_k = \operatorname{Tr}(\rho E_k)$）；藉由 Naimark 擴張定理，任意過完備 POVM 皆可透過分塊等距算子 $V : \mathcal{H} \hookrightarrow \mathbb{C}^K \otimes \mathcal{H}$ 還原為高維擴張空間上的正交投影譜測度（PVM）$E_k = V^\dagger P_k V$。
2. **Speicher 非交叉自由累積量與自由中心極限定理（Free CLT）**：當獨立性由張量積交換獨立替換為全福克自由獨立時，矩-累積量展開的配分格由全體配分格 $\Pi(n)$ 收縮為**非交叉配分格 $\mathrm{NC}(n)$**。四階交叉配分 $(13)(24) \in \Pi(4)\setminus\mathrm{NC}(4)$ 的消去，精確解釋了為何高斯場四階矩為 $3$（古典 $c_4=0$），而半圓自由場四階矩為 Catalan 數 $C_2 = 2$（自由 $\kappa_4=0$）。

---

## 2. 檔案與職責

| 檔案 | 行數 | 核心型別與公開介面 |
|---|---:|---|
| `noncommutative_measure.mbt` | 384 | 過完備算子測度 `PovmMeasure`、`povm_effect`、`povm_is_complete`、`povm_is_projective`、`povm_born_probabilities`、Naimark 構造檢驗 `verify_naimark_dilation`、Speicher 正逆轉換 `moments_to_free_cumulants` / `free_cumulants_to_moments`、自由加性卷積 `free_additive_convolution_moments`、`free_clt_scaled_moments`、古典累積量 `moments_to_classical_cumulants`、CPTP 通道 `apply_cptp_channel` |
| `laws.mbt` | 408 | 4 章 / **13 條命題**（`nc_all_laws`） |

---

## 3. 核心演算法記錄與簡介

| 演算法函式 | 輸入 → 輸出 | 數學原理與複雜度簡介 |
|---|---|---|
| `povm_born_probabilities` / `apply_cptp_channel` | `(PovmMeasure, QuantumProbState) -> Array[QVal]` | 驗算完備性 $\sum_k M_k^\dagger M_k = I$ 後，分別給出 Born 機率向量 $p_k = \operatorname{Tr}(\rho M_k^\dagger M_k) \in \mathbb{Q}_{\ge 0}$ 與對偶 CPTP Kraus 密度演化 $\Phi(\rho) = \sum_k M_k \rho M_k^\dagger$（保跡且保正定）。 |
| `verify_naimark_dilation` | `PovmMeasure -> (Int32, Bool)` | **構造性 Naimark 等距擴張演算法**：將 $K$ 個 $d\times d$ Kraus 根垂直堆疊為 $(Kd)\times d$ 分塊等距矩陣 $V = [M_0;\dots;M_{K-1}]$，並在擴張空間 $\mathbb{C}^{Kd}$ 構造對角分塊投影 $P_k = |k\rangle\langle k|\otimes I_d$，逐項驗證 $V^\dagger V = I_d$、$P_j P_k = \delta_{jk} P_k$、$\sum_k P_k = I_{Kd}$ 及壓縮恆等式 $V^\dagger P_k V = E_k$。 |
| `moments_to_free_cumulants` / `free_cumulants_to_moments` | `Array[QVal] -> Array[QVal]` | **Speicher 非交叉矩—累積量雙向遞迴演算法**：利用 R-變換與矩生成函數恆等式 $m_n = \sum_{s=1}^n \kappa_s (m^{*s})_{n-s}$，以 $O(N^3)$ 遞推維護 Cauchy 卷積冪 $m^{*s}$ 實作正逆雙射，免除指數級枚舉全部 Catalan 個非交叉配分。 |
| `free_additive_convolution_moments` | `(Array[QVal], Array[QVal]) -> Array[QVal]` | 利用自由累積量的可加線性化性質 $\kappa_n(\mu \boxplus \nu) = \kappa_n(\mu) + \kappa_n(\nu)$：先將兩輸入矩序列轉為自由累積量、逐項相加後再逆轉回合成矩序列。 |
| `free_clt_scaled_moments` | `(Array[QVal], Int32) -> Array[QVal]` | 對零均值單位變異數分佈計算自由獨立和 $S_N = \frac{X_1 \boxplus \dots \boxplus X_N}{\sqrt{N}}$ 的精確矩序列（奇數階清零、第 $n$ 階自由累積量縮放為 $N \cdot N^{-n/2}\kappa_n = N^{1-n/2}\kappa_n$）。 |
| `moments_to_classical_cumulants` | `Array[QVal] -> Array[QVal]` | 古典指數生成函數遞迴 $c_n = m_n - \sum_{s=1}^{n-1}\binom{n-1}{s-1} c_s m_{n-s}$，供古典對自由配分格分岔比較使用。 |

---

## 4. 定理與命題記錄（`[058]–[070]`）

| 編號 | 定理／命題 | 實算見證與負控制 |
|---:|---|---|
| `[058]–[061]` | **過完備非交換 POVM、Born 機率律與 CPTP 保跡定理** | $\mathbb{C}^2$ 上 4 結果勾股秩-1 POVM 滿足 $\sum_{k=0}^3 E_k = I_2$、$[E_1,E_2]\neq 0$ 且 $E_k^2 \neq E_k$；Born 機率總和 $=1$；不完備算子族被 POVM 與 CPTP 雙重拒絕。 |
| `[062]–[063]` | **Naimark 等距擴張定理與正交 PVM 刻畫** | 2 維 4 結果非正交 POVM 等距嵌入 $\mathbb{C}^8$ 正交 PVM（$V^\dagger V = I_2,\ V^\dagger P_k V = E_k$）。 |
| `[064]–[067]` | **Speicher 雙射、半圓律、自由 Poisson 與四階交叉分岔定理** | 正逆轉換無損還原；Catalan 矩自由累積量 $\kappa_2=1,\ \kappa_{n\neq 2}=0$（至 8 階全零）；$\mathrm{FreePoisson}(1)$ 累積量恆為 $[1,1,1,1,1]$；高斯律 $(c_4,\kappa_4)=(0,1)$ 對偶半圓律 $(c_4,\kappa_4)=(-1,0)$。 |
| `[068]–[070]` | **Voiculescu 自由中心極限定理、自由卷積半群與五階對偶閉環** | Rademacher 自由和在 $N=[1,4,9]$ 經 Richardson 外推零誤差命中半圓律 $m_4=2, m_6=5$；$\mathrm{FreePoisson}(2)\boxplus\mathrm{FreePoisson}(3)=\mathrm{FreePoisson}(5)$（矩 $[1,5,30,195,1530]$）；Stage IV 連續場 Wick 矩 $(m_6=15 \Rightarrow c_4=c_6=0)$ 與 Stage III 全福克矩 $(m_6=5 \Rightarrow \kappa_4=\kappa_6=0)$ 雙路閉合。 |
