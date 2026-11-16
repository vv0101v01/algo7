# 量子概率、非交換隨機空間與量子機率脈絡範疇合流 — 88 條定理與 26 項演算法完整記錄

> **對應分支與模組**：`7.1` · `qprob/{asymptotic,unbounded,fock,ccr_field,nc_measure,context_cat}` + `cmd/qprob` + `cmd/showcase`
> **驗證狀態**：`moon run cmd/qprob --target wasm-gc` → **`通過 88 / 88 個結構演化定理與演算法命題`**；`moon run cmd/showcase --target wasm-gc` → **`quantum probability context confluence: bicat=8, fibered_props=8, monad_kleisli=true, presheaf_gluing=true, diamond_confluence=true, noncomm_obstruction=true, holds=true`**。

本文檔對 `7.1` 分支開發完成的六階量子概率子聯邦（**16 個 `.mbt` 檔、6,503 行純 MoonBit 程式碼**）所實作的 **26 項符號／代數演算法** 與 **全部 88 條形式驗證命題（含 16 條負控制與分岔命題）** 作出完整記錄、數學原理與複雜度簡介，以及執行期精確有理數見證對照。

---

## 第一部分：核心演算法總錄（26 項演算法）

### Stage I · 代數子場與漸近極限演算法（`qprob/asymptotic`）

1. **正規形任意精度有理算術與負指數求冪（`qv_make`, `qv_pow`）**
   * **原理**：所有有理數 $p/q \in \mathbb{Q}$ 均以 `BigInt` 儲存並以 Euclid `qv_gcd` 化約為唯一正規形（$q > 0,\ \gcd(|p|,q)=1$，`0` 唯一表示為 `0/1`）。負整數次冪 $x^{-n}$ 先經 `qv_inv` 取逆再以 $O(\log |n|)$ 二進位反覆平方法計算。
2. **二次代數擴張體有理化求逆（`quad_inv`）**
   * **原理**：在 $\mathbb{Q}(\sqrt{d}) = \{a + b\sqrt{d} : a,b \in \mathbb{Q}\}$ 上定義 Galois 共軛 $\sigma(a+b\sqrt{d}) = a-b\sqrt{d}$ 與範數 $N(x) = a^2 - d b^2$。當 $N(x)\neq 0$ 時回傳 $\sigma(x)/N(x)$；當 $N(x)=0$（含非無平方因子 $d=k^2$ 的零因子 $k \pm \sqrt{k^2}$）時回傳 `None`。
3. **截斷非阿基米德 Laurent 噴流乘法與形式級數長除法求逆（`jet_mul`, `jet_inv`, `jet_standard_part`）**
   * **原理**：表示形式 Laurent 截斷級數 $\sum_{k=v}^{M} c_k \varepsilon^k \in \mathbb{Q}((\varepsilon))_{\le M}$，其中無窮小生成元滿足 $0 < \varepsilon^2 < \varepsilon < r$（$\forall r \in \mathbb{Q}_{>0}$）。求逆時提取首項 $c_v \varepsilon^v$（$c_v \neq 0$），對正規化冪級數執行 $O((M-v)^2)$ 遞迴長除法得截斷逆元。標準部商同態 $\mathrm{st}$ 對有界子環（$v \ge 0$）投出常數項 $c_0$，對無窮大元（$v < 0$）回傳 `None`。
4. **精確有理高斯列梯形矩陣秩（`qmat_rank`）**
   * **原理**：在 $\mathbb{Q}^{r\times c}$ 上執行非零主元搜尋、列交換與主元下方消去（上三角 Row-Echelon Form），避免浮點閾值誤判，時間複雜度 $O(\min(r,c)\cdot r\cdot c)$。
5. **射影極限塔相容執行緒檢驗與 Mittag-Leffler 穩定像秩（`tower_is_coherent_thread`, `tower_mittag_leffler_stable_rank`）**
   * **原理**：對射影系統 $(V_0 \xleftarrow{\pi_{0,1}} V_1 \xleftarrow{\pi_{1,2}} \dots \xleftarrow{} V_K)$，以複合轉移矩陣 $\pi_{j,k} = \pi_{j,j+1}\cdots\pi_{k-1,k}$ 驗證執行緒相容性 $\pi_{k,k+1}(x_{k+1})=x_k$，並以 $\operatorname{rank}(\pi_{k, K})$ 度量遠端穩定像子空間維度。
6. **Richardson–Neville 多項式連續極限外推（`richardson_extrapolate_limit`）**
   * **原理**：給定正整數尺度序列 $N_0,\dots,N_{m-1} > 0$ 與近似值 $A(N_i) = L + \sum_{r=1}^{m-1} c_r N_i^{-r}$，令 $h_i = 1/N_i$，以 $O(m^2)$ Neville 插值表在 $h = 0$ 求值，零誤差消去全部 $m-1$ 階離散截斷誤差。
7. **Shanks–Aitken $\Delta^2$ 單模態加速（`shanks_aitken_step`）**
   * **原理**：計算前向差分 $\Delta s_n = s_{n+1}-s_n$、$\Delta^2 s_n = s_{n+2}-2s_{n+1}+s_n$，映射 $s'_n = s_n - (\Delta s_n)^2 / \Delta^2 s_n$，對單一指數暫態 $s_n = L + c\lambda^n$（$\lambda \neq 1$）一步精確還原極限 $L$。
8. **Wynn $\varepsilon$-菱形多模態加速（`wynn_epsilon_limit`）**
   * **原理**：構造二維表 $\varepsilon_{-1}^{(n)}=0,\ \varepsilon_0^{(n)}=s_n,\ \varepsilon_{k+1}^{(n)} = \varepsilon_{k-1}^{(n+1)} + (\varepsilon_k^{(n+1)} - \varepsilon_k^{(n)})^{-1}$。依據 Wynn–Padé 定理，偶數列 $\varepsilon_{2K}^{(n)}$ 等價於 $[K/K]$ Padé–Shanks 行列式比，能以 $2K+1$ 個樣本零誤差同時消去 $K$ 個獨立指數暫態 $\sum_{j=1}^K c_j \lambda_j^n$。
9. **Cesàro 遍歷時間平均（`cesaro_mean`）**
   * **原理**：計算 $\bar{s}_N = \frac{1}{N}\sum_{k=0}^{N-1} s_k$，正則化無逐點極限但具遍歷平均的量子酉演化振盪序列。

---

### Stage II · 無界算子概率與正交多項式矩重構演算法（`qprob/unbounded`）

10. **共同不變稠密核無界 $^*$-代數算術（`uop_mul`, `uop_scale`, `uop_commutator`, `uop_anticommutator`）**
    * **原理**：在高斯有理複數體 $\mathbb{Q}(i)$ 上維護算子矩陣與 Sobolev 多項式成長階 `growth_deg`。非零複合累加成長階 $\deg(AB) = \deg(A)+\deg(B)$；零純量或零算子自動收斂成長階至 `0`。
11. **GNS 量子概率態構造與共用中心化算子（`qstate_pure`, `qstate_diagonal_gibbs`, `qstate_variance`）**
    * **原理**：強制檢驗密度矩陣自伴性、單位跡 $\operatorname{Tr}(\rho) = 1$ 及 Boltzmann 權重非負性；內部共用中心化算子 $A_0 = A - \varphi(A)I$ 以消除重複配置。
12. **Robertson–Schrödinger 完全不確定性證書（`check_robertson_schrodinger`）**
    * **原理**：對任意量子態 $\varphi$ 與兩無界觀測量 $A, B$，精確算出左式 $\operatorname{Var}_\varphi(A)\operatorname{Var}_\varphi(B)$、交換子下界 $\frac{1}{4}|\varphi([A,B])|^2$ 與反交換協方差項 $\frac{1}{4}|\varphi(\{A_0,B_0\})|^2$，同時支援不等式檢驗與真空最小不確定性飽和判定。
13. **Yosida 預解有界逼近（`yosida_diagonal_approximant`）**
    * **原理**：對非負自伴無界譜 $\{\lambda_n \ge 0\}$ 與 $\gamma > 0$，構造有界算子 $A_\gamma = \gamma A(\gamma I + A)^{-1} = \operatorname{diag}(\frac{\gamma\lambda_n}{\gamma+\lambda_n})$（`growth_deg == 0`），拒絕負特徵值輸入，並隨 $\gamma \to \infty$ 單調上升收斂至無界期望 $\varphi(A)$。
14. **Favard–Chebyshev–Lanczos 正交多項式矩重構（`reconstruct_jacobi_from_moments`）**
    * **原理**：輸入前 $2n$ 階矩 $m_0=1, m_1, \dots, m_{2n-1}$，定義線性矩泛函 $\mathcal{L}(\sum c_j x^j) = \sum c_j m_j$，在單一迴圈中遞推首一正交多項式 $P_0=1,\ P_{k+1} = (x-\alpha_k)P_k - \beta_k P_{k-1}$，反演三對角 Jacobi 係數 $(\alpha_k, \beta_k)$；若偵測到 $\mathcal{L}(P_k^2) \le 0$（違反 Hankel 正定性），立即回傳 `None`。

---

### Stage III · 全量子福克空間與 $q$-變形演算法（`qprob/fock`）

15. **稀疏張量詞正規化與 $q$-變形創生／湮滅（`fock_normalize`, `fock_create_left`, `fock_annihilate_q`）**
    * **原理**：在 $\mathcal{F}_0(\mathbb{Q}^d) = \bigoplus_{n\ge 0} (\mathbb{Q}^d)^{\otimes n}$ 上以排序稀疏基底詞 `(FockWord, QVal)` 唯一表示量子態；左創生前置單粒子向量，左 $q$-湮滅依跨位權重 $q^{k-1}$ 縮併第 $k$ 個張量因子，嚴格滿足 $\ell_q(g)\ell^*(f) - q\ell^*(f)\ell_q(g) = \langle g,f\rangle I$。
16. **對稱群逆序核與 Bożejko–Speicher $q$-Gram 商維度（`fock_inner_q`, `fock_q_gram_matrix`）**
    * **原理**：枚舉 $\sigma \in S_n$ 並計算逆序數 $\mathrm{inv}(\sigma)$，組合出 $n$ 粒子扇區 $d^n \times d^n$ Gram 矩陣 $G_q^{(n)}$，再呼叫 `qmat_rank` 算出物理商空間 $\mathcal{F}_0^{(n)} / \ker G_q^{(n)}$ 維度。
17. **乘法與微商二次量子化函子（`fock_gamma`, `fock_dgamma`）**
    * **原理**：在稀疏張量詞上實作張量積提升 $\Gamma(T)(v_1\otimes\dots\otimes v_n) = Tv_1\otimes\dots\otimes Tv_n$（保持么半群結構與真空）與導子提升 $d\Gamma(H) = \sum_{k=1}^n I^{\otimes(k-1)}\otimes H \otimes I^{\otimes(n-k)}$（保持 Lie 括號同態）。

---

### Stage IV · 連續塗抹算子場、Wick 縮併與量子隨機微積分演算法（`qprob/ccr_field`）

18. **多項式測試函數精確 $L^2([a,b])$ 內積與格點橋接（`continuum_l2_inner`, `fock_lattice_bosonic_commutator`）**
    * **原理**：將測試函數表為有理多項式，經係數卷積與解析原函數 $\frac{b^{k+1}-a^{k+1}}{k+1}$ 算出零誤差連續內積；同時提供 $N$ 點離散格點福克對易子，供 Richardson 外推驗證離散至連續場收斂。
19. **遞迴 Leibniz–Wick 正規序展開與多點關聯提取（`wick_normal_order`, `wick_vacuum_expectation`）**
    * **原理**：自右向左將任意場算子乘積正規序化；湮滅因子穿過創生因子時分裂為「交換穿透項」與「純量 $L^2$ 縮併項」，合併同類正規序算子詞後，真空期望值即常數縮併項係數。
20. **Weyl 辛上循環與 Hudson–Parthasarathy 量子 Itô 微元代數（`weyl_symplectic_form`, `qsde_ito_product`）**
    * **原理**：計算複測試函數相空間辛形式 $\sigma(f,g) = \operatorname{Im}\langle f,g\rangle$，並在四維微元基底 $\{dt, dA_t, dA_t^\dagger, d\Lambda_t\}$ 上實作非交換量子 Itô 二次變差乘法表（核心非零二次項 $dA_t \cdot dA_t^\dagger = dt$）。

---

### Stage V · 非交換算子測度與自由累積量演算法（`qprob/nc_measure`）

21. **過完備 POVM Born 機率與對偶 Kraus CPTP 通道（`povm_born_probabilities`, `apply_cptp_channel`）**
    * **原理**：驗證 $\sum_{k=0}^{K-1} M_k^\dagger M_k = I_d$ 後，在 Heisenberg 繪景計算 $p_k = \operatorname{Tr}(\rho E_k)$，並在 Schrödinger 繪景演化密度矩陣 $\Phi(\rho) = \sum_k M_k \rho M_k^\dagger$。
22. **構造性 Naimark 等距擴張檢驗（`verify_naimark_dilation`）**
    * **原理**：將 $K$ 個 $d\times d$ Kraus 算子堆疊為 $(Kd)\times d$ 等距算子 $V$，在擴張空間 $\mathbb{C}^{Kd}$ 構造正交投影族 $P_k = |k\rangle\langle k|\otimes I_d$，逐項驗證 $V^\dagger V = I_d$、正交完備性與壓縮還原 $V^\dagger P_k V = E_k$。
23. **Speicher 非交叉矩—自由累積量雙向遞迴與自由卷積（`moments_to_free_cumulants`, `free_cumulants_to_moments`, `free_additive_convolution_moments`）**
    * **原理**：利用非交叉生成函數關係 $m_n = \sum_{s=1}^n \kappa_s (m^{*s})_{n-s}$ 以 $O(N^3)$ 遞推維護 Cauchy 卷積冪實現正逆雙射，並藉由 $\kappa_n(\mu \boxplus \nu) = \kappa_n(\mu)+\kappa_n(\nu)$ 計算自由加性卷積與自由 CLT 縮放矩。

---

### Stage VI · 雙範疇、主命題纖維化、有理機率單子與脈絡合流演算法（`qprob/context_cat`）

24. **空間—子場雙範疇複合與 Godement 縱橫互換檢驗（`bicat_comp1`, `bicat_vcomp2`, `bicat_hcomp2`, `bicat_check_interchange`）**
    * **原理**：在 8 類空間／子場 0-胞上檢驗 1-態射源匯複合與正定保持性，並實作 2-態射水平 Whiskering 與垂直複合，驗證 $(\beta_2\circ_h\alpha_2)\circ_v(\beta_1\circ_h\alpha_1) == (\beta_2\circ_v\beta_1)\circ_h(\alpha_2\circ_v\alpha_1)$。
25. **Grothendieck 主命題纖維化笛卡兒提升與唯一泛因式分解（`pullback_principal_prop`, `cartesian_lift_morphism`, `factor_through_cartesian_lift`）**
    * **原理**：在 8 個基底物件的主命題纖維上計算逆變拉回贗函子 $f^*$、構造笛卡兒提升 $\mathrm{Cart}(f, R) : (X, f^*R) \to (Z, R)$，並對任意滿足基底分解 $g = f \circ u$ 的命題態射自動合成唯一中介態射 $\bar{u}$。
26. **Giry–Lawvere 有限有理機率單子、CPTP 對偶與 Bohr 脈絡菱形合流（`dist_bind`, `verify_cptp_kleisli_duality`, `verify_qctx_diamond_confluence`, `verify_grand_qprob_context_confluence`）**
    * **原理**：實作精確去重正規化單子 $(D_{\mathbb{Q}}, \eta, \mu)$ 與 Kleisli 通道合成；在兩兩對易觀測量定義的量子機率脈絡範疇 $\mathbf{QProbCtx}$ 上驗證效應逆變拉回守恆、預層截面三路自然性、非對易脈絡阻礙，以及不等價粗粒化脈絡菱形合流。

---

## 第二部分：全部 88 條形式驗證命題逐條記錄（`[001]–[088]`）

### Stage I · `qprob/asymptotic`（21 條命題：`[001]–[021]`）

| # | 章節 | 命題標籤與數學內容 | 執行期精確見證 |
|---:|---|---|---|
| `[001]` | Ch 1 | $\mathbb{Q}(\sqrt{2})$ 加法與乘法結合律與分配律 | $6^3 = 216$ 組樣本恆等成立 |
| `[002]` | Ch 1 | $\mathbb{Q}(\sqrt{2})$ 非零元素皆可逆（範數 $a^2-2b^2$ 在 $\mathbb{Q}$ 上無非平凡零解） | 全部非零測試元滿足 $x\cdot x^{-1}=1$ |
| `[003]` | Ch 1 | 範數乘法性 $N(xy)=N(x)N(y)$ 與共軛積 $x\bar{x}=N(x)\in\mathbb{Q}$ | $6^2 = 36$ 對樣本精確相等 |
| `[004]` | Ch 1 | Galois 子場定理 $\mathrm{Fix}(\sigma) = \mathbb{Q}$ | $6$ 樣本中 $4$ 個真擴張元被共軛移動，不動點恰為基體 $\mathbb{Q}$ |
| `[005]` | Ch 1 | $(\sqrt{2})^2 = 2 + 0\sqrt{2}$ 落回基子場 $\mathbb{Q}$，且負指數有理冪滿足乘法群律 | $(2/3)^{-3} = 27/8$ 且 $(2/3)^3\cdot(2/3)^{-3}=1$ |
| `[006]` | Ch 1 | **[負控制]** $d=4$ 非無平方因子產生零因子範數崩潰攔截 | $N(2+\sqrt{4}) = 0$，`quad_inv` 拒絕回傳 `None` |
| `[007]` | Ch 2 | 非阿基米德有序場嚴格序階層 | $0 < \varepsilon^2 < \varepsilon < 1/1000 < 1 < \varepsilon^{-1}$ |
| `[008]` | Ch 2 | 漸近 Laurent 噴流含奇異首項的形式長除法反元素 | $(\varepsilon^{-1}+2+3\varepsilon)^{-1}$ 賦值階為 $+1$ 且乘積 $\equiv 1 \pmod{\varepsilon^5}$ |
| `[009]` | Ch 2 | 標準部商同態定理 $\mathrm{st} : \mathbb{Q}[[\varepsilon]] \to \mathbb{Q}$ 保加法與乘法 | $\mathrm{st}(a\cdot b) = -15/8$，完全消去 $O(\varepsilon)$ 項 |
| `[010]` | Ch 2 | 標準部商核刻畫 $\ker(\mathrm{st}) = \varepsilon\cdot\mathbb{Q}[[\varepsilon]]$ | $a-\mathrm{st}(a)$ 賦值階 $= 1 \ge 1$，且 $a-a$ 為零噴流 |
| `[011]` | Ch 2 | **[負控制]** 無窮大噴流元不屬於有界子環無標準部 | $\varepsilon^{-1}+2+3\varepsilon$（$\mathrm{val}=-1$）經 `jet_standard_part` 回傳 `None` |
| `[012]` | Ch 3 | 射影極限相容執行緒判準 $\pi_{N,N+1}(x_{N+1}) = x_N$ | 指數相干態截斷 $(1/k!)_{k\le N}$ 在 $\varprojlim \mathbb{Q}^{N+1}$ 各層嚴格相容 |
| `[013]` | Ch 3 | 遠端射影轉移函子複合律 | $\pi_{0,3}(x_3) = [1, 1/2] = x_0$ |
| `[014]` | Ch 3 | Mittag-Leffler 滿射穩定像定理 | 截斷塔穩定像秩 $= [2, 3, 4]$（無穩定化虧損） |
| `[015]` | Ch 3 | 非滿射 Mittag-Leffler 子空間收縮 | 秩 $1$ 投影塔 $\operatorname{Im}(\pi_{0,3})$ 穩定維度 $= 1 < 2$ |
| `[016]` | Ch 3 | **[負控制]** 破壞第 1 層座標的偽執行緒攔截 | `tower_is_coherent_thread` 精確拒絕回傳 `false` |
| `[017]` | Ch 4 | Richardson 漸近外推消去高階離散誤差定理 | 4 點尺度 $[1,2,3,4]$ 消去 $N^{-1}..N^{-3}$ 誤差，精確命中 $L = 7/3$ |
| `[018]` | Ch 4 | Shanks–Aitken $\Delta^2$ 單模態精確極限定理 | $s_n = \frac{11}{5} + 3\cdot(\frac{1}{3})^n$ 單步變換全數恆等於 $11/5$ |
| `[019]` | Ch 4 | 二階 Shanks–Wynn $\varepsilon_4$ 雙模態精確極限定理 | 5 點序列 $2 + (\frac{1}{2})^n + (-\frac{1}{3})^n$ 經 $\varepsilon$-算法零誤差命中極限 $2$ |
| `[020]` | Ch 4 | Cesàro 遍歷平均正則化定理 | 振盪序列 $\frac{9}{4} + (-1)^k$ 在偶視窗 $N=8$ 平均收斂至 $9/4$（末項仍為 $5/4$） |
| `[021]` | Ch 4 | **[負控制]** 含奇異尺度 $N=0$ 輸入的外推攔截 | `richardson_extrapolate_limit` 回傳 `None` |

---

### Stage II · `qprob/unbounded`（12 條命題：`[022]–[033]`）

| # | 章節 | 命題標籤與數學內容 | 執行期精確見證 |
|---:|---|---|---|
| `[022]` | Ch 5 | 無界生成元自伴性定理 | 粒子數算子 $N$、位置算子 $Q_J$ 與對偶動量算子 $P_J$ 在 $\mathcal{D}_5$ 上皆滿足 $A^\dagger = A$ |
| `[023]` | Ch 5 | 無界 $^*$-代數反自同構與多項式成長階可加律 | $(Q_J P_J)^\dagger = P_J^\dagger Q_J^\dagger$，且 $\deg(Q_J P_J) = 2 = 1 + 1$ |
| `[024]` | Ch 5 | 無界算子 Lie 括號 Jacobi 恆等式 | $[[N, Q_J], P_J] + \text{循環} = 0$（$5\times 5$ 精確零算子） |
| `[025]` | Ch 5 | **[對易非零／負控制]** Dirac 自伴對易子與非交換性 | $[Q_J, P_J] \neq 0$，且 $i[Q_J, P_J]$ 嚴格自伴 |
| `[026]` | Ch 6 | 量子概率態正規化與 GNS Cauchy–Schwarz 不等式 | Gibbs 態與純態在 $2\times 5^2 = 50$ 對算子上全滿足 $\varphi(1)=1,\ \varphi(X^\dagger X)\ge 0,\ |\varphi(X^\dagger Y)|^2 \le \varphi(X^\dagger X)\varphi(Y^\dagger Y)$ |
| `[027]` | Ch 6 | **[負控制]** 含負權重非正泛函與零範數態向量攔截 | `qstate_diagonal_gibbs` 與 `qstate_pure` 均精確回傳 `None` |
| `[028]` | Ch 7 | 諧振子真空基態 $|0\rangle$ 最小不確定性飽和定理 | $\operatorname{Var}(Q)\operatorname{Var}(P) = 1 = \frac{1}{4}|\langle[Q,P]\rangle|^2$（等號精確飽和） |
| `[029]` | Ch 7 | Robertson–Schrödinger 完整不確定性不等式 | 疊加態與 Gibbs 混合態在非零協方差項下嚴格滿足 $\operatorname{Var}(A)\operatorname{Var}(B) \ge \text{交換子界} + \text{協方差界}$ |
| `[030]` | Ch 8 | Yosida 有界預解正則化與單調收斂定理 | $\|A_\gamma\| < \gamma$（`growth_deg = 0`），且 $\gamma = 10, 20, 40$ 時 $\varphi(A_\gamma)$ 嚴格單調上升逼近 $\varphi(N)$ |
| `[031]` | Ch 8 | Favard–Hermite 高斯矩重構定理 | 由無界高斯矩 $[1,0,1,0,3,0,15,0]$ 反演出 $\alpha=[0,0,0,0],\ \beta=[1,2,3]$（湧現玻色福克梯度） |
| `[032]` | Ch 8 | Poisson–Charlier 矩重構定理 | 由 Bell 數矩序列 $[1,1,2,5,15,52]$ 精確重構 $\alpha=[1,2,3],\ \beta=[1,2]$ |
| `[033]` | Ch 8 | **[負控制]** 違反 Hankel 正定性的偽矩序列攔截 | $[1, 0, -1, 0]$ 被 `reconstruct_jacobi_from_moments` 拒絕回傳 `None` |

---

### Stage III · `qprob/fock`（13 條命題：`[034]–[046]`）

| # | 章節 | 命題標籤與數學內容 | 執行期精確見證 |
|---:|---|---|---|
| `[034]` | Ch 9 | Cuntz–Toeplitz 等距代數恆等式 | $\ell_i \ell_j^* = \delta_{ij} I$ 在 4 個多粒子全福克態上精確成立 |
| `[035]` | Ch 9 | Cuntz–Toeplitz 真空餘投影定理 $I - \sum_i \ell_i^*\ell_i = |\Omega\rangle\langle\Omega|$ | 消滅全部 $2+4+8 = 14$ 個非真空詞並精確保持真空 $|\Omega\rangle$ |
| `[036]` | Ch 9 | 全福克真空半圓律定理 | $\langle\Omega, (\ell^*+\ell)^k \Omega\rangle_0 = [1,0,1,0,2,0,5,0,14]$（Catalan 數），Favard 重構得 $\beta=[1,1,1]$ |
| `[037]` | Ch 9 | **[負控制]** 全福克空間非交換張量詞序分離 | $e_0\otimes e_1 \neq e_1\otimes e_0$ 且 $\langle e_0\otimes e_1, e_1\otimes e_0\rangle_0 = 0$ |
| `[038]` | Ch 10 | 普適 $q$-對易關係 $\ell_q(g)\ell^*(f) - q\,\ell^*(f)\ell_q(g) = \langle g,f\rangle I$ | 在 $q \in \{-1, -\frac{1}{2}, 0, \frac{1}{2}, 1\} \times 4$ 個粒子扇區全數成立 |
| `[039]` | Ch 10 | Bożejko–Speicher 伴隨定理 $\langle \ell^*(f)u, v\rangle_q = \langle u, \ell_q(f)v\rangle_q$ | $5 \times 16 = 80$ 對多粒子態內積逐一精確相等 |
| `[040]` | Ch 11 | 全福克與嚴格插值正定無零空間定理（$q = 0, \frac{1}{2}$） | $d=2,\ n=0..3$ 扇區 Gram 秩實算為 $[1, 2, 4, 8] = d^n$ |
| `[041]` | Ch 11 | 玻色對稱福克商空間維度定理（$q = +1$） | $\mathrm{Sym}^n(\mathbb{Q}^2)$ Gram 秩實算為 $[1, 2, 3, 4] = \binom{n+1}{n}$ |
| `[042]` | Ch 11 | 費米反對稱商空間與 Pauli 不相容坍縮定理（$q = -1$） | $\Lambda^n(\mathbb{Q}^2)$ Gram 秩實算為 $[1, 2, 1, 0]$（3 粒子扇區維度坍縮為 $0$） |
| `[043]` | Ch 11 | **[負控制]** 超界變形 $q = 2 > 1$ 負範數幽靈態 | 反對稱單重態 $\langle 01-10 \mid 01-10\rangle_{q=2} = -2 < 0$（驗證 $|q|\le 1$ 緊緻不可放寬） |
| `[044]` | Ch 12 | 乘法二次量子化函子定理 | $\Gamma(AB)|\Psi\rangle = \Gamma(A)(\Gamma(B)|\Psi\rangle)$ 且 $\Gamma(I)|\Psi\rangle = |\Psi\rangle$ |
| `[045]` | Ch 12 | 微商二次量子化 Lie 代數同態定理 | $[d\Gamma(A), d\Gamma(B)]|\Psi\rangle = d\Gamma([A, B])|\Psi\rangle$（含 $[A,B]\neq 0$） |
| `[046]` | Ch 12 | 粒子數算子表現定理 $N = d\Gamma(I)$ | 在 3 粒子態上精確等於 $3|\Psi_3\rangle$，在真空 $|\Omega\rangle$ 上為 $0$ |

---

### Stage IV · `qprob/ccr_field`（11 條命題：`[047]–[057]`）

| # | 章節 | 命題標籤與數學內容 | 執行期精確見證 |
|---:|---|---|---|
| `[047]` | Ch 13 | 塗抹連續場 CCR 對易律 | $[A(1+2t), A^\dagger(3-t+t^2)] = \int_0^1 g(t)f(t)\,dt = 17/3$ |
| `[048]` | Ch 13 | 離散格點場 $\to$ 連續量子場漸近極限定理 | 格點尺度 $N \in \{2,4,8,16\}$ 經 Richardson 外推零誤差重現連續對易子 $17/3$ |
| `[049]` | Ch 13 | 連續正交波包解耦與雙線性 | $\int_0^1 1\cdot(2t-1)\,dt = 0$ 且 $[A(3g), A^\dagger(f)] = 3[A(g), A^\dagger(f)]$ |
| `[050]` | Ch 14 | Wick 正規序階層定理 $\langle\Omega|A(f_0)^n A^\dagger(f_0)^n|\Omega\rangle = n!$ | 單位模態實算 $n=2 \mapsto 2! = 2$，$n=3 \mapsto 3! = 6$ |
| `[051]` | Ch 14 | 連續高斯場 4 點關聯函數 Wick 三配對定理 | $16$ 支正規序展開總和 $= 4/3 =$ 三組二元配對內積乘積之和 |
| `[052]` | Ch 14 | **[負控制]** 粒子數不平衡場乘積真空期望消滅 | $\langle\Omega|A(f_1)A^\dagger(f_2)A^\dagger(f_3)|\Omega\rangle = 0$ |
| `[053]` | Ch 15 | Weyl 辛形式反對稱性與自正交性 | $\sigma(f, g) = 11/12 = -\sigma(g, f)$ 且 $\sigma(f, f) = 0$ |
| `[054]` | Ch 15 | Weyl CCR 群 2-上循環定理 | $\sigma(f,g) + \sigma(f+g,h) = 223/60 = \sigma(g,h) + \sigma(f,g+h)$ |
| `[055]` | Ch 16 | Hudson–Parthasarathy 量子 Itô 微元代數結合律與非交換表 | $5^3 = 125$ 組三元組全滿足結合律，$dA\cdot dA^\dagger = dt \neq 0 = dA^\dagger\cdot dA$ |
| `[056]` | Ch 16 | 量子隨機微分方程么正性定理 | $dG + dG^\dagger + dG^\dagger dG = 0 = dG + dG^\dagger + dG\,dG^\dagger$（Itô 修正 $|L|^2dt = 2dt$ 抵消耗散） |
| `[057]` | Ch 16 | **[負控制]** 忽略量子 Itô 修正項導致概率外洩 | $dG_{\text{naive}} + dG_{\text{naive}}^\dagger = (-2)dt \neq 0$ |

---

### Stage V · `qprob/nc_measure`（13 條命題：`[058]–[070]`）

| # | 章節 | 命題標籤與數學內容 | 執行期精確見證 |
|---:|---|---|---|
| `[058]` | Ch 17 | 非交換過完備 POVM 完備性與非投影不對易性 | $\mathbb{C}^2$ 上 4 結果勾股 POVM 滿足 $\sum_{k=0}^3 E_k = I_2$、`!PVM` 且 $[E_1, E_2] \neq 0$ |
| `[059]` | Ch 17 | Born 非交換測度機率公理 | 純態誘導機率 $p_0..p_3 \ge 0$ 且 $\sum_k \operatorname{Tr}(\rho E_k) = 1$ |
| `[060]` | Ch 17 | CPTP 量子馬可夫轉移核保跡與自伴保持定理 | Kraus 通道 $\Phi(\rho) = \sum_a K_a \rho K_a^\dagger$ 嚴格滿足 $\operatorname{Tr}(\Phi(\rho)) = 1$ 且 $\Phi(\rho)^\dagger = \Phi(\rho)$ |
| `[061]` | Ch 17 | **[負控制]** 不完備算子族 $\sum E_k \neq I$ 雙重攔截 | 被 `povm_is_complete` 與 `apply_cptp_channel` 同步拒絕 |
| `[062]` | Ch 18 | Naimark 算子測度等距擴張定理 | $\mathbb{C}^2$ 上 4 結果非正交 POVM 等距嵌入 $\mathbb{C}^8$ 正交 PVM（$V^\dagger V = I_2,\ \forall k\ V^\dagger P_k V = E_k$） |
| `[063]` | Ch 18 | 投影值譜測度（PVM）特例刻畫 | 正交譜投影族同時滿足 `povm_is_complete` 與 `povm_is_projective` |
| `[064]` | Ch 19 | Speicher 非交叉矩—自由累積量雙射定理 | 前 5 階矩 $\leftrightarrow$ 自由累積量正逆轉換精確無損還原 |
| `[065]` | Ch 19 | Wigner 半圓律自由高斯性刻畫 | Catalan 矩序列自由累積量為 $\kappa_2 = 1$，所有 $\kappa_{n\neq 2} = 0$（至 8 階全零） |
| `[066]` | Ch 19 | 自由 Poisson（Marchenko–Pastur）全單位累積量定理 | 非交叉計數矩 $[1,1,2,5,14,42]$ 的自由累積量恆為 $\kappa_1..\kappa_5 = [1,1,1,1,1]$ |
| `[067]` | Ch 19 | **[分岔／負控制]** 交換 vs 非交換四階交叉配分 $(13)(24)$ 分岔定理 | 高斯律 $(c_4=0,\ \kappa_4=1)$ 對偶半圓律 $(\kappa_4=0,\ c_4=-1)$ |
| `[068]` | Ch 20 | Voiculescu 自由中心極限定理（Free CLT × Richardson 外推） | Rademacher 自由和在 $N=[1,4,9]$ 外推至 $N\to\infty$ 零誤差命中半圓律 $m_4=2,\ m_6=5$ |
| `[069]` | Ch 20 | 自由加性卷積半群律 | $\mathrm{FreePoisson}(2) \boxplus \mathrm{FreePoisson}(3) = \mathrm{FreePoisson}(5)$（前 4 階矩 $[1, 5, 30, 195, 1530]$） |
| `[070]` | Ch 20 | 五階大統一對偶定理 | 連續 CCR 場 Wick 矩 $(m_6=15 \Rightarrow c_4=c_6=0)$ $\leftrightarrow$ 全福克自由場矩 $(m_6=5 \Rightarrow \kappa_4=\kappa_6=0)$ 雙路閉合 |

---

### Stage VI · `qprob/context_cat`（18 條命題：`[071]–[088]`）

| # | 章節 | 命題標籤與數學內容 | 執行期精確見證 |
|---:|---|---|---|
| `[071]` | Ch 21 | 子場 1-態射左逆截面定理 | $\frac{1}{2}\operatorname{Tr}\circ\iota_{\sqrt{2}}(-7/11) = -7/11$ 且 $\mathrm{st}\circ\iota_\varepsilon(-7/11 + \frac{9}{5}\varepsilon) = -7/11$ |
| `[072]` | Ch 21 | 空間與子場 1-態射水平範疇律 | $(h \circ_h g) \circ_h f == h \circ_h (g \circ_h f)$ 且左右單位 $\mathrm{id}_X$ 嚴格成立 |
| `[073]` | Ch 21 | 雙範疇 Godement 縱橫互換律 | $(\beta_2 \circ_h \alpha_2) \circ_v (\beta_1 \circ_h \alpha_1) == (\beta_2 \circ_v \beta_1) \circ_h (\alpha_2 \circ_v \alpha_1)$ 精確成立 |
| `[074]` | Ch 21 | **[負控制]** 不相容源匯 1-態射複合與錯位 2-胞複合攔截 | 非法水平複合、跨端點偽 2-胞與錯位垂直複合皆回傳 `None` |
| `[075]` | Ch 22 | 八空間與子場主命題錨定切面定理 | $\mathbb{Q}/\mathbb{Q}(\sqrt{2})/\mathbb{Q}((\varepsilon))$（不變量 $=1$）與五階量子空間（不變量 $=2$）全部實算成立 |
| `[076]` | Ch 22 | 主命題纖維化逆變拉回贗函子定律 | $(g \circ_h f)^*(R) == f^*(g^*(R))$ 且 $(\mathrm{id}_Z)^*(R) == R$ |
| `[077]` | Ch 22 | Grothendieck 笛卡兒提升唯一泛因式分解定理 | 任意主命題態射 $h : (X,P) \to (Z,R)$ 沿 $f\circ u$ 唯一分解為 $\mathrm{Cart}(f,R) \circ \bar{u}$ |
| `[078]` | Ch 22 | 五階主命題笛卡兒態射鏈貫通與非正定變形攔截 | 極限 $\to$ 無界 $\to$ 福克 $\to$ 連續場 $\to$ 非交換測度全鏈貫通，且 $q=2$ 偽變形態射被拒絕 |
| `[079]` | Ch 23 | Giry–Lawvere 有理機率單子 $(D_{\mathbb{Q}}, \eta, \mu)$ 單子三律 | 滿足左右單位律、Kleisli 結合律與雙層壓平恆等式 $\mu\circ D\mu = \mu\circ\mu_D$ |
| `[080]` | Ch 23 | 交換機率單子 Fubini 邊際與乘積期望定律 | $\pi_1^*(p\otimes q)=p,\ \pi_2^*(p\otimes q)=q$，且獨立積 $\mathbb{E}[X\cdot Y] = \mathbb{E}[X]\cdot\mathbb{E}[Y]$ |
| `[081]` | Ch 23 | CPTP 量子馬可夫通道 $\times$ 機率單子對偶定理 | $\mathrm{Born}(\Phi(\rho), E) == D_{\mathbb{Q}}(\pi_2)(\mathrm{Born}(\rho, E\circ\Phi^*))$ |
| `[082]` | Ch 23 | **[負控制]** 負權重準機率與零質量分佈攔截 | 準機率 $[3/2, -1/2]$ 與全零權重輸入皆被 $D_{\mathbb{Q}}$ 拒絕回傳 `None` |
| `[083]` | Ch 24 | 量子機率脈絡範疇 $\mathbf{QProbCtx}$ Bohr 良構性 | 相容對易觀測量族 $[Z_1, Z_2, ZZ]$ 通過 Bohr 公理，宇稱分佈 $= [17/25, 8/25]$ |
| `[084]` | Ch 24 | 量子機率脈絡菱形合流定理 | 兩條不等價中間粗粒化脈絡 $C_{\text{left}} \neq C_{\text{right}}$ 在 $\mathbf{QProbCtx}$ 與 $D_{\mathbb{Q}}$ 下零誤差合流至 $C_{\text{parity}}$ |
| `[085]` | Ch 24 | 脈絡預層截面三路自然性定理 | 粗觀測量在粗單子 $\mathbb{E}_{D_{\mathbb{Q}}(C_{\text{coarse}})}$、細單子拉回 $\mathbb{E}_{D_{\mathbb{Q}}(C_{\text{fine}})}\circ\pi$ 與算子跡 $\operatorname{Tr}(\rho A)$ 三路恆等 |
| `[086]` | Ch 24 | 非對角交換脈絡 $C(\sigma_x)$ 譜矩合流定理 | 機率單子期望值 $\mathbb{E}_{D_{\mathbb{Q}}}[\lambda^k]$ 與算子代數跡泛函 $\varphi(\sigma_x^k)$ 精確一致 |
| `[087]` | Ch 24 | **[負控制]** Heisenberg 脈絡不相容阻礙與不守恆粗粒化攔截 | 非對易對 $\{\sigma_x, \sigma_z\}$ 與效應不守恆映射皆被 `QProbCtx` 拒絕 |
| `[088]` | Ch 24 | **六階終極合流大定理** | 雙範疇 8 空間子場 $\times$ 主命題纖維化 $8/8$ $\times$ 機率單子 $D_{\mathbb{Q}}$ $\times$ 量子機率脈絡範疇 $\mathbf{QProbCtx}$ 全鏈合流（`all_holds = true`） |
