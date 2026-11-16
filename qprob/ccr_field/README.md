# `qprob/ccr_field/` — 連續創生與湮滅算子場、Wick 正規序與量子 Itô 代數（Stage IV · Layer 3）

> **架構位置**：套件 `qprob-ccr-field`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 3**，`depends_on: [qprob-asymptotic, qprob-unbounded, qprob-fock]`。
> **規模**：2 個 `.mbt` 檔、**727 行**、4 章、**11 條命題**（編號 `[047]–[057]`，含 2 條負控制）。

---

## 1. 數學結構定位與演變動因

當第三階福克空間的單粒子模態由離散座標 $\mathbb{Q}^d$ 連續化為時間區間 $L^2([a,b], dt)$ 時，逐點場算子 $[a(s), a^\dagger(t)] = \delta(s-t)$ 在單點不再是良定義算子，必須演變為**以測試函數 $f, g \in \mathbb{Q}[t] \subset L^2([a,b], dt)$ 塗抹（Smeared）的連續創生與湮滅算子場**：
$$[A(g), A^\dagger(f)] = \langle g, f\rangle_{L^2} I = \left(\int_a^b g(t)f(t)\,dt\right) I$$

這一連續化同時觸發三個關鍵結構與演算法：
1. **離散福克格點 → 連續場漸近極限**：將區間等分為 $N$ 個網格的玻色福克對易子具 Euler–Maclaurin 漸近展開，經第一階 `richardson_extrapolate_limit` 在有限格點即零誤差收斂至連續 $L^2$ 積分；
2. **Wick 正規序展開與高斯場多點關聯**：任意非正規序場乘積經遞迴交換縮併化為正規序 $\sum c_\alpha A^\dagger(\dots)A(\dots)$，真空期望值由全部二元縮併配對決定；
3. **Weyl 相空間辛上循環與 Hudson–Parthasarathy 量子隨機微積分**：連續量子白雜訊誘導非交換二次變差 $dA_t \cdot dA_t^\dagger = dt$，使量子隨機微分方程么正性必須計入 Itô 耗散修正項 $-\frac{1}{2}L^\dagger L\,dt$。

---

## 2. 檔案與職責

| 檔案 | 行數 | 核心型別與公開介面 |
|---|---:|---|
| `continuum_field.mbt` | 425 | 多項式塗抹測試函數 `ContinuumTestFn`、複相空間測試函數 `ComplexFieldFn`、精確原函數定積分 `poly_definite_integral`、連續內積 `continuum_l2_inner`、離散福克格點對易子 `fock_lattice_bosonic_commutator`、`wick_normal_order`、`wick_vacuum_expectation`、`weyl_symplectic_form`、`quantum_ito_mul`、`qsde_ito_product` |
| `laws.mbt` | 302 | 4 章 / **11 條命題**（`ccr_all_laws`） |

---

## 3. 核心演算法記錄與簡介

| 演算法函式 | 輸入 → 輸出 | 數學原理與複雜度簡介 |
|---|---|---|
| `poly_definite_integral` / `continuum_l2_inner` | `(ContinuumTestFn, ContinuumTestFn) -> QVal` | 多項式卷積乘法後逐項除以 $k+1$ 精確計算 $\int_a^b \sum_k c_k t^k dt = \sum_k \frac{c_k}{k+1}(b^{k+1}-a^{k+1})$，強制檢驗區間 $[a,b]$ 一致，零數值積分誤差。 |
| `fock_lattice_bosonic_commutator` | `(ContinuumTestFn, ContinuumTestFn, Int32) -> QVal` | 在 $N$ 點中點格點上將塗抹函數離散化為單粒子向量 $\tilde{f}, \tilde{g} \in \mathbb{Q}^N$（權重 $\sqrt{\Delta t}$），直接呼叫第三階 `@fock.fock_create_left` 與 `@fock.fock_annihilate_q`（$q=1$）計算真空對易期望 $\langle\Omega, [A_N(g), A_N^\dagger(f)]\Omega\rangle$。 |
| `wick_normal_order` / `wick_vacuum_expectation` | `Array[FieldFactor] -> Array[WickNormalTerm]` | **遞迴 Leibniz–Wick 縮併演算法**：將左側創生／湮滅因子逐一插入右側已正規序展開式中；每當 `Annihilate(g)` 跨過 `Create(f_k)` 時分裂為「交換穿透項」與「純量內積縮併項 $\langle g, f_k\rangle_{L^2}$」，最後合併同類算子詞並抽取純常數項（$m=n=0$）即得真空多點關聯函數。 |
| `weyl_symplectic_form` | `(ComplexFieldFn, ComplexFieldFn) -> QVal` | 計算相空間辛形式 $\sigma(f, g) = \operatorname{Im}\langle f, g\rangle_{L^2(\mathbb{C})} = \int (f_{\text{re}} g_{\text{im}} - f_{\text{im}} g_{\text{re}})\,dt$，決定 Weyl 位移算子乘法相位 $W(f)W(g) = e^{-i\sigma(f,g)/2}W(f+g)$。 |
| `quantum_ito_mul` / `qsde_ito_product` | `(QuantumSdeIncrement, QuantumSdeIncrement) -> QuantumSdeIncrement` | 實作 **Hudson–Parthasarathy 量子 Itô 乘法表**（僅 $dA\cdot dA^\dagger = dt$、$dA\cdot d\Lambda = dA$、$d\Lambda\cdot dA^\dagger = dA^\dagger$、$d\Lambda\cdot d\Lambda = d\Lambda$ 非零，其餘二次乘積皆為 $0$），線性擴張至一般隨機微元 $dX = c_{dt}dt + c_{dA}dA + c_{dA^\dagger}dA^\dagger + c_{d\Lambda}d\Lambda$。 |

---

## 4. 定理與命題記錄（`[047]–[057]`）

| 編號 | 定理／命題 | 實算見證與負控制 |
|---:|---|---|
| `[047]–[049]` | **塗抹場 CCR 對易律與格點 Richardson 連續極限定理** | $[A(1+2t), A^\dagger(3-t+t^2)] = 17/3$；格點尺度 $N \in \{2,4,8,16\}$ 經 Richardson 外推零誤差命中 $17/3$；正交 Legendre 多項式對易子為 $0$。 |
| `[050]–[052]` | **Wick 正規序階層與高斯場 4 點關聯三配對定理** | $\langle\Omega|A(f_0)^n A^\dagger(f_0)^n|\Omega\rangle = n!$（$n=2\mapsto 2,\ n=3\mapsto 6$）；高斯場 $\Phi(f) = A(f)+A^\dagger(f)$ 四點展開 $2^4=16$ 支總和 $= 4/3 = \langle f_1,f_2\rangle\langle f_3,f_4\rangle + \langle f_1,f_3\rangle\langle f_2,f_4\rangle + \langle f_1,f_4\rangle\langle f_2,f_3\rangle$；奇偶失衡場真空期望恆為 $0$。 |
| `[053]–[054]` | **Weyl 辛形式反對稱性與群 2-上循環定理** | $\sigma(f,g) = 11/12 = -\sigma(g,f)$ 且滿足 2-上循環恆等式 $\sigma(f,g)+\sigma(f+g,h) = 223/60 = \sigma(g,h)+\sigma(f,g+h)$。 |
| `[055]–[057]` | **Hudson–Parthasarathy 量子 Itô 結合律與 QSDE 么正演化判準** | $5^3=125$ 組微元三元組全數滿足結合律；生成元 $dG = (-iH - \frac{1}{2}|L|^2)dt + L\,dA^\dagger - L^*\,dA$ 精確滿足 $dG + dG^\dagger + dG^\dagger dG = 0$；忽略 $-\frac{1}{2}|L|^2 dt$ 修正項時 $dG+dG^\dagger = -2\,dt \neq 0$（負控制）。 |
