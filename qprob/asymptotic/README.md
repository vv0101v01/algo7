# `qprob/asymptotic/` — 代數子場塔與無窮漸近極限空間（Stage I · Layer 0）

> **架構位置**：套件 `qprob-asymptotic`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 0**，`depends_on: []`。零外部依賴，只匯入 `moonbitlang/core`。
> **規模**：3 個 `.mbt` 檔、**1,230 行**、4 章、**21 條命題**（編號 `[001]–[021]`，含 4 條負控制）。

---

## 1. 數學結構定位與演變動因

量子概率與非交換隨機過程的第一個障礙是**數域與無窮維截斷極限的雙重精確化**：
1. 平方根正規化（如偶極振幅、二次擴張本徵值）超出有理數 $\mathbb{Q}$，但不能退化為帶捨入誤差的 `Double`；
2. 預解正則化（$\varepsilon = \gamma^{-1} \to 0^+$）與離散格點連續極限（$h = N^{-1} \to 0^+$）需要同時表達**無窮小階**與**標準部商映射**；
3. 有限維截斷空間序列 $\{V_k\}_{k \ge 0}$ 需要透過相容轉移映射 $\pi_{j,k} : V_k \to V_j$ 收束為射影極限 $\varprojlim V_k$，並以符號外推演算法消除截斷誤差。

本套件在 Layer 0 建立三層數域與極限骨架：
$$\mathbb{Q} \;\subset\; \mathbb{Q}(\sqrt{d}) \;\subset\; \mathbb{Q}((\varepsilon))_{\le M}, \qquad \varprojlim_{k} (V_k, \pi_{j,k})$$

---

## 2. 檔案與職責

| 檔案 | 行數 | 核心型別與公開介面 |
|---|---:|---|
| `subfield.mbt` | 546 | 正規形有理數 `QVal`（含負指數冪 `qv_pow`）、二次擴張子場 `QuadElem`（共軛、範數、跡、反元素）、非阿基米德截斷 Laurent 噴流 `AsymJet`（賦值階、標準部商同態、形式長除法反元素） |
| `projective_limit.mbt` | 332 | 精確有理矩陣乘法 `qmat_mul` 與上三角列梯形秩 `qmat_rank`、射影極限塔 `ProjectiveTower`、Mittag-Leffler 穩定像秩、Richardson–Neville 外推、Shanks–Aitken $\Delta^2$、Wynn $\varepsilon$-算法、Cesàro 平均 |
| `laws.mbt` | 352 | 4 章 / **21 條命題**（`asym_all_laws`） |

---

## 3. 核心演算法記錄與簡介

| 演算法函式 | 輸入 → 輸出 | 數學原理與複雜度簡介 |
|---|---|---|
| `qv_make` / `qv_pow` | `(BigInt, BigInt) -> QVal` / `(QVal, Int32) -> QVal` | 以 Euclid 最大公因數維持唯一正規形（$\text{den} > 0,\ \gcd(|p|,q)=1$）；`qv_pow` 對負指數先經 `qv_inv` 取逆再執行 $O(\log |e|)$ 二進位平方求冪。 |
| `quad_inv` | `QuadElem -> QuadElem?` | 利用 Galois 共軛有理化 $(a+b\sqrt{d})^{-1} = \frac{a-b\sqrt{d}}{a^2 - d b^2}$；當範數 $N(x)=a^2-db^2=0$（例如零元或可約根號 $d=4$ 的零因子 $2+\sqrt{4}$）時精確回傳 `None`。 |
| `jet_inv` / `jet_standard_part` | `AsymJet -> AsymJet?` / `AsymJet -> QVal?` | 對首項係數 $c_v \varepsilon^v \neq 0$ 提因子後執行截斷形式冪級數長除法求得 $\varepsilon^{-v}(c_v + \dots)^{-1} \bmod \varepsilon^{M+1}$；`jet_standard_part` 對有界噴流（$\text{val} \ge 0$）投出常數項 $c_0$，對含負次無窮大項（$\text{val} < 0$）回傳 `None`。 |
| `qmat_rank` | `(Array[QVal], Int32, Int32) -> Int32` | 精確有理數主元選取與上三角高斯列梯形消去（Row-Echelon Elimination），時間複雜度 $O(\min(r,c)\cdot r\cdot c)$，無需對主元上方重複回代，供 Mittag-Leffler 穩定像維度與 Bożejko–Speicher Gram 秩共用。 |
| `tower_mittag_leffler_stable_rank` | `(ProjectiveTower, Int32) -> Int32` | 對指定層 $k$ 計算遠端轉移映射 $\pi_{k, K_{\max}} : V_{K_{\max}} \to V_k$ 的精確矩陣秩，判定射影極限塔是否無穩定化虧損。 |
| `richardson_extrapolate_limit` | `(Array[Int32], Array[QVal]) -> QVal?` | 在步長節點 $h_i = 1/N_i$ 上對漸近展開 $A(N) = L + c_1 N^{-1} + \dots + c_{m-1} N^{-(m-1)}$ 在 $h = 0$ 處執行 Neville 多項式插值，以 $m$ 個有限尺度零誤差消去前 $m-1$ 階截斷誤差。 |
| `shanks_aitken_step` | `Array[QVal] -> Array[QVal]` | 單步 Aitken $\Delta^2$ 非線性變換 $s'_n = s_n - \frac{(\Delta s_n)^2}{\Delta^2 s_n}$，對單模態幾何暫態 $L + c r^n$ 一步精確命中極限 $L$。 |
| `wynn_epsilon_limit` | `Array[QVal] -> QVal?` | 實作精確 **Wynn $\varepsilon$-菱形遞迴** $\varepsilon_{-1}^{(n)}=0,\ \varepsilon_0^{(n)}=s_n,\ \varepsilon_{k+1}^{(n)} = \varepsilon_{k-1}^{(n+1)} + (\varepsilon_k^{(n+1)}-\varepsilon_k^{(n)})^{-1}$；偶數階 $\varepsilon_{2K}^{(n)}$ 等價於 $[K/K]$ Padé–Shanks Hankel 行列式比，能以 $2K+1$ 個點零誤差消去 $K$ 個獨立指數暫態 $\sum_{j=1}^K c_j \lambda_j^n$。 |
| `cesaro_mean` | `Array[QVal] -> QVal?` | 算術遍歷平均 $\frac{1}{N}\sum_{k=0}^{N-1} s_k$，正則化無逐點極限但具時間平均的量子酉演化振盪序列。 |

---

## 4. 定理與命題記錄（`[001]–[021]`）

| 編號 | 定理／命題 | 實算見證與負控制 |
|---:|---|---|
| `[001]–[005]` | **二次擴張體公理與 Galois 不動子場定理** | $216$ 組結合分配律、非零元可逆、範數乘法性 $N(xy)=N(x)N(y)$、$\text{Fix}(\sigma)=\mathbb{Q}$，$(\sqrt{2})^2=2$ 且負指數 $(2/3)^{-3}=27/8$。 |
| `[006]` | **負控制（非無平方因子根號）** | $d=4$ 時 $N(2+\sqrt{4})=4-4=0$，`quad_inv` 精確攔截零因子回傳 `None`。 |
| `[007]–[010]` | **非阿基米德有序場與標準部商同態定理** | 嚴格序鏈 $0 < \varepsilon^2 < \varepsilon < 10^{-3} < 1 < \varepsilon^{-1}$；$(\varepsilon^{-1}+2+3\varepsilon)^{-1}$ 精確互逆；$\text{st} : \mathbb{Q}[[\varepsilon]] \to \mathbb{Q}$ 保加減乘且 $\ker(\text{st})=\varepsilon\mathbb{Q}[[\varepsilon]]$。 |
| `[011]` | **負控制（無窮大噴流無標準部）** | 賦值階 $-1$ 的 $\varepsilon^{-1}+2+3\varepsilon \notin \mathbb{Q}[[\varepsilon]]$，`jet_standard_part` 回傳 `None`。 |
| `[012]–[015]` | **射影極限相容執行緒與 Mittag-Leffler 穩定性** | 相干態截斷 $(1/k!)_{k\le N}$ 滿足 $\pi_{N,N+1}(x_{N+1})=x_N$ 與函子複合 $\pi_{0,3}=\pi_{0,1}\pi_{1,2}\pi_{2,3}$；滿射塔穩定秩 $[2,3,4]$ vs 非滿射秩 $1$ 投影塔穩定維度 $1<2$。 |
| `[016]` | **負控制（不相容偽執行緒）** | 篡改單層座標的序列被 `tower_is_coherent_thread` 拒絕。 |
| `[017]–[020]` | **四類漸近極限加速定理** | Richardson 4 點消去 $N^{-1}..N^{-3}$ 命中 $7/3$；Aitken 一步命中 $11/5$；Wynn $\varepsilon_4$ 以 5 點消除雙模態 $(1/2)^n + (-1/3)^n$ 命中極限 $2$；Cesàro 平均正則化 $9/4+(-1)^k \to 9/4$。 |
| `[021]` | **負控制（奇異尺度攔截）** | 含 $N=0$ 節點輸入被 `richardson_extrapolate_limit` 拒絕回傳 `None`。 |
