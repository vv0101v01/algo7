# `qprob/` — 五階量子概率與非交換隨機空間結構演化子聯邦

> **架構位置**：`architecture.json` 中的 qprob 子聯邦，歸屬第七聯邦 `discovery`（多線性張量與猜想發現聯邦）。
> 套件：`qprob-asymptotic`(L0) → `qprob-unbounded`(L1) → `qprob-fock`(L2) → `qprob-ccr-field`(L3) → `qprob-nc-measure`(L4) → `cmd-qprob`(L5)。
> 唯一聚合執行入口：`moon run cmd/qprob --target wasm-gc` → **70 / 70 個結構演化定理與演算法命題**。

---

## 1. 數學結構的五階演變脈絡（如何推導出定理與演算法）

```
[Stage I · L0] 有序代數子場塔 ℚ ⊂ ℚ(√d) ⊂ ℚ((ε))_≤M 與無窮漸近極限空間 lim_← V_k
   │  (演變動因：當維度 d→∞ 時，粒子數與座標算子範數發散，有界代數不再封閉)
   ▼
[Stage II · L1] 無界算子 *-代數概率空間 (𝒟, Op*(𝒟), φ) 與 Favard–Lanczos 矩重構
   │  (演變動因：高斯矩反演出 β_k = k，半圓矩反演出 β_k = 1；需要統一承載多粒子激發的希爾伯特空間)
   ▼
[Stage III · L2] 全量子福克空間 ℱ_0(ℋ) = ⨁ ℋ^{⊗n} 與 Bożejko–Speicher q-變形子空間
   │  (演變動因：單粒子空間由離散模態 ℚ^d 細分為連續時間區間 L²([0,T], dt)，逐點對易子發散為 δ(s−t))
   ▼
[Stage IV · L3] 連續創生與湮滅算子場 [A(g), A†(f)] = ⟨g,f⟩_{L²}、Wick 正規序與量子 Itô 代數
   │  (演變動因：非交換場與過完備觀測量不存在古典聯合 σ-代數測度，配分格由 Π(n) 收縮為非交叉 NC(n))
   ▼
[Stage V · L4] 非交換隨機分佈、正算子值測度（POVM ↪ Naimark PVM）與 Speicher 自由累積量統合
```

全部計算在 `BigInt` 精確有理數 `QVal`、二次域 `QuadElem`、複有理數 `QComplex` 與截斷 Laurent 噴流 `AsymJet` 上執行，**零浮點誤差、零近似容差**。

---

## 2. 檔案與規模總覽

| 套件 | Layer | 檔案 | 行數 | 章節 | 命題 |
|---|---:|---|---:|---:|---:|
| [`qprob/asymptotic`](asymptotic/README.md) | L0 | `subfield.mbt` (546)、`projective_limit.mbt` (332)、`laws.mbt` (352) | 1,230 | 4 | 21 |
| [`qprob/unbounded`](unbounded/README.md) | L1 | `probability_space.mbt` (543)、`laws.mbt` (363) | 906 | 4 | 12 |
| [`qprob/fock`](fock/README.md) | L2 | `full_fock.mbt` (435)、`laws.mbt` (341) | 776 | 4 | 13 |
| [`qprob/ccr_field`](ccr_field/README.md) | L3 | `continuum_field.mbt` (425)、`laws.mbt` (302) | 727 | 4 | 11 |
| [`qprob/nc_measure`](nc_measure/README.md) | L4 | `noncommutative_measure.mbt` (384)、`laws.mbt` (408) | 792 | 4 | 13 |
| [`cmd/qprob`](../cmd/qprob/README.md) | L5 | `main.mbt` (59) | 59 | — | **70** |
| **合計** | **L0–L5** | **12 個 `.mbt` 檔** | **4,490** | **20** | **70** |

---

## 3. 由結構演變導出的核心定理與演算法

| 階段 | 導出定理 | 導出演算法 |
|---|---|---|
| **Stage I** `asymptotic` | Galois 不動子場 `Fix(σ) = ℚ`；標準部商同態 `st : ℚ[[ε]] → ℚ`（`ker(st) = εℚ[[ε]]`）；射影塔 Mittag-Leffler 穩定秩定理 | `richardson_extrapolate_limit`（Neville–Richardson 零誤差消去 `N⁻¹..N⁻ᵐ`）、`shanks_aitken_step`、`wynn_epsilon_limit`（`ε_{2K}` 零誤差消去多模態幾何暫態）、`cesaro_mean` |
| **Stage II** `unbounded` | 稠密核 `Op*(𝒟)` 成長階加法封閉性；GNS Cauchy–Schwarz；Robertson–Schrödinger 不確定性不等式與基態飽和；Yosida 有界預解正則化 `‖A_γ‖ < γ` | `reconstruct_jacobi_from_moments`（Favard–Chebyshev–Lanczos 正交多項式三項遞迴：由無界高斯矩反演出 `β=[1,2,3]`，由 Poisson Bell 矩反演出 `α=[1,2,3], β=[1,2]`） |
| **Stage III** `fock` | Cuntz–Toeplitz 等距恆等式與真空餘投影 `I − Σ ℓ*_i ℓ_i = \|Ω⟩⟨Ω\|`；全福克場 `ℓ*+ℓ` 生成半圓律 Catalan 矩；Bożejko–Speicher `q`-對易與三統計維度分裂（`d^n` / `C(d+n-1,n)` / `C(d,n)` Pauli 核）；`[dΓ(A), dΓ(B)] = dΓ([A,B])` | `fock_q_gram_matrix`（逆序數加權 `q`-Gram 核秩計算）、`fock_gamma` / `fock_dgamma` 二次量子化算子提升器 |
| **Stage IV** `ccr_field` | 離散福克格點場對易子經 Richardson 外推 `N→∞` 零誤差收斂至連續 `L²` 內積 `[A(g), A†(f)] = ∫ gf dt`；高斯場 4 點關聯三配對定理；Weyl 辛形式 2-上循環恆等式；Hudson–Parthasarathy 量子隨機演化么正性判準 | `wick_normal_order` / `wick_vacuum_expectation`（遞迴 Leibniz 縮併正規序展開器）、`qsde_ito_product`（非交換量子 Itô 二次變差代數） |
| **Stage V** `nc_measure` | 非交換過完備 POVM 與 Born 機率律；Naimark 等距擴張 `V† P_k V = E_k`；半圓律自由累積量消失 `κ_{n≠2}=0`；古典 vs 自由四階分岔（交叉配分 `(13)(24)`）；自由加性卷積半群律與自由中心極限定理（Free CLT）；五階大統一對偶閉環 | `verify_naimark_dilation`、`moments_to_free_cumulants` / `free_cumulants_to_moments`（非交叉 Cauchy 卷積冪 Möbius 正逆轉換）、`free_additive_convolution_moments`、`apply_cptp_channel` |

---

## 4. 驗證與邊界說明

```bash
export PATH="$HOME/.moon/bin:$PATH"
moon check --deny-warn --target wasm-gc
moon build --target wasm-gc
moon run cmd/qprob --target wasm-gc           # 通過 70 / 70 個命題
python3 tools/arch_check.py                   # 69 packages / 78 components
python3 tools/federation_docs.py --check      # 生成文檔一致
```

**誠實邊界**：
* 全部 70 條命題是在具體有限截斷維度、精確多項式測試函數與有理樣本上當場重算的精確等式／不等式，並為每一層配置顯式負控制（如可約根號 `d=4`、無窮大噴流 `ε⁻¹`、非正 Hankel 矩、`q=2` 負範數態、忽略 Itô 修正項、不完備 POVM），**不是** Lean 形式化任意無窮維希爾伯特空間證明。
* 連續算子場以 `L²([a,b], dt)` 中稠密的多項式代數 `ℚ[t]` 表達塗抹測試函數，藉此獲得精確原函數積分與 Euler–Maclaurin 漸近展開。
