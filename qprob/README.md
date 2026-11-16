# `qprob/` — 量子概率、非交換隨機空間與量子機率脈絡範疇合流（六階子聯邦總覽）

> **架構位置**：第七聯邦 `discovery` 下的獨立六層演進子聯邦（`qprob-asymptotic` → `qprob-unbounded` → `qprob-fock` → `qprob-ccr-field` → `qprob-nc-measure` → `qprob-context-cat`，執行入口 `cmd/qprob` 並匯入旗艦驗算入口 `cmd/showcase`）。
> **零浮點純精確算術**：全程建立在正規形任意精度有理數 $\mathbb{Q}$、二次代數子場 $\mathbb{Q}(\sqrt{d})$、高斯有理複數 $\mathbb{Q}(i)$ 與截斷非阿基米德漸近 Laurent 噴流 $\mathbb{Q}((\varepsilon))_{\le M}$ 之上，無任何 `Double` 近似誤差。
> **整體規模**：6 個核心庫套件 + 1 個執行器套件，共 **16 個 `.mbt` 檔、6,503 行**（核心庫 15 檔 6,440 行 + 執行器 63 行），**24 章、88 條執行期命題**（含 **16 條負控制與分岔命題**），`88 / 88` 全數通過。

---

## 1. 六階數學演變脈絡與雙範疇合流圖

```text
  Stage I · Layer 0 : qprob/asymptotic (1,230 LOC · Ch 1–4 · Laws [001]–[021])
    代數子場塔 Q ⊂ Q(√d) ⊂ Q((ε))_≤M  +  射影極限塔 lim← V_k  +  Richardson / Aitken / Wynn-ε / Cesàro 外推
          │
          ▼  截斷維度 d → ∞ 使粒子數 N 與正則對 Q, P 範數發散，突破有界 C*-代數框架
  Stage II · Layer 1 : qprob/unbounded (906 LOC · Ch 5–8 · Laws [022]–[033])
    共同不變稠密核 Op*(D)  +  GNS 量子態  +  Robertson–Schrödinger 界  +  Yosida 預解  +  Favard–Jacobi 矩重構
          │
          ▼  高斯矩重構湧現線性 Jacobi 權重 β_k = k，自由半圓矩對應常數權重 β_k = 1
  Stage III · Layer 2 : qprob/fock (776 LOC · Ch 9–12 · Laws [034]–[046])
    全量子福克空間 F_0(H)  +  Bożejko–Speicher q-對易內積核  +  三統計分裂 q ∈ {0, +1, -1}  +  Γ(T), dΓ(H)
          │
          ▼  單粒子離散模態 Q^d 經格點外推過渡至連續時間測試函數空間 L^2([a,b], dt)
  Stage IV · Layer 3 : qprob/ccr_field (727 LOC · Ch 13–16 · Laws [047]–[057])
    塗抹連續算子場 [A(g), A†(f)] = ⟨g,f⟩I  +  Wick 正規序縮併  +  Weyl 辛 2-上循環  +  Hudson–Parthasarathy 量子 Itô 代數
          │
          ▼  不對易場觀測量無古典聯合機率空間，古典測度分裂為算子值測度與非交叉自由累積量
  Stage V · Layer 4 : qprob/nc_measure (792 LOC · Ch 17–20 · Laws [058]–[070])
    過完備 POVM / CPTP 通道  +  Naimark 等距擴張 C^d ↪ C^(Kd)  +  Speicher 自由累積量 κ_n  +  Voiculescu 自由極限定理
          │
          ▼  雙範疇空間轉移、依值主命題纖維化與有理機率單子 D_Q 的頂點統合
  Stage VI · Layer 5 : qprob/context_cat (2,009 LOC · Ch 21–24 · Laws [071]–[088])
    雙範疇 B_qprob (0/1/2-胞)  +  Grothendieck 纖維化 π: ∫Prop → B_qprob  +  機率單子 D_Q  +  量子機率脈絡範疇 QProbCtx 合流
```

---

## 2. 套件分層與量化指標總表

| 階段 | 層級 | 套件路徑 | 套件名稱 | `.mbt` 檔數 | 行數 | 章節 | 命題區間 | 負控制數 | 詳細文檔 |
|---|---:|---|---|---:|---:|---:|---|---:|---|
| Stage I | L0 | `qprob/asymptotic` | `qprob-asymptotic` | 3 | 1,230 | Ch 1–4 | `[001]–[021]` (21) | 4 | [`asymptotic/README.md`](./asymptotic/README.md) |
| Stage II | L1 | `qprob/unbounded` | `qprob-unbounded` | 2 | 906 | Ch 5–8 | `[022]–[033]` (12) | 3 | [`unbounded/README.md`](./unbounded/README.md) |
| Stage III | L2 | `qprob/fock` | `qprob-fock` | 2 | 776 | Ch 9–12 | `[034]–[046]` (13) | 2 | [`fock/README.md`](./fock/README.md) |
| Stage IV | L3 | `qprob/ccr_field` | `qprob-ccr-field` | 2 | 727 | Ch 13–16 | `[047]–[057]` (11) | 2 | [`ccr_field/README.md`](./ccr_field/README.md) |
| Stage V | L4 | `qprob/nc_measure` | `qprob-nc-measure` | 2 | 792 | Ch 17–20 | `[058]–[070]` (13) | 2 | [`nc_measure/README.md`](./nc_measure/README.md) |
| Stage VI | L5 | `qprob/context_cat` | `qprob-context-cat` | 3 | 2,009 | Ch 21–24 | `[071]–[088]` (18) | 3 | [`context_cat/README.md`](./context_cat/README.md) |
| Runner | L6 | `cmd/qprob` | `cmd-qprob` | 1 | 63 | 總驗算 | 全 `88 / 88` | — | [`../cmd/qprob/README.md`](../cmd/qprob/README.md) |
| **合計** | **L0–L6** | — | **7 個組件** | **16** | **6,503** | **24 章** | **88 條命題** | **16** | [`../docs/QPROB_THEOREMS_AND_ALGORITHMS.md`](../docs/QPROB_THEOREMS_AND_ALGORITHMS.md) |

---

## 3. 核心演算法索引（跨六階 26 項演算法）

| 階段 | 演算法 | 所在檔案 | 核心數學方法與不變量 |
|---|---|---|---|
| I | 二次擴張有理化反元素 `quad_inv` | `asymptotic/subfield.mbt` | Galois 共軛 $(a-b\sqrt{d})/(a^2-db^2)$，精確攔截範數零因子（如 $d=4$ 時 $2+\sqrt{4}$）。 |
| I | Laurent 噴流長除法與標準部 `jet_inv` / `jet_standard_part` | `asymptotic/subfield.mbt` | 提最低賦值階 $\varepsilon^v$ 後形式級數截斷求逆；標準部商同態 $\mathbb{Q}[[\varepsilon]] \twoheadrightarrow \mathbb{Q}$。 |
| I | 精確有理列梯形秩與 Mittag-Leffler 穩定像 `qmat_rank` / `tower_mittag_leffler_stable_rank` | `asymptotic/projective_limit.mbt` | $O(\min(r,c)rc)$ 精確高斯列梯形消去，計算遠端射影轉移映射穩定像維度。 |
| I | Richardson–Neville 多項式極限外推 `richardson_extrapolate_limit` | `asymptotic/projective_limit.mbt` | 步長節點 $h_i = 1/N_i$ 在 $h=0$ 處 Neville 插值，零誤差消去 $O(N^{-1}..N^{-(m-1)})$ 截斷項。 |
| I | Wynn $\varepsilon$-演算法 / Padé–Shanks 加速 `wynn_epsilon_limit` | `asymptotic/projective_limit.mbt` | 菱形反差分遞迴 $\varepsilon_{k+1}^{(n)} = \varepsilon_{k-1}^{(n+1)} + (\Delta \varepsilon_k^{(n)})^{-1}$，同時消除多模態幾何暫態。 |
| II | 無界 $^*$-代數複合與成長階追蹤 `uop_mul` | `unbounded/probability_space.mbt` | 共同稠密核 $\mathcal{D}$ 上追蹤 Sobolev 多項式成長階 $\deg(AB)=\deg(A)+\deg(B)$，零算子自動收斂階 $0$。 |
| II | Robertson–Schrödinger 證書 `check_robertson_schrodinger` | `unbounded/probability_space.mbt` | 同時精確計算對易子平方界與反交換中心協方差界，判定量子態是否飽和最小不確定性。 |
| II | Yosida 預解正則化 `yosida_diagonal_approximant` | `unbounded/probability_space.mbt` | 有界逼近算子 $A_\gamma = \gamma A(\gamma I+A)^{-1}$ 單調遞增逼近無界非負自伴算子期望。 |
| II | Favard–Chebyshev–Lanczos 矩重構 `reconstruct_jacobi_from_moments` | `unbounded/probability_space.mbt` | 由前 $2n$ 階矩單一線性泛函反演三對角 Jacobi 係數 $(\alpha_k,\beta_k)$，並以 $h_k \le 0$ 偵測非正定偽矩。 |
| III | 全福克稀疏正規形與 $q$-湮滅 `fock_normalize` / `fock_annihilate_q` | `fock/full_fock.mbt` | 張量詞字典序唯一表示與 $q$-Leibniz 跨位縮併 $\sum_{k=1}^n q^{k-1}\langle g, e_{i_k}\rangle$。 |
| III | Bożejko–Speicher $q$-Gram 秩分裂 `fock_q_gram_matrix` | `fock/full_fock.mbt` | 對稱群 $S_n$ 逆序數核 $\sum_{\sigma \in S_n} q^{\mathrm{inv}(\sigma)}$ 與精確秩計算，導出自由／玻色／費米維度分裂。 |
| III | 乘法與微商二次量子化 `fock_gamma` / `fock_dgamma` | `fock/full_fock.mbt` | 單粒子算子函子提升 $\Gamma(AB)=\Gamma(A)\Gamma(B)$ 與 Lie 同態 $[d\Gamma(A),d\Gamma(B)]=d\Gamma([A,B])$。 |
| IV | 塗抹測試函數精確 $L^2$ 內積 `continuum_l2_inner` | `ccr_field/continuum_field.mbt` | 多項式卷積與原函數解析定積分，零數值求積誤差。 |
| IV | 遞迴 Leibniz–Wick 正規序縮併 `wick_normal_order` | `ccr_field/continuum_field.mbt` | 任意創生／湮滅場序列遞迴化為正規序並提取高斯場 $2n$ 點配對真空關聯函數。 |
| IV | Weyl 辛形式與 Hudson–Parthasarathy 量子 Itô 積 `qsde_ito_product` | `ccr_field/continuum_field.mbt` | 相空間辛 2-上循環與非交換隨機微元乘法表 $dA\,dA^\dagger = dt$ 么正演化檢驗。 |
| V | 構造性 Naimark 等距擴張 `verify_naimark_dilation` | `nc_measure/noncommutative_measure.mbt` | 將過完備 POVM Kraus 根堆疊為分塊等距 $V:\mathbb{C}^d \hookrightarrow \mathbb{C}^{Kd}$，驗證 $E_k = V^\dagger P_k V$。 |
| V | Speicher 非交叉矩—自由累積量雙射 `moments_to_free_cumulants` | `nc_measure/noncommutative_measure.mbt` | $O(N^3)$ Cauchy 卷積冪遞推實現 $m_n \leftrightarrow \kappa_n$ 正逆轉換與自由加性卷積 $\mu \boxplus \nu$。 |
| VI | 雙範疇 1/2-胞複合與互換律檢驗 `bicat_hcomp2` / `bicat_vcomp2` / `bicat_check_interchange` | `context_cat/bicat_fibration.mbt` | 驗證空間—子場轉移路徑與兩條平行演化路徑間的 Godement 縱橫互換律。 |
| VI | Grothendieck 笛卡兒提升與泛因式分解 `cartesian_lift_morphism` / `factor_through_cartesian_lift` | `context_cat/bicat_fibration.mbt` | 逆變拉回贗函子 $f^*: \mathrm{Prop}(Y)\to\mathrm{Prop}(X)$ 與唯一笛卡兒提升分解。 |
| VI | 有理機率單子、CPTP 對偶與菱形脈絡合流 `dist_bind` / `verify_cptp_kleisli_duality` / `verify_qctx_diamond_confluence` | `context_cat/prob_monad_confluence.mbt` | 精確 Giry–Lawvere 有限分佈單子 $D_{\mathbb{Q}}$、Bohr 對易觀測脈絡檢驗、預層截面自然性與菱形合流大定理。 |

> 全部 **88 條命題逐條數學陳述、實算見證常數與負控制對照表** 請參閱專章文檔：[`docs/QPROB_THEOREMS_AND_ALGORITHMS.md`](../docs/QPROB_THEOREMS_AND_ALGORITHMS.md)。

---

## 4. 驗證指令

```bash
# 編譯與靜態無警告檢查
moon check --deny-warn --target wasm-gc

# 執行 qprob 六階 24 章 88 條命題完整套件
moon run cmd/qprob --target wasm-gc

# 執行跨全聯邦大合流旗艦驗算（含 quantum probability context confluence holds=true）
moon run cmd/showcase --target wasm-gc
```
