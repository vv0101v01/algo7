# `qprob/context_cat/` — 空間子場雙範疇、Grothendieck 主命題纖維化、有理機率單子與量子機率脈絡範疇合流（Stage VI · Layer 5）

> **架構位置**：套件 `qprob-context-cat`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 5**，`depends_on: [qprob-asymptotic, qprob-unbounded, qprob-fock, qprob-ccr-field, qprob-nc-measure]`。
> **規模**：3 個 `.mbt` 檔、**2,009 行**、4 章、**18 條命題**（編號 `[071]–[088]`，含 3 條負控制）。

---

## 1. 數學結構定位與演變動因

前五階（`asymptotic` $\to$ `unbounded` $\to$ `fock` $\to$ `ccr_field` $\to$ `nc_measure`）在各自的數域與算子空間中建立了 70 條具體量子概率定理。第六階將整個量子概率體系提升至**二階範疇論、依值邏輯纖維化與單子代數語義**，透過四步連續構造完成大合流：

1. **空間與子場雙範疇 $\mathcal{B}_{\mathrm{qprob}}$**：
   * **0-胞（`SpaceSubfieldCell0`）**：涵蓋代數子場塔節點 $\mathbb{Q}$、$\mathbb{Q}(\sqrt{d})$、$\mathbb{Q}((\varepsilon))_{\le M}$ 與五階量子空間節點 $\varprojlim V_k$、$\mathrm{Op}^*(\mathcal{D})$、$\mathcal{F}_q(\mathcal{H})$、$\mathrm{CCR}(L^2)$、$\mathrm{NCMeas}$；
   * **1-胞（`SpaceMorphism1`）**：子場嵌入與正規化跡／標準部左逆截面、Yosida 預解正則化、二次量子化提升、格點塗抹嵌入、Born 矩泛函與 Naimark 等距擴張；
   * **2-胞（`SpaceCell2`）**：平行 1-態射間的漸近收斂與比較變換，支援水平 Whiskering 與垂直複合並滿足 **Godement 縱橫互換律** $(\beta_2 \circ_h \alpha_2) \circ_v (\beta_1 \circ_h \alpha_1) = (\beta_2 \circ_v \beta_1) \circ_h (\alpha_2 \circ_v \alpha_1)$。
2. **主命題 Grothendieck 纖維化 $\pi : \int \mathrm{Prop} \to \mathcal{B}_{\mathrm{qprob}}$**：
   * 每個基底 0-胞 $X$ 上方懸掛主命題纖維偏序範疇 $\mathrm{Prop}(X)$（攜帶實算特徵不變量 `QVal` 與演繹強度秩）；
   * 沿基底 1-態射 $f : X \to Y$ 定義**逆變拉回贗函子 $f^* : \mathrm{Prop}(Y) \to \mathrm{Prop}(X)$**，滿足 $(g \circ_h f)^* = f^* \circ g^*$ 與 $(\mathrm{id}_X)^* = \mathrm{id}$；
   * 構造**笛卡兒提升 `cartesian_lift_morphism(f, Q)`** 與唯一泛因式分解 `factor_through_cartesian_lift`，貫通五階主命題態射鏈並攔截非正定 $q=2$ 變形偽態射。
3. **精確有理機率單子 $(D_{\mathbb{Q}}, \eta, \mu)$ 與 Kleisli 隨機核範疇 $\mathbf{Kl}(D_{\mathbb{Q}})$**：
   * 正規形去重有理機率分佈 `ProbDist[T]`（嚴格拒絕負權重準機率與零質量輸入）；
   * 證明單子左右單位律、結合律、雙層壓平 `dist_flatten`、交換單子張量積 `dist_product` 的 Fubini 邊際化定律，以及 **CPTP Kraus 量子通道與 Kleisli 馬可夫核的 Schrödinger–Heisenberg 對偶**。
4. **量子機率脈絡範疇 $\mathbf{QProbCtx}$ 與菱形合流大定理**：
   * 物件 `QuantumProbContext` 由量子態 $\rho$、**兩兩對易自伴觀測量族 $[A_i, A_j] = 0$**（Bohr–Isham–Butterfield 交換觀測脈絡）與相容完備 POVM 組成，非對易對 $\{\sigma_x, \sigma_z\}$ 由公理直接拒絕；
   * 態射 `ContextMorphism` 為滿足效應逆變拉回守恆 $E_{\text{coarse}}[j] = \sum_{\pi(i)=j} E_{\text{fine}}[i]$ 的結果粗粒化映射；
   * 證明粗粒化預層截面三路自然性（粗單子期望 $=$ 細單子拉回期望 $=$ 算子跡 $\operatorname{Tr}(\rho A)$），並證明共享細化分叉 $C_{\text{left}} \leftarrow C_{\text{apex}} \rightarrow C_{\text{right}}$ 在 $\mathbf{QProbCtx}$ 與單子 $D_{\mathbb{Q}}$ 下**零誤差菱形合流**至終端宇稱脈絡 $C_{\text{parity}}$。

---

## 2. 檔案與職責

| 檔案 | 行數 | 核心型別與公開介面 |
|---|---:|---|
| `bicat_fibration.mbt` | 597 | `SpaceSubfieldCell0`、`SpaceMorphism1`、`SpaceCell2`、`bicat_id1`、`bicat_atom1`、`bicat_comp1`、`bicat_id2`、`bicat_make2`、`bicat_vcomp2`、`bicat_hcomp2`、`bicat_check_interchange`、`subfield_quad_roundtrip`、`subfield_jet_roundtrip`、`FiberPrincipalProp`、`PrincipalPropMorphism`、`canonical_principal_prop_section`、`pullback_principal_prop`、`make_prop_morphism`、`cartesian_lift_morphism`、`factor_through_cartesian_lift` |
| `prob_monad_confluence.mbt` | 693 | `ProbDist[T]`、`dist_normalize`、`dist_pure`（$\eta$）、`dist_bind`、`dist_flatten`（$\mu$）、`dist_map`、`dist_product`、`dist_expect_q`、`kleisli_compose`、`verify_cptp_kleisli_duality`、`QuantumProbContext`、`ContextMorphism`、`qctx_is_valid`、`qctx_morphism_is_valid`、`qctx_to_prob_monad`、`verify_qctx_presheaf_section`、`verify_qctx_diamond_confluence`、`QuantumContextConfluenceReport`、`verify_grand_qprob_context_confluence` |
| `laws.mbt` | 719 | 4 章 / **18 條命題**（`context_cat_all_laws`） |

---

## 3. 核心演算法記錄與簡介

| 演算法函式 | 輸入 → 輸出 | 數學原理與複雜度簡介 |
|---|---|---|
| `bicat_comp1` / `bicat_vcomp2` / `bicat_hcomp2` | 雙範疇 1-胞與 2-胞運算 | 檢驗源匯相容性後複合轉移步驟、尺度因子與正定序保持旗標；2-胞水平與垂直複合嚴格維持雙線性缺陷傳播並支援 `bicat_check_interchange` 驗證 Godement 縱橫互換律。 |
| `canonical_principal_prop_section` | `() -> Array[FiberPrincipalProp]` | 即時重算 8 個空間與子場的主命題錨定切面：子場塔單位不變量 $1$，以及射影塔、無界算子、全福克、連續場、非交換測度的核心不變量 $2$。 |
| `pullback_principal_prop` / `cartesian_lift_morphism` | `(SpaceMorphism1, FiberPrincipalProp) -> PrincipalPropMorphism?` | 實作 Grothendieck 纖維化的逆變拉回贗函子 $f^* : \mathrm{Prop}(Y) \to \mathrm{Prop}(X)$ 與笛卡兒提升 $\mathrm{Cart}(f, Q) : (X, f^*Q) \to (Y, Q)$，並由 `factor_through_cartesian_lift` 計算唯一泛因式分解態射 $\bar{u}$。 |
| `dist_normalize` / `dist_bind` / `dist_flatten` | `ProbDist[T]` 單子引擎 | 拒絕任何負權重或零總質量輸入，合併重複支撐點並正規化至 $\sum_x p(x) = 1$；實作 Giry–Lawvere 單子三元組 $(D_{\mathbb{Q}}, \eta, \mu)$ 與 Chapman–Kolmogorov Kleisli 核合成 `kleisli_compose`。 |
| `verify_cptp_kleisli_duality` | `(Array[UnboundedOp], QuantumProbState, PovmMeasure) -> Bool` | 驗證量子開放系統 Schrödinger 態演化 $\mathrm{Born}(\Phi(\rho), E)$ 與 Heisenberg 對偶效應拉回經單子邊際推前 $D_{\mathbb{Q}}(\pi_2)(\mathrm{Born}(\rho, E\circ \Phi^*))$ 逐點精確相等。 |
| `qctx_is_valid` / `qctx_morphism_is_valid` | `QuantumProbContext -> Bool` / `ContextMorphism -> Bool` | 檢驗觀測量族兩兩對易 $[A_i, A_j] = 0$、自伴性與 POVM 完備性（攔截 Heisenberg 不相容脈絡如 $\{\sigma_x, \sigma_z\}$），並驗證粗粒化態射的逆變效應加總守恆 $E_{\text{tgt}}[j] = \sum_{\pi(i)=j} E_{\text{src}}[i]$。 |
| `verify_qctx_diamond_confluence` / `verify_grand_qprob_context_confluence` | `() -> QuantumContextConfluenceReport` | 驗證不等價中間脈絡 $C_{\text{left}} \leftarrow C_{\text{apex}} \rightarrow C_{\text{right}}$ 在範疇態射與機率單子推前下零誤差合流至 $C_{\text{nadir}}$，並串聯全部六階輸出完整合流證書（供 `cmd/showcase` 直接驗證）。 |

---

## 4. 定理與命題記錄（`[071]–[088]`）

| 編號 | 定理／命題 | 實算見證與負控制 |
|---:|---|---|
| `[071]–[074]` | **雙範疇 $\mathcal{B}_{\mathrm{qprob}}$ 截面律、範疇律與 Godement 縱橫互換律** | 子場左逆截面 $\frac{1}{2}\operatorname{Tr}\circ\iota_{\sqrt{2}}(-7/11)=-7/11$、$\mathrm{st}\circ\iota_\varepsilon(-7/11+\frac{9}{5}\varepsilon)=-7/11$；1-胞結合與單位律、2-胞 Godement 互換律精確成立；錯位源匯複合回傳 `None`（負控制）。 |
| `[075]–[078]` | **Grothendieck 主命題纖維化、逆變拉回、笛卡兒泛分解與五階貫通鏈** | 8 空間／子場主命題切面全數實算成立；$(g\circ_h f)^*(R) = f^*(g^*(R))$；任意態射沿 $f\circ u$ 唯一分解經由 $\mathrm{Cart}(f,R)$；五階主命題鏈貫通且非正定 $q=2$ 變形態射被攔截。 |
| `[079]–[082]` | **Giry–Lawvere 有理機率單子 $(D_{\mathbb{Q}}, \eta, \mu)$、Fubini 定律與 CPTP 對偶** | 單子左右單位律、Kleisli 結合律與雙層壓平恆等；獨立積邊際投影與 $\mathbb{E}[XY]=\mathbb{E}[X]\mathbb{E}[Y]$；CPTP 通道與單子邊際推前對偶恆等；負權重準機率 $[\frac{3}{2}, -\frac{1}{2}]$ 回傳 `None`（負控制）。 |
| `[083]–[088]` | **量子機率脈絡範疇 $\mathbf{QProbCtx}$、預層截面自然性、Heisenberg 阻礙與六階大合流** | 相容對易脈絡 $[Z_1, Z_2, ZZ]$ 宇稱分佈 $[\frac{17}{25}, \frac{8}{25}]$；不等價中間脈絡 $C_{\text{left}}\neq C_{\text{right}}$ 零誤差合流；粗單子／細單子拉回／算子跡三路恆等；非對角 $C(\sigma_x)$ 譜矩合流；非對易 $\{\sigma_x,\sigma_z\}$ 被攔截（負控制）；`verify_grand_qprob_context_confluence().all_holds == true`。 |
