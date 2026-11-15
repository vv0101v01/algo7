# `qprob/context_cat/` — 空間與子場雙範疇、主命題纖維化、機率單子與量子機率脈絡合流

> **架構位置**：套件 `qprob-context-cat`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 5**，
> `depends_on: [qprob-asymptotic, qprob-unbounded, qprob-fock, qprob-ccr-field, qprob-nc-measure]`。

## 1. 定位與四步範疇化合流

本套件將前五階（Stage I–V）的子場塔與量子空間提升為統一的高階範疇與機率單子脈絡體系：

1. **空間與子場雙範疇 `ℬ_qprob`**（`SpaceSubfieldCell0`、`SpaceMorphism1`、`SpaceCell2`）：
   - 0-胞涵蓋子場塔 `ℚ`、`ℚ(√d)`、`ℚ((ε))_≤M` 與五階量子空間 `lim_←V_k`、`Op*(𝒟)`、`ℱ_q(ℋ)`、`CCR(L²)`、`NCMeas`；
   - 1-態射承載子場嵌入、正規化跡左逆截面、標準部商同態與跨空間提升；
   - 2-態射承載漸近收斂與 Whiskering 偏差，嚴格滿足 **Godement 縱橫互換律** `(β₂ ∘_h α₂) ∘_v (β₁ ∘_h α₁) == (β₂ ∘_v β₁) ∘_h (α₂ ∘_v α₁)`。
2. **主命題纖維化 `π : ∫ Prop → ℬ_qprob`**（`FiberPrincipalProp`、`PrincipalPropMorphism`）：
   - 將八個空間與子場的主命題（攜帶實算特徵不變量與真值）纖維化於 `ℬ_qprob` 之上；
   - 實作逆變拉回函子 `f* : Prop(Y) → Prop(X)`、笛卡兒提升 `Cart(f, Q)` 與唯一泛因式分解 `factor_through_cartesian_lift`。
3. **精確有理機率單子 `(D_ℚ, η, μ)` 與 Kleisli 範疇 `Kl(D_ℚ)`**（`ProbDist[T]`）：
   - 以正規形去重支撐集實作 Giry–Lawvere 有限有理機率單子，滿足左右單位律、Kleisli 結合律、雙層壓平 `μ`、交換單子 Fubini 邊際化，以及 CPTP Kraus 通道對偶。
4. **量子機率脈絡範疇 `QProbCtx` 與菱形合流大定理**（`QuantumProbContext`、`ContextMorphism`）：
   - 以兩兩對易自伴觀測量族 `[A_i, A_j] = 0` 與相容完備 POVM 定義 Bohr 觀測脈絡（非對易對 `{σ_x, σ_z}` 由公理拒絕）；
   - 證明粗粒化脈絡預層截面三路恆等，以及分叉細化脈絡 `C_left ← C_apex → C_right` 在 `QProbCtx` 與機率單子 `D_ℚ` 下零誤差合流至終端脈絡 `C_nadir`。

## 2. 檔案

| 檔案 | 行數 | 職責 |
|---|---:|---|
| `bicat_fibration.mbt` | 597 | 雙範疇 `ℬ_qprob`（0/1/2-胞與 Godement 互換律）、主命題纖維化 `∫ Prop`、逆變拉回、笛卡兒提升與八空間主命題切面 |
| `prob_monad_confluence.mbt` | 693 | 有理機率單子 `ProbDist[T]`、Kleisli 複合、CPTP 對偶、量子機率脈絡範疇 `QProbCtx`、預層截面自然性與菱形合流大定理 |
| `laws.mbt` | 719 | 4 章 / **18 條命題**（含非相容態射、非正定變形、負準機率與 Heisenberg 非對易脈絡 4 條負控制） |
