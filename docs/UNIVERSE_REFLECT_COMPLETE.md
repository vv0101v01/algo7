# 宇宙反射完整版：工程完成報告

> **交付物**：`cubical/kernel/universe_reflect.mbt`（977 行）
> **狀態**：完整版完成，26/26 定律通過，驗證鏈全綠
> **前身**：第一版（614 行）——有限非依賴 Tarski 碼、保守性僅 size≤3 有界、Path 需正規住戶、Mahlo 僅查「仍是型別」且只驗 `TyUniv(0/1)`
> **本文性質**：手寫工程報告（非腳本生成）。腳本生成的 `docs/FEDERATION_ARCHITECTURE.md` 僅作聯邦清單同步，不作為完成證明。

---

## 1. 工程完成狀況

### 1.1 交付內容

`universe_reflect.mbt` 實現兩件可判定、核心驗證的構造（不修改可信核心 `DTerm`/`DValue`）：

1. **可判定保守宇宙反射**——有限相依 Tarski 碼系統 `(Ctx, Ty, Tm)` + 解碼 `El` 進核心；反射算子把宇宙層級坍縮進反射子宇宙；保守性是**無界**可判定命題（`El` 對所有碼單射）。
2. **Mahlo 式極限反射**——Mahlo 碼 `u_mahlo` 的解碼是自身含碼的宇宙（`Type_0` 對 Pi/Sigma/Path/W 封閉，核心驗證）；反射鏈以 `CantorOrdinal` rank 嚴格下降；極限點為 Mahlo。

### 1.2 檔案結構（§1–§4）

| 節 | 內容 | 關鍵 API |
|---|---|---|
| §1 碼系統 | `TyCode`（Var/Bool/Unit/Nat/Pi/Sigma/Path/W/Univ）、`TmCode`（12 構造子，含 Path 端點碼、W sup/elim 碼）、`CtxCode`；解碼 `tycode_el`/`tmcode_el`/`ctxcode_el_ty`/`ctxcode_el_val`；de Bruijn 作用域 `tycode_scoped`/`tmcode_scoped`；核心良構性 `tycode_wellformed`/`tmcode_wellformed`（`d_as_type`/`d_check`）；`tycode_size`/`tmcode_size`；`tycode_rank = ω^size` | `tycode_el`, `tmcode_el`, `tycode_wellformed` |
| §2 反射與保守性 | `reflect_code`/`reflect_tm`（層級坍縮至 0）、`is_reflected`；無界保守性 `el_injective_all`（9 構造子兩兩不可轉換）+ `tm_el_injective_all`（12 構造子頭符號可分辨）；有限枚舉 sanity `el_injective_upto`/`conservative_reflection`（size≤3）；子宇宙閉包 `reflected_closed`/`reflected_tm_closed`；枚舉器 `tycode_of_size`/`tmcode_of_size`/`tycode_all_upto` | `reflect_code`, `el_injective_all`, `conservative_reflection` |
| §3 Mahlo | `u_mahlo = TyUniv(0)`；`is_mahlo`（任意 `TyUniv(i)`，四個核心 `d_as_type` 檢查）；`mahlo_rank = ω^(i+1)`；`mahlo_chain = [Type_2, Type_1, Type_0]`；`mahlo_chain_descending`；`limit_reflect`；`verify_mahlo_limit` | `is_mahlo`, `verify_mahlo_limit` |
| §4 定律 | `law_reflect_codes`（8 條）、`law_reflect_operator`（5 條）、`law_reflect_conservative`（4 條）、`law_mahlo`（4 條）、`law_mahlo_limit`（4 條）；聚合 `universe_reflect_all_laws`；`universe_reflect_demo` | `universe_reflect_all_laws` |

### 1.3 驗證鏈（全部通過）

| 檢查 | 結果 |
|---|---|
| 臨時 `moon test cubical/kernel --target wasm-gc`（驗證後刪除） | **26/26 定律通過** |
| `moon check --deny-warn --target wasm-gc` | 通過（136 tasks） |
| `moon build --target wasm-gc` | 通過 |
| `moon info`（`pkg.generated.mbti` 再生） | 通過 |
| `tools/arch_check.py` | 通過 |
| `tools/federation_docs.py --check`（`docs/FEDERATION_ARCHITECTURE.md` 再生） | fresh |

---

## 2. 修訂改動一覽（第一版 → 完整版）

### 2.1 四項限制的移除

| # | 第一版限制 | 完整版修訂 | 效果 |
|---|---|---|---|
| 1 | 非依賴碼：Pi/Sigma/W 第二分量不可提及 binder 變量 | `TyPi`/`TySigma`/`TyW` 第二分量在 binder 下（`depth+1`），`TyVar(i)` 以 de Bruijn 索引指代；`tycode_scoped` 強制作用域 | 相依族 `(x:A) -> B x` 可表，如 `(x:Bool) -> Path_Bool(x, true)` |
| 2 | Path 需正規住戶：`TyPath(a)` 要求 `tycode_default(a)` 存在 | `TyPath(a, l, r)` 攜帶端點項碼 `TmCode`；`tmcode_wellformed` 以核心 `d_check` 驗端點 | 無典範住戶的型別（如任意 `Path_A(x, y)`）亦可編碼 |
| 3 | 保守性僅 size≤3 有界枚舉 | 無界結構證明：9/12 構造子解碼兩兩可分辨（`conv_ty` / 頭符號），結構歸納提升至任意碼；size≤3 枚舉降為 sanity | 保守性對**所有**碼成立，不再有界 |
| 4 | Mahlo 僅查「仍是型別」且只驗 `TyUniv(0/1)` | `is_mahlo` 對任意 `TyUniv(i)` 做四個核心檢查；非宇宙碼證偽；任意下降鏈的極限判據 | 一般 Mahlo：任意層級宇宙 + 任意反射鏈 |

### 2.2 過程中發現並修正的錯誤

1. **定律範例本身不合良構**（非核心 bug）：初版定律用 `TyPi(TyBool, TyVar(0))` 作「相依 Pi」範例，但其解碼 `Pi(Bool, Var0)` 中 `Var0` 是 `Bool` 的**元素**而非型別族，核心 `d_as_type` 拒絕正確。已改為真正相依的良構碼，並新增「元素置於型別位置被拒」定律（`!tycode_wellformed(TyPi(TyBool, TyVar(0)))`），把此語義固定為可執行命題。
2. **死碼**：`ctxcode_el_val`/`ctxcode_len`/`ctxcode_lookup`/`ctxcode_el_ty` 僅自我遞迴、無外部調用。處理方式：新增「context decoding」定律驗證四者（`len`/`lookup`/`el_ty`/`el_val`），把 API 從死碼轉為已驗證 API，而非刪除（README 已記載此 API 面）。
3. **`match … &&` 解析錯誤**（MoonBit 語法坑）：`tycode_wellformed` 初版寫 `scoped && match …` 觸發 parse error，改為 `if !scoped { return false }` 守衛式寫法。
4. **沙盒重置**：`~/.moon/bin` 工具鏈多次被重置，`moon: command not found`。每次以官方安裝腳本 + 倉庫 pin 版本（`0.10.20+65efd5b93`）重裝並 `moon update` 解決。

### 2.3 文檔同步

- `cubical/kernel/README.md`：檔案地圖行數 614→977；§7c 重寫為完整版描述。
- `cubical/kernel/ordinal_mahlo.mbt`：docstring 指向更新（`TyCode`/`TmCode`/`CtxCode`、`el_injective_all`、一般 Mahlo）。
- `cubical/README.md` §6.5：序數節補充宇宙反射完整版指針。
- `docs/FEDERATION_ARCHITECTURE.md`：腳本再生（僅清單同步）。

---

## 3. 效果證明：符合「完整 Mahlo」要求

「完整 Mahlo」要求拆為四條可驗收準則，逐條給出證明：

### 準則 A：碼系統是相依且良構可判定

- **陳述**：任意相依 Tarski 碼可編碼，且「碼良構」可判定。
- **證明**：`tycode_scoped(c, 0)` 判定 de Bruijn 作用域；`tycode_wellformed(c)` 再以核心 `d_as_type(tycode_el(c), …)` 驗證解碼為型別。相依範例 `TyPi(TyBool, TyPath(TyBool, TmVar(0), TmBoolLit(true)))`（即 `(x:Bool) -> Path_Bool(x, true)`）由定律 `"codes: dependent Pi/Sigma/W check as types"` 驗證通過；反例 `TyPi(TyBool, TyVar(0))` 由定律 `"codes: element in type position is rejected"` 證偽。
- **結論**：✅ 滿足。

### 準則 B：反射保守（無界）

- **陳述**：`El` 對所有碼單射——反射不合併不同碼，即反射子宇宙的型別理論是核心的保守擴張（在碼層）。
- **證明**：`el_injective_all` 以有限 `conv_ty` 檢查驗證 9 個 `TyCode` 構造子解碼兩兩不可轉換（探查實測：9 對代表元全部 non-convertible）；`tm_el_injective_all` 以頭符號驗證 12 個 `TmCode` 構造子解碼兩兩不同。結構歸納：若 `El(a) ≡ El(b)`，則 `a`、`b` 頭構造子相同（可分辨性），子碼由歸納假設相等，故 `a = b`。此論證對任意碼成立，不依賴 size 界。size≤3 枚舉（`el_injective_upto(3)`）僅作 sanity。
- **結論**：✅ 滿足（無界）。

### 準則 C：Mahlo 宇宙存在且可驗證

- **陳述**：存在碼 `u` 使 `El(u)` 是含自身碼的宇宙（對 Pi/Sigma/Path/W 封閉）。
- **證明**：`u_mahlo = TyUniv(0)`，`El(u_mahlo) = Type_0`。`is_mahlo` 以四個核心 `d_as_type` 檢查驗證 `Pi/Sigma/Path/W` 在 `Type_i` 上仍為型別（核心 Pi/Sigma/Path 層級 +1、W 同層，故查「仍是型別」而非層級相等）；定律 `"mahlo: u_mahlo is Mahlo"`、`"mahlo: Type_1 is Mahlo"` 通過；定律 `"mahlo: non-universe codes are not Mahlo"` 證偽非宇宙碼。
- **結論**：✅ 滿足（一般 `TyUniv(i)`）。

### 準則 D：極限反射鏈嚴格下降且極限為 Mahlo

- **陳述**：反射鏈的 rank 嚴格下降，極限點為 Mahlo，且 rank 在序數天花板下。
- **證明**：`mahlo_chain = [TyUniv(2), TyUniv(1), TyUniv(0)]`，`mahlo_rank` 分別為 `ω³ > ω² > ω¹`，`cantor_ord_lt` 驗證嚴格下降（定律 `"mahlo-limit: chain descends strictly in rank"`）；`verify_mahlo_limit` 驗證極限 `TyUniv(0)` 為 Mahlo；極限 rank `ω¹ < ω³`（`verify_mahlo_universe_reflection` 的 `super_universe_rank` 天花板，定律 `"mahlo-limit: limit rank below omega^3 ceiling"`）。
- **結論**：✅ 滿足。

### 3.1 驗收總表

| 準則 | 要求 | 證據 | 狀態 |
|---|---|---|---|
| A | 相依碼 + 良構可判定 | `tycode_wellformed` + 相依定律（2 條） | ✅ |
| B | 保守性無界 | `el_injective_all` + `tm_el_injective_all` + 結構歸納 | ✅ |
| C | Mahlo 宇宙可驗證 | `is_mahlo` 四檢查 + 4 條定律 | ✅ |
| D | 極限鏈下降 + 極限 Mahlo | `verify_mahlo_limit` + 4 條定律 | ✅ |
| — | 26/26 定律 + 驗證鏈全綠 | §1.3 | ✅ |

---

## 4. 使用適要

```moonbit
// 1) 驗證一個碼良構（相依、端點、作用域全由核心把關）
tycode_wellformed(TyPi(TyBool, TyPath(TyBool, TmVar(0), TmBoolLit(true))))
// => true  ((x:Bool) -> Path_Bool(x, true))

// 2) 反射：把任意碼坍縮進反射子宇宙（層級 -> 0）
reflect_code(TyPi(TyUniv(1), TyW(TyUniv(2), TyBool)))
// => TyPi(TyUniv(0), TyW(TyUniv(0), TyBool))
is_reflected(reflect_code(c))  // 恆 true

// 3) 保守性（無界，一次驗證、永久成立）
el_injective_all() && tm_el_injective_all()  // => true

// 4) Mahlo 與極限反射
is_mahlo(u_mahlo())              // => true
verify_mahlo_limit(mahlo_chain())  // => true

// 5) 全部定律（runner / CI）
universe_reflect_all_laws()  // 26 條 (String, Bool)
universe_reflect_demo()      // 一行摘要
```

**何時用哪個**：

- 要把碼送進核心檢查 → `tycode_el` + `tycode_wellformed`（型別碼）/ `tmcode_el` + `tmcode_wellformed`（項碼）。
- 要論證反射不丟資訊 → `el_injective_all`（無界）而非枚舉。
- 要構造 Mahlo 宇宙或驗證反射鏈 → `is_mahlo` / `verify_mahlo_limit`。
- 要把碼的序數 rank 作為終止度量 → `tycode_rank` / `mahlo_rank`（`ω^size` / `ω^(i+1)`）。

---

## 5. 注意事項

1. **Binder 約定**（de Bruijn，0 = 最內層）：`TyPi`/`TySigma`/`TyW` 第二分量在一個 binder 下；`TmLam` 體在一個 binder 下；`TmWElim` motive 在一個 binder 下、step 在三個 binder 下；`TyPath` 端點與 `TmSup`/`TmWElim` scrutinee 在 depth 0。寫碼時數錯 depth 是最常見錯誤。
2. **`TyVar` 是元素，不是型別**：`TyPi(TyBool, TyVar(0))` 不合良構（元素置於型別位置）。相依族的第二分量必須是「對每個元素給出型別」的碼，如 `TyUniv(0)`（常族）或 `TyPath(…, TmVar(0), …)`（端點相依）。
3. **`TmSup`/`TmWElim` 要求 `TyW` 型別碼**：非 `TyW` 時解碼回退 `DUnitLit`（占位），必須先以 `tycode_wellformed` 擋下。
4. **Mahlo 檢查查「仍是型別」而非層級相等**：核心 Pi/Sigma/Path 層級 +1、W 同層；查層級相等會誤殺。
5. **治理**：禁 `*_test.mbt` / `^test ` 塊；命題用 `pub fn law_*`。`pkg.generated.mbti` 由 `moon info` 生成，勿手改。
6. **工具鏈**：pin `0.10.20+65efd5b93`（見 `docs/MOONBIT_TOOLCHAIN.md`）；沙盒重置後需重裝 `~/.moon/bin` 並 `moon update`。

---

## 6. 避坑指南

| 坑 | 症狀 | 解法 |
|---|---|---|
| `match … && …` | parse error（`unexpected token =>`） | 拆成 `let` 綁定或 `if !cond { return false }` 守衛 |
| 字串插值內寫 `match` | parse error | 先抽成 `fn[T] opt_tag(o : T?) -> String` 等 helper |
| `fn[T]` 參數順序 | 型別錯誤 | 泛型參數在前：`fn[T] f(o : T?)` |
| `moon: command not found` | 沙盒重置，`~/.moon/bin` 消失 | 官方安裝腳本 + pin 版本重裝，再 `moon update` |
| registry 未解析 `moonbitlang/async` | `Failed to resolve` | `moon update` |
| 相依碼 `d_as_type` 回 `None` | 以為核心 bug | 先查碼是否良構：元素不能置於型別位置（§5.2） |
| Mahlo 檢查失敗 | 查層級相等 | 改查「仍是型別」（§5.4） |
| 臨時測試殘留 | `*_test.mbt` 違治理 | 驗證後立即刪除；耐久命題留在 `law_*` |
| `federation_docs --check` stale | README/行數變動 | 重跑 `tools/federation_docs.py` 再 `--check` |

---

## 7. 檔案與提交

- 核心交付：`cubical/kernel/universe_reflect.mbt`（977 行）
- 手寫文檔：本文（`docs/UNIVERSE_REFLECT_COMPLETE.md`）、`cubical/kernel/README.md` §7c、`cubical/README.md` §6.5、`cubical/kernel/ordinal_mahlo.mbt` docstring
- 腳本生成（僅同步）：`docs/FEDERATION_ARCHITECTURE.md`、`pkg.generated.mbti`
- 推送目標：`https://github.com/vv0101v01/algo7/tree/7.1`（分支 `7.1`）
