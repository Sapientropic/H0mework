# 最小支撑与逃逸完备性刻画

实时责任与机器签收只见[资本 active](../../../../../handoffs/source-generated-capital-relations-active-route.md)。
本卡的 source、actor、relation、raw claims、native responsibility 和 whole-ledger 均复用原资本链。

## 最小支撑

对原 `RawLaw` 定义：

```text
NoAsymmetry(law) :=
  ∀ raw port person,
    allowed(raw.tech, port, controller(raw.tech,port)) = true
    → allowed(raw.tech, port, person) = true
```

`Support.Law` 证明原完整五面合同 `Global.NoCapital law ↔ NoAsymmetry law`。
其五面包括 private phase、kernel、proper title、actual surplus 与 fresh historical control。
全开放是充分特例；整端口共同关闭也满足这枚合同。因此不把“全开放”、RootLawComplete 或 U8 都列成
排除 C 的独立必要前提；共同关闭也不被误认为已支付生活需求。

真实权限矩阵源保持原 stock、claims、Needs、指令和结算单位，只参数化控制者与受影响者的两枚 grant。
对任意原 clock／round，完整实际 kernel 存在 iff `ownerGranted=true ∧ recipientGranted=false`。
反过来 `NoAsymmetry` iff `ownerGranted=false ∨ recipientGranted=true`。开放受影响者时，原 actual inventory
与完整 next 相同；C 的消失没有删除原生产条件、实际支付或需要。
这枚逆命题明确消费该足够的真实源族；通用源的精确实际条件由下一层刻画。

## 每个原 C 的承重反解与原构造重建

`Support.Local/History` 从原 sealed witness 反解 accepted access、required port、原控制者准入与受影响者
排除、source/next 的 private phase，并保原 Need、appropriation、actor、relation、金融原址和历史。
proper title、actual surplus、private production 与 contribution 不改变这笔 access 来源。
跨 occurrence 的 Capital 同时反解原 access/need instruction 与当前 phase，不能用曾经的身份重发新 C。

`Support.Exact` 给原统一 family 的必要且充分支撑：原 title discovery、actual surplus discovery、historical
capital discovery 三支之一，连同该原项的实际 private phase／fresh control。真正 `ControlUse` 还须该原项
`Valid` 且实际调用所指 required port；family label 本身不替代执行。

`Models.Reconstruction` 直接运行原 compiler，输入只有原 law/current/word 与原 raw proposal/evidence：

- kernel 的 productive input、return flow、claim 三类：返回同 proposal 的原 C，或原 access/reciprocity/disposal guard 失败；
- appropriation 的 consumption、investment、retention、routed consumption、financial return 五类：返回原 dependency/evidence 的 witness，或精确原依赖／evidence guard 失败；
- 跨 occurrence 的 title、retention、consumption、investment 四类：同原 compiler 成功，或原 structural/evidence guard 失败。

任意既存 sealed C 都由自己的原字段精确重编译为同一值。模式量词来自原构造类型，不以几个实例充当全部世界。
充分性不收 `Checks` 或目标 C 作为 premise：原 checker 自己生成成功或失败。
真实库存返还、实际 issue、routed appropriation 三种非空源消费者保 Needs；issue 例的原 claim1 留存，
没有为支付生活把债务抹去。一般 guard 总分解是 checker 刻画，具体实物与金融源才是反模型 producer。

## 所有实际绕行的源内全账处置

`Escape.Rows/History` 沿原 `Epoch.Current.sourceLedger` 的 actual next 递归运输所有旧行。任意实际有限
截点都保持原 claim 的 injective image、原责任不 refill、已付行保持0；不造第二 row/claim registry。
code、review、migration、native birth 和普通 head 都由原 source dispatcher 选择。

`Escape.Material/Actual` 对任意有限源语法及其真实制度 history 证明：

```text
target stock + actual debit = original stock + actual credit
raw target claims = raw original claims + actual original financial delta
```

每个物量净增都反解到原返回 Report inventory 中的 accepted positive-credit item。外部补料、真实生产、
现金转移与金融发行不能互相替代；raw matrix 与尚待 head 消费的 native account 分开保持。
完整资源分栏、原生活维护与 actual clock 沿此前已签成本合同继承，不把“全账”简化为一个进度预算。

原根 `handlerFace` 直接读取 active public interpretation。任何被呈示为再生 C 的 kernel 都自产一枚具体
permission address：claimed law 在原见证地址拒绝 subject，active handler 在同址准入；因此不能用改名、
换 code 或投影把解释变更藏起来。合法新来源仍须成为原 source 输入或实际 revision，不能取得账外 authority。

`Escape.Authority` 直接消费既有 legislation compiler：每个预发射安装的合法 source program 生成
`RootLawComplete ∧ U8Available`，presentation／visible-residual rejection／rooted action+whole-ledger+next／
exact same-row conditional U8 穷尽；没有第五类。U8 的首写、旧新行与 next 使用原框架，不另造逃逸法庭。
“完整处置”包含精确拒绝和残差承担者，不把资源短缺报告成成功支付。

## 同原资本根的消费

`Characterization.Root.MinimalSupportAndEscapeAt` 继承原 `ClearingCostClaimsClosedAt` 及此前全部资本量词，
共同消费上述精确 iff、见证逆解、构造重建、真实反模型和任意实际绕行。原注册 `seed/grossClaim` 直接消费
整份合同，RootLawComplete/U8 与 actual next 仍由原源拥有。

源码相对 `Accounting/Quantifiers/Assembly/Strengthening/Characterization/`：
`Support/`、`Models/Permissions/`、`Models/Reconstruction/`、`Escape/`、`Root/Contract.lean`、`Consumers/Registered.lean`。
