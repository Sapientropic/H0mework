# 典范保持与严格付费生成进步

> 稳定机制；当前路线仍由 [Society active](../../handoffs/process-generated-society-active-route.md) 维护。

## 比较对象

比较同一 canonical paid tail 上已实际生成的有限前沿。令 `Hᵢ` 为原
`sourceGeneratedFiniteContributionCapacityPostSettlementFutureBirthFrontier` 到第 `i` 拍的前缀，
`Aᵢ` 为其中真实 `AnyPeriodicActualServiceExit` 的 authority image。
每个像点保原付款、实际服务、非捕获退出及原根身份；`authorityAt_fromNativeWrite` 将它认回原 native write。
这不是新 ledger、选项 registry、utility 或未来表。

结构严格序同时要求源、目标的 `FiniteExitCapacityConstitutionAt` 与 `Aᵢ ⊂ Aⱼ`。
完整一步合同另消费 arbitrary-Payment preservation、所有原 channels、whole-ledger、残差消费者和 generated next。
所以“严格更好”在此指 **典范结构保全，同时实际兑现的可行动发生严格增加**。
当前某个时点的可选动作总数、收入和幸福不充当这枚序；真实续约可以保持瞬时退出容量为 1。

## 原源如何支付严格性

1. `frontier_succ` 将原前沿原样保留，只附加原目标 occurrence；不是把旧 witness 重新贴上新名字。
2. `authorityAt_injective` 沿实际付款 occurrence 的单射认回源 visit，继而 `freshAuthority` 证明新 authority
   不属于**整个**旧像，`authoritySupport_strictMono` 给任意有限延伸的真包含。
3. 令 `i = cycleLifecycleIndex initial depth`。已有 responsibility difference 的边界取 `i - 1`，
   其左右 replay 正是 `i → i+1`。`sameEdge_authorityK_exact` 把新像点认回这枚 difference 的右 `K`。
4. `sameEdge_callerPayment_nextPaidBy` 对每个合法原 Payment 认回同一目标，保留调用者 Payment 本身；
   不将不同 Payment 证明值强等同。`sameEdge_wholeLedger_is_original` 保原整账。
5. 新 `K` 的独立消费者回到原 M9 exact event 与原 `RootInquiryU8CompletionRegression.entry`。
   所有旧 channel 在两端回到原 actor/relation，并从各自实际付款重新兑现。

这使严格增长既有“旧项保留”，也有“像外新项”。原 `p` 生成目标 occurrence，新增服务由目标自身
native Payment 兑现；比较在该目标已实际生成后读取，不在源 current 预记未付未来。

## 总口与直接消费者

- [Frontier.lean](../../../SaturationMonoid/ProcessGame/Regression/Society/M14/Progress/Frontier.lean)：
  原 finite frontier 的 authority image、真包含、任意有限距离与原 native write。
- [SameEdgeNovelty.lean](../../../SaturationMonoid/ProcessGame/Regression/Society/M14/Progress/SameEdgeNovelty.lean)：
  同边 replay／Payment／原行／independent consumer 对齐。
- [PaidStep.lean](../../../SaturationMonoid/ProcessGame/Regression/Society/M14/Progress/PaidStep.lean)：
  `preservation_and_novelty_strictlyBetter` 生成完整 `StrictCanonicalPaidStepAt`；
  `strictCanonicalProgress_iff_lt`、不可自反与传递性给同源有限链上的严格序。
- [WholeProgram.lean](../../../SaturationMonoid/ProcessGame/Regression/Society/M14/Progress/WholeProgram.lean)：
  `canonicalSociety_registeredFiniteCycleStrictCanonicalProgress` 直接消费原 whole sink 的
  `registeredFiniteCycleCanonicalRootLaw`，保其原 initial cycle 与 root-law 证书，覆盖请求前缀内每枚原 Payment
  并按需生成下一条边。没有新增运行时 authority。

原 grammar occurrence 比 lifecycle 起点晚两次付款；完整根法消费保留这个 `+2` offset，
不将 `i→i+1` 的首付边与 `i+2→i+3` 的 grammar 边合并。

## 量词与验收

逐拍结论针对这条源自己每次实际生成 birth 的 canonical productive cycle。
一般 cofinal productivity 只保证每个截点之后存在严格增长的有限窗口，不能凭此推出所有微 tick 严格增长。

[Regression.lean](../../../SaturationMonoid/ProcessGame/Regression/Society/M14/Progress/Regression.lean)
消费原 M9 initial visit 与零 observation fuel 的两条实际付款边，检查任意显式窗口；反控包括
保全而无新增、只新增却删除旧项、同 pulse 异 K、瞬时退出容量不变、cofinal 但有平拍。
focused `--trust=0 -DwarningAsError=true` 与原口公理检查通过；承重依赖仅 `propext / Classical.choice / Quot.sound`。
