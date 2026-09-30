# 原计数后继的信息损失与恢复

本卡承接[完整计数观察](source-counted-observation.md)与
[信息层合同](../../../../../../paperwork/Maybework/信息没有裸奔权：occurrence面账本与信息论重审备忘录.md)。
当前责任只见[maximum active](../../../handoffs/no-island-no-magic-mathematics-active-route.md)。

原 `fineTable = CountedObservation.run` 保留全部 count/H/mass/clock 与源残差。
实际 `mergeTable fineTable forgetClock` 按源计数权重合并，再由原 receipt 执行
`nextCoarseTable = CountedObservation.step ...`。`CountedAdvance.step_model_commutes`
和 `CountedMerge.continued_next_model` 把这份表的 `CountedPosterior.model` 认回原
动态 posterior；原完整 clock 恢复误差为零，既有 `MergeLoss.loss` 遂给出

```text
原 G 读者对 nextCoarseTable posterior 的加权平方恢复误差
  = MergeLoss.gap (advanced.tick.next) clockRead forgetClock。
```

原 nonunit index 与实际库存增长生成 actor 0、2：两者同 parity、不同完整 clock。
因此同一次后继的上述误差严格为正，既有 `InformationLoss.amount` 也严格为正；
完整 clock 的恒等观察则有零 gap。这首次排除“parity 粗表可免费恢复原 G”的压缩。
原 parity Field 的 fine/coarse 投影可以相同；这不消去完整 G 的区别或原混合残差。
旧 `CountedMerge.continued_next_field` 与新式在同 root/next 并列消费，旧 Field 证明
本身不依赖新式。

新值只在 root `calculationNormal` 生成后进入 `NativeModelStep.ObservationAt`：
该口固定 normal target current，材料 `generate (current.advance steps)` 的
`factorizes` 认回同 occurrence 的 whole-ledger，原 `CopyObservation.current_consumed`
再接收正损失。源 `CountedObservation.StageLaw` 与 `Calculation.sourceFrontier`
保持原样；目标正值不作源输入。原 `runtimeAt 3`、exact samples、可达预算对任意步实例化。

权威源码：`Conditional/CountedMerge/Information.lean`、
`Copy/Graph/NativeModelStep/Observation.lean`；验证：
`Verification/no-island/counted-observation/{Reachability,InformationNext,Gate}.lean`。
