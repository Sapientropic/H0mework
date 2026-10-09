# 查询与计算 reader 的环境合同

`SourceDatum.reader` 保留完整查询；`calculationReader` 可提供同发生的独立计算词。`SourceGeneratedInquiryReceiptAction.actionReader` 通过 `Option.getD` 选择实际计算读口。二者的 expression 与费用可以不同，环境对齐必须由生成源支付。

泛型 `Factory` 允许任意 `SourceDatum`，因此不能从查询费用或 `Paid` 推出计算 reader 与查询 reader 的环境相同。历史 `packet_decoder_paid` 的无条件 `rfl` 原源码独立保留；H0 补充的泛型消费者明确接收下面的输入源责任：

```text
对每个 n、seed、frame 和原 occurrence：
actionReader(frame, cfg, occurrence).environment
  = datum(frame, cfg).reader(occurrence).environment
```

实际 `Foresight.Contextual.factory` 使用 `Incoming.calculationReader`：没有 incoming tree 时沿用原 reader；有 tree 时保留原 environment，只把 incoming event expression 加到原 expression。`factory_action_environment` 从这两个构造分支直接生成上述等式。

有限 `Indexed.Installation.configuration` 也消费同一 `Incoming` 构造。这个定义修正把原先的 `calculationReader = none` 接到实际 `frame.pairInventory`；在 Some 分支，原 reader 加上同一库存根事件的 expression，实际 result、material 和费用随之使用这个计算词。`Incoming` 只读取 `datum.reader`，因此实际工厂再次设置该字段不会重复添加 expression。原查询 reader、decoder、环境和两份库存保持；这项修正由独立补充来源登记，原定义另存。

这个 producer 进入 `Generated.packet_decoder_paid` 和 `generic_native_environment`，随后由 `native_environment`、`ActiveClaim.Environment.decoder_active` 与 `Erasure.actual_after_environment` 消费。实际消费者的原定理声明及前提保持，环境责任没有成为最终实际入口的新 premise；它也不要求两个 reader 的完整 raw 或 expression 相等。

另一个实际机制是 residual request 的两枚 AST 节点费用。原 `Native.ResidualRequest.budget` 与 `firstStep` 的一次扣费共同推出 receiver 仍有正费用，`PaidSource` 因而不必借查询费用来假定计算费用。这是原 receiver 的付费事实，AST 费用不承担物理单位解释。

权威源码保留在 [补充源](source/second-edition/core/supplements/ContextualFactory-c62f3d25.lean)、[泛型输入合同](source/second-edition/core/supplements/GeneratedEnvironment-c62f3d25.lean) 与 [实际 receiver 证明](source/second-edition/core/supplements/EffectInstalled-c62f3d25.lean)。实际 H0 来源分别为 `06fe5ede76de8954633cdae179feafd9e482b359` 和 `4c2f8c5ccb1c2601849b5f414410625c7d36c6b5`，原 C62 来源、失败字节及变换由 [第二版映射](second-edition-map.json) 登记。实时验收只在 [材料状态](second-edition-readiness.md) 维护。

有限配置的 [实际计算接线](source/second-edition/core/supplements/FiniteCalculationInstallation-c62f3d25.lean) 与 [Incoming 定义](source/second-edition/core/supplements/FiniteIncoming-c62f3d25.lean) 来源为 `e6908c97bb87417071dcefc4edcf4c6793517e56`；原 `none` 构造独立保留在 [历史源](source/second-edition/core/historical/FiniteCalculationInstallation-c62f3d25.lean)。
