# 固定母源的单一定理认证

**Certified。** `FixedMotherRealization.root_admission_fixed_mother_complete_realization`
把原根律准入、固定母源的完整形成与原字段／操作恢复收束为一条无外加前提的命名单一定理。
[生产入口](../../../../SaturationMonoid/PhysicsCore/Stage10/SourceUniqueness/Formation/Declarations/Cumulative/FixedMother/CompleteRealization.lean)、
[机器审计](MotherFixedSourceRealization.lean)、[直接消费者](MotherFixedSourceRealizationConsumer.lean)、
[SHA 与认证凭据](MotherFixedSourceRealization.certification.json)。

## 精确结论

| 原量词域 | 同枚材料形成与完整恢复 |
|---|---|
| 任意 Type0 N、V、一般 AuthoritativeRoot 及原 LawfulWorldStateAt | 固定母有限程序像在 Completion 中的闭包；实际 formState 输出、完整世界 Sigma 与原材料左逆；原 occurrence、authority、disposition、patch、整账、next、advance 与 totalReality |
| 任意原 RootInquiryStateAt | 同枚高材料的完整闭包形成与全部父材料左逆；完整原世界／Clause、compile，以及每个合法 exact event 的完整编译 |
| 任意完整原 SourceNativeInquiryEngineProcess | 同枚高材料、实际 formProcess 与忠实限制；完整 State/stateAt/initial/successorAt、全部 compile、已有 sealed ask、完整 law、tick 及所有有限历史 |

量词直接使用原物理接口；rank、材料与 formation 都位于结论。`Origin` 的既有完整覆盖由已认证生产链生成，
没有将地址、表示、branch coverage 或 realization 作为新准入条件。完整过程相等保留所有状态与操作。

## 固定母与实际工厂

`MotherFamilyOccurrence.MotherRoot` 定义性等于原 `SpinPair.livingRoot` 的账本根。
低／高 `Programme` 均含这同一根的真实 `MotherVisit`；`lowProgramme_read` 和
`highProgramme_read` 精确还原原 `MotherPointwiseLaws.finiteLaw` 的实际求值。
`Raw` 是该求值器的像，`Material` 是其 Completion；`low_formation`／`high_formation`
由原嵌入的 dense range 证明每枚完整材料都在有限程序像闭包中。

总定理把此 formation 赋予三个既有 source producer 生成的**同枚材料**。
世界的原 `formTheory.get → restrictHeader → formState.get`、完整 inquiry 的实际 Clause 工厂、
宏过程的完整节点／successor 工厂均直接复用；所有父材料空间保持原左逆。
程序嵌入是实际求值的载体，read 定理是求值读出，两个 formation 定理提供完整来源结论；
三个 Prop record 汇合已生成字段，总定理完成统一的来源及消费者合同。

这是已签收来源链的单一定理收束；原固定 root、visit10、whole-ledger 与 generated next 未改变。
原 activation law 和 runtime 作为既有完整对象消费、运输。

## 机器证据

候选两文件及对应生产两文件均以 Lean 4.33.0、`--trust=0 -DwarningAsError=true` 新鲜窄编译。
迁移仅重定位一条 import；Formation 文件逐字不变。

- **64** 个新增声明：完整 type/value、level 结构、recursor 规则、声明元数据、owner 与依赖边逐项对应。
- 数学可信闭包：**82,345** 个声明、**2,459,064** 条完整元数据依赖边；仅 `propext`、
  `Classical.choice`、`Quot.sound`，无 unsafe 或可信 partial；新实例与 codegen-only 项均为零。
- **82,281** 个共享节点在两环境读取同一生产模块／olean；原 329 模块逐源码 SHA 与 olean SHA 保持不变。
  共享 owner 的 3,097 个实际导入 olean 另有精确 SHA 绑定，复用旧签收而不要求已退役 scratch 重新存在。
- **5** 个直接消费者的证明项均调用单一新 theorem mouth，并机器拒绝绕回旧 source 总口：
  三个任意原域、原物理 sealed ask／完整 law，以及完整 SameOccurrenceActivation 与 tick16→17／全部有限历史。
  消费者可信闭包为 **82,768** 个声明、**2,469,334** 条边，同样仅标准三公理。
- 生产导入无 scratch；宇宙正例与 Sort／Const 的 successor 反例控制通过；`git diff --check` 通过。

本轮只认证、迁移这两文件和直接消费者，旧生产证明、原框架与既有完整控制保持原范围。
