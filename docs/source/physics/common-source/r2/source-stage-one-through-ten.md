# Stage 1–10：同源物理成果贯通

> 全阶段成果与消费关系的稳定入口。实时状态只见 [Physics active route](../../handoffs/physics-cauchy-safe-active-route.md)。
> 最终贯通口：[Recovery/Consumer.lean](../../../SaturationMonoid/PhysicsCore/Stage10/Recovery/Consumer.lean)。
> 分阶段历史记录见 [物理交接目录](../../handoffs/physics/README.md)。
> 本页按实际证明对象区分生成、继承与历史合同；阶段编号不要求已退役接口重新进入生产依赖。

## 先确定成果的层次

Stage1–10 是面向现实物理的同源统一理论构造：几何、规范、物质、连续经典场、量子行为及预测
按各自已证合同由共同源生成并接入同一发生。`Recovery` 是其最后的总消费与忠实恢复接口；
该接口的 readout 分类不改变它实际消费的上游物理 producer 的构造性质。

这条已闭合生成链不以弦世界面、弦振动谱、弦紧致化或景观选态为输入。
它在各自已证统一合同内的依赖独立性，应作为正向成果进入理论比较；
相关前提必要性与唯一性论证的责任对照见[同源统一与弦论基础前提](../../research/physics/string-foundations.md)。

理解“fixed source”和“闭合”时，先读[根读恒等](../framework/authority/same-occurrence-inquiry-answer.md)
与[根法的领域实现](../framework/authority/root-law-dependent-face-realization.md)。这里固定的是 source、
law epoch、actual occurrence 与历史身份；不能仅凭 fixed 一词把成果解释为任意虚构宇宙，
也不能把未来尚未生成或某个 observer 尚未恢复的信息，反向变成已证场关系的不确定性。
根律的[全称刚性与后继生成](../framework/authority/same-occurrence-inquiry-answer.md#全称刚性不靠场景枚举)
由统一定理覆盖，不以穷举极端物理场景为前提；具体领域读出按同一命题身份消费它。
原宏观进程的 [`allMacroNext`](../../../SaturationMonoid/PhysicsCore/Stage10/Runtime/Activation.lean)
也量化任意 `index : ℕ`；有限拍回放不是该定理的量化上限。

| 完成项 | 已经支付的结构责任 | 权威详述 |
| --- | --- | --- |
| S9-CU 唯一性锁 | 原完整源历史的全部合法弱聚点值唯一，并忠实恢复同一九字段 actual | [CU 机制](source-history-weak-actual-uniqueness.md) |
| Stage10 零未登记权威锁 | 全部实际作用输入与已安装输出归根，完整 writer、整账与原生 next 同发生 | [Stage10 封印](source-stage-ten-physical-seal.md) |
| Stage1–10 总贯通 | 早期生成结构、当前完整场与真实后继由同一总消费者取得并精确相容 | 本页及 `Recovery/Consumer.lean` |

## 先读整条链

当前贯通对象为 `Stage10.Recovery.stageOneThroughTenClosure`，
独立总消费为 `Stage10.Recovery.stageOneThroughTenClosed`。

```text
同一原生 root occurrence
├─ 已安装的 source 读出
│  └─ 原 Stage8 raw source
│     ├─ Stage4 几何与有限作用量
│     ├─ Stage5 不可分引力—规范耦合
│     ├─ Stage6 单一 SU7 母连接
│     ├─ Stage7 实际表示、荷、手征、反常及限定的一圈读出
│     └─ Stage8 同一标量的质量/混合、同源物质态与电流
└─ 已安装的 configuration / quantum 读出
   └─ Stage9 同源连续场、现行作用量、唯一 actual、量子与相容
      └─ Stage10 原发生、全输入、整账、独立预测与原生 next

共同标量 / 质量 / 混合 / 内部表示作用
    = 当前 actual 的对应读出
    = 下一发生的对应读出
```

源数据与当前场分别来自原 runtime 的 `sourceFace.rootRead` 和
`classicalFace.rootRead`。贯通口同时消费既有 Stage10 封印及其
`SameOccurrenceActivation`；它是同根成果的总消费与恢复，不新增物理作用或 runtime。

## 阶段成果怎样进入总图

| 阶段 | 已证明的成果 | 在贯通链中的位置 |
|---|---|---|
| 1 | 原 constitutive gate 的空真反例明确了“schema 可居住”不足以生成物理的条件 | [合同形成与反例](../../../SaturationMonoid/PhysicsCore/ConstitutiveHardGateVacuityBoundary.lean)，保持诊断角色 |
| 2 | 同源 metric/Hodge 的类型化相容、四种变分责任与明确的 constitutive 接口 | [接口合同](../../../SaturationMonoid/PhysicsCore/SourceConstitutiveHardGateAdapter.lean)，由后续具体构造兑现，旧 adapter 不获得新 authority |
| 3 | internal/geometry 双轴的忠实联合投影、由坐标势生成几何、源信息不足的精确诊断 | [双轴 producer](../../../SaturationMonoid/PhysicsCore/SU7AdmittedRicherDualAxisCredential.lean)与其 imports；保留各自 source 范围，后续无需重走旧 thin-source gate |
| 4 | 同源非退化几何、物理 II+、有限统一作用量与真实变分 | `Recovery.stageSix.stageFive.stageFour`，由[原 Stage8 source](../../../SaturationMonoid/PhysicsCore/StageEightProofFreeSource.lean)生成 |
| 5 | 共享动态几何、不可加法分离的引力—规范作用、非零 stress 与 source-relative 驻点 | `Recovery.stageSix.stageFive`；[不可分性定理](../../../SaturationMonoid/PhysicsCore/NonseparableSourceCoframeRegression.lean)保留有限作用量范围 |
| 6 | 单一 SU7 母连接、非阿贝尔曲率、方程选出的 P286 子结构、母作用与严格限制 | `Recovery.stageSix`；[选择方程的双向刻画](../../../SaturationMonoid/PhysicsCore/SU7MotherLieAlgebra.lean)及源生成母 credential |
| 7 | 63 分量外幂表示的实际权重、手征、反常抵消与一圈系数读出 | `Recovery.stageEight.stageSeven`；[完整计算 receipt](../../../SaturationMonoid/PhysicsCore/SU7ExteriorMatterAnomalyRunning.lean)，由总消费者显式取得 |
| 8 | 完整原源 lineage、同源 matter jet/非零 current、同一标量的 Yukawa 质量与有限混合 | `Recovery.stageEight`；[原联合 producer](../../../SaturationMonoid/PhysicsCore/SU7GravityGaugeMatterJointCredential.lean)整体被携带 |
| 9 | 源几何、现行 form-native 作用、完整经典 actual 与弱唯一性、量子生成及经典—量子交换 | `stageOneThroughTenClosure.final.stageNine`；[Stage9 总机制](source-stage-nine-unified-credential.md) |
| 10 | 原生事件登记、全场反向恢复、整账、同 law 的 next、独立五点 observable | `stageOneThroughTenClosure.final`；[原固定源封印](source-stage-ten-physical-seal.md) |

Stage1–3 的诊断与通用数学帮助确定了后续构造的合法责任。它们在全图中有明确位置，
无需把已退役 schema 再包装成物理 producer。Stage4–8 的旧 source projection 与
Stage9 的当前 actual 则同时保留，并通过已证明的共同读出相接。

## Recovery 这一步新增了什么

[Source.lean](../../../SaturationMonoid/PhysicsCore/Stage10/Recovery/Source.lean)
从 Stage10 当前发生已经安装的源投影读取 `Runtime.source.stageEight`，恢复原
`canonicalPhysicalStageSix` 和 `canonicalStageEightGravityGaugeMatterCredential`。
后者已经携带 Stage7 计算结果，以及 Stage8 的同配置质量、混合和非零电流。

[Matter.lean](../../../SaturationMonoid/PhysicsCore/Stage10/Recovery/Matter.lean)
用 `MatterRecovery` 同时支付四条准确关系：

- 早期内部表示实际作用于当前完整 Dirac matter 的每个 spin 分量；
- 当前 scalar 的外幂读出等于早期 joint scalar；
- 当前完整 Yukawa mass map 等于早期 generated mass map；
- 当前有限 mixing matrix 等于早期 generated mixing。

[Consumer.lean](../../../SaturationMonoid/PhysicsCore/Stage10/Recovery/Consumer.lean)
把这些等式同时交付给当前 configuration 和原生后继，并消费原 Stage10
activation 与 prediction lock。早期结果进入可调用的总输出，读者不必从长 import 链猜测
哪些成果仍然有效。

## 相同部分与各自范围

同一 source 可以生成多个不同的数学读出。旧有限 matter jet、背景 connection、
source-relative action 与当前 SpinPair 场保留各自对象；共同的 scalar、mass、
mixing 和表示作用以精确等式接回。当前方程仍由现行 Dirac-dual form-native action
及完整 CWA 支付。后续连续理论已完成的责任，以 Stage9 当前总对象为准。

Stage7 的原一圈表使用其明确的 exterior Weyl carrier 与空 scalar inventory。
它作为这项既有计算完整保留；当前加入动态标量后的全理论 beta 系数需要相应的
完整物质清单。63 分量谱与有限两维 mixing 的适用范围也随原 receipt 保留。

## 最小性、源与经验怎样定位

[二点补结构初始性](../../../SaturationMonoid/ComplementObservationCarrierInitiality.lean)
与[构造性最小载体](../../../SaturationMonoid/ComplementObservationCarrierKernel.lean)
给出最小登记结构的地基；原 root 中已发生对象的正向结构归属见
[总体实在机制](../framework/ontology/total-reality-structural-identity.md)。
[SourceAnchor 接口](../../../SaturationMonoid/SourceAnchorConservationKernel.lean)
提供登记读出；它们不是 Physics Stage1，也没有被用作选出当前全部物理源数据的定理。

原生成器的数据接口是 `StageEightProofFreeSource.Source` 加
`SmoothUnifiedSource.continuousContactResidual`。这些字段的后续形成也已有实际 producer：
[源材料形成](source-material-formation.md)覆盖完整离散材料、原母势的全部实操作数像，
并对任意 `SmoothUnifiedSource` 生成完整九场 Euler 与同源量子响应；
[自主路径](source-physical-path-generation.md)在同一持续母史中形成并执行全部有限离散材料／
有理坐标程序；
[声明形成](source-declaration-formation.md)将一枚共同 law 接到全部原 source/state/center 的
writer、整账和 native next。各项的量词、物理作用与母史身份由对应机制卡详述。
评价源的选择自由度时，应同时计入这些形成链及本页的物理生成关系。

数学结构对仪器的映射及真实数据裁决，沿[分层 prediction lock](../../../../Verification/physics/stage10/prediction-lock/README.md)
进入独立经验通道。已生成的物理关系不重新统计为附加假设；经验接触的输入、读出身份与校准则按
实际协议核验。出现差异时定位其具体生成／投影责任，保留原结果，不以泛泛怀疑重开 CU，
也不以根读唯一性预先判实验错误。新增贯通口保留原物理源、作用、预测律和冻结版本。

## 使用与验收

- 了解整体成果：先读本页，再进入总消费者与所需阶段。
- 继续物理工作：回到唯一 active route，沿当前 exact occurrence 施工。
- 查旧 handoff：按其原 source/action 范围读取，后续已关闭责任以总图与当前源码为准。
- 独立验证：[贯通审计](../../audits/physics/stage1-10/README.md)。
- 按需研究极端场景：[普朗克尺度、黑洞与奇点的证明复用清单](../../research/physics/extreme-regimes.md)，不追加本链的验收项。
- 启动质量隙研究：[杨–米尔斯平坦重构与 Clay 终端合同](../../research/physics/yang-mills-launch.md)。

```bash
cd Lean
lake env lean --trust=0 -DwarningAsError=true SaturationMonoid/PhysicsCore/Stage10/Recovery/Consumer.lean
python3 scripts/living_law_runtime.py --module SaturationMonoid.PhysicsCore.Stage10.Recovery.Consumer --inquiry-runtime SaturationMonoid.PhysicsCore.Stage9C.Revision.physicalInquiryRuntime --fuel 19
```
