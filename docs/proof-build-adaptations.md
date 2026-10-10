# 可逆的证明构建适配

研究源码的身份与公开编译使用的证明体分开登记。`export-map.modules` 保留原 `source_sha256`、`source_revision` 与可用 epoch；`proof_body_rewrites` 用唯一完整定理锚点声明原／公开证明体，二者的定理陈述必须逐字相同。`target_sha256` 核对公开模块，`view_sha256` 核对恢复原路径后的适配视图。

`source_view.module_views` 返回公开视图和精确原件。默认原路径视图使用已适配的证明，便于构建；`--exact` 逆转证明适配及资源摘要变换，再核对原源码 SHA。资源、定义或定理陈述的变动不能借证明适配登记。实际 kernel 构建与完整声明审查负责验收适配证明的类型、值和信任闭包。

`build_adaptations` 登记原因、范围、原件／适配源工件及实际 H0 提交，不改变原研究来源。源码闭包摘要包含公开模块字节，因此同一陈述的证明适配仍要求受影响包重新构建和审查；原回执保留为原源码范围的历史事实。

## GSR 稀疏证明

`originalScalarOrbit_code` 先消费原 `originalRho_fast`，再用 `vacuumColumn` 的四个非零位置把 70 项求和化为四项，最后继续 `decide +kernel`。九份副本共享[原源码](source/second-edition/physics/historical/NativeGravityScalarReturn.lean)与[适配源码](source/second-edition/physics/adaptations/NativeGravityScalarReturn.lean)，陈述、前提、定义与编译选项保持。

原源码 SHA 为 `db77bbe6fd166b57969997d13a8da2469718704310b3448f4f69c9cc06d2a4b3`，适配原路径视图 SHA 为 `c42bdf3ae1a427b99cb800fbfaf5b712044b822201b65cec0e9c6d370f5d69b0`。实际适配提交为 `7ece6168f129032b804c9841dddbf616d140e0ba`。

`ci_memory.tsv` 为旧路径和 `ReleaseMaterials` 路径各登记内存键，九份副本均保持单独编译。逐包执行与缓存签收只在[当前验收状态](second-edition-readiness.md)维护。

## 局部实例与私有环境 owner

`local_instance_names` 给匿名局部实例显式、唯一的名称，保持类型、值和证明正文。Jets 或 DiracRay 与 GSR 共同导入时，`NormedAddCommGroup`、`SeminormedAddCommGroup`、`NormedSpace` 三类匿名实例都会产生同名声明，因此三类必须一并命名。DiracRay 六份晚期副本只命名这三类，其余四个局部实例保持原字节；四份已经命名的副本也保持原字节。原路径恢复时精确去除登记的名称。

charged 的 `MixedSpectatorCandidate` 下各模块也会生成同名 `DecidableEq` 等局部实例，必须按真实联合进口一起命名。71e 的十一源／十五实例与 9c73 的九源／十一实例分别登记；后者复用已命名的两份 Yukawa owner，其余不同 namespace 的局部实例保持。命名规则由完整源码逆验及原联合 theorem 消费者核对，不扩大 source epoch 或改变证明预算。

`private_owner_string_rewrites` 将执行中的 `.startsWith` 查询绑定到真实生产模块的完整私有 owner。登记区分带末尾点的 owner 与不带末尾点的 family 前缀；行数、后缀筛选和数学正文保持。只改唯一匹配的执行字符串，注释、与该调用无关的字符串及不匹配的长前缀不能命中。

`SourceMasterCorrectionJointPrice` 先在两分支中绑定 `(owner, namespaceName)`，再按原 member、原 namespace 与唯一候选取常量。相同登记也覆盖这条完整查找链的两个 owner 字符串；namespace、member、单例匹配、定义和预算保持。六份副本恢复同一原源码 SHA `ffe4fe9efc08edfe7493f4dcace742739bb6e37e661694474af004d0aa29dde2`。真实两个生产声明的类型、值和模块身份、完整 canonical 模块及[独立消费者](../evidence/second-edition/acceptance/joint-price-owner-consumer-20261010/result.json)已核对；[应用与逆验](../evidence/second-edition/acceptance/joint-price-owner-application-20261010/result.json)保存逐份规则，正式包验收消费新的公开源码摘要。

`private_owner_expression_rewrites` 将登记的 `Name.str` 私有模块构造恢复到实际完整模块名，保持其后 private counter 与原 namespace/member。`SourceActualThreeParticleCutoffTime` 的 causal／Parseval 两组来自真实 canonical R71 模块，平方可积声明来自 R9 模块；十个实际声明均核对类型、值和模块身份。三条规则不改变数学正文、导入及原 1,200,000 预算，精确恢复原源码 SHA `6fa9a820792b2a8332be92dd4e5cf5704a6b335a760351e16079c559ebf7f71d`。完整 canonical 模块及[三个原陈述消费者](../evidence/second-edition/acceptance/cutoff-time-owner-consumer-20261010/result.json)已通过，[单源应用](../evidence/second-edition/acceptance/cutoff-time-owner-application-20261010/result.json)保存实际规则与逆验。

私有声明的 owner 按实际生产模块绑定。`SourceWholeConfigurationPotential` 的 `source_scale` 定义在 `CanonicalPreparationSourceNativePoleBalance`，同名导入 shim 不拥有该声明。六份副本只校正现有规则的 `target_owner`，原 namespace/member、单例筛选和数学正文保持；完整逆验恢复原源码 SHA `f601c670aec227888ddb99cab320a8f979e1221e613767308142d7b050219ee1`。[真实 owner、完整模块与原陈述消费者](../evidence/second-edition/acceptance/origin-config-owner-consumer-20261010/result.json)及[六源应用](../evidence/second-edition/acceptance/origin-config-owner-application-20261010/result.json)分别保存实际记录。

## Prepared Ward

[prepared_increment_ward](../Lean/H0mework/Versions/R71e/ReleaseMaterials/Physics/LowEnergyPhenomenology/AlphaSource/EmIdentification/PhysicalPreparedCharge.lean) 用局部 `x/y` 保存左右实际 prepared leg，将同一 `increment_ward` 通过内积读口送入，再消费左右本征向量关系与自伴性。这样避免末尾 `simpa` 展开巨大 carrier 和乘积。原定理陈述、前提、定义与预算逐字保持，`proof_body_rewrites` 恢复完整原证明及原 SHA；后续包验收绑定适配后的完整源码范围。

## Pinned pole 点值证明

`sourcePinnedResolvent_boundary` 的非共振分支已进入 `ContinuousLinearMap.ext`。此时先用 `ContinuousLinearMap.add_apply`、`smul_apply`、`zero_apply` 将算子运算送到点值，再消费值空间的 `smul_zero` 与 `zero_add`，避免在整个 `SourceOp` 上搜索标量零实例。

七份副本的完整原源码 SHA 为 `ecdd416e7bf8cff2a7449a0f49e9ad7dae2ada3d8bff7bbacec8d4bd68e824ee`，适配原路径视图 SHA 为 `f47d8897c1a373d8f14fc19b76d3fa3439be1c23acf2441f47f57ba761a80e72`。原陈述、定义、前提、导入、选项及 attributes 逐字保持；两百万总预算与默认实例搜索预算保持。完整 C62 模块及[原陈述独立消费者](../evidence/second-edition/acceptance/pinned-pole-boundary-consumer-20261010/result.json)实际通过，[七源逆验](../evidence/second-edition/acceptance/pinned-pole-boundary-proof-identity-20261010/result.json)保留完整源码比较，原首轮消费者夹具失败另存。
