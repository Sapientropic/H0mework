# 证据对应表

本表将各稿主张连接到固定源码、程序和回执。执行命令见[复现指南](reproduction.md)，来源文档的角色与阅读方式见[来源材料索引](source-materials.md)。

## 来源与地址变换

源仓、完整提交与逐文件身份以 [`export-map.json`](../tools/export-map.json) 的 `source_repository`、`revisions`、`modules` 和 `artifacts` 为准。下表说明各标签对应的选集条目：

| 标签 | 选集条目 |
| --- | --- |
| base | 三篇原始稿（LifecycleRegression 修复提交，S 的直接后继） |
| H | source-process-core-supplement、native-flow、observation-dynamics |
| F | physics-common-source-f（Bell 补充） |
| T | low-energy-loop-response（Case 2）、constrained-local-quantum-t |
| T2 | constrained-local-quantum-t2 |
| T3 | constrained-local-quantum-t3 |
| V | constrained-local-quantum-v |
| X | physics-common-source-x、native-flow-x、observation-dynamics-x、constrained-local-quantum-x |
| Y | whole-ledger-accounting |
| Y1 | whole-ledger-accounting-y1（Y 的直接后继，一处 `rfl` 战术修复） |
| K15 | constrained-local-quantum-k15 |
| K16 | constrained-local-quantum-k16 |
| K17 | constrained-local-quantum-k17 |
| R2 | source-process-core-r2、physics-common-source-r2 |
| E | observation-dynamics-e |
| I | observation-dynamics-i |

同一源路径在不同修订处字节一致则共享一条导出记录，`source_revisions` 登记适用修订；不同字节版本保存在 `H0mework.Versions.<标签>.*` 命名空间。

迁移改写本地 `import` 地址、`resource_rewrites` 登记的 `include_str` 地址及 `resource_sha256_rewrites` 登记的资源摘要。声明名、命名空间、前提、量词和其余正文保持源字节。回执的原件／公开副本身份及字节合同见[公开回执与原始来源](evidence-publication.md)。

[`source_view.py`](../tools/source_view.py) 的 `verify_all` 核对模块的原始来源、工件的公开字节及 payload 身份。`make check-map` 输出模块、工件和派生回执的计数；原件对照通过精确模式运行。base 来源包含 LifecycleRegression 的纯战术修复，替代原 S 来源中不适配固定 mathlib 的 `simpa` 脚本，命题保持不变。

## 论文与入口

| 论文 | 来源标签 | 选集条目 |
| --- | --- | --- |
| source-process-core（过程核心） | R2；首版 base/H | `source-process-core-r2`；首版 `source-process-core{,-supplement}` |
| physics-common-source（同源物理） | R2；首版 base/F | `physics-common-source-r2`；首版 `physics-common-source{,-f}` |
| low-energy-phenomenology（低能唯象） | base | `low-energy-phenomenology`（L1–L17 及复现程序） |
| whole-ledger-accounting（整账会计） | Y/Y1 | `whole-ledger-accounting{,-y1}` |
| observation-dynamics（动态观察） | H/E/I/X | `observation-dynamics{,-e,-i,-x}` |
| low-energy-loop-response（Case 2） | T | `low-energy-loop-response` |
| native-flow（原生长河） | H/X | `native-flow{,-x}` |
| constrained-local-quantum（Case 5A） | T/T2/T3/V/X/K15/K16/K17 | `constrained-local-quantum-{t,t2,t3,v,x,k15,k16,k17}` |
| Bell 独立裁决（同源物理补充） | F/X | `physics-common-source-{f,x}` |

### R2 修订选集

两篇修订选集使用导出映射中 `revisions.R2` 的固定源码，入口分别为 [SourceProcessCoreR2](../Lean/H0mework/Papers/SourceProcessCoreR2.lean) 和 [PhysicsCommonSourceR2](../Lean/H0mework/Papers/PhysicsCommonSourceR2.lean)。过程核心纳入完整源树作用、独立树恢复、依赖输入与原收费 runtime 的消费者；同源物理纳入当前 Stage1–10 总消费、完整母源形成及同源作用的物理安装。各入口的 import 指定实际版本，逐文件身份以导出映射为准。

原论文标签及 base/H/F 等冻结链保持各自版本。下表保存首版命题编号到生产口和直接消费者的对应；Lean 声明的类型给出前提与量词。模块路径均相对于 `Lean/H0mework/`。

### source-process-core（C1–C13）

| 命题 | 本仓模块（producer／consumer） |
| --- | --- |
| C1 | [`Foundation/Responsibility/Lifecycle`](../Lean/H0mework/Foundation/Responsibility/Lifecycle.lean)、[`Foundation/Responsibility/LifecycleRegression`](../Lean/H0mework/Foundation/Responsibility/LifecycleRegression.lean) |
| C2 | [`Foundation/Responsibility/NoetherianClosure`](../Lean/H0mework/Foundation/Responsibility/NoetherianClosure.lean)、[`Foundation/Responsibility/NoetherianClosureRegression`](../Lean/H0mework/Foundation/Responsibility/NoetherianClosureRegression.lean) |
| C3 | [`Foundation/Runtime/AnswerHistory`](../Lean/H0mework/Foundation/Runtime/AnswerHistory.lean)、[`Foundation/Semantics/RootReality`](../Lean/H0mework/Foundation/Semantics/RootReality.lean) |
| C4 | [`Foundation/Runtime/Inquiry`](../Lean/H0mework/Foundation/Runtime/Inquiry.lean)、[`Checks/Runtime/Inquiry`](../Lean/H0mework/Checks/Runtime/Inquiry.lean) |
| C5 | [`Checks/Runtime/Inquiry`](../Lean/H0mework/Checks/Runtime/Inquiry.lean)、[`Checks/Runtime/U8Completion`](../Lean/H0mework/Checks/Runtime/U8Completion.lean) |
| C6 | [`Checks/Runtime/Inquiry`](../Lean/H0mework/Checks/Runtime/Inquiry.lean) |
| C7 | [`Realization/Operations/DerivationReduction`](../Lean/H0mework/Realization/Operations/DerivationReduction.lean)、[`Realization/Operations/Effects`](../Lean/H0mework/Realization/Operations/Effects.lean)、[`Realization/Operations/MixedTrace`](../Lean/H0mework/Realization/Operations/MixedTrace.lean)、[`Checks/Realization/OperationDerivations`](../Lean/H0mework/Checks/Realization/OperationDerivations.lean)、[`Fock/Cofinal/OperationDerivation`](../Lean/H0mework/Fock/Cofinal/OperationDerivation.lean) |
| C8 | [`Checks/Realization/QuantifiedUpdate`](../Lean/H0mework/Checks/Realization/QuantifiedUpdate.lean)、[`Realization/Operations/RuntimeEvolution`](../Lean/H0mework/Realization/Operations/RuntimeEvolution.lean)、[`Realization/Operations/RuntimeRelations`](../Lean/H0mework/Realization/Operations/RuntimeRelations.lean)、[`Realization/Operations/RuntimeSuccessor`](../Lean/H0mework/Realization/Operations/RuntimeSuccessor.lean)、[`Realization/Operations/ScalarExact`](../Lean/H0mework/Realization/Operations/ScalarExact.lean)、[`Realization/Operations/ScalarPresentation`](../Lean/H0mework/Realization/Operations/ScalarPresentation.lean)、[`Fock/Cofinal/DynamicsWitness`](../Lean/H0mework/Fock/Cofinal/DynamicsWitness.lean)、[`Fock/Cofinal/OperationPrefix`](../Lean/H0mework/Fock/Cofinal/OperationPrefix.lean) |
| C9 | [`Realization/Operations/BinaryInputs`](../Lean/H0mework/Realization/Operations/BinaryInputs.lean)、[`Realization/Operations/NativeState`](../Lean/H0mework/Realization/Operations/NativeState.lean)、[`Realization/Operations/FieldInputs`](../Lean/H0mework/Realization/Operations/FieldInputs.lean)、[`Checks/Realization/NativeBinary`](../Lean/H0mework/Checks/Realization/NativeBinary.lean)、[`Checks/Realization/NativeSource`](../Lean/H0mework/Checks/Realization/NativeSource.lean)、[`Checks/Realization/NativeUnitWrite`](../Lean/H0mework/Checks/Realization/NativeUnitWrite.lean)、[`Arithmetic/UnitArithmetic/Root`](../Lean/H0mework/Arithmetic/UnitArithmetic/Root.lean)、[`Fock/Cofinal/OperationNative`](../Lean/H0mework/Fock/Cofinal/OperationNative.lean) |
| C10 | [`Foundation/Semantics/CausalRealization`](../Lean/H0mework/Foundation/Semantics/CausalRealization.lean)、[`Realization/SourceComparison/GroundedRealization`](../Lean/H0mework/Realization/SourceComparison/GroundedRealization.lean)、[`Physics/MotherDescription/Consumer`](../Lean/H0mework/Physics/MotherDescription/Consumer.lean)、[`Physics/MotherSource/GroundedRealization`](../Lean/H0mework/Physics/MotherSource/GroundedRealization.lean) |
| C11 | [`Realization/JointEffect/PassiveController`](../Lean/H0mework/Realization/JointEffect/PassiveController.lean)、[`Realization/JointEffect/AuditTransition`](../Lean/H0mework/Realization/JointEffect/AuditTransition.lean)、[`Realization/JointEffect/AuditTransitionRegression`](../Lean/H0mework/Realization/JointEffect/AuditTransitionRegression.lean)、[`Realization/JointEffect/Residual`](../Lean/H0mework/Realization/JointEffect/Residual.lean)、[`Realization/Audit/U7Coface`](../Lean/H0mework/Realization/Audit/U7Coface.lean)、[`Foundation/Inquiry/ResidualCoface`](../Lean/H0mework/Foundation/Inquiry/ResidualCoface.lean) |
| C12 | [`Foundation/Responsibility/DebtCompiler`](../Lean/H0mework/Foundation/Responsibility/DebtCompiler.lean)、[`Foundation/Responsibility/DebtWorld`](../Lean/H0mework/Foundation/Responsibility/DebtWorld.lean)、[`Foundation/Responsibility/DebtWorldReadback`](../Lean/H0mework/Foundation/Responsibility/DebtWorldReadback.lean)、[`Arithmetic/FockResponsibility/DirectResponsibility`](../Lean/H0mework/Arithmetic/FockResponsibility/DirectResponsibility.lean)、[`Arithmetic/FockResponsibility/TargetSixActionDebt`](../Lean/H0mework/Arithmetic/FockResponsibility/TargetSixActionDebt.lean) |
| C13 | [`Checks/Runtime/Inquiry`](../Lean/H0mework/Checks/Runtime/Inquiry.lean)、[`Foundation/Inquiry/MinimalCoface`](../Lean/H0mework/Foundation/Inquiry/MinimalCoface.lean)、[`Foundation/Inquiry/SemanticRevision`](../Lean/H0mework/Foundation/Inquiry/SemanticRevision.lean)、[`Foundation/Inquiry/RevisionRecovery`](../Lean/H0mework/Foundation/Inquiry/RevisionRecovery.lean)、[`Arithmetic/FockResponsibility/DebtU7LivingRoot`](../Lean/H0mework/Arithmetic/FockResponsibility/DebtU7LivingRoot.lean) |
| 来源表／回执 | [`Physics/MotherDeclarationsNative/PhysicalQueryConsumption`](../Lean/H0mework/Physics/MotherDeclarationsNative/PhysicalQueryConsumption.lean)、[`Physics/MotherDeclarationsNative/PhysicalQueryInquiry`](../Lean/H0mework/Physics/MotherDeclarationsNative/PhysicalQueryInquiry.lean) |

### physics-common-source（P1–P20）

| 命题 | 本仓模块（producer／consumer） |
| --- | --- |
| P1 | [`Physics/RootRuntime/RecoveryConsumer`](../Lean/H0mework/Physics/RootRuntime/RecoveryConsumer.lean)、[`Physics/RootRuntime/RecoverySource`](../Lean/H0mework/Physics/RootRuntime/RecoverySource.lean)、[`Physics/RootRuntime/RuntimeConsumer`](../Lean/H0mework/Physics/RootRuntime/RuntimeConsumer.lean) |
| P2 | [`Physics/Actual/WeakCandidate`](../Lean/H0mework/Physics/Actual/WeakCandidate.lean)、[`Physics/QuantumFoundation/Classical`](../Lean/H0mework/Physics/QuantumFoundation/Classical.lean)、[`Physics/QuantumFoundation/FoundationAcceptance`](../Lean/H0mework/Physics/QuantumFoundation/FoundationAcceptance.lean)、[`Physics/QuantumFoundation/RuntimeConsumer`](../Lean/H0mework/Physics/QuantumFoundation/RuntimeConsumer.lean)、[`Physics/Geometry/CClassicalAcceptance`](../Lean/H0mework/Physics/Geometry/CClassicalAcceptance.lean) |
| P3 | [`Physics/Matter/SU7ExteriorMatterAnomalyRunning`](../Lean/H0mework/Physics/Matter/SU7ExteriorMatterAnomalyRunning.lean)、[`Physics/Matter/SU7GravityGaugeMatterJointCredential`](../Lean/H0mework/Physics/Matter/SU7GravityGaugeMatterJointCredential.lean)、[`Physics/RootRuntime/RecoveryConsumer`](../Lean/H0mework/Physics/RootRuntime/RecoveryConsumer.lean)、[`Physics/RootRuntime/RecoveryMatter`](../Lean/H0mework/Physics/RootRuntime/RecoveryMatter.lean) |
| P4 | [`Physics/MotherDescription/Consumer`](../Lean/H0mework/Physics/MotherDescription/Consumer.lean)、[`Physics/MotherSource/GroundedRealization`](../Lean/H0mework/Physics/MotherSource/GroundedRealization.lean)、[`Physics/QuantumCompatibility/DualResponse`](../Lean/H0mework/Physics/QuantumCompatibility/DualResponse.lean)、[`Physics/QuantumFoundation/Credential`](../Lean/H0mework/Physics/QuantumFoundation/Credential.lean) |
| P5 | [`Physics/QuantumCompatibility/Acceptance`](../Lean/H0mework/Physics/QuantumCompatibility/Acceptance.lean)、[`Physics/QuantumCompatibility/Stress`](../Lean/H0mework/Physics/QuantumCompatibility/Stress.lean)、[`Physics/QuantumFoundation/Credential`](../Lean/H0mework/Physics/QuantumFoundation/Credential.lean)、[`Physics/QuantumFoundation/RuntimeConsumer`](../Lean/H0mework/Physics/QuantumFoundation/RuntimeConsumer.lean) |
| P6 | [`Realization/SourceComparison/GroundedRealization`](../Lean/H0mework/Realization/SourceComparison/GroundedRealization.lean)、[`Physics/MotherDescription/Consumer`](../Lean/H0mework/Physics/MotherDescription/Consumer.lean)、[`Physics/MotherSource/GroundedRealization`](../Lean/H0mework/Physics/MotherSource/GroundedRealization.lean) |
| P7 | [`Physics/GlobalOrbit/Acceptance`](../Lean/H0mework/Physics/GlobalOrbit/Acceptance.lean)、[`Physics/GlobalOrbit/Observable`](../Lean/H0mework/Physics/GlobalOrbit/Observable.lean) |
| P8 | [`Physics/Bell/Preparation`](../Lean/H0mework/Physics/Bell/Preparation.lean)、[`Physics/Bell/Runtime`](../Lean/H0mework/Physics/Bell/Runtime.lean)、[`Physics/EmpiricalContact/Consumer`](../Lean/H0mework/Physics/EmpiricalContact/Consumer.lean) |
| P9 | [`Physics/MotherDeclarationsAll/SourceOriginConsumer`](../Lean/H0mework/Physics/MotherDeclarationsAll/SourceOriginConsumer.lean)、[`Physics/MotherDeclarationsAll/SourceOriginOperations`](../Lean/H0mework/Physics/MotherDeclarationsAll/SourceOriginOperations.lean)、[`Physics/MotherLaws/JointSourceConsumer`](../Lean/H0mework/Physics/MotherLaws/JointSourceConsumer.lean) |
| P10 | [`Physics/SourceFormation/Acceptance`](../Lean/H0mework/Physics/SourceFormation/Acceptance.lean)、[`Physics/SourceFormation/Consumer`](../Lean/H0mework/Physics/SourceFormation/Consumer.lean)、[`Physics/SourceFormation/EvolutionConsumer`](../Lean/H0mework/Physics/SourceFormation/EvolutionConsumer.lean) |
| P11 | [`Physics/MotherProgrammesFormationPaths/Consumer`](../Lean/H0mework/Physics/MotherProgrammesFormationPaths/Consumer.lean)、[`Physics/MotherProgrammesFormationPaths/Late`](../Lean/H0mework/Physics/MotherProgrammesFormationPaths/Late.lean)、[`Physics/MotherProgrammesFormationPaths/Steps`](../Lean/H0mework/Physics/MotherProgrammesFormationPaths/Steps.lean)、[`Physics/MotherProgrammesFormationProgrammes/AutonomousConsumer`](../Lean/H0mework/Physics/MotherProgrammesFormationProgrammes/AutonomousConsumer.lean)、[`Physics/MotherProgrammesFormationProgrammes/AutonomousCoverage`](../Lean/H0mework/Physics/MotherProgrammesFormationProgrammes/AutonomousCoverage.lean) |
| P12 | [`Physics/YangMillsSourceQuantum/JetEnergy`](../Lean/H0mework/Physics/YangMillsSourceQuantum/JetEnergy.lean)、[`Physics/YangMillsSourceQuantum/TimeJet`](../Lean/H0mework/Physics/YangMillsSourceQuantum/TimeJet.lean) |
| P13 | [`Physics/RootRuntime/RecoveryConsumer`](../Lean/H0mework/Physics/RootRuntime/RecoveryConsumer.lean)、[`Physics/QuantumFoundation/Credential`](../Lean/H0mework/Physics/QuantumFoundation/Credential.lean)、[`Physics/QuantumFoundation/FoundationAcceptance`](../Lean/H0mework/Physics/QuantumFoundation/FoundationAcceptance.lean)、[`Physics/QuantumFoundation/FoundationDescent`](../Lean/H0mework/Physics/QuantumFoundation/FoundationDescent.lean)、[`Physics/QuantumFoundation/FoundationInvariance`](../Lean/H0mework/Physics/QuantumFoundation/FoundationInvariance.lean)、[`Physics/QuantumFoundation/FoundationNativeAction`](../Lean/H0mework/Physics/QuantumFoundation/FoundationNativeAction.lean)、[`Physics/Geometry/FullMotherDescentAndTransport`](../Lean/H0mework/Physics/Geometry/FullMotherDescentAndTransport.lean) |
| P14 | [`Physics/SourceFormation/AuxiliaryAction`](../Lean/H0mework/Physics/SourceFormation/AuxiliaryAction.lean)、[`Physics/MotherProgrammesFormation/FullAuxiliaryConsumer`](../Lean/H0mework/Physics/MotherProgrammesFormation/FullAuxiliaryConsumer.lean)、[`Physics/SourceFormation/AuxiliaryFields`](../Lean/H0mework/Physics/SourceFormation/AuxiliaryFields.lean) |
| P15 | [`Physics/MotherProgrammesFormationClockBF/Action`](../Lean/H0mework/Physics/MotherProgrammesFormationClockBF/Action.lean)、[`Physics/MotherProgrammesFormationClockBF/Calculus`](../Lean/H0mework/Physics/MotherProgrammesFormationClockBF/Calculus.lean)、[`Physics/MotherProgrammesFormationClockBF/Consumer`](../Lean/H0mework/Physics/MotherProgrammesFormationClockBF/Consumer.lean)、[`Physics/MotherProgrammesFormationClockBF/Feedback`](../Lean/H0mework/Physics/MotherProgrammesFormationClockBF/Feedback.lean)、[`Physics/MotherProgrammesFormationClockBF/Preparation`](../Lean/H0mework/Physics/MotherProgrammesFormationClockBF/Preparation.lean) |
| P16 | [`Physics/ConstitutiveInterfacesQuantization/CheckConsumer`](../Lean/H0mework/Physics/ConstitutiveInterfacesQuantization/CheckConsumer.lean)、[`Physics/ConstitutiveInterfacesQuantization/CheckControls`](../Lean/H0mework/Physics/ConstitutiveInterfacesQuantization/CheckControls.lean)、[`Physics/ConstitutiveInterfacesQuantization/CheckCurrent`](../Lean/H0mework/Physics/ConstitutiveInterfacesQuantization/CheckCurrent.lean)、[`Physics/ConstitutiveInterfacesQuantization/CheckFermion`](../Lean/H0mework/Physics/ConstitutiveInterfacesQuantization/CheckFermion.lean) |
| P17 | [`Physics/MotherProgrammesFormationMatter/ActionBasis`](../Lean/H0mework/Physics/MotherProgrammesFormationMatter/ActionBasis.lean)、[`Physics/MotherProgrammesFormationMatter/ActionConsumer`](../Lean/H0mework/Physics/MotherProgrammesFormationMatter/ActionConsumer.lean)、[`Physics/MotherProgrammesFormationMatter/ActionMatrix`](../Lean/H0mework/Physics/MotherProgrammesFormationMatter/ActionMatrix.lean) |
| P18 | [`Physics/MotherDeclarationsJoint/CarrierFormationConsumer`](../Lean/H0mework/Physics/MotherDeclarationsJoint/CarrierFormationConsumer.lean)、[`Physics/MotherDeclarationsJoint/CarrierFormationCoverage`](../Lean/H0mework/Physics/MotherDeclarationsJoint/CarrierFormationCoverage.lean)、[`Physics/MotherDeclarationsJoint/CarrierFormationFactory`](../Lean/H0mework/Physics/MotherDeclarationsJoint/CarrierFormationFactory.lean)、[`Physics/MotherDeclarationsJoint/CarrierFormationSemantics`](../Lean/H0mework/Physics/MotherDeclarationsJoint/CarrierFormationSemantics.lean)、[`Physics/MotherDeclarationsNative/PhysicalQueryConsumption`](../Lean/H0mework/Physics/MotherDeclarationsNative/PhysicalQueryConsumption.lean)、[`Physics/MotherDeclarationsNative/PhysicalQueryInquiry`](../Lean/H0mework/Physics/MotherDeclarationsNative/PhysicalQueryInquiry.lean) |
| P19 | [`Physics/Actual/FieldsHistoryBounds`](../Lean/H0mework/Physics/Actual/FieldsHistoryBounds.lean)、[`Physics/Actual/WeakCompactBounds`](../Lean/H0mework/Physics/Actual/WeakCompactBounds.lean) |
| P20 | [`Physics/MotherDeclarationsPhysical/LawsCompletion`](../Lean/H0mework/Physics/MotherDeclarationsPhysical/LawsCompletion.lean)、[`Physics/MotherDeclarationsPhysical/LawsObservation`](../Lean/H0mework/Physics/MotherDeclarationsPhysical/LawsObservation.lean)、[`Physics/MotherDeclarationsPhysical/LawsSource`](../Lean/H0mework/Physics/MotherDeclarationsPhysical/LawsSource.lean)、[`Physics/MotherLaws/JointSourceConsumer`](../Lean/H0mework/Physics/MotherLaws/JointSourceConsumer.lean)、[`Physics/MotherLaws/PointwiseCompletion`](../Lean/H0mework/Physics/MotherLaws/PointwiseCompletion.lean)、[`Physics/MotherLaws/PointwiseNative`](../Lean/H0mework/Physics/MotherLaws/PointwiseNative.lean)、[`Physics/MotherLaws/RestrictionExtension`](../Lean/H0mework/Physics/MotherLaws/RestrictionExtension.lean)、[`Physics/MotherLaws/RestrictionInterpreter`](../Lean/H0mework/Physics/MotherLaws/RestrictionInterpreter.lean)、[`Physics/MotherLaws/RestrictionProcess`](../Lean/H0mework/Physics/MotherLaws/RestrictionProcess.lean) |

### low-energy-phenomenology（L1–L17）

| 命题组 | 本仓模块（生产／直接消费者） |
| --- | --- |
| L1 库存、归一化与仿射跑动 | [`Physics/LowEnergy/ScalarInventory`](../Lean/H0mework/Physics/LowEnergy/ScalarInventory.lean)、[`Physics/LowEnergy/Normalization`](../Lean/H0mework/Physics/LowEnergy/Normalization.lean)、[`Physics/LowEnergy/Running`](../Lean/H0mework/Physics/LowEnergy/Running.lean)、[`Physics/LowEnergy/Consumer`](../Lean/H0mework/Physics/LowEnergy/Consumer.lean) |
| L2 联合真空与质量坐标 | [`Physics/LowEnergy/JointMassCoordinates`](../Lean/H0mework/Physics/LowEnergy/JointMassCoordinates.lean)、[`Physics/LowEnergy/Consumer`](../Lean/H0mework/Physics/LowEnergy/Consumer.lean) |
| L3 共同局部解族与初值导数 | [`Physics/LowEnergyEvolution/Uniform`](../Lean/H0mework/Physics/LowEnergyEvolution/Uniform.lean)、[`Physics/LowEnergyEvolution/VariationDerivative`](../Lean/H0mework/Physics/LowEnergyEvolution/VariationDerivative.lean)、[`Physics/LowEnergyEvolution/Full`](../Lean/H0mework/Physics/LowEnergyEvolution/Full.lean) |
| L4 物质复合与密度 | [`Physics/LowEnergyQuantum/Carrier`](../Lean/H0mework/Physics/LowEnergyQuantum/Carrier.lean)、[`Physics/LowEnergyQuantum/Compression`](../Lean/H0mework/Physics/LowEnergyQuantum/Compression.lean)、[`Physics/LowEnergyQuantum/Preparation`](../Lean/H0mework/Physics/LowEnergyQuantum/Preparation.lean)、[`Physics/LowEnergyQuantum/Readout`](../Lean/H0mework/Physics/LowEnergyQuantum/Readout.lean)、[`Physics/LowEnergyQuantum/Density`](../Lean/H0mework/Physics/LowEnergyQuantum/Density.lean) |
| L5 径向 Jacobi 传播 | [`Physics/LowEnergySpacetime/Propagation`](../Lean/H0mework/Physics/LowEnergySpacetime/Propagation.lean)、[`Physics/LowEnergySpacetime/Cauchy`](../Lean/H0mework/Physics/LowEnergySpacetime/Cauchy.lean)、[`Physics/LowEnergySpacetime/Jacobi`](../Lean/H0mework/Physics/LowEnergySpacetime/Jacobi.lean) |
| L6 活跃作用与约束约化 | [`Physics/LowEnergyActiveGauge/Phase`](../Lean/H0mework/Physics/LowEnergyActiveGauge/Phase.lean)、[`Physics/LowEnergyActiveGauge/Hodge`](../Lean/H0mework/Physics/LowEnergyActiveGauge/Hodge.lean) |
| L7 相位、制备与最大发展 | [`Physics/LowEnergyFullPhase/Operator`](../Lean/H0mework/Physics/LowEnergyFullPhase/Operator.lean)、[`Physics/LowEnergyFullPhase/Preparation`](../Lean/H0mework/Physics/LowEnergyFullPhase/Preparation.lean)、[`Physics/LowEnergyFullPhase/Derivative`](../Lean/H0mework/Physics/LowEnergyFullPhase/Derivative.lean)、[`Physics/LowEnergyScalar/QuaternionSymbol`](../Lean/H0mework/Physics/LowEnergyScalar/QuaternionSymbol.lean)、[`Physics/LowEnergyScalar/ReducedSymbol`](../Lean/H0mework/Physics/LowEnergyScalar/ReducedSymbol.lean) |
| L8 低动量有效作用 | (程序证据：scripts/physics/low-energy/soft-phase) |
| L9 物质顶点与源交换 | [`Physics/LowEnergyExchange/Current`](../Lean/H0mework/Physics/LowEnergyExchange/Current.lean)、[`Physics/LowEnergyExchange/Static`](../Lean/H0mework/Physics/LowEnergyExchange/Static.lean)、[`Physics/LowEnergyFermion/Consumer`](../Lean/H0mework/Physics/LowEnergyFermion/Consumer.lean) |
| L10 自由外腿与作用留数 | [`Physics/LowEnergyKinetic/Jet`](../Lean/H0mework/Physics/LowEnergyKinetic/Jet.lean)、[`Physics/LowEnergyKinetic/Density`](../Lean/H0mework/Physics/LowEnergyKinetic/Density.lean)、[`Physics/LowEnergyKinetic/Scale`](../Lean/H0mework/Physics/LowEnergyKinetic/Scale.lean) |
| L11 电磁主部与静态电荷 | (程序证据：principal-normalization／charge-response／metric-response) |
| L12 占据态 48×48 响应 | (程序证据：occupied-response 及 causal；有限 CAR 时间见 docs/source/physics/low-energy/fock-dynamics) |
| L13 L² 发展与原 Dirac 方程 | [`Physics/LowEnergyMatterSpace/Source`](../Lean/H0mework/Physics/LowEnergyMatterSpace/Source.lean)、[`Physics/LowEnergyMatterSpace/Connection`](../Lean/H0mework/Physics/LowEnergyMatterSpace/Connection.lean)、[`Physics/LowEnergyMatterSpace/Multiplier`](../Lean/H0mework/Physics/LowEnergyMatterSpace/Multiplier.lean)、[`Physics/LowEnergyMatterSpace/Continuity`](../Lean/H0mework/Physics/LowEnergyMatterSpace/Continuity.lean)、[`Physics/LowEnergyMatterSpace/Spatial`](../Lean/H0mework/Physics/LowEnergyMatterSpace/Spatial.lean)、[`Physics/LowEnergyMatterSpace/Duhamel`](../Lean/H0mework/Physics/LowEnergyMatterSpace/Duhamel.lean)、[`Physics/LowEnergyMatterSpace/Phase`](../Lean/H0mework/Physics/LowEnergyMatterSpace/Phase.lean)、[`Physics/LowEnergyMatterSpace/GeneratorDomain`](../Lean/H0mework/Physics/LowEnergyMatterSpace/GeneratorDomain.lean)、[`Physics/LowEnergyMatterSpace/GeneratorSchwartz`](../Lean/H0mework/Physics/LowEnergyMatterSpace/GeneratorSchwartz.lean)、[`Physics/LowEnergyMatterSpace/Weak`](../Lean/H0mework/Physics/LowEnergyMatterSpace/Weak.lean)、[`Physics/LowEnergyMatterSpace/Uniqueness`](../Lean/H0mework/Physics/LowEnergyMatterSpace/Uniqueness.lean)、[`Physics/LowEnergyMatterSpace/RawWeak`](../Lean/H0mework/Physics/LowEnergyMatterSpace/RawWeak.lean)、[`Physics/LowEnergyMatterSpace/DualWeak`](../Lean/H0mework/Physics/LowEnergyMatterSpace/DualWeak.lean)、[`Physics/LowEnergyMatterSpace/PrimalSymbol`](../Lean/H0mework/Physics/LowEnergyMatterSpace/PrimalSymbol.lean) |
| L14 规范控制准备 | [`Physics/LowEnergyMatterSpace/PreparationHistory`](../Lean/H0mework/Physics/LowEnergyMatterSpace/PreparationHistory.lean)、[`Physics/LowEnergyMatterSpace/PreparationState`](../Lean/H0mework/Physics/LowEnergyMatterSpace/PreparationState.lean)、[`Physics/LowEnergyMatterSpace/PreparationGauge`](../Lean/H0mework/Physics/LowEnergyMatterSpace/PreparationGauge.lean)、[`Physics/LowEnergyMatterSpace/PreparationNative`](../Lean/H0mework/Physics/LowEnergyMatterSpace/PreparationNative.lean) |
| L15 空间 CAR 有限词与正性 | [`Physics/LowEnergyMatterSpace/SpatialCARAlgebra`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialCARAlgebra.lean)、[`Physics/LowEnergyMatterSpace/SpatialCARSpan`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialCARSpan.lean)、[`Physics/LowEnergyMatterSpace/SpatialCARWords`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialCARWords.lean)、[`Physics/LowEnergyMatterSpace/SpatialCARAdjoint`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialCARAdjoint.lean)、[`Physics/LowEnergyMatterSpace/SpatialCARState`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialCARState.lean)、[`Physics/LowEnergyMatterSpace/SpatialCARNative`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialCARNative.lean) |
| L16 局域电流与 Kubo 响应 | [`Physics/LowEnergyMatterSpace/CurrentOperator`](../Lean/H0mework/Physics/LowEnergyMatterSpace/CurrentOperator.lean)、[`Physics/LowEnergyMatterSpace/LocalOperator`](../Lean/H0mework/Physics/LowEnergyMatterSpace/LocalOperator.lean)、[`Physics/LowEnergyMatterSpace/LocalSource`](../Lean/H0mework/Physics/LowEnergyMatterSpace/LocalSource.lean)、[`Physics/LowEnergyMatterSpace/SpatialResponseEvolution`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialResponseEvolution.lean)、[`Physics/LowEnergyMatterSpace/SpatialResponseKubo`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialResponseKubo.lean)、[`Physics/LowEnergyMatterSpace/SpatialResponseSource`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialResponseSource.lean)、[`Physics/LowEnergyMatterSpace/SpatialResponsePhase`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialResponsePhase.lean)、[`Physics/LowEnergyMatterSpace/SpatialResponsePhaseDuhamel`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialResponsePhaseDuhamel.lean)、[`Physics/LowEnergyMatterSpace/SpatialResponsePhaseKubo`](../Lean/H0mework/Physics/LowEnergyMatterSpace/SpatialResponsePhaseKubo.lean) |
| L17 全时间演化与零幅度真导数 | [`Physics/LowEnergyMatterSpace/GlobalGlue`](../Lean/H0mework/Physics/LowEnergyMatterSpace/GlobalGlue.lean)、[`Physics/LowEnergyMatterSpace/GlobalFlow`](../Lean/H0mework/Physics/LowEnergyMatterSpace/GlobalFlow.lean)、[`Physics/LowEnergyMatterSpace/GlobalResponse`](../Lean/H0mework/Physics/LowEnergyMatterSpace/GlobalResponse.lean)、[`Physics/LowEnergyMatterSpace/GlobalOriginal`](../Lean/H0mework/Physics/LowEnergyMatterSpace/GlobalOriginal.lean)、[`Physics/LowEnergyMatterSpace/PerturbedVariation`](../Lean/H0mework/Physics/LowEnergyMatterSpace/PerturbedVariation.lean)、[`Physics/LowEnergyMatterSpace/PerturbedOperator`](../Lean/H0mework/Physics/LowEnergyMatterSpace/PerturbedOperator.lean)、[`Physics/LowEnergyMatterSpace/GlobalRadial`](../Lean/H0mework/Physics/LowEnergyMatterSpace/GlobalRadial.lean) |

### whole-ledger-accounting（Y）

| 主张组 | 本仓模块（生产／直接消费者） |
| --- | --- |
| 整账结构与债务编译 | [`Foundation/Ledger/*`](../Lean/H0mework/Foundation/Ledger)、`Foundation/Responsibility/Debt*`、[`Arithmetic/FockResponsibility/*`](../Lean/H0mework/Arithmetic/FockResponsibility) |
| PrimeShadow 整读 | [`Arithmetic/PrimeShadow/*`](../Lean/H0mework/Arithmetic/PrimeShadow)（含 Y 版 `Versions.Y.Arithmetic.PrimeShadow.*`） |
| CanonicalArithmetic 关系链 | `Versions.Y.Arithmetic.PrimeShadow.DomainConsumers.CanonicalArithmetic.*` |
| 单元算术因子分解 | `Versions.X.Arithmetic.UnitArithmetic.*`、`Versions.Y.Arithmetic.BlockSpecialization.*` |
| 实例 8.7 第三阶段付款结算 | `Versions.Y1.Arithmetic.RiemannRuntime.Debt.*`（Y1 版 Clozel 链） |
| 入口聚合 | [`Papers/WholeLedgerAccounting`](../Lean/H0mework/Papers/WholeLedgerAccounting.lean)（Y 钉住根）、[`Papers/WholeLedgerAccountingY1`](../Lean/H0mework/Papers/WholeLedgerAccountingY1.lean)（Clozel 结算根） |

Y 修订中 [PrimeExponentPoleReceiptRelationRoot](../Lean/H0mework/Versions/Y/Arithmetic/RiemannGraph/History/PrimePower/Factorization/Responsibility/LivingLawCanonicalRiemannPrimeExponentPoleReceiptRelationRoot.lean#L76)
的唯一性引理只拆出事件的 `support_eq`，未消去同事件携带的 `actionTrace_eq`，第 76 行
`rfl` 在固定 mathlib 下失败，并拖累 10 个同修订消费者（含实例 8.7 所用的
[ClozelStageThreeIncidenceNoetherianClosure](../Lean/H0mework/Versions/Y/Arithmetic/RiemannRuntime/Debt/Closure/ClozelStageThreeIncidenceNoetherianClosure.lean)）。Y 的原字节仍在非默认库 `H0meworkPinned`，
`lake build H0meworkPinned` 可复现该失败。Homework 修复提交 Y1 只把该处改为拆出并替换
`actionTrace_eq`，命题不变；条目 `whole-ledger-accounting-y1` 按 Y1 导出这 11 个模块
（[Versions/Y1](../Lean/H0mework/Versions/Y1/)，其余依赖与 Y 共享同一导出），进入默认构建。

### observation-dynamics（H/E/I/X）

| 主张组 | 本仓模块（生产／直接消费者） |
| --- | --- |
| 计数观察门与控制 | [计数观察模块](../Lean/H0mework/Checks/Observation/CountedObservation/)（E、I 两版字节） |
| 原始 Riesz 动态观察 | [原始 Riesz 机制](source/observation/original-riesz-dynamic-observation.md) |
| 运行时与恢复消费者 | [`Foundation/Inquiry/*`](../Lean/H0mework/Foundation/Inquiry)、[`Checks/Observation/*`](../Lean/H0mework/Checks/Observation)（H/X 版） |
| 入口聚合 | [`Papers/ObservationDynamics`](../Lean/H0mework/Papers/ObservationDynamics.lean) |

E/I 保存不同字节的 `Gate.lean` 与 README；`make check-obs` 重建两版视图并断言 `Gate.lean` 的字节差异。检查范围见[复现指南](reproduction.md#独立检查)。

### low-energy-loop-response（Case 2，T）

完整有序闭迹证据包保留来源身份：`full-quantum/` 下的闭迹、准备态完整词、玻色有效核、
轻核、双球窗、全角积分、解析余项及各包 `audit/` 独立检查脚本，连同其全部
`*_sha256`/`source_hashes`/`candidate_sha256` 钉绑输入（脚本、JSON、压缩矩阵、日志、
`.gitignore` 清单）。
默认 Lean 构建编译对应模块的变换副本，`make check-case2` 执行 `CASE2_AUDITS` 及闭迹 Python 检查。源仓验证脚本的额外依赖与本仓执行范围见[复现指南](reproduction.md#独立检查)。

### native-flow（H/X）

原生运行时、Navier–Stokes 完成链与历史消费者；入口 [`Papers/NativeFlow`](../Lean/H0mework/Papers/NativeFlow.lean)。
X 期补充使用 [`Papers/NativeFlowX`](../Lean/H0mework/Papers/NativeFlowX.lean)。

### constrained-local-quantum（Case 5A，K1–K17）

外部复合衰变程序 `Verification/physics/low-energy-phenomenology/external-composite-decay/`
按五个时代钉住（T/T2/T3/V/X），K15–K17 另按各自提交钉住（均不是 X 的祖先）。每时代的 `.lean` 伴生文件、独立消费者脚本与其回执钉绑
按版本导出；`make check-5a` 在 T/V/X 三个公开视图分别运行冻结独立消费者
（一阶 Cauchy、量子高斯截面、joint CCR/CAR ports），并用
[`tools/compare_evidence.py`](../tools/compare_evidence.py) 与冻结回执逐字段比对。

K15 完整 H0 弱历史（`GaussDiagonalHistory` 至 `WeakCoreEvolution`）、K16 分级与伴随图
（`GaussDiagonalGrade`、`GaussAdjointHistory`）、K17 共同族酉时间与全 CAR
（`SourceFamilyHilbert`、`GaussUnitaryHistory`、`GaussUnitaryCore`、`GaussCARHistory` 等）
的伴生 Lean 文件在 [Physics/LowEnergy/Quantum](../Lean/H0mework/Physics/LowEnergy/Quantum/) 下，由默认构建编译；入口为
[K15](../Lean/H0mework/Papers/ConstrainedLocalQuantumK15.lean)、[K16](../Lean/H0mework/Papers/ConstrainedLocalQuantumK16.lean)、[K17](../Lean/H0mework/Papers/ConstrainedLocalQuantumK17.lean)。`make check-5a-k` 在三个视图重跑
`source_diagonal_core_history`、`source_diagonal_grade`、`source_unitary_core_history`
并与冻结回执比对。

### physics-common-source 附录 D.5（论文侧检查）

[`scripts/physics/common-source/check_core_identities.py`](../scripts/physics/common-source/check_core_identities.py) 核对论文正文所列的有限矩阵与算术
公式，冻结覆盖与容差记录于
[`evidence/physics/common-source/core-identity-checks.json`](../evidence/physics/common-source/core-identity-checks.json)。它随论文编写、只依赖 numpy，
不是 Homework 导出，因此不在 `export-map.json` 中。`make check-physics` 重跑并要求组数、
评价次数与回执相同且最大残差不超过容差（不同 numpy 构建的末位残差可能不同）。

### Bell 独立裁决（F/X）

`Verification/physics/stage10/independent-bell/` 的裁决脚本、NIST 数据与回执；
Stage10 Bell 材料与 `RealFamily` 认证按 X 期钉住。

## 程序证据与回执

- 低能唯象的精确程序与独立检查在 [`scripts/physics/low-energy/`](../scripts/physics/low-energy/)，冻结回执在 [`evidence/physics/low-energy/`](../evidence/physics/low-energy/)，
  机制推导与认证记录在 [`docs/source/physics/low-energy/`](source/physics/low-energy/)。
- Case 2 全量子审计在 [`scripts/physics/low-energy/full-quantum/`](../scripts/physics/low-energy/full-quantum/)，冻结证据在同名
  [`evidence/physics/low-energy/full-quantum/`](../evidence/physics/low-energy/full-quantum/)。
- Case 5A 独立消费者输出与冻结回执在 [`evidence/physics/constrained-quantum/`](../evidence/physics/constrained-quantum/)。
- 物理主稿的量化电流数值验收回执在 [`evidence/physics/quantization-current/`](../evidence/physics/quantization-current/)；
  Bell 独立裁决的原始记录在 [`evidence/physics/stage10-independent-bell/`](../evidence/physics/stage10-independent-bell/)（拒绝结论针对
  source+ideal-apparatus 联合模型，见论文 §9.2／D.4）。

## 依赖闭包说明

上表列出的入口模块只覆盖论文显式引用的生产口与直接消费者；完整可构建集还包含它们的
传递 `import` 依赖、脚本同级 import 与路径字面量闭包、以及回执钉绑的全部输入；逐条校验及数量查询入口为 `make check-map`。
这些依赖保持原证明进入本仓，其中包含论文未单独成文的其他成果；范围与来源见各论文命题表
及提交信息。
