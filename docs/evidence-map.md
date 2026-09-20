# 公开证据对应表

三篇论文的承重主张与本仓源码的对应。源码固定来自 Homework 私有研究仓：过程核心与
物理主稿为 `e60a86058a…`（H），低能唯象稿为 `30218c1ae…`（S）；H 是 S 的祖先。
前两稿所需的2632个模块在H/S间逐字节一致；低能稿另引入145个H中尚不存在的模块。
全部2777个模块自S导出：其中2774个与S逐字节一致，回归消费者 LifecycleRegression 在S处的
simpa脚本已不适配钉住的mathlib（v4.33.0/`db584cd`），自Homework修复提交`8e29b8e1e…`
（S的直接后继，仅改该文件的证明脚本与两个私有列表引理，命题不变）导出；
逆向恢复字节与各该来源一致。
迁移仅改写本地 `import` 模块地址；声明名、命名空间、前提、量词与证明正文保持原样。

| 论文 | 固定来源 | 选集入口 |
| --- | --- | --- |
| source-process-core（过程核心） | Homework `e60a8605` | `source-process-core`（C1–C13 及其直接消费者） |
| physics-common-source（同源物理） | Homework `e60a8605` | `physics-common-source`（P1–P20 及其直接消费者） |
| low-energy-phenomenology（低能唯象） | Homework `30218c1a` | `low-energy-phenomenology`（L1–L17 及复现程序） |

主张的精确陈述、量词与前提以论文命题表为准；下表只给本仓模块入口。

### source-process-core（C1–C13）

| 命题 | 新仓模块（producer／consumer） |
| --- | --- |
| C1 | `Foundation/Responsibility/Lifecycle`、`Foundation/Responsibility/LifecycleRegression` |
| C2 | `Foundation/Responsibility/NoetherianClosure`、`Foundation/Responsibility/NoetherianClosureRegression` |
| C3 | `Foundation/Runtime/AnswerHistory`、`Foundation/Semantics/RootReality` |
| C4 | `Foundation/Runtime/Inquiry`、`Checks/Runtime/Inquiry` |
| C5 | `Checks/Runtime/Inquiry`、`Checks/Runtime/U8Completion` |
| C6 | `Checks/Runtime/Inquiry` |
| C7 | `Realization/Operations/DerivationReduction`、`Realization/Operations/Effects`、`Realization/Operations/MixedTrace`、`Checks/Realization/OperationDerivations`、`Fock/Cofinal/OperationDerivation` |
| C8 | `Checks/Realization/QuantifiedUpdate`、`Realization/Operations/RuntimeEvolution`、`Realization/Operations/RuntimeRelations`、`Realization/Operations/RuntimeSuccessor`、`Realization/Operations/ScalarExact`、`Realization/Operations/ScalarPresentation`、`Fock/Cofinal/DynamicsWitness`、`Fock/Cofinal/OperationPrefix` |
| C9 | `Realization/Operations/BinaryInputs`、`Realization/Operations/NativeState`、`Realization/Operations/FieldInputs`、`Checks/Realization/NativeBinary`、`Checks/Realization/NativeSource`、`Checks/Realization/NativeUnitWrite`、`Arithmetic/UnitArithmetic/Root`、`Fock/Cofinal/OperationNative` |
| C10 | `Foundation/Semantics/CausalRealization`、`Realization/SourceComparison/GroundedRealization`、`Physics/MotherDescription/Consumer`、`Physics/MotherSource/GroundedRealization` |
| C11 | `Realization/JointEffect/PassiveController`、`Realization/JointEffect/AuditTransition`、`Realization/JointEffect/AuditTransitionRegression`、`Realization/JointEffect/Residual`、`Realization/Audit/U7Coface`、`Foundation/Inquiry/ResidualCoface` |
| C12 | `Foundation/Responsibility/DebtCompiler`、`Foundation/Responsibility/DebtWorld`、`Foundation/Responsibility/DebtWorldReadback`、`Arithmetic/FockResponsibility/DirectResponsibility`、`Arithmetic/FockResponsibility/TargetSixActionDebt` |
| C13 | `Checks/Runtime/Inquiry`、`Foundation/Inquiry/MinimalCoface`、`Foundation/Inquiry/SemanticRevision`、`Foundation/Inquiry/RevisionRecovery`、`Arithmetic/FockResponsibility/DebtU7LivingRoot` |
| 来源表／回执 | `Physics/MotherDeclarationsNative/PhysicalQueryConsumption`、`Physics/MotherDeclarationsNative/PhysicalQueryInquiry` |

### physics-common-source（P1–P20）

| 命题 | 新仓模块（producer／consumer） |
| --- | --- |
| P1 | `Physics/RootRuntime/RecoveryConsumer`、`Physics/RootRuntime/RecoverySource`、`Physics/RootRuntime/RuntimeConsumer` |
| P2 | `Physics/Actual/WeakCandidate`、`Physics/QuantumFoundation/Classical`、`Physics/QuantumFoundation/FoundationAcceptance`、`Physics/QuantumFoundation/RuntimeConsumer`、`Physics/Geometry/CClassicalAcceptance` |
| P3 | `Physics/Matter/SU7ExteriorMatterAnomalyRunning`、`Physics/Matter/SU7GravityGaugeMatterJointCredential`、`Physics/RootRuntime/RecoveryConsumer`、`Physics/RootRuntime/RecoveryMatter` |
| P4 | `Physics/MotherDescription/Consumer`、`Physics/MotherSource/GroundedRealization`、`Physics/QuantumCompatibility/DualResponse`、`Physics/QuantumFoundation/Credential` |
| P5 | `Physics/QuantumCompatibility/Acceptance`、`Physics/QuantumCompatibility/Stress`、`Physics/QuantumFoundation/Credential`、`Physics/QuantumFoundation/RuntimeConsumer` |
| P6 | `Realization/SourceComparison/GroundedRealization`、`Physics/MotherDescription/Consumer`、`Physics/MotherSource/GroundedRealization` |
| P7 | `Physics/GlobalOrbit/Acceptance`、`Physics/GlobalOrbit/Observable` |
| P8 | `Physics/Bell/Preparation`、`Physics/Bell/Runtime`、`Physics/EmpiricalContact/Consumer` |
| P9 | `Physics/MotherDeclarationsAll/SourceOriginConsumer`、`Physics/MotherDeclarationsAll/SourceOriginOperations`、`Physics/MotherLaws/JointSourceConsumer` |
| P10 | `Physics/SourceFormation/Acceptance`、`Physics/SourceFormation/Consumer`、`Physics/SourceFormation/EvolutionConsumer` |
| P11 | `Physics/MotherProgrammesFormationPaths/Consumer`、`Physics/MotherProgrammesFormationPaths/Late`、`Physics/MotherProgrammesFormationPaths/Steps`、`Physics/MotherProgrammesFormationProgrammes/AutonomousConsumer`、`Physics/MotherProgrammesFormationProgrammes/AutonomousCoverage` |
| P12 | `Physics/YangMillsSourceQuantum/JetEnergy`、`Physics/YangMillsSourceQuantum/TimeJet` |
| P13 | `Physics/RootRuntime/RecoveryConsumer`、`Physics/QuantumFoundation/Credential`、`Physics/QuantumFoundation/FoundationAcceptance`、`Physics/QuantumFoundation/FoundationDescent`、`Physics/QuantumFoundation/FoundationInvariance`、`Physics/QuantumFoundation/FoundationNativeAction`、`Physics/Geometry/FullMotherDescentAndTransport` |
| P14 | `Physics/SourceFormation/AuxiliaryAction`、`Physics/MotherProgrammesFormation/FullAuxiliaryConsumer`、`Physics/SourceFormation/AuxiliaryFields` |
| P15 | `Physics/MotherProgrammesFormationClockBF/Action`、`Physics/MotherProgrammesFormationClockBF/Calculus`、`Physics/MotherProgrammesFormationClockBF/Consumer`、`Physics/MotherProgrammesFormationClockBF/Feedback`、`Physics/MotherProgrammesFormationClockBF/Preparation` |
| P16 | `Physics/ConstitutiveInterfacesQuantization/CheckConsumer`、`Physics/ConstitutiveInterfacesQuantization/CheckControls`、`Physics/ConstitutiveInterfacesQuantization/CheckCurrent`、`Physics/ConstitutiveInterfacesQuantization/CheckFermion` |
| P17 | `Physics/MotherProgrammesFormationMatter/ActionBasis`、`Physics/MotherProgrammesFormationMatter/ActionConsumer`、`Physics/MotherProgrammesFormationMatter/ActionMatrix` |
| P18 | `Physics/MotherDeclarationsJoint/CarrierFormationConsumer`、`Physics/MotherDeclarationsJoint/CarrierFormationCoverage`、`Physics/MotherDeclarationsJoint/CarrierFormationFactory`、`Physics/MotherDeclarationsJoint/CarrierFormationSemantics`、`Physics/MotherDeclarationsNative/PhysicalQueryConsumption`、`Physics/MotherDeclarationsNative/PhysicalQueryInquiry` |
| P19 | `Physics/Actual/FieldsHistoryBounds`、`Physics/Actual/WeakCompactBounds` |
| P20 | `Physics/MotherDeclarationsPhysical/LawsCompletion`、`Physics/MotherDeclarationsPhysical/LawsObservation`、`Physics/MotherDeclarationsPhysical/LawsSource`、`Physics/MotherLaws/JointSourceConsumer`、`Physics/MotherLaws/PointwiseCompletion`、`Physics/MotherLaws/PointwiseNative`、`Physics/MotherLaws/RestrictionExtension`、`Physics/MotherLaws/RestrictionInterpreter`、`Physics/MotherLaws/RestrictionProcess` |

### low-energy-phenomenology（L1–L17）

| 命题组 | 新仓模块（生产／直接消费者） |
| --- | --- |
| L1 库存、归一化与仿射跑动 | `Physics/LowEnergy/ScalarInventory`、`Physics/LowEnergy/Normalization`、`Physics/LowEnergy/Running`、`Physics/LowEnergy/Consumer` |
| L2 联合真空与质量坐标 | `Physics/LowEnergy/JointMassCoordinates`、`Physics/LowEnergy/Consumer` |
| L3 共同局部解族与初值导数 | `Physics/LowEnergyEvolution/Uniform`、`Physics/LowEnergyEvolution/VariationDerivative`、`Physics/LowEnergyEvolution/Full` |
| L4 物质复合与密度 | `Physics/LowEnergyQuantum/Carrier`、`Physics/LowEnergyQuantum/Compression`、`Physics/LowEnergyQuantum/Preparation`、`Physics/LowEnergyQuantum/Readout`、`Physics/LowEnergyQuantum/Density` |
| L5 径向 Jacobi 传播 | `Physics/LowEnergySpacetime/Propagation`、`Physics/LowEnergySpacetime/Cauchy`、`Physics/LowEnergySpacetime/Jacobi` |
| L6 活跃作用与约束约化 | `Physics/LowEnergyActiveGauge/Phase`、`Physics/LowEnergyActiveGauge/Hodge` |
| L7 相位、制备与最大发展 | `Physics/LowEnergyFullPhase/Operator`、`Physics/LowEnergyFullPhase/Preparation`、`Physics/LowEnergyFullPhase/Derivative`、`Physics/LowEnergyScalar/QuaternionSymbol`、`Physics/LowEnergyScalar/ReducedSymbol` |
| L8 低动量有效作用 | (程序证据：scripts/physics/low-energy/soft-phase) |
| L9 物质顶点与源交换 | `Physics/LowEnergyExchange/Current`、`Physics/LowEnergyExchange/Static`、`Physics/LowEnergyFermion/Consumer` |
| L10 自由外腿与作用留数 | `Physics/LowEnergyKinetic/Jet`、`Physics/LowEnergyKinetic/Density`、`Physics/LowEnergyKinetic/Scale` |
| L11 电磁主部与静态电荷 | (程序证据：principal-normalization／charge-response／metric-response) |
| L12 占据态 48×48 响应 | (程序证据：occupied-response 及 causal；有限 CAR 时间见 docs/source/physics/low-energy/fock-dynamics) |
| L13 L² 发展与原 Dirac 方程 | `Physics/LowEnergyMatterSpace/Source`、`Physics/LowEnergyMatterSpace/Connection`、`Physics/LowEnergyMatterSpace/Multiplier`、`Physics/LowEnergyMatterSpace/Continuity`、`Physics/LowEnergyMatterSpace/Spatial`、`Physics/LowEnergyMatterSpace/Duhamel`、`Physics/LowEnergyMatterSpace/Phase`、`Physics/LowEnergyMatterSpace/GeneratorDomain`、`Physics/LowEnergyMatterSpace/GeneratorSchwartz`、`Physics/LowEnergyMatterSpace/Weak`、`Physics/LowEnergyMatterSpace/Uniqueness`、`Physics/LowEnergyMatterSpace/RawWeak`、`Physics/LowEnergyMatterSpace/DualWeak`、`Physics/LowEnergyMatterSpace/PrimalSymbol` |
| L14 规范控制准备 | `Physics/LowEnergyMatterSpace/PreparationHistory`、`Physics/LowEnergyMatterSpace/PreparationState`、`Physics/LowEnergyMatterSpace/PreparationGauge`、`Physics/LowEnergyMatterSpace/PreparationNative` |
| L15 空间 CAR 有限词与正性 | `Physics/LowEnergyMatterSpace/SpatialCARAlgebra`、`Physics/LowEnergyMatterSpace/SpatialCARSpan`、`Physics/LowEnergyMatterSpace/SpatialCARWords`、`Physics/LowEnergyMatterSpace/SpatialCARAdjoint`、`Physics/LowEnergyMatterSpace/SpatialCARState`、`Physics/LowEnergyMatterSpace/SpatialCARNative` |
| L16 局域电流与 Kubo 响应 | `Physics/LowEnergyMatterSpace/CurrentOperator`、`Physics/LowEnergyMatterSpace/LocalOperator`、`Physics/LowEnergyMatterSpace/LocalSource`、`Physics/LowEnergyMatterSpace/SpatialResponseEvolution`、`Physics/LowEnergyMatterSpace/SpatialResponseKubo`、`Physics/LowEnergyMatterSpace/SpatialResponseSource`、`Physics/LowEnergyMatterSpace/SpatialResponsePhase`、`Physics/LowEnergyMatterSpace/SpatialResponsePhaseDuhamel`、`Physics/LowEnergyMatterSpace/SpatialResponsePhaseKubo` |
| L17 全时间演化与零幅度真导数 | `Physics/LowEnergyMatterSpace/GlobalGlue`、`Physics/LowEnergyMatterSpace/GlobalFlow`、`Physics/LowEnergyMatterSpace/GlobalResponse`、`Physics/LowEnergyMatterSpace/GlobalOriginal`、`Physics/LowEnergyMatterSpace/PerturbedVariation`、`Physics/LowEnergyMatterSpace/PerturbedOperator`、`Physics/LowEnergyMatterSpace/GlobalRadial` |

## 程序证据与回执

- 低能唯象的精确程序与独立检查在 `scripts/physics/low-energy/`，冻结回执在 `evidence/physics/low-energy/`，
  机制推导与认证记录在 `docs/source/physics/low-energy/`。
- 物理主稿的量化电流数值验收回执在 `evidence/physics/quantization-current/`；
  Bell 独立裁决的原始记录在 `evidence/physics/stage10-independent-bell/`（拒绝结论针对
  source+ideal-apparatus 联合模型，见论文 §9.2／D.4）。

## 依赖闭包说明

上表列出的入口模块只覆盖论文显式引用的生产口与直接消费者；完整可构建集还包含它们的
传递 `import` 依赖（共 2777 个本地模块）。
这些依赖保持原证明进入本仓，其中包含论文未单独成文的其他成果；范围与来源见各论文命题表
及提交信息。
