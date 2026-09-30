# 原完整应力的 canonical 配对载体

> 稳定机制；当前目标和责任见[原生全阶 active card](../../handoffs/navier-stokes-native-regularity-active-route.md)。
> 此载体从原 σ／U 生成，不用弱 U 单独配对替代完整应力。

## 源与完整载体

`NativePositiveKernelCarrier` 从任意正半定复核生成有限支撑形式的半内积空间，再完成化。
`vector_inner` 精确读回整个核；零范数向量由完成化识别，不提交 Gram 或 normalizer。

`NativeStressPairingCarrier.Data` 的输入是完整均值、Fourier reality、σ 及原协方差正性。
令 `Q=−U⊗U`，`R=σ−Q(U)`；正核为 `−R(k−l)ᵢⱼ`。完整空间为
`ℓ²(ℤ³;ℂ) ×₂ completion(−R)`。背景与 component 同时满足

```
⟪background(k), component(l,j)⟫ = U(k−l)ⱼ
⟪component(k,i), component(l,j)⟫ = −σ(k−l)ᵢⱼ
Σᵢ ‖component(0,i)‖² = −Σᵢ Re σ(0)ᵢᵢ
```

`cofinal initial` 直接消费原 canonical weak receipt、同次 refinement 的完整 σ 与已证
正性；总能量等于原 `wholeRestartKineticMassLimit`，不是弱均值能量。

`NativeHilbertDiracCurrent` 将原物质系数程序解释为 `Fin 4 → Fin 2 → Space data`。
dual 固定为原 `diracAdjointSpinSwap` 在左槽的 Hilbert 配对；原四个 Gamma 作用不变。
原 σ 的对称性来自同次接触应力极限。`cofinal_current` 给全四分量、全波的原 inherited
current，时间分量保留 `−tr R/8`。这是 Hilbert-valued 配对读出，没有声称等于旧有限
`DiracExteriorMatterCarrier` 或指定 `SpinPair.actual`。

## 原 compiler 写入与实际作用

`NativeResolvedPairingTransfer.resolved` 的应力是 `Q(mean)`；这份目标自身的残余完成空间
为零。`transfer` 将其等距嵌入固定原载体的均值槽，保留原 Gamma 及 canonical 配对。
该证明没有令原 cofinal 的 R 为零。

`NativePairedCarrierRegeneration` 从原 H¹ compiler 的 `target.nextReceipt` 读取实际均值，
生成固定 cofinal 空间中的 `sourceMatter`。相对原完整 matter 的差分，在残余槽中是原
向量的负值；这不是把正 Gram 核取负。`source_current_effect` 保留两交叉项和二次项，
完整响应认回 `−tr(Q(U(s))−σ)/8` 及原空间 current。末端直接读取原 next.contact 的
真实物理 L² 四电流，未替换 compiler。

`NativePairedCarrierJets` 证明写入为 `vacuum + matterCLM(original velocity)`；原完整频率
平移保持标量 ℓ² 范数。原 receipt 的已付时间 jets 经同一连续线性读出生成完整 Spinor
的强时间 jets，基域为 ℝ，范数为完整 Hilbert fibre 上的有限 Pi 范数。
`NativePairedDifferentialAction` 对原 spin-swap／Gamma 配对独立求导，两槽乘积法则所得
`currentRate` 精确认回原 `responseJet 1`。

`NativePairedCarrierControl` 直接从这些源 jets 得到完整 matter 及四 current 的 C∞On，
消费闭物理时间窗内紧集上的任意有限阶 `iteratedFDerivWithin` 与全 p Lp，包括 ∞。
测度为 dt；参数 wave 不在此积分。原 physical current 的四维控制及 Fourier 身份继续
由 `CofinalUnifiedControl/CofinalCurrentResponse` 提供。

## 完整 dual 与源作用积分

`PairedDualCarrier` 从同一个 spin-swap 配对生成连续 complex dual；外层映射为实 CLM，
所有 jets 在完整算子范数中成立。`PairedCompleteWrite` 从原 receipt 的 matterJet 1
积分，dual 积分由这同一 CLM 交换取得；primal 和 dual 的完整等式保持 canonical 配对，
并读取原 next.contact 四电流。原 cofinal 到本 receipt 入口的差量与本窗积分分开保留。

`ReceiptStrongVelocityWrite.velocityActionCLM` 直接复合原
`puncturedEuclideanizeCLM → wholeRestartKineticToVelocityCLM → wholeVelocityCLM`。
它消费 receipt.wholeTangent 的已有 L² 时间支付，严格消去负一阶的 sqrt λ 归一化；
零波为零，其余波 a.e. 认回原 BS(Gν)。原逐波 FTC 经 evalCLM 交换生成完整未加权
速度的 Bochner 积分，源口只接受已有真实 receipt，不另收窗口、光滑或预算。

`ReentryCompleteWrite` 将这份同源 L² 作用交给完整 matterCLM／dualCLM，给原 H¹
首 receipt 从零时到任意端点的完整配对写入。`ReentryPairedCarrier` 的 contact 值及
强导数严格接到原 nextReceipt 的零时值和作用，空间固定为原 cofinal fibre。
`source_inlet_write` 将首 receipt 积分接入下一 receipt 的原 inlet 差量；原 cofinal→H¹
恢复差量仍保留，不把它伪称瞬时时间力或 old cofinal C∞。

## 整个恢复内区间的实际配对

`NativeRecoveryPairedCarrier.source initial time` 在原 regularSet 消费 Q(U)，在域外消费
原 sourceStress；两种发生都生成完整 Gram／canonical current。均值精确读回原
wholeMild，且 `Σᵢ‖component(0,i)‖² ≤ 原 kinetic budget`，含完整缺陷且无额外维数因子。
这里是按时刻生成的 fibres，不宣称它们已经组成一个时间光滑的固定 fibre。

`NativeRecoveryPairedAction` 从 canonical 空间 current 与完整 Gram σ 计算动量、压力。
其动量认回常规发生的真实导数及域外原 moving-sample 的导数极限。动量的投影 curl
减原 ν 的 resolved tangent 精确生成完整修正；输出库存为 `F∪(F+F)`。
该实际作用直接消费整个恢复内区间内、固定 F 的全空间阶与全 p 控制，不借新估计。

## 跨时完整核与原积分

`RecoveryTimeGramRaw` 取原 `StressAt.refinement` 上的完整有限 Galerkin 轨道，索引包含
原 moving anchor、全部固定时间及全波／坐标，背景仍为原 ℓ² 基。原 kinetic account
统一控制全部 Gram 项；`RecoveryJointTimeKernel.generated` 由原轨道内部选择 cofinal
ultrafilter，生成一个固定完成空间。全实时间索引的同时极限没有被改报成一条普通子列。

`RecoveryTimeGramReadout` 从同核读回原 wholeMild 的全 U，并保留 anchor 的原完整 σ。
固定时间与 moving anchor 是不同取样发生；同一数值时间不强制两者应力相同。
wave 在此为测试／频率平移索引，component 范数不随该索引衰减，不将它们求和成物质场。

`RecoveryTimeGramAction` 在原有限轨道先应用实际 `finiteStateVorticityGenerator`，再取
单槽与双槽的真实物理时间积分。其同核极限给全部配对增量和 σ 的全部矩阵元变化。
`RecoveryTimeGramWrite` 积分的是完整 `ScalarSequence` 作用；全部有限源测试、两段
作用的内积和完整范数平方均取同一次极限。完成化的稠密测试进一步唯一确定作用向量。
这给出原积分的完整表示，不交换积分极限与 limiting path 的经典求导。

`RecoveryTimeGramForce` 用原压力 CLM 和 `Pdiv−νλ` 消费这些真实增量，anchor 精确
认回原 `EscapeMomentum`。完整 σ／U 的原 kinetic budget 直接进入已付 fixed-F
`JointStressFilter.spatial_Lp`；时间节点统一，阶数和 p 任意。原 H¹ 时刻的 U 通过
原 `PositiveTimeH1NextCurrent_sameEvent` 读回原 compiler 的 `target.initial`。

`RecoveryTimeCanonical` 把原 matter 程序解释在这个固定空间中；`program_original` 与原
spin-swap／Gamma 程序定义相等。`readBackground/readComponent` 反读原基与全部 component，
因而完整 matter 保留 U、全部 σ 和真实 current 积分响应。

`RecoveryRootActionSplice` 从原 cofinal 和 Galerkin whole-ledger 的 `nativeWrite` 消元
原 weak endpoint 与完整 finite stage。原完整作用使齐次坐标上的线性写入直接消费
`SourceGeneratedScalarEquivariantPerfectAction.generate`；其 perfect pairing 精确读回
原 σ 的所有矩阵元与实际变化。齐次坐标不是物理时钟，泛型 dual pullback 是代数测试的
反变作用，physical dual 仍由 canonical 程序固定。原 compiler 后继精确为 `.galerkin 0`；
这份 primitive 消费没有额外安装原根的 joint-transition inventory。

## 原时间测度与实际恢复方程

`RecoveryTimeStrongRefinement` 从原 `receipt.core.state_tendsto` 选择原 stress refinement
内部的严格子列，其原有限完整速度在 commonTime 测度下 a.e. 强收敛到原 wholePath。
联合核先消费这份源子列再取紧性，并将 ultrafilter 映回原 stress 索引；原全时间 Gram、
moving anchor、cofinal 性与 source bounds 同时保留，`Realization.fixedStrong` 保存新增读出。

`RecoveryTimeGramMeasured.source_stress_ae` 因而将 fixed-time 的完整 σ 认回原 Q(U)。
`forcingLp` 是从此 σ 计算的 Leray 散度在原 L¹ 时间载体中的实现；`source_forcingLp`
精确等于原 receipt 的已生成 forcing。`source_mild_from_kernel` 直接把它交给原
Duhamel 消费者，读回每个原时间的非零 U 行；零行由原 `source_velocity` 保留。
这里的 a.e. 身份没有消去 moving anchor 的应力，也没有把不同取样发生逐点认同。

`RecoveryTimeMomentumWrite` 将同核 `Pdiv σ−νλU` 接到原 AC rowExtension；原物理时间
内每个 Fourier 行的 a.e. 导数精确认回此作用。原 FTC 给从零时至任意原端点的积分，
结果是同核 U 的增量，含零波。这里签收逐行导数与完整波族的积分身份，没有把它改报为
整个未加权 ℓ² 速度的强时间导数；后者仍按实际完整载体的接口消费。

## 完整配对写入及其已证消费者

`RecoveryTimeCanonicalWrite` 用同一原 Bochner 积分写回完整 Spinor 与完整连续 canonical
dual。全部源测试、两段作用配对、真实 Pi/sup 范数平方极限与唯一性保持；四电流消费
两个交叉项和二次项，读回原 U／σ。

`RecoveryTimeBackgroundProjection` 从原背景 Gram 生成 ℓ² 等距嵌入及其 adjoint。
`meanRead_component` 精确读回全 TimeNode 的原 U；正交余项保留全部 σ−Q(U)、跨时间
mixedFlux 和原 anchor 应力，Pythagorean 账户没有删除余项。
`PhysicalReadout` 复合原 Fourier unitary 得到全频物理 L² 读出；`WholeReadout` 将三坐标
经同一 CLM 重组为原完整系数状态，保留原作用增量和 H¹ compiler 的原 initial。

`RecoveryTimeCanonicalControl` 在原 commonTime 测度下消元 fixed-time 的正交余项，
原 matter／dual 与同核 projected 代表 a.e. 相同。原 ControlledWindow 的完整强 jets、
C∞ 和各阶时间 Lp 作用于该代表；原未经修改函数取得零阶 MemLp，不冒称其逐点经典 jets。
`WholeReadout` 的四维全阶 Lp 直接消费相同原窗口的既有控制。
这些实际消费者保持各自范围；是否继续扩展，由原发生到统一全阶总调用的真实缺口决定。

## 原完整作用直接进入统一 temporal primitive

`UnifiedSourceActionFeed.actionAt` 在原联合核的每个 TimeNode 读取完整 σ 与 U。
原有限动量沿同一次 refinement 的全波极限，加上原 kinetic 支付的
`NegativeFourMomentum.actionState_norm_le`，通过 `lp.memℓp_of_tendsto` 生成整个
H⁻⁴ 动量。其可积性由原逐行积分与 `lp.hasSum_single` 产生，完整 Bochner 积分因此
精确等于原 U 的 H⁻⁴ 写入。`generatedState_original` 直接调用 Stage9 的
`canonicalTimePrimitive`，读回整个原 Icc(0,1) receipt；原 anchor 动量独立保留。

`UnifiedCofinalActionFeed.actionAt initial` 消费原 micro-contact 的同次 cofinal σ，
在相同 Hilbert 类型中生成零时动量。`actionAt_read/pressure/complete_stress` 对全波
恢复原动量、压力及 resolved＋原 R；没有重选应力。`UnifiedRootActionFeed` 再直接
消元原 `RecoveryJointCurrent` 的 regular／uncovered 分支，输入只需原 current 与物理
时间；零时读取该 cofinal 值。`source_action_read` 认回原每个内部时刻的完整作用，
原时间测度下的 a.e. 关系用于积分，不修改源函数在坏点或零时的值。

`UnifiedRootActionFeed.generatedState_original` 无 caller-stress 地生成原完整 receipt，
`source_generated_next` 在原 H¹ 时刻回读原 compiler target.initial。这里的完整 receipt
仍是同一源生成对象，H¹ 之后的 receipt 延拓不冒充 macro 实际后继轨道；后者由
`UnifiedSourceActionFeed.global_generated_next` 沿原 clockAdvance 精确认回。
H⁻⁴ 的全部系数可逐波反读；这些定理没有宣称逆权重是连续物理 L² 解码器，或把可积性
当成全阶光滑性。当前导数实现责任仅由 active card 维护。

`UnifiedSourceDerivative` 直接消费共享的 `IntervalIntegrable.ae_hasDerivAt_integral`，
得到原完整 H⁻⁴ Hilbert 态的 a.e. 强时间导数，导数精确为上述源动量；任意连续线性
测试都与该导数相容。原绝对全历史亦取得同一强导数消费，不接收点态连续性或 Smooth。
这项 a.e. 消费不修改 cofinal／坏点的原 σ 值，不提升为这些点的经典全阶 jets。

`UnifiedMacroActionFeed` 把原 bounded compiler 的 wholeMild／H¹ 时间通过既有
`toCore_eq_nativeTemporal` 消元到同一发生，只在真实恢复区间消费上述 profile。
累积点直接读取原 cofinal σ 动量，两端精确读取原 current／next 初值作用。
`UnifiedActionHistory` 沿原 `NativeReachable` 折叠这些实际作用；它的条件是从属 fold
接口，`UnifiedGlobalActionFeed` 全部用固定 `MacroActionFeed.action` 填入。

`UnifiedGlobalActionFeed.action seed` 因而覆盖原绝对全历史：每次 cofinal／恢复的 σ
动量都逐点保留，有限原历史的 max 账户给全时间点态界，原源 L∞ 时间类继续可用。
`generatedState_original` 将此实际 profile 交给共享 `canonicalTimePrimitive`，完整
写回原绝对全轨道。`source_generated_next` 对作用 profile 本身给原 clockAdvance
平移后的逐点等式；`generatedState_next` 保留相同状态读回。这里实际消费原
proof-relevant `terminal_unique`，没有重新选择未来表或仅以积分相等代替源作用认同。

## 全历史完整应力与作用的共同输入

动量是完整 σ 的散度／Leray 读出，不能由它恢复被投影消去的应力分量。
`UnifiedStressSource` 直接消元原 Root／Macro 的 regular、uncovered、cofinal 和真实恢复
区间，生成原完整 σ；`UnifiedGlobalStressSource` 沿原 `NativeReachable` 与 terminal
共同递归生成 `(U,σ)`。其第一投影逐点为原 GlobalPath，第二投影保留全部整数波与九个
张量分量；`source_generated_next` 对整个 pair 给出原 clockAdvance 下的逐点等式，包含零时。

`CompleteStressCarrier.Space` 是全部整数波上九分量复张量的 ℓ²，应力权重为：零波 1，
非零波 `integerWaveNormSq⁻¹`。原逐坐标 kinetic 预算与既有 critical-kernel 可和性支付
完整 H⁻² 范数。`read_ofBound/read_injective` 保留每个原 σ 系数，特别是零频 trace；
这个源输入没有把完整应力替换成其动量像。

`CompleteStressAction.momentumCLM` 从完整 `(原 U 的 L², 原 σ 的 H⁻²)` 作用到现有 H⁻⁴
速度载体。散度／Leray 使用原算子且范数不超过 `2π`；黏性保持原 ν 与原频率乘子。
`momentumCLM_source` 精确给出原 `P div σ − ν λ U`。其目标沿用原 punctured 动量载体；
非零波作用口与全波应力读回的量词分别保留。

`UnifiedCompleteSource.source seed time` 将上述共同原 pair 实现为完整 normed 输入。
源预算、`AEStronglyMeasurable`、全实时间 L∞ 及各紧时间域任意 p 的零阶 Lp 均由原数据
产生；σ 的 a.e. Q(U) 身份只用于测度消费，原 cofinal／坏点值不改动。
`source_momentum` 是完整 H⁻⁴ 向量等式，`source_primitive` 真正把
`momentumCLM (source …)` 交给共享 Stage9 writer，并读回原全轨道的 H⁻⁴ 状态。
其 a.e. 强导数、Bochner 积分与整个 normed source 的原 generated next 同时保留。
这里没有把 σ 的经典时间导数、物理高阶 Lp 或九字段 Smooth 放进声明范围。

## 原热作用与全历史 Duhamel 消费

`UnifiedHeatAction.rowEvolution` 将原 `−ν λ(k)` 送入共享 `NormedSpace.exp` 的同载体
endomorphism algebra，精确认回原 Fourier 热乘子。完整 `heatCLM` 是原速度载体上的收缩
半群，保留零时、时间复合与原 H⁻⁴ 嵌入；它没有把完整 σ 动量误当成同载体生成器。

`UnifiedGlobalDuhamel` 从原完整 σ 动量的 a.e. 强微分及原状态的 Lipschitz 写入获得每个
真实 Fourier 行的 AC，消费原向量 FTC／Duhamel path。全部整数波及任意 `0 ≤ a ≤ b` 均有
`U(b) = heat(b−a) U(a) + ∫ heat(b−s) P div σ(s)`，零波按原 source 约定消元。

`UnifiedHeatWrite` 先由完整 normed source 生成整向量 `forcingCLM`、真实热作用后的可积
forcing，再将上述等式提升为整个 H⁻⁴ 载体上的 Bochner Duhamel。实际积分区间内热时间
精确为 `b−s`。`heatForcing_generated_next` 保留整个 forcing kernel 的原时钟平移，
`source_generated_next` 计算原 compiler target 的初值读出。没有增添 σ 经典导数或 Smooth
前提；该源作用实现不单独宣称原物理高阶控制。

`TemporalActionCompression` 的真实时间平移作用于 L²(ℝ;E)。`HeatPulseDilation` 从
`a > 0` 生成脉冲 `jₐ(v)(s)=1_{s≥0}√(2a)e^(−as)v`；它是复线性等距嵌入，adjoint 是
范数不增的左逆。`jₐ* Tₜ jₐ=e^(−at)` 对 `t≥0` 成立，负时间端口保留全部耗散能量。
`HeatSourceDilation` 逐波消元原 `a=νλₖ`，生成完整 ℓ²(L²(ℝ;ℂ³)) 上的 unitary 平移；
整个原热半群由一个有界 adjoint 读回，不依赖逐波无界逆。

`HeatPulseContinuity` 直接消费 Mathlib 的连续测度保持平移。`UnifiedDilationWrite.kernel`
将原完整 σ 的实际 forcing 写成 `T_(b−s) j(forcing(s))`，原预算支付完整 Bochner 可积性。
`window_read` 通过同一个有界 adjoint 读取积分，严格恢复原 H⁻⁴ Duhamel 状态。
`window_generated_next` 则证明原 clockAdvance 换锚后的完整 ambient 窗口等于原 compiler
target 的窗口，`generated_next_initial` 计算 target 初值。窗口换锚的等式不声称丢弃或重置
原历史。该分支闭合实际作用表示；统一全阶口的 Smooth 消费仍按 active card 的源表示责任。

## 权威源码

- [正核完成化](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PositiveKernelCarrier.lean)、
  [原完整 Gram](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/StressPairingCarrier.lean)、
  [canonical 四电流](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/HilbertDiracCurrent.lean)
- [保配对等距传递](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/ResolvedPairingTransfer.lean)、
  [原后继完整差分](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PairedCarrierRegeneration.lean)
- [完整载体时间 jets](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PairedCarrierJets.lean)、
  [两槽实际求导](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PairedDifferentialAction.lean)、
  [直接时间 Lp 消费](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PairedCarrierControl.lean)
- [整个恢复区间的完整配对](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryPairedCarrier.lean)、
  [配对的实际动量与修正](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryPairedAction.lean)

- [完整 canonical dual](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PairedDualCarrier.lean)、
  [完整配对实际写入](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PairedCompleteWrite.lean)
- [原 wholeTangent 的强速度写入](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/ReceiptStrongVelocityWrite.lean)、
  [首 receipt 完整配对接缝](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/ReentryPairedCarrier.lean)、
  [从零时起的实际配对积分](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/ReentryCompleteWrite.lean)
- [跨时源核](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryJointTimeKernel.lean)、
  [全 U 与原 σ 读出](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeGramReadout.lean)、
  [真实双槽作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeGramAction.lean)、
  [完整作用写入](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeGramWrite.lean)、
  [压力、修正与原 next](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeGramForce.lean)
- [同核 canonical 程序](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeCanonical.lean)、
  [原整账及框架实际作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryRootActionSplice.lean)、
  [原全时空强收敛](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeStrongRefinement.lean)、
  [原时间测度与 Duhamel](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeGramMeasured.lean)
- [全部原波的真实动量积分](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeMomentumWrite.lean)
- [完整 canonical 写入](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeCanonicalWrite.lean)、
  [同核正交读出](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeBackgroundProjection.lean)、
  [物理 L² 读出](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimePhysicalReadout.lean)、
  [完整状态及原窗口消费](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeWholeReadout.lean)、
  [原 canonical 时间类消费](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryTimeCanonicalControl.lean)
- [完整 σ 到统一 primitive](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedSourceActionFeed.lean)、
  [原 cofinal 动量](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedCofinalActionFeed.lean)、
  [无需 caller-stress 的原源接线](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedRootActionFeed.lean)
- [共享微分口消费完整源作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedSourceDerivative.lean)
- [原单次 macro 作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedMacroActionFeed.lean)、
  [原实际历史 fold](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedActionHistory.lean)、
  [全历史 σ 动量与原 next](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedGlobalActionFeed.lean)
- [全波应力 Hilbert 载体](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/CompleteStressCarrier.lean)、
  [完整应力的实际动量作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/CompleteStressAction.lean)、
  [原 Root／Macro 完整 σ](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedStressSource.lean)、
  [共同全历史 pair](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedGlobalStressSource.lean)、
  [完整 normed 源的实际 writer 消费](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedCompleteSource.lean)
- [原热作用的共享指数实现](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedHeatAction.lean)、
  [原全波 Duhamel](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedGlobalDuhamel.lean)、
  [完整 Bochner 热写入与原 next](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedHeatWrite.lean)
- [完整时间平移及残余端口](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/TemporalActionCompression.lean)、
  [原热脉冲](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/HeatPulseDilation.lean)、
  [全波源作用表示](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/HeatSourceDilation.lean)、
  [真实平移的连续性](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/HeatPulseContinuity.lean)、
  [同源完整写入与原 next](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedDilationWrite.lean)
