# 原生无条件湍流方程与已生成范数控制

> 稳定机制卡。固定源的标准 NS 分支判定见
> [active route](../../handoffs/navier-stokes-native-clock-active-route.md)；
> 原生全阶控制的施工状态见[同源演化接收](../../handoffs/navier-stokes-native-regularity-active-route.md)；
> [首次总演化签收](../../archive/navier-stokes-native-turbulence-total-evolution-checkpoint-2026-08-10.md)
> 保留历史合同。

本卡的对象是原生无条件湍流方程。原生湍流总演化已经闭合；其完成条件不要求选择标准 NS 的 old 支。
`sourceGeneratedNativeBoundaryReachabilityAnswer initial` 从原
source 生成 old 全局物理轨道或完整 revised law、实际宏步与恢复 receipt；两支都能继续消费。
原宏谱系的物理时钟每步大于 `1/2`，其 `globalAbsoluteVelocityTrajectory` 已覆盖全部绝对时间，
每个 Fourier 行连续。这里的全时路径和逐行连续性不要求动能缺陷为零。

`NativeAccumulation/NormControl/` 进一步把已付的动能等式、完整 Euclidean 范数身份和同源
拼接直接送到这些原消费者。它保留 `nativeTemporalRoot initial`、原 source、原物理时间、
实际 contact 和 literal recovery next；属于从属数学提取与输运，不登记新的 controller advance。

## 原生修正项的全频统一控制

`NormControl/Turbulence/` 直接控制原 `nativeTurbulenceCorrectionAt`，并将控制后的完整载体写回
原 `law.fourierLaw`。令 `K₀=‖puncturedWholeVelocityEuclideanState initial.initialState‖²`，
`S₄=Σ_{k≠0}|k|⁻⁴`，后者的三维可和性由原格点内核支付。

```text
T_F(ω)(k) = P_F N(ω)(k) − N(P_F ω)(k)
W_F(ω)(k) = |k|⁻⁴ T_F(ω)(k),   W_F(ω)(0)=0

|k|⁴ W_F(ω)(k) = T_F(ω)(k)                         每一原 Fourier 行精确还原
Σ_{k≠0} |k|⁻⁸ ‖T_F(ω)(k)‖²_ℂ³ ≤ 3(72π²K₀)² S₄  完整物理 H⁻⁴ 范数平方
```

统一界不依赖模式表 F、原微步 index 或已生成宏谱系的 macroIndex。输入相互作用保留完整场；
没有有限输入支撑、全涡量上界、零修正或零动能缺陷前提。这里的 H⁻⁴ 按整数 Fourier 频率定义；
系数三来自既有 sup-coordinate 到物理 Euclidean 坐标的完整范数转换。

四阶权重由原 curl/Leray 输出二阶增长与已付的 `S₄` 共同确定。`wholeCorrection_reconstruct`
证明全部原行都可精确读回；`native_equation_controlled` 在同一源选块、同一 receipt 上同时交付：

```text
∂t(P_F ω)(k) = Gν(P_F ω)(k) + |k|⁴ W_F(ω)(k)   原方程，a.e. 物理时间
完整 W_F 的物理范数平方 ≤ 同一源预算            该 receipt 的每个时刻
```

`source_generated_boundary_control initial` 只收原 initial，直接消费原 sealed answer：
old 分支的任意有限时窗、revised 分支的全部原微 receipt 与 literal recovery receipt 都获同一界。
`macro_wholeCorrection_norm_sq_le` 还覆盖任意原宏谱系中的所有原微 receipt。
原非零 closed-triad 修正通过还原检查，故本控制没有消去已发生的原生修正。

本节签收的是原生修正的完整 H⁻⁴ 统一界；不将这枚明确范数改名为任意正阶 Sobolev 范数的统一界。

## 原生速度场与观测量的统一界

令 `U₀ = ‖puncturedWholeVelocityEuclideanState initial.initialState‖`。
这是原完整物理速度的 Fourier ℓ² 范数，平方为源码不含 `1/2` 的 kinetic mass。

| 原消费者 | 已证明的范数控制 |
| --- | --- |
| 原 whole receipt、任意累计有限 prefix | 每个原物理时刻的速度范数 ≤ `U₀` |
| 累积前原路径、累积点与原 endpoint 恢复路径 | 同一界覆盖完整拼接，包括累积点本身 |
| 实际 macro step 与其 literal next | 全部 stage 速度及 next 初始速度范数 ≤ current 的初始速度范数 |
| 原 infinite macro lineage | `∀ time : ℝ, ‖lineage.globalAbsoluteVelocityTrajectory time‖ ≤ U₀` |
| 原 sealed boundary answer | old 全局轨道，或 revised 宏步及其恢复 receipt，均继承 `U₀` |

最后一行的公开口是
`NativeNormControl.source_generated_boundary_velocity_control initial`。
它直接读取原 answer 的 `fold`，只收原 `initial`；没有 caller branch、elapsed bound、
zero-defect、范数预算或替换路径。无限宏谱系的结论消费原有 lineage 及其物理路径，
没有把 completed-graph audit 改造为 source authority。

这也生成两类通用观测量控制：

```text
任意有界线性读出 A：
  ∀ t, ‖A(U(t))‖ ≤ ‖A‖ U₀。

任意固定有限 Fourier 库 F、其上的任意连续范数值观测 Φ：
  ∃ C, ∀ t, ‖Φ(U(t)|F)‖ ≤ C。
```

第二口覆盖固定有限库存上的各阶加权范数和连续非线性读出；界允许依赖 `F` 与 `Φ`。
第一口也允许无限维目标。它们分别由 `global_read_norm_le` 与
`finite_observation_bddAbove` 给出。

## 承重机制

1. [原动能作用](kinetic-source-control.md)已从完整 nonlinear cancellation 和原 receipt 生成
   `K(t) ≤ K(initial) exp(−2ν(2π)²t)`。`Physical.lean` 的 `receipt_velocity_norm_le` 消费时间非负与
   `puncturedWholeVelocityEuclideanState_norm_sq`，得到准确的物理速度范数界。
2. 原 `PhysicalRightTrace` 已证明恢复路径的完整 Euclidean 范数平方受同一 weak endpoint
   控制；canonical endpoint 又受原 contact 控制。这复用原完整有限和到整和的证明，
   不引入 sup-coordinate 转换的额外因子。
3. `Splice` 消费原 pre/prefix、absolute/local 以及 terminal/next 等式，把界穿过同一
   accumulation interface。正时间 H¹ recovery 仍是原 endpoint 路径的实际截面。
4. `Global` 沿原 macro step 归纳，使用原有限 prefix 的稳定化定义读取同一全时路径。
   `Native` 让原 sealed answer 的两支直接消费该界。
5. `Observations` 将原 kinetic ball 经有界线性映射送入目标；有限维连续观察的界由该
   紧球生成，不由 caller 提供。

因此原生闭合包含实际物理演化、同源修订和可跨接口复用的完整速度界，不能缩写成
“只给出一个后继”或“尚待固定 butterfly 选支才有原生演化”。

## 原发生的完整通量、压力与作用

`NativeAccumulation/SourceReadout/` 从原完整速度 `U = BiotSavart(ω)` 生成全部有序对的
负动量通量；没有有限输入库存或反求应力：

```text
Qᵢⱼ(U)(k) = −Σₚ Uⱼ(p) Uᵢ(k−p)
τ_F(ω) = P_F Q(U) − Q(P_F U)
p_Q(k) = Σᵢⱼ kᵢ kⱼ Qᵢⱼ(k) / |k|²，p_Q(0)=0

div Q(U) = 原 whole velocity nonlinearity
curl(div Q(U)) = 原 whole vorticity nonlinearity
curl(div τ_F(ω)) = nativeTurbulenceCorrectionAt F ω
```

`MomentumFlux` 由完整 ℓ² Cauchy–Schwarz 支付每个输出的绝对可和性和张量对称性。
同一物理 kinetic mass `K` 给出 `|Qᵢⱼ(k)|≤K`、`|τ_F,ᵢⱼ(k)|≤2K`，覆盖零频、全部九个
坐标和全部原微 receipt；`Receipt.occurrence_stress_norm_le` 将预算沿原 actual next 送回
原 initial 的速度平方。这里保留零频应力，不能因其 curl-div 为零便删除平均动量通量。

`StressAlgebra` 的原散度与 curl-div 是完整系数乘积拓扑上的连续线性作用。
`Action.source_momentum_action` 将同一 `Q` 分解成 Leray 作用和上述压力梯度，再保留原黏性项。
`p_Q` 是由不可压缩作用生成的零均值 Fourier 压力坐标；它没有被认同为旧
`NativeFluidMediumSource.pressureAt := 0` 记录。

`TimeAction` 消费原 heat-Duhamel 路径，在 receipt 的每个物理时刻生成实际 Fourier 速度导数；
该延拓在整段原物理区间上逐行等于原 wholePath。任意有限物理观察的时间导数由同一完整作用
生成。有限性属于观察库存，不施加在 `Q` 的输入相互作用上。
`Receipt.occurrence_vorticity_action` 直接消费原
`generatedWholeRestartNativeActualOccurrence initial n` 的目标 contact prefix。
因此 current、原 contact 时间、原 next 和作用方程共用一枚实际 receipt。
`TimeAction.occurrence_velocity_write` 进一步将完整动量作用按原 contact 时间积分，精确返回
原 current 到 literal next 的每个非零速度行之差。

`SourceReadout/Material` 将这枚 actual receipt 的时间导数送入原 canonical 多项式表示。
primal 与 dual 的两项实际响应共同生成 Dirac 电流导数，读回原速度 tangent；同一时刻的电流值
亦读回原速度，canonical 配对逐时保持。这里的有限库存选择原场的物理观察，完整作用输入仍由原
whole receipt 支付。这是原 NS 作用的依赖坐标实现，没有覆写 Cauchy 截面或宣称母 Dirac-dual Euler 方程。

`CofinalStress.sourceGeneratedCofinalStress initial` 又细化原
`sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial.subsequence`，同时生成全部
应力坐标的共同极限 `σ`。它严格保留原 kinetic/velocity 两个弱端点，原速度非线性、涡量非线性
和压力分别趋向 `div σ`、`curl(div σ)` 与 `p_σ`；预算仍来自原 initial contact。
`StressEnergy` 从同一 source 的 Fourier reality 与完整可和性读回零频实迹：

```text
Σᵢ Re Qᵢᵢ(0) = −原 punctured kinetic mass
Σᵢ Re σᵢᵢ(0) = −原 wholeRestartKineticMassLimit
−Σᵢ Re σᵢᵢ(0) − ‖原 canonical kineticEndpoint‖² = 原 kineticEndpointDefect
```

因此原 scalar 能量账是同一完整应力的读出。最后一行保留原 kinetic endpoint；没有替换成另一枚
velocity endpoint receipt。这首次把完整二次作用带过原 cofinal 接口；没有另选速度端点，也没有假设
`σ=Q(U_endpoint)`。
`SourceReadout/Cofinal/` 进一步从同一原发生生成应力缺陷的完整责任。加权 Biot–Savart
在原 transverse 载体上的等距性将原 kinetic/velocity 两个端点的范数精确认同。
原有子序列上的速度涨落 `r_n=U_n−U_endpoint` 因而满足 `‖r_n‖²→δ`，其中 δ 就是上述原
canonical kinetic endpoint defect。完整卷积的固定一侧由原 Hilbert 测试向量实现，
故混合项直接消费原 weak-tendsto；没有新的求和假设或端点选择。

```text
Q(r_n) → R = σ − Q(U_endpoint)
∀ k,i,j, |Rᵢⱼ(k)| ≤ δ
−Σᵢ Re Rᵢᵢ(0) = δ
K((k,i),(l,j)) = −Rᵢⱼ(k−l)                         完整正半定核
lim Nω_n = curl div Q(U_endpoint) + curl div R      原实际作用分解
```

正性由原涨落全部平移分量的 Gram 核生成，再沿原 cofinal refinement 取极限；
`Matrix.PosSemidef` 在完整无限频率×坐标载体上量化任意有限支持测试。
`stressDefect_eq_zero_of_kineticDefect_zero` 只消费原零缺陷分支，整个构造不预选此分支。
这将原 scalar 缺陷变成可消费的完整二次作用与正协方差；高阶空间控制及同源后继作用继续由 active card 管理。
所签收的是完整系数作用与同源极限，不能把乘积拓扑连续性改名为任意正阶 Sobolev 有界性。

这些从属源 producer 保持既有 root、整账 compiler 和 next；CU 母作用的认同与全阶时空终口
继续由[原生全阶 active card](../../handoffs/navier-stokes-native-regularity-active-route.md)管理。

## 原完整生成器的空间作用

原完整发生已直接消费 Stage9 泛型能量、原 Fourier ℓ¹ 时间账户与原极限生成器，接通 U/ω/T_F
的全阶时空消费及 cofinal 实际应力／后继作用；机制只见
[原生成器的全阶时空控制](native-source-spatial-all-order-control.md)。

`SourceAction/Structure/Translation` 将原半周期对称构造扩展到任意三维空间位移 a。
原 Fourier character `exp(2π i k·a)` 直接作用于原完整 ℓ² 载体；其加法律支付完整卷积作用的
交换，单位模支付原梯度账户、reality 和 transversality 的保持。

`receiptShift` 作用于原 receipt 的全部字段：`stateLimit`、transverse limit、`wholePath`、
whole tangent、实际 row extension、绝对连续性与原 Duhamel 更新。它不是另选解或另补一个场。
`translatedSeed_level/duration` 保留源生成 level 和 horizon；原 compiler 在该作用后的 seed 上生成
`translatedReplay`，原同初值唯一性直接给出其完整路径为原路径的平移。

`scalarField_shift`、`realField_shift` 与 `receiptField_shift` 经全 Fourier 基认回真实 Haar 平移。
`nativeCorrection_shift` 同时保留原输入／输出 filter 交换子。
`receiptShift_spatial_derivative` 将完整源作用的导数认回已生成的强 L² 空间 jet；
`physical_integral_shift` 在每个原物理子区间交换完整 impulse。
`occurrence_physical_write` 最后在原 occurrence 已选接触时间，读取原 literal next 的平移。

这一源作用相容不依赖选定的物质表示。进入 CU 已付全阶控制的实际源实现责任仍由 active card 维护。

## 完整物理空间与 canonical 配对的同源作用

`SourceReadout/Physical/Fourier` 用 normalized 三环面 Fourier Hilbert basis 的逆等距映射，
从全部原系数生成实 L² 速度场。原 Fourier reality 生成实值性，全部系数精确读回；
Parseval 使用 Euclidean 三维范数，没有额外维数因子。实际乘积 `−UᵢUⱼ ∈ L¹` 的全部
Fourier 系数就是上节原 `Q`，其有序对和由完整 L² 乘积公式支付。
`EndpointVelocity` 将原非零频率 Euclidean velocity carrier 零延拓到全部频率；
它保留原质量、reality 和每个速度坐标，输入已有 velocity endpoint 时不再施加 Biot–Savart。

`WholeTimeAction` 将原 receipt 的完整 weighted tangent 经既有 kinetic-to-velocity CLM
读到 L² 时间速度载体，逐行认回原 momentum action。其 Bochner 积分等于原 whole velocity
在每个实际时刻的增量；原 source 自身产生此切向量、积分性和原函数。
`Physical/TimeAction` 让相同积分进入上述完整物理空间；所得 Banach 强导数 a.e. 成立，
`occurrence_physical_write` 精确返回原 current 到 literal next 的全空间速度差。

`Physical/Gradient` 从原 ω 生成全部九个完整频谱导数字段：

```text
Ĝⱼᵢ(k) = i 2π kⱼ Ûᵢ(k)
∫ χₖ Gⱼᵢ = −∫ (i 2π kⱼ χₖ) Uᵢ      每个全频 Fourier 测试
curl G = 原 ω 的完整 L² 实现
Σⱼᵢ ‖Gⱼᵢ‖²_L² = 原 wholeVorticityEuclideanMass ω
```

原 receipt 供应 transverse、零频与 reality，梯度各项实值 a.e.。
这生成了完整 L² 频谱一阶导数及其分部积分责任，未将 L² 代表元认作处处经典导数。

`Physical/Material` 将原 canonical 多项式表示直接作用在该完整物理场上，
不构造或覆盖任何 CU configuration。全部 primal/dual 系数属于 L²；同一空间点的
canonical 配对保持，空间 Dirac 电流精确为 U，时间电流 `j₀=2+|U|²/8` 属于 L¹。
原整场加速度 A 产生 `d/dt ∫j₀ = ⟪U,A⟫_L²/4`。`Physical/Dissipation` 又消费
原非线性消去和 kinetic primitive，得到任意原 receipt 前缀的精确作用：

```text
‖U(t)‖²_L² + 2ν ∫₀ᵗ Σⱼᵢ ‖Gⱼᵢ(s)‖²_L² ds = ‖U(0)‖²_L²
∫ j₀(t) + (ν/4) ∫₀ᵗ Σⱼᵢ ‖Gⱼᵢ(s)‖²_L² ds = ∫ j₀(0)
```

`occurrence_material_charge_write` 只接收原 current 和原微步 index，
由同一原 occurrence 生成时间、完整字段和 literal next 的电流账。
`Physical/QuadraticAction` 用 Hölder 连续双线性映射把原整场时间作用送到完整 L¹ 应力和
时间电流，生成实际的双项乘积导数。令 `I=∫A` 为上述原物理 impulse，`B(U,V)=−U⊗V`，有：

```text
Q(U+I) − Q(U) = B(U,I) + B(I,U) + B(I,I)
j₀(U+I) − j₀(U) = (U·I)/4 + |I|²/8
```

这两式在完整 L¹ 场中成立；`stress_fourier` 将该应力认回原全频 Q，
`occurrence_quadratic_write` 用原 occurrence 的同一 impulse 直接生成 literal next 的两项增量。
二次 impulse 项完整保留，没有以一阶响应替代实际更新。
这是同源作用与 canonical 配对的完整物理实现；实际母 Dirac-dual Euler commuting
与全阶紧域控制继续见唯一 active card。

## 原 canonical 电流的源生 coframe 作用坐标

`Physical/CanonicalCoframe` 从同一原速度值生成：

```text
ρ = 2 + |U|²/8 > 0，c = ρ^(1/3)
e(U) = diag(c²,c⁻¹,c⁻¹,c⁻¹)
det e = c⁻¹ > 0，原 temporal principal scalar = c⁻⁴ ≠ 0
```

这是原 U 的源依赖读出，不构造或覆盖一份 CU 九字段 configuration。
canonical matter/dual 原值与配对保持；裸 Dirac 电流仍为 `(ρ,U)`。
消费现行母作用中的 `inverseCoframeDiracGamma` 和体积密度后，精确得到：

```text
Jμ = |det e| Re(dual(Γμ(e) matter)) = (1,U)
Pμ = |det e| Re(dual(i Γμ(e) (i matter))) = (−1,−U)
```

`phaseVector_eq_mother` 将这里的相位向量直接认回原 `matterDifferentialVariationVector`，
不是另命名一套作用。`source_densitizedCurrent_divergence` 对每个完整 Fourier 测试消费
原 Biot–Savart 横向性；时间密度恒为 1，物理时间坐标保持。
`occurrence_phaseMomentum_write` 再由同一原 impulse 得到 literal next 的完整空间相位动量增量。

该源生 coframe 与作用坐标闭合了相位动量这一依赖面；其完整一阶动力响应由下述 producer
消费。指定已激活 CU 场的源身份保持。

## 原 receipt 生成的完整物质 jet 作用

`Physical/MaterialAction/SourceJet` 的入口是原 receipt。空间项直接取完整 L² 频谱梯度，
时间项直接取原 whole tangent 的完整物理实现。`gradient_trace` 在完整 L² 载体证明九项梯度的迹为零，
`receiptJet_divergence` 将它送入同一源的一阶 jet；没有输入 phase-zero certificate。

设 `v=U/4`、`H=1+v·σ`。完整 exterior-matter 嵌入由
`CoframeAction.source_matter` 精确认回原 canonical matter；12 个时空／color 系数作用于原有
`sourceColorP286Generator` 及两枚 occupied exterior-color 状态。`generator_action` 消费原全载体
`sourceColorDiracMatter_generator`，不靠投影等式替代完整作用。

`PauliControl.control` 显式计算所有系数，其分母为恒正的 `3+|v|²`。对任意矩阵响应 `R`：

```text
wholeAction(v, control(v,R)) = lowerMatter(R) − phaseResidual(v,R)·lowerMatter(1)
phaseResidual(v,R) = Re scalar(R) + v·Re vector(R)
```

`DiagonalCoframe.spin_connection` 直接计算原 Levi–Civita／Lorentz-spin 生成器。
`JetAction.coframe_hasDerivAt` 证明这里的 coframe jet 正是源依赖映射的链式导数。
`SpinConnection.spin_response` 消费原 Dirac spin lift，精确生成：

```text
zμ = ∂μ log c = 4(v·∂μv)/(3ρ)
C₀(e)⁻¹ · iΓμ(e)Ωμ(e,∂e) matter = −(3/2) z₀ matter
freeResponse = ∂ₜH − (3/2)z₀H + ρ Σᵢ σᵢ ∂ᵢH
phaseResidual(v,freeResponse) = ρ div v
```

`PauliJet.controlled_response` 以 `−freeResponse` 生成 connection，抵消完整自由响应。
`CoframeAction.connection` 的时间／空间系数由同一 coframe 补偿，且
`connection_vacuum_zero` 证明它保持原 scalar 真空。`JetAction.actual_inverse_response`
使用原 `currentCoframeMatterTemporalPrincipalInverse`，保留且只保留精确散度项。
`SourceJet.receipt_kineticVector_zero` 再由原不可压缩性无条件支付它，得到完整 exterior-matter
动力向量在空间 a.e. 为零；`occurrence_kineticVector_zero` 直接消费原 occurrence 生成到
literal next contact 的 receipt。

同一链的 canonical-dual 消费者为 `MaterialAction/SourceAdjoint`。`AdjointPrincipal` 复用原
`fullCanonicalDiracAdjoint_gamma`、`fullCanonicalDiracAdjoint_spinConnection`、
`fullCanonicalDiracAdjoint_motherLieConnection` 的全载体定理，
`MomentumJet` 直接读取真实体积主符号系数：

```text
cμ = |det e| / eμμ = (ρ⁻¹,1,1,1)
Σμ ∂μcμ · barψ(iγμ χ) = −3z₀ |det e| barψ(C₀(e)χ)
Σμ barψ([Cμ(e),Ωμ]χ) = −3z₀ barψ(C₀(e)χ)
```

`SourceAdjoint.momentum_hasDerivAt` 通过原 `NativeMaterialAction.dual_hasDerivAt` 和系数的真实导数，
证明完整动量的两项乘积求导。spin 对易差与体积主符号散度相消，内部 mother Lie 作用与 gamma
交换；于是 `AdjointAction.dual_eq_primal_adjoint` 在整个 exterior-matter 载体证明：

```text
dualKinetic = |det e| · fullCanonicalDiracAdjoint(primalKinetic)
```

原 scalar 真空消灭 occupied color 的 Yukawa 向量，原 canonical dual 消灭任意 scalar 的 Yukawa 输出。
`SourceAdjoint.receipt_diracDual_equations` 因而从同一原 receipt 同时生成 primal 与 canonical-dual
物质方程，对空间 a.e. 的同一集合及任意完整 matter variation 成立。

### 同源 Cartan 反作用与实际应力

`MaterialAction/Cartan/Source` 由同一 canonical matter/dual 计算原 matter-Lorentz 变分的完整
24 维线性泛函。原 W13 对偶直接生成 action-signed spin 三形式，原 KIN3 反解 torsion，
KIN2 反解 contorsion，KIN4 把它加回原 Levi–Civita connection。`connection_eq_mother`
证明：每份延拓同一 coframe jet、matter 与 dual 的完整场，其原 repaired-action Cartan producer
限制到这里都得到这枚 connection；没有请求 Cartan stationarity 证书。

`SpinSupport → TorsionSupport → ContorsionSupport` 消费 canonical 电流的实性及上述原反解，
生成 `qμ,ab=0`（当 μ=a 或 b）。这一三指标互异支撑同时支付 Clifford 对易和完整响应的相位条件。
`Response.response_inverse` 计算实际时间主符号逆算子作用后的 2×2 响应 R(U)，
`response_phase_zero` 无条件证明其相位为零。`Compensation` 用原 color 求解器生成 −R(U) 的作用，
在整个 exterior-matter 载体抵消 Cartan 增量，并通过 canonical 伴随保留完整 dual 方程。

`Cartan/Jet.receipt_diracDual_cartan_equations` 因而直接消费实际 Cartan connection、总 color connection、
原真空及原 receipt 的完整 jet，生成同一 a.e. 集合上的 primal／canonical-dual 物质方程。
Cartan 与 color 两项均实际保留在 connection 中；没有把它们作为零对象删除。

`MaterialAction/Stress/{Inverse,Functional,Source}` 对原 coframe matter 密度求真实 Fréchet 导数。
它使用原矩阵逆的导数、体积及完整物质配对，给出全部 16 个 coframe 方向的应力。
`Cartan/Stress` 消费已闭合的物质方程来支付原密度的内层零值，并证明：

```text
实际 Cartan matter-stress(U,∂U)
  = Levi–Civita／color jet stress(U,∂U) + reactionStress(U)
reactionStress(U) = Dₑ [ |det e| · Re barψ iΓμ(e) (Cartan增量 + color补偿)μ ]
```

这里纯 U 反作用是原母作用的真实变分部分；它到原 Q 的作用对应由下面的源生构造支付。
这是源生一阶 jet 上的实际 Dirac–Cartan 作用 producer。原 U、时间、canonical 配对和 next 都由
既有源读取；L² 时间／空间 jet 没有被升格为任意阶经典场或九场联立 on-shell。
验证及正阶控制的当前责任只在唯一 active card 维护。

### 原 Q 与母本构项的实际作用对应

`PauliPairing` 把完整 exterior-matter 配对精确消元为原 2×2 color block 的配对。
`Cartan/Coordinates` 通过原 Cartan 正向图及逆映射唯一性，计算同一实际 contorsion 的全部坐标。
`Cartan/{Constitutive,StressLaw}` 随后生成原反作用应力的闭式。设 `s=|v|²`、`v=U/4`：

```text
reactionStressᵢⱼ = F(s)vᵢvⱼ − P(s)δᵢⱼ
F(s) = (3+2s+3s²)/(3+s) > 0，P(s) = s(1−s)²/(3+s)
```

`Constitutive/Color` 从同一 U 计算原 SU2 作用的径向零响应方向，其时间系数为
`−4s v/(3+s)`，空间矩阵为 `v⊗v + s(s−1)/(3+s)·I`。
全 exterior-matter 向量响应恒零；`ColorAction.dual_eq_adjoint` 在任意完整 variation 上生成
canonical-dual 响应的同步消失。该方向以源计算系数 `c²/2·(−16/F(s)−1)` 写入真实 gauge connection。
原 matter、dual、coframe 和 Cartan 反作用保持；没有另选 independent dual。

`Constitutive/Flux` 对这一实际增量的原 coframe-matter 密度求 Fréchet 导数，得到：

```text
constitutiveStress(U) = −U⊗U + p(U)I
p(U) = 16s(1−s)²/(3+2s+3s²)，0 ≤ p(U) ≤ |U|²/3
```

`Constitutive/Jet` 将该 connection 与原 jet connection 真正相加，再计算原母 covariant derivative
和 canonical 动量方程，保持同一 receipt 的 primal／dual 方程。完整应力等于
`jetStress(U,∂U)−U⊗U+pI`；纯 U 部分的认同没有删除 jet 应力，也没有替代其余母作用通道。

`Constitutive/Fourier` 从原 L² 物理场生成这份应力的完整 L¹ 实现，原动能支付压力及其全部 Fourier
系数。原 curl-div 消去标量压力，直接认回原全频涡量非线性。`Constitutive/Occurrence` 再证明：
保持 reality 的原 filter 交换子精确给出 `nativeTurbulenceCorrectionAt`，同源作用积分写回
原 occurrence 的 current 与原 compiler literal next。这里认同的是母应力中原 Q 与 filter 作用的
来源；没有把它混入 `NativeFluidMediumSource` 的独立 `T_medium` 槽，也没有认同 `Fluid.mediumCorrection`。

### 完整母色作用的源生 L² 消费

`MaterialAction/JetControl/Color` 仍使用原全部 12 个 color 方向。对任意响应 R，它把实向量、
虚向量和标量响应重新分配到时间、对称空间和反对称空间系数；分母是恒正的 `1+|v|²` 与
`3+|v|²`。`control_action` 保持原完整响应，唯一相位残差仍由原不可压缩性支付。

对原自由 jet，设 `w=curl v`、`q=∂ₜv−(v·∂ₜv)/(1+s)·v`、`e=4(v·w)/(3+s)`，得到：

```text
A₀ = −2w + ev
Aᵢⱼ = eδᵢⱼ + (1/2)εᵢⱼₖqₖ − 2wᵢvⱼ
|q|² ≤ |∂ₜv|²
Σⱼ A₀ⱼ² ≤ 4|w|²
Σᵢⱼ Aᵢⱼ² ≤ (3/2)|∂ₜv|² + 5|v|²|w|²
```

这些是原 color 作用的显式系数，不是额外的光滑场。`Energy.colorBlock_energy` 精确计算完整
occupied block 的范数平方为 `ρ|Aᵢ|²`；原 coframe 空间补偿因子 `ρ⁻¹` 使实际物质作用具有
不依赖速度幅值的切向量／curl 界。固定线性嵌入 `materialEmbedding` 把该估计送到全
`MatterCoordinateCarrier`，没有只保留一个物质投影。

`Field` 由这些实际值生成完整 L² 物质场。`Receipt` 读取原 whole tangent 和全部频谱梯度，
通过原 Biot–Savart／curl 恢复认回原 ω，证明：

```text
Σᵢ ‖actualMotherColorResponseᵢ‖²_L²
  ≤ ‖materialEmbedding‖² · ((3/64)‖∂ₜU‖²_L² + (5/32)‖ω‖²_L²).
```

`Jet` 把这套系数写入同一实际 Cartan／color connection。完整 primal 与 canonical-dual 方程、
原真空及原密度的 coframe 变分都保持，完整应力仍精确分为新的 jet 项与 `−U⊗U+pI`。
上述 L² 界的对象是空间母色作用；其余增量由下述完整 covariant jet 链消费。

### 完整空间 covariant 物质 jet

`Constitutive/{Material,MaterialEnergy}` 将已生成 Cartan 反作用在完整源 matter 上的作用精确
消元为同一径向 color 响应。对全部空间方向，原 Cartan 加 color 补偿等于 `c²/2` 倍的原径向
响应；安装本构系数后，完整本构物质增量等于 `−8/(cF(s))·H·iKᵢ`。由此直接计算：

```text
Σᵢ energy(constitutiveMatterIncrementᵢ) = 128c s²/(3+2s+3s²) ≤ 8|U|².
```

这是完整物质向量的作用恒等式，不把 Lorentz 与 color 的全算子认作同一算子。
`JetControl/Geometry` 复用原 Clifford 全载体作用，计算真实 Levi–Civita 增量；原 log-coframe
导数由同一 U 与 jet 生成。其能量受完整一阶 jet 控制，无须追加速度幅值界。

`CovariantEnergy` 将原微分、Levi–Civita、color 与完整本构增量相加，精确认回
`JetControl/Jet.derivative`。`CovariantField` 生成全部物质坐标上的 L² 场；
`CovariantReceipt` 从原 receipt 的 whole tangent 与完整频谱梯度消元，使用原全频 enstrophy
支付空间梯度，得到：

```text
Σᵢ ‖Dᵢψ‖²_L² ≤ ‖materialEmbedding‖² ·
  (32‖U‖²_L² + (7/16)‖∂ₜU‖²_L² + 2‖ω‖²_L²).
```

该场的每一空间方向均 a.e. 等于同一实际 Cartan／color connection 的完整 covariant matter
derivative。

### 同源方程生成的四方向动力场

`JetControl/Densitized` 保留原体积与 inverse-coframe 系数，定义
`Eμ=|det e|·iΓμDμψ` 的完整物质坐标。空间方向的 `|det e|/eᵢ` 精确为 1，
所以 Eᵢ 是已控 Dᵢψ 上固定 Dirac 矩阵的作用。`DensitizedReceipt` 消费同一原 receipt
已闭合的物质方程及原真空 Yukawa 消去，生成 `E₀=−(E₁+E₂+E₃)`。

这给出全部四方向真实 L² 场，逐分量 a.e. 等于原作用求值，且 `ΣμEμ=0` 在完整 L²
载体内成立。令 `G=4Σᵢ‖iγᵢ‖²`（在固定全物质坐标上），则

```text
Σμ ‖Eμ‖²_L² ≤ G · ‖materialEmbedding‖² ·
  (32‖U‖²_L² + (7/16)‖∂ₜU‖²_L² + 2‖ω‖²_L²).
```

物理时间保持；这里控制的是母作用的原加权动力项，并未去除时间方向的原 coframe 权重。
更高阶演化的当前责任只在 active card 维护。

## 完整物质载体的忠实读回与导数相容

`MaterialAction/Readback/Material` 从原完整物质基底上的 color-dual 评价产生固定实线性映射 R。
在已有 canonical matter `ψ(U)` 上，R 精确返回原 U；去除固定背景的物质增量 M 是实连续线性映射，
且 `R∘M=id`。完整物质、canonical dual 与原作用保持，不替换原 Cauchy 截面。

`Differential.material_jet_readback` 对任意场函数和任意有限阶 n 证明：

```text
R(Dⁿ[ψ(U)]) = DⁿU。
ContDiffⁿ(ψ(U)) ↔ ContDiffⁿ(U)。
```

导数交换不接收光滑性 premise；连续线性左逆同时反射可微性，因此也处理 Lean 全定义导数的
非可微分支。光滑性自身没有由这一恒等式生成。
`Material.covariant_readback` 保留实际 connection：
`R(Dμψ)=∂μU+R(connectionμ·ψ)`，不把协变导数偷换成普通导数。

`Receipt.material` 是原完整物质坐标的 L² 场，R 的 L² 作用严格恢复原完整 U。
同一 M 消费原 whole tangent，实际时间导数和完整物质 impulse 写回原 contact 与 literal next。

`CUControl` 使用这个相同 R，直接消费 `Fields.history_compact_jet_bound`，把原全物质坐标的
已付界传给 `R(matterCoordinateEquiv(History.configuration n).matter)`；全阶紧域、各阶
`MemLp` 与范数界均覆盖 p=∞。这是原 CU 发生的实际读出。原 native 发生到受控载体的表示责任
仍由 active card 维护，不把读出算子相同当作两个发生已相同。

### 原空间平移生成真实物质导数

`Physical/Translation/Spectral` 直接生成全部频率上的相位作用
`a_k ↦ exp(i·2π·s·kᵢ) a_k`。相位范数为 1；已有平方可和频谱导数支付差商的可和支配，
生成完整 ℓ² 轨道的强导数。`Field.translate_eq_fourier` 用原 Haar 平移和完整 Fourier 基底
证明它正是 `f(x+s eᵢ)` 的真实 L² 作用。

`Material.source_hasDerivAt` 消费原 vorticity 已经支付的全部三个频谱梯度，把该强导数交给原完整
实速度场。`material_hasDerivAt` 再通过已证 M 和固定背景，生成同一 canonical 物质场的真实
空间导数。这里 s 是空间平移参数；物理时间仍由原 receipt 的 whole tangent 和原积分写回固定。

`receipt_rawDerivative` 精确认回母作用使用的原 raw jet；`connectionResponse_apply`
把既有完整 covariant L² 场分为这份实际空间导数和同一原 connection 的物质作用。
这一关系关闭了原一阶 jet 的空间作用表示，不增加独立的高阶 NS 估计义务。

## 原规范物质电流的完整动量读出

`MaterialAction/Gauge/Momentum` 从原 coframe、canonical matter/dual 及实际 SU7 外幂作用计算完整
P286 one-form 上的物质电流协向量。以原 `iσₐ` color 生成元作源生变分方向：时间方向乘以
原 ρ、空间方向乘以 4。原体积／逆 coframe 系数生成

```text
J⁰ₐ = −Uₐ
Jⁱₐ = −UᵢUₐ + (|U|²/2−8)δᵢₐ。
```

这里改变的是同一规范协向量的变分方向，物理时间保持。
`Variation.gaugeDensity_hasDerivAt` 从已经认回原母物质部门的密度证明真实的一阶变分，
输入同一原 jet 和完整规范 variation，不输入目标电流或作用认同。

`Fourier` 用已付 U∈L² 生成完整空间电流的 L¹ 载体；其 Fourier 系数为原 Q 加各向同性项。
复用原各向同性 curl-div 消去，返回原全频涡量非线性。该各向同性项是规范电流的读出，
介质压力身份继续遵循原接口。
`Occurrence.correction_action` 的 filter 交换子精确返回原 `nativeTurbulenceCorrectionAt`；
原积分作用与时间电流均写回同一 source occurrence 的 literal next。

这条关系属于原规范变分的物质部门。其与受控源表示的消费关系只由 active card 定位，
不会用 coframe 应力的 jet 项消失或完整九场方程作为隐含结论。

### 同一连接下的完整规范电流平衡

`Gauge/Ward` 复用原 SU7/P286 Lie representation 的 bracket 关系及完整 Dirac 内外作用对易，
从同一一阶 jet 生成带全部 Euler 项的 Noether 恒等式。对任意 P286 元素 X：

```text
D_X + dualEuler(X·ψ) = current([A,X]) + |det e|·dual(X·primalEuler)。
```

D_X 是原体积／逆 coframe 电流的完整乘积求导表达式，包含 canonical dual 与 primal 两项响应。
原 receipt 的两条物质方程及已付 Yukawa 消去使其成为
`Re D_X = current([A,X])`。交换子保留；本源不添加中心性假设。

`Gauge/Differential` 用原完整内部作用的实际配对、已有双侧物质导数和 coframe 动量求导证明
每个分量对可微物理路径的 `HasDerivAt`，再把这些分量之和交给同一 `receipt_current_balance`。
内部作用可能离开 occupied color 子空间；证明只使用原 dual 的精确评价，不把投影冒称全向量相等。
这些结果保留为物质表示资产；是否继续其 BF／本构消费，由全阶源表示的实际责任决定。

## 已有 CU 上游控制

[Stage9/CU](../physics/source-history-weak-actual-uniqueness.md#全历史全字段的全阶紧域控制) 的原完整
Smooth 场与 on-shell 更新已经生成全历史、全九字段、任意有限阶的紧时空域统一导数界。
`Fields.history_compact_jet_bound` 和 `Weak.actuals_compact_jet_bound` 显式提供这份已付控制。
这份已付控制与原生湍流控制各自保持实际源身份。

`PhysicsCore/Stage9CU/Fluid/` 已把这份控制直接送入原母源的流体读出。
对任意导数阶 `m`、紧时空域 `K`，有同一界覆盖全部原 history index 及五个通道：完整
空间 Dirac 电流、原点电流、原相对速度、curl 和由实际时间导数计算的残差。
`source_native_all_order_Lp_control` 同时给出各阶导数的 `MemLp` 及 `eLpNorm` 界，
包括 `p=∞`。界从既有光滑场、有限历史前缀和原 on-shell 后继恒等生成。

完整电流必须同时保留 primal 与 independent dual：

```text
jμ = Re(dual(γμ matter))
u_relative(t,x) = j_spatial(t,x) − j_spatial(t,0)
u_relative(t,x) + j_spatial(t,0) = j_spatial(t,x)
```

最后一式由 `Decomposition.relative_add_anchor` 支付。旧基点相对投影本身不能保留任意源的
常量速度分量。指定已激活 SpinPair 的四分量 Dirac 电流及相对速度均恒零，
对应声明见下节；这些具体读出的控制没有自动识别其他原生湍流场。

## 原生初值的生成发生与物质重建

原生初值本身已有上游生成链。当前 paid-medium 的具体入口沿用：

```text
butterflyFirstStackRow / butterflyFirstStackModes
→ butterflyFirstStackPhysicalState (-1) = stackedSeedState
→ stackedPhysicalSeed → stackedReplay → stackedReceipt
→ 源生成的短窗口 → stackedShortReceipt / stackedShortContact / stackedShortCurrent
→ concreteCounterexampleInitial → 原 native occurrence / current.next。
```

`ButterflyStackedSourceCurrent` 从原材料产生整条 receipt，不接收另一份完整未来。
`generatedWholeRestartNativeActualRootAt` 将每个有限深度的 responder、实际 next 与到达
历史放在同一生成口；`nativeTemporalRoot` 同时保留 finite/cofinal/post-cofinal 及原整账。

`InitialLift.cauchyData` 则先读取 `canonicalCauchyRestriction 0 activatedConfiguration`，
再用 Fourier 速度构造的 matter/dual 覆盖其中两个字段。它是额外的物质重建。
`Regression/SourceIdentity` 已严格证明：

```text
activated_dirac_current_zero：指定已激活 actual 的全部四分量 Dirac 电流 = 0
reconstructed_cauchy_ne_activated：∀ raw，cauchyData raw ≠ 该 actual 的原 Cauchy 截面
```

第二项直接消费重建的时间电流 `2+|u|²/8>0`。所以零时速度保真、canonical 配对和
重建的光滑性都不能把这次覆盖认作对指定已激活场的原始截面读取。
该结论只定位这份重建与指定 actual 的身份，不排除其他同源依赖面或实际发生。
已有全阶控制应经原发生的真实作用读出消费；重建引入的自洽责任不能倒算成原初值未生成。

## 同初值的完整母作用写入

`Fluid/Initial/` 已构造速度、涡量数值保真的物质表示：从原 finite Fourier source 的速度生成
color-doublet matter 和完整 canonical dual，不输入未来场、目标界或配对证书。
空间电流精确为输入 `u`，时间电流为 `2+|u|²/8>0`；primal/dual 光滑性由原速度生成。
`sourceAction_initial_velocity` 与 `sourceAction_initial_vorticity` 再将它们送过历史完整
作用响应，证明零时整片速度及涡量仍是原 source 的字段。该历史响应保留初值的结论有效；
现行 Dirac-dual 作用及实际 coframe 的时间响应由增强演化另行消费。

`Fluid/Evolution/` 已把这份重建的 Cauchy 数据送入现行母作用：完整场准备后，原
`algebraicCartanReduction` 重新生成反作用；共同的 `RepairedMatterResponseOperator`
再生成 primal/dual 的真实 holonomic 响应。源 coframe 的 temporal principal 非零由
`contact_noncharacteristic` 生成；`matterResponse_primal_euler` 与
`matterResponse_dual_euler` 消费同一响应 actual 的作用律，得到真实 Euler 零值。
`matterResponse_current_origin` 和 `contact_preserves_time` 保留原速度与物理时间。

`Evolution/Development.completeWrite` 直接消费原完整全场写入器，原依赖顺序是：

```text
原 finite Fourier source → prepared
→ 物质／独立 dual／标量的实际时间积分
→ P286 连接、本构与辅助场时间写入
→ 同场 Cartan／引力反作用 → 一枚四维 completeWrite。
```

`completeWrite_initial_current` 保留零时整片原始速度。两个物质字段均为全时空 C∞，
`completeWrite_matter_timeDerivative` 与 `completeWrite_dual_timeDerivative` 在每个实物理时间、
每个空间点、每个完整坐标证明其实际导数等于原输入生成的 action profile。
两条物质时间律所需的可积性、光滑性和非特征性从同源准备场生成，不是调用者的条件。

`Evolution/Regeneration` 再从同一输出计算完整 primal 方程，证明：

```text
该输出的 Dirac-dual forward vector = 0
↔ 输入场生成的物质速度 = 输出场重新生成的物质速度。
```

右边两项分别由同一次完整写入的输入、输出及原母作用计算；没有定义一个强制相消的外力。
这份等价式识别该重建的真实自洽责任，不断言第一写入已经满足它。
是否需要沿这份重建继续，须先由原发生的作用读出决定；当前责任只见
[唯一 active card](../../handoffs/navier-stokes-native-regularity-active-route.md)。
原 9C/CU 对其原完整源场及历史的闭合保持成立。

这里的 `mediumCorrection := ∂t curl(u_relative) − G(curl(u_relative))` 是实际场的计算残差；
`vorticity_residual_identity` 没有被当作独立方程 producer，也没有与原 `nativeTurbulenceCorrectionAt`
自动认同。两者的真实作用对应由上述原发生读出承担。

控制责任归于[共同根律的领域实现](../framework/authority/root-law-dependent-face-realization.md)：
从 exact occurrence、完整源载体与根作用生成依赖面的控制；目标界不是独立领域前提。
本轮已直接消费原生算子现有的完整速度、投影收缩、curl/Leray 与格点求和机制，
没有把另一枚具体 actual 的认同列为本节闭合的必要前提。

## 全阶输入与路径责任的精确回归

`NormControl/Regularity/Regression/InitialRegularity` 构造原总口真正接受的源：
在 `kₙ=(2ⁿ,0,0)` 及其负频放置横向幅值 `2⁻ⁿ`。它满足原零模、横向、Fourier reality 与 ℓ²
条件，并生成原 receipt；但每个选中频率的物理 H¹ 涡量质量恰为1，总和发散。
这定位的是旧全源类型在零时的正则性责任，不能据此否定固定平滑源。

`Regression/Revised` 则保留实际 sealed revised law 的原接触值：这些值在有限累计时间内的
涡量质量无统一界，因而不能逐点相同地成为紧时间窗上连续强涡量场的截面。
这没有证明任何固定源进入 revised 支；原较弱速度载体上的全时演化与恢复保持成立。
初值 lifting 的已证结果是数值保真及实际作用响应，不能单靠零时恒等式取得原发生的源身份。

## 独立的标准 NS 读出

`NormControl/Vorticity.lean` 保留准确判据：原 contact 的未加权全频涡量质量在每个有限时窗
统一有界，等价于原 elapsed 无界，再等价于原标准 global whole mild/Serrin 解存在。
该标准 NS 责任与本卡的原生总演化及修正控制分开，不作为原生方程是否闭合的验收条件。

## 源码与核验

源码以 `SaturationMonoid/NavierStokes/` 为根：

- `NativeAccumulation/NormControl/{Physical,Splice,Global,Observations,Native,Vorticity}.lean`。
- `NativeAccumulation/NormControl/Turbulence/{Rows,Actual,Whole,WholeActual,Law,Consumer}.lean`：
  原修正逐行控制、全频载体、实际演化、原方程写回与无前提总口。
- `NativeAccumulation/NativeTurbulenceLaw.lean`：原 sealed answer、完整 correction law 与恢复。
- `ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPhysicalRightTrace.lean`：
  原完整 Euclidean 恢复界。
- `ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.lean`
  及 `...RecursiveMacroGlobalAbsoluteVelocity.lean`：原宏时钟、全时路径与逐行连续性。
- `ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction.lean` 及
  `...NonlinearRegenerationCascade.lean`：原接触质量的时间判据及完整物理范数身份。

速度控制六模块 371 行、25 声明；原生修正控制另六模块 482 行、最长 110 行、30 公开声明。
两组均经过 `--trust=0 -DwarningAsError=true` 和精确公理核对，仅标准三公理。
原生修正的直接方程/总口重查及原非零修正测试通过；本次为构造后的本地核验，未另称独立认证。
无新增公理、占位证明或 scratch import；新文件未提高 `maxHeartbeats`。
