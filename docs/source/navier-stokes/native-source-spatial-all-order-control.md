# 原生成器的全阶时空控制

> 稳定机制卡。当前总目标与跨 cofinal 责任只见
> [原生全阶 active route](../../handoffs/navier-stokes-native-regularity-active-route.md)。
> 原总演化、CU 全历史与完整物质作用成果仍见
> [原生物理范数控制](native-physical-norm-control.md)。

## 同一完整源与实际控制消费

```text
原 rational Fourier 表 → stackedSeedState / stackedPhysicalSeed
→ 原 canonical replay.stage.physical
→ 原完整有限生成式、任意加权 Biot–Savart 观察
→ Stage9 泛型 mass/stiffness 能量消费者
→ 原完整 Q、Leray / 压力消元、黏性与原 Fourier ℓ¹ 时间账户
→ 原 Gronwall → 原 subsequence / wholeMildAssembly / wholePath
→ 原 contact / compiler next / run
→ 原完整强时间 jets、真实混合导数与四维 Fréchet / Lp 消费
```

`NativeFullOrderEnergy.stage_weightedVelocityEnergy_action_hasDerivAt` 直接从原
`GeneratedWholeRestartCanonicalStage.physical` 消元。它将原完整生成式在实际状态处冻结一个
线性输入腿，拉回加权速度的真实内积，并消费
`StageNineDiracMatterWeakGalerkinEnergy.galerkinWeakEnergy_hasDerivWithinAt`。
输出是原作用的 `E′=2P−2νD`，没有导数、目标界或 CU 配置身份前提。

此处复用的是 Stage9 的参数化下层机制。具名 CU 原历史的全九字段控制保持自身 source 索引；
原生场的控制由上面这条实际发生链生成，不以具名 CU 场等于原生场为条件。

## 原全阶账户

令 `F(k)=1+Σᵢ|kᵢ|`，`u(k)=BiotSavart(ω)(k)`，
`E_m=Σₖ F(k)^(2m)|u(k)|²`，`A=Σₖ|u(k)|`。
原 replay 已支付 `∫ A² ≤ wholeRestartVelocityCeiling seed`，右端不依赖 Galerkin radius。

`Convolution` 先在完整 ℓ² 内生成全频卷积，使用有界权重
`q_m,R(k)=min(F(k),R)^m`，证明

```text
q(p+q) ≤ 2^m(q(p)+q(q))
‖q·Qᵢⱼ(u)‖₂ ≤ 2·2^m A ‖q·u‖₂
2P−νD ≤ ((6·2^m)²/ν) A² E
```

同一个常数覆盖全部频率，且不依赖权重截顶 R 或模式表。有限模式上由原频率表生成 R，
使 q 严格等于未截顶权重；原积分 Gronwall 随即给出

```text
E_m(t) ≤ E_m(0) exp(K_m V_seed),  K_m=(6·2^m)²/ν。
```

`Limit` 消费原 `closure.weakClosure.subsequence` 与 `row_full_tendsto`；原
`wholeRestartWholeMildAssembly_fixedWave_eq` 将它认回原 `wholePath`。
每个原时刻、任意有限观察集和完整加权 tsum 同时受控；完整口显式产生 `Summable`。

`Initial.initialMomentBudget m` 是原 `butterflyFirstStackModes` 上原有理表经 Biot–Savart
读出的明确有限和。`Evolution.stacked_receipt_all_moments` 消元所有初始投影预算，原短窗口及
原 chosen contact 继承同界。

`Next` 沿原 `GeneratedWholeRestartCurrent.next` 递归：

```text
B_m(0)   = stackedMomentBudget m
B_m(n+1) = B_m(n) exp(K_m · wholeRestartVelocityCeiling (原 run n).contact)
```

`run_receipt_moment_control` 与 `run_nextReceipt_moment_control` 只读取原 index/time，
生成完整 moment 可和性与 B_m(n)/B_m(n+1) 界。预算属于各原窗口，不被解释为对 n 的统一界。

`Global` 模块的 `global_window_moment_control` 消费原 `GeneratedWholeGlobalPhysicalTrajectory stackedShortCurrent`
分支对象与其原 clock 有限覆盖，把各窗口预算相加为整个 `[0,T]` 的统一预算。原 path 与原
receipt chart 保持，零时和拼接端点均被覆盖；`global_window_spatial_control` 直接给出相同原
全局 U、ω 的空间全阶界，`finite_global_receipt_moment_control` 控制原
`WholeGlobalReceipt.ofTrajectory`。这个分支消费者不选择或排除 revised 分支。

## 正时间与原 cofinal 再入

`Dissipation.stage_energy_retained_dissipation` 保留 `E′_m+νD_m≤K_m A²E_m`。
非零原频率满足 `E_(m+1)≤8D_m`；在原物理半区间上积分、由均值定理产生估计中的中间时刻，
再消费原 Gronwall，逐阶生成 `PositiveTime.positiveTimeBudget seed m δ`。
原动能支付零阶；δ 是正观察下界，预算与 radius/权重截顶无关，也不要求全阶初值。

`receipt_positive_time_moment_control` 经原子列送入同一原 receipt。
`cofinal_occurrence_next_contact_momentRegular` 在原 cofinal occurrence 上直接消费原
H¹ slice → 原 seed → 原 compiler → 原 chosen contact；`macro_next_contact_momentRegular`
保留同一个实际宏后继。中间均值时刻只用于估计，没有替换 slice、clock 或 chooser。
该口不把此前整个弱恢复路径或 cofinal 瞬时认作已受全阶控制。

## 忠实空间场、导数与直接消费者

`Physical/Continuous` 从原已付 ℓ¹ 生成 `C(T³,ℝ³)` 值，严格认回原 `realField` 的 ae 值与
全部 Fourier 行，并直接消费原账户得到 `L²_t C_x`。

`Synthesis.spatialField` 是这个相同连续场沿真实 `ℝ³→T³` 的拉回。
原三维 critical kernel 将 m+2 阶平方 moment 送到 m 阶绝对可和导数界；
Mathlib `SmoothSeries` 生成 C∞ 及真实逐项求导。
`spatialField_word_eq` 保留原全部 Fourier 模式，方向导数乘子为
`i^m∏ⱼ(2π k·vⱼ)`。

`Consumer.run_receipt_spatial_control / run_nextReceipt_spatial_control` 对原速度与涡量同时给出
全空间 C∞、每个原窗口全部时刻的任意阶空间导数界。
速度界为 `(2π)^m(B_(m+2)(n)+ΣF⁻⁴)/2`；涡量由原横向 Biot–Savart 恒等式消费高一阶预算。
`run_receipt_spatial_Lp / run_nextReceipt_spatial_Lp` 直接生成任意紧空间域上的全阶 Lp，含 ∞。
`run_receipt_source_identity` 在全部原时刻保留原速度、涡量 L² 场及完整 Fourier 身份。

`Flux.run_receipt_flux_control` 同时生成原完整 `Q=-u⊗u` 每个坐标的任意阶全频 moment；
它继续消费相同原作用，不使用另一份本构或独立 dual。

`ActionMoments` 把原应力高两阶 moment 直接送入真实 curl-div。
`Correction.run_native_correction_control` 从原 Q 的投影交换子生成原 `nativeTurbulenceCorrectionAt`
的任意阶全频 moment；完整第二项 `Q(P_F u)` 保留，任意模式表 F 共用同一源预算。
原 `Fluid.mediumCorrection` 没有参与该识别。

## 原物理时间的完整作用递归

`Time.run_spatialWord_hasDerivWithinAt` 直接消费原逐频时间 producer、Leray 收缩、原压力作用及
新生成的全阶空间账户，对原窗口全部时刻生成任意空间词的一阶物理时间导数。
`run_spatialWord_on_interval` 将它认回相同原 `spatialField` 的迭代空间导数；
`run_wordRate_summable / run_wordRate_bound` 保留完整频率及原统一预算。
时间率始终是原 `receiptMomentumAction = BiotSavart(N−νλω)`，没有另定义残差强迫。
两端使用真实闭区间 `HasDerivWithinAt`，不宣称 clamp 的全实轴导数。

`TimeSource` 将原逐频时间率升级为相同原完整 Hilbert 速度的强时间导数，生成 rate 的全部空间
moment 与原完整 Q 的真实一阶时间导数。`TimeBilinear` 保留混合 Q 的左右顺序，证明连续双线性
作用、全频混合矩界以及一般 n 的二项式和求导法则。

`TimeCarrier` 将已付完整场与 moment 预算封在内部 `Profile` 中；原 initial 直接生成，有限加法、
缩放、完整双线性 Q/Leray 散度与黏性作用逐次生成后继 Profile。`TimeRecursion` 从原 U 定义

```text
j₀ = 原完整速度
jₙ₊₁ = −νλ jₙ + Leray div Σₐ binomial(n,a) mixedQ(jₐ,jₙ₋ₐ)。
```

`j₁=sourceRate` 由原作用认同，逐频微分与原 Bochner 积分恒等式生成每一层完整 Hilbert 强导数。
`sourceVelocity_iteratedDerivWithin` 将真实任意时间阶认回该递归；
`sourceVelocity_timeJet_moment_control` 在原闭窗内支付全部时间阶 × 空间阶 moment。
Profile 的泛型输入不进入这些原 source 终口。

`VorticityJets` 经原横向 BS 逆与零频定律认回原完整 ω。
`JetObservation/CorrectionJets` 将同一二项式作用送入原投影交换子和 curl-div，生成原 T_F 的
全部强时间 jet、全频 moment 与独立于 F 的显式预算。`CorrectionPhysical` 证明零阶的物理场
正是原两个有限 compiler 的输出差，完整 output inventory 保留。

## 原四维物理消费者与全局分支

`Mixed` 的 within 求和消费者直接生成所有原空间词的时间导数，证明任意时间／空间阶交换及
混合词的联合连续。`CorrectionMixed` 与 `VorticityJets` 对相同原 T_F、ω 完成同一消费；任意
空间紧域的全部混合阶 Lp 覆盖 ∞，窗口预算不依赖观察时刻或点，T_F 的混合预算不依赖 F。

`Spacetime` 从每个原 Fourier 模式的完整四维二项式乘积界生成闭凸域的 Taylor/tsum 消费者。
原 U 在 `Icc 0 duration × ℝ³` 上联合 C∞On；`SpacetimeObservables` 直接给相同原 ω 与 T_F。
任意紧时空域、任意完整 Fréchet 阶与任意 p（含 ∞）均获得实际有限界和 Lp。闭窗边界用
`iteratedFDerivWithin`；四维紧域存在界按各实际场给出，不将其自动改称 F 统一界。

`GlobalTime/GlobalJets` 从原 old 全局 trajectory 及 clock 有限覆盖消去局部 run index。
每层全局 jet 在任意原 receipt chart 上等于同一源 jₙ，故包括全部微步接缝；原 U 在 `Ici 0`
上强 Hilbert C∞，所有正时的普通 `iteratedDeriv` 认回原作用，全部时间／空间矩在 `[0,T]` 内
统一。这个消费者保留 `OriginalGlobal` 分支对象，不选择或排除 revised 分支。

`GlobalSpacetime/GlobalObservables` 将同一全局 jet 的有限时间窗重参数化到内部 Fourier
消费者，所有阶显式保留时间 Jacobian，再回到原物理时间。原 U、ω、T_F 在完整
`Ici 0 × ℝ³` 上联合 C∞On，任意紧时空域上全部 Fréchet 阶／全 Lp 均直接消费。
原零模、横向 BS 逆与完整 `Q(P_F U)` 保持；四维存在预算按实际模式表给出。

## 原弱恢复发生的控制生成

`EndpointEnergy` 直接消费原 endpoint stage 的实际有限生成式，生成相同 `E′=2P−2νD`。
`ScalarGain/EndpointGain` 复用正时间增益，在原绝对 `[a,b]` 内由零阶 K 和源活动账户生成全部
阶预算；估计中的 δ 与均值时刻不改动原 clock。

`Recovery` 从原 kinetic-viscous ledger 在每个内部时间带生成各 radius 的低 enstrophy 时刻，
由原 `finiteStateVorticity_sourceOwnedWholeStateCompactnessBudget_on_Icc` 消费其真实轨道，
产生局部统一活动账户。进一步抽取的仍是原 `core.subsequence`；其时间极限给出共同物理窗。
正时间增益再经原 whole-mild 全时行极限送入完整 U，任意有限频集消去截顶，生成全阶
Summable 与统一总界。`wholeMild_controlled_subinterval` 覆盖任意内部时间带中的非空子区间；
原 source 终口在 selected H¹ 之前保留绝对物理路径，不提交账户、正则性或另一份 field。

`RecoveryNonlinear` 独立在原整个 `[0,1]` 上识别 `nonlinearLimit=N(U)` 及原 Q/Leray 作用。
L² 速度强极限与 L¹ 非线性强极限的 a.e 子列合成仍沿同一原 radius 序列；原 Hilbert N 的
连续性与极限唯一性完成所有波数在同一 a.e 集上的身份，不需要控制窗或高阶前提。

`RecoveryRowAction/RecoveryWindow` 将原 `row_mild` 的逐行绝对连续作用提升为完整 Hilbert
强时间导数。`PolynomialJets` 复用完整有序 Q/Leray 与黏性递归；`RecoveryJets` 在原受控
窗生成全部真实时间 jets，并将每阶 Jacobian 返回原物理时间。`RecoveryObservables` 同时
认回原 U、横向 curl 产生的 ω 与原两个 compiler 的 T_F；全阶矩、混合导数、四维 C∞On
及紧域全 Fréchet 阶 Lp 均由同一窗消费。

`RecoveryAdvance.ControlSpan` 保留原 prelimit enstrophy／活动账户与同一 extraction。
`advance` 从原最后时刻的实际状态应用原局部吸收，延长物理窗并将新旧账户在该点精确相加。
任意有限 `iterate n` 保留原起点与 extraction，`RecoveryObservables.iteratedWindow` 直接
消费每次生成的窗；不宣称对 n 的统一预算或迭代上确界已到 terminal。

`RecoveryAE` 对原 kinetic-viscous 账户应用 Fatou，在几乎每个时刻生成同一原子列的有界
enstrophy refinement，再由原局部吸收生成右控制窗。全部合法 `ControlSpan` 的开区间之并
形成 `regularSet`；其余可右隔离的时刻可数，因此 selected H¹ 之前未覆盖时间集零测。
`RecoveryDomain` 在这个源生开域上认回原 wholePath，生成真正的四维 C∞ 与紧域全阶 Lp。

`RecoveryCoverage` 将原有符号 `netEnstrophyWork` 的频繁统一账户直接送入跨点控制窗。
在失败索引的未覆盖时刻，`sourceUncoveredAction` 则生成同一原 core/extraction 上的实际
stage 序列：sample 趋于该点、radius 趋于无穷，移动高频尾的原涡量质量与原净作用积分逃逸。
原 `Gν`、半 enstrophy 增量及任意固定观察集的原 K 界同时保留。这是 prelimit 作用责任；
不推断原极限 U 的高阶爆破或正 kinetic defect。完整恢复段及 cofinal 拼接的当前责任只由
active route 维护。

`CofinalMomentum` 从既有 `sourceGeneratedCofinalStress` 的原 stage/refinement 直接生成
完整 `(U,σ,BS(Gνω))` 联合极限。原黏性行随原弱速度极限认回，原非线性行随 σ 认回，
故实际动量极限为 `P div σ−νλU* = resolvedMomentum+P div R`。压力继续由完整 σ 的
原 contraction 生成，包含零波处理。此源属于原 contact cofinal occurrence，与上面的
endpoint-Galerkin 动时序列保持各自精确来源。

`CofinalRecovery` 以原 `PhysicalRightTrace` 生成恢复 U 的完整强 ℓ² 右迹，进而生成完整 Q
和动量的系数右极限；两侧实际动量之差正是 `P div R`。继承的 L¹ forcing 经原 a.e 身份
支付真实 N(U) 的积分，原 `row_mild` 随即将 σ 与完整 `Q(U(s))−σ` 消费为原 Duhamel 更新。
该更新通过原 selected H¹ 截面送入 literal next 的全部 receipt，并直接进入原
`nativeLaw.recoveryNextDuhamelEvolution`。

`EscapeCarrier/EscapeStress` 对恢复内部的失败索引发生保留另一条精确源链。原固定波数的
radius 统一 Lipschitz 与原 full-time 行极限，将动时动 radius 序列认回原 wholeMild U(t)；
原 K 球生成完整 Hilbert 弱极限。同一 refinement 生成全部应力坐标 σ、正协方差 R、
δ≥0 及 `|R_kij|≤δ`；原完整非线性 N 趋向 curl-div σ。原高频质量、净作用积分和全部
escape 趋向仍在同一载体，不能由 σ 的存在抹去。

`ReceiptProfile/ReceiptSpacetime/GeneratedSpacetime` 将已经支付的增益用于原任意生成器，
不再依赖固定 stacked 源。内部 `Window` 的全阶账户由原 `PositiveTime` 或 `Next` 消元；
一阶 jet 精确等于原 BS(Gν)，后续各阶直接消费 `PolynomialJets`。原 curl、完整 T_F 与
四维 Lp 使用同一场。任意 `current.nextReceipt` 的 `[δ,duration]` 全阶成立；若 current
由 cofinal/macro 生成，其 contact 再编译的 `nextReceipt` 的整个 `[0,duration]` 受控。
这里没有把 current 自身 receipt 的零时 H¹ 截面改称全阶；内部 `Profile 0` 的坐标尺与
原物理时间之间的全部 Jacobian 都由导数定理支付。

## 完整继承修正的空间导数

`FixedFilterGlobal/WholeVelocityFilter` 从原完整第二项的输入对直接生成
`support(T_F)⊆F∪(F+F)`。原统一 K 行界经真实有限 Fourier compiler 给出任意固定 F 的全部
空间阶与紧域全 Lp，预算不含原 time/index/macro。完整输入 Q(U) 始终保留，不能用有限输入
观察定理代替它。全时 velocity 读出是 `curl-div(P_FQ(U)−Q(P_FU))`；在已有原涡量载体上，
它严格认回原 T_F，而在 cofinal 处不自动包含继承 σ 的 R 项。

`JointFilter` 继续消费同源 σ，生成完整 `curl-div(P_Fσ−Q(P_FU))`，其原作用分解保留
`curl-div(P_FR)`。原 cofinal／escape 各自的 K 同时控制 σ 和 U，故这份完整继承物理场也有
固定 F 的全部空间阶及全 Lp。`FiniteJetLimit` 把有限真实输出系数的收敛送入全空间统一的
实际 `iteratedFDeriv` 差界；`InheritedFilterJets` 将原 T_F 沿原同一次 refinement 的每阶
空间导数认回该继承场。此处不要求极限点本身已具有 ℓ² 涡量。

## 源生有限宏修订与原绝对晚时全阶

`RecoveryDecay` 消费原 stage 的 `E′=−νY`、原整数频率 Poincaré 与 Gronwall，再沿原
wholeMild 子列生成所有时刻的完整物理速度平方界
`K(t)≤K_endpoint exp(−2ν(2π)²t)`。
`MacroDecay` 用原 `slice.time>1/2` 及原 curl/BS 逆认回 `next.initialState`，得到每次实际
宏边 `K_next≤qK`，`q=exp(−ν(2π)²)∈(0,1)`。

`RecoverySmallK` 从原 ∫Y 账户在各 radius 的早段生成估计起点；既有临界 barrier 使同一
原 stage 在整个 `[1/2,1]` 保持小 Y。原 full-time 行极限由此覆盖原 chosen H¹ slice。
`SmallSeed` 再沿原 canonical stage 与原 closure 支付完整 reentry receipt 的质量不增，
覆盖原 contact chooser，并推出该原 next 的 elapsed 无界。两个 chooser 都没有更换。
`SmallKFullOrder` 从原 slice 之前的源生短窗消费既有增益，支付 slice 的全部 moment；
原 next 自身 receipt 因而从零时起四维全阶。

`MacroExecution` 直接消费原 responder 的 `generatedBoundedRun`；source K 的几何衰减
给 `FiniteMacro` 一个有限 fuel。它返回原 exact NativeReachable 终点，或在该深度继续原
已生成 response；小 K 使该 response 的原后继停止宏修订。公开
`source_finite_macro_terminal seed` 不接未来 terminal、branch、noTerminal 或小量输入，
完整依赖不含 `ClassicalWholeRestartEndpointMacroRuntimeAudit`。原微步演化继续。

`GeneratedGlobal/GeneratedGlobalSpacetime` 将任意原全阶初始窗口通过原 next 递归及原
clock 有限覆盖送入 `WholeGlobalReceipt.ofTrajectory`，直接生成同一全局 U/ω/T_F 的
四维控制，包含接缝。`GlobalTail/EventualTail` 从上述源生 terminal 读取其原 run 2；
该窗口由原正时间 contact 已付全阶。两端原 receipt chart 与 `elapsedTime_run_add`
证明这份尾段正是原 globalPath 的物理时间平移，包含起点。

`FiniteMacroPhysical/FiniteMacroGlobal` 按原 NativeReachable 的每个实际 response 递归
原 clock、physicalStage 与 endpointSplice；任意中间原边及 suffix 都保留，完整 prefix 接上
原 terminal 全局轨道。`AbsoluteEventual` 的晚时起点为
`arrival.clock + terminal.elapsedTime 2`，原绝对全路径在该点后严格读回同一 tail。
公开 `source_absolute_spacetime_control/source_absolute_all_order_Lp` 只输入原 seed，
生成此绝对晚时半空间上的 U/ω/原 T_F 四维 C∞ 与任意紧域全 Fréchet 阶／全 Lp。
全时 Hilbert 速度仍读原实际全路径，受原 seed L² 界控制；早期全阶责任留在 active card。

## 原 W 的零热尺度全阶消费

令 `T=NativeAbsoluteEventualControl.startTime seed`。`SourceView/Window/Tail/Moments`
把上述同一 tail 的全阶矩直接送入**原** `NativeForwardWindowJets.jet seed rank t`。
原核及其全部导数支持于 `[-2,-1]`，所以 `T−1≤t≤H` 的实际样本全部落在
`[T,H+2]`。原 complete source 在这里的 σ 点态等于同一 U 的 `quadraticFlux`；
全阶卷积预算支付全部九个分量，包括零频。对任意时间阶 r、空间阶 m，源直接生成

```text
F(k)^m |U_r(t,k,i)|       ≤ Bᵁ(seed,H,r,m+4) F(k)^−4
F(k)^m |σ_r(t,k,i,j)|     ≤ Bσ(seed,H,r,m+4) F(k)^−4
```

常数先于时间、频率与分量；没有热尺度或 caller 范数输入。
`Spacetime/LocalFourier` 将这些局部共同包络送入原 Fourier 级数的所有普通时空导数。
证明中的紧支撑 bump 在原点邻域等于 1，最终消去，不成为新物理场。
`Tail/Physical` 因而对原 `jointField seed 0` 的 W／σ／R，在
`(T−1,∞)×PhysicalSpace` 上给 C∞，并对任意紧子集给普通 `iteratedFDeriv` 的全部 Lp 界。
R 仍由原 `σ−quadraticFlux(W)` 读取。`Tail/TimeAction` 直接逐项求导原 Fourier 级数，
把时间率认回原 `momentumField seed 0`。

`Heat/SpatialZero` 与 `Tail/HeatLimit` 进一步证明：对任意固定时间 jet 阶和空间阶，
原热作用的速度空间 Fréchet jet 随 h→0 在 `[T−1,H]×PhysicalSpace` 一致收敛，
所有 h≥0 共用同一预算。`Tail/StressLimit` 对原 σ 的任意阶加权 Fourier ℓ¹ 误差，
在该闭时间段及全部九分量上一致给零极限。

`Tail/Mixed/Series` 在开时空条带用同一可和包络交换原级数与全部普通 Fréchet 导数。
`Source/Physical` 直接认回原 U／σ 的热乘子；R 使用原双频乘子 `μₕ(p)μₕ(q)` 和
完整 `σ+U⊗U` 恒等式。`Readout/Outputs` 经有限分量装配和连续微分读出，得到原
U／σ／R、实际 curl、动量时间率整组输出的任意阶紧域一致 h→0。

`Consumer/ZeroTail.read_all_order_control` 实际消费原 runtime 已 emitted 的完整
`payload`，读取其 `view 0`；五项输出为 W、σ、R、真实 curl 和物理时间率。
控制域按原 `clockAt+time` 拉回，`rate_momentum` 保留原作用；
`controller_write_back` 保留原 activation、whole-ledger、literal next 和零热完整读出的 next。
`Consumer/ZeroLimit` 从同一 `payload.view h` 读出全部物理场，`read_zero` 定义性等于
上述原消费者。原时钟平移的全部普通导数恒等式将混合极限拉回实际消费域；
`all_Lp_common_bound` 的 B 及 h→0 邻域均先于全部 p，包含∞。
`all_Lp_converges` 由一致误差及紧域有限体积生成每个 p 的实际 Lp 误差趋零，
`controller_limit` 同口消费原 facade 覆盖、整账、literal next 及所有 h 的完整 view 平移。
原 `HeatQuery` 与 resolution=1 安装保持原合同。这里签收的是该原采样域上的零热面，
全物理时间的生成责任由 active card 维护。

## 原全历史的完整动量写入

`ReceiptMomentumIntegral` 消费任意原 whole receipt 的真实速度导数与完整 Leray/Q/黏性作用。
`OriginalMomentumIntegral` 从原 finite-prefix receipt 读取全部 micro 图；原 K 界支付固定波
作用的可积性，原全行左迹将积分写到同一 cofinal 端点。

`RecoveryMomentumIntegral` 从原 `row_mild` 的绝对连续路径与同源 a.e. forcing 认同，生成
wholeMild 任意 `[a,b]⊆[0,1]` 的实际动量积分，直接写回原 H¹ compiler next 的初始速度。
`MomentumIntegralSplice` 以真实时间平移拼接两个已经支付的动作；`MacroMomentumIntegral`
从原 step 消去前段与恢复的输入，`FiniteMacroMomentum` 再沿原 NativeReachable 写过整个历史：

```text
U_seed(b,k) − U_seed(a,k)
  = ∫[a,b] (P_k div Q(U_seed(t))(k) − ν λ_k U_seed(t,k)) dt.
```

公开 `source_momentum_write` 只输入原 seed、非负两端点与波；包含零频、反向积分及全部
cofinal/macro 接缝。`source_early_momentum_write` 将 `[0,startTime]` 的完整作用写到原受控
tail 的零时速度。所有 Q 输入保留完整 U；σ/R 保留原接缝动作极限，不产生额外 delta 冲量。
这里的积分等式量化全部 Fourier 行；早期正阶范数由同源全阶实现继续消费。

`FiniteMacroEvolution` 从 actual responder 的确定性证明完整 terminalRun 唯一，包含原
proof-relevant arrival。原 `clock_append` 与完整 prefix chart 继而给出
`U_seed(clock(arrival)+t)=U_current(t)`，量化所有 `t≥0`。对一拍 actual response，
右端 current 就是原 generated next；不存在另选终端造成的第二条未来路径。

`NegativeFourMomentum/GlobalHilbertAction` 复用原 critical kernel，把全部波的动量装入
H⁻⁴ Hilbert 载体；非零波的逆权重精确恢复原速度及完整 Q/Leray/黏性作用。源 K 账户支付
全半线 Bochner L∞，原逐波积分生成完整 Hilbert 积分与 Lipschitz 界。
`GlobalPhysicalCarrier/GlobalPhysicalAction` 再消费原物理 CLM：原实速度 L² 的 Fourier、
Parseval、完整物理乘积 Q 和 next 全时保持；加权物理表示具有同源 Bochner 写入、显式
L∞ 作用预算及原物理时间 a.e. 强 L² 导数。

## 统一控制的直接接收形状

`FinitePrefixWindow.window length` 从原 `WholePrefixReceipt.receipt stackedShortCurrent length`
读取完整路径，预算为已有 `runMomentBudget` 的有限和。`FinitePrefixChart` 的物理时间
`χ(s)=T·sigmoid(s)` 及显式逆坐标由同一 prefix duration 生成；完整 U 的原 Fourier 行、
contact 与 nextContact 均保留。chart 时间导数含实际 `χ′>0`，物理导数由逆坐标回收。

`Fluid.CurrentReadout` 把原 CU 电流消费者实际使用的 matter／dual 两面显露为共同 primitive。
原 `Fields.spatialCurrent` 的运行定义不变，其光滑性直接消费该 primitive。NS 的
`CurrentReadout` 从原 chart 完整 U 读取 canonical pair，统一电流的三个空间分量逐点等于
原 U，时间分量为 `2+‖U‖²/8`，所有空间 jets 同时认回。这里不构造七个未被消费的字段，
不需要九场联立自洽或具名 CU 历史身份。

`ChartPhysicalAction/CurrentAction` 保留原物理作用和 `χ′`，并证明完整 paired current 的
真实点态导数。`ChartPhaseWard` 从原全 Fourier 求导交换及 BS 横向性生成强点态散度零，
原 densitized current `(1,U)` 与母作用 phaseMomentum 的连续性／Ward 直接消费它。
`ChartVorticity.unified_curl_original` 则把既有 `Fluid.curl` 精确认回原完整 ω。

`PhysicalCurrent` 通过原逆时钟，在 `0<t<T` 的原物理 `BasePoint` volume 上消费普通
Fréchet 全阶／全 p 控制；`VorticityControl` 直接调用 `Fluid.curl_contDiff` 对原 ω 做同样的
消费。`RootSourceAction` 从原 authoritative occurrence 的 finite 构造消元真实 response，
`RootCurrentControl` 的同一物理读出及其导数索引该 target.initialState／target.contact。
`ChartTransport` 还给整场、matter、dual 的重叠对易、cocycle 和真实导数比率。

这些预算逐源发生、逐紧域给出。`index+2` 的窗口是继续执行原 compiler 生成的有限历史，
不是 `authority index` 已装入的未来字段；原完整 authority source、整账与 next 均未改变。
这项实际消费不把有限 prefix 范围替代全原生目标，也不借用原 CU 历史的统一预算。

`VorticityAction` 从原 paid curl jet 生成完整系数范数下强导数，用原 heat-Duhamel 逐行导数
认回全部 Gν，含零波；实际空间场导数另由已付 Fourier consumer 生成。`ResolvedAction`
将真实有限物理场导数写成原 resolved tangent 加完整 T_F。`ResolvedNonlinearReadout`
把原对称 cube 投影交回原 raw source compiler，消元横向性／reality，认回完整输出为
−平流＋拉伸；不增加第二次输出截断。

## 同一原微观历史的完整场与统一消费

`WholeHistoryClock` 读取原 duration，令 `f(t)=t/(1+t)`、`c=sSup(range(f∘duration))`，
生成 `χ(s)=c·sigmoid(s)/(1−c·sigmoid(s))`。原严格递增序列给出 `0<c≤1`、`χ′>0`，
时间像恰是 `{t | 0<t ∧ f(t)<c}`；所有 finite contact／next.contact 都严格落在像内。
无需选择原 elapsed 是否有界。这是完整已生成历史的数学读出，未将未来历史安装到较早
authority，也未将 cofinal 当作有限 chart 点。

`WholeHistoryField` 按 `χ(s)` 读取原覆盖 prefix 的 wholePath 与 BS 场；prefix coherence
保证所有覆盖给出相同完整场。`field_locally` 更在邻域消去可变 cover，留下固定原 prefix，
使 C∞ 直接消费已付 Window。没有新的场求解或 caller 提交的 U／全矩账户。

`WholeHistoryAction/Curl` 将同场强导数、全部 Fourier 作用及 `Fluid.curl` 对齐。
`WholeHistoryCurrent` 的 canonical pair 在整个 chart 上配对，共同 `Fluid.CurrentReadout`
直接支付四分量全阶／全 p 控制。`WholeHistoryPhysical` 的两个源口不收 index 或 Window，
以原时间像内紧域为定义域，在原物理 volume 下消费普通四维 Fréchet 全阶控制。
`WholeHistoryPhysicalAction` 直接证明 d/dt 电流与 curl，保留原 ν／完整 Gν，并认回
occurrence-derived target.initial／target.contact 的原 compiler 作用。
初值边界、cofinal、恢复与宏发生的接入由 active card 管理，不由此 chart 的定义补认。

## 原 T_F 与统一微分算子的作用对应

`SpatialOperators` 证明真实四维空间限制与导数、curl、Laplacian 对易。
`CurlCross` 先保留完整 `A div B−B div A`，再由原 raw compiler 的横向性消元；
`ResolvedViscousReadout` 将原 `(2π)²|k|²` 乘子认回 `−Δ`，保留任意 F、实 ν 与零波。

`ResolvedSpacetime` 的场是原同一历史的动态投影，不是另选静态场。系数 C∞ 直接消费
原 `observed_chain_smooth`／Window；`ResolvedUnifiedOperators` 将其 `Fluid.curl` 认回
ω_F，Laplacian 与 curl-cross 认回原完整 resolved tangent。

对原生成的 `F=wholeRestartModes radius`，`ResolvedUnifiedAction` 从原完整 ω 的强
时间导数和有限 Fourier compiler 得到真实 D₀，继而证明

```text
D₀ω_F = χ′ · (νΔω_F + curl(U_F×ω_F) + T_F)
χ′⁻¹D₀ω_F − (νΔω_F + curl(U_F×ω_F)) = T_F。
```

`χ′` 严格为正且为原物理时间导数，ν 是原 butterfly 黏性；T_F 完整输出含 F+F，未再
投影。`UnifiedCorrectionControl` 的 C∞ 证明实际消费此等式与原 Fluid 微分算子的光滑性，
其全阶 Lp 口使用原时间像内紧域、普通 Fréchet 导数与原物理 volume。预算按 radius、
紧域与阶数给出；两枚 target 读出认回原 occurrence-derived initial／contact。

这不是把具名 `Fluid.mediumCorrection` 的固定 CU 黏性或 anchor 改成原值。任意 F 的原
compiler 作用等式仍由 `ResolvedAction` 保留；上面的物理 curl-cross 认同消费实际源生成的
对称库存。cofinal／恢复作用的同源接入继续保留原 σ、R 与完整 next。

## 含原初值的物理历史

`PhysicalHistory` 在原物理时间直接定义 state，覆盖索引由原 duration 与 Nat.find 生成。
其域 `0≤t ∧ ∃ length, t<duration length` 包含零时及任意原闭窗。`state_read` 证明所有
覆盖读取同一原 wholePath，`read_locally` 在域内邻域消去可变索引，U／ω／任意 F 的
T_F 直接消费原 Window 的 C∞On。正时间精确认回前述逆时钟读出，零时读取原 stacked
raw initialState，不替换初值或源。

`PhysicalHistoryControl` 从真实 slab 生成 UniqueDiffOn，以域内迭代 Fréchet 导数消费
紧域全阶 Lp，测度为原 physical BasePoint volume；零时为物理半空间的一侧导数。
`PhysicalHistoryCurrent` 保留同一 U 的全时 canonical pair 与四 current，控制口不收
smooth、Window 或目标预算。`PhysicalHistoryInitialAction` 把原零时 receipt jet 接成
同一载体的真实右导数：原 BS(Gν) 与 Gν 的全部 Fourier 行均包含零波，curl jet 的认同
消费原 Q 的 curl-div 和横向性。四 current 的右导数同时保持；不报跨零时的两侧光滑。
cofinal／恢复／宏时间点的接入不由这些有限 slab 的并集补认。

## cofinal 原生更新后的同源消费

`CofinalUnifiedField.target_from_occurrence` 读取原 cofinal whole-ledger occurrence 执行的
H¹ compiler target。原 `cofinalNextWindow` 给 target.contact 起始的整个 target.nextReceipt
闭窗；完整 U／ω／T_F 和 canonical current 直接消费其 C∞On。

`CofinalUnifiedAction.inlet_from_cofinal/velocity_from_cofinal` 将这份场的全部非零 Fourier
行写成原 U*、σ、`Q(U(s))−σ`、H¹ slice、原 target.receipt contact 与下一 receipt 的完整
Duhamel 表达式。σ 和 transition 同时保留，不设置 R=0；物理时间导数的 momentum_row
另含零波。`CofinalUnifiedControl` 的全阶 Within Lp 使用原 physical BasePoint volume。
`field_generated_next` 认回原 target.next.contact；这些控制的零时是 target.contact，
不重命名为旧 cofinal 时刻或未覆盖的弱恢复时刻。

`PairedCurrentFourier` 在真实物理 L² 场上读取 canonical 配对。空间 current 的 Fourier
系数就是 U；二次时间 current 属于 L¹，系数为 `baseline−tr Q(U)/8`，其中
`Q(U)=−U⊗U`。`CofinalPairedCurrent` 消费原同次 refinement 的 U／σ 联合极限，生成
四 current 的全部 Fourier 极限。继承 current 与弱 U* 单独配对之差完整保留为
`−tr(σ−Q(U*))/8`；零频实部是原 kinetic defect `δ/8`。

`CofinalCurrentResponse` 用原 H¹ target.nextReceipt 的整个路径生成响应：空间分量是
`U(s)−U*`，时间分量是 `−tr(Q(U(s))−σ)/8`。原 Window 支付连续 Fourier 代表与真实
L² 场的 a.e. 同一，`controlled_current_read/controlled_current_fourier` 因而认回上面的
统一 current 全阶消费者。`generated_next_current` 读取原 target.next.contact。

`CofinalCurrentResponseAction.response_iteratedDerivWithin` 直接消费原 receipt 的全部
timeJet 递推与完整 mixedFlux：每个物理时间阶、四分量及全部波的真实域内导数均为该
同一响应的 jet。`fluxJet_one` 认回原 momentum 与 U 的双线性作用；证明不交换积分和
导数，也不增加高阶估计。原 fluctuation 平方范数极限支付 `δ/8≥0`；没有要求 δ 消失。

## 原 wholeMild 恢复的配对消费

`RecoveryUnifiedCurrent` 直接拉回原 `regularDomain` 到 physical BasePoint，局部窗口从原
ControlSpan 消元，完整 U 不被另造。canonical 四电流在原开域消费已付 C∞，给原 volume 上
普通四维 Fréchet 全阶／全 p 控制。真实 L² 配对电流与连续代表 a.e. 同一，其全部 Fourier
系数为 `coefficient(U,Q(U))`；该代表认同在已付域成立。

`RecoveryCurrentAction` 从同一窗口的原强时间作用认回 U／四电流的真实物理导数，动量
全部行是 `P div Q−νλU`。整段真实 L² current 的时间响应为 `−tr(Q(U(s))−σ)/8`；原强右迹
趋向弱 U* 的 canonical 配对，区别于保留 σ 的 inherited current。原 H¹ 终截面精确认回
compiler target.initial 的全频电流，不要求该截面落在 regularDomain 或全阶光滑。

`RecoveryCurrentJets` 将原 velocity 的实际 `iteratedDeriv` 在同一窗口邻域认回已付 timeJet，
完整 mixedFlux 再生成上述 current 响应的全部阶普通时间导数。证明使用整邻域等式；零阶
保留原 σ，正阶消费原 jets，未交换 Fourier 积分和微分。恢复开域外的原联合发生不被删去。

`EscapePairedCurrent` 沿原 SourceActionEscape／StressAt 的动时动频率提取生成四电流
Fourier 极限。空间分量读取同一 wholeMild U(point)；时间分量相对该弱 U 的单独配对保留
`−tr defect/8`，零频实部为原 kineticDefect/8≥0。`EscapeCurrentAction.currentCurve` 是
原固定 radius 的真实物理配对轨道。先求时间导数，再在原 sample 取值，空间分量沿同一
refinement 趋向已有 σ 动量。固定非零波最终进入原库存，零波独立保持；这不是对移动
sample 参数求导，也不是原 wholeMild 在极限点的经典导数。

`RecoveryJointCurrent` 对整个恢复内区间 `(0,H¹time)` 消元原 regularSet 成员性，生成
一个共同 σ：常规发生为 Q(U)，域外发生为原 sourceStress。完整 U、四 current、压力、
动量和修正均读取同一 σ；各处空间 current 都等于原物理 U 的 Fourier 读出。
`RecoveryJointAction` 保留两类实际时间作用与原压力，并给全波等式
`correction = P_F curl(momentum) − [curl div Q(P_F U) − νλ curl(P_F U)]`。
同一修正直接消费已付 JointFilter 的全部空间阶／全 p 界。预算依赖原 source、F、order，
不依赖恢复时间；完整 F∪(F+F) 保留。此口未添加时间可测性或域外时间高阶结论。

## H¹ 首 receipt 的原控制接入

`ReentryUnifiedField` 读取原 H¹ slice 的 canonical replay 和首 target.receipt，逐点用
t/2 的原 positiveWindow 消去 cutoff。U／ω／T_F／canonical 四电流在 `0<t≤target.duration`
上 C∞On；`ReentryUnifiedControl` 以原 BasePoint volume 消费全部四维 Within 阶与 Lp。
高端点为单侧，零时的原 H¹ 数据不被附加全阶前提。

`ReentryCurrentAction` 从同一原 timeJet 生成 U 和四 current 的物理时间导数，完整
momentum 各行认回原 ν 的 BS(Gν)，包含零波。contact 处整系数动量等于原
target.nextReceipt 的零时动量；与完整场接点身份一起保留真实作用。`initial_coefficient`
另以真实 L² 配对认回原 wholeMild 的 H¹ 终截面。正时间 moment 支付连续代表与真实 L²
电流 a.e. 相同及全 Fourier 读回；未在未付的零时使用该点态连续代表身份。

`UnifiedOccurrenceControl` 从原 SpinPair root 的任意完整 temporal occurrence 读取
`.inherited .configuration`。`projectionOutcome_heq_sourceOutcome` 保留原依赖字段，
`rootCofaceRead_consumerSafe` 保留完整消费者；原 material current 直接支付 Smooth。
`occurrence_all_order_Lp` 因而控制该发生的全部九字段与各阶导数，包括 p=∞；不需要先把
配置认同指定 `SpinPair.actual` 或证明 CWA。量词为每枚发生各有预算，不宣称任意 current
共用一界。原 NS 发生的实际表示／安装关系由 active card 管理。

本卡的 Fourier 逐阶控制、晚时口、H⁻⁴ 和作用表示均为可复用资产；其剩余困难不构成
统一理论的新法则责任，也不规定原生全阶必须逐点延展旧 contact 轨道。

## 完整 σ 的配对读出

原 cofinal 与恢复 σ 已生成完整 Hilbert Gram 载体，canonical 配对读回四电流；原
nextReceipt 的固定载体写入、完整强时间 jets 与两槽实际微分作用已相容。它们直接消费
已有时间／空间控制，各守真实定义域。载体、作用及消费者的唯一详述见
[完整源配对载体](native-paired-source-carrier.md)。

## 权威源码

- [完整连续物理场](../../../SaturationMonoid/NavierStokes/NativeAccumulation/SourceReadout/Physical/Continuous.lean)
- [原完整作用与全部有限后继](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/Next.lean)
- [统一电流共同 primitive](../../../SaturationMonoid/PhysicsCore/Stage9CU/Fluid/CurrentReadout.lean)、
  [原 occurrence 的完整 current 消费](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RootCurrentControl.lean)、
  [原涡量的统一控制](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/VorticityControl.lean)
- [原完整微观历史场](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/WholeHistoryField.lean)、
  [原物理时间全阶消费](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/WholeHistoryPhysical.lean)、
  [同场实际作用与 next](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/WholeHistoryPhysicalAction.lean)
- [原 T_F 的统一微分等式](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/ResolvedUnifiedAction.lean)、
  [原 T_F 的直接全阶消费](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedCorrectionControl.lean)
- [含原初值的物理历史](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PhysicalHistory.lean)、
  [含零时的全阶消费](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PhysicalHistoryControl.lean)、
  [原初值的实际单侧作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PhysicalHistoryInitialAction.lean)
- [cofinal 更新后的源场](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/CofinalUnifiedField.lean)、
  [完整 σ 作用与 current](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/CofinalUnifiedAction.lean)、
  [其直接全阶消费](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/CofinalUnifiedControl.lean)
- [真实物理配对 Fourier](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PairedCurrentFourier.lean)、
  [原 cofinal 四电流](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/CofinalPairedCurrent.lean)、
  [整窗响应与 next](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/CofinalCurrentResponse.lean)、
  [全阶作用相容](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/CofinalCurrentResponseAction.lean)
- [原恢复 current 全阶消费](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryUnifiedCurrent.lean)、
  [恢复 current 实际作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryCurrentAction.lean)、
  [其全部时间 jets](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryCurrentJets.lean)
- [域外原 current](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/EscapePairedCurrent.lean)、
  [其实际导数极限](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/EscapeCurrentAction.lean)
- [恢复联合载体](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryJointCurrent.lean)、
  [其共同作用与完整修正](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryJointAction.lean)
- [原 H¹ 首 receipt](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/ReentryUnifiedField.lean)、
  [首重入的全阶消费](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/ReentryUnifiedControl.lean)、
  [其真实入口与 contact 作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/ReentryCurrentAction.lean)
- [真实空间导数与 Lp 终口](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/Consumer.lean)
- [原完整 Q 的全阶账户](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/Flux.lean)
- [原 cofinal 再入的正时间全阶生成](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/PositiveTime.lean)
- [原 native correction 全阶作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/Correction.lean)
- [原物理时间与全部空间词](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/Time.lean)
- [原完整 Hilbert 时间作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/TimeSource.lean)
- [原全部强时间 jet](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/TimeRecursion.lean)
- [原四维物理终口](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/Spacetime.lean)
- [原 ω/T_F 四维消费者](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SpacetimeObservables.lean)
- [原 old 全局物理时间窗](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/Global.lean)
- [原 old 全局时间 jet](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/GlobalJets.lean)
- [原 old 全局四维观测](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/GlobalObservables.lean)
- [原弱恢复受控窗 producer](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/Recovery.lean)
- [原恢复非线性身份](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryNonlinear.lean)
- [原恢复四维 U/ω/T_F](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryObservables.lean)
- [同源 prelimit 账户推进](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryAdvance.lean)
- [开且满测度的恢复控制域](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryDomain.lean)
- [跨点作用控制与原高频发生](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/RecoveryCoverage.lean)
- [原 cofinal 完整联合动量](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/CofinalMomentum.lean)
- [原 cofinal 恢复与 next 的实际作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/CofinalRecovery.lean)
- [恢复高频发生的完整源应力](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/EscapeStress.lean)
- [任意原生成器的四维全阶消费者](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/GeneratedSpacetime.lean)
- [完整继承修正的空间 jets](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/InheritedFilterJets.lean)
- [原宏修订有限执行](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/FiniteMacro.lean)
- [原有限宏绝对物理路径](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/FiniteMacroGlobal.lean)
- [原绝对晚时全阶源口](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/AbsoluteEventual.lean)
- [原全历史的完整动量积分](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/FiniteMacroMomentum.lean)
- [原 generated next 的全路径相容](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/FiniteMacroEvolution.lean)
- [原全频物理作用](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/GlobalPhysicalAction.lean)
- [统一全阶 occurrence 接收口](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/UnifiedOccurrenceControl.lean)
