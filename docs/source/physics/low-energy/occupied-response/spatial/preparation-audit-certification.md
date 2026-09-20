# 独立认证：原控制历史生成空间准备态

Verdict: **certified**。三个冻结候选未发现声明或来源缺陷。

范围为 `PreparationHistory / PreparationState / PreparationGauge`，其中 Gauge 依赖最终正式 `LowEnergy.MatterSpace.GaugeForce`。未读取或纳入后续 `PreparationNative`、`Dual*`；只新增本目录证据，未修改候选、根文档或提交。

## 严格证据

三文件与候选 `Audit.lean` 均 fresh 默认预算 `lake env lean --trust=0 -DwarningAsError=true` EXIT 0。56 个公开口和独立 `Consumer.lean` 的 19 个口共 75 个，公理集合均包含于 `propext / Classical.choice / Quot.sound`。所有非空控制、源力、实值、因果性与准备态结论均由独立 Lean 消费者内核检查。

证据为 `focused.json`、`trust-summary.json`、三份候选 strict 日志、`Audit-strict.log`、`Consumer.lean` 和 `consumer-strict.log`。

## 实际历史先生成 K

`channelLinear / channelCoefficient / gaugeCoefficient` 从有限原规范通道的 `gaugeForceOperator` 生成双线性系数。连续空间控制剖面由实际 `compLpL₂` 进入 `controlHistory`；审计核对了其 Mathlib 构造和 a.e. 作用身份，所得 force 对内部向量和空间 L² 剖面均为有界线性作用。

通用控制系数属于原实规范通道的复化。下述独立消费者另支付一个实值原控制实例，未将任意复权重误称为实 Lie 代数元素。

`preparationOrbit` 直接定义为同一个源 `duhamel`。积分的真实可积性由连续历史支付，随后证明线性、范数控制，并通过 `mkContinuous` 生成 K；没有先接收目标波包、目标空间态或目标 K 再补证明。其准确控制是

`‖K_a(t)‖ ≤ |∫₀ᵗ ‖F_a(s)‖ ds|`。

绝对值处理负时间的区间方向，证明对任意实 t 成立。`preparationMap_integral` 和 `gaugePreparationMap_duhamel` 将它认回真实强积分与原 Duhamel。原 `−i` 已由正式 GaugeForce 携带，未在输入层重复或反转。

本构造使用已认证的同一空间群 U 和实际时间坐标 t；未换用无量纲时间、虚时间或另一个背景 Hamiltonian。原物理场的相位读回继续由正式 Phase 接口承担。

## 原 w、正性与幅度

`sourcePrepared` 从原 `originalTripletCoefficients(1,1)/2` 得到 w。`sourcePrepared_inner / norm` 计算其单位范数，`sourcePrepared_actual_origin` 直接证明 `actual.matter(0)=2 embed(w)`；没有额外提供一个期望的初始内部态。

空间向量 v 由 K 实际作用得到。`transportedDensity_generated` 通过真实 Hilbert adjoint 配对证明

`K |w><w| K† = |Kw><Kw|`。

因此正密度、正泛函和平方读数均从同一个 v 生成。`spatialResponse_source_pullback` 读取的是整个组合完成后的 `K† A K`，没有在传播中间插入旧八维压缩。单位值为 `‖v‖²`；原实际幅度 2 对二次读数产生因子 4，并由 `original_preparation_amplitude` 保留。

这里的 `K†` 是空间 Hilbert 算子的 adjoint，正泛函也有其独立算子类型。它没有被识别成母作用的 independent dual 字段，没有改变原 χ 或用共轭物质覆盖 χ。

## 非空性由实际力触发

`preparationMap_nonzero_some_time` 的输入是某时实际 force 对源向量非零，结论是某时真实 K 输出非零。证明假设所有输出消失，再用原强 interaction 导数的唯一性使该 force 消失，产生矛盾；它没有接受目标波包本身的非零证书。

归一化、单位正泛函、自伴幂等与 `0≤P≤I` 正确要求这个实际输出非零。独立负控制 `zero_time_is_not_a_unit_state` 对任意连续历史证明 `normalizedFunctional(...,0)(1)=0`；零响应没有被伪装为单位态。

## 独立真实规范控制消费者

审计未调用目标空间波包。它先选原时间 hypercharge 单通道，并由正式源矩阵证明

`T=I12`，`gaugeForceOperator(u)=−iu`。

再独立选择空间控制和历史

`b(x)=1_{|x|<1}`，`a(t,x)=max(t,0)b(x)`。

单位球体积严格正且有限，故该剖面实际属于 L²；`realCausalProfile_real_ae` 核验控制值几乎处处实，连续性和全部过去的零值也由 Lean 支付。它不是把空间常量背景塞进 L²。

`ball_control_actual_force` 通过两个指示函数的真实 a.e. 代表元证明原源注入恰为

`F_a(1)w = 1_{|x|<1}(-iw)`。

其 L² 范数由原 `‖w‖=1` 与正球体积得到严格正值。因此 `nativeHistory_source_nonzero` 在实际时间 1 提供了非空定理需要的真实 source witness。

独立终端消费者 `actual_native_history_generates_unit_occupation` 随后实际调用候选 producer，得到

**存在 t>0，使原 gaugePreparedFunctional 的单位读数为 1，preparedOccupation 是自伴投影，且 `0≤P≤I`。**

其中 t 的正性来自同一个 zero-past 历史及原 `preparationMap_zero_past`，而非手选一个假定非零的未来输出。整个证明是“原通道 → 实值连续 L² 控制 → 原 force → 原 Duhamel → 非零准备 → 单位正泛函及占据”的完整消费链。

## 分类与固定来源

K、密度、正泛函与归一 occupation 都是由给定源控制历史生成的 producer；原 w/幅度、Duhamel 身份和后续群作用是同源 readout/transport。正性来自实际 Hilbert 结构，未写入额外目标态假设。

该证书签收的是一族由原规范控制历史生成的空间准备态。它没有替均匀原源指定空间真空、CAR 全态或圈测度。

`positiveSmoothUnifiedSource`、修复后的 Dirac-dual 母作用、原 SpinPair、实际时间以及 Stage10 root/current/next 均保持不变。
