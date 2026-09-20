# 联合独立认证：原局域电流与空间一阶 Kubo/CAR 响应

Verdict: **certified**。冻结的 CurrentOperator、LocalOperator、LocalSource 与 SpatialResponse{Evolution,Kubo,Native,CAR,Source} 八模块无声明或来源缺陷。

本次只新增本目录证据；未修改候选、根文档或提交。后一组的生产回执位于相邻 `spatial/response/`，本证书统一覆盖两组。

## 严格验收

八文件 fresh 默认预算 `--trust=0 / warningAsError` 全部 EXIT 0。局域源 32 个、响应 52 个公开口，原响应 5 个消费者，独立 14 个构造／消费者，以及原样复验的 19 个 native 控制构造共 122 个声明，公理集合均包含于 `propext / Classical.choice / Quot.sound`。

独立 `Consumer.lean` 由真实单位球 L∞ 剖面与原 native 通道生成非零局域算子；`independent_check.py` 另外从原 H12 源系数重建一个非零 Duhamel/Kubo/CAR 纤维例。两者职责不同，未用有限纤维代替连续空间证明。

## 原 T 与 B 是两个不同口

`CurrentOperator` 从原 gaugeDiracMatrix、原 lapse、spinScale、canonical spin swap 和 Q 的实际关系得到

`T=Nγ0D_g`，`B=sNSD_g=−sQT`，`[Q,T]=0`。

原 P286 数据的 skew-adjoint 性和真实 Clifford 关系已生成 T Hermitian；Q 与 T 对易再生成 B Hermitian。这里没有使用同一个“耦合字段名”来认同两个权重。

`gaugeCurrent_canonical` 直接消费原 `gaugeCurrentValue` 和 fullCanonicalDiracAdjoint，证明该原密度等于 `Re〈v,Bv〉`。`spatialCurrent_original` 把它写为真实 L² 电流积分；`spatialCurrent_integrable` 由 L² 配对可积性支付积分，而非利用不可积函数的默认零积分。

独立 Lean 消费者在原时间 hypercharge 上证明 `T=I12`、`B=−sQ`，并用两个相反手征对角元证明 B≠T。原单位 w 的两个读数分别为 1 和 0；这种区别在实际源上已经可见。

## 局域有界乘法与真实实规范场

`boundedMultiplier` 调用 Mathlib 的实际 Hölder 双线性构造 `L∞×L²→L²`。审计核对 `memLp_of_bilin`、a.e. 代表元与 norm bound，所得有界性来自真实可积性及 Hölder 指数，未加入目标算子或目标场证书。

实值 profile 的 a.e. 条件用于内积左右标量的共轭一致，得到局域 R/B 自伴。只有 L∞ 范数连续的 profile 历史，才被 `localGaugeHistory_continuous` 送入算子范数连续扰动；没有把逐点连续误当 L∞ 连续，也没有宣称自由 U 在算子范数连续。

`LocalSource` 从 P286 数据的原实线性逐级推导 D_g、T、B 的实缩放。两个局域算子 a.e. 正是 `Re b(x) • data` 自己产生的原算子；b 是规范方向的标量剖面，不是改写 Higgs/scalar 字段。

独立消费者用单位球指示函数 b∈L∞ 和此前实际生成的 `forcedBall=1_ball(-iw)∈L²`，证明原局域时间 hypercharge R 满足 `R forcedBall=forcedBall`、R 自伴且非零。又生成实值、零过去的斜坡 L∞ 历史，并直接消费 `local_force_native` 的原 P286 场读回。没有把均匀物质背景当作 L² 常函数。

## Duhamel 先生成一阶响应

`perturbationForce` 使用原 U 和真实 `−iR(s)U(s)u`。R 的范数连续性与 U 的强连续性只在固定向量上组合，生成连续 L² forcing；firstOrder 随后直接调用原 Duhamel。

真实 interaction 导数、原 generator-domain 测试的弱方程、retarded 积分和零过去性均从这个 producer 产生。对初态的线性与

`‖D(t)u‖≤|∫₀ᵗ‖R(s)‖ds| ‖u‖`

先证明，再生成有界 `firstOrderOperator`。本包没有对整条 U 或 Heisenberg 算子族实施算子范数 Bochner 积分。

`epsilonPath` 明确定义为 `U(t)u+ε firstOrder(t,u)`。其真实实参数 HasDerivAt、两条电流变分腿以及 identity current 的一阶零变化均通过。签收的是这个实际 affine 路径的导数和原弱线性化响应，未额外声称有限 ε 的完整扰动流已经生成。

独立 Lean 反控制直接在**原空间 U** 上取 R=I，计算

`firstOrder(t,u)=−it U(t)u`，

并证明 ε=t=1 时 affine 路径的范数平方为 `2‖u‖²`。它与当前一阶声明完全一致，也排除了将该 affine 路径误当有限参数幺正流的读法。

## Kubo 号数、积分与 CAR

`currentVariation_kubo` 对真实向量积分分别处理左侧共轭线性配对和右侧线性配对。扰动 Hermitian 将结果变为

**`δJ_B(t)=i∫₀ᵗ〈u,[R_H(s),B_H(t)]u〉ds`**。

核连续性只使用 `s ↦ U(−s)R(s)U(s)u` 的向量连续性。由此支付标量积分的可积性，没有假设某个随时间选取的有限基连续。

CAR 核在实际共同 span `{u,R_H(s)u,B_H(t)u}` 中读两个完整四点字。R 与 B 的 Hermitian 条件分别用于左右配对转换；单位 u 则由实际非零 sourcePreparation 的归一范数支付。`kuboCAR_continuous` 通过这个已证明的全词值等于连续 Kubo kernel，而非通过任意基选择来推断连续性。

独立计算选原时间颜色 A01 通道及原单位 w。原 H12 真正保存由 `{w,Tw,QTw}` 生成的三维子空间，在其中精确生成 Duhamel 变分及其原 Hermitian 电流，得到

`i kernel(t,s)=2√2 sin(2ω(t−s))`，

`δJ(t)=√2(1−cos(2ωt))/ω`。

时间积分通过真实反导数的导数及端点差独立核对。该例非零，换成错误电流 T 则得到 0；删掉任一变分腿或翻转 commutator/i 号也不成立。同一原三维纤维的 CAR 四点差在一个精确相位实例中为 `−32√2 i/65`，吻合原核。这个纤维例用于核对原系数与号数，连续空间结论仍由 Lean 的 L² 构造承担。

## 原 current 与原 Stage10 同时读取完整响应

`local_force_original / local_force_native` 保留原力算子里的 `−i`。`measuredCurrent` 是 detector profile 加权的原 canonical-dual current 密度积分；其实际 ε 导数通过 `local_epsilon_current` 等于 Kubo 响应的实部。

`responseOperator` 在完整 L² 上先组成

`D(t)† B U(t)+U(t)† B D(t)`，

再通过正式 PreparationNative 交给原 Stage10 sourceResponse。电流自伴时这个完整响应算子自伴；任何中间乘积都没有先压到旧八维，也未把 K 的拉回当作乘法同态。

原带五个消费者 fresh 检查了：物理密度 ε 导数=原 Native 响应实部、Native 响应=完整 CAR 核积分、真实弱方程、因果零过去和一阶归一。detector 的实值前提在物理 current 与 Hermitian CAR 口保持显式；对任意复有界观测算子成立的通用 Kubo/Native 身份没有被误说成物理实 current。

原独立 dual 仍由 GaugeCurrent 保留；这里的 current 使用已声明的 canonical-dual 准备图。原 Q、lapse、ω、原时间以及 Stage10 root/current/next 均未替换。

## 证据

`focused.json`、`response-focused.json`、`consumer-focused.json`、strict 日志和 `trust-summary.json` 覆盖联合范围。`Consumer.lean` 的重放入口为 `verify_consumers.py`；它原样临时编译已认证 native 控制支持，不向仓库写构建产物。独立原纤维与反控制见 `independent_check.py`、`independent-check.log`、`independent-receipt.json`。
