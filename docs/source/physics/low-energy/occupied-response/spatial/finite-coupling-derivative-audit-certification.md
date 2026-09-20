# 真有限演化的 Variation2 + Operator/Phase/Response 联合认证

**Verdict: certified.** 冻结的 `PerturbedVariation`、`PerturbedVariationCurrent`、`PerturbedOperator`、`PerturbedPhase`、`PerturbedResponse` 五模块通过独立默认严格复验。真实有限发展生成状态、电流以及传播算子的参数导数，并接回原时间 Duhamel、Kubo 和 Stage10。没有候选缺陷。

全部 33 个公开口、两个原消费者、六个独立消费者和原样复用的 47 个源夹具共 88 项公理回执，仅使用 `{propext, Classical.choice, Quot.sound}`。见 [focused.json](focused.json)、[consumer-focused.json](consumer-focused.json)、[trust-summary.json](trust-summary.json)。所有编译均为默认预算、`--trust=0 -DwarningAsError=true`；无新增公理、`sorry`、不安全求值或预算放宽。Mouth lint 仅提示本仓既有的 `autoImplicit false`。

## 由真实 ODE 生成导数

`perturbed_deviation_bound` 消费原自伴 R 的真实解方程与范数守恒，得到整个 `uIcc(0,t)` 上的一阶偏移界。`couplingRemainder_derivative` 对真实时间余项求导，其导数是 `(-i epsilon) R_H(s)(y_epsilon(s)-u)`；第二次均值估计给出

`‖y_epsilon(t)-u-epsilon V(t)‖ ≤ |epsilon|² M² |t|² ‖u‖`。

M 来自原 R 在固定时间段的连续界。反向时间由 `uIcc`、`|t|` 与真实区间包含关系处理。初态依赖完整保留为 `‖u‖`，没有藏入一个随初态改变的 M。

`true_family_interaction_derivative` 只假设每个小耦合成员的时间 ODE 与初值；没有假设 family 对 epsilon 连续、可微或已有线性响应。零耦合的实际值由一阶偏移界在 epsilon=0 时生成，二阶界给出 O(epsilon²)，继而为 o(epsilon)。`true_family_physical_derivative` 只在固定时刻施加有界 U(t)，得到原 `firstOrder`。`PerturbedDevelopment` 消费者使用已经由 Picard 生成的 starts/evolves，而公开 local/source 接口直接调用 `localPerturbedDevelopment`，没有留下目标解族 premise。

`current_coupling_derivative` 对这个真实有限曲线的两条内积腿求导；Kubo 的 `+i[R_H(s),B_H(t)]` 与源 response 由原同一接口读回。本包的对象已经是有限演化的参数导数，不是仿射试探路径。

## 算子范数导数的量词

`couplingOperator_remainder` 在进入任意初态 u 的证明前固定同一个 M，并以 U(t) 的等距性将向量余项逐点读回。`ContinuousLinearMap.opNorm_le_bound` 因而生成真正的算子范数不等式

`‖W_epsilon(t)-U(t)-epsilon D(t)‖ ≤ |epsilon|² M² |t|²`。

同一小 o 论证给出算子空间中的 `HasDerivAt`，D 是既有 `firstOrderOperator`。没有要求源无界 Hamiltonian 或 U(t) 具有算子范数时间连续性。

准确的全参数图是 `couplingOperator`：`|epsilon|≤1` 使用真实传播，其外使用自由 U(t)。这足够支付 epsilon=0 的普通导数；区间外的图没有被称为扰动 ODE 解。独立消费者直接检查 epsilon=2 的分支确实为自由算子。

## 原时钟、准备与同源读回

`originalCurve` 从真实 `U_original=P U` 与同一交互发展构造，并支付原交互方程。原 local T 的 Q 对易关系通过真实唯一性产生有限 curve 与 P(r) 的对易，继而得到

`originalCurve_epsilon(t;P(preparedAt)u)=P(t+preparedAt) physicalCurve_epsilon(t;u)`。

准备时刻和演化时长分别保留。原电流 B 与局域 R 仍是不同权重；实控制与实探测剖面分别支付对应物理接口。有限 current 先完整传播、形成 `W† A W`，再进入原准备与 Stage10。导数接口 `original_local_coupling_derivative` 的值则是真正由 `U_original` 构造的 retarded 积分，而非重新命名一个目标响应；`original_prepared_current_source_derivative` 将同一原准备、原密度 current 的真实导数接到已认证的旧 Stage10 Kubo 读数。

## 独立消费者与非交换检查

[Consumer.lean](Consumer.lean) 原样消费先前已认证的 native 时间超荷控制、真实 L² 球初态与真实因果准备历史。其直接结果包括：

- 同一原生 `localPerturbedDevelopment` 的算子范数导数精确为 `(-i t) U(t)`。
- 同一有限原场的导数精确为 `(-i t) U_original(t) forcedBall`。取真正生成的 `radius/2>0`，其导数已证非零，没有调用者提供非空响应凭证。
- 真实原准备 current 的导数直接消费 Stage10 源声明；全参数图在物理耦合范围外的自由延伸也被明确检验。

[independent_check.py](independent_check.py) 从原 γ 和时间 A01 数据重建 T/B，并在实际不变空间 `{w,Tw,QTw,Qw}` 中构造完整有限 epsilon 解。按 Q 的两类本征空间，两个真实 Hamiltonian 块为

`H_epsilon,±=±omega I+epsilon sigma_x∓omega sigma_z`。

脚本先证明完整指数满足初值、时间方程和幺正性，再对这个有限解求 epsilon 导数，回写全部 12×4 原切向方程。真实有限 B current 为

`sqrt(2) epsilon omega (1-cos(2 t sqrt(omega²+epsilon²)))/(omega²+epsilon²)`，

其 epsilon=0 导数是 `sqrt(2)(1-cos(2 omega t))/omega`，与两条电流腿及 Kubo 积分精确相等。误用因式分解 `-i t U(t)T` 会留下 `[H,T]` 的非零二阶时间余项，误用 T 代替 B 则得到错误的零响应。原 Q 相位在真切向上的对易同样核验。五个正/负 epsilon 与正/负时间的算子余项数值对照作为精确恒等式的补充；其普遍不等式由 Lean 支付。详见 [independent-receipt.json](independent-receipt.json)。

本次联合认证的时间范围保持在源生成的共同局部区间，导数点为 epsilon=0。原作用、root/current/next 未变。本审计只新增 `derivative/audit/`；未修改冻结证明、active 或 Git 索引，未提交。临时夹具构建产物自动删除，`git diff --check` 通过。
