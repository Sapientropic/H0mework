# Global6 全时间与全实耦合独立认证

**Verdict: certified.** `GlobalRadial`、`GlobalWindow`、`GlobalGlue`、`GlobalFlow`、`GlobalResponse`、`GlobalOriginal` 六个冻结模块通过独立默认严格复验。它们从同一原源历史生成全部实 epsilon、任意 start/initial/time 的真实发展；没有发现候选缺陷。

48 个公开口、3 个原消费者、12 个独立声明与原样复用的 47 个源夹具，共 110 个精确公理回执仅使用 `{propext, Classical.choice, Quot.sound}`。见 [focused.json](focused.json)、[consumer-focused.json](consumer-focused.json)、[trust-summary.json](trust-summary.json)。全部编译使用默认预算、`--trust=0 -DwarningAsError=true`，无新增公理、`sorry`、不安全求值或预算放宽。

## 任意有限窗口确由原方程生成

`boundedRadial v=(1+‖v‖)⁻¹ v` 的范数界及全空间 2-Lipschitz 由实际范数代数证明。给定初态 u 后，辅助场为

`sphereField(t,v)=G_epsilon(t)[(1+‖u‖) boundedRadial(v)]`。

在任意有限 `[-radius,radius]` 上，原 R 的连续性生成 M；辅助场全空间界为 `L=|epsilon| M (1+‖u‖)`，Lipschitz 常数为 `2L`。Picard 球以初态为中心，取 `a=2 radius L+1`、初始内球半径 0，所以从窗口内任意 start 出发的最长时长均由同一个实际位移界支付。没有 `|epsilon|≤1`，也没有把时间窗口缩为 epsilon 或初态相关的小区间。

辅助场始终是原 skew 生成元乘一个实因子。`sphere_curve_norm` 在每个点直接消费真实解的导数，证明范数保持；它没有要求对径向范数函数另作可微性假设，也没有假设解先留在目标球面。随后 `sphere_curve_original` 用已生成的 `‖v(t)‖=‖u‖` 把该因子精确化为 1，得到同一曲线、同一时间变量下的原 ODE。辅助场在球面外可以不同，且不作为原方程全空间恒等式使用。

## 选择与拼接没有连续性偷运

`perturbed_global_exists` 分别从每个有限窗口生成真实解，再取 `radius(t)=|start|+|t|+1` 读取候选值。这个窗口选择函数的连续性不是 premise。

`agrees` 对任意两个有效窗口，在半径的最小值对应的共同区间上调用已证原唯一性；原 start 和待读时刻都严格位于共同区间。因而全局读取曲线在任意 t 附近，最终等于一个固定真实窗口解。`HasDerivAt.congr_of_eventuallyEq` 支付真实全时间导数，未对窗口选择求导。无效半径的兜底分支不会进入实际 `radius(t)>0` 的读取。

`globalPerturbedDevelopment` 由这一存在定理选择全参数曲线；公开 `globalLocalDevelopment` 直接消费原 P286 局域 R。所求发展、范数守恒、全窗口兼容性或参数连续性均没有留为 producer 输入。原历史只需每个有限区间的连续界，不需整条实轴统一的 M。

## 传播、导数与原钟

- 真实全时间范数守恒先生成差曲线唯一性，再生成复线性、任意中间时刻组合及双侧逆。`unitary` 的逆就是交换同一源发展的起止时刻。
- `physicalCurve=U(time) v(time;start,U(-start)u)` 保持起点并支付实际无界生成元定义域测试的弱方程。源 U 仍按强连续空间群消费，没有引入其算子范数时间连续性。
- `window` 保留原 global curve 本身。针对任意指定 time，以 `|time|+1` 为窗口半径消费已认证的二阶余项，从而得到该时刻的状态、算子范数和 current 的 epsilon=0 导数。global `physicalOperator` 对所有实 epsilon 都由真实幺正传播构造，没有旧图的自由延伸分支；局部图仅用于零点附近的导数识别。
- 原 `U_original` 交互方程、准备总相位 `P(time+preparedAt)`、范数与原 current 等式均为全部实时间及实耦合的声明。真实原 retarded 积分作为全时间场导数，原 T/B 权重与完整 Stage10 组合继续支付同一准备 current 的全时间 Kubo 导数。

## 独立实际消费者与控制

[Consumer.lean](Consumer.lean) 使用原 native 时间超荷 `T=I`、合法 L∞ 控制及真实非零 L² 球初态。它直接调用新的 `globalLocalDevelopment`，并由真实全局唯一性证明对任意实 epsilon/start/time：

`W_epsilon(time,start)u=exp(-i epsilon(time-start)) U(time-start)u`，

以及完全对应的 `U_original` 公式。明确机器实例包含 epsilon=3、start=100、time=-200，得到 `exp(900 i) U(-300) forcedBall`；未回退到自由图。

增长的真实局域控制 `boundedHistory(t)=max(t,0) boundedBall` 也直接进入 global producer。epsilon=-7、time=-1000 的消费者精确恢复原自由过去发展。另从实际因果 L² 准备历史的非零力生成某个 `preparedAt>0`，证明同一个原准备字段对所有实 epsilon/time 都保持单位范数。原准备 Stage10 current 导数和任意时刻的真正算子范数导数同时通过内核。

[independent_check.py](independent_check.py) 重建原时间超荷 T，核对径向因子在真实轨道上为 1、在显式离球向量 2w 上为 2/3。连续但无全时间统一界的 `R(t)=max(t,0)I` 给出精确未来相位 `exp(-i epsilon t²/2)`，在零点与过去的值及导数正确接合；任意有限窗口的 Picard 位移余量恒为 1。大正/负耦合与长正/负时间控制见 [independent-receipt.json](independent-receipt.json)。非交换 A01 的完整有限 epsilon 指数及原 current 导数已在上一证书精确通过，本轮直接复用其回执，没有重复宽回归。完整 L² 与任意窗口拼接的普遍性由本次 Lean 证据支付。

本证书签收同一原背景与源历史上的全空间物质发展及消费者；source/root/current/next 保持。只新增本 `global/audit/`，未修改冻结证明、active 或 Git 索引，未提交。临时夹具构建产物自动删除，`git diff --check` 通过。
