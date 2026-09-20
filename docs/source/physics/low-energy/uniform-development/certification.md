# 统一初值邻域、共同时间与同源唯一性认证

**Verdict: certified。** 2026-09-19，独立核验正式候选
`Evolution/Uniform.lean` 与 `Evolution/UniformUniqueness.lean`。
候选未修改；未发现目标 premise、量词偷换或字段身份遗漏。

分类为从属数学 **producer**（统一局部发展）与同源解的 **identity/readout**。
原 source、Dirac-dual form-native action、visit 10 / tick 16 / materialEntry 及
visit 11 / tick 17 后继保持，本组不改变 runtime authority。

## 统一 producer 的准确量词

对每个 `Admissible base`，`uniformDevelopment_exists` 生成一个共同 family、正初值半径 r、
正时间半径 T 和单一非负常数 C。对于闭初值球 `closedBall base r` 中的每个 initial，
同一 family 在整个 `(-T,T)` 上满足原 generator ODE、精确初值、Admissible 与时间 C∞；
同一个 C 控制所有这些时间与任意两个球内初值的 State 范数差。
半径、常数和 family 位于这些 initial/time 量词之外。

存在证明实际消费 Mathlib `IsPicardLindelof.of_contDiffAt_one` 及
`exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`，
所用向量场正是已签收的原 `Evolution.generator`。
原 Picard 定理返回同一初值球、同一时间区间和统一 Lipschitz 常数。

候选进一步由时间连续性和统一初值 Lipschitz 性取得联合连续性，
再将 Admissible 开集沿同一个 family 拉回到 `(base,0)` 的邻域。
取 `min r delta / 2` 与 `min time delta / 2` 后，实际乘积空间的 max 距离估计保证
整个闭初值球 × 闭缩小时间区间的值域都允许。这里没有逐 initial 重选时间半径。
ODE 正则性在这个已支付的共同值域上生成时间 C∞。

`UniformDevelopment.solution` 将每条实际 family 曲线连同共同时间半径封装为原 `Solution initial`。
`joint_zero` 因而消费原同一配置的完整九场证明，而不是另传目标残差。
Audit 同时从 family 在 t=0 的 admissible 与 starts 推导球内 initial 本身允许，
接回旧 `initialSolution` 时不需要外供新的每纤维 admissibility 证明。

## 全重叠区间与原九字段身份

`Solution.unique_germ` 在任意共同时间，由原生成器的局部 C¹ 性得到局部 Lipschitz 区域，
再实际调用 ODE 局部唯一性；两个 Solution 的连续性支付它们进入同一区域的值域条件。

`Solution.unique_on_overlap` 对同一 initial 的两条 Solution，证明整个
`(-min radius₁ radius₂, min radius₁ radius₂)` 上的曲线相等。
相等时间集合因连续性闭、因局部唯一性开，且由共同初值在 t=0 非空；
连通性将身份扩到完整重叠区间。没有把仅在原点的 germ 当成全区间结论。

`agrees_with_initialSolution` 将共同 Picard family 与此前已选择的原轨道直接识别。
其后真实字段消费者逐项付清：

- 五个 primitive 字段的值：coframe、规范连接、标量、matter、independent dual；
- 完整 continuum point field，包括真实引力/规范曲率、两种辅助场、乘子及协变导数；
- 原 holonomic configuration 的全部九字段 germ。原引力连接另由 `connection_generated`
  识别，辅助场和乘子由完整 point-field 身份提取。

`configuration_germ` 的九个坐标与原 `StageNineHolonomicConfiguration` 字段逐项匹配，
没有把 primitive 身份代替 Cartan、曲率或辅助字段身份。
这些身份位于共同时间条带内任意空间点的真实邻域。

## 直接消费者与严格结果

[Audit.lean](Audit.lean) 的六个公开消费者实际核验：统一正邻域中的九场解及非退化、
原 seed 上的共同常数与联合连续性、球内初值 admissibility 的内部生成、
与旧轨道的正长度全重叠身份、九字段 germ，以及一个由原 seed 直接产生的新旧 point-field germ。
后两个 source 实例实际调用存在性 producer，排除空 family 或不可能初值域。

两候选及最终 Audit fresh 执行
`lake env lean --trust=0 -DwarningAsError=true`，全部 **EXIT 0**。
13 个候选公开声明加六个消费者，共 **19 项**最终传递公理检查，
全部只含 `{propext, Classical.choice, Quot.sound}`。
无候选 `sorry`、`admit`、`native_decide`、自定义 axiom 或新增信任绕过。

真实日志保留一次审计 harness 的 let-binder 引入错误；修正只发生在 Audit，候选未变。
该失败输出不计为认证证据，最后成功段的 19 项公理已单独核验。
mouth lint 只提示仓库惯用的 `autoImplicit false`。
命令、退出值与最终公理见 [lean-audit.log](lean-audit.log)。

可按此统一局部发展与同源唯一性口径签收。共同邻域依赖 base；初值依赖在本组达到
联合连续与统一 Lipschitz，时间方向达到 C∞，不将这些类型改称初值 C¹。
唯一性针对原七维齐次生成器的 Solution 及其原场实现。
未 stage 或 commit。
