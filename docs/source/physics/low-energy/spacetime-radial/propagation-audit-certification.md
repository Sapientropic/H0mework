# 全波数基本解与原九通道响应补充认证

**Verdict: certified。** 2026-09-19，独立核验冻结的
`scratch/LowEnergySpacetime/{Oscillation,Propagation,Cauchy}.lean`。
本组消费[前七模块认证](../certification.md)，未修改或重开已签收候选。
未发现临界退化、除零、原时间替换或残差覆盖缺陷。

分类为 **all-momentum radial-profile producer / original nine-channel Jacobi readout**。
原 source/action、visit 10 / tick 16 / materialEntry 与 visit 11 / tick 17 后继保持。

## 三支实际基本解

设 `k²=∑ᵢ kᵢ²`，N 为原 lapse。
`fundamentalWave(k)(t,x)=Sₖ(t) cos(k·x)`，其中

| 条件 | 原时间频率 | Sₖ(t) |
| --- | --- | --- |
| k²<2 | r=N√(2−k²)>0 | sinh(rt)/r |
| k²=2 | 临界分支 | t |
| k²>2 | ω=N√(k²−2)>0 | sin(ωt)/ω |

两个含除法的分支分别使用严格的 rate 正性证明，临界分支直接调用时间恒等函数。
三分支覆盖全部实空间动量，没有以除零默认值完成临界情形。
每个固定 k 的时间函数及其速度为 C∞，真实导数满足

`Sₖ(0)=0`，`Sₖ′(0)=1`，`N⁻² Sₖ″ +(k²−2)Sₖ=0`。

Oscillation 从原 holonomic 空间导数计算 `∂ᵢ²u=−kᵢ²u`，再与真实时间二阶导数组装。
Propagation 实际得到原 `radialOperator(fundamentalWave k)=0`，
并消费前组已签收的 scalar Euler 身份；原任意测试方向的 scalar Euler 对全 k、全 ε、全时空点为零。
N 始终处于原频率公式与原标量算子中，没有时间换元。

## 临界非零与原 Cauchy 数据

单位初速度指时间因子 `Sₖ′(0)=1`；完整空间模式在初始切片的速度是 `cos(k·x)`，
在空间原点等于 1。Audit 从这条真实导数证明 `fundamentalWave k ≠ 0`，覆盖全部 k。

临界见证 `k=(1,1,0)` 满足 k²=2；在时间轴单位点，新的 fundamentalWave 读数为 1。
同一 k 的旧未归一化 growingWave 仍为零，两条 profile 的原定义均被直接核验。
带内 Audit 还证明完整 configuration 的准确关系

`configuration(fundamentalWave k, ε) = configuration(growingWave k, ε/r(k))`。

这保存了幅度归一化的来源。高波数见证 `k=(2,0,0)` 的 ω 严格正，
原正弦公式及其非零性也被实际消费。

原 scalar 值在整张 t=0 切片保持 actual；其真实原 covariant 时间速度为
`ε cos(k·x) • direction`。
Audit 直接消费 holonomicScalarCovariantDerivative，在 ε=1、时空原点读回原
`direction ≠ 0`，并核验原时间 canonical momentum 是
`−(ε/N) cos(k·x) · pairing(test,direction)`。
这些读数使用原字段与原动量，不外供速度槽。

## 完整九通道与二次余项

Cauchy 使用同一原 configuration，实际关闭通用 radial_residual 的平滑性、二次微分与
波方程前提。`fundamentalWave_residual` 对全部 k、ε 和时空点给出完整原 joint residual：
八个投影精确为零，coframe 投影为 ε² 乘同一单位幅度配置的原完整 Euler covector。
`fundamentalWave_nine_channels` 对全部 coframe 测试方向给出 ε=0 的真实一阶零导数。
原完整作用生成的二次余项保持，未被基本解归一化移除。

这些是逐点 C∞ 模式及原九通道一阶响应；本组没有 L²、波包或有限幅度全九场零残差的声明。

## 严格验收

三候选及 [Audit.lean](Audit.lean) fresh 执行
`lake env lean --trust=0 -DwarningAsError=true`，全部 **EXIT 0**；
三源 `.olean` 同次生成，无宽构建。
36 个候选公开声明加七个实际消费者，共 **43 项**传递公理检查，
全部属于 `{propext, Classical.choice, Quot.sound}`。
无 `sorry`、`admit`、`native_decide`、自定义 axiom 或新增信任绕过。
mouth lint 只提示仓库惯用的 `autoImplicit false`。

消费者覆盖全 k 非零性、原 scalar/covariant 速度及 momentum、完整 residual、临界非零解、
带内旧配置同值归一化与高波数正弦分支。真实输出见 [lean-audit.log](lean-audit.log)。
按上述口径签收；本审计未晋升、未修改候选，未 stage 或 commit。
