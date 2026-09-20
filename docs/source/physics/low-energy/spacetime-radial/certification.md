# 原时空径向波与九通道一阶响应认证

**Verdict: certified。** 2026-09-19，独立核验冻结的
`scratch/LowEnergySpacetime/{ScalarField,ScalarEuler,Modes,Dispersion,Stress,Channels,Jacobi}.lean`。
未修改候选；未发现求和范围、原时间符号、完整作用来源或通道覆盖缺陷。
Oscillation、Propagation 及后续空间耦合工作不在本次审计范围内。

分类为原 source 上的 **spatial-profile producer / nine-channel Jacobi readout**。
`positiveSmoothUnifiedSource`、原 Dirac-dual form-native action、visit 10 / tick 16 / materialEntry
与 visit 11 / tick 17 后继保持，没有新增 runtime authority。

## 实际标量场、动量与空间算子

`configuration profile ε` 只将原 actual.scalar 写成
`direction + ε profile(point) • direction`；原其余八个字段保留。
`configuration_zero` 精确回到原 actual。原 holonomic 导数、规范连接和真实 scalar momentum
逐项参与计算，最终生成的 profile 为全时空 C∞，关闭通用 helper 的微分前提。

原逆度量时间分量为 `−N⁻²`、三个空间分量为 1，N 是原 lapse。
`scalar_algebraic` 精确给出 `−2N ε profile · pairing(test,direction)`；
`scalar_momentum` 精确给出 `N ε inverseFactor(μ) ∂μ profile · pairing(test,direction)`。
实际动量散度由这一个函数的 fderiv 计算。原 Euler 的 algebraic-minus-divergence 符号因此产生

`radialOperator(profile) = N⁻² ∂ₜ² profile − (∑ᵢ ∂ᵢ² profile) − 2 profile`，

而原任意 scalar 测试方向上的 Euler 系数等于
`N ε radialOperator(profile) · pairing(test,direction)`。
空间和为一个三项和；末尾 `−2 profile` 位于求和之外。

## 非零空间模式与临界控制

令 `k² = ∑ᵢ kᵢ²`，`r(k)=N sqrt(2−k²)`。
候选实际 profile 为 `sinh(r(k)t) cos(∑ᵢ kᵢxᵢ)`。
其真实时间二阶导数为 `r² profile`，空间各二阶导数为 `−kᵢ² profile`；
`radialWave_operator` 因而读回 `(r²/N²+k²−2) profile`。
对 `k²≤2`，原 scalar Euler 在全部 ε、全部时空点和任意 scalar 测试方向精确为零。

`k²<2` 时 r>0，原点的真实初始时间导数等于 r，证明 profile 非零。
整个 t=0 切片的 scalar 值与原 actual 相同；其速度保留空间 cos 因子。
Audit 实际核验初始切片上的协变速度，以及原时间动量
`−(ε r/N) cos(k·x) · pairing(test,direction)`。

边界 `k²=2` 时，这个已定义的 sinh profile 精确为零，configuration 回到 actual。
Audit 用 `k=(1,0,0)` 给出非零空间动量的带内见证，用 `k=(1,1,0)` 核验真实临界见证。
这些是逐点 C∞ 空间模式；本组没有 L²、波包归一化或粒子态的声明。

## 完整原作用生成的二次 coframe 反馈

对任意候选 coframe e，`scalar_frozen_density` 从原 densitized scalar action 读出

`ε² |det e| q · [ (1/2)(∑μ ∑ν g(e)⁻¹μν ∂μ profile ∂ν profile) − profile² ]`，

其中 q 是原 scalar 方向的平方范数。双重求和覆盖完整动能，势项 `−profile²` 在两重和之外。
这项括号结构与原 kinetic-minus-potential 定义逐项匹配。

`coframe_density_quadratic` 展开完整 Dirac-dual form-native local density：
原引力、约束、规范和 matter kinetic 项保持同一值；原 independent dual 的 Yukawa 配对为零；
留下上述真实 scalar 差，得到对所有 e 的精确 ε² 差公式。
`coframe_euler_quadratic` 再调用原完整密度在非退化 actual coframe 的路径微分定理，
通过真实导数唯一性生成完整 Euler covector 的 ε² 缩放。没有把期望残差作为定义或 premise。

## 九通道与有限幅度读回

四条代数／Cartan 方程通过原 scalar-write 不变性消费 actual 的已证联合解。
原规范 Euler 的新增 scalar current 由径向 skew 配对严格消去；
primal 使用原 kinetic 与 radial Yukawa 零式；independent-dual adjoint 保留原动量散度，
并消费完整任意 matter 测试方向上的 Yukawa 消去。
连同波方程产生的 scalar Euler，共八个原通道对所有 ε 精确为零。

`growingWave_residual` 因而识别完整原 joint residual：八个投影为零，
coframe 投影等于 ε² 乘同一单位幅度配置的原完整 coframe Euler covector。
`growingWave_nine_channels` 对任意 coframe 测试方向证明该投影在 ε=0 的真实导数为零。

Audit 还将 k=0 的 configuration 精确识别为已签收的原 Contact.Profile.testField，
独立消费完整作用的旧 Load 定理，读回原点时间 coframe 分量为 `ε² q`。
ε 非零时该分量严格正；这与完整九通道的一阶零响应共同保留有限幅度反馈的准确强度。

## 独立严格验收

七个候选及最终 [Audit.lean](Audit.lean) fresh 执行
`lake env lean --trust=0 -DwarningAsError=true`，全部 **EXIT 0**；
七源 `.olean` 同次生成，无宽构建。
54 个候选公开声明加八个消费者，共 **62 项**最终传递公理检查，
全部属于 `{propext, Classical.choice, Quot.sound}`。
无候选 `sorry`、`admit`、`native_decide`、自定义 axiom 或新增信任绕过。

消费者覆盖全原残差、全 coframe 测试方向、真实 scalar/动量读回、非零空间见证、临界零波、
原 Contact 同值身份和有限幅度完整作用负载。没有外供目标残差或不可能域。
审计 harness 的命名空间、有限向量化简及 lint 调整保留在日志，候选未因此改变；
最终成功段的 62 项公理已单独核验。mouth lint 只提示仓库惯用的 `autoImplicit false`。
真实输出见 [lean-audit.log](lean-audit.log)。按上述精确口径可晋升，未 stage 或 commit。
