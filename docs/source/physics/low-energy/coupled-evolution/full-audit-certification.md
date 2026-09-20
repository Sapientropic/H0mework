# 原九场局部总装独立认证

**Verdict: certified。** 2026-09-19，独立 certify 阶段核验固定候选
`Lean/scratch/LowEnergyEvolution/{MatterStress,ScalarStress,MatterCoframe,Full}.lean`。
原九场方程的局部总装签收；候选未修改。

## 精确公开结论

`Evolution.source_local_development` 证明：对每个实参数 ε，存在 `rε>0`，使所有满足
`−rε < point 0 < rε` 的 BasePoint 均有

```lean
diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
  (solution ε).configuration point = 0
```

这是同一生成 configuration 在整个空间、非空开时间条带上的完整原 residual 零性。
量词是 **每参数分别存在正半径**；不将其解释为统一半径、参数光滑族或全时发展。

原 source、Dirac-dual form-native law、visit 10 / tick 16 / materialEntry 及
tick 17 / visit 11 保持。此项是完整原方程的局部数学 producer，没有新增 runtime authority
或宣告 controller advancement，也不宣告整个低能唯象目标完成。

## 非空实例与目标来源

`Solution` 的输入内容是原 generator 的局部轨道、原 seed、admissibility 和曲线 C∞；
其结构没有 jointZero、stationarity 或九场解字段。`solution_exists` 实际消费 Mathlib ODE
存在定理，`solution` 再从已证明的非空类型取值。Full 没有另建 solution。

实际字段仍是原 `Fields.raw`：同一曲线生成 coframe、gaugeConnection、scalar、matter、
独立 dual；原 `algebraicCartanReduction` 自行生成连接、两种辅助场和 multiplier。
所有九个分量都读取这个同一 configuration，没有 ghost field 或独立 endpoint 替代。

四个 Audit 消费者实际核验：

- 从 `source_local_development` 取得正半径，保留原 seed，并在确实属于条带的原点消费完整九场零性。
- 对条带内任意点同时消费 scale>0、clock>0、实际 coframe 非退化和原 joint residual 零性。
- 对任意 coframe 变分方向消费原完整 Euler covector 为零。
- 在 ε=1 的原点证明原 `holonomicScalarCovariantDerivative` 时间分量非零。
  该检查直接读取实际配置的导数，排除了将变分状态藏在未进入原字段的参数中。

## 九投影覆盖

复核了原 `DiracDualFormNativePointwiseJointResidualCarrier` 的全部字段与 ext 定理。
`Solution.joint_zero` 按原顺序消费如下九项，三个方向函数保持完整测试域：

| 原 residual 投影 | 实际消费的已证口 |
| --- | --- |
| gravityMultiplier | 原 algebraicCartanReduction_gravityMultiplier_zero |
| gravityAuxiliary | 原 algebraicCartanReduction_gravityAuxiliary_zero |
| p286GaugeAuxiliary | Solution.p286_auxiliary_zero |
| lorentzConnection | Solution.lorentz_euler_zero |
| p286GaugeConnection | Solution.gauge_euler_zero |
| scalar | Solution.scalar_euler_zero，任意 ScalarCoordinateCarrier 测试 |
| matter | Solution.adjoint_euler_zero，原独立 dual 方程，任意 MatterCoordinateCarrier 测试 |
| conjugateMatter | Solution.primal_euler_zero，任意 MatterCoordinateCarrier 测试 |
| coframe | Solution.coframe_euler_zero，完整连续线性 covector |

上游精确来源和直接消费已在[局部流／标量](../certification.md)、
[几何](../geometry-audit/certification.md)、[primal](../primal-audit/certification.md)、
[adjoint](../adjoint-audit/certification.md)、[规范](../gauge-audit/certification.md)、
[四约束与应力](../stress-audit/certification.md)中独立认证。本次不重复宽构建或重开这些关口。

## 最后 coframe 责任的核对

MatterStress 从原 independent dual 与原完整协变导数计算全部 16 个 kineticLoad 分量。
两端 dilution 的交叉乘积为 `s/a³`；dilution 与 boost 对该原配对的零性逐项证明，
phase 与 rotation 项保留。没有将 dual 换成 Hermitian adjoint。

原 kinetic density 沿候选 coframe 的函数是 `|det e|·inverseLoad(actualLoad,e)`。
原 primal 证明支付的是当前点的 inverseLoad=0，它在乘积求导中消去体积导数项；
inverse-coframe 的导数仍完整保留，给出非零 Dirac coframe 负载。
原 Yukawa 向量零性则证明整个 frozen-coframe Yukawa 密度函数为零。

ScalarStress 保留真实 volume 与 inverse metric 的 coframe 依赖，并冻结实际标量速度 `nw`。
其时间／空间系数精确为 `q a³(w²/2−f²)`、`−nq a²(f²+w²/2)`。
MatterCoframe 将这项与 Dirac density 的真实导数相加，再用原
`diracDualFormNativeCoframeMatterDensity_hasFDerivAt` 的导数唯一性识别原 covector。

Full 使用原恒等式 **gauge + matter − reaction**。时间方向正是已生成的 temporal balance，
三个空间对角方向正是同一 generator 的 spatial balance，其余方向逐项为零。
最后通过 `Matrix.matrix_eq_sum_single` 与原 covector 的线性性，从 16 个基方向扩展到全部变分方向。
因此并未用正常形的命名零性代替原 coframe 变分，也没有少算反作用负号。

## 严格验证与交付

最后四候选及 Audit fresh 执行 `lake env lean --trust=0 -DwarningAsError=true`，
全部退出 0；四份 `.olean` 同次生成，无宽构建。

25 个候选公开声明（21 theorem、4 def）与四个固定 source solution 消费者，共 **29 项**
传递公理审计全部属于 `{propext, Classical.choice, Quot.sound}`。
无 `sorry`、`admit`、`native_decide`、自定义公理或 kernel 跳过设置；生产目录未 import
这四份 scratch。mouth lint 的 broad simp 提醒对应有限 row/col 分情况，未构成证明或来源缺陷。
真实命令、公理与退出状态见 [lean-audit.log](lean-audit.log)。

**未发现实质缺陷，可按上述 exact claim 晋升。** 正式路径迁移后复验该总入口与消费者。
本认证只写 full-audit 目录，未修改候选、未 stage 或 commit；后继 Quantum／Spectrum 不在本页范围。
