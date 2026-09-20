# 原完整活跃二次作用独立认证

**Verdict: certified。** 原289变量、637个一阶 jet 坐标的四块二次作用、3071个 Euler 符号单项式、三步辅助场消元、Ward 行操作和五态源解读回均通过。没有候选修复项。

## 冻结对象与来源

- Lean：`LowEnergyActiveGauge/Phase.lean`；附审 `LowEnergyWard/Potential.lean`。冻结时为 scratch 路径；上游已认证的 ActiveSector／ScalarBlock 迁入正式路径不改变这些 proof bodies。
- 精确计算：上一层 `compute.py`、`receipt.json`、`exact-check.log`。
- 原 `positiveSmoothUnifiedSource`、repaired Dirac-dual form-native action、`SpinPair.actual`。本次为从属 producer/readout，原 `SpinPair.visit 10 / tickAt 16 / materialEntry` 及 tick17后继保持。
- 未审计未冻结的 `symmetries.py`；没有接受13个规范核或完整物理极点作为前提。

## 原作用逐块核对

程序的输入是原背景、P286 基、H／J 基及独立字段的一阶 jet。`Jet` 是按总次数≤2截断的多项式代数；输出 H 由四个二次多项式逐项变分生成，没有导入目标 Hessian、期望 Euler 行或目标逆。

| action 块 | 源定义与关键核验 |
| --- | --- |
| Gravity BF＋simplicity | `StageNineFormNativeMotherAction.generatedFormNativeGravityBFDensity/ConstraintDensity`；历史 lowered curvature 在 BF 中只升一次，故该交叉项没有第二个内指标号数；B 内对偶和 multiplier 项保留原 Lorentz 符号；BF／约束不乘体积 |
| P286 gauge | 原三个 native pairing 和 `K_e=σ⋆_e`；`⋆_e=(∧²e)⁻¹ J(∧²e)` 使用 live coframe；原 U1 pairing 的单位值是1，母迹限制的值是2；曲率完整保留 `B₀[a,a]` |
| Scalar J | 原实标量配对、正号 kinetic 与 `−‖φ−v‖²`；背景 `D₀v=0` 使二次系数只需要一阶协变 jet，仍含 gauge/scalar 两向交叉项 |
| Dirac H／独立 dual | 原 `Re χ(iΓ_e^μ D_μψ)`；ζ的实虚部独立，未替换为 ξ 的共轭；cofactor `det(e)e⁻¹` 保留全部16个 coframe 方向和体积项 |

背景 lapse 为正，因此 `abs(det e)` 在本点的二阶展开等于 `det e` 的展开；程序没有声称该替换对另一取向全局成立。
原零 chart 的 scalar／matter／dual frame-relative 读回恒等式保持，程序没有另冻一个随点变化的源 frame。

`Phase` 由原 upper/lower phase 证明 primal 与独立 dual 均按同一侧 R 旋转、`RγR=γ`、R 与 spin 偶积交换，并证明真实坐标导数。独立消费者把 `rotation_live_gamma_phase` 实际用于任意原 `inverseCoframeDiracGamma geometry 0`，得到 `frequency·Γ_e⁰γ⁵`，没有把 e 偷换为背景 e₀。由此常系数共转二次作用可以用于全部289个背景 Euler 读回；零值来自生成的未微分一次系数自动相消。

## 独立变分与矩阵核验

[`independent_check.py`](independent_check.py) 不导入候选 `compute.py` 或它的 `Jet/Number`。它消费已认证的外幂 bit 算法，从原 γ 文字和四项真空重建 source coefficients，以独立矩阵二阶变分公式核对四块 action：

- cofactor 使用 determinant 的 trace 二阶公式；Hodge 二阶由 `(∧²e)⋆_e=J(∧²e)` 逐阶解出；曲率、BF、simplicity 和独立 dual kinetic 用原矩阵双线性式逐阶求导。
- 四组稠密有理一阶 jet 覆盖289个实字段和637个已登记值／导数槽。四个 action 块各自精确相等，没有用总和掩盖跨块误差。
- 反控制分别改用母迹 U1 配对、删去原背景 commutator 接触项、冻结相位项中的 inverse coframe，均产生非零差值。候选另有删除 `B₀[a,a]` 后 Ward 不闭合的独立反控制。
- 从已存的四块二次作用重新生成全部3071个 Euler 单项式，和 H 一致；逐系数核验 `H(p)^T=H(−p)`。这里 `p=(λ,ik₁,ik₂,ik₃)`，并未将共转内部复结构当成 Fourier i。

四组 action 数值探针是独立回归控制；完整二次作用识别由已检查的源公式转录与精确生成程序承担，没有把有限探针称为 Lean 的全源识别证明。

## 消元保留原方程

程序依次消去 gauge B 的72维、gravity B＋multiplier 的72维、Lorentz connection 的24维，维数为 `289→217→145→121`。独立审计对每步实际常数代数块核验两侧逆，并用完整回写矩阵 E 检验 `H E` 的被消行精确为零，其余行给出登记的 reduced operator。未向程序供应 Cartan inverse 或目标 reduced H。

全12个源规范参数的 tangent T 保留 `δA=[X,A]−dX`、`δB=[X,B]`、`δψ=ρ(X)ψ₀` 和独立 `δχ=−χ₀ρ(X)`。全符号的 `HT` 恰好只剩原势的 scalar torque；该矩阵为 `−2N E_J^T Orbit`，秩9。

附审的 `Ward.Potential` 在原 Lean 势函数上证明：

`sourceTorque = −2 Volume · ⟨ρ(X)v,φ−v⟩`，

并在非退化 coframe 上证明全部 torque 为零当且仅当偏差属于原 `orbitAnnihilator`。独立源消费者沿真实轨道方向核验该负号。因而此处的9项 scalar 条件是原方程生成的约束。

选取源 J 的9个 pivot 后，scalar tangent 子块为单位矩阵。以 `T_broken(−p)^T H(p)` 替换原9个 scalar 行所得到的行操作为多项式矩阵；独立 checker 显式核验其左右逆。新 scalar 行只有可逆常数 torque 块；消去 η_J 后得到112个等价方程，旧 scalar 方程由逆行操作完整恢复。这不是删方程或补入 gauge fixing。

## 同源五态消费

独立 Lean 消费者从已形式化的 `Spectrum.actualJacobian` 读取索引 `(0,1,2,3,6)`，没有重新假设矩阵。所得五态 Jacobian 与程序重新微分原 generator 的结果一致，包含相位对 a／α 的反馈。

程序的 lift 使用原 coframe、A、独立 matter/dual、Cartan、`B_gravity=J(∧²e)`、`λ=J B−raise R` 和 gauge constitutive 写回。审计核对这些写回的源表达式，并把实际 lift、lift·J、lift·J² 重新送入完整 H；全部289×5残差为零，lift 的秩为5。特征多项式为

`X (X²+648/125) (X²−50/3)`。

上述 source coefficient、消元和五态互联是精确矩阵结果。完整289 action Hessian 的 Lean 源等同定理及物理极点不由本认证代填。

## 验收文件

- [`focused.log`](focused.log)：Phase、Potential fresh `--trust=0 -DwarningAsError=true` 全 EXIT0。
- [`Audit.lean`](Audit.lean)、[`lean-audit.log`](lean-audit.log)：19个候选声明＋7个独立源消费者，共26项公理检查，只有 `propext`、`Classical.choice`、`Quot.sound`，严格编译 EXIT0。
- [`dependency-promotion.log`](dependency-promotion.log)：上游迁入正式路径后，重新编译 Phase、Potential 与本组 Audit，全 EXIT0。
- [`replay.log`](replay.log)：冻结程序重新运行通过；完整 JSON 除运行时间外与冻结 receipt 一致。
- [`independent-check.log`](independent-check.log)、[`independent-receipt.json`](independent-receipt.json)：独立变分、两侧逆／回写、Ward逆行操作及289×5消费全 PASS。
- theorem-mouth lint 只有仓库既有 `autoImplicit false` 提示。候选无 `sorry`、`admit`、新增 axiom 或 `native_decide`。审计未改候选、未提交。

复验：

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/active-gauge/compute.py --root . --out /tmp/active-gauge-audit-replay.json
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/active-gauge/audit/independent_check.py --root .
cd Lean
lake env lean --trust=0 -DwarningAsError=true ../Verification/physics/low-energy-phenomenology/active-gauge/audit/Audit.lean
```
