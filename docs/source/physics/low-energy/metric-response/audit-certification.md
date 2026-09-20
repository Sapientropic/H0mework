# 原耦合静态度规响应认证

Verdict: **certified**。冻结 `compute.py`、`receipt.json`、`exact-check.log`、`README.md` 的原背景、静态 k₃ 轴响应范围全部成立。候选未改、未提交。

## 真实 metric 源与相容性

独立检查读取当前 `RawLorentzianMetricHodgeRecovery.lorentzianMetricOfCoframe` 与 `minkowskiInternalMetric`，从
`g(e)=eᵀηe`、`η=diag(−1,1,1,1)`、实际 `e₀=diag(N,1,1,1)` 对16个 coframe 基方向逐一求导，重建

```text
δg = e₀ᵀηh + hᵀηe₀,    N=3√30/25.
```

十个独立分量顺序为 `00,01,02,03,11,12,13,22,23,33`。重建的 M 与冻结 10×121 映射逐项相等，其余168个原字段列为零。单位 J00 是**纯时间度规分量的坐标源**：原 coframe `(0,0)` 方程注入 `−2N`，没有其他原字段的直接注入。

源约定为原局部作用密度中 `+∑μ≤ν Jμν δgμν`，完整注入是 `MᵀJ`。独立检查保留全部四个形式动量，逐单项式验证 `M T9=0`；相容性针对原三个 SU2 与六个 Lorentz 方向，未插入额外 diffeomorphism 核。

本组消费[原作用289坐标](../../active-gauge/audit/certification.md)及[faithful103商](../../active-gauge/quotient-audit/certification.md)。原 source、修复 Dirac-dual action、actual、visit 10 / tick 16 / materialEntry 与 tick17后继保持；本组是从属经典线性响应 consumer。

## 完整原方程与辅助回写

取 `λ=0,k=(0,0,√2q)`。实际103矩阵中只有已认证的30维、33维块承受这十列源，分别4列、6列。fresh 原程序实际求解这两块；独立检查不复用其 fraction-free solver，而直接在精确代数数有理函数域上验证给出的场列。

从**原289矩阵**重新构造实际各块方程，逐轮核验辅助块逆的左右乘积、`W=−D⁻¹H_eliminated,retained`、实际 Schur 矩阵及完整十列的回写：

| 正向消元 | 剩余坐标 |
|---|---:|
| gauge B 的72个字段 | 217 |
| gravity B / multiplier 的72个字段 | 145 |
| Lorentz connection 的24个字段 | 121 |

重建所得121矩阵与原生产者完全一致，取同一 faithful section 后得到同一103矩阵。反向次序确为 Lorentz → gravity B / multiplier → gauge B。

独立计算最终支付全部 **289×10** 有理函数恒等式

```text
H289(q) F(q) = Mᵀ,
H289(q) (−F(q)) + Mᵀ = 0.
```

原 scalar 行及九个 section 删除坐标均按真实方程核验，没有把它们直接视为无关行。因而正号外源的诱导字段为 `−FJ`，诱导度规为 `−RJ`，其中 `R=M F`。这是在有理函数域中的真实响应，通常实动量点按相应分母非零处解释。

受源场的 independent dual 也从当前原 `diracAdjointSpinSwap` 重建并验证
`ζ=Lψ`、`L=√2 diag(S₁₂,−S₁₂)`，保留原虚部负号。因此 canonical 条件由实际受源字段满足，没有预先删掉独立 dual 的方程。

## 全100条目与原时间响应

独立核验 `R=M F`、`R(−q)ᵀ=R(q)`，逐一对全部100条目求分子/分母 gcd，确认约分后的分母在 q=0 非零。72个恒零条目也包括在完整检查中。其有限延拓矩阵与冻结值逐项一致，故

```text
lim(q→0) q² R(q) = 0₁₀×₁₀.
```

实际时间条目精确为

```text
R00,00(q) = N³ (625q⁶+7800q⁴+15984q²−31104)
                 / (625q⁸+2550q⁶+7704q⁴+23328q²−93312).
```

由约分多项式在零点的值及最高次项独立读回：

```text
R00,00(0) = N³/3,
lim(q→∞) q²R00,00(q) = N³,
lim(|k|→∞) |k|²R00,00 = 2N³.
```

最后的2来自原 `|k|=√2|q|`，没有改变时间或动量单位。有限非零 q 的其他分母零点完整保留。

有限延拓说的是本次指定静态轴上的 **metric 读数**，不是完整场逆矩阵的延拓：独立检查在 F 中找到8个实际 `1/q` 极点，全部来自 J03 列，位于原 primal / independent-dual 行；其完整留数被 M 消去。原 H(0) 仍有已认证的零核，不能从 R 的有限值推出 H(0) 可逆或所有场有限。

## J00 与标准应力的归一关系

本候选 J 的下标是十个独立坐标系数的编号；代码没有将它定义为某个已生成的物质应力张量。原正 coframe 的体积密度为 `|det e₀|=N`。

如果采用明确的应力变分约定

```text
δS_ext = (1/2) ∫ N · ∑全部μν T^{μν} δgμν d⁴x,
```

那么与本候选的独立分量源逐项比较，必须有

```text
Jμμ = N T^{μμ}/2,
Jμν = N T^{μν}       (μ<ν).
```

非对角项的因子不同，因为标准全指标求和包含两次相同分量。独立脚本用任意对称 T 与任意 coframe h 验证了这个密度/坐标恒等式。若进一步给定纯静止源 `T^{00}=ρ/N²`，则 `J00=ρ/(2N)`，而不是直接令 `J00=ρ`。

这些是**在所写应力定义下的精确换算**。从原理论实际物质制备/current 生成这个 T、证明其能量及外态归一，并接入实验单位，仍未由本候选支付；因此本结果未识别 Newton 常数或 GeV 单位。

## 复验与反控制

- [replay.log](replay.log)：SymPy 1.14.0 fresh 重放 **EXIT 0**（51.188秒）；新旧 JSON 除计时完全相等。
- [independent_check.py](independent_check.py)、[independent-check.log](independent-check.log)：不 import 候选，从当前 metric / adjoint 源与原矩阵重建上述等式，**EXIT 0**（318.198秒）。全程为精确数域/有理函数运算，无浮点秩或抽样替代恒等式。
- [独立回执](independent-receipt.json)保存三轮实际 Schur 检查、100个非零零点分母、原点/UV值、八个完整场极点及条件性应力换算。
- 反控制实际拒绝：诱导场符号反转、对角 metric 源漏掉因子2、只保留 coframe 响应、漏回写 gauge B，以及由 metric 有限推出完整场有限。

本组没有新增 Lean 声明或公理。签收同一原背景的经典静态响应；不将这个指定通道的红外结果扩写为量子全理论 no-go。
