# 实标量源核与适配块行列式认证

**Verdict: certified，按两层证据分别签收。** 2026-09-19，独立审核
`real-scalar-sector/{compute.py,check.py,receipt.json,exact-check.log}` 与
`scratch/LowEnergyScalarSymbol/{Quaternion,Determinant}.lean`。
前者支付当前真实源到 43 实维基及背景色作用的精确计算；后者支付定义好的适配块矩阵的
普遍行列式、4×4 块逆与原参数代入。**没有把矩阵索引数 43 当作 Lean 中的源核维数定理。**

本组为从属 source readout / block-algebra 认证。原 source、Dirac-dual action、
visit 10 / tick 16 / materialEntry 与 visit 11 / tick 17 后继保持；没有新 authority。
原场方程到该矩阵的 ScalarBlock 桥不属于本次范围。

## 源输入与实结构

原 scalar 是 Λ⁴ℂ⁷，原 exterior basis 给出 35 复坐标。
程序按 Re35 / Im35 顺序实化为 70 坐标，实内积正是原
`scalarCoordinatePairingRe = Re ∑ conj(xᵢ)yᵢ`。

源身份已逐项核对：

- 原 positive vacuum 等于 `finiteGenerationJointBreakingScalar` 的四个单位外幂项。
  producer 从该定义读取；独立 checker 所消费的旧 scalar receipt 又经本审计直接与当前四项源码比对。
- P286 Lie 输入确为原 `diag(C₃,W₂,y,−y)` 的 12 维实基。
  反对称生成元的轨道列放在 Re 部分；虚对称、虚对角与 hypercharge 列放在 Im 部分。
- 混合 M 的两个外幂输入为 `+(1,5)`、`−(0,5)`，来自原 sourceColorDoublet、
  spinPairCoefficients 的右手分量及 `P_R=diag(0,0,1,1)`。14 个复输出槽覆盖其实际可能非零的 Λ⁶ 输出。
  两套计算分别用插入排序符号与独立的补集／余子式符号重建 M。
- 原 Lie action 的定义是在外幂的每个槽插入 fundamental matrix 并求和。
  这里使用该导出作用，没有使用 `1+A` 群输运或附加阶乘。
- 三个背景色生成元从当前 `sourceColorRaw` 的矩阵文字直接解析，并由已有
  `sourceColorP286Generator_color` 对齐实际 gaugePotential。
  完整实化为 `[Re T,−Im T; Im T,Re T]`，因而保留原虚部符号。

这里的 P286 orbit 指真空的实 **Lie 切向轨道** `spanℝ{Gφ₀}`。
目标空间为 `K = kerℝ M ∩ (spanℝ{Gφ₀})⊥`。

## 当前精确程序签收

| 对象 | 精确结果 |
| --- | --- |
| 实 scalar 载体 | 70 维 |
| 12 列实切向轨道 | 秩 9 |
| 实化混合矩阵，28×70 | 秩 18 |
| `[orbitᵀ; M_real]`，40×70 | 秩 27 |
| 完整零空间基，70×43 | 秩 43 |
| 三背景色生成元的 Casimir | 秩 20 |
| 同一适配基的分解 | 23 实 singlet + 5 个四实维 quaternion 块 |
| 旧实子空间与新增正交投影 | 40 维被包含；新增 3 维全为背景色 singlet |

计算实际检查 `M_real orbit=0`、全部零空间约束、Gram 非退化、正交投影的对称与幂等、
三个完整作用对 K 的不变性、Gram-skew，以及同一个可逆适配基对全部三个生成元的 intertwiner。
这给出上述定义 K 的全部 43 维，不是先挑出一个维数为 43 的候选子空间。

singlet / quaternion 分类针对这三个实际背景色生成元构成的 SU(2) 子代数，
没有将其改称整个 P286 的 singlet 分类。
新增三维投影还被本审计直接乘以完整约束矩阵，结果逐项为零。

fresh producer 写入临时目录，所得 receipt 与冻结候选解码后完全相等；未覆盖原 receipt。
独立 checker fresh 通过，四项实际负控制全部拒绝：实维数字段改为 40、
混合矩阵条目篡改、核基条目篡改、一个色块系数翻号。
其中原日志的 “mixed Yukawa row deleted” 标签实际操作是修改一个条目，本认证按该真实操作记录。
全部运算使用整数／Fraction，没有浮点容差。

原源基到适配基的这层结论属于已重放的精确程序证据，未冒称 Lean 端到端源码分支定理。

## Lean 块算术与精确连接

补充 [source_seam_check.py](source_seam_check.py) 直接解析当前 Lean `quaternionSkew` 的线性系数，
核验 receipt 的三个 4×4 生成元逐项等于其三坐标基矩阵各除以 2，轴顺序与符号相同。
Python 的第 `23+4b+i` 坐标对应 Lean 块索引 `Sum.inr (i,b)`；Audit 实际消费这个块读回。

Lean 证明对任意复 momentum，`Q(p)² = −(∑pᵢ²)I`，并对
`B(c,a,p)=cI+i a Q(p)` 给出

`det B = (c²−a²∑pᵢ²)²`，

以及分母非零时的实际逆 `B⁻¹=(c²−a²∑pᵢ²)⁻¹ B(c,−a,p)`。
独立消费者同时验证实际矩阵逆的左右乘积均为 I。
这里的平方和是代数 `∑pᵢ²`；实动量消费者使用逐坐标实数嵌入。

原 `gaugeScale²=18/25` 由原 Parameters 定义在 Lean 中证明。
`reducedSymbol 23 5` 的完整行列式因而为

`(z−(p²−2))²³ · ((z−(p²−73/50))²−(18/25)p²)¹⁰`。

每个四维块贡献二次式的平方，五块产生指数 10；总次数为 43。
Lean 还给出该适配矩阵行列式为零的精确析取条件。
z 在本组是自由复参数，原场方程对 z 的物理识别由独立方程桥承担。

## 严格验收与范围

两候选及最终 [Audit.lean](Audit.lean) fresh 执行
`lake env lean --trust=0 -DwarningAsError=true`，全部 **EXIT 0**；无宽构建。
12 个候选公开声明加五个消费者，共 **17 项**最终传递公理检查，
全部属于 `{propext, Classical.choice, Quot.sound}`。
消费者覆盖适配矩阵索引、同块读回、实 momentum 代入、左右逆，以及实际 regular / singular 对照。
无候选 `sorry`、`admit`、`native_decide`、自定义 axiom 或新增信任绕过。

日志保留一次 Audit 的不等式重写问题，修正只涉及消费者；最终成功段已单独核验。
mouth lint 只提示仓库惯用的 `autoImplicit false`。
Lean 输出见 [lean-audit.log](lean-audit.log)，精确程序重放、负控制和源连接检查见
[program-audit.log](program-audit.log)。
按上述程序／Lean 分层口径签收；未发现影响当前候选结论的实质缺陷。
候选源码、程序与冻结回执未改动，未 stage 或 commit。
