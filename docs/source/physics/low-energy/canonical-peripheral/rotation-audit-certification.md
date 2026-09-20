# 全三动量外围 canonical 旋转输运独立认证

**Verdict: certified。** 冻结有限旋转与全方向输运胶囊通过，没有候选修复项。已认证的轴向最大性双向输运到所有实三动量，得到522／524／530维分类。

## 对象与同源入口

本组覆盖上一层 `compute.py/receipt.json`、`transport.py/transport.json` 及 README。两个冻结程序 fresh replay 均 EXIT0，完整输出与冻结数据相同，有限旋转只排除运行耗时字段后比较。

消费[已认证外围轴向发生器与完整 Smith 分类](../../audit/certification.md)、原 FullPhase 系数，以及[已认证正式 Circle／Alignment](../../../active-gauge/rotation/audit/certification.md)。原 source、Dirac-dual action、actual、visit10／tick16／materialEntry 与 tick17 后继保持。本组是同一外围1082载体的从属 transporter；原289旋转只作为限制矩阵的消费者。

## 有限 exterior 构造与全部角参数

[独立程序](independent_check.py) 不导入任何候选计算模块。它直接解析当前原 γ、`sourceColorPauli` 和四项 v，由基本二色矩阵

`F2(z)=(1−z²)I2−4z·sourceColorPauli`

的真实 exterior 子式重建 Λ6、Λ2、Λ4 作用：没有占据二色位的分量固定；占据一位的分量使用 F2 对应元素；同时占据两位的分量由 `det F2=(1+z²)²` 生成。这一路没有使用候选的 infinitesimal 平方关系来供应有限矩阵。

再由原 spin 分子 `(1−z²)I4−2zγaγb` 生成全252维 U。与候选逐项相同，dual 为真实 `U(−z)ᵀ` 分子。统一除以 `(1+z²)²` 后，全部实参数上的左右逆、unitary 身份和 canonical 关系均通过精确多项式核验。

三轴都逐项支付四个 Dirac 主部、原连接常数项、原 Y、真实 FullPhase 时间项、Q 对易、原 ψ／v 固定、全部35个标量基 Yukawa 顶点及非零 M。spin 与原 right-chiral projector 对易也直接核验，没有只检查一个真空 Y 后推广到任意 scalar。

原 H 与 H⊥、两个 free 物质投影、J⊥61、K43 和18实混合标量都保持。原252系数的时间与三个空间恒等式在全部 z 上成立；free 864 实字段通过原投影的保持和完整系数等变支付。原289中 J／primal H／dual H 限制矩阵随后逐项吻合，未被用作外围源输入。

在 z=±1 时，空间矩阵相同而完整 spin/color lift 不同。独立反控制保留了这一差别，没有把 lift 宣称为仅由 SO(3) 矩阵决定的单值对象。

## 原 Cauchy 系数与实化

审计从已认证原发生器及三个实际 scalar／matter 背景作用，独立重建132块和86块的常数、三个线性动量系数、平方半径系数。全部与新冻结回执相同，轴向特化返回原发生器。

标量位置和速度采用同一有限矩阵；因此真正运输原 Cauchy 数据。场框架及其逆按全部参数精确核验，原132和86系数给出

```text
A(R(z)ᵀq) S(z) = S(z) A(q),
S132 C = C S84,
D S132 = Sdual48 D.
```

内部复系数先实化，再插入外部 Fourier `i qj`。canonical 关系 `U⁻ᵀ S=S conjugate(U)` 与独立 dual 作用均保持；没有把 Fourier 复化当作内部物质共轭。非轴向的正负动量消费者另行生成各自框架，核验两最大纤维的基空间互为复共轭。

## 每个真实方向与全部导约束

独立程序直接读取当前正式 Hodge 文件的 `rotateY/rotateZ` 字面矩阵，精确证明它们与本组有限空间矩阵相同。正式 `circle_surjective` 的实参数全覆盖、`momentum_alignment` 的所有非零实动量及零动量消费者，均经过本轮 fresh strict 接口消费。

空间与字段的实际顺序是

```text
R=RY(y) RZ(z),   Rq=r e3,
L=SZ(z) SY(y),   L⁻¹=SY(−y) SZ(−z),
A(q)L=L A(r e3),   DL=Ldual D.
```

这是源角参数矩阵的组合结果。零动量采用 identity；负 z 轴、负横轴和负 y 轴的参数分支也由独立实现实际核验，没有留下反极点分母。

[Source.lean](Source.lean) 额外严格证明普遍矩阵消费者

```text
A^n L = L B^n,
D A^n L = F D B^n    对每个 n≥0。
```

输入只有实际发生器的 degree-one intertwining 和实际约束 intertwining；没有把全导约束目标作为 premise。取已验证的 `B=A(r e3),F=Ldual`，F 与 L 的真实逆给出导约束核的双向对应。因此轴向 Smith 分类的必要性与充分性、最大性一起被保留。原限制发生器 G 原样运输，L 不含时间谱参数，所以特征多项式及局部重数保持。

这里的普遍性由正式实方向覆盖与全部角参数／系数恒等式支付，具体动量消费者不承担覆盖前提。

## 实际源消费者与反控制

冻结的两个三分量皆非零动量及原点，均由同一动量生成参数公式重新恢复。它们的原字段 W、限制 G 与回执相同，`AW=WG,DW=0` 及满秩成立，再直接回写全部70个 scalar、504个 primal、504个 independent-dual Euler 行。

两个非零消费者实际拒绝错误的 `SY SZ` 字段顺序，也拒绝只旋转 scalar 位置而冻结其速度。例外消费者由原 M 直接计算 `rank(Mη)=8`；一般与原点的该秩为0。

结合轴向完整分类，结果为：

| 原三动量 | 最大复化 Fourier 纤维维数 | 原 Mη 秩 |
| --- | ---: | ---: |
| `|k|²>0` 且 `|k|²≠5929/1800` | 522 | 0 |
| k=0 | 524 | 0 |
| `|k|²=5929/1800` | 530 | 8 |

一般相互作用块特征多项式直接读回为 `(X²+w+144/25)²−(576/25)w`，`w=|k|²/2`。原 `q=k/√2,τ=N√2t`、FullPhase 物质相位和原时间频率读回均保留。

此处签收逐动量的最大 canonical 制备纤维；没有把例外球上的纤维计数直接当作平方可积波包或物理外态的自由度，也没有把 canonical 子类替代整个独立 dual 理论。

## 回执

- [独立程序输出](independent-check.log)、[独立回执](independent-receipt.json)：源 finite exterior、全部矩阵系数、原回写、实场恢复及反控制全 PASS。
- [strict／公理输出](source-lean.log)：Source.lean EXIT0，3个正式公开源口和3个独立消费者共6项传递公理均为标准三公理。
- [冻结重放](replay.log)：两个程序 EXIT0，矩阵数据完全相同。
- 候选没有修改，未提交；所有新增审计材料仅在本目录。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/canonical-peripheral/rotation/audit/independent_check.py --root .
cd Lean
lake env lean --trust=0 -DwarningAsError=true ../Verification/physics/low-energy-phenomenology/canonical-peripheral/rotation/audit/Source.lean
```
