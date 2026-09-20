# 原216自由物质谱与外腿独立认证

**Verdict: certified。** 原252→216等距载体、全部实三动量的Hermitian谱投影／双侧resolvent／原时间传播、所有交叉和零壳，以及真实原字段外腿与70标量选择律均通过。未发现候选修复项。

## 对象与来源

冻结对象为上一层 `compute.py/source.json`、`spectral.py/spectral.json`、`external.py/external.json`、`scalar_readback.py/scalar-readback.json`、对应日志及README。四程序fresh replay全部EXIT0；完整回执一致，比较仅排除两份运行耗时字段。

保持原 `positiveSmoothUnifiedSource`、Dirac-dual form-native作用及actual。`Stage10/Runtime/Occurrence.lean` 的 `visit=SpinPair.visit 10`、`materialEntry (...)`、tick16与tick17后继保持。本组是同一源的从属自由Jacobi谱／传播／外腿producer和readout，没有controller推进。

上游原Pfree及相位消费 [canonical-peripheral](../../canonical-peripheral/audit/certification.md)、[FullPhase](../../full-phase/audit/certification.md)；完整源顶点消费 [matter-vertices](../../matter-vertices/audit/certification.md)。审计未修改候选、未提交。

## 实际共同载体与原时间

[`source_check.py`](source_check.py) 不导入候选程序。它从当前Lean的γ／Pauli／四项vacuum和独立bit外幂算法重新生成原Cμ、B、Y、Q及全部Hamiltonian系数。

真实F满足 `F†F=I216`、`FF†=原Pfree`；实际源Pfree自伴、幂等、秩216。每个块的连续列区间、实际源行支持、外幂级、手征、色作用和相位荷均逐项检查，无索引遗漏或重复。79块恰为50个二块和29个四块。

| 手征χ | 外幂级 | 色单态份数 | 色双态份数 | Q荷 |
| --- | --- | ---: | ---: | ---: |
| −1 | 2 | 10 | 4 | −1 |
| −1 | 4 | 15 | 10 | −1 |
| +1 | 6 | 5 | 1 | 3 |
| +1 | 2 | 5 | 4 | 1 |
| +1 | 4 | 15 | 10 | 1 |

每个块消费原常数项及三个空间系数，生成

```text
q=k/√2，i∂tψ=(N√2)h(q)ψ，N√2=6√15/25，
hχ,s=χ(3I/2+q·σ)，
hχ,d=χ(3I/2+q·σ⊗I+(3/10)Σσj⊗σj)。
```

Y保留在原H中，`Y(v)F=0` 由真实源矩阵支付。`H Pfree`自伴且与Pfree交换；完整252维H本身并不自伴，审计反控制明确拒绝把限制结论推广到整个载体。

原相位项给出 `Hstationary=Horiginal−ωQ`、`ω/(N√2)=3/5`；所有源块都检查 `QFblock=Qcharge·Fblock`。特别是Λ6的荷为3，不能沿用其余右手分量的荷1。

## 全动量谱、原点与交叉

[`spectral_check.py`](spectral_check.py) 用实际q坐标重建小矩阵，并分别作两个首一多项式除法：

```text
r²=qx²+qy²+qz²，t²=qx²+qy²+qz²+9/25。
```

这与候选的单位方向Groebner计算独立。对 `r>0,t>0`，逐项支付全部投影的Hermitian性、秩1、幂等、相互正交、总和为I及本征身份；另从实际2×2／4×4矩阵求特征行列式，并验证两种手征的resolvent分子左右乘积。投影分母只有r的至多二次幂和t的一次幂，**没有能差分母**，故所有非零谱交叉均保留有效投影。

原时间支完整为

```text
E=N√2·χ(3/2±r)，
E=N√2·χ(9/5±r)，
E=N√2·χ(6/5±√(r²+9/25))。
```

原点另由真实spin exchange矩阵生成 `(I+swap)/2`、`(I−swap)/2`，秩为3／1；三个相撞投影先合并再取极限，全部方向得到同一triplet投影。单态spin空间保留I2。完整原点频率除以N√2的分布为

`−9/5[42]，−3/2[50]，−3/5[14]，+3/5[15]，+3/2[50]，+9/5[45]`。

全部交叉由独立二次公式及**未平方方程的符号条件**重算，覆盖186对不同频率函数；没有浮点根／秩判定。原时间12个频率函数的九个交叉半径为

`0，3/20，9/20，3√3/5，77/60，36/25，3/2，33/20，9/5`。

共转16个频率函数的12个交叉半径为

`0，3/20，1/4，3/10，9/20，3/5，63/100，3/4，4/5，9/10，21/20，6/5`。

每一交叉的全部本征空间分组和合并重数均一致，总复维数仍为216。`r=77/60` 的原频率 `±13/60` 对应合并复维数39／40；这里只保留其与外围例外球相同的半径，没有把原／共转频率或不同载体的向量混同。

| 读回 | 原物理 `|k|²` | 零空间复维数 |
| --- | --- | --- |
| 原时间 | 54/25，9/2，162/25 | 29，50，29 |
| 共转时间 | 0，9/50，81/50，72/25 | 31，5，45，28 |

平方方程产生的伪根已被反控制拒绝；在原点保留单枚parallel投影会依赖方向，另一反控制拒绝该错误延拓。

## 原字段外腿及158源口

原时间Hamiltonian源恒等式不仅给出特征多项式。审计对任意E及三动量直接支付

```text
D(E,k)F=(Γ0/N)F(EI−Hsmall)，
F†S D(E,k)=(χsmall/N)(EI−Hsmall)F†。
```

因此每个实际源本征投影中的向量都给出原primal与独立dual平面波解；其canonical partner确为 `√2ψ†S`。全70个scalar力由实际混合矩阵／原顶点归零。没有改用另一波函数或省掉独立dual方程。

全部158个原bosonic顶点的两条线性腿逐系数为零：48 gauge、24 Lorentz、16 coframe、70 scalar。审计额外把背景上下手相位列分开验证，覆盖真实背景相位，避免只用原点相位的一次抵消；coframe的完整导数及graded phase系数保留。

全部70枚原scalar顶点还独立满足 `F†S Vscalar=0`，故free-free的复读数及Hermitian实源均为零。相反方向的混合Hermitian顶点有真实非零见证：scalar坐标 `(0,0)`、free列122、原其余坐标0的**未乘1/2**条目为 `−3√10/50`。此选择律没有删除自由—相互作用通道。

## 实际API消费者与量词

[`consumer_check.py`](consumer_check.py) 调用冻结的三个实际函数：

- `source_resolution` 在非轴向 `k=√2·radius·(1,2,2)/3` 对**任意正radius**返回30个正交源投影，秩总和216，原／共转频率和每个Q荷全部正确；原点另返回15个合并源投影。
- `source_propagator` 对该符号半径及原点的**任意实原时间**返回正确指数和实际导数，`U(0)=Pfree`。普遍正交投影与实本征值同时支付两侧unitarity和时间群律。
- `source_resolvent` 在非轴向 `|k|²=2` 对**任意避开谱点的复E**实际支付完整252矩阵左右乘积Pfree。
- 五份冻结外腿重新检查其非零单位范数、Pfree归属、原primal／independent-dual／scalar方程；覆盖原点、一般非轴向点与全部三个原时间零壳。

全实三动量结论由原四个H系数、实际F和普遍投影两分支共同支付，不从上述消费者点或方向外推。resolvent的数学域为全部实k和 `E∉spec(H|Pfree)`；原场乘积为Pfree而非I252。

API输入是物理实k。对未判定为零的symbolic k，函数生成非零分支公式；要在k=0使用原点分支，不能先生成含 `q/r` 的表达式再机械代零。全实数学覆盖不等于CAS具有任意实表达式的零判定算法。单位外腿指原252坐标的Euclidean范数，未作LSZ／作用留数或空间波函数归一。认证范围是已分离的216复维自由prepared Jacobi子类，不是全部物理粒子库存。

## 证据与复验

- `source-replay.log / spectral-replay.log / external-replay.log / scalar-replay.log`：四候选fresh EXIT0，回执逐项一致。
- [`source-check.log`](source-check.log)、[`source-receipt.json`](source-receipt.json)：独立原源、216载体、全部字段／顶点，4.313秒。
- [`spectral-check.log`](spectral-check.log)、[`spectral-receipt.json`](spectral-receipt.json)：普遍投影、左右逆、原点及完整交叉，6.180秒。
- [`consumer-check.log`](consumer-check.log)、[`consumer-receipt.json`](consumer-receipt.json)：实际API及真实非空外腿，60.795秒。

本组没有新Lean声明。新增谱和完整矩阵恒等式按精确符号程序证据签收；所消费Lean源口和标准公理集沿用上游证书，没有新增axiom或冒称新的Lean端到端谱定理。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/matter-modes/audit/source_check.py --root .
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/matter-modes/audit/spectral_check.py --root .
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/matter-modes/audit/consumer_check.py --root .
```
