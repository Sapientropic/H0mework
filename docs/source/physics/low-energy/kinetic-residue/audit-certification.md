# 原动能配对、留数与归一化独立认证

**Verdict: certified。** 冻结 Jet／Density／Scale、完整源频率核、18类投影留数、正相位荷接口及原四腿归一化回写全部通过，没有候选修复项。

## 对象与机器检查

候选为 `scratch/LowEnergyKinetic/{Jet,Density,Scale}.lean` 及上一层 `compute.py/receipt.json/README.md`。三模块 fresh `--trust=0 -DwarningAsError=true` 均 EXIT0；39个公开口传递公理全部在标准三公理内。本审计另有5个独立 Lean 消费者，strict 与公理检查均通过，共44项。

程序 fresh replay EXIT0，完整 JSON 与冻结回执相同。所消费[完整自由源／谱](../../matter-modes/audit/certification.md)、[在壳源／原289交换](../../onshell-sources/audit/certification.md)及正式 Fermion 链保持已认证身份。原 source、action、actual、时间坐标与 controller root/current/next 不变。本组是从属真实 jet producer、原作用 readout 及归一化 transporter。

## 真实 holonomic jet 与母作用系数

`Jet.profile_derivative` 对实际场 `u+x⁰v` 在原 `matterCoordinateEquiv` 中先证明 `HasFDerivAt`，再由该定理读取 directional derivative，未使用不可微时的默认 fderiv 值。`covariant_origin/point_origin` 将同一配置原点的全部字段及 covariant jet 识别为原 `withMatterJets`，连接和 coframe 继承 actual。canonical dual 在原点始终为 `s J(u)`。

`Density.original_action_time_affine` 消费 repaired 母作用自己的 affine law，得到

`L(u,εv)=L(u,0)+εs Re(i〈u,γ5v〉)`。

原 `Sγ0=γ5`、绝对体积 `|det e0|=N>0` 与逆coframe的 `1/N` 相消都在 proof body 内支付。这里生成的是原作用的真实时间系数 `G=sγ5`，不是把目标 G 写成额外 premise。该 holonomic 场族用于读取作用 jet，没有被称作新的全时空解。

`original_action_phase_rate` 则消费同一真实 jet、速度方向 `−iQ u`，得到相位速率密度响应 `BQ=sγ5Q`。这与时间动能 G 保持为两个原作用读数。

## 完整原核及有符号自由配对

[independent_check.py](independent_check.py) 不导入候选程序。从当前 γ／γ5 字面量及已认证原 Cμ、B、Y 重建整个252频率核，独立核验

```text
N s S Doriginal(E,k) = G(E−Horiginal(k)),
G=sγ5,  s=√2.
```

原时间 E 和全部三个空间动量同时保留；原 B 与单向 Y 均未删去。随后从真实 F 的矩阵 Gram 读出 chirality 与 Q，而非只统计回执标签：

`F†G F=s diag(−1[106],+1[110])`。

全部79个原二／四维 source copy 的频率核逐项回写。这个79是216自由载体的 irrep copies 数，和交换中的79维动态算子是不同对象。

在 Hermitian 的自由限制上，审计独立读取实幅坐标的二次单项式系数，四种小块（singlet／doublet × 两个手征）全部满足

`real Hessian = 2 Realify(K)`。

删除因子2的反控制非零；没有把全252非Hermitian部分也宣称为该实Hessian公式。复 sesquilinear K 与实 Euler Hessian 的表示始终区分。

## 实际留数与双侧频率逆

独立检查不止重复 `KΠ` 的本征关系：它用已认证各支 Π，实际组装两手征、generic及origin的 action resolvent，并精确验证每个小块的左右逆。

全称方向计算只使用 `nx²+ny²+nz²=1` 与 `t²=r²+9/25` 的精确多项式关系；原点使用其合并投影，不机械代入含方向分母的表达式。12个generic和6个origin的投影身份，共18类，全部通过。

原 E 留数为 `χΠ/s`，所以自由完整算子满足

```text
GK=GH γ5/s,
K GK=GK K=Pfree.
```

频率重合时是相应带符号投影之和。此处是原 Pfree 上的逆，没有把它写成 I252。

四个实际右手在壳向量 u 的原标量频率核均为 `s(E−Eoriginal)`，逐条直接求出的 pole limit 为 `+1/s`。一个原左手单态方向给出 `−s(E−Eleft)` 和 `−1/s`。符号由原 action 核生成，不能用绝对值替换；没有因此发出全理论 no-go。

## 正相位荷接口及其准确责任

实际矩阵给出

`F†BQF=s I202 ⊕ 3s I14`。

以这些正权重生成的 FQ／RQ 双向满足 `RQ FQ=I216,FQ RQ=Pfree`。原H的常数项和三个空间系数在该接口下全部 Hermitian，且逐项 intertwine。原 FullPhase 时间项在整个252载体上读回 `N s S·shift=ωBQ`；H占据子空间上的此读数也等于原 canonical S-density。

独立检查同时保留一个关键区别：

```text
FQ† G FQ = diag(1/Qcharge)
          = −1[106] ⊕ +1[96] ⊕ (1/3)[14].
```

因此 FQ 是 BQ 的正等距接口，并没有使原动能 G 在所有216方向上变成正单位矩阵。左手单位源在同一个正尺度后，kinetic配对为−1、phase-charge配对为+1，作为实际反控制核验。

## 右110归一及原四腿交换

`Scale` 的 θ 是实际正实数 `1/√s=2^(−1/4)`，满足 `sθ²=1,θ⁴=1/2`。其 right/chirality 与 coordinate-unit 条件是明确的 normalizer 输入；程序由实际 F 的110个右手列生成非空框架 R，支付 `R†GR=I110` 和 `RR†=Pright/s`。

原四条外腿全部为 Q=1 的 right Λ2／Λ4。审计逐条验证 θu 的原 primal／independent-dual 壳、kinetic与phase-charge单位配对，以及频率核恰为 `E−Eoriginal`。外积 `θu(θu)†=uu†/s` 对应这一实际 pole line 的留数；没有把单条外腿外积当作整个退化pole投影。

归一后的全部97个 transition source从实际 θu、pin／pout 顶点重新生成，逐项等于原 j/s。再从原 contact response 与动态 field lift 组装新的完整字段，支付全部289行。动态项、接触项与总直接系数分别精确变为原来的一半；局部项为 `−9√30/100`，总数为

```text
−18908441674971446080024956804334794870926877 √30
 /45777244125740677433226341415962030179029700.
```

Lean 的 `original_current_normalized/original_scalar_normalized` 直接消费原 Exchange 口；`four_leg_amplitude_normalized` 从原双产生态及固定复线性算子得到同一1/2，未将算子本身一起重标。

旧 CAR／Fock pairing 明确保留。独立 Lean 消费者在同一原 SpinPair 上核验归一后的左右 kinetic 读数为−2／+2，而原 oneParticle Fock 配对仍为2/s。对 coordinate-unit腿，旧Fock配对是1/s，不能被改称1。这里签收原action配对、pole留数和指定外腿幅度，不自动补全量子LSZ或实验截面。

## 证据

- [focused.json](focused.json)及三份 `*-strict.log`：三个冻结模块 fresh strict EXIT0。
- [candidate-axioms.log](candidate-axioms.log)：39个公开口标准公理。
- [独立 Lean 消费者](Consumer.lean)、[严格输出](consumer-strict.log)：5项实际jet、左右手与旧Fock反控制全部通过。
- [独立矩阵程序](independent_check.py)、[输出](independent-check.log)、[回执](independent-receipt.json)：全源核、双侧逆、真实频率留数、两种配对及原交换归一全 PASS。
- [replay.log](replay.log)：冻结程序 fresh EXIT0，完整 JSON 相同。
- [attention.log](attention.log)：只有仓库既有 autoImplicit 提示；无候选 trust escape。
- 仅新增本 audit 目录内容，未修改候选或提交。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/kinetic-residue/audit/independent_check.py --root .
cd Lean
lake env lean --trust=0 -DwarningAsError=true ../Verification/physics/low-energy-phenomenology/kinetic-residue/audit/Consumer.lean
```
