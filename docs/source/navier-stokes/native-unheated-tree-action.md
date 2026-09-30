# 原树的联合频率预算与完整作用写入

> 稳定机制；实时责任只见[active route](../../handoffs/navier-stokes-native-regularity-active-route.md)。
> 上游原 history、三次／四次／五次源及净矩账户见[未热原源机制](native-unheated-source-action.md)。

## 同一发生与实际六次源

令 B 为原 `UnifiedCompleteSource.budget`，G 为原 `SourceGradient.mass`。
全部输入来自同一完整 U／σ；原 N 由完整实际动量消费已付 H¹ a.e. 面后生成，
其 H⁻¹/² 范数受 `C_half·G` 控制。正卷积包络也有相同 G 预算，故绝对求和不借用
有符号 N 的取消。原 κ、物理起点和单位时钟保持。

原 Φ₅ 是已付五速度树的 S₅ 逆。每个旧 slot∈Fin3、leaf∈Fin4 的五个速度位置
各发生一次实际 N 替换，得到 60 个核。Sextic.Input.kernel 由原 normalizer
和所替换叶的真实 quarter 谱生成；`original_sextic` 在全部时间精确读回原 forcing。
K₆ 保留原 D、T、S₄、S₅ 及全部压力坐标，其四次方满足

```text
|K₆|⁴ ≤ ν⁻⁷ D⁻² T⁻² S₄⁻² S₅⁻³。
```

S₄≤2S₅ 后仍按原树的耦合频率求和。没有把不同边的衰减当成独立变量。
实际 60 个核的预算分四组：

| 原树分组 | 位置数 | 联合求和资源 |
| --- | ---: | --- |
| Comb | 20 | Hardy 与 CriticalSum 三输入 |
| Balanced | 20 | QuarterSchur 及两个真实 profile |
| RootBalanced | 10 | WeightedSquare 与 ShiftSchur |
| OuterComb | 10 | 原 indexEquiv、ShiftCriticalSum 与平移 Schur |

Schur/SchurThree 从非负有限行、列预算生成完整 ℓ² 双／三输入和。
LatticePrefix/Tail/RowSquare 给临界格点前缀、尾及平方核的真实估计。
Uniform 由任意平移立方体的 density2 和、临界前缀／尾及原平移 Schur 核生成
与输出 k 无关的 `cap(ν)·∏‖inputᵢ‖`。Outer 重新消费实际 indexEquiv 与联合 profile，
AllSlots 将改进送入全部六十种核；实际输入只消耗 `C_half·G·B⁴`。
全部内部频率、原零波及九分量保留。

## 共同载体与原端点

原完整应力载体使用 weight 编码物理 Fourier 系数。WeakCarrier 在其上增加
`density1=radical⁻¹`，故共同空间的真实编码为 `weight·density1·field`；
`read` 再乘 radical，精确返回原物理字段。`read_injective` 保持整个载体身份。
旧完整空间的 `lowerCLM` 是收缩，`read_lowerCLM` 等于旧 read，没有另造物理量。

EndpointInput 在一个原速度位置使用已付 inverseQuarter 收缩，其余四处使用原 U。
quarter 与 inverseQuarter 逐波精确恢复，故全部原 Φ₅ 端点有 B⁵ 预算；不要求端点 H¹。
EndpointCarrier 的 value 保留原 Φ₅(0)、任意双端点、可测性、紧时间可积性和原 next。

Uniform.Fields/Carrier 使用这份新核界，将完整 Q₆ 和原 Φ₅ 直接生成在旧 H⁻²
完整应力空间。两者的 lower 精确等于旧共同载体；Uniform.Evolution 经此同一连续
单射消费已证 writer，得到旧完整空间中的双端点等式、AC、强 a.e. 导数和原 next。

## 独立 Q₆ 与完整写入

Rows 从真实 forcing 的五项和支付完整内部绝对求和；Whole 把 slot、leaf、
四个压力坐标、九个张量入口和两种位置完整组装，常数为 87480。
Carrier 以此实际 field 生成共同空间的 Q₆，范数受 `C·G` 控制，Bochner L¹
直接消费原 `∫G`，field/value 的整个 macro next 都在 writer 之前成立。
Q₆ 的定义不调用 Φ₅ 的导数或时间写入。

Quintic.PrimitiveWrite 将原逐行 FTC 与全端点绝对和、两源的积分范数和相接。
全部内部和与有限坐标求和完成后，原五速度树认回既有 Q₅。于是

```text
Φ₅(b) − Φ₅(a) = ∫_a^b (Q₆(t) − lowerCLM(Q₅(t))) dt。
```

此式是共同完整载体的等式，适用于任意非负 a、b。Evolution 生成 AC、强 a.e. 导数；
原 Φ₅(0) 加 Stage9 canonicalTimePrimitive 精确返回原 Φ₅(t)。整个率与生成态均沿
原 clockAdvance 保留 actual macro next。

WindowEvolution 在完整空间中先保留 κ 分部积分的两端点，再由原 g 的支撑及光滑性
消去端点。其 `original_stress` 直接消费原 NativeForwardWindowJets.jet.snd：

```text
σ_n = Q₆Window_n − Φ₅Window_(n+1) − Φ₄Window_(n+1)
      − Φ₃Window_(n+1) − pairTail_(n+1,1)。
```

原 R、时钟、窗口与所有输出波保持。Φ₅/Φ₄/Φ₃ 窗口继续使用已生成的无权物理 L²
读出。新 Q₆ 窗口保留原 next。

这些是 `nativeTemporalRoot stackedShortCurrent` 下的从属实际 source producers 与
完整计算；原 finite row／cofinal row、整个 history、正热 runtime 合同继续消费原 next。
零尺度普通空间全阶的 controller 安装按 active route 的原物理责任完成。

## 任意有限树的原时间生成

Tree.Time 对任意 Fin n 叶定义原速度乘积、删叶 cofactor 与逐叶实际 N 替换的 forcing。
原 U 的 AC 与真实 N−νλU writer 生成乘积律；Tree.Window 保留原 κ 的双端点 FTC。
空树乘积为 1、forcing 与 rate 为 0。非空树的输出平方频率由所有叶频率的有限
Cauchy 支付，Tree.Output 给实际 Sₙ 逆的输出 weight 界。

Tree.NormalForm 定义 actual `primitive=Sₙ⁻¹·kernel·product` 与
`nextForcing=Sₙ⁻¹·kernel·forcing`。全零率时原 U 与 N 的零波直接消去实际行；
其余分支原乘积率给 `primitive′=nextForcing−kernel·product`。双端点、原 κ、AC
及两项 whole next 均由此生成，nextForcing 的定义不消费其导数或写入。

Tree.Leaf 将指定原叶分裂为 inside 与 parent−inside，保留真实压力系数、原其余叶、
完整新频率和输出。源展开内部消费原 H¹ 面与原 N 卷积。Tree.Input 将指定叶替换为
已付 Nhalf、其余叶保持原 U，给任意有限叶数的正输入预算和实际 forcing 认回。

## 原六速度树与完整物理 Φ₆

Sextic.Six.Rows/Fubini/Whole 把每个原五叶 forcing 展开为实际六速度树；全部五重
内部频率、60 种叶位置、压力坐标、九分量与零频保留。正绝对和与完整时间 Fubini
只消耗一个 G；完整 field 在同源 a.e. 面精确返回原 Q₆。

PrimitiveKernel 消费同一节点的实际 S₆ 逆，得到逐行原 primitive 和独立七次 forcing。
原 Φ₆ 的完整内部绝对和受 `C·G·weight(k)` 控制。PrimitiveSpace 因而生成无权物理
ℓ²，完整源范数在原 H¹ a.e. 面上实现并具有紧时间 L¹ 预算；没有另造正则场。
PrimitiveWindow 在原 Icc(0,observation+2) 上积分 κ，物理 L² Fourier 读出逐行等于
该原 Φ₆，全部有效观察时刻及原 macro next 保持。

Septic.Input/Kernel 将原六叶 forcing 精确展开为 360 个实际 N 替换。核保留四个压力
系数与原 D、T、S₄、S₅、S₆，并给四次方界
`ν⁻⁹ D⁻² T⁻² S₄⁻² S₅⁻² S₆⁻³`。这份正核及原 Φ₆ 行 FTC 是下一实际窗口计算
的输入；未积分 Q₇ 的全频 L¹ 不由该静态核界自动产生。

## 原七次累计窗口与物理消费

Septic.Window.Rows 预先定义每个原 septicTerm 的 κ 积分。六个原 N 替换先保留在同一
实际行中，原 normal-form 行 FTC 与 κ 分部积分消去两个真实端点，随后对全部五重
内频证明 `Σ‖∫κ·septicTerm‖` 有限，预算只消费 G 一次。它不将范数移入该七次积分。

Read/Assembly/Whole 将全部六十棵旧树、每行六个作用位置、全部压力坐标与九字段
组装，独立 field 与其预算在读取旧窗口之前生成。原和／积分 Fubini 精确给
`Q₇Window_n=Q₆Window_n+Φ₆Window_(n+1)`；此式直接进入原 σ 的七次展开。
Physical 使用原 σ 的无权物理态与此前 Φ／tail 的物理预算实现同一已生成 field，
`value_row/physical_fourier` 逐波认回全部系数，整个物理 current 随原 macro next 保持。

Septic.SevenRows 再以原 Tree.Leaf 展开该 same septicTerm，得到七原 U 和六内频。
固定旧 index 的新 inside 绝对和直接消费原半阶正包络；PrimitiveKernel 将实际 S₇
逆应用于此同一行，独立 octicTerm 保留全部七个下一 N 替换，原双端点／κ／next 均成立。

Septic.Transport 同时生成 literal `Σ_p U_a(p)·rawΦ₆_ij(k−p)`；全 3×9 通量在
H⁻²、未投影散度在 H⁻⁴，实际物理积分读回及 whole next 精确保持。a.e. 物理身份
内部消费原 H¹；原全点 Fourier field 保留。这份共同输运不等于全部 Q₇。

Tree.Riesz 的三模块对任意实 ℓ² 输入生成完整正三线性和
`Σ_(p,q) density1(p)density1(q)density1(p+q)|L_p M_q T_(p+q)|`
`≤3√C_Riesz‖L‖‖M‖‖T‖`。原输出、左右循环重索引和零波全部保留，未增加正则性
premise。其消费方向是实际层级黏性率的完整输出范数。

## 原压力热核与完整七叶物理空间

Tree.Heat.Kernel 在 `a,b≤1/2`、`a+b≥−1` 下把真实频率质量核
`μ(p+q)^((a+b+1/2)/2) μ(p)^(-a/2) μ(q)^(-b/2)/(μ(p)+μ(q))`
控制在 `2·density1(p)density1(q)density1(p+q)`，μ=1+|k|²只作范数权重。
Convolution/Space 使用原 Riesz 完整和及有限输出原 row 测试器，生成全部输出的
正／复数 ℓ²，逐波等于原完整卷积，范数不收目标预算。
Local 对原 νλ 给 pair 逆的 μ 和界；真实压力与指定 Tree.Leaf 的新 sumRate 内部
满足该核估计，全零率由原压力零分支消去，原物理耗散率不变。

Tree.Interpolation/Velocity 从原速度生成 `μ^(1/7)·|U|` 的正 ℓ² 输入；原零波消元后
H¹ 质量受 2G 控制，Holder 给 `‖input‖⁷≤2B⁵G`。完整源 AE 身份、可测性、积分
与原 macro next 直接消费同一原 history。

Topology/Evaluation 赋每个有 j 叶的 proper tree 指数 `1/2−3j/14`，每个真实二叉
节点消费同一热核，原 stress 顶层保留 pair 逆并去掉该处压力因子。完整七叶 joint
频率和生成无权输出 ℓ²，预算为 `C(ν)‖input‖⁷`。
Growth/LeafOrder 给整个 index×新频率与新树 index 的双射，并精确认回原 Fin.cons
顺序：新两叶在前，其余由原 selected.succAbove 保留。Coefficient 随每次原压力与
原新总率增长。Quartic 起点实际消费 D→T→S₄；内部 Alignment 由此生成并连续 grow，
Septic.Alignment 精确认回原 S₇ primitive，最终 Space 消费其生成值。

Septic.Physical 从全部 360 叶位置与 3¹⁰ 压力 Key 组装同一 primitive，保留原双位置、
全九 tensor 字段及零频。未加权 ℓ² 范数受 `127545840·C(ν,seed)·G` 控制。
source 的 AE 身份内部消费原 H¹，literal Fourier 场全点保留；完整 Bochner 可积性、
原 κ windowState、普通物理 L²、每个 Fourier 系数与 whole next 均从该同一源生成。

## 原八次累计作用与真正新逆率

Octic.Window.Rows 保留每个旧 SixRows.Index 内新增 newest／u／v／inside 的原分组。
每个 literal octicTerm 经原 κ 积分后，先由原行 FTC 给七速度积分加 Φ₇ 修正。
固定旧 index 的七速度 inside 绝对和由原 N 正包络支付；只有完整 Φ₇ 的绝对和可
在剩余频率间重排。旧分组的 norm-after-integral 因而受原 Q₇ 预算加 54 倍 Φ₇
积分预算控制，G 只消费一次。Whole 真正调用原 Physical.primitive_assemble，给
`Q₈Window_n=Q₇Window_n+Φ₇Window_(n+1)` 并进入完整原 σ。Physical 把预先独立
定义的 field 实现在无权 tensor L² 中，全部物理 Fourier 与 whole next 保持。

Octic.EightRows 从同一七叶 octicTerm 再展开为八个原 U；真实 S₈ 逆进入
PrimitiveKernel，独立九次 forcing 与原双端点／κ／next 同时生成。
Tree.RateChange 逐叶精确计算旧新原率差。RateTransfer 定义 `θ=crossRate/S_new`，
由原频率 Cauchy 给 |θ|≤1，并将真实新 primitive 与窗口等于 `(1+θ)` 倍同一行
多一层旧逆率；全零分支保留真实压力消元。Octic.PrimitiveKernel 直接消费此式。
inside 权会改变原 signed 分组的抵消；transfer 的界不自动结算该完整物理范数。

## 原双叶完整响应与真实时间作用

Octic.Temporal.Response 用原 inverse-gradient state 构造连续双线性响应；新内部率
始终为原其余叶的 A 加 νλ(p)+νλ(k−p)，平方根谱因子由该同一率消去。
完整 inside 和精确返回原 primitive_fiber；原 global H⁻¹ writer 生成真实双侧
responseRate、AC、任意非负双端点 FTC 与 macro next。
原 G 加权时间差受 `∫G(t)∫_[t,t+h]‖原rate(s)‖ds dt` 控制并随 h→0 趋零，
没有由此推断幂速率或更高 G 矩。

Octic.PairForcing 直接调用原 Heat(-1/2,0) 输出预算。两个实际 Nhalf/U 槽生成
完整物理 forcing；原 bare quadratic 在源 H¹ a.e. 面认回。设 P_A 是完整双叶响应：

```text
P_A′ − A P_A = pair_A(N,U) + pair_A(U,N) − U⊗U
P_A(a) = exp(−A(b−a)) P_A(b)
         − ∫_a^b exp(−A(s−a)) [P_A′(s)−A P_A(s)] ds。
```

全九分量 P_A 的无权 ℓ² 范数受 CνB² 控制；独立 forcing 的完整范数受
`Cν,seed G` 控制，Bochner 可积性直接消费原 G 一次账户。Temporal.Backward
先保留原指数权生成逐行公式；PairForcing.Source 以独立 forcing 的整场读出消元，
得到完整 L² 的 backward Duhamel、FTC／AC 和原 next。A 来自原其余叶率，
这里没有新增物理平滑尺度。

## 同一原率的完整 Gram 与实际 mixed work

Octic.Theta.Gram 把 `crossRate/(A+νλ(p)+νλ(q))` 写成原梯度指数腿的完整辅助
时间积分，保留全 F×F 交叉及复压力系数。Trace 给完整源腿的可积性与原能量界；
A=0 时迹精确返回原全速度能量。辅助时间被积分消去。

GramDual.Pulse/Work 将任意有限物理 L² 测试的原 Φ₈−bare 精确认回公共原 U 腿
与实际 dual vector 的 Hilbert 配对。其 work 保留 old-old 的全部交叉、同 inside
约束及原混合核 `K(A_i+A_j,q_i,q_j)`。vectorRate 独立读取原七速度 forcing−黏性，
全载体 Bochner 积分生成双端点 vector write、signed work write 和同一 next。
Cauchy 给原配对范数平方 `≤B²·work`；有限测试的功恒等式没有被改名为 uniform work 界。

GramDual.Generator/Dissipation 进一步在这枚完整 dual vector 上精确识别七槽
`sumRate=rest+rate(other)`。所有 old-old 交叉项的黏性功合成
`2⟨vector,dampingVector⟩_ℝ=‖boundaryVector‖²≥0`，其中 boundary 是同一脉冲在
辅助时间零点的有限和，不丢弃交叉。原物理时钟上因此有
`work(b)−work(a)=∫ₐᵇ(2⟨vector,forcingVector⟩−‖boundaryVector‖²)`；原
Φ₈−bare 配对消费者直接使用此式，forcing／boundary 各保持 macro next。
此恒等式不预装截断一致的 `∫‖forcingVector‖` 预算；数值闭合需由原七槽实际
N/U 作用生成该界，并在原 Stage9 全字载体上兑现相应依赖面。
GramDual.ForcingGate 已证明 forcingVector 的实际 Bochner 可积性，把上式拆成
`work(b)+∫‖boundaryVector‖²=work(a)+∫2⟨vector,forcingVector⟩`，并直接得
`work(b)≤work(a)+∫2⟨vector,forcingVector⟩`；原配对消费者取得相同上界。
这枚有号门没有把 forcing 功的积分假设为有界常数。
GramDual.L1Response 进一步用原曲线在 `[a,b]` 的实际最大范数和这枚耗散门证明
`‖vector(b)‖≤‖vector(a)‖+2∫ₐᵇ‖forcingVector(t)‖dt`；原 Φ₈−bare
配对平方直接受其右端平方控制。此步只需一次 forcing 积分，不要求源梯度质量
`G(t)` 的平方可积；截断一致的 `∫‖forcingVector‖` 与原初态范数仍须由源生成。
GramDual.KernelBound 消费原七叶 `Alignment.coefficient_bound`，并用每次实际
分叉的 `symbol≤2·factor(ν)` 生成统一旧树系数界；原槽位黏性率又支付
`‖sumRate⁻¹·pressure‖≤cap(ν)·2π`。因此每个完整 Gram `basis(entry)`
受仅依赖 ν 的常数乘 `|test(entry.output)|` 控制，独立于地址、inside 和全部
频率。全观察集的 forcing 范数仍需保留七槽输入的共同卷积结构，不能把
逐地址界直接相加。
GramDual.InitialShift 直接读取 `stackedSeedState` 的原有限 Fourier 表和
`NativeUnifiedCompleteSource.source stackedShortCurrent 0` 的同一速度行。
原七槽乘积在任一槽频率落表外时为零；完整 Gram 初态向量因此精确等于
只保留 `output−inside` 属于原七频和有限集的观察和。
GramDual.InitialNorm 用原七叶 alignment 的树波单射证明：inside 与七个槽频率
恢复整个 `(output, old index, inside)` 地址。固定七槽频率码的纤维是互不相交
inside 的 lp 单点和，Pythagoras 与 test 的 ℓ² 和支付每条纤维；码只取有限表
`piFinset(butterflyFirstStackModes)`。于是对全部有限观察集
`‖vector(0)‖≤initialCap·‖test‖`，常数只含原初频数、source budget 与 ν，
原 L¹ 响应与 Φ₈−bare 配对直接消费。
GramDual.CodeFiber 将同一纤维正交推广到任意时刻、任意由码权支付的系数：
`‖Σ c(entry)·basis(entry)‖≤basisCap·‖test‖·Σ_{码}weight`。原乘积与原 forcing
分别受逐槽 Fourier 权之积支付，`sum_pow'` 把码和压成触及频率上的 Wiener 和；
于是 `‖vector(t)‖`、`‖forcingVector(t)‖` 均由同一 source 的七次 Wiener 和控制，
观察一致的 forcing 积分精确交给 `∫(Σ'sourceWeight)^7`，其中 sourceWeight 为原 U
与原 N 的逐频坐标和。这是原 U／N 的零尺度空间预算（正热 Wiener 界在 h→0 的一致性），
不含观察集。

## 独立验收

各批默认心跳、`--trust=0 -DwarningAsError=true` 独立 fresh 编译；候选到生产的
逐声明 type/value、原始 moduleData 多重集、完整依赖边与数学闭包逐项一致。
仅 Classical.choice、Quot.sound、propext，opaque 全可读，无 unsafe／missing；数学证明闭包无 partial。
source14 中 pairMass.eq_1 的三个惰性生成发生均保留，没有按声明名去重。

| 已认证生产批次 | 手写／原始条目 | 完整／数学闭包 |
| --- | ---: | ---: |
| [格点 Hardy 六模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Sextic/Hardy.lean) | 69／130 | 19,774／19,726 |
| [临界三输入两模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Sextic/CriticalSum.lean) | 27／42 | 19,766／19,754 |
| [平移与四分之一 Schur 四模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Sextic/ShiftCriticalSum.lean) | 48／87 | 19,848／19,821 |
| [加权平方一模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Sextic/WeightedSquare.lean) | 7／8 | 14,615／14,615 |
| [完整 60 槽十四模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Sextic/AllSlots.lean) | 162／293 | 58,812／58,777 |
| [原 Φ₅ 端点三模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Quintic/EndpointCarrier.lean) | 39／53 | 58,821／58,818 |
| [完整 Q₆／原 Φ₅ 写入七模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Quintic/WindowEvolution.lean) | 62／80 | 61,909／61,904 |
| [输出无损核五模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Sextic/Uniform/Sum.lean) | 33／38 | 19,831／19,831 |
| [原六十槽统一界两模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Sextic/Uniform/AllSlots.lean) | 10／10 | 58,538／58,538 |
| [原 H⁻² 完整写入三模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Sextic/Uniform/Evolution.lean) | 33／40 | 59,307／59,304 |
| [任意叶数原时间律两模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Tree/Window.lean) | 21／27 | 60,333／60,328 |
| [原输出与逆率两模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Tree/NormalForm.lean) | 25／35 | 60,362／60,359 |
| [六速度与物理 Φ₆ 七模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Sextic/PrimitiveWindow.lean) | 101／125 | 61,243／61,230 |
| [原七次输入与核三模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Septic/Kernel.lean) | 29／41 | 58,385／58,383 |
| [全频 Riesz 三模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Tree/Riesz/Control.lean) | 37／51 | 29,856／29,848 |
| [原 U×Φ₆ 输运三模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Septic/Transport/Divergence.lean) | 54／81 | 59,025／59,008 |
| [原七次累计物理窗口五模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Septic/Window/Physical.lean) | 57／92 | 62,742／62,465 |
| [七原速度与实际 S₇ 两模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Septic/PrimitiveKernel.lean) | 29／29 | 60,624／60,624 |
| [原压力热卷积四模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Tree/Heat/Local.lean) | 56／81 | 31,504／31,486 |
| [原 2/7 速度输入两模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Tree/Velocity.lean) | 29／39 | 57,997／57,994 |
| [同源七叶全频空间十一模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Septic/Space.lean) | 124／295 | 58,349／58,248 |
| [完整 Φ₇ 物理消费者三模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Septic/Physical/Window.lean) | 54／70 | 60,850／60,845 |
| [原八次累计两模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Octic/Window/Whole.lean) | 41／61 | 62,830／62,563 |
| [原 Q₈ 物理消费者一模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Octic/Window/Physical.lean) | 8／9 | 62,877／62,877 |
| [原八速度及逆率作用四模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Octic/PrimitiveKernel.lean) | 35／41 | 60,464／60,462 |
| [原全历史响应两模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Octic/Temporal/Evolution.lean) | 38／70 | 58,338／58,324 |
| [同率完整 Gram 两模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Octic/Theta/Trace.lean) | 38／55 | 57,692／57,679 |
| [原 backward writer 一模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Octic/Temporal/Backward.lean) | 14／16 | 58,272／58,270 |
| [完整双叶物理 forcing 三模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Octic/PairForcing/Source.lean) | 79／121 | 58,689／58,672 |
| [实际 mixed-rate work 两模块](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Octic/GramDual/Work.lean) | 40／75 | 59,156／58,871 |

Φ₆ 的手写根计数含局部 Haar 实例；生产晋升保留该实例及其证明的模块名对应。
Septic.Kernel 惰性生成的 SixRows.base.eq_1／kernel.eq_1 按真实 moduleData 发生保留。
原七次窗口的15个宏／parser值另按封闭 Lean.Name 组件核对模块名变化，全部 raw 发生保留。
原七叶结构递归的15个编译器 `_unsafe_rec` 辅助发生按完整 raw 清单保留并核同，数学根闭包不可达；未写源级 partial。
原 GramDual 的六个模块敏感 parser／宏发生也完整核对封闭 Lean.Name，未跳过 raw 值。
