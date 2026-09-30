# 同源迹算子、伴随时间作用与对偶预算

当前责任只由[原生全阶控制 active card](../../handoffs/navier-stokes-native-regularity-active-route.md)维护。
原 Z、迹能量及完整 σ 梯度见[同源黏性 normal form](native-window-viscous-normal-form.md)。
整端族、普通终值、原 cofinal 精确演化与两时钟预算见[原端点能量](native-window-terminal-energy.md)。

## 同一原发生上的实际迹算子

固定原 seed、g、σ_F、B=P对流−P压力、Z=σ−B 与 τ=tr Z。Trace.Operator 从
原完整矩阵的对角和生成 −τ；canonical 物理 pairing／duality 将它实现为

```text
T = I＋νΛ−τI；J = id−T。
```

真实物理读出为两侧 P_F 测试与原 τ 的配对，J 的每个双线性读出精确等于
τ 的乘积功减去原 νΛ 功。正部来自同一 trS Gram；原 trB 的小量通过 H¹
物理乘积界由 νΛ 吸收。源生阈值使所有原 physicalSpace M 测试满足

```text
〈v,v〉＋(ν/2)curlPair(v,v) ≤ 〈v,Tv〉。
```

F 不必包含于 M。泛型接口保留单独谱集合 L，只有 L=M 时才是完整 I＋νΛ。
T 与旧全矩阵 𝔅=I＋νΛ−Z 是同源的不同实际作用，二者没有被宣称相等。
每个固定时间阶的真实系数功由 T 自身能量相对控制，常数统一于 M、外 cube
和紧时间；一阶直接是实际 `|d_t〈v,T(t)v〉|≤C〈v,T(t)v〉`，此处 v 固定。

## 原 Stage9 非自治时间消费者

原 H⁻¹ state 经 finite faithful Riesz 得 U_M(sample)=P_M 原 U(sample)。
其真实演化保持

```text
U_M′ = A_M(sample)U_M＋f_M；
f_M = 原 N(U)−N(P_MU) 的有限原读出。
```

A_M 是同 ν、同原 advector 的完整物理 Oseen 作用。真正的 adjoint 用同 ν
和负 advector；原物理配对直接证明 A/A† 相容。Stage9 的全紧区间线性
系数积分器实际生成 backward 曲线，满足给定终值和 `p′=−A†p`。
原黏性 Green 给倒向物理 L² 收缩，常数为 1，独立 M。

固定 observation，终值取原 J(observation)U_M(b)。propagated 是该真实
backward，response η=J(observation)U_M−propagated；η(b)=0。源方程直接给

```text
η′＋A†η = q；q=JAU_M＋A†JU_M＋Jf_M。
d〈U_M,propagated〉/ds = 〈f_M,propagated〉；
d〈U_M,η〉/ds = 〈f_M,η〉＋〈U_M,q〉。
```

原强 AC、完整净率可积性与全部紧区间端点 FTC 直接消费这些式子。
`propagated_work_bound` 的普通终值范数仍是字面的 `‖JU_M(b)‖`；截断一致
的终值控制由下面的原对偶质量提供，不从 L² 收缩单独推出。

## 原 g 直接支付联合测试的对偶能量

T 的强制性生成其真实有限逆。J=id−T 的同一对偶能量满足

```text
0 ≤ 〈T⁻¹Jv,Jv〉 ≤ 〈v,Tv〉−〈v,v〉。
```

inverse 由实际 T 的 injectivity/finite equivalence 产生，原场或预算没有
作为附加输入。Dual.Window 又将完整原 g 的 T 能量精确认回

```text
∫g〈U_M(s),T(observation)U_M(s)〉
  = 原 spectralWindow_M ＋〈trS＋trB,trS〉。
```

原 G 统一支付谱窗口，完整 σ 的已付 L² 界和 trB 小量支付第二项。因此
同一原源生成有限 budget(seed,H)，使原 g 的 `〈T⁻¹JU_M,JU_M〉` 窗口统一
于内 M 和外 cube，只需 M 最终覆盖 F 的非零频率。它保持固定 observation
的原 T、原 sample 历史与原 g，未要求演化 raw U 的新 H² 或普通终值 L² 界。

原字段、T/J、原样本系数和完整 dualWindow 均保持实际宏 next。
Coupled.Next 用同一黏性作用的紧区间唯一性，进一步认回实际 backward、
propagated 和 response 的 selector 平移；其完整能量与终值一同保持原 next。

## 两个真实时钟的控制

原系数实际导数的 Gronwall 消费在两个方向生成

```text
T(t) ≤ exp(C|t−s|)T(s)；
T(t)⁻¹ ≤ exp(C|t−s|)T(s)⁻¹。
```

C 和低阈值来自原源与紧时间，独立 M/外 cube。逆比较由原正二次型与实际
有限逆推导；canonical 右逆只须认回对应原 T 的右逆等式即可直接消元。
这把固定 T(observation) 的窗口预算交给需要 T(sample) 的质量读出，同时
保留真实时间差。完整输运 Lyapunov 与 forcing-response 净功不由该比较删除。

## 移动逆质量与完整合成输入

Inverse.Mass 从原 coercivity 生成实际 T(sample) 及其逆。z=T(sample)⁻¹w
的强时间 writer 同时保留原系数率、两腿 Lyapunov 与响应输入：

```text
E′ = −T′(sample)[z,z] − Lyapunov(A(sample),T(sample);z)
       ＋2〈z,responseRate〉。
```

E 非负并支付 z 的真实质量与 ν/2 梯度；原相对时间界支付 |T′[z,z]|。
完整净率具有 L¹ 与 FTC，未将其拆开的每项改称统一预算。

Coupled 使用固定 T(observation)，从原 U_M 与同一 propagated 生成

```text
r = U_M−propagated；q=T(observation)⁻¹r；
r′ = −A†(sample)r＋lift(input)；
input = 2 rawRate−N(raw U)−N(P_M raw U)；
lift(input) = −2νΛU_M＋f_M。
```

原 H⁻¹ 配对直接给 `‖input‖≤capν(1+G)`。因此真实合成能量满足

```text
E′ = −Lyapunov(A(sample),T(observation);q)＋2〈q,lift(input)〉；
|E′＋Lyapunov| ≤ 2 capν(1+G) sqrt(2E/ν)。
```

一次 G 的 L¹ 成本被实际 H¹／H⁻¹ 作用消费，没有从 forcing 拆分产生 G²。
其终值恰是原 `〈U_M(b),T(observation)U_M(b)〉`，由前述原 g 谱／应力窗口
支付。完整有符号 Lyapunov 仍在其真实双时钟与倒向积分方向内消费。

## 同一 cutoff 表示及严格时间收缩

Pcut 的实际全分量作用进入 Zcut=Z＋Pcut；normal form 和两个低功见
[完整应力作用](native-window-viscous-normal-form.md#cutoff-实际作用的完整消费)。
其 canonical Tcut=T−tr(Pcut) 乘法保留原两侧 P_F 测试，实际 Jcut=id−Tcut。
源生阈值直接给 Tcut 自身的质量／梯度强制性，以及任意小的相对形式差。
直接消费者生成

```text
½T ≤ Tcut ≤ ³⁄₂T；⅔T⁻¹ ≤ Tcut⁻¹ ≤ 2T⁻¹；
∫g〈Tcut⁻¹Jcut U_M,Jcut U_M〉 ≤ ³⁄₂ 原 Dual.Window.budget。
```

真实逆由 Tcut 本身生成；上述预算保留原 g、完整 source 与宏 next。

原有限物理空间排除了零频，故 ν(2π)² 是真实黏性谱 gap。原 backward
满足 `‖p(a)‖≤exp(−ν(2π)²(b−a))‖p(b)‖`。原 g 的采样 b∈[t+1,t+2]
因此给严格因子 `cν=exp(−ν(2π)²)<1`；这没有宣称任意两个样本都相距至少 1。

Endpoint.Action 实际调用同一 Stage9 积分器生成前向 x′=A(sample)x。原
J＋νΛ 的 physical paired read 恰为 τ 乘法，完整配对导数给

```text
d〈x,U_M〉/ds = 2〈x,J U_M〉−2〈x,(J＋νΛ)U_M〉＋〈x,f_M〉。
```

普通黏性项由这一实际两腿写入送入原时间积分；原有限读出的 f_M 保持原值。

## 原核加载的零终端伴随与源数值付款

`Trace.Distributed.Response` 用同一 Stage9 responder、原 A† 与原核 κ 生成
`p′=−A†p−κ(observation−t)Λtest`，终值 p(b)=0。取 b=observation+2、a=0，
`Green.window_original/window_source_green` 精确给原 W 的有限读出：

```text
〈W_M(observation),Λtest〉 = 〈U_M(0),p(0)〉 + ∫₀ᵇ〈f_M,p〉。
```

`Lyapunov.mass_split` 将原 T 认回 `I+νΛ+P_trace`；P_trace 是原九分量矩阵的
迹势。原场的相对算子界把势的黏性费用吸入 `−ν²‖Λz‖²+C E(p)`，其中
z=T⁻¹p。质量斜对称性消去对流的零阶项，保留同一原 K_U 的实际功
`convectionWork=2ν〈Λz,K_Uz〉+2〈P_trace z,K_Uz〉`。

`Initial.source_initial_pair_paid` 消费原 Stage9 零时矩，给任意 ε>0 的
`|〈U_M(0),w〉|≤ε E(w)+Dε`。阈值与常数先于全部 M、外 cube 和 w。
`Weighted` 再调用原移动逆质量 AC 与指数积分，将实际时钟费用一起支付：

```text
E(p(0)) + (ν²/2)∫₀ᵇ exp(Ct)‖Λz‖²
  ≤ ∫₀ᵇ exp(Ct) convectionWork + B‖test‖²；
B = H exp(CH) (2/ν²) kernelBound(0)²。
```

low、C、B 由源及 H 生成，先于 M、observation 和 test，b≤H。
`source_weighted_window` 将这份付款直接交给原 W，左侧仍保留
`ε(ν²/2)∫exp(Ct)‖Λz‖²`，右侧为 Dε、显式核预算以及原号的
`∫〈f_M,p〉+ε∫exp(Ct)convectionWork`。这里没有新增源正则性或 Y² 积分前提。
这五模块是同源数值 producer 及原 W 数学消费者；后续余功责任由 active card 维护。

`Distributed.Mean` 从原 `StageNineWholeRelative.source_drift_relative` 消元任意输入，
将 whole-history 的均值作用实际用于 z=T(time)⁻¹p。对彼此独立的 frame、time，
源先生成阈值与 C，使 `|meanWork|≤δ‖Λz‖²+C E(p)`，任意 δ>0。
`meanValue_window` 将该均值精确认回同一原 W 的有限读出；余作用恰为
`transport(U_M(time)−W_M(frame))z`，未把两个时钟压成逐 lag 点态界。

`Distributed.SourceTest` 直接生成 φ_M=ΛW_M，故原窗口测试值是 `‖φ_M‖²`。
先取已付图门的 C、B，再令 ε=1/(4(B+1))，原核费用被吸入该同源平方：

```text
½‖ΛW_M‖² + (εν²/4)∫₀ᵇ exp(Ct)‖Λz‖²
  ≤ D + ∫₀ᵇ〈f_M,p〉 + ε∫₀ᵇ exp(Ct) centeredWork(observation,t,z)。
```

C、ε、D、low 先于 M 和 observation；p 仍由原 responder 生成，其测试也由原 W
生成。该消费者不引入 W 的高阶预算，也不要求整个外部测试族的响应图范数先受控。

## 原响应的混合张量与实际扩散消项

`Distributed.Tensor` 用原有限 U_M(t) 与同一 z=T(t)⁻¹p 生成
`B(u,z)(k,i,j)=quarter(k)·mixedFlux(u,z)(k,i,j)`。
这是 H¹ᐟ² 编码，零频和九分量均保留；不能交旧 H⁻² decoder。
原双线性缩放与源梯度账生成 `‖B(U_M,z)‖²≤C Y(t)E(p)`。
`CenteredTensor` 对固定 frame 的 v=U_M(t)−W_M(frame) 生成
`‖B(v,z)‖²≤C(1+Y(t))E(p)`，实际使用原均值 H¹ 预算。
这些 C 先于有限 M、frame、观察时刻和外部 test；没有引入 Y² 积分。

`TensorTime` 对原强 writer 和原 Stage9 响应求导，移动 T 始终保留。
`Clock` 从原二次型时间控制消元得到 `E(T′z)≤C²E(p)`；
`TensorClock` 与 `CenteredClock` 由此支付真实负 `T⁻¹T′z` 张量功，
对应系数分别为 Y 和 1+Y。

`TensorSpatial` 直接在上述 quarter 编码中证明

```text
heatWork(u,z)
 = 2〈B(u,z), B(−νΛu,z)+B(u,νΛz)〉
 = 2ν [Σⱼ‖B(u,Dⱼz)‖² − Σⱼ‖B(Dⱼu,z)‖²]。
```

`ConvectionTensor` 将同一 Leray／空间交换子交给这一负平方：
对任意 η>0，生成先于 M、u、z 的 A≥0，

```text
|2ν〈Λz,K_u z〉| + (A/2ν) heatWork(u,z)
 ≤ η‖Λz‖² + A Σⱼ‖B(u,Dⱼz)‖²。
```

`CenteredPayment` 直接取 u=v，保留原迹势功
`potentialWork=2〈P_trace(t)z,K_v z〉`。它积分并消费原 `SourceTest`，得到

```text
½‖ΛW_M‖² + (εν²/8)∫eᶜᵗ Graph + ε(A/2ν)∫eᶜᵗ heatWork(v,z)
 ≤ D + ∫〈f_M,p〉 + εA∫eᶜᵗ Jplus(v,z) + ε∫eᶜᵗ potentialWork。
```

`Rate`／`CenteredRate` 将这份 heat 真正接入同一响应的平方 writer：
`(‖Q_c‖²)′=heatWork+2〈Q_c,remainingRate〉+clockWork`。
remainingRate 保留两项 K_U、完整 `f_M+A_U W_M(frame)`、原 κ 载荷，
以及 `T⁻¹(ν[Λ,P]+ν[K_U,Λ]+[K_U,P])z`。
frame 在样本时间中固定，T 依然随样本时间变化。
正响应梯度平方 Jplus 没有被这个负平方消项付清。

`Compensated` 从原完整 state 的 AC、moving inverse 与原 p 的 AC 生成 Q_c² 的 AC。
原 p(b)=0 消去终端后，FTC 给

```text
∫₀ᵇ eᶜᵗ heatWork = −‖Q_c(0)‖²
 − ∫₀ᵇ eᶜᵗ[2〈Q_c,remainingRate〉+clockWork+C‖Q_c‖²]。
```

`source_test_actual_budget` 将此精确代回原 W 二阶口；初端平方移到右侧为正。
同模块从原张量和时钟界生成 `clockWork+C‖Q_c‖²≤K(1+Y)E`。
实际平方率与积分均已支付，不据此宣称补偿表达式正定。

## 覆盖观察频带后的原迹势半阶控制

`Distributed.CoveredBand` 直接消费原两个 high current 的定义。
当 F⊆cube(radius) 时，投影后的高频速度为零，两个实际 current 因而为零；
原 `correctionJet` 的全部时间阶均严格为零。原 Trace.field 字面回到同一
`physical(traceStress)`。对 cube(outerRadius) 可由源内选取
`radius=max low outerRadius`，保持原源、原 W、原完整 forcing 和原响应方程。
这不是对任意未覆盖 radius 的零式。

`PotentialHalf` 从既有 `halfTrace` 读出原应力的真实 Fourier 半阶编码，
消费 `HalfProduct.scalar_product_of_spectrum` 生成原迹势的 H¹ 乘法平方预算。
同一 T 的 coercivity 随后给
`‖P_trace(t)T(t)⁻¹p‖²≤C E(p)`；low、C 先于 M、时刻和两个截断。
该口保持 `outerRadius≤radius`，由上述源内覆盖选择直接满足。

`PotentialWork` 直接作用于 v=U_M(t)−W_M(frame)。原 finite moment Cauchy 给
`moment₃(z)²≤moment₂(z)moment₄(z)`，非零 velocity 频率给 `moment₄≤C Graph`。
连同原输运估计、源 v 的 H¹ 矩和上述迹势乘法，四次 Young 生成
`|potentialWork|≤η Graph+Cη(1+Y)E`，任意 η>0。点态高次 Y 被这一不等式消元，
最终时间费用只用已经生成的 Y∈L¹。

`PotentialBudget` 使用原 energy AC 的连续性保证乘积积分合法，并在同一
`Compensated.source_test_actual_budget` 中实际代换这项势功。
最终 `source_test_potential_paid` 由源选择 `radius=max low outerRadius`，
无需调用者提供覆盖证书；原正 graph 系数留为 εν²/16。
右侧完整 F·p、Jplus、Q_c 初端和 remainingRate 保持原号。

## 原双钟载体与核载荷降阶

`Distributed.TwoTimePair` 从原 `coefficients(modes M)` 的 range 构造实 Hilbert
张量积。`row_pair` 保留两个独立有限频率及全部九分量；范数精确认回原物理 L²
配对。其 `diagonal ∘ rightInverse(time)` 直接读回原 quarter 编码的 Q_c，
包括零输出频率，没有换用旧负阶 decoder。

对 R(s,t)=v(s)⊗p(t)，原两条实际 writer 沿 `(s+ξ,t−ξ)` 给

```text
∂ξ ‖R‖² = −2ν[curl(v(s))‖p(t)‖² + ‖v(s)‖²curl(p(t))]
           + 2〈R, Fc(s)⊗p(t)+v(s)⊗load(t)〉。
```

两枚 K_U 各自在自己轴上斜对称，无 s=t 假设。
`PairTrace` 从原 mass、势乘法与 coercivity 生成 `‖ΛT⁻¹w‖²≤C‖w‖²`，
并把实际 `Jplus(v,T⁻¹w)` 界于 `C curl(v)‖w‖²`。
这是原 rank-one pair 的第一轴 Dirichlet 费用接口；
双时间体积分并不由此自动成为对角时间的 Dirichlet 界。

令 k(t)=κ(observation−t)。`KernelLift` 定义同一响应的源内表示
`q=p−(k/ν)φ`，原 p 可精确恢复。其真实率为

```text
q′ = νΛq + K_U q + (k/ν)K_Uφ − (k′/ν)φ，
k′(t) = −kernelJet 1 (observation−t)。
```

原 κΛφ 已消去，q(0)=p(0)、q(observation+2)=0 由原核端点生成。
`source_test_green` 与 `centered_forcing_restore` 保持原 φ=ΛW、完整 F 和 Fc 的号。
`KernelBudget` 使用上述 PairTrace、原中心 H¹ 矩和 Y∈L¹ 支付显式补项：
`∫eᶜᵗJplus(p)≤2∫eᶜᵗJplus(q)+Kκ‖φ‖²`，Kκ 先于 M、观察时刻和 test。

`IntegralComparison` 对任意原响应积分真实 centered heat 比较。
`KernelAbsorption` 先固定原图门 C／核预算 B、比较常数 A、上述 Kκ，
再生成 `ε=1/[4(B+A Kκ+1)]`，最后按这个 ε 重新支付原初态。
因此新增核补项被**实际吸收**，原 W 左侧保留
`¼‖ΛW_M‖²+(εν²/16)∫eᶜᵗGraph`，Jplus 只剩 q 且系数为 2εA。
完整 F·p、原 Q_c 初端和原剩余作用率仍以原 p 保留；这项吸收没有暗换它们的作用。

## 独立验收

| 模块组 | 行数 | canonical 根 | raw 发生 | 完整声明闭包 |
| --- | ---: | ---: | ---: | ---: |
| 同源迹算子及真实作用 | 325 | 36 | 84 | 61,686 |
| 原cutoff小流与完整primitive | 750 | 74 | 125 | 60,946 |
| Stage9非自治adjoint与真实FTC | 537 | 50 | 107 | 61,356 |
| 原g联合测试对偶终值预算 | 351 | 24 | 37 | 61,815 |
| 两个真实时钟与逆质量比较 | 167 | 6 | 6 | 61,566 |
| 移动逆质量与完整FTC | 501 | 34 | 60 | 62,213 |
| 原cutoff的完整normal form | 711 | 82 | 155 | 66,685 |
| Zcut的两低项实际吸收 | 347 | 30 | 39 | 66,873 |
| 同源Tcut与相对形式控制 | 221 | 22 | 49 | 61,630 |
| 实际合成输入与完整宏next | 565 | 36 | 69 | 62,220 |
| Tcut真实逆与原g对偶窗口 | 243 | 11 | 16 | 61,966 |
| 原非零频谱严格收缩 | 130 | 11 | 13 | 60,751 |
| Stage9前向测试与原配对导数 | 108 | 12 | 25 | 61,203 |

各批默认 strict、标准三公理。完整 type/value、raw 发生、opaque 及实际
消费者与生产逐项对应；没有新增源正则性、目标预算或完整未来字段。

`Distributed/{Lyapunov,Response,Green,Initial,Weighted}` 五模块独立 focused
`--trust=0 -DwarningAsError=true` 通过；15 个关键口仅标准三公理，完整 import 闭包
无 scratch。其公开数值口保留原两项有号功，不把它们记作已付预算。
`Mean`、`SourceTest` 及共享积分器的独立 strict 验收通过，15 个相关口仅标准三公理；
完整 import 闭包无 scratch，双钟语义与源自选吸收常数已核验。
`Tensor` 至 `CenteredRate` 的混合张量、移动时钟、正负扩散与直接 W 消费分别独立 strict 通过；关键口仅标准三公理，生产 import 闭包无 scratch。`CoveredBand` 的覆盖量词与原 high current 消元同样经独立验收；`PotentialHalf` 的四个公开口 strict 通过且仅标准三公理，H¹ 乘法平方与真实 Fourier 半阶编码已核验。`Compensated` 的实际 AC／FTC、`PotentialWork` 的四次 Young 及 `PotentialBudget` 的源内覆盖选择和积分直接消费均独立 strict 通过，关键口仅标准三公理。

`PairTrace`、`TwoTimePair`、`KernelLift`、`KernelBudget`、`IntegralComparison`、
`KernelAbsorption` 均独立默认 strict 通过，关键口仅标准三公理，生产 import 无 scratch。
双钟方向、原对角读出、核导数符号及新 ε 的生成次序均已核验。

## 权威源码

- [Trace.Inverse.Integral](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Inverse/Integral.lean)：实际移动逆质量及完整净率 FTC。
- [Trace.Distributed.Weighted](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Distributed/Weighted.lean)：原 κ 零终端响应的图费用、初态与时钟付款，直接进入原 W 有号读出。
- [Trace.Distributed.Mean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Distributed/Mean.lean)、[SourceTest](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Distributed/SourceTest.lean)：原 Stage9 均值付款与 W 自生成测试的二阶预算入口。
- [Trace.Coupled.Bound](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Coupled/Bound.lean)、[Next](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Coupled/Next.lean)：原合成输入的一次 G 付款与实际选择曲线宏 next。
- [ConvectionCutoff.Operator.DualWindow](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/ConvectionCutoff/Operator/DualWindow.lean)：同源 Tcut 的真实逆与完整原 g 对偶预算。
- [Trace.Adjoint.Gap](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Adjoint/Gap.lean)、[Endpoint.Action](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Endpoint/Action.lean)：原物理黏性收缩与真实前向配对写入。
- [Trace.Operator.Action](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Operator/Action.lean)：原 T/J 的实际物理配对与 next。
- [Trace.Adjoint.Write](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Adjoint/Write.lean)：原非自治 source 与 propagated/response 的端点 FTC。
- [Trace.Dual.Control](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Dual/Control.lean)：同源逆与原 g 对偶终值的统一预算。
- [Trace.Clock.Inverse](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/Trace/Clock/Inverse.lean)：两个真实时钟与 canonical inverse 的直接比较。
- [ConvectionCutoff.Window](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/StressHeat/ConvectionCutoff/Window.lean)：原 cutoff 的全 κ 黏性 primitive、实际散度与 next。
