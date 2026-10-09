# 整个原轻球上的量子源曲率贡献

本包把原五项空间响应中的**两条量子源变化**真正积分到整个原轻动量球。
保持同一原准备、完整native current、物理测度和非零均值；reader为原A1/S01，
outgoing current动量p=0，双频 `z=w=6c(1−i)`，外背景仍为 `cos(q·x)dx1 S01`。

令 `B=√2 ε`、`ε=5234375/294988800512`。对每个单位外物理方向n，所得真实
q-Hessian贡献严格满足

`−6.25928534×10⁻²² < S_n < −5.34484924×10⁻²²`。

精确有理区间见receipt.json。这是原源单位下的Hessian，Taylor二次系数为其一半。
场传播变化与reader接触是完整空间响应的其他加数，未在这里删去或冒称已相加。

## 从原字段产生全空间native系数

GlobalTransfer给同一原theta的真实函数

`X0(z,k)=(z A(k,U,T)+Bcol(k,U,T))/(D(U,T)(z²−c²U))`，

其中 `T=|k|²/2`，`U=T R(T)` 是原完整Fhat的同一个根，
`D=Fhat_U/cF`。此处Bcol是字段多项式，与球半径B不同。
原场采用负Fourier相位，所以双腿导数为 `(bar z,+ik)` 和 `(z,−ik)`。

从原bijet及全部72个辅助current的真实本构回写生成

`Qeff=QA+Σ (b_reader)_j QBj`，
`b_reader=−star D_A(reader)/σ`，
`reader derivative=(−12c,0,0,0)`。

所需实际系数为

`C(k)=1/2 X0(z,k)† Qeff X0(z,k)`。

程序先在独立kx,ky,kz,U,T上计算全部分子，而不是用数值动量样本拟合。
它有685项，全部系数实；共同分母正好为

`D(U,T)² c⁴ (U²+5184)`。

原点直接给 `C(0)=√15/25000`。原非轴动量k=−kin的分子在完整Fhat上严格回读
已签ReducedCurrent，分母也逐项同值；因而物理Fourier号、native配对、两腿时钟和
原current的1/2同时保留。

## 全球严格正界与真实测度

同一原根已给 `0≤U≤T≤ε²`、`39/40≤D≤41/40`。
程序进一步直接由D的非恒定系数生成δD，得到 `|D−1|≤δD<1/40`。
对分子每个非恒定单项式，使用

`|ki|≤√2 ε<3ε/2`，`|U|,|T|≤ε²`

及整数平方根产生的根式有理区间，累加成原分子的统一变化界。
除以上正分母，整个轻球的真实C都在

`0.0001549193308186325975 < C(k) < 0.0001549193368779607818`。

这里的多项式估计对整球和原点成立，没有用中心值代替C(k)，也没有改用低阶色散。

原物理积分测度为 `(2π)⁻³d³k`，因此球的实际体积权重为

`B³/(6π²) ∈ [2.6685289152662552116,2.6685289152662552117]×10⁻¹⁶`。

π由原纯有理Machin／交错余项算法生成，√2由整数平方根区间生成。
没有除以球体积或重新归一波包。

## 同一真实量子源的外q Hessian

在固定原ψ和P上，记原current的raw向量为
`b_k(z)=Bhat_k(z)ψ`，原余弦幅度ε导数为 `c_q,k(z)=Chat_cos(q),k(z)ψ`。
对应源噪声变化是

`N1(q;k,k)=<c_q,k,b_k>+<b_k,c_q,k>`。

CosineMomentum的真实强导数和CosineCurvature的完整半轴积分已生成

`H_n(k)=D_q² N1(0;k,k)[n,n]`。

原位置矩把其严格区间送到整个轻球、全部单位n。消费的实际区间为

`−0.015140743693003218 < H_n(k) < −0.012928791594747486`。

它是raw的完整均值加connected，不用connected的方向符号替代raw。
所有复交叉都在原两腿Gram中；k=k且z=w时，上述两项之和及其Hessian为实。
原cos两个半幅的二階q导数加在一起，不额外乘1/2。

原五项空间公式的noise两腿在p=0时都有固定窗口wB(k)，不随背景q移动。
因此这一实际加数的Hessian恰为

`S_n = ∫|k|≤B C(k) H_n(k) d³k/(2π)³`。

球内C严格正、H_n严格负。用以上实际全球区间和真实测度作一次积分，便得到开头
的严格负区间。保留外半径R=B；这是实际量子源加数的整球积分，而非一点校准。

## 全时间读数与native辅助边界

同一GlobalTransfer的retarded核为

`χ0(t,k)=[A cosh(c√U t)+Bcol sinh(c√U t)/(c√U)]/D`。

原 `0≤U≤ε²`、`c<1`、`ε<1/50000` 给整个轻球共同增长界1/50000。
U=0的sinh商取其真实整个延拓t。A/Bcol及其各分量在球上的界，直接由有限多项式
系数绝对值和上述根式／径向界生成；因此χ0有统一 `const(1+t)e^(t/50000)` 界。
原量子B、C及外q二阶／四阶强差商由既有位置矩给多项式时间界。
两份阻尼Re z=6c>5共同支配这些真实核，支付空间／两时间Fubini和q二阶微分交换。
这里只使用同一未扰动传播χ0；不需要把未完成的非共线Gδ时间结论当输入。

native Qeff所需的Bg时间边界也在全动量上实际支付：

- A的全部spatial gauge行恒零，所以其核在初始时刻为零。
- 原curvature derivative作用于 `zA+Bcol` 的z²系数，所有72行精确为零，
  因而第一曲率transfer严格proper。连续强迫下其场初值为零。
- 原投影源Z的全部72个Bg行恒零，故同一场一直处在原线性本构图上。

场本身从零过去卷积产生，初值为零。这些实际零式使极化Bg二阶回写中的e²、eF1、AA
在任一时间端点为零，才允许weak reader取两频率之和。A0的非零核初始项未删除。
因此整球积分消费的C确实是原native current的同一双时间读数。

## 重放与证据身份

```sh
uv run --offline --with sympy==1.14.0 --with python-flint==0.8.0 python Verification/physics/low-energy-phenomenology/full-quantum/packet-gauge-spatial-source-curvature/compute.py
```

最终回执为4.352秒EXIT0；原685项分子、完整分母、全球区间、原完整根读回和实际
时间边界检查均保存于receipt.json。新结果是源精确程序、既有强导数及上述解析积分
的共同消费者，没有新增Lean声明或controller更新。
