# 原空间外场的完整 current 插入与窗口积分

本包生成同一原 current 的五项空间卷积，以及原入射球窗和原尺度观察窗共同产生的
边界算子。它是后续实际动量矩的直接积分消费者；不把尚未积分的核命名为耦合常数。
原 source、准备、Dirac-dual、物理时间和 visit10／tick16→17 保持。

## 原空间约定与两个不同窗口

原场使用负相位 `exp(−ik·x)`，原 current 的输出 Fourier 也使用负相位。
所以输出 p 配对的是两个场标签 k 与 k−p。量子 current probe 是物理 k，
Lean 中 `h=k/(2π)`；量子内部 matter Fourier 变量另记 r。
以下 `dμ(k)=(2π)⁻³d³k`。时间参数为两个独立的 z,w，实部在原共同正则域内。

记原入射球半径为 B，`w_B(k)=1_{|k|≤B}`。同一原方程的一次插入先产生完整输出，
`PacketScale.physicalRead` 再以 `C_R` 读取其输出谱；这个操作给 `w_R(k)`。
它不加入 H 或 Noether 方程。R=B 时两种窗也须先分别保留，因为空间外场会移位。
未施加输出观察窗的 current 可将以下所有 w_R 取1。

设 `F_z(k)` 是原 unvaried theta transfer 在物理导数 `(z,−ik)` 的289列。
它的 theta 根、准备源和分母属于 k。对于 `a_δ=e^{iδ·x}dx1 S01`，定义
`G_{z,δ}(K)` 为同一完整源逆产生的有序响应：输出负相位标签为K，输入为K+δ。
其原方程是

`H0(z,−iK)G_{z,δ}(K)+Vδ(K←K+δ)F_z(K+δ)=I1δ(K←K+δ)`。

V、实际本构变化、先生成的Noether补源和168辅助回写来自 JointTransfer／JointCausal。
G保留**入射K+δ的原theta根和分母**，不重取输出根。

取固定投影 `P=|ψ><ψ|`。以下量子向量可统一取

`j_z(k)=Pchoice Bhat_k(z)ψ`，`z_{z,q}(k)=Pchoice Chat_cos(q),k(z)ψ`，

其中 `Pchoice=I` 给raw，`I−P`给connected，`P`给mean。Chat由同一个余弦扰动的
两条Duhamel腿及直接current项生成；其两支Cσ已各含余弦半因子一次。
恒有raw=connected+mean，原准备与normalizer不随外场重置。

## 五项精确空间卷积

定义真实两腿导数

`L_z(k)=(bar(z),+ik)`，`R_w(l)=(w,−il)`，`r_b=(−bar(z)−w,−ip)`。

`Q_b(L,R)` 是完整native current，包括真正Bg二阶回写。
`Q'_{b,δ}(L,R)` 是 ReducedContact 的完整12变量接触，外插入为 `(0,iδ)`；
必须满足 `L+R+(0,iδ)+r_b=0`。这同时保留原scalar项和本构lift责任。
下式写的是有序复配对，不提前丢弃其虚部。Q的双腿交换性在同参数物理读数中
给原真实密度；一般p的Fourier值仍可为复数。

对σ=±1令δ=σq、l=k−p+δ。三个场／reader核是

```
ΦRσ(k) = < Fz(k) jz(k),
            Qb(Lz(k), Rw(k−p)) Gw,δ(k−p) jw(l) >
ΦLσ(k) = < Gz,−δ(k+δ) jz(k),
            Qb(Lz(k+δ), Rw(l)) Fw(l) jw(l) >
ΦCσ(k) = < Fz(k) jz(k),
            Q'b,δ(Lz(k), Rw(l)) Fw(l) jw(l) >.
```

第一个槽共轭线性，Q作用于右场指标。左传播的−δ在求实余弦和时重标而来。
两条noise核在未移动的场输出k,k−p上为

```
ΦNZ(k) = < Fz(k) zz,q(k), Qb(Lz(k),Rw(k−p)) Fw(k−p) jw(k−p) >
ΦZN(k) = < Fz(k) jz(k), Qb(Lz(k),Rw(k−p)) Fw(k−p) zw,q(k−p) >.
```

相应窗口必须逐项取

| 核 | 原入射窗 | 输出观察窗 |
|---|---|---|
| ΦRσ | wB(k)wB(l) | wR(k)wR(k−p) |
| ΦLσ | wB(k)wB(l) | wR(k+δ)wR(l) |
| ΦCσ | wB(k)wB(l) | wR(k)wR(l) |
| 两noise | wB(k)wB(k−p) | wR(k)wR(k−p) |

乘这些窗后的核记为T。完整的空间一阶插入是

`Π_b(p,q;z,w) = 1/4 Σσ ∫(TRσ+TLσ+TCσ)dμ + 1/2 ∫(TNZ+TZN)dμ`。

前面的1/2来自原二阶涨落current，前三项另一1/2来自cos两支。
noise的Chat已经含cos半因子，不能重复乘。q=0时此式精确回到已签
NativeResponse／JointFamily的两场腿、reader接触和两noise腿。

证明在原双线性频域current中插入有序源变化，使用物理Fourier和变量平移。
对源逆实际生成且在所用紧支持上有界的列，空间Cauchy–Schwarz付每个积分存在；
Q中的空间导数也在该支持上有界。左腿仅重标输入k并将σ改为−σ，
这给表内不同的观察窗。没有丢掉一条输入路径，也没有改变原传播源。

本包签收上述频域配对及空间窗口积分算子。若将它识别为整球非共线响应的双时间
Laplace读数，必须再消费该Gδ族的统一proper／timejet与原Bg两个时间初始边界。
既有固定incoming／共线JointCausal及固定动量JointFamily只支付其各自范围，
本包没有把它们自动推广为整球的时间Fubini或完整finiteε演化。

这是完整**线性化方程的一次插入**空间消费者。整空间有限ε余弦boson流的统一构造
另由其实际发生支付；本公式不从一个固定入射动量的有限族偷推出它。

## 所有同向外动量的真实窗口二阶算子

取 `p=α s n,q=s n`、`|n|=1`、s↓0。R=B时，窗 `w_R(k−c s n)` 的中心集合为

| 核 | 全部c |
|---|---|
| ΦRσ | 0,α,α−σ |
| ΦLσ | 0,−σ,α−σ |
| ΦCσ | 0,α−σ |
| 两noise | 0,α |

若0<R<B，则在 `|s|(1+|α|)<B−R` 内，表中入射窗在输出支持上自动为1。
此时前三集合分别为 `{0,α}`、`{−σ,α−σ}`、`{0,α−σ}`，noise仍为`{0,α}`。
这个严格内尺度极限与R=B必须按各自原窗计算。

球的凸性使任意中间中心的约束由极端两球推出。令
`a=(max c+min c)/2`、`d=(max c−min c)/2≥0`。
对该项的实际复核Φ(k,s)，令

`Ψj(k)=(∂s+a∂n)^j Φ(k,s)|s=0`，j=0,1,2。

当这个核的两阶jet在闭球邻域强连续时，真实积分的三个系数是

```
I0 = ∫ball Ψ0
I1 = ∫ball Ψ1 − d ∫sphere |n·ν| Ψ0
I2 = 1/2 ∫ball Ψ2
     + d²/2 ∫sphere (n·ν) ∂nΨ0
     − d ∫sphere |n·ν| Ψ1.
```

即 `I(s)=I0+s I1+s² I2+o(s²)`；乘原物理测度以及上面的真实1/4、1/2。
I2是Taylor系数，二阶导数对应2I2。反向s使用真实变换后的核和端点；
只有原分支／真实读数的反射关系支付后，才可把一次项合并成|s|。

这给同一source空间卷积的**精确积分口**。实际F、G、j和z的所有乘积导数都在Ψ内；
本包不把未提供的整球joint jet或积分值当作已经算出。ProbeLaplace／ProbeMoments
与原全动量transfer消费者直接付这些实际jet。

证明沿n作球弦。平移k=y+a s n后，长弦端点为`−h+d s,h−d s`。
展开核而保留这两个真实端点，得到上述I1、I2；端点导数差正是
`∫sphere(n·ν)∂nΨ0`，不是可以省略的零。
短弦h<d s的横向面积为`πd²s²`、原球内体积为`4πd³s³/3`，因此不贡献s²。
紧闭球上的二阶导数连续模量给o(s²)；若C³且三阶有界，得到统一O(s³)。
`assembly.py` 对任意复四次以内弦jet直接积分，逐个核验零、一、二系数。

α=0时两传播和接触的窗宽均为|s|，noise窗不动；α=1时实际出现0、|s|和2|s|
三种宽度。这就是p独立于q的实际区别。旧autocorrelation只有在
`Φ=B(a(k),a(k+s n))` 的真实对称恒等式下，才把端点二阶项消成旧体积分。
例如`Φ=s`的真实二阶边界项是`−2πR²d`，旧抵消法会错误地给零。

## 原shell消费者

原 `C_R−C_r` 作用于完整输出场。对任意双线性current，尺度差恒为
`shell–shell + low–shell + shell–low`；同一恒等式对参数插入继续成立。
接触项的有效平移为p−σq，所以即使p=0，也没有原零平移正交性可以删掉交叉。
程序给出实际三维正体积盒：外半径2、内半径1、平移e3时，体积1/100的盒中
一个点在内球而另一点在壳。它是此正交错误的显式反控制，不替换原source准备。
真正shell二阶读数直接取上述原尺度系数之差，保留两序cross。

本包证据是原phase／48个源双jet／contact约定、精确窗代数与解析积分证明。
它不新增Lean声明；当前原theta的完整数值空间积分由这个口继续生成。
