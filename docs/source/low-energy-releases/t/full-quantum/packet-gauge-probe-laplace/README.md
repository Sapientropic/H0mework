# 原current探针的全时间Laplace导数

本包从同一原矩阵生成全部物质动量上的真实Sylvester逆，并给原current与其恒定规范
场ε响应的两阶物理探针导数。原准备波包的移动、固定中心化及全时间积分同时保持。
它直接补齐空间外场匹配中两个current探针随动量移动的责任；原root／SpinPair／时钟不变。

## 原准备自身生成8维入口

在已签完整252→12载体中，原V满足 `P8=V²/N²` 是秩8正交投影，且它与H0、全部Hj、
V、K对易。原 `C0⁻¹ seed` 位于其像中。因此原Green产生的同一ψ、全部原发展和current
都留在P8内；没有投影后重新归一或更换制备。
P8按原K的两个本征值±√2分成实际4＋4，每块对H、V均双侧reducing。
原完整Y非零的事实保持，这只是本源真实限制。

## 同源特征方程生成全动量逆

令 `c=N sqrt2`、`h=H/c`、`x=|physical p|²/2`。从实际轴向Hermitian矩阵的
characteristic polynomial直接生成

\[
 P_-(u,x)=u^4+6u^3+(324/25-2x)u^2
 +(1458/125-6x)u+x^2-108x/25+2187/625,
\]

`P_+(u,x)=P_-(-u,x)`。程序再在三个独立物理动量变量上逐项支付 `P_chi(h(p),x)=0`。
没有从有限方向样本外推。

在16维商代数 `C(x)[u,v]/(P(u,x),P(v,x))` 中，左右乘法分别由两个真实companion
生成，基为 `u^a v^b`（0≤a,b≤3）。取本次原频率

\[
 z=c\zeta,\qquad\zeta=6(1-i).
\]

程序实际求出 `zeta−i(u−v)` 的双侧逆，保存它的16个有理系数s_ab(x)。原两侧
Cayley–Hamilton身份给对全部真实p的实际算子

\[
 \boxed{\mathcal R_z(A)=c^{-1}\sum_{a,b=0}^3
 s_{ab}(|p|^2/2)h(p)^a A h(p)^b,\qquad
 (z-i\operatorname{ad}_{H(p)})\mathcal R_z=1.}
\]

商代数逆的全实域也由原矩阵支付：每个x≥0，P是实际轴向Hermitian矩阵的特征多项式，
其所有根实。两个companion的联合三角形因此给谱 `zeta−i(Ea−Eb)`，实部始终为6；
即使P有重根，原16维矩阵仍可逆。已约分系数的分母整除其行列式，不在x≥0造伪极点。

真实矩阵Laplace积分为

\[
 \mathcal R_{z;L,R}(A)=\int_0^\infty e^{-zt}e^{itH_L}Ae^{-itH_R}dt.
\]

两H均Hermitian，故对全部η=Re z>0存在，Hilbert–Schmidt范数界为1/η；实际微分和
∞端消失给 `zR−i(H_LR−RH_R)=A`。逆的唯一性识别上述生成多项式与这一真实积分。
这里的z是时间Laplace参数，原制备Green的E=0／η=1并未替换它。

## 固定输出动量的原current核

现在固定物质输出动量p，current探针为物理k，输入因此是p−k。令

\[
 \mathcal R_k=(z-i(H(p)\,\cdot-\cdot\,H(p-k)))^{-1}.
\]

原完整current和其恒定背景幅度ε导数直接给

\[
 B_k=\mathcal R_k\left(\frac K{N^2}[H(p)+H(p-k)]\right),
\]
\[
 C_k=\mathcal R_k\left(\frac{2KV}{N^2}+i(VB_k-B_kV)\right).
\]

C是同一原 `H+εV` 的真变化，保留两条传播腿与直接current项；不是两个单粒子
Laplace逆的乘积。k=0时恰恢复全时间守恒的
`B0=2KH/(N²z)`、`C0=2KV/(N²z)`。

由于输出p固定，探针微分作用在**右侧**H(p−k)。原逆的真实微分给

\[
 B_i=\mathcal R_0[-KH_i/N^2+iB_0H_i],\qquad
 B_{ij}=\mathcal R_0[i(B_iH_j+B_jH_i)],
\]
\[
 C_i=\mathcal R_0[iC_0H_i+i(VB_i-B_iV)],
\]
\[
 C_{ij}=\mathcal R_0[i(C_iH_j+C_jH_i)+i(VB_{ij}-B_{ij}V)].
\]

这些有限有理运算构成全部p上的可消费matrix circuit，不要求展开巨大的世界坐标表。
原Hi是物理动量导数，1/c仅出现在真实Sylvester逆中；没有另乘2π或漏掉原时间缩放。

## 同一实际波包也必须移动

原Fourier输出是 `B_k(z,p) psi(p−k)`，C同理。对G=B或C，真正的向量导数为

\[
 g_i=G_i\psi-G_0\partial_i\psi,
\]
\[
 g_{ij}=G_{ij}\psi-G_i\partial_j\psi-G_j\partial_i\psi
             +G_0\partial_{ij}\psi.
\]

原normalizer和P保持固定。程序在p=0从原 `(i−H)R=iC0⁻¹` 生成包的一、二阶jet，
二阶保留单位球的 `−delta_ij/5` 项，再消费真实B/C核。
三条一阶和三个对角二阶导数均有 `psi wedge g` 非零minor，消去任何均值倍数。
真实Green、球Fourier代表与Sylvester有理核在p=0附近连续，所以非零保持在开集，
产生同一L²载体中的真实中心化导数非零；不是仅凭单点推断L²。

## 全时间强导数与真正积分交换

所有原位置矩由既有源生成。对单位n令X=n·y、
`P_m(t;f)=sum_j binom(m,j)(N|t|)^(m−j)||X^j f||`。
原群保持这些域，且原有界V的Duhamel积分满足

\[
 \|X^mD_V(t)f\|\le N|t|P_m(|t|;f),\qquad\|D_V(t)\|\le N|t|.
\]

从同一current直接微分M_k，m阶方向导数的真实范数界为

\[
 A_m^B=\alpha[2P_m(t;H\psi)+N|k|P_m(t;\psi)+mNP_{m-1}(t;\psi)],
\]
\[
 A_m^C=\alpha N[2P_m(t;\psi)+4tP_m(t;H\psi)
 +2N|k|tP_m(t;\psi)+2mNtP_{m-1}(t;\psi)].
\]

m=0时最后项取0，`alpha=sqrt2/N²`。左右Duhamel腿均在其中；混合方向由同一源矩和
Hölder支付。`bounds.py`生成m=0…3的实际非负有理多项式；m=1／k0准确回读已签probe界。
原差商与位置矩支配给真正强C∞，不预支H²ψ。

所有η>0的完整半轴阶乘moments给强导数与积分交换；三阶界另给真实二阶Taylor
余项 `|h|³ L3/6`，在连线位于原探针球时统一有效。固定expectation／P以及Hilbert
内积将这些实际向量jet送到raw、mean和connected的完整两probe Gram导数。

另一个直接接口是：`C_cos(q;k)`对每个k均为q的偶函数，真实联合位置矩给混合强导数，
所以q0处 `Dq=0` 及 `Dk Dq=0`。当两个探针也随外动量移动时，其二阶source项是已经
生成的真实外q Hessian加此处恒定输入的完整两probe Hessian；两probe乘积交叉仍保留。
场传播与尖窗边界继续由各自原producer消费。

## 验收入口

`resolvent.py`实际生成两份全动量商逆，在新非轴物理p上对全部16矩阵单位支付双逆，
全部B/C一、二阶方程通过；错把右Hi写到左侧确有非零差。
`consumer.py`给原准备包的实际非零jet，`bounds.py`付整半轴强积分与余项。
按这三个程序重放，冻结文件见 `construction.json`。
这是原源精确代数与上述连续证明，无新增Lean声明。
