# 原空间 reader 接触项的真实球窗展开

同一原 S01/dx1 reader 与外场、p=0、`z=w=6c(1−i)`、原球窗及 R=B 下，
完整 native reader 接触项已生成整个轻球上的真实单侧展开。原准备 ψ/P、完整均值、
Dirac-dual、物理钟和固定 root 保持。

对全部单位物理方向 n、s↓0：

\[
 I_C(sn)=I_0+I_1(n)s+I_2(n)s^2+o(s^2),
\]

\[
 1.28716\cdot10^{-23}<I_1(n)<1.54479\cdot10^{-23},
 \qquad |I_2(n)|<3.687\cdot10^{-26}.
\]

I1 是真实的 `|q|` 球窗边界项。I2 是二次 **Taylor 系数**，没有把整个函数称为
原点处的二阶可微函数。它的大小比已闭合两 source 腿的二次系数至少小7000倍。
这三项合计的二次系数仍严格为负；另外两条场传播腿继续分别保留。

## 源直接生成实际接触

输入为已签收 GlobalTransfer、ReducedContact 的完整12变量矩阵、SpatialCurrent
五项／窗口公式，以及 ProbeMoments 的真正全时间波包矩。

在原 source 的同一完整289坐标中，所选 Q′ 有97个 coframe 项和4个 scalar 项。
实际 theta 的全部 scalar 列在全动量上恒为零。保持全部输入动量后取

`left=(bar z,+ik)`，`right=(z,−i(k+q))`，
`external=(0,iq)`，`weak reader=(−12c,0)`。

原实际 coframe 子块自动化为

\[
 Q'(q)=Q_0+\sum_jq_jQ_j,\qquad Q_0^\dagger=Q_0,\quad Q_j^\dagger=-Q_j.
\]

它不依赖两场自身的动量。这些等式来自原 full contact 表的逐项计算；
没有套用 q=0 contact，也没有丢弃原 scalar 矩阵后再假定其作用为零。

令 F(k) 是同一 GlobalTransfer 的实际 coframe 列，
`b(k)=Bhat_k(z)ψ` 是固定原包上先完整作用后的 quantum current 向量。
在共同 Hilbert 空间取 `A(k)=F(k)⊗b(k)`。该记号消费真实源 Gram，
不把全 Fock 算子乘积改成一粒子乘法同态。

两支各1/4的实际积分为

\[
 I_C(q)=\frac14\sum_{\sigma=\pm1}
 \int_{|k|\le B,\ |k+\sigma q|\le B}
 \langle A(k),Q'(\sigma q)A(k+\sigma q)\rangle\,
 \frac{d^3k}{(2\pi)^3}.
\]

这里 `B=sqrt2*5234375/294988800512`，两个窗口均保持。
Q的实际伴随身份让中心变量 `k±q/2` 的两支互为共轭，因而积分等于
一半中心 lens 上的实部。native quadratic 的1/2与cos两支的1/2已经计入。

## 原球面项兑现精确抵消

记 `K(k,s)=Re⟨A(k−sn/2),(Q0+sQn)A(k+sn/2)⟩`，`Qn=ΣnjQj`。
K 对 s 为偶函数。原两球弦公式给

\[
 I_1(n)=-\frac14\int_{|k|=B}|n\cdot\nu|K(k,0)\,d\mu_S,
\]
\[
 I_2(n)=\frac14\int_{|k|\le B}K_{ss}(k,0)\,d\mu
       +\frac1{16}\int_{|k|=B}(n\cdot\nu)\partial_nK(k,0)\,d\mu_S.
\]

K_s(k,0)=0，因此第三个可能的混合表面项由同一源伴随身份消去。
使用真正的散度定理，再展开同一 A 的乘积导数，得到精确实际消费者

\[
 \boxed{I_2(n)=\int_{|k|\le B}
 \left\{\frac14\operatorname{Re}\langle A,Q_0A_{nn}\rangle
       +\frac12\operatorname{Re}\langle A,Q_nA_n\rangle\right\}d\mu.}
\]

左右一阶导数的交叉项是在体积与球面通量中精确相消，不是被删除。
特别是 A 的真实线性原点项：若直接丢掉通量，会产生非零的 O(B³) 二次系数；
保留通量后这一项严格为零。`shape.py` 对原真实 tensor 逐系数支付抵消，
丢通量所得 e1 项大于最终严格 bound 的一百万倍。

## 同一原根和真正全时间探针产生 C³ 界

`bounds.py` 从原完整 `Fhat/cF` 计算 D=F_U 及其所有三阶偏导。
对同一个真实根 U(T)，直接微分原方程：

\[
 U'=-F_T/D,\quad
 U''=-(F_{TT}+2F_{UT}U'+F_{UU}U'^2)/D,
\]
\[
 U'''=-\{F_{TTT}+3F_{UTT}U'+3F_{UUT}U'^2+F_{UUU}U'^3
          +3(F_{UT}+F_{UU}U')U''\}/D.
\]

全部界由原多项式系数、`0≤U≤T≤epsilon²` 和实际 `D>39/40` 生成。
对任意单位混合方向，T 的一／二／三阶界是 B、1、0，U对应界是
`U1 B`、`U1+U2 B²`、`3U2 B+U3 B³`。
有限多项式与真实分母 `D(z²−c²U)` 的乘积／逆微分生成 F 的混合 C³ 范数界。
分母使用实际 `|z²−c²U|≥|z|²`，不截断色散或供应目标导数证书。

同一原 F(0)=0。其原点 first、second jets 从完整 source 产生并保存。
原点 packet 的 `||b(0)||²` 与三方向 `⟨∂i b(0),∂j b(0)⟩=M δij`
直接消费 ProbeMoments 的 **raw、全时间** 两 probe 积分，非零均值保留。
再消费 ProbeLaplace 的实际 B2、B3 位置矩界，生成整球 b 的混合 C³ 界。
混合方向沿用原位置矩的 Hölder 与有序 H_n 插入界，未要求 H²ψ。

记这些实际生成的界为 `a1>=||DA(0)||`、`a20>=||D²A(0)||`、
`a2>=sup||D²A||`、`a3>=sup||D³A||`。
实际约为 `a1=0.0142181`、`a2=0.0212403`、`a3=1.79034`。
它们来自固定的原 A，未作为 caller 输入。

从 A(0)=0，将上述精确 I2 中的两项分别减去
`Re⟨DA(0)k,Q0 D²A(0)[n,n]⟩` 与
`Re⟨DA(0)k,Qn DA(0)n⟩`。这两项在整球上为奇函数，积分严格为零。
Taylor 的真实积分余项和 Cauchy–Schwarz 随后给

\[
 |I_2(n)|\le\frac{B^5}{10\pi^2}\left[
 \frac{\|Q_0\|}{4}
   \left(\frac{a_2a_{20}}2+a_1a_3+\frac{a_2a_3B}2\right)
 +\frac{\|Q_n\|}{2}
   \left(\frac{3a_1a_2}2+\frac{a_2^2B}2\right)\right].
\]

原矩阵行范数、完整 mixed packet Gram 及所有有理根式界实际代入后，得到
`|I2|≤3.686515414428545×10⁻²⁶`。原测度完整保留，`∫ball|k|²dμ=B⁵/(10pi²)`。
这也支付 shape 公式所需的真实 C² 与余项，没有只有一个条件积分接口。

## 非零尖窗项与直接消费者

原 first jet 给出具体矩阵

\[
 (DF(0))^\dagger Q_0DF(0)
 =-\tau\operatorname{diag}(2,1,1),\qquad
 \tau=\frac{32041\sqrt{30}}{31492800}>0.
\]

原球面的实际 `∫|n·ν|ννᵀdΩ=pi/2*(Id+nnᵀ)` 因而给

\[
 I_{1,\mathrm{lead}}(n)=\frac{G_0 B^4\tau}{64\pi^2}(5+n_1^2),\qquad
 I_{0,\mathrm{lead}}=-\frac{G_0 B^5\tau}{15\pi^2},
\]

其中 G0 是实际 raw packet 的全时间零 probe Gram。
同一 a1/a2 的 Taylor 界控制整个球面的 remainder，得到开头的全方向严格正 I1，
以及 `I0∈[−2.75662487,−2.75634186]×10⁻²⁸`。没有只报告 leading 符号。

把已独签两 source 腿的 **Hessian 除以2**，再加本接触项的二次系数，得到三项的
共同严格区间

`[−3.13001133,−2.67205597]×10⁻²²`。

原非零均值与全部复配对仍在其中。该消费者闭合了五项中的第三项；
两条 Gδ 场传播项不在这里被代填，也不把这个局部响应称为 kinetic beta。

## 证据与重放

顺序运行 `bounds.py`、`shape.py`，使用离线 SymPy1.14.0／python-flint0.8.0。
两程序均 EXIT0；源矩阵、原点 jets、完整源域界、严格积分区间和反控制分别保存于
`bounds.json`、`shape.json`。新结果是原精确代数与上述解析消费者，新增 Lean 声明为0。
原已签未扰动 theta 因果核及 packet 全时间支配使这些读数仍为真实双 Laplace 读数；
接触 coframe 项没有场导数槽，scalar项在同一场上为零，不借用新的 Gδ 时间结论。
