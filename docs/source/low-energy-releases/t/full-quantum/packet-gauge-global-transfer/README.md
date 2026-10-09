# 原289场的无角框架全动量 theta transfer

本包由原 pole-source 的 A、B、Z 同时生成无角框架公式，保留同一原 θ 根、own residues、
FullPhase 和物理时间。Z 先从原源表生成，再核完整场方程；不是用目标场反定义外源。
构造完成后的冻结入口为 construction.json，独立认证另行进行。

## 原三列的实际表示

原轴向数据满足

\[
A=-\frac c{c_F}\frac{V(u,q)-V(-u,q)}{2u},\qquad
B=-\frac{c^2}{c_F}\frac{V(u,q)+V(-u,q)}2,
\]

其中 c=N√2=6√15/25、c_F=−100383300000000。Z 是原 pole-source 中已经生成的
source_projection_numerator。A/B 按原 field 圈 L 运输，Z 按源协向量 L⁻ᵀ 运输；
后者的真实生成元是 −Gᵀ，不能从字段名称猜同一个 variance。

对每列的实际表示，程序计算 C=−ΣGᵢ²，并证明只有 j=0、1、2，且 Gz 权重为0。
三个原投影分别给：

| 原列 | j=0 非零轴向行 | j=1 | j=2 | 全球非零多项式行 |
|---|---:|---:|---:|---:|
| A | 21 | 22 | 13 | 87 |
| B | 35 | 17 | 26 | 114 |
| Z | 18 | 12 | 7 | 56 |

每个实际分量恰有 qʲ 因子，剩余为 U=u²、T=q² 的多项式。没有预设 rank，也没有
保留1/|k|角分母。原反射 Ly(1)、九个 Lz 系数、field／covector 两套完整 circle ODE，
以及每列9个完整生成元等变恒等式逐项通过。相同初值与实际 circle ODE 的唯一性将下式
识别为原任意圈运输，而不是从有限方向样本外推。

对任一列，写其径向部分为 W0、W1、W2，令
C2=(Gy²W2+3W2)/2、E2=Gz C2。其全球分子为

\[
\begin{aligned}
\mathcal N_W(k,U,T)={}&W_0-\frac{k_zW_1+k_xG_yW_1-k_yG_xW_1}{\sqrt2}\\
&+\frac{2k_z^2-k_x^2-k_y^2}{4}W_2
+\frac{k_xk_z}{2}G_yW_2-\frac{k_yk_z}{2}G_xW_2\\
&+\frac{k_x^2-k_y^2}{2}C_2+\frac{k_xk_y}{2}E_2.
\end{aligned}
\]

线性负号是原 ell(−k) 反射。A_global 精确回到已签 SeedRegularity 的87行，B、Z 是新增
实际列。三列均有 conj N(k)=N(−k)。source.json 保存全部有限多项式及原点值。

## 全三维原方程与因果核

令 T=|k|²/2，U=T R(T)，R 是原 axialPhase sourceRoot 的同一根。记
D=∂U Fhat/c_F，则

\[
\boxed{X_0(\lambda,k)=\frac{\lambda A_g(k,U,T)+B_g(k,U,T)}
 {D(U,T)(\lambda^2-c^2U)},\qquad I_0(k)=\frac{Z_g(k,U,T)}{D(U,T)}.}
\]

物理 Fourier 符号为 (λ,−ik)。程序以 λ、U、T 为独立符号，在2T=|k|²下直接生成

\[
\boxed{H_{289}(\lambda,-ik)(\lambda A_g+B_g)
 =(\lambda^2-c^2U)Z_g-\frac{c^2}{c_F}\widehat F(U,T)j_{g00}.}
\]

这是全部289行的多项式身份，未先代入近似色散。沿原完整根，最后项归零，真正得到
H289 X0=I0。实际 I0 是原两极点的源投影；不会变成完整负 g00 注入。
冻结 Causal／JointMomentumJet 的非轴 X0、I0 及共同分母，在本公式 k=−kin 处全行同值。

此外实际时间系数满足 H2A=H2B=0、H1A=Z、H0A+H1B=0，故真实 retarded kernel 为

\[
K_\theta(t,k)=\frac{A_g\cosh(c\sqrt U\,t)
 +B_g\sinh(c\sqrt U\,t)/(c\sqrt U)}D\quad(t\ge0),
\]

负时间取零。sinh 商在 U=0 取 t，两整个函数的幂级数无奇性。
Kθ(0)=A/D、∂tKθ(0)=B/D，分布方程恰为 H(∂t,−ik)Kθ=(Z/D)δ0。
H2Kθ 恒零，未要求强迫 current 有二阶时间导数。
Re λ>c√U 时真实半轴 Laplace 积分就是上述 X0；整个原轻球在 Re λ≥5 内共同成立。

原点直接给 B_g(0)=0、D(0)=1，因而 X0(λ,0)=A_g(0)/λ、I0(0)=Z_g(0)。
A_g(0) 有8个原物质分量，Z_g(0) 有11个原 coframe／物质源分量；它们由原轴向表读取，
不是另装的延拓值。

## 同一完整隐根的物理一、二阶导数

原规范化方程精确满足
Fhat(Tr,T)=c_F T[r−125/162+TP(r,T)]。在原轻球
|k|≤√2·(5234375/294988800512)，原发生唯一且 D∈[39/40,41/40]。
多项式隐函数定理及已生成唯一性给含原点、闭球附近的同一解析 U(T)。

\[
U'=-F_T/F_U,\qquad
U''=-\frac{F_{TT}+2F_{UT}U'+F_{UU}(U')^2}{F_U}.
\]

原点的确切值为 U′(0)=125/162、U″(0)=−76325/78732。

对任一显式函数 g(k,U,T)，真实物理导数是

\[
\partial_i g=g_i+k_i(g_T+U'g_U),
\]
\[
\partial_{ij}g=g_{ij}+\delta_{ij}(g_T+U'g_U)
+k_i(g_{jT}+U'g_{jU})+k_j(g_{iT}+U'g_{iU})
+k_ik_j(g_{TT}+2U'g_{UT}+(U')^2g_{UU}+U''g_U).
\]

jets.evaluate_jet 直接用这些公式生成 X0、I0 的289维值／梯度／Hessian；U′、U″保持
为 a/D、b/D³ 的实际共同分母，不把完整 F 商环中的巨大逆展开成无用系数。
输出向量是明确分母下的分子，匹配的 denominators 按0／1／2阶给出。
原点和新非轴 k=√2ρ(2,−3,6)/7、ρ=1/131072、物理 λ=c(7−2i) 都回写全部289行及
其3个一阶、6个二阶方程。完整 F 上的反控排除把 U′换成125/162或删除 U″。

这些解析导数来自同一个函数和完整源根；没有把几个有限 jet 当成函数存在凭证。
在任意远离实际两极点的紧 λ 域上它们均一致有界。因果核对 U 的整个幂级数同样给出
物理 k 导数，其多项式时间因子乘共同指数界可被 Re λ≥5 支配，故可交换真实积分。

## 原固定世界 section 的额外读回

原 removed9=[21,27,39,58,59,60,63,64,68]，A_global 的9行恒零，B_global 的
21/27/39、63/64/68 六行真实非零；各组三行分别是同一径向系数乘 kxky、kxkz、kykz。
两系数在 q=1/131072 与完整 F 互素，不能把轴上的零误当全世界坐标零。

原 K0 的世界 minor 也不恒定，恰有

\[
\det K_{removed}=3\sqrt2(25p_1^2+18)/1000
 =3\sqrt2(18-25k_x^2)/1000.
\]

它在整个原轻球非零；section.py 只保存这一实际读回，没有另造 replacement section。

## 运行与身份

依次运行 source.py、equations.py、jets.py、section.py，使用离线 SymPy 1.14.0。
四组原源计算、回执及日志由 construction.json 绑定。所有内容只写本包，未改上游或权限。
这是精确源程序加上述解析机制，没有新增 Lean 声明，也不自行完成独立认证。
窗口和量子 current 卷积继续消费原各自 producer；本包保持实际两极点投影与共转场坐标。
