# 整入射轻球上的真实接触与因果传播

本包将原联合空间插入接到整个入射轻球。每个入射点使用它自己的原canonical frame，
在外动量变化时保持该frame固定。源生共同复域、完整频率次数和真实时间界共同生成

\[
\mathcal G_{k,d}=P_1(k,d)\delta'_0+P_0(k,d)\delta_0
                 +\mathbf1_{t\ge0}K_{k,d}(t).
\]

这是原source、修复Dirac-dual作用、SpinPair.actual、visit10/tick16→17的从属producer；
source、whole-ledger与controller保持。全部字段、Noether补源、原时钟和同一准备态进入
构造。它提供两条空间传播项的整球弱时间消费者，入射拼接处的电流trace由其源包支付。

## 原source族与完整回写

在固定入射frame中取

\[
p_{in}=(cx,0,0,i\sqrt2\rho),\qquad
p_{out}=(cx,i\kappa_1,i\kappa_2,i\kappa_3),
\qquad |\rho|\le\epsilon.
\]

ρ保留符号，包含canonical反射后的两个轴向方向。原全球theta给
`X0=(cx A+B)/[c² D(U,ρ²)(x²−U)]`，U保持同一完整Fhat的轻根。
forcing.py在独立ρ、U、κ、x上运算，不用截断色散或有限方向拟合。

原`a=dx1 S01`经入射frame的逆作用，落在实际九维空间规范方向：
`dx_i⊗{g1,g0,g6−g7}`，i=1,2,3。三个原圈的全部有限系数验证该span保持。
对每个方向，直接用原曲率与Hodge生成`b=−star F1(a)/σ`，再从原primitive顶点与72个
真实auxiliary reader生成V(a,b)。没有将Bg冻结。

covariance.py对六个独立空间动量、变量x和所有九方向验证三个原生成元恒等

\[
J^TV_a+V_aJ+\partial_{R^Tp}V_a+V_{Ja}=0,
\qquad \partial_{R^Tp}b_a+b_{Ja}=Jb_a.
\]

原有限圈ODE及初值将其识别为真实有限作用。因此上述轴向多profile表示确实消费原世界
插入。V的实际x系数恒为零，这一项也逐条检查。

ward.py独立用真实field action和`E1=H(p_external)(a,b)`生成K1、C1；全部九方向
在六个独立空间动量上同时满足两侧九列Ward及全部12规范方向的Ward。原Noether源为

\[
(I_1)_{removed}=M_-^{-T}[-K_1^TI_0-C_1^TX_0],\qquad
(I_1)_{retained280}=0,
\]

其中M_-是原K0(−pout)的removed9 minor。这个源先于待求场。共同域内M_-可逆；
I1乘共同theta分母后，频率次数最多为2。

retained280源为零，使I1不进入真实112 forcing或168辅助particular。forcing.py仍将
全部72＋72＋24辅助逐块消元、回写，保留九个scalar。原同一个torque图及两侧恒等随后给

\[
X_1=\frac{1}{c^2D(x^2-U)}
 \left[\frac{\mathrm{part}}{\Delta^2}
       +\mathrm{lift}_{103}\,Q_{103}^{-1}\mathrm{force}_{103}\right].
\]

这里part含scalar图与全部辅助particular，lift含全部辅助场，Δ是原removed9 minor。
三个量都由原源程序生成。原保留行方程成立后，Ward使最后九行残差与K0(−pout)配对为零；
同一M_-的可逆性遂给全部289行原方程。

## 全参数的次数证明

grading.py在所有三维κ上生成原scalar torque图。它的完整112剪切矩阵det=1；
scalar块是原非零常矩阵。已签FixedSectionDomain因而给Q103真正的频率次数126，
最高次系数在共同域内一致非零。它依赖κ，未声称最高次系数是常数。

对Q103各条目的真实x次数，程序生成一个完整匹配及行／列权重。所有条目次数都不超过
相应两权重之和，匹配权重总和为126，故最高可能次数恰与真实det次数相同。

每个inverse[j,i]的余子式由匹配的交替路径控制。删除row i、column j后的任一排列，
由一条对应路径与若干循环组成；权重最优性排除正循环。因此有限最长路径给全部103²
余子式的真实次数上界，除去126次det后直接成为inverse条目的次数界。
程序验证完整匹配、dual权重、无正循环及全部路径，保存每个条目的上界。

将真正force103的逐行次数代入后，所有九个profile均得到

- 9个动态分量O(x⁻¹)；
- 54个分量O(x⁻²)；
- 40个分量恒为零。

全部scalar／168回写后，八个profile的完整289上界为O(x)，另一个为O(1)。
这是独立ρ、U和三维κ的多项式支持证明，不靠原点jet或若干频率样本。
于是同一原有理族的多项式部分最高λ一次；其余部分严格proper。

## 原共同域与源生统一界

FixedSectionDomain已签：所有原入射轻动量，固定原incoming frame，
外d满足`max|d_i|≤r=1/200000`时，共用原物理围道`|λ|=Γ=5c<5`，det次数恒126。
κ与d由该实际实正交frame联系，输入U和D始终来自原同一θ根。

bounds.py逐项对真实source多项式、scalar图、所有profile与完整lift取有理绝对值界。
它以源生det下界及103维cofactor给Q103的界，再除去实际Δ²与theta分母，最后同时支付
实际frame和逆frame，得到记录在bounds.json的有限常数C：

\[
\sup_{k,d,|\lambda|=\Gamma}\|X_1(k,d,\lambda)\|_\infty\le C.
\]

九个profile按矩阵行和一起计入；两次frame界分别支付原外场分解与完整世界字段回写。
这里是289列的分量最大范数，转Euclidean范数另乘17。

同一围道直接生成完整多项式接触和普通核：

\[
P_1=\frac1{2\pi i}\oint\frac{X_1(\lambda)}{\lambda^2}\,d\lambda,
\quad P_0=\frac1{2\pi i}\oint\frac{X_1(\lambda)}{\lambda}\,d\lambda,
\quad K(t)=\frac1{2\pi i}\oint e^{\lambda t}X_1(\lambda)\,d\lambda.
\]

围道内的原有限极点、频率恒次数及上述proper分解保证这些确为原∞ Laurent系数和
真正retarded核。原物理时钟给4<Γ<75/16，故

\[
\|P_1\|_\infty\le C/4,\quad\|P_0\|_\infty\le C,\quad
\|\partial_t^mK(t)\|_\infty\le5^{m+1}C e^{75t/16}.
\]

固定incoming后，外d的holomorphic性及同一复域给多指标导数界
`α! C/r^|α|`；在半径r/2的内部小域取相应Cauchy半径r/2。
这些界对整个入射轻球统一，原frame只需已有的Borel性和有限范数。

V没有频率一次项，X0严格proper，而I1∞由上述先在源直接读出。因此原完整场方程的
高频系数给全部参数上的四条真实初始身份：

\[
H_2P_1=0,\quad H_2P_0+H_1P_1=0,
\]
\[
H_2K(0)+H_1P_0+H_0P_1=0,\quad
H_2K'(0)+H_1K(0)+H_0P_0=I_1(\infty).
\]

它们分别支付零过去场方程的δ三阶、二阶、一阶和零阶。

## 真正时间域和空间积分消费者

在这个外动量域内，两current探针的物理模长均小于1/20000。原TimeJet和Green能量界
给同一raw、固定中心化或mean分量的全时间界`||J||≤8`、`||J′||≤22/20000`。
没有换准备态或增加H²域条件。

实际响应是

\[
\mathcal G*J_+=P_1\delta_0J(0)
 +\mathbf1_+[P_1J'+P_0J+K*J].
\]

普通部分的分量范数不超过`C(8+22/80000+40t)e^(75t/16)`，初始δ系数不超过2C。
正阻尼Re z≥5支付完整半轴积分与Fubini；其精确积分常数写入bounds.json。
普通J′的Laplace为`z Jhat−J(0)`，与保留的δ项合并才成为原`X1(z)Jhat(z)`。

两条native current场腿使用两个独立时间变量。原first-jet reader按分布分部积分，
因此所有瞬时项都进入同一个真实bilocal读数。没有在同一时间任意相乘分布。
空间积分可先重排为固定incoming：扰动腿是`G(k,d)J(k)`，外d微分只落在G上。
因此P1/P0/普通核的统一导数界和同一个J／J′直接给普通部分的强参数C²；初始δ部分
按同样系数微分。另一条未扰动腿中的移动probe由原ProbeLaplace的一／二阶强导数及
全时间矩界支付。更一般的写法中，时间分布微分也与实空间参数微分交换；两种读法均不
要求J′的强混合H²域。

入射动量球体内的外d微分，由上述统一界和原probe位置矩支配。原物理球窗／shell及
canonical拼接继续由SpatialCurrent和CurrentSeam的真实积分口消费；这里不从Borel
选择反推全G跨缝平滑。它提供完整五项响应中两条传播腿的真实时间及外参数基础。

## 实际完整消费者与重放

consumer.py选用新ρ=1/262144、原圈参数1/7与−2/5、物理λ=c(7−2i)，
取非共线出射轴坐标`√2ρ(1/3,−1/4,7/6)`。它直接从原S01场生成九个profile系数，
检查真实103双逆、世界vertex圈作用，再分别在轴向和世界坐标先生成Noether补源，
核对全部289方程与源variance。实际g00分子在完整Fhat上非零。

重放顺序：grading.py、forcing.py、covariance.py、ward.py、bounds.py、consumer.py。
使用SymPy 1.14.0／官方python-flint 0.8.0精确后端。无新Lean声明、公理或浮点判零。
forcing.json.gz是确定压缩的原数学多项式表，保留实际分子而非只存次数标签。
