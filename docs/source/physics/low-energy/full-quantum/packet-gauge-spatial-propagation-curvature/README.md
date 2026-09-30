# 原两传播腿的整轻球积分与完整五项响应

同一 S01/dx1 外源与 reader、`p_out=0`、`z=w=6c(1−i)`、原准备 ψ/P、原球窗和
观察半径 R=B 下，两条 G 传播腿的实际 q² 系数已完成整个轻球的严格积分包围。
与已签收的两 source 腿及 reader 接触相加，完整五项的 raw 对角区间为：

| 物理方向 | 完整五项 q² 系数，单位10⁻²⁰ |
|---|---:|
| e1 | [−1.355200, −1.309214] |
| e2 | [2.140271, 2.186257] |
| e3 | [−1.742600, −1.696614] |

完整 real 对称二次系数矩阵的 raw 与 connected 都有两负一正惯性；矩阵误差界也控制
全部 mixed 项。mean 独立保留，其 e2 区间跨零，没有用 connected 替代 raw。
`complete.json` 保存各 sector 的完整严格有理区间及任意单位方向规则。

尖窗的真实 |q| 项保持。两传播腿 raw 的该系数对全部单位方向落在
`[−7.470844,−7.370030]×10⁻¹⁸`。因此本包给的是保留尖窗项之后的 q² 系数，
不将整个响应称为 q=0 的 Hessian。

原 `positiveSmoothUnifiedSource`、修复 Dirac-dual、SpinPair.actual、visit10/tick16→17
及其 controller 保持。这是同一 root 下原空间一次插入的从属 producer。289物质坐标仍为
已签收的 FullPhase 共转表示，物理时间不变；原 gauge current 的相位读回继续消费原接口。
这里没有另选真空、重准备、加入实验单位或重复加入 matter Schur。

## 固定入射变量的实际两腿

原场采用负空间相位。设 y 为入射物理动量、d 为外场动量，输出是 y−d。定义

\[
\mathscr R(y,d)=
 F_z(y-d)^\dagger Q_{\rm native}(y-d)
 G_{z,d}(y-d;y)\,
 \langle B_{y-d}(z)\psi,B_y(z)\psi\rangle.
\]

G 的 theta 根、准备源和公共分母属于 y。`source.py` 在全部六个空间变量上，从原作用
生成 V、真实 Bg 变化、背景 Euler、K1、C1 和 Q；两侧九列 Ward 及全部12规范方向同时通过。
Noether 补源先于场解生成。原 χ 的 formal transpose 与独立动量号保留，未换成 bra。

同频原 native Q 的 Hermitian 身份和真正变量平移，将左传播腿认回右腿的共轭。
原 native quadratic 的1/2和 cos 两支的1/2因此给

\[
 I_G(d)=\frac12\sum_{\sigma=\pm1}\operatorname{Re}
 \int_{|y|\le B,\ |y-\sigma d|\le B}
 \mathscr R(y,\sigma d)\frac{d^3y}{(2\pi)^3}.
\]

`B=sqrt2*5234375/294988800512`。两窗、两传播腿及两个半幅均计入一次。
量子 B 是实际全时间半轴积分，使用 ProbeMoments 的全部复 raw/mean/connected 矩；
没有用 t=0 的旧 Hessian 除以 |z|²替代。

## 原实际 frame、全九方向与全半径核

`native-covariance.py` 对原九个空间 SU2 方向、三个真实生成元，以及两个独立四动量的
全部系数验证完整 native current 的 Lie 恒等式。原 Bg 本构图、scalar 和 independent dual
都在原矩阵中。实际 circle ODE、逆 profile 的全部系数将它接成有限旋转身份。
Cartan 方向准确为原6−7，九方向的规范化没有改写。

对同一原 paired frame，`L=Lz(tz)Ly(ty)`，空间矩阵 `R=Ry(ty)Rz(tz)`，实际有

\[
 L^{-1}(dx^1S01)=a(v),\qquad a(v)_{ij}=v_iv_j,\quad v=Re_1.
\]

外方向进入轴向坐标为 m=Rn。这是原有限作用对同一外源的读回，未用二次 Hessian 旋转
代付三次 current。详述与反控制见 `native-covariance.md`。

`axis.py` 由原源生成9×9 reader/source张量以及真实 radial/external 的全部15个二阶 jet；
每个方向的289方程、原Noether先源和全部辅助回写通过。沿一个固定原 frame，输入物理轴向
坐标为 r；其原根 U=(r²/2)Rθ(r²/2)。`kernel.py` 继续生成未截断 r、U 的实际多项式
force、源补偿与三个辅助回写。原 I0 的 gravity_B 投影源保留；扰动的额外 particular
只在72个 gauge_B 坐标非零，另外96个 auxiliary particular 精确为零。

核的计算中使用 q=r/sqrt2，外 e=d/sqrt2。当前符号为 `p3=−i sqrt2 q`。
`radial_inverse.py` 读取旧正号表并生成全部112的真正全q有理双逆；当前消费者明确使用
`P_current(q)=P_old(−q)`。`consumer.py` 逐项支付该全族身份和奇阶导数负号，继而在
新非零 q=1/262144 上，核对全部9×10×289原方程、原六次 Fhat、同一分母和相同 removed9。
唯一径向逆表为确定压缩的 `radial-inverse.json.gz`，解压摘要见 `radial-compression.json`。

`origin.py` 的第二个 constant native frame 是其固定射线族在 r=0 的解析延拓；
它不被称为 canonical k=0。两个 frame 的7项低阶 scalar jet 确实不同。
实际积分在 r>0 使用原 paired frame，正负 r 共用同一 frame；零点不贡献测度。
正式 `PacketField.PositiveRay` 与 `Reflection` 支付这一原定义身份。

## 真正的径向球窗系数

取 d=sn、|n|=1、s↓0，u=n·ν。直接沿固定角 ν 作径向 cap 展开，得到

\[
\begin{aligned}
 I_2(n)={}&\frac12\int_B\operatorname{Re}\mathscr R_{dd}
 +\frac12\int_{\partial B}u\operatorname{Re}\mathscr R_d\\
 &+\frac14\int_{\partial B}
 \left[u^2\partial_{\rm radius}\operatorname{Re}\mathscr R_0
 +\frac{3u^2-1}{B}\operatorname{Re}\mathscr R_0\right].
\end{aligned}
\]

体与两项表面测度均带原 `(2pi)⁻³`。同一输入角上的 frame 径向固定，因此这里不要求
对 canonical frame 作角导数，也不要求 G 自身跨 seam 光滑。径向球弦消费者见
`../packet-gauge-radial-window/`；实际均匀径向导数由本包源核给出。

`angular.py` 实际使用 paired frame 的北半球×2，r的正负号始终保持。
R 的角多项式按真实球面 Beta 积分逐项积分，没有假设噪声径向或保留某个旋转平均。
原完整 Gram 左／右／mixed 二阶矩全部进入后，虚部与 mixed 矩才在实际角积分中相消。
删掉两项 flux 会改变真实 leading 系数。两传播腿二次部分的 raw 三个中心值分别为
`(−1.3031969814, 2.1922740186, −1.6905967190)×10⁻²⁰`。

## 同一源解先发生，再取严格范数

直接对每个矩阵因子取绝对值会丢失本案的实际相消。本包没有把这种松估计当作结果。

`inverse_series.py` 从原 A0 双逆和全部三维多项式系数生成40阶矩阵 series。
256位 dyadic rectangle 运算均向外舍入；复乘法保留实虚交叉及全部有序矩阵乘积。
原实际 Neumann 估计在 q 圈 `1/8192` 给出真实逆，Cauchy 支付未存储系数的尾。
所有矩阵系数均来自原 H，而非调用方提供的 bound 或 regular 证书。

`solution_series.py` 再把同一原 force 与逆真正作用，之后才取范数。原隐式源满足
`Fbar(T*r,T)=T*(r−125/162+T*P(r,T))`。在上述复q圈内，程序生成
`R² sup|P|<1/20` 与 `R² sup|P_r|<1`。原固定点迭代因此生成该复邻域的唯一
holomorphic 分支；实侧由已付唯一性认回原 U。其原 F_U(0,0)=1又逐项生成真实 Taylor
系数，不输入目标根或所需导数。

令 normalized 解为 Y。对 source 的真实 δ-jet，精确递推为

\[
 Y_{n,\alpha}=P_0 f_{n,\alpha}
 -\sum_{(j,\beta)\ne(0,0)}
 {\alpha\choose\beta}P_0 A_{j,\beta}Y_{n-j,\alpha-\beta}.
\]

有限36阶运算包围这同一个解析解的系数；原圈上的 force、Noether 与逆界再付真实尾项。
例如对每个原 unit profile，normalized Y 的向量 ℓ∞ 轴向0至4阶界约为
`(0.001669,0.190606,0.074193,0.141750,0.357796)`。
所有真实系数和尾界见 `solution-series.json`。这保留了原源的矩阵相消。
实际 dyad 的九个系数的 ℓ1 范数≤3；reader与source的这两个因子均在末端统一界计入。

`uniform.py` 先生成原 effective reader 行 `F†Q E D` 和真实 Bg particular，再与这些
source 解导数相乘。q坐标到物理r/d的每阶 `2^(−order/2)` 在末端付清。
量子端消费已独签 FourthProbe 的真实全时间 C4界；全方向混合矩来自同一向量的 Hölder。
同一固定 P、I−P 只是最后对完整 source 向量作用，raw／mean／connected从未重新准备。

## 整球有效余项与五项总消费者

正负r沿同一个原 paired frame成对，body 的一次径向项、first-flux的二次项和
zeroth-flux的三次项在整球中严格相消。它不需要另加 parity 假设。
若同一真实核的物理 mixed 四阶界为 M22、M31、M40，实际误差为

\[
 |I_2-I_{2,\mathrm{quadratic}}|\le
 \frac{B^5}{\pi^2}\left[
 \frac{M22}{40}+\frac{M31}{48}
 +\frac{1+1/\sqrt3}{144}M40\right].
\]

这里的常数来自真实 `∫|u|`、`∫u²` 和 `∫|3u²−1|`，没有省略一个 cap。
`remainder.py` 逐项消费 source、完整复两probe Gram和原半轴位置矩，得到全方向误差

| sector | 两传播腿 q² 统一误差 |
|---|---:|
| raw | ≤2.070265023×10⁻²² |
| mean | ≤1.336529936×10⁻²⁴ |
| connected | ≤2.052969554×10⁻²² |

`combine.py` 将它们与已独签 ProjectedSourceReader 的同 sector 三项相加，得到开头的
完整五项区间。raw=mean+connected是原完整配对的恒等式；区间分别向外包围。
mixed 数值按 `nᵀTn` 中的 Tij保存，交叉单项式仍为2Tij ni nj。

本包完整保留G的λ多项式部分及其原 P1δ′/P0δ身份，未只取 proper 部分。
零过去解释继续消费同一 UniformSpatialContact、原 current 时间导数和共同阻尼域；
这里的新闭合是该完整频域五项的实际空间积分，不从一个逆矩阵另行推断因果性。
这是指定原准备与带宽下的诱导响应；没有将它改名为 vacuum loop、kinetic beta 或全部
homogeneous/cross场。

## 验证入口

离线 SymPy1.14.0／python-flint0.8.0。依次运行
`source.py → origin.py → axis.py → native-covariance.py → radial_inverse.py → kernel.py →
inverse_series.py → solution_series.py → uniform.py → angular.py → remainder.py → combine.py → consumer.py`。
原源数据、直接消费者、精确区间与日志由 `construction.json` 绑定，实际时间见
`focused.json`。新 Lean 声明为0；证据为原源码生成的精确有限代数、严格有理包围和上述解析
消费者，独立认证另行进行。
