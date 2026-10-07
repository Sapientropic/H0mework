# 补充材料：完整证明

**《这浩瀚宇宙里，我们没找到魔法：Spin×SU(7) 理论的同源生成与经典—量子对应》**

**作者：高健（Jian Gao）**

本补充给出正文定理 6.7–6.14、命题 9.1–9.3 及 §6.9 末、§9.2 相关结果的完整书面证明与核验说明。正文已陈述结果并给出证明思路；这里逐条交代对象与定义域、实际输入与量词、构造、关键引理、决定性推导，以及同一对象在后续结果中的直接使用，最后对应到形式声明或冻结回执。记号与正文相同，定义、定理与公式编号均指正文；正文 §2–§5、§6.1–§6.6、§7、§8 的证明已在正文与附录 A–C 中给出，不在这里重复。

每节末的“形式对应”列出承载该结果的 Lean 声明或冻结回执；所在源提交、完整路径与回执身份见正文附录 D.7–D.8，公开复现入口见正文“代码与数据可得性”。固定提交别名 AB、AC、AD、AE、CAP、H、F 的定义见附录 D.1 与 D.7–D.8；本补充对固定源文件只做核读，未重新构建、编译或运行任何程序。

证据身份分五类，逐条标注：**形式定理**（Lean 内核验证的声明）、**有限精确计算**（在证明核中逐项判定的有限恒等式，如实报告所用判定手段）、**固定精确源程序及其独立重算**（固定提交中的精确计算程序，各配同一提交下独立实现的重算）、**双实现数值核验**（两套独立实现各自产生的冻结回执及其容差）、**统计合同**（带预先登记错误率的随时检验）。物理解释与硬件身份不在任何一类中扩展。

---

## S0 共同记号与工具

以下对象在后文反复出现，先统一定义。

**S0.1 配置与测试空间。**固定源与原作用 (3.1)。$\mathscr U_{103}=\mathscr U_q\times\mathscr U_x\times\mathbb R^{36}$ 是共同非特征开域（$v_e>0$、$\det h\ne0$、$g_{00}\ne0$、$h^{00}\ne0$、$\det D_9\ne0$ 及四阶时间—电块 $\det\mathscr M\ne0$ 的含源连通分支），$\mathscr U_{100}$ 是三稳定子截面（S1）。$\mathcal I=\{+,-\}\times\{0,1,2,3\}\times(\Lambda^6\sqcup\Lambda^2\sqcup\Lambda^4)$ 是 504 个 CAR 模式指标，$\mathcal F_{504}=\Lambda^*\mathbb C^{504}$。配置 Hilbert 空间 $\mathscr H$ 由 (S1.4) 的加权 $L^2$ 直和给出；量子测试空间 $\mathcal Q=C_c^\infty(\mathscr U_{100};\mathcal F_{504})$ 在其中稠密。

**S0.2 截断压缩与保留项。**对截断指标 $F$（Gauss 酉历史的有限指标），$C_F(p)$ 表示完整原生 Hamiltonian $H_0$ 在动量 $p$ 处对 $F$ 的自伴压缩，$A_F$ 为未截 Yukawa 的保留项，$K_F(p)=C_F(p)+A_F$ 为实际生成元。$C_F$ 保持 $\Lambda^6$ 占据分级，$A_F$ 升一级（S1.3）。$T_p(t)=e^{-itK_F(p)}$，$R_p(z)=(K_F(p)-z)^{-1}$（$z$ 非实）。截断指标按包含定向；“对共尾的 $F$ 成立”表示沿源滤子在某个终段以外的全部 $F$ 上成立。

**S0.3 响应点与五因子核。**一个**响应点** $q$ 携带：截断指标 $F$、左/右物质动量 $p_L,p_R$、两个非实频谱参数 $z,w$（$\operatorname{Im}z\ne0$、$\operatorname{Im}w\ne0$）、准备精度 $\varepsilon>0$、有限窗 $T$ 及源场曲线。电流读口 $J$ 是母作用一阶变分的量子化。五因子核为
$$\mathcal K_q(t)=T_{p_R}(-t)\,R_{p_R}(z)\,J\,R_{p_L}(w)\,T_{p_L}(t).\tag{S0.1}$$
$\mathbb C^{289}$ 是九组场的实方向空间，$H_{289}(p)$ 是四个复动量 $p$ 处的 Jacobi 矩阵（S5）。

**S0.4 预解式与 Duhamel 工具。**自伴算子 $A$ 的预解式满足 $\|(A-z)^{-1}\|\le|\operatorname{Im}z|^{-1}$（$z$ 非实），以及预解式差公式 $R_p-R_k=R_p(C_F(k)-C_F(p))R_k$。酉群的 Duhamel 公式 $e^{-itB}-e^{-itA}=-i\int_0^te^{-i(t-s)B}(B-A)e^{-isA}ds$ 在算子范数拓扑中使用。Bochner 积分 $\int_0^\infty e^{-\lambda t}\Phi_t\,dt$ 对一致有界强连续算子半群在 $\operatorname{Re}\lambda>0$ 时收敛；对 $\Phi_t(X)=T_{p+k}(-t)XT_p(t)$ 型的双腿作用逐分量定义。

**S0.5 有限精确恒等式的核查方式。**本文多处证明归结为有限条在证明核中逐项判定的恒等式：如 $H_{289}$ 的 3071 项字典（系数在 $\mathbb Q(\sqrt2,\sqrt{15})$）、576 个多项式条目的矩阵乘积、289 维矩阵的显式逆。这些等式的判定手段在各节“决定性推导”处如实写明，实际使用的有三类：项表与字典的逐条相等由 `decide +kernel` 判定（证明核把两边归约到同一典范形式）；系数域 $\mathbb Q(\sqrt2,\sqrt{15})$ 中的标量等式由 `ring`、`norm_num`、`field_simp`、`linear_combination`、`nlinarith` 逐条判定；有限维矩阵等式在逐指标展开后由 `decide +kernel`、`fin_cases` 结合上述标量判定完成。这类判定的结论是定理而非数值拟合。

**S0.6 数据型声明的核查方式。**命题 9.1–9.3 中标注“双实现核验”或“统计合同”的款项，其数值结论由两套互不共享前向计算的程序（主实现与独立实现）各自产生冻结首回执后交叉核对；判据文件在执行前冻结，统计合同预先登记总错误预算（如联合 $\alpha=1/20$）。回执身份逐项列在 S9 与附录 D.8。

---

## S1 定理 6.7：共同量子 Hamiltonian

**对象与定义域。**固定源与满足正文 §4 非特征条件的原作用 (3.1)：$v_e>0$、$\det h\ne0$、$g_{00}\ne0$、$h^{00}\ne0$、$\det D_9\ne0$、$\det\mathscr M\ne0$（见 S0.1 与正文 (3.2)–(3.6)、(4.1)–(4.6)）。物质配置为完整 252 维 Dirac×色符号 $\psi$ 与独立对偶 $\chi$。

**输入与量词。**全部结论对任意满足非特征条件的源邻域成立；“61”“504”“103”“100”“392” 是源生成的固定维数，非可调参数。第 3 款的恒等式对每个四元复动量 $p$ 成立。

**构造。**分四步：正则一形式与 CCR/CAR；共同域上的四能量；三稳定子截面与测度；作用认回。

**(1) 正则载体。**

*Legendre 图。*空间 Gram $h=e_{\rm sp}^{\mathsf T}\eta e_{\rm sp}$ 给 coframe 六速度图
$$\Pi_e=M_e\dot e+b_e,\qquad Z^{\mathsf T}(\Pi_e-b_e)=0,\qquad \dot e=Q_e(\Pi_e-b_e)+Z\lambda,\tag{S1.1}$$
其中 $M_e=D_h^{\mathsf T}B_hD_h$（$B_h=(4v_e)^{-1}\operatorname{Hess}_h\det h$），$\det h\ne0$ 时秩六，$Q_e=R_hB_h^{-1}R_h^{\mathsf T}$ 由显式右逆生成而不是任意伪逆；十条主约束由 $Z$ 的十列（四时间列加六 Lorentz 列）给出。标量图要求 $h^{00}\ne0$：$\Pi_\phi=h^{00}(\dot\phi+\rho^{70}_{A_0}\phi)+b_\phi$。规范图要求 $g_{00}\ne0$：$K_E^{-1}=-\tfrac{\sigma v_e}{g_{00}}(g^{-1})_{\rm sp}$，十二个时间分量动量为零。物质对偶 $p=-i\chi E$ 由 $E=v_e(e^{-1})^0{}_a i\gamma^a\otimes I_{63}$ 给出；$\chi$ 不预先识别为 $\psi^\dagger$。共同正则一形式为
$$\Theta=\Pi_e\cdot\delta e+\Pi_\phi\cdot\delta\phi+\sum_i\Pi_A^i\cdot\delta A_i+\operatorname{Re}(ip\,\delta\psi),\tag{S1.2}$$
能量为 $H_{\rm cl}=H_e+H_\phi+H_{\rm g}+H_{\psi,{\rm rem}}$，共同十二维 Gauss 为 $\mathcal G=\mathcal G_A+\Pi_\phi^{\mathsf T}\rho^{70}\phi+\operatorname{Re}(ip\,\rho^{252}\psi)$。

*61 对 CCR。*取 $\ker O^{\mathsf T}$ 的固定实基 $R\in\mathbb R^{70\times61}$（$O=(O_1,\dots,O_{12})$ 为原规范—标量轨道矩阵，$\operatorname{rank}O=9$，$D_9=O_b^{\mathsf T}O_b$ 在源点等于 $256$），在标量约束图上写 $\phi=v+Rx$、$\Pi_\phi=R^\vee\pi+O_b\zeta$（$R^\vee=R(R^{\mathsf T}R)^{-1}$，$\zeta$ 由九个非稳定 Gauss 的余项经 $D_9^{-\mathsf T}$ 生成）。因 $O_b^{\mathsf T}R=0$，$\Theta$ 在该图上精确拉回为 $\pi\cdot\delta x$，得 61 对 CCR $[x_j,-i\partial_{x_k}]=i\delta_{jk}$。

*504 模双支 CAR。*物质一形式 $\operatorname{Re}(ip\,\delta\psi)$ 的实正则坐标为 $(\operatorname{Re}\psi,\operatorname{Im}\psi)$，动量为 $(-\operatorname{Im}p,-\operatorname{Re}p)$。两个独立实支复化后，模式指标为 $\mathcal I$（S0.1），$|\mathcal I|=504$，产生/湮灭算符满足标准 CAR（正文 (5.2)）。双支规范流矩阵为 $Q_a=\operatorname{diag}(i\rho_a^{252},i\overline{\rho_a^{252}})$；物质 Hamiltonian 矩阵 $M$ 的双支实现为 $\operatorname{diag}(M,-\overline M)$。这是一次对 504 维整体的 CAR 量子化，不是把 $\psi$ 与 $\chi$ 各自量子化后再配对。

*四能量共同域。*把 coframe 六速度写成正交动量 $\kappa_r=-i\partial_{q_r}$ 与 Lorentz 流的组合（下三角空间参数化 $L(q)$，$v=\det L$），四项能量在
$$\mathscr D_{103}=C_c^\infty(\mathscr U_{103};\mathbb C)\otimes\mathcal F_{504}\tag{S1.3}$$
上实际相加，任一有限有序复合保持该域。各系数由已给非退化矩阵的逆与有限次微分生成，在 $\mathscr U_{103}$ 上光滑；交叉主部在原系数上有 944 个非零条目，61 个原 Yukawa 力方向保留。注意 $103=6+61+36$（coframe、标量切向、规范连接），是配置维数而非传播商维数。

**(2) 截面、测度与共同 Hamiltonian。**

*三稳定子。*令 $S\in\mathbb R^{12\times3}$ 张成 $\ker O$。用原 Gram $G$ 定义 $B=E_b-S(S^{\mathsf T}GS)^{-1}S^{\mathsf T}GE_b$，则 $[B,S]$ 是规范代数完整基，三稳定子满足 $[S_a,S_b]=-2\epsilon_{abc}S_c$；原作用另给 $[S_a,B]=BC_a$、$\rho_{S_a}O_b=O_bC_a$、$\rho_{S_a}R=RT_a$ 与 $C_a^{\mathsf T}D_9+D_9C_a=0$。

> **引理 S1.1（三稳定子与共同作用对易）。** 三稳定子在 $\mathscr D_{103}$ 上生成的 $\widehat G_a$ 满足 $[\widehat G_a,\widehat H]=0$，共同核非零并对四项能量的任意有限有序复合不变。

*证明。* 由上述协变律，$V_aD_9=-C_a^{\mathsf T}D_9-D_9C_a$，故 $V_aF=C_aF+FC_a^{\mathsf T}$（$F=D_9^{-\mathsf T}$）；代入动量平方的有序展开，法向系数与流矩阵的变化逐槽相消，不需交换内层动量。规范部分用原 Gram 不变性与 Lie 导子律；coframe 部分 spin 矩阵与外幂规范作用通约。非零性由保持三稳定子的占据向量（如 $|(7,259)\rangle$）乘紧支撑函数给出；带荷单模式给出非零作用，故共同核是 Fock 纤维的真子空间。∎

*量子截面。*量子配置为 103 维 boson 部分（物质已由 CAR 纤维实现）。用与经典约化相同的三个规范枢轴：指定源处轨道矩阵 $M=I_p^{\mathsf T}V$ 满足 $\det M_*=-54\sqrt2/125\ne0$。局部轨道图 $\Phi(\alpha,z)=\exp(\sum_a\alpha_aL_a)(z_{\rm base}+I_fz)$ 在源点导数可逆，逆函数定理给非空局部开图。延拓 $\mathcal E$ 与限制 $\mathcal R$ 满足 $\mathcal R\mathcal E=I$、$\widehat G_a\mathcal Ef=0$；约化算子 $H_{100}=\mathcal R\widehat H\mathcal E$ 保持每个有限次组成（由引理 S1.1 的 $\widehat H\mathcal E=\mathcal EH_{100}$）。

*测度相消与半密度。*轨道 Jacobian 给截面权重 $\rho_3(z)=8a_1^2a_{12}>0$（源点值 $54\sqrt2/125$）。九个非稳定标量条件是第二类约束：固定基体积、法向动量积分与第二类行列式三因子乘积为
$$\frac1{256}\cdot\frac{256}{|\det D_9|}\cdot|\det D_9|=1,\tag{S1.4}$$
故量子截面的实际测度是 $\rho_3$ 而非再乘 $|\det D_9|$；十二维几何延拓的密度另为 $\rho_{12}=|\det D_9|\rho_3/256$，两者职责不同。占据数为 $m$ 的扇区配权 $v^{m+2}$：
$$\langle f,g\rangle=\sum_{w\subset\mathcal I}\int_{\mathscr U_{100}}\overline{f_w}g_w\,\rho_3v^{m+2}dz,\qquad \mathscr H=\bigoplus_{w}L^2(\rho_3v^{m+2}dz).\tag{S1.5}$$
紧支撑光滑域在其中稠密（截断—逼近—磨光的逐占据数论证）。半密度映射 $(Uf)_w=\rho_3^{1/2}v^{1+m/2}f_w$ 是到平坦测度的满射等距；$v^{m+2}$ 因子是 coframe 伴随闭合所必需。

*形式伴随对与最小闭包。*在 (S1.3)–(S1.5) 的同一稠密域 $\mathscr D_{100}$ 上，令 $H_0$ 为 coframe、形式排序标量（$\sum_j\Pi_j^\dagger\Pi_j/(2h^{00})$ 排序）、规范与非 Yukawa 物质能量之和，$Y$ 为原单向 Yukawa 的 CAR 实现。

> **引理 S1.2（伴随对与闭图）。** $H_0$ 形式对称；完整 $H=H_0+Y$ 与独立 $H^\sharp=H_0+Y^\dagger$ 满足 $\langle f,Hg\rangle=\langle H^\sharp f,g\rangle$（$f,g\in\mathscr D_{100}$）。两者可闭，且各有单值最小图闭包。原全部 Yukawa 及其伴随的共同一体零空间在两个独立支上共 392 个模式；其 Fock 载体约化 $H_0$，在该载体上 $Y=Y^\dagger=0$，限制形式对称。

*证明。*逐项分部积分：标量采用指定的 $\Pi^\dagger\Pi$ 排序；规范 Gram 与磁导数对称；coframe 的动量、混合流、正规积项与系数导数项在权 $v^{m+2}$ 下配对；非 Yukawa 物质矩阵在双支配对中 Hermitian。只有原单向 $Y$ 在伴随时变成 $Y^\dagger$——这是对不对称的唯一来源，也是一个实质反例：对两粒子向量 $|144,396\rangle$，源点 $\|Y|144,396\rangle\|^2=4N^2=216/125$ 且 $Y^2$ 非零，故 $Y$ 在整个 Fock 作用上不为零、不隐对称。70 个 Yukawa 正 Gram 的非零谱为 $10N^2$（重数 42）与 $30N^2$（重数 14），共同双侧零空间每支 196 维；取共同核正交投影得 $196\times2=392$ 模限制。

闭性：若 $f_n\to0$ 且 $Hf_n\to g$，则对任意 $h\in\mathscr D_{100}$，$\langle h,g\rangle=\lim_n\langle H^\sharp h,f_n\rangle=0$，稠密性给 $g=0$；交换 $H,H^\sharp$ 同理。这给出各自的最小图闭包，不先选自伴扩张。∎

*四时间 Weyl 表示与全部正则运动。*在 $U\mathscr D_{100}$ 上，存在由原系数唯一读取的二次动量符号 $\sigma_0+Y$，使 $\operatorname{Op}_W(\sigma_0+Y)=UHU^{-1}$：先读二阶 $K$，再用第一条散度修正读一阶 $B$，零阶项补回；coframe 的 $\operatorname{divdiv}(K)/4$ 与半密度势合为 $n(3\mathrm{Number}^2+18\mathrm{Number}+20)/(16v)$；$\sigma_0$ 的 Hermitian 性由逐项分部积分与引理 S1.2 给出；$Y$ 不含动量且 $U$ 按占据数为标量，故原样保留。由此 $H$ 生成全部 100 对 CCR 与 504 对 CAR 的正规积运动。

**(3) 作用认回。**原作用—力系数是配置依赖的 $4W$，$W\ge1$ 由原标量 Gram 生成。实际核 $K(p)$ 含原全 Yukawa、配置物质、保留的时间与自旋项及物理动量，且对每个 $p$ 精确满足
$$S_{\rm phys}(p)+Y=S_{\rm nat}+S_{\rm cf}+K(p)-K_{\rm ret}.\tag{S1.6}$$
认回是逐槽的：$S_{\rm phys}$ 的各二阶密度项由原生部门 $S_{\rm nat}$、余标架部分 $S_{\rm cf}$ 与 $K(p)$ 回收，剩余槽恰为 $K_{\rm ret}$；$K_{\rm ret}$ 不是外设余项，它作为同一核定义的一部分由原作用自身给出。恒等式在 $\mathbb C^{289}$ 符号字典上逐项成立，$W$ 的配置依赖保留在每个方向。

**直接使用。**(1)(2) 的载体与最小闭包是定理 6.8 的 $H_0$、$Y$、$R$ 与准备态的载体；(3) 的 $K(p)$ 与 $4W$ 进入定理 6.9 的真变场响应与定理 6.10 的 Ward 通道；$\mathscr H$ 与分级结构是定理 6.12 谱论证与命题 9.2 读出模型的底层载体。

**形式对应。**定理 6.7(1)(2) 的子结论逐条固定于约束局部量子化源程序的较早提交，生产口与证据类别如下（`ecd/` 简记 `Verification/physics/low-energy-phenomenology/external-composite-decay/`，别名与提交见正文附录 D.7）：

| 子结论 | 固定提交 | 生产口 | 证据类别 |
| --- | --- | --- | --- |
| 61 对 CCR（$O_b^{\mathsf T}R=0$、$\Theta$ 精确拉回） | `85cb5386…` | `ecd/source_scalar_gauss_reduction.py` 与 `independent_*.py` | 固定精确源程序及其独立重算 |
| 103 维共同域、944 个非零交叉条目、61 个 Yukawa 方向 | `85cb5386…` | `ecd/source_joint_local_quantum.py` 与 `independent_*.py` | 固定精确源程序及其独立重算 |
| 504 模双支 CAR 及规范流矩阵 $Q_a$ | `85cb5386…` | 同上两程序 | 固定精确源程序及其独立重算 |
| 三稳定子协变律与共同核非零（引理 S1.1） | `f9b73392…` | `ecd/source_quantum_stabilizer.py` 与 `independent_source_quantum_stabilizer.py` | 固定精确源程序及其独立重算 |
| 经典约化相空间图与规范枢轴 | `f9b73392…` | `ecd/source_stabilizer_phase_reduction.py` 与 `independent_source_stabilizer_phase_reduction.py` | 固定精确源程序及其独立重算 |
| 量子截面、第二类测度相消 (S1.4)、半密度 (S1.5) | `6726f385…` | `ecd/source_quantum_gauss_section.py`、`source_gauss_section_measure.py`、`source_full_gauss_section.py` 与同名 `independent_*.py`；`ecd/SecondClassReduction.lean` | 固定精确源程序及其独立重算＋Lean 形式定理（相消恒等式） |
| Hilbert 载体 $\mathscr H$、$H_0$ 形式对称、伴随对 $(H,H^\sharp)$、最小闭包、392 模共同核约化（引理 S1.2） | `6726f385…` | `ecd/SourceQuantumConfigurationHilbert.lean`、`SourceQuantumHalfDensityHilbert.lean`、`GaussRadialDomain.lean`、`FockFilteredWords.lean`、`GaussSymmetricGraphClosure.lean`、`AntiunitaryDefectPair.lean`、`GaussYukawaCoefficient.lean`、`GaussYukawaNullspace.lean`、`RadialHilbertTransfer.lean`、`GaussHalfDensity.lean`；`ecd/source_hilbert_space.py`、`source_yukawa_cocycle.py`、`source_adjacent_cocycle.py`、`source_symmetric_graph.py`、`source_temporal_cofinal.py` 与 `independent_*.py` | Lean 形式定理＋固定精确源程序及其独立重算（程序承担有限维载体计算） |
| 四时间 Weyl 表示 $\operatorname{Op}_W(\sigma_0+Y)=UHU^{-1}$ | `6726f385…` | `ecd/source_{coframe,scalar,common}_weyl_symbol.py`、`source_common_temporal_form.py` 与同名 `independent_*.py` | 固定精确源程序及其独立重算 |
| 100 对 CCR 与 504 对 CAR 的全部正则运动（配置端口与正规积端口） | `eec031c4…` | `ecd/source_joint_ccr_car_ports.py` 与 `independent_source_joint_ccr_car_ports.py`；`ecd/JointCCRCarPorts.lean` | 固定精确源程序及其独立重算＋Lean 形式定理（正规积端口） |

同一源程序在这些提交中的其余结果（时间约束约化、量子时间图、完整 122 输入与时间／Lorentz 约束轨道等）不进入本文承重；本文只直接消费上表所列子结论，提交别名见附录 D.7 与 S10 中 phys.P26 一行。其中程序部分**不是** Lean 定理：它们是固定精确源程序（符号/精确算术，非浮点拟合），每枚都有同一提交下的独立重算程序作双实现核查；Lean 部分逐条是形式定理。

定理 6.7(3) 作用认回：`alpha-source/CanonicalPreparationActionCoreDecomposition.lean` 的 `physical_action_decomposition`，及同前缀 `FieldQuantization{Symbols,Core,Contacts}.lean`（Lean 形式定理）。提交 AB（6.7(1)(2) 的载体部分按上表所列四枚较早固定提交）。

---

## S2 定理 6.8：全阶时钟、完整固定 $R$ 与同一源准备

**对象与定义域。**定理 6.7 的载体 $\mathscr H$、稠密域 $\mathscr D_{100}$、$H=H_0+Y$ 与最小闭图。约束系统的四个时间方向由源系数矩阵 $T,S,C$ 生成的主力 Jacobi $J_4$ 描述；$J_4$ 在源支撑正锥上可逆（正文 (4.3) 类条件）。

**输入与量词。**(1) 对每个阶 $k\ge0$ 与四个时间方向 $a$；(2) 对全部标量测试函数；(3) 对每个 $\varepsilon>0$；(4) 对序列 $\varepsilon_n=1/(n+1)$。时钟、$R$、源算子与源能量都由源内生成，不由调用方提供。

**构造与关键引理。**

**(1) 全阶时钟。**时钟递归按阶组织：第 $k$ 阶时钟是四个时间方向、长 $k+1$ 槽的符号族。初始阶取源时钟值在第零槽、其余槽为零；递归步由
$$C_{k+1}(a,\mathrm{last})=-\sum_b (J_4^{-1})_{ab}\,R_{k+1,b}\tag{S2.1}$$
给出，其中 $R_{k+1,b}$ 是该阶在第 $b$ 条时间方程上的残差符号，由已付低阶的 42 个阶/槽函数、有序乘积词与原 13 个时间叶组成。

> **引理 S2.1（生成与保持）。** (i) 新阶由 (S2.1) 精确生成；(ii) $C_{k+1}$ 在前 $k+1$ 个槽上与 $C_k$ 一致（已付低阶不被改写）；(iii) 对每个 $k$、$a$，阶 $k+1$ 的四个后继力在原支撑闭集（位置锥、归一动量方向、$p\ne0$）上恒为零。

*证明。* (i)(ii) 是递归定义的直接性质。(iii) 记该阶残差为 $r_b$、新时钟为 $n_b=-(J_4^{-1}r)_b$；阶 $k+1$ 的第 $b$ 个力对新阶的响应是线性的，等于 $r_b+(J_4n)_b$（逐方向的力量响应 Jacobi 就是 $J_4$，条件为源时钟在正锥上非零）。代入 $n=-J_4^{-1}r$ 得 $r+J_4(-J_4^{-1}r)=0$；这里用到 $J_4$ 在源支撑上的实际可逆性。∎

全部 100 个方向的有限阶导数预算（保留重复方向的重数）与原系数表由同一引擎生成。

**(2) 完整固定 $R$。**能量尾 $E_{\rm tail}$ 先生成 Fourier 核（保留 $\pi(\xi+\eta)$ 的全平移结构）与双侧 Schur 界，完整能量形式在 Schwartz 输入上分解为
$$\mathcal E_B(g,f)=\mathcal E_{\rm prin}(g,f)+\mathcal E_{\rm tail}(B;g,f),\tag{S2.2}$$
两部分各自可积。经 Riesz 表示，$E_{\rm tail}$ 给出自伴尾部算子。定义
$$R=E_{\rm tail}-C_{\rm src},\tag{S2.3}$$
$C_{\rm src}$ 为源原生组成项。

> **引理 S2.2（$R$ 的固定性）。** $R$ 是有界自伴算子，有源生范数界 $\|R\|\le\|E_{\rm tail}\|_{\rm est}+\|C_{\rm src}\|_{\rm est}$；对全部原标量测试函数 $g,f$，由原闭因子 $A$（$B_1^2$ 的闭因子）与 $R$ 组成的形式满足
> $$\langle Ag,Af\rangle+\langle g,Rf\rangle=\mathcal E_B(\check g,\check f),\tag{S2.4}$$
> 即恰为完整 $B_1^2+E_{\rm tail}$ 的原 Weyl 能量形式。$R$、由 $A$ 与 $R$ 组成的源算子 $\mathcal T$、源能量 $E$ 都不依赖任何准备精度。

*证明。*分解 (S2.4) 把左端按 $R$ 的定义展开成主部形式加尾部形式，即 (S2.2)；自伴性继承自能量尾与组成项的各自自伴性。范数界推导：能量尾的 Fourier 核 $k(x,y)$ 满足双侧 Schur 估计——行、列积分别有源生有限界 $S_1=\sup_x\int|k(x,y)|\,dy$、$S_2=\sup_y\int|k(x,y)|\,dx$，Schur 检验给出 $\|E_{\rm tail}\|\le\sqrt{S_1S_2}$；组成项 $C_{\rm src}$ 有独立源生界，故 $\|R\|\le\|E_{\rm tail}\|+\|C_{\rm src}\|$。∎

**(3) 同一源准备。**准备点不是逐条构造的，而是由同一个源工厂一次产出：

> **引理 S2.3（同一准备点）。** 对每个 $\varepsilon>0$，源算子定义域中存在点 $x_\varepsilon$，同时满足：单位范数 $\|v_\varepsilon\|=1$；近谱 $\|\mathcal Tx_\varepsilon-Ex_\varepsilon\|<\varepsilon$；源产生等式（准备像等于源创造的对象）；原弱形式恒等式 $\langle\mathcal Tx_\varepsilon,y\rangle=\langle A\hat x_\varepsilon,Ay\rangle+\langle x_\varepsilon,Ry\rangle$；原生 Yukawa 荷读出 $=-1$；八条外腿的范数受统一的源生界控制；独立的时间—频率字段（对每个 $p,k$、李指标、截断、$z,w$（$\operatorname{Im}z,\operatorname{Im}w>0$）与全部离散指标，双时读数收敛到频率读数）；全 Yukawa 的定义域成员、值等式、截断界
> $$\|Y_{\rm closed}v_\varepsilon-\mathrm{cut}_n(v_\varepsilon)\|\le(915/916)^{n+1}\cdot 916\cdot b,\tag{S2.5}$$
> $b$ 为源生 Yukawa 系数界；以及截断序列的极限 $=$ Yukawa 值。

*证明要点。*存在性的实际机制如下。由 $A,R$ 生成增广闭形式（图形域上加 $(1+\|R\|)$ 倍），它确定唯一算子 $\mathcal T$ 并给出正、单射的有界预解式 $B=(\mathcal T+1+\|R\|)^{-1}$。取源能量
$$E=\|B\|^{-1}-(1+\|R\|):\tag{S2.5a}$$
因为 $B$ 是正有界算子，$\|B\|$ 是其谱点；对正有界单射，谱点 $\|B\|$ 产生单位近似本征向量（近似谱判据），其经 $B^{-1}$ 还原为 $\mathcal T$ 在 $E$ 处的单位近似本征向量 $x_\varepsilon$（一般引理为对有界正单射的逆算子版本）。弱形式恒等式是增广形式的逐域成员恒等式，不需另选点。八条外腿与时间—频率收敛由同一构造的附加字段携带；全 Yukawa 四字段由闭 Yukawa 图的原域估计给出，几何比 $915/916$ 是源 Yukawa 系数比值的显式上界。∎

**(4) 两个残差同时趋零。**取 $\varepsilon_n=1/(n+1)$，令 $x_n=x_{\varepsilon_n}$。在同一个固定的 $R$、$\mathcal T$、$E$ 下：

- 近谱残差：$\|\mathcal Tx_n-Ex_n\|<1/(n+1)\to0$；
- 全 Yukawa 截断残差：由 (S2.5)，$\|Y_{\rm closed}v_n-\mathrm{cut}_n(v_n)\|\le(915/916)^{n+1}\cdot916\,b\to0$（几何级数）。

两个收敛共用同一序列 $\{x_n\}$，不是各自另取的态。**这是残差收敛**：它不断言 $x_n$ 在范数下收敛，也不把 $x_\varepsilon$ 称为精确本征态。

**直接使用。**因果、接触、正阻尼时间尾与非线性读数（定理 6.9–6.10、6.12）消费同一准备点的全部字段；$R$ 的固定性使 (4) 中的 $\mathcal T$、$E$ 不随 $n$ 改变。

**形式对应。**`alpha-source/CanonicalPreparationEngineProgram.lean`（`sourceEngine`、`sourceEngine_generated`、`sourceEngine_preserves`）、`CanonicalPreparationEngineCancellationForces.lean`（`sourceEngineForces_successor_zero`）及同前缀 `Filtration`、`PaidForces`、`ActualRadial`；`CanonicalPreparationFullEnergyForm.lean`（`completeEnergyForm_split`、`actual_closed_form_complete_energy`）、`CanonicalPreparationSourceRemainder.lean`（`sourceRemainder_decomposition`、`sourceRemainder_selfAdjoint`、`sourceRemainder_norm`、`sourceRemainder_readback`）；`CanonicalPreparationSource{PreparedState,BoundarySequence,CausalState,NonlinearState}.lean`（`sourcePreparation_exists`、`preparationSequence_residual`、`preparationSequence_yukawa_residual`、`sourceCausalState_same_preparation`、`sourceNonlinearState_same_preparation`）。提交 AB。

---

## S3 定理 6.9：真变场响应与截断交换；及 §6.9 末的谱测度与全时收敛

**对象与定义域。**定理 6.7–6.8 的载体、$H=H_0+Y$、固定 $R$、同一准备序列 $x_\varepsilon$。场曲线指原场空间中经源坐标切片参数化的光滑曲线 $z\mapsto$ 物理图上的点；响应点 $q$ 如 S0.3。截断指标 $F$ 沿包含定向；截断阶槽取有限值 $n$ 时是第 $n$ 阶 Yukawa 截断、取未截值时是未截项。

**输入与量词。**(1)(4) 对每个场曲线与测试态；(2) 对任意阻尼 $\gamma>0$ 与满足 $|r|\le r_*(f,\psi,p,n,\gamma)$ 的非线性参数 $r$（$r_*$ 为源生非线性半径）；(3) 对每个 $F$、每个非实 $z$ 与原局部场邻域。§6.9 末两条对每个原核输入 $g$ 与任意有界插入成立。

**关键引理。**

> **引理 S3.1（截断 jet 极限）。** 对每个固定场曲线、$p$、$F$、非实 $z$ 与实参数 $r$：截断 Yukawa jet $Y_n(p,F,r)$ 当 $n\to\infty$ 收敛到未截 $Y_\infty$；预解式、电流、接触、插入与逆接触五项依次收敛到对应的未截算子。

*证明。*核心事实是**有限保留集**：对每个固定的 $F$ 与动量 $p$，保留项作用只落在某个有限保留指标集上，因而对每个固定参数组 $(f,p,F,z,r)$ 序列**逐点终站**——存在 $N$ 使 $n\ge N$ 时第 $n$ 阶 jet 与未截 jet 作为对象相等。最终常值序列在其（有限维）算子空间中按 $\mathcal N$ 邻域拓扑收敛，与该空间的范数收敛等价——故 $Y_n\to Y_\infty$、$R_n\to R_\infty$、电流、接触、插入五项各自成立（每条是对应 `Tendsto` 声明），只是稳定阶数 $N$ 依赖参数组，不是对全部输入一致。预解式极限亦可由逆映射连续性得到：$z$ 非实时未截移动对角元可逆，矩阵求逆在该点连续。∎

> **引理 S3.2（截断准备的读回）。** 对每个截断阶 $n$，第 $n$ 阶截断响应在原读出通道上与准备响应的截断值逐项相等；响应、其一阶导数、二阶导数各有逐点恒等式。

*证明。*截断响应的定义展开成完成外腿与截断预解式的配对；引理 S3.1 给出各因子的收敛，内积的联合连续性把收敛传到读数；导数情形使用同一恒等式先作逐点重写，再用一、二阶 jet 的收敛。∎

**决定性推导。**

**(1) 真变场。**原 106 维逆与全部原生、余标架、保留项生成真正的 289 维场向量与 36 个曲率读数：每个读数是经原场曲线输运的密度积分——实际 Gauss 密度 $Jv^{N+2}$ 与半密度比的前两阶导数随曲线输运，对角纤维保持分级压缩 $\sum_gP_gP_FH_{\rm phys}P_FP_g$ 的布局。完整形式及其截断压缩有真正的二阶射流：原生积分与余标架积分各在 $|r|<r_*(f,a)$ 的源域上带连续二阶导数与显式余项，合成后亦然；有限截断的逆直接给同一准备的一阶 $-RJR$ 与完整二阶接触项。

**(2) 非线性响应。**对阻尼 $\gamma>0$，非线性 Laplace 响应在源生半径 $r_*$ 内有真正的参数导数（在 $r=0$ 处可微，导数显式），余项满足
$$\bigl\|\Phi(r)-\Phi(0)-r\Phi'(0)\bigr\|\le L^2\,\bigl(s(f,g,\psi,p,n,\gamma)\cdot m(\gamma)\bigr)\,|r|^2\,\|u\|^2,\tag{S3.1}$$
其中 $L$ 为外腿界、$s$ 为源生余项尺度、$m(\gamma)$ 为 Laplace 质量、$u$ 为准备像。两条独立转移链保持动量标签 $p,\ p+\ell,\ p+k,\ p+k+\ell$ 及力的负号、接触的正号。

**(3) 截断到未截。**原移动闭 Yukawa 有稠密闭图，保留空间与准备的八条外腿在其真定义域内。字面截断的 0、1、2 阶 jet 都收敛到未截者：这是引理 S3.1 与 S3.2 的合取——先由有限保留集得算子收敛，再由逐点读回恒等式与 jet 收敛把交换传到准备响应与全部 36 个曲率读数。

**(4) 母态与固定测度。**原状态平方的坐标边与对角线认回同一个母作用态，生成全部四个有序 Hessian 块；在源邻域内移动纤维积分严格等于原固定测度纤维——密度导数由同一输运恒等式消去（注意：消去的只是已付的密度导数，响应本身照常读出），母电流、原生与余标架 jet 及保留余额照常进入同一准备的截断与未截一、二阶导数。

**§6.9 末：原 $H_0$ 的谱测度与全时响应。**对原 $H_0$，每个原核输入 $g$ 由同一源滤子生成 $\mathbb R$ 上的正有限测度 $\mu_g$，质量为 $\|g\|^2$：源滤子的每个有限级给出通道分解，各通道平方范数之和恰为 $\|g\|^2$，正性与一致性由投影族保证，极限测度在共尾指标上唯一。它同时读取全部非实 $z$ 的预解二次振幅（Stieltjes 型）与偶阶能量矩；对非零 $g$ 的归一化概率测度有对应极限陈述。对任意有界插入 $A$ 与阻尼 $\mu>0$，完整复迟滞振幅在整条实频轴上 $L^1$ 收敛——逐项误差由预解式价格与质量分解控制——经逆 Fourier 变换对全部时间一致收敛到时间响应。**这些是原 $H_0$ 源响应的量**：正测度承载在自由生成元的谱上，不改称完整相互作用的粒子谱。

**直接使用。**(3) 的截断—未截交换是定理 6.10 双腿 Ward 与定理 6.12 半轴论证的前提；(1)(4) 的曲率读数进入定理 6.11–6.13 的场返回。

**形式对应。**`alpha-source/CanonicalPreparationSourceNonlinearState.lean`（`preparedLaplace_derivative`、`preparedLaplace_remainder`、`sourceNonlinearState_same_preparation`）、`CanonicalPreparationYukawaObservedLimit.lean`（`sourceY_limit`、`sourceResolvent_limit`、`observed_uncut_limit`、`observed_uncut_limit_near`、`observed_first_exchange`、`observed_second_exchange`、`curvature_uncut_limit`、`curvature_first_exchange`、`curvature_second_exchange`、`finiteRetainer` 相关声明）、`CanonicalPreparationHalfDensityCompressionFeed.lean`（`diagonalFiber_source`、`transportedForm_fixed`、`transported_first_fixed`、`transported_second_fixed`、`compression_fixed_source`）；AC 增加 `CanonicalPreparationSpatialFullFormFeed.lean`（`completeForm_source`、`complete_first_source`、`complete_second_source`、`nativeIntegral_fixed`、`coframeIntegral_fixed`）、`CanonicalPreparationJointMixedResponse.lean`（`mixedCurvatureMatrix_generated`）、`CanonicalPreparationRawJointFiveTerms.lean`（`eulerCovector_generated`、`fiveKernel_generated`）、`CanonicalPreparationOriginalPreparedGreen.lean`（`original_green_equation`、`original_forced_field`）、`CanonicalPreparationPhysicalFeedbackField.lean`（`physicalField_generated`）。§6.9 末：`external-composite-decay/SourceHamiltonianSpectralMeasure.lean`（`actual_channel_mass`、`actual_stieltjes`、`actual_even_moment`、`actual_source_spectral_measure`、`actual_probability_limit`）、`SourceBoundedInsertionTime.lean`（`actual_time_error`、`actual_uniform_time_response`）。提交 AB（§6.9 末）与 AC（共同场消费）。

---

## S4 定理 6.10：荷—电流 Ward 恒等式与同一准备

**对象与定义域。**定理 6.7–6.9 的载体：504 模 CAR 纤维、量子测试空间 $\mathcal Q$、动量作用 $P(k)$、荷作用 $Q_a$（$a$ 为原生李代数元）、单体空间电流 $J_{\rm sp}(k,a)$ 与对电流 $J_{\rm pair}(k,a)$。两腿响应由截断指标 $F$、截断阶 $n$ 与非实 $z,w$ 参数化。

**输入与量词。**(1) 对每个测试态、每个动量 $k$、每个 $a$；(2) 对每个截断 $(n,F)$；(3) 全局荷有界性对每个时间方向，联合动量表示对 106 维轨道上的加权函数。

**关键引理。**

> **引理 S4.1（量化正规序的对纤维）。** 对任意复矩阵 $A,B$（模式维数任意），量化映射满足
> $$Q(A)Q(B)=Q(AB)+\Pi(A,B),\tag{S4.1}$$
> 其中 $\Pi(A,B)=\sum_{ijkl}A_{ij}B_{kl}\,c_i^\dagger c_k^\dagger c_l c_j$ 是对纤维算子；$\Pi(A,B)$ 与每个粒子数权重算子对易。

*证明。*逐指标展开并用 CAR：$c_jc_k^\dagger=\delta_{jk}-c_k^\dagger c_j$、$c_jc_l=-c_lc_j$，故
$$Q(A)Q(B)=\sum_{ijkl}A_{ij}B_{kl}\,c_i^\dagger c_jc_k^\dagger c_l
=\sum_{ijl}A_{ij}B_{jl}\,c_i^\dagger c_l+\sum_{ijkl}A_{ij}B_{kl}\,c_i^\dagger c_k^\dagger c_l c_j
=Q(AB)+\Pi(A,B).$$
权重对易性由 $Q(A)$、$\Pi(A,B)$ 都保持占据数得到。∎

> **引理 S4.2（对电流的单粒子湮灭）。** 在每个配置点 $z$ 的纤维上，$J_{\rm pair}(k,a)\,f=\Pi(P_k(z),Q_a)\,f(z)$；因而在单粒子投影上 $J_{\rm pair}=0$。

*证明。*逐点用引理 S4.1：$P(k)Q_a f$ 的坐标等于 $J_{\rm sp}(k,a)f+\Pi(P_k,Q_a)f$；单粒子扇区上两个湮灭算符无从同时作用，$\Pi$ 项恒为零。∎

**(1) 荷—电流分解。**由引理 S4.1、S4.2 直接得到正文 (6.4)：$P(k)Q_a=J_{\rm sp}(k,a)+J_{\rm pair}(k,a)$，对电流的四算子和以动量与荷的单体矩阵为系数，与全部粒子数密度权重对易，并在单粒子投影上为零。

**(2) 完整 Ward。**未投影的原物理作用加 Yukawa 的荷差精确保留四个通道：配置力矩、空间电流、四次对电流、Yukawa 力矩——写为
$$[Q_a,H_{\rm full}]=J_{\rm cfg}(a)+J_{\rm sp}(a)+J_{\rm pair}(a)+J_{Y}(a).\tag{S4.2}$$
在任意截断 $(n,F)$ 上，压缩缺陷与 Yukawa 截断差 $Y_n-Y$ 原样进入余项：有限插入在共尾 $F$ 上等于
$$\mathrm{finIns}_{n,F}=W_{\rm core}+\Delta^{Y}_n(Q_a f)-Q_a\,\Delta^{Y}_n(f)+\text{压缩缺陷},\tag{S4.3}$$
即缺陷不被静默删去。双腿响应 $\langle x,R_{\rm full}(p+k,z)Q_aR_{\rm full}(p,w)y\rangle$ 精确等于解析通道（核心通道加输运余项）之和：把两腿分别解析为 $\widetilde x=R(p+k,z)^*x$、$\widetilde y=R(p,w)y$，先作源内近似，再用 (S4.3) 读出；响应有统一价格
$$\|\mathrm{resp}\|\le\|x\|\Bigl(c_a\,b_n(w)+b_n(z)\,c_a+|z-w|\,v_a(n,z,w)\Bigr)\|y\|,\tag{S4.4}$$
$c_a$ 为荷的价格、$b_n$ 为截断预解式界、$v_a$ 为顶点价格。

**(3) 全局荷与同一准备。**原 12 个时间方向由实际作用生成全局有界荷 $Q$：每个方向的读出算子有显式价格 $c_a=\|\mathrm{quantized}(C_a)\|$。沿同一曲线，裸 Hamiltonian 与保留项的 $-rQ$ 变化相消——完整 $H$ 减保留项不产生虚假的 $-rQ$ 项；原生 106 维轨道的联合图生成加权联合动量表示 $\sum_iP_i^\dagger(c_i f)=-Q$（联合读出算子有界、图闭、稠密）。真实双腿 Ward 由同一源滤子完成——在共尾 $F$ 上压缩缺陷为零，(S4.3) 趋于 Ward 核——并由同一准备点（S2）的八条外腿与 36 个曲率读数的十二个时间列直接读取。

**边界说明。**这些读数尚未识别为物理电磁耦合、电子或 Thomson 极限；正文 §6.10 末的同一声明在此保留。单粒子扇区对电流为零是消去事实，不是全部电流为零。

**直接使用。**分解 (6.4) 与双腿 Ward 是定理 6.12 五因子核、定理 6.13 静态留数与共源相容条件的输入；全局荷 $Q$ 的价格界被 6.14 的整词预算消费。

**形式对应。**`alpha-source/CanonicalPreparationElectricPairCurrent.lean`（`quantized_normal_order`、`pairFiber_weight`、`full_current`、`pairCurrent_original_words`、`pairCurrent_oneParticle`）、`CanonicalPreparationElectricCoreWard.lean`（`physical_full_ward`、`original_full_ward`、`finite_full_core`、`finite_full_core_eventually`、`compressionDefect_eventually`）、`CanonicalPreparationElectricWeightedGraph.lean`（`weighted_adjoint_constraint`、`original_weighted_ordering`、`jointReader_price`、`original_joint_graph_closed`）、`CanonicalPreparationElectricPreparedWard.lean`（`insertion_actual_channels`、`resolvedChannels_original_response`、`original_response_price`、`resolvedChannels_price`、`resolvedChannels_samefilter`、`preparedChannels_same_state`、`curvatureChannels_same_state`）、`CanonicalPreparationTemporalGlobalCharge.lean`（`temporal_hamiltonian`、`temporal_contact_balance`、`globalReader_norm`）。提交 AB。

---

## S5 定理 6.11：母作用的二阶变分就是这个 $H_{289}$

**对象与定义域。**固定源、原作用 (3.1) 与构造 4.1 的指定解。289 个实方向是九组场（coframe、Lorentz 连接、规范、标量、primal、独立对偶等）在 holonomic 配置下的实坐标；$p\in\mathbb C^4$ 为四个复动量；$H_{289}(p)$ 是原 Jacobi 字典（3071 项，系数在 $\mathbb Q(\sqrt2,\sqrt{15})$）。

**输入与量词。**(1) 对该解处的所有 289 方向变分；(2) 对每个 $p$；(3) 对全部 289 个场单位方向；(4) 对任意非退化余标架。

**关键引理。**

> **引理 S5.1（光滑性与二阶密度分解）。** 母密度由十二个源支撑节点（逆余标架、三阶 $H$ 系数、非阿贝尔接触、标量轨道与独立对偶的三阶系数及伴随矩阵）在指定解处光滑生成；其 Fréchet 二阶变分是对称双线性型，并按引力（拓扑 BF 与线性 $\Lambda$ 残差）、规范、标量、Dirac（含独立对偶）四部门分解为 234、406、220、790 项的二阶密度；95 个常量全部回到原源系数。

> **引理 S5.2（Fourier 归并）。** 每个二阶密度项是两个场腿与一个动量单项式的乘积；Fourier 变换把每项写成两个带符号贡献。全部 1650 项产生 3300 个带符号双腿贡献，按原字典排序合并后逐项等于原 $H_{289}(p)$ 的 3071 项；左 Euler 导数的负号只插入一次。

*证明要点。*逐项比较是有限集合上的等式，实际判定分两步：两个项表各自典范化后的逐条相等由 `decide +kernel` 判定（证明核归约到同一典范项表）；Fourier 归并把字面二阶项写成带符号双腿贡献的正确性是一条独立的重述定理，再与上述项表相等复合。系数域为 $\mathbb Q(\sqrt2,\sqrt{15})$，标量系数等式由 `ring`、`norm_num` 等逐条判定，非浮点比较。∎

> **引理 S5.3（holonomic Euler 读数）。** 对 holonomic 配置，Euler 读数等于“值的偏导减动量散度”。九组母残差沿全部 289 个场单位方向的拉回逐方向等于该读数：184 个不含导数的槽给零动量与零散度，标量、primal 与连接三类方向（9、24、72 个）满足“值减散度等于原 Euler”。

> **引理 S5.4（Legendre 回读）。** Lorentz 连接的完整二次型 $\tfrac12\omega^{\mathsf T}\mathcal H\omega$ 中，$\mathcal H$ 由 216 个结构系数与非退化余标架的有理矩阵 $K_0$ 生成（$e^{\mathsf T}K_0e/\det e$）；576 个多项式条目的乘积验证 $K$ 是两侧逆。加入自旋与几何载荷 $J$ 后唯一消元为 $\Omega=-KJ$，值为 $-\tfrac12J^{\mathsf T}KJ-3\det e$。余标架 16 个正则动量与 10 个初级约束的 Legendre 变换返回 S1 的余标架动能；八个 Clifford 方向的 CAR 收缩给自旋常数项 $\tfrac{3\,\mathrm{lapse}}{4V}\mathrm{Number}-\tfrac{\mathrm{lapse}}{2V}\mathrm{normal}$；线性电流与粒子数径向动量的配对产生的 $\mathrm{Number}^2$ 项与混合 Gram 的额外项精确相消，剩 $-\tfrac{9\,\mathrm{lapse}}{8V}\mathrm{Number}$。

**决定性推导。**(2) 由引理 S5.1 给 Hessian 的源生成分解、由引理 S5.2 把它归并为同一个 $H_{289}(p)$——同一枚矩阵对象，不是同构或近似；(3) 由引理 S5.3 逐槽成立；(4) 是有限维二次型消元（$K$ 的可逆性由引理 S5.4 的乘积验证）加 CAR 正规序的有限收缩。

**直接使用。**定理 6.12 的 Green 等式、九个相容残差与 36 个曲率读数消费的 $H_{289}$ 就是这个矩阵；定理 6.13 的静态极点在它的源半径域内展开。

**形式对应。**`alpha-source/CanonicalSourcePropagationOriginalHessianReturn.lean`（`nativeCompleteLiteralTerms`、`nativeHessian_complete_source`、`nativeActionFourierHessian_original`、`nativeJacobi_original`、`nativeAction_sourceField`、`nativeAction_original_regular_point`、`nativeAction_sourceField36`、`nativeAction_noetherField`、`nativeAction_noetherField36`）、`CanonicalSourcePropagationPreparedMotherEulerReturn.lean`（`actualPreparedMotherEuler_generated`、`actualPreparedMotherEuler_linear`、`actualPreparedMotherEuler_multiplier`、`actualPreparedMotherEuler_{gravityAuxiliary,gaugeAuxiliary,coframe,independentDual}`、`nativeHolonomicEuler_raw`、`nativeHolonomicEuler_raw_near`、`preparedMotherForcing_cosources`）。提交 AD。

---

## S6 定理 6.12：同一保持电流经完整半轴返回 $H_{289}$

**对象与定义域。**定理 6.11 的 $H_{289}$（原 Jacobi）、定理 6.9–6.10 的核 $K_F(p)$ 与读口 $J$、响应点 $q$（S0.3）。$\mathbb C^{289}$ 到配置 Hilbert 空间的原生配置嵌入记为 $\iota_{289}$（S1 的全场载体；不与 6.13 的五方向嵌入 $E_0$ 相混）。原 Green 数据的四个构件一次定义：$D$ 为接触块逆、$P_a$ 为活跃 103 维块的正交投影、$K_{\rm ext}$ 为扩展核（活跃核加空槽补项）、$P_{\rm null}$ 为九维零方向投影；行提升记 $L$、回读记 $R_b$（$R_bL=I$，S7 详述）。算子 pencil 为 Sylvester 型
$$\mathcal P_q(\lambda)A=\lambda A+\mathcal A_L A-A\mathcal A_R,\tag{S6.1}$$
$\mathcal A_L=-iK_F(p+k)$、$\mathcal A_R=-iK_F(p)$。Green 因子矩阵记 $\Xi$（不与截断指标 $F$ 相混）：原 Green 为
$$G=\Xi\,\bigl(D^{-1}+P_aK_{\rm ext}^{-1}\bigr)\,\Xi(-p)^{\mathsf T},\qquad H_{289}\,G=I-\Xi(-p)^{-\mathsf T}P_{\rm null}\Xi(-p)^{\mathsf T},\tag{S6.2}$$
第二式在活跃 103 维块行列式非零的正则域上成立。

**输入与量词。**(1) 对每个响应点、外力与截断 $F$；(2) 对每个非实谱参数与 $\operatorname{Re}\lambda>0$；(3)(4) 对每个非实 $w$、动量 $k$ 与响应点；(5) 对 $\operatorname{Re}\lambda>0$ 的每个频率及一个源生具体实例（时钟 $\lambda_0=3-g$、读频 $3$，$g$ 见 (5)）。

**(1) 共同场与有限窗恒等式。**

*构造与量词。*同一空间半密度与完整配置积分生成共同场向量（289 个分量）与 36 个曲率读数；场对源场曲线是 $C^2$ 的，Hessian 对称——36 格每格由 1296 个混合响应条目组成（$36\times36$）。母 Euler 的原项是 $-4W\cdot DH$，完整密度接触项由同一输运恒等式消去。

*关键推导。*九项展开：五因子乘积的时间导数由乘积法则逐因子展开，与五项时间导数核逐项一致——原生五项核与同一窗口的 Euler 余向量同时生成。有限窗恒等式是加权分部积分：对原场曲线 $c(s)$ 与 forcing，
$$\Xi(-\lambda,-ik)^{\mathsf T}\cdot\mathrm{forcing}
=\int\bigl(\text{时间 jets}\bigr)\,dt-\bigl(\text{终值}-\text{初值}\bigr),\tag{S6.3}$$
场曲线的导数等于 Green 作用于该 forcing。原 Green 等式 (S6.2) 与强迫场等式由原 Jacobi、$\Xi$ 与活跃 103 维块交织的有限矩阵恒等式在系数域中验证；正则域非空：源生有理数值点上的扩展核乘以源生逆项矩阵等于单位阵（逐条由 `decide +kernel` 判定），右逆即给行列式非零，该点即一个正则点。

*使用。*本款的 Green 等式同时供 6.13(4) 的相容判据。

**(2) 57 项多项式时间界与完整正半轴。**

*关键引理（分级界）。*压缩部分 $C_F$ 保持占据分级，保留项 $A_F$ 升一级，故 $K_F=C_F+A_F$ 的 57 次纯升级为零；Duhamel 展开截于 56 阶，全载体时间演化恰为有限和
$$\text{时间界}(\text{切断}\,c,t)=\sum_{n<57}\bigl(|t|\cdot\|c\|\bigr)^n\tag{S6.4}$$
——物理时间演化的界是 $|t|$ 的 56 次多项式，系数为切断范数幂。这是演化多项式界的真实来源：不是对半群范数的整体假设，而是分级结构的组合截断。

*半轴。*对每个 $\operatorname{Re}\lambda>0$，多项式界乘 Laplace 权 $e^{-\lambda t}$ 逐项 Bochner 可积；取源价格 $\eta=\operatorname{Re}\lambda/8$，范数包络 $e^{(\operatorname{Re}\lambda/2)t}\cdot e^{-\operatorname{Re}\lambda t}=e^{-(\operatorname{Re}\lambda/2)t}$ 给出完整正半轴 forcing $\Phi^+$ 与场响应。(S6.3) 的 $T\to\infty$ 极限即**半轴恒等式**
$$\Xi(-\lambda)^{\mathsf T}\,\Phi^+=\Sigma^++B_0,\tag{S6.5a}$$
其中 $\Sigma^+$ 为时间 jet 积分项、$B_0$ 为 $t=0$ 初值边界项（与 6.13 的静态张量 $S$ 不再同号）；有限窗与半轴之差有显式指数尾
$$\bigl\|\Phi^+-\Phi_T^+\bigr\|\le\frac{2}{\operatorname{Re}\lambda}\,c\,e^{-(\operatorname{Re}\lambda)T/2},\tag{S6.5}$$
$c$ 为同一源在 $\eta$ 处的范数价格（$c=\text{源价格系数}(\eta)$），末端共源趋零。

**(3) 两个半平面的 Bochner 逆与谱轴。**

*两侧逆。*对 $\operatorname{Re}\lambda>0$，正时间积分 $R^+(\lambda)=\int_0^\infty e^{-\lambda t}\Phi_t\,dt$ 由时间方程 $X_t'=A X_t-X_t B$（$\Phi_t(X)=T_{p+k}(-t)XT_p(t)$）满足两侧逆恒等式
$$\mathcal P_q(\lambda)\,R^+(\lambda)=R^+(\lambda)\,\mathcal P_q(\lambda)=\mathrm{id}\tag{S6.6a}$$
（左作用 $\mathcal P_q(\lambda)X=\lambda X+AX-XB$ 与右作用 $X\mathcal P_q(\lambda)=\lambda X+XA-BX$ 各由一次分部积分把 $\lambda$ 权换成时间导数得出），是该 pencil 在右半平面的两侧逆；对 $\operatorname{Re}\lambda<0$ 用负时间（过去）积分同理得左半平面逆。两个开半平面各有一枚有界逆，故 pencil 谱只能含于虚轴 $\operatorname{Re}\lambda=0$。

*零转移的谱点。*在零转移（两腿动量相同）处，pencil 生成元与单腿生成元重合，恒等算子属于核，而载体中存在非零单元（同一准备的单位向量），故 $0$ 是 pencil 的实际谱点；其响应恰为 $\lambda^{-1}\langle\cdot,\cdot\rangle$ 型读数——在 $\lambda=0$ 无界，与“谱含于虚轴”一致。

**(4) Picard 迭代与实际变背景。**

*推导。*给定 $C^1$ 场历史与幅度参数 $a$，两腿各自由非自治生成元 $\mathcal G_a(t)$ 驱动：原始腿 $U_a'= \mathcal G_aU_a$、对偶腿 $V_a'=-V_a\mathcal G_a$，初值 $U_a(0)=V_a(0)=1$；解作为有界生成元在有限窗 $[0,T_*)$ 上的演化存在且唯一（源窗对象给出生成元在窗内的一致范数价格与对 $a$ 的 Lipschitz 界）。两腿间的物理背景映射（左乘 $T_{p+k}(-t)$、右乘 $T_p(t)$ 的算子上算子）是**自治**的：其生成元 $\mathcal E$ 是固定的 TransferOp，$\mathcal E$ 与映射值对易、初值为 $1$，故该映射恰为 $\exp(t\mathcal E)$（自治唯一性）；两个指数间有 Volterra/Duhamel 恒等式
$$e^{tL_1}=e^{tL_0}+\int_0^t e^{(t-s)L_0}(L_1-L_0)\,e^{sL_1}\,ds\tag{S6.8}$$
幅度在 $a=0$ 处的导数由同一恒等式给出——原始腿的变分是常数变易积分
$$\partial_aU\big|_0=T_p(t)\int_0^t T_p(-s)\,\partial_a\mathcal G_a\big|_0(s)\,T_p(s)\,ds,\tag{S6.9}$$
对偶腿为负号共轭形；积分号下对 $a$ 求导由参数化导数引理（有限窗上生成元割线界、演化界与解的振幅界三张主项同时成立，控制收敛交换导数与积分）支付。有序历史源（Noether 历史源）保持有序乘积词的序而非按频率排序，原生历史核的时间一、二阶导数逐项回到该源；母 Euler 的当前变体、forcing 共源与变背景下的母返回在同一实际构造中生成——历史返回不是近似，是逐项等式。

**(5) 实电流算子、信号 jet 与反馈不动点。**

*实电流连续线性算子。*同一准备的实电流在完整 289 维实场上生成连续线性算子：加权电流核的 Bochner 积分 $\int_0^\infty e^{-\lambda t}J_t\,dt$ 在 $\operatorname{Re}\lambda>0$ 收敛，有限窗与半轴之差在算子范数中满足同一尾界 (S6.5)；场版本同结论。

*实 Fourier 信号。*原四维实 Fourier 信号 $\operatorname{Re}(e^{ip\cdot x}a)$ 的两个实正交分量各为复线性算子；其 0、1、2 阶时间 jet 进入实际有序历史输入，与母 Euler 逐项一致——信号因果响应把同一准备读到场。

*行列式—伴随矩阵与唯一不动点。*反馈矩阵为 $I-\mathcal U$（$\mathcal U$ 为源生更新算子，原 Green 与五方向残差的合成，不是外加投影）。对任意 $289\times289$ 矩阵，行列式—伴随矩阵等式无条件成立；在 $\det(I-\mathcal U)\neq0$ 的频率上它给出显式两侧逆，响应方程 $\varphi=f+\mathcal U\varphi$ 有唯一不动点 $\varphi=(I-\mathcal U)^{-1}f$。

*源生实例与 $3/16$ 界。*源生锚点取初值预算 $B$（原 Green 范数与时间 jet 矩阵范数等的源生界，$B\ge0$）、读隙 $g=\frac1{8(1+B)}$、时钟 $\lambda_0=3-g$、读频 $3$。$3/16$ 的真实推导：锚点频率处的反馈更新算子拆为 Laplace 电流项与初值项两块，源生价格分别给 $\le\frac1{16}$ 与 $\le\frac18$，故
$$\|\mathcal U\|\le\tfrac1{16}+\tfrac18=\tfrac3{16}.\tag{S6.6}$$
由 $\|\mathcal U\|<1$ 得 $\det(I-\mathcal U)\neq0$（谱半径小于 1，核为零则行列式非零），正则域非空；响应方程写为 $\varphi=f+\mathcal U\varphi$，故
$$\|\varphi\|\le\|f\|+\tfrac3{16}\|\varphi\|\ \Longrightarrow\ \|\varphi\|\le\tfrac{16}{13}\|f\|.\tag{S6.7}$$
初值共源与九个相容残差始终保留。

**直接使用。**(1) 的 Green 等式与 (3) 的零点谱点直接供定理 6.13 的静态极点域、相容判据与留数；(2) 的半轴恒等式被 6.13(5) 的原点权重公式消费；(5) 的反馈不动点是 6.12 场反馈的闭式解。

**形式对应。**(1)：AC `CanonicalPreparationSpatialFullFormFeed.lean`（`completeForm_source`、`transportedForm_fixed`）、`CanonicalPreparationJointMixedResponse.lean`（`jointHessian_symmetric`、`mixedCurvatureMatrix_generated`）、`CanonicalPreparationRawJointFiveTerms.lean`（`fiveKernel_generated`、`eulerCovector_generated`）、`CanonicalPreparationOriginalPreparedGreen.lean`（`original_green_equation`、`original_forced_field`、`generatedRegularPoint`：右逆恒等式逐条 `decide +kernel`）、`CanonicalPreparationPhysicalFeedbackField.lean`（`physicalField_derivative`）。(2)：AD `CanonicalPhysicalLaplace.lean`（`timeBound cut t = Σ_{n<57}(|t|‖cut‖)^n`）、`CanonicalPreparationPhysicalTimePolynomial.lean`、`CanonicalPreparationPhysicalSourceGrowth.lean`、`CanonicalPreparationPhysicalActualEnvelopes.lean`、`CanonicalGradedMixed.lean`（`graded_mixed_zero`、`source_homogeneous_zero`）、`CanonicalPreparationPhysicalFullHalfAxis.lean`（`weighted_integrable`、`halfForcing`、`halfForcing_readback`、`halfField_equation`、`halfField_cosources`）、`CanonicalPreparationPhysicalControlledFieldTail.lean`（`actual_controlled_field_tail`、`explicitSourceTail`、`source_scalarCoefficient`）。(3)：AD `CanonicalSourcePropagationAxisReadback.lean`（`actualResolvent_{left,right,isUnit,spectral}`、`actual_spectrum_axis`、`zero_transfer_{source_kernel,pencil_unit,resolvent_unit,prepared_pole_read,actual_spectral_point}`）、`CanonicalSourcePropagationSourceSpectralInverse.lean`（`sourcePencilUnit`、`sourcePoleSet` 有限性、`sourceSpectrum_sub_poles`）、`CanonicalSourcePropagationSpectralAxis.lean`。(4)：AD `CanonicalSourcePropagationActualBackgroundEvolution.lean`、`CanonicalSourcePropagationActualPreparedHistoryVariation.lean`（`historyPrimal/Dual Variation_generated`、`orderedHistoryDirection_*`）、`CanonicalSourcePropagationActualNativeHistoryReturn.lean`（`actualPreparedHistoryKernel`、`actualPreparedHistorySource`）。(5)：AE `CanonicalPreparationSourceHalfAxisCurrentOperator.lean`（`sourceHalfCurrent` 积分、`sourceHalfCurrent_generated`、`sourceWindowJacobian` 范数收敛与 $(2/\operatorname{Re}\lambda)\cdot\text{sourceCurrentPrice}\cdot e^{-(\operatorname{Re}\lambda/2)T}$ 尾）、`CanonicalPreparationSourceHalfAxisFieldOperator.lean`、`CanonicalPreparationSourceNativeFourierHistory.lean`（`sourceSignalOperator_{left,right}`、`sourceHistoryInput`）、`CanonicalPreparationSourceOrderedSignalOperator.lean`、`CanonicalPreparationSourceSignalCausalResponse.lean`、`CanonicalPreparationSourcePreparedSignalEuler.lean`、`CanonicalPreparationSourceCurrentFeedbackAdjugate.lean`（`sourceFeedbackMatrix_actual`、`sourceFeedbackAdjugate_{left,right}`、`sourceFeedbackResolvent_{left,right}`、`sourceFeedbackResponse_{generated,unique}`）、`CanonicalPreparationSourceAnalyticRegularPoint.lean`（`sourceInitialBudget`、`sourceAnchorGap` $g=1/(8(1+B))$、`sourceAnchorClock` $3-g$、`sourceAnchorUpdate_price` $\le3/16$、`sourceAnalyticResolvent_price` $\le16/13$、`sourceAnchorDenominator_ne_zero`、`sourceRegularDomain_nonempty`）。提交 AC、AD、AE。

---

## S7 定理 6.13：极点、约束与静态留数

**对象与定义域。**定理 6.11–6.12 的 $H_{289}$（原 Jacobi）、原 Green $G(p)$、Green 数据 $L$（行提升）、$R_b$（回读，$R_bL=I$）、$P_{\rm null}$（九维零方向投影），以及 6.12 的五因子电流读口与响应点 $q$。静止八态记八个指标 $l,r$；动量 $p$ 处的移动八态基由源的 $4\times4$ Hermitian 矩阵在两个手征上各给出四态。本节的静态张量记 $S$；6.12(2) 的时间 jet 积分项记 $\Sigma^+$，两者不再同号。正文“变化 forcing 的未清场极限”由 `actualAxisWindow_tendsto` 与 `axisCosource_tendsto`、`axisNullCosource_tendsto`（见下方形式对应）承担。

**输入与量词。**(1) 对任意三动量与 Gauss 算子 $A$；(2) 对每个 $F$、非实 $z$ 与动量对；(3) 对静态域（非空穿孔区间）中的每个 $\kappa$、forcing $f$ 与实际转移（左动量 $-\kappa e_1$、右动量 $0$、$\lambda=0$、有限窗 $T$），留数极限沿该域内 $\kappa\to0$；(4)(5) 对每个响应点、两腿动量、静止态指标、$\lambda$ 与有限窗 $T$。

**(1) moving 载体与重叠酉阵。**

> **引理 S7.1。**moving 基与静止八态的重叠矩阵 $U(p)$ 是酉矩阵：同一 $\varepsilon$ 准备的正交归一给 $U(p)^\dagger U(p)=I$，有限维中右逆随之成立（另有显式双侧酉性）；$U(0)=I$。动量 $p$ 处的准备、产生算子、原始腿、纤维向量与同 $\varepsilon$ 准备都是静止者的 $U(p)$ 组合；读出张量满足
> $$M(p_L,p_R)[A]=U(p_L)^{\dagger}\,M(0,0)[A]\,U(p_R),\tag{S7.1}$$
> 即整个算子 $A$ 保留，八态只承担外端坐标。

*证明。*正交归一列给出左逆；$8\times8$ 维数有限，左逆即酉，另有逐层的两侧酉性构造。张量公式由两端内积的双线性展开：外端坐标各乘一枚 $U$。∎

**(2) 动量仿射与联合连续。**

> **引理 S7.2。**压缩 $C_F(p)=C_F(0)+v_F(p)$，其中 $v_F$ 是连续实线性动量作用，故 $\|C_F(p)-C_F(k)\|\le\|v_F\|\,\|p-k\|$；由预解式差公式（S0.4），$\|R_p(z)-R_k(z)\|\le|\operatorname{Im}z|^{-2}\|v_F\|\,\|p-k\|$。有限保留集与保留项 $A_F$ 跨动量相同，故联合生成元、联合预解式、联合时间演化、289 个读口、五因子张量与有限 Laplace 窗都对动量连续（各自的连续声明逐一生成）。单谱标签的连续性不作假设。

*证明。*动量作用经量子化与固定压缩是实线性的，速度算子有界即给 Lipschitz 常数 $\|v_F\|$；预解差式两边取范数即得。保留集只依赖固定的保留指标集与 $F$ 而不含 $p$，故保留项跨动量相同；联合生成元的动量差由同一速度界控制，时间演化作为生成元的范数指数复合保持连续。∎

**(3) 静态极点与留数。**

> **引理 S7.3（静态主块）。**在物理动量 $p_\kappa=(0,i\kappa,0,0)$ 处，$H_{289}$ 的全部含 $\kappa$ 字典项恰按 $-\kappa^2$ 收集为首项 $-\kappa^2S$，$S$ 为静态张量。$S$ 在 98 维补空间加五方向块的扩展下显式可逆（源生逆项列表的逐项乘积验证），有源生范数预算；归一化核在源生正半径内可逆（Neumann 型论证），该半径给出非空穿孔静态域。

> **引理 S7.4（极点分解）。**未清分母的完整 289 维 Green 在穿孔静态域中分解为
> $$G(\kappa)f=\ \text{接触项}\ +\ (-\kappa^2)^{-1}\cdot V_0S^{-1}V_0^{\mathsf T}\!f\ +\ \text{98 维补空间正则部分},\tag{S7.2}$$
> 九个零方向的 forcing 保留。各因子沿 $\kappa\to0$ 连续：归一化逆收敛到加块逆 $S^{-1}_{\rm pad}$，有效框架收敛到原生五方向框架 $V_0$，读出收敛到 $V_0^{\mathsf T}$。于是对固定 forcing $f$，
> $$-\kappa^2\,G(\kappa)f\ \longrightarrow\ V_0S^{-1}V_0^{\mathsf T}f=:\rho_{\rm st}(f).\tag{S7.3}$$
> 对变化 forcing，同一分解的轴窗与轴余源各有未清场极限（形式对应中的 `actualAxisWindow_tendsto` 等）。

*证明。*接触项与补空间项乘 $-\kappa^2$ 后趋于零；中间项各因子逐项收敛后复合；静态域非空由引理 S7.3 的正半径给出。∎

> **引理 S7.5（原点权重与模式读出）。**五方向原点嵌入 $E_0:\mathbb C^5\to\mathbb C^{289}$（原生框架经原变量代换）作用于双分量向量；对实际转移的电流，留数为
> $$\rho_{\rm st}=E_0\Bigl(-\tfrac9{125}\sqrt{30}\,\mathfrak{w},\ -\tfrac{67}{72}\sqrt{30}\,\mathfrak{w},\,0,0,0\Bigr),\qquad \mathfrak{w}=\tfrac{3\sqrt2}{10}\bigl(J_{21}-J_{34}\bigr)=-c_{114},\tag{S7.4}$$
> 其中 $-\tfrac9{125}\sqrt{30}$、$-\tfrac{67}{72}\sqrt{30}$ 是 $S^{-1}$ 作用在五方向权重上的两个精确分量（$\sqrt{30}=\sqrt2\sqrt{15}$）；$\mathfrak{w}$ 恰为负的第 114 号实际共源（见 (4)），两个规范槽是指标 $21$ 与 $34$。

**(4) 约束相容判据与第 114 行。**

> **引理 S7.6（轴场相容）。**原 Green 等式 (S6.2) 的两边作用于实际窗口场：
> $$H_{289}\,\varphi=w_{\rm win}-L\,(\text{九维轴零共源});\tag{S7.5}$$
> 故 $H_{289}\varphi=w_{\rm win}$ 当且仅当九维轴零共源为零——正向直接，反向用 $R_bL=I$（由 $\Xi$ 的原变量代换回读）。该判据是定理给出的条件，不由定理产生。

> **引理 S7.7（约束行 114）。**原回读的第 114 行是三个线性读数之和：荷项、协变约束项与不受支项；不受支项在实际电流窗口与半轴上恒为零。故实际第 114 号共源只剩荷项与协变项，其 Ward 边界形式见 (5)。

*证明。*$H_{289}\varphi=w_{\rm win}$ 与九维共源为零的互推是 (S6.2) 与 $R_bL=I$ 的两行线性代数；行 114 的三分解是回读矩阵的逐行展开，不受支项为零由该行在实际电流上的逐项结构给出；$\mathfrak{w}=-c_{114}$ 是实际共源与原大权重的逐行等式。∎

**(5) 原点权重的接触—偏离分解、带权 Ward 形式与价格。**

*接触—偏离分解。*$\mathfrak{w}$ 分解为原生接触窗减配置偏离窗：
$$\mathfrak{w}=\kappa_{\rm ct}-\delta_{\rm cf},\qquad \kappa_{\rm ct}=\int_0^T\!(\text{极点读出}\circ\text{接触核})\,dt,\qquad \delta_{\rm cf}=\int_0^T\!(\text{极点读出}\circ\text{偏离核})\,dt,\tag{S7.6}$$
由模式读出接触核与偏离核的实际关系逐点成立。

*带 Laplace 权的 Ward 形式。*实际第 114 号共源对任意谱参数 $\lambda$ 与有限窗 $T$ 为
$$c_{114}(\lambda,T)=\int_0^Te^{-\lambda t}\,(\text{N1 色 Ward 读出})\,dt+\int_0^Te^{-\lambda t}\,(\text{协变约束电流})\,dt-\Bigl(e^{-\lambda T}Q(T)-Q(0)\Bigr),\tag{S7.7}$$
三项分别对应 (4) 的荷项（N1 正规化后与 primal 正规化一致）、协变项与分部积分边界项；(3) 的实际转移取 $\lambda=0$（权恒为 $1$），此时
$$\mathfrak{w}=\kappa_{\rm ct}-\delta_{\rm cf}=-c_{114}(0,T),\tag{S7.8}$$
即正文 (5) 的公式。

*价格。*偏离窗由两枚物质预解式的 $|\operatorname{Im}\cdot|^{-1}$ 界与偏离读口 $D_0F$ 的算子范数控制：
$$|\mathfrak{w}-\kappa_{\rm ct}|=|\delta_{\rm cf}|\ \le\ \frac1{|\operatorname{Im}z|}\,\|D_0F\|\,\frac1{|\operatorname{Im}w|}\cdot|T|,\tag{S7.9}$$
留数误差再乘五方向极点向量的范数（该向量即 $E_0$ 的两非零分量列）。原生留数收敛与价格一同成立。

**边界说明。**$\kappa$ 静态极限与物质 Abel 极限各自取，次序不交换；这些读数尚未识别为物理电磁耦合、电子或 Thomson 极限。

**直接使用。**留数公式 (S7.4) 与相容判据是 §6.13 的终点；模式核与 $Q(T)$ 的时间演化在 6.14 的扩散分解中复用。

**形式对应。**`alpha-source/CanonicalPreparationSource{MovingPoleCurrent,MovingPoleGaussPreparation,MovingPoleGaussVertex}.lean`、`CanonicalPreparationSourceStaticPoleDomain.lean`（`staticTensor_generated`、`paddedStaticInverse_{left,right}`、`normalizedKernel_isUnit`、`normalizedKernel_inverse_price`、`staticRadius_pos`、`staticDomain`）、`CanonicalPreparationSourceStaticOriginalGreen.lean`（`staticNativeField_{uncleared,whole}`、`staticDomain_nonempty_regular`）、`CanonicalPreparationSourceStaticActualPole.lean`（`staticNativeField_{pole_factor,pole_price,residue}`、`staticResidue`、`normalizedInverse_tendsto`、`nativeEffectiveFrame_tendsto`、`actualStaticField_{whole,schur,pole_price}`、`actualOriginWeight`）、`CanonicalPreparationSourceModeCurrent.lean`（`sourceMode{Kernel,Current}_generated`、`actualOriginWeight_sourceReader`、`actualCurrent_staticResidue_modeReader`、`actualRestState_mode_charge_clock`、`sourceModeStatic{Coefficient,Residue}_generated`、`sourceModeHalfWeight_Abel`）、`CanonicalPreparationSourceFullOriginCurrent.lean`（`fullNativeOrigin`、`actual_current_ward`、`actual_effective_dynamics`、`actual_complement_return`、`actual_native_reconstruction`、`actual_forcing_twoSectors`）、`CanonicalPreparationSourceConstraint{Read,Boundary}.lean` 与 `CanonicalPreparationSourceColorBoundaryWard.lean`（`constraint114_source_linear`、`constraintUnsupported_actual{Window,Half}_zero`、`sourceActualCosource114_generated`、`sourceActualCosource114_actualWardBoundary`）、`CanonicalPreparationSourceN1{Prepared,NormalWard,Dynamics}.lean`（`sourceActualN1Primal_*`、`sourceActualCosource114_N1WardBoundary`——带 Laplace 权 $\lambda$ 的 (S7.7)、`actual{C,A,Generator,Time}_sourceN1_range`）。以上各文件在 AE 与 CAP 逐字节相同，首钉于 AE。

(1)(2) 的载体与连续性及 (4)(5) 的分解、相容与价格固定于 CAP：`CanonicalPreparationSourceMovingCarrier.lean`（`movingOverlap_right_unitary` 与逐层 `movingOverlap_*` 组合）、`CanonicalPreparationSourcePreparedTensor.lean`（`sourceTensor_generated`、`actualModeTensor_{generated,same_carrier}`）、`CanonicalPreparationSourceMomentumContinuation.lean`（`actualC_affine`、`actualC_difference_price`、`actualC_continuous`、`sourceResolvent_difference_price`、`sourceTime_continuous`、`sourceModeKernel_continuous`、`actualModeTensor_continuous`、`movingOverlap_zero`、`actualModeWindow_continuous`）、`CanonicalPreparationSourceRetainerMomentum.lean`（`sourceRetainer_momentum`、`actualA_momentum`、`actualJoint{Generator,Resolvent,Time}_continuous`）、`CanonicalPreparationSourceReaderMomentum.lean`（`rawReader_momentum_continuous`）、`CanonicalPreparationSourceFullPoleTensor.lean`（`actualAxisField_{whole,residue,coupled_residue}`、`actualAxisWindow_tendsto`——变化 forcing 的未清场极限）、`CanonicalPreparationSourceReferenceContact.lean`、`CanonicalPreparationSourceModeNativeSymbol.lean`、`CanonicalPreparationSourceModeContactRead.lean`（`sourceContactKernel`、`sourceDeviationKernel`、`sourceActualMode_contact_deviation`——(S7.6) 的接触—偏离逐点关系、`sourceDeviationReader`）、`CanonicalPreparationSource{GaussConnection,GaussKineticTorque,GaussColorWard}.lean`（色荷、协变力矩、配置力矩的 Ward 恒等式）、`CanonicalPreparationSourceNativePoleBalance.lean`（`nativeContactWindow`、`configurationDeviationWindow`、`actualOriginWeight_native`：$\mathfrak{w}=\kappa_{\rm ct}-\delta_{\rm cf}$、`origin_native_Ward_balance`、`actualOriginWeight_residue_tendsto`）、`CanonicalPreparationSourceNativePolePrice.lean`（`configurationDeviationPrice`、`actualOriginWeight_native_price`——(S7.9)、`sourcePoleVector`、`actualResidue_price`）、`CanonicalPreparationSourceAxisCompatibility.lean`（`axisCosource_{actual,tendsto}`、`axisNullCosource_tendsto`、`actualOriginWeight_cosource114`：$\mathfrak{w}=-c_{114}$、`actualAxisField_constraint_residue`、`actualAxisField_compatibility`：$H_{289}\varphi=w_{\rm win}\iff$ 九维轴零共源为零）。(4) 的原 Green 等式与 6.12(1) 共用 AC `CanonicalPreparationOriginalPreparedGreen.lean` 的 `original_green_equation`。

直接消费者：`alpha-source/AuditCanonicalPreparation{SharedPoleCarrier,FullPoleContinuation,PhysicalModeContact,PhysicalGaussColorTorque,PoleConstraintReturn}.lean`。提交 AE（静态与 Ward 主线）与 CAP（moving 载体、动量连续、极点分解、相容与价格）。

---

## S8 定理 6.14：matched 整词预算与 renormalized 端点共同尾

**对象与定义域。**完整原生历史 Hamiltonian $H_0$、其有限压缩 $C_F=H_0-d_F$（$d_F$ 为保留项）、量子测试空间 $\mathcal Q$ 上的算子（记为 End）、阻尼参数 $\sigma=\mu>0$、复合源时钟 $\varphi$。两颗种子 $(g,\rho g)$ 生成归一化状态 $w$；$A=aD$ 为根作用与 Gauss 方向之积，$U=a^2$；$D_c$ 为中心方向；$n=\sqrt{54/125}$ 为 lapse。延迟频率 $z=\mathrm{line}(\mu,t)$ 满足 $\operatorname{Im}z\ne0$。

**记号。**$R_3$ 为字面延迟整词（即源中的 matched 源整词 $R_{\rm forcing}$）；$J_3$ 为 matched 价格 $\Pi_{m,\ell,F,z}(g)=P_3(w)+12\,\mathrm{cp}(z,w,v)/n-3\,\mathrm{contact}_{\rm cf}$，其中 $P_3$ 为原生压力项（一双原生压力算子在 $w$ 上的实配对，定义见引理 S8.1），$\mathrm{cp}$ 为局部时钟价格；$\mathrm{sh}_{40}(w)=\sum_i\|\mathrm{sh}_{40,i}w\|^2$ 为 40 位移列二阶矩（$\mathrm{sh}_{40,i}$ 为位移列算子）；$\mathsf{sc},\mathsf{cf}$ 分别为标量形与余标架 Gram；$M_\mu(k)$ 为源 $\mu$ 因子，$P_\rho$ 为半径价格，$C_{\rm J}$ 为闭合联合价格，$\mathcal E$ 为 renormalized 端点，$R_{\rm df}$ 为扩散余项。

**输入与量词。**(1) 对所有 $m,\ell,F$、非实 $z$ 与域元 $g$；(2) 对每个 $\varepsilon>0$、$\mu>0$、域元 $g,k$，存在 $N$ 使**所有** $m\ge N$、$\ell\ge m$、共尾的 $F$ 与**两种**锐截断（一个布尔选择，两种取值）一致成立；(3) 同 (2) 的量词但对象换为绝对端点积分，含两个因果口（一个布尔选择）；(4) 在共尾的 $F$ 上对所有 $m,\ell,z,g$ 成立。

**关键引理。**

> **引理 S8.1（matched 正源）。**记匹配列 $C_3:=UD+3iD_cU$（$D_c$ 为中心方向），原生压力项
> $$P_3(f)=\operatorname{Re}\bigl\langle f,\bigl([A,[A,H_0]]+3U[D,H_0]+2U\,M_{\rm matter}+\tfrac85U\,V_{\rm vac}\bigr)f\bigr\rangle.\tag{S8.0}$$
> 检验子恒等式、精确相位修正与逐槽下界同时成立：
> $$\mathcal T:=C_3+2U=UD+3iD_cU+2U=UD+i\,U\bigl(3D_c+4i\bigr),\qquad J_3=R_3+6\,\sigma\,\operatorname{Im}\langle C_3w,w\rangle,\tag{S8.1}$$
> $$J_3\ \ge\ \tfrac{3n}{8}\|C_3w\|^2+\tfrac{5n}{2}\mathsf{sc}(Uw)+10n\,\mathrm{sh}_{40}(w)+\tfrac{3n}{4}\mathsf{cf}(Uw)+18n\|w\|^2,\tag{S8.2}$$
> 右端各槽非负，且 $P_3(w)\le4J_3$。

*证明要点。*检验子的两个形式经对易式 $D_cU-UD_c=2iU$（逆扩张关系）互推，是有限算子恒等式；相位修正是 $J_3-R_3$ 的逐项展开（压力项与 $U$ 交叉项的归并，由 $D$ 的生成元对易式代入）；下界由 matched 槽展开：局部时钟价格下界、标量形与余标架 Gram 的非负性、位移矩与态能量逐项非负。$P_3\le4J_3$ 是同一槽展开的推论：压力项由时钟价格与 Gram 槽的四倍控制。∎

> **引理 S8.2（共同相位付款）。** 对 $\mu>0$、$g$ 与任意 $\varepsilon>0$，存在 $N$ 使所有 $m\ge N$、$\ell\ge m$、共尾的 $F$ 与两个因果口满足
> $$\int_{\mathbb R}\bigl(J_3-2R_3\bigr)_+\,dt\ \le\varepsilon\tag{S8.3}$$
> 这是**正部**积分而非绝对值界：只付 $J_3>2R_3$ 的一侧——$J_3-2R_3$ 为负的区间不产生责任（精确形式是 $\int^{-}\mathrm{ofReal}(J_3-2R_3)\le\varepsilon$）。吸收链如下：由 (S8.1) 精确有 $J_3-2R_3=12\sigma\operatorname{Im}\langle C_3w,w\rangle-J_3$（$\sigma=\operatorname{Im}z$，实际频率上 $\sigma=\mu$）；相位价格不等式（Cauchy–Schwarz 后 Young，取 $t=\eta\cdot3n/8$ 并用 (S8.2) 的 $\tfrac{3n}{8}\|C_3w\|^2\le J_3$ 槽）给出
> $$\bigl|6\sigma\operatorname{Im}\langle C_3w,w\rangle\bigr|\ \le\ \eta J_3+\frac{24\sigma^2}{n\eta}\|w\|^2;$$
> 取 $\eta=\tfrac12$ 得 $J_3-2R_3\le2\bigl|6\sigma\operatorname{Im}\langle C_3w,w\rangle\bigr|-J_3\le\tfrac{96\sigma^2}{n}\|w\|^2$，故正部被积函数被 $K\cdot$(归一态能量) 控制，$K=96\mu^2/n$；归一响应的普通共同尾以目标 $\varepsilon/(K+1)$ 给同一 $N$，两个相位同时付清。

> **引理 S8.3（半径预算）。** 半径平方分解
> $$\rho^2=1+\tfrac{2\|\mathrm{vac}\|^2}{25}+\tfrac12\|\varphi-\tfrac{2\mathrm{vac}}5\|^2-\tfrac14\|\varphi-\tfrac{4\mathrm{vac}}5\|^2\tag{S8.4}$$
> 给出
> $$\|v_\varphi\|^2\le\Bigl(1+\tfrac{2\|\mathrm{vac}\|^2}{25}\Bigr)\|w\|^2+\frac{J_3}{20n}.\tag{S8.5}$$

*证明。*$\|\varphi-\tfrac{4\mathrm{vac}}5\|^2$ 项由 $10n\,\mathrm{sh}_{40}(w)$ 槽支付：$10n\,\mathrm{sh}_{40}\le J_3$（由 (S8.2) 各槽非负），故 $\tfrac12\mathrm{sh}_{40}\le J_3/(20n)$，代入半径恒等式。∎

> **引理 S8.4（端点共同尾）。** renormalized 第二 Green 端点
> $$\mathcal E=\operatorname{Re}\langle k,(H_0-\operatorname{Re}z)Aw\rangle-\|k\|^2\operatorname{Re}(1/z)\tag{S8.6}$$
> 在共尾的 $F$ 上只读两个原 $H_0^2g_i$ 输入（固定端点词）；其绝对全频 $L^1$ 尾有共同 $N$：$\int|\mathcal E|\,d\omega\le\varepsilon$，两个因果口同时成立。推导分两半：固定频率价格满足源生界
> $$\mathrm{fixPrice}(m,\ell,\mu,\eta)\ \le\ 4\eta\cdot\frac{\pi}{\mu}+C(\mu,\eta,g)\cdot\Sigma,\tag{S8.7a}$$
> 其中 $\frac{\pi}{\mu}=\int_{\mathbb R}\frac{dt}{t^2+\mu^2}$ 是 Lorentz 型核的质量（系数 $\frac{\pi}{4\eta\mu^3}+\frac{\pi}{4\eta\mu}$ 乘二阶源质量进入 $C$），$\Sigma$ 为固定源范数平方和。取 $\eta=\varepsilon\mu/(8\pi)$ 则 $4\eta\cdot\frac{\pi}{\mu}=\frac{\varepsilon}{2}$；再由源的四阶 jet 与 Ritt 三、四阶梯度界（常数 32、256）把 $\Sigma$ 压到 $\varepsilon/(2(C+1))$，从而 $C\Sigma\le\varepsilon/2$，合得 $\varepsilon$。

> **引理 S8.5（扩散协变）。** 扩散流 $\Gamma_L(X)=\mathcal D^{\mathsf T}X+X\mathcal D-2AXA$（$\mathcal D=A^2-3D_{\rm clk}$，$D_{\rm clk}$ 为漂移时钟算子）满足
> $$\Gamma_L(1)=0,\qquad \Gamma_L(V)=18\cdot1\tag{S8.7}$$
> （$V$ 为体积作用，$VU=I$）；噪声核 $K_t(x,y)=2\int_0^t\rho_s(x)\rho_s(y)\,ds$、$\rho_s=(V(x)+18\max(s,0))^{-1/2}$ 对每个有限点族正定；carré 保留完整交叉：
> $$\Gamma_L(X^2)-\Gamma_L(X)X-X\Gamma_L(X)\big|_{X=H_0}\ =\ 2\,\|[A,C_F]f+[A,d_F]f\|^2.\tag{S8.8}$$
> 正则化偏差 $\|A-\mathcal D_t\|^2$ 有共同付款 $(192t/n)J_3$ 与同量词的全频尾。

**决定性推导。**(1) 是引理 S8.1。(2) 把三条预算组合：锐截断下的半径响应价格预算（$C_{\rm J}\le\varepsilon/2+C\cdot(\text{齐次项}+4\,\text{相位预算})$）、齐次半径预算（$\delta$）与共同相位付款（$\delta$，其 $\varphi$ 响应预算形如 $\delta+2(\mu/(20n))\int R_3^{\,+}$）；相位误差经引理 S8.3 的 $J_3/(20n)$ 因子换成 matched 整词正部积分 $\int R_3^{\,+}:=\int(R_3)_+\,dt$（源形式为 $\int^{-}\mathrm{ofReal}\,R_3$），系数
$$C\cdot5\delta+4C\cdot\bigl(2\,\mu/(20n)\bigr)\cdot\int R_3^{\,+}\ \longrightarrow\ \varepsilon+48\,M_\mu(k)\,P_\rho\,\frac{\mu}{20n}\int R_3^{\,+}\tag{S8.9}$$
（取 $\delta=\varepsilon/(10(C+1))$、$C=6M_\mu(k)P_\rho$，系数恒等式 $4C\cdot2\mu/(20n)=48M_\mu(k)P_\rho\cdot\mu/(20n)$ 逐项核对：$4\times6\times2=48$，与 `actual_original_native_matched_Gamma_budget` 的右端一致）。(3) 是引理 S8.4。(4) 由引理 S8.5 与字面展开：在共尾的 $F$ 上
$$R_3=\frac{\mathcal E}{\sigma^2}-\frac{D_{\rm ren}}{2\sigma^2}+R_{\rm df},\qquad D_{\rm ren}=W_{C_F}^{(2)}-2\|v_{\rm fix}\|^2\operatorname{Re}(1/z),\tag{S8.10}$$
其中 $W_{C_F}^{(2)}$ 为二阶 $C_F$ 整词、$v_{\rm fix}$ 为固定列。同款的扩散源价格经相位恒等式恰为 matched 价格：$\Pi_{\rm df}=R_3+6\sigma\operatorname{Im}\langle C_3w,w\rangle=J_3$（即电力整词形式 $W_{\rm elec}+6\sigma\operatorname{Im}\langle C_3w,w\rangle$），不是 $R_3$ 本身。

**边界说明。**(2) 是对给定两种锐截断与原源责任的预算，不是完整 $C_F$ 半群结论；$D_{\rm ren}$ 与 $R_{\rm df}$ 是 $R_3$ 中由各自消费者结算的部分。

**直接使用。**(1) 的 matched 价格是 (2)(4) 的统一天平；端点尾 (3) 使 §6.9 末的正测度在复合源时钟上有对应的全频收敛。

**形式对应。**`external-composite-decay/SourceClockPhiNativeMatchedSource.lean`（`matchedColumn`、`matchedTester`、`matchedPrice`、`matchedForcingWord`、`actual_native_matched_source`、`actual_native_matched_common_payment`）、`SourceClockPhiNativeMatchedGammaBudget.lean`（`radius_shifted_norm`、`actual_original_native_matched_radius_budget`、`matchedBudget`、`actual_original_native_matched_Gamma_budget`）、`SourceClockPhiRenormalizedSecondGreen{,Tail}.lean`（`renormalizedEndpoint`、`actual_renormalized_fixed_source`、`actual_renormalized_endpoint_absolute_common_tail`）、`SourceClockPhiMatchedDiffusionSource.lean`（`diffusionDrift`、`diffusionCurrent`、`noiseKernel`、`diffusionRemainder`、`original_matched_diffusion_covariance`、`fixedEndpointWord`、`actual_matched_diffusion_source`）、`SourceClockPhiFixedSourceJets.lean`、`SourceClockPhiRittHigherGradient.lean`。提交 AE；依赖闭包中经 `SourceScalarEssentialBudget.lean` 使用的原几何体时间预算 `SourceGeometricBulkTimeBudget.lean`（`actual_original_geometric_budget`）不在 AE 提交中，其字节保存在 Homework `fa15016c…`（见正文附录 D.7）。

---

## S9 命题 9.1–9.3 与 §9.2 的公开实验证据

每款按正文表 4 的三类身份分开陈述：**数学**（源内形式定理，给证明）；**双实现核验**（两套互不共享前向计算的程序，各产冻结首回执后交叉核对）；**统计合同**（预先登记错误预算的随时检验，给检验统计量、预算与判据）。未在款内标注身份的历史数字按 §9.2 原冻结身份保留；本节不重新运行任何事件流或拟合。

### S9.1 命题 9.1：光学完整源域与联合 95% 严格正 CH

**对象与定义域。**NIST 2015 公开计数的条件源族：坐标 $(m,z,x,r,e)$ 描述同一两偏振 TMSV、共同实 Jones 框架与标量损耗；$k=(1-2\lambda)T$ 保留逐脉冲相位混合；训练口径是六个置信区间（四个 single、两个 joint）。

**(1) 完整源（数学）。**

> **命题 S9.1a（相位纤维）。** 合法原始源的共同符号常数 $k$、物理平方界与全部训练 slab 成立，当且仅当存在合法相位 $\lambda$ 与快照——即从原生源与合法 $k$ 内部生成，不由调用者提供。
>
> *证明要点。*“当且仅当”的两向分别是消元与重构：正向把训练区间翻译成对 $k$ 的线性约束与平方界；反向由 $k$ 反解 $\lambda=(1-k/T)/2$ 并逐项核对该 $\lambda$ 落回原合法域，快照的每格计数由同一源生成。∎

> **命题 S9.1b（均值图）。** 四个实际均值恢复共同协方差坐标 $(m,z,x,r)$；全部 single 区间当且仅当八个半空间的交。严格增序生成 $z>0$、$R^2>0$。
>
> *证明要点。*四均值是坐标的线性读出，可逆性由系数矩阵显式行列式非零给出；每个 single 区间对坐标是一对半空间，四个给出八个。∎

> **命题 S9.1c（协方差源）。** 任意正规五元组（$z>0$）与合法 $k$ 自产 $\arctan$ 共同轴、原 RawSource 与合法相位，并精确读回五坐标与全部格/五脉冲窗口；纯模边界 $n_V=0$、$T=0$ 与全部 $\lambda$ 读出等价保留。
>
> *证明要点。*轴由 $\arctan$ 从 $(x,r)$ 生成；$T$、两强度由 $m,z$ 与透射关系反解；读回是逐坐标的代数恒等式。∎

**(2) 端口与无限 Born（数学）。**

> **命题 S9.1d（环境端口）。** 实际偏振作用保持 $\mathrm{Pol}\otimes\mathrm{Env}$；六端口对任意 $T_H,T_V\in[0,1]$ 与 $|\xi|\le1$ 生成全部 $n$ 的效果 $\Gamma_n=O^\dagger X^{\otimes n}O$；$\xi=1$ 恢复原始全 $n$ 的 $\Gamma$；两环境分量不可由旧占据 $\Gamma(R)$ 代替。
>
> *证明要点。*端口作用是两模式幺正的原生符号实现；$\Gamma_n$ 是按占有数的逐块恒等式，正性由效果作为压缩给出；$\xi=1$ 代入即原 $\Gamma$。∎

> **命题 S9.1e（matched 无限 Born）。** matched 情形的完整无限 Born 联合概率为
> $$Q_{AB}=\frac{1}{1+n_V\,(T_A+T_B-T_AT_B)}.\tag{S9.1}$$
>
> *证明要点。*逐扇区 Born 项由实际源根与 $D$ 生成（保留复相位与扇区质量预算），对全部 $n$ 求和是几何级数，分母即 $1+n_V(T_A+T_B-T_AT_B)$。∎

**(3) 统计纤维与正负成员（双实现核验）。**六训练区间各自可在完整区间内变化；两棵独立覆盖树（主、独立实现）各逐项重算 **81,922 个节点**，支付初始全域、每次区间收缩的外侧性、完整划分、排除依据及全部封顶与边界段——主保留 15,061 块、独立保留 11 块。512 个成员各自从原生配方重生：主 256 个 Gaussian 包络全含、独立 256 个实际 Born 包络全含；**141 项实际 Born 越界反证**（主 47、独立 94）统一包含留出——例如独立第 6 号成员的 $j_{01}\approx0.00016726781197301952$ 严格高于原上界 $0.00016712361973910759$；这些源满足全部六训练 CI，故训练约束不蕴含全部留出落带，而整个源族没有被拒绝。

十二个 CI 的全数据交集 $F_{\rm all}=F_{\rm train}\cap$全部公开留出 CI 上，另 81,922 节点与 128 成员的验收给出：每条路径 **64 个实际 $\Gamma$/Fock 源**满足全部十二项精确 CI 与完整结局，其中 **41 个严格正 CH、23 个严格负 CH**；具体符号证人反证整个 $F_{\rm all}$ 的统一严格正与统一严格负（域的符号证书登记为两号混合）。**这是条件相容源族的回顾性核验，不是实际装置配置的识别，也不是盲态验证。**

**(4) 联合 95% 域（统计合同＋数学内核）。**原 $1/20$ 联合预算内，消费实际设置曝光、完整四结局与源生成的精确归一化支持函数
$$h=\ell\cdot\mathrm{CH}-\varepsilon(1-\varepsilon)\min(c^{A}_{01},c^{B}_{10},c_{11}),\qquad d_k=1+2^{-k}h,$$
$$\log E_k=W_{\rm obs}\log a_k+L_{\rm obs}\log b_k-T\log d_k.\tag{S9.2}$$
其中 $c^{A}_{01}$、$c^{B}_{10}$、$c_{11}$ 分别为 A 侧 01 结局、B 侧 10 结局与联合 11 结局的计数。
安全旧失败界为 $3/(80\times32767)$；总预算 $1/20$ 扣除该失败界后等分给 24 项完整曝光 contrast 族与 $24\times4\times6\times40$ 个条件方向 bet。源内核自产精确支持顶点、$d_k$ 正性与一步期望界（`NormalizedSourceBet.lean`）；统计交叉证书逐项核 576 个新区间、23,040 个方向 bet、480 个原 fixed-bet 基础值与 24 个有理反演括号。新联合 95% 接受域非空：**8 个原 $\Gamma$/Fock 物理成员**同时满足旧 72 CI、新 96 项条件约束与四项联合 source cut，完整连续外覆盖成立，且**每个**接受源满足
$$\mathrm{CH}_{N5}>1.3790180504\times10^{-6}\tag{S9.3}$$
（精确有理下界由证书保存；两个统计首分别冻结于 `5a35416ec6` 与 `85d5b45efa`）。

**(5) 公开审查（统计合同）。**24 项公开 spacelike 源签名族在 $\alpha=0.05$ 下家族上界约 $0.00241643$；具名环境校准名义模型的整个连续名义域与原置信区间严格不交；r6/r6.1 十九个源的五个公布控制全部偏离（该判决保持原合同身份，不解释为新的 Bell 计数检验）。

**直接使用。**(1)(2) 的源域与端口是 §9.2 观测生成切片的源内核；(3)(4) 的成员与接受域被命题 9.1 正文直接引用；(5) 是 §9.2 公开审查入口。

**形式对应。**AD：`nist-real/nominal-replay/observable-closure/full-statistical-fiber/`（`PhaseFiber.lean`、`TrainingChart.lean`、`CovarianceSource.lean`、`CovarianceSourceCertification.lean`、`PhaseCertification.lean`；核验回执 `cross-verification.json`、`all-data-verification.json`、`all-data-sign-certification.json`、`criterion.md`、`criterion-all-data.md`）、`environment-source/`（`MatchedSource.lean`、`EnvironmentSource.lean`、`SectorSource.lean`；`criterion.md`）、`public-review/source-compression/`（`NormalizedSourceBet.lean`；回执 `statistics-cross-verification.json`、`kernel-certification-first.json`、`domain-verification.json`、`source-compression-verification.json`）与 `public-review/`（`complete-review*.json`）。提交 AD。本次未重新运行覆盖、成员生成或统计验收。

### S9.2 §9.2 的其余 NIST/Storz 公开实验结果

**(a) Storz 名义锁（既有冻结统计合同）。**ETH 数据 [8,9] 前 100000 行试次按冻结规则读取；在 $\alpha=0.025$ 下零半径模型被拒绝：最大 $\log E=46803.6234$，独立高精度回执 $p_{\rm any}\approx2.783760711\times10^{-20327}$（原 JSON 的 `0.0` 为浮点下溢）。半径 $0.01,0.02,0.05$ 仍拒绝，$0.1,0.2$ 未拒绝。相位桥缺口（控制映射代入原 CHSH 符号定义得 $S=0$）使底层源理论的单独判定保持**不可裁决**。

**(b) NIST 名义重放 r0003（双实现核验）。**名义模型按 §9.2 的固定选择（归一化 $|HH\rangle+r|VV\rangle$ 族、镜像角、效率乘积联合计数、逐试次背景、CH 型组合）；效率半宽预先冻结为概率 $0.003$。中心与 16 角点的数值最优构成预先声明的带，加宽 $\pm0.05^\circ$、$\pm0.0005$ 后为
$$r\in[0.3051567847356201,0.3257119970321657],\quad \theta_0\in[4.727559269219637^\circ,5.179646420478821^\circ],$$
$$\theta_1\in[-27.552833724021912^\circ,-26.90090064406395^\circ].\tag{S9.4}$$
中心为 $(0.315463895,\,4.954737358^\circ,\,-27.232869633^\circ)$。文档五值 $r=0.2872$、$\theta_0=4.2^\circ$、$\theta_1=-25.9^\circ$ 及两个 Bob 镜像角全部落在带外（主实现判定 `REPLAY_DEVIATION_EXCEEDS_PREDECLARED_BAND`，独立实现同判）。这是冻结输入下名义模型的最优点判定，不是新的 Bell 事件检验，不撤销原实验结论。

**(c) Table S-II 条件源成员（双实现核验）。**四格全计数（五脉冲窗，$N=177{,}358{,}351$，保留无点击结局）上以 00、01、11 三格训练全 Fock 源、第四格留出：12 个概率包络全部落在同时平均概率域内——公开计数上的条件相容成员，不是实际装置配置的识别。

**(d) AC 观测生成源切片与 Bob 两角更新（双实现核验＋Lean 消费者）。**修订切片只从 00、11 两格取四个 single 与 joint00 中心，joint11 放回原置信区间，01、10 两整格留出。两个独立覆盖构造各产出 **69 段**：32 全合法、35 排除、2 边界，68 个划分切、无缺段重段、无封顶段。合法外侧区间 $\eta_A\in[0.7411896212237604,\,0.7414274323892578]$；规范有理成员 $\eta_B\approx0.76465288593$、$\lambda\approx0.00409579367$，两规范成员的 12 个数学概率都在原 CI 内，全切片两个留出格的预测包络也落在留出 CI 内：
$$\text{01}:\,[0.00015821397237,\,0.00015855716089],\qquad \text{10}:\,[0.00015026944774,\,0.00015053199993].\tag{S9.5}$$
保持同一源与训练相位，两独立导数体系在四角各 $\pm0.05^\circ$ 完整舍入盒上给出 **Bob 两角同时减 $0.01^\circ$** 的严格有限更新（更新角 $(4.2,-25.9,-4.21,25.89)$，共同方向、步长 $1/100$ 度）：主实现共同增益下界 $\approx1.99\times10^{-9}$、独立实现 $\approx1.69\times10^{-9}$、独立 Fock 端点增益 $\approx3.8493\times10^{-9}$。Lean 消费者（`ObservableClosure.lean`、`ClosureConsumer.lean`、`ScalarFiber.lean`、`ScalarFiberConsumer.lean`）把切片读回为源族对象。**这是一条一维具名切片上的条件相容结果**：不主张完整六维统计纤维、不识别实际硬件驱动、不恢复装置最优点。

**形式对应。**AB：`nist-real/nominal-replay/{criterion-r0003.md,replay-r0003.json,independent_replay-r0003.json}`；AC：`observable-closure/{criterion-ef0002.md,verification.json,slice-primary.json,independent-slice.json,cross-receipt.json,receiver-criterion.md,receiver-verification.json}` 与四枚 Lean 消费者（见上）。提交 AB、AC。

### S9.3 命题 9.2：零经验输入预测、完整原子读出域与同律参数

**对象与定义域。**Rosenfeld 等人原子 Bell 实验 [11] 的读出模型：Bloch 探针由 $(\mu,u,z)$ 参数化——$\mu$ 为增益、$u$ 为 Bloch 向量部分、$z$ 为偏置；效果 $E_\pm$、概率 $\Pr_\pm$；XZ 轴设置。

**(1) 预测锁（数学）。**

> **命题 S9.3a。**原源对全部合法 XZ 轴生成概率族与统一界 $|S_{\rm CHSH}|\le2\sqrt2$；固定正交轴与归一角平分线自产 32 格精确预测，达到 $2\sqrt2$。构造器不含数据、器件或校准参数。
>
> *证明要点。*上界的实际证法是显式 Cauchy–Schwarz：把 $S_{\rm CHSH}$ 写成两个四维向量 $u=(\pm a_0^x,a_0^z,a_1^x,\pm a_1^z)$ 与 $v=(b_0^x+b_1^x,b_0^z+b_1^z,b_0^x-b_1^x,b_0^z-b_1^z)$ 的内积，两轴的单位性给 $\|u\|^2=2$、$\|v\|^2=4$，故 $S_{\rm CHSH}^2\le8$，开方得 $|S_{\rm CHSH}|\le2\sqrt2$（对两个 herald 符号统一成立）。32 格预测是四结局×两站×四设置的逐格代数值，满足归一、非负、$\tfrac12$ 边缘与对齐性；取到 $2\sqrt2$ 由固定轴（对角方向 $\pm1/\sqrt2$）代入 CHSH 公式逐格计算。∎

**(2) 完整读出域（数学）。**

> **命题 S9.3b（往返）。**任意合法二元读出通道（含负或零增益）与 XZ 轴生成紧效果 $(\mu,u,z)$；反向由半径与源锥生成合法通道与轴，往返精确；四个效果给 12 个实坐标的完整域。
>
> *证明要点。*正向是效果矩阵的 Bloch 分解（紧性由系数有界给出）；反向由半径条件保证构造出的矩阵是合法量子效果、源锥条件保证轴合法；两向复合逐分量恒等。∎

**(3) 全部试次（统计合同）。**Munich 两次运行的 10,201 与 10,202 个有效配对保持原序；检验为前缀最大似然比（随时 $e$-值）对理想零误差面：April 在第 **3974** 条首次越过阈值 40（最大 $E\approx494.849935$）而被拒绝；完整读出域在两次运行各有一枚精确原始证人，全部 20,403 条前缀严格低于 40（April 最大 1，June 约 1.338729277）；两运行的联合随时预算为 $1/20$。

**(4) 同律与纤维（数学）。**

> **命题 S9.3c。**两套合法设置族给出同一概率律，当且仅当四个偏置与两组 X/Z 乘积矩阵相等——全域的最大观测商；在正则范围内，同律效果恰为唯一非零 $(s,t)$ 的合法反向尺度。
>
> *证明要点。*“仅当”：概率等式在全部输入上成立迫使两族逐坐标读出相等——偏置由常数项读出，乘积矩阵由二次项读出；“当”：相同参数生成相同律。尺度的实际结构：正则性给 $a_0^u b_0^u\neq0$ 与 $a_0^z b_0^z\neq0$，乘积矩阵相等经秩一分解（带非零锚点的逐行逐列因子化）把另一侧的全部 $u$ 坐标写成 $s$ 倍、全部 $z$ 坐标写成 $t$ 倍，对侧按 $1/s,1/t$ 反向；目标效果合法当且仅当 $(s,t)$ 满足源锥的合法尺度条件，此时另一族恰由尺度变换生成；尺度唯一——$s$、$t$ 由正则锚点坐标的比值显式恢复，任何生成同一族的 $(s',t')$ 必与之相等。故在正则范围内，**每个同律效果是某个唯一非零 $(s,t)$ 的合法反向尺度**。∎

**(5) 响应界（数学＋双实现核验）。**整个原置信域上全部有效增益至少 $0.36579$，两类规范误率都低于 $0.37916$：界由源内响应公式给出（数学部分），全置信域的逐点核验由两套独立实现完成（双实现核验）。

**直接使用。**(2) 的读出域与 (4) 的同律商是命题 9.3 的全部输入；(3) 的证人域被 9.3(1) 的联合增益上界消费。

**形式对应。**`Bell/TheoryBlind.lean`（预测锁、CHSH 界、32 格）、`Bell/ReadoutEffects.lean`（效果往返）、`Bell/ReadoutIdentification.lean`（同律、纤维、唯一尺度）、`Bell/ReadoutResponseBounds.lean`（响应界）；`munich/`（`README.md`、`criterion-mu0001.1.md` 及 `readout-domain/` 的 `parameter-recovery.md`、`history-source.md`、`verification.json`、`identification-verification.json`、`response-projection-verification.json` 等回执）。提交 AD（Lean 入口）、AE（Munich 消费者）。

### S9.4 命题 9.3：硬件逆、脉冲可实现像与原后测历史

**对象与定义域。**同 S9.3 的读出域；探测器效果 $E_{\rm click}=dI+kJ$、$k=(1-d)\eta$；Garthoff 的原 12 态矩阵、18 个自然跃迁与 7 个电离通道生成 GKSL 动力学；有限矩形脉冲。

**(1) 联合增益上界（双实现核验）。**同一全前缀联合域给出 8 个跨设置增益乘积上界与 6 条最大射线界：April 的最大增益 $>0.67020$、每侧 $>0.44918$；June 分别 $>0.66386$、$>0.44071$。两套实现各自产生冻结首回执后交叉一致。

**(2) 两探针唯一逆（数学）。**

> **命题 S9.4a。**在已识别的正则完整律上，两个源已知的独立 Bloch 探针的带符号响应与非零识别行列式给出两侧逆，恢复全部族坐标，效果族唯一；探针可来自不同设置，零行列式另有反例。
>
> *证明要点。*探针响应是族坐标的线性读出；两探针的响应矩阵行列式非零时，克莱默法则给两侧逆并逐项恢复坐标；唯一性由任何同律效果给出相同响应、逆像唯一。零行列式时线性系统欠定，显式反例给出两族共享全部响应。∎

**边界说明。**两探针唯一逆需要独立制备的探针输入；原 2021 论文 [13] 的名义设置与 AOM 通道身份不代付这一输入。

**(3) 探测器纤维（数学）。**

> **命题 S9.4b。**$E_{\rm click}=dI+kJ$、$k=(1-d)\eta$；对正增益，全部合法 $(d,k)$ 恰满足
> $$0\le d\le m,\qquad M-d\le k\le1-d,\tag{S9.6}$$
> 其中 $m=(1-\mu-g)/2$、$M=(1-\mu+g)/2$ 为效果点击概率的最小、最大值；逆原子唯一，且 $\eta\,\lambda_{\max}(J)\ge\dfrac{2g}{1+\mu+g}$。
>
> *证明要点。*$d$ 的界是暗计数率的物理范围；$k$ 的上下界由效果 $0\le E_{\rm click}\le I$ 在 $J$ 的谱上逐特征值翻译——谱最小端给下界 $M-d$、最大端给 $1-d$；逆原子唯一由 $E$ 的 Bloch 展开系数唯一恢复 $(d,k,J)$；效率下界把 $\eta=k/(1-d)$ 代入谱端条件整理即得。∎

**(4) 原子前向与脉冲像（数学＋双实现数值前向）。**本款分两种证据身份，不合并陈述。

*数学（源内 Lean 定理）。*
> **命题 S9.4c（可实现性刻画）。**对正增益效果与具名谱，记 $b,d$ 为谱的亮、暗率，$\gamma=b-d>0$ 为谱隙：脉冲可实现当且仅当两条源内平方不等式成立
> $$(u^2+z^2)(b+d)^2\le(1-\mu)^2\gamma^2,\qquad (u^2+z^2)\bigl(2-b-d\bigr)^2\le(1+\mu)^2\gamma^2,\tag{S9.7}$$
> 等价地当且仅当生成的背景率与速率因子构成合法速率；可实现时，由该谱与生成的轴造出的原子效果经探测器后逐坐标等于原效果（背景率 $<1$、效率 $\in(0,1]$）；两个不同的可行谱可实现同一效果而原子不同。这是可实现性的“当且仅当”刻画，不涉及半群存在性。
>
> *证明要点。*可实现性按定义是背景与探测器两条余量不等式；把速率因子 $g/\gamma$ 代入并乘 $\gamma$，两条余量恰好配成 (S9.7) 的两条平方不等式（两边均非负方可平方等价）；实现的效果逐坐标展开即回原 $(\mu,u,z)$；谱可由效果的最大/最小原子读数恢复，故原子层面区分不同谱。∎

> **命题 S9.4d（面积上限）。**在探测器速率合法（$\mathrm{Rates}\,d\,k$）、实现关系 $\mathrm{Realizes}$、背景 $d<1$、偏置界 $|\mu|\le B$、效率上界 $0\le\eta_{\rm up}\le1$ 且 $\eta\le\eta_{\rm up}$、面积平方上界 $0\le A_{\rm up}$ 且 $\mathcal A^2\le A_{\rm up}$，以及**前向不等式** $p^{\rm at}_{\max}\le7\mathcal A^2/4$ 全部成立的条件下，
> $$g\ \le\ \min\Bigl(1,\ \frac{(1+B)\,\eta_{\rm up}\,\bar a}{2-\eta_{\rm up}\,\bar a}\Bigr),\qquad \bar a=\min\Bigl(1,\frac{7A_{\rm up}}4\Bigr),\tag{S9.8}$$
> 其中 $\mathcal A=\int\Omega_{12}\,dt$ 为无量纲读出 Rabi 面积，$p^{\rm at}_{\max}=(1+\mu_{\rm at}+g_{\rm at})/2$ 为原子效果的最大点击概率。前向不等式本身是数值前向的结论（下段），不是本定理的前提内部结论；本定理在给定此前向不等式时给出增益上限。
>
> *证明要点。*原子读数上界：$p^{\rm at}_{\max}\le\min(1,7A_{\rm up}/4)=\bar a$（原子增益 $\le1$ 与前向不等式、面积上界合成）；于是效率×原子积 $\eta\cdot p^{\rm at}_{\max}\le\eta_{\rm up}\bar a\le1$；代入乘积上界定理（raw_product_cap_gain：$\eta\cdot p^{\rm at}_{\max}\le c\le1$ 时 $g\le\min(1,(1+B)c/(2-c))$）即得 (S9.8)。∎

*双实现数值前向。*Garthoff 的原 12 态矩阵、18 个自然跃迁与 7 个电离通道 [12] 的 GKSL 前向由两套互不共享前向计算的程序各自模拟，给出：(i) 命题 S9.4d 所消费的前向不等式 $\mathrm{gain}\le\min(1,7\mathcal A^2/4)$（固定图模型的 `source_inequality`，主实现与独立实现回执一致）；(ii) 各运行各侧最大读出 Rabi 面积及其平方的严格下界（如 2016-04-15 均匀射线 $\mathcal A^2>46056427315/120259084288$、$\mathrm{gain}>46056427315/68719476736$）；(iii) 四个具名脉冲在两次运行×四个角色的 32 个域上都可实现，六组严格不同的原子响应仍给同一联合概率与全部前缀因子（逐域回执）。注意回执同时登记 `atomic_response_forward_model_kernel_proved=false`：12 态前向模型本身是双实现数值核验，不是内核定理——这正是本款两种证据身份分开陈述的原因。

**(5) 完整历史与后测时钟（数学＋双实现核验）。**

> **命题 S9.4d。**原源、第 10 次访问与 16→17 运行步的完整历史保持当前、后继与全部已安装输出；完整历史纤维的每一步由完整观察唯一决定；原写入器、整账与已安装投影逐项认回，当前场与下一字段都是原配置，tick 限制保留。
>
> *证明要点。*逐步归纳：每一步的完整观察唯一确定该步状态与后继；原记录的字段由写入器定义逐条生成；当前/下一字段的原配置身份与 tick 限制是逐条投影恒等式。∎

两个独立解析器恢复 41,673 条本地记录的九个原字段与 867 条未配对记录（双实现核验，解析字节级回执）；原记录时钟另登记 41,603 个正间隔、66 个零间隔与 4 个右删失末端，有序两时钟承诺保同一历史。

**直接使用。**(2)(3) 的逆像与纤维是 §9.3 精确尺度等价的载体；(4)(5) 把读出接到原子硬件与原历史，供 §9.2–9.3 的边界句引用。

**形式对应。**`Bell/ReadoutAnchors.lean`（`BlochProbe.{response,probability}`、概率非负与归一、`recoveredU`、`recoveredZ`、`same_law_two_probes_unique`、`anchored_same_occurrence`、`same_law_split_probes_unique`）、`Bell/ReadoutDetectorFiber.lean`（`click_bounds`、`click_gap`、`max_atomic_bounds`、`feasible_iff_rates`）、`Bell/ReadoutPulseRealization.lean`（`realizationRates`、`realization_background_lt_one`、`realization_efficiency`、`pulse_realizes`、`feasible_gap_lower`、`realized_effect_eq`、`atomic_effect_injective`、`two_spectra_same_effect`）、`Bell/SourceHistory.lean`（`next_generator`、`whole_history_read`、`history_frontier`、`whole_common_read`、`full_observation_event`、`constructor_code_faithful`、`complete_history_fibre`、`full_observation_determines_step`、`complete_model_determines_step`、`original_{writer,whole_ledger,installed_projection,entry,successor_entry}`、`current_field_is_original_configuration`、`next_field_is_original_configuration`、`original_{tick,next_tick}_restriction`）；`munich/readout-domain/` 回执（`shared-response-verification.json`、`fiber-verification.json`、`pulse-realization-verification.json`、`atomic-forward-verification.json`、`detector-fiber-verification.json`、`history-verification.json`、`clock-verification-cl0001.json`）。提交 AE（Lean 与 Munich 消费者）、AD（`Bell/TheoryBlind.lean`、`Readout{Effects,Identification,ResponseBounds}.lean`）。

---

## S10 首发主张与证明位置表

选集编号与公开代码选集的首发映射（H0mework `docs/first-release-map.json`）中的 `phys.Pn` 一致，供逐条复核。P1–P22 的书面证明在正文对应节与附录（位置按选集的 `text_location`）；P24–P36 的书面证明在本补充与正文证明思路，回执身份见附录 D.8。

| 选集编号 | 正文结果 | 书面证明 | 固定提交 |
| --- | --- | --- | --- |
| phys.P1 | 总链实际生成（构造 4.1；定理 8.3） | 正文 §4、§8；附录 C.8 | H |
| phys.P2 | 完整经典世界及唯一性（定理 4.2–4.4） | 正文 §4；附录 A、B | H |
| phys.P3 | 早期物质接回实际场（命题 2.5） | 正文 §2.5；附录 A.3 | H |
| phys.P4 | 经典—量子配对等式（定理 6.2） | 正文 §6.1–6.2，式 (6.1)–(6.2) | H |
| phys.P5 | 电流、动能负荷、输运与外幂余项（定理 6.3、命题 6.4） | 正文 §6.3–6.4；附录 B.4 | H |
| phys.P6 | 完整表示、全事件与宏后继（定理 8.3） | 正文 §8；附录 C.8 | H |
| phys.P7 | 全时规范—Dirac 轨道（定理 7.1） | 正文 §7.1–7.2 | H |
| phys.P8 | 解析预测与 Bell 概率族（定理 7.3、命题 7.4） | 正文 §7.3–7.4、§9.2；附录 D.4 | H |
| phys.P9 | 任意物理源家族形成（定理 8.1） | 正文 §8；附录 C.2 | H |
| phys.P10 | 任意源的完整经典—量子实现（定理 8.1） | 正文 §8；附录 C.8 | H |
| phys.P11 | 完整源路径与自主程序（定理 8.2） | 正文 §8；附录 C.3 | H |
| phys.P12 | 量子时间导数恢复轨道能量（定理 7.2） | 正文 §7.2 | H |
| phys.P13 | 生成几何进入实际作用（命题 2.3–2.4、3.3） | 正文 §2.3–2.4、§3.3；附录 B.3、B.6 | H |
| phys.P14 | 辅助场精确有符号消元（定理 3.2） | 正文 §3.2；附录 B.2 | H |
| phys.P15 | clock–B 耦合与非零反馈（构造 5.1、定理 5.2–5.4） | 正文 §5.1–5.4 | H |
| phys.P16 | 标准 Fock 保持（定理 6.5、例 6.6） | 正文 §6.5–6.6；附录 D.3 | H |
| phys.P17 | 完整物质作用由母材料形成（定理 C.1） | 附录 C.5 | H |
| phys.P18 | 完整联合载体与非零反馈（命题 C.2） | 附录 C.6 | H |
| phys.P19 | 全历史全阶紧域界（定理 4.5） | 正文 §4 | H |
| phys.P20 | 母法则完成与连续过程表示（命题 C.3） | 附录 C.7 | H |
| phys.P22 | 固定母源完整实现（定理 8.4、推论 8.5） | 正文 §8；附录 C.9 | F |
| phys.P24 | NIST 2015 名义重放 r0003（§9.2；附录 D.4.6） | S9.2(b)；附录 D.4.6 回执 | AB |
| phys.P25 | 公开计数条件源成员（Table S-II，§9.2） | S9.2(c) | AB |
| phys.P26 | 定理 6.7–6.10 与 §6.9 末（完整量子构造） | S1–S4、S3 末；正文 §6.7–§6.10 | AB（6.7(1)(2) 载体另按 `85cb5386…`、`f9b73392…`、`6726f385…`、`eec031c4…` 四枚较早提交，见 S1） |
| phys.P27 | 定理 6.12(1) 原完整 289 Green 进入真有限窗场反馈 | S6(1)；正文 §6.12 | AC（反馈场算子与半轴版本在 AE） |
| phys.P28 | §9.2 观测生成源切片与同源接收更新 | S9.2(d) | AC |
| phys.P29 | 定理 6.11 母作用认回同一个 $H_{289}$ | S5；正文 §6.11 | AD |
| phys.P30 | 定理 6.12(2)–(4) 完整时间支付半轴、谱轴、实际变背景 | S6(2)–(4)；正文 §6.12 | AD（(2) 的半轴消费文件与指数尾部分在 AE） |
| phys.P31 | 命题 9.1 光学完整源域与联合 95% 严格正 CH | S9.1；正文 §9.2 | AD |
| phys.P32 | 命题 9.2(1)(2)(4)(5) 预测锁、读出域、同律尺度、响应界 | S9.3；正文 §7.4、§9.2 | AD |
| phys.P33 | 定理 6.12(5) 实电流算子与源生双逆＋定理 6.13(3)–(5) 静态留数、约束相容、原点权重 | S6(5)、S7(3)–(5)；正文 §6.12–6.13 | AE（静态主块、极点分解、Ward 主线）；6.13(4)(5) 的相容判据、接触—偏离分解与价格在 CAP |
| phys.P34 | 定理 6.14 matched 原 $\Gamma$ 整词全频预算与端点共同尾 | S8；正文 §6.14 | AE |
| phys.P35 | 命题 9.2(3) 与命题 9.3 硬件逆、脉冲可实现像、原后测历史 | S9.3(3)、S9.4；正文 §9.2 | AE（Lean 入口与 Munich 消费者） |
| phys.P36 | 定理 6.13(1)–(3) 同源 moving 载体、动量连续与变 forcing 场极点 | S7(1)–(3)；正文 §6.13 | CAP（静态分解与 (S7.3) 的基础文件在 AE 与 CAP 逐字节相同） |

“形式对应”中的路径前缀：`alpha-source/` 指 `Verification/physics/low-energy-phenomenology/alpha-source/`，`external-composite-decay/` 指 `Verification/physics/low-energy-phenomenology/external-composite-decay/`，`Bell/` 指 `Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/`，`nist-real/` 指 `Verification/physics/stage10/independent-bell/nist-real/`，`munich/` 指 `Verification/physics/stage10/independent-bell/munich/`。提交别名与 blob 记录见 `checks/first-release-source-audit.json`。
