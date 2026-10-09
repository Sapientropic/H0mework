# 原局域余弦规范场的全时间响应

这是源程序与解析构造胶囊，消费同一原作用、原 E0η1 波包、原物理时间和既有
`PacketGaugeNoise`／`PacketGaugeDynamics`。本包生成

\[
 A_\varepsilon(x)=\mathrm{actualA}(x)
       +\varepsilon\cos(q\cdot x)\,dx^1S_{01},\qquad \varepsilon\in\mathbb R,
\]

的真实发展、电流参数导数、完整双时间中心化 Gram 及其正阻尼双 Laplace 导数。
源矩阵与有限消费者由 `source.py` 精确支付，连续算子与积分证明写在下文；没有新增 Lean 声明。
本轮是原根下的 subordinate producer，不改 root、current、whole ledger 或准备态。

## 原源、空间与时间

令 \(N=3\sqrt{30}/25\)、\(c=N\sqrt2=6\sqrt{15}/25\)。实际外场与输出动量固定为

\[
 k_{\rm in}=\sqrt2(21/13844480,9/1730560,119/22151168),\quad
 q=k_{\rm in}/2,\quad k_{\rm out}=3k_{\rm in}/2.
\]

它们由已签原 circle 的 \(\rho=1/131072\) 生成；\(|k_{\rm in}|=\sqrt2\rho\)。
以下物理相位 \(M_k=e^{ik\cdot x}\) 对应 Lean 的 `phaseShift (k/(2π))`。
接 boson 源时，量子两探针为 \(k=-k_{\rm in}\)、\(l=-k_{\rm out}\)。
共同实际频率是 \(z=w=6c(1-i)\)，其阻尼 \(6c>5\)，\(|z|^2=7776/125\)。
没有把时间换成 \(t/N\)；脚本的 \(\tau=ct\) 只用于有限矩阵系数运算，回执保留换回因子。

从原含体积的 A1/S01 密度顶点，程序重新生成

\[
 V_{252}=-iC_0^{-1}(\mathrm{densityVertex}/N),\quad
 V=F^\dagger V_{252}F,\quad h(p)=h_0+\sum_jp_jh_j,
 \quad K=\sqrt2\gamma_5.
\]

原 252 维 \(h_0,h_j,V\) 对实际 occupied frame F 均双侧 reducing。
\(F^\dagger F=1\)，原 actual matter 为 \(2Fw\)，完整原 Yukawa 对 F 两侧均为零。
在此 12 维空间，\(h(p),V,K\) 自伴，\([K,h(p)]=[K,V]=0\)，且

\[
 \|V\|=N,\quad \|K\|=\sqrt2,\qquad
 H_k:=\sum_j k_jh_j,\quad H_k^2=N^2|k|^2I.
\]

V 的范数来自真实秩 8 投影 \(V^2/N^2\)。原 full252 H 的非自伴反控制保留。
余弦是实标量乘法，故同一个 F 的双侧 reducing、K 对易与完整源身份逐点延续。
正式 `PacketGaugeNoise.Profiles.cosinePotential`、`Transfer.selected_cosine` 支付
primitive 实 P286 profile 与 t=0 两转移，不能单独代替下面的全时间构造。

原 \(\psi=G(i)b/\|G(i)b\|\) 是 `filteredPacket 0 1`，\(b\) 为既有 unit-ball packet。
它单位范数、属于这个 F-valued L² 空间的原 H 域；原 Dirac Green、C0 逆和包都保持 F。
\(P=|\psi\rangle\langle\psi|\)、sourceFilter 和归一化固定，不随 ε 重准备。

## 同一原族的真实全时间发展

在 \(\mathcal H=L^2(\mathbb R^3,\mathbb C^{12})\) 上，H 是 \(h(2\pi\xi)\)
的最大 Fourier 自伴乘子。定义

\[
 W_q=\cos(qx)V=\tfrac12(M_q+M_{-q})V,\quad
 H_\varepsilon=H+\varepsilon W_q,\quad D(H_\varepsilon)=D(H).
\]

\(W_q\) 有界自伴，\(\|W_q\|\le N\)。有界自伴扰动定理产生每个实 ε 的自伴
\(H_\varepsilon\) 和单位群 \(U_\varepsilon(t)=e^{-itH_\varepsilon}\)，保持同一域。
也可直接由强相互作用 \(U_0(-t)W_qU_0(t)\) 的迭代积分构造：第 n 项在每个有限
时间窗有界于 \((|\varepsilon|N|t|)^n/n!\)，定义 CLM 的级数在范数中收敛；向量
Volterra 唯一性和自伴生成元给单位性与群律。这里不假设 U 的算子范数时间连续。
原 `FullQuantum.GaugeHistory.Primitive.localForce_original_ae` 给相同源相互作用，
`Uniqueness.full_interaction_unique` 识别这个构造与原实际发展在 F 上的限制。
有限 ε 流包含全部动量链；下面的两转移是其真实一阶变分，不是有限链截断。

原仿射主部与局域乘法直接给

\[
 H_\varepsilon M_k-M_kH_\varepsilon=M_kH_k.
\]

这也使 M_k 保持共同域。K 保持该域并与整群对易。将原
`PacketFourier.Current.phaseCurrentField_apply` 的两个完整项限制到这个 reducing 空间，得到

\[
 B_{\varepsilon,k}(t)=\frac K{N^2}
 [2T_{\varepsilon,k}(t)H_\varepsilon+R_{\varepsilon,k}(t)],
 \quad T_{\varepsilon,k}=U_\varepsilon^\dagger M_kU_\varepsilon,
 \quad R_{\varepsilon,k}=U_\varepsilon^\dagger M_kH_kU_\varepsilon.
\]

Hε 只作用固定初态，\(H_\varepsilon\psi=H\psi+\varepsilon W_q\psi\)；未使用
\(H^2\psi\)。与同一 sourceFilter 复合后，原 Green 恒等式使 H·sourceFilter 有界，
因此这些原 current 也有真正的有界源接口。

## 两条真实 Fourier Duhamel 核

置 \(E_p(t)=e^{-ith(p)}\)。实际波函数变分为

\[
 D_q(t)=\partial_\varepsilon U_\varepsilon(t)|_0
       =-i\int_0^tU_0(t-s)W_qU_0(s)\,ds.
\]

对 \(\sigma=\pm1\)，定义没有余弦半因子的矩阵

\[
 d_\sigma(t,p)=-i\int_0^t
 E_{p+\sigma q}(t-s)V E_p(s)\,ds.
\]

则

\[
 \widehat{D_q(t)f}(r)=\tfrac12\sum_{\sigma=\pm1}
 d_\sigma(t,r-\sigma q)\widehat f(r-\sigma q).
\]

它恰为 \(\exp[-it\left(\begin{smallmatrix}h(p+\sigma q)&V\\0&h(p)\end{smallmatrix}\right)]\)
的右上角。两边使用不同的真实 h；这个 24 维块只是变分实现。
对每个 \(\Re z>0\)，源 h 自伴给两侧真逆与范数界

\[
 R_z(p)=(z+ih(p))^{-1},\quad\|R_z(p)\|\le(\Re z)^{-1},\qquad
 \int_0^\infty e^{-zt}d_\sigma(t,p)dt
       =-iR_z(p+\sigma q)V R_z(p).
\]

Fubini 由 \(Nt e^{-\Re zt}\) 支配；式中没有能级差分母。程序在实际非零 q、
新三分量 incoming p 和 \(z=6c(1-i)\) 核对完整 24×24 两侧逆，错误使用两个相同
fibre 的核有非零残差。

## 完整 current 变分与 Sylvester 频域口

从同一有限 ε 族直接微分，令

\[
 T_k^{[1]}=D_q^\dagger M_kU_0+U_0^\dagger M_kD_q,
 \quad R_k^{[1]}=D_q^\dagger M_kH_kU_0+U_0^\dagger M_kH_kD_q,
\]
\[
 C_{q,k}(t)=\partial_\varepsilon B_{\varepsilon,k}(t)|_0
   =\frac K{N^2}[2T_{0,k}W_q+2T_k^{[1]}H+R_k^{[1]}].
\]

给出可直接消费的完整两转移 current 表。置
\(A_k(p)=K[h(p+k)+h(p)]/N^2\)、
\(B_k(t,p)=E_{p+k}(t)^\dagger A_k(p)E_p(t)\)。输出动量 \(p+k+\sigma q\) 的系数是

\[
\begin{split}
 C_{\sigma,k}(t,p)={}&E_{p+k+\sigma q}^\dagger\frac{KV}{N^2}E_p\\
 &+\tfrac12d_{-\sigma}(t,p+k+\sigma q)^\dagger A_k(p)E_p\\
 &+\tfrac12E_{p+k+\sigma q}^\dagger A_k(p+\sigma q)d_\sigma(t,p).
\end{split}
\]

\(\widehat{C_{q,k}f}(r)=\sum_\sigma C_{\sigma,k}(t,r-k-\sigma q)
\widehat f(r-k-\sigma q)\)。直接接触已含余弦的半因子一次；左右传播项均保留。
它满足源生初值和微分方程

\[
 C_{\sigma,k}(0,p)=KV/N^2,\qquad
 \dot C_{\sigma,k}=\mathcal L_{p+k+\sigma q,p}(C_{\sigma,k})
 +\tfrac i2[V B_k(t,p)-B_k(t,p+\sigma q)V],
\]

其中 \(\mathcal L_{l,r}(A)=i[h(l)A-Ah(r)]\)。该算子在矩阵 Hilbert–Schmidt
空间上反自伴，故所有 \(\Re z>0\) 的 \(\mathcal R_{z;l,r}=(z-\mathcal L_{l,r})^{-1}\)
真实存在、范数不超过 \(1/\Re z\)。因此完整 current 的 Laplace 核为

\[
 \widehat B_k(z,p)=\mathcal R_{z;p+k,p}(A_k(p)),
\]
\[
 \widehat C_{\sigma,k}(z,p)=\mathcal R_{z;p+k+\sigma q,p}
 \left(\frac{KV}{N^2}+\frac i2[V\widehat B_k(z,p)-\widehat B_k(z,p+\sigma q)V]\right).
\]

这是真正的 Sylvester resolvent；不能把它改成两单粒子 Laplace 算子的乘积。
按 column-major 向量化，可直接生成
\(zI_{144}-i[I\otimes h(l)-h(r)^T\otimes I]\)。
`source.py` 用不交换指数幂及原两项 current 独立比较两 σ、两实际探针和零探针的
0 至 4 阶时间系数，全部12×12条目通过；有限检查不替代上面的全时 Duhamel 推导。

## 固定准备的全时间余项与双参数积分

单位群的真实 Duhamel 差给全部实 ε、全部实 t

\[
 \|U_\varepsilon-U_0\|\le|\varepsilon|N|t|,\qquad
 \|U_\varepsilon-U_0-\varepsilon D_q\|\le\varepsilon^2N^2t^2/2.
\]

记 \(\alpha=\sqrt2/N^2\)、\(h=\|H\psi\|\)、\(v=N\)、\(r_k=N|k|\)，

\[
 a_k=\alpha(2h+r_k),\quad b=2\alpha v,\quad
 z_k(t)=b+2va_k|t|,\quad d_k(t)=2vb|t|+2v^2a_kt^2.
\]

展开 \(U_\varepsilon^\dagger A U_\varepsilon\) 并用两侧单位性，可得其差界
\(2|\varepsilon|v|t|\|A\|\) 与余项界 \(2\varepsilon^2v^2t^2\|A\|\)。
代入原 Hεψ，得到 B0ψ 范数不超过 a、Cψ 不超过 z、真实差不超过 |ε|z、
真实二阶余项不超过 ε²d。全 ε 的 \(\|B_\varepsilon\psi\|\le a+b|\varepsilon|\)
与时间无关。

保持实际复均值及其两腿：

\[
 \mu_{\varepsilon,k}(t)=\langle\psi,B_{\varepsilon,k}(t)\psi\rangle,
 \quad J_{\varepsilon,k}=(1-P)B_{\varepsilon,k}\psi,
 \quad\mu_k^{[1]}=\langle\psi,C_{q,k}\psi\rangle,
 \quad Z_{q,k}=(1-P)C_{q,k}\psi.
\]

P 固定且范数1，所有向量界原样保持。完整 covariance 为

\[
 \Pi_\varepsilon(k,t;l,s)=\langle J_{\varepsilon,k}(t),J_{\varepsilon,l}(s)\rangle,
 \quad \Pi^{[1]}=\langle Z_{q,k},J_{0,l}\rangle+\langle J_{0,k},Z_{q,l}\rangle.
\]

差的精确两腿展开给
\(|\Pi_\varepsilon-\Pi_0-\varepsilon\Pi^{[1]}|
\le\varepsilon^2[d_k(t)a_l+a_kd_l(s)+z_k(t)z_l(s)]\)。
对任意独立 \(z=\eta_1-iE_1,w=\eta_2-iE_2\)，\(\eta_1,\eta_2>0\)，真实强积分
\(\widehat J_{\varepsilon,k}(z)=\int_0^\infty e^{-zt}J_{\varepsilon,k}(t)dt\)
存在，其参数导数为同权 \(\widehat Z_{q,k}\)。确切 moment 界是

\[
 L_k(\eta)=b/\eta+2va_k/\eta^2,\qquad
 D_k(\eta)=2vb/\eta^2+4v^2a_k/\eta^3.
\]

积分余项不超过 ε²D。因此

\[
 \mathcal N_\varepsilon(k,l;z,w)
 =\iint e^{-\bar zt-ws}\Pi_\varepsilon(k,t;l,s)dt\,ds
 =\langle\widehat J_{\varepsilon,k}(z),\widehat J_{\varepsilon,l}(w)\rangle,
\]
\[
 \mathcal N^{[1]}=\langle\widehat Z_{q,k}(z),\widehat J_{0,l}(w)\rangle
                 +\langle\widehat J_{0,k}(z),\widehat Z_{q,l}(w)\rangle.
\]

统一二阶余项为
\(\varepsilon^2[D_k(\eta_1)a_l/\eta_2+a_kD_l(\eta_2)/\eta_1+
L_k(\eta_1)L_l(\eta_2)]\)。`bounds.py` 精确核对全部多项式半轴 moments。
这些支配界支付 Fubini 与积分参数微分，不使用时间尾截断或动量 UV 截断。

同一 `PacketGaugeNoise.Readback.filteredWord_read` 可把实际 J／Z 或其真实积分放入
\(\mathrm{create}\,\psi\;\mathrm{annihilate}\,J_L\;
\mathrm{create}\,J_R\;\mathrm{annihilate}\,\psi\) 的完整词。
两变化腿各一词后相加，原 Stage10 读数即上述 Gram／导数。完整词生成后才走原 Mother，
sourceFilter 只在两端；不同连续 transfer 没有标签正交假设。

## 原波包的非零消费者与错误平移控制

当 current 探针 k=0 时，\(T_{\varepsilon,0}=I\)、\(R_{\varepsilon,0}=0\)，所以
\(B_{\varepsilon,0}(t)=2K(H+\varepsilon W_q)/N^2\) 对全实 ε,t 精确不变。
这与 t0 `selected_cosine` 相接。任意 k 的每条真实变化腿初始时间斜率为

\[
 \partial_t C_{\sigma,k}(0,p)=\frac{iK}{2N^2}\{V,H_k\}.
\]

错误取 \(\tfrac12(C_{{\rm const},k+q}+C_{{\rm const},k-q})\) 会多出各自的
\(\sigma iK\{V,H_q\}/(2N^2)\)。真值减错误值的总斜率为

\[
 D_k=\frac K{N^2}M_k\sin(qx)\{V,H_q\}.
\]

在 k=0，D0 是 Hermitian 的有限矩阵乘 sin，原 q1 非零。程序从真实原 Dirac-filtered
packet 的 p=0 内部因子验证 \(K\{V,H_q\}\widehat\psi(0)\ne0\)：省写的原 ball Fourier
零点值及固定归一化均非零。连续性使未乘 sin 的
L² 向量非零；sin 的零集合为零测度平面，故 D0ψ 非零。
若 \((1-P)D_0\psi=0\)，则 ψ 是 D0 的非零特征值 L² 特征向量。对有限 Hermitian
矩阵逐谱分解，这要求非零分量支持在 sine 的一个零测度水平集，矛盾。因此连真正
**中心化**的 Z 也不能使用旧平移式。
上述初斜率只需有界 commutator：\(\dot T_\varepsilon=iR_\varepsilon\)、
\(R^{[1]}=O(t)\) 给 \(T^{[1]}=O(t^2)\)；其 Hψ 项除 t 后趋零，不需要 H²ψ。

## 共同实际频率的完整 cross 包围

消费原包已付的 \(h<2\)、所有单位方向的 \(X_\psi=\|(x\cdot e)\psi\|<3\)、
\(X_{H\psi}<4\)。它们由同一 Green 和 unit-ball 初态生成，不作为新可调输入。
真实位移界 \(\|x_eU_0(t)f\|\le X_f+N|t|\|f\|\) 及
\(|\cos(qx)-1|\le|q\cdot x|\) 给

\[
 \|(D_q-D_{\rm const})(t)f\|
 \le N|q|[|t|X_f+Nt^2\|f\|/2].
\]

比较完整 current 的左右传播腿时，左差项经过 \(U_0(t)^\dagger M_kU_0(t)\)，
其位置矩贡献为 \(tX_f+3Nt^2\|f\|/2\)，右差项为
\(tX_f+Nt^2\|f\|/2\)。所以在 \(r_k\le1\) 时

\[
 \|(C_{q,k}-C_{{\rm const},k})(t)\psi\|
 \le |q|(24+88|t|+40t^2).
\]

η≥5 的半轴积分给 \(\|\widehat Z_{q,k}-\widehat Z_{{\rm const},k}\|<9|q|\)。
原相位位移界同时给 \(\|\widehat J_k-\widehat J_0\|<8|k|\)、
\(\|\widehat Z_{{\rm const},k}-\widehat Z_{{\rm const},0}\|<9|k|\)。
这里是实际波包的向量界；未假设 cos(qx) 在算子范数中趋向1。

在本轮 \(z=w=6c(1-i)\)，原零探针基点是
\(\nu_0/|z|^2\)、\(d_0/|z|^2\)，其中同一原波包
\(\nu_0\approx45.28703602\)、\(d_0\approx2.39857504271\)。
由 \(|k_{\rm in}|<1/90000,|k_{\rm out}|<1/60000,|q|<1/180000\)，
`bounds.json` 给全部 cross 与均值变化都保留的严格包围：

\[
 \boxed{0.72777152911660043517<\Re\mathcal N_0
                  <0.72821599726474858333,}
\]
\[
 \boxed{0.03808031867377651805<\Re\mathcal N^{[1]}_{\cos}
                  <0.03903436248330032759.}
\]

两量的虚部不强置零。其绝对值分别不超过
\(e_0=j_L+j_R+j_Lj_R\)、
\(e_1=z_L+z_R+\frac47(j_L+j_R)+z_Lj_R+j_Lz_R\)，其中
\(j_L=8/90000,j_R=8/60000,z_L=9(1/90000+1/180000),
z_R=9(1/60000+1/180000)\)。机读文件保留精确有理矩形与 outward 十进制端点。
另一个实际非零 q、零 current 探针消费者由全时间常量性直接给
\(\mathcal N^{[1]}_{\cos}(0,0;z,z)=d_{\cos}(q)/|z|^2>0\)，
\(|d_{\cos}(q)-d_0|<336|q|\)。

本包交付原局域规范场的量子双参数 source 变化。与 boson mixed-momentum 的原双时间
顶点组合时，仍须消费其对应 transfer 与左右参数；它不等同对角同时间 current 的单 Laplace。

## 重放

仓根运行 `uv run --offline --with sympy==1.14.0 python -u` 后接本目录的
`source.py` 与 `bounds.py`。两程序只写本目录对应 json。`source.log`、`bounds.log`
记录精确源检查与区间构造；`construction.json` 绑定冻结输入输出，独立认证写入 `audit/`。
