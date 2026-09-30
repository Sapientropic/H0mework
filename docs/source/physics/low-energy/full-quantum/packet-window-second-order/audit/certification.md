# Sharp-ball 二阶响应独立认证

**Verdict: certified。** 同一原 sharp 球窗、实际 289 场 seed、实对称 Q、E0η1 准备及物理测度下，
\[
\mathcal L(sv)=\mathcal L(0)-c_vs+K_vs^2+o(s^2),\qquad s\downarrow0,
\]
\[
K_v=\frac1{4(2\pi)^3}\int_{B_R}B_Q(a,\partial_v^2a)\,d^3k.
\]
这里 \(\mathcal L=\operatorname{Re}L\)。损失扣除线性窗项后的系数是 \(-K_v\)。
同一源正则性还支付全方向统一余项，给扣除一次齐次窗项后的二阶 Peano 多项式。

认证对象为 compute.py、receipt.json、README.md、check.log、construction.json 五个冻结文件。
本包为解析证明及精确源程序；无新增 Lean 声明或公理。本次只写 audit，未修改候选、source、root/current 或提交。

## 解析责任已支付

在每根长球弦上，第二腿 Taylor 展开保留实际移动上限 \(h-s\)。补回尾段后，
\(s^2c'(h)/2\) 与 \(-s^2e(h)\) 由对称实配对的 \(c'=2e\) 精确相消。
这给正确的端点首项及体积二阶项，没有删掉边界条件。

短弦的横向面积为 \(\pi s^2/4\)、原球内体积为 \(\pi s^3/6\)：
补回零阶及一次项只产生 O(s³)，补回二次项产生 O(s⁵)。因此不改变 K。

候选 C² 一致余项的各项独立核对如下，均在乘物理因子 \(1/[2(2\pi)^3]\) 之前：

- 第二腿积分余项为 \(\operatorname{Vol}(B_R)M_0\omega_2(s)s^2/2\)。
- 三个长弦尾段的系数之和为 \(5M_1^2/6+4M_0M_2/3\)，乘 \(\pi R^2s^3\)。
- 短弦的零、一次补项合为 \(5\pi M_0^2s^3/12\)，二次补项为 \(\pi M_0M_2s^5/12\)。

共同乘 \(\|B_Q\|\) 即为声明界。C³ 的积分余项确可改为
\(\operatorname{Vol}(B_R)M_0M_3s^3/6\)。
闭球紧性和强连续二阶导数使 \(\omega_2(s)\to0\)；
用全二阶导数的统一模量同样支付所有单位方向。没有对指示窗作普通函数微分。

[Seed](../../packet-seed-regularity/audit/certification.md) 的全球解析 W 和
[Moments](../../packet-current-moments/audit/certification.md) 的同一原中心化 current 强 C∞
共同生成实际 \(a=WJ\) 的这些条件，包括原点与 frame 接缝。
上游 [Boundary](../../packet-window-boundary/audit/certification.md) 的能量／源／几何身份保持关闭。

## 球面通量和复交叉

常系数 Q 与真实散度定理给
\[
K_v=\frac1{4(2\pi)^3}\left[
\int_{\partial B_R}(v\cdot n)B_Q(a,\partial_va)\,dS
-\int_{B_R}B_Q(\partial_va,\partial_va)\,dk\right].
\]
球面通量一般非零。它没有被长弦表达式中那两个特定尾段的相消删除。

按内积左反线性，设
\(\beta=W^\dagger QW,\ \alpha=W^\dagger QW_v,\ \zeta=W^\dagger QW_{vv}\)，
\(N=\langle J,J\rangle,\theta=\langle J,J_v\rangle,\eta=\langle J,J_{vv}\rangle\)。
实际 product rule 是
\[
B_Q(a,a_{vv})=\operatorname{Re}\zeta\,N
 +2\operatorname{Re}(\alpha\theta)+\beta\operatorname{Re}\eta.
\]
梯度能量的交叉则为 \(2\operatorname{Re}(\overline\alpha\theta)\)。
因此两处虚部项的符号相反；候选完整 beta 导数改写正确。物理 k 导数与 Fourier h
的关系保留 \(k=2\pi h\)，没有重复 Fourier 因子。

## 独立执行与反控制

[check.py](check.py) **1.797 秒 EXIT 0**。原冻结程序隔离重放与 receipt 除运行时间外全部相同；
五文件及三个源输入的摘要均一致。重放只向 audit 写文件。

独立算法使用水平圆盘截面，在真正重叠平面 \(t=-s/2\) 两侧分别积分半径
\(\sqrt{R^2-t^2}\) 与 \(\sqrt{R^2-(t+s)^2}\)，没有调用候选球弦积分函数。
选物理方向 \(v=(2,-1,2)/3\)，对包含全部三空间坐标与复混合项的二次测试场作完整三维积分。
该场使用原 source 向量 \(b=e_9+e_{259}\)，从实际 Q 直接读得 \(B_Q(b,b)=4\)。

测试得到
\[
K_v=\frac{6R^5+10R^3}{45\pi^2},
\]
同时逐式核对端点首项、O(s³) 余多项式、原球面通量与梯度体积积分。
这一测试场验证普遍身份，不替代实际 WJ 的积分。

独立反控制另取原 b 上的 \(W=e^{3it}b,\ J=e^{-5it}\)：
完整二阶收缩为 \(-16\)，丢虚部交叉错误得到 \(-136\)；
实际梯度收缩为 \(16\)，错误共轭次序得到 \(256\)。
删球面通量及混淆响应／损失符号也被精确三维例子拒绝。

验收数据见 [receipt.json](receipt.json)、[check.log](check.log)、[replay.log](replay.log)。
重演入口为本目录 check.py，使用 uv run --offline --with sympy==1.14.0 python。

**Defect scope: none。** 签收实际 K 的解析积分公式与全部必要源接线；
本包未计算该实际整球积分的数值，也未将带尖点的完整响应声明为原点二次可微。
