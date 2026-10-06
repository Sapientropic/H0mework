# 12 态原子响应的来源与误差合同

af0001 从原始原子控制生成电离 effect，再运输到原 compact XZ readout。
固定 `positiveSmoothUnifiedSource`、`SpinPair.visit 10`、material row、whole-ledger 与
current16→17；这是从属数值 producer，直接消费者为独立响应锚与 readiness，
`controller_advance=false`。

## 公开生成器

[Garthoff 2015 官方论文](https://xqp.physik.uni-muenchen.de/publications/files/theses_master/master_garthoff.pdf)
§3.3.1–3.3.2、Eq3.5–3.13（正文与 PDF pp44–49）固定 12 态、RWA 与矩形脉冲。
Appendix A（p89）给出各相干及耗散子过程。论文中的 F=2 与 F′=3 各合并为单态，
电离连续谱合并为吸收态 3。这些是具名模型规则。
一枚 instrument 的各脉冲段共用同一 bright／dark 控制 chart；段间原始 Rabi、cycling、
电离率与时长可变。段内偏振旋转或额外 ground 横场不是 Eq3.7 的生成器输入。

`Γij` 表示从 j 到 i；所有耗散跳跃为 `sqrt(Γij)|i><j|`。
Eq3.12 目视列出 18 条自发跳跃，左列 11 条、右列 7 条；
p44 的“20”没有对应两条额外公式。按明确公式生成，不补猜跃迁。
来源 JSON 保留完整 18 条自发率和 7 条电离率。
逐个相加后，D1 激发态 2、7、8、9、10、12 的自发总率均为 Γ1，
cycling 态 6 的总率为 Γ2。电离率均为 `Aion Γ1`。

Eq3.7 的相干边为
`(1,2),(1,9),(4,7),(4,12),(5,6),(8,11),(10,11)`。
以 `R=Ω12/Γ1`、`C=Ω56/Γ1` 表示独立 readout／cycling 控制，
Eq3.9 给出 `Ω19=Ω4,12=sqrt(6)Ω12`、`Ω8,11=sqrt(3)Ω12`；
其余 D1 边与 Ω12 相同。`H/ℏ` 的非对角项为 Ωij/2，
7、8、9、12 的对角项为 −δ。

全部动力学使用角频率。p48 的能级差 814.5 MHz 转为 `2π·814.5 MHz`，
与 `Γ1=2π·5.7500 MHz` 相除，得
`Δ=δ/Γ1=3258/23`、`Γ2/Γ1=30333/28750`。
无量纲时间为 `τ=Γ1 T`，不能把普通 MHz 与角频率直接混用。
这些固定比值使用文中的名义中心数值；括号中的原子常数不确定度不改写为实际运行的
95% 参数盒。响应包络支付给定模型的数值计算误差，原始输入的不确定域另行消费。
Eq3.8、3.10、3.11 的原始功率映射为
`I=2P/(πw²)`、`E0=sqrt(2I/(c ε0))`、`Ωij=dij E0/ℏ`；
有效场幅、waist 与时间窗口保留为原始输入，校准曲线未充当输入目标正确率。

## 整个 qubit 的相位结构

相干图有五个块：
`B={1,2,9}`、`D={4,7,12}`、`R={11,8,10}`、`C={5,6}`、`I={3}`。
H 对这些块保持块对角。rank-one 跳跃的 gain 项为
`Γij ρjj |i><i|`，只由 population 生成 population；
loss 项的 `L†L=Γij |j><j|` 为对角。
因此块对角 Hermitian 空间在所有脉冲段内闭合，实维数为
`3²+3²+3²+2²+1²=32`。

任意对每个块施加的独立整体相位与 H 对易；每个跳跃只获得一个相位，
在 Lindblad gain／loss 中抵消。完整演化与这些块相位变换交换。
bright=1 与 dark=4 的 off-block coherence 保留其非平凡相位荷，
不能产生任意 population，尤其不能产生电离态 3 的 population。
从任意 qubit density matrix 起始时，电离概率因此只消费其 bright／dark 对角项。
由同一前向演化生成的 `JQ` 恰为 `diag(pb,pd)`，不需要将 qubit 输入假设为经典混合。

运输到旧 readout 还需具名的实际控制 chart。
给定合法 XZ 轴 `(ax,az)` 后，
`JQ=[(pb+pd)I+(pb−pd)(ax X+az Z)]/2`。
背景 d 与片段注册率 η 生成
`E_dark=(1−d)I−(1−d)ηJQ`，故
`μ=1−2d−(1−d)η(pb+pd)`，
`u=−(1−d)η(pb−pd)ax`、`z=−(1−d)η(pb−pd)az`，Y 分量为零。
对角性是动力学结论；实际轴身份由原始光学控制负责，名义角度表不代付该身份。

## 可加的验证误差

对每一矩形脉冲段，生成器为有限维 GKSL：
`L(ρ)=−i[H,ρ]+Σj(Lj ρ Lj†−{Lj†Lj,ρ}/2)`。
令 `K=−iH−Σj Lj†Lj/2`、`J(ρ)=Σj LjρLj†`。
`exp(tK)ρ exp(tK†)` 为完全正映射，`exp(tJ)` 是完全正映射的非负幂级数。
有限维 Lie 乘积极限生成 `exp(tL)`，完全正性在极限中保持；
`Tr L(ρ)=0` 给出 trace preservation。非负时长段的组合仍为 CPTP。
这直接支付该具体生成器的半群责任；
[Lindblad 原始论文](https://link.springer.com/article/10.1007/BF01608499)给出一般生成器定理。

[Watrous 官方 TQI](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)
Corollary3.40、Eq3.241（正文p168／PDF176）给出正且 trace-preserving 映射的 trace norm 收缩。
若第 j 步的 Hermitian 局部误差为 δj，则后续精确 CPTP 段不放大它，
终端 trace-norm 误差至多 `Σj ||δj||1`。
Taylor 多项式自身不需要被声称为 CPTP；收缩用于传播误差的精确演化。

对与输入范数一致的 induced matrix norm，若 `R=||hM||<n+2`，
Taylor n 阶的尾和由相邻项比值控制为
`R^(n+1)/(n+1)! / (1−R/(n+2)) * ||input||`。
步 cap `R≤4` 与阶数 `n=80` 满足该条件；`R≤1/2` 不是必要条件。
所有有限运算舍入与平方根误差另以向外区间支付。

32 个实 Hermitian 坐标含 12 个 diagonal、20 个 off-diagonal real／imaginary 坐标。
若每坐标误差≤r，完整矩阵 Frobenius 范数满足
`||E||F²≤(12+2·20)r²=52r²`，
故 `||E||1≤sqrt(12)||E||F≤sqrt(624)r<25r`；使用 `32r` 是合法保守上界。
必须保留 off-diagonal 的重复权重与 Hermitian 重建，不能套遗漏 imaginary 坐标的系数。

平方根 midpoint 仅近似 H：只要 midpoint H 仍 Hermitian、耗散率保留精确非负值，
其精确演化仍 CPTP。若同一时间段中 `||H−Hmid||op≤εH`，
variation-of-constants 与 `||[ΔH,ρ]||1≤2||ΔH||op||ρ||1` 给出
密度态响应差≤`2τ εH`；多个段直接相加。
大 detuning 不进入全程 `exp(||M||τ)` 的误差放大因子。

主实现用 32 维 Hermitian restriction 的 induced infinity 范数作 Taylor 尾界，
并以 `32r` 转成 trace norm。独立实现保留完整 144 个复数矩阵坐标，
以 `Σij(|Re ρij|+|Im ρij|)` 控制尾与有限运算舍入。
该 entrywise 范数直接上界 trace norm；实际 action 的诱导范数由
`2 maxrow Σ|Hij|+2 maxj outgoing_j` 控制。
每个复数坐标的两个 real 分量各作最多半 quantum 的 nearest 舍入，
一项向量舍入因此≤`144/2^bits`；按 Taylor 递推传播并逐项累加。
独立 H 使用有理 midpoint，平方根替换另由上述 Duhamel 界支付。
两种算术均在完整 Hermitian 误差上消费 exact-channel contraction。

## 整个低脉冲面积域的排除

同一生成器对所有非负 readout／cycling／电离率及有限矩形脉冲段给出统一 bound。
初态取 i=1 或 4，令 `P(t)=1−ρii(t)`。原 jump 清单没有从 i 出发的通道；
流入 i 的 spontaneous population 非负，只会减小 P 的增长。
第 i 条 Hamiltonian 行仅耦合两个 excited state，Rabi 比为 1 与 sqrt(6)。
因此，无论其余 coherences 的相位如何，

```text
Pdot ≤ ΩR |Im ρij + sqrt(6) Im ρik|
     ≤ sqrt(7) ΩR sqrt(|ρij|²+|ρik|²)
     ≤ sqrt(7) ΩR sqrt(ρii(ρjj+ρkk))
     ≤ sqrt(7) ΩR sqrt(P(1−P)).
```

第三步由 positivity 的两个 2×2 principal minor 生成，最后一步消费 trace=1。
`P(0)=0`，对任意 ε>0 积分 `sqrt(P+ε)` 的导数，随后令 ε↓0，得
`P(T)≤7 A²/4`，其中无量纲原始 readout pulse area
`A=∫Ω12(t)dt=Σsegment omega_r·duration`。
电离态不等于 i，故 `p_ion≤P`；两种初态均消费同一个 A。
由于 `0≤pb,pd≤1`，

```text
g = (1−d)η |pb−pd| ≤ max(pb,pd) ≤ min(1,7A²/4).
g≥G>0  ⇒  A²≥4G/7.
```

旧 whole-parent-CS 的同时 gain 下界由此生成新的原始控制必要域。
它排除所有小面积脉冲、任意 cycling／电离参数及任意合法 d／η 的整个纤维，
不靠有限测试点、不花新 alpha。结论在具名 12 态模型内统一；
额外从初始 ground 态直接流出的未登记 noise jump 不属于这个生成器。

保留 `sqrt(P(1−P))` 还给出严格更强的解析口。
用 `fε(P)=∫₀ᴾ dx/sqrt((x+ε)(1−x+ε))` 正则化两端，
`d fε(P(t))/dt≤sqrt(7)ΩR(t)`；ε↓0 后
`2 asin(sqrt(P(T)))≤sqrt(7)A`。
因而 `g≥G` 蕴含 `A≥2 asin(sqrt(G))/sqrt(7)`。
af0001 的有理平方域 consumer 消费 `A²≥4G/7`，不把浮点 arcsin 当认证端点。

## 冻结 driver 与剂量消费者

[af0001 合同](criterion-af0001.md)固定四枚理论 pulse 及首次回执的身份。
`atomic_forward_run.py` 的两种 role 分别加载主／独立计算程序，独立 role 不导入
主数值 producer。独立端重建完整 144-coordinate action，核原始 pulse、全部 restriction
系数与严格包络交集；p 包络宽度≤10^-50，trace_j 宽度≤2·10^-50。
主包络保留向外数值误差，零边界不因微小负 lower 被拒；
交集必须与精确物理域相交，宽度条件独立验收。
`trace_j` 的两个端点恰为同次 `p_bright+p_dark` 的两个端点；
所有误差上界必须非负。trace 锚不能由独立的窄数值表替代同枚电离 effect 的 trace。
构造的两枚响应是否 unequal trace，由实际包络决定，不能成为生成器 premise。

`atomic_dose.py` 逐项消费 cp0002 的四个 gain 下端；driver 的独立 role 自算
`G/(7/4)`，用整数 square-root 检查 80-bit 向下 dyadic 根及下一格平方。
两条算术分别产生相同的八枚 individual necessary dose bounds。
cp0003 的 uniform／alice／bob ray 分别覆盖全四 setting、Alice 两 setting、Bob 两 setting。
原 entire-lower-orthant exclusion 支付对应 `max gain>G`，
遂生成相应 `max area²>4G/7` 与向下根的严格下界，共六枚 joint-maximum bounds。
这些范围是原 whole-parent-CS 与登记物理域的交集投影，不是新的置信集合。
原证书及完整 run 身份先由原消费者核验；不打开试次、不重拟合、沿用 1/20。

`atomic_forward_verify.py` 消费冻结的主／独立 first 与各自 attempt，
核同一科学 freeze 的祖先关系、程序字节及独立端绑定的主 first SHA。
消费者复核十二项包络交集、12,288 项完整 restriction 系数和全部剂量根，
不调用原子 `propagate`、不重做矩阵指数或寻找新的脉冲。
全部 common-scope 字段按类型和值匹配，控制响应不能被改记为实际响应锚或唯一硬件。
回执位置 override 消费同一 canonical 证书，不替换科学程序。

## 绝对尺度与实际身份

不同 trace 的独立前向响应 `J0,J1` 与完整 law 的两偏置可恢复共同 d／η，
公式由[已登记恢复接口](hardware-anchor-access.md)承担。
前向 pb／pd 由原始脉冲生成，不能把恢复目标、拟合 F0／F1 或实际 gain 填入生成器。

若两 setting 仅作同一脉冲的旋转，`τ0=τ1=τ`，共用 d／η 时偏置也相同。
设 `k=(1−d)η`，取附近 s>0：
`k′=sk`、`d′=d+(1−s)kτ/2`、`η′=sk/(1−d′)`。
偏置保持，向量响应乘 s；在器件域内部，s 的开邻域仍合法。
两侧分别取 s 与 1/s 后，所有 X/Z 乘积及完整 joint law 保持。
这表明公开物理前向子域不会因加入“原子动力学”名称便自动变成单点。
该构造位于 equal-trace／common-bias 子域，不把它套到两个偏置不同的旧固定证人。

已发生硬件对象的确定性与从公开观测恢复它的能力分别消费；
实际 λ、actual optical chart 与独立响应锚仍需来源绑定。
af0001 生成具名模型的响应证书，不把构造控制点登记为两次实际运行的唯一参数。
