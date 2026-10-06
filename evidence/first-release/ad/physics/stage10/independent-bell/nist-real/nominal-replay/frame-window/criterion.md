# fw0001：共同偏振参考平面的完整源、校准 fringe 与泵控制

合同、来源、程序及Lean候选各自提交后才执行；本合同先于任何本版数值执行。
公开结果已经暴露；模型检验是回顾性的。历史冻结文件保持，root/whole-ledger/tick 保持。

## 1. 同一源与作用顺序

原始真空源为两偏振 TMSV，tH,tV∈[0,1)。每个 pulse 先以概率 λ 对原源的 V-number
施加 π phase flip，再在双方施加同一实正交 Jones 矩阵

`Rδ=[[cosδ,sinδ],[-sinδ,cosδ]]`。

两支 φ=0/π 的 pair kernel 是 `Rδ diag(sqrt(tH),exp(iφ)sqrt(tV)) Rδᵀ`。
公开 Klyshko targets 的中心固定为 KA=.747、KB=.756；每侧两偏振 scalar transmission
由下面的 coupled calibration 逆读生成。损失、phase flip 与 R 的顺序
固定；把 phase flip 改成接收端 V-number、窗口后才混合或只改分析器而不改源，均是不同源。

五个 fresh-vacuum pulse 各自生成 phase branch，再形成本地 any-click；每 pulse 独立 OR 背景
为 bA=8.9e-7、bB=3.2e-7。calibration 使用同一 R、scalar loss 与 noise channel，制备和泵强
由各自具名协议指定。该模型不把共同 R、均匀 loss 或 noise order 宣称为实际装置已识别。

理想平衡 φ=0 源的 raw kernel 是 zI，共同 R 保持整个 Fock 源。φ=π 支不具有此不变性，
故加入 R 后不得复用 cb0001 的 δ=0 visibility→λ 换算。

### 1.1 公开 Klyshko targets 的同源逆读

指定 cal0001 的 matched、单偏振、single pulse、signal-only 协议，tcal=1/10000。
Klyshko 下标是被 herald 的一侧：KA=J/SB、KB=J/SA。目标来自原公开概率单位 ±.003 盒。
同一几何 TMSV 与 bucket 读出生成

```
t=tcal, Q=KA+KB−KA*KB, Delta=(1+t)²−4t Q
w=2t/(1+t+sqrt(Delta))
SA=KA*w, SB=KB*w
TA=2KA(1−t)/(1+t+sqrt(Delta)−2KA*t)
TB=2KB(1−t)/(1+t+sqrt(Delta)−2KB*t)
```

这个小根是 vacuum-continuous branch。PGF 生成
`J=SA*SB*(1+t−SA−SB)/(t−SA*SB)`，故 w 满足
`Qw²−(1+t)w+t=0`。另一个根 w≥1；本公开域 KA/KB>t 时给 SA/SB>t，违反合法 T≤1 的
geometric bucket bound。分支由实际源方程与合法性产生，不按 Bell 或 calibration 结果选根。

raw loss packet 保留 exact rational KA/KB/tcal 和 exact Delta、branch 标记；TA/TB 是以上
同一二次代数表达式，数值输出另给向外包络。**TA/TB 不量化或截值。** 重读完整 Klyshko 必须
证明 equals target；校准端点不会因 raw T 量化跑出原盒。Delta≤0、分母非正或 TA/TB∉[0,1]
失败，禁止切到大根。原 cb0001 固定 raw-center 历史保持。

下文 ηA/ηB 只记本版生成的 exact TA/TB，不再把它们与公开 Klyshko 数字等同。

## 2. 公开 single-only 源生成

只消费 SI 的 00、11 两行完整 denominator 和四个本地 marginals：
`pA=(N+++N+0)/Nrow`、`pB=(N+++N0+)/Nrow`。
数据接口只交付这四个有理概率；源生成器不得接收单独 joint、01/10 行、global N、CI、
印刷最优态比例或最优角目标。joint-marginal-preserving 修改和整个 01/10 修改必须保持源。

单边概率生成 `μ=(1-b)/(1-p)^(1/5)-1`。五次根由整数幂比较产生向外有理包络。
训练的 signed Alice 角为 a0=4.2°、a1=−25.9°，Bob 为 −a0、−a1；X 的 odd 项不能使用绝对角。
令 ci=cos(2ai)、si=sin(2ai)，

```
ui=(μAi/ηA+μBi/ηB)/2
vi=(μAi/ηA−μBi/ηB)/2
Z=(u1−u0)/(c0−c1)
M=u0+Z c0
X=−(s0 v0+s1 v1)/(s0²+s1²)
```

这是几何固定的三个 covariance 坐标。完整理想映射为
`μAi/ηA=M−Z ci−X si`、`μBi/ηB=M−Z ci+X si`；四个 scalar 的 reconstruction residual
分别保留。最小二乘生成合法源不会把这四个 residual 自动变成零。

M/Z/X 包络分别确定同一个 15 位 nearest decimal grid point（半格 tie 朝 +∞）；否则失败。
取三个有理点 Mq/Zq/Xq，C=sqrt(Zq²+Xq²)。必须 exact 检查 Mq≥0、Mq²≥Zq²+Xq²。
C>0 时，cos2δ=Zq/C、sin2δ=Xq/C；用半角恒等式生成 cosδ≥0 的 exact R。
Xq=0、Zq=−C 时固定 δ=π/2；C=0 时固定 R=I，并报告 single 数据未识别方向。

nH=Mq+C、nV=Mq−C。各自的 t=n/(1+n) 包络再确定同一个 15 位有理 grid point，
作为合法 RawKernel 的 exact tH/tV；不截值或换点。R 保持上述 exact 方向。
最终 kernel 的 mean、covariance、single residual 与两级表示误差分别报告；不能把量化后的
Mactual/Zactual/Xactual 冒充未经量化的逆读值。所有取点规则只依赖训练 single 和固定几何。

角度 trigonometry 使用冻结 π 包络及显式 Taylor/Lagrange 余项；向外精度不足则记录
`SOURCE_GRID_UNRESOLVED`，不调整数据、grid、背景或 angle。

## 3. 最大态完整校准 fringe

指定 balanced calibration tH=tV=tcal=1/10000，单 pulse、signal-only；同一 R/η/λ。
设 n=tcal/(1−tcal)、D=(1+nηA)(1+nηB)、L=n(1+n)ηAηB、
`K0=1−1/(1+nηA)−1/(1+nηB)`。
Bob 固定 b=0（HV）或 b=π/4（DA），Alice 扫完整 a∈R/πZ：

```
Jλ(a,b)=K0+(1−λ)/(D−L cos²(a−b))+λ/(D−L cos²(a+b−2δ))
Vb(λ)=(max_a Jλ(a,b)−min_a Jλ(a,b))/(max_a Jλ(a,b)+min_a Jλ(a,b))
```

max/min 必须由全域消费者产生。不得只评价 0/90 或 ±45 的端点，不得调用局部 fringe optimizer。
两分支分母严格正；每个候选的 `Jmax+Jmin>0` 也须验收。

### 3.1 有理 projective profile 与全部实根

q=tan a，U=1+q²，ρ=Zq²+Xq²。ρ=0 时使用 R=I 的固定 profile。
ρ>0 时的两个 quadratic 为：

```
HV: A=D U−L,             B=D U−L (Zq+Xq q)²/ρ
DA: A=D U−L (1+q)²/2,  B=D U−L ((Zq+Xq)−(Zq−Xq)q)²/(2ρ)
J(q)=K0+(1−λ) U/A+λ U/B
P(q)=(1−λ)(U' A−U A') B²+λ(U' B−U B') A²
```

P 的次数≤6。所有 coefficients 属于同一个 exact ordered quadratic field Q(sqrt(Delta))；
δ 的 profile coefficients 只使用 rational Zq/Xq/ρ，所以不引入第二个 radical。
每个 field element 存 reduced fractions `(a,b)`，表示 a+b sqrt(Delta)。若 Delta 是有理完全平方，
先以整数 isqrt 检查 numerator/denominator 并归约成 Q。否则 `(a,b)=(0,0)` 才是零。
同号项直接定符号，异号项以 a² 与 b²Delta 精确比较；inverse 用 conjugate/norm。
不得把 field coefficient 浮点化后再做根计数。

主实现自行生成 polynomial coefficients，删 exact leading zeros；Euclidean gcd 生成 monic
square-free P。Sturm 序列固定为 P、P'、逐次 `−remainder`，只可清正分母，不可单独翻转某项
或把每个 remainder 强制成正首项。完整 polynomial/gcd/sequence 的 coefficient pairs 均报告。
用 Cauchy bound 的经 exact field-order 验证的向上整数
`Broot≥1+max_i|pi/pd|` 包含全部实根；精确有理 dyadic
二分，Sturm variation difference 计数。端点命中有理根须单列并 deflate，不能用 epsilon 跳过。
每个 root bracket 的 count 必须为 1，全部 brackets 的总 count 必须等于整个 Cauchy 域的 count。
P≡0 时核 profile 恒定，登记 constant fringe；不能制造一个任意 extremum。

逐个 root bracket 上评价完整 J 包络，并单列 q=∞ 的 leading-coefficient 极限；取所有候选
区间的 max/min 包络。每个λ probe保存profile输入、degree/gcd、Sturm variations、全部root brackets、q∞、J候选与
final extrema；P与square-free/Sturm coefficient由冻结生成器和probe参数完整重建，避免重复巨大系数。
verifier重新生成完整序列及全部根计数，不能消费主报告的proof bool代替全域计算。

默认把 visibility 包络宽度压到 1e-14。λ 决策遇到目标落在包络内时，只细化同一次全根
brackets 和向外算术。root refinement depth≤256、每次 Sturm split≤32768；超限为
`FRINGE_EXTREMA_UNRESOLVED`，不是物理拒绝。重复根由 exact gcd 处理。

### 3.2 λ 的唯一固定生成规则

反射 a→2δ−a 交换两分支，因此 Jmax/Jmin 在 λ↔1−λ 下对称；Jmax 凸、Jmin 凹。
在 [0,1/2] 内，Jmax 不增、Jmin 不减，正读出 VDA 不增。这项机制须由具体 producer/consumer
证明；不得把单调性作为 caller 已完成字段。

target=.996。先由完整 fringe 包络证明 `VDA(0)>target>VDA(1/2)`，否则登记 no-root、
indistinguishable calibration 或 unresolved，不回退 cb λ。固定
`λ*=inf{λ∈[0,1/2]:VDA(λ)≤target}`。
主实现以 exact rational midpoint 二分 [0,1/2]；probe 的 VDA 下界>target 则更新左端，
上界<target 则更新右端。含 target 的 probe 只提高同一全根精度，不能任选方向。
最多 64 次 λ 决策；宽度≤2^-60 后，固定 bracket=[left,right]。
每个决策保存全 fringe 回执。无法证明决策或达到 cap 即 `LAMBDA_ROOT_UNRESOLVED`。

**source weight 是以上完整 fringe threshold 的 exact real root descriptor λ*，不是 bracket midpoint。**
λmid=(left+right)/2 只用于 float 优化候选/展示；最终 pulse、window、strict gain 与 band 的
数学读出对整个 certified root bracket 外包。两独立实现各自从原 calibration 生成同一 root
descriptor 与 enclosure，不从另一方读 λ。

最终再独立核完整 HV/DA fringe：HV 全包络须包含于 [.998,1]。DA target=.995/.996/.997 由
exact root descriptor 支付 `VDA(λ*)=target`，因此本身属于原 [.995,.997]；数值 full-fringe
包络须包含这个 target 并达到规定宽度。不能把覆盖 root bracket 的包络微小越过 endpoint
当成 exact source/calibration 失败，也不能扩大实验带。中心数值误差/包络宽度≤1e-14
单列为计算精度。λ* 必须满足 0≤λ*≤1/2；no-root、负均值或非法 source 均失败，不作 clipping。

## 4. Klyshko、全 Fock 与五窗口

Klyshko 以原源 eigenpolarization matched herald 接收对应完整 partner mode；
其完整 bucket ratio 与 raw transmission 不同，由 §1.1 同一源的公开 target 逆读支付。
共同 R 和 phase flip 对这种 matched 模式同次 transport；实际 NIST calibration port 身份保持未识别。

非最大态两 branch 从 raw tH/tV 和 R 分别生成 pulse vacuum probabilities：
P0A=1/(1+μA)、P0B=1/(1+μB)、P00=1/((1+μA)(1+μB)−|κ|²)，
其中 μA/B 和 κ 均是同一 rotated raw kernel 的读出。先按 λ 混合 pulse P00，才作五窗口。
`P0Awin=[(1−bA)P0A]^5`，P0B 类似，`P00win=[(1−bA)(1−bB)P00mixed]^5`。
`sA=1−P0Awin`、`sB=1−P0Bwin`、`j=1−P0Awin−P0Bwin+P00win`。

独立实现从 number-basis coherent source amplitudes 和实际 Γ effects 计算所有 h+v≤6 sector，
对两 branch 各自保留 off-diagonal coherences。R 以各 sector 的 symmetric tensor action 作用于
source；接收端 effect 留在原 signed angle。finite prefix 不重新归一。
exact rational τ=1−(1−tH)(1−tV) Σ_{h+v≤6}tH^h tV^v 是原源遗漏质量。
由合法 number-conserving positive contractions 支付每个 no-click 的 [0,τ] 后再混合和作窗口。

独立 calibration 使用 q 与 w=cot a 的两个 compact charts [−1,1] 覆盖整个 projective fringe。
从相干 Γ/Fock prefix 直接生成 chart polynomial，Bernstein subdivision 产生全域 extrema
上下包络，统一支付 calibration source tail。自有导数与 Bernstein sign/variation 辅助排除
不含临界点的区间；每个 chart、边界与 tail 都须覆盖。全局最大下界来自已评价点，最大上界
来自全部未排除 boxes；最小值反向处理。不能读主 polynomial、root brackets、λ 或源点。
独立 λ 同样按完整 envelope 二分，必须产生相同 source grid/root descriptor，两个 certified
dyadic brackets 必须相交。概率包络必须消费各自整个 root bracket；midpoint 一致不构成认证。
source/cell 比较只在两份首科学回执都生成后发生。

四 joint 与八 cell-single 的两实现数学包络，各自完整包含于原 po0003 同时域才登记
`EXHIBITED_FRAME_WINDOW_MEMBER`；否则 `NOT_CERTIFIED_BY_ENCLOSURE`，保留具体失败分量。
alpha、公开数据、CI、角度、效率域与源取点规则保持。sc0001.1 的 aligned-source contrast
结果另保留；其 aligned mirror null 不自动适用于本版 R-source，不能用旧 null 的拒绝给新源判负。
训练 single residual 和各 paired-single source prediction 均报告，不把单分量 CI 相容升级为
实际 calibration/source/reference-plane 身份。

## 5. 来源支付的泵 actuator 与四角 optimum consumer

Meyer-Scott Appendix A 的 H_spdc 在固定 ε 下使用 `sqrt(2)ε sinγ` 和 `sqrt(2)ε cosγ`。
其实际 optimization 因此固定 raw gain norm gH²+gV²=2ε²；fixed gH 没有这份代码来源。
主文的 pump HWP 固定总 pump polarization norm；将其转换为 gain circle 要支付 equal branch
conversion。unequal κH/κV 对应另一个 gain ellipse，实际比值未绑定，不冒充本版 circle。

从本版 raw kernel 生成 gH0=atanh(sqrt(tH))、gV0=atanh(sqrt(tV))、
G=sqrt(gH0²+gV0²)。具名 source family 固定 G/R/λ/η/background/window，H-dominant pump actuator θ∈[0,π/4]
生成 gH=G cosθ、gV=G sinθ、tH/V=tanh²(gH/V)。原 branch 命名使 θ 与 author γ 互补；
真实 HWP 转角仍为 polarization-balance 转角的一半。泵强重新定义为 constant n、constant q、
fixed gH 或按 joint 调 G，均不属于此 actuator。

receiver angles (a0,a1,b0,b1) 各自独立，模 π；禁止 beta=−alpha 的旧三变量约束。
原印刷 receiver 四角作为读出点；同一源生成
`CH=j00+j01+j10−j11−sA(a0)−sB(b0)`，正值表示 violation。
最优研究同时消费真实 θ actuator 和四个 receiver angles。λ/R/G 不随 Bell objective 重拟合。

两套确定性搜索各自优化同一五坐标，不读取joint counts、CI或公布r作种子。
主路径coarse source-relative grid：θ=[10,20,30,40]°，a0/b0=[−12,−4,4,12]°、
a1/b1=[−36,−24,24,36]°，receiver加入源生δ，共1024点。按score/lexicographic保留前8；
各自Nelder–Mead，simplex step3°、reflection1、expansion2、contraction1/2、shrink1/2，
最多2500迭代、diameter≤1e−7°停止；θ出界拒绝，四角模180°。
随后按十个单坐标±step邻居作严格CH数学包络改善，step=1/20°，最多16 accepted moves/level、
20 halving levels，tie用lexicographic。邻居数是10，不接回旧mirror约束。

独立路径coarse θ=[8,16,24,32,40]°，a0/b0=[−10,−2,2,10]°、
a1/b1=[−34,−22,22,34]°，同样加入自身源生δ，共1280点，保留前8。
使用五坐标循环的coarse全轴scan及黄金分割，axis grid step6°，每轴选最佳grid cell及相邻
周期cell包夹，每次黄金分割最多64步/width≤1e−7°，最多80个完整cycles；更新量≤1e−7°停止。
概率/目标由独立coherent Fock prefix和原tail产生；双方最终候选及公布控制用各自完整数学包络复核。

回执登记已检查的数值重放、起点、停止原因、候选控制及严格score改善。
两实现逐分量容差沿用原r0003：angle .001°、r 1e−5、CH 1e−10。
连续全域global-max kernel证明为false。4096-split interval全域上界可作显式可选诊断，
不作为有限数值比较的新增义务；其未付gap必须保留，不可冒充已证明global optimum。
原门禁的实际source/configuration身份由原合同另外验收。

### 5.1 五个印刷分量的另具名消费者

目标仅在 producer 完成后从冻结 instrument 读取：rpub=VV/HH、a0/a1/b0/b1 四个 receiver 角。
本版 r*=sqrt(tV*/tH*) 是 optimized raw kernel 的 one-pair conditional eigenbasis amplitude ratio，
不是 total-pump balance 的 tanθ，也不是含 R 后某个 lab-basis coefficient 的比值。
R 的 source-to-instrument H/V 身份未识别时，这项比较保持具名 source-eigenbasis 条件范围。

四角各自模 180°规范到 [−90°,90°)，不再由 Alice 两角生成 Bob 两角；不沿用 r0003 的
全局 angle-sign 翻转，因为固定 R 时该变换通常不保持源。实两相位源的合法离散对称为
四角同时 a→2δ−a。优化器同时登记同一源下的两份代表；主代表由 a0−δ≥0 选择（等号
再以 a1−δ≥0，仍等号则 lexicographic）。δ 由 source 读出，不为靠近文档改代表。
目标四角以同一个 source/δ 规则规范，原 receiver 角也原样报告。

`fw_center_five_component_rounding_check` 逐分量报告文档值距中心优化候选的差及原 rounding
half-width：r±.0005，四角各±.05°。它不包含输入 uncertainty box；本项为双实现数值比较，
不登记连续全域optimum的kernel证明。

`fw_Klyshko_DA_nine_point_component_band` 是独立于 r0003 的具名盒合同：center 加
KA=.747±.003、KB=.756±.003、DA target=.996±.001 的八角点。每点先生成 exact raw TA/TB，
再按同一四 single 重新生成 source/R/λ/G，在其 H-dominant gain circle 上做四角 optimization。calibration
tcal、background、window 与全部取点规则固定；HV full fringe 仍是独立校准验收。
每点五分量包络的逐坐标 min/max，再按原 r±.0005、angle±.05°加宽。
必须完成全部九点、各自两实现及 source/calibration/optimization 验收才给该具名 band 判定。
缺点不跳过、失败点不丢弃；双数值候选超容差或搜索未闭合时记录 `NUMERICAL_BAND_UNRESOLVED`。
全部九点闭合后，按实际包含登记 `NUMERICAL_BAND_CONTAINS_ALL_PRINTED_COMPONENTS` 或
`NUMERICAL_DEVIATION_EXCEEDS_DECLARED_BAND`，不把该有限带改称连续域kernel结论。

所有 K targets 保留原公开盒；每个角点的 raw T 通过同一 exact algebraic branch 产生。
K 重读 source law、TA/TB 合法性、HV/DA 全 fringe 或 source generation 失败时，登记
`BAND_CALIBRATION_DOMAIN_NOT_REALISED`，不删角点、切分支、平移容差或选择较易实现的 raw 盒。
若 canonical target 在九点产生不同 receiver-angle 实代表，先登记 representation 差别；
不可把不同目标的坐标混成同一个通过判定。

原 r0003 的中心+16角点包含 q/visibility 的旧模型口；本版九点不替代那17点、旧带或旧
判定。只有原 source/configuration identity 与原 gate 全合同另外闭合时才能更新原 optimum gate。

pair-at-least-one、exactly-one、mean pair number、one-pair conditional amplitude ratio、gain norm
与 eigenaxis另读出。论文 q≈.0005、印刷幅度及角度作来源对比，不进入源/λ/G 生成；approximate q
没有给出估计式与误差，不能生成隐含验收带。

## 6. 验收、失败和独立控制

kernel 目标是 raw source→R 的真实 symmetric tensor action/normalization→同一局域 covariance，
balanced reflection→全 fringe monotonic readout、真实 pump gain norm→四角 consumer。
calibration extrema/root、Gaussian closed vacuum formula 与 full Fock consumers 的证明范围分别登记。
source 欠缺时不引入 completed covariance、visibility extrema、target probability 或 optimum premise。

正控：R=I、一般 R、balanced φ0 whole-Fock invariance、pure H/V、λ=0/.5、两个 mirror signs、
phase-before-R 顺序、source normalization/tail、matched Klyshko 与整个 HV/DA fringe。
反控：把 −25.9 改绝对角、把 π branch 当 R-invariant、旧 δ0 λ、遗漏一个 critical root/q∞、
局部 extrema、Sturm root count 假 bool、未支付 Fock tail、prefix renormalization、窗口后 mixture、
joint 输入源、heldout 行输入源、fixed gH 冒 gain circle、旧 mirror optimizer 冒四角、虚假实际身份。

回执分开记录 source generation、calibration closure、public observable inclusion、strict improvement、
global optimum gap 与实际配置身份。数学相容不能写成 apparatus optimum verified；readiness 和
active card 在草稿阶段不改。未解析数值、非法 source 与具名 source deviation 分别登记。

<!-- FW-FROZEN-BEGIN -->
```json
{
  "version": "p23-frame-window-fw0001",
  "status": "frozen_before_execution",
  "source": "V_number_phase_flip_before_common_real_Jones_rotation_of_two_polarization_TMSV",
  "klyshko_target_center": [
    "0.747",
    "0.756"
  ],
  "klyshko_probability_half_width": "0.003",
  "raw_transmission_representation": "exact_coupled_Klyshko_small_root_quadratic_field",
  "visibility_HV_interval": [
    "0.998",
    "1"
  ],
  "visibility_DA_center": "0.996",
  "visibility_DA_interval": [
    "0.995",
    "0.997"
  ],
  "calibration_geometric_ratio": "1/10000",
  "calibration_window_pulses": 1,
  "calibration_background": "signal_only",
  "calibration_matched_polarization": "original_source_eigenmode_after_same_R",
  "training_rows": [
    0,
    3
  ],
  "training_quantities": "four_local_single_marginals_only",
  "training_signed_A_angles_deg": [
    "21/5",
    "-259/10"
  ],
  "angles_deg": [
    "21/5",
    "-259/10",
    "-21/5",
    "259/10"
  ],
  "window_pulses": 5,
  "background_per_pulse": [
    "89/100000000",
    "32/100000000"
  ],
  "covariance_grid_digits": 15,
  "source_grid_digits": 15,
  "root_precision_digits": 40,
  "lambda_domain": [
    "0",
    "1/2"
  ],
  "lambda_root_rule": "exact_left_threshold_of_complete_DA_visibility",
  "lambda_source_representation": "exact_real_root_descriptor_with_certified_dyadic_enclosure",
  "lambda_midpoint_role": "float_candidate_and_display_only",
  "lambda_bracket_width": "1/1152921504606846976",
  "lambda_decision_cap": 64,
  "fringe_initial_visibility_width": "1/100000000000000",
  "fringe_root_refinement_depth_cap": 256,
  "fringe_sturm_split_cap": 32768,
  "fringe_bernstein_split_cap": 65536,
  "calibration_center_computational_error": "1/100000000000000",
  "source_pair_cutoff": 6,
  "primary_precision_digits": 40,
  "independent_precision_digits": 40,
  "primary_terms": 12,
  "independent_terms": 14,
  "implementation_tolerance": "1/1000000000000",
  "pump_actuator": "fixed_raw_gain_norm_with_polarization_HWP",
  "pump_branch_conversion": "named_equal_branch_conversion",
  "pump_balance_domain_deg": [
    "0",
    "45"
  ],
  "optimization_coordinates": [
    "pump_balance",
    "a0",
    "a1",
    "b0",
    "b1"
  ],
  "optimization_initial_step_deg": "1/20",
  "optimization_neighbours": 10,
  "optimization_accepted_moves_per_level": 16,
  "optimization_halving_levels": 20,
  "global_optimum_split_cap": 4096,
  "global_optimum_gap_tolerance": "1/1000000000000",
  "documented_source": "../../instrument.json",
  "five_component_ratio": "optimized_source_eigenbasis_sqrt_tV_over_tH",
  "five_component_rounding_half_width_r": "1/2000",
  "five_component_rounding_half_width_angle_deg": "1/20",
  "nine_point_band_axes": [
    "Klyshko_A_target",
    "Klyshko_B_target",
    "DA_visibility_target"
  ],
  "nine_point_band_point_count": 9,
  "nine_point_band_replaces_r0003_band": false,
  "public_confidence_report": "../observable-prediction/public-comparison-po0003.json",
  "public_counts": "../observable-prediction/public-observables.json",
  "source_mapping_identified": false,
  "publication_configuration_identified": false,
  "production_admitted": false,
  "actual_window_model_identified": false,
  "calibration_protocol_identified": false,
  "noise_channel_identified": false,
  "source_pair_rate_reference_identified": false,
  "common_Jones_map_identified": false,
  "equal_branch_conversion_identified": false,
  "actual_pump_actuator_identified": false,
  "bell_event_files_read": 0,
  "retrospective": true,
  "primary_optimizer": {
    "pump_grid_deg": [
      10,
      20,
      30,
      40
    ],
    "angle0_grid_deg": [
      -12,
      -4,
      4,
      12
    ],
    "angle1_grid_deg": [
      -36,
      -24,
      24,
      36
    ],
    "keep": 8,
    "simplex_step_deg": "3",
    "iterations": 2500,
    "diameter_stop_deg": "1/10000000",
    "reflection": "1",
    "expansion": "2",
    "contraction": "1/2",
    "shrink": "1/2"
  },
  "independent_optimizer": {
    "pump_grid_deg": [
      8,
      16,
      24,
      32,
      40
    ],
    "angle0_grid_deg": [
      -10,
      -2,
      2,
      10
    ],
    "angle1_grid_deg": [
      -34,
      -22,
      22,
      34
    ],
    "keep": 8,
    "axis_grid_step_deg": "6",
    "golden_steps": 64,
    "golden_width_deg": "1/10000000",
    "cycles": 80,
    "update_stop_deg": "1/10000000"
  },
  "optimization_tolerance": {
    "angle_deg": "1/1000",
    "r": "1/100000",
    "CH": "1/10000000000"
  },
  "global_optimum_kernel_proof": false,
  "global_bound_is_optional_diagnostic": true
}
```
<!-- FW-FROZEN-END -->
