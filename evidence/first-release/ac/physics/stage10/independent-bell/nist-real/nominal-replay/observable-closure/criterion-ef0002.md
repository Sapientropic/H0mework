# ef0002：完整标量源域与共同留出预言

ef0001精确中心的两个实根均不合法：一个loss超域，另一个phase coherence>1。
两个独立首回执已经形成；这些是印刷采样中心的结果，不是全部统计域的源族拒绝。
本修订将低计数joint11放回原不确定性域；模型、物理界、原CI、alpha和数值容差保持。
合同/来源先提交，程序和每次修复先提交后执行；旧首回执字节保留。

## 训练接口与整个源slice

源顺序、角、N5/OR、完整λ∈[0,1]、conditional stationary、scaled变量和H/L/T²沿用
[ef0001](criterion.md)。输入仅为00整行的sA0/sB0/j00、11的sA1/sB1，以及
原po0003 `j[3]`的两个CI端点。先验证五个中心均在原训练CI。
joint11的中心值、01/10的outcome分配及CI不进入源生成器。

原CI的共同N和选择预算是已冻结design exposure。这个回顾性划分不宣称统计独立；
固定N、各行denominator、预算及训练端点后，01/10所有outcome重排必须保持生成域。
只修改原CI的heldout条目也必须保持生成域。
全部source/cover/预言先形成，随后才读取heldout观测与CI。

四single给r/m/z/x/h/v/R，joint00给w0。对全部
`e∈(0,min(1,r)]`生成`c(e)=H0(e)/(g0 sqrt(T²(e)))`、`λ(e)=(1−c(e))/2`。
不拟合一个e，不把违法c截成一个物理点。保留整个满足物理界与训练条件的slice。
它是六维训练域内的一个具名子域；五个中心不被宣称为实际真概率。

## 一维半代数合同

`|c|≤1`等价于四次不等式
`Pphase(e)=H0(e)²−g0² T²(e)≤0`。
该等价口限定合法e、h>v>0、r>0、g0≠0；T>0由这些源域条件生成。
从joint11原CI和两fixed singles反N5/OR，得到pulse端点`wlo/whi`。
反根前验证两个`1−sA1−sB1+jCI`端点在(0,1]且有序；无法支付即unresolved，不暗改端点。
令

```
Q1(e)=L1(e)²−g1² T²(e)>0
N1(e)=L1(e)+(g1/g0)H0(e)
Plow(e)=N1(e)−wlo Q1(e)≥0
Phigh(e)=whi Q1(e)−N1(e)≥0
```

Plow/Phigh至多二次。实际源同一个e生成joint00、joint11及两heldout；
g0=0或既有source-axis/pure-mode退化时明确unresolved，不改为另一个slice。

## 完整cover与预言

主实现以有理向外系数的Bernstein凸包评价上述三多项式及Q1；
独立实现自行恢复源和系数，以自有有向区间/Taylor包络评价，不读取主cover或源点。
覆盖从`[0,min(1,r_upper)]`开始，按左/右有理二分，所有末端区间形成无缺口partition。
e=0只作outer closure；合法有限源成员必须e>0。

严格物理/训练违反的整段可排除并登记其证据。
整个区间满足e>0、e≤min(1,r_lower)、Pphase≤0、Plow/Phigh≥0、Q1>0时登记inside。
其余区间二分到width≤2^-40；depth≤64、split≤32768。
达到cap或无法判定的所有区间保留为boundary/unresolved，不能丢弃以使预言变窄。
判定依据是区间端点，不用浮点bool或中心符号代替整个区间。

所有inside和boundary的可能合法子集共同产生01/10的配对预言。
boundary计算可将c的外包与[−1,1]作集合交，明确是合法fiber的outer约束，
不是改造一个违法source；若投影无数学包络，保留[0,1]并记unresolved。
每个区间的两格都来自同一e，不能逐格挑选不同点。
汇总逐分量min/max只作显示，不作为joint可行性充分证书。

规范成员取按lower排序的首个完整inside区间的有理midpoint e；
λ/R/t/loss仍是原观察生成的exact real表达式，interval只作外包。
此规则不看heldout。在独立数值路径中自行生成自己的cover和规范成员；
两个规范点可以不同，不能要求靠相互输出对齐。
交叉验证分别验证对方规范点的同源Fock/Γ和原质量尾、训练资格与全部12个概率，
但必须在两source首回执形成以后。

主source forward直接用原Gaussian law和phase消元式双读出。
独立规范成员从相干Fock/Γ前缀6加原尾计算完整window概率；slice区域另给自有有向数学外包。
precision=40、π20位、trig12/14、原数值容差1e−12保持。
全cover partition、每段分类、未解析段、配对区域、规范成员与六训练资格分别报告。

## 统计与验收

原po0003的12个CI原样消费；alpha=.05、ε=.003、6runs×32767 masks×16features×40保持。
规范成员的全部12数学概率包络包含于原CI才签收
`EXHIBITED_CALIBRATION_FREE_SLICE_MEMBER`。
整个slice预言包络包含于heldout CI可另签收`SLICE_PREDICTION_ENVELOPE_CONTAINED`；
它仍是已暴露数据上这个具名slice的相容性，不授予实际source或整个六维置信fiber的覆盖。
不包含、无inside或cap触发分别记录，不拒整个源族、不改变旧最优性门禁。

必要反控：完整partition缺段/重复段、丢弃boundary、非法midpoint、CI端点篡改、
只改heldout/其CI即改变source、η/λ截值、两个heldout不同e、prefix重归一、
将slice覆盖偷换成完整six-dimensional统计fiber、将source相容改成实际最优复现。
整个source模型、完整Born身份、统计覆盖及实际装置资格按既有独立口径验收。

<!-- EF2-FROZEN-BEGIN -->
```json
{
  "version": "p23-observable-closure-ef0002",
  "status": "frozen_before_execution",
  "parent": "criterion.md",
  "training_rows": [0, 3],
  "training_center_quantities": ["sA0", "sB0", "j00", "sA1", "sB1"],
  "training_interval_quantity": "joint11_original_po0003_CI",
  "held_out_rows": [1, 2],
  "source_slice": "all_legal_scalar_loss_with_five_fixed_training_centers_and_joint11_interval",
  "scalar_cover_width": "1/1099511627776",
  "scalar_cover_depth_cap": 64,
  "scalar_cover_split_cap": 32768,
  "boundary_segments_preserved": true,
  "witness_rule": "midpoint_of_first_complete_inside_interval_in_ascending_loss_order",
  "full_statistical_fiber_certified": false,
  "source_mapping_identified": false,
  "production_admitted": false,
  "apparatus_optimum_verified": false,
  "controller_advance": false,
  "bell_event_files_read": 0,
  "retrospective": true
}
```
<!-- EF2-FROZEN-END -->
