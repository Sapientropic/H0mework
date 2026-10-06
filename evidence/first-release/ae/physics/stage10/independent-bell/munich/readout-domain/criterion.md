# rd0001：完整同源读出域的公开试次裁决

## 源与参数域

原positiveSmoothUnifiedSource、SpinPair.visit 10、material row、whole-ledger及tick16→17固定。
[已认证源口](source-certification-first.json)从原Born概率生成合法读出、连续完整像及精确有理导出。
生成器不接受观测目标概率表或相容性证书。原tb0001构造盲性、mu0001.1理想运输拒绝保持。

每run、每侧、每个local setting各有一个效应坐标`(mu,u,z)`：

```text
-1 <= mu <= 1,
u^2+z^2 <= (1+mu)^2,
u^2+z^2 <= (1-mu)^2.
```

同一local setting跨两个herald共享效应。该连续域完整等于全部合法单位XZ轴与非对称binary
readout通道的联合像，包含负/零gain和圆极点；有理witness不是离散覆盖。
源内部生成gain、canonical轴及两种误分类率。共同depolarizing visibility可吸收入通道，
不加独立参数；herald-dependent制备噪声不属于本合同。

全部四outcome由同一母源生成：

```text
C_h(a,b) = mu_Aa*mu_Bb - sign(h)*u_Aa*u_Bb - z_Aa*z_Bb,
q_hab(x,y) = [1+sign(x)*mu_Aa+sign(y)*mu_Bb+sign(x)*sign(y)*C_h(a,b)]/4.
```

`sign(0)=+1, sign(1)=-1`。两herald相关的差/和给出两个rank1 outer product；
两侧边缘共享于herald及remote setting。参数不得按每格独立改写。
全部32种全局binary重命名保持此完整域，并由参数orbit生成；不从结果选物理字典。

[公开方法约束](method-constraints.md)支付原pure Psi±、两个local beam、逐side/run分离及
同一herald触发序列的名义语义。碎片效率不是F0/F1；k-sigma和器件描述不装为95%CI。
整run固定参数、双侧乘积读出及官方valid-pairs选择后的条件源律是受裁决的具名合同。
给定全部过去及当前herald/settings，该run下一结果的条件概率为同一个q_hab。
本次是已曝光公开数据的回顾性source-domain裁决，不声明认知未曝光或新盲实验。

## 输入与完整序列

只使用原两个官方ZIP及mu0001.1冻结parser/source绑定；保全部20,403个valid pairs原顺序。
原行引用、四种全文件offset、±100ms、raw字段identity、flag及未配对审计沿原准入合同。
重新解码后计数、原pair字节、token字典及原序trial摘要必须和旧冻结first交叉。
不换run、切点、label、分母，不解封ETH，不改publish，不读取新实验或私有校准。
原序records的缓存不进Git；回执绑定其来源及完整内容摘要。

## 完整联合置信域

每run四个LR财富初值均为1；当前结果之前由过去计数固定forecasters：

1. full：每`(h,a,b)`的四outcome Dirichlet(1/2,1/2,1/2,1/2)预测`(2N_xy+1)/(2N+4)`，factor=r_full/q_xy。
2. Alice：全run过去二元Jeffreys预测`(2N_x+1)/(2N+2)`，factor=r_A/q_A(a,x)。
3. Bob：同类全run过去二元预测，factor=r_B/q_B(b,y)。
4. complement：每`(h,a,b,c)`过去二元Jeffreys预测，两个c都先固定；factor=r_c(x)/(q_xy/m_c)，c=x xor y。

`q_A,q_B,m_c`由同一source q求和生成。条件parity参与整个joint factor，不后选择。
四个factor各由归一化forecaster与同一q给出条件均值不超过1；完整support时为1。
zero-support结果在该model下为概率零事件，置信反演直接排除实际出现该结果的point。
固定主财富为
`E=E_full/2+E_A/6+E_B/6+E_complement/6`。
逐setting的model marginal进入Alice/Bob分母，不能以一个pool概率替代。

每run阈值40、anytime alpha1/40；两run联合预算1/20。
完整置信域是全连续source参数域与**全部原序prefix**上`E<40`的交集。
若model对一个已观察outcome给q=0，该point排除；无观察的zero-mass parity不消费条件项。
不得以epsilon替换边界或以优化器状态代替数学裁决。

该固定统计函数在上述conditional-source合同下具有统一覆盖；搜寻nuisance参数或编码orbit
不增加独立model选择次数。程序构造时间不被改写成原实验的预注册资格。
具体地，四因子的源加权和分别为`sum_support r_full`、`sum_support r_A`、
`sum_support r_B`及`sum_c m_c sum_support r_c`，均不超过1。
乘积财富因此为非负supermartingale，固定凸混合保持这个性质；
[Ville界与置信序列](https://arxiv.org/abs/1810.08240)给出每个真实参数的
`P(any prefix E>=40)<=1/40`，两run的union bound给出`1/20`。
原公平零误差面上的complement/Alice/Bob财富回到mu0001.1；新E不小于旧E的一半。
因此April原完整峰值已排除整个零误差面，不能由更宽置信函数洗成通过。

## 生成与独立检查

数值生成可用浮点优化寻找primitive effect候选；terminal目标仅为搜索入口。
候选转换为canonical exact Fraction并先核完整cone。它不携带数值签收权限。
原参数域、预算、forecaster、所有源码及来源先提交，再运行新的统计/拟合。

主检查采用正确向外舍入的Decimal log/exp区间；独立检查采用integer atanh级数、显式尾界
与向外exp区间。source概率及所有primitive保持exact；全prefix的E上界严格低于40才接受
该witness。下界达到40排除point；区间跨阈值时提高精度，不猜结果。
[Decimal合同](https://docs.python.org/3/library/decimal.html)保证`ln/exp`正确舍入；
对输入区间端点计算后再向外扩一ulp，基础算术分别向下及向上舍入。
独立q由原完整八维向量、母操作及reported POVM实际Born收缩生成，不调用主polynomial。
两套检查各支付原序及完整64格，不重复搜索优化器。

全域nonempty的签收条件是每run各有一个合法同源primitive witness，独立核全部prefix
与全部outcome；当前内核一步消费者还逐格核witness严格正support，接回已认证normalizer。
完整carrier保留zero边界，其统计扩展沿前述支持和不等式。
全域reject必须有完整连续域覆盖/解析排除证书，搜索失败不形成no-go。
所有first/attempt独占创建，成功或失败均保留；后续修复另冻版本，不覆盖原结果。

实际闭合输出为完整joint源族及置信交集的相容或拒绝裁决，readiness单独消费它。
它不指定唯一硬件参数，也不以拟合后的相容性替代原理论的独立构造证书。

<!-- MUNICH-READOUT-RD0001-BEGIN -->
```json
{
  "version": "stage10-munich-readout-rd0001",
  "source": "positiveSmoothUnifiedSource",
  "root_visit": 10,
  "current_tick": 16,
  "next_tick": 17,
  "controller_advance": false,
  "runs": ["2016-04-15", "2016-06-14"],
  "carrier": "complete_compact_local_effect_mu_u_z_cone",
  "real_parameters_per_run": 12,
  "shared_across_herald": true,
  "distinct_by_own_setting_side_run": true,
  "fixed_per_run_conditional_source_contract": true,
  "source_preparation": "original_pure_Psi_minus_color_Z_Psi_plus",
  "independent_visibility_parameter": false,
  "fragment_efficiency_used_as_assignment_CI": false,
  "encoding_maps": 32,
  "selection": "all_original_official_pairs_mu0001.1_admission",
  "confidence_kind": "all_prefix_source_parameter_intersection",
  "component_weights": {"full": "1/2", "alice": "1/6", "bob": "1/6", "complement": "1/6"},
  "full_prior": ["1/2", "1/2", "1/2", "1/2"],
  "binary_prior": ["1/2", "1/2"],
  "per_run_alpha": "1/40",
  "familywise_alpha": "1/20",
  "threshold": "40",
  "source_probabilities": "exact_rational_source_polynomial_and_independent_8D_Born",
  "primary_numerics": "outward_Decimal_log_exp",
  "independent_numerics": "integer_atanh_exp_with_explicit_tails",
  "search_is_verdict": false,
  "rational_witness_is_continuous_cover": false,
  "retrospective_public_data": true,
  "human_outcome_unexposed_claimed": false,
  "actual_hardware_identity_claimed": false,
  "original_ideal_rejection_preserved": true
}
```
<!-- MUNICH-READOUT-RD0001-END -->
