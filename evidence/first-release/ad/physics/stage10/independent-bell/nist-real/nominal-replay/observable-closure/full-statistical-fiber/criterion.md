# ef0003：完整训练统计域的同源纤维与配对读出

公开Table S-II与旧结果已经暴露。本合同生成具名conditional-stationary源law在完整六训练CI中的
全部合法成员、配对留出外包与可认证关系。合同、程序及每次数学修复先提交后执行。
原ef0001/ef0002、r0001/r0002/r0002.1/r0003/r0006首回执与各自判决保原字节。
此处是bounded subordinate optical producer/readout，不改变原root、SpinPair.visit10或tick16→17。

## 源law与统计事件

源law沿用ef0001：两偏振TMSV、每pulse V-number ±phase先于双方共同实Jones R，
未知scalar etaA/etaB、完整lambda∈[0,1]，五fresh pulses的本地any-click，
每pulse独立OR背景bA=89/10^8、bB=32/10^8。nH≥nV≥0，scalar losses在(0,1]。
conditional stationary/window/OR是具名模型资格，不由统计CI冒充实际历史资格。
整个概率域不使用公开K、visibility、泵强、κ、印刷r或optimizer。

输入固定为po0003的原有理CI：
j[0],j[3],sA_cell[0],sA_cell[3],sB_cell[0],sB_cell[3]。
四single与两joint均在完整CI内变化，不固定五个采样中心。
alpha=1/20、16features×40固定赌注×6runs×32767masks与原setting条件界保持。
CI端点只读exact_lower/exact_upper，不重建计数中心或边际预算。
固定共同N=177358351、行denominator、预算和训练端点后，
01/10的outcome重排或留出CI修改不能改变source/fiber生成。

## 同源坐标及完整相位消元

令m=e(nH+nV)/2,z=e(nH−nV)cos(2delta)/2,x=e(nH−nV)sin(2delta)/2，
r=etaA/etaB,e=etaA，R2=z²+x²，T²=(m²−R2)((m+e)²−R2)，k=(1−2lambda)T。
物理域为m≥0,m²≥R2,r>0,0<e≤min(1,r),k²≤T²。

四single的反N5/OR均值为alpha_i、beta_i，来自各CI的单调第五根。
它们成为同一(m,z,x,r)的八个线性半空间：
alpha_i_lo≤m−z cos(2a_i)−x sin(2a_i)≤alpha_i_hi；
r beta_i_lo≤m−z cos(2b_i)−x sin(2b_i)≤r beta_i_hi。

主图谱用四个alpha/beta的完整盒与自由e，独立图谱用上述source polytope与自由e。
sin(2a0)>0、sin(2a1)<0和正beta给出严格非零ratio分母。
A1/A0与B1/B0的CI不交叠生成z>0、R2>0，不人为另选source轴。
这些排除必须由有理/trig包络实际验收；失败即保留退化而不换模型。
r和协方差初始盒由四single CI的正系数ratio与线性消元生成；
独立可另消费PSD/非平行方向给出的紧m界。不得引入人工eta下限。
e=0只属于紧致outer closure，不生成有限Snapshot。

每格由同一source给D=(1+meanA)(1+meanB)，
L=D−[h(h+e)U²+v(v+e)V²]/r，g=2UV/r，E=L²−g²T²，
其中h=m+sqrt(R2),v=m−sqrt(R2),U=sin(a−delta)sin(b−delta),V=cos(a−delta)cos(b−delta)。
pulse双无点击为w=(L+gk)/E，E由同源合法物理域保持正。

两个joint CI各生成一个共同k线性slab：
w00_lo E00−L00≤g00 k≤w00_hi E00−L00，
w11_lo E11−L11≤g11 k≤w11_hi E11−L11。
与[-T,T]交，整个非空区间保留。g=0只测试常数约束，不能除零或删除该纤维。
T=0时k=0，lambda的全部[0,1]保留为读出等价fiber。
二次/一次/恒零、多根与重根由自由e×共同k域自动保留，不挑最吻合分支。

可用无平方根的同源系数：
d=cos(a−b),Y=z cos(a+b)+x sin(a+b),A=m²+R2+em，
ell=2R2(1+meanA)(r+r meanB)−A(R2 d²+Y²)+2R2(2m+e)dY，
gamma=R2 d²−Y²，w=2rR2(ell+gamma k)/(ell²−gamma²T²)。
source矩阵或有向区间导出的代数等价稳定式允许；所有新式先冻结并由实际Born读出核对。
near-one的第五根可用有理binomial Taylor与显式几何余项，不使用浮点bool裁决。
pulse covariance和N5 small-click展开可避免真空相消，不能改变phase-before-window规则。

## 全域cover与配对读出

cover只在五维基域上二分，k由完整共同slab消元。
主路径先按loss轴二分至normalized width≤1/32，再按最大normalized width/固定轴次序；
独立路径用线性halfspace contractor和source矩形的最大relative width。
所有contractor只做可证明的outer收缩，不能按midpoint排除整块。
排除必须有整块物理、single或joint训练违反；所有剩余块、cap与boundary保留。
严格inside可额外认证，但coverage不依赖inside分类。全树无缺叶、重叶或丢边界。

每叶保存同一source基域、共同k域与两格共享k的配对readout；
所有四outcome、single、joint、两个joint之和/差与N5 CH由同一source生成。
分量hull只作外包和展示，不代替共同可行源。
g跨零或e=0 closure不能直接求商时保留合法outer；不得据此缩窄纤维。

固定规则从训练域产生非空成员：四single坐标依次取midpoint、1/4、3/4、lower、upper；
loss j/64，j=1..64；相位可行区间依次取midpoint、lower、upper。
按固定lex顺序保留至多256个合法成员。候选只用训练CI，不读取留出。
每个成员须证明物理合法与六训练概率数学包络落入原CI；
没有候选不拒整个fiber，也不把旧ef2成员字段作为新生成器输入。
独立路径可从自有polytope及同一公开训练坐标独立生成其成员，保存差异。

source域、cover及成员的配对预测完整形成并输出source-stage digest后，才读取留出CI。
原公开01/10 CI用于裁决：uniform contained、具体训练合法越界成员、或outer尚不能裁决。
若uniform失败仍签收非空/全域coverage/共享相位及no-signaling关系，不放宽CI。
另一后验集合F_all=F_train∩全部留出CI只能作为明确的回顾性过滤结果，
不得冒称新的留出预测或让其反向改变F_train。

## 双实现、内核与消费者

主路径有向有理Gaussian law，独立路径独立source-space cover与实际端口读出。
规范成员以normalized occupation Γ/Fock prefix6加原numberMass尾独立核对，
可直接计算clicked Born正项，真空严格0，前缀不重归一。
全域Gaussian代数外包与实际数值Born比较按各自范围记录；
不由有限prefix或双实现一致授予一般无限Born/determinant的新增Lean内核身份。

两条科学源码与首回执形成前不互读；共同sources manifest与本合同是唯一共享科学输入。
交叉可以共享公开训练坐标/loss/phase recipe，再各自重生源；外国保存的源字段或概率只比较。
最终消费者核来源、树完整性、全部保留区域、成员/实际Born、配对读出和统计域角色。
新公开认证字段独立消费，原nominal_apparatus_optimum及r6负向门禁保持。
实际source/epoch身份不作为条件fiber certificate的新前提，也不由该certificate自动赋予。

正控覆盖合法source、共享phase、g=0、pure-mode和no-signaling。
反控覆盖丢叶/重叶/丢boundary、cap假complete、五中心冒完整CI、误读heldout、伪inside、
两格选不同k、非法loss/phase、窗口后混合、prefix重归一、source scripts注入和force-pass。
所有结果保留原alpha、CI、模型law与public exposure身份；scope旗标直接由实际验收生成。

<!-- FULL-FIBER-FROZEN-BEGIN -->
```json
{
  "version":"p23-full-statistical-fiber-ef0003",
  "status":"frozen_before_execution",
  "parent_criterion":"../criterion.md",
  "training_rows":[0,3],
  "held_out_rows":[1,2],
  "training_ci_fields":["sA_cell[0]","sB_cell[0]","sA_cell[3]","sB_cell[3]","j[0]","j[3]"],
  "all_training_intervals_used":true,
  "conditional_source_law":"two_TMSV_V_number_phase_before_common_real_R_scalar_loss_fresh_N5_local_OR",
  "angles_deg":["21/5","-259/10","-21/5","259/10"],
  "window_pulses":5,
  "background_per_pulse":["89/100000000","32/100000000"],
  "alpha":"1/20",
  "features_in_global_union":16,
  "fixed_bets":40,
  "runs_covered":6,
  "pulse_subsets_covered":32767,
  "settings_probability_bounds":["994009/4000000","1006009/4000000"],
  "base_cover_dimensions":5,
  "phase_variable":"k=(1-2lambda)*sqrt(T2)",
  "complete_phase_slab_intersection":true,
  "source_polytope_contraction_is_outer_only":true,
  "loss_zero_is_closure_only":true,
  "pure_mode_and_zero_coupling_preserved":true,
  "primary_split_cap":16384,
  "independent_split_cap":24576,
  "max_depth":48,
  "normalized_width_stop":"1/128",
  "loss_first_normalized_width":"1/32",
  "precision_digits":50,
  "binomial_terms":14,
  "binomial_input_abs_max":"1/100",
  "primary_trig_terms":12,
  "independent_trig_terms":14,
  "pi":["3.14159265358979323846","3.14159265358979323847"],
  "witness_axis_fractions":["1/2","1/4","3/4","0","1"],
  "witness_loss_denominator":64,
  "member_limit":256,
  "source_pair_cutoff":6,
  "comparison_tolerance":"1/1000000000000",
  "new_full_Born_kernel_claim":false,
  "new_statistical_coverage_kernel_claim":false,
  "source_mapping_identified":false,
  "publication_configuration_identified":false,
  "actual_epoch_identified":false,
  "apparatus_optimum_verified":false,
  "controller_advance":false,
  "bell_event_files_read":0,
  "retrospective":true
}
```
<!-- FULL-FIBER-FROZEN-END -->
