# r0006：同源raw校准与名义五控制重放

版本`nominal-environment-replay-r0006`。本判据先提交冻结，再运行任何本版CH搜索。
旧r0001/r0002/r0002.1/r0003与所有已冻结源研究回执保持。
已经见过旧模型最优带，科学规格由原公开设计与具名光学作用确定；不以接近公布r/角选择源。

## 1. 输入与模型身份

唯一输入生成合同是[nec0001](observable-closure/environment-source/calibration-criterion.md)，
先冻`23294e59d9`。它分别消费原Klyshko百分数、背景本地窗、两个raw可见度与公开16°总pair读出。
同一个固定G产生reference制备及balanced calibration，实际端口产生完整计数。
默认对称环境分解的17点进入名义带；两个中心单侧分解是具名override，各自裁决，不合并带。
所有合法校准根保留来源和branch身份，任何未解析点/根都保留UNRESOLVED，不能删去后生成完整带。

名义源由等branch conversion、固定G、phase0和固定环境作用定义，来自打印设计Hamiltonian及
公开不可区分性机制；它是独立说明的名义物理规格。实际原optimizer配置没有由数值拟合追认。
原名义合同允许独立说明的装置目标与公开信道输入；逐run Drive、绝对mW或actual XOR3 epoch
不新增为名义门禁前提。

主、独立两实现各自解析本判据与nec，消费各自先冻结的calibration首回执及自己的源程序。
两套新重放源码与首输出形成前不互读，源字段/概率只在双首冻结后交叉。
公布instrument仅在所有最优点形成之后生成comparisons，不进入calibration、搜索、起点或选根。

## 2. 同source控制与完整读出

保持G、两scalar透射、环境c/allocation、phase和背景，控制beta∈[0°,45°]改变
`gH=G cos beta`、`gV=G sin beta`；原paired振幅生成`tP=tanh(gP)^2`与Z。
实际单对VV/HH振幅比是`tanh(gV)/tanh(gH)`，记录为r_one_pair；
不能以tan(beta)代替，也不能固定pair量或每次重标定环境/损失来更新source。

四实receiver角(a0,a1,b0,b1)各自独立，原生V-port向量为(sin a,cos a)，
同一Pol⊗Env和全部n效果生成完整local/joint probability。
主要目标保留原设计的N1 raw CH：
`CH=J00+J01+J10−J11−SA(a0)−SB(b0)`，正值表示违反。
N5 any-click仅为固定读出诊断，不进入本名义优化；不能将pulse joint相加冒充窗口joint。

可用Gaussian闭式搜索候选，最终每point候选均须由该路径的实际源/端口区间复核。
独立实现另外以total-pair≤6的coherent occupation Born加原numberMass尾消费全部候选。
前缀不重新归一；有限计算或双实现一致不授予连续全域argmax内核结论。

## 3. 五维确定性搜索

beta有界，四receiver角模180°折回[-90°,90°)。只允许同时反号的实源等值规范化，
取a0≥0；不交换H/V、primed/unprimed、party或三个不同校准模型。

主路径在每point执行完整1024点网格：beta=[10,20,30,40]，
a0/b0=[−12,−4,4,12]，a1/b1=[−36,−24,24,36]，score/lexicographic保留前8。
独立Nelder–Mead step3°，reflection1、expansion2、contraction1/2、shrink1/2，
最多5000迭代，diameter≤1e−7°停止，beta越界拒绝。
按十个单坐标±step邻居作同模型细化，step=.05°、最多16次严格accepted moves/level，
20个halving levels。记录停止原因和全部候选；自己的center候选可作为角点额外起点。

独立路径每point执行完整1280点网格：beta=[8,16,24,32,40]，
a0/b0=[−10,−2,2,10]，a1/b1=[−34,−22,22,34]，保留前8。
五坐标循环全轴scan，grid step6°，选最佳grid cell及相邻周期cell包夹，再黄金分割，
最多80个cycles、每线最多80步/width≤1e−7°，whole-cycle改变量≤1e−7°停止。
它不调用主概率或优化函数，也不从主输出取source/seed。
各路径可使用代数等价且保真空消去的稳定式，所有新式必须先冻结再执行并经实际Born读出核对。

## 4. 数值带与消费者

默认17点按nec的四轴顺序保留，包括所有校准root branch；
各模型/branch分别生成r和四角的分量包络，加原r±.0005与角±.05°。
同一个branch的五文档值全部在带内才为CONSISTENT，否则为DEVIATION；
不能将互异branch/override的分量带拼成通过。未完成校准/搜索或独立复核记UNRESOLVED。
逐point独立容差沿用r0003：r1e−5、angle.001°、CH1e−10，源/readout容差沿用nec1e−12。

真实文档值从原instrument生成，r=amplitude_VV/amplitude_HH、四角由原setting角色读取；
不调整振幅舍入传播来扩大原.0005，也不依据现有结果扩大输入域。
两份来源绑定、全部point/branch、actual-source读出、带与逐比较都通过，消费者才消费名义判决。
原r0003负向回执保留历史身份；新版本的pass/fail如实记录。
生产路径拒绝合成回执；测试正控、显式disable/JSON-only override及look-alike模型分别验收。

## 5. 冻结字段

<!-- NOMINAL-ENVIRONMENT-FROZEN-BEGIN -->
```json
{
  "criterion_version": "nominal-environment-replay-r0006",
  "status": "frozen_before_execution",
  "calibration_version": "p23-nominal-environment-calibration-nec0001",
  "calibration_contract_freeze": "23294e59d9",
  "nominal_role": "independently_specified_equal_branch_fixed_environment_model",
  "production_allocation": "symmetric",
  "center_allocation_overrides": ["Alice_rank_one", "Bob_rank_one"],
  "default_box_point_count": 17,
  "total_points_with_overrides": 19,
  "all_physical_calibration_roots_retained": true,
  "source_gain_update": "fixed_G_times_cos_sin_beta",
  "source_phase": ["1", "0"],
  "receiver_angle_degrees_of_freedom": 4,
  "receiver_coordinate_order": ["a0", "a1", "b0", "b1"],
  "objective": "raw_CH_LHS_minus_RHS",
  "objective_pulses": 1,
  "diagnostic_pulses": 5,
  "pump_domain_deg": ["0", "45"],
  "receiver_period_deg": "180",
  "primary_optimizer": {
    "pump_grid_deg": [10,20,30,40],
    "angle0_grid_deg": [-12,-4,4,12],
    "angle1_grid_deg": [-36,-24,24,36],
    "keep": 8, "simplex_step_deg":"3", "iterations":5000,
    "diameter_stop_deg":"1e-7", "neighbor_count":10,
    "neighbor_step_deg":".05", "accepted_moves_per_level":16, "halving_levels":20
  },
  "independent_optimizer": {
    "pump_grid_deg": [8,16,24,32,40],
    "angle0_grid_deg": [-10,-2,2,10],
    "angle1_grid_deg": [-34,-22,22,34],
    "keep":8, "axis_grid_step_deg":"6", "coordinate_cycles":80,
    "golden_steps":80, "coordinate_stop_deg":"1e-7"
  },
  "band": {"r_widen":".0005", "angle_widen_deg":".05"},
  "tolerance": {"r":"1e-5", "angle_deg":".001", "CH_abs":"1e-10"},
  "source_readout_tolerance":"1e-12",
  "total_pair_prefix":6,
  "prefix_renormalized":false,
  "input_sources":[
    "observable-closure/environment-source/calibration-criterion.md",
    "observable-closure/environment-source/calibration-sources.json",
    "observable-closure/environment-source/sector-certification.json",
    "observable-closure/environment-source/verification.json"
  ],
  "documented_values_source":"../instrument.json",
  "outputs": {
    "primary":"observable-closure/environment-source/replay-r0006.json",
    "independent":"observable-closure/environment-source/independent-replay-r0006.json",
    "verification":"observable-closure/environment-source/replay-verification-r0006.json"
  },
  "actual_publication_configuration_identified":false,
  "global_argmax_kernel_proof":false,
  "new_full_Born_or_Gaussian_determinant_kernel_claim":false,
  "controller_advance":false,
  "retrospective":true,
  "event_files_read":0
}
```
<!-- NOMINAL-ENVIRONMENT-FROZEN-END -->
