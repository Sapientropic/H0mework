# nec0001：公开名义读出生成同源校准

公开名义Klyshko、发对概率、HV/DA可见度生成同一个paired source与固定环境作用。
本版只生成校准源，不优化CH，不读取Table S-II或公布r/角。
合同、来源、程序及每次修复先提交冻结，再执行新数学计算。
原r0001/r0002/r0002.1/r0003与全部已冻研究输出保持。

## 名义物理规格与来源角色

原Meyer-Scott Appendix A的两个commuting pair terms支付固定raw gain norm与等branch conversion。
公开Fig.1给出名义pump方向16°，DAQ给PumpHWP8°及balanced pump22.5°命令。
因此gain为`gH=G cos beta`、`gV=G sin beta`，`tP=tanh(gP)^2`，
`Z=(1-tH)(1-tV)`。使用physical H/V标签与原生V-port，source phase固定0。
这里生成具名、独立说明的名义模型，不把等conversion追认为实际装置的已测属性。
pd/ef旧条件族的gain、loss、lambda和κ全部不进入新源。

每pulse至少一对的源读出`q=1-Z`，在公开reference beta16°处等于公布名义q；
单个balanced HH强度与这个总量保持不同定义。先用该读出反解G，
再在同一G的beta45°产生balanced calibration source。
这项明确读法消费原q中心.0005及[.0004,.0006]盒，不能将q再次直接赋给HH epsilon²。
calibration gain和实验源gain由同一固定G产生，绝对功率在本名义规格中无需单独输入。

本地scalar透射TA、TB由matched V/V校准产生，固定环境ξ跨制备保持。
背景是公开625/781ps本地窗口的每pulse独立OR概率，calibration按N1测量口读回；
它没有被换成N5试次，也不以DAQ raw-record sums冒充local any-click。
K_A=J/S_B、K_B=J/S_A，party身份由herald分母确定，不依软件字段名。
双百分数74.7±0.3%／75.6±0.3%转换为概率.747±.003／.756±.003。
两个实现分别解析文字与机读块，单位冲突即拒绝生成。

公开最大态HV=.999±.001与DA=.996±.001分别消费各自raw coincidence fringe。
不把DA可见度直接设成环境overlap，也不将两个不同basis读数合并成一个visibility。
默认固定环境分解为`xiA=xiB=sqrt(c)`，即uA=uB=c、xiA xiB=c≥0。
这是显式对称mode分解；两个中心override分别取`(xiA,xiB)=(1,c)`与`(c,1)`，
各自从同样raw读出重新生成c。override不合并进默认源盒或未来最优带。
所有分解都来自已证六端口，无未知completed Gram、相位channel或非最大态输入。

## Klyshko全部物理解

balanced单个V branch的thermal mean为`n=t/(1-t)`。
令`a=S_A`、`r=K_B/K_A`、`S_B=r a`、`w=1+r-K_B`、`zeta=(1-bA)(1-bB)`，

```
Q(a) = q0 + q1 a + q2 a²
q0 = 1-bA-bB-bA*bB/n
q1 = bA*r+bB+(bB+r*bA)/n
q2 = -r*(1+1/n)
P(a) = (1-w*a) Q(a) - zeta*(1-a)*(1-r*a)
TA = (a-bA)/(n*(1-a))
TB = (r*a-bB)/(n*(1-r*a))
```

P的全部实根由完整有理Sturm隔离，不用局部Newton择根。
根只在`a∈[max(bA,bB/r), min((bA+n)/(1+n),(bB+n)/(r*(1+n)))]`内有物理资格，
正herald、非零合法分母、TA/TB∈[0,1]及原raw K往返都要验收。
无合法根记MODEL_INPUT_REJECTED；多个合法根全部保留，不择最接近K或公布最优点的根。

数值adapter先以源生G有理区间确定唯一15位nearest grid点，半格tie朝+∞；
没有唯一grid点即SOURCE_GRID_UNRESOLVED。balanced n同样确定唯一15位grid。
用该有理n建立精确Sturm多项式，保留原G/n外包及grid误差；
原真实source/calibration forward必须包含目标读出或与目标相差≤1e−12。
grid只支付数值输入转换，不能登记为exact校准内核身份。

## 完整HV/DA条纹与环境逆读

balanced source、scalar透射及real环境下，以z=cos²a∈[0,1]表示HV条纹、
以y=sin2a∈[-1,1]表示固定Bob45°的DA条纹。
从实际E/X和同源determinant生成完整J(z)/J(y)，不只把四个端点写成completed extrema。

HV的全z导数须由有理区间在全部z域证明严格为正；其max/min才可读作a0/90°端点。
DA先保留c∈[0,1]全部合法域。对c∈[0,.9]，从原n≤1的Born、
真实n≥2质量尾及独立OR背景生成全fringe对比度上界，只有严格小于所有target才排除。
对剩余c∈[.9,1]，须由完整J(y)导数区间证明全域严格为正，
才可用y=±1计算raw visibility=(Jmax-Jmin)/(Jmax+Jmin)。
若该充分证书失败，保留UNRESOLVED；不能靠端点或局部optimizer宣称完整极值。
通用q=tan a导数degree≤14的口已验证，但不借旧rank1的six-degree root cap。

默认和两个override的c分别独立有理二分[.9,1]，整个根区间运输至ξ、原端口和所有readout。
二分前须验证target被端点区间包围，且由实际公式生成的dV/dc全域严格为正；
精度不足如实UNRESOLVED，不截c到[0,1]或以target直接赋overlap。
HV全fringe外包必须落入公开[.998,1]，DA读回目标且width≤1e−12。
这些是nominal measurement roles，不授予原始校准逐run身份。

## 独立路径与验收

主实现可消费已冻结六rows/determinant，独立实现从Pol⊗Env实际投影和自己的interval algebra
生成读出，并在全部校准源用total-pair≤6的相干occupation Born加原尾核对。
两边分别读本判据、生成中心加16角点与两个中心override，源/首回执形成前不互读新代码/结果。
没有foreign gains/loss/overlap或概率进入forward。
共有源坐标由冻结输入及相同grid规则生成，双方各自保留全部根区间；
交叉核G/n/TA/TB/c、full-fringe证书、K/visibility及同源非最大态参考forward。
尚不产生最优点、五分量带或apparatus_optimum旗标。

<!-- NEC-FROZEN-BEGIN -->
```json
{
  "version": "p23-nominal-environment-calibration-nec0001",
  "status": "frozen_before_execution",
  "nominal_role": "independently_specified_fixed_environment_and_equal_branch_conversion",
  "reference_pump_beta_deg": "16",
  "balanced_pump_beta_deg": "45",
  "source_phase": ["1", "0"],
  "pair_quantity": "probability_at_least_one_total_pair_at_reference_drive",
  "K_A": {"center":".747", "half_width":".003"},
  "K_B": {"center":".756", "half_width":".003"},
  "pair_probability": {"center":".0005", "box_low":".0004", "box_high":".0006"},
  "HV_raw_visibility": {"center":".999", "half_width":".001", "box_low":".998", "box_high":"1"},
  "DA_raw_visibility": {"center":".996", "half_width":".001", "box_low":".995", "box_high":".997"},
  "background_per_pulse": [".00000089", ".00000032"],
  "calibration_pulses": 1,
  "calibration_K_basis": "matched_V_V_balanced_source",
  "HV_fixed_Bob_deg": "0",
  "DA_fixed_Bob_deg": "45",
  "default_allocation": "symmetric",
  "center_allocation_overrides": ["Alice_rank_one", "Bob_rank_one"],
  "four_box_axes_order": ["K_A", "K_B", "pair_probability", "DA_raw_visibility"],
  "box_corner_order": "itertools.product(low,high), leftmost_axis_changes_slowest",
  "default_point_count": 17,
  "total_source_points_with_overrides": 19,
  "precision_digits": 40,
  "source_grid_digits": 15,
  "source_grid_tie_rule": "toward_positive_infinity",
  "root_interval_max_width": "1e-16",
  "readout_tolerance": "1e-12",
  "total_pair_prefix": 6,
  "prefix_renormalized": false,
  "full_fringe_derivative_degree_cap": 14,
  "coherence_low_domain": ["0", ".9"],
  "coherence_inverse_domain": [".9", "1"],
  "CH_optimization_executed": false,
  "old_scalar_inverse_gain_or_published_controls_admitted": false,
  "source_mapping_identified": false,
  "exact_calibration_inverse_kernel_claim": false,
  "new_full_Born_or_Gaussian_determinant_kernel_claim": false,
  "actual_source_or_hardware_identity_verified": false,
  "apparatus_optimum_verified": false,
  "controller_advance": false,
  "retrospective": true,
  "event_files_read": 0
}
```
<!-- NEC-FROZEN-END -->
