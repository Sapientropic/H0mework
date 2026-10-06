# cb0001：公开single校准的完整源与四joint预言

2026-10-02。合同、来源、每份程序与Lean候选先提交，再执行。
公开结果已暴露，本版是回顾性条件模型检验。全部历史冻结资产保持。

## 共同源及校准规则

原始源为gw0001的两偏振TMSV，tH,tV∈[0,1)。每pulse独立应用V-number phase flip：
ρ=(1−λ)|ψφ=0⟩⟨ψφ=0|+λ|ψφ=π⟩⟨ψφ=π|，0≤λ≤1。
它是实际unitary phase作用的经典混合；不以Γ替换Gaussian determinant内的coherence项。
同一loss/noise作用于最大态校准与非最大态候选。每侧H/V透射相等，固定为公开效率中心。
这些是具名模型责任，不赋予实际NIST校准或noise机制身份。

指定Klyshko校准为单偏振、单pulse、signal-only，geometric ratio t_cal=1/10000。
原cal0001完整bucket读出及2n bound核生成效率进入公开k=1区间，不能把T当精确ηK。
最大态校准tH=tV=t_cal、同loss/noise、单pulse、signal-only。
HV固定Bob0、Alice0/90；DA固定Bob45、Alice±45，并核全fringe的单调性。

n_cal=t_cal/(1−t_cal)，A=ηA、B=ηB、U=A+B−AB，
Jplus=1−1/(1+n_cal A)−1/(1+n_cal B)+1/(1+n_cal U)，
Jminus=[n_cal A/(1+n_cal A)] [n_cal B/(1+n_cal B)]。
Vbase=(Jplus−Jminus)/(Jplus+Jminus)，λ=(1−V_DA/Vbase)/2，V_DA=.996。
λ合法才构造；不截值、不用joint或CI修正λ。HV应在[.998,1]，DA应在[.995,.997]。
若D=(1+n_cal A)(1+n_cal B)、K=n_cal(1+n_cal)AB，
(1−λ)(D−K)^2≥λD^2支付DA完整扫角的单调性，端点对比才作为完整visibility读出。

## single-only源构造

只消费SI的00与11行四个本地single marginals及各自完整row denominator。
不消费任何独立joint统计量，不消费01/10的任何outcome、global N、目标最优点或CI。
固定N=5及每pulseOR背景，单边probability p生成
µ=(1−b)/(1−p)^(1/5)−1。
对两个绝对角a0=4.2°、a1=25.9°，令
u_i=(µAi/ηA+µBi/ηB)/2，d=sin²a1−sin²a0>0，
Δ=(u1−u0)/d，nV=u0−sin²a0 Δ，nH=nV+Δ。
tH=nH/(1+nH)、tV同。它们由single校准生成，不输入论文的最优态比例。
第5次根使用精确有理outward enclosure；源取15位最近有理grid point，
两端须给同一grid point。非法均值、无法确定grid或非法λ记录失败，不另找种子。

## 完整Fock/window消费者

两相位source各自从raw参数生成全photon probabilities；先在单pulse no-click上按λ混合，
再作五个独立pulse的any-click及OR背景。窗口后才混合是不同源历史，反控必须拒绝。
主路径使用源生Gaussian读出；独立路径分别求两相位coherent number-basis前缀，
精确支付h+v>6的原源质量，再混合及生成窗口。有限前缀不重新归一。

全部四joint及八cell-single均进入原po0003同时统计域；不改变alpha、数据或CI。
12个完整数学包络分别包含于原域才记录EXHIBITED_PUBLICLY_CALIBRATED_WINDOW_MEMBER。
否则记录NOT_CERTIFIED_BY_ENCLOSURE，具体分量保持。两实现各自生成首回执后才比较。

source的pair-at-least-one、exactly-one、mean和单对conditional amplitude ratio另报告。
论文q≈.0005及印刷态幅度只作后验来源对比，不作为source构造或新增验收带。
公开q未给估计式、误差、参考面或epoch，不能用approximate文字生成隐含容差。

正控覆盖λ=0/.5、phase±、calibration visibility、matched Klyshko、vacuum和零/单位loss。
信息流反控分别改变joint但保持训练marginals、改变整个01/10，源必须不变；
另拒绝wrong phase mixture、漏尾/归一、假calibration身份、数字冒proof bool及CI放宽。
不读取trial/count archives、不修改publish或发送外联。root/whole-ledger与旧optimum门禁保持。

<!-- CB-FROZEN-BEGIN -->
```json
{
  "version": "p23-calibrated-window-cb0001",
  "source": "independent_per_pulse_V_number_phase_flip_of_pair_only_two_polarization_TMSV",
  "eta_center": ["0.747", "0.756"],
  "eta_probability_half_width": "0.003",
  "visibility_HV_interval": ["0.998", "1"],
  "visibility_DA_center": "0.996",
  "visibility_DA_interval": ["0.995", "0.997"],
  "calibration_geometric_ratio": "1/10000",
  "calibration_window_pulses": 1,
  "calibration_background": "signal_only",
  "training_rows": [0, 3],
  "training_quantities": "four_local_single_marginals_only",
  "window_pulses": 5,
  "angles_deg": ["21/5", "-259/10", "-21/5", "259/10"],
  "background_per_pulse": ["89/100000000", "32/100000000"],
  "source_grid_digits": 15,
  "root_precision_digits": 40,
  "source_pair_cutoff": 6,
  "primary_precision_digits": 36,
  "independent_precision_digits": 30,
  "primary_terms": 12,
  "independent_terms": 14,
  "implementation_tolerance": "1/1000000000000",
  "public_confidence_report": "../observable-prediction/public-comparison-po0003.json",
  "public_counts": "../observable-prediction/public-observables.json",
  "source_mapping_identified": false,
  "publication_configuration_identified": false,
  "production_admitted": false,
  "actual_window_model_identified": false,
  "calibration_protocol_identified": false,
  "noise_channel_identified": false,
  "source_pair_rate_reference_identified": false,
  "bell_event_files_read": 0,
  "retrospective": true
}
```
<!-- CB-FROZEN-END -->
