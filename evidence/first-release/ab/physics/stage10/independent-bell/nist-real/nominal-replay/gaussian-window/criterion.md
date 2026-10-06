# gw0001：实际几何源生成全Fock与五窗口读出

2026-10-01。op0001/po0003公共源族已签收；旧最优性判决保持。
本合同与来源先提交，每份新程序/Lean候选也先提交，再执行新数值或编译。
公开16计数、三个已有成员与所有历史结果已暴露，本版为回顾性条件模型检验。
所有旧冻结criterion、程序和回执保持，不读取trial/count archives，不修改publish或外联。

## 源primitive与原生count law

本版以两条HH/VV单模pair kernel、固定真空和实际本地保偏振纯损失作为primitive。
每pulse原生生成两独立TMSV源：
ψ=√((1−tH)(1−tV)) Σh,v≥0 tH^(h/2)tV^(v/2)e^(ivφ)|h,v>_A|h,v>_B。
tH,tV∈[0,1)，相位由实际unit-circle参数生成，全部number sectors保留；
归一因子与count PGF来自geometric series，不接纳目标概率、covariance、Wick或PGF证书。
入臂H/V的真实损失/探测透射TAH,TAV,TBH,TBV∈[0,1]，
源与effect同用H-first；V参考click向量(sin a,cos a)。
这是明确的single-mode Gaussian子族，不授予任意多模源或实际NIST身份。
原N=4截断源及加性D(n)+d不被提升为此unbounded source。

nH=tH/(1−tH)、nV同。源生成µA=nH TAH sin²a+nV TAV cos²a，µB同，
κH=√(nH(1+nH)TAH TBH)、κV同，
C=κH² sin²a sin²b+κV² cos²a cos²b
+2κHκV cosφ sin a cos a sin b cos b。
局域anomalous与正常跨臂相关为0，从pair-only真空源生成。
单pulse无点击概率P0A=1/(1+µA)、P0B同，
P00=1/[(1+µA)(1+µB)−C]。这些是实际Gaussian状态/threshold效果的读出，
不以caller已准备的covariance替代源。intensity coincidence I=µAµB+C另记录。

窗口明确为相同raw kernel、fresh vacuum和同loss重复N次，本地各接受对应N个slots；
源原生生成product time-bin state。两侧outcome是本地any-click，joint为两者同时any-click，
故J_N=1−P0A^N−P0B^N+P00^N。不是pair-time matching或每pulse计数相加。
独立每窗背景以OR加入，b_N=1−(1−b)^N；无限Fock不使用加性背景effects。
fixed-kernel候选的mean等于其恒定概率；这不是对实际任意漂移历史的pointwise预算。

## 公共校准成员构造

固定消费po0003的independent_OR成员七坐标，来源由完整10格未读的三格训练生成。
这些坐标只作本版候选构造种子，不被宣称为实际photon means。
设公共窗口N=5；对每pol令A=AH或AV、B=BH或BV、L=H或V。
den=N L−AB须>0，n=AB/den、TA=den/(N B)、TB=den/(N A)，t=n/(1+n)。
只按此固定转换生成原始源/loss参数，不用任何目标rate、CI或held-out修正这些参数。
cosφ=X/√HV，选择unit-circle上非负sinφ的共同源相位；它不是新的实装相位估计。
若合法性条件失败则记录NO_VALID_CALIBRATION_SEED，不截TA/TB或另找候选。
构造后从raw t/loss/phase重新生成µ/C/PGF和全Fock概率，核种子坐标的代数映射。

冻结po0003的全部12个公共CI直接复用，不改变alpha、setting/source假设、数据或置信域。
全部Gaussian窗口概率数学包络落入同一CI才记EXHIBITED_FULL_FOCK_WINDOW_MEMBER。
若不能认证记录NOT_CERTIFIED_BY_ENCLOSURE；真实点、数学外包络和统计域分别报告。
不优化或重算原名义最优点；family compatibility不识别actual source或原优化配置。

## 独立Fock与误差支付

主实现消费源生thermal/anomalous对象及Gaussian vacuum determinant，使用精确有理外包络。
独立实现直接从上述ψ求number-basis Born和本地no-click effect的对称张量幂Γ(E)，
E=I−diag(√T_H,√T_V)|v><v|diag(√T_H,√T_V)，
不调用Gaussian vacuum/µ/C函数、主代码或主数值作为概率输入。
固定总pair sector h+v≤6；剩余probability为exact geometric尾
1−(1−tH)(1−tV) Σn≤6 Σh≤n tH^h tV^(n−h)。
no-click effect number-conserving且0≤Γ(E)≤1，尾sector对各no-click概率贡献在[0,tail]。
完整window概率在尾支付后生成；截断不当作physical source，未重归一有限sector。

π消费Mathlib已证20位上下界；sin/cos用12/14项分别有理Taylor余项，sqrt用isqrt外包络。
独立程序先产生自身回执，再看主回执；verifier消费两路径、源/尾/窗口和全部CI。
正控含vacuum、pure H/V、unit/zero losses、phase0/π/2、N=1/5，
one-pol source的闭geometric no-click律；反控包括漏多对、加性背景无限推广、
错误source/effect交换、把pulse coincidences相加冒充window以及漏尾归一。
public source角色与实际source认定分开；readiness只接受具名研究字段。

<!-- GW-FROZEN-BEGIN -->
```json
{
  "version": "p23-gaussian-window-gw0001",
  "source": "pair_only_two_polarization_single_mode_TMSV_from_vacuum",
  "seed_model": "independent_OR",
  "seed_report": "../observable-prediction/public-comparison-po0003.json",
  "window_pulses": 5,
  "angles_deg": ["21/5", "-259/10", "-21/5", "259/10"],
  "background_per_pulse": ["89/100000000", "32/100000000"],
  "pi": ["3.14159265358979323846", "3.14159265358979323847"],
  "primary_terms": 12,
  "independent_terms": 14,
  "source_pair_cutoff": 6,
  "primary_precision_digits": 36,
  "independent_precision_digits": 30,
  "implementation_tolerance": "1/1000000000000",
  "controls": {
    "geometric_ratio_pairs": [["0", "0"], ["1/10000", "0"], ["0", "1/20000"], ["1/10000", "1/20000"], ["1/500", "1/1000"]],
    "transmission_HV": [["1", "1", "1", "1"], ["0", "0", "0", "0"], ["4/5", "7/10", "3/4", "13/20"]],
    "phase_cos": ["1", "0", "-1"],
    "windows": [1, 5],
    "endpoint_angles_deg": ["0", "90"],
    "angles_deg": [["21/5", "-259/10", "-21/5", "259/10"], ["37/10", "-112/5", "-51/10", "121/5"]]
  },
  "publication_configuration_identified": false,
  "source_mapping_identified": false,
  "production_admitted": false,
  "actual_window_model_identified": false,
  "bell_event_files_read": 0,
  "retrospective": true
}
```
<!-- GW-FROZEN-END -->
