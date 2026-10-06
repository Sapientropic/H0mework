# po0001：公开全计数的共同源族回顾性检验

2026-10-01。op0001 已于 be90dbed91 冻结；随后 Table S-II 的16个整数计数经
PDF第16页目视核对。该暴露发生在本统计扩展之前，目标和规则不是盲态预注册。
以下规则及 public_compare.py、公开原始计数先提交，再计算频率、误差界或源族成员。
旧 op0001 和历史冻结资产不改；trial/count archives 未读。

## 完整计数与概率

表中行 ab,ab′,a′b,a′b′ 对应 00,01,10,11；列 ++,+0,0+,00 全保留。
每行 denominator 是该行四个 count 的和；共同 N 是全部16项之和。
N 不由主文 Nχ、总运行时长或另一个 pulse grouping 替换。
共同8个 Bernoulli features 为4个 setting-specific ++，2个 Alice-setting click 和
2个 Bob-setting click；后4个在伙伴两种设置上聚合，完整 click 包含单点击。
它们不必互相独立。

对每个 feature 的序列 Yt∈{0,1}，pt=E[Yt|past]，K=ΣYt、Λ=Σpt。
任意预先固定 λ 都给非负 supermartingale
L=exp(λK−(expλ−1)Λ)，因为 E[exp(λYt)|past]
=1+pt(expλ−1)≤exp(pt(expλ−1))。
Ville 界同时覆盖所有停止时刻。固定 λ=±2⁻k，k=1..20，不按观测另选网格。
λ>0给 Λ≥(λK−log(1/δ))/(expλ−1)，λ<0给同式的上界。
各界截到[0,N]，再除以N。δ=α/(8·40·6·(2¹⁵−1))，α=1/20；
union 覆盖6个已分析 runs、15个slots的任意非空子集及8features/40界。
整个固定网格均消费；选择最紧的已覆盖界不再消耗误差预算。
数值以 Decimal 正确舍入的 exp/ln 及相邻 representable 数构成外包络，
每次算术采用有向舍入；统计推导单独审查，不冒称 Lean 概率定理。

消费 SI I.C/III.D 的具名设置假设：给定过去与共同源时，两侧选择独立，
各设置概率在 [(1−ε)/2,(1+ε)/2]，ε=.003。
因此 joint-setting 概率在 [(1−ε)²/4,(1+ε)²/4]。
feature mean 的外包络除以上下界，得到整个同epoch共同平均 Born joint/singles
的外包络；不要求固定源或 i.i.d.，也不从公开 observed setting biases 替换条件预测界。
该假设及同effect/setting-independent源仍是条件合同，不由表中计数自动证明。

## 固定源族反演与成员证书

采用 op0001 固定校准 joint 00,01,11，held-out10不参与重构。
中心率以各 setting 行的 count/denominator 及 pooled singles 条件频率生成。
四公开中心角固定；这些是公开设计 effects，不授予实际硬件无误差身份。
报告三种具名探测率模型。五窗 singles-only/M3 背景为5倍公开每窗概率；
OR 背景为1−(1−b)⁵，明确需要独立 OR 背景窗的条件解释。
S1/OR对共同漂移源的平均率有线性运输；M3中心和固定成员单独报告，
不以平均 singles 乘积替代一般漂移的平均 product。

inverse 的 H,V,X 和 AH,AV,BH,BV 以15位小数固定有理候选，不用held-out修正。
若 H,V≥0、X²≤HV、H≤AH,BH、V≤AV,BV 且
U=(AH+BH−H)+(AV+BV−V)≤1，则生成真实有限源成员：uA=uB=1、Q=U，
UH=AH+BH−H、UV=AV+BV−V，制备功率 UH/U,UV/U。
每侧有2个 collected bins及1个 lost bin，Optic beta=(0,0,1/2)。
H路径 CC00功率 H/UH、CL02=(AH−H)/UH、LC20=(BH−H)/UH；
V路径 CC00=X²/(H UV)、CC11=(V−X²/H)/UV、
CL12=(AV−V)/UV、LC21=(BV−V)/UV。
V路径CC00相位按sign X固定为0或π。其同源 CC Gram 正好是 H,V,X，
完整 singles 正好是 AH,AV,BH,BV；未读模保持相干与失模的共同来源。
H=0、UH/UV=0或条件未满足时记录 NO_CENTER_WITNESS，不后验更换拟合点。
这种 inverse 是相容性成员构造，不识别 actual source，不复现设计优化器。

π使用已有内核界[6283/2000,3927/1250]；12项有理Taylor余项外包络消费
固定候选 Gram/singles，生成实际 forward rates 的数学区间。
三校准格、held-out和四 singles 的全部区间均须落入上述共同置信外包络，才记录
EXHIBITED_COMPATIBLE_MEMBER。判决表示存在相容成员；不验证实际S1模型、Born法则或最优点。
没有中心成员不拒绝整个源族；这里没有完备的全部成员不可行性求解器。
whole-window multipair或死时间没有自动支付，实际模型检验须另消费相应 residual。
新成员和区间由独立全模前向复算，来源/控制/统计资格分别记录。

<!-- PO-FROZEN-BEGIN -->
```json
{
  "version": "p23-public-observables-po0001",
  "target": "public-observables.json",
  "alpha": "1/20",
  "runs_covered": 6,
  "pulse_slots": 15,
  "pulse_subsets_covered": 32767,
  "features": 8,
  "lambda_grid": {"positive_and_negative": true, "powers_of_two": [1, 20]},
  "settings_predictability": "3/1000",
  "decimal_precision": 60,
  "witness_decimal_places": 15,
  "window_pulses": 5,
  "background_per_pulse": ["89/100000000", "32/100000000"],
  "pi": ["6283/2000", "3927/1250"],
  "interval_terms": 12,
  "calibration_rows": [0, 1, 3],
  "held_out_row": 2,
  "models": ["S1_signal", "independent_OR", "named_M3"],
  "source_mapping_identified": false,
  "publication_configuration_identified": false,
  "production_admitted": false,
  "bell_event_files_read": 0
}
```
<!-- PO-FROZEN-END -->
