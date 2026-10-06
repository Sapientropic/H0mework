# po0002：统计域内的合法源成员

2026-10-01。po0001 直接中心逆读的三支均为 NO_CENTER_WITNESS，原因是 X²>HV。
该消费者没有遍历置信域，故此结果未排除共同源族。旧规则、源码、目标和回执保持。
新消费者先提交，再计算；公开计数与 po0001 结果已暴露，仍是回顾性成员检验。

完整试次、8features、固定指数网格、Ville/selection union、设置条件预测界、
π/Taylor 外包络、三个具名探测模型及窗口资格沿用 [po0001](public-criterion.md)。
alpha、count、效果、背景、误差包络均不调整。M3保持stationary具名责任，
统计误差不授予 multipair/effect 的实际物理身份。

校准三格 00,01,11 和4 pooled singles 仍生成原15位有理候选。
若 H,V 非负，将相干投到同一 Gram 的允许范围：
Xnew=sign(X) min(|X|, floor(10¹⁵ sqrt(HV))/10¹⁵)。
floor 由整数 isqrt 作用于 HV·10³⁰ 的下取整生成，正性以精确分数核验。
H,V、AH,AV,BH,BV 保持；held-out10及其 confidence envelope 不参与投影。
这是给定两布居时的最小相干修正，不是放宽观测带或拟合第四格。
投影后若其余 source 条件不满足，记录 NO_PROJECTED_WITNESS，不另搜点。

合法七量按 po0001 的3×3原始模和确定性 C/L 光学列生成真实有限源；
完整 forward 的八个概率数学区间全部包含在原共同置信域内，才记录
EXHIBITED_COMPATIBLE_MEMBER。三校准率也重新接受检验，不强迫它们等于噪声中心。
held-out率和全部 singles 同时检验；独立程序从完整模振幅复算这个成员。
相容性成员证明“不拒绝此联合条件族”；它不证明 actual identity、Born法则或最优性。
没有成员仍只否定这一个冻结构造，不等于全部源族无解。

<!-- PO2-FROZEN-BEGIN -->
```json
{
  "version": "p23-public-observables-po0002",
  "parent_criterion": "public-criterion.md",
  "parent_consumer": "public_compare.py",
  "projection": "fixed_populations_coherence_PSD_integer_floor",
  "witness_decimal_places": 15,
  "calibration_rows": [0, 1, 3],
  "held_out_row": 2,
  "no_held_out_in_projection": true,
  "source_mapping_identified": false,
  "publication_configuration_identified": false,
  "production_admitted": false,
  "bell_event_files_read": 0
}
```
<!-- PO2-FROZEN-END -->
