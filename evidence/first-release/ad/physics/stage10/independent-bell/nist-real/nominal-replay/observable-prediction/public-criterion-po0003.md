# po0003：整格留出与全部单侧率

2026-10-01。po0002 从 pooled singles 取得同源校准量，故 OR/M3 的校正间接读取
了10格。它的联合回顾性相容性有效，但不是整格独立留出。原冻结文件与回执保留。
本修订先提交规则/源码，再执行数值；所有公开目标和旧结果的暴露保留。

源族、3×3成员构造、固定布居下的 PSD 相干投影、三种背景解释、source/multipair/effect
资格沿用 po0001/po0002。alpha=.05、λ网格、ε=.003、6runs×32767pulse subsets、
完整trial/no-click和π区间保持。计数概率采用相同的非iid supermartingale/Ville推导。

训练函数只接收00,01,11的原始outcome四计数。j00,j01,j11由各自四计数的和归一；
sA0,sB0仅从00，sA1,sB1仅从11取得完整single。inverse和PSD投影的参数列表不存在10格。
00/11的single估计对应实际指定setting pair，统计运输除πxy界，不能除单侧πx界。
整体N、10格的任何count和confidence envelope均在成员生成之后进入评估。

最终检验12项：四joint、四cell中的完整Alice率、四cell中的完整Bob率。
setting-specific single feature仍是逐完整trial的0/1指标；12个process全部除πxy上下界。
δ=α/(16·40·6·32767)，其中额外4个process覆盖旧pooled-single口，避免同一公开表上
两个single读出合同共用全部α。所有误差运输仍是共同源/效果及具名选择条件下的外包络。
成员的全部12个概率数学区间均须包含在对应CI内，才记 EXHIBITED_COMPATIBLE_MEMBER。
held-out10的joint及两single都参与最终检验；不把采样误差中的率当作精确无信号等式。

表的设置/源资格、实际背景、multipair/window、效果误差没有由相容性支付。
S1/OR生成共同平均源成员；stationary M3另列，不能自动运输平均product。
本结果是回顾性源族相容性，不是盲态验证、实际源身份或最优性判决。
原nominal_apparatus_optimum判决保持。没有找到这一个投影成员仍不排除全部源族。

<!-- PO3-FROZEN-BEGIN -->
```json
{
  "version": "p23-public-observables-po0003",
  "statistical_parent": "public-criterion.md",
  "source_parent": "public-criterion-po0002.md",
  "training_rows": [0, 1, 3],
  "single_training_rows": {"A0": 0, "A1": 3, "B0": 0, "B1": 3},
  "held_out_row": 2,
  "held_out_count_access_in_member_construction": false,
  "features_evaluated": 12,
  "features_in_global_union": 16,
  "witness_decimal_places": 15,
  "source_mapping_identified": false,
  "publication_configuration_identified": false,
  "production_admitted": false,
  "bell_event_files_read": 0
}
```
<!-- PO3-FROZEN-END -->
