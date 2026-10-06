# r0006.1：同模型独立坐标搜索的数值补全

本版保持[r0006](criterion-r0006.md)的全部科学输入、光学源、目标、19点、校准根、
分量带和验收容差。主路径及独立路径的完整首回执保留。
主路径19点全部完成；独立路径的`default:corner_1000`最高候选在80个cycles后
末次变化为1.048831279604201e−7°，其余18点和同点若干候选已经满足原1e−7°停止条件。
线搜索原宽度也为1e−7°，这个离散线精度不足以稳定触发whole-cycle停止。

该点首回执仍是UNRESOLVED，不能用主路径结果或较低score的converged候选覆盖它。
这里先冻结数值补全过程，再运行任何新坐标计算；没有新的科学盲态或统计检验。

## 补全规则

独立程序、source与score保持原冻结版本，从自己的完整首回执选择所有未完成point，
对该point的全部8个原候选各自的最后坐标继续计算，不消费主控制/source作为起点。
保持原全轴6°scan与黄金分割，whole-cycle停止仍为1e−7°。
新的线搜索宽度收紧为1e−9°，每线最多80步，每candidate最多追加80个cycles。
这个精度变化仅缩小数值包夹，没有改变模型、输入域、目标或候选物理责任。
若仍未满足停止条件则继续保留UNRESOLVED，不调整停止阈值或band。

新增程序直接消费自己的固定G/环境/裸透射、原score函数及source验证器；
原科学程序和首JSON逻辑字节不改。追加trace保留每candidate/每axis的stop和score，
同score/lexicographic规则选择最高候选。已完成18点可复用原记录，来源指向原Git blob。
补全点的四cell全部由独立coherent Γ prefix6及原质量尾重核，N5保持诊断身份。
默认17点band和两个override重新生成，不能拼合不同源模型。

主路径没有未完成point，保留其r0006原搜索和完整原生区间读出作同模型消费者。
最终交叉以同一科学model id `nominal-environment-replay-r0006`和不同numerical revision登记，
逐point差仍须满足原r1e−5、angle.001°、CH1e−10；source/readout仍为1e−12。
只有两边所有point/根/角色及来源通过，才裁决公开五分量；r0006独立首UNRESOLVED保留历史身份。

<!-- NOMINAL-NUMERIC-COMPLETION-BEGIN -->
```json
{
  "numerical_revision": "nominal-environment-replay-r0006.1",
  "scientific_model_id": "nominal-environment-replay-r0006",
  "scientific_criterion": "criterion-r0006.md",
  "scientific_criterion_freeze": "026102bf0c",
  "primary_first_commit": "2dc881d0a6",
  "primary_first_logical_sha256": "adde7242ff7522c67e209b76c5c518d3839412a277c9dfda420fcf10224edf0e",
  "independent_first_commit": "4987380af3",
  "independent_first_logical_sha256": "6356523599dffa91ef454b916ad251c343ac7d8e0dfa1c9d1012a56758d3881d",
  "independent_program_freeze": "044762fb0a",
  "unresolved_points": ["default:corner_1000"],
  "all_eight_own_final_candidates_retained": true,
  "axis_grid_step_deg": "6",
  "line_stop_deg": "1e-9",
  "whole_cycle_stop_deg": "1e-7",
  "golden_steps": 80,
  "additional_cycles_per_candidate": 80,
  "completed_point_records_reused": true,
  "model_inputs_objective_bands_or_acceptance_changed": false,
  "new_scientific_blind_first_run_claim": false,
  "source_or_seed_from_primary_used": false,
  "outputs": {
    "completion": "observable-closure/environment-source/independent-replay-r0006.1.json",
    "verification": "observable-closure/environment-source/replay-verification-r0006.1.json"
  },
  "actual_publication_configuration_identified": false,
  "global_argmax_kernel_proof": false,
  "new_full_Born_or_general_Gaussian_determinant_kernel_claim": false,
  "controller_advance": false,
  "retrospective": true,
  "event_files_read": 0
}
```
<!-- NOMINAL-NUMERIC-COMPLETION-END -->
