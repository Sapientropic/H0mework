# tc0001：四single误差域的同源协方差图谱

输入源为原Snapshot或PhaseFiber.RawSource的基本nH/nV/etaA/etaB/delta字段。
四single均由同一个源实际读出，所有区间完整保留。
不修改PhaseFiber、PhaseConsumer、旧源库或冻结数值输出。

## 精确图谱

同源m,z,x,r遵循pf0001的协方差定义。
任意实际角a的meanA=m-z cos(2a)-x sin(2a)，
r meanB=m-z cos(2a)-x sin(2a)。镜像Bob角-a给正x sin项。
四实际均值生成ratio、z、m、x：

r=(s1 alpha0-s0 alpha1)/(s1 beta0-s0 beta1)，
u_i=(alpha_i+r beta_i)/2，z=(u1-u0)/(c0-c1)，
m=u0+z c0，x=-(alpha0-r beta0)/(2s0)。

s0>0、s1<0及beta0/beta1>0直接生成ratio分母严格负；
c0>c1使协方差消元非退化。恢复公式不接收完成的r/z/m/x端点、coverage或目标等式。
A1>A0、B1>B0和c0>c1共同生成z>0、R2>0；pure nV=0仍在合法域。
任意训练区间membership双向等价于同一个源坐标的八个线性halfspace约束。

## 直接消费者

消费者把全部四single membership和原两joint pulse interval资格，
接到同一RawSource/phase的source polytope、完整physical k和两线性slab。
所有训练合法源在同一个协方差/相位图谱内原生生成其全部N5/OR窗口与local singles。
源→图谱的普遍覆盖是代数身份；不声称数值tree覆盖、统计confidence事件或实际epoch身份。

合同/来源先冻结；candidate及每次修复commit后才compile。
fresh trust0/werror验证直接依赖、两个candidate及独立consumer；fresh certify审查精确口、
同源对象、反控与传递依赖，只接受标准三公理。
原root、SpinPair.visit10、whole-ledger和tick16→17保持。
新science程序和数值回执不进入构造。

<!-- TRAINING-CHART-FROZEN-BEGIN -->
```json
{
  "version": "p23-training-covariance-chart-tc0001",
  "status": "frozen_before_compilation",
  "parent": "criterion-lean.md",
  "source_generated_means": true,
  "ratio_denominator_negative_from_signs": true,
  "four_actual_means_recover_source_chart": true,
  "interval_polytope_iff": true,
  "z_positive_from_both_mean_increases": true,
  "pure_mode_preserved": true,
  "same_source_phase_and_N5_consumer": true,
  "new_numeric_tree_coverage_kernel_claim": false,
  "new_full_Born_kernel_claim": false,
  "new_statistical_coverage_kernel_claim": false,
  "controller_advance": false
}
```
<!-- TRAINING-CHART-FROZEN-END -->
