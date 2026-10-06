# sc0001：公开曝光与联合计数压缩共同源域

消费六个公开run各N=1/3/5/7四窗的完整setting×outcome计数，共24项。
每项的四个setting曝光从同一完整十六计数生成，不从不同run借参数。
压缩对象是XOR3的原EF共同source：四mean、loss及共同每pulse相位，
保留全部原72CI、N9诊断、旧N5前缀和原Γ/Fock源身份。
本合同是回顾性统计反演；它不产生新盲测或新的硬件身份认证。

## 源合同与统计资格

同一合法Snapshot自产每个N的全部四outcome概率、正性、归一化、NoSig与CH。
同run的conditional outcome law在每个past及当前setting下等于该共同Snapshot的读出；
fresh pulse、固定effect及source平稳沿用原EF模型条件。
设置允许依赖past，设置选择不改变这一conditional源law。
这些是具名模型的条件，不由聚合曝光本身证明。
四窗重叠仅用union bound，跨run的source各自保持。

## 完整曝光的一步归一化

原ε=3/1000、l=(1−ε)²/4、u=(1+ε)²/4、ρ=l/u、q0=u/(u+l)保持。
未知setting分布为Π={[l,u]^4，Σπ=1}，可随past漂移。
同源W=j00，L=(onlyA01,onlyB10,j11)，CH=W−ΣL。
原20个固定bet为a_k=1+ρ·2^-k、b_k=1−2^-k，k=1..20。
Π上的精确支持函数是

```text
h(source,N) = supΠ[ρπ00 W−π01 L1−π10 L2−π11 L3]
            = l·CH−ε(1−ε)·min(L1,L2,L3).
d_k(source,N) = 1+2^-k h(source,N).
```

最大点取π00=u、最小loss对应π=l+ε(1−ε)、其余两个π=l。
每trial的全部outcomes，包括neutral，均除以同一d_k。
原source自产d_k>0及归一化乘子的一步期望≤1。
CH≤0自产h≤0，源签名和强度不由目标premise供给。

完整公开计数给T总曝光、Wobs、Lobs；每个候选source的证据为

```text
E(source,N) = (1/20) Σ exp[Wobs ln(a_k)+Lobs ln(b_k)−T ln(d_k)].
```

它消费全部T和relevant mass，不改q0，不用条件胜率替代全trial归一化。
对h单调递减。逐窗生成有理二分括号：lower点的E严格大于选择阈值，
upper点的E不大于阈值；数值未分离时保存未决包络。
因而合法源必须满足h>lower。约束保留同一source、同一phase和三个loss的联合关系。

## 当前setting的完整计数域

每setting保存六个事件：both、onlyA、onlyB、neither、singleA、singleB。
只在当前setting命中时更新原固定λ=±2^-k指数bet。
其一步界为1+q(expλ−1)≤exp(q(expλ−1))；未命中时乘子1。
源conditional law和predictable sampling产生时间统一的q区间，
曝光为本setting的实际n，不能以固定n二项假设替代这一合同。
全部24×4×6个区间和40个方向bet保存。
完整outcome、simplex、NoSig及各窗均约束同一Snapshot。

## 95%联合预算

旧72CI及其所有字节不改。原δ=1/(16·40·6·32767·20)=1/2516505600，
每CI的40bet支付≤40δ，安全联合界βold=72·40δ=3/(80·32767)。
新的总预算仍为α=1/20。
αcontrast=αconditional=(α−βold)/2。
contrast的选择族为24，阈值为24/αcontrast；
conditional的每个方向bet支付δnew=αconditional/(24·4·6·40)。
旧72CI、全部新conditional域及全部新contrast接受域的交集具有≥1−α联合覆盖。
不把两份各95%事件直接叠称联合95%，不将σ、近似pair或跨epoch器件值插入成功事件。

## 连续源域与验收

原四single完整根交集加入新的conditional singles；四joint共同相位slab加入新joint。
完整four-outcome约束同时保留。共同相位上的三个H_i=lCH−ε(1−ε)L_i
用同k多项式和Bernstein外界消费h cut，不独立选择各格相位。
整个盒只有在物理违反、某原/新区间严格不交或全部H_i上界不大于lower时才能排除。
边界、zero loss、pure mode及资源cap保留。外包叶不自动成为存在证人。
非空由原物理source生成的Γ/Fock前缀6加原尾、全部72旧CI和全部新约束同时落带支付。
若没有非空证人，保存该结果；不得仅删除旧负号成员宣称已生成更小源域。

主统计和独立有理统计分别首次生成，随后消费者核全部方向bet、二分端点与来源。
源域producer生成一次树/成员；独立checking核partition、每个排除/保留witness及原生源读出，
不重新搜索、拟合或枚举另一棵树。正例、副本override、disable和形似反例必验。
全部科学源码及修复先提交后执行；新首回执不覆盖旧产物。
原nominal optimum/r6拒绝、root/current/whole-ledger/tick16→17保持。

<!-- SOURCE-COMPRESSION-FROZEN-BEGIN -->
```json
{
  "version":"p23-public-source-compression-sc0001",
  "alpha_total":"1/20",
  "old_CI_count":72,
  "old_inverse_delta":2516505600,
  "old_bets_per_CI":40,
  "new_budget_split":"1/2",
  "epsilon":"3/1000",
  "public_family_size":24,
  "spacelike_pulse_counts":[1,3,5,7],
  "conditional_features":["both","onlyA","onlyB","neither","singleA","singleB"],
  "setting_count":4,
  "bet_powers":[1,20],
  "bisection_steps":42,
  "decimal_precision":60,
  "rational_exp_terms":48,
  "rational_log_terms":128,
  "source_workbook":"diag-xor3.xlsx",
  "source_split_cap":512,
  "phase_partition_count":8,
  "source_member_limit":8,
  "source_member_mean_fractions":["1/2","1/4","3/4"],
  "source_member_phase_fractions":["1/2","1/4","3/4"],
  "source_member_loss_denominator":128,
  "source_pair_cutoff":6,
  "original_CI_modified":false,
  "calibration_sigma_inserted_as_CI":false,
  "actual_hardware_identity_claimed":false,
  "global_all_mask_family_rejected":false,
  "bell_event_files_read":0,
  "controller_advance":false
}
```
<!-- SOURCE-COMPRESSION-FROZEN-END -->
