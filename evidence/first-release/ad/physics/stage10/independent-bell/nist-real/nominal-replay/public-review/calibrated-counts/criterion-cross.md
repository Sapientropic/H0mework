# ncc-cross0001：条件 ENV 连续域与 complete counts 独立核验

核验已封 ncc0001 首报，不重跑 q/K/fringe inverse、Sturm、优化器或科学首 producer。
全部十九个已生成源（17 symmetric default、Alice/Bob rank-one各一override）须从原
calibration-primary逐根恢复，原完整 G/TA/TB/c 区间运输至两套 ENV determinant 和
独立占据 Γ/Fock cutoff6+原 numberMass 尾。全部19×72概率及19×96 outcome逐项重算，
必须核同源包络交集、原CI严格不交证人，不能接受完成字段为前提。

ENV的 ξ 是每光子环境嵌入；不消费 EF 的每pulse phase λ 或其calibrated source字段。
q_reference=1−sech²(G cos16)sech²(G sin16)是参考方向的至少一对概率；
同一个 G 在45°给 balanced thermal n=sinh²(G/√2)。q_cal、reference q、n、N1 raw click
保持各自定义。K_A=J/S_B、K_B=J/S_A，百分数除100，背景保持每pulse独立OR；
全部窗口先本地加背景，再对同一个源 no-click 做 fresh N 次幂。

## 连续域解析责任

此处的 whole-domain 排除独立于十九点的排除。对所有 G≥0、TA/TB∈[0,1]和任意合法
本地环境分解（包括所有校准inverse根），使用以下完整链。

1. q/(1−q)=S+nH nV≥S，其中 S=nH+nV。因为 x cosh x−sinh x 的导数为 x sinh x≥0，
   sinh(x)/x单调；0<sin16<cos16给 nV/S≤sin²16。q>0时 S>0，除法合法。
2. q≤tanh²(G cos16)+tanh²(G sin16)≤G²，sinh(G/√2)≥G/√2，故 n≥q/2。
   f(u)=sinh²√u=(cosh(2√u)−1)/2具有非负幂系数，因而凸；2n≤S≤q/(1−q)，
   故 n≤q/[2(1−q)]。没有以参考 nV 替代 balanced n。
3. 匹配 V/V 的每边 signal click为1−(1−T)^N，N是共同 thermal整数，E[N]=n、
   E[N²]=n+2n²。按N条件独立loss/background，raw A≤bA+TA N、raw B≤bB+TB N。
   所以 J≤(bA+TA n)[(1+2n)TB+bB]，且
   SA=bA+(1−bA)TA n/(1+TA n)≥(1−bA)(bA+TA n)/(1+n)。
   正herald下 K_B≤(1+n)[(1+2n)TB+bB]/(1−bA)，从而
   TB≥[KbLo(1−bA)/(1+nHi)−bB]/(1+2nHi)=TBLo。
4. SB≥bB+(1−bB)TBLo nLo/(1+TBLo nLo)=SBLo>bB。
   N≥1时 Alice signal≥TA；Bob raw herald中至多bB来自N=0，故
   K_A≥bA+(1−bA)TA(1−bB/SB)，推出
   TA≤(KaHi−bA)/[(1−bA)(1−bB/SBLo)]=TAHi。
5. reduced marginal在H/V number基对角，局部环境嵌入不改变对角。bucket signal click
   ≤transmitted photon mean，所以 a0=4.2°的raw pulse click≤
   bA+(1−bA)TAHi qHi/(1−qHi)[sin²a0+sin²16(cos²a0−sin²a0)]。
   cos²a0−sin²a0>0由两套有尾 trig 区间支付。背景只在此每pulse加入一次。
   1−(1−p)^N在[0,1]上单调，严格 transport至各N。

原 adapter 的 absolute readback tolerance 1e−12 扩张 q两端、Ka上端、Kb下端。
检查十九个完整源interval的q和原balanced raw K读回处于该扩张域；grid不是实际校准身份。
仅当整个连续域 single上界低于某原exact CI下端，才签收该连续名义族被排除。
N1若不分离必须保留未决，N9不能被授予新spacelike身份。

本认证给 conditional nominal ENV count incompatibility 的完成裁决。K/visibility σ不变为
95%硬界，自定q盒不变为公开不确定度；actual epoch、硬件、实验/Born拒绝、最优性和
controller推进旗标均False。未给新的Lean/∞Born/统计coverage kernel证明。

<!-- NCC-CROSS-FROZEN-BEGIN -->
```json
{
  "version":"p23-calibrated-count-cross-ncc-cross0001",
  "candidate_version":"p23-calibrated-environment-complete-count-review-ncc0001",
  "source_points":19,
  "default_points":17,
  "CI_count":72,
  "outcomes_per_source":96,
  "pair_cutoff":6,
  "adapter_tolerance":"1e-12",
  "continuous_domain_from_point_scan":false,
  "source_search_rerun":false,
  "foreign_EF_fields_used":false,
  "actual_source_epoch_identified":false,
  "experimental_or_Born_law_rejected":false,
  "calibration_sigma_hard_confidence_bound":false,
  "new_continuum_Lean_kernel_claim":false,
  "actual_hardware_identity_verified":false,
  "source_epoch_identified":false,
  "nominal_optimum_contract_replaced":false,
  "controller_advance":false
}
```
<!-- NCC-CROSS-FROZEN-END -->
