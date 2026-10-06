# ncc0001：公开校准环境源与完整计数联合读出

nec0001 已从自己的 K、reference q、HV/DA 读出生成十九个 ENV 源（17 default、2 allocation override）。
每个源的同一 G、裸 TA/TB、c 与环境分解在 beta16°和公布四接收角生成全部 N1/3/5/7/9。
两套已冻结 ENV 原生效果／determinant 程序分别读取同一个完整源区间，不读优化参数，
不拼接 EF 的 gain/loss/phase 或窗口预测。完整 XOR3 60 CI 与原停止截点 12 CI 同时核对。

名义规格保留：equal branch conversion、同 G 的 beta16/45、matched V/V N1 K、固定环境；
K 和 visibility 的 ± 为 k=1 σ，q 的 [.0004,.0006] 为原名义自定盒。联合裁决不将这些值
转成硬物理量或新的95%校准成功事件，不授予实际 epoch/configuration 身份。
原名义最优性与 r6/readiness 证据各保留原结果。

有限点逐源保留全部六 endpoint、十二概率、十六 outcomes 与所有严格不交证人。
19 个点全排除首先拒绝该有限名义合同，不能据此拒绝整个连续域。

## 连续名义输入域的 single 上界

原源的 nH=sinh²(G cos16°)、nV=sinh²(G sin16°)，q=1−1/[(1+nH)(1+nV)]。
因此 S=nH+nV≤q/(1−q)。函数 sinh(x)/x 随非负 x 单调，给出 nV/S≤sin²16°。
源的本地 reduced density 在 H/V number 基对角；全部合法环境分解的 single mean 为
TA(nH sin²a+nV cos²a)。bucket click≤透射 photon mean。因此 a=4.2°的 single pulse
点击概率不大于 bA+(1−bA)TA·q/(1−q)·[sin²a+sin²16°(cos²a−sin²a)]。

匹配 balanced V thermal n=sinh²(G/√2) 满足 q/2≤n≤q/[2(1−q)]。
下界来自 tanh x≤x（故 q≤G²）与 sinh x≥x；上界来自
sinh²√u 的正系数幂级数凸性和 (1+nH)(1+nV) 恒等式。

令 nLo、nHi 覆盖全 q 域，KaHi/KbLo 为原 nominal K 包络。
热 n 的 E[N²]=n+2n²、独立 loss 与背景给出
Kb≤(1+n)/(1−bA)[(1+2n)TB+bB]，所以
TBLo=[KbLo(1−bA)/(1+nHi)−bB]/(1+2nHi)。
SBLo=bB+(1−bB)TBLo nLo/(1+TBLo nLo)。
至少一个 Bob signal click 时 n≥1，Alice click≥TA；因此
Ka≥bA+(1−bA)TA(1−bB/SB)，给出
TAHi=(KaHi−bA)/[(1−bA)(1−bB/SBLo)]。
这些界覆盖全部合法 K inverse 根，环境参数不进入对角 marginal；不做新 point scan。
原 adapter 的读出 tolerance1e−12扩大 q/K 输入界，不能把 grid 点冒充精确校准。

有理界与独立 trig 包络支付上述 single 上界；每个 N 的 fresh OR 单调地运输该界。
只有具体原 CI 下端严格大于整个连续名义域的 single 上端，才签收连续域拒绝。
若界不分离，保留未决。该结论只消费本页列出的名义源 law 和输入域。

## 冻结与消费

合同、来源、代码、测试与修复先 commit 后执行。保存新首与完整来源；不改旧 frozen 字节，
不读 raw event、不外联、不改 publish。输入报告 override 只改变同字节复制的位置；
形似少 CI、跨源字段、把条件性证书改成实际 source epoch 均拒绝。

<!-- NCC-FROZEN-BEGIN -->
```json
{
  "version": "p23-calibrated-environment-complete-count-review-ncc0001",
  "source_version": "p23-nominal-environment-calibration-nec0001",
  "default_source_points": 17,
  "allocation_overrides": ["Alice_rank_one", "Bob_rank_one"],
  "total_source_points": 19,
  "source_report": "../../observable-closure/environment-source/calibration-primary.json",
  "source_allocation": "source_owned_default_and_override",
  "reference_beta_deg": "16",
  "published_angles_deg": ["4.2", "-25.9", "-4.2", "25.9"],
  "pulse_counts": [1,3,5,7,9],
  "old_stop_pulse_count": 5,
  "all_CI_count": 72,
  "readout_tolerance": "1e-12",
  "nominal_pair_input_box": [".0004", ".0006"],
  "nominal_K_A_box": [".744", ".750"],
  "nominal_K_B_box": [".753", ".759"],
  "background_per_pulse": ["89/100000000", "32/100000000"],
  "calibration_sigma_inserted_as_95_percent_CI": false,
  "pair_box_claimed_as_public_uncertainty": false,
  "r6_optimum_parameters_used_as_source": false,
  "source_epoch_identified": false,
  "actual_hardware_identity_verified": false,
  "nominal_optimum_contract_replaced": false,
  "controller_advance": false,
  "bell_event_files_read": 0,
  "retrospective": true
}
```
<!-- NCC-FROZEN-END -->
