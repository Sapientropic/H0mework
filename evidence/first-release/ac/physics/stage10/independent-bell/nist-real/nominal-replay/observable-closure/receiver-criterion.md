# rx0001：同源接收角更新与严格CH改善

ef0002的完整scalar slice及两个首结果已经暴露。本合同先提交，两个程序与所有修复先提交后执行。
源族、训练接口、完整cover、原CI与历史最优性合同保持；新接收角不回送源生成器。

## 目标与实际读出口

消费每个保留e段的同一ef0002源。h/v/r/R/λ及背景/pulse均固定，
仅更新接收projection角。公开角是相对vertical polarizer的有效角；
Appendix A中polarizer angles以degree优化，机械HWP为其一半，不能把公开角自行减半或加入offset。
泵κ、gain circle/ellipse和泵响应不进入本消费者。

固定检查四个方向，分别对应两站共同effective rotation及原mirror优化坐标：
`Acommon=(1,1,0,0)`、`Bcommon=(0,0,1,1)`、
`mirror0=(1,0,−1,0)`、`mirror1=(0,1,0,−1)`。
四个单角partial另作诊断，不以它们代替具名可用坐标。
这些是原模拟参数域的projection updates；不登记实际硬件电压或机械输入身份。

## 保持同一源的生成式

令`S(e)=hv(h+e)(v+e)`，训练生成`K(e)=H00(e)/g00=(1−2λ)T`。
K由原训练接收角生成，更新角时保持；不得重拟合K/λ使joint00再次等于旧计数中心。
任意新cell使用同一个e/source，生成

```
L=(1+μA)(1+μB)−[h(h+e)U²+v(v+e)V²]/r
g=2UV/r, N=L+gK, Q=L²−g²S>0
w=N/Q
CH=−QA0−QB0+[(1−bA)(1−bB)]^5*(w00^5+w01^5+w10^5−w11^5)
```

其中局域means、U/V均由更新projection与原R生成。对任一方向t，
`w'=[(L'+g'K)Q−N(2LL'−2gg'S)]/Q²`。
主实现用有理向外角jet生成完整tube上的CH方向导数，数学余项沿用ef的trig/π界。
独立实现自行生成e-slice、source和各cell的mean/U/V显式angle导数，
消费exact branch vacuum law，不导入主jet；规范点端点用相干Fock/Γ+原尾核rawCH变化。
不把两端点相减的数学不确定度解释为采样误差。

## 有限更新合同

对四方向分别检查原点及原四角各±.05°舍入盒的全slice导数包络。
规范有限更新消费整个舍入盒；source仍由原训练生成，不能随box中的角重新校准。
正负方向按固定顺序`(+1,−1)`，
步长按`1/100 degree`起，依次减半共16个候选，不按公布最优目标取步长。
每个候选在t∈[0,step]的完整tube与全部34个保留e段（含boundary）上重算方向导数。
所有段严格正且分母/phase合法域已支付，才产生
`CH(updated)−CH(original)≥step*min_derivative>1e−10`，沿用原rawCH数值容差。
每方向先签收首个满足条件的候选；全四方向完成后按方向固定顺序取首个已支付更新。
无候选则明确未认证，不能放宽容差/改变source/删boundary。
输入更新角本身由这个规则产生，不要求caller提供更新后score或改进certificate。

两首回执形成后才比较方向符号、首步规则、全段包络及严格改善。
原数学容差1e−12、precision40、π20位、主/独trig12/14、Fock前缀6保持。
来源分别登记具名law导数、完整Fock端点验证、finite mean-value transport、物理投影可达域及实际硬件身份。

此结果检验公开源slice中的原projection点，而不是当时另一次设计运行的source。
严格receiver改善若成立，泵响应不能在这个固定源族内把原接收点改称驻点；
后续必须支付source/效果/设计epoch映射，不用拟合κ或自由角offset来制造最优重现。
原最优门禁保持其判决；没有新的Bell原始计数检验。

<!-- RX-FROZEN-BEGIN -->
```json
{
  "version": "p23-observable-closure-rx0001",
  "status": "frozen_before_execution",
  "source_parent": "criterion-ef0002.md",
  "directions": {"Acommon": [1,1,0,0], "Bcommon": [0,0,1,1], "mirror0": [1,0,-1,0], "mirror1": [0,1,0,-1]},
  "direction_order": ["Acommon", "Bcommon", "mirror0", "mirror1"],
  "signed_update_order": [1,-1],
  "initial_step_degree": "1/100",
  "receiver_rounding_half_width_degree": "1/20",
  "strict_improvement_lower_bound": "1/10000000000",
  "halving_candidates": 16,
  "all_retained_scalar_segments_required": true,
  "boundary_segments_preserved": true,
  "training_phase_held_fixed_under_receiver_update": true,
  "source_mapping_identified": false,
  "actual_hardware_drive_identified": false,
  "apparatus_optimum_verified": false,
  "controller_advance": false,
  "retrospective": true,
  "bell_event_files_read": 0
}
```
<!-- RX-FROZEN-END -->
