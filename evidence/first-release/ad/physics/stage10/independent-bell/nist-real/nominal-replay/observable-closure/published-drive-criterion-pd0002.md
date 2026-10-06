# pd0002：公开输入生成同源增益轨道

公开PumpHWP8°与主文Fig.1的16°方向相接，rc0001已生成接收效果及原Γ消费者。
本合同消费ef0002完整合法源域与这个非零reference Drive，生成整个条件控制口。
pd0001保留未执行身份；其逐run/设计epoch资格不增加为原公开名义门禁的前提。
合同、来源、程序与每次修复均先进入commit，再执行；旧source、rx和重放输出保持。

## 同一carrier与控制作用

原pre-R两pair kernels在同reference泵强度下线性消费Drive分量。
在公开名义方向β0=16°处，原source fiber生成nH=h/e、nV=v/e及
`gH0=atanh(sqrt(nH/(1+nH)))`、`gV0=atanh(sqrt(nV/(1+nV)))`。

```
u0=cos16°; v0=sin16°
κeffH=gH0/u0; κeffV=gV0/v0
gH(β)=κeffH cosβ; gV(β)=κeffV sinβ
nH(β)=sinh²(gH(β)); nV(β)=sinh²(gV(β))
tH(β)=nH(β)/(1+nH(β)); tV(β)=nV(β)/(1+nV(β))
gH²/κeffH²+gV²/κeffV²=1
```

域为β∈[0,45]°，只消费固定grid 0/8/16/24/32/40/45。
两mode的physical身份保持，不能跨点排序、交换R或改变phase；endpoint零mode直接生成。
未知绝对reference amplitude吸收入κeff，不认作绝对转换效率或mW。
不设κ相等，不消费公布最优r或接收角生成κ。

同一source的训练λ、R、ηA=e、ηB=e/r保持。全部34保留段和两个boundary都进入输出，
boundary的phase外包与已付合法λ∈[0,1]相交；没有删去可能的合法源。
四角沿用ef已公开配置，N5 fresh pulse/独立OR背景沿用原law。
每个control生成两gain、means、t、总pair量、gain norm与rawCH/四格完整outcomes。
gain平方和的真实β导数由轨道产生；它不被替换为原equal-coupling circle的零导数。
rawCH的β导数由同一kernel直接生成，degree/radian转换必须显式支付。

## 独立性与验收

主路径从原有理source/cover读回，以正项atanh/sinh/cosh级数及严格余项生成轨道。
独立路径从自己的training inverse/cover重新生成整个域，使用自有hyperbolic/导数与forward。
两程序不互读新coupling、source点、control值或结果，直到各自首输出进入commit。
原训练与receiver结果已经公开；不登记新数据盲态。

precision40、旧π区间、trig12/14与1e−12实现容差保持；新增hyperbolic正项数24。
source/matrix概率包络不足则保存unresolved，不改precision/tol或选择另一个源。
规范source继续取原first-inside midpoint；独立以相干Γ/Fock前缀6和原numberMass尾核对7个grid，
不得重归一有限前缀。外国packet只在双方首结果冻结后用于比较。

验收：全34段/7个grid完整、16°源读回、κeff/ellipse往返、endpoint、全概率/outcome质量、
norm与rawCH实际导数、完整Fock尾、source-role字段及错误等κ/角offset/绝对功率反控。
既有ci同Plant定理承担生成机制；不新建证明相同接口的wrapper。

## prep作用的配对反控

最大态fringe不能独自生成非最大态channel。固定native端口与同一个channel N，令
`W=X_A⊗X_B`、`Bℓ(ρ)=((1+ℓ)/2)ρ+((1−ℓ)/2)WρW†`、`Cℓ=N∘Bℓ`。
balanced pair态被W固定，所以所有balanced测量读出相同；非最大态的边缘与rawCH控制导数可不同。
有限single-pair反控取N为Alice端X/Z独立Pauli混合，pX=1/2000、pZ=1/500，ℓ=1/1和1/2。
normalized balanced HV/DA fringe分别为.999/.996；反控通过真实density/效果trace生成。
source balanceγ取16°，固定接收四角由同一公开配置读入；两边角/η/目标K完全相同。
计算balanced完整矩阵一致、normalized fringe及nonmax rawCH和每degree导数的差别。
该finite反控不登记为XOR3或完整N5的新源，不否定ef具名law；它拒绝把max fringe当作完整channel witness。

## 消费范围

输出是公共观测条件族的同Plant控制轨道；同一pair-kernel/environment在制备改变下的身份
与最终nominal设计模型另由相应来源消费。它生成下一层calibration/control问题，
不授予实际硬件、完整channel唯一性、五控制argmax或原门禁通过。
原名义consumer只需公开source/channel/objective/rounding，逐run日志与绝对mW不是新增前提。

<!-- PD-FROZEN-BEGIN -->
```json
{
  "version": "p23-published-drive-pd0002",
  "status": "frozen_before_execution",
  "published_pump_direction_degree": "16",
  "reference_drive_amplitude": "1",
  "pump_domain_degree": ["0", "45"],
  "pump_grid_degree": ["0", "8", "16", "24", "32", "40", "45"],
  "all_retained_scalar_segments_required": true,
  "boundary_segments_preserved": true,
  "physical_mode_identity_held_fixed": true,
  "training_phase_held_fixed_under_pump_update": true,
  "hyperbolic_terms": 24,
  "precision_digits": 40,
  "implementation_tolerance": "1e-12",
  "independent_Fock_prefix": 6,
  "countermodel": {"ell": ["1", "1/2"], "pX": "1/2000", "pZ": "1/500", "gamma_degree": "16", "scope": "normalized_single_pair_calibration_operator"},
  "printed_optimum_as_coupling_input": false,
  "published_nominal_drive_direction_bound": true,
  "samePlant_law_is_condition_of_observed_source_family": true,
  "absolute_reference_power_identified": false,
  "source_mapping_identified": false,
  "full_channel_uniquely_identified": false,
  "actual_epoch_required_by_original_nominal_gate": false,
  "apparatus_optimum_verified": false,
  "controller_advance": false,
  "retrospective": true,
  "bell_event_files_read": 0
}
```
<!-- PD-FROZEN-END -->
