# rc0001：原生波片配方生成名义测量效果

来源为NIST Bell Test Research Software and Data的`code/daq/bell_client.zip`。
只读源代码/配置，没有执行归档DAQ、连接硬件或读取Bell事件。
合同和来源先提交，新的安全重实现与Lean候选各自提交后执行/编译。

## 原门禁范围

原registry要求独立或原生apparatus objective、公开名义channel及rounding criterion；
`checks→readiness`的最优字段消费该名义数值结果。
criterion-r0003 §0/M3/M6/F9/§7明确只消费公开全局值，不要求actual XOR3 epoch、
绝对功率或逐run输入记录。实际数据资格不提升为该名义门禁的新增前提。
旧r1/r2/r2.1/r3输出保持历史字节；本合同不签收最优门禁通过。

## 原生control producer

CH程序的默认waveplate分支由两站HWP1数组逐项扫描，固定HWP2/QWP；PC分支另名。
原代码执行PumpHWP=8°；主文Fig.1给16°pump polarization，机械→偏振倍角相接。
公开固定offset与扫描公式是source body；它们不能当作独立证明公布最优点的argmax producer。

物理(H,V) basis、最终physicalV click port。静态PCoff取I，

```
H(t)=[[cos2t,sin2t],[sin2t,−cos2t]]
Q(q)=(I−i H(q))/sqrt2
U(m,o,q)=H(o)Q(q)H(m)
E=U† |V><V| U
```

Alice：q=2o；Bob：q=2o+90°。H(o)|V>是Q的本征vector，因此Q只留下整体相位，
原生反拉vector生成`p(a)=(sin a,cos a)`、`a=2(o−m)`，effect严格等于`p p†`。
不把a或完成的projector等式作为primitive，不额外加入source rotation或自由offset。
PC-on是另一具名retarder消费者，轴/retardance未由这个PCoff定理支付。

程序固定数组：`Angles=−[-4.19/2,25.93/2]`；
Alice o=5.5、m=o−Angles，Bob o=−8、m=o+Angles。
两个setting由原生formula生成(+4.19,−25.93)/(−4.19,+25.93)，
来源值作控制身份，公布舍入角只在生成完成以后比较，不参与拟合。

从physicalV/H到原MeyerScottfirst-port basis可用signed quarter-turn
`T=[[0,−1],[1,0]]`。它把physicalp送到与code(cos a,−sin a)相差整体负号的vector。
source、effect、R和phase作用一同conjugate，不能只换态标签或把整体phase当物理噪声。
不同合法basis运输保持其参数约定，不制造额外optical event或root authority。

## 原生calibration/count readout

`motorScriptExample.switch_path`提供纯H/V及balanced DA/AA的具名制备/接收角色；
`cmdline2.update`实际除数决定herald角色，C/S_A与C/S_B不能按字段名推作接收侧ηA/ηB。
所有source extracts登记函数/行号及原sha；字段到公开效率的赋值仍按被herald端口支付。
源码没有提供最终这次校准counts，就不制造实测receipt。

CH_over_network的PC函数按每setting denominator生成概率，log2版本保rawcounts+N；
defaultwaveplate扫描按固定时长、不同pulse-count denominator输出。
rawCH与normalized-B是两个读出，不因同违反条件而互换argmax。
顺序/归一化来自实际函数body，显示排序或旧脚本异常不作为最终论文test pipeline。

## 验收

安全decoder只解析/重实现纯常量和代数，不import/执行归档脚本。
主/独独立Jones paths在一般o/m与两QWP choices上读回原nativeeffect；
positive完整recipe、非目标一般角、offset同时改变保持sameeffective、错误半角/端口/onlystatebasis反控。
matched制备角色、herald除数和CH各readout分别消费，不能靠fieldname猜语义。
数值模型不在本版重优化；有效角/端口/校准readout闭合后，进入剩余nominalchannel口。

kernel范围为primitive waveplate/port→同源complexJones→rank-one effect及directBorn消费。
全Fock/Born、实际waveplate误差/PC-on/hardwarezero/设计epoch、最优性分别验收，不授予新增kernel flags。
source/basis/fulln consumers在既有入口范围内消费生成的realprojector，不制造新wrapper。

<!-- RC-FROZEN-BEGIN -->
```json
{
  "version": "p23-receiver-control-source-rc0001",
  "status": "frozen_before_execution",
  "source_archive_sha256": "2ab050486473caf71a7b991a6598ef8a139d92e52d738b5a26ac5870e59c28d7",
  "source_url": "https://s3.amazonaws.com/nist-belltestdata/belldata/code/daq/bell_client.zip",
  "measurement_scope": "ideal_nominal_PCoff_static_waveplate_recipe",
  "physical_click_port": "V",
  "mechanical_to_effective_angle": "2*(HWP2-HWP1)",
  "QWP_axes": ["2*HWP2", "2*HWP2+90degree"],
  "source_pump_HWP_degree": "8",
  "published_pump_direction_degree": "16",
  "effective_angle_inputs_from_recipe": true,
  "recipe_controls_prove_argmax": false,
  "actual_epoch_required_by_original_nominal_gate": false,
  "actual_source_or_hardware_identity_verified": false,
  "PC_on_retarder_identified": false,
  "apparatus_optimum_verified": false,
  "controller_advance": false,
  "retrospective": true,
  "raw_event_archives_read": 0,
  "archive_programs_executed": 0
}
```
<!-- RC-FROZEN-END -->
