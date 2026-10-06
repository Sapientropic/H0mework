# Munich：未知角度族的实际仪器裁决

[完整读出联合域](readout-domain/README.md)已取得两run全部20,403前缀的同源相容证书，
并由实际readiness消费；以下mu0001.1记录保留其零误差必要合同的原判决。

原source对全部合法XZ轴、两个herald给出两侧边缘`1/2`及`p00=p11, p01=p10`。
这些必要关系消去连续控制角和32种全局二元编码歧义，直接审查官方完整试次。
理论源、SpinPair.visit 10、whole-ledger及tick16→17保持。

## 完整裁决

[官方档案](https://zenodo.org/records/22936124)的两个原ZIP按字节绑定，全部20,403个
valid pairs保原顺序评分；两套parser和统计实现独立重解码、核local原行与全部精确前缀。

| 运行 | 有效pairs | 判决 | 首次越过40 | 最大E |
|---|---:|---|---:|---:|
| 2016-04-15 | 10,201 | rejected | 3,974 | ≈494.849935 |
| 2016-06-14 | 10,202 | not_rejected | 无 | 13/6 |

两run各用anytime alpha `1/40`，完整族预算`1/20`。
共同名义仪器合同被拒绝；April的Bob两类原编码计数为4852/5349，Alice为5085/5116。
拒绝作用于理想source概率到实际制备、readout、选择与顺序的共同运输，
未知角度或二元标签重命名不改变该判决。June未拒绝这个必要合同，不等于认证完整joint分布。

## 固定机制

[当前科学合同](criterion-mu0001.1.md)固定官方全部pairs分母、每侧全文件行号offset候选、
原字段identity、±100ms配对、raw flag审计及全部未配对local原行。
被采用的offset均唯一为`[1,1]`；不从统计值挑偏移或事件。
公开flag词典没有被补猜，官方选择后的条件概率资格明确留在受裁决合同中。

主统计量等权混合joint互补配对、Alice边缘、Bob边缘三个Jeffreys e-process。
两个parity bet均先由过去固定；当前parity参与整个joint factor，不作后选择。
过去计数更新预先登记的bet，理论轴、概率、效率或背景没有据结果重选。
两实现分别使用前缀递推与odd-products/factorial闭式，完整前缀SHA、终值、峰值、
首次cross及local审计精确一致。独立实现不读取主回执。

## 冻结与消费者

- 初版科学冻结`fc4305fe13`；两首次格式准入失败保存在`889eea7344`，没有统计判决。
- [格式修订依据](format-repair-mu0001.1.json)：lab2 header带空尾列，记录只有六个语义列。
  修订只接受这个无语义尾列省略并修复Git cwd；旧[criterion](criterion.md)及旧first字节保留。
- mu0001.1在真实重执行前冻结`b1247f063f`；[主首](primary-first-mu0001.1.json)与
  [独立首](independent-first-mu0001.1.json)冻于`e377420499`。
- [最终证书](verification.json)`31aea2ffd8`消费全部前缀cross、完整来源/程序/attempt，
  并由16context和两侧计数独立重算三个终值；intake不打开事件档案。
- [readiness实际回执](../nist-real/evidence/readiness-munich-mu0001.1.json)`3b7ab30ca5`登记
  `public_instrument_adjudication_completed=true`、实际经验裁决已执行、共同合同`rejected`。
  独立专用模式在旧NIST统计、仪器和Lean重生成之前返回。

59项focused控制通过：18主实现、27独立实现、9cross、5readiness，含正例、
位置override、disable、形似反控、32种编码翻转及全文件行号候选。
源声明与内核证书由[sources](sources.json)的13项绑定保持；构造盲性仍由
[tb0001](../theory-blind/README.md)独立承担，已访问记录不重记为未揭盲。

## 接口

`verify.py --check-only`只消费冻结证书，`--certificate`只移动回执位置。
`../nist-real/readiness.py --munich-adjudication-only`消费当前裁决；
`--disable-munich-adjudication`保持经验门关闭，`--munich-adjudication-dir`不替换程序。
旧first及实际readiness回执不能覆盖；后续执行必须使用新冻结合同和具名回执。
这条线的当前责任由[同源公开裁决active入口](../nist-real/nominal-replay/investigation/README.md)维护。
