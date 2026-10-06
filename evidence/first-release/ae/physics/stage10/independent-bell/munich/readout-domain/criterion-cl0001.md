# 当前pointer与后继记录clock：cl0001

原source、root、material row、whole-ledger、tick16→17与hr0001.1完整历史保持。
本读口消费已准入四份local记录；同run、同side、原地址的相邻行形成记录观察。
全部行保留；不按time重排，不跳过未配对／invalid／Maintenance／CEMs off，末行右删失。
相邻记录表示观察继续，不定义物理nativeAction。

原Unix-ms字段按精确Fraction解析，差值单位保持ms。
无法解析、负差、同time均显式保留；local timestamp是原随机数身份，不指定物理单位。
每枚观察同时保两端原地址和行SHA、setting/result/herald、raw flag/comment及已付pair-membership。
不赋予新的loss、click极性或pulse宽度标签。

固定CDF cuts(ms)：100、500、1000、2000、3000、5000、10000、20000、40000、
80000、160000、320000、640000。全部非负差均进入所有cut的精确累计计数，
其余status单列。按完整两端公开context分组，仅作为raw domain table，不作为参数或判决。
两个独立parser/差值及group实现须有相同ordered observation commitment、status和全部counts。

公开source机制见[完整发生恢复](history-source.md)：measurement后presence与条件reload，
两trap就绪和BSM重试生成下一storage事件；clock能否显影真实电离由该作用及joint fibre裁决。
典型加载时间不是硬support界；gap可同时含另一侧重载、环境loss、BSM等待、维护和clock误差。

criterion、两个实现、执行器及focused controls在新clock表消费前提交。
首attempt和首result独占创建。CEM-pair×clock域表按原pairs的地址重新准入，
使用旧两个独立parser核原offset／field／time identity，不能由两个membership集合排序猜配对。
同时保当前完整(h,a,b,x,y)与每侧下一原local行的clock，不按下一valid pair替代下一原记录。
pairs只供原地址和context身份，不拟合、传播或重播旧prefix。
没有新的统计拒绝、confidence预算或actual硬件唯一性claim。
此raw feed直接供原控制／clock／record语义square及既有joint/history消费者。
