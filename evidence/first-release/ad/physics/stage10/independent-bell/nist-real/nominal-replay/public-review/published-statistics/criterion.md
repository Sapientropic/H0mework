# ps0001：原发表二项尾概率的独立算术验收

合同、输入、程序、测试及每次修复先提交再执行。
消费 SI Table S-I 的24个 `(Nχ,NS)` 与96项印刷 p，以及主文 Table I 的8项印刷 p。
所有原 ε、切点、成功数和印刷精度保持；不消费新 CI 或 multi-window 科学结果。
结果允许全部相容、具体不相容或方向包络未决，不因论文数字调整算法。

`Nχ` 是 relevant T 事件数，`NS` 是指定前缀中的正事件数；完整 `NTotal` 另存。
完整公开 aggregate 不能替代原停止前缀。公开 sufficient statistics 足以验算数值，
不自动认证实际切点的预声明时间或逐trial执行 lineage。
本口为从属 numerical producer，直接消费者为公开实验审查及 NIST readiness。
原 root/current/whole-ledger/tick、名义最优性和既有统计 CI 保持。

## 源与算法

公开 ε∈{0,.0001,.001,.01} 的SI值，及主文 ε∈{0,.003} 分别按原印刷值验收。
`q=(1+ε)^2/[2(1+ε²)]` 全部用 Fraction 精确产生。
尾口为 `Σ[k=NS..Nχ] C(Nχ,k)q^k(1−q)^(Nχ−k)`，含 NS，不调用 SciPy/CDF/正态近似。

写 q=a/D、b=D−a，`k0=max(NS,min(Nχ,floor((Nχ+1)q)))`。
首项 `C(Nχ,k0)a^k0 b^(Nχ−k0)/D^Nχ` 用完整整数构造，再量化到60位向外格。
上递推因子 `(Nχ−k)a/((k+1)b)`，下递推因子 `k b/((Nχ−k+1)a)`；
两侧均从众数向外，因此因子≤1。每一步分别向下/向上整除，保存逐项误差。
从 NS 至 Nχ 的每项恰消费一次；分支长度、首项与最终方向和全部保存。
q=0/1、NS=0、Nχ=0单独按分布定律消元。非法计数与 ε 拒绝。

整数格的累计宽度上界由两侧步数原生生成，不能以目标印刷值作为停止标准。
总尾上界与1相交来自概率归一化；下界不能超过1。
每个印刷十进制按末位 `u` 生成闭舍入域 `[p−u/2,p+u/2]∩[0,1]`。
完整数学尾包络包含于该域才验收印刷精度相容；与其不交则为具体不相容；其余未决。
该口认证印刷精度相容性，不替出版社指定未报告的半格 rounding tie 规则。

首科学回执保存100个不同 `(Nχ,NS,ε)` 算术口与104项印刷验收。
源角色与执行身份分别保存；算术正向结果不冒充新的盲试或 actual source 身份。
首输出不可覆写，check-only 可按同一已冻程序重算并比较。

<!-- PS-FROZEN-BEGIN -->
```json
{
  "version":"p23-published-statistics-ps0001",
  "status":"frozen_before_execution",
  "decimal_grid_digits":60,
  "SI_pairs":24,
  "SI_epsilon_values":["0","0.0001","0.001","0.01"],
  "main_epsilon_values":["0","0.003"],
  "printed_checks":104,
  "unique_tail_inputs":100,
  "tail_includes_NS":true,
  "retrospective":true,
  "raw_event_files_read":0,
  "new_multiwindow_results_read":false,
  "controller_advance":false
}
```
<!-- PS-FROZEN-END -->
