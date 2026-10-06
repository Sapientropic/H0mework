# mw0001：完整公开运行的共同脉冲读出

## 审查对象

只消费已经公开的六份 diagnostics 工作簿及其三十组完整十六计数。
源入口冻结为 `89cd2e5039`；全部计数和旧 Table S-II 已暴露，合同为回顾性审查。
同一 run 的嵌套 pulse-OR 窗口共享曝光和潜在 source，不作独立似然相乘。
XOR3 完整曝光为182137032，旧停止截点177358351保留原身份。
跨 run 不固定同一个 source、loss、phase 或接收配置。

工作簿标签由 workbook XML relationship 绑定；SI脉冲号为标签各位数字加一。
N=1/3/5/7对应[6]/[5,6,7]/[4,5,6,7,8]/[3,4,5,6,7,8,9]。
N=9的[2..10]全部计数也验收，但时空分离资格单列，不能授予四组窗口的Bell身份。
不消费Excel缓存的正态近似p值，不执行公式，不读取原始事件档。

## 原统计合同及完整覆盖

逐完整trial的12项feature依次为四joint、四cell Alice single、四cell Bob single。
setting条件概率为[(1−ε)^2/4,(1+ε)^2/4]，ε=.003。
α=1/20，δ=α/(16·40·6·32767)，λ=±2^-k，k=1..20。
这是原po0003固定指数supermartingale/Ville族的同一allocation；不同mask与所有停止时间
已在原族内覆盖，不增大α，不缩小family，不把旧截点和完整终点视为独立样本。
E[exp(λY)]≤exp(p(exp(λ)−1))给出每feature累计可预测均值的包络。
同源/effect和上述setting界成立时，将累计feature均值除π上下界产生共同Born均值包络。
计数本身不证明conditional setting界、无串扰或source平稳。

主实现用既有Decimal邻接界生成全部360包络；独立实现从原xlsx重读整数，用有理Taylor
及几何余项生成exp/ln外界。两实现分别保存所有40个bet，之后比较相互包络。
单侧0计数、全计数、空或负计数、漏setting、错pulse标签和错曝光均明确处理。

## 共同单脉冲源的必要关系

先对每run每窗口检验共同本地setting single交集。
具名fresh-pulse/independent-OR模型中，原每脉冲背景bA=8.9e-7、bB=3.2e-7；
某窗口的no-click分别为Q_A^N、Q_B^N、Q_AB^N，phase混合在N次幂之前完成。
同一个脉冲law要求每窗口Nth-root的bare源no-click区间有共同交集。
Q_A根除1−bA，Q_B根除1−bB，Q_AB根除(1−bA)(1−bB)。
joint no-click由1−sA−sB+j生成，所有CI采用外区间；不从中心率固定源。
分别保存N=1/3/5/7以及含N=9的交集，不以未获同等spacelike资格删除N=9公开读出。
任一空交集即证明该run的共同identical-pulse模型不相容；这不反证根法或原Bell统计。
非空必要交集不自动宣称完整Gaussian source存在。

四共同single根内部生成每脉冲mean，随后可由已认证CovarianceSource的m,z,x,r,e图谱
生成全source及共享k slab。该构造必须保留全部joint/window、phase、pure边界和resource-cap叶。
若identical-pulse口被拒，合法下一口是pulse-indexed实际作用与乘积readout，
不能强迫数据通过旧stationary表示，也不能将不同源字段拼接。

## 独立局域计数界

每trial的正事件为(++|ab)，负事件为(+0|ab′)、(0+|a′b)、(++|a′b′)，
其余事件乘子为1。局域确定赋值满足正事件的unweighted indicator≤负事件之和。
上述setting界因此给出predictable P(win)≤r P(loss)，r=((1+ε)/(1−ε))^2，
q0=r/(1+r)。固定p_k=q0+(1−q0)2^-k，k=1..20，
乘子win=p_k/q0、loss=(1−p_k)/(1−q0)产生非负supermartingale。
等权混合仍为supermartingale，Ville赋予任意终点p≤min(1,1/E)。
全部6×32767固定mask联合的p≤min(1,6·32767/E)单列；
XOR3四个具名spacelike窗口联合p≤min(1,4/E)单列。
后一口只说明这一具名四窗合同，并非事先盲选实验或原论文p值的重新认证。
所有幂与log数值保存严格有理/方向舍入证书；不将Excel近似p值当证书。
原论文的逐trial设置质量与原分析方法按其公开声明另审，不由聚合表推定。

## 验收与身份

科学代码与每次修复在首次执行前提交。原r1/r2/r2.1/r3/r6、ef3/ef3.1首回执保持。
新源绑定、两套独立CI、共同脉冲必要判决、逐run局域bet证书均具名保存。
原nominal_optimum仍消费自己的r6负向证据；公开计数审查不覆写它。
Klyshko的±.003及fringe的±.001为k=1估计σ，不作为硬物理域或95%联合CI。
公开pair≈.0005没有公开误差；原[.0004,.0006]自定盒不能冒充公开置信界。
本接口为从属optical producer/readout，直接消费者为NIST readiness。

<!-- MW-FROZEN-BEGIN -->
```json
{
  "version": "p23-public-multi-window-mw0001",
  "inputs": "../public-summaries/inputs.json",
  "source_epoch_policy": "distinct_run_sources_shared_within_each_run",
  "pulse_counts": [1, 3, 5, 7, 9],
  "spacelike_review_pulse_counts": [1, 3, 5, 7],
  "alpha": "1/20",
  "features": 16,
  "runs_covered": 6,
  "pulse_subsets_covered": 32767,
  "lambda_grid": {"powers_of_two": [1, 20], "positive_and_negative": true},
  "settings_predictability": "3/1000",
  "decimal_precision": 60,
  "rational_exp_terms": 48,
  "rational_log_terms": 128,
  "root_precision_digits": 50,
  "background_per_pulse": ["89/100000000", "32/100000000"],
  "local_bet_grid_powers": [1, 20],
  "complete_counts_required": true,
  "source_stationarity_is_named_condition": true,
  "retrospective": true,
  "bell_event_files_read": 0,
  "publication_configuration_identified": false,
  "nominal_optimum_contract_replaced": false
}
```
<!-- MW-FROZEN-END -->
