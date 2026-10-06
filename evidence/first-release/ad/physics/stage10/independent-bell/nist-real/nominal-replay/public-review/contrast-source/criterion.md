# ct0001：同源Eberhard读出与一步统计有效性

原EF Snapshot生成全部解析角、完整phase-before-window及任意N个fresh pulse的Gaussian/OR读出。
对称phase Cauchy与原正分母生成所有四outcome非负、归一化与本地single restriction。
原N5读出字节保留；新任意N读出在N=5精确接回旧ClosureConsumer。
原Root/current/whole-ledger/SpinPair.visit10/tick16→17保持。

## 源自产contrast

同一个源的四cell与共同本地single生成
W=j00，L=(sA0-j01)+(sB0-j10)+j11。
W-L等于j00+j01+j10-j11-sA0-sB0的原CH口，关系在证明内部生成。
No-signaling把两个single差读回01的(+0)与10的(0+)概率，因此W/L非负。
不向caller索取完成的CH/contrast关系或actual身份等式。

## 设置误差与一步乘子

epsilon∈[0,1)，pl=(1-epsilon)^2/4，pu=(1+epsilon)^2/4。
每个设置概率pi在[pl,pu]，四项之和1。
同一个constant source的CH≤0给W≤L，并生成
weightedW≤(pu/pl)*weightedL，q0=pu/(pu+pl)。
win是00的(++);loss是01的(+0)、10的(0+)与11的(++);
其它完整outcome的乘子为1。
任意fixed p∈[q0,1]，win乘子p/q0、loss乘子(1-p)/(1-q0)。
源自己生成完整期望和other质量，证明expected multiplier≤1。
源、设置和p可在一个已知past条件下实例化该一步不等式；
概率过程与Ville的累计尾控制由原统计协议消费，不新建重型过程公理。

16局域deterministic assignments内部构造为概率law并证明CH≤0。
该局域口与任意合法constant source CH≤0的更强口分开；
后者也适用于负CH量子source，不要求局域deterministic分解。

## 范围与验收

generic概率helper消费非负、归一化、no-signaling的law，不生成actual硬件身份。
具体EF实例从原Snapshot物理字段内部支付上述law；phase、背景和N不改变contrast代数。
Gauss法则的正性与NoSig是原指定法则的代数身份，
不新增一般无限Born/determinant或实际实验执行lineage的内核身份。

合同与来源先commit；candidate及每次repair先commit后compile trust0/werror。
独立certify检查具体源→law→contrast→setting bound→一步乘子及16assignment边界，
只接受标准三公理。旧源码、输出、publish与原门禁判决保持。

<!-- CONTRAST-SOURCE-FROZEN-BEGIN -->
```json
{
  "version": "p23-source-contrast-ct0001",
  "status": "frozen_before_compilation",
  "source": "original_EF_Snapshot_Gaussian_phase_before_window",
  "window_pulses": "any_Natural_N",
  "epsilon_domain": "0<=epsilon<1",
  "pl": "(1-epsilon)^2/4",
  "pu": "(1+epsilon)^2/4",
  "q0": "pu/(pu+pl)",
  "p_domain": "q0<=p<=1",
  "win": "00_both",
  "loss": ["01_onlyA", "10_onlyB", "11_both"],
  "other_multiplier": "1",
  "source_CH_identity_generated": true,
  "source_outcome_positivity_generated": true,
  "source_no_signaling_generated": true,
  "negative_CH_quantum_source_in_null_scope": true,
  "local_assignment_count": 16,
  "new_stochastic_process_kernel_claim": false,
  "new_full_Born_kernel_claim": false,
  "actual_hardware_identity": false,
  "controller_advance": false
}
```
<!-- CONTRAST-SOURCE-FROZEN-END -->
