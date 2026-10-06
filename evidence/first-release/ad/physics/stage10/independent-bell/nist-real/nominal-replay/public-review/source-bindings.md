# 公开实验声明与同源联合审查

公开审查消费实验报告的操作定义、完整计数及源法则，产生相容、拒绝或精确的未辨识纤维。
裁决对象是已发表的实验声明；原名义最优性与实际配置身份分别保存。
本接口为从属 optical producer/readout，直接消费者是 NIST readiness。
原 positiveSmoothUnifiedSource、SpinPair.visit10、material row、whole-ledger 与 tick16→17 保持。

## 可直接消费的公开观测

[NIST 公开计算页](https://www.nist.gov/pml/applied-physics-division/bell-test-research-software-and-data/repository-bell-test-research/bell)
的六份 diagnostics 工作簿各给出五组窗口的完整十六 outcome 计数。
[原字节及提取入口](public-summaries/inputs.json)保存每项 URL、SHA、单元格与 XML relationship。
各组 `A1:P1` 均为整数常量，顺序为 `(++,+0,0+,00)` × `(ab,ab′,a′b,a′b′)`。
工作簿下方的 no-signaling/setting 检验采用 i.i.d. 正态近似；这些缓存 p-value 不作新的置信证书。

[官方目录说明](https://www.nist.gov/document/bell-test-data-file-folder-descriptions) p.5
明确 Excel 标签与 SI 脉冲号相差一位：

| Excel sheet | SI 脉冲 | 脉冲数 |
| --- | --- | --- |
| `5` | 6 | 1 |
| `456` | 5–7 | 3 |
| `34567` | 4–8 | 5 |
| `2345678` | 3–9 | 7 |
| `123456789` | 2–10 | 9 |

每个 run 的五组完整计数之和相同，并与 SI Table S-I 的 `NTotal` 相等：
02-54 为 203629242，03-43 为 107032197，19-45 为 182560876，
XOR1 为 178781131，XOR2 为 177785896，XOR3 为 182137032。
XOR3 的全运行计数与旧 Table S-II 的停止截点 177358351 分别保存；两者有重叠，不能视为独立实验。
九脉冲组保留公开观测身份；目录说明没有为它授予与四组 Table S-I 相同的时空分离置信。

最高杠杆的同源口是同一个 XOR3 source 的 `N=1,3,5,7` 联合读出。
它绕开跨运行校准的身份转接，直接检验源在不同 pulse-OR 窗口中的共同关系。
原 [po0003](../observable-prediction/public-criterion-po0003.md) 的固定指数 supermartingale/Ville
已声明覆盖 `16×40×6×32767` 的 process 族与所有时间；新消费需核对同一 feature、setting 界、
pulse 选择和完整曝光口。原 CI 不改；新的完整运行 CI 由另冻的统计程序生成。
同一个 stationary source 的关系仍由具名光学 law 支付，不由聚合计数自行推出。

## 输入、操作与绑定

| 公开输入 | 实际给出的量或操作 | 已有 producer / consumer | 联合审查规则 |
| --- | --- | --- | --- |
| `74.7±0.3%`、`75.6±0.3%` | 主文 p.4：用 Klyshko 方法测得的 Alice/Bob 系统条件效率；概率 σ 为 .003 | [CalibrationLaw](../calibration-readout/CalibrationLaw.lean) 的 `source_matched_klyshko` 与完整 PGF | 按 herald 分母定 party：`K_A=J/S_B`、`K_B=J/S_A`。不能直接赋给 pure-loss η；校准制备、偏振筛选、背景扣除和曝光口须在审查类内明确 |
| `0.999±0.001` HV、`0.996±0.001` DA | 主文 p.4：最大纠缠制备的 coincidence visibility；两种 basis 分别报告 | [fw 全 fringe](../frame-window/forward.py)；[ENV 校准](../observable-closure/environment-source/calibration-criterion.md) | 两条观测分别消费全扫角 extrema。DAQ 的 `(high-low)/(high+low)` helper 使用传入计数，未把这两次实际测量的 high/low、扣背景规则或 epoch 绑定给论文数字 |
| 全部 `±` | 主文 ref.[34]：estimated standard deviation，coverage factor `k=1` | 单位解析器已核百分数 → 概率；统计 consumer 单独验收 | 声明值相容性可用具名 k=1 包络。不能称为硬物理边界或并入旧 95% 联合 CI 的成功概率 |
| `pair≈5×10⁻⁴ / pump pulse` | 主文 p.4 的近似发对概率，没有给估计式、误差、参考面或校准 epoch | [pairAtLeastOne / pairExactlyOne / pairMean](../calibration-readout/CalibrationLaw.lean)；[收集参考面恒等](../investigation/source-identity.md) | 三种源量、共同入模对率、`q_eff=S_A S_B/J` 与 balanced HH gain 分别保存。原 `[.0004,.0006]` 是名义合同自定盒，不能登记成公开 σ |
| 79.3 MHz、99.1 kHz、15 个可用 pulse | 主文：pump/clock，除 800 的 trial 时钟；固定测量设置期间多 pulse | [analysis-readout](../observable-closure/analysis-readout/sources.json) 与原 N5 OR consumer | 每 pump pulse、小到达窗口与完整 trial 是三种归一化。不同 N 的计数用各自完整 run 曝光；不拿 pump 频率替代 setting-trial denominator |
| bA=8.9×10⁻⁷、bB=3.2×10⁻⁷ | 主文 p.4：单个到达窗口背景概率；本地窗约 625/781 ps | [时间窗链](../observable-closure/analysis-readout/sources.json)；原 OR / additive 支路 | 公开窗口由 78.125 ps/tick、radius4/5 生成跨度 625/781.25 ps。每 pulse 独立 OR 是具名模型；背景平稳、独立及校准同口没有被目录摘要自动证明 |
| pump polarization 16°；PumpHWP8°、22.5° | 主文 Fig.1 给 16°、phase 设置为 0；DAQ recipe 给非最大态8°与最大态/DA-AA的22.5°命令 | [原 recipe](../observable-closure/receiver-control-source/source-and-receiver-recipe.txt)、[偏振校准 recipe](../observable-closure/receiver-control-source/polarization-calibration.txt)、已证 Jones/HWP consumer | 控制规则可同源生成 pump 路径。两个 path 的真实 conversion、绝对功率、共同 gain 或最终 XOR3 执行记录不能由命令文字自动决定 |
| `ε²=coinc/(ηAηB rep_rate)` | Meyer-Scott Appendix A：balanced pumping 的一个 HH setting，coinc=33000/s；历史 Bob 效率.732 | [原四模 Hamiltonian](../source-code/README.md)；全 number source | 这是原代码的强度定义和历史配置。不能与论文总 pair≈.0005 或最终 Bob .756 合并身份 |
| 接收波片和电光规则 | 主文 Fig.2：bit0为 PC off，bit1为 PC on；DAQ 保留 offset、QWP/HWP recipe、motor zero 加减规则 | [receiver-control-source](../observable-closure/receiver-control-source/sources.json)、RC 原生投影 | 公开程序证明规则可执行，不能独自证明最终 run 使用了哪份 motorConfig、PC 电压/retardance 或版本 |
| 十二项 Table S-II、三十组 diagnostics | 停止截点的 N5 完整十六计数；六个 full run × 五个 N 的完整十六计数 | [ef0003 全纤维](../observable-closure/full-statistical-fiber/README.md)；[新公开输入](public-summaries/inputs.json) | 可生成同一 run 的多窗口联合源域。跨 run 不固定同一 η、phase 或 gain；同一 run 的重叠窗口不乘独立似然 |
| Rate Estimates File | rough rates、已观察 rates、Nχ cutpoint 计算；目录 p.5 说明来自此前 run 和当前丢弃首段 | [原值与公式源](public-summaries/inputs.json) | 它支付 rate planning、停止/曝光和选择历史，不提供最大态 K/fringe 的六项校准计数 |

## 运行与 source 身份

[SI IV.A](https://journals.aps.org/prl/supplemental/10.1103/PhysRevLett.115.250402/LHFSupplementary.pdf)
报告不同配置的六个 analyzed runs。02-54 末段 laser 失锁；03-43 开始前修复，末段 cryostat 升温；
blind17-04 前重新对准；19-45 前小幅重新对准；XOR1 前重新对准；XOR2 与 XOR1 之间未重新对准；
XOR3 开始前重新对准。目录 p.2 将 XOR3 对应到 `02_31_...ClassicalRNGXOR_3`。
主文 p.5 说明最终 run 最稳定、对准最好，并报告 coupling 和 PC stability 的变化会影响 violation。
这些公开记录支持分别审查各 run，不能把所有校准和运行装成一个已测的固定 snapshot。

公开 DAQ 保存规则、源文件名和记录时间的生成方式；读取的两份小 DAQ archive 没有最终
`motorConfig.yaml` 或由运行日志绑定的 XOR3 波片/电压 snapshot。
此项是所列公开证据的实际身份状态，不是必须等待私有披露的判决。
发布证据审查可直接判定声明域是否与同源理论关系相容，并把未绑定字段量化为 nuisance 纤维。
若所有合法 nuisance 分支都产生同一结果，就直接签收；若存在合法相反分支，就保存具体证人。

## 同源模型选择

EF 的每 pulse `±V-number phase` 混合与 ENV 的每 photon `Pol⊗Env` overlap 是不同作用。
相同单对 fringe 数字没有给出全 number 效果、bucket singles 二阶项或不同制备之间的相等。
新联合消费者必须从一份源重新生成校准与实验读出，不能拼接两份已拟合 source 的字段。

原 cal/cb/fw/nec 的 N1、signal-only 或 OR、固定 `t_cal`、matched V/V、固定 gain norm、
equal conversion、对称 environment 分解都是具名合同选择；公开文本与数学选择在
[来源库存](sources-public-review.json)中分列。
完整公开输入覆盖在该库存所列材料内验收，不宣称所有公开资料不可识别。

NIST 是公开程序与工作簿的来源。原始工作簿字节和 [完整 notice](public-summaries/NIST_NOTICE.txt)
一并保存；提取 JSON 保留原值与公式源码，不执行公式或宏。原 r1/r2/r2.1/r3/r6 与 ef3 科学首保持。
