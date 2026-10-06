# NIST验证信息访问记录

NIST原始/压缩/processed/HDF5试次评测文件及其档案派生表保持未读，未执行事件解码。
公开论文SI的16项整数计数已作为回顾性文献目标，进入op0001/po0003消费者；
来源、统计规则和训练依赖见下方最新记录。历史各阶段的未读声明只适用于相应阶段。

初轮读取的一手材料为 NIST 官方仓库介绍、官方格式说明、格式补充说明和原论文；
后续扩展访问按下方分次记录。
初始设计保留态、偏振基、角度、设置/检测几何、格式及所需校准种类。
后续公开信道值和公开全计数的输入角色分别在其冻结revision中登记。
论文与格式文档属于文献来源，试次评测文件须另行登记。

必须披露：网页检索工具在查找控制段落时自动返回了邻接的已发表统计结果文字，
论文控制页还同时展示了装置测量数值。这些内容曾进入会话上下文，不能声称完全未见。
初轮邻接统计文字未作为信道参数、拟合目标、容差、数据分区选择或就绪证据。
Lean泛族候选在这次邻接结果暴露前已构造并编译。公开全计数的后续用途见最新revision，
不再沿用初轮的统计未使用声明。

因此可主张的是 **评测文件/试次数据未读**；不可主张更强的“任何已发表结果均未暴露”。
接入前由未接触结果的独立复核人检查冻结材料；该角色的签字未登记。

访问入口：
- https://www.nist.gov/pml/applied-physics-division/bell-test-research-software-and-data
- https://www.nist.gov/document/bell-test-data-file-folder-descriptions
- https://s3.amazonaws.com/nist-belltestdata/belldata/File_Folder_Descriptions_Addendum_2017_02.pdf
- https://arxiv.org/pdf/1511.03189

本记录是会话工具访问与用途披露，不伪称操作系统级的数据访问沙箱证明。

历史纠正：下方2026-09-24“任何公开渠道均不存在”的全称表述没有调查覆盖依据。
当前可签收范围是：在逐项列出的出版物、仓库及所核版本中未识别出原2015优化器和完整输入表。

## 2026-09-24 · NIST 公开渠道专项调查（子代理执行）

为评估名义装置最优门禁的三项缺失输入（独立名义目标函数、信道输入、舍入判据），
公开渠道检索**未打开、下载或解析任何评测事件文件**：
S3 桶只读 `?list-type=2` 索引（193 keys）及文档/代码小文件（`bell_analysis_code.zip`
仅读中央目录与小型 `.py/.yaml/.txt`，事件数据成员按名登记）；PDR 只读记录元数据。

实际访问范围：
- NIST 官方：`nist.gov` Bell 仓库各 landing 页、`bell_analysis_code.zip`（77 条目全名清单，
  内容为数据管道代码，无设置优化/装置仿真条目）、DAQ 两 zip、`The Rate Estimates File.xlsx`、
  `data.nist.gov` PDR（仅有 2017 数据集记录，纯事件 .bin）、`nvlpubs` NIST.IR.8175/8208、
  `github.com/usnistgov/libtrevisan`；Bitbucket `qittlab` 工作区已停用（死链）。
- 文献：arXiv:1511.03189 v2 主文与发表版 PRL SI（LHFSupplementary.pdf，仅统计/时序/RNG 三章，
  无装置模型章节）；Eberhard 1993 预印本扫描（Table 2 不可读）及第三方复现 arXiv:1410.6888；
  Bierhorst Nature 2018、Zhang PRL 2020、Shalm Nat. Phys. 2021 及其 SI；
  **Christensen 博士论文（UIUC 2016）Appendix A**，公开了装置模型方程、三类噪声分解、
  多对负二项分布与含噪 S_CH 目标函数及优化变量/约束。

随检索进入上下文的已发表数值：主文全局信道值（Klyshko 效率 74.7±0.3%/75.6±0.3%、
visibility 0.999/0.996、SNSPD 91±2%、背景概率 8.9×10⁻⁷/3.2×10⁻⁷、对概率 ≈5×10⁻⁴、
门槛 72.5%、多对 <1%）、各后续论文的重述值与角度符号约定差异。这些均为文献公开值，
非评测文件内容；未作为信道参数、容差或分区选择写入设计文档，门禁状态未因此改变。

结论登记：目标函数有公开方法层文档（Christensen App. A）；信道输入有主文全局公开值、
无逐 epoch 效率/visibility/背景值；**舍入判据与 2015 仿真实现代码在任何公开渠道均不存在**。
重放路径与剩余缺口由父会话评估，本记录不签收门禁。

## 2026-09-24 · 独立名义重放（nominal-replay/）

按调查报告执行独立重放：新增 `nominal-replay/` 目录（判据 `criterion.md`、App. A 与论文
信道段落的逐字节提取、`replay.py`/`independent_replay.py` 及回执、11 项自检）。执行顺序为
判据先行（a-priori integrity statement + F1–F16 逐项引证 + 冻结机读块），r0001→r0002 修订
由公开阈值 72.5% 检验驱动并完整披露，r0001 输出原样保留。r0002回放重新抓取
Christensen 博士论文与 arXiv:1511.03189v2 两件文献（与上轮同一来源），未打开任何评测
事件文件；未修改 `readiness.py`/`request.json`/`instrument.json`/`checks.py`/`real_family.py`。

机器判定：`REPLAY_DEVIATION_EXCEEDS_PREDECLARED_BAND`（独立复核
`CERTIFIED_...`，17 盒点最差 Δθ=5×10⁻⁷°）。文档五点全部在预声明带外；模型本身复现
两个公开阈值（0.668≈2/3、0.7264≈72.5%）。该输出是门禁复核的**候选输入**，不是门禁通过。

## 2026-10-01 · r0003 效率单位映射修订与重放

已见旧重放与 P23 的窄带核读后，依据现有来源提取的 `±0.3%` 修正机读半宽为0.003。
新 `criterion-r0003.md` 先在 `8e4b0643de1ceffbd5c39c72609358d240f3097c` 提交，再执行本版模型测试和双重放。
旧 criterion／r0001／r0002／r0002.1 输出保持原字节；新回执与门禁见
[名义重放入口](nominal-replay/README.md)。只读取既有装置文档与公开来源提取，未获取新PDF、
未读取 NIST 试次事件、未创建数据检验锁；合成门禁控制使用临时目录，未进入生产回执。

## 2026-10-01 · 可见度载体与完整四角研究

科学合同先在 `4808fe0f2ad291613a8a5db60d13b61fcc292fc5` 提交，再执行新模型。
原论文/thesis与官方SI重获PDF，哈希及设计页范围见 `investigation/design-sources.json`；
PDF未提交。原文p.3–4、SI p.1和thesis PDF59/61为本地设计提取页；公开检索/工具整页输出
夹带相邻已发表图中文字（含子代理thesis PDF62），没有用作信道值、目标、容差或分区。
未下载、解压、读取任何试次事件/计数表，未发送外联。双实现、Lean证明及来源缺额由
[研究入口](nominal-replay/investigation/README.md) 维护；原各revision字节保持。

## 2026-10-01 · 光源收集模式与输入身份核查

重新读取 NIST 引用的 Evans2010、Dixon2014 和 Bierhorst2015，以及原作者2015 SPDcalc
源码/设计笔记；来源版本和哈希见研究入口的 `additional-source-review.json`。
为取参考文献，本地提取主文 PDF8–9 时意外显示了已发表 Table I 的计数/p值；
Bierhorst 方法页提取也夹带了其他旧实验的已发表表格。没有读取任何试次评测档案，
这些公开结果未进入参数、目标、容差、分区或验收。新查 PDF 和代码仅在临时目录，未提交。
核查范围为符号身份；没有运行新模型或修改冻结criterion、程序、输出，没有发送外联。

## 2026-10-01 · 原 NIST2015 四模代码恢复与r0005重放

新来源为 Waterloo Meyer-Scott 2016 thesis 的项目/方法/代码页，以及Jennewein
photon-toolbox规格和Tan QO原语；PDF及源页哈希见 `nominal-replay/source-code/sources.json`。
只读设计、公式和代码，PDF及原语留在临时目录，未提交大文件。设计代码的33k校准rate
是本版明示历史输入；没有把Bell统计量当参数或拟合目标。

科学合同/source先在 `7756ce61784f8e705444450c03b12996340090f5` 提交，再执行两份独立
四模重实现。两边各完成19点，原MATLAB脚本未执行；原各revision原字节保持。
未下载或读取任何Bell试次/计数档案，未做事件解码或统计检验，未创建评测锁或发送外联。

文献网页/设计提取的邻接文字进入上下文，含源表征rate及一个已发表校准标量；
没有使用这些数值/图曲线决定模型、目标、输入、容差或拟合。
后续Eq.(1.1)/表征方法核读的来源范围见 `source-code/objective-design-addendum.json`，
它是源码语义补充，未改冻结输入或执行另一优化目标。

## 2026-10-01 · 最终配置的公开附件与版本核查

检查arXiv v1/v2源码包的完整成员清单及装置/控制TeX段；两版公开信道与最优值段落
忽略空白后相同。补充PDF与统计图的payload未在本步读取；原稿摘要/邻接已发表结果文字
进入上下文，未作为输入或拟合目标。Waterloo四个bundle仅检查分页完整的附件元数据，
未读自动TEXT、THUMBNAIL或LICENSE内容；作者2015/2016公开站点只核源代码树与SPDC代码。
Christensen已覆盖的Chapter5设计核读混排出现p值图caption，未用于本线输入。
范围、URL与哈希见 `source-code/public-configuration-review.json`。未运行新数值模型、
未改任何冻结输入/重放输出、未访问试次档案、未发送外联；源码包/元数据留在临时目录。

## 2026-10-01 · 公开复现、重优化与争议检索

核查来源为官方仓库说明、Crossref/PubMed更正元数据、公开论文/回复与精确参数检索。
范围与来源见 `source-code/public-discussion-review.json`；其他装置的重优化和NIST统计重分析
未被当作同实例最优重放。网页/PDF核读出现公开正文、附录及表格中的统计数值，
未用于输入、目标、容差、拟合或重评分。未下载/读取Bell试次或计数档案、未执行新模型、
未修改冻结源/回执或publish、未发送消息；Glancy讲稿PDF访问失败，内容未核。

## 2026-10-01 · r0006连续角响应与固定改善步

沿用既有instrument、RealFamily/VisibilityCarrier、r0003/r0004 criterion及原文提取，
未获取新的实物参数；新增Mathlib已证π界的只读源码绑定。
新criterion/sources先在 `b818e92fbdeca40d4a34c26e4bbf5ad90a0a4f80` 提交，再编译候选、
独立认证与执行新数值。参数、两支校准解释、舍入域和±0.1°更新均预先固定。

Lean构造、认证及数值双实现分工独立。r0006主实现首次数值执行前已接收独立摘要，
未用作输入、种子、控制更新或物理模型选择；此前未读独立代码/JSON。
主CH早期包络过宽；按冻结规则改进计算包络的收集项、自动微分和效率角点凸包后证成，
未改物理域。独立科学AST不变，后验comparison才读主最终JSON并重核中心/来源。
verifier同时消费两程序并重算精确区间与源多项式恒等；该阶段不再声称代码/输出隔离。

连续符号与更新认证是条件same-preparation local-Pauli M3族的数学读出；
未读取Bell试次或计数档案、未创建预测锁、未推送或修改publish、未发送外联。

## 2026-10-01 · 收集源集成与cr0001.1响应

local-response与collected-source的原冻结/成果提交完整合并，25条回执来源绑定通过。
集成focused检查重验LR保存证书与拒绝/override控制，并运行CS的11项测试；
LR的7227点属于原保存回执，未在集成检查中重新执行。
两原worktree与本地分支已移除；原四个提交保持main祖先，只有可重建的__pycache__被清理。

cr0001先冻结于a26869a1f3，执行前增加坐标端点控制的cr0001.1冻结于4a8e1753f4；
原cr0001未执行且字节保持。新输入来自既有CS模型/独立全模路径及r0006舍入域。
源状态/effect共同置换、λ0/1率、三pair预算、Γ/r_col条件和固定±.05°更新均预声明。
双实现首次数值计算各自生成输入，之后才读取对方回执进行比较；后验字段适配与只读CLI
没有改变科学函数、冻结域或独立科学AST。

新验证重算32组原生源收缩、导数、更新与区间；Lean独立认证实有限模式，
复相位由Python振幅路径核对。公布幅度的参考面与真实最终校准没有被赋予身份。
本地审计摘要的84/60/19数字没有源码及绑定回执，未登记为第三实现事实；
窗口率、读出比与源码语义的核对范围见[集成复核](nominal-replay/integration-review.md)。
未读取Bell试次/计数档案、未创建预测锁、未发送外联；publish保持只读，未推送。

## 2026-10-01 · 公共可观测源族与完整计数

op0001合同先冻结`be90dbed91`，随后重新取得已登记hash的PRL补充PDF，
目视核对第16页Table S-II全部16个整数。它是发表文献，不是trial/count archive。
公开设计角、完整outcome、五pulse窗口和计数角色固定于
[public-observables](nominal-replay/observable-prediction/public-observables.json)。

po0001的统计/数据/消费者规则与源码分别先提交`925b241a77`、`a0cfeadec3`，
再计算中心与同时域。中心不是合法PSD点的结果保持；po0002先冻`990b8ee678`
后构造PSD成员，pooled singles对10格的信息依赖保留披露。
po0003先冻`af26fdcb74`后执行；训练只接00/01/11，完整10格进入最终检验，
N在成员生成后用于共同置信运输。公开计数已暴露，三版均是回顾性消费者。

公开信息支付指定校准格和同时统计域，不用于修改旧最优性参数、目标或五分量带。
源/效果、探测背景和多对/window的实际资格独立登记；相容性不授予actual source身份。
主有限源与独立全模路径分别生成336控制；公开成员由独立全模源码复算，数学/统计
包络的包含和floating复算分别签收。所有新可执行源码与Lean认证源码先提交后运行。
未取得原始试次、未创建L2预测锁、未推送、未修改publish、未发送外联。

## 2026-10-01 · 完整Fock源与五脉冲窗口

gw0001科学合同及来源先冻`5b5814bceb`；新程序、Lean候选与编译修复先提交后执行。
公开来源为Quesada等的threshold/vacuum读出、Cardin–Quesada的Gaussian photon moments及
Weedbrook等的TMSV/纯损失，URL见`nominal-replay/gaussian-window/sources.json`。
这些文献支付物理子族与读出规则，没有提供NIST最终优化配置。

公共输入直接复用po0003的independent_OR三格源种子与原12项同时域；没有新增计数或改变统计带。
raw source转换不读取10格或CI，不以q/visibility字段赋予未核测量身份。
主路径用Gaussian真空读出；独立路径先生成相干Fock前缀、精确尾及完整窗口回执，
后读取主回执作比较。verifier同时读取两源码/回执并复算，独立科学AST及首次源码快照绑定。

三层Lean独立认证与双实现控制分别消费源计数和具名物理读出。
原始trial/count archives保持未读，未做事件解码；公开16项文献计数保持既定回顾性用途。
未发送外联、未推送、未修改publish。

## 2026-10-02 · 原生端口与校准测量读出

ge0001合同先冻`1458fa3856`，原生端口/Γ候选与全部编译修复先提交后执行。
cal0001合同先冻`d9ead286cf`，PGF与独立numberMass程序先冻`2a485ea67c`/`c3032d45bf`；
各自生成首科学回执后才读取另一回执，事后comparison独立冻结`51f246f406`。
输入复用既有公开材料、原gw参数及统计域，12个校准支路没有被择优删减。

独立Lean认证分别消费真实全sector端口效果与同源条件效率；Gaussian闭式及全窗口
Born身份仍保留原数值口径。readiness分别登记两项研究能力，原名义最优性判决保持。
原始trial/count archives保持未读，未新增公开计数；未发送外联、未推送、publish保持只读。

## 2026-10-02 · single-only校准候选与源结构检验

cb0001合同先冻`435305719b`，主/独程序先冻`396cf14aba`/`3aa4fee3cd`后各自首算。
源构造只交付00/11四single；joint、01/10、global N、CI及目标态比例不进入构造。
双首算后才读另一回执，事后比较另冻`3c89d01c7a`；全部首回执保持。

sc0001初稿matched比值录入错误，未执行；sc0001.1在`b4114c8e81`先冻后执行。
主首尝试在`1a09029d51`后执行，因ln(1)邻数的分数序列化失败，没有完成科学JSON。
独立摘要随后已向主暴露；主`337c370db7`修复exact ln(1)=0及正控后生成成功首回执。
数据、科学函数AST、效率域、族预算和λ网格保持；双首算互盲为false，不登记blind p-value。
独立`193c847081`首算未读主代码/回执；两成功首回执和`152f8bf1de`事后比较保持原字节。

源候选及独立认证候选全部先提交后编译。统计合同是回顾性具名conditional null，
与po0003 α分别登记；公开文献全计数用途延续，没有取得trial/count archives、外联或publish写入。

## 2026-10-02 · 共同参考面的完整源与九点控制重放

fw0001合同及35项来源绑定先冻`4c86dd68e7`。源构造只消费既有00/11四single，
Klyshko/DA校准域沿用公开单位；joint、01/10、CI及公布r不进入源生成或优化。
原作者代码的固定总raw gain与四个独立receiver角形成具名控制合同，
equal branch conversion、实际校准输入及参考面没有由相容性追认。

主科学程序先冻`4af1a446b0`；完整首输出sha256为
`15ee9b8dba95a45fcc8d1775a412e27a5107fce026c3fc97815069e5ce3bb8d1`。
存储适配另冻`ca338e67d0`，删除重复巨型系数的紧凑回执及source snapshot保持科学数值，
完整首输出保留hash；18个端点checkpoint逐项重建相等，详细回执另存。
独立程序先冻`5c4e8dc7c3`；首次尝试遇到二次域消去的向外精度不足，
`33041bc3a6`按系数幅度增加guard digits后重算，源、数据、域和算法保持。

两份source首科学输出、两份九点optimization首输出各自完成后才读取另一实现，
source与optimization互盲分别登记为true。主replay首输出冻`9ec7702332`，
独立replay首输出冻`9cfc487fa1`；公开计数用途为回顾性，不登记blind检验。
事后comparison最终程序另冻`114d87154b`，完整消费九点源、108项观测及五分量带。
它另外独立逆读公布r在同一gain circle上的pump输入并重算CH，
区分独立首输出的训练source-balance基线与完整公布五控制点；原首输出保持。

Klyshko小根producer/consumer预编译冻`477d8cd184`，独立审计预编译冻`b32e348045`，
五层fresh trust0/werror及五文件LSP通过，认证由原PGF及两个herald方向承担。
原始trial/count archives保持未读，未新增公开计数、外联、推送或publish写入。

完整fringe消费者先冻`0adb738ecd`，九点585个square-free/Sturm序列、1170实根全部重建，
q∞/极值/visibility逐项相等；全覆盖回执冻`4ed4ec6f1d`。
verification冻`d97bb657a7`，16项focused tests及显式fresh退出0，readiness实际消费研究回执。
默认门禁保留原五核心true、nominal optimum false与退出1，没有用新九点带覆盖旧17点判决。

## 2026-10-02 · 源快照、已记录输入与实际反馈

ci0001合同先冻`ef11f683ff`，producer/consumer最终预编译冻`9b0a271dce`，
独立审计与执行程序先冻`3c60c5d250`。两个合法不同Plant/单位Drive由任意正snapshot生成；
κ比值2是合同固定见证，不由FW偏离或公布最优点选择。
source/calibration等值限定gain-only读出及未记录输入的接口，不登记所有公开来源不可识别。

实际单位pump角轨道的HasDerivAt、known-input recovery和samePlant乘法更新独立认证；
139候选声明/26417闭包节点，三文件fresh trust0/werror及LSP通过，仅标准三公理。
反馈函数只消费已记录current Drive、同Plant observed Gain和desired Gain，
target等式不在primitive；signed current独立例生成正新输入、power13和ratio3/2。
没有运行硬件、追认历史输入、改变原门禁或增加全Gaussian/Born声明。

## 2026-10-02 · 完整matched概率到同源控制

os0001合同先冻`3bec60e1a4`，完整三层候选及所有编译修复先提交后执行，最终先冻`c3f330ff6f`。
输入只包含A/B/J观测域及测量角色，不以预知t、η或gain作为inverse前提。
H/V直接消费同一个RawKernel；samePlant生成source、概率域和逆Gain，再生成目标输入。
独立审计先冻`45b22ac574`，两行werror顺序修复先冻`214859141f`，生产候选字节保持。
八文件fresh trust0/werror与LSP通过，未知η例、双herald、完整source返回和非法域kernel验收。
542候选声明、17383闭包节点，仅标准三公理；未读取新计数或运行硬件。
exact inverse没有把有限计数中心提升为实际概率，实际NIST资格及旧门禁保持。

## 2026-10-02 · 有限计数源域与有界反馈

fc0001合同先冻`aaa0563f02`，程序先冻`c1e2c97615`，固定rounded-expectation fixture冻
`ae867f905a`后执行。β=.01、240 fixed bets、N=1e8及source/取点/whole-box规则保持。
标定输入不含隐藏t/η/gain/κ；独立numberMass6+原尾核对240边界及真source/gain/κ/newgain包含。
它是合成控制，没有取得新实际记录或把旧Bell表改作N=1标定。

反馈候选先冻`fddf0ef60b`，独立审计先冻`d24d48a7dd`，九文件fresh trust0/werror及LSP通过。
数值128位floor/ceil唯一及相同有理midpoint独立消费；统计/Ville和数值adapter的kernel旗标保持false。
19项focused tests通过，验收回执冻`19d0854c2e`，原science first及来源保持。

共享Git遗留锁曾阻止冻结，precompile guard停止后没有启动独立计算/Lean编译。
只读诊断确认无Git writer，唯一language server持有只读句柄；旧锁字节完整保留于本地临时存储，
原index前后sha相等，未停止外部reader。首次守卫失败日志另冻`0f496fd3ff`。
原root/门禁/publish保持，未运行硬件、发送外联或推送。
