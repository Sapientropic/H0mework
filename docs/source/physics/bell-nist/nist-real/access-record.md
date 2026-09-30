# 本轮信息访问记录

本轮未读取、下载、解压或解析任何 NIST 原始/压缩/processed/HDF5 评测文件，
未打开派生计数表、结果表或分析输出；没有执行 NIST 事件解码或统计检验。
测试只使用手写合成参数、固定种子随机数和文档中的制备/角度。

读取的一手材料限于 NIST 官方仓库介绍、官方格式说明、格式补充说明和原论文。
保留到设计中的控制事实只有态、偏振基、角度、设置/检测几何、格式及所需校准种类。
论文与格式文档是文献，不是本轮将要接入的评测文件。

必须披露：网页检索工具在查找控制段落时自动返回了邻接的已发表统计结果文字，
论文控制页还同时展示了装置测量数值。这些内容曾进入会话上下文，不能声称完全未见。
它们未作为信道参数、拟合目标、容差、数据分区选择或就绪证据，也没有抄入设计文档。
Lean 泛族候选在这次邻接结果暴露前已构造并编译。

因此可主张的是 **评测文件/试次数据未读**；不可主张更强的“任何已发表结果均未暴露”。
接入前应由未接触结果的独立复核人检查冻结材料；本次不替该角色签字。

访问入口：
- https://www.nist.gov/pml/applied-physics-division/bell-test-research-software-and-data
- https://www.nist.gov/document/bell-test-data-file-folder-descriptions
- https://s3.amazonaws.com/nist-belltestdata/belldata/File_Folder_Descriptions_Addendum_2017_02.pdf
- https://arxiv.org/pdf/1511.03189

本记录是会话工具访问与用途披露，不伪称操作系统级的数据访问沙箱证明。

## 2026-09-24 · NIST 公开渠道专项调查（子代理执行）

为评估名义装置最优门禁的三项缺失输入（独立名义目标函数、信道输入、舍入判据），
本轮对 NIST 公开渠道做了专项检索。**未打开、下载或解析任何评测事件文件**：
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

## 2026-09-24 · 独立名义重放施工（nominal-replay/）

按调查报告执行独立重放：新增 `nominal-replay/` 目录（判据 `criterion.md`、App. A 与论文
信道段落的逐字节提取、`replay.py`/`independent_replay.py` 及回执、11 项自检）。施工为
判据先行（a-priori integrity statement + F1–F16 逐项引证 + 冻结机读块），r0001→r0002 修订
由公开阈值 72.5% 检验驱动并完整披露，r0001 输出原样保留。本轮回放只重新抓取
Christensen 博士论文与 arXiv:1511.03189v2 两件文献（与上轮同一来源），未打开任何评测
事件文件；未修改 `readiness.py`/`request.json`/`instrument.json`/`checks.py`/`real_family.py`。

机器判定：`REPLAY_DEVIATION_EXCEEDS_PREDECLARED_BAND`（独立复核
`CERTIFIED_...`，17 盒点最差 Δθ=5×10⁻⁷°）。文档五点全部在预声明带外；模型本身复现
两个公开阈值（0.668≈2/3、0.7264≈72.5%）。该输出是门禁复核的**候选输入**，不是门禁通过。
