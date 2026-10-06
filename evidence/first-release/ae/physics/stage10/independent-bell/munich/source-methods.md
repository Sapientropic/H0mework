# Munich mu0001：公开控制桥

本接口消费已冻结 tb0001 的原 source/effect，是仪器标签到理论概率的从属输运。
原 `positiveSmoothUnifiedSource / SpinPair.visit 10 / tick16→17`、whole-ledger 与生成后继保持。
方法访问先冻于 `2268d2aae8`，header-only修订先冻于 `3471ee8db8`；
[来源绑定](sources.json)保存官方档案、原README字节与六个精确表头。

## 运行与分母

Zenodo [22936124](https://zenodo.org/records/22936124)公开保存 April 15 与 June 14, 2016 两次运行；
CC-BY-4.0。官方顶层 README 说明两个原下载 ZIP 未重处理。
ZIP 字节已取得；两份相同的 `Readme.txt`与每个CSV首个非空表头已解码。
六个表头之后的记录行未读取、解码或打印。

[SI §I.E，p7](https://journals.aps.org/prl/supplemental/10.1103/PhysRevLett.119.010402/BellTest-supplement.pdf)
规定每次成功 BSM 后在两侧记录 state、setting 与 CEM 结果。
README 所称每侧全部 measurement attempts 是上述本地测量尝试，不能改作全部原子光学激发。
`*_pairs.csv` 保存有效 atom–atom 配对事件；分母与后续准入规则必须从该 event-ready 责任产生。

## 字段及事件选择

两份 README 的字段定义相同：Unix ms 时间；随机输入 `setting`；测量 `result`；
识别所用随机数的 high-precision `local timestamp`；`Bell-state` 仅在 lab1 与 pairs；
`excluded from evaluation` 及 `comment`；pairs 另外含两侧原行号，行号从 header 后起算。
README 给出的两侧时间匹配窗口为 ±100 ms，用于容纳计算机钟抖动。

两次运行的对应表头逐字相同；它们没有增加 token 或角度值字典。
lab1使用分号，字段带有两处前导空格：

```text
time (Unix time in ms);setting;result; local timestamp;Bell-state;excluded from evaluation; comment
```

lab2使用分号，末尾保留空列：

```text
time (Unix time in ms);setting;result;local timestamp;excluded from evaluation;comment;
```

pairs使用TAB分隔八个字段：`timestamp lab 1 (unix time ms)`、`Bell-state`、
`setting lab 1`、`result lab 1`、`setting lab 2`、`result lab 2`、
`line in lab 1 file`、`line in lab 2 file`。
三类header的原字节、长度与SHA256随sources.json固定；不根据后续数据猜分隔符。

README没有确定首记录为0或1，也没有给出exclusion flag的token字典。
行引用采用预声明的完整`{0,1}`起点候选；每个候选都必须通过整文件identity核验，
保留所有成功候选，不依据评分挑选。官方pairs的全部有效记录始终是唯一评分分母。
每侧被引用local行须共享一个raw flag，允许空值；原值按字节保留，
`flag_semantics_verified=false`，不把它擅自解释成ASCII `0/1`。
只有pairs及被引用local行承担模型字段必填和二元责任；
未配对local行保原字节、时间、raw flag与comment审计，模型字段可以缺失，
不以这些非评分行生成setting/outcome/herald字典。

README 把维护时触发、CEM 故障及激光故障列为 invalid 示例。
[SI §IV，pp23–24](https://journals.aps.org/prl/supplemental/10.1103/PhysRevLett.119.010402/BellTest-supplement.pdf)
预先固定总事件数、BSM/CEM 接受时间窗口、分析规则：
激光故障从扫描 Fabry–Perot 监视确定的故障起点至修复整段排除；
CEM 高压击穿关断后至修复自动排除。
每24小时维护包括激光、磁场及 BSM 光路偏振检查；无数据相关的额外裁剪规则。

## 原投影与 herald

[PRL 119, 010402，p2](https://journals.aps.org/prl/pdf/10.1103/PhysRevLett.119.010402)
定义实验的共同 x 基底

```text
u_x = (u_z+d_z)/sqrt(2)
d_x = i(u_z-d_z)/sqrt(2)
Psi± = (u_x⊗d_x ± d_x⊗u_x)/sqrt(2).
```

固定源 qubit 基底 `0=u_x, 1=d_x`。原 singlet 对应 `Psi−`；
Bob 的原 color-Z 把它送到 `−Psi+`，全局负号在 Born 概率中消去。
因此 `Psi−→herald=False`、`Psi+→herald=True`，不从相关值选择 herald 符号。

正文 p3 给出被电离与未电离态：

```text
up_gamma   = sin(gamma/2) u_x - cos(gamma/2) d_x
down_gamma = cos(gamma/2) u_x + sin(gamma/2) d_x.
```

激光线偏振相对水平的角为 `gamma/2`，`gamma` 是 spin-space 角。
两态投影在上述共同基底为

```text
P(up_gamma)   = [I - sin(gamma) X - cos(gamma) Z]/2
P(down_gamma) = [I + sin(gamma) X + cos(gamma) Z]/2.
```

正文 p4 的方法段规定至少一个电离片段点击记 `up`，无片段记 `down`。
于是对原 `Axis.atAngle(gamma)`，`up→outcome=True (−1)`、`down→False (+1)`。
这是谱投影定义产生的标签桥，不能以检测片段效率代付整个制备/读出 fidelity。

对正文给出的名义最优 recipe `alpha=0, alpha'=90, beta=−45, beta'=45`，
理论 Alice `A0/A1` 对应 `alpha/alpha'`，Bob `B0/B1` 对应 `beta'/beta`。
即 Bob 两个设置标签交换；plus herald 仅在 Alice `A1` 翻转 outcome，
与原 `TheoryBlind.alignedAliceOutcome` 相同。
32格精确概率因而可直接消费 tb0001，不调整经验参数。

## 几何与编码无关的直接裁决

原完整source/effect概率对所有合法XZ轴和两个herald生成同一硬合同：

```text
sum_y p(x,y) = 1/2
sum_x p(x,y) = 1/2
p(0,0) = p(1,1)
p(0,1) = p(1,0).
```

这些恒等式直接来自原概率公式；未知连续角不改变它们。
任何固定的二进制setting、outcome或herald重命名都保持该关系。
经验裁决可直接消费此合同，无需逐run角日志、结果定号或公开表拟合。
实际观测按冻结合同裁决这些必要恒等式，未知标签不会改变统计量。
未拒绝不认证完整joint分布；原选择、配对、顺序及readout运输均属于受裁决的仪器合同。

## 固定32格的编码责任

顶层 README、ZIP README、六个CSV表头与SI记录规则没有给出以下值字典：

- `setting` 的具体 token 到 `alpha/alpha'` 和 `beta/beta'`；
- `result` 的具体 token 到 `up/down`；
- `Bell-state` 的具体 token 到 `Psi−/Psi+`；
- 各运行采用该名义 recipe 的独立 command 记录。

原正文 p2 将上述角列为理论最优设置例子；不把这个句子升级成逐运行硬件命令记录。
固定32格若作为具名模型消费，未知binary编码必须由预声明完整有限union消费，不能在结果后挑单个符号方案；
若新增正式非事件控制文件给出唯一映射，则应在事件解码前绑定它。
这不改变理论构造的盲性，也不授予实际硬件为零误差的身份。

## 访问记录

读取范围为 landing、官方 JSON Export、两份 README、六个首个非空header、正文 p2/p3与 p4 左侧方法裁片、
SI pp2–7、§IV pp23–24和§V p25方法段、官网存档 p8下载目录。
官网存档 p4/p5由 URI 识别为 event list，正文未读；p6/p7结果正文未读。
方法相邻文本和一次页头裁片包含已公开结果概要；人类认知未曝光不成立。
未读取April/June计数表、CSV或pairs记录行及新的观测概率。
理论轴、投影、herald 与源码概率保持固定，公开结果概要不参与符号或参数选择。
