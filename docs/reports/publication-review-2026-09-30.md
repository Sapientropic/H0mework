# 公开准备审查 · 2026-09-30

审查基线：`87f914a90601b886d76d383d05de38f5901b50ba`，纳入同日公开回执变换。交付版本为本报告所在的提交。日期采用 Asia/Shanghai。检查覆盖导出文件、私有原件、Git 历史与现有远端状态。

结论：65 处私人路径已清除，16 份公开回执与私有原件对照通过，三个资源消费者实际重编通过。公开分支保留前 6 个干净提交，后续导出内容接入为一枚脱敏提交；原件可从私有研究仓的固定版本恢复。第三方摘录按其版权和研究引用用途保留，版本构建的实际覆盖记录如下。

## 机器验收

| 验收 | 结果与条件 |
| --- | --- |
| `make check-map` | exit 0；16789 个模块、969 个工件验证通过，包含 16 个派生回执的 payload 校验 |
| `make check` | exit 0；精确读出、稳定子回执、全时间控制、非交换有限块导数检查通过 |
| `make check-obs` | exit 0；E/I 视图重建及 Gate 字节差异断言通过 |
| `make check-physics` | exit 0；20 组、501 次评价，最大残差 `1.5543122344752192e-15` |
| Y1、K15、K16、K17 最新入口 | 一次定向 `lake build` exit 0，12.355 秒；使用现有缓存，11755 jobs |
| 资源输入与默认失败隔离 | Lake 的 27 个资源输入均已跟踪；11 个 Y 历史失败模块由非默认 `H0meworkPinned` 保存 |
| 固定来源文档 | 105 个文档工件的原字节与映射哈希一致 |
| 映射内模块静态扫描 | 剔除注释和字符串后未发现 `sorry`、`sorryAx`、`axiom`；27 处 `admit` 均为字段或构造子用法 |
| 作者文档与说明 | 320 个本地链接及锚点通过；原路径重建、读出和来源查询示例实际执行通过 |
| 公开回执对照 | 16 个旧 `source_sha256` 保留，变换仅涉及 65 个路径字符串和 1 个 Bell 绑定摘要 |
| 资源消费者 | WholeCell.SourceData、TrueTube.SourceData、BandSource.Data 实际重编通过；exit 0，98.663 秒 |
| 双视图及变换测试 | 9 项测试通过；19 个受影响文件的公开／精确视图分别验证通过 |
| Bell 独立重算 | exit 0，69.53 秒；新鲜复核输出与公开冻结回执语义比对通过 |
| Case 2 | `make check-case2` exit 0，完整独立检查通过 |
| 生成来源 | 固定源重新生成的导出输出与已保存状态完全一致；导出映射再生成也完全一致 |
| 独立候选目录 | 全部 17802 个公开文件及 10 个 gzip 工件路径扫描零命中；候选内导出检查及 9 项测试通过 |

最新入口的实际命令在 `Lean/` 下运行：

```bash
lake build H0mework.Papers.WholeLedgerAccountingY1 \
  H0mework.Papers.ConstrainedLocalQuantumK15 \
  H0mework.Papers.ConstrainedLocalQuantumK16 \
  H0mework.Papers.ConstrainedLocalQuantumK17
```

本次没有运行 clean clone 的完整默认构建，也没有重新运行 `check-5a`、`check-5a-k`。已有默认构建成功日志记录 25504 jobs，时间为 9 月 28 日，早于 9 月 29 日的 Y1/K15–K17 配置更新。定向构建提供最新入口的增量验收。

依赖提交与 manifest 一致。mathlib 两份 benchmark 脚本、batteries 的文档 README 在本地由符号链接变成普通文件，内容均与固定提交的链接目标逐字一致；没有 Lean 依赖源码差异。命令覆盖和配置规则见[复现指南](../reproduction.md)。

## 路径与历史扫描

审查了 16 个提交中的 17921 个唯一 blob，并解压检查 10 个 gzip 工件。常见私钥、服务凭据、赋值式认证信息、原始会话标记与本地协作文件模式没有命中。

基线的 16 份 JSON 含 65 处私人路径：52 处运行命令、10 个输入身份表的路径键、3 个根目录字段。公开工作树已经去掉这些地址；数值、失败结果及原始输入摘要保留。各文件的原始和公开字节摘要详见导出映射的 `publication` 记录，变换合同见[公开回执与原始来源](../evidence-publication.md)。

公开的 Bell 复核回执更新了 `bindings["replay.json"]`，绑定其实际读取的公开回执；输入身份表继续记录原始计算输入。三个 Lean `packetSha256` 更新为公开 JSON 的完整字节摘要，源哈希及可逆改写登记于模块记录。

`origin/main` 的全部 3 个提交与最后干净基线的全部 6 个提交均无私人路径。最后干净基线为 `6278c8a314810857db735d4754c6d64df66400c3`；其后的 10 个私有导出提交含旧路径，原 `papers-2026-09` 标签也指向该历史。

公开分支从上述干净基线接入已核验的导出树，`papers-2026-09` 标签重新绑定交付提交。16 份原始回执和三个原始资源消费者都已逐字节比对源仓的固定 Git 版本，可随时从源仓重新提取；候选副本、重复原件存档和独立历史备份在交付后删除。验收日志继续留在忽略的本地目录。

## 第三方材料

原创内容、第三方摘录与外部晶体数据的版权、引用用途及归属分列于 [NOTICE](../../NOTICE) 和[来源材料索引](../source-materials.md#第三方材料)。Christensen 的选定五页用于核验装置模型与参数，保留原作者版权及完整出处。

### Shalm 摘录核对

从 [APS 官方全文接口](https://harvest.aps.org/v2/journals/articles/10.1103/PhysRevLett.115.250402/fulltext) 一次获取开放发表版，核对冻结 arXiv v2 摘录的三个正文块。实质文字、数值和公式均对应开放版；保留的版本差异包括冠词、介词、单复数、引用编号，以及停止规则的 `criteria` / `criterion`。冻结文件的第 171–176 行合并了两栏，恢复分栏后对应文字一致。

APS PDF SHA256：`49c40d39e6a61c8cb961aae327ce7bc266132d9ed20ceefa93792930cd99c1da`。冻结摘录的来源身份仍由导出映射记录，正文保持原字节。

## 文档与远端

本仓作者维护的入口由 README、[复现指南](../reproduction.md)、[证据表](../evidence-map.md)和[来源材料索引](../source-materials.md)承担。冻结材料中的历史过程记录单列导航，原文作为来源快照阅读。

原冻结 Markdown 的相对链接扫描发现：288 个目标可经导出映射定位，331 个目标未纳入选集。当前指南使用本仓路径；原快照的旧链接由来源材料索引解释。

审查时 GitHub 仓库为 PRIVATE，远端 main 为 `56bda95b8e7aef63da1c627563533ff4858ca308`。交付内容可由该远端版本快进同步；同步分支属于发布操作。[2026-09-20 CI](https://github.com/Sapientropic/H0mework/actions/runs/35515578224) 的独立证据 job 成功，Lean job 因 `no space left on device` 失败，记录的是旧构建环境的磁盘不足。当前版本的本地构建验收与远端 CI 分别记录。

本地 `du -sh` 实测 `Lean/.lake/build` 为 112G、依赖树为 8.2G，含现有缓存与历次构建产物。该占用用于选择构建环境；新环境的实际需求以实测为准。

## 复核记录

原始验收日志保存在忽略的私有审查目录，公开文档保存其内容哈希。

| 记录 | SHA256 |
| --- | --- |
| `public-map-check.log` | `ed576b935903f28c2a65b65f21c87a73a349408d47a449ccd532eeaf1d46870b` |
| `evidence-check.log` | `26416a42d1ee0f3d427d2077e7a15b97f4e09f2c731a83e9db9f454aa24c141d` |
| `case2-check.log` | `4df5d8965a0f8f3367a67001cca9fdd83fb713430f837e9423cab48819c88dd4` |
| `lean-consumers.log` | `b19428112dfa5533eda029c6daab8d6db08d11014263c629566d07037fab8359` |
| `bell-independent-check.log` | `2489b3a53b87de4ed34127760018ed2bb1c966a1dc22e33b570bbe8cb0edc3a9` |
| `migration-fresh-plan.json` | `f5cd69e30830dbba65fac54deb63e55626d710b74a3edcf4fcf312652538cc73` |
