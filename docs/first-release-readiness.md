# 两篇首发准备

首发范围为过程核心与同源物理旗舰（CourtyCourt Case 0）。逐主张的固定版本、生产声明、直接消费者、公开地址与检查身份由[首发映射](first-release-map.json)维护，运行命令见[复现指南](first-release-reproduction.md)。

## 验收状态 · 2026-10-07

选集为 final：过程核心 26 项、物理 34 项，八份中英正文与补充材料均已按定稿文件摘要核对。60 条主张的生产声明、直接消费者、资源依赖及对应检查均已验收。

15 个版本入口的完整增量构建通过，实际构建耗时 142.63 秒。随后在各自独立的 Lean 环境中执行 trust0／werror 审查，遍历所选声明的类型、值及互递归／归纳元数据闭包；全部通过，`unsafe = 0`、`partial = 0`，公理均为 `propext`、`Classical.choice`、`Quot.sound`。范围、输入摘要、构建缓存及实际结果见[证明验收回执](../evidence/first-release/acceptance/proof-20261007/receipt.json)。

过程核心 selection 登记的 21 个补充声明已纳入审查根集，包含 `second_resolution_is_direct` 与 `Frame.request_budget`。15 个入口的完整 trust0／werror 审查再次通过，共 4,151 个范围内审查根，`unsafe = 0`、`partial = 0`。全部证明输入与原构建一致，预检查使用 `--no-build`，编译产物摘要保持；实际根集与结果见[补充审查回执](../evidence/first-release/acceptance/proof-root-supplement-20261007/receipt.json)。

导出身份、资源及公开原路径恢复检查通过。六项入口检查与十四项 Bell 检查均已验收，实际程序、输入、耗时、新输出及原反控见[科学执行回执](../evidence/first-release/acceptance/scientific-20261005/receipt.json)。验收汇总来自多个真实运行，原冻结输出及失败判决完整保留。

P26 的全部 18 个固定量子独立程序已通过，实际耗时 4,721.66 秒；原物理时间、系数、判决与范围逐字段保持。新结果及原／新输出身份见[量子执行回执](../evidence/first-release/acceptance/quantum-20261005/receipt.json)。

AD 完整双树、统计消费者、完整域和最终消费者已完成实际重算，四组原反控共 47 项全部通过，具体结果登记于科学执行回执。

导出中的私有声明和认证观察命令所属模块地址已同步修正。十个科学视图与十八个量子视图恢复后的输入均与原执行字节一致，原回执保留执行时的映射身份；当前对应关系见[来源兼容核验](../evidence/first-release/acceptance/scientific-20261005/source-compatibility-after-cap-command-names.json)。

## 来源与成品

必要来源修正已由主仓 `089a1727` 与 `fa15016c` 保存，公开地址、原／目标摘要和依赖版本见首发映射。AB／AC 的状态暴露证明采用已提交 AE 版本的展开修正。波片生产体与直接消费者采用 AE 中已有的完整证明，原 AC 候选保持原字节并归入历史构建范围；具体来源与地址见首发映射的 `build_source_adaptations`。

源码与证据选集已保存为[公开验收提交 `234817b3`](https://github.com/Sapientropic/H0mework/tree/234817b3c3f7a1023226e7a4fdb8660ddcbc9d0a)，版本绑定见首发映射的 `local_delivery`。

两篇论文的代码可得性、来源索引、生成器和 arXiv／Zenodo 元数据已同步，写作仓版本由首发映射的 `local_delivery` 登记。八份阅读版 PDF、两个可独立编译的英文 arXiv 包及对应 PDF、可编辑正文、图源、排版脚本与书目均已备齐，见[两篇首发成品](../papers/first-release/README.md)；精确文件身份、页数与验证记录见[成品清单](../papers/first-release/manifest.json)。全部 613 页已渲染并视觉复查。

selection 中核心 C13 的两项声明已使用源码全名，21 个补充根均已审查；60 条主张的数学陈述、量词、固定来源及证明／科学输入保持。当前元数据与原验收的对应关系见[选集兼容核验](../evidence/first-release/acceptance/paper-binding-20261007/metadata-correction-compatibility.json)。首发的源码选集与论文成品均已完成本地交付。

## 公开记录 · 2026-10-07

H0mework 已公开，两篇论文以 v1 预印本发布于 Zenodo。每条记录包含中英正文与中英补充材料四份 PDF，采用 CC BY 4.0；均引用上述固定验收提交。

| 论文 | 版本 DOI |
| --- | --- |
| 过程核心 | [10.5281/zenodo.23210084](https://doi.org/10.5281/zenodo.23210084) |
| 同源物理旗舰 | [10.5281/zenodo.23210292](https://doi.org/10.5281/zenodo.23210292) |

## 历史版本

首版八稿与 `papers-2026-09` 保持原绑定。R2 固定快照的最终构建记录有四处 elaboration 失败；原字节保留为历史版本，新首发主张按各自版本验收。[旧复现入口](reproduction.md)继续描述原八稿检查。
