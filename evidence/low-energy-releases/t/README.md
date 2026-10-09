# Homework

私人研究与工程施工仓，用于跨设备保存可继续推进的源码、Lean 证明、实验、研究设计和笔记。
本仓承担持续研究与共享记忆；成果的准确范围以源码、机器验证和对应权威入口为准。

## 从这里开始

| 工作 | 权威入口 |
| --- | --- |
| 仓库协作、改动与验证纪律 | [AGENTS.md](AGENTS.md) |
| Lean 环境、模块入口与验证方式 | [Lean 工作区](Lean/README.md) |
| 数学、物理、算术、意识与社会等研究线 | [Lean 文档索引](Lean/docs/README.md) |
| living-law 框架控制与领域路由 | [框架 active route](Lean/docs/handoffs/living-law-framework-active-route.md) |
| TruthChild AGI 原型 | [TruthChild](TruthChild/README.md) |
| 生物医学实证输入与来源清单 | [Biomedical](Biomedical/README.md) |

当前研究责任只在各自唯一 active route 中维护。本页保持稳定导航，不复制实时进展。
历史 SU7 / Borromean 资产从 [Lean 文档索引](Lean/docs/README.md) 的历史入口查阅。

## 目录

| 目录 | 内容 |
| --- | --- |
| `Lean/` | 形式化源码、证明设计、验证脚本及登记的研究资产 |
| `TruthChild/` | AGI 原型、模型架构、运行时与冻结实验历史 |
| `Biomedical/` | 实证来源清单、计算脚本和轻量可复现材料 |
| `Verification/` | 数学与物理验证程序、实验报告和轻量输出 |
| `Aha/` | 概念笔记、论述和跨领域研究设计 |
| `VibeMath/` | SAT 等探索性数学与程序实验 |
| `Demos/` | 独立演示与交互原型 |
| `output/` | 筛选保留的可阅读成果与导出物 |

## Lean 起步

环境版本由 `Lean/lean-toolchain` 和 `Lean/lake-manifest.json` 固定。

```bash
cd Lean
lake exe cache get
lake env lean Path/To/ChangedFile.lean
```

需要验证当前生产入口的跨模块整合时，使用 `lake build LivingLawActive`。
历史模块与研究资产不因存在于仓库中而成为默认构建入口；具体边界见 [Lean README](Lean/README.md)。

## 保存与清洁

- 源码、必要输入、验证方法和有明确用途的研究资产纳入 Git。
- 临时 probe 的去留与长期研究资产登记见 [scratch 入口](Lean/scratch/README.md)。
- 当前状态留在 active route；稳定机制各有唯一说明；冻结历史保留在 archive 和 Git 历史中。
- `Data/`、`.lake/`、`target/`、`node_modules/`、编译产物、缓存和 raw source archive 留在本地。
- 大型数据跨设备另行同步，仓库只保存必要的来源清单或复现脚本。

提交前检查 `git status --short`、`git diff --check` 和 `git diff --stat`，只提交本次整理或施工的文件。
