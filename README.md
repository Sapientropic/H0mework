# H0mework

H0mework 收录研究论文的 Lean 证明选集、复现程序与冻结证据。选集按固定源提交导出，包含入口的完整依赖闭包；构建与独立检查使用本仓文件。

## 快速上手

准备 elan/Lake、Git、make 和 Python 3（含 `venv`），在仓库根目录运行：

```bash
make bootstrap   # 获取固定 Lean / mathlib 版本的缓存
make build       # 构建默认证明选集
make check       # 运行低能唯象的冻结证据独立检查
make check-map   # 全量核对导出文件与固定源字节
```

工具链由 [`Lean/lean-toolchain`](Lean/lean-toolchain) 与 [`Lean/lake-manifest.json`](Lean/lake-manifest.json) 固定。完整命令、环境要求、版本视图和构建例外见[复现指南](docs/reproduction.md)。

## 研究入口

| 研究线 | 内容 | Lean 入口 |
| --- | --- | --- |
| 过程核心 | 生命周期守恒、有限结算、完整历史与残差修订 | [SourceProcessCore](Lean/H0mework/Papers/SourceProcessCore.lean) |
| 同源物理 | Spin×SU7 共同作用、九场解、量子/Fock 对应与动力学 | [PhysicsCommonSource](Lean/H0mework/Papers/PhysicsCommonSource.lean) |
| 低能唯象 | 低能展开、传播、物质交换与全时间 Kubo 响应 | [LowEnergyPhenomenology](Lean/H0mework/Papers/LowEnergyPhenomenology.lean) |
| 整账会计 | 整账结构、债务结算、PrimeShadow 与 Fock 消费者 | [WholeLedgerAccountingY1](Lean/H0mework/Papers/WholeLedgerAccountingY1.lean) |
| 动态观察 | 计数观察、E/I 版本证明与运行时消费者 | [ObservationDynamics](Lean/H0mework/Papers/ObservationDynamics.lean) |
| 低能环响应（Case 2） | 闭迹、准备态完整词、玻色有效核与解析余项 | [LowEnergyLoopResponse](Lean/H0mework/Papers/LowEnergyLoopResponse.lean) |
| 原生长河 | Navier–Stokes 原生演化与历史消费者 | [NativeFlow](Lean/H0mework/Papers/NativeFlow.lean) |
| 约束局部量子（Case 5A） | 版本化复合衰变程序、量子约束与共同族时间演化 | [ConstrainedLocalQuantumK17](Lean/H0mework/Papers/ConstrainedLocalQuantumK17.lean) |

[证据对应表](docs/evidence-map.md)列出各稿主张、源码入口、来源修订与配套证据，包括 Bell 独立裁决。

## 阅读与来源

- [复现指南](docs/reproduction.md)：本仓支持的构建与检查命令。
- [证据对应表](docs/evidence-map.md)：主张到模块、程序、回执及版本的对应。
- [来源材料索引](docs/source-materials.md)：机制说明、认证报告、历史过程材料与第三方摘录的阅读方式。

`Lean/` 保存证明与固定依赖配置，`scripts/` 保存复现程序，`evidence/` 保存冻结回执；[`tools/export-map.json`](tools/export-map.json) 记录源路径、导出路径、修订和哈希。

本项目原创内容采用 Apache-2.0；许可原文与归属见 [LICENSE](LICENSE) 和 [NOTICE](NOTICE)。第三方材料的版权、许可与引用范围见[来源材料索引](docs/source-materials.md#第三方材料)。
