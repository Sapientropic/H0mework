<p align="center"><img src="docs/assets/banner.svg" alt="H0mework · 未干的地图：名字里的 0 是一笔朱砂圈；同样的圈落在地图上，一张未干的地图从那里长出" width="100%"></p>

简体中文 · [English](README.en.md)

这里是一组论文背后的证明与证据。

它们从同一个源出发：过程怎样保留自己的历史，场和粒子怎样从同一处生成，经典与量子怎样相认，账平之后债为何还在，观察为何总要为压缩付账。论文用文字把这些故事讲给人听；这里的 Lean 证明、复现程序和冻结回执，则把每一句写成定理的话交给机器，从头再核一遍。

读者不必相信作者。你可以亲手检验。

## 首发论文

| 论文 | Zenodo | 正文与补充 | 证明选集 |
| --- | --- | --- | --- |
| **状态不是历史，源才是**：过程同一性、责任承接与最小修订<br>*The State Is Not the History, the Source Is* | [DOI](https://doi.org/10.5281/zenodo.23210084) | [首发成品](papers/first-release/README.md) | [首发证明与复现](docs/first-release-reproduction.md) |
| **这浩瀚宇宙里，我们没找到魔法**：Spin×SU(7) 理论的同源生成与经典—量子对应<br>*We Found No Magic in This Mighty Universe* | [DOI](https://doi.org/10.5281/zenodo.23210292) | [首发成品](papers/first-release/README.md) | [逐主张映射](docs/first-release-map.json) |

## 更多研究线

| 研究线 | 内容 | Lean 入口 |
| --- | --- | --- |
| 低能唯象 | 低能展开、传播、物质交换与全时间 Kubo 响应 | [LowEnergyPhenomenology](Lean/H0mework/Papers/LowEnergyPhenomenology.lean) |
| 低能环响应 | 闭迹、准备态完整词、玻色有效核与解析余项 | [LowEnergyLoopResponse](Lean/H0mework/Papers/LowEnergyLoopResponse.lean) |
| 约束局部量子 | 原作用约束、量子约束与共同族时间演化 | [ConstrainedLocalQuantumK17](Lean/H0mework/Papers/ConstrainedLocalQuantumK17.lean) |
| 原生长河 | Navier–Stokes 的原生演化与历史消费者 | [NativeFlow](Lean/H0mework/Papers/NativeFlow.lean) |
| 整账会计 | 整账结构、债务结算与不可伪造的结算 | [WholeLedgerAccountingY1](Lean/H0mework/Papers/WholeLedgerAccountingY1.lean) |
| 动态观察 | 计数观察、版本证明与压缩的精确代价 | [ObservationDynamics](Lean/H0mework/Papers/ObservationDynamics.lean) |

## 亲手检验

入口检查需要 Git、make 和 Python 3（含 `venv`）。在仓库根目录：

```bash
make check-first-release-entry  # 检查导出身份、完整 Fock、Born 与精确控制
```

构建 Lean 证明另需 elan/Lake，首次执行 `make bootstrap` 取回固定依赖缓存，再运行 `make build-first-release`。完整验收运行 `make check-first-release-full`。范围与运行依赖见[首发复现指南](docs/first-release-reproduction.md)，实际结果见[首发准备状态](docs/first-release-readiness.md)。工具链版本由 [`Lean/lean-toolchain`](Lean/lean-toolchain) 与 [`Lean/lake-manifest.json`](Lean/lake-manifest.json) 固定。原八稿的命令与版本说明见[旧版复现指南](docs/reproduction.md)。

## 从论文走到证明

- [证据对应表](docs/evidence-map.md)：每篇论文的主张落在哪个模块、哪段程序、哪份回执，包括 Bell 实验数据的独立裁决。
- [来源材料索引](docs/source-materials.md)：机制说明、认证报告、研究过程材料，以及引用的第三方原文。
- 首版论文正文中的"代码与数据可用性"一节，对应标签 [`papers-2026-09`](https://github.com/Sapientropic/H0mework/tree/papers-2026-09)；首发修订选集按[逐主张映射](docs/first-release-map.json)使用各自固定来源。

`Lean/` 是证明，`scripts/` 是复现程序，`evidence/` 是冻结的计算结果；[`tools/export-map.json`](tools/export-map.json) 记下每个文件的来处与哈希。`papers/first-release/` 保存两篇首发论文的正文、补充、可编辑来源与成品。

## 许可

原创代码与证据采用 Apache-2.0，见 [LICENSE](LICENSE) 与 [NOTICE](NOTICE)。首发论文沿用成品元数据登记的 CC BY 4.0，见[论文许可](papers/first-release/source/papers/source-process-core/zenodo-metadata.md#licenses)。引用的第三方原文保留原作者的版权与许可，详见[来源材料索引](docs/source-materials.md#第三方材料)。
