<p align="center"><img src="docs/assets/banner.svg" alt="H0mework · 未干的地图：一张从源点长出的地图，每块区域只贴着已有区域生成" width="100%"></p>

这里是一组论文背后的证明与证据。

它们从同一个源出发：过程怎样保留自己的历史，场和粒子怎样从同一处生成，经典与量子怎样相认，账平之后债为何还在，观察为何总要为压缩付账。论文用文字把这些故事讲给人听；这里的 Lean 证明、复现程序和冻结回执，则把每一句写成定理的话交给机器，从头再核一遍。

读者不必相信作者。你可以亲手检验。

## 论文

| 论文 | Lean 入口 |
| --- | --- |
| **状态不是历史，源才是**：过程同一性、责任承接与最小修订<br>*The State Is Not the History, the Source Is* | [SourceProcessCore](Lean/H0mework/Papers/SourceProcessCore.lean) |
| **这浩瀚宇宙里，我们没找到魔法**：Spin×SU(7) 理论的同源生成与经典—量子对应<br>*We Found No Magic in This Mighty Universe* | [PhysicsCommonSource](Lean/H0mework/Papers/PhysicsCommonSource.lean) |

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

需要 elan/Lake、Git、make 和 Python 3（含 `venv`）。在仓库根目录：

```bash
make bootstrap   # 取回固定版本的 Lean 与 mathlib 缓存
make build       # 构建论文证明
make check       # 独立复核低能唯象的冻结证据
make check-map   # 逐字节核对本仓文件与原始来源
```

完整的构建较长，工具链版本由 [`Lean/lean-toolchain`](Lean/lean-toolchain) 与 [`Lean/lake-manifest.json`](Lean/lake-manifest.json) 固定。其余命令与环境说明见[复现指南](docs/reproduction.md)。

## 从论文走到证明

- [证据对应表](docs/evidence-map.md)：每篇论文的主张落在哪个模块、哪段程序、哪份回执，包括 Bell 实验数据的独立裁决。
- [来源材料索引](docs/source-materials.md)：机制说明、认证报告、研究过程材料，以及引用的第三方原文。
- 论文正文中的"代码与数据可用性"一节，对应本仓的标签 [`papers-2026-09`](https://github.com/Sapientropic/H0mework/tree/papers-2026-09)。

`Lean/` 是证明，`scripts/` 是复现程序，`evidence/` 是冻结的计算结果；[`tools/export-map.json`](tools/export-map.json) 记下每个文件的来处与哈希。

## 许可

原创内容采用 Apache-2.0，见 [LICENSE](LICENSE) 与 [NOTICE](NOTICE)。引用的第三方原文保留原作者的版权与许可，详见[来源材料索引](docs/source-materials.md#第三方材料)。

---

*Lean proofs, reproduction programs and frozen evidence behind a family of research papers. The papers tell the story; the proofs take the stand. Every statement written as a theorem can be rechecked here by machine, from scratch. Start with the table above, then `make build`.*
