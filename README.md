# H0mework

> 论文负责讲述，证明负责作证。

这里是八篇论文背后的证明与证据。

它们从同一个源出发：过程怎样保留自己的历史，场和粒子怎样从同一处生成，经典与量子怎样相认，账平之后债为何还在，观察为何总要为压缩付账。论文用文字把这些故事讲给人听；这里的 Lean 证明、复现程序和冻结回执，则把每一句写成定理的话交给机器，从头再核一遍。

读者不必相信作者。你可以亲手检验。

## 八篇论文

| 论文 | Lean 入口 |
| --- | --- |
| **状态不是历史，源才是**：过程同一性、责任承接与最小修订<br>*The State Is Not the History, the Source Is* | [SourceProcessCore](Lean/H0mework/Papers/SourceProcessCore.lean) |
| **这浩瀚宇宙里，我们没找到魔法**：Spin×SU(7) 理论的同源生成与经典—量子对应<br>*We Found No Magic in This Mighty Universe* | [PhysicsCommonSource](Lean/H0mework/Papers/PhysicsCommonSource.lean) |
| **共同源模型的低能展开**：传播谱、物质交换与量子响应<br>*Low-Energy Expansion of a Common-Source Model* | [LowEnergyPhenomenology](Lean/H0mework/Papers/LowEnergyPhenomenology.lean) |
| **两负一正，裸迹宣誓**：有序闭迹与整球响应曲率<br>*Two Minuses, One Plus, and a Bare Trace Under Oath* | [LowEnergyLoopResponse](Lean/H0mework/Papers/LowEnergyLoopResponse.lean) |
| **天底下没有免费的 lapse**：原作用约束与共同量子 Hamiltonian<br>*No Free Lapse* | [ConstrainedLocalQuantumK17](Lean/H0mework/Papers/ConstrainedLocalQuantumK17.lean) |
| **同源流的有限宏修订、完整应力与晚时全阶演化**<br>*Finite Macro Revisions, Complete Stress, and Eventual All-Order Evolution of Source-Native Flows* | [NativeFlow](Lean/H0mework/Papers/NativeFlow.lean) |
| **账平了，债还在**：源生整账与不可伪造的结算<br>*The Books Balance. The Debt Remains* | [WholeLedgerAccountingY1](Lean/H0mework/Papers/WholeLedgerAccountingY1.lean) |
| **未来来收压缩账单**：自主观察与下一拍精确信息损失<br>*The Future Sends the Bill* | [ObservationDynamics](Lean/H0mework/Papers/ObservationDynamics.lean) |

其中《两负一正》与《天底下没有免费的 lapse》属于 *CourtyCourt · The Theory Takes the Stand* 系列：让理论出庭，接受交叉质询。

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

*Lean proofs, reproduction programs and frozen evidence for eight research papers. The papers tell the story; the proofs take the stand. Every statement written as a theorem can be rechecked here by machine, from scratch. Start with the table above, then `make build`.*
