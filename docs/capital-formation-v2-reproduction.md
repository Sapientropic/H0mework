# 《资本主义的结构总定理》第二版证明与复现

[第二版逐项映射](capital-formation-v2-map.json)登记正文 19 项编号结果。定理 12、定理 1 的第五分肢、例 2 和附录 E.3 采用 CF17。首版的结果 1–11 保留编号，原结果 12–18 对应第二版 13–19。

| 范围 | 固定公开证明 | 验收 |
| --- | --- | --- |
| CF0–CF16 | [EconomicConstitutionSourceDF](https://github.com/Sapientropic/H0mework/tree/2d6fbc96e33b7c4c3cfd91104fda74e3caeda045) | [首版验收](capital-formation-readiness.md)保存 2,825 个模块闭包和所采用的 160 项完整类型。 |
| CF17 | [SocietyBookRiskCompensation](https://github.com/Sapientropic/H0mework/blob/fd6147f8c337d88ebf72d91ddadef0aa601e6c2e/Lean/H0mework/Papers/SocietyBookRiskCompensation.lean) | [本地验收](../evidence/capital-formation-v2/acceptance/index.json)记录 1,372 个模块闭包、4 个生产模块和 5 个直接消费者的 17 项完整类型及信任审计。 |

CF17 的 55 个定价模块和 3 个支撑根可从公开 owner 逆恢复，已与 Homework 的固定 Git 字节逐项比较。回执同时登记研究库独立 T1 验收的原始摘要。该原件含本机路径，公开执行的三个回执保留本次实际结果。CF17 的公理依赖为 `propext`、`Classical.choice`、`Quot.sound`。

从当前 H0mework 根目录核对发行文件、来源视图及实际验收回执：

~~~sh
python3 tools/capital_formation_v2.py entry --output .local/capital-formation-v2-entry
~~~

使用现有 Lake 缓存重新运行 CF17：

~~~sh
python3 tools/society_book.py build --package risk-compensation --output .local/cf17-build
python3 tools/society_book.py trust --package risk-compensation --output .local/cf17-trust
python3 tools/society_book.py types --package risk-compensation --output .local/cf17-types
~~~

双语正文、技术附录和可编辑包见[发布登记](../papers/capital-formation/2026-11-12-v2/manifest.json)。从解压根目录按包内 README 重建四份 PDF。复核通过的源和 PDF SHA-256 分别由包内清单和发布登记固定。

[缓存保全核对](../evidence/capital-formation-v2/acceptance/cache-preservation.json)记录本地计划与相同证明范围的远端计划比较。站点发布与 Lean 全选集验收分别登记。
