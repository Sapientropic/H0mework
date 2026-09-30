# 来源材料索引

本仓的有效用法见[复现指南](reproduction.md)，主张与源码对应见[证据表](evidence-map.md)。本页负责定位研究来源、冻结认证与历史过程记录。

## 固定来源的阅读方式

[`docs/source/`](source/) 和 [`docs/physics/`](physics/) 内的材料均作为固定来源工件导出。每份文件的原路径、来源修订与 SHA256 记录在 [`export-map.json`](../tools/export-map.json) 的 `artifacts` 中；正文保持该版本的原字节。

其中的“当前”“本轮”、运行耗时和完成状态指对应源修订。原文中的命令及链接使用研究源仓布局；本仓的执行命令以复现指南为准。旧链接的目标可能已迁移，也可能没有纳入选集。

按 `artifacts.source` 或 `modules.source_path` 查询原目标，`path` 给出本仓文件地址。下面查询生命周期原文引用的证明：

```bash
python3 - <<'PY'
import json
with open('tools/export-map.json') as stream:
    data = json.load(stream)
source = 'Lean/SaturationMonoid/ResponsibilityLifecycleKernel.lean'
for row in data['modules']:
    if row['source_path'] == source:
        print(row['path'], row['source_revisions'])
PY
```

查询没有记录时，该目标不在选集内。原路径视图恢复已导出的材料及其字节；可用参数见[原路径版本视图](reproduction.md#原路径版本视图)。

## 机制与认证

| 材料 | 详细来源 |
| --- | --- |
| 责任、债务与结构归属 | [foundation](source/foundation/)；[生命周期](source/foundation/responsibility-conservation-lifecycle.md) |
| Navier–Stokes 原生载体与控制 | [navier-stokes](source/navier-stokes/)；[配对载体](source/navier-stokes/native-paired-source-carrier.md) |
| 计数观察与原始 Riesz 动态观察 | [计数观察](source/observation/source-counted-observation.md)；[Riesz 观察](source/observation/original-riesz-dynamic-observation.md) |
| 低能唯象推导与认证 | [验证入口快照](source/physics/low-energy/verification-README.md)及其同级目录 |
| Case 2 全量子机制与认证 | [full-quantum](source/physics/low-energy/full-quantum/)；[完整物质时间生成元](physics/low-energy/full-quantum/README.md) |
| Case 5A 不同时代材料 | [T 期入口](source/physics/constrained-quantum/README.md)；[X 期入口](source/physics/constrained-quantum/README-x.md) |
| Bell 名义装置重放与冻结判据 | [重放说明](source/physics/bell-nist/nist-real/nominal-replay/README.md)；[criterion](source/physics/bell-nist/nist-real/nominal-replay/criterion.md) |

`certification.md`、`audit-certification.md` 等报告保存对应修订的验收结果与条件；[`evidence/`](../evidence/) 保存机读回执及失败结果。公开回执的路径变换与原件身份见[公开回执与原始来源](evidence-publication.md)。

## 历史过程材料

以下材料描述源仓的历史进度、讨论或访问过程，单独作为过程依据阅读：

- Navier–Stokes [2026-08-10 checkpoint](source/navier-stokes/navier-stokes-native-turbulence-total-evolution-checkpoint-2026-08-10.md)。
- 动态观察 [Living-Law ledger](source/observation/living-law-framework-checkpoints.md)、[卷 45](source/observation/living-law-framework-checkpoints-volume-45.md)与 [source-word ledger](source/observation/source-word-checkpoints.md)。
- Bell [协议草案](source/physics/bell-nist/nist-real/protocol.md)、[信息访问记录](source/physics/bell-nist/nist-real/access-record.md)与 [controller capsule](source/physics/bell-nist/nist-real/controller-capsule.md)。

这些文件保留原路径与哈希，便于回执复核和源版本重建。当前主张的消费入口由证据表指定。

## 第三方材料

| 材料 | 作者与出处 | 版权与使用依据 |
| --- | --- | --- |
| [Shalm 论文摘录](source/physics/bell-nist/nist-real/nominal-replay/shalm2015-channel-inputs.txt) | L. K. Shalm et al., *Strong Loophole-Free Test of Local Realism*, Physical Review Letters 115, 250402 (2015)，[DOI 原文](https://journals.aps.org/prl/pdf/10.1103/PhysRevLett.115.250402)；摘录自 arXiv:1511.03189v2 | APS 已发表版本采用 [CC BY 3.0](https://creativecommons.org/licenses/by/3.0/)。冻结摘录与发表版的对应见[Shalm 摘录版本对应](#shalm-摘录版本对应)。arXiv v2 的[非独占分发许可](https://arxiv.org/licenses/nonexclusive-distrib/1.0/license.html)保留为原提取版本的来源记录。 |
| [Christensen 博士论文摘录](source/physics/bell-nist/nist-real/nominal-replay/christensen-appendix-a.txt) | Bradley G. Christensen，*Advanced tests of nonlocality with entangled photons*，University of Illinois Urbana-Champaign 博士论文（2016），[学校馆藏条目](https://www.ideals.illinois.edu/items/92889) | Copyright 2016 Bradley Christensen。引用范围为 Appendix A 与 §4.6.2 的五页，用于核对特定装置模型、公式读法和偏振参数；文件保留作者、页码、来源和 PDF 哈希。 |
| L-alanine 40 K 晶体与计算回执 | 论文作者 Hayashi、Nishioka、Kasai、Nishibori，[IUCr 官方原文](https://journals.iucr.org/m/issues/2025/03/00/woz5001/woz5001.pdf)；数据作者 Eiji Nishibori，[Zenodo 记录](https://zenodo.org/records/14688662) | 原论文与数据采用 [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。派生计算与来源记录保存在 [`evidence/biomedical/`](../evidence/biomedical/) 中。 |

Christensen 摘录用于研究核验与评述，[美国版权法的合理使用原则](https://www.copyright.gov/fair-use/)将该用途列为评估情境，并结合作品性质、使用范围与替代影响判断。本项目据这一研究用途保留选定材料及其引用上下文；第三方原文继续保留原作者版权。

## Shalm 摘录版本对应

冻结的 arXiv v2 摘录包含三个正文块，其实质文字、数值与公式均对应 [APS 开放发表版](https://harvest.aps.org/v2/journals/articles/10.1103/PhysRevLett.115.250402/fulltext)。冻结文件保留冠词、介词、单复数、引用编号，以及停止规则的 `criteria` / `criterion` 等版本差异。第 171–176 行的原提取合并了两栏，恢复分栏后对应文字一致。

APS PDF SHA256：`49c40d39e6a61c8cb961aae327ce7bc266132d9ed20ceefa93792930cd99c1da`。冻结摘录的来源身份由导出映射记录，正文保持原字节。

项目原创内容的 Apache-2.0 许可见 [LICENSE](../LICENSE)；第三方原文保留作者、出处、版权和适用许可。归属汇总见 [NOTICE](../NOTICE)。
