# 资本主义的结构总定理：公开材料复现

[逐结果映射](capital-formation-map.json)按论文18项编号结果连接原文、固定源码与实际消费者。第10项为命题；其余为定理。正文、双语附录及可编辑源码的正式文件由[发布清单](../papers/capital-formation/2026-11-04/manifest.json)固定，[验收身份](capital-formation-readiness.md)区分本篇来源核对与原证明执行。

## 检查当前公开材料

在本仓根目录执行，需要Git和Python 3，不需要私有研究仓：

```sh
python3 tools/capital_formation.py entry --require-ready --output .local/capital-formation-entry
```

入口逐项核对五份发布文件与编辑包内清单、四份原稿、18项结果分类、105份来源登记、100个采用模块及其递归导入环境、实际直接消费者、160项既有完整类型观测及五份辅助源码。直接消费者另引用63个已验收owner，合计163个公开支持模块；675处源声明位置与160项已索引完整类型观测分别保存。

公开证明固定于提交[`2d6fbc96e33b7c4c3cfd91104fda74e3caeda045`](https://github.com/Sapientropic/H0mework/tree/2d6fbc96e33b7c4c3cfd91104fda74e3caeda045)。检查器只读取该Git对象、已签收回执和本篇发布字节，不生成新的Lean认证，也不覆盖原回执。

浅克隆需先取回这个固定提交的Git对象：`git fetch origin 2d6fbc96e33b7c4c3cfd91104fda74e3caeda045`。检查器沿用该验收绑定的source-view helper字节。

## 复用已有证明与缓存

本篇的100个采用模块处于原`economic-constitution-source-df`包的2825模块实际导入闭包。原研究epoch为`df421ff600085cbc290a7ae946193961bed7c83b`；公开owner按该epoch的source alias、目标字节及递归环境认回，不另造命名空间或库。

需要实际重跑时，沿用本仓工具链、固定依赖和已有缓存；首次缺少依赖时运行`make bootstrap`。以下命令在同一公开证明包上构建并检查，输出另存：

```sh
python3 tools/edition_release.py --edition economic-constitution build --package economic-constitution-source-df --output .local/capital-source-df-build
python3 tools/edition_release.py --edition economic-constitution trust --package economic-constitution-source-df --output .local/capital-source-df-trust
python3 tools/economic_constitution.py types --package economic-constitution-source-df --output .local/capital-source-df-types
```

`trust`保留Lake freshness与原信任强度，类型检查使用既有完整Expr DAG机制。Linux与macOS的构建产物按实际平台区分。完整原选集与全部十六包复现见[原验收包指南](economic-constitution-reproduction.md)。单包重跑的范围由实际命令承担，不替换旧回执。

## 原文与辅助来源

编辑包保留四份Markdown、同名PDF、十张双语SVG及矢量PDF、书目、来源对应、必要构建器和实际审阅记录。从包内`packaging-README.md`进入论文重建。原始绑定与源选择分别为`records/public-source-binding.json`、`records/source-selection.json`，原字节保留在发布ZIP中。

五份辅助文件同时原字节保存在[公开来源目录](../papers/capital-formation/2026-11-04/source-excerpts/)。它们分别承担形态实例、分配引理和归档／零发行反例；一般生产声明已经处于已验收包。这五份文件是保全资源，不作为新的独立编译owner或新认证。

原来源登记还保留31条包外的词法直接导入参考，沿其原source与读深解释；本篇实际前向imports闭包已经闭合。网站仅把确实属于已验收闭包的消费者链接为公开Lean模块。

本次接入没有更改Lean源码、库owner、默认覆盖、工具链、依赖、CI布局、工作流或远端proof-cache。新论文复用原成功证明和固定依赖；科学回放保持原执行身份。
