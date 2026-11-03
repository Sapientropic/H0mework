# 资本主义的结构总定理 · 首版

[Zenodo：10.5281/zenodo.23927949](https://doi.org/10.5281/zenodo.23927949) · 2026-11-04。

双语正文、技术附录与可编辑源码的原字节保存在此处。五文件均已匿名下载并核对完整SHA256；[发布清单](manifest.json)保存DOI、大小、哈希与回读结果。

| 阅读版 | 页数 | PDF |
| --- | ---: | --- |
| 中文正文 | 24 | [capital-formation.pdf](pdf/capital-formation.pdf) |
| English article | 35 | [capital-formation-en.pdf](pdf/capital-formation-en.pdf) |
| 中文技术附录 | 11 | [capital-formation-supplement.pdf](pdf/capital-formation-supplement.pdf) |
| English technical supplement | 15 | [capital-formation-supplement-en.pdf](pdf/capital-formation-supplement-en.pdf) |

[可编辑源码包](editable/capital-formation-v1-editable.zip)含四稿、四PDF、五组双语SVG与矢量PDF、图源、书目、精确来源、五份辅助Lean原件、本稿构建器及七个共享依赖。解包后从README.md及packaging-README.md进入，先运行包内 `python3 papers/capital-formation/scripts/package_editable.py --check` 核对，再按其命令重建。编辑包白名单、公开变换与依赖检查见[打包回执](metadata/capital-formation-editable-package.json)。

## 证明与复现

[逐结果映射](../../../docs/capital-formation-map.json)对应正文18项编号结果，其中第10项为命题。研究来源固定Homework df421ff600085cbc290a7ae946193961bed7c83b，公开证明固定 [`2d6fbc96e33b7c4c3cfd91104fda74e3caeda045`](https://github.com/Sapientropic/H0mework/tree/2d6fbc96e33b7c4c3cfd91104fda74e3caeda045)。100个采用模块在既有SourceDF的2825模块导入闭包内；160项完整类型观测接回原回执。原声明位置、实际消费者、原epoch及认证各保实际身份。

[五份辅助原件](source-excerpts/)另按各自来源SHA保存，不作为新增编译owner。公共复核命令和实际范围从[复现指南](../../../docs/capital-formation-reproduction.md)及[就绪状态](../../../docs/capital-formation-readiness.md)进入，沿用已有依赖与证明缓存。

论文与原图件采用CC BY 4.0；代码和形式化采用Apache-2.0。完整双语Zenodo元数据见[metadata/capital-formation.json](metadata/capital-formation.json)。
