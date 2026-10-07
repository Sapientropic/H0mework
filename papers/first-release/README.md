# 两篇首发成品 · 2026-10-07

过程核心与同源物理旗舰（CourtyCourt Case 0）的正式正文、补充材料、可编辑图源与构建输入。证明和数据绑定验收提交 `234817b3c3f7a1023226e7a4fdb8660ddcbc9d0a`；逐主张对应见[首发映射](../../docs/first-release-map.json)，验收命令见[复现指南](../../docs/first-release-reproduction.md)。文件摘要见[成品清单](manifest.json)。

| 稿件 | 中文 | English | 中文补充 | English Supplement | arXiv |
| --- | --- | --- | --- | --- | --- |
| 过程核心 | [PDF](pdf/source-process-core.pdf) | [PDF](pdf/source-process-core-en.pdf) | [PDF](pdf/source-process-core-supplement.pdf) | [PDF](pdf/source-process-core-supplement-en.pdf) | [PDF](arxiv/source-process-core-arxiv.pdf) · [源码包](arxiv/source-process-core-arxiv.tar.gz) |
| 同源物理旗舰 | [PDF](pdf/physics-common-source.pdf) | [PDF](pdf/physics-common-source-en.pdf) | [PDF](pdf/physics-common-source-supplement.pdf) | [PDF](pdf/physics-common-source-supplement-en.pdf) | [PDF](arxiv/physics-common-source-arxiv.pdf) · [源码包](arxiv/physics-common-source-arxiv.tar.gz) |

## 可编辑来源

`source/papers/<paper-id>/` 保存中英正文、补充材料、图的 Python／SVG／PDF／PNG 和阅读版排版源码。两篇的参考文献在正文中；共用 BibTeX 记录见 `source/shared/references.bib`。论文引用的算术稿简介按原文保存为导航材料。arXiv 源码包包含英文正文、完整英文补充与矢量图，可单独解包编译。

阅读版需要 Python 3、Pandoc 3、XeLaTeX、xeCJK、TeX Live 的 Latin Modern OTF 及 Noto Serif／Sans CJK SC 常规和粗体字体。进入对应 `source/papers/<paper-id>/` 目录：

```bash
python3 scripts/build_pdf.py manuscript.md
python3 scripts/build_pdf.py manuscript-en.md
python3 scripts/build_pdf.py supplement.md --no-toc
python3 scripts/build_pdf.py supplement-en.md --no-toc
```

从 `source/` 重建英文 arXiv 包：

```bash
python3 shared/scripts/arxiv_package.py papers/source-process-core
python3 shared/scripts/arxiv_package.py papers/physics-common-source
```

代码可得性由 `shared/scripts/code_availability.py <40位提交> --only <逗号分隔的正文路径>` 更新；元数据由 `shared/scripts/zenodo_metadata.py --only source-process-core,physics-common-source` 更新。论文沿用元数据中登记的 CC BY 4.0；原始代码沿用仓库 [Apache-2.0](../../LICENSE)，第三方材料见 [NOTICE](../../NOTICE)。
