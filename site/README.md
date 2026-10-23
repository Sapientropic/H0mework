# 可视化网站

把仓库里的论文、逐主张映射和 Lean 声明做成可浏览的站点。所有页面在构建时直接读取 `../papers`、`../docs/*-map.json` 与映射指向的 Lean 文件，不复制、不转写任何主张。

```bash
bun install
bun run build      # 先跑图的模型自检与构建，再出 dist/
```

本机 Homebrew node 断链时，脚本已用 `bun --bun` 运行 astro。

## 结构

- `src/lib/registry.ts`：发布了什么。`PAPERS` 是论文与各版 DOI，每条带 `theme`；`THEMES` 是论文目录的主题及顺序（`preface` 总序在首页森林里是根上的 0，不占一根枝）。`RELEASES` 说明每次发布的日期、映射、正文（目录或可编辑 ZIP）、PDF 与入口检查命令。
- `src/lib/claims.ts`：把各发布映射的不同 schema 读成同一种主张行。第二版映射按发布选集的证明包成行。整账法按 `docs/whole-ledger-map.json` 成行，正文位置取自已发布可编辑包里的选集，Lean 声明经 `tools/export-map.json` 按源路径与源提交定位到公开模块。一比特按已发布选集成行，Lean 依据取其已验证的 H0 绑定。映射里的 `kernel: pending` 只表示公开包在 CI 中的重新验收，页面不把它当作状态。
- `src/lib/excerpts.ts`：主张展开后先给论文原文。按登记位置里的结果编号（“定理9.1”“命题3.3–3.6”）从该主张所属发布的正文（页面语言）取出定理、命题、定义等的陈述，截到证明之前；位置只写章节（低能两稿）时取这些章节里的结果，标为“所在章节的结果”；位置带文字限定的段落（“§9.2 NIST 名义重放段”）不取。映射里的登记陈述折叠在原文之后，没有原文可取时照常显示。
- `src/lib/papers.ts`：标题、摘要（KaTeX 渲染）、章节标题与统计，取自最新一版正文。`citesOf` 从两种语言正文的参考文献段读出引用了哪些兄弟稿：按任一版 DOI 或主标题匹配（同系列稿在有 DOI 前按标题引用），论文页据此列出“它引用 / 引用它的”。`ORDERED` 是目录顺序（按主题，再按登记），翻页也按它。
- `src/data/reading-<lang>.json`：读者措辞层。映射受验收回执的哈希绑定，措辞是为机器核对写的，所以页面措辞放在这里而不改映射：`title` 换掉中英混杂或整句式的标题（用论文自己的中文术语），`passages` 以段首文字指定要引用的正文段落（位置只写段落描述、没有结果编号时），`cite` 补引结果编号，`statement` 仅在正文没有可引段落时给出整理后的陈述并标明“本站据登记陈述整理”。每条带所据登记原文的指纹，原文改动后构建告警并回退；登记原文始终折叠在“映射中的登记陈述”里。`bun scripts/reading.ts --lang zh|en` 列出过期条目，`--merge <file>` 并入新条目。
- `src/data/claims-<lang>.json`：登记原文不是页面语言时显示的译文（英文页译中文主张，中文页译以英文登记的主张），每条带所译原文的指纹；原文改动后构建告警并回退原文。`bun scripts/translations.ts --lang en|zh` 列出缺译与过期条目，`--merge <file>` 并入新译文。
- `src/components/CheckCommands.astro`：入口检查命令块，右上角带复制按钮；剪贴板不可用时退化为全选文本。
- `src/components/Home.astro`（`/`）：留空的开场画框（创世框占位，只有一句话）、一句介绍与全局统计、论文森林、最近三篇的配图卡片，以及到全部论文的入口。
- `src/components/Forest.astro`：首页的论文森林。朱红的 0 为根，每个主题一根枝，实心节点是已发布论文（链接），空心节点是 `registry.ts` 里 `UPCOMING` 登记的在写稿件（只登记各主题篇数，不写题目；`soon` 为已写成待发布）。旁边的面板随指针显示节点详情。入视口时生长一次；空心节点的虚线环慢转、核心反复凝聚，只在视口内运行；`prefers-reduced-motion` 下静止。
- `src/components/PaperIndex.astro`（`/papers/`）：按主题分区的全部论文；桌面左侧主题导航随滚动标出当前主题，窄屏为吸顶 chips；行尾是迷你主张打孔带。
- `src/components/CheckPage.astro`（`/check/`）：各次发布的入口检查命令，以及每次发布包含哪些论文与复现指南。
- 跨页过渡：支持的浏览器在页面间用 View Transitions，论文标题与配图从卡片或目录行移到论文页的位置（`vtTitle`、`vtFigure` 命名）；不支持的浏览器照常跳转，`prefers-reduced-motion` 下关闭。
- `figures/kit/`：取自 [anatomy](https://github.com/wheresryan22/anatomy)（MIT，commit `689dcf9`）的等轴测绘图核心。
- `figures/<name>/`：一张图一个目录。`model.mjs` 是真值模型，`check.mjs` 用论文定理校验它，`build.mjs --fragment` 输出到 `src/generated/` 供页面挂载；不带参数时输出独立页到 `out/` 用于截图与线端检查。

## 站点元信息

`astro.config.mjs` 设了 `site: https://h0mework.wiki` 并启用 `@astrojs/sitemap`（双语 hreflang，404 不入册）；`public/robots.txt` 指向 sitemap。每页带 canonical、双向 hreflang + x-default、OG/Twitter 卡片。

`public/og/` 是分享预览图：有配图的论文用配图的机器图，其余页面用 `default.png`（打孔卡）。配图更新后重新生成：`bun scripts/og.mjs` 把 1200×630 的静态页写进 `.og/`，逐页截图覆盖 `public/og/<name>.png`（`.og/` 不入库）。

## 新增论文

1. 在 `PAPERS` 加一项，并从 `UPCOMING` 对应主题减一：slug、`theme`（`THEMES` 之一，新主题同时在 `THEMES` 登记双语名）、各版 `{ release, doi }`，系列稿可加 `series`。
2. 新的发布目录在 `RELEASES` 登记（2026-10-17 起的发布在 `papers/<发布>/<日期>/` 放 Zenodo 上传的原字节文件，`manifest.json` 记 DOI 与每个文件的 SHA-256）；映射 schema 与已有发布不同时，在 `claims.ts` 的 `ADAPTERS` 加一个读取函数。
3. 分别以 `--lang en`、`--lang zh` 运行 `bun scripts/translations.ts`，为列出的条目补译文后 `--merge`。
4. 没有配图的论文在首页卡片里显示主张打孔卡；配图做好后在该项加 `figure`，并在 `scripts/og.mjs` 的 `FIGURES` 加同名条目，重截该论文的 og 图。

## 图

| 图 | 论文 | 主张 | 定理 |
| --- | --- | --- | --- |
| `source-tape` | source-process-core | core.C23 | 定理 3.9：整树程序的执行、计费与独立逆读 |
| `pairing-balance` | physics-common-source | phys.P4 | 定理 6.2 与例 6.6：经典—量子配对与暗时刻反例 |
| `current-witness` | low-energy-phenomenology | low1.L17 | §1 与定理 8.1–8.2：有限发展、双侧导数与 Kubo 积分读出同一电流 |
| `curvature-dome` | low-energy-loop-response | low2.Q4 | 定理 1.2 与 §§7–11：完整五项的响应曲率在全部方向上两负一正 |
