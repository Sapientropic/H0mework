# 可视化网站

把仓库里的论文、逐主张映射和 Lean 声明做成可浏览的站点。所有页面在构建时直接读取 `../papers`、`../docs/*-map.json` 与映射指向的 Lean 文件，不复制、不转写任何主张。

阅读入口默认使用最新稿和当前复现命令，主张与目录不重复标版本号。论文页底部的“版本信息”默认折叠，保留各版下载、DOI与对应复现；检查总页同样先列当前论文，再折叠历史发布。

```bash
bun install
bun run build      # 先跑图的模型自检与构建，再出 dist/
```

本机 Homebrew node 断链时，脚本已用 `bun --bun` 运行 astro。

## 结构

- `src/lib/registry.ts`：发布了什么。`PAPERS` 是论文与各版 DOI，每条带 `theme`；`THEMES` 是论文目录的主题及顺序（`preface` 总序在首页森林里是根上的 0，不占一根枝）。`RELEASES` 说明每次发布的日期、映射、正文（目录或可编辑 ZIP）、PDF 与入口检查命令。
- `src/data/paper-plan.json`：论文地图的分组与立题总数快照，只公开分组数量，不公开未发表题名。`THEMES`从此读取，`UPCOMING`以各组总数减去实际发表记录自动计算；结果触发席位单列`reserved`，不计入已立题或在写数。扩充论文地图时更新这份快照，默认构建检查分类唯一、数量非负、分组总和及发表／在写之和。
- `src/lib/claims.ts`：把各发布映射读成同一种主张行。过程核心第三版新增 C46–C54，沿固定映射读取自己的证明及整账法中已验收的共享条目。整账法第二版使用可编辑包内的正文位置，将容量核与 WA41–WA45 接入 WA1–WA40 的已验收映射。两篇的 Lean 链接直接使用映射登记的公开 owner。一比特按已发布选集及其 H0 绑定成行。
- 社会总定理与经济宪法直接沿各自已验收 map 的精确 owner，源码链接固定到证明提交；DOI 从发布 manifest 读取，正文和附录从可编辑 ZIP 读取。当前 v2 以 `replacesClaimsFrom` 接替 v1 的原文引用，两个版本的下载各保原文件，主张只显示一次。社会的 G10–G12 保留引用接口。经济的八项制度原则与八项采用的形式结果分别展示：空心点表示规范原则，其 Lean 形式支撑可展开核对。`bun scripts/check-society-economic.ts` 核对两版发布文件、v2双语原文、固定来源、唯一主张及分类。
- 资本总定理按本稿的18项编号结果逐项展开，保留第10项为命题。`docs/capital-formation-map.json`从已发布编辑包的原来源绑定与实际原文派生；100个采用模块及63个额外直接消费者均沿同一固定验收闭包，160项既有完整类型观测单独计数，五份辅助原字节源码作为资源展示。新文档由`documentationCommit`链接当前发布版本，Lean源码继续固定到证明提交。`bun scripts/check-capital-formation.ts`核对双语原陈述、编号分类、实际链接及引用。
- `src/lib/excerpts.ts`：主张展开后先给论文原文。按登记位置里的结果编号（“定理9.1”“命题3.3–3.6”）从该主张所属发布的正文（页面语言）取出定理、命题、定义等的陈述，截到证明之前；位置只写章节（低能两稿）时取这些章节里的结果，标为“所在章节的结果”；位置带文字限定的段落（“§9.2 NIST 名义重放段”）不取。映射里的登记陈述折叠在原文之后，没有原文可取时照常显示。
- `src/lib/papers.ts`：标题、摘要（KaTeX 渲染）、章节标题与统计，取自最新一版正文。`citesOf` 从两种语言正文的参考文献段读出引用了哪些兄弟稿：按任一版 DOI 或主标题匹配（同系列稿在有 DOI 前按标题引用），论文页据此列出“它引用 / 引用它的”。`ORDERED` 是目录顺序（按主题，再按登记），翻页也按它。
- `src/data/reading-<lang>.json`：读者措辞层。映射受验收回执的哈希绑定，措辞是为机器核对写的，所以页面措辞放在这里而不改映射：`title` 换掉中英混杂或整句式的标题（用论文自己的中文术语），`passages` 以段首文字指定要引用的正文段落（位置只写段落描述、没有结果编号时），`cite` 补引结果编号，`statement` 仅在正文没有可引段落时给出整理后的陈述并标明“本站据登记陈述整理”。每条带所据登记原文的指纹，原文改动后构建告警并回退；登记原文始终折叠在“映射中的登记陈述”里。`bun scripts/reading.ts --lang zh|en` 列出过期条目，`--merge <file>` 并入新条目。
- `src/data/claims-<lang>.json`：登记原文不是页面语言时显示的译文（英文页译中文主张，中文页译以英文登记的主张），每条带所译原文的指纹；原文改动后构建告警并回退原文。`bun scripts/translations.ts --lang en|zh` 列出缺译与过期条目，`--merge <file>` 并入新译文。
- `src/components/CheckCommands.astro`：入口检查命令块，顶部独立放复制按钮，长命令在下方横向滚动；剪贴板不可用时退化为全选文本。
- `src/components/SiteStats.astro`：首页与目录共用统计，数字和单位作为完整项目，只在项目之间换行。
- `src/components/Home.astro`（`/`）：留空的开场画框（创世框占位，只有一句话）、一句介绍与全局统计、论文森林、全部论文的配图卡片架（最新在前，可横向滑动，每屏三张），以及到全部论文的入口。
- `src/components/Forest.astro`：首页的论文森林。朱红的 0 为根，每个主题一根枝，实心节点是已发布论文（链接），空心节点是自动计算的在写稿件（不显示未发表题名；`soon`须有已完成成稿依据）。结果触发席位用独立点线空环表示，不混入在写数；分枝显示已发表／已立题及另列的预留数。面板汇总按三列对齐，节点详情与图例叠放，切换时保留图例所需高度。入视口时生长一次；在写节点的虚线环慢转、核心反复凝聚，只在视口内运行；`prefers-reduced-motion` 下静止。
- `src/components/PaperIndex.astro`（`/papers/`）：按主题分区的全部论文；桌面左侧主题导航随滚动标出当前主题，窄屏为吸顶 chips；行尾是迷你主张打孔带。
- `src/components/CheckPage.astro`（`/check/`）：当前论文的入口检查命令与复现指南，旧发布折叠保存。
- 跨页过渡：支持的浏览器在页面间用 View Transitions，论文标题与配图从卡片或目录行移到论文页的位置（`vtTitle`、`vtFigure` 命名）；不支持的浏览器照常跳转，`prefers-reduced-motion` 下关闭。
- `figures/kit/`：取自 [anatomy](https://github.com/wheresryan22/anatomy)（MIT，commit `689dcf9`）的等轴测绘图核心。 本仓有两处改动：`pathOf` 丢弃画面上看不出的亚像素共线点（容差 0.04 px），`stepsFor` 让几像素大的小部件少分段；两者都只为减小片段体积和转视角时的重绘量。
- `figures/<name>/`：一张图一个目录。`model.mjs` 是真值模型，`check.mjs` 用论文定理校验它，`build.mjs --fragment` 输出到 `src/generated/` 供页面挂载；不带参数时输出独立页到 `out/` 用于截图与线端检查。 页面脚本不内联：`src/pages/figures/[name].js.ts` 把它压缩后输出为 `/figures/<name>.js`，`Figure.astro` 以内容哈希作 `?v=` 引用。

## 站点元信息

`astro.config.mjs` 设了 `site: https://h0mework.wiki` 并启用 `@astrojs/sitemap`（双语 hreflang，404 不入册）；`public/robots.txt` 指向 sitemap。每页带 canonical、双向 hreflang + x-default、OG/Twitter 卡片；论文页另从最新稿自动生成 Highwire Press `citation_*` 学术元标签、页面可见作者与 ORCID 署名、完整可见摘要、`ScholarlyArticle` JSON-LD 结构化数据，并在与摘要页同目录的 `/papers/<slug>/<slug>.pdf` 与 `/en/papers/<slug>/<slug>.pdf` 输出同域同子目录 PDF 直链（同时保留 `/papers/<slug>.pdf` 与 `/en/papers/<slug>.pdf` 兼容直链），由 `scripts/check-scholar-meta.ts` 在每次构建后校验 Google Scholar 收录规范。

`public/og/` 是分享预览图：有配图的论文用配图的机器图，其余页面用 `default.png`（打孔卡）。`bun run figures`（以及 `dev` / `build`）会自动运行 `bun scripts/og.mjs`：直接从 `PAPERS` 读取全部配图名，将 1200×630 静态页写入 `.og/`，比对每张 PNG 内嵌的 `og-sha256` 指纹块，仅在新增或配图/样式变更时调用无头 Chrome 自动重截 `public/og/<name>.png`（`.og/` 不入库）；页面元标签自动附带 `?v=<hash>` 破除社交平台缓存。

## 新增论文

1. 在 `PAPERS` 加一项：slug、`theme`、各版 `{ release, doi }`，系列稿可加 `series`。已立题稿发表后自动离开在写计数，不手工改`UPCOMING`；新增立题或新主题先更新`paper-plan.json`的分组与总数。
2. 新的发布目录在 `RELEASES` 登记（2026-10-17 起的发布在 `papers/<发布>/<日期>/` 放 Zenodo 上传的原字节文件，`manifest.json` 记 DOI 与每个文件的 SHA-256）；映射 schema 与已有发布不同时，在 `claims.ts` 的 `ADAPTERS` 加一个读取函数。
3. 分别以 `--lang en`、`--lang zh` 运行 `bun scripts/translations.ts`，为列出的条目补译文后 `--merge`。
4. 没有配图的论文在首页卡片里显示主张打孔卡；配图做好后在该项加 `figure`，运行 `bun run figures` 或 `bun run build` 即自动生成该论文的 og 预览图。

## 图

| 图 | 论文 | 主张 | 定理 |
| --- | --- | --- | --- |
| `source-tape` | source-process-core | core.C23 | 定理 3.9：整树程序的执行、计费与独立逆读 |
| `pairing-balance` | physics-common-source | phys.P4 | 定理 6.2 与例 6.6：经典—量子配对与暗时刻反例 |
| `current-witness` | low-energy-phenomenology | low1.L17 | §1 与定理 8.1–8.2：有限发展、双侧导数与 Kubo 积分读出同一电流 |
| `curvature-dome` | low-energy-loop-response | low2.Q4 | 定理 1.2 与 §§7–11：完整五项的响应曲率在全部方向上两负一正 |
| `ghost-register` | one-bit | ob.OB2 | 命题 2.3、引理 2.2 与定理 2.6：两枚布尔值，一个世界 |
| `whole-ledger-tower` | whole-ledger-accounting | wla.WA10 | 定理 6.2、命题 5.2 与结清类型 (44)：每拍一页的整账与债 A 的结清 |
| `exit-run` | generated-society | G4 | 定理 5.1、命题 5.2–5.3 与定理 1.3：退出容量与来源保留 |
| `clepsydra` | economic-constitution | R4 | 结果 4、5、7：贡献可以结清，控制必须续约 |
| `replay-bakery` | capital-formation | R8 | 定理 2、3、8：资本核心与公共功能重放 |
| `quan-heng` | enforceable-peace | PE2 | 命题 4 与式 (5)–(8)：责任回接的止战比例 |
