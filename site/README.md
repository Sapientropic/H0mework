# 可视化网站

把仓库里的论文、逐主张映射和 Lean 声明做成可浏览的站点。所有页面在构建时直接读取 `../papers`、`../docs/*-map.json` 与映射指向的 Lean 文件，不复制、不转写任何主张。

```bash
bun install
bun run build      # 先跑图的模型自检与构建，再出 dist/
```

本机 Homebrew node 断链时，脚本已用 `bun --bun` 运行 astro。

## 结构

- `src/lib/registry.ts`：发布了什么。`PAPERS` 是论文与各版 DOI，`RELEASES` 说明每次发布的日期、映射、正文（目录或可编辑 ZIP）、PDF 与入口检查命令。
- `src/lib/claims.ts`：把各发布映射的不同 schema 读成同一种主张行。第二版映射按发布选集的证明包成行；一行若混有已通过与待完成的主张，页面逐条列出。
- `src/lib/papers.ts`：标题、摘要（KaTeX 渲染）、章节标题与统计，取自最新一版正文。
- `src/data/claims-en.json`：英文页的主张译文，每条带所译中文的指纹；中文改动后构建告警并回退中文。`bun scripts/claims-en.ts` 列出缺译与过期条目，`--merge <file>` 并入新译文。
- `figures/kit/`：取自 [anatomy](https://github.com/wheresryan22/anatomy)（MIT，commit `689dcf9`）的等轴测绘图核心。
- `figures/<name>/`：一张图一个目录。`model.mjs` 是真值模型，`check.mjs` 用论文定理校验它，`build.mjs --fragment` 输出到 `src/generated/` 供页面挂载；不带参数时输出独立页到 `out/` 用于截图与线端检查。

## 新增论文

1. 在 `PAPERS` 加一项：slug、各版 `{ release, doi }`，系列稿可加 `series`。
2. 新的发布目录在 `RELEASES` 登记；映射 schema 与已有发布不同时，在 `claims.ts` 的 `ADAPTERS` 加一个读取函数。
3. 运行 `bun scripts/claims-en.ts`，为列出的条目补英文后 `--merge`。
4. 没有配图的论文在首页显示主张打孔卡；配图做好后在该项加 `figure`。

## 图

| 图 | 论文 | 主张 | 定理 |
| --- | --- | --- | --- |
| `source-tape` | source-process-core | core.C23 | 定理 3.9：整树程序的执行、计费与独立逆读 |
| `pairing-balance` | physics-common-source | phys.P4 | 定理 6.2 与例 6.6：经典—量子配对与暗时刻反例 |
