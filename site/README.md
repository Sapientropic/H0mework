# 可视化网站

把仓库里的论文、逐主张映射和 Lean 声明做成可浏览的站点。所有页面在构建时直接读取 `../papers` 与 `../docs/first-release-map.json`，不复制、不转写任何主张。

```bash
bun install
bun run build      # 先跑图的模型自检与构建，再出 dist/
```

本机 Homebrew node 断链时，脚本已用 `bun --bun` 运行 astro。

## 结构

- `src/lib/papers.ts`：论文标题、摘要（KaTeX 渲染）、PDF/DOI 链接、主张 → Lean 声明。DOI 以根 README 为准。
- `figures/kit/`：取自 [anatomy](https://github.com/wheresryan22/anatomy)（MIT，commit `689dcf9`）的等轴测绘图核心。
- `figures/<name>/`：一张图一个目录。`model.mjs` 是真值模型，`check.mjs` 用论文定理校验它，`build.mjs --fragment` 输出到 `src/generated/` 供页面挂载；不带参数时输出独立页到 `out/` 用于截图与线端检查。

## 图

| 图 | 论文 | 主张 | 定理 |
| --- | --- | --- | --- |
| `source-tape` | source-process-core | core.C23 | 定理 3.9：整树程序的执行、计费与独立逆读 |
