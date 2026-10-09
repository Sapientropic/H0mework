# Case 2 原创图示

`make_figures.py` 生成三张可编辑 SVG，并以本机 headless Chrome 打印为单页 PDF、再由 Poppler 按 2 倍像素栅格化出 PNG 预览（与论文 PDF 同一渲染器）。无需网络图片或外部字体文件。

在 publish 根目录运行：

```sh
python3 papers/low-energy-loop-response/figures/make_figures.py
python3 papers/low-energy-loop-response/figures/make_figures.py --lang en
python3 papers/low-energy-loop-response/figures/make_full_return.py
```

默认中文；`--lang en` 生成 `fig01-two-branches-en`、`fig02-lens-flux-en`、`fig03-inertia-en` 的 SVG／PNG，只切换标签与英文优先字体栈。两种语言共用同一绘图主体，几何、区间、mixed 界与字号一致。`--svg-only` 可只重建 SVG，不启动栅格渲染。

`make_full_return.py` 只生成第四图，默认同时写 `fig04-full-return` 与 `fig04-full-return-en` 的 SVG／PNG，支持 `--lang zh/en` 和 `--svg-only`。它复用 `house_style.py`、`svg_text.py` 与本机字体度量（Python 依赖 `fontTools`），不会触及原三图。

视觉语言遵循 `shared/figure-style/`：色值与字体栈取自 `house_style.py`，图内不放大标题（标题在正文图注），画布宽 1000 像素、最小字号 17 像素（W/60），朱红只标一处：图1为完整五项，图2为两类通量所在的交集球面及其结论，图3为零线。

图1 `fig01-two-branches`：同一原作用的有序词／准备支路和原场空间响应支路；完整五项真实依赖。图2 `fig02-lens-flux`：两球交集、尖窗一次项、body 与两类 flux；仿射原字段的真实边界反控制。图3 `fig03-inertia`：raw／connected 的最终对角区间、每行两个 mixed 界后的包围以及零分离。

图4 `fig04-full-return`：原作用密度的 Fourier Hessian 认回 H₂₈₉；Q5 的五原点方向及45＋21＋32维坐标补空间生成完整 Schur、实际清分母原场恢复；Q6 的完整有序五因子分别进入原实场半轴读口与实际创建／同背景差读口，生产完整289×289响应和母 Euler 窗口导数，最后由同一原约束 Green 回写全场。朱红聚焦实际完整响应。

图4按正文第12、13节的对象命名。`B_raw / N_f` 分别是两支路的原读口；它们在零幅度相同，接触导数分别保持。原准备半轴的 `Re λ > 0`、实际非线性来源的 `0 ≤ T < τ(d,k,P,a)` 与实际线性化半轴的 `Re λ − γ(P) > 0` 三个条件分列。γ 是原信号源时钟增长率；Bλ 是原初末共源。箭头表示构造与消费依赖，五因子行从左到右先相乘再评价。

图4的中英 SVG／PNG 均已实际生成并逐张目视检查；两种语言共用全部框形、连线与因子顺序，主标签不低于17像素。新入口执行前后，原三图保原字节。

所有坐标、区间和公式来自本稿固定来源；图2几何尺寸为示意，未将放大示意当作实际 B。图3横轴单位为 10⁻²⁰（raw 深蓝、connected 金色），宽带不是额外独立观测，而是同一行的 Gershgorin 包围。mean 的第二轴跨零，正文单独记录。

渲染和阅读检查见 ../revision-audit.md 及 ../validation/。中英三图均已实际查看；英文标签检查包括真实字体的字宽与画布／框界。中文 SVG 已按默认入口重建并逐字节对照原图；原中文 PNG 保留。图2的原版标签间距经过视觉审校后修订。

图文对应：图1的两条量子源腿标“固定窗”，场传播两腿与读出接触标“移动交集”；该标注对应正文的零输出动量、两窗等半径设置。图2深色阴影始终表示保留的交集，图注将一次损失定位到入射球中交集外被裁去的球冠。图3的数值、坐标和包围宽度不变，mixed 标签译为“混合”。
