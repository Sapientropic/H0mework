# 整账法证明与复现

本选集对应 WA1–WA40，原生产证明、直接消费者和历史来源由 [逐项映射](whole-ledger-map.json)登记；实际执行与源码绑定由 [准备状态](whole-ledger-readiness.md)签收。

从完整责任账，经原请求 AST、有费执行、同债付款和完成回答，走到同一次 whole write、canonical next 与后继消费者。WA38–WA40 的原 Factory、initial、cfg、全部实际共尾 ordinal、环境、作用词及观察位置保留在原构造的类型中。

## 入口核查

需要 Git、make、Python 3（含 `venv`）。在仓库根目录运行：

```sh
make check-whole-ledger-entry
```

该命令运行既有 `check-map`，核对 WA1–WA40 的公开对应、各包的完整 import 闭包、可逆原路径源码与冻结资源。检查直接读取本仓文件，复原同一选定源码的完整生产体与依赖，不读取研究仓或私人缓存，也不运行科学求解。

## 完整 kernel 核查

证明工具链由 [`Lean/lean-toolchain`](../Lean/lean-toolchain)、[`Lean/lake-manifest.json`](../Lean/lake-manifest.json)固定：Lean 4.33.0 与 Mathlib v4.33.0。首次准备固定依赖：

```sh
make bootstrap
make check-whole-ledger-full
```

完整核查依次执行入口恢复、全部已注册历史包的 Lake 构建、声明审查和完整类型提取。构建沿用 `--trust=0` 与 `warningAsError=true`；审查遍历完整类型、证明值、互递归声明、归纳类型、构造子及递归器元数据，公理集限定为 `propext`、`Classical.choice`、`Quot.sound`，检查 unsafe／partial 依赖。原控制文件中的匿名例子由其原文件的 kernel 构建验收。

每个 epoch 使用独立 `H0mework.Papers.WholeLedgerAccountingR…` 环境，全部准确入口和执行参数见 map 的 `proof_packages`。分包复核可用：

```sh
python3 tools/edition_release.py --edition whole-ledger build \
  --package whole-ledger-ba7e274b --output .local/whole-ledger-my-run/build
python3 tools/edition_release.py --edition whole-ledger trust \
  --package whole-ledger-ba7e274b --output .local/whole-ledger-my-run/trust
python3 tools/whole_ledger.py types \
  --package whole-ledger-ba7e274b --output .local/whole-ledger-my-run/types
```

输出目录必须为未使用的 `.local/` 子目录；复核一次后换一个目录名。完整命令的四个步骤共用同一个运行目录，显式 `WLA_RUN` 覆盖也会传给所有步骤。构建回执明确登记已有工作区缓存与实际源码闭包，不将其写成 clean clone。完整依赖来自公开选集与固定第三方依赖，新声明的完整 elaborated 类型另由 `types` 入口生成。

完整类型使用 `lean-expr-dag@1`：共享子项按拓扑顺序登记，完整保存常量名、数字／卫生名字、宇宙层级、显式／隐式 binder、应用、let、literal、projection 与类型中的证明项。每个声明在 Lean 中从公开 JSON 独立重建，并核对与原 kernel 类型定义等价；非逻辑 `mdata` 注释按 Lean 的表达式序列化语义剥离。该表示避免将同一依赖项重复展开成巨大文本；逐声明的类型摘要与工件索引由 map 定位，完整 codec 在 `tools/whole_ledger.py` 中。

## 原件、公开视图与适配

[`source_view.py`](../tools/source_view.py)按 `export-map` 反转 import、资源地址、明确登记的私有 owner 和构建适配；具体规则见 [公开字节身份](evidence-publication.md)与[构建适配](proof-build-adaptations.md)。完整相同的原源码及递归依赖共享已签证明体，每个历史地址保自己的来源身份。

原 Y 与 Y1 的意义保持：实例 8.7 使用 Y1 的实际修复链，其余原 Y 材料保持原 epoch。receiver 费用、action／query 环境及有限 Incoming 的既有源补充按实际定义或证明责任登记；恢复有效补充和恢复失败原件各有自己的 SHA。

CP132–135 的固定 ledger 保留原认证状态与原回执 SHA；原 verdict 的可访问性和本选集的新执行分列。其他原认证束的摘要、声明类型及 closure 由逐项映射定位。公开回执的运行路径变换与无损压缩保留原结果、状态和源摘要。

节点语法费用、数学完成、同债付款与领域终止各消费其原对象。数值 effect 为零仍保留实际语法付款；新责任的预算由自己的发生生成。
