# 一比特材料与复现

[OB1–OB11 映射](one-bit-map.json)定位本篇使用的原声明、历史环境和证据。OB2 增补原 ghost 反例；其他证明复用整账法与首发核心／物理的准确已签包，详见[准备状态](one-bit-readiness.md)。

在仓库根目录运行读者入口：

```sh
make check-one-bit-entry
```

入口核对五个原包的完整源码／import 摘要、原具名审查根和选中资源，并从本仓公开模块精确恢复选定源码。它不读研究仓或私人缓存，不执行科学计算。整个 export-map 的检查仍可用 `make check-map`。

新增 control 的完整实际验收：

```sh
make bootstrap
make check-one-bit-full
```

该命令依次执行本篇入口、新 control 的最小 Lake 闭包构建、完整 metadata trust 和完整类型核验。原包的有效验收按同一源码范围复用；它不重新启动整账法或完整物理包。四个步骤共用新建的忽略目录，可显式指定：

```sh
make check-one-bit-full ONE_BIT_RUN=.local/one-bit-my-run
python3 tools/one_bit.py entry --require-ready --output .local/one-bit-my-ready
```

输出目录须未使用。工具链与依赖由 `Lean/lean-toolchain`、`Lean/lake-manifest.json` 固定；继承的 Lake 配置和原源码均保持。新 control 使用原有 `H0mework.Checks.+` 库，按 `--trust=0`、`warningAsError=true` 构建。完整类型复用[整账法的 Lean Expr DAG codec](whole-ledger-reproduction.md)，在 Lean 中由 JSON 重建并核对原类型；23 个声明逐项绑定类型工件索引与摘要。

原 ghost 源码和全部 31 个直接／递归依赖可独立恢复：

```sh
python3 tools/one_bit.py source --output .local/one-bit-original-view
```

原 source SHA 为 `59132da0687ab67b235ac4fdffb9fe585ed02c104787571ee5f1d0928f2aaf06`。[迁入身份](../evidence/one-bit/source-intake.json)记录完整闭包复用、import 迁移与精确逆验；[control 映射](../checks/one-bit-control-map.json)保存 17 个原声明及 6 个准入 producer 的完整类型和新回执。raw 值不等、合法投影相同与真实发生不同各由独立声明检查；非法 API 应用另保原编译反控。

`source` 从已注册 control 的实际 import 闭包选出全部原路径，委托既有 `source_view.reconstruct` 恢复，并逐件核对原 Y 字节摘要。单文件恢复仍可直接使用 `source_view.py --path … --at … --exact`。
