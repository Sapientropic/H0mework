# 复现指南

本指南描述仓库根目录的有效命令。各项命令的实现以 [`Makefile`](../Makefile) 中同名 target 为准；主张与版本关系见[证据对应表](evidence-map.md)。

## 环境与构建

系统需要 Git、make、elan/Lake 和含 `venv` 的 Python 3。CI 使用的 Python 版本见 [`ci.yml`](../.github/workflows/ci.yml) 的 `actions/setup-python` 配置。

Lean 工具链固定于 [`lean-toolchain`](../Lean/lean-toolchain)，mathlib 及其传递依赖的提交固定于 [`lake-manifest.json`](../Lean/lake-manifest.json)。Python 检查依赖 `sympy`、`mpmath`、`numpy`，由 `Makefile` 的 `.local/venv/bin/python` 规则安装；该规则没有固定 Python 包的精确版本。

```bash
make bootstrap
make build
```

`bootstrap` 获取 mathlib 的预编译缓存；`build` 执行 `Lean/` 下的 `lake build`。初次获取工具链、缓存与 Python 包需要网络。构建产物写入 `Lean/.lake/`，检查产物写入忽略目录 `.local/`。

默认构建与资源输入由 [`lakefile.toml`](../Lean/lakefile.toml) 的 `defaultTargets`、`lean_lib`、`input_file` 和 `needs` 配置确定。包级参数包含 `--trust=0`；主库及资源消费者启用 `warningAsError`。`H0meworkRelaxed` 保留固定源中会产生硬警告的模块，采用相同的包级参数并保留警告。

单独复核一个入口：

```bash
(cd Lean && lake build H0mework.Physics.RootRuntime.RecoveryConsumer)
```

完整构建需要为 `.lake` 产物留出磁盘空间。构建前可用 `df -h .` 查看可用空间，构建后用 `du -sh Lean/.lake/build Lean/.lake/packages` 查看实际占用。Lake 为每个模块写入的 `Lean/.lake/build/ir/*.setup.json` 列出全部传递依赖的产物路径，全量构建合计可达上百 GB；它只在模块开始编译时读取，编译完成后删除不会使构建失效，可用 `find Lean/.lake/build/ir -name '*.setup.json' -delete` 回收空间。

2026-09-30，提交 `bf78b3674ec5680c7baab77e70107d148c281c9d` 在 macOS 上完成完整默认选集构建：`make build` exit 0，25560 jobs，复用现有缓存，实际重编 6509 个模块，耗时 6 小时 52 分 34 秒。

## 独立检查

以下目标按顺序执行。它们共用 `.local/check-views/`，其中 `check` 会清空该目录。

| 命令 | 实际覆盖 |
| --- | --- |
| `make check` | L2 精确读出与根隔离、稳定子回执比对、L17 全时间控制及非交换有限块真导数 |
| `make check-map` | 模块固定源身份、工件目标哈希及公开回执 payload 校验 |
| `make check-5a` | T/V/X 三个时代的一阶 Cauchy、量子高斯截面、joint CCR/CAR 独立消费者及回执比对 |
| `make check-5a-k` | K15/K16/K17 原程序重放及冻结回执比对 |
| `make check-case2` | T 视图中的 Case 2 全量子 Python 审计消费者 |
| `make check-obs` | E/I 原路径视图重建及 `Gate.lean` 字节差异断言 |
| `make check-physics` | 同源物理附录 D.5 的有限矩阵与算术检查，要求覆盖和残差满足冻结回执 |
| `make check-all` | 上述全部独立检查 |

完整复核依次运行 `make bootstrap`、`make build`、`make check-all`；`check-all` 的依赖中不含 Lean 构建。

`check-obs` 重建两版材料并比较 `Gate.lean`。默认构建编译 `ObservationDynamicsE`、`ObservationDynamicsI` 入口及其依赖；冻结的 `Gate.lean` 审计与 `verify-e.py`、`verify-i.py` 不在该 target 中执行。Case 2 的原 `audit/verify_*.py` 还调用源仓的编译树和 lint 工具；本仓提供默认 Lean 编译与 `CASE2_AUDITS` 中列出的 Python 检查，执行范围分别以配置和脚本为准。

回执比对由 [`compare_evidence.py`](../tools/compare_evidence.py) 的 `normalize` 实现；省略字段完整定义于 `VOLATILE`，其中包括时间、主机路径与 `revision` 等元数据。固定来源和字节身份由导出映射及 `source_view.py` 校验。

已有虚拟环境缺少依赖时，可补装：

```bash
.local/venv/bin/python -m pip install sympy mpmath numpy
```

排查跨环境结果差异时，用 `.local/venv/bin/python -m pip freeze` 保存包版本，并保留新鲜输出与失败信息。`make clean` 清除检查视图。

## 原路径版本视图

[`source_view.py`](../tools/source_view.py) 的 `reconstruct` 默认生成可运行的公开原路径视图。固定源的精确视图、私有原件存档与两种身份的验证方式见[公开回执与原始来源](evidence-publication.md)。版本关系见[证据表](evidence-map.md#来源与地址变换)。

按冻结回执选择输入：

```bash
python3 tools/source_view.py --output .local/readout-view \
  --receipt evidence/physics/low-energy/results/exact-readout.json
.local/venv/bin/python scripts/physics/low-energy/check_readout.py \
  --root .local/readout-view \
  --receipt evidence/physics/low-energy/results/exact-readout.json
```

按时代选择整个已导出的源目录：

```bash
python3 tools/source_view.py --output .local/observation-e \
  --at E --path-prefix Verification/no-island/
```

`--at` 接受映射中的标签或唯一提交前缀。输出目录必须尚不存在，仓内只允许写入忽略的 `.local/`；重复运行时另选新目录。全部参数见 `python3 tools/source_view.py --help`。

## 固定失败版本

Y 来源的唯一性引理在固定依赖下编译失败，原字节保存于非默认库 `H0meworkPinned`。默认构建采用对应的 Y1 战术修复；错误位置、修复来源与消费者见[整账会计证据](evidence-map.md#whole-ledger-accountingy)。

在 `Lean/` 下执行 `lake build H0meworkPinned` 可复现这项历史失败。该命令的失败结果用于核对 Y 快照。

## CI 范围

[`ci.yml`](../.github/workflows/ci.yml) 定义两个 job：`evidence-checks` 执行 `make check`，`lean-build` 执行默认 Lean 构建：仓库私有期间只在手动触发（workflow_dispatch）时运行，公开后每次推送运行。其他独立检查通过上述 make targets 运行。云端工作流的执行结果见 [GitHub Actions](https://github.com/Sapientropic/H0mework/actions)。
