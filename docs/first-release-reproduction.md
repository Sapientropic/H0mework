# 两篇首发证明与复现

过程核心与同源物理旗舰（CourtyCourt Case 0）的证明、程序和输入采用各自主张的固定版本。[首发映射](first-release-map.json)登记生产声明、直接消费者、资源地址和实际验证身份；[准备状态](first-release-readiness.md)登记本地交付结果与论文成品状态。

## 入口检查

需要 Git、make、Python 3（含 venv）。在仓库根目录运行：

```bash
make check-first-release-entry
```

`check-first-release-entry` 核对导出身份，并实际执行有限矩阵恒等式、完整八模 Fock／CAR、独立八维 Born 收缩以及 matched Γ／第二 Green 尾／扩散源的原精确控制。具体程序与输入由 [runtime 配置](../checks/first-release-runtime.json)指定。它可以独立运行，不需要先编译 Lean。

Python 环境使用 `.local/venv`，依赖为 NumPy、SymPy 和 mpmath；每次执行创建独立 `.local/first-release-runs/` 目录。工具保存源码身份、实际退出结果和新输出。已有冻结回执保留原执行身份。

## 完整检查

需要 elan／Lake。工具链及依赖由 [lean-toolchain](../Lean/lean-toolchain) 和 [lake-manifest.json](../Lean/lake-manifest.json)固定。首次构建先取回固定依赖缓存：

```bash
make bootstrap
```

```bash
make check-first-release-full
```

该目标依次构建全部证明包、执行选定声明的 trust0／werror 审查、检查导出映射，再运行全部公开独立检查。审查遍历声明类型、值及互递归／归纳元数据的完整依赖闭包，检查标准三公理以及 unsafe／partial。不同来源版本各自导入，避免同名声明的不同证明混入一个 Lean 环境。

`make build-first-release` 可单独构建映射中 `proof_packages` 的全部版本入口。构建并发由 [`build_environment`](../tools/first_release.py) 按 CPU 与内存选择：每 16 GiB 内存分配一槽，最多八槽，读取到的容器内存上限参与计算。生成证明行会占用数 GiB，预留内存供其他进程使用。显式设置 `LEAN_NUM_THREADS` 可覆盖默认值，例如 `LEAN_NUM_THREADS=6 make build-first-release`。并发设置不改变 Lean 源码或 Lake 构建摘要，已有有效产物继续复用。

声明审查也使用这一并发上限，每个证明包在独立 Lean 环境中运行，分别保存源码、范围、日志和结果。`LEAN_NUM_THREADS=1 make trust-first-release` 可改为串行审查。审查开始前用 Lake 检查现有构建，缺失或过时的产物必须先增量构建。

Bell 检查使用 [bell-inputs](../evidence/first-release/bell-inputs/sources.json)登记的三个官方 ZIP。仓内副本与原执行的字节身份一致，出处及许可见[来源材料](source-materials.md#第三方材料)。也可以指定保存同名官方文件的目录：

```bash
make check-first-release-bell FR_ARCHIVES=/path/to/bell-inputs
```

完整范围包含 ETH 的原有序试次与全部前缀、Munich 的完整配对记录／本地历史／后继时钟，以及 NIST 的源域、统计纤维和压缩树消费者。每个运行保留原输入、原判决和新执行的关系；具体范围由 runtime 配置指定。历史失败和适用条件随相应版本保留。

P26 的量子载体检查按 T／T3／V／X 固定来源运行原独立程序，重算 Gauss 约化、共同配置域、稳定子、量子截面与测度、Hilbert 载体、伴随及 Weyl／CCR／CAR 系数。原程序与输入由[量子配置](../checks/first-release-quantum.json)登记，完整检查包含这组程序，也可单独运行：

```bash
make check-first-release-quantum
```

新结果逐字段比对原冻结结果，只排除原顶层墙钟耗时 `elapsed_seconds`；物理时间、系数、判决及原范围字段均参与比较。

NIST 来源核对使用固定版本的历史校验程序及[明确保存的 Mathlib 源文件](../evidence/first-release/mathlib/sources.json)。它们在各自版本的任务视图中恢复，原 Git／导入闭包记录保留历史身份；当前证明由上述公开 Lean 入口验收。

## 定向检查与来源查询

已有构建可以单独运行 `make trust-first-release`；缺失或过时的构建使预检查失败。按包检查时，先查询包名与实际入口：

```bash
python3 - <<'PYCODE'
import json
with open('docs/first-release-map.json') as stream:
    for package in json.load(stream)['proof_packages']:
        print(package['id'], package['lean_target'])
PYCODE
python3 tools/first_release.py build --package source-process-core-ae --output .local/my-first-release-build
python3 tools/first_release.py trust --package source-process-core-ae --output .local/my-first-release-trust
```

输出目录必须是新的 `.local` 子目录。完整的构建与审查回执为其 `result.json`；独立程序的回执为 `report.json`，子目录保存各消费者的新输出与日志。

[export-map](../tools/export-map.json) 保存所有模块和工件的原／公开摘要、变换与来源版本。`source_origin` 指定必要的正式来源补齐或冻结生成源；依赖仍按对应的证明时代编译。公开原路径视图与 JSON 路径变换见[来源视图](reproduction.md#原路径版本视图)和[字节合同](evidence-publication.md)。

## 旧版入口

原八稿、旧标签和历史 R2 快照继续保留。[旧版复现指南](reproduction.md)给出各自入口；[证据表](evidence-map.md)保留原命题编号的对应。首发修订采用本页及首发映射登记的版本。
