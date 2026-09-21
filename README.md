# H0mework

三篇论文的源码与复现准备仓：证明选集、固定版本依赖、冻结证据回执与可运行的独立检查。
当前仓库保持私有，正式公开另行确定。

研究开发在私有仓 Homework 进行；本仓按论文选集从固定源提交导出，历史独立、可独立构建，
后续论文按批次扩展。选集入口、模块对应与来源记录见[证据对应表](docs/evidence-map.md)。

| 论文 | 内容 | 代表入口 |
| --- | --- | --- |
| 过程核心（source-process-core） | 生命周期守恒、有限结算、完整历史、忠实实现、残差修订（C1–C13） | [`Lean/H0mework/Foundation/Responsibility/Lifecycle.lean`](Lean/H0mework/Foundation/Responsibility/Lifecycle.lean) |
| 同源物理（physics-common-source） | Spin×SU7 共同作用、九场解、量子/Fock 对应、全时动力学（P1–P20） | [`Lean/H0mework/Physics/RootRuntime/RecoveryConsumer.lean`](Lean/H0mework/Physics/RootRuntime/RecoveryConsumer.lean) |
| 低能唯象（low-energy-phenomenology） | 低能展开、传播、物质交换与全时间 Kubo 响应（L1–L17） | [`Lean/H0mework/Physics/LowEnergy/Consumer.lean`](Lean/H0mework/Physics/LowEnergy/Consumer.lean) |

## 来源与导出方式

- 证明源码固定取自 Homework 的两个提交：过程核心与物理主稿 `e60a8605`（H）、
  低能唯象 `30218c1a`（S）；H 是 S 的祖先。前两稿所需的2629个模块在H/S间逐字节一致，
  低能稿另外引入145个H中尚不存在的模块，因此统一自S导出；对应关系见[证据对应表](docs/evidence-map.md)。
- 导出是布局变换：只改写本地 `import` 模块地址，声明名、命名空间、前提、量词与证明正文
  保持原字节。`tools/export-map.json` 记录每个模块与证据文件的源／目标地址及 SHA256；
  `tools/source_view.py` 可从本仓逆向重建原路径源码并逐字节校验（见下）。

## 环境

- Lean `leanprover/lean4:v4.33.0`（由 `Lean/lean-toolchain` 固定，elan 自动安装）
- mathlib 输入 `v4.33.0`（实际修订 `db584cd6d46c92f209a44c0f1c829460d327499d`，
  由 `Lean/lake-manifest.json` 固定）
- 独立检查需要 Python 3 与 `sympy`、`mpmath`（`make check` 自动向 `.local/venv` 安装）

## 构建与复现

```bash
make bootstrap   # 获取固定版本 mathlib 预编译产物
make build       # 独立构建全部公开选集（--trust=0，warningAsError）
make check       # 重建原路径源码视图并运行冻结的独立证据检查
```

构建覆盖三篇论文入口的完整 import 闭包（含传递依赖，共 2777 个本地模块）。
定向复核某个直接消费者时，在 `Lean/` 目录运行如
`lake build H0mework.Physics.RootRuntime.RecoveryConsumer`。

`make check` 做两层验证：

1. `tools/source_view.py` 依据 `tools/export-map.json` 与冻结回执中的 `source_sha256`，
   把本仓导出文件逆向重建为原路径源码树（默认写入忽略目录 `.local/check-views/`），任何字节差异都会失败；
2. 在重建树上运行随论文冻结的独立检查脚本：
   - `scripts/physics/low-energy/check_readout.py`（L2 精确读出与特征多项式根隔离）
   - `scripts/physics/low-energy/stabilizer_check.py`（L2 稳定子有限检查，输出与冻结回执比对）
   - `scripts/physics/low-energy/occupied-response/spatial/global/independent_check.py`（L17 全时间控制）
   - `scripts/physics/low-energy/occupied-response/spatial/finite-coupling-derivative/independent_check.py`
     （L17 非交换 A01 有限块与真导数）

## 目录

```text
Lean/                     导出的 Lean 选集（H0mework.* 模块）与固定依赖配置
scripts/physics/          精确程序与独立检查脚本
evidence/physics/         冻结回执（结果、独立检查输出、原验证记录）
docs/source/physics/      机制推导与认证记录
docs/evidence-map.md      三稿主张 → 本仓模块/脚本的对应表
tools/export-map.json     源/目标地址与 SHA256 导出映射
tools/source_view.py      原路径源码重建与逐字节校验
```

## 范围说明

- 本仓以三篇论文的入口和消费者确定选集，纳入完整依赖闭包与配套证据；传递依赖包含尚未
  单独成文的其他结果。与本选集无依赖关系的成果留在私有档案，后续按论文扩展。
- `ResponsibilityLifecycleRegression` 回归消费者已经由 Homework 修复提交
  `8e29b8e1e`（S 的直接后继，纯战术层修复）重新纳入，见
  [证据表的来源说明](docs/evidence-map.md)；当前构建覆盖全部 2777 个导出模块。
- 迁移维护配置（选集状态、同步工具）留在本地忽略目录，公开构建与检查只依赖已跟踪文件。
- 许可：全仓 Apache-2.0，见 [LICENSE](LICENSE) 与 [NOTICE](NOTICE)。导出的 Lean 源码与其固定
  研究来源逐字节一致，不带逐文件许可头；仓库级许可约束全部内容（含脚本、回执与文档）。
