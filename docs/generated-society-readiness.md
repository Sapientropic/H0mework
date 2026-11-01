# 典范社会总定理：选集与验收

当前选集为 G0–G27 加 G2a，其中 G10–G12 只接收实际引用接口。原声明、完整类型、直接消费者、来源 epoch、公开 owner 和资源归[逐主张映射](generated-society-map.json)；执行命令和可引用声明归[复现](generated-society-reproduction.md)。

## 本地验收

完整五包构建、trust 和完整类型验收全部通过；[本次实际回执](../evidence/generated-society/acceptance/expanded-g0-g27/summary.json)绑定执行时的 map 快照、固定源闭包和配置 SHA，三次执行的输入均前后不变。最终 map 绑定真实类型与回执，并按原类型明确了 G20／G27 的严格进展预算及 G26 的依赖类型 HEq。

| 检查 | 实际结果 |
| --- | --- |
| Lean 完整构建 | 12463／12463 jobs；新增 542 个默认模块实际完成，旧模块重编译 0 |
| 五包 trust | 967 个声明根；完整 type/value、互递归和归纳元数据闭包；unsafe=0、partial=0 |
| 完整类型 | 967 项 Lean Expr DAG 独立重建并经 Lean 检查；全部保留 universe、量词和前提 |
| 选集身份 | 29 主张、428 映射项、3753 公开证明 owner、80 项资源、10 个选定 epoch |
| 公开与精确恢复 | 两种视图均通过；全部原认证资源的精确恢复使用按源 SHA 保存的原件 |
| 默认覆盖 | Lake 实际枚举 51085 个默认模块；全部模块恰有一个库 owner |
| 旧材料与入口 | 六篇固定材料身份不变；整账法 40 主张／13 包／5025 类型、一比特 23 control 类型及首发入口检查通过 |
| 工具 | 409 项完整工具测试通过；`make check-map` 通过 |

社会总口保留真实标准三公理 `propext`、`Classical.choice`、`Quot.sound`。原 strict／T1 认证按各自实际 epoch 保留，本次 H0 执行单独记账；历史失败与未恢复原件的状态保持。

| 独立入口 | 固定来源 | 实际闭包模块数（含入口） |
| --- | --- | --- |
| `GeneratedSocietyMInfinity` | e60 | 1078 |
| `GeneratedSocietyRegeneration` | AB | 1037 |
| `GeneratedSocietyInterfaces` | df | 1584 |
| `GeneratedSocietyProgress` | 1d7 | 1042 |
| `GeneratedSocietyEconomy` | df | 1042 |

五个入口均位于 `H0mework.Papers`。G13 保留历史 1d7 环境，并显式核对 df 当前实例；不同 epoch 的 Cycle／Payment 未被等同。G14–G27 及语法、路由／服务、关系再选择和记忆链的真实 producer、直接消费者与 whole 均进入完整构建。

## 来源与补稿

本次接入按 publish 固定提交 `a21f8b21a8c9bce2707f59f34e4cc6c731feabf9` 的 claims 及逐结果来源恢复；收稿上限仍为 Homework `df421ff600085cbc290a7ae946193961bed7c83b`，各历史证明保留实际 epoch。[独立来源审查](../evidence/generated-society/acceptance/expanded-g0-g27/source-review.json)核对了 245 项相关论文来源引用、完整 producer／consumer 和资源闭包；[最新补稿复核](../evidence/generated-society/acceptance/expanded-g0-g27/paper-review.json)确认社科读者改写未改变证明范围。并行未提交的 5.12 所用声明及实际 value 依赖另有明确记录。

独立附录 C13／PT15 的 receipt-window 接口保持原未闭合记录，未由本次 G13–G27 的验收转授认证。论文正文及其未提交文件保持由写作窗口负责。

## 缓存保全

[本次逐片报告](../evidence/generated-society/acceptance/expanded-g0-g27/cache-preservation.json)确认：相对接入前提交 `6edbad82`，全部 51981 个旧模块的源码、owner、递归 imports、有效强弱选项、39 个编译资源和默认分片归属保持；相对最初 main 的 49055 个模块身份也全部保持。新增 540 个证明 owner、两个入口及五份来源文档，1036 处来源 epoch 标签只追加不删减。

原有 62 个分片的完整记录、指纹和缓存键不变，仅新增 `s5-03`：542 模块，预计 0.77 runner 小时。计划为 11 阶段、63 片，每阶段最多 20 片；`plan --update-layout` 前、后及最终完整计划相同，固定布局只追加新模块位置，未执行 `--rebalance`。

| 完整选集身份 | 指纹 |
| --- | --- |
| 最初 main 基线 | `345402a3c337566e053d60f264f8dca9487d594f2adfaf1daec37ed5765ec9f2` |
| 本次扩展前 | `f0b3feec6ad427afa32bb28cbef5c06b762c9b56fad196a8bf5299b7603b6a82` |
| G13–G27 接入后 | `b1bf6b3260efaf715795900878404e87a7dc624ad888a9087297b84918144f39` |
| compatibility／CACHE_VERSION | `23f23031eec00a03d30ee31d`／`lean-parts-v1` |

原 61 片的 Linux 完整成功存档齐全，包括两组分卷的全部六个载荷；`s3-09` 保持其本地已验收身份，尚无远端成功存档。新旧选集的远端待验部分为 `s3-09` 与 `s5-03`，共 3468 个 owned 模块，预计 4.22 runner 小时。本机 Darwin 产物与 Linux runner 身份分别处理。

工具链、manifest、工作流、CI 算法及缓存版本保持。9 个固定依赖的 Git 身份和既有源码状态前后一致。Bell 与量子载体的程序、配置、资源及双引擎科学输入比较均相同，保留原成功回执，`full_replay=false`；旧 artifact 过期及历史 Makefile 导致的 verifier `miss` 保留原状态，详见[科学输入核对](../evidence/generated-society/acceptance/expanded-g0-g27/scientific-input-binding.json)。

## 远端 CI

[只读收尾核对](../evidence/generated-society/acceptance/expanded-g0-g27/remote-cache-preservation.json)确认远端 main 仍为 `48dc9ad13ffa79d9c2e9a93a8bc755a2388320bc`，proof-cache 的 76 项资产 metadata 前后相同；[最近成功运行 39771257871](https://github.com/Sapientropic/H0mework/actions/runs/39771257871)仍绑定历史来源 `8d6e6f09007e759bc07dea0d8c34d3379207bf61`。

本次新选集已通过本地完整验收，尚未运行远端 CI，也未取得新 seal。没有推送、远端合并、工作流触发、手工 seal／save／prune 或缓存删除。
