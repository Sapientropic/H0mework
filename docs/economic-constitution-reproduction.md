# 可能性的经济宪法：证明材料复现

[逐主张映射](economic-constitution-map.json)保存 ECN1–ECN8 实际采用的原声明、来源、公开 owner、生产与消费者；[选集](../checks/economic-constitution-selection.json)决定完整 import／资源闭包。[验收状态](economic-constitution-readiness.md)分别记录原科学认证与本轮 H0 执行。

本轮十六包构建、trust 与 3313 项完整类型已全部本地通过，执行前后输入稳定；`entry --require-ready` 已核对实际回执。[验收总回执](../evidence/economic-constitution/acceptance/initial-intake/summary.json)及[公开登记](../evidence/economic-constitution/acceptance/initial-intake/publication.json)保存执行映射、完整日志与哈希。

## 固定来源与独立环境

| 来源提交 | 本篇采用范围 | 生产入口 `H0mework.Papers.*` |
| --- | --- | --- |
| `e60a86058abcb74b7f2225f2383c182be8343785` | M∞、实际退出、通路与共同清算的引用接口 | `EconomicConstitutionE60` |
| `df421ff600085cbc290a7ae946193961bed7c83b` | 社会实际经济链、资本、公共生产及实际采用的认证接口 | `EconomicConstitutionSourceDF` |
| `1d7db207f618738c642d0f14635949b8b21a9e19` | 原 Cycle／Payment 的严格已付进展 | `EconomicConstitutionPaidProgress` |
| `6c24593364cd7763e3cdccf8f3654996a6dc8b5f` | 公共功能 current-frame、原六项合同、任意 start/count 续行与完整净成本 | `EconomicConstitutionPublicFunction` |
| `59df7e39d81e8698f3cf8507e64b93829bb1cac3` | 独立公共规划、初始切口比较、源生预算、双发票及逐事件实付 | `EconomicConstitutionPlanning` |

本选集列出 330 个原路径根，采用 3313 个独立声明，分为上述五包与十一份原消费者程序的独立包。原 311 根完整保留，终稿新增的显式采用与消费者均已在原五主包的实际闭包，不增加 owner 或改写生产入口。十一程序的 201 个匿名例包括公共功能原 75 项合同及 17 项续行、规划 109 项合同／反控；每份程序直接以其实际公开模块作为入口，避免把各自的辅助定义合入同一环境。公共功能主包另显式纳入原终验的 40 份支持／regression 源及其 755 个具名声明。完整包名和模块路径由映射的 `proof_packages` 给出。

历史 1d 与 df 的 Cycle／Payment 分别保持来源。公共功能 6c 与独立规划 59df 也各自保留实际发生、费用和后继。公共认证采用本篇引用接口；来源补充的固定 Git、原认证绑定及依赖身份均在 export-map 的对应 source record／alias 中保存。

DF 认证链的辅助 `Trace.Challenge` 显式采用原 6c 的完整 `scopeBoundary` carrier 与第六分支。原 DF／E0 源和首次 H0 失败原件独立保留；恢复时按记录取实际辅助源，不能把收稿上限读成所有依赖体都与 DF 原字节相同。

ECN 的八项制度原则具有自己的规范论证。形式材料兑现各自明确的量词和原场景；专用货币的 carrier、mint／spend／noReplay、试点及新增限域审计交接继续按独立实现合同登记。

## 公开检查与完整验收

在仓库根运行，需要 Git、Python 3、make 和 elan。沿用 `Lean/lean-toolchain` 的 Lean 4.33.0 与 manifest 固定的 mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。已有缓存直接复用；首次缺少固定依赖缓存时才执行 `make bootstrap`。

每次选择新的 `.local` 输出目录：

```sh
make check-map
python3 tools/edition_release.py --edition economic-constitution verify-map
python3 tools/economic_constitution.py evidence --output .local/economic-evidence
python3 tools/economic_constitution.py entry --output .local/economic-entry
python3 tools/economic_constitution.py source --output .local/economic-public-source

python3 tools/edition_release.py --edition economic-constitution build --output .local/economic-build
python3 tools/edition_release.py --edition economic-constitution trust --output .local/economic-trust
python3 tools/economic_constitution.py types --output .local/economic-types
python3 tools/economic_constitution.py entry --require-ready --output .local/economic-readiness
```

默认 `build`／`trust` 覆盖全部十六包。`trust` 先检查 Lake freshness，再核所选声明的完整 type/value、互递归、归纳及 recursor 元数据；`types` 独立重建完整 Lean Expr DAG 并检查类型等价。本轮实际结果仅依赖 `propext`、`Classical.choice`、`Quot.sound`，unsafe=0、partial=0；[构建](../evidence/economic-constitution/acceptance/initial-intake/build/result.json.gz)、[trust](../evidence/economic-constitution/acceptance/initial-intake/trust/result.json.gz)和[完整类型](../evidence/economic-constitution/acceptance/initial-intake/types/result.json.gz)分别留有真实回执。

十一原程序的 201 个匿名例用可逆名称进入这些检查，公开名只保一层 `H0mework`。原 recursive 第 17 例和 reentry 第 11 例为类值观察，显式登记 `@[instance_reducible]`；该属性与命名均不改变原类型和证明／值字节，exact 视图逆回原 SHA。mutation 中的 `True`／`fail_if_success` 保持原编译反控。[早期观察名失败](../evidence/economic-constitution/acceptance/initial-intake/attempt-observation-names/build-result.json.gz)保留原状态，最终通过另有完整回执。

`--package` 可用于定向检查，例如 `--package economic-constitution-public-function`；单包结果不能替代完整十六包验收。`entry --require-ready` 核对已归档的真实 build／trust／types 回执；自行重跑不会自动覆盖固定回执。

## 原科学证据与两种视图

`evidence` 只读核对固定 6c 终验清单 SHA `e78e39e5c01671fca2dde2acf2f2910b9db9ee411c3d832859a544c4f567d10f` 的 1200 份源码及 58 份原证据，[本轮身份核对已通过](../evidence/economic-constitution/acceptance/initial-intake/original-evidence.json)。1200 份中，1198 份进入 Lean 闭包，两份原运行程序作为 artifact 保留；包括原 12-case actual 程序。本命令保存原 current-frame 判决、七路原两轮结果及未采用 execution-frame 的处置，`actual_programs_executed=false`、`scientific_recalculation=false`。

默认 `source` 按 epoch 恢复可构建的公开原路径视图。匿名消费者名称、明确构建适配与路径清理按 source_view 的既有规则保存。精确恢复另逆转这些变换，核对原 SHA；经过隐私清理的原回执需要按源 SHA 命名的原件目录：

```sh
python3 tools/economic_constitution.py source --exact \
  --private-originals "$ECONOMIC_ORIGINALS" \
  --output .local/economic-exact-source
```

原件及缺失时的处理见[公开证据规则](evidence-publication.md#两种视图)。后收托管提交只承担保全身份，不改变原执行的 epoch、成功／失败状态或验收结论。

本轮[公开视图恢复](../evidence/economic-constitution/acceptance/initial-intake/source-views/economic-public.json)及[原字节逆恢复](../evidence/economic-constitution/acceptance/initial-intake/source-views/economic-exact.json)均已通过。

## 默认覆盖与缓存

```sh
python3 tools/ci_plan.py coverage
python3 tools/ci_plan.py plan --plan .local/economic-ci-plan.json
```

实际库 owner 由 lakefile 唯一确定，新增模块和入口进入默认构建。工具链、manifest、工作流及 `CACHE_VERSION=lean-parts-v1` 保持；固定布局给新模块追加位置，旧分片位置保持。[当前缓存报告](../evidence/economic-constitution/acceptance/initial-intake/cache/current-report.json)是唯一最终入口，列出逐片指纹、完整键与复用依据。52523 个旧模块身份及 63 个旧分片完整记录保持；新增 2106 个 owner、7 个论文入口与 306 份资源／原回执，真实默认覆盖为 53198 个模块、65 片、11 阶段。

复用分三层：Lean 产物按平台／工具链／compatibility／分片完整身份取回并经 Lake freshness 判断；mathlib 等九个固定依赖 head 保持，沿用既有缓存；Bell 与量子载体按原程序、配置及输入身份处理原 artifact，保留原命中与未命中记录，`full_replay=false`。Darwin 产物与 Linux runner 存档分别记账。本轮有限选集已取得自己的本地完整验收，旧 seal 保留原指纹，未重跑科学任务。

本轮本地验收和远端 CI 分别报告。推送、触发远端工作流和远端缓存写入不属于这些复现命令。
