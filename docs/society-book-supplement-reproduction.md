# 《舞蹈生成舞者》追加证明与第 91 号位证据

本选集以著作台账 `5c32c2a` 盘点的 29 个原文件为根，纳入直接消费者、完整递归导入和原验证资源。每个模块按其实际依赖复用公开 owner。[固定选集](../checks/society-book-supplement-selection.json) · [逐项来源与类型](../checks/society-book-supplement-map.json) · [缓存保全](../evidence/society-book-supplement/acceptance/cache-preservation.json)

| 采用范围 | Homework 来源 | 公开入口 |
| --- | --- | --- |
| 到期结算、滚动准备金、逐人工时恢复、安全任期及提前交接 | `5e4033a644` | [SocietyBookExactQuantities](../Lean/H0mework/Papers/SocietyBookExactQuantities.lean) |
| 原账开立、原槽换货、桥储、实付交接与联合补料 | `3b3d24a43b`，交接闭合于 `db2106944d` | [SocietyBookAccountedTransition](../Lean/H0mework/Papers/SocietyBookAccountedTransition.lean) |
| 原钟 117 后废料再生、原交付槽恢复与 126–150 无损续行 | `cb21139265`，再生闭合于 `66c09668dd` | [SocietyBookProductiveContinuation](../Lean/H0mework/Papers/SocietyBookProductiveContinuation.lean) |
| 战争临界、M11 防卫、原账追偿、平民止战及应急期限 | `f1d585505c` | [SocietyBookConflict](../Lean/H0mework/Papers/SocietyBookConflict.lean) |
| 38–40 整批供料组合隐私与实际供料者读回 | `7e013eddb9`、`ffa160b338` | [SocietyBookDonorPrivacy](../Lean/H0mework/Papers/SocietyBookDonorPrivacy.lean) · [PublicDonorLiveOwnerSource](../Lean/H0mework/Versions/Rffa160b3/ReleaseMaterials/Scripts/Verification/PublicDonorLiveOwnerSource.lean) |
| 跨域行动者生成的原 G8 整体回归 | `f9493be380` | [SocietyBookCrossDomainG8](../Lean/H0mework/Papers/SocietyBookCrossDomainG8.lean) |

第 91 号位保存 `06ca9cbeee` 的原签收及其绑定的九份原始回执。50 个安装程序的原字节与执行截面 `48baefa97d` 的配置摘要相符。离线读回重新消费四份保留日志，产出的独立回执与原件逐字节相同。控制夹具单独记账。[原签收](../evidence/society-book-supplement/original/R06ca9cbe/Verification/public-audit/regeneration/productive/supply-source-view.json) · [原始回执目录](../evidence/society-book-supplement/original/R06ca9cbe/Verification/public-audit/regeneration/productive/supply91-original/) · [读回与控制回执](../evidence/society-book-supplement/acceptance/supply-91.json)

从仓库根目录运行以下命令。构建沿用固定工具链、manifest 和可用的 Lake 产物。每次执行选用新的输出目录。

```bash
make check-map
python3 tools/society_book.py --supplement entry
python3 tools/society_book.py --supplement source --output .local/book-supplement-public
python3 tools/society_book.py --supplement build --output .local/book-supplement-build
python3 tools/society_book.py --supplement trust --output .local/book-supplement-trust
python3 tools/society_book.py --supplement types --output .local/book-supplement-types
```

原字节恢复使用 `source --exact --private-originals <原件目录>`。路径出版规则作用于明确登记的运行地址。私有原件以映射里的原 SHA-256 为文件名，提取方式见[证据出版](evidence-publication.md#两种视图)。

构建适配为 `Forecast.Use` 补入 `Production.material` 的原定义模块，在 `Consumers.Actual.Path` 注释已公开的 `drain_preserves_control` 的旧私有打开命令。两处都保留原声明和证明体。原路径公开视图保留适配，精确视图逐字节恢复原文件。

供料隐私闭包中的生产调度使用已有的增量轨迹执行内核检查。[证明适配](proof-build-adaptations.md#生产调度的增量内核重放) · [本机验收与分片缓存](../evidence/society-book-supplement/acceptance/dispatch-build-optimization.json)

在恢复的公开源视图中，使用装有 `cryptography` 的 Python 运行第 91 号位的本地控制夹具。

```bash
cd .local/book-supplement-public/06ca9cbeee5f3e4ff9f4ab17ff4ef51501ecb093
python3 Lean/scripts/verification/public-supply-disposition-check.py
```

原始读回程序 `public-supply-live-check.py` 的离线运行使用历史四机日志和原部署输入。签名处分、成功回执及本地验收在映射中各有固定身份。

生产续行与供料者隐私的原 Lean 检查器分别验收。[读回程序回执](../evidence/society-book-supplement/acceptance/standalone-readers.json)登记用于复验的公开导入地址、原文件摘要和实际空内核重放结果。
