# 《舞蹈生成舞者》的社会线证明补集

定额、转轨、生产续行、冲突、供料隐私与第 91 号位的后续公开入口见[追加证明复现](society-book-supplement-reproduction.md)。

[九项来源映射](../checks/society-book-map.json)登记原提交、原路径、完整声明名、公开行号、源码和公开文件摘要，以及核验过的完整类型。每项的 `selection_roots` 列出整个模块族与直接消费者。递归导入由[导出映射](../tools/export-map.json)给出，固定根见[选集](../checks/society-book-selection.json)。

| 范围 | Homework 固定提交 | 公开入口 |
| --- | --- | --- |
| PF10 限域独立核验、PF11 实付撤权、续窗与异人交接 | `fb9e88a77a955af973dc46b1ba849e63cf8a58eb` | [SocietyBookScopedAudit](../Lean/H0mework/Papers/SocietyBookScopedAudit.lean) |
| 完整原来源自适应隐私、完整观察分布与独立乘积规律、公开时序及各支私域后继 | `ac87df0871be9c286bba31984070d2fa865c6781` | [SocietyBookSourcePrivacy](../Lean/H0mework/Papers/SocietyBookSourcePrivacy.lean)，另有同 epoch 的 `HaTimingOwnerSource` 读回程序 |
| 源生成风险报价、四分金额准入、原根实付与负值替代 | `7c228ac7fd77350d3fe761c24b887cbf2f6e5afc` | [SocietyBookRiskCompensation](../Lean/H0mework/Papers/SocietyBookRiskCompensation.lean) |
| 统一定额域、同根跨区段、共终及事前自适应紧界、成本偏序、各实付定额、捕获前退出需求与报价重读 | `7c228ac7fd77350d3fe761c24b887cbf2f6e5afc` | [SocietyBookQuantities](../Lean/H0mework/Papers/SocietyBookQuantities.lean) |
| 旧行动者再出现时的继承与同债后继 | `df421ff600085cbc290a7ae946193961bed7c83b` | `ReappearanceSuccessionRegression` 的 `target_reappears`、`target_succession`、`target_not_birth` 与 `reappearance_same_debt` |

固定来源采用四个独立截面。风险补偿与定额使用实际来源命名空间 `R7c228ac7`，其中源码、语义来源和递归导入均相同的依赖直接使用既有公开 owner。新增源保留原声明和证明，13 个模块的 `open private … from` 按实际 owner 可逆重写。原读回程序各自保留 `main`，在独立环境中构建。

风险补偿的 `Consumers.Prices` 证明两支均实际支付 4。报价 3、4、7、100 分别进入提供方受偿不足、足额补偿、盈余、付款方缺额的判例，负值替代由 `Outside.Consumers` 保留。

从仓库根目录执行以下命令。

```bash
make check-map
python3 tools/society_book.py entry
python3 tools/society_book.py source --output .local/society-book-public
python3 tools/society_book.py source --exact --output .local/society-book-exact
```

在固定 Lake 依赖可用时，使用以下命令验收十二个环境。复跑时为 `--output` 选择新目录。

```bash
python3 tools/society_book.py build --output .local/society-book-build
python3 tools/society_book.py trust --output .local/society-book-trust
python3 tools/society_book.py types --output .local/society-book-types
python3 tools/society_book.py scoped-kernel --output .local/society-book-scoped-kernel
```

`scoped-kernel` 使用[原空内核重放程序](../evidence/society-book/original/Rfb9e88a7/Lean/scripts/verification/public-scoped-audit-kernel.lean)，可逆地换用公开模块地址。它检查两路核验各自的依赖，并在空环境中重放原定理闭包。实际构建、信任检查与完整类型的公开回执由[来源映射](../checks/society-book-map.json)绑定。[CI 缓存保全记录](../evidence/society-book/acceptance/cache-preservation.json)分别登记旧分片的完整键、新分片和科学回执输入复核。
