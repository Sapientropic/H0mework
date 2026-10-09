# L1–L28 公开证明材料需求

本稿本地正文、证明和图件接收 **L1–L28**。逐项合同见 [release-selection.json](release-selection.json)，已核机器事实见 [release-source-audit](validation/release-source-audit.md)。本窗口对 Homework／H0mework 保持只读；下列迁入和验收由获得 H0 写授权的材料窗口执行。

## 已确认的固定身份

| 范围 | Homework 来源 |
| --- | --- |
| L1–L17 | S=`30218c1aea92640eae09b1d9204a09b01a2d0e47` |
| L18–L23 | `e05558097256e86b537c019c8ca63cd449d6b2d2` |
| L24–L25 | `c62f3d25c42d4bf2b77ac009b49fc71cfd752f46` |
| L26–L28 | `71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9` |

原 S 选集经 base=`8e29b8e1e58f9846fdddedaaeab9fc8724cdcb87` 导出。base 的父提交就是 S，唯一变化为生命周期回归；本稿所核字节相同。公开继承绑定为 `ba591b43e13a59ac676919aa153569615f8d4cb2`／`H0mework.Papers.LowEnergyPhenomenology`，真实标签指向及原验收已核。

新增公开观察固定 **`51867c59042460646e57d5ead4c405cbca05c240`**，tree=`b05a81c3834762abef15a196944a77b1a60e0adb`。L18–L28 的实际关键生产口均无路径映射。当前没有覆盖全部28项的新聚合入口或验收提交。

## 迁入写集

以 selection 中各项的 production、direct consumer、original receipts 为根，恢复其原编译包的实际声明／资源闭包；同 SHA 的公开依赖直接复用。机器可读完整源 epoch 布局在 [压缩闭包索引](validation/release-public-closure.json.gz)：15,043 个 `(source_commit,path)` 节点含 13,825 个精确对应、1,212 个无映射及6个不同字节记录。

这个扫描来自真实递归 import／资源。它描述重新编译各 epoch 的完整布局；原认证最小已消费声明／依赖包另有身份。六个不同字节记录只对应两条广 import 路径，不能因此重开生化或标量科研。优先复用原已签依赖包，再补真实主口、消费者和必要资源。逐节点 imports、resources、SHA 与现有目标均可从索引读取。

新增根分三组：联合荷／static projection／complete static scalar／dressed character／electron unit／prepared ordinary；actual electron 静止腿、完整静态 reader／window、一次 Coulomb 与 ordinary；actual E carrier／action／clock、whole289 Newton、created moving connected及 N3 composite dressing。不得只导入最后一枚 theorem 或旧 S 聚合入口。

## 原生成源与模块归属

三份源不在该 Git 树中，但已由原清单固定且现有原件 SHA 相同，应通过 retained-source provider 接入：

| 原模块 | SHA-256 |
| --- | --- |
| `CanonicalPreparationSerializedConsumer` | `4a54a2c3355f37e6e5825a113bc22eee0f3ddec2a2b03ce8b3cc621e1110b275` |
| `SourcePhysicalEnergyChannels` | `953308bf3e7821ba355caddc8df4b9edc813a0a8b7395b66107ae990998c4c56` |
| `SourcePhysicalEnergyResidues` | `e43b738e1da273558fd24330793c4e6c8452db024145d712e75fd84e1016ed76` |

固定清单为71e的 `Verification/physics/low-energy-phenomenology/alpha-source/canonical_preparation_physical_energy_pole_charge_return_sources.json`；原路径、清单摘要及 provider 字段见审计 JSON 的 `receipt_bound_retained_sources`。其余 overlay 别名按原编译包/source inventory恢复；审计的16条 `overlay_alias_intake_requirements` 给出实际候选及归属要求，不能仅凭 basename 选模块。

Newton 的 `paidRadialGreen%` 在 `SourceChannelRadialSlope.lean:102` 按 `_private.SourceChannelFundamentalPotential.` 字符串找同一原 owner 的八个已付函数。迁移必须保留该归属，或显式记录并验证可逆前缀改写。现有 private-name 改写不改字符串字面量，不能自动承担这一步；原函数 type/value 与唯一 owner 条件须保留。

## 既有工具与实际执行

H0 本地已有 `.local/migration/tools/migrate2.py`，已核支持 `plan`、`sync`、`check` 及 retained-source providers。配置应合并全部既有 catalog entries 与新增 low1 entries，保留现有状态；单独用新 entries 覆盖旧 catalog 会缩减既有导出，迁移器也拒绝这种遗漏。

在 H0 根目录，以材料窗口实际生成的配置路径与源仓路径执行：

```sh
MIGRATE2_CATALOG=CATALOG MIGRATE2_MODULES=MODULES MIGRATE2_STATE=STATE MIGRATE2_PROVIDERS=PROVIDERS python3 .local/migration/tools/migrate2.py plan --source SOURCE --json
MIGRATE2_CATALOG=CATALOG MIGRATE2_MODULES=MODULES MIGRATE2_STATE=STATE MIGRATE2_PROVIDERS=PROVIDERS python3 .local/migration/tools/migrate2.py sync --source SOURCE --json
MIGRATE2_CATALOG=CATALOG MIGRATE2_MODULES=MODULES MIGRATE2_STATE=STATE MIGRATE2_PROVIDERS=PROVIDERS python3 .local/migration/tools/migrate2.py check --source SOURCE --json
```

Catalog entry 的实际字段为 `id,ref,roots,files,artifacts,aggregate,paper`；显式 Lean 文件字段为 `source,target,ref`；provider 行字段为 `ref,path,provider,sha256,origin`。这些命令是既有工具的真实 CLI，本窗口没有执行迁入。

创建独立的实际 low1 map／版本化聚合入口，保持首发两篇的 map 与验收。下列 `ACTUAL_PACKAGE_ID` 要换成材料窗口真正创建的 map package；不把它登记成已有模块：

```sh
python3 tools/first_release.py verify-map --map docs/low1-release-map.json --require-ready
python3 tools/first_release.py build --map docs/low1-release-map.json --output .local/low1-release-build --package ACTUAL_PACKAGE_ID
python3 tools/first_release.py trust --map docs/low1-release-map.json --output .local/low1-release-trust --package ACTUAL_PACKAGE_ID
python3 tools/source_view.py --verify-all
```

## 回填验收

材料窗口交回完整40位提交、实际聚合入口、逐项源／目标 SHA、import／资源闭包、原认证继承、实际 build／trust／必要科学检查的命令与回执。工具链已核四个来源均为 Lean `v4.33.0` 与 mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。原 Lean／完整矩阵认证与新公开执行分别登记。

收到真实验收后，更新本稿 selection 的 `public_evidence`，用薄入口刷新两语言代码可得性与 Zenodo Related works，再构建、渲染和重打材料包。当前正文与图件交付不删除任何新增成果；整体公开就绪由这个真实绑定决定。
