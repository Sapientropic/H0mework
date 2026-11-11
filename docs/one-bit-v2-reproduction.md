# One Bit 第二版证明增量

[固定选集](../checks/one-bit-v2-selection.json)和[逐主张映射](one-bit-v2-map.json)登记 OB2、OB12 和 OB13 的新材料。OB1–OB11 已公开的证明和原 ghost 对照沿用[首版复现入口](one-bit-reproduction.md)。

- **OB2** 固定在 `b81a4438`。原单根准入防火墙编译 21 个直接导入和 8 条精确诊断断言，同时核对根表示与询问同一性的正向消费者。Homework 提交 `089a1727` 校正 `installedAmbient_factorizes` 的安装面投影类型，`26b91feb` 对 `parentComponentInstallation` 的分类结果分支核对。H0 的 `existingComponentInstallation` 展开两层投影，再按父投影分类核对原 `outcome_heq`。固定选集登记三处适配的原件。
- **OB12** 固定在 `df421ff6`。已付语法树的恢复进入 `cofinal_paid_method_faces` 与 `finite_paid_method_faces`。上下文预测的四个依赖采用 CP483 原运行守护的源码字节。
- **OB13** 固定在 `df421ff6`。整词逐原语回放、原物理读回和同次微分、出生库存、后继进入 `actual_relation_cochain_method`。

CP483、CP485 各保留原认证、裁决和同发生链，完整来源与摘要见映射。公开回执沿用[运行路径规范化](evidence-publication.md)。本地构建、公理依赖与完整声明类型的回执也由映射索引。

从仓库根目录运行，每次复验使用新的输出目录。Lake 按固定工具链、manifest 和现有产物的实际新旧关系构建。

```sh
make check-map
python3 tools/one_bit_v2.py entry
python3 tools/one_bit_v2.py source --output .local/one-bit-v2-public
python3 tools/one_bit_v2.py build --output .local/one-bit-v2-build
python3 tools/one_bit_v2.py trust --output .local/one-bit-v2-trust
python3 tools/one_bit_v2.py types --output .local/one-bit-v2-types
```

`build`、`trust` 和 `types` 可重复指定 `--package`，包名为 `firewall`、`paid-method`、`relation-cochain`。精确恢复原回执时，将私有原件按原 SHA-256 命名后提供归档目录。

```sh
python3 tools/one_bit_v2.py source --exact \
  --private-originals "$ORIGINAL_RECEIPT_ARCHIVE" --output .local/one-bit-v2-exact
```

[缓存保全报告](../evidence/one-bit-v2/acceptance/cache-preservation.json)登记 Linux 的旧分片键、现有存档及新增分片的构建量。
