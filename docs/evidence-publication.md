# 公开回执与原始来源

公开回执保留计算数据、结果和失败记录，将运行路径改为相对地址。原件由私有研究仓的固定 Git 版本保存，导出映射同时记录原件和公开副本的身份。

## 字节身份

[`export-map.json`](../tools/export-map.json) 的工件记录使用以下字段：

| 字段 | 含义 |
| --- | --- |
| `source_sha256` | 固定来源提交中的原始字节摘要 |
| `target_sha256` | 本仓文件的完整字节摘要 |
| `publication.kind` | 声明的公开变换；当前为 `relative-runtime-paths/v1` |
| `publication.payload_sha256` | 路径规范化后的原始序列化字节摘要；保留数值的原始写法 |
| `publication.digest_rewrites` | 公开回执读取另一个公开回执时，对绑定摘要的明确更新 |

没有 `publication` 的工件保持原字节，两个文件摘要相同。带 `publication` 的工件使用派生字节；其原始提交和 `source_sha256` 保留。

[`publication.py`](../tools/publication.py) 的 `normalize_paths` 只改运行根目录、命令路径及 `source_inputs`／`input_sha256` 中的路径键，并检查键碰撞。原始输入摘要保留为计算来源记录。`digest_rewrite` 更新指定的 `bindings` 字段；`payload_bytes` 反转这项绑定更新后核对完整 payload。

变换限定于上述路径标签和声明的绑定摘要，其他序列化字节保持不变。该变换直接替换 JSON 字符串，不重新序列化数值。

## Lean 资源消费者

包含公开回执的 Lean 模块继续校验文件的完整 SHA256。导出记录用 `resource_sha256_rewrites` 登记原、新资源摘要，用 `view_sha256` 登记公开原路径视图的字节身份。

`resource_rewrites.data_sha256` 保留原始资源身份，`target_artifact` 指向公开资源；公开资源的摘要取其工件记录的 `target_sha256`。这些地址及摘要改写可逆，模块的原 `source_sha256` 可以逐字节复核。

## 两种视图

[`source_view.py`](../tools/source_view.py) 默认重建公开原路径视图：恢复本地 import 与资源地址，保留公开回执及其新资源摘要。它只需要本仓文件。

`--exact` 重建固定来源的原字节。带公开变换的回执从 `--private-originals` 指定的临时私有目录读取；每个原件以 `source_sha256` 为文件名。原件可按映射中的 `source_revision` 和 `source` 从源仓 Git 提取，对照结束后可删除临时目录。原件缺失或摘要不符时，精确重建失败。

将 `ORIGINAL_RECEIPT_ARCHIVE` 指向私有原件目录后，可完整验证原件到副本的关系：

```bash
python3 tools/source_view.py --verify-all --exact \
  --private-originals "$ORIGINAL_RECEIPT_ARCHIVE"
```

公开检查入口为 `make check-map`。输出分别报告 `published_receipts` 与 `private_originals_verified`；公开 payload 校验和私有原件对照各有明确计数。

## 生成与验证

迁移生成的收尾调用 `publish_outputs`，随后导出公开字节身份及变换记录。生成器与当前映射的一致性验收记录在[版本审查](reports/publication-review-2026-09-30.md)中。

针对变换、路径碰撞、结果篡改、公开视图和精确视图的测试：

```bash
python3 -m unittest discover -s tools -p 'test_publication.py' -v
```

公开分支从已核验的干净基线接入导出内容，论文标签绑定该分支的新提交。原始回执由固定源版本保存；公开分支携带已清理的文件。
