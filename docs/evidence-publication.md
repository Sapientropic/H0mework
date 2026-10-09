# 公开回执与原始来源

公开回执保留计算数据、结果和失败记录，将运行路径改为相对地址。原件由私有研究仓的固定 Git 版本保存，导出映射同时记录原件和公开副本的身份。

## 字节身份

[`export-map.json`](../tools/export-map.json) 的工件记录使用以下字段：

| 字段 | 含义 |
| --- | --- |
| `source_sha256` | 固定来源提交中的原始字节摘要 |
| `target_sha256` | 本仓文件的完整字节摘要 |
| `compression` | 可选的无损 gzip 编码及解压后的字节数、SHA256；来源摘要保持原件身份 |
| `publication.kind` | 声明的公开变换；JSON 使用相对路径或精确指针，程序及文本使用 `declared-text-runtime-paths/v1` |
| `publication.runtime_paths` | v2 的精确 JSON 指针、字典键位置及对应相对地址 |
| `publication.payload_sha256` | 路径规范化后的原始序列化字节摘要；保留数值的原始写法 |
| `publication.digest_rewrites` | 公开回执读取另一个公开回执时，对绑定摘要的明确更新 |

没有 `publication` 的工件内容保持原字节。若另有 `compression`，工具先核对压缩文件，再解压并核对完整原件；否则两个文件摘要相同。带 `publication` 的工件使用派生字节；其原始提交和 `source_sha256` 保留。原路径视图自动恢复解压后的文件，路径变换与压缩分别核验。

[`publication.py`](../tools/publication.py) 的 `normalize_paths` 只改运行根目录、命令路径及 `source_inputs`／`input_sha256` 中的路径键，并检查键碰撞。原始输入摘要保留为计算来源记录。`digest_rewrite` 更新指定的 `bindings` 字段；`payload_bytes` 反转这项绑定更新后核对完整 payload。

变换限定于上述路径标签和声明的绑定摘要，其他序列化字节保持不变。该变换直接替换 JSON 字符串，不重新序列化数值。

首发证据中的来源文件、编译对象、编译搜索路径和原失败日志使用 v2：`declared_runtime_paths` 只替换 `runtime_paths` 指定位置的字符串。字典路径键通过 `key_index` 登记，公开记录不包含私人原键。其他字段及数值写法保持原字节，目标键冲突或声明位置缺失会使变换失败。原件对照使用相同声明验证 payload；原执行的结果和失败状态保持。

原复现程序中的机器路径由 `text_runtime_paths` 按明确字符区间替换。区间必须指向机器地址且互不重叠，公开记录保留位置和相对地址；其余程序、表达式及数值字节保持。原件摘要与路径替换后的完整 payload 分别核验。

## Lean 资源消费者

包含公开回执的 Lean 模块继续校验文件的完整 SHA256。导出记录用 `resource_sha256_rewrites` 登记原、新资源摘要，用 `view_sha256` 登记公开原路径视图的字节身份。

`resource_rewrites.data_sha256` 保留原始资源身份，`target_artifact` 指向公开资源；公开资源的摘要取其工件记录的 `target_sha256`。这些地址及摘要改写可逆，模块的原 `source_sha256` 可以逐字节复核。

Lean 私有声明的名称包含所属模块地址。模块迁移时，显式引用这些名称的源码用 `private_name_rewrites` 登记原／新地址；[`source_view.py`](../tools/source_view.py) 的 `rewrite_private_names` 只改声明的名称引用，保留注释、字符串和相似长名称。原路径视图恢复所属模块地址并核对原摘要。

通过 `Name.toString.startsWith` 查找私有函数的原宏使用 `private_owner_string_rewrites` 登记原／新 owner。`rewrite_private_owner_strings` 只改唯一的、已登记的可执行 `.startsWith` 完整前缀字面量；保留普通消息、注释、raw／转义字符串及相似长名称。逆向恢复后仍核对完整原源码摘要，宏的唯一 owner 条件与实际函数值保持。

同一命名空间的不同模块若生成了冲突的匿名局部实例名，`local_instance_names` 登记对应声明前缀与显式名称。`name_local_instances` 只插入名称，保留实例类型、值和定理正文；恢复原路径视图时移除该名称并核对原摘要。

同一原模块在不同恢复布局中出现时，原模块名、完整源码及递归 import 签名一致的布局共享一个完整证明 owner。`source_aliases` 保留各原路径、SHA、epoch 和来源；原路径视图为每个地址恢复完整源码，逐项映射按该地址的来源核验。实际包只导入一次该声明 owner。

认证消费者保留数学定义与证明的原字节。末尾的 `run_cmd` 或 `elab` 观察命令用 `audit_module_rewrites` 对齐所查询的模块地址；`audit_command_name` 为独立审查固定各自的命令注册名，使其可以合并导入。Bell 消费者的 `audit_boundary_fallbacks` 保留原边界文件覆盖，在没有提供文件时完整遍历依赖图，委托边界为空；`audit_full_closure` 只调整其观察命令的执行预算。`rewrite_audit_module_names`、`name_audit_command` 与 `rewrite_audit_runtime` 将这些变换逆向恢复，原路径视图继续核对固定来源摘要。选定声明的完整 trust0／werror 审查由[首发验收入口](first-release-reproduction.md#完整检查)执行。

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

迁移生成的收尾调用 `publish_outputs`，随后导出公开字节身份及变换记录。生成产物的身份检查使用 `make check-map`。

公开单文件上限为 100 MiB。`python3 tools/publication.py --check-file-sizes` 检查已跟踪和未忽略的新文件；`source_view --verify-all` 同时检查。超限原件必须无损压缩，并登记新引用、压缩摘要和解压身份。运行日志的 `.log.zst` 编码与原始字节身份由相邻 `publication.json` 登记。

针对变换、路径碰撞、结果篡改、公开视图和精确视图的测试：

```bash
python3 -m unittest discover -s tools -p 'test_publication.py' -v
```

公开分支从已核验的干净基线接入导出内容，论文标签绑定该分支的新提交。原始回执由固定源版本保存；公开分支携带已清理的文件。
