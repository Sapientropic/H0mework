# 第二版与低能首发复现

[第二版映射](second-edition-map.json)登记过程核心 C35–C45 和物理旗舰 P37–P40 的新增证明；原 60 条主张继承[固定首发映射](first-release-map.json)。[低能映射](low-energy-release-map.json)覆盖 L1–L28 与 Q1–Q6，各证明包保持实际 source epoch。实际执行结果和本地交付见[准备状态](second-edition-readiness.md)。

## 读者入口

在仓库根目录执行：

```sh
make check-map
python3 tools/edition_release.py --edition second verify-map
python3 tools/edition_release.py --edition low-energy verify-map
```

`check-map`核对每个公开文件的字节与可逆源身份；`verify-map`核对选定生产声明、直接消费者、资源和已登记的验收。后者不会自行构建或重放科学程序。加入 `--require-ready` 还要求全部已登记 kernel/runtime 验收完成。

导出计划和 `check-map` 均拒绝超过 100 MiB 的单文件。大型执行日志以 `.log.zst` 无损保存；`publication.json` 的 `target_sha256`核对压缩文件，`transforms`中的 `uncompressed_sha256`核对解压后的公开日志，原运行字节的 `source_sha256`保留。用 `zstd -dc <日志路径>`读取完整内容。未推送历史的日志修复与提交替换表见[历史改写回执](../evidence/second-edition/acceptance/local-history-rewrite-20261010.json)。

Lean 工具链与 Mathlib 使用 [toolchain](../Lean/lean-toolchain) 和 [manifest](../Lean/lake-manifest.json) 的固定版本。`make bootstrap` 获取固定依赖缓存。Python 运行依赖沿用 [Makefile](../Makefile) 的 `.local/venv/bin/python`，包含 NumPy、SymPy 和 mpmath。

## 按论文构建与完整声明审查

每次输出必须使用尚不存在的 `.local/` 子目录。`--paper`选择该论文的独立 epoch 证明包；各包的 Lean 环境和声明审查保持独立。

```sh
python3 tools/edition_release.py --edition second --paper source-process-core build --output .local/edition-runs/core-build-NEW
python3 tools/edition_release.py --edition second --paper source-process-core trust --output .local/edition-runs/core-trust-NEW
python3 tools/edition_release.py --edition second --paper physics-common-source build --output .local/edition-runs/physics-build-NEW
python3 tools/edition_release.py --edition second --paper physics-common-source trust --output .local/edition-runs/physics-trust-NEW
python3 tools/edition_release.py --edition low-energy --paper low-energy-phenomenology build --output .local/edition-runs/low1-build-NEW
python3 tools/edition_release.py --edition low-energy --paper low-energy-phenomenology trust --output .local/edition-runs/low1-trust-NEW
python3 tools/edition_release.py --edition low-energy --paper low-energy-loop-response build --output .local/edition-runs/low2-build-NEW
python3 tools/edition_release.py --edition low-energy --paper low-energy-loop-response trust --output .local/edition-runs/low2-trust-NEW
```

省略 `--paper` 会执行该 edition 的全部证明包。用 `--package <map中的id>`可以选择单包；同时给出 `--paper` 时，显式包必须属于该论文。

P37／P38 的完整 Audit 与原认证 ProductionConsumers 定义同名声明，各自属于原独立编译环境。映射用精确 `source_paths` 选择完整源文件，并分别登记聚合入口与根声明；两种包分别构建和审查。每份原认证消费者的完整生产正文、原测试根、原 source／object SHA 与认证回执均保留。

低能稿 1 的最终 L23 使用固定 c62 原单位修复，独立包为 `low-energy-l23-prepared-owner-c62`，入口为 `H0mework.Papers.LowEnergyL23PreparedOwnerC62`。其 13 个选定根包含原单位 owner、匹配转换与完整 full-light 消费者；旧 E055 源和原回执保持，原 E055 包继续用于 L21／L22。整篇 `--paper low-energy-phenomenology` 命令包含该独立包；原路径视图使用同名 view ID。

构建执行实际选定生产与消费者的 import 闭包，沿用 trust0／werror。`trust`先以 `lake --no-build`检查现有编译结果与当前源一致，再检查选定声明的完整类型、值、归纳与 recursor 元数据闭包，记录标准公理、unsafe／partial 与检查数量。运行记录注明缓存和实际输入；本轮本地执行复用了工作区编译缓存。

## 原路径与冻结资源

两份 map 的 `runtime_views`登记精确原路径、source epoch、原资源大小与 SHA256。`paths`包含源码及其嵌入资源，`resource_bundles`另外恢复冻结的大型数据。恢复只读取 H0 的公开材料：

```sh
python3 tools/edition_materials.py --edition second --view second-edition-physics-registered-forcing --output .local/edition-runs/bell-view-NEW
python3 tools/edition_materials.py --edition low-energy --view low-energy-l26-action-clock-71e --output .local/edition-runs/action-clock-view-NEW
```

其他 view ID 由对应 map 选择。`view-identity.json`登记实际恢复的每个源文件和资源。Bell 的 30 件冻结输入以确定性压缩副本保存；解码恢复原科学 payload，并逐项核对原大小和 SHA。恢复会使用约 1.14 GB 磁盘空间。

固定 9c73 的核心、物理、Physlib 与 CPS1 完整原路径视图使用：

```sh
python3 tools/source_view.py --at 9c73a630 --path-prefix Lean --path-prefix Verification/physics --path-prefix Verification/no-island/riemann-comb-source --path-prefix Verification/framework/source-policy --path-prefix third-party/Physlib --path-prefix Biomedical/runtime --output .local/edition-runs/new9-source-view-NEW
```

[实际恢复验收](../evidence/second-edition/acceptance/fixed-cap-9c73-public-source-view-20261010/result.json)覆盖 21,168 个源码布局、84 件工件及 38 个嵌入资源；178 条资源相对地址全部通过。低能九个新增视图均带齐 23 个嵌入资源，[实际恢复](../evidence/second-edition/acceptance/low-reader-resources-candidate-20261010/result.json)核对了全部 288 条资源地址。默认视图使用已登记的公开资源与构建适配字节；原始摘要与公开摘要在各回执分列。

## Bell 已冻结消费者

使用项目 Python 环境运行：

```sh
.local/venv/bin/python tools/edition_replay.py --edition second --output .local/edition-runs/bell-replay-NEW
```

入口恢复公开 view，分别运行原 shared-background intake、registered Duhamel、registered forcing 与其完整独立消费者。只消费已冻结 inlet、完整 free bank 和原 Chebyshev 数据；源登记要求保留。历史 Git blob 查询由已核实的公开源身份解析，原科学函数与结果字段保持，记录 `Git_ancestry_replayed=false`。每项保存真实结果与字段比较；原失败记录独立保留。

## 历史来源与兼容

核心 PR／C62 的历史 `InventoryTransport.born_kernel_member` 采用收稿上限前的纯证明修正。H0 另外修正了实际 receiver 的付费证明、泛型环境输入合同及有限配置的实际计算 reader 接线；物理 prepared Ward 以纯证明补充直接消费已证等式。定义变化与纯证明补充分别登记。原源码、原失败、本次实际构建与声明审查保持各自身份，详情见[环境与计算合同](source-action-environment.md)及映射中的 `source_origin`。低能 S/base 同字节关系限定于本轮实际选定源，按每个导出记录的 `source_revisions`核验。

第一版成品、60 条主张、原命令和冻结结果继续使用[首发复现指南](first-release-reproduction.md)。CI 新模块追加到独立阶段；旧模块、资源、库强选项与分片身份的实际保留结果由准备状态链接的回执记录。

GSR 九份副本的内存证明适配保留原来源 SHA 和 epoch；默认原路径视图使用适配证明，`source_view.py --exact` 恢复原字节。适配源码和可逆规则见[构建适配合同](proof-build-adaptations.md)，受影响包的新构建／审查与原回执分列。
