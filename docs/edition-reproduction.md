# 第二版与低能首发复现

[第二版映射](second-edition-map.json)登记过程核心 C35–C41 和物理旗舰 P37–P40 的新增证明；原 60 条主张继承[固定首发映射](first-release-map.json)。[低能映射](low-energy-release-map.json)覆盖 L1–L28 与 Q1–Q6，各证明包保持实际 source epoch。实际执行结果和本地交付见[准备状态](second-edition-readiness.md)。

## 读者入口

在仓库根目录执行：

```sh
make check-map
python3 tools/edition_release.py --edition second verify-map
python3 tools/edition_release.py --edition low-energy verify-map
```

`check-map`核对每个公开文件的字节与可逆源身份；`verify-map`核对选定生产声明、直接消费者、资源和已登记的验收。后者不会自行构建或重放科学程序。加入 `--require-ready` 还要求全部已登记 kernel/runtime 验收完成。

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

构建执行实际选定生产与消费者的 import 闭包，沿用 trust0／werror。`trust`先以 `lake --no-build`检查现有编译结果与当前源一致，再检查选定声明的完整类型、值、归纳与 recursor 元数据闭包，记录标准公理、unsafe／partial 与检查数量。运行记录注明缓存和实际输入；本轮本地执行复用了工作区编译缓存。

## 原路径与冻结资源

两份 map 的 `runtime_views`登记精确原路径、source epoch、原资源大小与 SHA256。恢复只读取 H0 的公开材料：

```sh
python3 tools/edition_materials.py --edition second --view second-edition-physics-registered-forcing --output .local/edition-runs/bell-view-NEW
python3 tools/edition_materials.py --edition low-energy --view low-energy-l26-action-clock-71e --output .local/edition-runs/action-clock-view-NEW
```

其他 view ID 由对应 map 选择。`view-identity.json`登记实际恢复的每个源文件和资源。Bell 的 30 件冻结输入以确定性压缩副本保存；解码恢复原科学 payload，并逐项核对原大小和 SHA。恢复会使用约 1.14 GB 磁盘空间。

## Bell 已冻结消费者

使用项目 Python 环境运行：

```sh
.local/venv/bin/python tools/edition_replay.py --edition second --output .local/edition-runs/bell-replay-NEW
```

入口恢复公开 view，分别运行原 shared-background intake、registered Duhamel、registered forcing 与其完整独立消费者。只消费已冻结 inlet、完整 free bank 和原 Chebyshev 数据；源登记要求保留。历史 Git blob 查询由已核实的公开源身份解析，原科学函数与结果字段保持，记录 `Git_ancestry_replayed=false`。每项保存真实结果与字段比较；原失败记录独立保留。

## 历史来源与兼容

核心 PR／C62 的历史 `InventoryTransport.born_kernel_member` 采用收稿上限前的纯证明修正。H0 另外修正了实际 receiver 的付费证明、泛型环境输入合同及有限配置的实际计算 reader 接线；物理 prepared Ward 以纯证明补充直接消费已证等式。定义变化与纯证明补充分别登记。原源码、原失败、本次实际构建与声明审查保持各自身份，详情见[环境与计算合同](source-action-environment.md)及映射中的 `source_origin`。低能 S/base 同字节关系限定于本轮实际选定源，按每个导出记录的 `source_revisions`核验。

第一版成品、60 条主张、原命令和冻结结果继续使用[首发复现指南](first-release-reproduction.md)。CI 新模块追加到独立阶段；旧模块、资源、库强选项与分片身份的实际保留结果由准备状态链接的回执记录。
