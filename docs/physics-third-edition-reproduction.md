# 物理旗舰第三版复现

[固定选集](../checks/physics-third-edition-selection.json)与[逐主张映射](physics-third-edition-map.json)登记 P45–P47。首发源纪元承担谱选择、四腿临界等价、Volterra、全阶能量和根封印。电磁材料采用 `df421ff6` 的固定收稿源码，并按[原编译对象与回执](../evidence/physics-third-edition/original-em-search.json)恢复导入。公共底层固定在 `2cccd55f`。早期电荷、Thomson 与后期 Ward 各有对应的证明包。四维曲率采用 `7e4da746`，Bell 的 291、300 和 301 沿用各自的实际原证明纪元。

从仓库根目录运行。每次复验使用新的输出目录。Lake 使用固定工具链及 manifest，已有产物由 Lake 的新旧检查复用。

```sh
make check-map
python3 tools/physics_third_edition.py entry
python3 tools/physics_third_edition.py source --output .local/physics-v3-public
python3 tools/physics_third_edition.py build --output .local/physics-v3-build
python3 tools/physics_third_edition.py trust --output .local/physics-v3-trust
python3 tools/physics_third_edition.py types --output .local/physics-v3-types
```

`build`、`trust` 和 `types` 支持重复指定 `--package`。每个证明包的公开入口和完整命题位置见映射。原独立查询与反控进入相应的编译闭包。公理与类型回执按实际公开编译环境生成，原认证作为独立证据保留。

固定选集的 `import_sources` 登记原独立编译中跨目录或跨纪元的导入。`public_owners` 在历史布局有多份公开副本时固定实际装载的 owner。公开原路径视图按该绑定恢复各个源树。`original_proof_supplements` 同时固定电荷证明的旧适配和归档原件。需要原回执字节时，把原件按 SHA-256 放入私有目录，再运行精确视图。

```sh
python3 tools/physics_third_edition.py source --exact \
  --private-originals "$ORIGINAL_RECEIPT_ARCHIVE" --output .local/physics-v3-exact
```

[公开证据变换](evidence-publication.md)记录回执运行路径的可逆规范化规则。第一版、第二版的验收与复现入口见[首发](first-release-reproduction.md)及[第二版](edition-reproduction.md)。
