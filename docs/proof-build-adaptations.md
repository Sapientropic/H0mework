# 可逆的证明构建适配

研究源码的身份与公开编译使用的证明体分开登记。`export-map.modules` 保留原 `source_sha256`、`source_revision` 与可用 epoch；`proof_body_rewrites` 用唯一完整定理锚点声明原／公开证明体，二者的定理陈述必须逐字相同。`target_sha256` 核对公开模块，`view_sha256` 核对恢复原路径后的适配视图。

`source_view.module_views` 返回公开视图和精确原件。默认原路径视图使用已适配的证明，便于构建；`--exact` 逆转证明适配及资源摘要变换，再核对原源码 SHA。资源、定义或定理陈述的变动不能借证明适配登记。实际 kernel 构建与完整声明审查负责验收适配证明的类型、值和信任闭包。

`build_adaptations` 登记原因、范围、原件／适配源工件及实际 H0 提交，不改变原研究来源。源码闭包摘要包含公开模块字节，因此同一陈述的证明适配仍要求受影响包重新构建和审查；原回执保留为原源码范围的历史事实。

## GSR 稀疏证明

`originalScalarOrbit_code` 先消费原 `originalRho_fast`，再用 `vacuumColumn` 的四个非零位置把 70 项求和化为四项，最后继续 `decide +kernel`。九份副本共享[原源码](source/second-edition/physics/historical/NativeGravityScalarReturn.lean)与[适配源码](source/second-edition/physics/adaptations/NativeGravityScalarReturn.lean)，陈述、前提、定义与编译选项保持。

原源码 SHA 为 `db77bbe6fd166b57969997d13a8da2469718704310b3448f4f69c9cc06d2a4b3`，适配原路径视图 SHA 为 `c42bdf3ae1a427b99cb800fbfaf5b712044b822201b65cec0e9c6d370f5d69b0`。实际适配提交为 `7ece6168f129032b804c9841dddbf616d140e0ba`。

`ci_memory.tsv` 为旧路径和 `ReleaseMaterials` 路径各登记内存键，九份副本均保持单独编译。逐包执行与缓存签收只在[当前验收状态](second-edition-readiness.md)维护。
