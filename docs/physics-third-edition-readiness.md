# 物理旗舰第三版验收

P45–P47 的 10 个证明包在本机 Darwin/arm64 通过增量构建、`--trust=0` 信任闭包和 145 项完整声明类型核验。公理依赖合计为 `Classical.choice, Quot.sound, propext`。原路径公开恢复与原字节恢复分别核对 10,404 个文件，包含原认证、程序和资源。

[逐主张映射](physics-third-edition-map.json) · [固定选集](../checks/physics-third-edition-selection.json) · [复现](physics-third-edition-reproduction.md)

| 证明包 | 完整声明类型 |
| --- | ---: |
| `analysis` | 12 |
| `authority` | 15 |
| `bell` | 14 |
| `chargebridge` | 6 |
| `curvature` | 53 |
| `gravity` | 9 |
| `phenomenology` | 12 |
| `spectral` | 10 |
| `thomson` | 5 |
| `ward` | 9 |

- [构建回执](../evidence/physics-third-edition/acceptance/build.json.gz)
- [信任闭包回执](../evidence/physics-third-edition/acceptance/trust.json.gz)
- [完整类型回执](../evidence/physics-third-edition/acceptance/declaration-types.json.gz)
- [公开恢复回执](../evidence/physics-third-edition/acceptance/source-public.json)
- [原字节恢复回执](../evidence/physics-third-edition/acceptance/source-exact.json)


首发 Bell 的 14 项和量子载体的 18 项科学复现保持原输入与回执。[Bell 复用](../evidence/physics-third-edition/acceptance/first-release-bell-cache.json) · [量子载体复用](../evidence/physics-third-edition/acceptance/first-release-quantum-cache.json)

## CI 缓存

旧 83 个 Linux 分片的完整缓存键逐项一致，成功存档均已核实。新增 9 个分片，共 58,068 个默认模块与 11 个阶段。新增计划的整体指纹为 `5e4c76578abe3c2c326b51af0dcfa26af7800097f14ed6c585c7f03d4039400a`。[逐片报告](../evidence/physics-third-edition/acceptance/cache-preservation.json) · [基线 CI](https://github.com/Sapientropic/H0mework/actions/runs/42701258971)

本地验收固定于上述回执，新增选集的远端 CI 由推送后的工作流记录。
