# 《可能性的经济宪法》第三版复现

[逐项证明映射](economic-constitution-v3-map.json)覆盖十八项正文结果。八条制度原则在正文各自给出规范论证。定理 1.2 综合分域构造。定理 9.3 在每个深度的同一次实际付款上联结六项条件，并保留下一根访问的精确身份。

| 范围 | 固定公开提交 | 主要入口 |
| --- | --- | --- |
| 经济宪法原选集与同发生再生 | `2d6fbc96e33b7c4c3cfd91104fda74e3caeda045` | [原十六包](economic-constitution-reproduction.md)、`H0mework.Papers.GeneratedSocietyRegeneration` |
| 退出需求、同债再现、限域核验与原隐私通道 | `fd6147f8c337d88ebf72d91ddadef0aa601e6c2e` | [社会账本补集](society-book-reproduction.md) |
| 有限独立抽样 | `3c6a36c3d7ddd920f52afeb52990f0456ee53c83` | `Privacy.IndependentProduct`，见[逐项证明映射](economic-constitution-v3-map.json) |

新模块沿每次实验的公开初态、策略、步数与有理加权外生噪声带构造有序联合律。`Network.independent_productLaw_eq_of_same_public_draws` 允许各次私域选择独立改变。`Network.independentProductLaw_pair` 恢复原双次抽样律。两者直接消费固定 `Privacy.Network`。

定理 8.1 的证明通过同次共同清算后的实际续行回读外部责任。原根、付款和服务发生各有索引单射。定理 9.3 引用 `periodicSameOccurrenceRegeneration_nextIsNextStep`，在该原源上识别同根实际后继。

## 核验命令

在仓库根目录用固定 Lean 工具链运行。新一轮使用新的输出目录。已有 Lake 产物和固定依赖可继续使用。

```sh
make check-map
python3 tools/economic_constitution_v3.py entry --output .local/ecn-v3-entry
python3 tools/economic_constitution_v3.py build --output .local/ecn-v3-build
python3 tools/economic_constitution_v3.py trust --output .local/ecn-v3-trust
python3 tools/economic_constitution_v3.py types --output .local/ecn-v3-types
```

`entry` 复核已登记的接受范围、完整类型、源码逆变换和五份发布文件。提供 `--homework-repository` 时，另逐一和原 Git 字节比较。新模块的明确来源选集见[导出选择](../checks/economic-constitution-v3-selection.json)。原始收据保留在其对应[经济选集](economic-constitution-readiness.md)与[社会账本补集](society-book-reproduction.md)。

[本地验收](economic-constitution-v3-readiness.md)保存新增检查与旧缓存核对的结果。
