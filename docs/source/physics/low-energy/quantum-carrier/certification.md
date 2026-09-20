# 原完整载体与端点反馈认证

**Verdict: certified。** 2026-09-19，独立 certify 阶段核验
`Lean/scratch/LowEnergyQuantum/Carrier.lean` 与 `Compression.lean`。
分类为 **whole-carrier transporter / endpoint-feedback readout**，未修改候选。

## 精确机器范围

`internalBasis` 直接取原 `su7ExteriorBasis 6 / 2 / 4` 的 product basis；这些基本身来自原
`su7FundamentalBasis.exteriorPower`。`wholeBasis` 通过四分量原 DiracSpinorIndex 的 Pi basis
覆盖原 `DiracExteriorMatterCarrier`，未更换内部表示或原 matter carrier。

原载体为 `Λ⁶ V × (Λ² V × Λ⁴ V)`，故完整复维数为
`4 × (C(7,6)+C(7,2)+C(7,4)) = 4 × (7+21+35) = 252`。
`index_card` 对实际 basis 与原 carrier 的 finrank 完成核验；坐标标签保留原 spin 与外幂索引。

- `coordinates` 是完整线性等价，`operatorMatrix` 是完整 End 代数到同基方阵的 AlgEquiv。
- `matrix_action` 读回原算子作用；`matrix_faithful` 对任意两个原 End 给出矩阵相等与算子相等的等价。
- `matrix_composition` 保持 `A.comp B → M(A)M(B)`，右端先作用 B，再作用 A。
- `full_response` 对任意原 independent linear dual、任意 End、任意原 matter 精确成立。
  dualCoordinates 取原 dual 在 basis 向量上的值；没有引入复共轭或替换配对。

这组声明没有构造物理 Hamiltonian、量子时间、正状态或实验概率，也没有新增 runtime authority。
原 physics root/current/next 保持。

## 原 Yukawa 与返回见证

`matrix_yukawa_nonzero` 的非零见证固定为原 `Y(exteriorBreakingScalar)`；
不将其量化为所有标量输入的非零性。
`matrix_yukawa_products` 对任意两个原标量 s、t 证明完整矩阵乘积 `M(Y(s))M(Y(t))=0`，
直接消费原 whole-carrier `Response.Yukawa.ordered_product_zero`。

`full_return_detected` 消费已签收的原 ReturnChannel.prepared、原 independent dual 配对和非零幅度，
证明 `M(G)M(Y(mixedDirection))≠0`。原 Λ⁶ 中间输出被完整 basis 保留，复合在原 End 中完成。
返回见证使用原固定准备，未宣称是新的物理装置或新的量子态。

四个 Audit 消费者核验完整维数与忠实性、任意 dual 下的有序复合响应、Yukawa 的精确量词，
并将原 prepared 的返回复合实际写成 252 坐标求和，证明该原配对非零。
因此操作次序与原返回读数都被消费，未停留在未接线的矩阵接口。

## 原八坐标端点反馈

`Compression` 继续使用原 `Stage9DEF.Compatibility` 的嵌入 E 与读回 R，
已有 `R ∘ E = id`。`retained = E ∘ R` 是幂等投影 P，`complementary = id − P` 是代数补投影 Q；
这里没有增加正交性或内积解释。

对任意两个原 End，`compression_product` 无目标 premise 地证明
`C(A ∘ B) = C(A) C(B) + C(A ∘ Q ∘ B)`，其中 C 是原八坐标 `compression`。
其证明通过同一源上的 P/Q 分解与原矩阵复合完成，没有替换算子或辅助作用项。
`complementary_yukawa` 对所有原标量 s 证明 `Q ∘ Y(s) = Y(s)`，
故 `yukawa_excursion` 把完整 Yukawa 返回压缩精确读成补空间反馈。

`return_entirely_complementary` 实际消费原 ReturnChannel：
`C(G) C(Y(mixedDirection)) = 0`，但 `C(G ∘ Q ∘ Y(mixedDirection)) ≠ 0`。
新增两个 Audit 消费者核验通用分解，并将这一反馈接回原 `vectorRead 0`，证明原读数非零。
接回时保留 `responseMatrix` 原有的行翻转；矩阵乘法公式针对 C，未把行翻转后的响应矩阵误作代数表示。
此项是原操作的精确端点反馈读出，不增加源 action 或物理 Hamiltonian。

## 严格验证

Carrier、Compression 与 Audit 均 fresh 执行 `lake env lean --trust=0 -DwarningAsError=true`，
全部退出 0；候选 `.olean` 同次生成，没有宽构建。
Compression 顺序扩审保留已签收的 Carrier 范围，最终 Audit 同时消费两个模块。

26 个候选公开声明（16 theorem、8 def、2 abbrev）与六个消费者，共 **32 项**传递公理审计
全部属于 `{propext, Classical.choice, Quot.sound}`。
无 `sorry`、`admit`、`native_decide`、自定义公理或 kernel 跳过设置；生产目录未 import 此 scratch。
mouth lint 只有仓库惯用 `autoImplicit false` 提示。真实输出见 [lean-audit.log](lean-audit.log)。

来源复核包括原外幂 carrier／basis、Dirac carrier、Mathlib toMatrixAlgEquiv 与列向量作用约定、
原 ordered Yukawa zero、原八坐标嵌入／压缩和实际 ReturnChannel 配对。未发现 target premise、维数／域缩减、
算子复合顺序反转或源身份替换。

可按上述输运／读出口径晋升。后续 moving-actual 响应或物理谱不属于此认证。
本审计只写 quantum-carrier 目录，未 stage 或 commit。
