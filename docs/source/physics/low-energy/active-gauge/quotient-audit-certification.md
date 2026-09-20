# 九个源对称方向的忠实轴向截面认证

Verdict: **certified**。冻结 `quotient.py/json` 的 faithful section、完整符号分解及精确秩范围均成立；未发现候选缺陷。本次不改候选、不提交。

## 输入与分类

输入是[已签收原作用](../audit/certification.md)的 112 方程矩阵及[本轮复验](../principal-audit/certification.md)的九个实际源对称列。原 289→121 的辅助消元和 121→112 的 Ward 方程等价保持，不用新矩阵替换 source。控制 capsule 保持原 visit 10 / tick 16 / materialEntry → visit 11 / tick 17。

本组是从属、忠实的方程 transporter，轴向约定 `p=(λ,0,0,ik)`。标量域为 `Q(√2,√15,i)` 的动量有理函数域；没有供入预期秩、diffeomorphism 商或待证的逆。

## 完整保真恒等式

冻结索引均按原字段编号读取。九个删除坐标为
`[21,27,39,58,59,60,63,64,68]`，即三个 gauge A 坐标及六个 coframe 坐标；原 scalar J 的编号 0–8 已在上游 Ward 方程中处理，截面没有再次删除它们。

九个源列 `T(p)` 在这些行组成动量无关 minor，其行列式为 `27√2/500 ≠ 0`。以 C 表示其余 103 坐标的包含、Q 表示读回、U 表示九个源参数的读回，独立复验从冻结回执解码并精确验证：

```text
U T = I₉
Q C = I₁₀₃
C Q + T U = I₁₁₂
Q T = 0
K = Cᵀ H C
H(p) = Q(−p)ᵀ K(p) Q(p)
```

Q、T、K 均为动量多项式，U 为常数，未引入 λ 或 k 的分母。因而对每个轴向动量，完整 112 个方程与 103 维截面方程保真相接；九个已生成源方向在所有这些点保持线性独立。

直接 source consumer 进一步验证 `H C = Q(−p)ᵀ K`，以及投影 `P=Q(−p)ᵀCᵀ` 满足
`P²=P`、`T(−p)ᵀP=0`、`P+UᵀT(−p)ᵀ=I`。因此，在 K 可逆处，对所有满足原相容条件 `T(−p)ᵀj=0` 的源，`C K⁻¹ Cᵀj` 确实解全部原 112 方程；任意齐次差别正是源对称方向。相容源条件的地位明确，没有把任意源硬投影后称为原方程解。

## 精确秩及原点

fresh 原算法使用代数数域精确算术，在 `(λ,k)=(2,1)` 计算完整 103×103 非零行列式，与冻结巨大有理倍 `√30` 完全一致。这个实际非零特化支付一般秩下界；九维核和截面恒等式支付上界，所以一般 `rank H = rank K = 103`。

独立检查另用素数 `1000000009`，以
`√2↦291087696`、`√15↦263655498`、`i↦430477711` 映射局部化的系数环。逐一核验三条平方关系、原 primitive element 最小多项式以及遇到的 210 种有理分母均与素数互素；未使用浮点秩。

| 轴向点 `(λ,k)` | H 精确秩 | K 精确秩 | 独立 `det K mod p` |
|---|---:|---:|---:|
| `(2,1)` | 103 | 103 | 817841615 |
| `(1,0)` | 103 | 103 | 101276167 |
| `(0,1)` | 103 | 103 | 521822140 |
| `(0,0)` | 98 | 98 | 0 |

有限域结果只用于秩下界及非零见证。原点的上界单独由原代数数域中的 **五个明确独立 K 零向量**支付，并逐项验证其经 C 提升后被原 H 消去；零向量完整存入[独立回执](independent-receipt.json)。所以原点 K 的核为 5 维、H 的总核为 14 维，额外退化没有被九维对称商抹去。冻结 `source_kernel_dimension: 9` 指已生成的源对称子空间；H 的完整核只在一般点及所列非零轴点为 9 维。

## 命令结果与边界

- [replay.log](replay.log)：`uv run --with sympy==1.14.0 python -u .../quotient.py --receipt .../receipt.json --symmetries .../symmetries.json --out /tmp/quotient-audit.json`，**EXIT 0**，195.861 秒。新旧 JSON 除计时字段外完全相同。
- [independent_check.py](independent_check.py)、[independent-check.log](independent-check.log)：不 import 候选，重新解码原矩阵与冻结 transporter，核验全部恒等式、相容源消费者、独立模素数见证和原点真实零向量，**EXIT 0**，63.889 秒。

本组没有新增 Lean 声明或公理；相关原 Hodge 的 11 项标准公理检查见[主部认证](../principal-audit/certification.md)。这里签收的是轴向精确矩阵商与一般可逆性，不将 103 坐标解释为 103 个物理极化，也不把指定主块因子或一般非零行列式当成完整传播因子。未展开 resolvent 的各项，未认证未冻结的 propagation 候选。
