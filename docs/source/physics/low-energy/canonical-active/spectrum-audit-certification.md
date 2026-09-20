# Canonical79 / independent-dual24 轴向谱拆分认证

Verdict: **certified**。冻结 `compute.py`、`receipt.json`、`exact-check.log`、`README.md` 的 79＋24 保真拆分、精确常数、因子及原点重数均通过独立认证。候选未改、未提交。

## 原源与制备子类

输入为[已签收 canonical 制备闭合](../../audit/certification.md)、[原 faithful103 商](../../../active-gauge/quotient-audit/certification.md)及[完整轴向除子](../../../active-gauge/propagation-audit/certification.md)。原 independent-dual 字段域完整保留；79 是所选 canonical 制备子类的商，24 是同一理论中实际字段的补空间，不称其为 unphysical。

原 `positiveSmoothUnifiedSource`、修复 Dirac-dual action、actual 与 visit 10 / tick 16 / materialEntry → visit 11 / tick 17 保持。本组是从属谱读出及等价坐标 transport，无 controller 推进。新运算范围为 `p=(λ,0,0,ik)`。

[独立检查](independent_check.py)从当前 Lean `diracAdjointSpinSwap` 字面量重建原 S₁₂ 与
`L=√2 diag(S₁₂,−S₁₂)`，包括虚部反号。实际字段关系为

```text
ψ = w + z,    χ = L(w − z),    L²=2I.
w = ψ/2 + Lχ/4,    z = ψ/2 − Lχ/4.
```

这直接生成 `[C,Cminus]` 的两侧逆，随后逐项对照已认证源坐标。C 与 Cminus 非正交，独立检查明确拒绝 `Cᵀ` 冒充左逆。另从原 H112 重算两侧混合块为零及 A79，不只信任输入回执的 `full_equation_closure` 标记。

## 全部矩阵与行列式单位

从原 section/readback 生成并核验

```text
F(p) = Q103(p) [C E79, Cminus]
Finv(p) = [Q79(p) Cleft S103 ; Cminus,left S103]
Finv F = F Finv = I103
F(−p)ᵀ K103(p) F(p) = diag(A79(p), B24(p))
B24 = Cminusᵀ H112 Cminus.
```

两侧变换全部条目都在常数域 `Q(√2,√15,i)[λ,k]` 内；未引入动量分母。实际验证 `F=F0(I+U)`、`U²=0`，支付常数 determinant。

单位还通过独立算法从原源 minor 重建，未复用候选的 103×103 determinant：

| 实际来源 | 值 |
|---|---|
| 原103截面九阶源 minor | `27√2/500` |
| canonical 截面九阶源 minor | `−1/8` |
| 两组行置换符号 | 原103：`+1`；canonical：`−1` |
| 原字段变换 `det[C,Cminus]` | `2^36` |

比值得到同一非零单位

```text
det F = 2^34·5^3·√2 / 3^3 = 2147483648000√2/27.
```

因此分拆在整个轴向动量平面保真；canonical 或补块中的非零方向都不会在原 faithful103 表示中被抹去。

## 完整因子与常数读回

沿用原 `λ=N√2u, k=√2q, N²=54/125`，`Bbar=B24/N`。fresh 原算法精确计算 Bbar 的实际 determinant，得到整体常数 **`2^48`**、**8 个不同 Q 因子、总次数24**。

独立检查另在素数 1009、1013 下，各用 `i²=−1` 的两个根，以模素数 Gaussian 消元覆盖完整 25×25 次数界网格：共 **2,500 次**精确 determinant 检查，验证四个完整多项式模像。所有系数分母检查可逆。精确 Q 因式分解由 fresh 源算法支付，模像检查为不同算法的独立复核。

完整103因子的重数逐项等于 canonical 与补块重数之和，没有遗漏或负重数。连同原103的非零常数与上述单位，精确核验

```text
det A79 = (det F)² det K103 / (N^24 det Bbar).
```

所得 canonical 除子有 **14 个不同 Q 因子、总次数102**，完整常数保存于冻结回执。fresh 计算与既有 A79 在原 `(λ,k)=(2,1)` 的精确 determinant 完全相等。独立检查又将实际 A79 作明确可逆常数缩放到 Q(i)，直接核对四个动量特化下的 determinant；其三个非零点模秩79、原点模秩77，与预测常数和因子完全一致。这里没有省略 `det F` 的平方、N 的24次幂或额外字段缩放。

## 两边原点重数直接复验

候选通过补块与已认证103重数相减得到 canonical 重数。本次另直接计算两边各自的原点矩阵与二阶截断 Toeplitz 矩阵：先实化，再用 Python `Fraction` 做独立有理消元。

| 块 / 轴 | 原点矩阵秩 | 二阶 Toeplitz 秩 | 两个截断核维数 | determinant 消失阶 | 非零部分重数 |
|---|---:|---:|---|---:|---|
| canonical79 / 时间 u | 77 | 154（158×158） | `[2,4]` | 4 | `[2,2]` |
| canonical79 / 空间 q | 77 | 154（158×158） | `[2,4]` | 4 | `[2,2]` |
| complement24 / 时间 u | 21 | 44（48×48） | `[3,4]` | 4 | `[1,1,2]` |
| complement24 / 空间 q | 21 | 42（48×48） | `[3,6]` | 6 | `[2,2,2]` |

表中列出复秩；实际实化矩阵秩为其两倍。每条轴的第二截断核维数已等于从精确因子独立读出的 determinant 消失阶，排除了未计入的大于2的部分重数。因此 canonical 原点核为2维、补块为3维，完整五维原点核保留。

## 低动量分支与原五态

四条既有 gapless 因子的重数归属逐项核验：

| 原时间/动量首项 | 所属块 |
|---|---|
| `λ²=+k²/3+O(k⁴)` | canonical79 |
| `λ²=−594k²/1675+O(k⁴)` | canonical79 |
| `λ²=−18k²/25+O(k⁴)` | independent-dual24 |
| `λ²=−3k⁴/20+O(k⁶)` | independent-dual24 |

完整原五态多项式 `u(u²+6)(u²−3125/162)` 共同整除的唯一 canonical 因子为12次因子。其 q=0 限制实际为

```text
u² (u²+6) (75u²+34) (162u²−3125) (27u⁴+500) / 328050.
```

原 gauge 根经同一读回给出 `λ²=50/3`。该12次因子的 gapless 首项确为 `+k²/3`；另一条 canonical gapless 支属于10次因子。这里的共同归属是完整多项式因子的准确身份，不将原点两条相交零模的任意场向量自动指定为某条有限 k 延拓。

## 证据与范围

- [replay.log](replay.log)：冻结 `compute.py` 使用五份已认证输入 fresh 重放，**EXIT 0**，23.307秒；新旧 JSON 除计时字段外完全一致。
- [independent-check.log](independent-check.log)、[独立回执](independent-receipt.json)：源 adjoint 重建、显式非正交逆、完整 signed congruence、源 minor 比值常数、模多项式、两侧直接原点秩与实际因子归属，**EXIT 0**。
- 明确反控制拒绝转置替代真实左逆、丢掉一个 `det F` 因子、把补块的四次低动量支塞入 canonical。

本组没有新增 Lean 声明或公理，保持精确程序证据身份。签收所选 prepared canonical 子类及其实际 independent-dual 补块的完整**轴向**特征拆分；不将因子重数改称实验粒子数、物理子类唯一性或已经完成的全方向传播谱。
