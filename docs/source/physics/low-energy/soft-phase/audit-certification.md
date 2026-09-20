# 原两相位有效二次作用独立认证

Verdict: **certified**。冻结 `compute.py`、`receipt.json`、`README.md`、`exact-check.log` 的源相位归一化、四动量消元、原作用/Noether 读回与四阶壳系数全部通过。候选未改、未提交。

本轮按 living-law-controller → lean-agent → certify 进行从属数学认证。原 `positiveSmoothUnifiedSource`、修复 Dirac-dual action、`SpinPair.actual` 与 `Stage10.Runtime` 的 visit 10 / tick 16 / 原 materialEntry → tick 17 后继保持。消费[已认证 canonical79](../../canonical-active/audit/certification.md)、[原点相位](../../active-gauge/origin-audit/certification.md)及[canonical 精确除子](../../canonical-active/spectrum/audit/certification.md)，未重开旧关或增加 authority。

## 原相位与可逆的77方向

独立检查从当前 Gamma 字面量、实际 ψ₀ / independent dual χ₀ 重建原点第1、3列（从0编号）：

```text
ϕ：δψ=iψ₀，    δχ=−iχ₀；
θ：δψ=−iγ₅ψ₀，δχ=−iχ₀γ₅。
```

两列完整匹配原289坐标及冻结相位数据，并真实位于原 canonical 切向。字段缩放由原 field labels 重建，`G=SᵀK79S/N`，`u=λ/(N√2)`、`qj=kj/√2`、`pj=ikj`，所有四个动量保留。

源相位必须通过实际 `Q(p)` 读回：独立确认 `P(p)−P(0)` **非零但完全属于77列 E**。实际 T=`[P(0),E]` 有双侧逆，且

```text
(T⁻¹)light P(p) = I₂,
(T⁻¹)light Graph(p) = I₂.
```

因此使用 P(0) 作常数 light basis 合法，源相位相对它的非零 heavy shift 也被完整保留；没有把 `P(p)=P(0)` 当成事实或另行重标定角度。

原 `D₀=EᵀG₀E` 的给定逆与实际矩阵左右相乘均为 I₇₇。独立算法用有限 Neumann 展开作用于 B，重新生成 W₁…W₄，而不是复用候选的递归函数；各 Wn 的全部四动量系数与 n 次齐次性逐项相同。可逆性来自实际 D₀，不是外供稳定性或目标解证书。这里的77方向指原点可逆方向，不计作77个物理粒子。

## 全部原行与真实作用归一

独立重建原三轮辅助 field lift V，以及含原九条 broken-gauge Ward 行的 equation lift J，逐项核验

```text
H289 V = J G,
G Graph = T⁻ᵀ[:,0:2] (K₂+K₄) + R,
H289(V Graph) = J T⁻ᵀ[:,0:2](K₂+K₄) + J R.
```

归一化 R 和完整原289余项的实际非零齐次次数均为 **5、6**；全部系数保存并核对。没有只验证选中的两个 light 行。删去原九条 Ward 行，或把其中的 `−p` 误换成 `+p`，都会产生实际非零矩阵残差。

额外直接验证的作用消费者为

```text
V(−p)ᵀ J(p) = N I79,
[ (V Graph)(−p)ᵀ H289(p) (V Graph)(p) ]≤4 = N(K₂+K₄).
```

连同原二次作用的 1/2，这支付原作用密度的 N、符号和幅度，而非仅把归一化 G 命名为原作用。

## 二阶作用及原 Noether 来源

二阶算子精确为

```text
K₂ = diag((32/11)u²+(160/67)|q|²,
          −40u²+(2500/81)|q|²).
```

恢复原坐标并做分部积分，得到

```text
L₂ = −8/(11N)(∂tϕ)² + 40N/67 |∇ϕ|²
     +10/N(∂tθ)² + 625N/81 |∇θ|².
```

独立 Noether 检查先读原
`StageNineMatterCovariantDerivativeAffine.matterCovariantDerivativeVariationVector`
的 `i Γe·Dψ`，以及修复作用中同一 independent dual、原体积密度的配对。原正 coframe 上 `Vol·e⁻¹=adj(e)`。对**局部相位梯度**取系数后，才作原场线性化，得到

```text
Jϕ^μ = −Vol Re χ Γe^μ ψ,
Jθ^μ =  Vol Re χ Γe^μ Q ψ.
```

完整 Q=`γ₅+2P₆` 的来源与原动能/Yukawa 保持已由 [FullPhase](../../full-phase/audit/certification.md) 支付；在本次原占据 H 及其 active 变化上 Q 限制为 γ₅。独立检查使用两份原 matter 坐标，未用 canonical 关系提前删去 dual 变分。

coframe 部分由真实 adjugate 微分
`δadj(e₀)=det(e₀)[tr(e₀⁻¹h)e₀⁻¹−e₀⁻¹he₀⁻¹]` 生成。因此 θ 时间密度包含三个空间 coframe 对角方向，各系数 `4√2`；省略该 cofactor 项会改变实际领先响应，反控制明确拒绝。

这还通过了比“与有效 L 吻合”更直接的源检验：独立生成全部四个 current 的线性 covector，并对**所有289个扰动列**核验

```text
∑μ pμ δJ^μ + ZᵀH289 = 0.
```

这里 Z 是上述两条原相位列。此后再代入实际 full graph，才读到

```text
δJϕ⁰ = −16/(11N) ∂tϕ + O(∂²),
δJθ⁰ =  20/N ∂tθ + O(∂²),
Jϕ,0⁰=0，Jθ,0⁰=4√2，所有背景空间 current 为0。
```

它们与 L₂ 的两条共轭动量精确相同，来源、体积因子与角度幅度都已独立支付。

## 四阶壳与精确原因子

完整 K₄ 系数逐项核对，且确实不在这个固定 heavy 截面上显式各向同性。独立检查将各对角项代入相应领先壳 `u²=−55|q|²/67`、`u²=125|q|²/162`，结果严格只含 `|q|⁴`。

另外直接从已认证 canonical 的10次、12次**精确原因子**构造 `P(x,r)`，其中 `x=u²,r=q²`，独立作隐函数二阶系数计算。所得原坐标分支与本次 Schur 展开完全相同：

```text
λϕ² = −594/1675 |k|² −10152864/939884375 |k|⁴ + O(|k|⁶),
λθ² =  1/3     |k|² −3053/29160       |k|⁴ + O(|k|⁶).
```

二次壳之间的领先系数不同；K₄ 的 off-diagonal mixing 不进入这一次四阶修正。原坐标读回因子分别为 N² 与 N²/2，未丢 `k=√2q` 的尺度。各向同性签收的是上述实际壳系数，不强加未成立的离壳矩阵恒等式。

## 回执与范围

- [replay.log](replay.log)：SymPy 1.14.0 fresh 重放 **EXIT 0**（19.748秒）；新旧 JSON 除计时完全一致。
- [independent_check.py](independent_check.py)、[independent-check.log](independent-check.log)：不 import 候选，从原算子、相位与动能重建上述身份，**EXIT 0**（32.441秒）。
- [独立回执](independent-receipt.json)记录 Neumann 图、余项次数、原作用 N、完整 Noether Ward 身份、两条原因子壳比对及反控制。

本组无新增 Lean 声明或公理。签收同一 canonical 制备中的**经典、相位幅度二次、四阶导数有效作用**及精确有限余项；不替代完整非线性作用，也不追加 physical particle 或 quantum vacuum 同一性。
