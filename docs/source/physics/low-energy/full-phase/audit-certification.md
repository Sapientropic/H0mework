# FullPhase 完整分级相位独立认证

**Verdict: certified。** 三枚冻结 Lean 核心、完整252常系数读回及五类量子频移均通过；没有候选修复项。

## 原源与对象

候选为 `LowEnergyFullPhase/{Operator,Preparation,Derivative}.lean`，以及本轮另行冻结的上一层 `compute.py/receipt.json/README.md`。矩阵输入消费已认证的原 H289、232维制备投影和原外幂载体。原 `positiveSmoothUnifiedSource`、Dirac-dual action、actual、visit10/tick16/materialEntry及tick17后继保持。

这是同一场的可逆分级表示变换，没有改变原时间或独立 dual 字段域。外围 canonical 联立不变空间没有由本证书代填。

## Lean 核心与实际源消费者

`Operator` 对原 Λ6／其余两级分别给出固定 rate，生成真实双侧 inverse。`gamma_preserved` 和 `yukawa_preserved` 使用原 gamma 与原 right-chiral Yukawa，对全部 scalar 参数成立；没有改用 Hermitian completion。`original_matter` 消费实际场；`original_mixing_stationary` 保留 M0 的完整值。

`Preparation` 证明 `J(Uψ)=Jψ∘V`，包含原 s 的制备关系保持。独立消费者补核原 `actual.conjugateMatter=χ0∘V`，而非仅核对任意 abstract preparation。

`Derivative` 从原 `phase_hasFDerivAt`、两个有限 coefficient 槽和真实 linear/continuous-linear map 生成 `matterCoordinateEquiv` 中的 holonomic 导数。它先证明 `HasFDerivAt` 再读取 `fderiv`，没有使用不可微时的默认零值。其公开口是固定 test matter 的真实 phase derivative；对原 actual 取实际 seed 的消费者进一步核验整个原 matter 场导数。

原 generator 是 `Q=γ5+2P6`，得到 `V iγμ U′=ω γμQ`。独立 Lean 消费者将该恒等式实际用于任意 `inverseCoframeDiracGamma geometry coordinate`，证明 live coframe 下相同的 Γ组合，而非只查背景矩阵。另有两项 source 反控制：变换后的原 mixed witness 对每个 point 仍非零；在该同一非零方向上删去2P6会改变 generator。

25个公开候选声明及8个独立消费者，共33项传递公理检查，只有 `propext`、`Classical.choice`、`Quot.sound`。三候选与独立 Audit fresh strict 全 EXIT0。

## 全部252系数的独立重建

[`independent_check.py`](independent_check.py) 不导入候选程序。它直接解析冻结 Lean 三个 rate 定义，得到：

| 分级 | primal 上／下手 | dual 上／下手 |
| --- | --- | --- |
| Λ6 | −ω／−3ω | +3ω／+ω |
| Λ2、Λ4 | +ω／−ω | +ω／−ω |

原 source 参数另由 `N²=54/125,κ²=2,α=3κ/5` 重算 `ω=3N(κ−α)/2=18√15/125>0`。所有 phase support 在 Laurent 变量 `z=exp(iωt)` 中检验；其共轭规则由原实 rate 的 phase-star 定理支付。

从原 γ 字面量、四项 v 和独立 exterior bit 算法重新生成全部 Cμ、B、Y及35枚标量基顶点，逐项对照冻结矩阵。全部满足 `V Cμ U=Cμ`、`V B U=B`、`V Y(η) U=Y(η)`。M由35个真实 `Y(η)ψ0` 列生成，复秩9，且 `V z⁻¹ M=M`。

真实 phase derivative 逐条给出正号时间项 `ωΓ_e⁰Q`，其中 Q在 gamma 右侧。独立反控制验证 Γ0Q不能换成QΓ0；沿全部外幂级机械沿用旧 ungraded R 会留下 `z⁻²Y`，不能得到所声称的常系数。

两份实际背景满足 stationary primal 与 independent-dual 方程。Hamiltonian 明确读回为

`Hstationary=Horiginal−ωQ`，`[Horiginal(k),Q]=0`。

这包含实际常数项和三个动量系数。原232维制备投影与Q交换，free H0的 phase shift 仍 Hermitian。该结论保持既有固定scalar制备范围。

## 原289与完整量子响应的直接消费

独立程序按原 field labels 重新取出 H289 中24实 dual／24实 primal 的固定连接子块。以独立 dual 配对 `diag(I,−I)R(D)` 重新生成四个 derivative 系数和一个常数系数，共五个24×24矩阵，逐条完全相同。

完整响应为 `ζ V A U ξ`；canonical 子类通过 `S V=U†S` 得同一值 `s ξ†U† S A Uξ`。按独立解析的 rate 人口重算全部252²个算子坐标：

| 频移／ω | −4 | −2 | 0 | 2 | 4 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 算子坐标数 | 1568 | 15876 | 28616 | 15876 | 1568 |

总数63504。它们是算子坐标的五类相位频移，并非五个物理能级或完整动力谱的全部频率。

原背景响应独立核验为 `I → 2s(z²+z⁻²)`、`S → 4s`；在 z=i 时前者为−4s，后者保持+4s，反控制拒绝把两种原读数混同。

在Q=q分量上，`Eoriginal=Estationary+ωq`；若用时间指数λ，则 `λoriginal=λstationary−iωq`。程序实际检查Hstationary不同于Horiginal，因此没有把 shifted/quasi 参数直接改称原分量频率或实验能量。

## 回执

- [`focused.log`](focused.log)、[`Audit.lean`](Audit.lean)、[`lean-audit.log`](lean-audit.log)：三候选和独立消费者严格通过，33项标准公理检查。
- [`replay.log`](replay.log)：新冻结程序重放 EXIT0，完整 JSON 与冻结 receipt 一致。
- [`independent-check.log`](independent-check.log)、[`independent-receipt.json`](independent-receipt.json)：直接 Lean rate 读回、原252系数、35个顶点、非零M、真实Hessian子块及63504个算子频移全 PASS。
- mouth lint 只有仓库既有 `autoImplicit false` 提示。候选无 `sorry`、`admit`、新增 axiom 或 `native_decide`。审计未修改候选、未提交。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/full-phase/compute.py --root . --out /tmp/full-phase-audit-replay.json
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/full-phase/audit/independent_check.py --root .
cd Lean
lake env lean --trust=0 -DwarningAsError=true ../Verification/physics/low-energy-phenomenology/full-phase/audit/Audit.lean
```
