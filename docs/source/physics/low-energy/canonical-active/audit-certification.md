# Canonical 活跃块的完整方程与商认证

**Verdict: certified。** 原112行在88维 canonical 切向上的闭合、完整回写、全四动量79维多项式商及同源五态发生消费者均通过独立认证，没有候选修复项。

## 对象与继承来源

候选为 `LowEnergyCanonicalActive/{Phase,Readback}.lean` 和上一层 `compute.py/receipt.json/README.md`。原 H289→H112 来自[已认证的原作用及 Ward 消元](../../active-gauge/audit/certification.md)；九个源切向来自[已认证的主部／对称列](../../active-gauge/principal-audit/certification.md)。它们分别是三个原色 SU2 与六个 Lorentz 方向，没有添加四个 diffeomorphism 核。

原 source、独立 dual action、actual、`visit 10 / tick16 / materialEntry` 和 tick17后继保持。本组是原制备子类的从属方程 producer／transporter，不替换整个独立 dual 理论的字段域。

## 原 canonical 切向与全部112行

`Phase.canonical_rotation` 使用原 upper/lower phase 和完整 canonical adjoint，证明对任意252复维 matter 都有 `J(Rψ)=(Jψ)R`；原 s=√2 由 `scaled_canonical_rotation` 保留。独立 Lean 消费者也核对 `J(iψ)=−iJψ`、H12 的相位消费和实际尺度回写实例。

因此原实化坐标上的切向确为 `L=s diag(S₁₂,−S₁₂)`，而非遗漏虚部负号的矩阵。独立 checker 从 Lean 原 `diracAdjointSpinSwap` 字面量重新构造 L、C、Cminus 与 R，并核对原112字段的 group、顺序和所有系数。

完整四动量多项式恒等式为：

```text
K = Cᵀ H112 C
Cminusᵀ H112 C = 0
Cᵀ R = I88
H112 C = R K
```

审计另显式构造补行回写 Rminus，并验证 `R Cᵀ + Rminus Cminusᵀ = I112`。Cminus 是与 C 组成可逆坐标变换的补空间，不是正交补；本次没有错误使用正交投影推导。

`Readback.whole_rows_zero_iff` 是明示闭合／忠实前提的通用消费者；上述实际矩阵计算支付相应前提，没有把这个通用定理误称为 source Hessian 生成器。独立 Lean 反控制同时证明：一个 pullback 可以为零，而原完整行仍非零，说明额外24行必须另算。本候选已逐项算为零。

## 全四动量的79维忠实商

独立审计先重算 `T112=C t88`、`H112 T112=0` 和 `K t88=0`，再从 t88 的真实常数行重新求 pivot。得到同一删除坐标 `[49,50,51,54,55,59,64,76,77]` 和实际 minor `−1/8`；未向矩阵构造供应79这个期望秩。

由该常数 minor 生成 U、section E 与 quotient Q，独立精确核验：

```text
U t = I9        Q E = I79        Q t = 0
E Q + t U = I88
A = Eᵀ K E
K(p) = Q(−p)ᵀ A(p) Q(p)
K(p) E = Q(−p)ᵀ A(p)
```

所有条目均按四个独立 p 的多项式解码；多项式强制转换拒绝动量分母。这是全四动量的符号身份，未退化为轴向抽样。

一般可逆性另外用独立素数域消元检验。在 `p=(2,0,0,i)`，A 的模素数秩为79、行列式非零，并与冻结 exact determinant 的模像一致。使用素数1000000009及已核验的 √2／√15／i 根，逐项检查 primitive element 最小多项式和全部遇到的有理分母。非零特化给出一般秩下界79，矩阵维数给出上界；未用浮点秩。

79是该制备子类模去已验证九个源对称方向后的 faithful 坐标数，不是传播极化数。

## 同一五态发生的真实微分消费

审计使用原 H289、同一 J₅ 和真实289×5 lift F，重新核验：

- 原 primitive F112 确实等于 C F88，canonical 条件没有丢独立 dual 分量。
- 原289行、Ward112行、canonical88行全部消去 `F exp(tJ₅)`。
- `F79=Q(∂t)F88` 通过多项式系数与真实 J₅ 幂生成；它不等于冻结 `Q(0)F88`，该误用被独立反控制明确检测。
- A 的全部79行消去 `F79 exp(tJ₅)`，并由 E 与真实 source symmetry differential operator 重构 F88。
- F79 的 H／b 两列严格为零，给出值秩上界3；独立模素数秩为3。加入一次时间 jet 后模秩为5，结合五列上界给出精确 jet 秩5。
- 原 `λ²=50/3` 的增长向量是同一 J₅ 的特征向量，79维读回非零，并直接代入 A(λ,0,0,0) 得零。此前全部289行消费保持。

因此增长切向确属当前 canonical 子类，并且没有被九维源对称商消去。这里签收的是实际 Jacobi 发生及其方程等价，不扩大为全部 physical 外态或完整79维传播因子的识别。

## 机器证据

- [`focused.log`](focused.log)：Phase、Readback fresh `--trust=0 -DwarningAsError=true` 全 EXIT0。
- [`Audit.lean`](Audit.lean)、[`lean-audit.log`](lean-audit.log)：4个候选公开声明＋6个独立消费者／反控制，共10项公理检查，仅 `propext`、`Classical.choice`、`Quot.sound`，严格编译 EXIT0。
- [`replay.log`](replay.log)：原程序重新运行通过，完整 JSON 除运行时间外与冻结 receipt 一致。
- [`independent_check.py`](independent_check.py)、[`independent-check.log`](independent-check.log)、[`independent-receipt.json`](independent-receipt.json)：不导入任何候选生成器，使用独立稀疏多项式算法、源 S 实化和模素数消元；全 PASS。
- 候选无新增 axiom、`sorry`、`admit` 或 `native_decide`；审计未改候选、未提交。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/canonical-active/compute.py --receipt Verification/physics/low-energy-phenomenology/active-gauge/receipt.json --symmetries Verification/physics/low-energy-phenomenology/active-gauge/symmetries.json --out /tmp/canonical-active-audit-replay.json
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/canonical-active/audit/independent_check.py --root .
cd Lean
lake env lean --trust=0 -DwarningAsError=true ../Verification/physics/low-energy-phenomenology/canonical-active/audit/Audit.lean
```
