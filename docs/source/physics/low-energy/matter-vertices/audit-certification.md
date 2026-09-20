# 完整物质源与原289交换的独立认证

**Verdict: certified。** 冻结的158个full252顶点、97个活跃源的原H289交叉项、18条local Ward恒等式、全四动量289双侧分解及带源回写全部独立通过。原prepared实源的24补块消失和轴向接触项也已由实际源重算，未发现候选修复项。

## 对象与权威

冻结对象是上一层 `compute.py / receipt.json / exact-check.log`、`exchange.py / exchange.json / exchange.log` 及 `README.md`。两程序 fresh replay 均 EXIT0，两份完整JSON与冻结回执完全相同；审计未修改候选、未提交。

固定 `positiveSmoothUnifiedSource`、Dirac-dual form-native作用及 `Stage9C.Material.SpinPair.actual`。`Stage10/Runtime/Occurrence.lean` 的 `visit=SpinPair.visit 10`、`entry=materialEntry (...)`、`tickAt 16` 与 `tickAt 17` 后继保持，`Activation.sameOccurrenceActivation` 保留同一整账及 `macroAnswerNext`。本认证是从属经典源／交换消费者，不声称controller推进。

输入采用既有已认证的 `active-gauge`、`canonical-active`、`full-phase` 与 `weak-exchange/spatial` 原作用和传播结果；没有重开这些关口。

## 原作用口与形式消费

[`Audit.lean`](Audit.lean) 直接消费原母密度的 `generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing`：完整kinetic与单向Y由同一独立复线性dual评价，并乘原volume。原连接affine定理进一步给出真实参数导数；原live coframe密度消费 `HasFDerivAt`，没有把目标Euler或壳条件放入输入。

独立消费者还验证FullPhase在任意live inverse coframe下给出 `+frequency·Γ_e Q`，保留实际定向第五对 `(3,1)` 的反号，并验证 `j(iξ,iζ)=−j(ξ,ζ)`。lowered连接的六对 `1/2` 公式由既有ordered-pair `1/4`定理支付。

strict `--trust=0 -DwarningAsError=true` 全 EXIT0；7个实际源口和6个独立消费者共13项公理检查，仅 `propext / Classical.choice / Quot.sound`。新增完整矩阵身份由下述精确符号计算认证，没有冒称它们已成为新的Lean全矩阵定理。

## 158个原顶点与Ward

[`independent_check.py`](independent_check.py) 不导入候选程序。从Lean原γ字面量、定向pairs、四项原vacuum、原color Pauli与独立bit外幂算法重建原表示、Y与背景连接。`N²=54/125`、原frequency、`Q=γ5+2P6`及正lapse均逐项一致。

48个gauge、24个lowered Lorentz、16个coframe、70个scalar顶点逐项等于冻结full252矩阵。coframe采用与候选不同的Jacobi公式：

```text
dvol[h] = N tr(e⁻¹h)
dadj[h] = N [tr(e⁻¹h)e⁻¹ − e⁻¹he⁻¹].
```

背景det正，故它们同时是原绝对volume的局部导数。Y体积项与graded phase均被保留；phase项在 `(0,1),(0,2),(0,3),(1,1),(2,2),(3,3)` 六个coframe方向非零，不能提前丢弃。

所有97个活跃玻色源与48个物质实坐标的4656项原占据腿逐系数一致，两侧Hessian方向及 `H(−p)ᵀ=H(p)` 同时检查。独立dual实配对为 `[[Re V,−Im V],[−Im V,−Re V]]`，Hermitian替换的反控制非零。

原四个formal动量与另外四个局部参数动量全部保留。12个native gauge与6个Lorentz的

`δD + N D(p+r)T − N T D(p)=0`

逐项为零，包含原背景交换子、Y、coframe变换与live graded time shift；未假定外腿on-shell。

## 289分解、源接触与完整回写

审计从原H289逐轮直接求出72维gauge B、72维gravity B／multiplier、24维Lorentz代数逆，独立重建 `−D⁻¹H_aux,retained`，再与原Schur写回核对。每一逆的两侧身份、消元后的两侧交叉为零均成立。九个scalar Ward方向产生真实可逆contact块；它们保留为source坐标。

完整F及其逆均无动量分母，双侧乘积为289维恒等；完整四动量验证

```text
F(−p)ᵀ H289(p) F(p)
  = diag(Mscalar9, A79, B24, 0local9, Dauxiliary).
```

每个97源的变换严格是 `f=F(−p)ᵀI j`。全部contact源、接触二次核、field response以及79／24字段lift逐项一致，原289行满足

```text
H289 Rc + L79 f79 + L24 f24 + Lnull fnull = I,
H289 F79 = L79 A79,    H289 F24 = L24 B24,
H289 Fnull = 0.
```

所以 `+j·field` 源约定下的诱导字段为 `−[Rc j+F79 A79⁻¹f79+F24 B24⁻¹f24]`，相容条件 `fnull=0` 支付全部原方程。九行相容map真实非零，未被删除。对应树交换的整体符号是 `−1/2`。

省略 `−p` 转置、反转诱导字段符号均给出非零反控制。两个已认证的原weak五源lift被实际映入同一F，其完整五维作用逐项恢复，且其补块源及null相容行均为零。

## prepared实源与轴向接触

原independent-dual的f24仅从真实Lorentz连接源进入。其中12枚full252补块顶点确实非零；因此该补块没有被独立dual理论删除。该source map为常数，spin顶点也无外腿动量，故这里没有把不同p／q的coframe顶点Hermitian化问题混入消去。

对实际 `χ=√2 ξ†S` 制备，source矩阵是 `√2(SV+V†S)/2`。全部24枚补块矩阵恒等为零。24个实际prepared spin源以独立Hilbert–Schmidt投影准确落在四个Hermitian矩阵 `√2 Sγaγ5` 上，投影map秩为4。

直接从原24维连接块重新求双侧逆，得到

```text
Caxial = spinMapᵀ Dω⁻¹ spinMap = (3N/8) diag(1,−1,−1,−1),
Lspin,contact = (3N/16) [−(A⁰)²+(A¹)²+(A²)²+(A³)²],
Aᵃ = √2 ξ†Sγaγ5ξ.
```

审计把 `ωinduced=−Dω⁻¹ spinMap·A` 实际代回24行方程和原二次作用；缺少Hermitian化的 `1/2` 或反转contact符号均不相同。

认证范围是原97活跃源的经典树交换normal form，动态逆接口在相应可逆域并保留相容行。外围61个scalar的交换、完整物理外态与经验单位不由本回执代填。

## 可复验入口

- [`replay.log`](replay.log)：两份冻结程序 fresh replay，完整JSON逐项一致。
- [`independent-check.log`](independent-check.log)、[`independent-receipt.json`](independent-receipt.json)：完整符号核验与反控制。
- [`Audit.lean`](Audit.lean)、[`lean-audit.log`](lean-audit.log)：原作用口strict消费及13项标准公理检查。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/matter-vertices/compute.py --root . --out /tmp/matter-vertices-audit-replay.json
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/matter-vertices/exchange.py --root . --out /tmp/matter-exchange-audit-replay.json
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/matter-vertices/audit/independent_check.py --root .
cd Lean
lake env lean --trust=0 -DwarningAsError=true ../Verification/physics/low-energy-phenomenology/matter-vertices/audit/Audit.lean
```
