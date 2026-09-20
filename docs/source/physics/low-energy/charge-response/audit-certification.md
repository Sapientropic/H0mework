# 原静态十二电荷源及软留数独立认证

**Verdict: certified。** 冻结候选的12个原静态A0源、全289行强迫回写、144个零动量正则读数、相容源的canonical `q⁻²` 留数分解及全实方向的统一运输全部通过。有限方向极限非恒定、有限非零动量分母和两个原软相位均保留。

候选为上一层 `compute.py / receipt.json / README.md / exact-check.log`。fresh replay EXIT0，完整JSON与冻结回执一致。审计只新增本目录，未修改候选、未提交。原 `positiveSmoothUnifiedSource`、Dirac-dual form-native作用、`SpinPair.actual`、visit10/tick16/materialEntry→visit11/tick17保持；这是从属经典静态源响应，不新增controller authority。

## 由原算子生成极点系数

[`independent_check.py`](independent_check.py) 不导入候选程序，直接消费已认证的原canonical79算子、字段缩放S、两个源相位P和77个重方向E。静态全三动量设 `pj=i√2 qj`，重算 `G=S A79 S/N`。

原 `T=[P,E]` 有双侧逆，`G0 P=0` 且 `D0=EᵀG0E` 的77维双侧逆成立；`TᵀG0T=diag(0₂,D0)`，因此恰有两个soft方向。重轻两侧交叉在原点均为零，light块的0阶和1阶项也为零。独立从原矩阵系数计算

```text
K2 = (PᵀGP)₂ − (PᵀGE)₁ D0⁻¹ (EᵀGP)₁
   = |q|² diag(160/67,2500/81).
```

这不是从候选硬编码系数反推。D在原点可逆，所以精确Schur补在邻域内解析；其领先矩阵可逆。分块逆的 `q⁻²` 项只有light-light块，交叉因子在0处为零。恢复原作用密度后，该项为 `P K2(unit)⁻¹ Pᵀ/N`。所有 `−p` 只在原点取值时归为同一常数，未把有限动量的转置号忽略。

进一步从原289字段lift构造 `U0=Fcanonical(0) S P`，逐项验证

```text
U0−Z = Fnull(0) B,
B[2,0]=B[2,1]=2，其余为0；
Zᵀ I97=0，
U0ᵀ I97 = Bᵀ Cnull(0).
```

Z的非零项全部在原primal／independent-dual物质字段。故完整97源的canonical逆留数准确是

```text
Res = Cnull(0)ᵀ R9 Cnull(0),
R9[2,2] = 9023/(5000N)，其余为0。
```

原点Cnull核维数88，独立检查Res消去整个核；Res本身真实非零。准确量词是：源族j(q)在0有有限极限，并在邻域满足原 `Cnull(q)j(q)=0`，则其canonical `q⁻²` 留数为零。该命题不自动排除 `q⁻¹` 或有限项，也不对任意不相容源作相同断言。

## 原十二源与完整强迫方程

十二列按原H289的 `gauge_A`、时间坐标0和原native标签顺序选取，源项约定 `+ΣjT A0T`。全部静态轴向动量均满足原九行相容式，且原independent-dual补块源为零。

独立算法从真实103算子提取六个互相隔离的支撑块，直接求完整双侧逆，未复用候选的 `solve_den` 输出：

| 块维数 | 该块源数 |
| ---: | ---: |
| 2、2 | 各1 |
| 16、16 | 各2 |
| 30 | 2 |
| 33 | 4 |

两侧块外耦合为零、原字段缩放与N归一化、103响应列均逐项相同。随后直接使用原H289验证

`H289(p) Fcharge(p)=Icharge`，

全部三轮辅助字段的原行也为零。正号源对应诱导字段 `−Fcharge j`；反号测试确实不满足强迫方程。

原时间规范字段读数 `R=IchargeᵀFcharge` 满足 `R(−q)ᵀ=R(q)`。144项逐条约分，所有分母在0非零，完整R0与冻结结果一致，故 `lim q²R(q)=0`。回执保留多个非恒定动量分母，没有将其删除。完整289字段列仍有 `1/q` 项；正则性签收在该12×12源读数上。

有理逆与强迫回写先在相应分母非零处使用；R的零动量值是其约分后正则延拓，不等于宣称整个H289在0可逆。

## 全实方向与统一有界运输

从已认证的原289有限空间／spin／color矩阵逐条取出实际A0×12子块。三个轴的全部非零entry都保持该slice及其补空间；子块与参数反号的矩阵左右相乘均为I12。

每项实际形式为 `Σ_{m≤8} c_m z^m/[d(1+z²)^4]`，原d全为1。审计独立重建系数和冻结bound。

[`Audit.lean`](Audit.lean) 严格证明

```text
∀ z∈ℝ, m≤8, |z^m| ≤ (1+z²)^4,
|Σ c_m z^m/[d(1+z²)^4]| ≤ Σ|c_m|/d     (d>0).
```

它再直接消费原 `momentum_alignment` 的同一有限y、z，给每个非零实动量的对齐参数同时附上该界。strict `--trust=0 -DwarningAsError=true` EXIT0，4个独立消费者和原alignment共5项公理检查仅标准三公理。

字段顺序保持已签收的 `L=Sz(z)Sy(y)`，其charge子块U每个entry可统一界为400。由原 `LᵀH(pk)L=H(pa)` 和该slice的双向不变性，指定源读数运输为 `U Raxis Uᵀ`。U的界不依赖角度；Raxis在0的所有entry有界。因此任意实空间方向、包括随径向参数改变的方向，都有 `|k|²R(k)→0`，其中 `|k|²=2q²`。

有限极限本身没有被误报为方向无关。实际第二轴参数1/2给

`(U R0 Uᵀ−R0)[1,1]=6√30/625≠0`。

本结论是原背景、原源归一化的经典树级零动量Coulomb留数消失；不由此删除原soft模式或有限动量极点，也不形成全量子或非微扰no-go。

## 复验

- [`replay.log`](replay.log)：冻结程序 fresh EXIT0，完整JSON相同。
- [`independent-check.log`](independent-check.log)、[`independent-receipt.json`](independent-receipt.json)：独立Schur系数、六个直接逆、全289行、旋转bound及反控制全PASS。
- [`Audit.lean`](Audit.lean)、[`lean-audit.log`](lean-audit.log)：全实参数界与原任意动量消费者的严格核验。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/charge-response/compute.py --root . --out /tmp/charge-response-audit-replay.json
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/charge-response/audit/independent_check.py --root .
cd Lean
lake env lean --trust=0 -DwarningAsError=true ../Verification/physics/low-energy-phenomenology/charge-response/audit/Audit.lean
```
