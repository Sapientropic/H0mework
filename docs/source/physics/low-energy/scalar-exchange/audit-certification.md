# 外围标量完整源交换独立认证

**Verdict: certified。** 冻结的61维标量双侧投影逆、原非零Yukawa混合返回、全部原scalar／primal／independent-dual行及70标量源接缝独立通过。没有候选修复项。

## 对象与来源

本次对象为上一层 `compute.py / receipt.json / README.md / exact-check.log`。fresh replay EXIT0，完整JSON与冻结回执一致；候选未修改，未提交。

保持 `positiveSmoothUnifiedSource`、原Dirac-dual form-native作用、原actual及FullPhase同一可逆分级表示。`Stage10/Runtime/Occurrence.lean` 仍为 `SpinPair.visit 10`、`materialEntry (...)`、`tickAt 16` 与 `tickAt 17` 后继。本组是从属经典源响应producer／readout，没有controller推进。

直接消费已认证的 [ActiveSector](../../active-sector/audit/certification.md)、[实标量源核](../../real-scalar-sector/audit/certification.md)、[FullPhase](../../full-phase/audit/certification.md)。新增上游 [matter-vertices](../../matter-vertices/audit/certification.md) 已独立完成认证；其完整活跃交换的九行源相容条件在本组接缝中保留。

## 原投影与全四动量逆

[`independent_check.py`](independent_check.py) 不导入候选程序。从当前Lean的四项vacuum、γ／Pauli字面量及独立creation／annihilation bit算法重新生成外幂作用。

原12列实轨道的秩为9，重新求rref后取出的J与原J完全相同。以原实配对生成

```text
PJ=J(JᵀJ)⁻¹Jᵀ，P=I70−PJ，rank P=61。
Pd=−(4/3)(Σρi²)P，Ps=P−Pd。
```

两个实际正交投影分别秩36／25。三个 `2ρi Pd` 的平方、反交换和带原定向的quaternion乘积均逐项成立，故36实维为九个四实维块；25维上三个ρi全部为零。这是61维外围，不是旧的43维Yukawa核。

源标量Euler口为 `−N·covariantKleinGordon`，原inverseFactor为 `(-N⁻²,1,1,1)`。据此独立生成

```text
K(p)=(p0²/N²−2)I70−Σ(pj I70+αρj)²，原Hscalar=N K。
```

候选归一 `p0=N√2u, pj=√2rj` 与此精确相同。保留全部四个实微分参数验证 `NKG=GNK=P`、`PG=GP=G`、`G(−p)ᵀ=G(p)` 后，才作外部Fourier代入 `pj=ikj`。得到

```text
a=λ²/N²+|k|²−2，b=a+27/50，R(k)=Σkiρi P，
G=(1/N)[Ps/a+(bPd+2iαR(k))/(b²−α²|k|²)]，
N²=54/125，α²=18/25。
```

双侧身份是精确多项式身份及其分母非零域上的有理逆，不是轴向取样或浮点秩判断。

## 非零M及全部原字段回写

独立重建原252维的四个principal系数、原连接B、单向Y、`Q=γ5+2P6` 与真实正号相位项 `frequency·Γ0 Q/N`，全部与源FullPhase一致。35个真实 `Y(η)ψ0` 列给出复秩9／实秩18的M；同时直接验证所有 `χ0Y(η)=0`。

令 `DR` 为逐系数实化的原D，`MR=realify(M)`、`C=diag(I252,−I252)`。审计由原独立复线性dual作用实际组装1078×1078实Euler矩阵，顺序为scalar70／primal504／dual504：

```text
H=N [ K       0               MRᵀ C
      0       0               DR(−p)ᵀ C
      C MR    C DR(p)         0          ]。
```

全部有号转置身份成立。这里的C不能替换成Hermitian配对。完整70行scalar、504行primal与504行dual均进入消费者，没有把独立dual删成共轭背景。

M输出只落在28复维Λ6，原Y在Λ6输入上为零。独立union-find重新取得D6的五个4复维块及一个8复维块。各块另按手征非对角结构求2×2／4×4余子式，核对冻结复逆的左右乘积；随后逐系数实化，再核对实逆左右乘积及完整原Euler行。

每个回写块直接满足原dual-test行；所有其余行的关联项逐项为零。另有224个剩余复物质坐标明确检查 `Dother,6=0` 与 `Mother=0`，所有原scalar-to-dual变分由 `χ0Y(η)=0` 消去。最终Green列满足

```text
H F=(P,0,0)ᵀ，
正号外源的诱导字段：η=−Gz，ζ=0，ξ=+D6⁻¹ M Gz。
```

primal回写分子有80个非零条目；`MG`确实非零。单向Y使scalar读数不含额外Dirac分母，却没有删除真实primal返回。原内部复数先实化、外部Fourier后代入；反过来的操作已给出明确非零反控制。

外围与活块的隔离也实际消费：原12条scalar current腿乘 `DμP` 为零；88个原gauge／Lorentz／coframe顶点的占据腿 `χ0V|Λ6` 全零，包含实际coframe及graded phase系数。其余原辅助字段没有额外物质依赖，沿用已签收ActiveSector分离。

## 70源接缝与静态接触

70枚原scalar顶点重新生成且精确为 `N·Y(η)`，包括35个虚方向；没有漏掉原volume因子。它们与实际九个活跃scalar顶点逐列满足J投影。

```text
zJ=Jᵀz，z⊥=Pz，J(JᵀJ)⁻¹Jᵀ+P=I70。
```

`zJ`是对偶源，不能替换成坐标左逆 `(JᵀJ)⁻¹Jᵀz`。连同其余88源形成97×158完整源map，并实际接到已认证 `matter-vertices/exchange.json`；继承的9×158相容map仍非零。**合成完整原场响应的条件仍是这九行相容式为零，并在相应动态逆的可逆域内。** 本证书没有给任意外腿自动添加on-shell条件。

外围新增交换为 `−½ z⊥(−p)ᵀG(p)z⊥(p)`，与上游完整活跃交换相加无标量遗漏或重复。在原点

```text
G(0)=−Ps/(2N)−50Pd/(73N)，
Lscalar,contact=zᵀPs z/(4N)+25zᵀPd z/(73N)。
```

[`regular_point.py`](regular_point.py) 给出实际可逆点 `u=2,r=0`：scalar和全部六个D6块都可逆，故本口不空真。同一真实D6在原点的块秩为 `4,4,4,4,4,5`；因此标量Green有限不能解释成完整场逆可逆，也未从该分子／分母直接推断每个诱导字段是否有可去奇点。此处是原背景经典二次作用的源响应，不代填canonical非线性保持、物理外态或经验单位。

## 验收证据

- [`replay.log`](replay.log)：冻结程序 fresh EXIT0，完整receipt完全相同。
- [`independent-check.log`](independent-check.log)、[`independent-receipt.json`](independent-receipt.json)：独立源重建、原1078行、全四动量逆及全源接缝通过，耗时146.843秒。
- [`regular-point.log`](regular-point.log)、[`regular-point.json`](regular-point.json)：明确非空可逆域及原点实际秩通过。
- 六项反控制分别拒绝漏N、反转源响应符号、删除M返回、实化／Fourier混序、源covector错用Gram左逆及独立dual的Hermitian替换。

本组候选没有新Lean声明；上述新增全矩阵身份是精确符号程序证据，没有冒称新Lean端到端定理。所消费的Lean源口及标准公理集沿用对应已签收证书，无新axiom或信任逃逸。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/scalar-exchange/compute.py --root . --out /tmp/scalar-exchange-audit.json
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/scalar-exchange/audit/independent_check.py --root .
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/scalar-exchange/audit/regular_point.py --root .
```
