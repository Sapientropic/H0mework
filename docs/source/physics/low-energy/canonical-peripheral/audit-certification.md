# 原外围 canonical 最大发展纤维独立认证

**Verdict: certified。** 冻结源发生器、FullPhase 接缝与完整轴向分类均通过，没有候选修复项。一般／原点／两个非零例外纤维的最大维数分别为 **522／524／530**；非零例外处保留秩8的实际标量—物质混合。

## 冻结对象与来源

本证书覆盖上一层 `compute.py/generator.json`、`phase_match.py/phase-match.json`、`closure.py/closure.json` 及 README。三程序 fresh replay 均 EXIT0；完整数据与冻结回执相同，closure 只排除运行耗时字段后比较。

原 `positiveSmoothUnifiedSource`、Dirac-dual action、`SpinPair.actual`、visit10／tick16／materialEntry 与 tick17 后继保持。本组从属同一源的线性发展消费者。外围原1021个实字段由61个标量、480个 primal、480个独立 dual 构成；加入61个标量速度后是一阶1082维载体。

新发生器与 Smith 分类属于精确符号程序结果。[Source.lean](Source.lean) fresh `--trust=0 -DwarningAsError=true` 通过，核对其消费的9个正式公开源口，传递公理均只有 `propext`、`Classical.choice`、`Quot.sound`：FullPhase 的真实场、Y／M、制备与时间导数，ScalarBlock 原 Euler，原 scalar Yukawa 源，以及原 spin current 投影。未把完整矩阵分类冒称为新增 Lean 定理。

## 独立生成真实时间算子与实化

[source_check.py](source_check.py) 不导入候选程序。它直接消费[已独立认证 FullPhase](../../full-phase/audit/certification.md) 的原252维 `Cμ,K,M`，重新生成

```text
Aprimal,0 = −C0⁻¹ K/(N√2),
Adual,0   =  C0⁻ᵀ Kᵀ/(N√2),
Aprimal,j = −C0⁻¹ Cj/N,
Adual,j   = −C0⁻ᵀ Cjᵀ/N.
```

全部时间和三个空间系数逐项匹配冻结发生器。原频率满足 `ω/(N√2)=3/5`，并显式核验 `C0⁻¹=N²C0` 的左右逆。dual 保留独立复线性对偶：空间系数提供了把转置误换为 Hermitian adjoint 会失配的非零反控制；该背景的常数 K 恰为实矩阵，不能仅靠常数项区分两者。

原标量三个背景生成元从当前 `sourceColorPauli` 字面量和独立 exterior bit 算法重建。原 scalar Euler 的 `−Δ−2` 与原 Yukawa 变分给出，在 `τ=N√2t,k3=√2q` 下，

```text
ηττ − Σj(i q δj3 + (3/5)ρj)²η − η
  + (1/2) R(M)ᵀ diag(I252,−I252) R(Z) z = 0.
```

使用 `η=√2 E a` 的真实框架、实际时间主部的 Gram 左逆，独立生成全部70个 scalar、504个 primal、504个 dual 原未投影 Euler 行，再由这些行生成完整132维发生器，逐项一致。删去独立 dual 配对的负虚部块会改变原 scalar force，反控制非零。

canonical 图直接从原 `χ=√2ψ†S` 得到列坐标 `ζ=√2Sᵀ conjugate(ξ)`；源 S 的对称性另行核验。实化时的内部共轭 `diag(I24,−I24)` 被明确保留，不能省去。外部 Fourier 因子在实化之后加入，核验 `A(−q)=conjugate(A(q))`，没有把这两个虚数责任合并。

## 真实外围分解与518维旁块

独立检查两套24复维作用框架的满秩、实际左逆、全部时间／空间不变性，以及 M 的九个非零列和复秩9。原 H 投影与两作用框架正交；补投影各为216复维、幂等自伴，并与各自全部时间／空间系数交换。

原 `Y Pfree=0`、primal 侧没有混合反灌、free dual 侧没有 scalar force，均逐项成立。原 S 将 primal free 子空间映到 dual free 子空间，canonical 图在全部系数下保持，因此864个独立实物质坐标留下432个 prepared 一阶坐标。

对原43实标量核，重新核验满秩、`M F=0`、`JᵀF=0` 和三个背景生成元不变性。18实混合标量也满足 `JᵀE_R=0`，两部分正交且联合秩61，确实张成完整 `J⊥`。原43标量加速度的86维发生器也逐项一致。于是实际分解为 `86+132+864=1082`，两旁块的 prepared 维数为 `86+432=518`。

## 完整导约束与 Smith 完备性

[closure_check.py](closure_check.py) 从已核验 A、C、D 独立重算 `B=(AC)前84行` 和 `E0=DAC`，核对 `DC=0, AC=CB+LE0`。C 的前84行是恒等，D 的末48列是恒等，故 `im C=ker D`；没有用投影删除原补方程。

独立依据 B 及全部 E0 行的支撑重新生成13个分块：`2,2,4,4,8,8,8,8,8,8,8,8,8`。每个 n 维块均计算完整 `E0 B^j,j=0,…,n−1`，没有使用候选的提前停止条件作为充分性依据。

审计额外生成并保存显式多项式左右矩阵 U、V，核验

```text
U O V = SmithDiagonal,
det U、det V ∈ Q(i)×.
```

随后逐项证明完整高阶导约束经 V 变换后被对应 Smith 对角多项式整除，零对角列也仍为零。因而所有补查导约束都属于候选有限 O 的**同一 Q(i)[q] 行模**，包括所有例外点；这比一般动量的数值秩相同更强。Cayley–Hamilton 将 n 阶以后的条件归回这些有限导约束。

非单位因子恰为八份 `q²−5929/3600`，以及最后一块的两份 `q`。全部复根及重数经过精确因式分解与次数相等核验，实例外集合完整为 `0,±77/60`。显式变换及其单位 determinant 保存在 [smith-witnesses.json](smith-witnesses.json)，不是仅保存一次 Smith 函数返回的因子名称。

## 最大性、充分回写与实际混合

| 实轴向 q | 作用块最大维数 | 外围最大维数 | 原 Mη 秩 |
| --- | ---: | ---: | ---: |
| 不在三个例外点 | 4 | 522 | 0 |
| 0 | 6 | 524 | 0 |
| ±77/60 | 12 | 530 | 8 |

每一类都直接核验满秩 W、`AW=WG`、`DW=0`，并用独立完整导约束的秩证明其维数达到必要核的上限。因此既有真实发展充分性，也有最大性。每个 W 同时回写全部70+504+504个原 Euler 行；非零例外的 Mη 秩8取自原 M 的真实输入，未改用质量 Gram。

四类限制发生器的特征多项式与候选完全相同：一般为 `(X²+(q−12/5)²)(X²+(q+12/5)²)`；原点为 `(X²+144/25)³`；非零例外为 `(X²+529/3600)⁴(X²+4489/3600)(X²+48841/3600)`。

±q 的基空间互为复共轭，原点及一般常基空间也满足真实场恢复条件。因此这里计数的是原实字段 Fourier 复化后的纤维维数；原点同时给出真实齐次 Cauchy 维数。

原始标量速度基向量 `a′0=1` 在 q=0 满足 `Dw=DAw=0`，却有 `DA²w≠0`，其具体原132坐标和非零第二导约束重新核验。它直接拒绝把瞬时制备兼容核当作发展空间。

原坐标恢复始终为 `At=N√2 Aτ`，`η=√2Ea,ξ=Pp,ζ=Zz`，物质还需乘回原 U、V；两个非零例外的原 `k3²=5929/1800`。本证书签收整条实轴上的最大 prepared 子类，没有将其推广到整个独立 dual 理论或所有空间方向，也没有把 X 当作实验能量。

## 证据与复算

- [源检查输出](source-check.log)、[源回执](source-receipt.json)：原系数、全部 Euler 行、132发生器、1082分解及符号反控制全 PASS。
- [闭包检查输出](closure-check.log)、[分类回执](closure-receipt.json)：全导约束、显式 Smith 变换、最大性、真实场恢复及非传播反控制全 PASS。
- [源公开口 strict 与公理输出](source-lean.log)：EXIT0，9项标准三公理。
- [发生器重放](generator-replay.log)、[相位重放](phase-replay.log)、[闭包重放](closure-replay.log)：均 EXIT0。
- 审计只新增本目录文件，没有修改候选或提交。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/canonical-peripheral/audit/source_check.py --root .
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/canonical-peripheral/audit/closure_check.py --root .
cd Lean
lake env lean --trust=0 -DwarningAsError=true ../Verification/physics/low-energy-phenomenology/canonical-peripheral/audit/Source.lean
```
