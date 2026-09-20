# 实际在壳源与完整弹性交换核独立认证

**Verdict: certified。** 冻结的八变量源 Ward、实际正 helicity 四外腿、完整79动态响应、两种源排列及原289行回写均通过，没有候选修复项。

## 对象与依赖

对象为上一层 `compute.py/receipt.json/README.md`。fresh replay EXIT0，完整 JSON 与冻结回执相同。输入消费[完整源／交换认证](../../matter-vertices/audit/certification.md)和[已完成独立认证的 matter-modes](../../matter-modes/audit/certification.md)，后者的 F、块标签、Q 和双侧原 Dirac 外腿接口均已签收。

原 source、修复 Dirac-dual action、actual 及 controller root/current/next 保持。本组是从属在壳源消费者，没有新 Lean 声明或公理；新增完整矩阵结果属于精确符号计算，不冒称新的 Lean 全矩阵定理。

## 全部八变量源身份与原 coframe 导数

[source_check.py](source_check.py) 不导入候选模块。从正式 γ、实际定向 Lorentz pairs（包含 `(3,1)`）、当前 color Pauli 与独立 bit exterior 算法重新生成12个 native P286 和6个 Lorentz 算子；D直接由已认证 FullPhase 的四个 Cμ 和常数项生成。

对原实际 null9 map 与 broken scalar-contact9 map，各自逐项核验完整252矩阵身份

```text
SourceMap(r) V(p) = N[T D(p) − D(p−r) T].
```

审计独立展开全部 p0…p3、r0…r3 系数：常数项为 `N[T,K]`，pμ项为 `N[T,Cμ]`，rμ项为 `N CμT`。没有预先代入轴向或壳条件。把 transfer 改成 p+r 的非零反控制明确拒绝相反符号。

全部16个 coframe 顶点另从实际正 coframe 的

```text
dvol[h] = N tr(e⁻¹h),
dadj[h] = N[tr(e⁻¹h)e⁻¹ − e⁻¹he⁻¹]
```

重新生成，并保留 `dvol·Y`、原 gauge/spin 连接和 `+ω Γ_e⁰Q`。它们与冻结顶点逐项相同。158个原 `S V_b(p)` 全部与自伴 Q 对易；其 Hermitian 伴随部分也因此保持相同 Q 选择律。

## Hermitian 源的两条真实腿

原制备的复 Fourier 系数为

`j_b=√2 uout†[S V_b(pin)+V_b(pout)†S]uin/2`。

这里 p 是实际 primal 导数，`p0=−i Estat,pj=i kj`，transfer 是 `pin−pout`。第二项使用 pout，不能把 pointwise 同一波函数的 Hermitian 表达式机械改成两边都用 pin。

第一部分由输入 primal 壳与输出 independent-dual 壳归零；第二部分使用反向身份的伴随，由输出 primal 壳与输入 independent-dual 壳归零。自由 F 接口实际支付每条腿的两份原方程；审计也逐腿重验，再将两部分分别代入两套九行 map，均为零。原 map 的系数实性和 signed transfer 一并保留。

反控制直接把两侧 coframe 顶点都代入 pin，所得源不同，且其 null9 条件实际非零。这排除了只靠合并后一次数值抵消来供应壳条件。

全部70个 scalar 顶点重新满足 `F†S Vscalar=0`。24个补块 source map 是原常数 map；其每个组合顶点满足 `S W+W†S=0`，因此 prepared 实源的消失是算子身份，而不是删去原独立 dual 方程。

## 由实际 F 生成的非空四外腿

原块表按源规则取第一个 right Λ4 singlet（F列146起）和第一个 right Λ2 singlet（F列120起）。审计检查实际列支撑的外幂级、right chirality、Q=1、正交单位性及三个 color 生成元的湮灭；没有只相信标签。

正 helicity 投影的旋量从其第一个非零列归一化生成，再用原完整 spin 矩阵 `−iγ2γ3,−iγ3γ1,−iγ1γ2` 检验正 helicity。四腿实际为

```text
Λ4: +z/√2 → +x/√2,
Λ2: −z/√2 → −x/√2.
```

各腿同时满足原 full252 primal／independent-dual 壳、Pfree归属、单位 coordinate 范数及原 Hamiltonian 本征方程。原能量均为 `2N√2`，共转能量为 `2N√2−ω`。总原能量和三动量守恒；两个 source transfer 恰好相反且时间分量为零。

两条97维源都非零。全部158个原顶点的跨 Λ4／Λ2 transition 均实际为零，包括外围 scalar 顶点；因此该通道的物种交换顶点消失有源矩阵依据。Q相同则原与共转能量转移相同，没有把共转频率重新命名为原能量。

## 原79算子与两份289响应

[exchange_check.py](exchange_check.py) 从原 H289 与真实场 lift 重建

`A79(r)=L79(−r)ᵀ H289(r) L79(r)`，

并从原 injection 重算两条 f79，逐项等于冻结接口。第一条保存的响应直接代回 A79。审计另外求解未存于候选的第二条源在相反 transfer 下的响应，采用原精确数域 `Q(√2,√15,i)`；两条原源均非零。

该点的 A79 非奇异有独立模素数证据：在素数1000000009上，以满足三个平方关系的像代入，全部实际有理分母均可逆，得到 determinant 像266255995≠0。映射及所用平方根像保存于回执，因此没有用“给出了一个解”代替动态逆的可逆域核验。

两条响应都加回原 contact field response，再分别支付全部289行：

```text
H(r) F1 = I j1,
H(−r) F2 = I j2.
```

正号源的诱导字段为−F；反转此符号的实际原方程残差非零。

## 两排列、接触项与直接系数

完整 signed-transpose 身份 `A79(−r)ᵀ=A79(r)` 和 `Ccontact(−r)ᵀ=Ccontact(r)` 被保留。审计分别计算两次实际源赋值，得到

```text
D12 = D21,
C12 = C21 = −9√30/50,
−½(D12+D21+C12+C21) = −D12−C12.
```

两个值还分别等于直接以另一源读出原289字段的结果；没有只在79子块中宣布相等。只取一次赋值留下错误的1/2；把 Fourier 双线性转置改为共轭转置也给出不同结果，均有非零反控制。

逐接触块检查显示该消费者只有原 Lorentz 接触非零，其余 gauge B、gravity B／multiplier、scalar Ward 接触均为零。独立从原 γ 重建四个轴向矩阵 `√2Sγaγ5`，以原 `(3N/8)diag(1,−1,−1,−1)` 再算同一接触，得到 `−9√30/50`。

最终直接系数确为

```text
−18908441674971446080024956804334794870926877 √30
 /22888622062870338716613170707981015089514850.
```

这签收上述 coordinate-unit 外腿的完整树级源系数；没有把它等同于已完成外腿留数／LSZ归一的散射幅或实验截面。

## 证据与复算

- [replay.log](replay.log)：冻结程序 fresh EXIT0，完整 JSON 相同。
- [源检查](source_check.py)、[输出](source-check.log)、[回执](source-receipt.json)：原八变量身份、真实 coframe 导数、四外腿、两部分壳条件及原接触全 PASS。
- [交换检查](exchange_check.py)、[输出](exchange-check.log)、[回执](exchange-receipt.json)：原79重建、非奇异证据、相反 transfer 求解、两份289回写及两排列全 PASS。
- 只新增本 audit 目录文件，没有修改候选或提交。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/onshell-sources/audit/source_check.py --root .
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/onshell-sources/audit/exchange_check.py --root .
```
