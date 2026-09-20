# 原占据态规范响应独立认证

**Verdict: certified。** 冻结 H12 源算子、全部48个规范力／电流、全四变量独立 dual 图、两份12模 resolvent 及原289行消费者均通过，没有候选修复项。

## 冻结对象与来源

对象为上一层 `compute.py/receipt.json/README.md`。fresh replay EXIT0，除执行耗时外，完整 JSON 与冻结回执一致。原 source、repaired Dirac-dual action、actual、原时间和 controller root/current/next 保持。

本认证消费已有正式 full252 源系数、原289作用和其双线性顶点；没有读取未冻结的 FockDynamics 候选。这里新增的是精确矩阵消费者，没有新 Lean 声明、公理、真空圈测度或完整耦合量子理论认同。

## 实际 H12、制备与物理时钟

[source_check.py](source_check.py) 不导入候选模块。它从完整外幂基重建 H12 的12个实际索引和嵌入 F，逐项证明原完整 Dirac 四系数保持该空间。原正 lapse、frequency、independent-dual scale 均与已认证源一致。

实际 `spinPairCoefficients` 从当前 Lean 字面表读取，生成原 ψ0；它与原289背景数据完全相同。`w=ψ0/2` 的完整坐标范数平方为1。原 canonical dual 是 `s ψ0†S`，两侧背景 Dirac 方程均为零。

源 c0 的双侧逆生成 h0／Hj；四个系数 Hermitian 且与 Q 交换。直接由原完整 Hamiltonian 核验

`Horiginal(k)|H12=h(k)+ωQ`。

实际 w 的两个 Q 分量各有范数平方1/2、原频率−ω／+ω，按原 `phase(rate)=exp(i rate t)` 恢复 actual 的 upper／lower 两相位。审计同时确认 h0 非零、整个 `Horiginal(0)` 不等于 ωQ，因此时钟认同确切限定在生成的制备轨道，而不是全部任意状态的算子身份。

## 原48个力与current

由当前原 γ 和独立 bit exterior 算法重建12个 native P286 生成元。48个 densitized 顶点逐项生成为 `VμT=N Cμρ(T)`，与上游顶点相同。

在完整252载体及其实际 H12 限制上，审计核验

```text
Tc=γ0 Vc,
Bc=s HermitianPart(SVc)=−s QTc.
```

两类矩阵各自 Hermitian，Tc与Q对易，全部保持H12。B是原作用对规范字段的实current读数，T是实际时间方程的发生器；二者不能直接混同。原 forcing 为 `−iTcψ0`，reader seed 为 `Bcψ0`，没有用单位 w 替换原幅度2。

## 原实化与全部独立 dual 行

审计依据实际 field labels 验证 Re／Im／spin／color 的坐标顺序，直接从原 H289 提取 M48、HmA、HAm。另从原 `Re ζDξ` 及真实双线性源独立重建三块：

```text
M48(p) = [[0, N R(D(−p))ᵀc], [N c R(D(p)), 0]],
c=diag(I12,−I12).
```

48列 HmA 也由每个真实 `c R(V)` 的两条原背景腿直接生成，和原 H289 逐项相同。没有只查候选内部自洽。

canonical 图 `L=[I24;s R(S)c]` 及 C 从原时间系数生成。全部四个实 formal derivative 变量上支付

```text
M48 L=C KR(p),
HmA=−C f,
HAm L=[Bseed†,Bseedᵀ] Split.
```

C 的实际列秩24，原 independent-dual 方程完整保留。先做内部实化、再代入外部 Fourier `p0=−iE,pj=ikj`；把这两步颠倒，或省去 dual 图中的内部共轭 c，都会产生非零反控制。

## 有序双resolvent与全变量接口

`Split=[I,iI;I,−iI]` 及实际逆的两侧乘积精确为恒等。独立全四变量核验

```text
Split KR(pF) Split⁻¹
  =diag(−i(E−h(k)), −i(E+h(−k))ᵀ),
Split KR(−pF) Split⁻¹
  =diag(i(E+h(−k)), i(E−h(k))ᵀ).
```

因此在两个12维分母均可逆的域内，先由这些恒等式求出 `R(D(pF))⁻¹` 和 `R(D(−pF))⁻¹`，再利用上述 off-diagonal M48 的块结构得到其完整逆。其代入 canonical forcing 后给出

```text
Pi=Bseed† (E−h(k))⁻¹ Tseed
   −Bseedᵀ (E+h(−k))⁻ᵀ conjugate(Tseed)
  =−HAm M48⁻¹ HmA.
```

这是由全变量源身份和普通矩阵逆法则生成的接口，不依赖三个样本覆盖任意动量。域内可逆性的非空实例由下一组实际完整逆支付。

## 三份完整逆与289余项

[response_check.py](response_check.py) 没有调用候选的48维 solve。它直接求两个12模逆，按原 off-diagonal action 构造整个48维 inverse，并在每个冻结点核验 **左右乘积均为 I48**。这些点为纯时间、含非零 k3、以及后一项的频率／动量共同反向。

三个点的全部2304个电流条目均等于原 `−HAm M48⁻¹ HmA`；源场响应与冻结矩阵逐项相同。正反向 Pi 满足原 signed transpose reciprocity。

原规范注入加生成的物质响应后，全部289行实际余项重新生成并逐项核对。48个物质行完全为零，gauge行恰为 `HAA+Pi`。非物质余项确实非零：原 scalar J、gauge A、coframe、Lorentz 和 gauge B 均有保留的行，详细计数见回执。这证明原物质方程及current Schur块，没有把外加规范脉冲宣告成完整boson自洽解。

删去反向resolvent、以T代替B、反转物质响应符号、或以单位w替代ψ0，都在实际消费者上给出不同结果。使用单位w重新计算的Pi恰为原来的1/4，明确核验原幅度平方4。

## 非零条目与真实pole

审计采用与候选不同的算法：先由原 h0/ω 的五个本征值构造 Lagrange 多项式谱投影，核验其幂等性、本征身份和完备性，再组装正反两份resolvent。得到

`Pi00(zω,0)=−200√30/[27(z²−4)]`。

在 z=3，与原48维消元同样得到 `−40√30/27`。该标量读数在 z=±2 的实际留数分别为 `−50√30/27,+50√30/27`，因此没有把它们约掉或当成普通可逆点。其他原12维谱分母也由完整resolvent保留，单个条目的取消不代表整个矩阵取消。

另对 `E=3ω,k3=ω/N` 直接重算正向分母，秩恰为11，并取得非零一维核见证；不在该点使用普通 inverse。

本证书签收原占据物质的规范脉冲响应、原current Schur身份及完整方程余项。有限CAR的时间响应定理仍是另一个消费者；真空圈与整个耦合量子完成没有由该矩阵身份代填。

## 证据

- [replay.log](replay.log)：冻结程序 fresh EXIT0，完整数据除耗时一致。
- [源独立检查](source_check.py)、[输出](source-check.log)、[回执](source-receipt.json)：原252顶点、actual制备、全变量48独立dual图与两份符号分解全 PASS。
- [响应独立检查](response_check.py)、[输出](response-check.log)、[回执](response-receipt.json)：完整48双侧逆、全2304条目、289余项、谱推导与pole见证全 PASS。
- 只新增本 audit 目录文件，没有修改候选或提交。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/occupied-response/audit/source_check.py --root .
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/occupied-response/audit/response_check.py --root .
```
