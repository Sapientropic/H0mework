# Gauss100 配对与 retarded 弱历史

本机制从固定`positiveSmoothUnifiedSource / repaired Dirac-dual / SpinPair.actual`
读取原载体、作用与配对；`visit10/tick16/materialEntry → tick17`保持。
当前模型责任只由[Physics active route](../../../../Lean/docs/handoffs/physics-cauchy-safe-active-route.md)维护。

## 原 Gauss100 载体

`GaussHistoryHilbert.lean`使用原`Coframe × scalarSlice × coordinateSlice`；
原源轨道与截面等价生成维数100。它与商前`Configuration`的103维Hilbert空间分开。
令`D(A)(a,w)=[a,A]+w`，`D₀`为同一实际源的轨道／截面等价，则

```text
J₀ = sqrt(det Gram(D₀ b))，b为定义域的native正交基，
J(A) = J₀ |det(D₀⁻¹ D(A))|。
```

原native内积与完整轨道切映射决定J₀。实际源点、正coframe、原scalar chart及原
`a₁>0,a₁₂>0`截面进入开域；完整Jacobian为正。其配置测度取原三个native体积的乘积，
Number扇区权重为`J(A)v^(N+2)`。全部504模、全部占据数及严格内部紧支撑C∞复子模
给出真实Hilbert空间与稠密core，没有输入一个稠密域见证。

`source_gauss_history_domain.py`在全部33个规范变量上重建相对切映射，得到

```text
J₀ = 81√2/250，det(D₀⁻¹D(A)) = (250√2/27)a₁²a₁₂，
dμ_native100 = 1024√3 dz₁₀₀，
J(A)dμ_native100 = 768√3 ρ₃ dz₁₀₀，ρ₃=8a₁²a₁₂。
```

因此新Jacobian正条件由原正截面生成。独审直接用原7×7括号与native配对重算三行
minor和体积因子，原SpinPair基变换同时作用轨道列及定义域Gram。
这保留了原局部群轨道体积；没有添加Haar概率归一或场Z。

`GaussHalfDensity.lean`构造乘以`sqrt(J(A)v^(N+2))`的满射复线性等距及原除法逆。
源点读数为`sqrt(J₀)`。native100裸测度与`dz₁₀₀`之间的独立常数仍按上述等式返回，
不能把源点半密度改成1。`NativeHistoryGrade.flatHistory_pairing`实际消费这个等距。

## 原始协变动量的实际算子域

`GaussLiveMomentum.lean`在同一Gauss100开域的每个点构造

```text
D_z(a,x,W) = (a·(vacuum+φ_z)+x, [a,A_z]+W),
NativeLie12 × (scalarSlice61 × coordinateSlice33) ≃ Scalar70 × Gauge36。
```

原broken9 consistency消去broken分量；原残余Jacobian消去stabilizer3。
因此完整106维映射的逆I_z由源结构生成。该逆在原开域光滑，且
`dI_z[h]v = −I_z(dD[h](I_zv))`。协变量延拓满足原轨道值`−charge(a)`和截面值`p(x,W)`，
并由这两条读口唯一确定；没有输入新的逆矩阵或非退化见证。

`GaussNativeMatter.lean`从原P286母作用生成全部504模上的CAR作用R(a)，包括独立dual分支，
证明其反Hermitian配对，并精确限制回原stabilizer作用。这是全部native12方向的表示；
没有把broken9改称固定源作用的first-class对称性。

写`I_zv=(α_v,β_v)`，`GaussCoreDifferential.lean`生成

```text
Π_v f(z) = −i [df_z(0,β_v(z)) + R(α_v(z))f(z)]。
```

任意紧支撑光滑完整Fock测试函数经Π_v仍在同一测试空间。轨道方向返回`−iR(a)f`，
截面方向返回原方向导数。`GaussCoreHilbert.lean`证明这一测试空间与原加权
`fockTestDomain`线性等价，并将Π_v装配成实际稠密、保持core的`LinearPMap`。
这里使用同一`numberMeasure`；连续函数的几乎处处识别由其正支撑测度支付。

`source_native_core_momentum.py`以106维直接逆和原12维隐式约束求解交叉验证源点及原非零点，
逐项消费全部94个逆映射导数、106个动量及12＋94个读口；独立bit-CAR复现原电流。
原source scalar-form修正和coframe/contact项仍按原H₀组装，不能把一阶约化动量的裸平方
当作已经证明的完整原H₀。

### 原配对生成伴随与二阶作用

`GaussDensityCore`从同一`w_N=J(A)v^(N+2)`生成光滑权重及其倒数，给出
`∂_b†f=−w_N⁻¹∂_b(w_Nf)`。原native体积的Haar性质和紧支撑分部积分把此公式返回
实际`SectorHilbert N`内积。`GaussScalarTransport`用同一载体自产有限frame，把它组装到
实际可变方向`β_v`；微分读口精确等于`df(β_v)`，所以结果不依赖所选frame。

`GaussFockWeights`证明原native电流保持实际Number，并与任意Number权重通约。
`GaussFockPair`将完整加权Fock内积返回同一源积分，生成`R(α_v)`的加权反Hermitian配对。
`GaussMomentumAdjoint`于是实际构造

```text
Π_v† = i [D_v† − R(α_v)]，D_v f=df(0,β_v)，
FormalAdjointPair (GaussCoreHilbert.momentum v) (realizedAdjoint v)。
```

两端使用同一个已生成的稠密core，伴随和配对证明均不作为输入。

`GaussInverseSecond`核验原指数轨道曲线的真正一、二阶导数，并由同一双逆生成逆曲率。
其截面导数保留移动指标项`−I L(α_v)w`和轨道槽中的半括号项。
`GaussSecondCore`从测试函数的实际Fréchet一、二阶导数和完整CAR作用生成C²读口，
继续保持同一core。原112轨道图的106个native输出、106²个输入对全部返回；
19个方向的移动指标修正非零。

`source_native_second_form.py`还以直接嵌套的`Π†GΠ/2+V`回读原native部分，逐项保留
密度、散度、shift、电流及CAR平方。该比较在原flat读口中进行，内外动量都消费原半密度
共轭项；原加权Π的定义保持。它与原coefficient-left H的normal-CAR算法在
源点和原非零四时间配置分别返回11、19个输出词。这为原native伴随形式提供直接装配口；
完整H₀继续消费它及原coframe/contact/matter项。

## 原source时间列的native能量与实际二次型

`GaussNativeEnergy`先从原coframe构造完整四时间矩阵，再读取`SpinPair.actual`的时间列
`(n,0,0,0)`；`n`为原lapse，`σ`为同一source生成的三个共同耦合。
设空间三角coframe为Q、`v=det Q>0`，则原BF的`−XᵀηX/(σ det e)`实际返回

```text
电场块 = n QᵀQ/(σv)，磁场块 = −v Q⁻¹Q⁻ᵀ/(σn)，混合块 = 0；
G_scalar = −n/v I₇₀，G_gauge = σv/n Q⁻¹Q⁻ᵀ（使用原native Lie配对）。
```

电场块的双逆、原Lorentzian scalar逆度规及这些系数的光滑性都在整个原开域由Lean证明。
原空间二形式顺序固定为`(23,31,12)`。`GaussNativePotential`消费原scalar作用与同一
`magneticOfConnection A=([A₁,A₂],[A₂,A₀],[A₀,A₁])`，从原作用逐项返回光滑实势能。
时间列在原完整作用变分后读取；非零时间shift仍使用已签四时间族。

`GaussNativeForm`用完整scalar70及native Lie12的原正交基，将自产系数、Π和Π†实际装配为
`ΣΠ†GΠ/2+V`。每项保持原完整Fock紧支撑core，`native_core_pair`在原加权Hilbert内积中
证明整个native作用的对称性；对称见证、G和势能均没有作为外供premise。
`realize`直接提供同一稠密域与core不变性，供完整H₀装配消费。

`source_native_energy.py`在全部六个coframe符号上返回原BF块，并以非零时间shift确认
上述零混合块的确切适用范围。源点及原非零配置的完整106维G、V和shift导数均回读；
磁势另外由原7×7矩阵括号及native迹配对计算。三枚生产Lean的15个公开闭包仅标准三公理。
此具体native块与原coframe/contact及matter一起组成H₀，不能单独替换完整作用。

## 完整原H₀实际进入时间生成器

`GaussCoframeCore`从同一配置测度和Number密度生成六个coframe动量及其实际伴随。
`GaussCoframeKinetic`消费原Legendre矩阵K，全部六变量的系数返回见
`source_diagonal_core_history.py`。`GaussQuantumMultiplier`把任意完整CAR一体作用的
Number保持送入原加权配对；`GaussCoframeSpin`使用原Clifford矩阵及独立dual分支，
生成七个Hermitian电流Qₐ。其前三个来自`γ₀γᵢ/2`，中间三个来自
`iγⱼγₖ/2`，最后一个来自`−γ₅/2`，空间对顺序为`(23,31,12)`。

原coframe的完整96项normal-CAR张量在全部六变量上化为七个固定电流平方，系数为
`(−3/4,−3/4,−3/4,−1,−1,−1,3/4)`。原一体／排序修正同时返回，所得加权作用为

```text
H_coframe = Σ Πᵢ† Kᵢⱼ Πⱼ + 原四个对称交叉项
          + (n/v)[Σ wₐ Qₐ² − (9/8)Number] + 3nv。
```

`GaussCoframeForm`把它逐项装配到同一core。原半密度共轭产生
`3n(N+2)(N+4)/(16v)`，与normal-ordering的一次Number项精确抵消；flat读口保留
`n/v[ΣwₐQₐ²+3N²/16+3/2]+3nv`。`number_apply`返回原占据数。
这个恒等式消费整个normal-CAR张量，未固定Fock态或占据数。

`GaussMatterCore`直接消费原`diracMatrixMatterAction`与原native母表示，证明二者通约；
原Dirac空间主符号及独立dual的`−conjugate`分支生成完整Hermitian matter_noY。
`GaussDiagonalHistory.diagonalAction`实际相加native、coframe和matter_noY三项，
`diagonal_pair`、稠密性和core不变性由这些具体producer生成。

`GaussDiagonalHistory.history`于是以这个literal H₀调用下面的全时构造，给出初始恒等、
强连续收缩、实际core的每时导数、原左测试方程和`retarded_source`分布源项。
这个source mouth不输入H、形式对称见证、稠密域或传播子。
它保持原homogeneous／物理k=0作用的范围；向量弱历史的群性质与双侧算符历史没有被代填。

符号回读覆盖全部六coframe变量和原Dirac主符号。原嵌套CCR-CAR算法在源点与原非零点
分别检验N=0、2、3，移动半密度及两支Fock作用全部返回；七枚生产Lean的18个公开闭包
仅标准三公理。当前后续责任由Physics active route维护。

## 同一不变 core 生成时间核

`FiniteCoreEvolution.lean`对给定对称作用T，遍历其原domain的全部有限子集F，
自产有限张成空间、正交投影P_F及Hermitian压缩`T_F=P_F T P_F`。
每个压缩给真实幺正指数。原domain稠密时，`P_F→I`，且对每个原core向量x，
`T_Fx→Tx`；无需提供一个完备基或谱分解。

当F包含x时，`‖U_F(t)x−U_F(s)x‖≤|t−s|‖Tx‖`。
当Tx仍在core且F同时包含x和Tx时，完整时间轴上的Taylor余项满足

```text
‖U_F(t+h)x−U_F(t)x−h(−i U_F(t)Tx)‖ ≤ |h|² ‖T(Tx)‖。
```

`WeakCoreEvolution.lean`用一个共享的cofinal ultrafilter及Riesz生成E(t)，
给出强连续收缩、`E(0)=I`和每个时刻的强导数`E′(t)x=−iE(t)Tx`。
原左测试方程`⟨E(t)x,Ty⟩=⟨E(t)Tx,y⟩`同时成立。
对末端为零的C¹测试η，前向核实际满足

```text
∫₀ᵇ [η′(t)⟨E(t)x,y⟩ + iη(t)⟨E(t)x,Ty⟩]dt = −η(0)⟨x,y⟩。
```

这些是完整时间族及分布源项，有限阶源jet没有代填该极限。
返回的是原作用的弱历史；本口没有把它识别成酉群或Heisenberg自动同构。

## 原 Number／G 消费

`NativeHistoryGrade.lean`由原504模和原Λ6的56模生成全部
`Number0…504 × G0…56`正交投影P，保持同一Gauss100 core并分解恒等。
`ΣP E(t)P`生成保分块的强连续收缩与原点恒等；原T保持／通约这些投影时，
原微分方程、左测试配对和retarded源项全部返回。半密度再把它送到原flat读口。

通用引擎的T参数由`GaussDiagonalHistory`以具体原H₀支付，对称性与不变稠密core已实际消费。
`NativeHistoryGrade`的原Number／G合同继续由同一作用的分级producer支付；双侧算符域按
独立真实接口消费。这些通用引擎保持原strict核验及标准三公理范围。
