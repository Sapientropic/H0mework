# 共同源量子域、配置体积与时间预解算子

本接口从固定 `positiveSmoothUnifiedSource / repaired Dirac-dual / SpinPair.actual`
发生生成；`visit10/tick16/materialEntry → tick17` 不变。它消费同一原四能量作用及已生成的
canonical 量子时间图；当前全局责任见 [Physics active route](../../../../Lean/docs/handoffs/physics-cauchy-safe-active-route.md)。

## 实际 Hilbert 载体与半密度

`SourceQuantumConfigurationHilbert.lean` 用实际六个 coframe 坐标、原 `scalarSlice` 和三份
`NativeLie` 空间连接生成开配置域，测度取这些原内积空间的规范体积。coframe 的三个对角坐标
为正，scalar 部分在已生成的非退化 chart 内；实际 `SpinPair.actual` 给出域内源点。

完整模式为原 `Quantum.Index ⊕ Quantum.Index`，基数 504；全部 `Finset` 占据构成 Fock
载体。每个真实占据数 m 的权重是 `v^(m+2)`，v 为空间 coframe 行列式。
`FockHilbert` 是实际复 Hilbert 空间，严格内部紧支撑光滑复子模 `fockTestDomain` 在 Hilbert
范数下稠密。`SourceQuantumHalfDensityHilbert.fockHalfDensityEquiv` 是乘以
`sqrt(v^(m+2))` 的满射复线性等距，逆映射除以同一正函数；源点两者均为 1。

原 `NativeLie` 的八个 color、三个 weak 和一个 hypercharge 实坐标由双向线性等价生成，
维数为12；Scalar70、三空间连接36也从实际类型生成。原真空四槽外代数作用给九个实坐标
左逆；原 Cartan、mixing 和它们的 Lie bracket 生成三维核。rank-nullity 与原内积正交补
因此给 orbit9、stabilizer3、broken9、scalarSlice61 及商前 configuration103。

同一 `SpinPair.actual` 的三个空间连接是 `gaugeScale·Gᵢ`。原三个 source color 生成元
参数化整个 stabilizer，并由实际括号生成规范轨道的三行 minor
`diag(-gaugeScale/2,gaugeScale/2,-gaugeScale/2)`，行列式为正的 `gaugeScale³/8`。
因此 residualOrbit 单射，其 native 正交补 gaugeSlice 有33维，源线性配置截面
`Coframe × scalarSlice × gaugeSlice` 为100维。上述维数和单射均由 Lean 的原源作用证明，
没有输入 rank 或目标维数。

加权 Hilbert 实例仍位于 residual Gauss 商之前；线性100截面与非线性商后的 `ρ₃` 是
不同消费者，后者由原 Python 截面链支付。测试子空间的 Hilbert 稠密性没有代填某个无界
算子的 graph-core 定理。

`SourceQuantumGaugeSliceCoordinates.lean` 将原三个 gauge 行定义的坐标截面与 native
正交截面实际接通。源 minor 的逆生成 `P_coord`，原内积生成 `P_orth`；两者消去同一
residualOrbit，给出 `sliceEquiv` 和完整 `(stabilizer × coordinateSlice) ≃ Gauge` 双逆。
原 coframe 和 scalarSlice 保持，同一实际 sourceGauge 位于该坐标截面。

`source_gauge_slice_coordinates.py` 由原 Gram 矩阵生成两截面的 native Jacobian
`3√2/16`，以及坐标体积与 native product 体积的比例 `1536√6`。
原 native Haar 相对原坐标 Haar 的比例为 `2√2`，故同一个已生成的局部轨道 chart Φ 满足

```text
Φ* dμ_native103 = (768√3 ρ₃(z)) dμ_nativeHaar dz₁₀₀,
ρ₃(z) = 8 a₁² a₁₂  > 0  on the connected source chart.
```

完整504模的原酉群作用保持每个占据数和 coframe，因而局部 equivariant 延拓的实际范数为
`μ_nativeHaar(U) ∫ 768√3 ρ₃ v^(m+2) ‖f‖² dz₁₀₀`。非恒等原群元素和偏移截面的
103维 Jacobian、原 Maurer 微分与真实 N2 占据范数均由另一算法复现。
半密度为 `sqrt(768√3 ρ₃ v^(m+2))`；固定 Gram 因子在同一 `U H U⁻¹` 中消去。
这是已生成的局部配对之间的等式，群轨道体积保留显式，没有额外归一化常数。

`SourceQuantumResidualFlow.lean` 从原 stabilizer 在 scalarSlice 和 Gauge 上的作用生成
`flow(a)=exp(generator(a))`，并实际构造 `flow(a)(source+sliceInjection(w))`。
源点严格导数等于已生成的 `sourceSplitEquiv`；逆函数定理由此生成非空局部轨道图、
局部逆及含源点的开100维物理截面。有限流上的标量坐标延拓精确回读 f(w)，
局部可逆性与 Jacobian 都没有作为输入。

`SourceQuantumResidualFlowMeasure.lean` 进一步由原 scalar/gauge skew 证明流保持两个
native 配对，coframe 不变。Configuration 的范数是 max 产品范数；真实分量分解同时
给该范数的满射等距与原 `configurationMeasure` 产品体积保持，没有把 max 范数当作
内积范数。ambient Number 权重保持，整条实际源轨道在原 chart 中且权重为1；
一般 chart 权重运输使用真实的输入、输出端点。

`SourceQuantumResidualChartFlow.lean` 又从同一原作用生成
`C(A_a φ)=K_a C(φ)−C(φ)K_a`。沿真实指数流夹持求导给 consistency 共轭与行列式不变，
因此整个原 scalar/configuration chart 都被双向保持。原 chartMeasure、Number 测度、
每个 `SectorHilbert N` 的复线性配置拉回酉等价及严格内部紧支撑光滑测试域双向保持均已
由 Lean 签收。

`SourceQuantumFockGauge.lean` 从原 occupation 插入／删除符号证明 CAR 配对伴随恒等式，
以 full504 原母表示及独立 dual 的 skew 生成真正 ℓ² 纤维上的 Γ。原 Number 与 Γ 对易，
因此跨 Number 的矩阵系数严格为零。`SourceQuantumFockGaugeHilbert.lean` 将它和配置拉回
接成同一原加权 `FockHilbert` 的酉等价，逐 occupation 的 a.e. 公式精确为
`U_a Ψ(z)=Γ(a,−1) Ψ(chartFlow(a,z))`。原半密度在同 Number 项中精确抵消；
原全部紧支撑 C∞ 测试域双向保持，完整504载体和原留数归一均保持。

## 原 coframe 作用的体积—形状表示

令 r=√v，五个形状坐标为 θ=(u,w,a,b,c)：

```text
q = r^(2/3) (exp u, a, exp w, b, c, exp(-u-w))
dq₆ v^(m+2) = 2 r^(2m+7) dr dθ₅
U_m = √2 r^(m+7/2)
```

r 是配置体积坐标，不是空间距离或强子相对距离。Jacobian 的 √2 没有改变外腿留数。
`source_coframe_volume_shape.py` 直接把原 BF/primary 消元产生的微分系数、所有正规双电流和
live 单电流项变换为

```text
U_m H_coframe(n,b) U_m⁻¹
  = n[-3/16 ∂r² + (-Q_m+C_m)/r² + 3r²].
```

Q_m 的五个 covariant 动量为 `P_j+dΓ(B_j)`，`P_j=-i(V_j+div V_j/2)`。
五个 V 的显式全局流、原常量 Hermitian spin8 连接 B、正 Gram G 均由原系数生成。
流的实际 Jacobian 和完整 CAR exterior action 给出全局幺正群；`Cc∞` 保持且群强连续。
原有限 Fock 常量为

```text
C_m = 原 normal-current tensor + dΓ(-9I/4)
      + Σ_j dΓ(B_j)² + [3(2m+7)(2m+5)/64 - 1/4]I,
||C_m|| ≤ 15m²/8 + 15m/8 + 89/64.
```

这里保留两个有序 current 槽；原 two-spin 矩阵的行范数界为 3/2。
独立算法从原 BF Hessian 重建，直接展开完整 `-Q+C` 的 N1/N2 二阶 jet；两者均与原嵌套
作用相同。遗漏 `-1/4` 的实际差是 `3√30/800`。

## 完整四能量的精确体积伸缩族

同一实际配对给出 `U_λ f(q,x,A)=λ^(3m/2+6) f(λq,x,A)`，λ>0。
`source_common_volume_pencil.py` 从完整原系数生成五个伸缩权重：

```text
U_λ H(n,b) U_λ⁻¹ = Σ_{p∈{-3,-1,0,1,3}} λ^p H[p].
```

权重 −3 包括完整 coframe 动能/current 及 scalar form；−1 包括有序 scalar shift 和
非 Y Dirac 空间项；0 为原完整 Y；1 包括整个原 BF gauge 作用与 scalar 空间势；3 为
coframe 体积势及 scalar 真空势。这里 H[0]=Y，与 Fock 分级中的保级算子 H0 名称不同。
所有 live 导数和正规乘积保持，实际完整 Gauss/N2 消费者的五个权重均非零。

配置体积半密度后，同一群是 `U_λ f(r,θ)=λ^(3/4)f(λ^(3/2)r,θ)`，发生器为
`D=-i(3r∂r/2+3/4)`；在共同紧支撑光滑域上精确有 `i[D,H]=Σ_p p H[p]`。
群与四个时间参数无关，因而原四条时间约束也保持同一有限权重分解。
这给出完整局部量子作用的精确算子族；它没有将配置伸缩改作时空伸缩。

## 同一 canonical 时间图的精确系数映射

对原四个时间变量 `y=(n,b)`，令 `C_a=c_a I+D_a`、`J_a(X)=(C_a X+X C_a)/2`，
`l=(1,-rω)`，`R_l=(Σ_a l_a J_a)⁻¹`。此处积分变量 r∈[0,1] 与上面的配置体积半径无关。
原分母和二次分子的精确映射为

```text
1/[n(n²-|b|²)] = 2∫₀¹ r dr Avg_S² (n-rω·b)^(-3),
T_ab = ∫₀¹ r dr Avg_S² (R_l J_a R_l J_b R_l + R_l J_b R_l J_a R_l).
```

原 13 权重由四个 J、`(T_00-T_ii)/2`、`-T_ij` 和 `-T_0i` 组成。对中心 c 求导而保持
D 固定，`∂c_j R_l=-l_j R_l²`、`∂c_j J_a=δ_aj I`，生成原四条 `-∂y H` 的有序权重。
这些是同一 canonical primary graph 的映射，原子标签不被当作 canonical 坐标。
构造核对了 850 个有序 Jordan 矩及 3400 个原 force 矩；独审另检验完整有序链。

在实际粒子数 m 上，若 `C=N I+R` 的 R 具有严格正 source grade，则原紧支撑光滑 core 上

```text
J_C^(-s) X = Σ_k (-1)^k binom(s+k-1,k) N^(-s-k) J_R^k(X)
```

精确有限终止。X 可以是原无界 grade0 微分作用；每个给定光滑向量的界由有限个真实 graph
半范数生成，不输入有界 X 假设。已有原 `FockFilteredWords` 消费全占据分级。
实际完整 Gauss/CAR 的 `H0 f`、`H0(Yf)`、`H0(Y²f)` 保留所有 Y 系数导数；`Y H0 Y` 非零，
删 Y 导数产生非零差，完整 Sylvester 逆回写残差为零。

该有限提升支付正 grade 部分。完整 grade0 clock 及连续嵌套 R/J 的实际 form 域由原四条
时间方程生成；单一正 injective clock 的条件性相对 form 逆不替代它。
`pureY` 是原形式系数代数的 specialization，没有被命名为实际闭合物理 sector。

## 原配置余切锥与量子 clock 系数

完整原二阶符号在全部 CAR 占据上为标量。原两组 Gauss 拉回生成
`A=a₀₂` 和正电 Gram `S₂`，记 T=tr(S₂)。在源定义的开余切锥
`A>0`、`T I-S₂>0` 上，原四力满足

```text
b·F_b = -n bᵀ(T I-S₂)b/(n²-|b|²)²,
C₀=(sqrt(T/(2A)),0,0,0).
```

因此 C₀ 是整个未来类时时间锥内唯一的主符号根，四力 Jacobian 非退化。
真实 source covector 经全部原 Gauss 条件给 `S₂=diag(1/4,1/4,1/3)`、
`A=625/648`、`p_r²=32708/6075`，精确读回 n=N；独审另从原系数生成第二个 rank3 见证。
这些是配置余切方向，不是外腿的时空动量。

原 canonical inner graph 的首个 Jordan Poisson 项逐对抵消，原力的阶一符号直接生成
`C₋₁=-J₂⁻¹ F₁(C₀)`。完整504模 lapse 修正有256个非零矩阵项；实际 N2 读回保留
真实 current 及四力零残差。原 `{A,T}` 非零，没有因这次抵消被设为零。

原 affine12 Gauss 系统的二次微分进一步生成 A、T、C₀ 的全部200维相空间梯度和 Hessian。
同一图的首个几何量子力为

```text
δF_n = [P²(C₀,T/C₀²)/C₀ + P²(C₀,T/C₀)/C₀²]/16,
δF_b = 0,
```

其中 P² 是原100对 canonical 坐标的二阶 Moyal 收缩。
这个非零项与原四能量 Weyl 零阶、C₋₁ 的矩阵 Jordan 交叉及二次 principal 项共同生成
实际源相空间点上完整 N2 的 C₋₂ 和约化能量 E₀。原 Y 首次在此 clock 阶进入，
其 lapse 系数为 `-324Y/625`；全部正规双电流、94维图导数与密度修正保持。
四条原力的阶零残差均为零；几何项独自没有代填完整 C₋₂，也没有把该有限符号展开当作谱。

## 同一作用的任意有限阶形式递推

`source_clock_symbol_recursion.py` 将原四能量 Weyl 符号的动量次数 2、1、0 作为叶子，
由同一13时间权重及独立原Y槽生成每阶余项。叶子工厂直接重建原作用；有限 canonical
导数由原100坐标和100动量实际微分，不输入外部 jet 或时钟。Moyal 节点保留非恒定
`C₀(z,p)`、T、S 在原相空间上的导数。

任意 k≥1 时，`Moyal_r` 的每项恰有 r 次动量导数。新 `C₋k` 在原力的 `2-k` 阶只能
无导数地线性出现，其系数正是已生成的 J₂；其余项仅用更高阶 clock 和原源叶子。
因此内部计算余项 Rₖ 后，`C₋k=-J₂⁻¹Rₖ` 生成唯一下一项。这个降阶及归纳论证支付
任意有限阶能力；有限测试没有被用来外推 uniform 结论。

完整可遍历微分 DAG 实际生成到四阶：3,934 节点、747 表达式，所有新力系数回写为零，
能量整个子图均不依赖当阶新 clock。完整504模 C₋₁、两粒子 C₋₁/C₋₂ 与对应能量直接
回读已签消费者。原叶子的真实 `∂q₀² A=-9/100` 与完整100对 Moyal 读数 `9/400` 独签。
三、四阶产物是可消费的源微分表达式；全阶形式符号不代填算子求和或谱测度。

DAG 使用确定性 gzip 保存，主回执同时绑定压缩文件和解压内容；全部14个叶子只消费一次，
原Y没有在nongauge槽和独立槽中重复计入。

## 原主 Hamiltonian 的锥内传播

令 `E=Π_A G_native⁻¹ Π_Aᵀ/2`，则 `S₂=v L⁻ᵀ E L⁻¹`。
`source_clock_characteristic_cone.py` 从原12维 Lie 作用、scalar70 和两次实际 Dirac
约化证明六个 E 分量与 A、T 及彼此 Poisson 对易。这里保留 broken9 标量约束和
residual3 规范约化，并没有把它们换成另一群商。

先在原正则配置 chart 上生成解析 Hamiltonian `P=2AT` 的流，再使用其守恒量：
`P`、E 和 `I₂(E)=((tr E)²-tr(E²))/2` 均保持。初始 `P>0`、`I₂(E)>0` 与原电 Gram
的半正性生成 `rank E≥2`；原 L 可逆、v>0 继而给 `T>0`、`A=P/(2T)>0` 和
`T I-S₂>0`。因此每个仍在原配置 chart 内的有限相空间端点都保持实际 clock 锥。
这一步先生成不含平方根的流，没有把锥内传播作为假设。

原约化主能量是 `H₂,red=√P=T/C₀`，并有
`X_H=X_P/(2√P)`；此正时间比例沿每条轨道恒定。实际源 covector 给
`I₂=11/48`、`P=3125/1944` 和 `X_H=(9√30/125)X_P`。
原完整200维二jet独立检验六个守恒量、15个相互括号及全部梯度，两个实际向量场各有16个
非零分量。这个传播口消费同一全阶递推的主能量，范围是配置余切主符号流；它没有代填
完整量子传播或全局完备性。

## 同一源锥内的实际紧域与符号界

`source_symbol_compact_majorants.py` 在原配置余切变量上生成非空紧域 K₁₅：配置分量有界、
`1/2≤|p|≤2`，原正 coframe、D₉、−det M₃、A、T 及 `TI−S₂` 均保持显式正裕度。
原 covector 归一化后有 `|p_source|²=14252/2025`，
`A=15625/114016`、`T=3375/28504`、`λ_min(TI−S₂)=2025/28504>1/15`。
这些是分析表示中的源域条件，不是物理动量截断。

原 D₉/M₃ 的仿射系数和行列式下界给逆矩阵零阶界，微分真实双逆方程生成全部高阶界；
原 BF/coframe 系数的单项式分母给所有 q 导数。带次序的 Leibniz 递推随后支付全部200方向
上 A、T、C₀、J₂⁻¹ 的任意有限阶导数，以及原几何 Moyal `C₋₂` 的邻域界。
源 guard 的实际裕度与这些导数界自动生成正内外盒；首次离域论证保证整个外盒仍在原锥内，
没有把源点 jet 当作邻域估计。

独立阶乘归一 Taylor 算法复现全部保存的界并实际运行到六阶，原1720项梯度/Hessian读数
均落入界；内盒 cutoff 的支持、导数和端点平坦性也由明确函数生成。
这套主符号界由下面的完整 CAR 叶子与实际符号实现继续消费。

## 完整四能量叶子、全阶微分图与光滑符号

`source_weyl_leaf_majorants.py` 由原四能量的实际公式生成全部14叶、三个齐次动量次数的
42份任意有限阶导数界。scalar/gauge 的两个逆图、完整 ρ 导数和 divdiv Weyl 势、
coframe 的单电流／正规双电流／Number 项全部保持。原 matter_noY 与 Y/n 分开，Y只计一次。
13个 timelike 读数由源 N 生成，原时间权重的真实满秩矩阵给出精确 reader。

全部504模的有限 CAR 范数直接从原 tensor-slot 作用支付：在 N 粒子扇区
`‖dΓ(Q)‖≤N‖Q‖`，原正规乘积由不同槽的作用给出界。独审使用更紧的
`N(N−1)‖Q‖‖R‖` 支付构造中的 `N(N+1)` 上界；真实42列是独立消费者，
没有代填全扇区证明。

`source_clock_dag_majorants.py` 对同一源递推的每个有序词、有理系数和有限 Moyal 节点
生成半范数。实际有理极点仅为 c、T、det(TI−S)，其逆界由原正锥生成；未付极点被拒绝。
全部200个 canonical tensor 非零项给精确的绝对 Moyal 因子 `100^r/r!`。
递归需求图先算出所需源导数阶，再支付完整叶子界。`source_clock_bounds(k,m)` 因而可
对任意有限 k、m 生成四个 clock 与能量的界；实际四阶／四次导数消费了八阶源叶子，
3,930节点、707表达式及774个有理系数由另一工作队列／Taylor算法签收。

`source_clock_smooth_symbols.py` 进一步生成真正的局部 C∞ 符号：

```text
C(z,p) = θ(z,p/|p|) [C₀(z,p) + Σₖ≥1 χ(|p|/Rₖ) C₋ₖ(z,p)],
E(z,p) = θ(z,p/|p|) [E₂(z,p) + Σₖ≥1 χ(|p|/Rₖ) E₂₋ₖ(z,p)].
```

θ来自同一源内外盒，χ是明确的平坦 cutoff。原微分图的实际界、200变量复合导数和径向
导数共同生成 Rₖ；前四个半径按精确 dyadic 指数保存为 `2679,11441,15738,24460`。
Rₖ≥2ᵏ使每个有限相空间邻域只有有限项，故这是实际光滑函数。对任意固定 m、N，
所有 k≥max(m,N+1) 的相应加权半范数均≤2⁻ᵏ，因此完整原同渐近展开成立。
独立集合分拆算法核对全 mixed 导数和尾界，真正 `evaluate` 在两阶都活跃的源射线上
逐词回读四 clock 与完整能量，原 Y 保留。

这些半径指定分析中的同渐近代表，没有改变物理截断或外腿留数。原 cone/Sylvester
映射的实际算子复合、余项消除及精确 operator clock 是下一算子消费者；光滑符号本身
不代填谱测度。

## 原正配对上的实际 Weyl 算子

`source_weyl_quantization.py` 用原平坦 cutoff `χ(2|p|)` 完成低频光滑延拓，
在 `|p|≥1` 与已生成的符号完全相同。原高阶尾界和有限源微分图给出每个指定阶的完整
200变量符号半范数；高阶常数保留为明确的有限源计算表达式，不输入未知范数。

原 θ 使100维配置支撑紧致。对配置变量作未归一部分 Fourier 变换，实际 Weyl 算子的
频域核为

```text
K(ξ,η) = (2π)^(-100) â(ξ−η,(ξ+η)/2).
```

配置分部积分与原源半范数直接给可积 Schur 上界。clock 取51次 `(1−Δ_z)`，
energy 取52次并保留实际 Peetre 因子；`∫⟨k⟩^(-102)dk=π^50/50!`。
因此完整 CAR 上的 clock 为有界 `L²→L²` 算子，energy 为实际 `H²→L²` 算子。
同一估计对每个整数 s≥0 给 `Op(a):H^(s+d)→H^s`，d为原符号阶0或2。
102/104阶范数是已生成的有限源计算表达式；实际低阶执行与独立 Beta/Gaussian 算法分别验收。

原两倍配置盒仍严格位于原 chart 内，给出 ψ=1 覆盖 θ 配置支撑的真实紧支撑函数。
U 是同一源半密度到 flat chart 的等距，J 是该 chart 到 R100 的零延拓，故 native 算子为
`U⁻¹ J* ψ Op(a) ψ J U`。两侧 ψ 的 Sobolev 乘子都进入界，chart 没有被当成整个 R100。
输出支撑与全部 Sobolev 阶共同证明原紧支撑 C∞ 测试域在所有这些算子及其测试伴随下保持，
因此每个有限有序复合拥有同一稠密真域。

实际核满足 `K_a(x,y)†=K_(a†)(y,x)`；原 Y 留在能量中，其伴随只进入独立测试口。
该稠密伴随口生成实际单值最小闭图。这里量子化的是已生成的源局部光滑代表；
原13映射的实际复合及精确量子时间方程继续由后续消费者支付。

## 实际有序复合与积分余项

`source_weyl_composition.py` 从上述实际 Fourier 核的乘积生成

```text
(a # b)(z,p) = (2π)^(-200) ∫ exp(i z·(ξ+η))
  â(ξ,p+η/2) b̂(η,p−ξ/2) dξ dη.
```

原矩阵次序保持。用 t 缩放两个动量偏移，再对真实积分作带积分余项的 Taylor 展开，
得到每个有限 N、m 的实际 `S^(d+e−N)` 余项；两侧支撑体积及全部低于所需阶的源半范数
分别进入界。配置矩估计还支付复合符号的非紧支撑尾，因此后续有序复合继续有可积界。

native 复合精确为 `U⁻¹ J* ψ Op(a # ψ² # b) ψ J U`。
ψ 在原符号全部配置导数支撑上等于1，使 `a # ψ²−a` 和 `ψ² # a−a`
成为实际 `S^−∞` 误差；结论来自任意阶真实 Taylor 余项，不能删掉原中间 ψ²。

原作用给出 `Y0=Y/n` 对原 scalar61 仿射，并且与 coframe、gauge、四时间参数无关。
因此完整独立 dual 分支上的两侧实际复合精确终止于一阶：
`Y0 # a=Y0 a+(i/2)ΣY_j ∂p_j a`、`a # Y0=a Y0−(i/2)Σ∂p_j a Y_j`。
原源内角向点的完整光滑 clock 给出严格非零交换子；原两粒子 CAR 列和全部 scalar 动量
梯度由独立算法重建。这里保持原 Y，未加入 Y†。

这些实际乘积与平滑余项直接进入原13个 cone/Sylvester 映射；精确量子时间方程仍须
消费并消去其余项。

## 同一局部能量的闭形式

`source_positive_energy_form.py` 对已经生成的 Gauss100 局部能量取原外代数分级的对角部分。
完整504占据载体保持；在原非负分级代数中，该读回恰好由原Y槽取零生成。
原Jordan／Sylvester递推及实四力Jacobian给出每阶对角clock／energy的Hermitian归纳。

令 `h2=T/c=√(2AT)`，原θ、β=χ(2ρ)、χ1=χ(ρ/R1)生成真正光滑因子

```text
b1 = √θ √β √h2,
b0 = √θ χ1 E1 / (2√h2),
B = b1+b0.
```

平方根cutoff的所有端点jet与全部源导数界直接生成。b1为实标量，
`b1²+2b1b0`精确恢复原局部能量的二阶和一阶项；一阶自Moyal严格为零。
真实积分余项因此给 `R0=Ediag−B†#B ∈ S0`。k2零阶项始终保留在有限头部，
配置矩界支付非紧支撑的R0及其实际L²界；没有用点态正性代替Weyl算子的正性。

仍取原Gauss100配对、U、J和ψ。原测试域上的 `A0=OpW(B) ψ J U` 有稠密伴随域，
故其图闭包A为实际闭算子。`q(f,g)=⟨Af,Ag⟩+⟨f,Rnative g⟩` 在D(A)上闭且下有界。
加入源生界M+1后，Riesz映射生成唯一的form关联自伴Hdiag。
原测试域按A的定义就是图稠密域；沿图逼近延拓核恒等式，证明Hdiag在原测试域上
精确等于原 `U⁻¹ J* ψ OpW(Ediag) ψ J U`，无需额外core输入。

实际首个活跃E1 CAR列、低频延拓与完整200变量的平方因子二阶Moyal独签；后者为
`158853308791√30/15820312500000`，没有被设为零。
本节载体是已有量子化使用的Gauss100局部chart，商前103维Lean空间通过原disintegration
桥联系；此处不把两者作定义相等。原正分级Y保留给完整局部能量的传播消费者，
原四条精确量子时间方程仍须消费真实余项。

## 完整局部能量的有限 retarded 演化

原full504模式中，Λ6分级容量由两独立分支×四Dirac spin×七个Λ6基向量生成，精确为56。
`SourceQuantumFockGrade56.lean` 在全Fock载体证明57个原Y插入归零，
允许任意grade0与非交换boson因子穿插；原70项coupling及其实际表示的57次幂直接消费此口。
真实系数导数同样保持分级，无固定粒子数前提。

`source_local_energy_evolution.py` 保持同一已生成Gauss100局部能量代表，
将其写成 `Hlocal=Hdiag+V`。正grade项V由原energy的k2及以后项生成；
原源尾界和Schur计算给其实际L²界。原grade投影保持平方形式，继而与Riesz映射、
Hdiag及其谱演算对易；因此每个含57个V的有序词为零。

```text
D0(t)=U0(t),  D(r+1)(t)=−i ∫₀ᵗ U0(t−s) V Dr(s) ds,
U(t)=Σ(r=0..56) Dr(t),
R(z)=Σ(r=0..56)(−R0(z)V)^r R0(z),  Im z≠0.
```

这些是实际强Bochner积分和双侧resolvent。有限Volterra恒等式与唯一性生成
Hlocal的强连续群及原D(Hdiag)生成元；其retarded核为 `−i 1(t≥0)U(t)`，
消费同一Hilbert中的`L¹_loc`强迫。完整Hlocal保持原非Hermitian正grade项，未加Y†。
实际两个修正都活跃的源射线回读四条原Y列，范数平方严格为`216/125`。
完整物理谱密度、proton识别和Γ／τ不由该局部能量代表的演化代填。

## 原 cone 响应的实际参数逆与缺陷

`source_cone_sylvester_parametrix.py` 从原13时间读数及其派生trace生成230个后缀响应：
132个R前缀、84个J前缀及14个基口。原参数`h=−rω`、`0≤r≤1`的系数和相应导数界
统一进入每阶共同Borel半径；前两阶`log₂R=4639,13019`。

R前缀是该真实光滑响应；J前缀始终由实际Weyl Jordan乘法构造。
辅助Borel J符号与真实乘法之间的误差由已付积分余项控制。内层η的支撑完全位于原θ=1、
β=1区域，原132个Sylvester方程的实际η夹积残差均为`S^−∞`，不输入全空间clock逆。

同一cutoff使原四prepared力的无限和逐阶精确合并为
`−βθ[(1−χ(ρ/R1))A_a^1+(1−χ(ρ/R2))A_a^0]`。
这是原Y仍在其中的实际紧支撑平滑缺陷。源ρ=2的lapse力有11条非零CAR列；
该点值和`η#F#η`的点值保持区别。原四时间方程的精确闭合继续消费并消去这些缺陷。

## 同一 clock／响应场的实际有限修正

`source_clock_linear_response.py` 以原 `q=βθ/c` 构造实际Jordan超算子P，
J仍为原`J_(C_l)`。对每个有限N，

```text
E=I−JP,  L=I−PJ,  P_N=P Σ(j=0..N−1)E^j,
JP_N=I−E^N,  P_NJ=I−L^N.
```

其Fréchet响应保留左右缺陷，未输入真逆或小范数。
同一原四clock与132个R响应场一起更新；4868节点的实际图逐行回写线性项、
有限逆缺陷及全部`t²`余项，原四力／energy变化表保持完整。源点的11个非零clock修正
消费实际原力，四轴主Jacobian回写为零；真正的耦合线性化残差仍在图中保留。

实际多频Weyl积分API已消费非零频率和半移参数。native算子词逐叶插入中间ψ²，
非平凡ψ²=1/4读回通过；空词为`I_native`，不能把`N(1)=ψ²`当作该单位。
原未乘cutoff的仿射Y0满足flat层`J_q(Y0)=qY0`，源纤维范数平方为250/27；
该恒等式不替换`βθY0`或native复合所需的真实乘积。

此构造已生成可消费的实际有限更新及精确残差。消去有限逆／二次／耦合线性化残差
仍需同一作用生成的实际逆或收敛机制。

这里的共同未知量是四个clock算子和132个随原cone参数h变化的响应算子场，
不是136维数值矩阵。四力对独立R场为仿射；clock依赖由Sylvester方程耦合。
各后缀按长度排列时，响应Jacobian为对角块J的下三角算子系统。
上式P_N只近逆各R响应方程中的Jordan算子J_(C_l)；
其剩余E^N和四力耦合均由真实图保留。

该prepared current来自`SourceResponseValues.action`的原光滑clock／response叶。
`source_native_time_force_packet.py`的归一波包则从常数seed `(N I,0,0,0)`
读取完整force；其固定右波包压缩的谱和逆域见[主轨道源矩](source-clock-moment-equation.md)。
Gauss100中的`physical_configuration_cutoff`是算子夹积所用ψ，
native103中的`amplitude`是归一量子波包；两者不以名称相同来识别。
因此裸seed的`(K+κ)^−1`不能回填实际prepared current的共同Jacobian。

## 原连续cone力的精确仿射切片

`source_prepared_force_slice.py`直接消费上述prepared current。
原四力对132个独立R算子场满足`F(B)=T B−A`；T保留原cone积分
`h=−rω, dν=r dr Avg_S²`，总质量为1/2。
原224个非零、次数至一的系数给出

```text
Γ=T T*=diag(28,8,8,8),  det Γ=14336,
R_F=T*Γ^−1,  T R_F=I,
Z_F=−R_F F_prepared,  B*=B_prepared+Z_F,
F(B*)=0,  Q=I−R_F T,  TQ=0, Q²=Q。
```

这里T*只转置实cone系数，R_F作用于原力，不给作用添加Y†。
两组已有trace线性身份保持。变化Z_F为原紧相空间平滑算子场；
在`L²(ν;HS)^132`上，其源代价精确为
`‖F₀‖²/28+Σ_(i=1)^3‖Fᵢ‖²/8`，Q是正交投影。
旧R背景仍是原order2场，不能据此给它或任意后续P_N变化安装HS范数。

固定clock时，全部132条原约束逐行生成
`S*_w=S_w+J_(C_l) Z_F,w−Z_F,child`。
每个J child由真实有序Jordan乘积重建；这一步精确仿射，无二次余项。
新增1108个图节点保留全部原残差及native中间ψ²。
指定源相点／CAR输入的读数生成56个非零R变化，并以原cone积分读回四力零。
原残差仍按全局共同Schwartz模块和已付inner-η夹积消费。

因此整个力零切片为`B*+QV`，不能用`Q B_prepared`丢弃裸源A。
这个切片消去四条力方程；其上132条Sylvester约束仍决定实际共同解与能量。

## 同一完整clock的原生单位延拓

`source_prepared_clock_extension.py`保持上述B*和四力零式，使用原双倍source盒及全部Borel系数生成

```text
C♯₀=N I_native+Native[βout θout(c−N+Σ_(k≥1)χ(ρ/Rk)ρ^−k C₀,−k)],
C♯ᵢ=Native[βout θout Σ_(k≥1)χ(ρ/Rk)ρ^−k Cᵢ,−k],
βout=χ(4ρ)。
```

θout在原响应θ_R支撑上恒为1，2δ外为0；原400Lδ界支付双倍盒的全部guard。
I_native是真正单位，低频与外层支撑之外保留N，而非把Native[N]当单位。
已有Borel半径和原Schur有限积分界支付所有新clock的有界性。

全部132个原响应场保持不变，每个J child重新取C♯的真实Jordan乘积。
原非交换系数逐行消去阶2和阶1；主因子为标量，使一阶Jordan Moyal项连同θ_R导数精确消去。
原native ψ²仍保留。所有完整Sylvester残差因而属于全局order0，
从原公共Schwartz域延为同一L²上的有界算子，包含原θ过渡区。

首个cutoff余项为完整200维收缩
`D(r)=−[P₂(c,θ_R r)−θ_R P₂(c,r)]/8`，J₀ child保留自己的同类贡献。
原coframe有限dilation律运输全部实际jets；源θ_R=1/8处该项严格非零。
公共径向API在真实首个活跃Borel半径消费全部四CAR列。
因此阶0及平滑余项继续由同一原作用消费，不把有界化当作方程归零或HS性质。

## 原cutoff余项的完整负阶更新

`source_prepared_cutoff_correction.py`从全部132条原响应与连续cone积分生成

```text
b_cut=(−D(T/c²)/(2c)−D(T/c)/(2c²),0,0,0),
M_cut=θ_R J₂,
x₀=c³(b_cut)₀/(θ_R T)。
```

D是上节完整200维cutoff收缩，四力forcing由全表给出，未从单trace行外推。
实际平坦边缘保留θ_R导数，x₀不被直接当作全局光滑符号。
取原边距`d_i=δ−|coordinate_i−center_i|`和
`L(ρ)=1+log²(2+ρ)`，生成`σ_ρ=∏χ(L d_i/δ)`及径向head`χ(ρ)`。
在ρ≤1处修正为0；ρ>1时L>2，绝对值中心位于χ的平坦平台。

真实clock变化为`δC₀=χ(ρ)σ_ρ x₀`，其余三轴为0。
原χ导数比值的全阶多项式递推支付所有边缘极点；
在σ支撑上只留下log增长，因此`δC₀∈S_(1,0)^(-7/4)`。
band余量由原平坦性降为`exp(−const·log²ρ)`，保留的低频head一并属于S^−∞。

全部132条原三角递归生成δR，再以原R_F消去真实四力余量
`χ(ρ)(1−σ_ρ)b_cut`。四力精确保持零，原trace与Y不变。
新图保留真实δC#δR、每个J child及全部native ψ²。
原完整Weyl余项给出**每条新约束残差属于S_(1,0)^(-3/4)**；
没有把log项提升为全局多齐次展开，也没有删掉真实低阶项。

独立原Gauss隐微分重建五个S分量的完整200梯度，两个指定源径向点消费全部132项。
通用`symbol_values`从原函数及其有限导数取值，不以caller提供的jets代填源。

## 同一严格增生clock的真实逆及完整锥消费者

`source_prepared_clock_inverse.py`保留完整Borel系数和上节对数修正，
由原源范数生成更晚的频率实现半径。原主头的Wiener范数不超过`N·2^−251`；
Borel全尾及对数修正各不超过`1/256<N/128`。因此在整个原实cone上

```text
‖C_l−NI‖ ≤ qN,  q=1/64+2^−251<1,  α=(1−q)N>0，
Re⟨C_l u,u⟩ ≥ α‖u‖²。
R_C(B)=2∫₀∞ exp(−tC_l) B exp(−tC_l) dt。
```

右腿仍是原C_l。原chart零延拓像在`NI+ψ Op(a)ψ`下不变，故演化可限制回native域。
原精确整数Sobolev jet只产生严格降导数次数的块；闭源界M_s给
`‖exp(−tC_l)‖_Hs≤exp(−αt) Σ_(j≤s)(M_s t)^j/j!`。
积分的两端边界于是实际生成`J_C R_C(B)=B=R_C J_C(B)`。
全部132响应由原230后缀逐项生成，源域为`H²→L²`。

`source_true_cone_words.py`把原每个R替换为
`P_m(B)=Σ_(n<m)(−1)^n N^(−n−1) J_(C_l−NI)^n B`，
再对原h参数作精确锥积分。系数积分与算符次序分离：原20项能量及四组各57项力
都得到完整有限native词，每词恰含一个原二阶源A，且保持中间ψ²。

同一H² jet给真逆及所有有限P_m共同界

```text
ρ=1/α+M₂/(2α²)+M₂²/(4α³),
δ_m=(1/N) Σ_(r=0)^2 (M₂/(2N))^r
                   Σ_(j≤min(r,m)) binom(m,j) q^(m−j)/(1−q)^(r−j+1)。
```

原后缀范数/误差对从`(a_slot,0)`出发；J步骤乘`J=N(1+q)+M₂/2`，
R步骤送到`(ρb,ρe+δ_m b)`。以A为原14个源界之和，原表和绝对锥矩生成
能量误差`24δ_mρ²J²A`、时间力误差`96δ_mρ³J²A+12δ_mρ²JA`、
三个空间力误差`32δ_mρ³J²A+12δ_mρ²JA`。
`ν(1)=1/2`、`ν(|h_i|)=1/6`；范数误差不使用奇矩相消。

M₂来自原clock的有限源导数fold和ψ Leibniz和；每个a_slot来自原A的104阶Schur fold，
包含输入H² cutoff乘子。它们均有无caller范数的可执行计算口；
两个定义clock小量的102阶fold已数值执行，更高的整组常数保持闭源有限表达。
这给出完整能量与四力在`B(H²,L²)`中的收敛消费者。
新力由真R重新计算，旧独立R场的力零式不自动保留。

## 真响应消元后的非线性clock映射

`source_true_clock_variation.py`逐原后缀生成

```text
D R_w[X] = R_C(D child[X] − J_(X_l) R_w)，
D² R_w[X,Y] = R_C(D² child[X,Y] − J_(X_l) D R_w[Y] − J_(Y_l) D R_w[X])。
```

每个J child保留全部乘积项；原四力及20项能量直接消费这些真实变分。
两点差同时满足新点逆与旧点逆的两种有序表达，未交换右腿或循环trace。
在方向范数`Σ_a(‖X_a‖_L²+‖X_a‖_H²)/2≤1`下，源半径`r=1/(4ρ)`
使新逆由`(I+t R_C J_X)^−1 R_C`的收敛级数产生，并保持原严格增生下界的一半。

原含d个R、j个J的后缀具有全阶majorant
`g_w(t)=a_slot[ρ/(1−ρt)]^d(J+t)^j`。
其系数给全部混合Fréchet导数及Taylor余项；原绝对锥矩继续支付完整四力和能量。
一／二阶各五个有限消费者保留全部内层逆截断，并由原230后缀递推其H²误差。
这里的native有限词限制到原`ψ Op(x) ψ`方向，独立X/Y flat kernels之间保留ψ²；
一般有界方向的抽象算符导数不被误当作这种sandwich展开。

同一图中的实际方向`K_a=C_a−N δ_a0 I`生成保持外部`N I`的路径，
步长由ρ及原K的source jet界产生。全clock径向缩放另用于完整表的齐次恒等式，
不被安装为改变N或proper clock的新source发生。

## 真四力的负阶源界、紧性与全相位符号

`source_true_compact_force.py`对同一retimed旧残差逐原132行生成负阶范数。
原前三齐次项的抵消、N3 Weyl尾、log修正的N1尾、二次项、head／collar、
频率重实现和中间ψ²共同形成9,644项；每项阶数不超过−3/4。
非紧的中间Weyl乘积使用原`z^γ∂a`的L¹ moments；完整配置导数和Peetre权重
生成真实`L²→H^(3/4)`界。高阶总fold是原导数／半径的有限求值程序。

`source_true_compact_gain.py`在原flat chart插值H0/H1半群，给同C_l真逆增益界
`ρ_g=1/α+M₁/(2α²)`。全部差满足
`ΔR_w=R_C(Δchild−E_w)`，J child的界为`N(1+q)+M₁/2`。
它们在原H²域与已有差一致，继而延为`L²→H^(3/4)`；原四力是`TΔR`。
先在L²上对该有界差取伴随，再用同源C_l†估计，得到相同增益界；原Y不变。

所有差在两端supported于suppψ，且该集合严格位于原chart内。
原χ生成内半径2δ、外半径5δ/2的χout，原first-exit预算实际验证其仍在chart内。
δ缩放oscillator `1−δ²Δ+|q−q₀|²/δ²`的全Hermite degree≤L投影P_L保留
完整Fock504。令`V e_a=χout h_a`、`Q=VV†`，则

```text
M=V† F V， QFQ=V M V†， rank≤binom(L+100,100)·2^504，
‖F−QFQ‖≤2[3828/(2L+103)]^(3/8) · source_force_gain_bound。
```

V不是等距嵌入；同源Gram `G=V†V`由原χ的实际一维积分张成，未代为I。
以原有限逆词F_m生成`M_m=V†F_mV`时，再支付
`frame_H2_bound(L)·‖F−F_m‖_(H²→L²)`，获得完整L²算子误差。
矩阵核的源位置／动量积分保留全CAR、两个外ψ及每个中间ψ²；
这些矩阵是原四力的有限精度消费者，不是物理Hamiltonian谱或开放道投影。
符号精度表达式保持惰性；实际整数日程用源有理上包与整数不等式，避免巨整数分解。

`source_true_mixed_commutators.py`进一步对任意位置／导数commutator逐行生成
真实逆公式及`H^s→H^(s+3/4+r)`界；r只计位置commutator。
右腿分到clock时，剩余响应的输入实际移到`H^(s+r_C)`；
有理s的两端半群由原整数jet及其Hilbert伴随给出，不改原作用。

`source_true_force_symbol.py`直接定义同一F的Kohn–Nirenberg符号

```text
a_F(x,p)=exp(−ix·p) F[χout exp(i·p)](x)，
∂x^α ∂p^β a_F=i^|α|(−i)^|β| exp(−ix·p)
              ad_D^α ad_x^β F[χout exp(i·p)](x)， D=−i∂。
```

原双侧支持精确消去Dχout项；mixed两端界与调制Sobolev51估计生成
完整`S_(1,0)^(-3/4)` seminorm，Fourier反演严格恢复原F。
有限原F_m与Gaussian平均生成实际点积分；误差分别由平滑尺度和原Neumann尾支付，
不外供kernel、symbol或point值。source KN表示与原Weyl表示描述同一算子。

## 完成后时钟的精确有限分级响应

`source_true_grade_response.py`对原Lambda6占据生成固定P₀…P₅₆；
各秩为`binom(56,g)·2^448`，总和等于全Fock504。
原Borel每项保持非负grade，范数收敛保持同一零块。
令`D_a=Σ_g P_g C_a P_g`、`V_a=C_a−D_a`，原pinching保留正实部和Sobolev界；
grade0的已签伴随归纳还给出D_a自伴、D_l≥αI及源生成的真Jordan逆R_D。

```text
R_C(B)=Σ_(j=0)^56 (−R_D J_Vl)^j R_D(B)，
F[r]=Schur_(D,A_diag)[C[r]] + grade_r F(C[<r],A)。
```

第一式在原非负grade算子module上精确成立，两侧telescoping与真逆唯一性识别原R_C。
全部132响应和原20+4×57项consumer均实际接入；不要求`ρ‖J_V‖<1`。
对角逆的源Neumann逼近经有限57项及原后缀范数递推给完整H²→L²误差。
第二式由逐原230后缀归纳生成；grade1/2的460个自由非交换恒等式已独立展开。
这里的Schur在同一D背景上作用于cross-grade块，未把grade0块逆代为全部块的逆。
任意负grade算子不满足上述57项界；全算子差grade为−56…56，一般界为113步。

## 同一Schur的完整矩阵与两腿面逆

`source_diagonal_clock_schur.py`把原230后缀的变分直接编译为4×4
superoperator矩阵；每词恰含一个原grade0响应B_w，其余为真R_D及J_Da。
原h积分、四条能量变分及对原C[1]／C[2]的作用都由同图生成。
共同pair域是两腿各H²的H^(2,2)，不是单腿H²；有界因子的源半群积分
支付两腿四次jet polynomial。对词转置、反序给原稠密core上的配对伴随和
可闭性；未据此宣布完整闭包自伴。所有Jordan associator和逆commutator保持。

`source_pair_schur_principal.py`从同一原表生成双高频corner：

```text
−S_corner = w_L diag(T_L,T_L I−S_L) + w_R diag(T_R,T_R I−S_R)，
w_L=(3d_L+d_R)/(2d_L²(d_L+d_R)²)，
w_R=(d_L+3d_R)/(2d_R²(d_L+d_R)²)。
```

这里S_L／S_R已带原θρ²，两时钟独立。原源界给
`−S_corner≥(θ_Lρ_L²+θ_Rρ_R²) I/(240N³)`，正权区域内主逆直接生成。
右参数是原算子的输入动量：在核X(x,y)的Fourier变量中为−η_y，
原非偶角向窗口也反射。该主部不替代另一腿仍低频时的实际算子。

两个单腿高频面由完整Schur词直接产生：另一腿保留原D_l和D_a，
R因子为`2(dI+D_l)^−1`，J因子为`(dδ_a0 I+D_a)/2`。
源预算给`d/N∈[1023/1024,1025/1024]`及`Q<1/63`；原有序词的
telescoping和绝对cone矩给完整矩阵扰动界15/64，参考gap为63/256。
正权(2,1,1,1)的双Schur检验作用于原Hilbert范数，因此真面逆的
Neumann比≤20/21、范数≤`1280N³/(θρ²)`，同式给任意有限阶的几何误差。
作用在右因子的转置及原组合方向保留，两个面均未把对侧替成标量。

这些逆解决完整矩阵的高频面；实际Schur的非局部平滑部分、完整源forcing
的range及驻定更新仍由该同一矩阵消费，不从面逆推断全逆。

## 同一源生成的实际时钟下降步

`source_diagonal_clock_descent.py`使用原100维flat实现中的固定Bessel滤波
`P=⟨D⟩^−52=(1−Δ)^−26`及`B=ψP`。P为单射，其range在H²稠密，
故对原H²→L²四力有`P F P=0 ⇔ F=0`。滤波不改变驻定目标或外腿留数。
必须用`χout F=F`支付外部HS界；ψ不满足这一投影身份。
原全内部维度保留在
`‖Pχout⊗Id_Fock‖²_HS≤2^504(5δ)^100/[(4π)^50·51!]`中。

```text
f=P F_diag P， A(Z)=P Schur_D[B Z B†]P， g=A* f，
X=−B g B†/M²， Dnew=D+ηX， Cnew=C+ηX。
```

A*实际消费已签配对core伴随；原两个cone积分各自绑定自己的h。
M、f的界、原二阶Taylor界及η均由同一源有限fold生成，未外供方向、范数或步长。
实际η严格留在原解析半径内，并给出

```text
‖P F_diag(Dnew) P‖²_HS ≤ ‖f‖²_HS − η‖g‖²_HS/M²。
```

新对角真逆由原R_D的收敛Neumann级数生成；原132行逐条回写。
完整Cnew保留旧V与原Y，原57项公式再生成全部132条full响应，
对角／完整两套能量和四力重新消费这些值。源N、外部NI、grade0 Hermitian
方向及共同H²域保持。m1/m2有限梯度图和双腿四阶jet尾给源内误差；
高阶源范数fold未被当作已数值展开。

下降式不预设实际g非零；g=0时保留真实`ker A*`的forcing责任。
该步不替代完整驻定收敛或物理谱与寿命消费者。

## 原径向方向的合法范围消费者

`source_diagonal_radial_range.py`从原230后缀直接生成
`Schur_D[D]=−2(F_diag+A_bare)`，保留原非交换次序与全部cone积分。
令Π为`{ψ>0}`的真正支撑投影。D、真R均与Π通约，每个Schur词的唯一原B_w
使它湮灭完全处于补空间的输入。χoutDχout可作为同作用的辅助H²测试；
真正安装到更新口的方向由下述ψ-sandwich生成。

取完整Hermite degree≤L投影P_L，令

```text
V_L=B P_L， G_L=V_L†V_L， E_L=V_L G_L^−1 V_L†，
Z_aL=P_L G_L^−1(V_L†D_aV_L)G_L^−1 P_L，
X_aL=B Z_aL B†=E_L D_a E_L。
```

G_L是原Bessel热核与ψ²生成的新Gram。局部施加`(1−Δ)^26`及有限Hermite
解析性证明每个G_L严格正；未假设其最小特征值有统一下界。
E_L强收敛到Π，X_aL保持源外NI并有统一算子界。
Schur词中唯一二阶B_w由其所在腿的外P及已签H²／core伴随支付，
另一腿用ΠP的HS界；因此有界strong-*收敛实际传成filtered Schur的HS收敛。

```text
A(Z_L) → −2(f+a)， a=P A_bare P，
Π_(ker A*) f = −Π_(ker A*) a。
```

该源范围身份保留裸源项。由同一图的真实迹消费者
`t_L=Re⟨f,A(Z_L)⟩`、`n_L²=Σ‖Z_aL‖²_HS>0`得到
`‖A*f‖²≥t_L²/n_L²`。原有限逆还生成t_Lm及
`|t_Lm−t_L|≤error_g(m)n_L`，从而给有限精度梯度下界；不外供迹的值或符号。

## 原完整负阶力与首次严格更新

`source_diagonal_force_subprincipal.py`从原230后缀和四组57项生成完整首个负阶
四力系数；独立算法回读800个源微分条目、13个原504维一阶叶及四个原C₋₁。
原Gauss隐微分、100→103嵌入和全部200个横向方向保留；二次CAR commutator
在完整矩阵代入后才在该源族上消去。

原相点取`q0=1+3δ/4`，其余源坐标／单位协向量保持。这里θ=1/2、
θ_q0=−4/δ、θ_q0q0=0，原ψ及外clock窗口为1。四个完整504矩阵的非零
条目数为`[256,0,0,0]`。lapse矩阵的一项具有由原δ给出的严格符号；
这一项见证完整矩阵非零，不替换四力载体。

在该点的源内相邻域，原log窗口最终为1，有限retimed Borel头恢复原系数。
有限Weyl展开、真Jordan逆的全Sobolev／mixed界与pseudolocal尾证明该项
属于实际消元后的F_diag；保留全局log项，不声称其全局多齐次。

原完整Schur／core伴随的对角主项为`−θ diag(T,T I−S)/c³`。
`g=B† Schur♯[P f P]B`包含六个P，因此非零力系数生成阶−311的
非零实际HS梯度；X再含两个P，其非零阶为−415。原η>0遂给
`Cnew≠C`及严格HS残差下降，直接消费上一节的更新后真响应。
这是第一次实际更新的严格性，不预设后续current的范围或收敛。

## 全相空间负阶修正与更新后的真响应

`source_global_cutoff_force_correction.py`从原字段生成任意canonical200导数，
完整θ梯度／Hessian、13个原一阶CAR源及四个C₋₁共同产生四力的首个负阶系数。
原230后缀与37组交换子保留；`a_D=−P₂(c,θ)/8`及`W₀a=−P₂(C₋₁,a,θ)/8`
包含一般过渡区的乘法项。原正T与`T I−S`给

```text
C₋₃ = c³ diag(1/T,(T I−S)⁻¹) (F₋₁/θ)。
```

除θ只作用于已生成的局部微分系数。原log band、radial head及ψ的Weyl
sandwich生成实际全局修正。`source_global_cutoff_force_bounds.py`由完整源字段
逐项给`S^(-11/4)`界；同一四轴L²／H²总预算生成R₃，使两种范数同时小于
`N/8192`及`1/(8ρ_old)`。高阶有限fold和半径具备源内求值口，未当作已展开数值。

`source_global_cutoff_response.py`从原current加上该修正，保持原N、Y及外部NI。
令P_m为旧真逆的原有限词，旧误差为δ_m；新有限逆为

```text
S_nm = Σ_(j<n) (−P_m J_ΔC)^j P_m，
‖R_new−S_nm‖ ≤ 8ρ_old/(7·8^n) + 64δ_m/49。
```

新真逆及每个有限词都有共同界`8ρ_old/7`。同一图逐行生成全部132响应及
完整能量／四力，双索引误差进入原绝对锥矩。有限被积式保留原精确pushforward；
`finite(m,n)`仍能按需完成h多项式积分，内部Fock504和每个中间ψ²均保留。

在任意θ>0的紧相子域，原Borel/log头最终为1，真逆的局部展开给新四力
degree−1系数为零。全局非局部剩余力保留在同一新消费者中，不从这条局部
系数身份外推完整力已归零。

## θ两权的全阶源Borel时钟

`source_cutoff_weighted_recursion.py`在原230后缀中使用
`M_r^(u,v)(a,b)=θ^(−u−v) B_r(θ^u a,θ^v b)`。
clock外权为0、response外权为1；新clock内部保留其所有源因子。
第k阶未知量只通过r=0进入同一原principal Schur，故其原逆从已生成残差产生C_k。
实际原θ的全Leibniz微分实现该递推；θ=1限制逐系数返回原Engine。

`source_cutoff_weighted_majorants.py`沿同一DAG反向生成有限微分需求，消费原13叶及Y、
原principal cone和`c,T,det(T I−S)`有理系数。Bell多项式支付所有归一化θ比值，
完整log幂在最终系数才吸收一次，给每个(k,m)的全局`S^(−k+1/4)`clock界。

`source_cutoff_weighted_borel.py`由这些界生成递增的R_k=2^r_k，满足
`A_k/R_k≤2^−k`及`W_k R_k^(−k+1/4)≤2^(−k−11)`，并有`R_(k+1)≥16R_k`。
原主头和所有`χ(ρ/R_k)χ(ρ)σ C_k`之和局部有限，给同一native全局S⁰算子。
外部NI保留为真正恒等；四轴总界为`Nq`，`q=2^−10+2^−251`。

所有整数Hs的原ψ双侧Leibniz和源jet生成M_s，严格增生界`α=N(1−q)`给

```text
R(B)=2∫₀∞ e^(−tC_l) B e^(−tC_l)dt，
‖R‖_(B(H^(s+d),Hs)) ≤ Σ_(i≤s,j≤s+d)
  2 M_s^i M_(s+d)^j (i+j)! / [i!j!(2α)^(i+j+1)]。
```

右腿仍是同一C_l。原230场、132真R、20项能量和四组57项力全部重建；
原裸A中的Y保留一次，新生成clock系数中的内部Y按原递推消费。
Borel半径的高阶有限fold并未数值展开；其求值函数只有原源与整数索引。
该时钟不与旧有限C₋₃或首次下降后的current混同。

## 同一Borel current的完整平滑四力

`source_cutoff_borel_residual.py`从原两权递推生成所有230个参考响应。
对非裸源使用`β₀ θ [ρ²r_w0+Σ_(k≥1) χ(ρ/S_k) ρ^(2−k) r_wk]`，每阶S_k共用于全部响应；
这里没有σ，裸源保留完整A₂、A₁、A₀和一次Y。源flat估计支付全局θ比值，
log collar保留半个指数衰减后支付任意ρ幂，所有原边界处都作真实平滑延拓。

用统一`E=J(reference input)−reference output`，原真方程给

```text
ΔB_R = R_C(ΔB_child−E_R)，
ΔB_J = J_C(ΔB_child)+E_J。
```

每行E的源分解包含完整有限Weyl积分余项、两侧Borel尾、radial heads、
σ collar及两项native ψ²余项；真正NI直接作用，不为它安装配置L¹界。
统一S_k使每阶原cone项相消，参考四力精确留下

```text
Fhat_a = −β₀ θ [(1−χ(ρ/S₁)) A₁,a +(1−χ(ρ/S₂)) A₀,a]。
```

这里A₁是完整一次齐次场，A₀,0含原Y。上述紧频率头与全部216行E都具备
任意负阶闭源范数。相同C_l的真逆在每个`H^(−r)→H^r`双腿递推中输运这些界，
从而生成原完整四力的smoothing范数；右腿只用分析伴随支付负Sobolev界，
实际逆仍含同一C_l。能量的真／参考差同样为smoothing。

`residual_smoothing_bound(slot,word,r)`与
`SourceWeightedBorelResidual().smoothing_transport(r)`是源内求值口。
S₁的指数4655已实际计算；所有高阶总Fourier预算按有限源fold给出。
这些范数供真实非线性驻定求解消费，没有将剩余平滑力设为零。

## 完整Borel Schur的源范围与余核

`source_borel_schur_range.py`在同一完成current上消费原920方向列及完整16项Schur。
以实HS配对取原57grade投影Π_T：保留全部严格升grade块，grade0取自伴部分；
它是实正交投影，不假作复线性。原P与B=ψP给

```text
f=P F(C) P， A Z=P S[B Π_T(Z) B†]P，
A* f=Π_T B† S*[P f P] B。
```

配对伴随逐词反序并取原系数的分析伴随；非自伴C_l的逆配对给C_l†，
没有改动物理Hsharp或Y。唯一无界源响应前后分别用H^(2,2)与L²界，
源16项范数生成M>‖A‖，其原逆截断误差生成ε_m。

令`μ_n=M²2^−n`、`T_n=I−(AA*+μ_n I)/(M²+μ_n)`，则
`0≤T_n≤q_n I`、`q_n=2^n/(2^n+1)`。
同一实际逆由Neumann总和生成，长度L的尾界为`q_n^L/μ_n`。
`‖A_m A_m*−AA*‖≤2Mε_m`和真resolvent恒等式支付第二个截断索引。
这些有限多项式作用于完整exact f，不将源力替换成有限矩阵。

完整方向`Z_n=−A*(AA*+μ_n I)^−1 f`的线性化残差为
`μ_n(AA*+μ_n I)^−1 f`。正算子AA*的谱演算生成该向量到
`Π_(ker A*) f`的强极限；真实余核由原source算子决定，不输入谱隙或零投影。
这是驻定方程的范围消费者，不是物理Hamiltonian的谱测度。

## 完整范围方向的实际非线性更新

`source_borel_range_update.py`取有限正多项式
`p_L=(M²+μ)⁻¹ Σ_(j<L) T_n^j`，同一原力给`Z=−A* p_L(AA*)f`及`X=BZB†`。
在实际谱区间`0≤λ≤M²`，`0<p_L(λ)≤1/(λ+μ)`，所以

```text
D=⟨f,AA* p_L(AA*)f⟩ ≥ μ‖Z‖²， ‖Z‖≤zbar=fbar/(2√μ)。
```

D=0恰等价于这个current的A*f=0。源fbar保留完整2^504配对：
`PFP=(Pχ_out)(FP)`中只将`Pχ_out:L²→L²`作为HS。
原230词的完整二阶微分生成L：一条方向按双H²的HS输入支付，另一条按有界
H²方向支付，唯一无界A及其core伴随始终用`H²→L²`界。
令G为四轴域转换源常数、ρ为真实双腿逆界，定义

```text
K=M²+L fbar+M L zbar+L² zbar²/4，
η=(1+K/μ+4ρG zbar+2G zbar/α)⁻¹。
```

原二阶Taylor余项给真实非线性式
`‖f(C+ηX)‖²≤‖f(C)‖²−ηD`。
同时`ηG zbar<1/(4ρ)`且`ηG zbar<α/2`，新Cl保持严格增生与原双腿H²域。
同一新Cl的近邻逆比<1/4，全部132响应及原energy／force按原230表重建；
新逆尾界为`4ρ/(3·4^m)`。这给每个有限L的实际源更新，不预设无限迭代收敛。

## 每个有限更新的全阶Borel保持

`source_borel_update_smoothing.py`使用`K_r(T)=‖T:H^(−r)→H^r‖`。
每个原Schur词与反序伴随都只含一个原二阶响应B_w；内侧因子保持K_(r+2)，
B_w用原`H^(r+2)→H^r`界，外侧因子保持K_r。原57grade投影在K_r上的
块Schur界为57，不把它在HS上的收缩界挪用到这里。

同一normal polynomial的实际有界算子T_n满足逐项预算

```text
U₀(r)=Fbar_r，
U_(j+1)(r)=q U_j(r)+A_r A*_(r+2) U_j(r+4)/(M²+μ)。
```

原四力具备所有K_r界，故每个有限长度的Z、X与ηX都由有限源递推支付。
只有实际更新`ηX=η ψ P Z P ψ`两端具有原ψ紧支撑；P作用后的f或Z不作此断言。
Sobolev分布求值从同一算子生成核，完整Fock矩阵HS因子为2^252，
原100维Gaussian双腿给`200ε`乘下一阶核界的实际误差。

紧支核的逆Weyl积分按原相对坐标分部积分，生成每个(R,m)的真实S∞符号界。
因此该更新保持所有原Borel系数。新commutator由`2^j K_j(ηX)`支付，
与旧源jet相加生成新M_s；原步长给α_new≥α/2，同一双侧半群产生所有Hs真逆。

新230场的真实差仍按原R/J方程逐行递推，完整cone回写使新四力和平滑能量差
保留所有K_r界。源API包括`delta_bound(r)`、`kernel_bound(m)`、
`symbol_bound(R,m)`和`force_and_energy_bounds(r)`；不输入无限多项式或整个
非线性迭代在所有seminorm中的收敛。

## 当拍重新生成的有限clock历史

`source_borel_clock_history.py`以自然数stage为唯一外部索引，从同一Borel current开始。
第j拍使用level j与j+1个normal项，重新把原Schur模板绑定到当拍Cl和230场，
生成当拍f、配对伴随、方向及源η，再回写下一拍全部响应、能量和四力。
初始native表达式保留真正NI与原ψ²；后续图使用实际算子复合，cone参数各自局部绑定。

`SourceHistoryNorm(kind,stage,order,slot)`生成有限源fold：同拍按
`α/jet/C0 → force/range/M/L → step → delta`排序，跨拍只向过去依赖。
统一宽M/L按完整原词重新付费，第一拍不强等同旧单步示例的η。
原预算给`debit_j=η_j G zbar_j<α_j/2`、`α_(j+1)=α_j−debit_j`，
故每个有限stage的真逆存在；每个增量及新四力沿前节保全阶平滑结构。
真实下降逐拍给有限望远镜`Σ_(j<n) η_j D_j≤‖f₀‖²−‖f_n‖²`。

## 实际历史的极限与统一正性储备

`source_borel_clock_history_limit.py`直接消费同一历史的扣减望远镜。
令`t_m=α_m−inf_j α_j`，四轴增量在L²、H²与
`K₂=B(H⁻²,H²)`中绝对收敛，尾界随`t_m→0`。
每个增量紧，故`C∞−C_initial`紧；初始非零order0主头仍在，
没有把完整初始clock改写为NI加紧算子。

原预算的固定常数还给更强结论。`b₂=2^1313`来自原ψ的H²界，
`G=2(1+b₂²)`；原`B=ψP52`在L²中的范数不超过1。
对实际四轴HS方向Z，逐拍有

```text
Σ_a ‖η X_a‖L² ≤ 2η‖Z‖HS ≤ debit/(1+b₂²)，
Σ_a ‖η X_a‖K₂ ≤ 2ηb₂²‖Z‖HS ≤ b₂² debit/(1+b₂²)。
```

同一历史的总debit不超过α₀，故所有有限current及实际极限在整个闭锥上满足
`Re C_l ≥ α₀ b₂²/(1+b₂²) ≥ α₀/2`。
α_j是递归预算，不等于实际算子的最小实部；其下确界可以为零，
而实际共同clock仍保留上述统一正性。该推论不改变原η或引入新位移限制。

一般退化约化仍由`source_limit_cone_kernel.py`完整保存：正仿射锥的内部核共用P₀，
132条件分解为10个bare条件、42个child-R坐标和80个零式；
原trace恒等式把bare条件写成slots4–12的九个压缩矩阵。
全部360列原锥矩矩阵给四力PP完成，保留原能量与Q／mixed块。
对上述实际历史，统一正性直接给P₀=0，因此这一退化分支无需外供相容假设。

`source_borel_history_uniform_response.py`在这一实际极限上生成
`R∞(A)=2∫₀∞e^(−tC∞)A e^(−tC∞)dt`。
原二阶jet折叠给统一`M₂*=M₂_initial+247248α₀`；配合同一正性储备，
H²半群的二次多项式产生双腿逆界及有限辅助时间积分的指数尾界。
这不是将右腿改成伴随，也不要求整个无限历史在所有Hs中收敛。

同一两点逆恒等式逐条输运全部230后缀，给以`t_m`为因子的实际差界。
所有原20／4×57项在完整闭锥上共同有界，原`r dr AvgS²`积分因此存在且与历史极限交换。
K₂增量插入唯一源A时，左右两种乘积分别通过H²与H⁻²支付，
原裸源始终使用其`H²→L²`及分析伴随界。
由此全部非bare响应差在L²算子范数中收敛为紧算子，四个真实极限力紧；
能量只声明相对初始能量的差有界且紧。
`limit_L2_readout_bounds()`直接给这些实际力的源范数，供极限处的新Schur与更新消费。

## 极限处的完整Schur与新源更新

`source_borel_limit_schur.py`把原920方向的逆／Jordan导数重新绑定到上述真实极限230场。
全部16项Schur及全词反序伴随使用当前Cl、原锥binder和真实力，
`A Z=P52 S[B Π_T Z B†]P52`在同一实HS空间上有闭源界M。
原唯一二阶源通过两腿H²域支付；其完整二阶变分给L。
紧力的原双ψ支撑沿范数极限保持，故原χ_out P52的全Fock HS界给当前f的范数。

`SourceLimitSchurNorm(0..2).evaluate_source()`生成这三个有限源fold。
令`μ=M²`、`y=f/(2M²)`、`Z=−A*f/(2M²)`、`X=B Z B†`；
沿同一非线性源步长公式，以真实统一下界β=α₀/2替代旧递归预算。
它生成新clock与全230场、132方程及原能量／四力，满足

```text
Re C_new ≥ β/2，
‖f_new‖² ≤ ‖f‖² − η‖A*f‖²/(2M²)。
```

新真逆的近邻级数比小于1/4；m1／m2完整消费者及每个230词的W误差均由源递推生成。
所需域为L²、H²、K₂和实HS，不从有限阶段的S∞保持推断无限历史的全阶正则性。
此口生成实际下一步；当前梯度为零时，剩余责任仍是原Schur伴随核中的完整forcing。

## 完整极限的径向范围与裸源余核测度

`source_borel_limit_radial_measure.py`直接把原230词、920方向的径向恒等式
绑定到全部57grade的实际非自伴C∞，得到`S_C[C]=−2(F+A_bare)`。
原`V_L=B P_L`的双heat Gram在整个100维Hermite次数球乘完整Fock上正定，
生成`E_L=V_L G_L⁻¹ V_L†`及实际`X_L=E_L C∞ E_L=B Z_L B†`。
标量空间投影保留real-upper tangent，故无需把完整C∞改成自伴或grade0。

原16块Schur的每个展开项只有一个二阶源门。固定外P腿用W及分析伴随W界支付它，
另一腿的ΠP是HS；同源半轴和锥积分有共同上界。
因此支持内一致有界的strong-*方向经过Schur在HS中收敛，
实际`A(Z_L)→−2(f+a)`，其中`a=P A_bare P`使用原四bare源及一次Y。
Π仍是实际支撑投影，不要求它保持H²，也不要求E_L的H²范数一致有界。

在当前实HS上令`K=A A*`、`Q=I−K/M²`；闭源M给`0≤K≤M²I`。
同一算子的有界自伴PVM生成`ν_a(E)=‖E_K(E)a‖²`。
整数API生成`b_m=Q^m a`、`q_m=‖b_m‖²`以及完整矩展开，且

```text
q_m−q_(m+1) = ⟨b_m,(2K/M²−K²/M⁴)b_m⟩ ≥ ‖A*b_m‖²/M²，
b_m → P_kerA* a， q_m ↓ ν_a({0})，
P_kerA* f = −P_kerA* a。
```

这给出真实force余核投影为零与裸源零原子为零的等价。
完整F归零还需另生成当前`A*f=0`；未把零原子、谱隙或统一收敛率作为输入。
该测度属于实际Schur的normal算子，独立于seed谱及完整物理Hamiltonian谱。

## 原Gauss源的共同中点核

`source_borel_limit_gauss_midpoint.py`消费原全Gauss恒等式
`A_i=Σ_j G_ij(q) D_j`，其中`G=(L Lᵀ)⁻¹`，`D_j`为原slots10–12。
Gauss图不改变六个coframe坐标，原半密度与G通约，D不含coframe动量；
因此完整未截断Weyl叶的同式保留全部零阶和CAR项。
原βθ在同一符号处相乘，再作原ψ双腿限制，直接给

```text
K_Ai(x,y)=Σ_j G_ij((x+y)/2) K_Dj(x,y)。
```

这里是同一Weyl核的依赖读数；把G移成端点左乘或两端Jordan平均会改变表达式。
原ψ支持的凸中点盒保持L可逆；原χ_out生成
`G_ext=I+χ_out(G−I)`，其全阶导数由实际Laurent矩阵及原cutoff有限fold支付。
过滤后的原次序是`P52 M_mid(G)(D) P52`。
替换这三个bare输入后，同一actual K/PVM、所有q_m和ν_a完全一致；
独立bare输入因而归约为完整lapse及已经进入Schur的三个Maxwell cross。

## 过滤后的同源Gauss有界因式

`source_borel_gauss_filtered_factor.py`进一步支付完整实HS³载体上的连接。
在两个100维核变量上令`W=P_x P_y`、
`D=(1−Δ_x)²⁶(1−Δ_y)²⁶=W⁻¹`；原次序对应`T=W M_(G_ext) D`。
其伴随`S=D M_(G_ext) W`具有有限Leibniz展开。
每个打到中点G的导数产生1/2，剩余各腿的至多52个导数被原P52支付。
105组完整系数由`(1+100(1+t/2)²)^52`生成，总和为`226^52`；
不打到G的项先精确合并为G乘子。原源104阶jet遂给S及T的有界延拓。

原外盒内L的六个非零条目均不超过2，故`G_ext≥I/24`。
同一源逆矩阵的导数满足
`U_m≤24 m! (1+24 C_m)^m`，`C_m=3 SourceMidpointExtensionJet(m)`。
再次有限展开生成`T⁻¹=W M_(G_ext⁻¹) D`，两侧逆恒等式从Schwartz核延至完整HS³。
G的实中点对称性与全Fock标量性同时保留算子伴随和原分级。

实际源消费者为

```text
a_shift=T (P52 D_cross P52)，
⟨u,a_shift⟩_real=⟨T* u,P52 D_cross P52⟩_real。
```

原D_cross通过其H²→L²和支撑界给HS输入，分布核上的`D W=I`支付该等式。
完整lapse、actual Schur／normal PVM保持原值，因此全部q_m与ν_a不变。
T是由原源生成的有界同构；没有把P与中点乘法交换，也没有要求T与normal零谱投影通约。

## 完整seed Schur的共同闭形式与内部零谱

`source_borel_schur_seed_attack.py`把原920列精确代入`C=(N,0,0,0)`，得到
`S_seed(X)_a=−Σ_b(K_ab X_b+X_b K_ab)/(2N³)`，其中
`K=[[tr S,2dᵀ],[2d,tr(S)I−S]]`使用原slots4–12。
未截断K的每个native color有六行Maxwell平方
`D(e,b)(x₀,x)=(e x₀−b×x,b x₀+e×x)`；原九个divergence支付排序。
实际磁交换子非零，电PVM只消费其电分面。

`source_cutoff_schur_form.py`保持原`w=√(χ(2ρ)θ)`与ψ，构造
`Q=D_raw ψ OpW(w) ψ`及`P=Qbar†Qbar`。
原完整Gauss／half-density桥保留target的adjoint-color×CAR作用。
scalar w使两项一阶Weyl贡献精确相消，完整三项余式E₀仍按原Taylor积分消费，给

```text
K_cut=P−E， E=ψ OpW(E₀)ψ， ‖E‖≤M_source。
```

E的全配置moments由原源有限fold生成，因此K_cut有相同core上的半有界自伴实现。
原jet再以源长度`ε_H=N/[1024(1+M₂)]`重标度，给实际H²_ε小扰动；
裸源范数同步保留ε_H⁻²代价，不据此填完整Schur的相对逆界。

`source_seed_schur_form.py`在四份HS的同一clock index上令`J(X)_a=X_a†`。
原K的entry对称与core对称给右作用`J L_K J`；两腿形式在真实稠密交域求和闭合。
令`T=P_pair−(E_L+J E_L J)`，则`T≥−2M_source`且`S_seed=−T/(2N³)`。
取`μ_shift=2M_source+1`，同源有序Neumann和生成
`R=(T+μ_shift)⁻¹`，其尾界为`[2M_source/(2M_source+1)]^m`。
这些shift和Sobolev长度均是求解器参数，物理参考尺度仍为`1+4π²`。

`P₀=s-lim_n [I−(R−μ_shift⁻¹I)²]^n`是完整seed的实际零谱投影，
双索引有限filter保留显式误差。真正`Π=1_(ψ>0)`通过闭形式约化K；不要求Π保H²。
两腿的四个支撑角分别保持，双外角在核中，混合角不被误写成零模。
原native F满足`ΠFΠ=F`，所以`P₀F`的三个外角为零，留下真实内部读数。
非局部滤波后的`f=P52 F P52`不套用此支撑断言。
该辅助seed谱不替代当前Borel Schur、完整Hamiltonian或proton的谱消费者。

## 原 native electric 的共同连续谱

`source_electric_joint_spectrum.py` 直接使用原商前103维chart：其条件仅涉及coframe与scalar61，
Gauge36为整个线性空间，Number权重不依赖A。原native Gram G的行列式为1536；
配置Haar与对偶Haar的系数分别为`(det G)^(3/2)`及其倒数。
`SourceQuantumGaugeTranslations.lean` 在该原载体上生成强连续复酉Gauge36平移群，
保持整个chart、Number测度与原严格内部Cc∞域，并核对
`U_a⁻¹ T_h U_a=T_(R_a h)`；原Γ逆方向保持。原光滑代表的`−i`方向导数公式也已逐点回读。
同一完整加权Fock空间上的partial Fourier因此把六个原电算子送到实乘子
`E=Π G⁻¹ Πᵀ/2`，其最大乘子域生成六个强对易自伴闭包及实际共同PVM。

白化 `X=ΠG⁻¹/²` 把对偶Haar精确变成dX。Gram极分解给出联合谱的测度类

```text
E>0:  dν(E) = [131072 π^16 / 42525] det(E)^4 ∏(i≤j)dEij.
```

联合谱为PSD3，rank3投影为恒等；`Q_E=tr(E)I−E`正且injective，其逆取真实稠密乘子域，
没有统一谱隙。该PVM与原residual3的`Γ⁻¹×chartFlow`强对易；只在原作用实际保持的chart上消费。

原A_source中心Gaussian的Fourier变换保留真实相位。源生base67紧支撑归一与原单位N2纤维
给出完整103维单位波包，其电Gram概率密度为
`[2^18/Γ₃(6)] det(E)^4 exp(−2 tr E)`。
六均值为`(3,3,3,0,0,0)`；电trace热作用范数平方为`(1+t)^−18`，
电trace逆作用的范数平方为`1/68`。原非恒等逆向Γ列、真实矩形谱投影正反例和完整源配对
均由独立算法复现。

这是六个原电算子的实际连续谱；Gauss100局部能量通过原disintegration桥关联，
完整相互作用H谱及外腿相空间保留各自算子与载体责任。该N2测试态不自动充当Gauss不变态。

## 原完整时间 Hessian 的闭形式与自然逆

`source_native_time_jacobian.py` 从原 Hodge 和13个时间权重直接生成四力的208个
有序一阶系数。原 coframe、scalar、matter、Y 对时间均为仿射；二阶变化完整保留
电、磁及混合项。在商前 native103 的原齐次连接族上，

```text
B = ([A2,A3], [A3,A1], [A1,A2]),
S = v L^-T (E + 2 B G B^T) L^-1,  T=tr S,
K = [[T,2d^T],[2d,T I-S]].
```

原 Gauge 部分傅里叶变换后含真实四阶磁微分项；六电算子的共同谱保持其原组件范围。
实际3479项 native 系数、全部13个原子与四力经独立 Gaussian Wick 算法回写，
位移动量处的 mixed 项非零，原 Y 只消费一次。

以源 Gram 的真实平方根定义
`a=√(v/2)L^-T(−i∂A)B_G^-T`、`b=√(2v)L^-T B B_G`，
原紧支撑光滑域上的72行算子为
`D0(ν,u)=(aα ν+u×bα, bα ν−u×aα)α`。
九个收缩磁导数全部为零，故原排序精确给出 `D0†D0=K`。
稠密形式伴随生成其图闭包 D；闭形式 `‖DU‖²` 生成唯一关联正自伴 K。
沿原图域逼近回写原微分作用，无额外 extension 或 core 前提。

`SourceQuantumGaugeCenterMagnetic.lean` 支付原 Lie 中心的范数1、左右中心性，
以及实际连接磁 Gram `162/625 I3` 的非零 minor。
闭 D 方程按紧支撑测试配对保持分布意义；中心三个不受限配置坐标的 Fourier
变换把零核中的 lapse 限制到 `p_center=0`，该集合测度为零。
剩余 shift 满足 `u×bα=0`；实际非零磁多项式 minor 给出几乎处处 rank≥2，因而 u=0。
这证明整个闭形式域的 `ker K=0`。中心磁场为零的陈述限于上述原齐次连接族。

`source_native_time_hessian_inverse.py` 据此生成
`K^-1=∫λ^-1 dP_K(λ)`，其稠密自然域为 `∫λ^-2 dμ_f<∞`，精确等于 ran K。
完整电磁算子没有统一正下界：白化后的原规范坐标取行宽度 `(r^-2,r,r)`，
沿同一 N2 base67 包构成单位态，第一 shift 的真实形式值为
`33〈q0(q2²+q4²+q5²)/(q2 q5)〉/r²`。
常数33同时消费12维电项和原结构常数平方范数60的磁项；它不是纯电谱下缘的移用。

四个算子变化使用 `HS(H)^4`。左右 K lift 共用同一个四分量指标；它们的实际主符号
交换子非零，不能代换成双侧指数半群。两者闭形式的平均生成正自伴 J，且 `ker J=0`。
原光滑有限秩测试同时属于两个 lift 的算子域，表示定理直接给出
`J(X)a=Σb(Kab Xb+Xb Kab)/2`，无需假定额外共同 form core。
`L_cl=−N^-3 J` 是原四力在 `(N I,0,0,0)` 的有序线性化的闭形式扩张。

`source_native_time_force_packet.py` 用原 source base67 包和 A_source 中心 Gaussian
生成归一化 ψ，逐点重建 live `(q,x)` 原系数及全部103个真实一、二阶导数。
四个 `F_a ψ` 都有实际源平方范数积分：base 系数为紧支撑光滑函数，规范变量为
次数至多4的多项式乘 Gaussian。原 Y 保留；在变化 coframe／scalar 处冻结源点系数
会留下已算出的非零缺陷。
于是 `B_a=|F_a ψ⟩⟨ψ|` 是完整四分量 HS 源，其核与范数由同一原配对生成；
原无界力 F_a 本身未被当作 HS 算子。

对该真实 HS 四力源 B，`Δε=N³(J+ε)^-1 B` 属于 D(J)，并严格满足
`B+L_cl Δε=ε(J+ε)^-1 B →0`。
更新本身在 HS 中收敛当且仅当 B 属于 J 逆的自然谱域；非线性四力的全域
Fréchet 可微性和二次余项收敛不由这条闭线性化恒等式代填。
此谱是完整时间 Hessian 的谱，完整物理 Hamiltonian 和质子寿命继续使用各自消费者。

## 原中心动量生成的定量四力响应

`source_center_clock_response.py` 消费完整 J 及上述实际四力源 B。
原中心三个规范方向的 Fourier 变量与 coframe 乘法共同降低 J：光滑酉字符保持原测试域，
继而保持闭图；其谱投影保持闭形式与算子域。有界可测投影不被误称为保持光滑测试域。

令 `wL=√(vL/2)L_L^-T pL`、`wR=√(vR/2)L_R^-T pR`，`W=[wL,wR]`。
完整 J 的中心平方和等于
`diag(tr(WᵀW), tr(WᵀW)I−WWᵀ)/2`。
因此实际乘法投影 `Pδ=1_{λmin(WᵀW)≥δ}` 降低完整 J，且在其像上 `J≥δ/2`。
`Pδ B` 自动进入原 J 逆的自然域；非中心电、磁项全部留在这个逆中。

原 scalar／Gauss 矩阵和完整 normal 系数给出 B 在左中心变量上的 Gaussian 多项式次数至多2，
右变量保持原 Gaussian。source 和 live q/x 两个消费者逐 CAR 支付实际部分 Fourier 与 Parseval。
原67维盒生成 `(1/3)I≤TTᵀ≤(3/4)I`；中心三变量的正交 Hermite 评价核精确为
`5/2+2|p|⁴`。真实3×2 Gram 的较小特征值服从 `Exp(2α)`，两个特征值之差服从
`Gamma(2,α)`；原 Gaussian 积分直接生成

```text
‖(I−Pδ)B‖² ≤ (236439/32) δ ‖B‖² < 8192 δ ‖B‖²,  0<δ≤1.
δ_n = 2^(-2n-13),
Δ_n = N³ J^-1 Pδ_n B,
‖B+L_cl Δ_n‖ ≤ 2^-n ‖B‖,
‖Δ_n‖ ≤ 2^(2n+14) N³ ‖B‖.
```

这里的 B 范数是已构造的原四力平方积分，未外供常数或负谱矩。
同一 resolvent 还生成有限更新 `N³Σ(k=1..m)(J+I)^(-k)Pδ_n B`，其原残差精确为
`(I−Pδ_n)B+(J+I)^(-m)Pδ_n B`，两项正交。
源生 `m_n=2^(2n+15)(n+1)` 给出显式有限运算的误差界。
这些是实际原力的定量线性响应；未滤波更新的收敛和原非线性余项保留为各自责任。

## 同一源波包的原非线性更新

`source_clock_packet_descent.py` 保持四个仿射 atom 在原 force 中固定为 `−A_a`，
含完整 Y；变化仅由九个原规范 atom 产生。
以已经归一化的 ψ 定义 `B_a=|F_a ψ⟩⟨ψ|`、`D_a=N³B_a`，并令
`C_a(s)=C_seed,a+s D_a`。s 是算子变形参数，不是物理时间。
每个 D_a 两端都是原 base 光滑、Gauge Schwartz 向量，全部九个规范 atom 的左右乘法
具有实际有限平方范数积分。

所有 D_a 共用同一 bra。对原 cone 中的 `ℓ=(1,−rω)`，
`D_ℓ=Σℓ_a D_a` 满足 `D_ℓ²=η_ℓ D_ℓ`，其中 η_ℓ 是同一源内积。
实际 Jordan 逆在原 atom A 上具有闭式

```text
R_(N I+s D_ℓ)(A)
 = A/N − s(D_ℓ A+A D_ℓ)/[N(2N+sη_ℓ)]
   + s²D_ℓ A D_ℓ/[N(2N+sη_ℓ)(N+sη_ℓ)].
```

双侧代回保留完整非交换顺序，η_ℓ=0 时公式仍成立。原 cone 的全部有限词作用于
`V+Σ_j A_j V`，`V=span{ψ,F_0ψ,…,F_3ψ}`；原无界 force 与其有限秩变化各自保持原域。
这给出实际解析曲线 `R(s)=F(C(s))Pψ`，而非只指定一阶形式系数。

其真实一阶项为 `R'(0)=−(JB)Pψ`。原右侧中心 Gaussian、源 coframe 盒和完整平方形式
直接给出 `Re⟨B,(JB)Pψ⟩≥‖B‖²/6`。令 `S=‖B‖`，九个原 atom 的图范数为
`G=Σ(j,a)‖J_(D_a)(A_j)‖HS`。原252个 cone 词生成确切主控多项式 `72U⁵+8U³`，
其中 `U=max(1,2/N,3N/2)`；它与 S、G 生成解析余项界及明确正步长，
使 `‖R(s)‖²≤(1−s/6)‖B‖²`。全部36个真实 `A_j F_aψ` 源列及原 Y 的 `1/N`
力归一化已独立读回；原场点值和完整源图范数积分分别消费。
这个界属于固定右 ψ 的源响应，没有给完整 J 安装谱隙。

该曲线保持原 Y，通常并非自伴时钟；这里消费的是同一 native 波包上原方程的实际解析下降。
多步更新及完整约束空间上的精确量子时钟继续由原方程验收。

## 同一右波包的有界 clock Jacobian 逆

`source_packet_clock_jacobian.py` 直接计算原 `κ_ab=⟨ψ,K_ab ψ⟩`。
真实 A_source 中心 Gaussian 的磁 Gram 由常数、线性噪声及二次噪声三项生成，
总值为 `10887/625 I3`；电 Gram 为 `3I3`，mixed d 的期望为零。
完整 coframe 前系数因此为 `23649/625 I3`。

仍用原归一化 base67 包。令 `u=M5/M4`、`v=M3/M4`、`x=δ²C2/C0`，
其中各矩及 δ=1/45 均为前文同一源积分，则

```text
w = (v(u+xv)², uv(u+xv), u²v),  c=23649/625,
κ = c diag(w0+w1+w2, w1+w2, w0+w2, w0+w1),
κ_min = c u v(2u+xv) > 0.
```

原 rank-one 列映射 `Rψ(u)_a=|u_a⟩⟨ψ|` 为等距映射。
原208个有序变分系数和实际36个规范图像逐 CAR 回写
`[DF(C_seed)Rψ(u)]ψ=−(K+κ)u/(2N³)`。
因此源压缩算子 `Hψ=(K+κ)/2` 在原 D(K) 上自伴且下有界，
有全域有界逆 `‖Hψ^-1‖≤2/κ_min`；这里未要求 κ 与 K 对易。
原 clock Jacobian 的逆界为 `2N³/κ_min`，源积分数值读回约 `0.00750165946545`。

完整原四力向量 f 因而生成 `u_source=N³Hψ^-1 f`，
其实际闭线性化读回满足 `[F_seed+DF Rψ(u_source)]Pψ=0`。
这是固定右 ψ 的压缩，完整 HS 算子 J 的零谱下缘保持。
返回域为 D(K)。同一原角的算子图核、共同九 atom 域内的定量逆逼近和原非线性重复更新
见[时钟共同图域](source-clock-common-domain.md)；没有将整个 D(K) 换成逐 atom 域。

## 权威实现

- `SourceQuantumConfigurationHilbert.lean`、`SourceQuantumHalfDensityHilbert.lean`。
- `SourceQuantumNativeDimensions.lean`、`SourceQuantumScalarOrbitDimensions.lean`、
  `SourceQuantumResidualGaugeSlice.lean`。
- `SourceQuantumGaugeSliceCoordinates.lean`、`source_gauge_slice_coordinates.py` 及同名独审。
- `SourceQuantumResidualFlow.lean`、`SourceQuantumResidualFlowMeasure.lean`。
- `SourceQuantumResidualChartFlow.lean`、`SourceQuantumFockGauge.lean`、`SourceQuantumFockGaugeHilbert.lean`、
  `SourceQuantumFockGrade56.lean`、`SourceQuantumGaugeTranslations.lean`、
  `SourceQuantumGaugeCenterMagnetic.lean`。
- `source_coframe_volume_shape.py` 与同名 `independent_` 程序。
- `source_common_volume_pencil.py` 与同名 `independent_` 程序。
- `source_temporal_cone_resolvent.py` 与同名 `independent_` 程序。
- `source_principal_clock_cone.py`、`source_clock_subprincipal.py`、
  `source_clock_principal_jets.py`、`source_clock_second_order.py` 及各自独审。
- `source_clock_symbol_recursion.py`、其独审及压缩微分 DAG。
- `source_clock_characteristic_cone.py` 及同名独审。
- `source_symbol_compact_majorants.py` 及同名独审。
- `source_weyl_leaf_majorants.py`、`source_clock_dag_majorants.py`、
  `source_clock_smooth_symbols.py` 及各自独审。
- `source_weyl_quantization.py`、`source_weyl_composition.py`、`source_positive_energy_form.py`、
  `source_local_energy_evolution.py`、`source_cone_sylvester_parametrix.py`、
  `source_clock_linear_response.py`、`source_electric_joint_spectrum.py`、
  `source_native_time_jacobian.py`、`source_native_time_force_packet.py`、
  `source_native_time_hessian_inverse.py`、`source_center_clock_response.py`、
  `source_clock_packet_descent.py`、`source_packet_clock_jacobian.py` 及各自独审。
- `heavy-exchange-envelope/compute.py` 消费上述精确范围及同一源码绑定。

这些对象供共同量子传播和谱消费者使用。完整 Hamiltonian 扩张、proton 不变识别、开放道和
宽度不由局部系数或静态谱代填；寿命保持 `SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED`。
