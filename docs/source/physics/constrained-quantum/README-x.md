# 同源四块交换、动量电流与复合谱接口

本包从同一 source occurrence 生成四块树交换的静态算符、动量电流与因果响应：

原源 → 四条在壳外腿 → 固定作用留数 → CAR 复合态
     → Contact + canonical79 + dual24 + scalar61
     → 源静态谱算符 → 动态开放道与寿命

root 是 `positiveSmoothUnifiedSource; repaired Dirac-dual; SpinPair.actual;
visit10/tick16/materialEntry -> tick17 unchanged`。

## 已闭合的源对象

- `onshell-sources` 给出四条实际 252 模在壳外腿、完整 Ward 恒等式、289 场回写，以及非零且相容的动量依赖源电流。
- 上述四条右手外腿的作用极点留数是 `chi/s=sqrt(2)/2`（完整自由族保留 `χ/√2` 的手征符号），右手归一因子是 `2**(3/4)/2`。
- `normalizedDoubleOccupation` 在完整 252 模 CAR 上范数平方为 1，源正规乘积矩阵元为 `54/125`。
- 12 个守恒 sector 荷和全部 158 个顶点选择规则来自 `matter-charge-selection`；它们保持 source sector 身份，不能由坐标标签直接命名 B/L 或质子。

## 选定 probe 与完整树核

三条 `sourceColorP286Generator` 顶点在四模 `wedge²` probe 上给 selected-probe pole `-81/125`；三粒子 probe 的 2×2 块给 `-921/250`。这两个数只属于 selected probe。

新的 `full_source_rest_exchange` 消费同一源在 `p=0` 的共同 primal/dual Dirac shell：

- shell 维数 `33`；非零 source transitions `55`，transition rank `15`；
- 九条 Ward 相容行逐项在这些 source currents 上为零；
- canonical79 原点二维零模先按 source-compatible range 解出；independent-dual24 与外围 scalar61 在该 shell 的源严格为零；
- Contact 与 canonical79 合成对称四费米双线性，并在 `wedge²` 的 528 维两粒子载体上得到自伴算符，rank `406`、零特征空间维数 `122`；
- `normalizedDoubleOccupation` 的完整静态算符作用严格为 `0`，它位于 122 维零空间中，连通分量大小为 `1`；该静态结果不生成动态孤立复合极点。

因此不能把该 probe 的 `-81/125` 升级为完整树核对该候选的谱值；完整静态核给出退化零空间和精确的 source spectral carrier。动态 `p0,k` 的 retarded resolvent、开放道投影、相空间和衰变宽度仍必须由同一四块 source operator 继续生成，不能用静态零模代填寿命。

## 当前低能结论

共同作用、配对与算符域见[共同量子域](source-quantum-domain-and-cone.md)；
原完整力、约束jet运输及动态源接线见[量子延迟反馈](source-quantum-retarded-feedback.md)。

单位与 `mu0_source=1+4*pi²` 来自 sourceGeneratedUnifiedCouplings，阈值 ledger 来自 source spectral faces，有限matching修正仍需从这些谱面实际生成。外部 Lambda、任意 Z、实验质量、强子矩阵元或 B/L 命名都不是第二 completion。

寿命由同源动态谱、charge/hadron识别和开放道共同生成。当前状态及责任统一见[Physics active route](../../../../Lean/docs/handoffs/physics-cauchy-safe-active-route.md)；静态退化特征空间不代填动态寿命。

## 实际能量转移与零过去响应

`dynamic.py` 从原252模作用重新生成外腿及全部current，处理原elastic样本和新的非零能量转移。
后者按 `k=√2 q` 使用四个外动量
`q=(0,0,3/4),(3/8,0,0),(0,0,−1/4),(−3/8,0,1/2)`，
保留总能动量，transfer时间分量为 `−9√15 i/100`。两方向分别消费四块响应并回写完整289方程；
`independent_dynamic.py` 从原Hessian重建算符和源映射，复现两种tree赋值及作用留数归一。

`causal.py` 在原tangent生成的removed9截面内新生成零过去Ward completion：
`Ĵ(λ)=j₀/(λ−r₀)−b`，其中 `b` 在该九坐标支持内唯一。它保持正时间外腿current、原驱动频率留数
与scalar70，补上初始 `−δ₀b`；仅改变逆的频率而冻结current会产生真实非零Ward缺陷。
对上述非零能量transfer，完整四块解给59次分母、严格根界 `|x|<8`、`x=λ/(6√15/25)`，
以及 `P₁δ′+P₀δ+θ(t)cO exp(ctC)e`。完整289多项式方程及所有初始分布项逐项成立。
这是固定空间transfer、指定源准备的因果响应；安全Laplace半平面由实际companion系数生成，
不以任意 `η>0` 或 `η→0` 代填。精确范围由 `independent_causal.py` 独立检查。

`causal_pair.py` 由第二条真实源独立生成另一ordered因果响应。两完整函数不同，驱动留数相等；
两条实际reader的时间相位分别运输所有δ导数。合并后的最小分母次数117，δ′系数为 `5√6/288`。
`causal_fock.py` 将两项接成 `c†₁ c†₃ c₂ c₀`，全部16个外模占据态核验符号与荷；
其零频谐波驱动留数精确回读完整归一direct tree系数。该驱动极点不命名为复合粒子极点。

## 全动量响应与整个自由电流族

`all_momentum.py` 从原作用构造符号 `x,q` 上全部79／24分块双侧逆和scalar61 Green，
`p=(c x,0,0,i√2 q)`、`c=6√15/25`。79的10块、24的6块分别覆盖完整载体；
其时间分母对每个实 `q` 都monic，scalar分母也有常数非零首项。点值逆在生成分母非零处消费；
因果响应在由实际系数生成的安全Laplace半平面消费。
源码给出 `P=I−E(CE)⁻¹C`、`CP=0`、`P²=P` 和全289场回写；P作用于**频率依赖源电流**，
正时间current的零过去切换同时生成初始补源。该接口不要求任意静态CAR态被Ward算符湮灭。

每个分母的总次数等于时间次数。置 `r=max(1,|q|)` 后，归一companion系数有源生成的常数界，
极点模及时间生成子至多线性增长于r；在任意有界动量域共享实际Laplace半平面。
精确大系数保存在 `all-momentum.json.gz`，`independent_all_momentum.py` 直接检验多项式witness，
不调用构造求逆器。计算采用精确Gaussian多元分数自由消元，双侧identity仍逐项检查。

`all_momentum_causal.py` 将每个完整矩阵逆转成实际全半径状态空间，逐项生成
`Q(D/c)δ₀ + c O exp(ctC)E θ(t)`、全部接触和普通核的初始两jet。
canonical79的22维块有真实δ′，另五块有δ；dual24和scalar61在该逆层没有瞬时项。
原source-map、field-lift和Ward projector的微分作用继续保留，不能从逆层阶数猜测合成响应的接触阶数。
每块都有源系数生成的有界动量域范数界与安全半平面；普通核可作用于该域的L²波包，
δ导数则消费光滑时间测试或具备相应导数的实际源。这没有向原作用加入UV截断。
独立程序用 `R=N−Qd` 重建余项，从原作用重新验证17族的双侧多项式身份、全部δ系数、两初值jet和范数界，
不调用构造方的多项式除法。

`world_momentum.py` 消费原三圈完整多项式合同和Lean可测paired alignment，
将同一发生的field／source分别按 `L`／`L⁻ᵀ` 运输到任意实三维动量；±k使用同一frame。
它连同scalar70的J9／P61及25/36分解运输完整四块。旧world minor为零的方向仍有源响应，
零动量读回恒等frame。不同截面的场可相差零源方向；原实际相容reader保持同一配对。

`free_current_family.py` 不选本征spinor：从常数 `F:C²¹⁶→C²⁵²` 生成全部97个八变量电流矩阵，
保留完整谱投影、两侧Dirac Ward因子化及源Noether归一。70个scalar和24个dual源在该自由族恒零。
`free_current_dynamics.py` 进一步由左右真实Hamiltonian生成
`J_a(t)=exp(iH_out t) B_a exp(−iH_in t)`，保留六个独立空间动量并逐矩阵证明
`C_space B+C_time i(H_out B−B H_in)=0`。真实初值缺陷 `C_time B` 进入同一个P的δ补源。
独立程序从原252维先相乘再压缩，复验全部affine系数、时间Ward及作用／Noether归一。

`MomentumFock.lean` 是任意有限标签上非可分四腿核的正式代数consumer：直接用原CAR生成quartic算符，
给出完整两粒子矩阵元、总荷及粒子数定理。独立 `MomentumFockAudit.lean` 消费两ordered任意系数，
验证其和与交换负号；两文件均strict、仅标准三公理。整个连续物理Hamiltonian未被该generic consumer代填。

## 两有序的完整动量四腿核

`multiparticle_kernel.py` 消费整个216自由载体的原2／4维块目录、97个时间电流和全三维Green。
每条流保留完整内部指标；真实Sylvester生成其半轴源，reader的各个时间相位移动完整响应参数，
同时移动瞬时接触。两种次序分别生成，最终按原作用的 `−1/2` 相加。
这里每条腿使用同一源的正Noether坐标框架，原有符号作用留数另外保留，没有再乘统一的四腿因子。

非轴向两组完整doublet的消费者覆盖 `4×4×4×4` 全部指标、13+13个实际时间频移；
全部256系数非零，两个ordered不相等，漏reader相位使256项都产生偏差。
独立程序由原252维顶点重建电流，直接解16维Sylvester及原canonical算符，逐项回写289行并比对全部系数。
全轴向半径上的prepared dual24零式和初始Ward接触另直接核验。
矩阵见证保存在 `multiparticle-kernel.json.gz`，独立回执同时绑定压缩文件和解压内容。

该核是 `J₂(t)·[G_ret*J₁](t)` 的实际源驱动读数，可逐系数进入quartic CAR。
其驱动频率不自动成为复合粒子极点，也不能将这个拉普拉斯读数直接填成谱方程的自能。
谱消费者需要同一原作用生成的物质—场反馈；完整252的canonical反作用保留独立dual与coframe时间主部。

## 完整物质的canonical反作用

`full_matter_ports.py` 从原Dirac-dual密度生成 `E=N C₀`、空间项K和 `H=−i E⁻¹K`。
每个原密度顶点分为 `V_a=E_a p₀+K_a`，其Hamiltonian切向为
`W_a=−E⁻¹ E_a H−i E⁻¹K_a`。全部158原顶点和97活跃方向均回写原方程；
coframe的逆时间主部导数真实非零，不能只保留后一项。
正式单位CAR动量是 `p_CAR=−iχE`，原场方程上严格有 `χV_aψ=−p_CAR W_aψ`。
这把作用电流与反作用端口接在同一归一上，不把Hermitian电流矩阵直接当Hamiltonian切向。

完整12sector荷继续保持。原free216经实际端口生成22个补方向，并在174个非零H／W系数下闭合，
得到238维最小不变载体。独立源投影计算证明其14维补空间包含原occupied H12全部12维，
另两维是right Λ² e34；该238载体不能替代完整物质系统。
回执保留全部252矩阵、free／补空间双向端口及原生闭包列，后续有限场反作用直接消费它们。
独立算法从原phase系数重建时间主部的单项逆、全部切向和逐步张成关系；正式Source／CAR的相关口strict通过。

## 局部原作用反作用与非线性forcing

`spectral_splice.py` 将原regular harmonic四块场的phase0实系数作为有限场扰动，
从同一 `adj(e)`、`det(e)`、connection和Yukawa重建完整252局部Hamiltonian。
其超出线性切向的760项、原prepared输入上的8项反作用和35个真实current反馈均独立复验；
原 `ψ=2w, χ=2√2w†S` 的 `4√2` 幅度保持。这是有限局部配置的原作用反作用，未代填自洽时空史。

`spectral_splice_linear.py` 直接将原289场中的primal／dual分量lift回252，
四组完整线性方程回写证明原Jacobi已经包含背景物质反馈。随后原Euler余项
`R(u)=Euler(actual+u)−Euler(actual)−Jacobi(u)` 的两侧0／1阶严格为零，
真实phase0的2至5阶逐坐标生成；漏dual散度或错用 `r·Re(Y)` 均产生非零反例。
实际jet始终是各实字段的 `−Re(r_mu Y)`，之后才lift内部复坐标。

`reaction_harmonics.py` 将整个真实Fourier pair送入原作用，保留
`∂mu=r_mu z∂z`。双侧第n阶具有 `h=−n,−n+2,…,n` 的实际谐波，
2至5阶共288项；全部Laurent系数及phase0消费者由另一卷积算法独立核验。

`native_boson_residual.py` 另从完整原密度生成二阶whole289与full70 forcing，
保留live Hodge、native非对角Gram、完整scalar协变和全部辅助行。
独立密度自动变分核验三个谐波的289行、70 scalar行及full252物质交集。
peripheral scalar61在0／1阶为零，二阶三个谐波各有4个非零源项；它们是非线性Euler余项，
没有改写free-free scalar current的零式。Jacobi更新同时消费原外腿source的变化，
保留完整289源口和原背景的线性matter Schur。

`full_jacobi_source.py` 将原已付多项式场变换直接用于完整289输入，生成完整contact、79／24源映射和九行C9。
全四动量恒等式为 `H C_contact+L79 S79+L24 S24+Lnull C9=I289`、`C9 H=0`；
响应的精确残差是 `−Lnull C9 f`，不改写或投影实际forcing。原97源口是它的限制。
真实二阶forcing在±2谐波的Lorentz六行、零谐波的三行有非零相容缺陷；下述实际外腿电流支付这些缺陷。

`external_leg_feedback.py` 已由同一实Fourier场生成全部四条外腿的32个实际primal／independent-dual更新，
同源和交叉场、正反current次序都保留。每个完整252初值问题由实际二维cyclic载体和三维augmented发生器生成；
其中16侧有真实共振线性时间项，另16侧无。原raw ψ／χ修正的初值为零，而
`δp_CAR(0)=−iχ E_a` 的真实非零初值变化单独保留。
独立算法由原Dirac及二维特征投影重算全部更新，coframe dual时间项的16个反控制均非零。
这些是实际外腿的受迫响应，不把世俗增长系数命名为复合极点或衰变宽度。

`nonlinear_source_update.py` 将energy-transfer的第一对外腿及其真实场接回原97个电流，
保留独立dual、实际修正ket的时间导数和原顶点本身的变化。24个状态空间信号给出
`C9(D)(J2−R2)=0` 的完整时间恒等式；三个谐波的共同湮灭多项式次数为5、6、5。
独立算法从原252强迫方程递推及原密度双方向余子式重建电流，复验发生器与全部所需初值；
删顶点变化、删独立dual或冻结ket时间动量，三个谐波均有真实非零缺陷。

令实际普通forcing为 `f(t)=J2(t)−R2(t)`。原完整null lift生成零过去源
`θ f−δ₀ Lnull C_time f(0)`，三个谐波的补源分别有13、8、13个非零坐标。
全频身份 `C9 N=d C_time f(0)` 及 `C9(N−d Lnull C_time f(0))=0` 逐项成立；
bulk forcing、自由暂态和共振项全部保留。这个全时相容源可直接进入完整retarded Jacobi，
其驱动湮灭多项式不作为相互作用谱或复合极点。

## 实际二阶retarded场与scalar反馈

`second_order_retarded.py` 把上述完整289源送入原contact／79／24分块逆，
连同外围scalar61生成三个谐波的因子化有理场；全频相容、frame协变及原方程分解保持。
同一源给出共同Laplace域 `Re(x)>16`；`x=17` 的实际完整289行与70 scalar行逐项回写，
289场非零项数为194／171／194，独立dual24为8／4／8，scalar61各4项。
零空间动量仍消费时间相关的原逆，原canonical零因子保留。

`second_order_causal.py` 将原Green块与实际source companion串联，直接生成三谐波的
86／90／86维状态及全部289输出。发生器作用于原坐标时间t，`λ=c x`；proper clock仍为 `τ=N t`。
独立程序从原分子／分母核每个状态身份，再以原H₀／H₁／H₂核全部时间的普通场方程。
初始δ／δ′分别有58／5、23／3、58／5项；H(D)产生的更高分布严格相消，回读原初始补源。
`ordinary_jet(h,n,spatial_orders=(a,b,c))` 直接返回实际普通场的0⁺混合导数，
前三时间jet已独签，δ族保持独立。完整稀疏C／O／v保存在 `second_order_causal.json.gz`，
没有用一个频点或对角化代填时间演化。

`second_order_scalar.py` 直接生成三个真实scalar时间场的3维companion。
原全部70顶点对本Λ4外腿及其实际纠正双侧为零，因此外围forcing严格等于 `−P61 R2`。
该源落在25维singlet，36维doublet因子的取消由全Green分子身份支付；
原70方程、零初值和所有δ／δ′项独立核验。该场到原背景物质的完整252回读为零。

零谐波实际为 `Φ₀(t)=θ(t) f₀(cosh(c t)−1)/(2N)`，其中 `c=6√15/25`。
`+c` 的四项留数 `f₀/(4N)` 严格非零。这是当前背景的二阶受迫增长模，
其有限阶响应不代填全非线性长期演化或复合谱。

`scalar_feedback.py` 将这三个真实时间场继续送回原scalar密度，生成scalar2×scalar2的
原四阶Euler分量。九个状态乘积保留全部16个coframe和48个gauge变化；实际gauge反馈为零，
coframe反馈在五个空间谐波上均非零，首个非零时间jet为二阶，并满足全时间九行相容式。
零谐波的三个空间对角应力含非零 `exp(2ct)` 系数，lapse行的同次系数精确相消。
这保留了scalar到几何的真实反馈；其余四阶混合项各自保持，未合并成完整四阶发展。

## 原完整物质作用与实际时间生成元

`second_order_matter.py` 从原实坐标重建两侧full252读回，逐四动量证明它们与原H289的对应。
实际时间场使原primal／independent-dual Euler的二阶ordinary系数在`t>0`严格为零；
原R2及非零P61场都参与回写。三个谐波每侧各保留2项真实初始δ，δ′／δ″相消。
这些初始source与ordinary消零分别成立。

`second_order_hamiltonian.py` 直接生成完整252、所有incoming动量上的二阶canonical生成元。
原`E=N C0`、空间项K与`H=−i E⁻¹K`给出
`Q=−E0⁻¹ E1 H1−E0⁻¹ E2 H0−i E0⁻¹ K2`；它与实际97个二阶场端口及70坐标上的P61时间场合成H2。
全部时间的原系数方程和九个实际右jet独签，12-sector荷保持。
`FullTimeMatterGenerator().jet(h,n,k)`返回真实ordinary生成元的混合导数，保留
`k→k+h*r_space/i`及独立canonical dual的逆向标签；此处不把给定场历史上的生成元代填完整Fock谱。

`scalar_matter_response.py` 保留完整252输入／输出，生成1008维受迫时间实现与所有动量的接口。
三个谐波的原V虽在free→补空间块为零，canonical `W=−i E⁻¹V`却原生生成rank2反作用；
实际原free块46／47／48送到非free坐标`[3,66]`。独立dual的逆向响应另外生成，
原四条外腿在本scalar时间场中双侧严格为零。非free方向本身不命名重质量极点。

`scalar_matter_exact.py` 进一步消费原Λ6不变空间和dual Λ2商空间：
完整动力与Λ6投影实际不对易，但任意时间间隔的第二次scalar插入严格消失，
因而一次Duhamel式给出该指定scalar历史中的确切full252演化及独立dual。
不同粒子的CAR正规乘积保持；这一体结论没有删除多粒子相互作用。

## 原标量正则场与实源CCR–CAR耦合

`scalar_canonical_phase.py` 从原scalar密度生成`Π=−φdot/N`及122维正则相空间。
原61个pivot列R通常非正交：`G=RᵀR`，实际读回为`φ=Rq`、`Π=R G⁻¹p`，
故ambient CCR为`i P61`。全动量`A(k)J+J A(−k)ᵀ=0`、原Green的清分母resolvent身份、
Peierls互易式及`Hscalar(D) Gret=P61 δ`均由原密度独立复算；全部70／61原Yukawa端口保留。

`real_scalar_car_source.py` 消费原实作用的独立ψ／χ。令`p=−iχE`，
真实canonical坐标为`q=(Reψ,Imψ)`、`P=(−Im p,−Re p)`；逐原空间微分系数实化后才代入`∂=ik`。
完整两支发生器为`diag(H(k),−conj H(−k))`，实际标量力为`Re(pWψ)=−Re(χVψ)`。
两支canonical坐标是`(ψ,conjψ)/√2`和`(p,−conjp)/√2`；half与√2由原动能生成。
504是原252复变量的实坐标表达，未增加物理场库存。

`ScalarCCR.lean` 在多项式域实际实现Q与`P=−i∂`，证明全部CCR。
`ScalarFock.lean` 连接原70个Hamiltonian端口、完整252 CAR和真实tensor态，保留独立dual与不同粒子的正规乘积；
该文件的单支耦合消费holomorphic分量。
`RealScalarFock.lean` 的`diag(W,−conj W)`两支耦合进一步直接回读原实作用：
`original_real_action_branches`对任意独立χ和完整ψ等于原`−Exchange.yukawaSource`，
`original_real_scalar_force`给出联合态上的准确标量力。
旧252单位CAR保留为归一plus支；原raw变量的同模CAR为`2δ`，不能将两者无缩放认作同一算子。
六个候选／审计模块strict通过，46个公开口仅标准三公理。
这给出了原实作用的代数耦合；完整四块共同Hamiltonian、物理态与连续谱由下游消费。

`scalar_joint_hamiltonian.py` 将一个非零共轭Fourier对组织成244维实对称Hamiltonian，
而零模单独保持122维；它保留原full252物质的`k→k±κ`卷积和独立dual的反向转置，
不使用有限动量格或alias。`retained_matter_action.py` 从原289 Hessian只消去168个纯辅助坐标，
保留73个原玻色／几何坐标及48个原物质实坐标，逐动量重建79／24／Contact与9行Ward相容性。
它提供242维presymplectic Legendre接口；mixed response lift不再作为额外玻色子和CAR重复相加。
两者的独立算法分别从原scalar density与原289 primitive blocks重建。

`ScalarHamiltonian.lean` 生成共同的`H=Hscalar+Hmatter+Hint`，其原full252两支自由项保留
`−conj H(−k)`；`projected_original_real_source`直接消费任意独立χ与完整ψ。
`ScalarHamiltonianAudit.lean` 在实际多项式／Fock tensor态上分别消费位置、动量、annihilation、
independent-dual creator四条Heisenberg方程，10个关键口strict通过且仅标准三公理。
这个正式代数消费者的R／K仍为显式参数，具体源系数及连续动量域分别由其下游安装。

## 原Ward规范商的时间发生器

`retained_hamiltonian_reduction.py` 从原121作用生成正则一致初值空间。
先以`K2`的精确右逆读回商去掉冗余速度，242维降为172维；实际初值链
`Vnext=V ∩ E⁻¹(Omega V)`进一步给出`172→156→147→138`。
完整源方程`Omega C A=E C`生成时间发生器，原9个Ward函数及其时间导数恰好张成12维退化方向。
对这些原生方向取商得到126维非退化Hamiltonian发生器、能量及规范无关的商演化。

当前机器范围是零动量与原energy-transfer的非轴向动量`(−3√2/8,0,3√2/4)`。
非零动量的126是复Fourier fiber维数，现实场同时保留反向共轭fiber。
零动量`det(lambda I−A126)`精确等于原canonical79及dual24的monic特征因子乘积，
因此旧频域因子现在由原约束作用的实际时间发生器消费。
该发生器属于完整mixed Jacobi线性化；它没有给物质坐标另赋boson CCR，也不代填相互作用复合谱。

`source_full_linear_split.py`由原密度补齐整个1310实场的共同Jacobi载体：
显式场embedding与inverse双向回读7358个原非零条目，原active289、外围scalar61及
完整物质complement960共同保留。原occupied12的Hermitian投影约化全部非标量顶点，
24个标量顶点有非零单向交叉；真实背景标量源的像为9复／18实维，全部落在P61内。
全部158顶点的790个incoming系数、原70标量和97个mixed接口均由原密度独立重建。

实际尾部发生器按独立dual480、scalar122、primal480排列；令B为dual→scalar、
C为scalar→primal，则`CB=0`而`C A_scalar B≠0`，首次两段传播位于三阶时间jet。
原两个已签动量的active126与这个1082尾部共同给1208维相空间纤维。
非零k为复Fourier纤维，真实±k对合并共轭纤维；零模本身为1208实维。
该库存不代填其他动量的active商秩。独签入口为`independent_source_full_linear_split.py`。

`source_stationary_cauchy_orbit.py`把这份完整Jacobi接回实际原source轨道。
literal source的全部玻色Cauchy速度为零，原ψ与独立χ按两条不同的整数相位表示演化；
原146个密度系数及全部158顶点的任意Laurent相位恒等、原1310初始Euler和完整双Dirac
全时方程均独签。所有原双线性jet保持相位权零，因而该显式轨道全时满足原方程；
局部解析唯一性将它识别为同一Cauchy producer的literal初值发展。
完整密度先共旋再变分，精确回读`K_stat=K_orig+iωE Rp=K_orig−iωRd E`和共同1310场线性化。
原时间与`τ=N t`保持。独签入口为`independent_source_stationary_cauchy_orbit.py`。

`source_full_linear_retarded.py`沿该实际轨道生成完整1082尾部传播。
原两侧matter各240复维的90个源组件、8类小块逆及12个单向Yukawa feed生成完整real480双逆；
原70场Green与原动量符号给scalar122双逆。全算符含完整
`Rp C Rs B Rd`，两向身份与实际1082回写独签。非轴向真实初值有24维精确不变时间载体，
primal读数二阶时间导数零、三阶为`162√30/3125`；它没有丢弃任何被该初值激活的坐标。

完整tail的全实三动量因果口为`Re(z)>153√30/625`，由原matter斜Hermitian空间主部、
scalar能量界及有序Duhamel项生成。原相位响应为
`R(t) Θ(t−s) exp((t−s)A_stat(k)) R(s)⁻¹`；公开时间状态口返回普通指数因子，
retarded消费者显式乘零过去因子`Θ(t−s)`，原初始δ系数为I1082。
该统一界属于尾部；旧active289／126／canonical79／dual24仍按自己的已证口消费。
独签入口为`independent_source_full_linear_retarded.py`，共旋Laplace极点不代填相互作用复合谱。

`source_tail_schwartz_flow.py`由同一全动量界生成整个1082尾部的三维空间发展。
原`A(k)`为次数2多项式；对任意`m=|α|`，有序Duhamel词给出
`||∂k^α E(t,k)|| ≤ C_m (1+|k|²)^((2m+1)/2) (1+|t|)^(3m+2) exp(β|t|)`，
其中`C_m=10^m m! C0^(m+1) D^m`、C0／D／β均由原系数生成。
所有Schwartz半范数及时间导数因此受控，任意三维Schwartz初值生成唯一全实时间线性解；
紧时间支持的Schwartz forcing由零过去积分生成，原两端相位保持这些界。
原完整多项式、20个不限动量Gaussian混合jet及非零三阶空间cascade均独签；
全阶推导独立核对，不以有限阶检查代替。范围是实际source轨道的完整1082线性尾部，
旧active126与一般非线性全时发展分别消费。独签入口为`independent_source_tail_schwartz_flow.py`。

原`FullQuantum.Source`对任意live configuration已给出full252的非线性
`hamiltonian`／`normalizedMomentum`与原时间Euler读回。
完整原P286变量包含scalar70和独立的ψ252／χ252；不能用`active-gauge.build()`的二阶Jet
或`native_boson_residual`的occupied12展开替代它。
规范B的live本构消元与gravity simplicity已有正式口；后续Lorentz完成平方首先产生reduced action，
其几何load含`de`，必须随后重算Legendre动量，不能直接同号称为Hamiltonian contact。

当前修复的`StageNineHolonomicConfiguration.gaugeConnection`及
`FullQuantum.Source.connection`使用`P286ConnectionField`／`p286LieBlockEmbed`，为4×12端口。
母SU7全48连接、作用和驻点资产分别存在，但旧Stage5母作用证明未直接支付当前repaired根的全48动态响应。
对应额外源方向必须通过同一修复作用的限制恒等式、原电流与约束连接；母轨道rank34不计作48个传播场。
固定actual现已生成全部48母方向的一阶连接／辅助／Gauss源，精确回读native12并在横向相消；
唯一详述与独审见[同源母方向一阶源](source-mother-gauge-first-covector.md)。

## 全部标量端口与固定占据数的有序算符串

`FockRaising.lean` 从原CAR占据数算子证明：保持总占据数、每次将目标子空间占据数提高1的
算符串，在N占据sector上长度超过N就严格为零。具体矩阵的逐项grade条件直接进入原`quantize`，
没有把最终消零作为前提。`FockRaisingTensor.lean`将该结论送入任意共同玻色代数域的真实tensor态，
完整保留所有玻色因子的原有次序。独立Fin4消费者中`W²=0`而二粒子`dGamma(W)²`矩阵元为2，
第三次作用为零；另用不对易的两个实际算符核验tensor次序。

`scalar_dyson_fixed_N.py`把全部61个实际canonical标量端口分解为
`W_a=T6 W62_a T2ᵀ`，并保留原自由发展中的背景`Λ2→Λ6`项。
原全动量发展保持Λ6及Λ2商，因此相互作用绘景的端口仍提高同一占据grade。
源内`normalProduct(W0,W0)`从占据`{145,152}`到`{0,1}`的矩阵元为`27/125`，
不同粒子的作用确实保留。该机制关闭固定N的高阶有序被积算符。

## 源时间积分、Peierls项与连续动量外态

`scalar_dyson_time.py`消费全部61个端口、原Λ6／Λ2时间发生器和实际scalar CCR流，
生成非零共轭Fourier对的760个及独立零模的400个矩阵指数时间原函数。
所有源分量、原实作用两支、`k_out=k_in±κ`与独立dual均保留；最大状态维数129。
逐分量微分独审验证`O u=0`、`H u=v`、`H G=L H`，因此
`d/dt(O exp(Gt)u)=exp(Lt)v`对全部时间成立，包括共振。
这给出完整N=1标量相互作用绘景演化；另有136维实际有序二阶分量，未将单分量称为完整N=2。

`scalar_dyson_peierls.py`将同一自由CCR流的双时间交换子回读为原70场的Peierls核。
有序乘积保留Weyl二次项，Dyson常数项为`−iΔ/2`，不选择真空或Hadamard态。
完整实源的初始斜率收缩有4968个有序线系数；2396是同动量内部CAR读回的非零项数，
连续载体始终保留完整`(p,i)`标签，包括标量κ=0时不同粒子的不同动量。
原完整投影和从占据`{149,150}`到`{0,1}`生成`243√30/3125`，
对应Dyson常数斜率`−243i√30/6250`。该读数与全时间核分别保留其范围。

`WavepacketGrade.lean`／`WavepacketInteraction.lean`直接作用于
`(Fin N → M × I) → B`：动量M无需有限，I为内部模，B可承载不对易CCR算符。
逐粒子线的实际动量移位和源grade条件生成任意N长词消零，并保持带置换符号的反对称性。
独立实动量消费者允许同内部模处于不同动量，二次作用为12而任意三时间作用为零；
三个模块strict通过，24个口仅标准三公理。此处闭合连续标签的代数算符，
光滑紧支持域和时间积分交换另由源系数界支付；自由标量流作用于Weyl代数，
不假设二次自由Hamiltonian指数保持固定多项式态域。

## 同一标量作用的有限Magnus演化

`WavepacketCurrent.lean`从真正逐粒子线的源grade生成任意时间／动量的物质电流交换律。
玻色因子与物质电流分别保留，`ScalarMagnusAlgebra.lean`将原c-number CCR直接送入实际联合作用：
`[B(t),B(s)]=−i Σ Δ_ab(t,s)ρ_a(t)ρ_b(s)`，其与全部`B(u)`交换。
原始`B=−iV`包含全部scalar作用，诱导的Peierls项不另加一次到B中。

`scalar_dyson_magnus.py`消费全部一阶原函数，给出6688个非零Fourier对与3184个零模的
二阶logarithm系数recipe。每个recipe是实际有限状态：
`Z′=L_left Z+Z G_rightᵀ`，`Y′=(i/2)ΣJ_bc Z_bc`，
`Z(0)=v_left e_lastᵀ`、`Y(0)=0`；左右入射动量独立，完整矩阵可按需生成。
这是一组完整保留的recipe，不代表每条最终系数都非零。
同号scalar transfer只在完整源reader求和后消零，50个单实phase分量的反控实际非零。

`scalar_dyson_bounds.py`从原矩阵生成全部1160个系数的统一导数界。
令`|κ_j|≤R`，则增长界为`Λ(R)=27√30/100+27√15 R/125+9√30 R²/50`，
与入射动量无关，三方向微分常数均为`6√30/25`。
对`r=|α|`，实际时间原函数满足
`||∂p^α Y(t,p)|| ≤ |t|^(r+1)/(r+1) exp(TΛ(R)) ||v|| ∏ C_j^αj`。
非零源词每条粒子线至多作用一次，因而测试支持`P`变为`P+R`；这些是测试域界，不是物理截断。
源矩阵及全阶变分常数论证分别由独立原作用算法核验。

`MagnusDerivative.lean`／`WavepacketFiltration.lean`生成有限指数的微分公式，
从占据过滤律支付全部尾项，包括N=0。`MagnusExponential.lean`给同一有限多项式的双侧逆，
`MagnusTriangle.lean`生成与执行口一致的`r+2q≤N`三角展开。
这些正式口中的D为显式Leibniz算子；下面的Cauchy消费者由实际源系数支付分析时间微分，二者的认证范围分别保留。

`scalar_wavepacket_evolution.py`的`ScalarWavepacketEvolution.evolution(N)`实际作用于
`((p_1,i_1),...,(p_N,i_N))`上的CCR多项式值波函数，配置长度与N绑定。
`Ω1`逐线消费完整源原函数与Q/P作用，`Ω2`消费两条不同线的全部匹配recipe；
`U_N=Σ_(r+2q≤N) Ω1^r Ω2^q/(r!q!)`保留Weyl项。
`TimeCoefficient.realization()/exact_value()/coefficient_jet`读回具体源有限发生器，
两时间接口保持`U(t,0) U(s,0)^−1`的原次序。
当前scalar transfer为一个非零共轭对或独立零模，物质动量保持连续。

`scalar_wavepacket_cauchy.py`进一步生成实际`B(t)`与唯一Cauchy解：
全部1160个源时间交织和9872个二阶reader给出`Ω1′=B`、`Ω2′=[B,Ω1]/2`，
原源混合时间／动量导数界支付逐系数积分及FTC。
共同域按目标占据数k限制玻色多项式次数为`d+k`；非target粒子线的动量支持在K，
target线支持在`K∪(K+κ)∪(K−κ)`。原B保持这个反对称光滑域。
逐grade积分生成任意N的存在唯一性，实际有限Magnus作用就是该解，满足
`∂t U(t,s)=B(t)U(t,s)`、`U(s,s)=I`及两时间组合／双侧逆。
独立配置oracle与原密度算法复验全时身份，非恒定玻色多项式的实际N2残差严格为零。
这闭合指定scalar transfer下的真实分析Cauchy演化；完整Lean的C∞路径定理仍为单独安装项。

`scalar_momentum_energy.py`另从原完整动量主部生成全空间能量界：
`P L(k) P=|k|²P+Σk_j M_j+M0`，精确源范数为`||M0||≤2`、`||M_j||≤3√2/5`。
取比较能量中的`a=102/25`，原发生器给
`E′=−2Na Re〈Π,φ〉`，于是实际122／244自由流满足
`||exp(tA(k))||≤C√(1+|k|²) exp(153√30|t|/625)`，
`C=4√(45√2+177)/5`。独审以显式正平方分解支付矩阵范数，并核验全部源基变换。
全阶动量导数保持多项式增长，故自由流连续作用于空间Schwartz数据；
比较能量不修改原物理作用，低动量的时间增长仍保留。完整未涂抹量子相互作用与UV责任另行消费。

## 未截断的原作用与 live Legendre

共同源的实际完整 Fock Hilbert 空间、半密度等距、coframe 体积—形状算子及精确时间
cone/Sylvester 映射统一见[量子域与时间预解算子接口](source-quantum-domain-and-cone.md)。

`source_lorentz_contact.py`从原BF／simplicity与完整独立χ、ψ生成非线性Lorentz消元。
24维Hessian满足`det H(e)=256 det(e)^12`，在全部可逆coframe上给
`Ω*=−H(e)^−1(G(e)de+j_matter)`；原72辅助Euler与几何、交叉、物质三项全部保留。
完整实物质流rank8，prepared轴向rank4为其子读数；两支504维CAR系数来自同一原`Re`作用。
此Lorentz接触与scalar Ward余项之和才回读既有完整Contact。

`source_coframe_legendre.py`直接消费这个消元后的原密度。
令`h=E_spatialᵀηE_spatial`、`D_h=∂h/∂e`，真实速度Hessian为
`M=D_hᵀ Hess(det h) D_h/(4 det e)`。非特征切片给6维速度商和10条主约束；
null切片给4维商和12条约束。实际`Π_e=M dot(e)+b`保留
`b=−G_tᵀH^−1(G_s∂_s e+j_matter)`，由此生成受约束Hamiltonian。
完整64／256一二阶jet和独立dual导数返回原16条Euler。
四向BF边界通量同时保留，`θ原−θ消元=δF⁰`的消元拉回含速度、空间jet和物质依赖。

`source_scalar_legendre.py`消费原chart0的完整70实标量和12个native规范生成元。
以`h^{μν}=|det e|g^{μν}`、`b=Σ_i h^{0i}D_iφ`，原动量为
`Π_φ=h^{00}D_0φ+b`，Hamiltonian为
`||Π_φ−b||²/(2h^{00})−Π_φ·(A_0φ)−Σ_ij h^{ij}D_iφ·D_jφ/2+|det e|V`。
全部48连接端口、coframe双取向的32变分链和原140→122背景消费者独签。
`ScalarLiveLegendre.lean`将任意live coframe的原动量、速度逆和这个Hamiltonian直接接回原密度；
23个口strict独签，实际源`N≠1`及非零shift的原配置均有直接消费者。
三组Python构造各有独立原密度审计；原gravity／Lorentz、scalar各自的Legendre域分别保留。
完整共同作用的接续责任统一见active route。

`source_gauge_legendre.py`保留原native12配对、非正交Cartan和超荷Gram1。
原Hodge为`(Λ²e)^−1 J(Λ²e)`，BF消元给`B=−*_eF/σ`；
电动量矩阵由`g_00 g_ij−g_0i g_0j`及有符号`det e`生成，源背景为`N/σ`。
电速度逆要求`g_00≠0`，与标量／物质的`g^{00}≠0`分别保留；
null电块rank1时，原12条`Π_A0=0`之外产生24条约束。
全48连接Euler消费原70标量和252物质流，空间通量为`Π_Ai A0`。

`source_common_hamiltonian.py`在两个时间条件的共同域上，实际相加原coframe、
标量、规范Hamiltonian及`Ω=0`的剩余物质项。
coframe块已经消费完整Lorentz流；其对该流的导数为`−Ω*`，包括原主约束乘子，
因而物质Hamilton方程自动恢复完整连接。再次加入`H_matter(Ω*)`会重复计数。
`p=−iχE(e)`只换独立dual，原ψ保持；canonical一形式仍为`Re(i p δψ)`。
固定p的coframe Euler保留校正`−Re[χ (δE)E^−1 R_χ]`，
活系数的空间散度进入完整独立dual演化。
共同作用提供22条玻色主约束及包含三类源的native12 Gauss；
约束保持、量子算符域和谱消费者由active route另行记账。

`source_constraint_preservation.py`从原固定源势得到
`dot(G)−ad(A0)ᵀG=−2|det e|Oᵀφ`，其中`O_a=ρ_a v_source`。
因此`G=0`的保持生成9条`Oᵀφ=0`；其核投影精确回读原P61。
原标量速度继续生成`D(φ)A0=Oᵀ(Π_φ−b)/h00`，
`D_ab=(ρ_a v)ᵀρ_bφ`，保留3个源稳定子参数与退秩时的相容条件。
原scalar Euler、规范速度及完整Yukawa再生成`D dot(A0)=dot(r)−dot(D)A0`。
独审核验全部840个Yukawa协变矩阵及原Ward9；实际非零Yukawa反馈给
`Δdot(r)_2=−54/125`并改变九个`dot(A0)`分量。
这里消费满足Gauss及上述保持方程的局部场jet；coframe约束和全局共同轨迹保持独立责任。

`source_ward_contact.py`进一步由这些原约束重建完整289维联动切向`T_b`，
保留规范连接、辅助B、primal及独立dual各腿。
原作用的`M=−2N Gram9`和`J9(p)=T_b(−p)ᵀ injection97`生成全部571项Ward Contact，
加上Lorentz72项，精确恢复完整643项Contact及原289场回写。
这不是单独A0逆，保留原约束的共同Hamiltonian不再额外叠加这份消元读数。
九条完整252维Dirac-defect恒等式逐incoming／transfer系数独签，
四条实际在壳外腿消费Ward源零；离壳非零源保留，不据此要求任意静态CAR态消零。

`source_coframe_constraints.py`将原gravity／Lorentz、scalar、gauge及剩余Dirac应力相加，
生成完整16条coframe Euler。generic16-coframe的六个Lorentz Noether恒等式独签，
实际full252双侧流使六投影为零；四个时间coframe方向的`δE=0`及零动量列在离壳也成立。
它们生成四条不含纯coframe加速度的初始约束。全63内部求和采用精确tensor迹，
独审直接重算完整252矩阵电流与96个时空导数，保留独立dual。

`source_coframe_initial_constraints.py`以同一canonical Hamiltonian生成一致初值。
写`e[:,0]=(n,b)`、`φ=v+u P61 e23`、`Π_φ=r u P61 e23`，
`ψ=ψ_source+α e135`、`χ=χ_source+β e126`；其真正源点是`u=α=β=r=0`。
原源coframe／规范动量重新计算为零，整个族的共同Hamiltonian给
`a=9/5−αβu/2+(73/200−r²/4)u²`、`b=0`、`n²=(486/625)/a`，域为`a>0`。
原点回读`N²=54/125`，四约束Jacobian行列式为`800/3`。
非零`u=1/4, α=β=1, r=1/3`生成`n²=559872/1221175`，
其原四时间Euler、Gauss、C9及完整物质方程精确成立，标量速度和Yukawa源非零。
这些是由原方程生成的局部一致数据；原初值族的参数导数不代替完整canonical流。

`source_temporal_coframe_flux.py`将四个时间coframe的空间导数收进原Hamiltonian通量。
离壳身份保留主约束乘子的平移：`H(g,λ)=H0(λ+δλ)+Π:Jg`；
在原10条主约束及其30条空间延拓上，四条真实约束成为
`F_a=−∂H0/∂e_a0+Σ_i ∂iΠ_ai`，未知time-coframe的空间微分项消去。
独审以完整252物质和原Legendre图生成动量jet，四个非零通量散度直接回读原Euler。
点上满足主约束不能代替空间延拓；这里的三向Hamiltonian通量和原四向BF通量分别保留。

`source_joint_temporal_rates.py`从完整canonical向量场生成四个time-coframe与九个broken A0的联合更新。
在前述初值族加入原规范动量`Π_Ai=γ A_i G_native`后，
规范系数为`c_γ=162/625+9γ²/100`，源约束给`n²=3c_γ/a`。
完整状态切向在实际初值处冻结，再对time-coframe求导，生成约束forcing；
这保留全部场和动量的变化，原源的能量导数为零并不使约束forcing消零。
联合13维矩阵为`[J4,0;B,D9]`，`B`由原标量速度对time-coframe的导数生成，独立非零消费者保留。
`u=1/4, α=β=1, r=1/3, γ=1/5`给`n²=567648/1221175`、
`dot(n)=103923/244235`及`dot(A0)_2=−283824/1221175`。
原动量律再生成coframe／规范／标量加速度；同一二阶时间jet上，
完整1310条原实Euler、主约束10、Gauss12、C的一二阶及四时间约束保持全部精确成立。
独审从原密度重建全canonical切向与加速度；该消费者的空间范围为齐次初值，完整时间发展由active route接续。

`source_homogeneous_canonical_flow.py`生成一般齐次初值上的完整canonical向量场，
保留非零空间coframe速度、真实`dot(E⁻¹)`、Lorentz消元的`dot(G)`和速度商`dot(Q)`。
原八组变量的共同Hamiltonian方向导数由未拆密度独立重算，完整1310条原实Euler直接回写。
六个Lorentz主约束以原动量minor求解，`φ`取原61切片；四时间coframe由原约束的
解析隐函数分支生成，九个broken A0再由原D9逆生成。原source的三个非退化量为
动量minor行列式`−1`、时间Jacobian行列式`800/3`、D9行列式`256`。
这给1229维实坐标上的解析ODE；原Noether支付整个坐标图的约束切向，
Gauss零初值由其线性齐次保持方程传播，无须假设Gauss零集是正则流形。
因此源附近一致初值在固定六Lorentz／三稳定子代表下生成局部唯一齐次原作用解；
该结论来自源解析系数、真实分支和ODE存在唯一性论证，Lean时间路径安装另行保留。
一般空间PDE与完整量子谱按active route接续。

`source_scalar_gauss_reduction.py`以同一原Gauss生成标量法向动量，
`φ=v+R x`、`Π_φ=R(RᵀR)⁻¹π+O_b ζ`，其中
`ζ=−D9(φ)⁻ᵀ selectᵀ(G_gauge+G_matter+G_scalar(Rdual π))`。
完整独立canonical物质流为`Re(i p ρ_a ψ)`；规范动量散度及三条稳定子Gauss保留。
由于`O_bᵀR=0`，真实联合正则一形式的标量拉回严格为`πᵀdx`，
即使ζ依赖其余场及空间jet，也不产生附加交叉二形式；原61维CCR的基和对偶基得到精确回读。
共同Hamiltonian先保留原`div(Π_Ai A0)`边界，再拉回该动量图。
源生A0使法向动量链的系数`O_bᵀ dot(φ)=0`，broken A0系数为已消去的九条Gauss；
剩余三条Gauss及coframe约束继续保留，法向动量能量没有被丢弃或另加作第二份Contact。

`source_gauss_quantum_current.py`将原`Re(i p ρ_a ψ)`生成真实504维两支CAR电流，
`Q_a=i realify(ρ_a)`在复分支上为`diag(iρ_a,i conjugate(ρ_a))`，
仍使用`a=(ψ,conjugate ψ)/√2`、`b=(p,−conjugate p)/√2`，独立p不改作伴随。
全部native12 Lie身份、原full70 scalar和36 gauge CCR moment map独签；
61切片独立压缩不构成完整12维Lie表示，原稳定子三方向保持该切片。
源系数`K0=−N Gram9⁻¹/2`的法向能量`Σ K0_ab(B_a+dΓQ_a)(B_b+dΓQ_b)`
保留不对易玻色次序，由原CAR正规序定理生成四次项及480个非零一体矩阵元。
单粒子消费者给`−9√30/200`且四次项为零；真实不对易CCR⊗CAR混合项为`−3√30 i/100`。
它是同一约束动量平方的源系数算符消费者，变系数及连续场乘积继续消费各自原口。

`source_gauss_live_ordering.py`继续由原算符方程`D(φ)ᵀζ=−G`生成`ζ=−F(x)G`，
其中`F=D⁻ᵀ`、`b_a=Rdualᵀρ_a(v+Rx)`。
原法向动量平方精确成为`Σ K_cd G_cG_d+Σ L_dG_d`，
`K=FᵀGram F/(2h00)`，`L=−i Σ_c F[:,c]ᵀGram(b_c·∂F)/(2h00)`。
源点L为零，实际偏离源点的九个分量均非零；原切向／法向divergence trace常数都为零。
独审以61变量光滑紧支持波包张量双支CAR态，先解真实内层动量、再求导作用外层，
嵌套平方与`KGG+LG`精确相等，遗漏L产生非零残差。
该法向能量组件保留局部光滑系数算符域，完整共同Hamiltonian和时间谱按active route接续。

`source_scalar_shift_quantum.py`将原完整标量动量写为`Π=Rdual π+O ζ`，
直接平方`Π−b`，其中`b=Σ_i h0i ρ(A_i)φ`是实际齐次coframe shift。
它包含外围动能、live法向平方、两类shift交叉项及原空间／势能。
`w=FᵀOᵀb`精确消去标量依赖，仍保留与原规范／标量电流的不对易性；
97变量实际波包消费全部70个动量平方，非零`h01=1/5`及broken规范扰动给`w0=1/85`，
法向shift交换子和遗漏项反控均非零。原非零A0标量项只在完整共同Gauss中消去。

`source_coframe_quantum_kinetic.py`由六个原Spin主约束求解dependent coframe动量，
并在原minor对应的配置横截面拉回一形式，生成六对真实CCR及独立real504 CAR。
原source系数下，完整coframe能量包含纯动能、动量—物质交叉、四次与一体项；
一体收缩为`−9N/8 I504`。实际多项式⊗CAR作用和六个Heisenberg坐标速度独签，
速度读取包含保持横截面的Lorentz补偿。完整Lorentz消元只消费一次。

`source_coframe_live_ordering.py`保持原来明确的系数在左次序，将六个coframe坐标全部变为
真实变量。原动量平方生成一阶drift与额外current修正
`−9N/(8q0 q2 q5) I504`；在source点取值仍非零，冻结系数会删掉它们。
原ε-Hessian、primary线性解、六向系数导数与完整exterior-CAR实际作用已独签。
这是所显示排序的确定算符，不主张不同量子排序等价。

`source_joint_local_quantum.py`将这个live coframe项、完整scalar Gauss动量平方、原native
规范能量及`dΓ(diag(Hm,−conjugate(Hm)))`放在同一103配置变量域：6个coframe、61个scalar、
36个空间规范坐标，张量原real504 CAR。原四项密度、10条primary、9条broken Gauss和原独立
双支归一逐项回读；真实非分离波包的共同作用、944个scalar／gauge交叉主部条目及原61个
Yukawa力由另一算法独签。共同`Cc∞(Uq×Ux×R36)⊗CAR504`域由原光滑系数和有限阶作用保持。
该对象是固定原time-coframe参数下的齐次局部Hamiltonian；四个时间约束、三个稳定子量子
约束及其物理态演化保持实际待消费身份。独签入口分别为同名`independent_*.py`。

`source_quantum_lapse_constraint.py`让同一time-coframe成为正实参数`eTime=(Nν,0,0,0)`。
原BF／metric／native Hodge和全部物质系数直接生成
`H(ν)=ν H_A+ν⁻¹ H_B`，HA含coframe／scalar／matter，HB为原native gauge；
六个live q、真实系数导数和两槽CAR正规乘积分别保留。
原主约束读者给`C(ν)=H_A−ν⁻² H_B`及pencil`ν² H_A−H_B`；
真实紧支持三阶germ上的完整交换子为`[H_A,H_B]f=5/16−1/8=3/16`。
这份参数族不能直接用可交换能量比代替。

`source_temporal_dirac_reduction.py`从原四时间方程生成其实际消元：
`J=∂y F`的source行列式为800/3，四主／四次约束的Poisson矩阵
`Δ=[[0,−Jᵀ],[J,K]]`可逆，K保留真实`{F,F}`；源八阶行列式为640000/9。
其逆的右下块严格零，故保留变量的Dirac括号等于原canonical括号。
同源解析分支`y=Y(z)`、`Pi_y=0`使原一形式直接回读，
`H_red(z)=H(Y(z),z)`生成原受约束发展，真实非平凡时间更新已独立重建。
源非线性初值族直接读出`H_red=2√(3ca)`，`c=162/625`，a来自原物质／标量／动量。
这里的时间约束是第二类，不能把formal pν／C同时作为第一类量子态核安装；
约化能量的量子排序需消费其实际源分支。两份producer及同名独审分别保存精确矩阵和消费者。

`source_quantum_temporal_symbol.py`保留原全部字段，直接生成完整齐次约化符号。
原primary／broken Gauss拉回后，全部非规范能量系数对四时间coframe线性；
四个系数、六空间coframe及21个完整native电／磁／交叉Gram生成原Hamiltonian。
原四方程的Jacobian为`diag(−√30,−2√30/3,−2√30/3,−2√30/3)`；
任意阶系数由低阶残差和其实际逆生成，既有解析隐函数分支消费这些系数。
原完整系数恒等、实际31参数来源和另一多项式算法的七阶回写独签。
该实际数据仍保留三条残余稳定子Gauss值，不能把它直接命名为已约化量子态。

`source_temporal_algebraic_elimination.py`进一步把空间coframe吸入原Gram，
得到四个非规范系数`a0,a`、对称矩阵`S`及向量`d`共13个同源不变量：
`Hg=(n² trS−bᵀSb−2n bᵀd)/(2n(n²−bᵀb))`。
令`v=b/n`、`h=n²(1−vᵀv)`、`λ=2nHg`，三shift由
`v=(S−λI)⁻¹(ha−d)`生成，原四驻点方程等价于两条标量方程。
其中一条为`B h²+2C h−D=0`，源分支用
`h=D/(C+√(C²+BD))`生成，再代入另一条得到一个正则标量代数根。
源上`S−λI=−648/625 I`、根式分母`18/5`，最后标量导数为1；
不除源点消失的`a`或`aᵀ(S−λI)⁻¹a`。回写给`Hred=λ/n=2n(a0+aᵀv)`。
这13量是原全场的readout，未以13维carrier替换原变量。

`ImplicitSourceCoefficients.lean`生成并证明通用系数递归、唯一性和逐阶消去；
实际原有理表达式的最高系数律由源重建及独立有理代数论证支付。
`TemporalStationarityReduction.lean`核验正则根式、两标量消元与能量恒等。
这是完整时间约化的经典解析符号；非对易量子化保留原排序，
不直接把算子塞进可交换根式。两份同名`independent_*.py`保存独立原作用回写。

`source_quantum_stabilizer.py`从原native括号生成稳定子`su(2)`，并用原Gram选择其不变的
broken9正交补。该补空间仍生成原O、D9及scalar61；先拉回动量再排序，完整Hamiltonian与
三条残余Gauss算子精确对易。全部61个D系数、70动量协变、210个原Yukawa和432个规范
bracket导数独签；原native范数紧支持波包张量CAR `(7,259)`真实位于三Gauss共同核，
四项能量作用均非零。共同核由所有有限Hamiltonian幂保持，未代填时间演化。
旧rref补空间不被稳定子保持，其平方有真实排序余项；新旧图在完整经典Gauss面同值，
不宣称旧新量子平方在共同核上自动相等。原rref算子保持先前明确排序范围，后续约束消费者
使用新native正交补算子。

`source_stabilizer_phase_reduction.py`给出同一原三Gauss的真实局部辛约化。
原607对配置／动量包括103个玻色配置及504个实物质配置；原独立物质动量为
`(-Im p,-Re p)`。源轨道在三个空间规范坐标`[0,6,18]`上的minor行列式为`−54√2/125`。
固定这三个坐标为原source值，完整moment map精确生成对应三个ΠA；其余604对保留原
canonical一形式和Dirac括号，从而得到实际1208维chart。
非平凡全场数据回写原12Gauss与10coframe primary；离约束面的完整Poisson逆也已独签。
这份非线性局部chart与旧active126＋tail1082的生成器识别需要实际切向接线，不能由维数相等代填。
两份独签见同名`independent_*.py`。

`source_physical_phase_splice.py`已把整个1082尾部接入这份实际1208维切空间。
原`δp=−i δχ E`经`(-Im p,-Re p)`给独立dual的真实canonical映射；一形式、辛嵌入及
双侧reader独签。完整原密度重新生成尾部能量，保留非零scalar–dual交叉并满足
`Ω_tail A_tail(k)=H_tail(k)`及`H_tail(-k)ᵀ=H_tail(k)`；所有三动量、原约束切向和
共旋Noether shift均保留，实际三阶retarded传播在约化坐标中直接回读。
`source_active_phase_splice.py`继续在零动量接通完整active126。
原138一致载体先回写289辅助与9条Ward时导，再进入同一源切片；canonical读者湮灭
原12维radical后才降至126。原`δPi_e=GtᵀδΩ+(δGt)ᵀΩ_source`、原B磁分量给ΠA、
`δp=−iδχE−iχ_sourceδE`全部独立重建，非零附加项保留。
完整`126+1082↔1208`双向映射、辛正交、原能量同余与时间发生器交织独签。
非零空间动量的active接线仍需原Gauss散度与动量依赖Ward切片。

`source_quantum_gauss_section.py`从同一原群和真实gauge切片生成局部量子Gauss解。
对任意100变量切片上的有限CAR光滑germ，原局部orbit逆生成
`E(f)(g·z)=Γ(g)f(z)`，三条Gauss零式是输出；restriction直接回读输入。
原quaternion／exterior群作用、完整103变量二jet、实际带荷`(5,258)`的三零式及309条
一阶导数均独签。`H_red=R H_native E`逐原四项作用，常切片截面的连接纠正为
`875√30/1944`，零值但非零导数的CAR词完整参与。
该口签收局部germs；原中心固定source玻色点却使奇CAR词反号，全群atlas与各稳定子的
相容下降分别保留。独签入口分别为同名`independent_*.py`。

`source_gauss_section_measure.py`从同一原103坐标Lebesgue实现的局部orbit Jacobian生成
量子切片配对。coordinate-Haar的identity密度为1，切片权重为`ρ=8a₁²a₁₂`，
源值`54√2/125`；原native Gram为`2I₃`，故metric-Haar相差`2√2`，
相应源切片权重为`27/125`。两种读法给同一Jacobian和局部范数，全部群体积因子保留。
原有限CAR群作用酉，因而该配对对任意局部截面直接下降。

实际紧支持100变量波包由原D9系数的支撑界生成，精确分部积分给
`p†=p−i∂logρ`，`U f=√ρ f`给半密度表示。原四项Hamiltonian在两个完整Gauss二jet上
独立读回，非零相似变换纠正为`−3961√30/64800+575√15 i/16632`；原排序未改。
这是局部配置配对及原算符的坐标表示，不代填衰变相空间、全群商、Hamiltonian自伴性或
完整时间演化。独签入口为`independent_source_gauss_section_measure.py`。

`source_spatial_stabilizer_orbit.py`由原Gauss散度生成全部实三动量规范轨道
`V_i(k)=−ad(A_i)S−ik_i S`。原native Gram给
`N(k)=V(k)† G36 V(k)=2[(|k|²+2a²)I+2ia cross(q)]`，
`a=3√2/5`、`q=(k₂,k₁,−k₃)`均从原源实算。
多项式平方和直接证明锐下界`N(k)≥36/25 I`；相对原稳定子Lie度量的界为18/25。
双侧逆没有实动量排除点，`P=I−VN⁻¹V†G36`生成rank33的native正交横向投影，
原rank3纵向参数、±k现实性及非轴实际场分解独签。
旧三坐标minor在`k₁=±a`为零时，完整轨道仍rank3；此处需要换读法而非删除外态。
该Gram支付规范轨道逆，不替换Hamiltonian动能，也不作为粒子质量或衰变谱值。
独签入口为`independent_source_spatial_stabilizer_orbit.py`。

`source_spatial_phase_tangent.py`将该全k规范读法接到全部原607个canonical坐标／协向量对。
令`E(k)`为完整源轨道，原Gauss为`C(k)=E(−k)ᵀJ`，native切片为`F(k)u=R(k)δA`，
并令`B=JF(−k)ᵀ`。精确六约束矩阵给
`T=I−EF+BC`、`T²=T`、`rank T=1208`及`T(−k)ᵀΩ=ΩT(k)`。
这给全部实三动量的非退化配对载体，无需选择新的全局33坐标frame。

同一`F(k)u`作用于原ψ与独立dual动量；canonical Gauss的协向量项不额外乘native Gram。
原9条broken方程直接解出完整Πφ法向分量，保留`ik_i δΠ_Ai`。
剩余571个canonical对与native横向33对的原配对相同，已解出的规范法向动量与整个
横向平面的配对为零。零动量及非轴±k完整复切向量回写全部12Gauss，漏掉散度的
scalar动量差严格非零。该通用Gauss切向口与active动力学交织分别验收。
独签入口为`independent_source_spatial_phase_tangent.py`。

`source_spatial_active_phase_splice.py`在实际非轴
`k=(−3√2/8,0,3√2/4)`及`−k`上消费原138一致jet，然后才降至126物理商。
全部289方程、原Ward jets、含`−ik A0`的BF动量、完整`χ_source δE`及法向Πφ均回写。
内部复矩阵先实化再Fourier，禁止对整个Fourier振幅重新取Re／Im。
同一native参数作用于原全部场，actual126与tail1082有原辛正交配对，
`R X=I1208`、`X R=T(k)`及`H=R(−k)ᵀ H_split R`全列因子独签。
原canonical Hamiltonian与split发生器在整个载体交织，真实datum沿两条作用路径相等；
两侧完整映射满足±k共轭。独签入口为`independent_source_spatial_active_phase_splice.py`。
这对实际非零纤维的验收不代填其他动量的active商秩。

`source_active_retarded_inverse.py`直接生成零动量及上述非轴动量的完整active126逆。
原SCC特征多项式和实际有向块结构给有限Horner响应；最大74阶块保持全部原耦合。
`CayleyHamiltonRetarded.lean`直接消费`Matrix.aeval_self_charpoly`，由
`Q=aeval A (charpoly(A) /ₘ (X−C z))`证明两侧分子为`charpoly(A)(z) I`，
在该实际分母非零时生成双侧逆，不需要调用方给逆或Cayley–Hamilton零式。

完整126维的一般z多项式残差、数域双侧作用与原时间递推分别验证。
原矩阵行／列界给`β_active`，零动量与非轴的保守整数上界分别为20、260；
`Re(z)>β_active`时，零过去`Θ(t)exp(tA)`的Laplace积分等于同一有理逆，初始跳为I126。
实际`t=1/40`、`1/520`的20阶作用有共同严格余项界
`38197/61447927938102830227783680000`。全部向量参与验证，回执只压缩展示行。
增长极点及非半单部分完整保留；该线性响应与相互作用复合谱分别消费。
独签入口为`independent_source_active_retarded_inverse.py`：独立完整126系统求解与时间幂
重算消费全部原分量，Lean通用分子口独立核验。

`source_common_retarded_phase.py`在同一已签非零±k物理载体上组合完整响应
`G=X diag(G_active,G_tail) R`。原双侧恒等式为
`(zI1214−A)G=G(zI1214−A)=T`，且`TG=GT=G`；零过去解的初始分布是`δT`。
严格API只接受`Tf=f`，显式projection API同时返回`Tf`及被改变的源。
独立全1208系统求解回写全部1214分量、原Gauss／切片和真实dual→scalar→primal响应；
两种边界测试与±k共轭通过。共同Laplace半平面为
`Re(z)>max(β_active,153√30/625)`。真实外腿j到仿射约束／物理forcing的映射独立承担，
不以把任意电流投T代填原强迫方程。

`source_common_phase_time.py`由同一完整1208发生器生成收敛的全时间级数；
原1214 Hamilton方程、全部空间约束和±k现实性直接消费该级数。
实际`Δt=1/520`的20阶值有严格余项，原发生器／embedding范数上界为260／49。
完整尾级联的前三阶primal响应为0、0、`162√30/3125`。

原两支Dirac相位先通过`p=−iχE`与全部16 coframe的`χ_source δE`生成canonical旋转S。
全体Clifford、incoming coframe和Lorentz-current系数支付任意时间协变；
实际场从原289 map读回，四个time-coframe分量非零。
原轨道响应为`S(t) X exp((t−s) A_split) R S(s)⁻¹`，初始跳为`T(s)`；
非零起点上`T(s)≠T(0)`的真实反控与完整原一、二阶时间导数已独签。
这里闭合指定±k的完整经典线性发展；相互作用量子谱保持独立责任。
独签入口为同名`independent_source_common_retarded_phase.py`及
`independent_source_common_phase_time.py`。

`source_forced_hamiltonian_reduction.py`从原172维descriptor的
`172→156→147→138`一致性链生成带源仿射图，再降至126物理forcing。
每一步未解障碍都精确因子化为原九条Ward源条件，电流本身不被投影修改。
原自由导数修复动态截面，给出
`(∂t−A)ξ=F(∂t)j`、`field=Xξ+Pfull(∂t)j`；
F为三次、仿射项为二次，全部289行是全列多项式恒等式。
分布源保留相应导数与初始δ，原辅助Contact只加入一次。
漏导数、漏仿射项和重复Contact在真实相容源上均有非零反控。

`source_onshell_phase_forcing.py`实际生成与该±k一致的四条252模外腿：
原双侧Dirac及完整Hamiltonian在壳，四条能量均为`189√15/400`，
外腿作用因子为`2^(−1/4)`。实际97电流支持30／34项，九Ward逐项为零；
dual24和原70标量源在这四条外腿上为零。
电流经原仿射图进入共同响应，完整12Gauss精确等于实际`j_A0`，
稳定子三Gauss为零，法向scalar动量的非零源偏移完整保留。
同一Ward代表下与独立canonical79加Contact逐项相同；Contact为`−9√30/100`。
该弹性读数是共同有理核在零能量转移的meromorphic/tree值，
不把有增长模时的零频读数写成收敛的无限时间Laplace积分。
两份同名`independent_*.py`分别独立重建原descriptor、外腿与原79系统。

`source_onshell_cauchy_response.py`直接消费这组电流的时间forcing：
`ξ(0)=0`、`ξ(t)=Σ_{n≥1}A^(n−1)f t^n/n!`，完整原场为
`Bξ+affine_field`，其初值由源约束生成且非零。
原289算子恒等式支付所有时间阶，完整12Gauss及法向scalar动量图同时回写；
21个全向量系数、`Δt=1/520`的20阶读数和严格余项独立核验。
非零源时刻的原两支相位、`χ_source δE`及原289场导数完整保留。

`source_nonzero_frequency_onshell_response.py`进一步生成同一±k上的真实能量转移。
原252在壳能量为`51√15/100 ↔ 21√15/50`，
实际频率为`ζ=∓9i√15/100`；另一species反向交换，完整2→2能动量守恒。
四外腿保留原作用因子，几何current因子`1/√10`由实际spinor生成。
`F(ζ)`、`P(ζ)`的全部源导数项进入共同响应，原289及独立四块逆在同一Ward代表一致；
错用ζ=0会同时破坏Ward与forcing。Contact为`−81√30/1000`，只消费一次。
真实`j(t)=exp(ζt)j0`给`ξ⁽ⁿ⁺¹⁾(0)=Aξ⁽ⁿ⁾(0)+ζⁿf`，
原场包含`affine_field exp(ζt)`；全部时间阶Euler／Gauss与21个全向量核验，
`Δt=1/522`的20阶读数有严格余项，proper clock仍为`τ=N t`。
当前电流没有被Θ截断，源要求的总场初值也没有被置零。
共同独签入口为`independent_source_onshell_time_response.py`；该守恒交换不命名为衰变。

`source_quantum_grade_structure.py`在同一完整局部量子算子上生成占据分级：
原`Λ⁶⊕Λ²⊕Λ⁴`的两支CAR504中，Λ⁶占据数给56秩单粒子投影。
完整`H_native=H0+Y`保持总粒子数；所有非Yukawa项保持该grade，原70个Yukawa系数
使grade提高1。live coframe导数、原scalar Gauss平方和所有native规范电流均保留。
原群作用、Gauss延拓／限制及源半密度变换与grade对易，故分级下降到实际局部100变量截面。

`FockFilteredWords.weighted_tensor_word_vanishes`以严格Lean核验支付任意交错词：
在粒子数N扇区，超过N个提升因子的有序词精确为零，grade-zero因子可任意穿插，
非对易玻色微分因子保持原次序。真实四能量作用、局部Gauss截面及非零`Y M0 Y`
同时消费原源；这不以单粒子`Y²=0`代填多粒子结论。
该代数分级控制完整相互作用展开的层数；H0的时间发展、时间第二类分支的量子实现和
动态谱仍由各自消费者生成。
独签入口为`independent_source_quantum_grade_structure.py`；原504系数的独立计算与
Lean通用词定理分别按其实际范围签收。

`source_quantum_ordered_temporal.py`把原四时间参数的完整量子Hamiltonian
写成14个固定微分／CAR算子的线性组合，保留全部live导数、scalar／gauge交叉项
及原103变量作用；源时间限制逐组件等于已签`H_native`。
这些算子及任意有限有序复合都作用于同一紧支撑Gauss截面。

该family另生成一个指定的形式延拓：以原source标量族为展开中心，
原算子系数放左，四个时间增量按既定次序排列，再用实际J0递归消去。
各阶能量是原算子的有限有序词，前四阶词数为`1,5,37,341`；
三阶非交换词已逐项独审。形式ε记录该展开，未作为新物理耦合。
原Yukawa字母升grade一阶，其余13字母保grade；已有Lean加权词定理
直接控制每个N粒子扇区超过N次提升的词。
在真实两粒子输入`(144,396)`上，源点`Yf`完整四分量的范数平方为`216/125`，
二阶升两级系数给四个输出，每项为`√30/30`；这保持量子系数身份。

原正配对下取真实紧支撑Gauss截面`f`及`g=Yf`，
`⟨g,H_native f⟩=∫ρ‖Yf‖²>0`，反向配对严格为零。
实际变化的ρ、全部61个Y导数及两包Gauss jets均被消费。
这精确确定固定time算子与首个形式约化系数的非对称性；
指定有序延拓与先经典消元再量子化的等价、ε=1求和及完整谱各自另需构造。
独签入口为`independent_source_quantum_ordered_temporal.py`。

`source_yukawa_reducing_carrier.py`从全部70个实际Y与Y†生成正Gram。
其谱为`0,10N²,30N²`，重数为`196,42,14`；零空间已经约化全部
canonical顶点及其伴随，给出该条件下最大的196复模／392独立实CAR载体。
同一原动能E生成`Pdual=E Pprimal E⁻¹`，全部158个原顶点的182个动量系数
及原Dirac满足`V Pprimal=Pdual V`。独立χ由原`p=−iχE`限制到同一双侧载体，
不额外要求两种表示使用相同投影。

全部144个泛型spin矩阵、native current、群与中心均保持该载体。
outside(P)的二值占据荷由既有`Fermion/Charge.lean`三口提升到完整Fock空间；
coframe、scalar61与gauge36及其交叉相互作用完整保留，真实两粒子上四能量均非零。
含Y的有序词在此子理论上消失，零至三阶保留词数为`1,4,28,244`。
两组已签散射中的四条Λ⁴外腿在此块，四条Λ²外腿在补空间，
原外腿库存与作用归一全部保留。该子理论没有被等同于完整模型、Ward兼容核或质子识别。
独签入口为`independent_source_yukawa_reducing_carrier.py`；形式对称性另由原配对核验。

`source_reducing_quantum_adjoint.py`从原全部live系数计算完整真空coframe伴随：
在原ρ下，`L†−L=(N/v)(q·∂+3/2)`，`v=q0 q2 q5`。
真实同grade紧支撑Gauss包`g=(q0−1)f`给完整Hamiltonian配对差
`(N/2)∫ρ|f|²/(q2 q5)>0`；其余能量保留q依赖，但在这个实例中逐点相消。

`source_reducing_coframe_metric.py`由原K与完整混合current生成正向配对：
`M_r†−M_r=2i t_r I`、`t=K∇log v`，故m粒子层的权重为`w_m=v^(m+2)`。
全Fock写成`W=v^(2+Number)`，源点W=1；coframe-only且源归一的权重由可逆K唯一生成。
完整Hermitian mixed部分的普通／加权散度为零，全部正规current二槽张量、
onebody、live correction与原势均通过伴随恒等式。
固定`y_source`、整个六q正chart上的完整coframe算子因此对`ρW`形式对称。

半密度`U=v^(1+Number/2)`把这个正配对读回原ρ，实际算子变为散度形式，
并生成实势`ΔV=3N(Number+2)(Number+4)/(16v)`。
真实两粒子全CAR作用沿两条路径逐项相等；U保持Gauss截面、392投影与紧支持。
权重改变时原CAR的伴随也被消费：`a†_W=v⁻¹a†`，
`√v a`与`v^(-1/2) a†`是源归一的互为伴随CAR，U把它们送回原正交表示。

该配对没有替换旧ρ的权威范围；scalar／gauge不求q导数且守Number，
其原伴随条件被原样运输。coframe-only权重允许乘x/A函数，完整measure的唯一性
还受这些因子影响。
两份同名`independent_*.py`分别支付原缺陷与新的完整coframe正配对。

`source_full_gauss_section.py`由原native12群作用生成完整112配置变量的局部100维截面，
保留scalar70、三组规范连接36、六coframe及原CAR504群延拓。
原约束的隐式逆给全部一、二jet；源点和变化场上的12条几何Gauss及1344条导数均独签。
完整配置Jacobian给`ρ12=|det D9(φ)|ρ3/256`，源点为`54√2/125`；
非正交scalar frame与native metric Haar因子`16√6`保留。

物理消元直接使用原broken9与scalar-normal9的第二类矩阵
`Δ=[[0,D9],[-D9ᵀ,K]]`，其中K保留残余Gauss值。
同一D9逆生成完整Δ双逆、`det Δ=(det D9)²`和右下零块；
原scalar正则frame的phase Jacobian为1，三个约束测度因子为
`(1/256)(256/|det D9|)|det D9|=1`。
因此原canonical103相测度消元后不带额外D9因子，实际群下降仍消费residual3的
`ρ3=8a₁²a₁₂`。完整12群图是原动能的几何接口；固定源势的broken torque保留，
没有把broken9改成第一类规范方向。
`SecondClassReduction.lean`直接证明通用双逆、剩余正则括号与测度相消，
原D9、frame及真实局部变化由Python实例与`independent_source_full_gauss_section.py`支付。

`source_scalar_form_hamiltonian.py`在这个真实测度上保留原动量图
`Π_j=−i a_j·∂+c_j−b_j`，生成`Π_j†=Π_j−i div(a_j)`，
由指定动能sesquilinear form得到`H_scalar,form=Σ_j Π_j†Π_j/(2h00)+V_original`。
全部97坐标导数、Hermitian原current与scalar／gauge交叉主部被消费；
它与旧系数在左平方的差为`−iΣ_j div(a_j)Π_j/(2h00)`。
该差在源点为零，变化场上16条散度非零，真实两粒子residual3截面的完整作用差独签，
包括值为零但导数非零的CAR分量。
原h00符号和势保持；这里唯一的是指定form与配对的微分代表，旧量子排序不与它混同。
实际action取源时间列，通用伴随公式保留实shift；同名独审支付独立散度形式及Gauss二jet。

`source_scalar_temporal_form.py`将这个动能form接回原四时间列`(n,b₁,b₂,b₃)`。
原动量图a、c及`r=div(a)`与时间列无关，原metric给
`(1,h01,h02,h03)/(2h00)=W(q)(n,b₁,b₂,b₃)`，因此
`−iΣr_jΠ_b,j/(2h00)`直接生成四个固定差算子。
实际三个非零shift、全部shift导数及scalar／gauge交叉项由70动量嵌套与独立97坐标散度形式回写。
原14算子族只更新nongauge0..3，原Yukawa、其余10项和源seed保持，完整Gauss二jet有实际消费者。

`source_temporal_coframe_pairing.py`由原全六q／四时间系数证明同一
`ρ3 v^(2+Number)`配对与半密度仍成立，实势为`3n(Number+2)(Number+4)/(16v)`。
完整系数同时给`Hcoframe(n,b)=n/N_source Hcoframe(N_source,0)`；
三shift在该组件中精确消去，scalar的真实shift作用继续保留。

`source_temporal_gauss_relations.py`再由原12个生成元、完整97微分与504 CAR电流生成
`a−G(q)d=R(q,A)Gs`，`G=(L Lᵀ)⁻¹`，L为同一空间coframe。
scalar的`Π†U+UΠ`接触完整包含`∂U`与`div(a)U`，两者之和按原散度式消去；
broken current与matter的相应项消去，留下原residual3电流。
实际Gauss截面因此给`a=G(q)d`；源q上为`a=d`，变化q上G仍是系数算子。
两个带荷Gauss二jet和完整shift补项独签，真空紧支撑截面的实际见证给
`[Hcoframe,G₂₂]f=N_source`，不能把G移过coframe导数。
旧三阶自由词反转差168项是自由表达式读数；实际算子还必须消费上述依赖关系及导数。
这三份producer各有同名独审，时间约化方程与有序级数求和由其下游消费者生成。

`source_joint_form_hamiltonian.py`把指定scalar form与原coframe、native-gauge和matter
放在同一`Cc∞(Ω100)⊗Fock(K392)`上；正配对为`ρ3 v^(2+Number)`。
原gauge电逆实对称且只依q，完整matter的spin／internal反Hermitian因子彼此交换，
Y及Y†在392上为零，四组件因此共同形式对称。
实际变化q／scalar／gauge上的四能量均非零，完整混合Hessian与零值非零导数项保持。
同一半密度`U_m=√ρ3 v^(1+m/2)`给完整100坐标读回，与独立散度表示逐项一致；
`independent_source_joint_form_hamiltonian.py`从原密度和隐式群图重建全部作用。
这里固定源时间列，392补空间与全部外腿库存保持；原标量排序差没有被抹去。

`source_full_quantum_adjoint.py`保留完整504模，给同一配对上的
`H=H0+Y`与`Hsharp=H0+Y†`。H0的全部系数伴随恒等式不需要392投影；
原Y是保持粒子数的乘法算子，数目层上的权重为标量，故其加权伴随正好是Y†。
全部70项与420条residual3协变身份保留，两种作用保持同一紧支撑测试域。
Hsharp是独立的伴随测试口，没有加入原H。
真实补空间两粒子Gauss包给完整四组件、H／H0／Hsharp以及非零Y²、Y M0 Y，
第三次提升与交错第三次提升为零；同名独审从原密度重建全部输出。
原H的异grade正反配对不相等，Hsharp则给准确伴随读回，392对称限制继续保持。

`SymmetricGraphClosure.lean`给共同作用的通用最小闭扩张机制。
两个部分线性作用T、S只需在稠密的S定义域满足`⟨Tx,y⟩=⟨x,Sy⟩`，
原T图的拓扑闭包就生成单值线性闭作用，延伸T且包含于任何闭扩张；
`x_n→0`与`Tx_n→y`必给`y=0`。S只作为形式伴随测试口，对称作用取S=T。
原full504分析链消费这一机制得到其唯一最小图闭包。
`OpenChartTestDomain.lean`还从正则测度生成有限维开chart上`1≤p<∞`的Lp稠密光滑测试域，
测试函数的闭支撑严格位于chart内部。
具体源 product chart 上的完整 Fock 加权L²、稠密测试子模与半密度等距已由
[共同量子域接口](source-quantum-domain-and-cone.md)安装；商后的原算子图仍按实际域连接。
图闭包不选择自伴扩张，也不提供时间约化求和或谱测度。

`SourceQuantumScalarChart.lean`直接固定原`positiveSmoothUnifiedSource`的标量真空与
`scalarP286ActionBilinear`，以原native配对生成orbit、稳定子及其正交broken空间。
`D(phi)=O†rho(phi)`在源点是单射O的Gram，双逆与非零行列式由源生成；连续性给包含源点的
实际开scalarChart及每点双逆。该口是native Riesz代表，非正交B坐标下为`Gram_B⁻¹ D9`。
`SourceQuantumScalarHilbert.lean`用原scalarSlice内积的规范体积及open-comap安装实际复L²，
严格chart内部的紧支撑光滑函数构成稠密复子模。这里没有外供矩阵、measure、normalizer或稠密性前提；
数值9／61维与完整100坐标量子商仍按各自原坐标接线。

`source_common_temporal_form.py`将四类能量接成同一全504模四时间族：
`H(n,b)=H0(n,b)+Y(n)`与独立测试伴随`Hsharp(n,b)=H0(n,b)+Y(n)†`。
原实gauge电逆与势、全部Dirac spin因子及scalar shift图给同一`ρ3 v^(2+Number)`配对，
实际Gauss二jet的完整作用等于原14项重构；参数导数直接产生四个时间约束的伴随口。
反酉消费为`C H0(n,b)=H0(n,−b) C`：真实非零shift必须反射，原Y继续保留其非零差。
同名独审由原BF／Hodge、97维散度形式和隐式群截面重算全部四组件。

`source_temporal_energy_adjoint.py`进一步消费原指定coefficient-left形式递推及真实`a=G(q)d`。
十三实时间权重的多项式rank13使真空atoms逐个形式对称，故有限词伴随反转合法。
三阶K3在同一真空Gauss紧支撑三次germ上的伴随差精确为
`6623√30/145673515584`，完整30个含coframe的词独立重算；其余138词无q导数，
最高四阶、drift与低阶jet项的消去均被消费。错误冻结G的q依赖会给零。
这确定了该指定第三阶排序的实际性质；原四时间作用、其他源生约化与ε=1求和分别保持其责任，
没有用能量平均或附加Y†替换原作用。

`source_coframe_weyl_symbol.py`、`source_scalar_weyl_symbol.py`与
`source_common_weyl_symbol.py`把同一四时间form完整写到原100坐标的canonical Weyl表示。
这些坐标是`(q6,x61,Afree33)`及其共轭动量，原13个时间压缩量保持读数身份。
coframe的精确转换保留`divdiv(K)/4=−n/(4v)`，与原半密度势相加为
`n(3Number²+18Number+20)/(16v)`；全部原mixed current、正规四费米和onebody项保持。
Weyl乘积还精确读回原`G₂₂(q)`交换子，包括源真空germ的非零值。

scalar／gauge先通过原residual3群图生成真正的94坐标动量，再消费原`ρ3`半密度。
原D9与三维轨道逆的全部一、二导数生成`div(P)`、`divdiv(P)/4`及密度势，
broken9和residual3的12类CAR电流及其正规平方完整保留。
三个独审分别用原BF的Weyl对称乘积、另一隐式逆微分及原97场／完整Gauss二jet回写。
完整504模四块满足`OpW(σ0+Y)=U H(n,b) U⁻¹`，`U=√ρ3 v^(1+Number/2)`；
σ0为Hermitian符号，原Y乘法项保持。实际补空间两粒子的H／Hsharp与全部四组件逐项一致，
漏掉scalar或gauge的二导修正均产生非零差。这个表示保留四个原时间参数；
时间消元、相空间量子合成与最终谱继续消费它，不把符号在零动量的值代填经典源seed。

`source_canonical_temporal_hessian.py`从原121场的172维速度商生成
`(canonical132,time4,A0_native12)`的真实148维双逆；全三动量依赖是平方为零的坐标剪切。
原BF边界项与`δp=−iδχE−iχ_sourceδE`完整保留，辛形式精确为`diag(−J66,0)`。
先消broken A0九维，再由实际`Hyy=−J0`生成
`y_z=−Hyy⁻¹Hyz`与`Hred_zz=Hzz−Hzy Hyy⁻¹Hyz`。
127个时间交叉条目及4280个Schur条目在全三动量上生成，原20个顶点系数直接支付尾部零交叉。
完整1214 canonical载体由实际双向映射接回1208物理相空间。

两个已签非轴动量上的完整126+1082能量和发生器逐项匹配；零／非零频率的四条真实
在壳电流先生成原source covector，再穿过broken与time两次Schur。
完整132动态、四时间约束及原126 forcing回写同一响应；12条Gauss等于实际A0电流，
保留诱导scalar法向动量。唯一Contact与原仿射偏移均在原处消费。
同名独审直接解原172方程，独立重建全动量双逆和上述实际消费者；
这是源点处的完整canonical线性化，量子时间消元继续使用原共同Weyl表示。

`source_canonical_star_temporal_reduction.py`在同一原作用上生成指定的canonical量子时间图。
取原四对`η=y−y_source, π_y`，使用线性图生成元`G_D=−Σπ_y,a D_a`，
`U_D=exp(ad⋆G_D/i)`、`R_D=ev_(η,π)=0 U_D`与`L_D=U_D⁻¹ incl`。
原`R_D(−∂y H_ε)=0`逐阶生成D，每阶只解已生成的源Jacobian J0。
原η／π的显式Weyl乘法强制产生Jordan迭代；没有把13个读数当canonical坐标。

形式三阶上，四条原时间方程、`R L=id`、L的乘法及原lifted Heisenberg动力学均逐词成立。
R本身不是乘法同态：`R(η⋆π)=i/2`，而`Rη⋆Rπ=0`。
同一源再生成`H_T=H+ΣπΛ`的时间乘子，全部primary／secondary演化归零，
且`Λ=[D,RH]⋆/i`，原时间字段的演化与约化动力学相同。
H0的图、能量和乘子均Hermitian；完整Y与独立sharp分支分别生成，互为伴随而不增添Y†。

新K1／K2保持原算子词及实际canonical Moyal项；与commuting替代的K2差含
精确`−√30/320 κ₀²`。新K3由四条原约束生成，实际Gauss三次germ上的旧伴随差被
生成修正精确消去。原Gauss域和Fock分级保留，真实补空间N2的二阶grade2四分量均为
`√30/30`，源点Fock范数平方为`2/15`，三次Y作用为零。
同名独审改用原Heisenberg关系的PBW正常序及normal→Weyl读回。
这些恒等式的验收范围是`mod ε⁴`；ε=1可求和作用、实际量子传播及谱由下游生成。

`source_quantum_antiunitary.py`由原`gamma0`与独立dual双支生成
`C=Γ(U) conjugation`，`U=[[0,gamma0],[gamma0,0]]⊗I63`。
完整504模H0的六q混合项、正规四费米张量、live correction、scalar／gauge与matter系数
逐项给`H0 C=C H0`；C固定玻色坐标、数目权重与原residual3群延拓。
真实两粒子Gauss二jet、全部四组件与正配对沿两条路径一致，完整Fock上
`C²=(-1)^Number`，不要求C为对合。原Y与392投影的非零交织差同时保留，
这项对称属于固定源时间列下的完整H0。
`AntiunitaryDefectPair.lean`把测试域方程与实际`T† u=z u`等价，
由原域不变及`TC=CT`生成到共轭z缺陷空间的反线性等距等价；逆直接来自C⁻¹。
因此正负i缺陷空间有同源配对机制，自伴扩张选择与原H的谱仍有各自消费者。
Python同名独审使用原密度系数、完整64×64张量及外幂行列式重建该作用。

`source_gauge_quantum_energy.py`从原native12 Hodge及Gram生成全部36规范坐标的
`H=(p−C)ᵀW(p−C)/2+V_B`，`W=K_E⁻¹⊗Gram⁻¹`、`C=vec(K_mix B Gram)`。
原九个散度恒等式使导数排序常数精确零，非零shift的动量交换子保留72个非零项。
原source读回`W=(σ/N)I3⊗Gram⁻¹`、`C=0`及完整磁势；真实36变量波包与原Legendre独签。
完整`−A0·G_gauge+div(Π_Ai A0)`保留给共同Gauss消费者，Y使用native范数1。
标量与规范这两组件的coframe仍为源允许的参数；各自紧支持算符域不代填完整共同时间发展。

`source_spatial_principal.py`直接从原空间primary消元生成四时间约束的非零二阶符号。
对于任意非退化空间metric h，曲率协向量
`P=((kᵀh⁻¹k)h⁻¹−h⁻¹kkᵀh⁻¹)/2`经原逆动能映为`2 det(e) kkᵀ/det(h)`，
故曲率与其逆动能配对、任意纵向metric梯度的曲率均为零。
源上的非零四阶反馈平方为零；欧氏动能替换不能保持这个消去。
另对原轴向任意实q的17个canonical79／dual24／scalar61响应块，实际矩阵相似变换给
`D_r⁻¹ C(q) D_r=r C_r(q)`及`||C_r||∞≤M`，其中`r=max(1,|q|)`。
由矩阵指数级数得到真实加权增长界与解析半径损失，包含非对角化情形。
这里的`c=N√2`是companion发生器比例，proper clock仍为`τ=N t`；
任意h/k的曲率身份与轴向响应界各守范围，变量系数空间PDE由active route继续构造。

`source_spatial_time_coframe.py`直接对原native规范密度作普通坐标拉回，保留其非零defect Q。
原gravity／scalar／完整Dirac-dual密度的相应协变身份同时支付普通坐标Noether。
先解原36条Maxwell电方程，再取`div Q`对四个time-coframe速度的系数，
源矩阵为`diag(−18/5,−2√30/3,−2√30/3,−2√30/3)`，行列式`32√30`。
固定F直接求导会漏掉非零本构反馈。真实full252与scalar70的空间jet生成四个时间更新，
保留样本的Gauss初始残差；这里只使用Q的散度保持，Q本身不设零。

`source_spatial_lorentz_time.py`以12条空间torsion保持和六条原metric Euler生成18个Ω_i速度。
原Cartan恒等式与metric Hessian给泛型联合逆；真实完整物质流支付contorsion导数，
24个`∂i∂j eTime`符号按反对称逐项消去。实际非零空间jet回写Lorentz24、Spin6及metric6，
四时间初始残差保留。代表固定为原source的`Ω0=0`；它与旧canonical `λ=0`的速度分量分别读取。

`source_coframe_constraint_transport.py`进一步由原metric6与Spin6重构
`E_sp=K(e)F4`，保留离约束面非零的空间Euler。
代入原普通坐标Noether后得到`eᵀ∂tF4+Σ_i eᵀK_i∂iF4+B(e,de)F4=0`；
原源读回`∂tF0=N div(F_i)`、`∂tF_i=0`。
原非退化空间三平面使Lorentz列独立，完整重构与时间系数在该source chart上可逆。
独立12×12线性解、四组方向导数及原Noether全部F／dF系数独签；
先消费其他约束和原Euler，再以解析零初值唯一性支付F4保持，次序不循环。

`source_first_order_cauchy.py`将这些原更新汇合为真正1500实变量的一阶系统：
`e16, Ω_i18, A_i36, F72, φ70, U_μ280, ψ/χ1008`，其中`U_μ=D_μφ`。
所有速度只消费场值和一阶空间jet；原`Ω0=0`及三稳定子代表固定，
`A0`由原D9逆生成，4+18、scalar divergence／curl和完整双Dirac按无环顺序求出。
非特征逆只依场值，并在原source处非零；这支付标准一阶解析Cauchy定理的实际输入。
对源chart内满足初始约束的三维解析profile，源RHS递推生成唯一局部解析解germ。
初始约束必须在空间邻域作为零germ成立，不能仅在一个点消零。

引入的scalar-gradient缺陷V、curvature缺陷W、C9和spatial torsion先传播，
原Gauss再以明确的C／V／W修正项传播；它们恢复其余原Euler后，F4齐次PDE支付最后四约束。
原168辅助场重构后，全部1310实Euler及固定代表下的原场唯一性成立。
独审重建全部1500 RHS，并在真正非零V／W／C／G的ambient数据上从定义微分，
72个A0和432个P的对称二阶占位量实际消去；原source与非平凡一致初值分别回写全部原Euler。
该闭合是局部解析空间Cauchy；一般光滑数据、全时间、完整量子谱和Lean时间路径安装各按原接口消费。

## 源color与spin不变量

`color_singlet.py` 从真实primitive gauge／Lorentz顶点提取生成元，消费原252维作用及12维H载体。
其220维三粒子wedge中，八个color生成元的完整共同核维数20，由epsilon×Sym³(spin)基底和投影生成。
实际spin Casimir给 `15/4` 的16维子空间及 `3/4` 的4维子空间。
源H0在spin-half子空间的外泄rank为4，三个空间生成元保持color核；该完整外泄矩阵供相互作用
consumer消费，不是对dressed hadron的no-go，也不据sector标签命名B/L或质子。

完整相互作用继续消费252载体及scalar-matter反馈，支付上述投影的dressed稳定性、连续谱测度和开放道。
当前责任统一见[active route](../../../../Lean/docs/handoffs/physics-cauchy-safe-active-route.md)。

## 验证

```sh
uv run --with sympy==1.14.0 python compute.py
python test_readout.py
uv run --with sympy==1.14.0 python dynamic.py
uv run --with sympy==1.14.0 python independent_dynamic.py
uv run --with sympy==1.14.0 python causal.py
uv run --with sympy==1.14.0 python independent_causal.py
uv run --with sympy==1.14.0 python causal_pair.py
uv run --with sympy==1.14.0 python independent_pair.py
uv run --with sympy==1.14.0 python causal_fock.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python all_momentum.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_all_momentum.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python world_momentum.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python all_momentum_causal.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_all_momentum_causal.py
uv run --with sympy==1.14.0 python free_current_family.py
uv run --with sympy==1.14.0 python free_current_dynamics.py
uv run --with sympy==1.14.0 python independent_free_current.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python multiparticle_kernel.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_multiparticle.py
uv run --with sympy==1.14.0 python full_matter_ports.py
uv run --with sympy==1.14.0 python independent_full_matter_ports.py
uv run --with sympy==1.14.0 python spectral_splice.py
uv run --with sympy==1.14.0 python independent_spectral_splice.py
uv run --with sympy==1.14.0 python spectral_splice_linear.py
uv run --with sympy==1.14.0 python independent_reaction_residual.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python reaction_harmonics.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_reaction_harmonics.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python native_boson_residual.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_native_boson_residual.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python full_jacobi_source.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_full_jacobi_source.py
uv run --with sympy==1.14.0 python external_leg_feedback.py
uv run --with sympy==1.14.0 python independent_external_leg_feedback.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python nonlinear_source_update.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_nonlinear_source_update.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python second_order_retarded.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_second_order_retarded.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python second_order_causal.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_second_order_causal.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python second_order_scalar.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_second_order_scalar.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python scalar_feedback.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_scalar_feedback.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python second_order_matter.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_second_order_matter.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python second_order_hamiltonian.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_second_order_hamiltonian.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python scalar_matter_response.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_scalar_matter_response.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python scalar_matter_exact.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_scalar_matter_exact.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python scalar_canonical_phase.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_scalar_canonical_phase.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python real_scalar_car_source.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_real_scalar_car_source.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python retained_hamiltonian_reduction.py
uv run --with sympy==1.14.0 --with python-flint==0.9.0 python independent_retained_hamiltonian_reduction.py
uv run --with sympy==1.14.0 python color_singlet.py
uv run --with sympy==1.14.0 python independent_color.py
```

`Audit.lean` 以 `trust=0`、warning-as-error 消费已证明的 `54/125` 正规乘积矩阵元，推出三轴 selected contact 矩阵元 `-81/125`；Python 回执精确重建在壳 source、完整四块静态树核、Fock rank/nullity、probe 诊断和源单位。
