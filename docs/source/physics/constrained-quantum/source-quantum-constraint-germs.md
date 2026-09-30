# 同源量子约束jet与原作用回读

固定`positiveSmoothUnifiedSource / repaired Dirac-dual / SpinPair.actual`，
原visit10／tick16／materialEntry及tick17不变。本卡保存从属配置jet接口；
实时责任见[Physics active route](../../../../Lean/docs/handoffs/physics-cauchy-safe-active-route.md)。

## 原Lorentz primary的源生逆二jet

`source_lorentz_quantum_section.py`从原空间coframe轨道`T_a e_sp`、原spin表示S_a
和已有六坐标切片生成12×12逆及其二阶复合。输入是任意有限CAR germ的值、六个梯度
与Hessian；`extend_jet`直接生成同一载体的16-coframe jet，不输入primary解。

原坐标固定为

```text
TIME      = (0,4,8,12)，
FREE      = (5,9,10,13,14,15)，
DEPENDENT = (1,2,3,6,7,11)。
```

实际源minor为−1。输出满足原四条时间动量primary为零，以及六条
`Z_spᵀΠ+Q(i·diag(S,S̄)⊗I63)=0`；全部16方向的一阶导数同时成立。
864个一般germ系数支付这些关系，原CAR504与所有内部sector完整保留。
时间coframe的四个参数值保留；这里的primary不是四条时间secondary或物理时空Ward。

## 同一原coframe作用的两种排序

`ambient_action`把生成jet交给原full16、系数左置的完整移位动量平方。
它和旧`SourceCoframeLiveOrdering`六坐标排序在实际源点、任意有限CAR germ上满足

```text
H_ambient(extend f) − H_reduce-first(f)
  = (N/2)(−∂q0+∂q5) f。
```

主部、全部CAR一体导数、零阶一体与完整正规二次张量均逐系数比较，
差精确为上述中央漂移。两个既有作用均保持原值，不把不同排序静默合并。
原共同H的form／半密度／Weyl层按自身已付接口消费；本比较直接命名上述coframe组件。

原轨道Jacobian为`J=q0 q2² q5³`。漂移在源点等于
`−K·∇log(J/v²)·∂`，是同一几何量的读回；configuration Jacobian与约束phase测度
是不同消费者，此式没有指定新的物理配对或声称两H已经幺正同一。

## 独立验收

`independent_source_lorentz_quantum_section.py`由Gram、反向Cholesky、正时法向与logΛ
另算78条曲线，重建144个一阶及1728个二阶项。原Noether与full16系数导数、
vacuum／8个一体／64个跨内部双粒子／28个同内部双粒子列、54梯度与21主部系数全部通过。
三组新germ保留真实混合jet；错Spin符号、删逆曲率及颠倒current字阶均产生非零反控。
相关九枚CAR Lean口以`trust=0/werror`核验，仅标准三公理。

## 同一100输入的完整122配置

`source_joint_quantum_section.py`把上述Lorentz逆二jet与原native12逆二jet复合，
从同一个CAR-valued100germ生成`coframe16 + scalar70 + gauge36`的完整122jet。
两群原矩阵的72个交换式成立，混合Hessian仍保留；它包含两群CAR作用的真实交叉乘积。
输出满足18个配置关系及2196个一阶导数，四个时间primary保持。
native broken9继续按二类约束解释，没有由配置关系改成full12物理first-class。

原122作用与早先`SourceJointLocalQuantum`的系数左置100作用在源点的差，
经全部动量、current及正规pair系数比较，恰为`d·∂`。非零100坐标为

```text
d0=−3√30/50，d5=3√30/50，
d7=21√30/200，d9=9√30/200，d12=9√30/40，d14=33√30/200。
```

本点native12的整个有序pair差及一体差均为零。
`native_action_from_extended_jet`使用原section embedding拉回梯度，再减去源生成的d，
对`extend_jet`生成的germ精确回读上述旧排序；调用方不给drift或约束证书。

## 返回当前form／半密度／Weyl H

`source_joint_current_hilbert_section.py`进一步实际消费原scalar `Π†Π` form与
`U_m=√ρ₃·v^(1+m/2)`的inverse二jet，再生成完整122jet并执行上述运输。
scalar form与旧`ΠΠ`的系数差在原源点全零；此处不消去它在其他配置的导数。
返回值直接等于当前`SourceJointCCRCarPorts`的四项微分H，旧H与原正配对均未改变。

`independent_source_joint_quantum_section.py`用相反组合顺序、原70动量逐个复合及
独立半密度微分核验。新N2跨sector、混合N=0/2/3和零值N1导数germ均回读当前H，
删半密度与删mixed二jet有非零反控；全部源荷sector及完整CAR504保留。
这把当前共同H接回完整配置载体，物理时间／空间Ward按其原电流和力另行消费。

## 全四时间参数的实际排序差

`source_lorentz_temporal_ordering.py`保持空间源切片，令原时间列为
`y=(n,b1,b2,b3)`，直接重算两种原coframe排序。原generic16 Hodge／Dirac恒等式、
24维Lorentz Hessian、24×16混合项及16×6 metric lift均消费六个原生成元；
全部24个current槽保留完整y。常线性Lorentz变换下，两个Pshift及内层系数导数
共同变换，没有由配置源点值外推量子排序。

令`b²=b1²+b2²+b3²`、`D=∂q0+∂q2+∂q5`，实际差为

```text
Δ_cf = H_ambient − H_reduce-first
     = (n/2)(−∂q0+∂q5) − (b²/4n)D − (3b²/8n)Number。
```

全部主部与current-gradient差为零；完整正规二次tensor反对称，故其双体算子为零。
一体项精确为`−3b²/(8n) I8⊗I63`。用原
`U_m=√ρ₃·v^(1+m/2)`实际拉回后，Number项与漂移的半密度导数相消，

```text
Δ_cf,current = (n/2)(−∂q0+∂q5) − (b²/4n)D + (3b²/4n)I。
```

在`b=0`恢复已签源点差；新增b²项保留在二阶时间响应中。
两种既有H仍各自保留原排序，该差没有被添加为新的物理相互作用。

## 当前H生成的偶时间力与13维原约束轨道

`SourceTemporalLorentzBalance.generate(value,gradient100,Hessian100)`让原逆半密度germ
同时进入当前四时间form及上述ambient作用，逐项消费完整y排序差。
它生成当前H的值、`Fμ=−∂yμ H`和全部时间Hessian，输入不含时间依赖或约束证书。
实际三粒子源germ的H与F0各有20个输出词，三个shift力各有一个非零输出词。
原`a=Gd`由同一残余Gauss section消费；四个时间primary没有代填secondary方程。

`orbit_direction_jet(u13)`生成time4、空间Lorentz6与残余su(2)3组成的
真实轨道输出二jet及同一122配置曲线的两阶嵌入。它使用原coframe列的
`y_body=exp(−tT)(y+t·dy)`及原Spin／native外幂作用；物理时钟仍为`τ=N t`。
所有time×Lorentz、time×native和两群mixed项均保留。

在原输入primary成立的germ上，空间Lorentz口满足
`i[H,Gsp,a]f=−Σμ(T_a y)_μ Fμ f`；三个boost非零、三个旋转为零。
加回同一时间primary项后完整Lorentz口消去。残余su(2)的原系数方向微分
直接给H及四个F的协变，不把broken9二类关系改为量子规范对称。

这是当前H在原约束轨道上的输出jet与偶Noether balance。
输入二jet不确定H输出的任意水平100导数，也不直接给固定ambient Π的全部16力；
该力消费者须保留原坐标变换的轨道动量项。
原固定Π的完整16力及其算符Noether现由[量子反馈接口](source-quantum-retarded-feedback.md#原full122作用的完整16-coframe力)详述。

`independent_source_temporal_lorentz_balance.py`在新非零三shift处另用有限非交换
Lorentz变换、原inverse numerator／Dirac平方和bit-CAR核验101个完整系数态。
两枚新N2／N3词的原U字面二导数与排序差相符；另一RawGauss section生成
vacuum／N2混合germ，H的10个词、四力10／1／1／1、13个基方向和两条混合曲线
均逐项回读，包括完整122嵌入的曲率。43项源绑定一致，删U产生非零反控。
