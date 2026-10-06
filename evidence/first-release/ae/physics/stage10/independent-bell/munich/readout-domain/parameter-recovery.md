# 参数逆读：可识别量与完整等价族

完整joint law精确决定四个读出偏置，以及两组相关乘积矩阵X、Z。
全域内，两套合法effects产生同law，当且仅当这三组量相同。
这是[ReadoutIdentification](../../../../../../Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutIdentification.lean)
的最大观测quotient；逆读消费原source产生的概率，不把目标概率输入源生成器。

本页的 law 纤维指静态 joint 概率读口；完整源场、actual action 和全部历史记录由
[完整发生恢复](history-source.md)消费。静态同 law 不推出完整历史不可恢复。

两run已签law的X00、Z00均非零。在该regular范围，全部同law参数恰由唯一非零s、t生成：

```text
Alice: (mu,u,z) -> (mu,s*u,t*z)
Bob:   (mu,u,z) -> (mu,u/s,z/t)
```

合法域由四个原始cone完整给出，平方坐标S=s²、T=t²下为
Alice的`u²S+z²T≤(1-|mu|)²`及Bob的`u²/S+z²/T≤(1-|mu|)²`。
所有正负尺度分支保留。canonical channel从每枚effect内部生成；原signed-gain及ideal-label
分解的身份沿旧source image保存，canonical代表不替实际硬件选择标签。

## 已识别的机器结构

两run各有完整连续矩形s、t∈[0.95,1.05]。
四个worst-case平方界支付整个矩形的合法性，参数点枚举不承担覆盖。
isotropic与anisotropic替代成员的128格Born概率独立重算，与原64格概率完全相同。
source/current/next保持，原20,403个prefix的所有统计因子因而恒等。

其中s=t的整族连全部轴都保持。Alice响应gain乘s，Bob响应gain除s，
两侧canonical误分类率变化而joint law不变。
因此该观测无法把两侧绝对响应强度分开；增加同类试次的精度仍保这条等价族。
完整纤维给出保全部静态 joint 概率的精确参数集合，实际已发生硬件对象的确定性保持。

## 整个原置信域的偏置外包

原E<40蕴含两侧component E_A、E_B<240。
固定一个own-setting的p=(1+mu)/2后，另setting用exact MLE likelihood上界消去，
得到原component的profile下界。两端的Decimal／integer log区间均达到log240，
导数符号支付外侧整段排除；八个区间共享原1/20联合预算。

| 运行 | Alice 0 μ | Alice 1 μ | Bob 0 μ | Bob 1 μ |
|---|---|---|---|---|
| April | [-0.05513, 0.07853] | [-0.08480, 0.04914] | [-0.10928, 0.01755] | [-0.11514, 0.01244] |
| June | [-0.05716, 0.07029] | [-0.07009, 0.05900] | [-0.06534, 0.07834] | [-0.01826, 0.12410] |

μ为固定raw编码下的P(recorded0)−P(recorded1)。表格向外取整；权威端点为
[主首次结果](identification-first.json)与[独立结果](identification-independent-first.json)中的exact Fraction。
这些是整个parent置信域的同时必要外包，不把固定law纤维或两枚拟合证人当作经验误差条。
外包的Cartesian product可以含被完整joint条件排除的点，原April零误差拒绝保持。

## 证书与消费

id0001科学先冻84f0639bf0，46显式声明、170模块声明、22一般consumer独立认证，仅标准三公理。
[内核签收](identification-certification-first.json)支付全q↔quotient、完整regular逆读、
合法尺度生成及原source/current/next；[最终consumer](identify_verify.py)核双实现、
全部区间端点、原counts／factor身份及source绑定，不读事件或重新拟合。

实际readiness单独登记最大可识别量、完整regular纤维及置信投影；
完整joint相容门保持通过，唯一硬件参数字段保持false。

```sh
python3 identify_verify.py --check-only
python3 ../../nist-real/readiness.py --munich-identification-only --output <新回执路径>
```

识别证书的override只移动回执；`--disable-munich-identification`关闭该读口。
source/root/whole-ledger/current/next、旧冻结结果、ETH custody及publish保持。

## 完整固定law纤维的近锐硬件范围

fb0001将原四cone消去为四个配对二次式，直接生成第二平方尺度T=max L。
一般convex dual消费同一source的四cone与canonical gain²；每个端点有一枚合法的
有理数近可达参数，gain²的界与可达值相差≤10⁻⁸。四个尺度符号分支全部覆盖。

| 运行 | side／setting | gain | e0 | e1 |
|---|---|---|---|---|
| April | Alice 0 | [0.76176, 0.98827] | [0, 0.11326] | [0.01173, 0.12499] |
| April | Alice 1 | [0.74810, 0.98212] | [0.01788, 0.13489] | [0, 0.11701] |
| April | Bob 0 | [0.79474, 0.95402] | [0.04598, 0.12562] | [0, 0.07964] |
| April | Bob 1 | [0.78985, 0.94852] | [0.05148, 0.13082] | [0, 0.07933] |
| June | Alice 0 | [0.67929, 0.99342] | [0, 0.15707] | [0.00658, 0.16365] |
| June | Alice 1 | [0.68308, 0.99445] | [0.00555, 0.16124] | [0, 0.15568] |
| June | Bob 0 | [0.76478, 0.99348] | [0, 0.11435] | [0.00652, 0.12087] |
| June | Bob 1 | [0.73196, 0.94690] | [0, 0.10747] | [0.05310, 0.16057] |

表格向外取整；[最终纤维证书](fiber-verification.json)保存exact端点和完整dual／primal。
这是两枚已签生成law的完整等概率纤维范围。实际置信域的必要外包由下一节独立支付。
gain为effect谱宽，e0/e1为原source生成的canonical channel误率；ideal-label身份不由代表选择。

## 整个原置信域的响应与误率外包

cp0001进一步从原full component E_full<80生成每run八个相关区间。
固定一个even-parity质量后，其他context及该context组内likelihood用exact MLE上界消去，
得到实际E_full的profile下界。两外端达到log80，精确导数符号支付外侧整段排除。
原32格source correlation、四corner bias乘积及Cauchy界自产gain下界，再运输至canonical误率。

cp0002消费同一个局部effect跨两个herald和两个partner setting共享的结构。
假设该gain≤G，四context的parity质量同时受bias乘积±G约束；组内与其他context用MLE消去。
八context全局Dirichlet常数只计一次，再累加四个受限likelihood损失。
允许域随G嵌套扩张，故profile非增，下端达到log80排除整个低响应区间。
这将八个旧下界全部严格收紧；以下表格是当前权威外包，旧表由cp0001回执和Git历史保存。

| 运行 | side／setting | gain | e0 | e1 |
|---|---|---|---|---|
| April | Alice 0 | [0.40218, 1] | [0, 0.32647] | [0, 0.33818] |
| April | Alice 1 | [0.38480, 1] | [0, 0.35000] | [0, 0.33217] |
| April | Bob 0 | [0.39699, 1] | [0, 0.35614] | [0, 0.31028] |
| April | Bob 1 | [0.39054, 1] | [0, 0.36230] | [0, 0.31095] |
| June | Alice 0 | [0.38830, 1] | [0, 0.33443] | [0, 0.34100] |
| June | Alice 1 | [0.36713, 1] | [0, 0.35148] | [0, 0.34593] |
| June | Bob 0 | [0.38894, 1] | [0, 0.33820] | [0, 0.34470] |
| June | Bob 1 | [0.36579, 1] | [0, 0.32623] | [0, 0.37916] |

这些是整个原联合置信域的同时必要外包，沿用原1/20预算，不使用固定law点作误差条。
八项有效gain均≥0.36579，canonical两类误率均低于0.37916；表格向外取整。
Cartesian盒可以含被完整joint条件排除的组合；April共同零误差面的拒绝保持。
[最终统计证书](response-projection-verification.json)保存16个相关区间、32个整数log端点核验、
八组exact响应界及原counts／factor身份。参数范围的裁决不需要未公开校准或新实验。
[共享响应证书](shared-response-verification.json)进一步保存八个36bit profile阈值bracket、
16端点、64项context likelihood和逐项改善。该bracket定位放宽后的profile阈值，
不宣称完整source域的真实gain极值达到此界。

fb0001科学先冻b903a7d501，26显式／85模块声明、21一般source-coupled消费者独立认证；
cp0001先冻0b89ec0e00，22显式／26模块声明、8一般消费者独立认证。两者仅标准三公理。
主／独立首次结果均通过，分别接入[纤维readiness](../../nist-real/evidence/readiness-munich-fiber-fb0001.json)
与[置信readiness](../../nist-real/evidence/readiness-munich-response-projection-cp0001.json)。
cp0002先冻62c6c0f800，原22声明source强口及1/20预算复用；[源与数学审查](shared-response-audit.md)、
双实现和[共享门禁](../../nist-real/evidence/readiness-munich-shared-response-cp0002.json)独立消费。
intake不打开事件、不执行优化或生成新端点。receipt override只移动相同证据，关闭开关先于读取。

```sh
python3 fiber_verify.py --check-only
python3 response_projection_verify.py --check-only
python3 shared_response_verify.py --check-only
python3 ../../nist-real/readiness.py --munich-shared-response-only --output <新回执路径>
```

## 完整联合响应资格与硬件等价身份

cp0003直接消费原source的乘积强口`|C−mu_A mu_B|≤g_A g_B`。
四响应cap共同约束八context，每项parity质量在bias乘积加减gain乘积的区间中取clipped MLE。
全局Dirichlet常数计一次，八项likelihood损失共同生成原E_full的下界。
profile达到80时，整个四维低响应矩形从原置信域排除，原预算1/20保持。

| 运行 | max(g_A0,g_A1,g_B0,g_B1) | max(g_A0,g_A1) | max(g_B0,g_B1) |
|---|---:|---:|---:|
| April | >0.67020 | >0.44918 | >0.44918 |
| June | >0.66386 | >0.44071 | >0.44071 |

严格下界向下取整。左右两侧的相同阈值来自该relaxation对两侧cap的对称性，
不表示实际硬件响应相同；max界也不读成每个setting都达到此值。
这是全部source点必须遵守的共同资格，原cp0002八个逐项界继续同时成立。

April四gain均设0.402182、June均设0.388945时，每项均在旧cp0002投影中，
新的联合profile仍分别给出logE≥781.8093和≥722.7543，严格排除两个整个向下矩形。
两枚原合法primitive证人的48bit向上gain外包通过该必要检查，原全prefix会员证书保持。
联合资格因此实际剔除了Cartesian投影允许的组合；通过该profile的组合仍由原完整source条件判定。

[cp0003合同](criterion-cp0003.md)先冻57c5855203；主首9c81304950与独立首ec83a15d02
核六个36bit阈值bracket、十二端点、96项likelihood与四控制的另外32项likelihood。
[联合消费者](joint_response_verify.py)同时消费原joint非空、cp0002外包及id0001完整regular等价纤维；
最大观测quotient与完整参数等价类是已认证身份，实际硬件唯一参数保持false。
联合cap对同law的任意合法替代硬件仍成立，不把统计剪枝当作等价尺度消失。

```sh
python3 joint_response_verify.py --check-only
python3 ../../nist-real/readiness.py --munich-joint-response-only --output <新回执路径>
```

公开单侧校准的作用与前向原子模型由[公开锚接口](public-anchors.md)维护。
Table5.4的H/V表示制备条件，尚未绑定两个指定run／两AOM／conditional泄漏；
这些名义函数没有被充当当前置信域的硬约束。

## 独立响应如何恢复唯一effect

ia0001将同law纤维的识别责任变成可执行逆读：完整law先自产X/Z产品比值，
两个已知归一化probe的signed响应自产两行线性系数。行列式非零时内部生成两个方向的
signed坐标，进而恢复全部四个effect。X/Z乘积锚与probe可以在不同setting，
坐标极点不要求补造非零坐标。该恢复消去四个符号分支，不选择canonical代表。

[原source恢复口](../../../../../../Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutAnchors.lean)
的`reconstruct_split_eq`及`same_law_split_probes_unique`由
[独立源认证](anchors-certification-first.json)核完整40显式／119模块声明及40独立consumer声明，
165新依赖节点及50已付source边界，仅标准三公理。
[两套有理实现](hardware-anchors-audit.md)分别以逆矩阵与Gauss消元核验；
响应误差区间按同一仿射逆像保留宽度，不读成实际精确点。

[ia0001合同](criterion-ia0001.md)先冻efbad2dad9，
[构造首证书](hardware-anchors-first.json)ddaaeedf26核34个已知law控制、68个signed响应、
1088格source概率与全部四符号分支；另外通过坐标极点、共线反控与误差区间控制。
测试响应由已知仪器生成，actual独立锚已有及actual唯一参数字段保持false。
完整Bell经验概率的精确识别没有被放入输入。

[新的运行／AOM来源](hardware-anchor-access.md)已支付两指定run的名义控制表，
不把光学命令、原子处实际方向、rawCSV编码和响应尺度合成同一身份。
该接口同时给出原子前向响应的trace差如何把已识别偏置转成绝对器件尺度；
原始控制生成J的责任与上述已签唯一逆读分别消费。

```sh
python3 anchors_certify.py --check-only
python3 hardware_anchors_run.py --check-only
```

## 原始脉冲自产响应与全域面积约束

af0001把原始矩形脉冲传到12态原子电离响应，Hamilton图及rank1 jump自产32-real闭包。
主Directed Decimal稀疏传播与独立144复坐标整数传播交叉；四理论控制的12个概率／trace
包络及12,288个符号restriction系数通过。两套误差由CPTP trace-norm收缩支付，
[源与误差合同](atomic-forward-source.md)分别绑定公开动力学来源和数值实现。
理论两响应的trace严格不同，兑现绝对尺度逆读所需的非退化控制。

同一生成器对两个初态支付`gain≤min(1,7 area²/4)`，
`area=∫Omega12 dt`为读出Rabi面积。cp0002整个原CS的gain下界因此直接生成原始控制约束：

area单位为rad，该必要界覆盖登记的固定bright/dark chart、任意非负cycling／ion强度
及有限矩形序列，沿用原1/20预算。最初逐项／共同数值由af回执保留；
同时消费完整器件分解后的更强当前数值见下一节。
名义原子常数和理论控制不作为两个run的实际波形或置信盒。

[af0001合同](criterion-af0001.md)先冻43773f9162，主首6d82888e4f、独立首8ff61c0ac9，
[最终证书](atomic-forward-verification.json)f9f0e42e5e核八个逐项与六个共同面积界。
44项focused控制通过；[实际门禁](../../nist-real/evidence/readiness-munich-atomic-af0001.json)
消费概率传播和全域必要约束，intake不读事件或重跑传播。
actual独立锚可用性、actual唯一硬件及新增内核GKSL证明字段保持false。

```sh
python3 atomic_forward_verify.py --check-only
python3 ../../nist-real/readiness.py --munich-atomic-only --output <新回执路径>
```

## 完整探测器分解与微硬件共同资格

df0001从同一source effect构造完整探测器实现：E_click=dI+kJ，k=(1−d)eta。
令m=(1−mu−g)/2、M=(1−mu+g)/2；g>0时全部实现恰为
`0≤d≤m, M−d≤k≤1−d, J=(E_click−dI)/k`。
合法J及逆向保真由源口自产，零响应／零探测因子另有精确层；
任意合法J的特定pulse实现由物理前向producer分别承担。

完整分解支付`eta lambda_max(J)≥2g/(1+mu+g)`。原click字典未签，
以B=max(|mu_lo|,|mu_hi|)消去两种polarity，整个原CS的gain≥G生成
`H=2G/(1+B+G)`、`eta lambda_max(J)≥H`及`d≤(1+B−G)/2`。
与af0001联立，生成`eta min(1,7 area²/4)≥H`及`eta area²≥4H/7`。

| 运行 | role | eta下界 | area下界(rad) | d上界 |
|---|---|---:|---:|---:|
| April | Alice 0 | 0.54322 | 0.55715 | 0.33818 |
| April | Alice 1 | 0.52368 | 0.54703 | 0.35000 |
| April | Bob 0 | 0.52712 | 0.54883 | 0.35614 |
| April | Bob 1 | 0.51876 | 0.54446 | 0.36230 |
| June | Alice 0 | 0.53243 | 0.55158 | 0.34100 |
| June | Alice 1 | 0.51089 | 0.54031 | 0.35148 |
| June | Bob 0 | 0.53015 | 0.55040 | 0.34470 |
| June | Bob 1 | 0.49103 | 0.52970 | 0.37916 |

下界向下、上界向上取整；效率是fragment效率，背景d是具名探测分解的概率，
不与canonical assignment错误合并。所有角色还同时受原gain与完整joint资格约束。
六个原max-ray生成更强的最大面积必要界：

| 运行 | 全四角色至少一个 | Alice至少一个 | Bob至少一个 |
|---|---:|---:|---:|
| April | >0.65499 | >0.57849 | >0.57285 |
| June | >0.65141 | >0.57735 | >0.56733 |

原始盒以eta≤eta_U、area²≤A²_U定义；s=eta_U min(1,7A²_U/4)自产
`gain≤min(1,(1+B)s/(2−s))`，四cap直接消费旧八context joint profile。
两枚原cap控制的raw-hardware回拉通过必要资格；两枚逐项合格低响应控制的完整原始盒被联合排除。
这种通过不登记物理pulse会员，完整源域与可达性分别消费。

四个已冻理论原子响应×八角色生成32必要探测器域、64极性分支。
零／弱读出对应的16个整个响应盒被排除；另外16个必要域非空。
主边交点与独立半平面裁剪保留闭边、线段与点；非空域不成为实际控制输入。

[源口](../../../../../../Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutDetectorFiber.lean)
38显式／85模块声明、29独立consumer与完整120新依赖通过认证，仅标准三公理。
[df0001合同](criterion-df0001.md)先冻0096b842f2，主首dbd4d97770、独立首c9583ca37f，
[最终证书](detector-fiber-verification.json)4a68516eac保存八逐项、六共同界与全部响应域；
[实际门禁](../../nist-real/evidence/readiness-munich-detector-df0001.json)消费完整分解与微硬件共同资格。
54项源／数值验收及4项readiness控制通过。intake不重跑量子传播或joint profile，
原预算1/20、actual唯一性false与source/current/next保持。

```sh
python3 detector_fiber_verify.py --check-only
python3 ../../nist-real/readiness.py --munich-detector-only --output <新回执路径>
```

## 真实脉冲像接入完整joint域

rf0001以原始矩形pulse自产的真实pb/pd取代任意合法J。
给定已签source effect，g=sqrt(u²+z²)>0，b=pb、r=pd，
两条native谱条件
`g(b+r)≤(1−mu)(b−r)`及`g(2−b−r)≤(1+mu)(b−r)`
充要地产生合法k=g/(b−r)、d=(1−mu−k(b+r))/2、eta=k/(1−d)。
单位XZ轴由−(u,z)/g符号生成；原子constructor独立生成J，读出恰恢复原effect。
realizer运输已有source证人，不把证人解释为实际精确q或新的物理预测。

整个响应盒以同一worst corner(b_lo,r_hi)核两个有理平方不等式，
gain²直接来自原u²+z²；完整盒与真实响应均被覆盖，midpoint不承担验收。
四枚固定pulse的双实现响应均满足两个run全部八role的条件：

| 固定pulse (tau,R,C,A) | pb近似 | pd近似 | 两run八role |
|---|---:|---:|---|
| (4,4,25,83/25) | 0.9789524726 | 0.0220589984 | 全部通过 |
| (5,4,25,83/25) | 0.9805187204 | 0.0273147267 | 全部通过 |
| (4,5,25,83/25) | 0.9794876419 | 0.0341879463 | 全部通过 |
| (5,5,25,83/25) | 0.9808471203 | 0.0422676907 | 全部通过 |

表中数值只用于阅读，验收使用原未经剪裁的严格传播包络。
四组pb/pd两两严格分离，形成六对不同物理原子响应；每组生成的读出effect均相同，
因此原64格joint概率和全部20,403前缀因子／财富判决由源等式保持。
登记逐role物理pulse-image域与原joint置信域的交集非空，
不同真实pulse响应的同law实现歧义已经构造，不依赖隐藏数据或新实验。

该模型沿用per-ownsetting合法读出，d/eta按role生成；
两AOM共用同一d/eta的更强合同未由这些逐role构造代付。
原子的模型中心、构造方向和新器件值未登记为实际输入，actual唯一参数保持false。

[源realizer](../../../../../../Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutPulseRealization.lean)
26显式／74模块声明、43一般consumer与125新依赖独立认证，Std3。
[rf0001合同](criterion-rf0001.md)先冻f7e422aed6，主首e337b1bb9b、独立首619ab3fbd5，
[最终证书](pulse-realization-verification.json)35a0d83035核四响应、12包络、12,288系数、32实现域及六分离对。
[实际门禁](../../nist-real/evidence/readiness-munich-pulse-rf0001.json)消费真实pulse像、保真joint会员及物理响应纤维。
44项源／数值验收与4项readiness控制通过；intake不传播、不读事件或重播prefix，原预算1/20保持。

```sh
python3 pulse_realization_verify.py --check-only
python3 ../../nist-real/readiness.py --munich-pulse-only --output <新回执路径>
```
