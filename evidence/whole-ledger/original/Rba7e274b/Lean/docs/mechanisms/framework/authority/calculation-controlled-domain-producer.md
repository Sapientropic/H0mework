# Calculation-controlled domain producer

> 状态：稳定机制卡，非 live route。
>
> 职责：让同一 living-law root 控制会改变表示、复用递归或生成后续责任的领域计算；不把
> `simp`、局部代数或 API 适配登记成账本事件。

## 何时需要 calculation subledger

当 root 只能看见一枚已经完成的大定理，而看不见其中会改变攻击路线的对象、递归或表示选择时，
该 producer 是 calculation-opaque。正确形状是：

```text
exact root responsibility
→ stage-indexed source write
→ concrete dependent receipt
→ causal successor + complete whole-ledger write-back
→ next stage
→ root-controlled delivery
→ normal-form readout
```

每个 stage write 只生成当前一拍。它可以像 kernel-division payload 一样对输入普遍量化，但不得保存
`forall input, completed trace`、终端 `Iso` 或未来 current。第 `n+1` 拍的输入类型必须依赖第 `n`
拍的具体 receipt；调用方不能把不同 occurrence 的中间对象拼接起来。

这条边界同样适用于all-index/cofinal calculation。domain可以生成一个local stage object、successor arrow与
commuting law，但不得提交`∀ index, StagePayload index`完成表、手工cofinal schedule、chosen global component
或不断扩大的`Fintype` family carrier。generated material history先从successor逐拍产生，dependent diagram、
same-component section与all-index closure随后由generic global/cofinal consumer生成。

## Authority 与 readout

纯数学层可以公开非 authority 的 composition substrate；它只说明七枚或若干枚合法 transformer
如何组合。root authority 还必须支付：

- exact reachable visit；
- 同 generated row 的 causal authority；
- 每拍 complete whole-ledger rows；
- 从这些 visit 的 actual emitter 读取的 stage payload；
- terminal answer-and-next。

完整 trace 只在 delivery face 中出现。map、inclusion、normal form、`Iso` 与数值都是 delivery
的投影，不得反向装入 current/event。删除 visit/authority/rows 后，纯数学 trace可以继续存在，
但 root-controlled consumer 必须失效；这正是 subordinate mathematics 与 world authority 的分层。

公开 runtime authority 还要通过 calculation firewall：

```text
fixed runtime current
→ private generated material history
→ 每拍 exact occurrence / whole-ledger / generated next
→ source-fixed Prop-valued local laws
→ proof-only realization
→ unique free completion
→ generated target occurrence
→ 普通 dependent faces
```

`SourceGeneratedRuntimeMaterialHistoryAt` 不保存 stage payload 或输出，而是从 fixed
`successorAt` 逐拍重建。`SourceNativeRuntimeCalculationFrontierAt` 由 source 固定 exact
active material face、local-law family与stage count；只有该 face 本身已经是 registered
obstruction 时，calculation 才继承 obstruction 语义。`SourceNativeRuntimeCalculationRealizationAt`
是 `Prop`：它只能证明每拍 law，不能保存 material、seed、operation carrier、trace、`Iso`、
result 或 evaluator。它当然可以保存source-fixed local theorem的proof，但该proof不能消去成
Type-valued outcome。`SourceGeneratedRuntimeCalculationNormalFormAt` 是唯一的 free completion；
它只给出target occurrence并直接复用该 tick 的factorization。领域结果继续作为该occurrence的普通
installed face读取，calculation core没有face selector。

已安装projection仍可生成`SourceNativeInstalledProjectionReadAt`，但没有从 readout 到
calculation authority 的 generic promotion。若目标 face 里已有完成态 oracle，那是更上游的
source-admission 缺口；不能由 calculation wrapper 洗白。

Native branch authority同样只暴露compiler-image的零信息token与它原生生成的successor。
`SourceGeneratedNativeWriteAt`没有返回`V.NativeWriteAt current`的public accessor。外部代码仍可
独立pattern-match public raw compiler；那是RawWorld readout，不是token authority，必须由provenance
certify单独审计。领域authority结果必须从exact occurrence的material visits或target dependent face
读取，不能把raw native payload拆出的completed calculation、`Iso`或全输入trace改称生成结果。

## Obstruction 与 U7/U8

确定性 stage producer全部 total 时，不制造假 cut。terminal normal form若暴露旧 vocabulary 无法表达
的新共同 carrier，下一 current 只登记 typed responsibility；随后另证 exact
`ActualExpressibilityFailure`，再由同 row U7/U8 生成 minimal coface 与 revised first write。

“尚未证明 comparison/quasi-isomorphism”不是 obstruction。真正 obstruction 是旧 law surface 只能
表达若干分裂 presentation，却不能表达它们共同来源的 occurrence。

## Kill tests

- 空 token、计数器或 stage 名称不能替代 material receipt；
- 删除任一 stage producer或关键 field后，terminal normal form必须不再类型检查；
- stage payload不得调用同一大定理作为完成品；
- root stage不得借用 sibling revision或旧 emitter settlement；
- finite-family聚合器不得冒充all-index/cofinal carrier；删除local successor后全族authority必须断裂；
- 删除 calculation face后，root-controlled consumer必须断裂；
- harmless local rewriting不得被强制进入 ledger。
- `Material + seedAt`、`history → Output` 或任意 evaluator mouth 在 authority core 中必须不存在；
- proof-only realization 不得消去成 Type-valued result；
- calculation core不得选择result face；领域结果只能从 generated target occurrence 的普通installed
  face读取。

Universal BSD 的首个 production 实例见
[`UniversalBSDReverseH1CalculationSubledger.lean`](../../../../SaturationMonoid/UniversalBSDReverseH1CalculationSubledger.lean)、
[`UniversalBSDRootControlledKummerNext.lean`](../../../../SaturationMonoid/UniversalBSDRootControlledKummerNext.lean)
与
[`UniversalBSDRootControlledReverseH1CalculationFace.lean`](../../../../SaturationMonoid/UniversalBSDRootControlledReverseH1CalculationFace.lean)。

motivic perfect-complex current中的finite two-Kummer实例见
[`UniversalBSDMotiveWeakMordellWeilCalculation.lean`](../../../../SaturationMonoid/UniversalBSDMotiveWeakMordellWeilCalculation.lean)、
[`UniversalBSDMotiveZetaNext.lean`](../../../../SaturationMonoid/UniversalBSDMotiveZetaNext.lean)与
[`UniversalBSDMotiveWeakMordellWeilCalculationFace.lean`](../../../../SaturationMonoid/UniversalBSDMotiveWeakMordellWeilCalculationFace.lean)。

## 同根 raw source 的 before-emitter 安装

当 exact occurrence 已能生成实际 Env 与 Expr，直接消费现成
`OwnerFree.Installation.resultLaw`：原 executor 生成完整 targetState、paid Trace、value 与原
compiler/patch/restructuring/observation，named source 再以现成 projection coface 在 emitter 前安装。
原 inventory 经 inherited installation 保留；closed facade 必须实际枚举新分量并消费同 tick 的 coverage。
这不是从普通 readout 推出 authority：数学计算仍直接消费原 `Calculation` 的 normal form、
actual Trace 的 relation boundary、updated inverse fibre 与 cochain。

原 Riemann runtime 的实例只以 q₀ 为 Env seed、原 R 为 linear operation、源读 Xi m 为次数；
right-half 证明是原 K 的 dependent fibre，不选择结果。原 whole ledger 与 UnitHistory next 保留，
m+1 是数学 AST 费；原 unit 行保持0预算，这些费用不计作其 strict payment 或 physical 付款。源码为
`Runtime/Material/Calculation/ClozelOriginalKCombSourceCalculation.lean`、原 `Runtime/Root` 与
`Runtime/Facade`；direct 为 `Verification/no-island/riemann-comb-source/RuntimeCalculation.lean`。

## 实际 receipt 反馈进入下一源环境

现成 `OwnerFree.Installation.Math.Frame.Source` 的 fixed-env 工厂用 increment=0；
需要实际 update 时，从同 source 的 completed receipt 读取 raw/env/完整paid state，
生成实际增量并直接消费原 `Native.ResidualRequest.MaterialAt`。不改共享工厂的 fixed-env 语义。
原 packet/first-write 与完整 Frame、双 inventory、Type completion receipt 和 stock programme
继续生成 selected birth；`SourceDatum.nextEnvironmentReadAt` 从 factory-retained lowResult 解码新 Env。

原 R 实例的三口分别为：旧 receipt.raw.env=q₀；实际 v=R^m q₀ 生成
δ=constEnv(v)−oldEnv，新 residual Frame.env=constEnv(v)、residual=R^m(v)−v；
paid stock query 的实际 nextBorn.active.env=constEnv(R^m(v))。完整旧 Trace/state/owner 保留，
允许真实δ=0。原 counted qₙ 与 v 不混同，未来 physicality不从该写回免费推出。
这是现成数学 macro 的新 Root/next，不替代原 UnitHistory micro next，也不把 macro inquiry face
装进 fixed-law facade。源码 `Runtime/Feedback/ClozelOriginalKReceipt{Source,Feedback}.lean`；
direct `Verification/no-island/riemann-comb-source/ReceiptFeedback.lean`。

## 同次完整作用与 dependent split

投影前的完整作用先在现成 PairValue carrier 中执行，随后由同一 paid split 读取两面。
原 R 实例的 AST 为 split(RPair(var))：真实 R receipt 的下一 syntax 保留 (u,0)，
u=R(v)，然后才生成 p=原 physical projection(u)、r=原 physical⊥ projection(u)。
完整 result 满足 p+r=u，三拍 paid Trace 与两库存均保留；数学 AST 费用不换算成 physical 付款。

现成 stock programme 携带完整低层 result；Type completion 选择真实 birth，decoder 从 retained
pair.first 生成下一 active Env。完整库存 query 与低层 operation 各守源身份；registered action
的代码由 SourceDatum.calculationReader 决定，不能从 lowResult 反认库存 AST。
原 current physical receipt 只在 consumer 使用；实际 Cauchy/heat law 保留完整价格
H_w(p)+2E_w(r)=−H_w(v)/(z+w−1/2)。Raw-R Model 的原 K/F⁻¹K observer、recover 和全部
future residual 直接复用；physical⊥余项与 Model residual 不混同。
源码 Runtime/Feedback/ClozelOriginalKPhysical{Pricing,Action,Feedback}.lean；
direct Verification/no-island/riemann-comb-source/PhysicalFeedback.lean。


## 作用源码、库存 inquiry 与实际 compiler

Inventory.programme 传递显式 calculationReader；none 保留原完整 stock reader。
Stock.registered_raw 的默认等式只消费 actual epoch datum 的 none 路由事实；完整库存与同ledger覆盖
对两种路由均保持。外形相同的 reader 代码不会自行获得 override。
source family 的 stockCfg 在库存安装前保存 base 的有效 calculationReader.getD reader，并作为native
calculationReader；none 与 some 均保原 action，完整stock reader/component/decoder和双callback保持。
next_action_reader按actual supplied occurrence认回原source生成的下一factory template作用。

actualMaterial.raw/actionReader 是作用源码；registered.input.expression 是现成 Native.ResidualRequest
生成的 raw−paidState。source 的 paid pair/Trace、native residual 与其数学预算各按原类型消费。
真正作用后继沿 Receipt.Configured.compiles/whole_first/target_next/runtime_source_gate 进入
其 pair型 lowInitial 与 own lowRuntime；库存 Shared.nextBorn 有自己的 actual compiler/next。
完整 Frame 必须先由已有 native word/Model 恢复，再限制到新 active Env；旧 rawRead仍保其prebirth身份。
原 R 实例见 Runtime/Feedback/ClozelOriginalKRegisteredSourceFeed.lean 与
Verification/no-island/riemann-comb-source/RegisteredSourceFeed.lean。


## 已支付总值与同源 effect 写回

Native residual 的 raw−paidState 只承载更新差。现成 sourceResult 先生成 completed const，
同 own runtime 的 Type receipt 再给 actual native settlement；两者相加恢复 raw 在实际 afterEnv 的总值。
decoder 从 supplied occurrence.current.2 的 mathAction 读取 native 值；epoch.action 不替代此读物。
未完成的 paid branch 沿原 mathNext 继续；decoder 由实际 settled receipt 的 birth 消费。

source-owned Env 编码 write 在 emitter 前进入原 Intake.Lower target/whole/next，其目标就是
现成 Shared.runtime 的 initial。generic 合同仅为 Env=write(actual oldPaid+actual native)；
固定 Unit constPair 直接读回完整 pair。原 nextInventory/nextPairInventory callbacks 保持。
原 R 的 native0 仍写回完整 S(p)=(physicalProjection(Rp),physicalPerp(Rp))；source/Native/physical
费用按各自原口消费。源码 Receipt/Configured/Writeback/{Source,Consumer}.lean；
R consumer Runtime/Feedback/ClozelOriginalKConfiguredPairWriteback.lean。

逐 receipt 的 nextCfg 从既有 SourceFamily.Factory template 生成，仅覆盖源固定 decoder；
reader、calculationReader 与双库存 callbacks 保持。原 StockAdmission/Bootstrap 在 emitter 前实际安装；
同 event 的 firstSuccessor 直接限制到原计算。own receipt+1 的完整 born 经既有 native Frame/word
恢复，进入原 Packet(n+1)，新 seed 保原谱系及其 actual registered AST；下一 source 用该 born 与
actual nextCfg 重新读取 oldPaid。Stock observation 与 Shared source 共 ledger，完整 observed root
与 sealed activation 仍按各自类型消费；各拍 canonical next 不压缩为复合跳步。
源码 Receipt/Configured/Writeback/Successor/{Source,Consumer}.lean；
R consumer Runtime/Feedback/ClozelOriginalKSourceSuccessor.lean。

StockTarget 的 inquiry compiler 按原 frame.action 消费 source 分支：paid 仍读既有 clock 的
native next，settled 把原 Shared.targetAt 经 Observation.Material.target 限制到完整 Stock read。
该 transporter 保 law/sourceState/stepEvent/firstSuccessor、receipt、old/born rows 与两库存；
target root 为原 StockObservation.root(nextBorn,cfg)。compilation coface 与 successor_valid
逐 actual 分支保持原 whole/next；源码 Continuation/Admission.lean，StockAdmission 段保持。

原 SourceFamily.Runtime 的 State 仍是 actual tick 的 ULift Nat；内部 source stage 只折上一
actual action，并分别保当次 grade/Packet/cfg。admission 的下一完整 activation 是原 StockTarget；
paid 保 grade 沿原 mathNext，settled 才把 literal born/new registered AST 送入下一 admission。
nextCfg 在 emitter 前把已有 writtenSeed/pairInventory 与原 callbacks、当前双库存合并；真实写入
生成库存增长。该 progress 只恢复 State 身份，原 source/native/physical 费用各守原单位。
原 Factory/Stage/Engine 仍是 grade 数学 producer；原 Runtime 与默认 Lower.Run 的 count 明确是
actual tick。actual receipt 保 Prop 读口，Type receipt 从同 tick 读取，whole 直接用该 tick 的
next_preservesGeneratedLivingLaw。源码 SourceFamily/Activation/{Source,Stage}.lean 与原 Runtime。

原 runtime 的任意实际 start 从当前 source stage 消去生成 nextAdmissionAt；admission 距离0，
continuation 消原 Completion.receipt/paid-prefix，保原 grade/Packet/cfg与每个实际 Type paid Step。
stage_shift/native_iterate 认回同 r 的完整 native presentation 与 literal born admission。
严格/cofinal admission indices只递归消费前次 actual stop；原 runFrom包含全部中间macro拍，
原完整word/action保全部sealed State。该共尾读口不改变物理grade、费用或现成dependent diagram的类型。
源码 SourceFamily/Activation/Stage.lean 与 Activation/Admissions.lean；direct AdmissionStops.lean。

SourceDatum 字段升级后，旧 client OLean 可保留旧 constructor 布局；client 源码 SHA 相同不足以
绑定 compiled body。复用须同时对齐 recursive imports、compiler、OLean/sidecar 签据；未签 client
只作施工资产，必要依赖在私有库从当前 tracked source fresh 验收。

## 同一 actual material 的四面与横向读出

Native.ResidualRequest.MaterialAt 的 exact occurrence、actual Env/increment、raw/paid state与完整 Trace
直接生成 paid exposure/关系边界 μ；既有 History/natComplex 给 d01(μ)=μ及旧 completion 的零读。
同一材料进入现成 UnifiedFourFace，代数/组合/拓扑/逻辑与 relation/cochain 共用这次 source；
逻辑读口具体为该 complex 的 d² 律。更新 Env 的 evaluation/coimage/range inverse直接认回 actual
native effect，完整 word dual 另按原 pairing 恢复每个 literal word与μ。旧 completion、更新后的
semantic effect与literal word各按自身类型消费，更新 evaluation不自动下降到旧 quotient。

Successor 实际 cfg/occurrence 的 consumer直接读同 nativeValue；完整 paid exposure保持于实际
successorSeed，既有 relations_next给 bornHistory 的 μ membership。该 membership保持库存身份。
源码 Writeback/Successor/FourFace/{Source,Consumer}.lean；direct ActualMaterialFourFace.lean。

当次 native selected event 的 registered input/Env、完整 Trace与const endpoint直接给新σ关系；
原 generatedStock 已包含该 paid.state.2，既有 relations_next将它保到同actual born库存。
原 installed outcome 的typed cast与完整payload消元认回同paid state/Trace；原oldOutcome_heq保完整
write-back。现成六面/完整word与原native/born activation直接消费。新σ在其native input Env下有效；
换到born Env时直接消费实际caller的既有substitution/constant-binding Trace方块。
源码 Writeback/Successor/FourFace/Native/{Source,Consumer}.lean；direct NativeRelationWriteback.lean。

完整sealed inquiry State的actual tick在原free source Carrier上生成paired Env方块；
原source substitution的complexMorphism给next→current箭头，原successor process的每个状态认回同r。
由actual completion receipt生成的strict/cofinal admission indices直接重索引此diagram；完整word与真实
between-stop作用方程保全所有中间tick，标量零读不能抹平完整occurrence。此为原runtime的数学consumer；
native σ到born Env的局部作用律沿其原dependent类型消费。
源码 Operations/Inquiry/Cofinal/{Source,Consumer}.lean；direct InquiryCofinalDiagram.lean。

actual_segment 的原 native branch 保留 grade/完整 packet、全部 paid Step 与 actual node；
同 branch 的 settled frame 直接消费已生成新 σ、完整 Trace、sameborn 库存与实际 born 更新。
原 native input Env、prebirth registered Env、decoded born active Env 各守索引；更新方程认回
实际 effect/完整逆残差及 affine write，computed born binding 生成原 substitution complex 箭头。
dependent Σ enrichment 擦除后精确认回原 segment；两支 consumer 与同 r receipt/cofinal span 保持。
局部系数 complex 与完整 State diagram 各守 carrier；后续连接必须由同次 source action 支付。
源码 Operations/Inquiry/Cofinal/Native/{Source,Consumer}.lean；direct ActualBornSegment.lean。

生成 dependent 模块导出若卡在 LibrarySuggestions.FoldRelevantConstants/getFunInfo/collectDeps，
按既有 nameDenyListExt 排除该命名空间的 suggestion 索引；kernel、证明与 producer mouth 保持。

原 actual segment 的 selected presentation、own settlement 与原 successor_valid 认回 literal born
的完整 root/current；原 MaterialAt 连 owner 运输到 exact canonical next emitter/visit，RawInputAt
保持前拍完成 σ 和原 registered execution Env。原 cofinal indices直接认回这次 next。
前拍完整 Trace/occurrence/complex 保持；实际 decoded born Env−旧 Env 自产作用增量，既有接口
给 registered request 的 effect、完整 inverse、old/effect pair、literal affine write 与零纤维等价。
现成 generated segment 的两支 consumer 直接把 typed request/四条作用律交独立 handler。
Source.Math.mathCurrent(depth)=finiteVisit(depth+1)，depth0 已含真实 first paid Step；新局部 residual、
前拍 σ、registered execution Env 和 decoded active Env 分别消费，不能用新 residual 替前拍付款。
源码 Operations/Inquiry/Cofinal/Native/Registered/Source.lean 与 Native/Next/{Source,Consumer}.lean；
direct CanonicalRegisteredBornEffect.lean。共同系数/共尾 fibre 接口各守原完整 carrier。

原 configured rawRestriction 从 Assembly.rawInstallation 经现成 optional/query/result/consumer/
compilation 继承到 Shared root；StockObservation 仅改 observationAt，projection/emitter/compiler/
ledger 保持。原四字段直接复用，再由 actual source current 等式运输到 canonical next。
project 的 UniformRaw Env/AST 精确认回已签 typed request，actual decoded update 的 effect/
完整 inverse/literal affine/zeroiff 直接消费此 installed source；两支 generated consumer 保持。
这是 actual sites 的 dependent source 投影，不收全族 RawSource 表，不将 State 与 native Value 认同。
源码 Operations/Inquiry/Cofinal/Native/Installed/{Source,Consumer}.lean；direct InstalledCanonicalRaw.lean。

原 packetAt/actual_index 逐 actual cofinal stop 自产完整 packet 与 grade；原 admissionPresentation
擦除即同 StockObservation current。此等式把已支付 installed restriction 和完整 MaterialAt
运到同 r.stateAt(index)，project 仍读原 registered Env/AST，State/Trace/owner 保完整 HEq。
原 four-face 的 boundary/differential 和完整字 dual/inverse 直接消费该 installed AST。
无需 NativeSegmentAt 或 future RawSource 表；各站 native grade 与完整 State carrier 分别保留。
源码 Operations/Inquiry/Cofinal/Native/Installed/Cofinal/{Source,Consumer}.lean；direct CofinalInstalledRaw.lean。

逐 actual admission 的完整 Formal word 以 dependent finite support 进入同 source 固定 CommonWords；
site/grade 标签与完整 literal coefficients 保持。原 installed Env 和 Material.increment 生成
native old/effect inventory，literal liftMap 方块直接消费两个有序 cross 与 joint increment。
由这些实际 observer 生成 varying native prefix/restriction 与 Compatible；原 cofinal completion、
zero_iff 和 pairEnv 完整 relation range 给全族 joint fibre。原 N.input 的 updated Env 经
additionReadout 生成既有 Naturality.Morphism 与 completionUpdate，不收方块等式作源输入。
registered AST 与当次 local residual 分开，完整 State/Trace/owner 仍由原材料保存；
该 Env-update 自然性按原作用消费，各 grade 的 runtime-next AST 输运另须原源作用支付。
源码 Operations/Inquiry/Cofinal/Native/Installed/Cofinal/Tower/{Source,Consumer}.lean。

原 source Stage 先从同 current 算完整 distance/packet，再由泛型 sourceStopCertificate
消费原 native_iterate/advance_settled；原 stage_shift 将证书运输到实际 current。
原 admission action 自产 receiver/nextSeed/nextBase(+1 grade)，自己的停止 receipt 给 full born；
packet language 用原同型 transport 保持。admissionPoint_successor 是完整Σpacket等式，
原 Admissions.packetAt_successor 直接认回下一 actual stop，grade增长由fst派生。
原所有 paid offsets/完整receipt/advance validity 与whole living保持；这是原源dependent投影恢复。
源码 SourceFamily/Activation/{Stage,Admissions}.lean；direct FullSourcePacket.lean。

原 receiver 的 input/AST 是实际 actionReader Material 的 N.input/residual；原born AST是自己
selected request，不能用旧raw的liftExpr替换。scalar/pair旧库存逐literal lift进receiver，
全部paid-prefix保持双库存，同停止selected的wholepaidtrace/generatedjoint进入sameborn。
sourceWordAction是原liftMap+原语言线性transport，实际relation word进该born库存；
原SubstitutionLift.word支付完整替换方块，评价只读原receiver.registeredEnv的fst/snd。
原decoder计算oldPaid+同receipt nativeValue，精确认回born.activeEnvironment；原packetAt下一
整包认回同sourceBorn。原State/Trace/owner与价格保持，Env各按真实索引消费。
源码 Operations/Inquiry/Cofinal/Native/Installed/Cofinal/Action/{Source,Consumer}.lean；
direct ActualCofinalSourceAction.lean。

原sourceWordAction经语言与完整actual_next_packet的word等价运输到actual下一site，
DFinsupp.lsum延拓为CommonWords作用；全旧word实际入同next库存。receiver平方由两等价
逆读原registered Env，保自己的old/effect。原jointObserver与该source作用直接生成现成
allowed-action-word Model、最大future不变核、完整allword/site fibre和modelAction。
空作用词的current观察给合法nativeRestriction至原jointCompletion；model_action_native读取
实际作用后残差，不向静态Completion免费赋作用。sameordinal source_span与完整State/word/
全部betweenstop、next库存和receiver平方由actual_source_word_step直接消费。
源码 Operations/Inquiry/Cofinal/Native/Installed/Cofinal/Action/Common/{Source,Consumer}.lean；
direct ActualCommonSourceAction.lean。

原selected material的完整boundary与executable residual AST由∀Env的源语义恒等连接；
lift、语言与完整packet运输保持该关系，实际source action逐允许word/site保持其完整future fibre。
原own receipt驱动StockTarget.compiles_settled/birthProgram，原完整nextpacket认回其canonical current。
同一MaterialAt运输到该current，保Env/AST/full State与Trace/owner；writable request直接从该材料
生成，现成Model身份实际作用于此request.expression，不从quotient选Raw。原whole firstDestination
和ledgerEvolution.destination直接给旧责任与born责任行；全部future joint observer与Sort-valued
dependent consumer消费同一request、原compiler和整账。此为同根表示与原consumer实接。
源码 Action/Common/RootConsumer/{Semantics,Source,Consumer}.lean；direct ActualRootResidualConsumer.lean。

原Factory.datum可在emitter前安装同源calculationReader：一枚sourceCode经原liftExpr递归
生成各grade codeAt，Raw.Env直接取同occurrence的原reader；旧reader、decoder与四个完整库存
callback保持。实际actionReader经原Installation生成value/完整Trace，原writeback给oldPaid+
nativeValue的updated-total；每层collapse只合并外部old/effect。原packetAt_successor、nativeAfterAdmission
和bornAfterNative给每个actual共尾nextpacket的code与真实执行值。default reader的外Env总值
认回原cursor三次实际更新。RH原P.code在该真实sourceinput执行，完整pair满足p+r=R(actualInput)，
allactualcofinal与原whole/current直接消费；actualInput与旧physical projected必须另付同源Env方程。
源码 SourceFamily/Calculation/Factory/{Source,Consumer}.lean与ClozelOriginalKCalculationFactory.lean；
direct SourceCalculationFactory.lean。

原Installation.residualAt与supplied exact occurrence给N.input.Env，消dependent update后
精确认回同frame.activeEnvironment；withActualInput在emitter前只更新calculationReader，
原reader/decoder/四库存callback保留。递归codeAt在每个actual共尾packet自产完整Raw/AST与
真实Step/Trace/value。原SS.nextCfg保旧decoder：第一born仍承接其原source receipt，fresh数学
作用必须由下一枚自己的receipt/SS.born写入。RH原firstBorn的完整(p₂,r₂)给R p₂，原第二
receipt的updated-total/born_environment写回(p₃,r₃)，原whole-next与121root_future同次消费。
源码 SourceFamily/Calculation/ActualInput/{Source,Consumer}.lean与ClozelOriginalKActualInputCalculation.lean；
direct Verification/framework/source-policy/SourceActualInputCalculation.lean。

完整residual source由原sourceCode经liftExpr/subst与实际regroup节点生成：generic输出
sourceCode.eval physicalInput与sourceCode.effect physicalInput residualInput，合值来自eval_update。
原P.code的真实var/linear结构给RH residual分支R r；physical与residual的完整Pa/rem split
在同actual Env执行，完整Trace按新AST费用4，旧r未置零或装入Pa。原Q.sourceBorn供(p₂,r₂)，
原同源receipt/decoder实际写回四值并接whole-next/cofinal/rootfuture。总R(p+r)从实际双分支
之和生成；原物理Rp分支保持自己的源身份与价格。
源码 SourceFamily/Calculation/FullResidual/{Source,Consumer}.lean与ClozelOriginalKFullResidualAction.lean；
direct Verification/framework/source-policy/SourceFullResidualAction.lean。

原AS.nativeAfterAdmission/nextBase的sourceMaterial与own native receipt给bornAfterNative实际Env；
真实AS.write与SS.write同restriction逐值消费updated-total，完整Frame/库存不强同。
stock_action_reader消stock/base cfg作用，真实decoder Some给同frame E.At，原born firstpaid
通过next_after_born/mathNext保持当前Env。packetAt_successor认回整next packet；原grade+HEq
经plain collapse消新增old/effect外层，保基底p/r。完整joint source因此给next_pair/raw_successor，
原R迭代由实际方程归纳，原Model.action/recover、完整history与root_future直接消费。
RH raw0是实际首cofinal packet完整总量，原更早Xi source身份须按其自己的source链认回。
源码 SourceFamily/Calculation/FullResidual/Dynamics/{Source,Consumer}.lean与ClozelOriginalKFullSourceDynamics.lean；
direct Verification/framework/source-policy/SourceFullSourceDynamics.lean。

原first完整source直接用P.initial/F.configuration的actual actionReader；Frame.depth0事件
已在initialEvent之后，原Native.budget与remainder生成当前真实paid，updatedEnv=v。
自己的原SS receipt/decoder/born写入完整split R(v)=(p₁,r₁)，完整旧库存/Trace3与whole-next
保持，旧scalar born不替换。actual BasePair born/seed在emitter前进入现成joint factory。
原D.packetAt0 literal初packet与AS own首receipt自产first collapsed value与真实grade；
第一joint raw₀=R(Rv)，actual cofinal recurrence保全全部R作用。原Xi精确m emittedreceipt
认回原comb谱系与R^(m+q+2)，原K/FourierK observer、Model/allfuture/history/whole-rootfuture消费。
源码 ClozelOriginalKFirstFullSource{,Dynamics}.lean与FullResidual/Dynamics/Initial.lean；
direct Verification/framework/source-policy/SourceFirstFullSource.lean。

不同actual source以真实Env增量运输：normalized零阶rawψ来自原CompletionSource的
EvenAdditive realization，原comb receipt保存旧Env/AST/State-owner。δEnv=ψEnv−oldEnv在
emitter前进入literal lift原R^m AST，原executor生成(v_comb,Expr.effect)及自身Trace m+1。
原SS ownreceipt/decoder/born写全old/effect、whole-next与全部旧库存；total由eval_update
生成R^mψ。原一步completion/directR intertwiner归纳认回既有DivisionAdditiveState_m，再消
已支付raw/physical identity，原DirectConsumer给实际Fourierexpected/read≠0/evaluator≠0及
finitepart。未从completed physicalstate或非零结果作source输入，原comb/B₀/history与各单位保持。
源码 Runtime/Feedback/ClozelOriginalKNormalizedSource{Update,Consumer}.lean；direct SourceNormalizedInputUpdate.lean。

实际query/action统一读取完整source Raw：Receipt/Inventory/ActualQuery由原completeMaterial、
同次actionReader的整Raw及其actual Result/Trace生成commonMaterial。原stockLaw的
Projection/Active/Inactive/classify不变；旧完整outcome经inheritedCoface独立坐标保持，
common坐标由componentCoface安装。新query/result/action读取common Raw restriction，
resultFace.rootRead保存整ResultAt，其实际值/Trace由原executor生成；旧migratedTrace、
completeWritten、库存callback及decoder保持。RH ClozelOriginalKActualQuery直接从该
result值生成物理total/原DirectConsumer/finitepart，自己的receipt/born/whole-next消费新cfg。
源码 Receipt/Inventory/ActualQuery/{Source,Consumer}.lean；direct SourceActualQueryMaterial.lean。

canonical下一发生的完整Raw投影保其自己的Env：ActualQuery/Next从原targetRoot在实际
 targetVisit的oldProjection(commonInstalled)读取完整payload。原registered residual AST、
owner与born activeEnv分别保持。Intake.Lower在同一parent emitter前安装next programme，
实际admitted target/current/whole认回该receiver；admittedCommon在这个真实next发生取
同源Raw，新query/action按Raw自己的Env执行literal lift，外层0保完整旧inner effect。
其own ResultAt/Trace及第二receipt/born保存完整四值并消费原physical/Fourier/finitepart。
原m AST换成decoded bornEnv会生成m+m阶；两Env控制拒绝把此重执行冒充原m阶。
源码 Receipt/Inventory/ActualQuery/Next/{Source,Consumer}.lean、RH ClozelOriginalKNextCompleteQuery.lean；direct SourceNextCompleteQuery.lean。

实际born更新保Raw.Env与decoder.Env各自身份：ActualQuery/Next/EnvironmentUpdate从原
actionReader的fullRaw与own SS.born.activeEnvironment生成δ=bornEnv−Raw.Env。原liftExpr
在pairEnvironment执行完整old/effect；source_env_update、effect_actual与source_sum_actual
直接给实际新Env方程，own query/receipt/decoder写全部结果、旧库存及whole-next。
各PairValue层沿原PUnit sort与原群实例消费，普通源数学先认回后再消dependent结果。

Next/Linear从canonical实际next common投影读取同一完整Raw，在原Intake的父emitter前
安装一枚linear action节点，AST费用加1。RH splitRecord将完整八值作为第一坐标保留，
第二坐标记录其total的原p与原orthogonal r；不额外迭代R。自己的grade2 receipt写完整
十六值与whole-next，同次FourFace的inverse/differential/relation及complete-word仍消费
该actual AST。原m AST对bornEnv的total是ambient Division_(m+m)，Xi exact order仍m；
原physical closure k≤m不扩张。独立completed-Mellin read保physical p读出与ambient r
读出之和，残差原样写回。源码 ClozelOriginalKSourceEnvironmentEffect.lean、
ClozelOriginalKCompleteSourcePhysicalSplit/{Source,Consumer}.lean；direct SourceActualEnvironmentFullSplit.lean。

原SourceFamily的actual增量在原W的下一grade安装：EnvironmentUpdate从同一parent
fullRaw及其own bornEnv生成liftExpr旧值/真实effect，仅更新原Factory.datum的n+1条目；
入站sourceCfg、receiver、完整nextSeed和所有库存callbacks保持。AS.template/nextBase/nextCfg
与source-owned新programme认回，StockAdmission在parent emitter前实际安装。当前native
receipt仍消费自身已注册residual；自己的完整born packet读取新Raw，其下一admission
才生成新registered input/AST。两次发生保持原owner、grade和完整seed，裸zero seed
不能代替原完整谱系。原actualpacket0/actual_next_packet确认同initial/cfg的实际共尾链，
RootConsumer.actual_root_eliminate直接消费该request、Model、任意history/site future、
compiler与whole；不把calculationRaw认作当前writable residual。源码
SourceFamily/Calculation/ActualInput/EnvironmentUpdate/{Source,Consumer}.lean；direct SourceFamilyActualDatumPacketFuture.lean。

逐current读取完整源材料：原Installation.materialAt已含raw/nextRaw、paid State/owner、
oldTrace/pairTrace及全部relations。Mother.reader的relationMap表达式保其原关系语义；
CurrentMaterial在原Factory每grade的datum中直接读取同occurrence的raw AST与真实increment，
消费原pairTrace，既有ActualQuery.programme将完整Raw/Result与旧stock/coface同次安装。
AS.nextBase认回仅带原WB decoder的nativeLowProgramme经Q.programme，common coface
遂真实继承到actual AS.nextCfg；默认库存query与complete action保持各自读口。

原selected的own receipt生成frame/occurrence与整份NativeMaterial，源字段不以该
consumer bundle为输入。paired AST=lift原paid.raw，settled动作由同State generate及
own receipt给出，paired Env=pair(paid.environment,paid.increment)。原RootConsumer的
paid材料因而与source/effect同一；原writable request/current/Model、任意future words/sites、
compiler和whole直接消费该发生。消去收整份实际材料，不铺重复concretepacket包装；
Raw/result/Trace及完整谱系不丢。源码 CurrentMaterial/{Source,Consumer}.lean；direct ActualCurrentMaterialSource.lean。

原下一writable request读取前ordinal paid residual：born registered AST/Env先认回N.expression/N.input，再经actual_next_packet的语言/grade依赖投影交canonical rootedRequest。自身paid Trace与更新律产生request.eval=同source pairedResult.effect；不能对当前request再做一次raw差分。

原born已走第一步，Clock remainder_generated与原residual AST syntax费生成剩余credit；born.action的Type分支消费实际state，由原Pay.payment生成同债payment，strictDebit与sameDebt unique直接来自原debtStep。payment的原root与丰富query coface root各保authority，同ledger/temporalVisit及whole evolution/destination用既有HEq依赖消元接回原current row。BornWholeWrite保整份原receipt/owner/authority，canonical实际nextpacket把born的原丰富query current认回RC.generatedCurrent，并由原RC.consume直接消Model、任意future观察、compiler与whole。numerical effect为零不抹除真实syntax支付；AST完成与world faithfulTerminal各保原口。源码 CurrentMaterial/RootedEffect/{Source,Consumer}.lean；direct CanonicalRootedRequestEffectPayment.lean。


原completed source直接消费已有Clock.suffixHistory.target，与CompletedEvent/state/current精确认回；endpoint深度从原AST费用和实际prefix/suffix生成。原Trace更新律及rootedMaterial State.sound把完成值认回同previouspaid effect。actualaction自产settled后交既有StockTarget.compiles_settled，消费同root/visit/exactTemporalCausalEvent产生的debtAdmission、targetAnswerAndNext.answer/receipt、whole旧/born destination与canonicalnext；直接用既有generatedAction，不再造carrier。原source AST完成时same-debt target仍非空，按原law输运；本口生成source disposition与actual answer，不把该源事实升成whole faithfulTerminal或U8。
源码 CurrentMaterial/RootedEffect/Completion/{Source,Consumer}.lean；direct CompletedSourceDisposition.lean。

实际receiver的common source只在其原epoch内读取：originalOccurrence→原Q.common payload保completeMaterial/native action Raw/原EnvAST-indexedResult及Trace；registered residual Raw不替代native action。原datum lookup先消整份dependent SourceDatum equality再读reader，保持registered/occurrence；同完整frame仅depth变化仍命中，其他frame原datum保留。literal liftExpr+原linear action在Intake实际安装，ownselected receipt直接消费。

后继actual occurrence Env不能冻结为初值；原Expr.eval_update生成完整actualupdatedSource=initialResult+同actualMaterial.effect，保原source群实例，ownwrite使用实际updatedSource。完整common/nativeTrace/newmaterialTrace、更新方程、whole/next/inventory与initial原Mellin p+r直接同口消费。合同限原receiver注册epoch；source effect与更新量保原群实例，初值物理身份不转给任意后继值。
源码 Next/Linear/Receiver/{Source,Consumer}.lean、ClozelOriginalKReceiverSourcePhysicalSplit.lean；direct ReceiverSourceLinearAction.lean。

同actualMaterial的literal .linear action AST对任意真实eval Env与实际increment都执行原hom，updatedSource与effect的图像资格由源语法产生。原splitRecord保完整first8并用其total生成p/r，projection subtype直接给p会员，r原样保留；普通Joined无该资格。same material read-update先保source群，再固定ordinary carrier读取total，Installation.source_value认回原initial actionResult。更新Mellin读actual新total与sameeffect，only initialtotal认原Division_(m+m)；ownwritten的实际born Env point直接读取该newtotal，并与原Trace/whole/next/inventory同口消费。
源码 Next/Linear/Receiver/Action.lean、ClozelOriginalKUpdatedSourceMellin.lean；direct UpdatedSourceMellin.lean。

原actual cofinal R源的raw_xi_source识别整份packet场为R^(m+n+2)(comb0)，原Division gap及收缩dilation/Bochner闭积分生成每n positionGap。ambient pricing提取原R作用实际所需gap，原scalarKernel由原积分计算产生；完整r保留，k>m的gap不提升全physical闭包。原next_pair/raw_successor把n→n+1作用交完整p+r独立读数，并与原source history/runtimewhole/root_future同口消费；receiver Raw/Env发生维持自己的authority。
源码 ClozelOriginalKAmbientPricing.lean、ClozelOriginalKCofinalRAction/{Source,Consumer}.lean；direct CofinalOriginalRAction.lean。

原L2 Bochner作用通过原projection内积生成整个无限Pa closed-range normal equation，Pa observer资格只限定读口，source不输入Pa成员/forcing零/strongTranspose L1或xL2。sameactualcofinal R/raw/Env/code直接实例该核；原Boundary生成StrongR作用与真实QP T/QP F T forcing两速度，完整Observed actionDefect/joint fibre消费同action。原physical p拆Pahead+PaOrth，common-gap全r保留，原packet/history/whole/rootfuture与独立normal/forcingconsumer一口消元。同D实际source与原firstResponse Bh各保发生身份，wholeclosedPa normal unique识别口与source constructor分开。
ClozelOriginalKPaSourceKernel.lean、ClozelOriginalKCofinalPaAction/{Source,Consumer}.lean；direct CofinalOriginalPaAction.lean。


原 complete seed/initial/factory 中，literal pairedRSource 由原 R 及其 Fourier sibling 执行 comb0，自己的 source receipt 与 decoder 写入 B/0。withActualInput 在 parent emitter 前安装 B_h literal action；原 own born 环境给输入 B，下一枚自己的 receipt 执行并生成 sourceNext。原 B 的 Integrable、firstMoment 和 mean 由源取得，两方向 dilation 的 SamplingKernel/MobiusSource 与 gapCoefficient 给整个 closedPa normal kernel，完整 correction 为 B_h(QB)−Q(B_hB)。kernel 读取此 own Bh 初值；任意后继 actualMaterial.increment 继续由 eval_update 写完整实际值/effect。两次 whole/next、完整 seed/callback/库存与 Model/rootfuture 同口消费。PaHead 的 strong 域不由 B 的源域免费继承，D 的原 R-successor 与此 Bh-source 各保发生身份。
源码 ClozelOriginalKPairedSourceKernel.lean、ClozelOriginalKPairedSourceAction/{Source,Consumer}.lean；direct PairedOriginalSourceKernel.lean。


同原 cofinal D packet 的 T_(n+1)=R T_n 直接消费原 arbitrary-L2 signed boundary 与 strong orbit：U_hT_(n+1)−χ_hT_(n+1)=χ_hBoundary(T_n,h)，实际导数−(ρ/2−1/4)T_(n+1)=完整T_n。此 sourceRecover 沿原作用反向恢复任意有限 steps，保每个 p+r 及Pahead+PaOrth+r；candidate/前件唯一性为独立识别口。D.raw_n 来自 packetAt(n+1)，实际宏 tick 按原 Admissions.index(n+1)认回；RC.actual_root_eliminate 在 source ordinal n+1 的原 compiler/whole 下直接消费方程，并保 canonical next packet(n+2)的完整 material Env/AST/State/owner 与原future。强域由原R作用自产，deriv在此实际源上消费，不报全局连续逆/物理范数或齐次forcing。
源码 ClozelOriginalKCofinalStrongAction/{Source,Consumer}.lean；direct CofinalOriginalStrongAction.lean。


原 R 的 strong source law/reflection 自产 ker R=⊥，已有 LinearMap.leftInverse 生成纯代数 inverse。literal inversePair 对完整 p+r 执行 inverse 再按原 physical/orthogonal 投影分裂，两 old/effect 分支分别执行；不把此代数逆当 CLM。原 D 的真实 parent admission 交 inverseFactory；AS.nativeAfterAdmission/bornAfterNative 给 actual incoming programme，生成 HasActualInput 后自身 action receipt 才消费 inverse AST。parent registered residual 的原 native payment/born Env 继续由 FullSourceDynamics.updated_total/actual_writeback 生成；inverse 数学 receipt与此前该 paid receipt 各保发生身份。真实 updated Env/effect 与下一 ownwrite、whole旧/born行、canonicalnext直接消费；初始 Rrange 的逆读由同actual源来认，后继 delta 按 Lδ 忠实保存。


原R residual通过实际parent HasActualInput认回literal R raw；oldPaid const/真实effect语法自产R(实际增量)。native receiver AST/input及CurrentMaterial完整Raw restriction保同receipt，L在parent emitter前安装后恢复总量；其完整pair按自己的AST/fibre保留。原R raw语法费自产current/mathNext正余额，两paid phase环境投影生成真实updated=initial的本次源事实，nativewrite同值由此证明。bare Q programme的query/action reader一致；actual stock query由库存生成，不假认它等同calcReader。own数学Trace经Configured.lowWritten、Lower.Stock.scalar、AS.scalar及paid-prefix库存保全进入actual bornStock，boundary进relationClosure；同born sourceWord old/effect square及bornBinding substitution直接消费。Pay只收nativePacket.base，内部stock一次，完整Frame Eq将实际born写回与同债支付/whole/next绑定；不宣称第三born会员。
源码 ClozelOriginalRResidualInverse/{Kernel,Source,Qualification,Residual,Action,Consumer,Words,Updated}.lean；direct OriginalRResidualInverse.lean。


原D parent的R payment给actual incoming完整值；在emitter前安装的两方向四项AST按wholePa source correction、原unit character、actual signedUnitSource/Response差及PaOrth+r的原R作用执行old/effect。原unit radius realization适用于负向radius>4，signed source差保全而不借空Ioc/Pa资格清零；bare all-h Bochner/Volterra律只直接消费。sameactualmaterial增量由dependent HasActualInput认literal raw，生成U±h Rδ，再nativewrite到同born；完整mathTrace/boundary与sourceWord old/effect square进真实born库存，整Frame identity绑定内部stock一次的同债payment/whole/next。原Riesz K与ordinary FourierK读四项；Physical all-h Laplace是独立数学consumer，原D future不认成newfactory future。
源码 ClozelOriginalKCofinalTwoDirection/{Kernel,Source,Readback,Effect,Writeback,Physical,Inventory,Payment,Consumer}.lean；direct CofinalOriginalTwoDirection.lean。


原installed right-half K的finite action/forcing由源生成；dilation unitarity与Fourier sibling给固定K/FourierK的有限Ward读，不把原R强域转给K。pre-emitter联合literal R Ward AST与primitive-owned K-self profile/FourierProfile/A/beta源程序，原K receipt和R material保持不同occurrences。own native oldPaid+nativeValue保actualinput+真实increment；减该同material生成的R Ward(input+delta)，actualSelfRead恢复primitive-owned自源量。原installed fixedResidual直接读这份反馈，K/FourierK各带自己的norm²单位价，不归一成1或由向量0免费推标量0。完整Raw/effect/write/bornEnv/mathTrace/边界/word库存及sameborn Frame/payment/whole/next直接消费；原Psi edge与真实residual保持。
源码 ClozelOriginalKFiniteWard/{Kernel,SelfSource,Source,Feedback,Residual,Inventory,Payment,Consumer}.lean；direct OriginalKFiniteWard.lean。


原installed K finite forcing经自己的primitive源阶段实际birth，完整F±字段构成W_h=F_h+(χ(starρ,h)−1)K=U_hK−K。existing Expr.bilinear对变量执行原Gram及unit Gram；源能量E_h=⟨W_h,W_h⟩，unitarity生成0≤E_h≤4G与两方向/Fourier读数，源evaluator自产(pairedχ−1)G+½E_h。actual increment带入bilinear左、右、joint三项，after square和更新预算保完整δ；初始4G不免费转给任意after场。native实际written energy/unit字段减同receipt字面三项effect后，原fixedResidual按两个各自norm²价格读取Ward。forcing与Gram两个实际receipts各保完整Trace/boundary/sourceWord库存、sameborn Frame/同债payment/whole/next；同一sourceBorn语言restriction只消费既有native_packet_actual/born_transport，不把同值不同packet认作同发生。
源码 ClozelOriginalKFiniteWardGram/{Kernel,Bilinear,Bindings,Force,Source,Readback,Budget,Physical,Effect,Dynamics,Writeback,Ward,Inventory,Payment,Consumer}.lean；direct OriginalKFiniteWardGram.lean。

原K完整columns/两mean/defect合成与原R真实更新在同current交叉作用，完整η/contact源Ward RHS经实际AST/effect/write、cochain/word库存和sameborn whole-next消费。稳定carrier/源律/单位/独立读口详见[原K—R源cochain](original-k-r-source-cochain.md)。
