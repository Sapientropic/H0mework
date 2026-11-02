# 原残尾恢复的实际计量与支出

单轮入口为 `Native.Future.Recovery.Metering.produce receipt tariffPosition`；
多轮入口为原 `Native.Future.Recovery.produceWorkload tariffPosition receipt`，沿原 `Walk` 执行。
`receipt` 是原旧词运输的真实 Receipt；费用动作从该实际 source 的 `actions[tariffPosition]?` 取得。
索引只配置价格身份，不提供付款、恢复成功或目标评估证书。

## 两次预留与实际后继

运行时检查费用由原残头本人签名、同意者均为本人，是本人非负且含正量的外部物料支出，
并排除原 scope 的 `TaskUse`。非费用动作或越界索引产生 `unpriced`，不改用另一费用。

先把一单位目录构造／计量费用交给原 `Mandate.Replay.compile` 并在同一 source 实际执行。
成功后才从收费后的真实 current 生成 `Search.repairs`。目录结构自产比较预留量，
再次实际支出成功后，`Ranked` 才计算并缓存各候选评分，随后比较缓存值。
所有候选在第二次支出后的同一 current 评估；选中准备合法，且对这个目录最大化原位置消费。
选中准备与原残尾的实际输出追加到同一 `Machine.Continuation`，并生成自己的实际后继。

`comparisonUnits` 为一单位、目录项数、baseline 原残尾长度与每项
`3 × preparation.length + residual.length` 之和。
`every_evaluated_request_visit_is_reserved` 证明 baseline、全部候选的 `requestVisits` 及选择比较数严格小于该预留。
这里的计量单位是声明的请求解释器检查；目录构造按一项登记服务计价，不是通用 CPU 时间定理。

## 失败与完整原账

构造或比较账单拒绝时，真实合法费用前缀与首拒绝都保留，原任务的 consumed／residual 不变。
`a_refused_invoice_has_its_exact_actual_financial_or_permission_obstruction` 给出同一实际 item 的失败。
支付费用不能成为原任务位置的履责信用。恢复执行只追加实际消费的原位置，完整原词分割始终保持。

`Prefix` 保存较早实际事件和 current，生成完整金融账户／出生／档案的 `Coupling.Match`。
它不要求账单前后的账户相等。`Output` 将同一次结果及完整 native 清单装到自己的根；
读回、whole-ledger writeback 和 own next 都由同一 `active.tick` 消费。

`reportFrom` 直接对该实际 source 调用原 `Window.evaluate`，保留费用、原损失和恢复成本坐标。
在 `start ≤ begin.depth` 下，窗口到达实际恢复后继并包含期间全部费用／恢复 ordinal。
## 原消费者的多轮执行

`Metering.Stage` 从同一 cursor 生成 `result = run` 及缓存 `endpoint = result.finish`。
`executeWorkload` 在空残尾直接 finished；否则读取同一 endpoint 判断进展。
严格缩短原残尾才进入下一轮，各轮重新从自己的实际 current 付款和搜索。
评分终点由 Stage 保存，进展判断和最终根读回不会重复评分。
`run` 和 `Result.finish` 各构造一次目录；这不提供目录构造或 CPU 总量的计数证书。

`workloadStopped` 的最终输出是 `endpoint.attempt`：无报价、拒付或付费搜索无进展，
都保真实账单前缀后实际尝试原残尾，不赋予计量服务否决旧工作的权力。
`Funding.ofWalk` 提取同一 Stage 的 typed 失败，原 source、登记位置及拒绝证明保留。
`WorkloadMetered` 由原 producer 递归生成，每个释放搜索对应自己的两个先行实付。

原 `Recovery.Output` 的 Pricing 区分 unpriced、batch 和 workload；batch 含显式空词。
同一个原 recovery face 消费 Metered、Closed、原词分割、完整 native disposition、
whole-ledger writeback 和自己的 next；`Evaluation／Assessment` 从同一最终 source 读整窗费用。
原完整 Tensor、Selection、Prefix.Global 与 selected execute 已消费同一 Pricing.execute；选前完整报告／Funding 与选后原根输出精确认同，详见[统一报价、资金阻塞与全责任选择](public-function-owned-learning.md#统一报价资金阻塞与全责任选择)。Task 已以源绑定槽位贯通原公开出生与完整选择，详见上述机制卡；外层原完整规划已由上述机制卡的源生账单与实际预付合流；跨替代全部未来能力由[唯一 active route](../../../handoffs/process-generated-society-active-route.md)维护。

## 同一计量核心消费实际History

`Search.Billing`保存原`Ranked／choose／comparisonUnits`及访次预留证明。原`Native.Future.Recovery.Metering`直接使用该核心，保原源槽索引报价及实际Machine continuation；新`Handoff.World.Input.Recovery.Metering`从完整Inventory的实际current／新scope／actionsAt构造上下文，也直接使用该核心。

History费目录由原source动作与实际登记目录共同生成。`Tariff.declaration actor bundle`是精确同词的`[marker actor, fee actor bundle]`，marker明确本人声明；两项必须在原输入ordinal的真实先后cut获准，fee满足本人／非TaskUse／非负正额external use。私有`Entry`保原`actualExecution`、输入位置、实际submitted及before；`Entry.extend`证明任意后续真实输入或账单仍保原身份和接受cut。

`Tariff.directory`保primitive菜单来源或实际Entry，`Metering.Fee.registered`直接消费该origin；完整费用投影认回同一个source目录。`feeContext`只扩大费用目录，`catalogue`继续使用原planner的`cursor.model.actions`。普通外部消费不算登记，分开输入的marker与费用、错人marker、零额及实际拒付不生成报价；没有登记时保原准确unpriced。

登记本身由原World.submit真实消耗一单位费用；`Tariff.evolution／financialRun`与原计量Runtime接续到同一个响应根。`registration_does_not_grant_a_seat_or_clear_a_claim`证明登记保technology及claims。费用目录、评分或Released不生成authority或责任结清。

`Cursor.appendActual`把账单的Replay输出交给原World.submit，原consumed／residual不动，完整Inventory／Evolution／Financial.Run延长。History入口在一单位构造费先付后生成原目录的精确计数；完整比较预留实际付清后，才生成完整候选目录并在第二次付款后的同一current缓存评分，再由原Replay／World.submit执行准备及原残词。`Stage`保同一次生成结果与缓存endpoint，未释放分支不记原请求完成。

`Metering.Runtime`将Stage装在该实际收费后库存的原Event响应根，完整原责任、金融、whole-ledger及own next由同一根消费。`Metering.Projection`是可计算观察，逐分支证明与原Runtime.read同一次结果精确认同；不提供authority或native见证。实际新scope消费者支付登记1、构造1、比较4单位后修复原review，保新旧principal；比较中途拒付保实际前缀及全部原拒绝。同窗Report与typed Funding由下述接口生成；原GlobalPolicy的全报告族接线及跨替代全部未来能力由唯一active维护。

## 原History目录的精确计数与逐次invoice

`Search.Counting`从原menu大小、actionLimit及实际生产limit计算目录项数与总动作长度。bounded words以`(r,s) ↦ (1+m*r,m*(r+s))`递推，生产前缀按原range逐长度合并；列表重复项保留原位置。无需授权时取原repairs计数，需要授权时计入每个真实preparation前后的原三种授权词，得到`(7*r,7*s+12*r)`。`catalogueSize_is_original`精确认回原完整catalogue，`comparisonUnits_is_original`给出与原Billing同一Nat值；计数不替代候选执行或评分。

`Replay.Repeated.generate`以原count为索引逐次执行同一request，在每个实际cut调用原rebase／Valid／step，首拒绝即返回。output、consumed和succeeded分别等于原`Replay.compile (List.replicate count request)`，未访问suffix不分配为列表。原invoice单位与request保持；首拒绝仍带原raw item、实际index与非法性证明。

History的`Metering.attempt／units`及可计算Projection直接消费这两个源。`units_is_original`保原比较费，`run_is_the_actual_billed_stage`保同次实际结果；费用未付清时不生成完整修复目录，实际已付前缀仍写回同一World。付款本身继续保原任务consumed／residual，完整Event.Evolution与Financial.Run沿原Stage续接。原generic Native入口仍按前节原算法消费Billing；当前实现接线范围是History入口。

## 同一原根的完整帧读回

`OutstandingSource.History.foldedFrameAt`按原ordinal更新raw与完整付款档案，实际发词只由该轮原frame和原`word`生成。`foldedFrameAt_is_the_complete_original_frame`对任意visit精确认回原`trailAt.frame`，包含原输入之后的自产后缀，不截断未来历史。

公开`currentAt`在内核中仍定义为原`ProgrammeHistory.visitAt`的root读面；私有`rootCurrentAt_codegen`用上述全帧等式把编译执行替成fold。私有原root读函数保持reducible，供既有金融证明按原接口展开，公开reader的状态不变。该读回不生成授权、结清或新资源。

`reportAt`继续直接使用原`report`、同一任意current及原ordinal，付款子式`originalPaymentsAt`定义上就是原trail的完整档案。`originalPaymentsAt_codegen`从同一全帧等式取得`computedPaymentsAt`，使原input的发词与完整报告共同消费该读回。付款子式保持可约，原Transcript、金融History与Portfolio消费者继续按原公开形状展开；不包装整枚报告。编译检查按真实调用目标识别旧trail／frame重放，不能把共享专用化名字中的trailAt或actualAt当作实际callee；必须核对调用方IR及候选引用。

未采用的独立 `ExecutionFrame` 候选中，`History.frameExecution`在同一折叠帧上计算原word，并以原law.execute／law.next生成完整ExecutionFaceAt；其类型仍由原visit的emitted occurrence索引。原actual_frame对齐before与submitted，actual_raw_next对齐root next；actualExecution_eq_frame是完整函数等式，保留interpreted与after全部数据。它不把原投影缩成发词字段，也不增加授权、结清或退出能力。

该等式须在首次生成原wordAt别名的模块编译前进入环境。仅在较晚consumer导入等式，仍可能复用上游旧编译表示；候选隔离编译刷新原Mandate.History.Runtime后，Financed.Continuing.Runtime的traceGrant会消费该等式；原literal的IR借用调用也必须随之刷新，因此这条优化没有纳入已验收的current-frame。核验应同时检查原完整ConstantInfo、真实IR callee及C函数体；等式通过本身不代表实际调用已改用读回。

`RootFrame.produce`将付款Frame与原RootVisit放在同一次ordinal递归中：原initialVisit起步，每步仅从before.frame生成advanceFrame，再构造包含原past追加的完整Current，并用同一before.visit.next运输原ReachableAt。ReachableAt是Type值历史；`next_visit_eq`以完整successor Current等式认回原next，保留整枚visit，不以proof irrelevance丢历史。`foldedRootVisitAt_is_the_original_visit`与原Continuing.Runtime的`stateAt_eq_frame`是完整对象／函数等式；原process消费新stateAt实现，原root、词与责任含义保持。安装与实际调用状态只在active中维护。

六个上层Runtime有独立的stateAt构造。它们各自的I先展开为原OutstandingSource.History.input：Closure保原fuel／inputs；Future保branchInputs；Settlement与Joint.Future保epochSource及advance／staged后的inputs；World与World.Input保epoch.source及reviewed／advance后的inputs。每个stateAtFromFrame保持自己的V和扩展root，完整函数等式只替换finite visit的生成；原process的闭包必须实际指向该口新函数。下层process的替换不自动覆盖这些独立构造，单独保留的旧stateAt导出与process所用闭包应分别核对。

`Lifecycle.Runtime.frameCurrentAt／frameWordAt`针对原无额外inputs的`bound.source`，在原`visit + 1`读取同一`frameAt`的raw与原`frameWord`。`currentAt_eq_frame／wordAt_eq_frame`由原`canonical_frame／actual_execution_word`生成完整函数等式；原`Financed.history`的两枚reader直接消费它们。这里的carrier是原source完整帧，区别于带inputs的`OutstandingSource.History`折叠。原状态、原发词及其ordinal保持，不另造历史、授权或结清。

更换编译实现会使旧专用化调用方引用失效的私有helper。装配须扫描导入闭包的两套IR条目、递归核对每个实际direct／closure callee的provider，并定向刷新所属模块；数据定义的类型、值与安全性逐项相同，自动生成的regular高度差单独登记；同类型而证明项改变的声明在原冻结库环境逐项交给内核重查，依赖仍限safe声明和标准三公理。满足这些条件才复用已付内核证据；自动证明辅助声明集合改变时，改在实际新库重放原根与实际fixture的完整依赖。实际完整消费者结果由唯一active另行签收。

## History完整实际窗与原融资判定

`Metering.Assessment.produce inventory word`只消费原`Metering.Runtime.read`的缓存Stage。Report的response是原Event的同一次生成，packet逐字段认回原计量Runtime.packet。`recovery／native`把指定实际前缀、原endpoint.native及原响应native顺序追加；不存在新Machine或新期accountAt重置。

`costs`直接消费该Evolution的原`Event.Costs.records`，保前缀登记、构造、比较、实际恢复及响应各自原发生窗。operating good、debtPayment good与elapsed保持原单位；`material_balance_in_each_original_good`验证真实库存／实收／支出守恒。`accounts／financeReceipt`直接消费同一路径的全族`Event.Funding`，逐承担者／good保selected与remainder的现金及全部原债槽净变化。`rows`为最终完整census；`originalRow`沿实际运输保任意旧新责任的原admission、历史前缀与完整native Run。

`Funding.ofResult`从原Result自产缺价、构造拒付或比较拒付，各自保残头、原报价、先付证明及具体失败raw item；finished／searched为无融资失败。`failed_funding_never_credits_an_original_request`排除费用拒付被记为原词履责。可计算Projection的状态与该typed结果精确认同，用于实际消费者。

`Funding.Order.NoWorse／check`是原Tensor已经使用的optional资金判定：已融资的旧结果不能被新拒付替换。原`Restoration.accepts`和新Report.preservesFunding直接共用此定义；两端仍保存各自source-indexed Failure。完整报告关系进一步使用下述候选依赖接口；实际History候选的选前供源及自身先付由唯一active维护。

`Assessment.Runtime`在原Metering根追加Report coface，继承全部原face，读回同一缓存、packet、whole-ledger和own next。Report不作为authority或责任结清的生成来源。

## 不同实际终态的完整Report关系

`Whole.Restoration.Family.Tensor`按候选的真实present索引各自Report与Refusal，不要求两个终态或scope相同。共享`Accepts`联合消费present关系、每个required原词的完整Report关系及原资金不退化关系。`ReportsNoWorse`是旧新接口共同的Option消去口；两个Report都实际生成才可能通过，保双方完整typed payload。

原`Whole.Restoration.Tensor.family`逐字段读取原present与原restoration；原`accepts`直接消费共享核心，仍使用原`Synthesis.accepts`、完整`Assessment.NoWorse`和同一required词族。原Selection、Prefix.Global与GlobalPolicy沿此口消费，旧关系没有降为标量或optional资金门。

`History.Assessment.Relation.Window first`保同一更早实际packet及各自`Event.Evolution first endpoint`。`Window.NoWorse`按该first的原槽及实际transport对齐terminal；每个已报告terminal须有同一native archive。两端最终census保持各自全部新生责任，每条原row保admission／history前缀／complete native Run。

经济关系逐Bool承担者、原feedstock／service分别比较operating、debtPayment、elapsed、selected／remainder融资净账及实际stock，保原单位；它是明确的逐坐标Pareto关系。`tensor seed`直接对该seed的实际Inventory读取原Runtime Stage生成完整Report和Funding；`ReportNoWorse`还比较同一原请求的剩余长度，并把原响应native拼回共同first。资金门独立消费同一原typed Funding。完整关系接受时，旧已完成原请求在新端仍完成。

共享接口及原旧消费者已独立核验；原GlobalPolicy的实际History种子供给、新核算先付与默认调用由唯一active维护。完整History关系的类型检查不替代其native整账可执行验收。

## 原候选source供词与联合准入

`Relation.Feed.source`直接使用原`Whole.controller／schedule`和同一个canonical joint opponent；`words`按原`Cut.horizon`逐visit读取该候选`actualExecution(...).submitted`。它接收原程序及实际库存，不接收Report或选中结果。`window`交给原`Event.run／runEvolution`，每条原提交词在当前真实World执行并产生该World自己的响应；两种解释的current不被等同。`Source.boundSource`复用原`Authority.Sources base epoch.scope`里的Machine，源task与World task定义性相同，库存和全部旧金融族保持独立实物来源。

联合Tensor的present同时保存原完整Tensor和实际History Window；present门合取原完整`accepts`与`Window.NoWorse`，未来门从每个World自身原Stage生成完整Report／Funding。原`required`词族沿用，已通过的原比较和History全关系分别有直接consumer。共同external table保存原canonical candidate source，继而保存提交词、World分支和整枚联合Tensor。

`Feed.Selection.candidates`在原`Selection.Restoration.candidates`上逐项filterMap：每个原row都须通过上述联合门。全部检查之后才调用原`Distributed.choose`；原axes／benefit保留，所以其最大性限定在联合准入池的原坐标。拒绝保具体原row，并由共享Family返回present／原词／融资失败。`verify／review`从原source重算关系及候选池；报告或排序不生成authority。

## 原programme基数与准确短付的等值执行

`Protocol.Continuation.Whole.Counting`按原`sequences`、policy Pi、逐key的ownMoves及rules目录生成精确基数；`programCount_exact`认回原`Whole.programs`的完整length，保位置、重复与各key不同的选项数。计数不先分配programme或policy函数目录。

原`Accounting.selectionUnits／Result／run`不变。`selectionLowerUnits = 2 + programCount`由同一目录证明不超过原`1 + selectionUnits`账单；个人费率的非负性给出`covers_smaller_units`。`runCounted`在该下界已短付时直接生成原`selectionShort`及完整账单不足的证明，其余情况回原run。`run_eq_counted`是无新增目标premise的函数等式，原Stage经csimp实际消费；fallback的IR保原run且无回指循环。

公开复跑入口`public-counted-accounting-consumer.lean`覆盖足额、短付、无价、零率、显式legacy及实际空charge；大actionLimit实例有73786888333945733115个原候选位置，由原Accounting.run直接准确拒绝。此优化不越过Source.seed，也不更改原发生、付款或generated next。

## 原Source合法性反例的一次生成

`Source.seedOnce`先调用原`Initial.Failure.generate`。存在反例时直接返回该次生成的准确拒绝；无反例时仍调用原完整`seed`，包括显式安装的verifier。`seed_eq_once`证明两函数在任意原Task及实例上相等，原GlobalPolicy经csimp消费，无新增准入premise。

`public-seed-once-consumer.lean`实际覆盖完整准入、显式原verifier、原高成本raw词的准确legal拒绝与原planner消费。原215份安全声明的type／body不变，重新编译只允许regular reducibility高度变化；新增4份声明由空环境内核重放验收。

## 原任务的World输入与已付前缀

`World.TaskInput`是按原law／scope索引的raw GADT，唯一构造载荷是实际`Inventory`。原`Task／Request.worldInput`保存该输入，`PublicTask.task／Feedback.task／RecallBirth.born`原样运输；出生可以生成另一native machine，不把原库存或两个current等同。

`TaskInput.schema`在任何候选解释前读取原inputs逐词长度、全部past/current Grant／Challenge／Service位置及原金融槽数，保存顺序计数与重复位置。`Accounting.selectionUnits`为每个已声明候选／row／控制与required词解释位置增加该输入schema预留。它是输入ingestion/schema服务，不是完整History执行总量或CPU计数。缺独立accountingRate产生`unpricedWorld`；原`Planning.Stage`只有实际Charge.paid和完整声明覆盖同时成立才释放，原任务位置不因核算付款而结清。

`Feed.Prefix`直接filterMap原`Prefix.Global.candidates`，因此使用真实paid-prefix的原残尾池与原全坐标verify。每个候选在取首项前通过完整联合History关系；保原committed_prefix，失败分别携带原验证Failure或原History row。`verify／review`从原source重算两种接受关系和逐tail拒绝。原默认invoke已由同批缓存口消费；完整接线见下节，更广未来能力由唯一active维护。

源码：`Distributed/Reaction/Native/Future/Recovery/{Source/Cursor,Source/Walk,Runtime,Evaluation,Funding,Metering,Metering/Runtime}.lean`。
独立消费者：`scripts/verification/public-workload-recovery-{consumer,kernel}.lean`；完整选择接线由 `public-recursive-metering-{consumer,kernel}.lean` 消费，Task 声明与同源实际俘获后实付由 `public-task-workload-{consumer,kernel}.lean` 消费；外层自身实付由 `public-accounting-prepayment-{consumer,kernel}.lean` 消费；单轮兼容由 `public-native-recovery-metering-consumer.lean` 保持。

## 隔离装配保留原模块包身份

原ModuleSetup.package参与本机符号命名。隔离源码严格编译须保原module name、package及import顺序；省略原SaturationMonoid包会让旧lp_符号和initializer失去provider，即使全部原ConstantInfo及C函数原型保持相同。配置由固定Lean的ModuleSetup.toJson生成并经官方--setup传入，连同源码、OLean和C绑定在自己的编译收据中；不以改名或额外authority补缺。

选定刷新DAG从实际冻结OLean的导入图与本次新增import生成；未刷新模块的工作树源码不能代替其已编译导入头。逐模块守卫覆盖全部选定依赖的OLean及private／server部分；依赖上下文不变才复用已付编译，缺失依赖边只修复受影响阶段。

C ABI检查同时覆盖生成模块、原Boot、initialize/runtime_initialize/meta_initialize与run_main；不同参数类型的六族负控必须失败。链接后的存活Lean外部符号须逐项由实际对象或固定官方库提供，清零后才能运行初始化或原consumer。实际image由原exe散列及完整`nm -aj`定义／undefined表固定：已移除IR helper若在该image完全缺席，可逐项记为未保留代码；严格`-undefined,error`保证没有存活外部调用悬空。此处不豁免borrowed／owned发生变化的callee，其实际旧caller仍须刷新；C文本中未进入image的移除helper引用不反向增加已发生consumer的执行义务。包身份更新只刷新实际缺失符号的调用owner，保留已付源码编译及原native作业；生产重编使用相同setup。

Lean在检查-R前解析源符号链接。保留原PublicDefaultActualNative模块名时，编译根内使用原源文件的逐字节副本，并在编译前后重核权威源及副本hash；不以指向根外文件的symlink作alias。安装消费者仍须来自已安装源，保原OLean完整逻辑体检查，并比较已实际执行模块的整份C字节。

## 原完成决策的直接金融续责

`Programme.Completion.Decision.financialRunDirect`直接消费同一原Decision：paid与replacementBlocked使用各自原fresh的handoffFinancialRun，reviewBlocked保原finalFinancialRun接空Run。`financialRun_eq_direct`是完整函数等式，保存实际付款事件序列及原packet的金融终点；不把净余额相等代替完整Run。原Disposition的逻辑体保持，编译口消费Direct，省去为读金融历史再生成World.generate及完整handoff。

计算等式必须在直接consumer生成IR前登记。逻辑函数类型与原证明体相同，也不保证编译ABI不变：原实现可能抹去未使用的decision参数，Direct开始读取该参数后，旧redArg或boxed符号会消失。按实际C引用重编Event与Replacement，并在初始化前核对全链接C原型及存活符号。C原型不表达借用所有权，还须对比原／新IR的borrow参数；变化签名及被移除helper的全部实际引用必须来自已刷新的owner，不以额外别名填补旧helper。

独立链接验收从具体module及编译receipt重建预期object替换映射，核对实际rsp与完整link命令，再绑定同literal源、完整main C／object和原包库。单独验过三个候选文件不能代替证明它们实际入链。

## 原执行口的同源代码生成

`Migration.Readback.cohort／origin`直接读取原`Runtime.cursorAt`及原实际history，分别由`frames_cursor`证明等于原安装frame读数。原`Repair.choose`、`Actual.decide／receive／dispatch`与`Registered.Compile.compile`沿该读回执行；私有`AttemptAt／CheckedAt`工厂和原raw输入保持。

`Micro.Readback.successor`以同一`SourceInput`的实际cursor调用原`Physical.ledgerCompiler`，索引仍是原occurrence与原`generated.wholeLedgerWriteBack`。原successor及receipt与其代码生成实现均为`rfl`等式；原`NativeService.actualReceipt`继续消费原receipt，原服务线程按实际付款携带或结清。共享History.receive方程由各自定义模块生成，局部和cross消费者共同引用同一声明。

完整World执行从原`Handoff.generateEpoch → Continuation.initial → World.initial`生成Inventory；`World.submit`把同一保存账户交给原`Family.consumeVisit`，实际推进新旧服务、Grant与Challenge。原生消费者读取全金融槽、原账矩阵及非空的新旧服务线程；费用支出保原本金和technology。完整Inventory是执行carrier，完整Report及默认服务的验收各沿其本来接口。

## 完整报告目录、共享比较与原Stage先付

`Relation.Feed.Work.jobs`从原`Selection.rows`和有界原`Whole.programs`生成完整目录；每项在自己的原`Feed.present`结果上按原`Restoration.required`逐位置调用`Assessment.Runtime.read`。重复词保留独立位置，`Entry.funding`直接读取同一Report，不重建另一报告。私有`Batch`构造口保原目录顺序与完整性。

`Work.units`等于目录内每个实际World窗一单位，加各query的报告、原联合处置、五入口服务及原词请求位置单位；报价按原world的精确table数加权求和后乘programme数量，避免先分配原tables或全笛卡尔积。`Batch.every_charged_unit_is_an_actual_execution_position`认回声明目录量，`Cell.compare_is_the_complete_original_history_relation`将共享比较精确认回原`Feed.Accepts`，保各自实际终态与原scope。五入口的内部新发射raw位置未另作逐项报价。

`TaskInput.Work`用原raw GADT消去得到同一law／scope的目录。`GlobalPolicy.World.preflight`先生成原Stage，在其原ready、源费率及实际付款上检验`1 + Accounting.selectionUnits + World.units`覆盖；成功分支才允许`consume`生成完整Batch。缺World显式沿legacy，缺价／零价／新增目录不足保原typed分支与已付费用。这些单位是声明的离散服务位置，不是CPU计数。原Report完整读口、Batch、缓存比较和默认invoke／Feedback均可原生执行；实际非空整账验收及全部未来能力由唯一active维护。

## quiet同源目录与原完整准入

`Feed.Quiet`只在原`PublicDomain.quiet`为真时，消费既有quiet controller定理：每个原external table rival与同world的silent restriction给出相同完整source、World Window及Report族。`Selection.quiet_holds`保原完整准入关系，不从语法相似或同一个rival的restriction推出任意table相等。

`Counting.tableCount／rowCount`用原Pi目录的精确乘积基数保重复位置；`Work.positions_exact／units_are_exact_directory`认回原全部jobs和声明报价。默认`Work.execute`在quiet源保存依赖Cell工厂；每个被消费的Cell仍由原`Feed.present／Runtime.read／Iteration／ScopeForecast`生成，内部共享同次Report。非quiet或显式`executeEager`沿原完整物化路径。

`Lookup.quietScan`对每个原world检查候选与reference的完整Cell关系，经`quiet_holds`提升为全部原rows；准确拒绝保由原枚举器生成的具体row。`check_iff`与`Work.Prefix.candidates_are_the_original_joint_pool`保原完整关系及原paid-prefix候选池。`QuietCheck.all_iff_original_directory`允许actual payload属性按world×programme实际检查，并证明等价原全部逻辑jobs的同一属性。

`Batch.cells`保原目录兼容展开，调用时仍会物化全部jobs；默认门使用精确`Work.units`及源索引Lookup。声明目录服务单位与实际CPU工作分开，实际整账IO由唯一active签收。

## 原完整Report与同批缓存的默认消费

`Assessment.nativeProduce`直接消费原`Metering.stage (Recovery.begin inventory word)`，两处`Runtime.Readback`经内核等式认回原Report及原Replacement工厂。原`Outcome.fold`与依赖`Execution.fold`逐原分支保完整参数并等于原recursor；programmeEvolution、financeAlong和原责任`Transport.follow`沿同一实际路径递归。完整Report的原packet、全部新旧责任、成本窗与全金融族仍来自这枚路径。

`Work.Lookup`按原生成的row位置和完整programme的可计算索引读取私有Batch目录；不要求对任意Opponent判等，也不从Prop抽取数据见证。`rowComparison_iff／check_iff`认回原完整History准入，准确拒绝仍是原`Feed.Selection.Rejection`。`Work.Prefix.candidates_are_the_original_joint_pool`将缓存筛选精确认回原paid-prefix联合候选池；失败保原verify拒绝或原History拒绝。

`GlobalPolicy.World.Selection`同时保存`batch = execute`与`outcome = compile batch`。原`GlobalPolicy.invoke`只在preflight的covered分支调用它；short保原Stage和实际缺额，legacy使用原编译器。`Service.Contract`、完整金融前缀与原根whole-ledger／own next继续消费同一结果。公开`World.select`是未门控的下级工厂，付款保证属于原invoke／run路径。

原`Feedback.WorldResult`保完整联合拒绝及其生成关系。成功候选直接执行原suffix；无候选或缺额才求值延迟的`later`，从原Stage实际finish经原Frame.advance续行，并重新调用原付费服务。`Walk.actual_source／restores／each_new_service_has_its_own_actual_payment`和原预算闭合定理覆盖该分支。单步Continuation保该typed结果；不会把History失败伪装为旧Global.Failure交给旧Repair。

## 原未来准入消费实际联合后继

`Feed.FutureNoWorse`保原`ReportNoWorse`并合取`JointNoWorse`及`ScopeNoWorse`。`jointWindowWith`将同一Report完整实际路径接到原`Iteration.Step.native`；`jointWindow`只调用该Report终点的原`Iteration.produce`。两端保各自真实scope及next，从共同原cut比较完整责任终态、物量、时间与全部金融坐标，不要求历史相同。

`ScopeForecast.generate`从每个joint endpoint的真实packet重新调用五类`Input.emit`，以原Report残差为pending，分别进入原`Requests.produce`。每个Port保存原Report、Funding、Iteration处置和native next；比较保旧完成请求仍完成，并比较接回共同原cut的完整Window与原Funding。其构造只接收真实seed和raw残差，不接收成功证书。

`Work.Entry`私有构造口同次缓存原Report、原联合处置和五个新scope Port，均带原工厂等式。每口的真实next packet再由`TaskSource.admit`生成原`Owned.Source.seed (TaskSource.task ...)`；接受保原完整准入关系，拒绝保原具体row，不接收成功cache或可行性见证。

`ScopeForecast.taskWindow`把原Requests的native接到同一Task的实际`preparation`：空inputs时真实提交自己的source词；非空时保持原cut。`NoWorse`逐口同时消费原Port关系、该完整准备Window及原Task准入不退化。由此准备时的物量、时间、原新责任和金融账也进入比较，而非止于Task准备之前。

`Cell.jointWindow／scopeForecast`只读同一缓存；比较等价定理和原Lookup／Prefix在取候选前消费，任一入口的原Task准入或准备窗退化都会拒绝原row／word。依赖类型的forecast等式先在`Cell.scopeNoWorse`命题内封装，再精确迁回原完整关系。

每个目录位置报价为一个World窗加各query的`2 + ScopeForecast.services + word.length`；`services = 20`，每口分别登记Report、原Iteration、实际Task编译及原source准入，另保原报告、联合处置与原请求位置服务。原TaskInput.Work／Stage先付门直接消费源生报价。这是精确的声明服务调用计量；内部新发射raw词长度和CPU工作不由这二十单位逐项计数。

## 新请求、失败残差与实际下一轮

`Shared.Iteration.Requests.Cursor`保存真实packet和raw待办。`produce`只生成一枚`Runtime.read saved (pending ++ incoming)`，原`Iteration.produce`消费该Report完整终点；`Result.next`保该真实后继和原Report残差。`rawOrigins`逐当前提交位置认回原拒绝，后续raw动作在残差之后。原责任身份／完整Run另由跨轮实际Evolution运输，不把新轮raw位置冒充原位置。

`receive`沿每次真实`next`递归接收全部输入，空观察保待办；`tick／after`在每轮重新读取当前packet原source发出的ownWord。active端从该Report的新epoch消费原Shared回复及自己的FutureReceipt，whole-ledger／矩阵／own next随同一原根；terminal须有原WholeTerminationReceipt。物量、现金和所有原债的窗口均由Report路径接原joint路径生成。

`Decision.fold／Openness.fold`完整保原分支载荷，`Future.Native.produce`与原Future工厂精确相等。`Progress.Native.produce`直接执行原完整Trace的结构递归；剩余步数仍由当轮原source的horizon与已执行输入生成，不接收调用者燃料或目标终点。

`Progress.Native.evolution`与`Evolution.Native.challenge`沿原Trace／Evolution结构递归，保完整旧Challenge运输。`Shared.Execution.answer／native`认回原Shared提交、Dispatch及同一次Progress响应；`Past.Native.produce`、`Iteration.Native.{joint,produce}`和`Requests.Native.evolution`分别与原完整工厂精确相等。所有代码生成替换均由这些等式释放，原terminal仍须WholeTerminationReceipt，原active根、全金融矩阵和own next保持。

原非空Report及Shared整账实际调用均已签收；跨替代全能力消费与默认非空完整目录的当前验收由唯一active维护。

## 原准入失败词进入实际修复

`Initial.Failure.Raw.inspect`按原反馈horizon扫描同一`actualExecution`，再按原law.rawItems顺序提取首拒绝。Fault保存更早完整词的位置、同词合法前缀、原失败item及剩余items；原请求不先rebase。`originalRejection`消费同一point身份，生成原Selection的legal行。

`TaskSource.Refusal.resume`只写回失败offset之前的完整词，再将完整失败词按`old pending ++ word`送入原Requests.produce；其实际Report、修复费用和joint后继连接同一次Communication.result。完整native运输原责任历史与全部金融族，原domain位置及baseline进入自产Task。pending为空时才认回原失败item的before；pending非空保原词和顺序，由收到后的实际raw执行处置。

`Result.nextCall`直接调用原GlobalPolicy消费该重建Task；该值本身不把后续费用计入此前native。原`Iteration.Current.fromRebuilt`消费同次缓存及工厂等式，保原Task、World输入、pending、law及current身份，不从裸packet重新初始化。

原`Step`缓存原GlobalPolicy输出和精确恢复结果。`Transition`在同一分支中绑定target与native：拒绝且有raw恢复时取同一`Result.nextCurrent／native`，拒绝且无恢复时保原Task并typed blocked；原Service分支保自己的`after／afterNative`。原`Run`沿该target继续调用原GlobalPolicy，累计native与finance因此包括实际修复和随后真正发生的Service、费用及责任；有限观察不作结清证明。target与native合包也避免Lean为分别匹配的endpoint展开整个Requests源。


## 实际packet自产原规划代码

`World.TaskSource`直接消费实际Inventory和raw pending。空inputs先由原World.submit提交自己的source词，非空inputs保持原样；动作语言由完整实际输入、原残差、当前ownWord、五类原Input.emit和原Tariff.actions生成，不接收Machine或成功终点。Code保原law／task，语法支持不赋予原law下的合法性。

原拒绝作为public prefix保留，第一条实际输入作为reference，其余实际输入经原Feedback.Execution overrides按顺序重放。Cursor.source认回同一Machine；完整历史为原original加全部实际inputs，native current与原World.current精确相等。控制预算由保存的tail位置与原source expiry horizon生成，不延长原law期限。

`TaskSource.Task`由这枚source生成原Owned.Task的model、domain、point、实际WorldInput及五入口futureRequests，位于原GlobalPolicy之下；`TaskSource.Planning`调用同一原planner。`Admission`自产原Source.seed并通过`passed_iff`认回完整原准入，`failure`保原准确拒绝。该分层让实际下一scope的原Task在当前候选选定前参与比较，不形成planner递归import。

原initialVerifier、Stage、Report／Funding及完整选择门保留。总报价与单位费率分别取自实际source offer；单位费率须同付款人并逐good不超过总报价。此关系允许分别登记足额总价和小单位价；总账仍须原Accounting.covers按实际工作单位核验，缺价／短款照原门拒绝。

生成Code固定两actor、两good、一信号和单事件步。完整任意策略空间保持、跨实际替代递归准入及服务后全部实际事件回灌，由唯一active维护；精确current等式不单独替代这些责任。


## 实际服务全分支回灌及新scope再入

`TaskSource.Service.controls`保存原Service的实际完整past（包括Stage构造／比较费用）及选中时原protocol suffix。`full_is_the_actual_control_installation`统一unavailable、blocked、worldShort、无候选和selected分派；安装前缀等式自产原起始cut身份，控制数自产实际终点地址。

`Writeback.words`逐位置读取该同一full source的actualExecution.submitted。`Writeback.append`在原scope law下逐词调用原World.submit，不在中间自动换scope；native单步等式与原saved cut合成完整endpoint等式，拒绝词也原样保留。完整旧责任、金融Run和全部新生事件由同一路径运输。

全部实际词落账后，原Requests.produce接收原pending与空新增词，保其同一Report残差和Iteration.next；由该实际packet重新生成Task并调用原GlobalPolicy。空输入的source preparation也显式拼入native，不只藏在规划输入中。

`TaskSource.Iteration.Step`缓存同一次原规划输出、actual target及native。Run要求step精确等于原produce，递归索引只读缓存target；避免在归纳类型索引中反复展开整个依赖Task。初始拒绝保原typed row及实际preparation；生成输出的每种Service都沿实际next重编译。计数是观察上界，不构成终局责任证明；完整策略保持与多轮IO由唯一active维护。


## 同一实际cut的保法代码扩展

`Distributed.Reaction.Feedback.Extension.code`只追加有限动作／历史／事件目录并放宽其上界，保原law、task、站点／信号、本地读数、记忆转移和真实通信费用。全部旧生成policy、合法history、script及scenario仍由原枚举器生成。packet／frame／state的显式运输保完整字段；对任意旧policy、历史自适应opponent和任意有限cut，原`Feedback.advance／run`与运输交换，旧mailbox、待递送地址及绝对时间戳不经`Code.start`重置。

`resume`逐cut读取原机器的`feedbackPolicy`，包括已安装override。`Extension.produce`从机器自身恢复installed input；无feedback或非空explicit continuation生成各自准确typed阻塞。私有`Active`给出替代state、同次实际请求和target自己的law.next，并与原source的actual current、完整history、Runtime原责任、whole-ledger及own next认同。这是同一实际source的保法解释，不从语法扩展生成新授权。

真实`NetworkRenewalSource`以付费发送／递送后的非均匀mailbox为起点，跨两次不同Code继续原策略；原付款、费用、缺递送未结债和未付费无packet均由原解释器实际执行。跨新scope的授权法、原TaskSource安装与完整准入关系由唯一active维护。

## 跨法通信事件的实际重放

`Feedback.Reconstruction.transcript`读取旧Machine实际首响应的emissionEvents，再逐原feedback cut保存同一`feedbackPolicy`与`decision`；显式none及空观察保留各自位置。新Code只替换law、initial、bootstrap与task，继承原站点、信号、传感、记忆转移和通信费用。重放从新实际cut与空frame开始，经原`Feedback.advance／Code.step`生成新的packet、mailbox、word和时间戳，不搬运旧合法性标志或旧frame。

首响应内部事件成为各自新的cut，故这是新法下的实际重试，历史无需相同。`failure?`保新解释器实际拒绝的rawItem、缺失packet地址、未就绪站点或耗尽预算；`Run`保每步原观察等式，失败后的后续命令仍按序执行。其current等于全部新词的原law fold，完整history和每个cut均可读回。

`World.TaskSource.Communication.produce`从实际Inventory固定新law、current和task，预算来自原命令数与旧实际反馈余量；同一Run生成的每个词经原`Writeback.append／World.submit`落账。重建state.current精确认回同一实际World终点，全部原责任行沿该native路径续责；原`Requests.produce`接收该实际packet与pending，生成自己的响应及next。

`Service.reconstructCommunication`只从同一次`made.full`与自己的`next.saved`获取旧cursor及新scope。抽象packet的两投影经`appendAt`消元后合流原Evolution，避免为Sigma索引的表示等式展开整条Requests产生式。


## 新法实际通信进入原Machine与Task

`Communication.Source`把同一transcript交给原`Feedback.Execution.target`，每个cut实际安装自己的optional policy与move。新Code保原本地架构及动作／事件语言，首响应为空；Machine初始化的两次空词显式经World.submit落账，随后原actualExecution的全部反馈词逐词回灌。Cursor不含外给frame：当前mailbox、packet、合法性和本地记忆均由该Machine自行执行。其actual current与同一World终点精确相等；`failureAt`分类该真实cut的拒绝。完成重放后的调度余量是旧实际余量与新epoch原Expiry.horizon的最大值，调度余量不赋予动作合法性。

`Communication.task`使用这枚Cursor作为原Owned.Task的实际point。其domain为`(actual :: prior.domain).map Source.cursor`：每个旧位置由自己的实际emitter重建，顺序和重复均保留，实际点不必原先在domain中。新horizon不小于整个旧domain的horizon，因而完整旧baseline不被截断。原Rule的work与owned events、报价、费率、本地读者和编码保持；WorldInput来自实际point的同一次写回，futureRequests保原raw请求并追加该终点自产的五口。原Owned.Source.seed和GlobalPolicy.produce直接消费该Task，准入仍由完整原关系决定，不接收成功证书。

`Writeback.Prefix`、`Communication.Core`与`Communication.Task.Core`分别拥有原raw写回、跨法重试及整域Task工厂；planner再入保留在高层，低层Task工厂不依赖GlobalPolicy。`Service.reconstructedTask／reconstructedTaskNative／reenterReconstructed`由同一Service.full及自己的next.saved生成上述Task，并合流原native路径。

`Feed.continuation`从每个原候选的同一row、外部表及programme取得真实source、takeover input、全部feedback overrides和post-cut；不是统一规划起点。`continuedForecast`调用该候选实际World上的原五入口工厂，各口自己的next.saved和pending再进入整域Task及原Source.seed。`continuedWindow`把同一五口native接到自己的新法实际重建路径，包含初始化、全部重试费用、全责任和自己的World；不要求旧法raw终点与跨scope的实际World相等。默认完整重建门见下节；全部未来能力的当前责任由唯一active维护。


## 默认选前的完整重建与原能力目录

`Communication.Capability.catalogue prior`是原Code、整个旧domain horizon上的完整`Whole.programs`。每个原programme的全部controls经同一个真实`Communication.rule`重编码，不截尾；其`Admissible`由新Task的原`Selection.acceptable`计算。私有`Snapshot`缓存同次原`Source.seed`及每个原programme的实际判定，逐位置精确认回完整目录。`NoWorse`保原准入及全部原可接受programme，不把nondomination或某个成功witness塞进producer。

`Feed.Work.Reconstruction.Axis`覆盖原全部row／外部表、required query和原五入口。它直接使用原`Lookup.cell`缓存的Report／joint／port；每个programme的`oldCursor`来自相同source、表和post-cut。各口自己的next.saved／pending生成整域Snapshot，`preparedWindow`将同口native和每个`actual :: prior.domain`位置的实际重建native相接。`Holds`同时比较每个位置的完整Window、原准入及完整能力目录；`Rejection`保存新增关系真实失败的axis。

`Work.Prefix.Reconstruction`从原完整`Work.Prefix.candidates`逐项过滤后取首项。blocked保原Outcome及每个原候选的新增准确Rejection；selected保原verify／History关系及新增完整关系，再投影为原`Prefix.Global.Candidate`。调用方不提供筛选成功证书。

每个Snapshot计全部重建cursor、Task编译、原准入及完整原programme评估；每次比较分别预留两侧Snapshot，再计每个位置Window和一次完整能力比较。`queryCount／axes_count`从原Pi目录精确计算全部轴而不物化表值。`GlobalPolicy.World.units`把整笔新增单位加入原完整work；原`Accounting.covers`覆盖后，`World.select`才从同一prior Task／实际WorldInput生成两份目录并执行新门。缺价／短付保原实付prefix和typed分派，原Service消费相同候选投影。

以上窗口属于各候选原Feed的实际五口后继；最终Service另按下节自产同次实际后继并接受选前比较，两条实际事件链保持各自身份。

## 最终Service同次实际后继的选前合流

原Task自产`worldPending`及可选`worldCurrent`。后者只标识原law与实际cut/current，不承诺准入或未来成功；未写回的continuation会清空旧标识，源生成的初始Task和通信Task则从自己的实际current证明自产标识。缺失标识由`Work.Prefix.Actual`返回独立`unbound`，不伪造旧关系失败。

`TaskSource.Commitment`从同一prior point、rival和`past ++ suffix`安装完整Cursor，直接调用与最终Service共用的原`Writeback.next`。每个`actual :: prior.domain`位置沿自己的新法实际Machine生成完整Window；另检查同一次新Task的原Seed和整个旧有界programme目录。测试清单完整枚举，失败保具体Window位置、准入或programme位置。原完整重建池先按这项关系过滤，再取首项。

新增报价预留两侧全部控制词检查、Requests响应、完整重建与Snapshot，并计全部测试。`World.units`把原目录、原重建及本项合为一单，在原`Accounting.covers`先付门之后才选择。`Service.Actual.selected_next_is_the_prechecked_actual_next`先识别同一`(next, full)`参数对，再通过同一个`Communication.result`证明实际next、重建Task和target三者相同；显式类型的参数对避免证明器展开整个Requests计算。

此Commitment关系比较reference与候选各自的真实后继；原query基准由下节的独立保护门固定。全部新输入与后续修订的责任由唯一active维护。


## 同一次Service后继携带Task/source递归

`Service.Actual.next`读取携带Task的真实point深度及同一`made.full`的全部控制长度，经原`Writeback`逐词提交，随后调用原Requests。`raw_writeback_reaches_the_same_service_endpoint`消费已生成的law／current对齐，证明该raw终点精确等于同一次Service的Machine终点；所需等式是发生身份，不是合法性、成功或能力证书。

`Communication.result`在一枚抽象Packet上缓存同次`Communication.task`、target、native及law／current对齐，`Actual.rebuildAt`直接复用该工厂，再由`Actual.rebuilt`与Service原native合流。这样源身份通过同一packet消元，依赖类型检查不展开整条Requests产生式。它保每个旧domain位置自己的重建、完整baseline和horizon，并把实际Service Cursor加入新Task。

原`TaskSource.Iteration.execute`只初始化一次私有`Current`。初始Current保原Requests.Cursor、真实prepared packet、准备Evolution及原Task；准备只在进入首拍时纳入native。每拍`Current.produce`直接调用原`GlobalPolicy.produce state.task`，保持原Source.seed、Stage和World门。生成分支把`Actual.rebuilt`的Task和source存入后继Current；拒绝分支只打开已有准备，保同一Task。`Current.Run`沿每次生成的target递归，零观察保原cursor；整条native由原责任transport和Financial.Run共同消费。

`Current`同时保存Task.worldInput与ready packet、worldPending与实际pending的发生对齐；每个实际选中分派从原Selection提取完整保护，并识别同一次Service后继再进入原递归。选前Feed各口仍有自己的真实事件链。


## 原请求在最终重建target上的完整承接

`Commitment.Requests.cursor`直接读取同一次`Commitment.rebuilt.target`；其Window将原writeback native与Communication native按序相接。原Feed row／required query保持原Fin位置及重复项，实际提交词为`target.pending ++ q`；`Batch.entry.report`精确等于该target上原`Requests.produce target q`的报告。原q在新法下重新执行，旧合法性不被搬运为新法许可。

生成器固定一枚Rebuilt／target及其native，按原row保存一次Reports。每个Report保原joint disposition与五口Forecast；`Accepts`将完整`ScopeForecast.NoWorse`直接对照原`Lookup.cell`的同query Forecast，覆盖准确residual、完整Window／Funding、taskWindow及原Task admission。该基准属于原发生，reference后继的失效不能改写它。失败保具体原query；`Prefix.Actual.Preserves`把本门与原Commitment同时放入原池取首之前，原Selection直接携带查询保护。

原report split与raw inventory长度给出`target.pending.length ≤ prior.worldPending.length`。报价覆盖实际Reports及quiet原Batch可能逐query重造整行的费用；联合reserved定理在同一perProgramme预算内支付两侧。`pointServices × Feed.tableCount`按原Pi基数直接计算全部row权重，`perProgrammeUnits_is_the_exact_original_row_quote`认回完整原目录总价；报价不先分配table函数值。原World.units包含该报价，原Accounting.covers在任何生成与比较前付费。

此接口量化原Task的完整required目录。实际新输入进入该目录的源由下节给出；跨替代全部未来能力由唯一active维护。

## 实际新输入进入原Current的递归

`Current.Incoming.Result`缓存同一`Requests.produce ⟨state.ready,state.cursor.pending⟩ word`及其准确生成证明。原接收法先执行`pending ++ word`，再用同一response的next.saved／pending调用Communication；私有registered只把收到的原word追加到prior.futureRequests，不改source、rule、quote或两种rate。新Task由真实新法／World重建，接收失败的原raw位置继续对应target.pending。登记不产生许可、付款或结清。

`Incoming.advance`对同一个rebuilt.task调用原Current.produce。`Step.every_generated_successor_keeps_the_request_directory`覆盖service、实际修复及未修复拒绝；`Incoming.receive`对任意有限输入列沿实际target继续，typed内生阻塞后仍可接收外部材料。Run保整个旧目录及所有收到的word；native按每次接收与原step顺序连接，finance／funding／原责任admission、历史前缀及完整native.Run共用这条实际Evolution。目录保持不等于未来机会无损，也不证明原预算足以支付新目录。


## 原报价搜索的共享计算

`TaskSource.quotedActions`直接生成原`Code.actions`；原received、pending、自己的generated word、完整futureWords及逐项fee offer保持原次序和重复。`quoteRateCached`在原有限搜索前固定一次actions／rates／billing context；`rateCached`在原逆序单位搜索前固定相同对象，保原签名人和两种good的quantity比较。`quoteRate_eq_cached／rate_eq_cached`是完整函数等式，原Task经`@[csimp]`消费共享计算；原quote、rate、Offered、UnitOffer及Task定义的逻辑体保持。

冻结OLean或原生对象不会自动获取后来加入的`csimp`属性。将计算替换接入旧实际消费者时，按依赖图重编受影响consumer；跨模块私有specialization的共享名字可能改变，公共ABI相同不能代替一致的编译闭包。原声明身份、原函数等式和同字节实际main分别由自己的检查消费。按需生成的congr_simp证明可能移到更早导入的模块；此时仍须在完整导入环境比较原ConstantInfo的完整类型和证明体，不以单文件归属判断证明丢失。

## 原current的完整帧读回

`OutstandingSource.currentAt`与带外部输入列的`OutstandingSource.History.currentAt`是不同原入口。前者的`canonical_frame`已经将同一原root的raw current认回`frameAt`的raw；独立`Outstanding.CurrentFrame`据此给出完整函数等式，调用方保原current类型和发生身份，执行时直接读取同一完整付款帧。底层已签收模块无需重新展开其内部证明声明。

实际caller须由冻结C对象映射及真实函数体确定，不能从共享specialization名字中的`Repair.actualAt`推断调用路径。替换provider后，对其全部移除或改签名helper找出真实外部C caller，再按选定依赖DAG刷新；完整C ABI与IR的borrowed／owned调用约定共同约束装配。此读回不产生授权、责任结清或新的未来能力。

## 生产重编的依赖目录与写时物化

Lean优先命中首个模块命名空间目录；生产隔离库若只创建输出祖先目录，后列冻结库中的同命名空间导入可能被遮蔽。生产库以已验收的完整原依赖树补齐缺失项；编译前在独立materialize锁内逐层把链接目录展开为同一冻结子项链接，再解除当前OLean及private／server链接后写入。原执行库保持不变。

原literal主模块的输出不通过冻结输入链接写回；安装消费者使用根内逐字节源副本，完整C与已实际执行模块相等后才复用实际收据。目录修复只恢复未付生产重编，不重放实际调用或安装写入。

历史消费者通过同一source-provenance的historical_sources解析全部源码位置，包括strict编译和contract记录；其expected源码hash、OLean、精确依赖、内核及actual记录保持原字节。工作树已安装新等值实现时，原记录仍回放对应原快照；生产重编继续核对当前已安装源码。缺失指针补到已有同hash原快照，不改expected hash。


## 任意轮的同源分段与完整处置

`Iteration.Current.Continuation.causalAt state n` 由原 `Autonomous.tick` 逐拍生成；完整函数前缀通过 `exact_observed_prefix` 认回原 `Autonomous.execute`。`successive_prefixes` 使任何较晚前缀恰为较早实际 Current 的继续，`segment` 因而生成同一两端之间的 `Event.Evolution`。全部 query 目录、已收 basis、逐原责任身份与完整历史、金融 receipt 都沿这个 segment 运输。

`dispose` 消费原 `Current.Step`：未修复的原拒绝保其 row、原 Task 与 blocked 标记；修复保同一 `Refusal.Result.nextCurrent`；原服务保实际 `after` 与 `SelectedNextIsChecked`。`WorldProtection` 仅从实际已选 candidate 取得同次原 query、当前与祖先 future 保护。`ServiceReview` 同时完整检查内部分派：不可用保原 ready=none，legacy selected 保 fullAccepted，legacy blocked 对每个原 tail 保 Failure，short 保实际 ¬covers，World 结果保原 Selection.reviewed。完整 service 仍携带具体 source outcome，拒绝中的 current／ancestor 与 intent 见证可直接析取。

这些合同对任意 start/count 成立；原 `Incoming.receive` 对任意有限实际输入列的合同继续适用。源生第 n+1 轮不把第 n 轮阻塞变成终止或 authority；未来资源与候选成功仍由各轮实际产生。
