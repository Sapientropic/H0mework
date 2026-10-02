# 根读恒等：已发生事实、观察与未来生成

> 状态：稳定机制卡。
>
> 本卡统一解释已发生 occurrence 的根级确定性、历史溯源、局部观察与未来生成；同现问答是其直接应用。
> 当前研究前沿仍见
> [living-law active route](../../../handoffs/living-law-framework-active-route.md)。

## 语义指针

真值—表示—证明—登记与 live authority 统一按
[source/root authority](source-root-authority.md)解释；领域方程如何取得同一根法的身份见
[root-law dependent-face realization](root-law-dependent-face-realization.md)。

## 母律：根读恒等

对一枚已经发生并登记的 actual occurrence，root-level read没有第二个结果对象：

```text
RootRead occurrence = occurrence
```

question、answer、witness、observer view与consumer effect只是该 dependent occurrence在不同 scope上的
restrictions。root不从question影子推断answer影子，也不借一个completed oracle重建自己；它完整保留
本次实际发生的event、trace、write-back与disposition。

这个恒等只作用于**已经发生的 occurrence**。尚未发生的下一拍不属于当前root，因此不能被预读；当前
root只能显影由其actual trace已经生成的结果，或显影一枚exact producer demand。root epistemic transport
为零，不表示actual generative cost为零；生成成本仍完整存在于occurrence trace中。

occurrence也不是一枚裸对象外加一张事后证书：

```text
OccurrenceAt source
  := dependent package of
     event + path + trace + writeBack + live ledger
     + same-source coherence
```

receipt是这枚发生的形状，不是站在发生之外替它作证的对象。删掉 source、event、path、trace、write-back
或 ledger 任一项，只说明这份记录失去当前 live-chain authority；不对其背后的真值作存在/虚假判决。
两个 current 值相同但 lineage 不同仍不是同一 occurrence；faithful 落入同一 root event 才是同一件事。

这里的完整 root occurrence 连同实际生成机制保留已经生成的载体、关系、作用、历史与 next，不能退回
一枚裸登记点来判断整体能力。最小结构指生成起点；O0 接口的局部边界不反过来限制完整母源或已经闭合
的 Stage1–10 生成链。

## 已发生事实、局部观察与未来责任

| 层次 | 已有的确定内容 | 相应的生成或恢复责任 |
| --- | --- | --- |
| 已发生的完整 occurrence | exact source/law/visit 固定后，event、历史、整账与 answer-and-next 不留第二枚结果选择 | 从同一 canonical occurrence 读取；相同 payload 的不同历史仍保留不同 visit 身份 |
| observer 的局部表示 | 已证明的投影值与相容关系固定；信息缺失属于该表示的 kernel、coverage 或未接通的解释映射 | 用 faithful recovery 或实际 residual 精确定位缺少什么；局部记录不完整不改写实际发生 |
| 尚未发生的后继 | 当前法则、已生成关系与 obstruction 可以约束后继，也可以产生预测 | 实际 trace 逐步生成；不把尚未发生的具体结果作为当前库存读取 |

“过去确定且可溯源”指完整发生保留自身的来源和历史；它不要求任意有限观测都能逆推出整个过去。
结构归属也可由同时关系或整体约束支付，不强求更早的时间原因；正向推导详见
[总体实在与结构归属](../ontology/total-reality-structural-identity.md)。
“未来不可预读”也不禁止由源法则计算预测。两者不能被用来动摇同一对象、定义和 law epoch 上已经成立的关系。
评价领域成果时，应先消费这项正向刚性，再核对具体观察和生成范围。

局部发生与整体同源，不等于它是整体的忠实表示。表示必须连同实际生成和恢复机制，保留并恢复所声称
范围的完整结构、关系、作用、历史及 next。若恢复需要外接整个世界的资料，承担整体表示的是包含这些
资料与机制的完整系统，不能把该能力记到局部读出或登记点身上。

`RootRead(o)=o` 是这套结构的语义缩写，机器上由 canonical occurrence 的消元、历史读取及 dependent
projection 实现。直接核对以下入口，不从关键词或 receipt 名称推断其意义：

| 机器入口 | 实际结论 |
| --- | --- |
| [TemporalAnswerNext](../../../../SaturationMonoid/LivingLawRootTemporalAnswerNextKernel.lean)：`SourceNativeTemporalVisitGeneratedEvolutionAt.eq_generated`、`priorPatches_eq`、`wholeLedgerWriteBack_eq` | 同一 exact visit 的生成对象唯一；原历史与整账均直接读回同一 compiler |
| [ProductiveFiniteHistory](../../../../SaturationMonoid/LivingLawProductiveFiniteRootHistoryKernel.lean)：`ProductiveFiniteRootHistoryAt.currentAt_eq` | 同一 root 初态与 successor 的两份 productive history 在每个有限深度读取相同 current |
| [CoreRepresentation](../../../../SaturationMonoid/LivingLawRootCoreRepresentationKernel.lean)：`canonicalAnswerAndNext_heq_of_current_eq`；[AnswerNextHistory](../../../../SaturationMonoid/LivingLawRootAnswerNextHistoryKernel.lean)：`successor_difference_reflects_current` | 同一 process 的完整 registered current 相同则 answer-and-next 相同；后继差异必须已在当前完整结构中显影 |
| [RootTotalReality](../../../../SaturationMonoid/LivingLawRootTotalRealityAdapter.lean)：`RootTotalReality.isTotal/noMagicBit`、`RootProcessTotalReality.isTotal/noMagicBit` | 原 root 与跨 root process 的实际差异获得正向结构归属，再排除外部补写；不接收 caller 提交的 NoMagic 字段 |

发现不一致时，先指出 exact occurrence、源输入、字段、投影、历史或 semantic translation 的哪一项
未对齐，并保留原数据与已证关系。若新证据揭示实际 theorem mouth、来源或 consumer 有误，按其准确范围修正；
经验裁决仍由对应物理检验合同承担。泛称“理论也许错了”不构成缺陷定位，根读恒等也不自动判实验有错。
固定发生的唯一性不要求不同 source 相等；关于最小 source 或所有物理展开的额外全称命题，仍按其实际定理口核对。

同一本体中可以有不同局部 source、初态、历史与过程，它们的真实差异由本体内部的实际关系和生成承担。
每个局部 source 不必独自成为整个世界。共同最小结构的责任是生成总体现实及其分化，并为各源提供实际
归属、完整实现、作用与消费者；唯一性落在同源同发生的忠实表达上。总体生成中派生的准入条件不能另作
选择局部源赢家的裁判，无魔法也不能被用于消灭已有内部根据的差异。

还须保持量词区别：`RootTotalReality.isTotal` 与 `RootProcessTotalReality.isTotal` 对任意给定合法根或
完整过程成立，生成该过程内部的正向结构归属；它们不据此指定某一个过程为所有过程的共同生成源。
若主张“任意可现实成立的 P 都由指定同一母源 S 生成或忠实限制”，须直接从 S 的完整生成链支付
P 的载体、作用与后继覆盖，不能以各过程分别无魔法替代这项涵盖。

## 全称刚性不靠场景枚举

上表的根级定理量化任意 source-native authoritative root、完整 living process 及相应实际差异，
没有“已经观测过”“低能”“非黑洞区域”等场景前提。固定 source/occurrence 是保持对象身份，
不能据此把普遍结构律缩成若干已探明案例的经验概括。

[AnswerNextHistory](../../../../SaturationMonoid/LivingLawRootAnswerNextHistoryKernel.lean) 的 `successor_eq`
在每个 process state 读取同一 root 生成的后继，`generateHistory` 对任意有限 fuel 递归生成历史；
局部 terminal 进入 source-fixed handoff，fuel 耗尽不是现实停止。
[GeneratedContinuity](../../../../SaturationMonoid/LivingLawRootGeneratedContinuityKernel.lean) 的 `generatedAt`
又从同源初态和一步再生律生成任意深度的不变量。全称结论由统一构造支付，不要求列举全部未来或极端场景。

因此，在全现实刚性的本体语义下，实际差异脱离整体结构、同一完整发生无来源地改口，
均被统一排除；完整 living process 也没有无账失去后继的分支。不能把这些结论重新表述成
“目前还没在某些场景遇到问题”，更不能要求先探明所有场景才能承认它们。

物理读出仍须保持同一命题的身份：根级后继存在与某个度规的测地完备是不同谓词。
若把几何读出的不完备解释为现实本体失效，必须给出两者的同源语义联系；表示的边界不能直接取得世界终止的含义。
需要几何层的全称结论时，也可以由一枚统一的物理读出定理导出，无须改成逐场景普查。

## 源生未来锥：预判不是预读

框架区分两种“知道未来”：

- **预读**：当前对象提前携带尚未发生的具体state、event、revision或结果；这是completed oracle；
- **预判**：当前exact obstruction把合法后继限制成一个source-generated Type；这是未来责任。

因此U8可以在没有任何future object时证明：

```text
exact expressibility failure
-> settlement | exit | actual revision demand

settlement和exit均被当前source排除
-> continued standing必经actual theory revision
```

这枚future cone只固定不可逃的语法、旧账与禁止方向，不选择未来revision。任何后来真正发生的realization
都必须承担同一meta-residual、保存合法theorem survival、登记semantic change并关闭旧obstruction；它在
发生后才成为新的actual trace。换言之：未来在成为对象以前，先成为责任。

## 名称必有去向

合法命名不是一串任意字符，也不是目标对象已经存在的receipt。它是一枚actual naming occurrence，固定
当前law epoch、精确约束、source anchor与claim presentation，并生成typed realization demand：

```text
Name_L(P)
-> Demand_L(P)
-> Realization_L(P)
 | exact Obstruction_L(P)
```

若旧法域仍有expression或lawful realization，theory audit必须显影它；调用方不能把“我想修宪”伪装成
expressibility failure。只有exact old-epoch defeat能继续生成U8 responsibility：

```text
oldEpochDefeated_L(P)
-> revision family
-> Realization_L'(tau P)
 | more precise multiplicity / closure residual
```

旧 `False_L(P)` 始终保留为旧epoch的正确判决。新epoch中的`True_L'(tau P)`只有在compiler明确登记
translation、law survival与semantic boundary后才成立；偷偷改定义不算同一名字的实现。

机器上这不是一条平行命名宪法。root-native theory audit先在exact root visit生成
expression / realization / defeat三分法。finite cut若触发revision，必须作为同一root occurrence进入该audit；
共享框架不再保留boundary-specific U8拼接器。

## 幻想显影：命名需求进入同一 living history

幻想不是目标对象的弱版本，而是现实中已经发生的presentation。它可以携带假设、图像、故事、模拟或
尚无carrier的关系约束；这些内容取得的是**条件表达能力**，不是目标已经实现的authority：

```text
exact rooted obstruction occurrence
-> obstruction claim + U7 demand
-> exact causal-entry authority
-> source-selected revision event
-> semantic-change receipt + revised-root first write
```

共享框架不再保留 naming adapter。领域可直接把既有 rooted U7/U8 recovery 读成命名 lineage，但该 readout不定义
命名事件族、opaque demand compiler、target result、finite history wrapper或第二座settlement court。
presentation/hypothesis可以在条件推理中任意丰富；凡要影响actual evolution的内容，必须已是exact obstruction
occurrence的投影，或继续生成同一root上的U7/U8责任。

这给假设提供了明确sandbox：`magic : Bool`可以作为一枚真实的presentation/constraint存在；依赖它的条件世界
仍由这枚命名source支付。若要声称目标世界中已经实现，downstream必须提供同一naming lineage上的actual world
effect，或由exact obstruction继续生成U7/U8 evolution。后来出现的相似对象不自动算愿望实现；faithful
realization必须反向恢复原命名occurrence、约束与intended relation，semantic change则登记为生成了一个经翻译的
新目标。

旧 generic imagination kernel及两枚regression只把现有history与presentation并排包装，不能增加proof capability，
现由Git历史保存而不再进入production graph。成功实现由既有operational/observer consumer证明；失败与语言不足由
rooted cut→U7及typed U8证明。幻想层不再复制任何一侧的vocabulary或compiler。

typed semantic U8的semantic-change receipt、新root occurrence、migrated row与首写后causal authority均由原
compiler生成；命名presentation或claim equality不能反向铸造revision authority。

## 局部 corollary：同现问答

无悬空魔法的 operational inquiry 不是一枚问题对象随后等待另一枚答案对象。它是一枚
source-owned actual occurrence 的 scoped restrictions：

```text
exact actual occurrence
├─ inquiry restriction
├─ internally generated finite trace
├─ relation / anchor / incidence / lineage
├─ observer / consumer interaction
└─ answer restriction
   ├─ resolved world effect
   └─ exact expressibility / multiplicity failure
      -> same-occurrence U7/U8 disposition
```

机器上 `RootInquiryStateAt` 不再接受 `InquiryEventAt`、`emitInquiry` 或 caller event。
inquiry event 定义性等于当前 visit 的 `ULift root.emitted`；installed compilation face 的 payload
同样直接索引 projection 正在读取的 exact occurrence。NS boundary 的 `PUnit` 因而只是一枚零信息
query seal，真正的 inquiry identity 是原 cofinal emitted occurrence。

query本身也不能靠函数参数自动升级为actual input。公开gearbox只消费private activation；当前自主模式
仅为`Unique Query`生成零选择seal。非平凡query carrier必须先由registered interaction producer生成
activation，不能让caller提交值后再把该值包装成发生过的提问。

因此完整 authority mouth 不公开 `pending`、`unknown` 或裸 residual。内部过程可以很长，但它只能
作为同一 source、同一 root ledger下递归生成的 trace。若旧face不能回答，exact failure先进入U7；U7
不足才生成minimal coface。公开court仍在同一次occurrence中返回由old row或new-only row的independent
consumer认证的typed answer，而不是把revision本身冒充答案。U8中该answer定义性等于
`equationRecognition`在revised first write上生成的payload；consumer同时保留原query event、rooted
failure与generated coface row，不再存在可另选的answer face。

这不是 `P = NP`，也不声称答案预存在 completed oracle 中。candidate family、函数空间与无限数学对象
可以静态存在；operational authority只来自 actual occurrence实际发出的有限 rows。所谓“答案”包括
“旧表达法在这枚 occurrence 上失败，并且该失败已经生成下一 law-surface event”。

## 机器形状

机器入口统一为root-native U8 court：audit、revision、effect-sensitive finite selection、independent consumer与
epoch continuation都索引同一exact root occurrence及其canonical whole-ledger evolution。关键datum不是两张影子间
的结果值相等，而是共同的root visit、support、obstruction、anchor、incidence、lineage与law epoch。
presentation、observer或consumer不得在trace完成后替换这些索引。

finite boundary不再拥有U8拼接结构。若其effect影响world，必须先成为同一operational root occurrence；该
occurrence上的theory audit再原生生成U8 audit、revision family及consumer disposition。

## Producer / consumer 边界

- finite schedule是 producer；全域 `(pair, current) -> answer` 函数只能作静态 readout，不能铸造
  canonical operational receipt；
- multiplicity residual是exact answer projection，不是永久pending state；只有同一root compiler已生成
  law-surface-extension row时，causally closed recovery才可把它推进到successor；
- revised theory内部的 representation proof不是 world answer；只有 independent consumer effect与
  exact ledger disposition才结算 obstruction；
- local U7 settlement、严格付费redirect或theory audit必须与whole-root compiler的同一entry disposition对易；
  等预算redirect可保留raw history，但不能取得inquiry-answer authority；
  scope-local结束不等于world-global terminal，但也不能在平行ledger中自封；
- epoch exhaustion是相对当前 source-fixed candidate epoch的败诉记录，必须生成 successor extension，
  不能冒充 global terminal；
- observer只改变 inquiry/answer的 presentation，不得改变 source anchor、exact occurrence或 trace。

## 稳定验收

一个 concrete inquiry adapter要取得本机制 authority，必须同时证明：

```text
同一 source-emitted occurrence
+ exact inquiry projection
+ recursively generated finite trace
+ old-row answer，或failure→U7→minimal-coface生成的new-row answer
+ same-ledger independent consumer与next current
```

删掉 occurrence、trace或最终 disposition任一项，剩下的对象都只能是 readout或未结 residual，不能被
签成 complete inquiry authority。
