# Homework Coin 试点协议：从 shadow replay 到真实 spend

> **性质**：现实部署与经验验收协议，不是新的货币本体，也不是已经运行的系统。
>
> **架构依赖**：[《生成型货币》](generated-money.md)。社会根法与经济宪法分别见
> [《舞蹈生成舞者》](dance-generates-dancers.md)和
> [《可能性的经济宪法》](economic-constitution-of-possibility.md)。
>
> **当前边界**：generic Society action/U8 mouth 已闭合；Homework capability carrier、authoritative mint、
> spend 与 empirical runtime 尚未部署。本文预先锁定它们必须通过的协议与失败处置。

---

## 一、试点唯一问题

Homework Coin 不以币价、交易量或 market cap 证明成功。它只检验：

> 一次真实作业能否生成可被下一次独立作业消费、不可重放、保留责任来源并允许退出的 typed capacity？

首期不售币、不预挖、不兑法币、不承诺升值，也不另造 blockchain。试点必须先证明“币拥有作用”，再讨论
market interface。

---

## 二、为什么 Homework 是合适的首个场域

Homework workspace 已天然拥有：

- exact theorem / implementation demand；
- Git source lineage 与 commit identity；
- Lean kernel、tests、build 与 reproducibility verifier；
- direct consumer；
- axioms / provenance audit；
- failed attempt、counterexample 与 residual；
- compute、review、maintenance、context 与 attention 等真实稀缺资源。

这些对象仍须进入同一 source-generated carrier；“仓里已经有 Git/Lean”不自动产生货币 authority。

---

## 三、创世：历史只校准，真钱从零开始

历史提交用于 shadow replay：

\[
\boxed{
\operatorname{HistoricalShadowReplay}(h)
\Rightarrow
\operatorname{CalibrationEvidence}(h)
\land
\neg\operatorname{CurrencyAuthority}(h).
}
\]

shadow receipt 不可转让、不可消费、不进入 wallet，也不生成治理权。历史 proof/code 已经获得真实报酬：它们
进入了共同世界；不得补发为私有币、预挖、祖父份额或永久租金。

创世条件：

\[
\boxed{
\operatorname{GenesisPrivatePortfolio}=\varnothing,
\qquad
\operatorname{RetrospectiveMintAuthority}=\varnothing.
}
\]

第一枚 authoritative capability 必须来自 genesis 之后的新 occurrence：

```text
public pre-existing demand
→ post-genesis actual work
→ independent verification / consumption
→ first authoritative mint
```

---

## 四、公开顺序：仓先币后

schema、source、fixture、attack model 与 shadow replay 先公开；货币接口后开。启用 mint 前至少需要：

1. public repository 与可复算 fixture；
2. 不受发行团队单独控制的 external green builds；
3. genesis/no-grandfathering audit；
4. challenge 与 consumer-liability mouth；
5. 目标 jurisdiction / law epoch 的 typed release review。

release review 只授权对应 \((j,e)\)，有期限、限制和重新审查触发器；它不是全球永久合规 oracle。审查未闭合，
该辖区接口保持关闭并登记 residual。

禁止在此之前公开 ticker、私人 allocation、authoritative balance、交易市场、募资或升值宣传。

---

## 五、首批 capability families

### 5.1 ProofCapacity

由 exact demand、focused compile、direct consumer、axiom audit 与 provenance check 闭合的 proof occurrence 生成。
proof term 进入 commons；capacity 只结算后续 proof search、review 或 integration 的稀缺 consequence。

### 5.2 ComputeCapacity

一次明确 runtime/model/duration/resource envelope 的可执行调用权。首期只覆盖仓内可复算 Lean build、test、
benchmark 与可复现推理。外部 GPU/energy 只有在物理测量、读取 channel 与 residual consumer 闭合后才取得 authority；
账单、供应商 dashboard 或模型自报不是能源 oracle。

### 5.3 ReviewCapacity

由真实 audit consumer 生成。发现 target-smuggling、第二 ledger、假 positive 或隐藏 residual 可以比新增代码行产生
更高价值的 review consequence。

每枚 review 必须公开 bounded independence readout：producer/consumer lineage 交叠、共同控制/资助、近期互评与
challenge authority。目标不是禁止合作，而是排除封闭联盟自产、自验、自铸。

### 5.4 MaintenanceCapacity

用于依赖、文档、测试、迁移、reproducible environment 与长期 runtime。维持世界继续可用本身是生产。

### 5.5 RepairCapacity

由 exact obstruction、reproducible failure、source-aware repair route 与 downstream regression consumer 生成；
“已经修好”的裸 verdict 不发行。

---

## 六、一枚 source-generated 试点事件

审计 readout 至少包含：

```text
parent current
+ exact demand
+ fixed source program / commit
+ actual trace / artifact hash
+ verifier outcome
+ independent consumer
+ resource debit
+ residual bearer / disposition
+ generated capability outputs
+ whole-ledger write-back
+ next current
```

这不是客户端可填写的 JSON schema。public input 只有合法 source program/attempt；其余 fields 必须由 fixed
compiler 在 exact event 上生成并由 consumer 重算。

---

## 七、钱包与 spend

钱包只做 derived query：

```text
all generated capability incidences
− exact consumed incidences
− expired / settled dispositions
= visible unspent portfolio
```

不得以可手工修改的 balance table 为 authority。

一枚真实 spend 必须：

- 指向唯一 unspent incidence；
- 生成 actual transformation、accepted maintenance 或 typed failure；
- 完成 resource/responsibility write-back；
- 生成 next；
- 使原 incidence 不可再次消费，除非 source compiler 先生成守恒 split。

转账只改变 exercise authority，不删除 provenance、expiry、resource debt 或 affected bearer。

---

## 八、发行正例与反例

### 正例

- theorem demand → proof → kernel check → downstream theorem consumer；
- failing route → reusable counterexample → route compiler 实际剪枝；
- regression failure → source-local repair → test consumer；
- review 发现 material defect → 修复进入 checkpoint；
- infrastructure maintenance → 后续 build/runtime 恢复。

### 不发行

- 只有 token 数、工时、FLOPs 或模型自评；
- 无 exact demand 的自选 busywork；
- 无 direct consumer 的 artifact；
- result 重复包装或同一 acceptance 重放；
- 只改措辞而未改变能力；
- 把 residual 丢给其他线程；
- 使用未授权数据、隐私泄漏或不可复现外部环境；
- 为刷币制造无意义任务。

失败若生成 reusable obstruction，其 result 进入 commons；只有被 downstream consumer 实际使用的 route-pruning
consequence 才可生成 typed capacity。

---

## 九、challenge 与 consumer liability

acceptance 是可挑战的 authority action，不是免责印章。

成功 challenge 必须同时具备：

- exact challenged acceptance；
- source-backed evidence；
- 不受原 mint coalition 垄断的裁决 consumer；
- 实际撤销、修复或责任 disposition；
- reward 的真实 source（bond transfer、public audit pool 或 verified scarce closure gain）。

admissible 但未成立的 challenge 进入 typed rejection，不铸币，也不因失败自动处罚。只有 source-proven replay、
串通、重复提交或 challenge-budget abuse 才产生 debit。

错误/串通 acceptance 被坐实后，consumer 必须成为 residual bearer，不能只回滚 producer balance。

---

## 十、baseline、公共池与 newcomer standing

试点必须周期续约基础 compute/review/participation capacity；新人无需先产出高价值 proof 才有资格继续参与：

\[
\boxed{
\text{unconditional baseline renewal}
\neq
\text{source-free issuance}.
}
\]

机器、维护、审核与 opportunity cost 仍需结算。“无条件”只是不以历史余额、雇佣角色或绩效评分为 standing
renewal 条件。

公共池优先来自 verified scarce closure gain：若一次生成真实减少后续 compute、review、maintenance 或 coordination
成本，其被独立消费的节省可注资 baseline。non-rival theorem/code 本身仍进 commons，不征“知识税”。

流入比例由可修订 budget law、当前 baseline obligation 与 actual capacity 生成，不成为 founder 永久常数。

---

## 十一、隐私与有界审计

\[
\boxed{
\operatorname{FullOccurrenceProvenance}
\land
\operatorname{ObserverBoundedReadout}
\land
\operatorname{ChallengeRecoverability}.
}
\]

工资、医疗、家庭支持、照护或安全研究可以隐藏正当私密内容。public face 只证明 demand 类别、合法 source、
settlement conservation、conflict disclosure 与 challenge mouth。争议发生时，有 standing 的 consumer 取得最小
充分证明，而不是把原始生活史广播全网。

完整 provenance 不等于全民围观；隐私也不能制造不可挑战的暗箱。

---

## 十二、货币政策与 market firewall

- supply 来自 actual settled capacity，不来自固定总量神话；
- inflation 是 nominal claims / executable accepted capacity 的上升；
- non-rival result 不过期，scarce claim 可以有 source-generated expiry/renewal；
- fee 必须对应 ordering、verification、storage、privacy、dispute 或 maintenance consumer；
- fiat quote、custody 与 wrapper 永远标记为 claim；
- protocol 没有价格托底、回购或制造稀缺的 authority。

\[
\boxed{
\operatorname{ProtocolPriceSupportAuthority}=\varnothing.
}

首期禁止法币兑换。未来 market bridge 必须另过 no-replay、credit marking、run risk、bankruptcy、privacy 与 residual
disposition；market 热度不能替代验证纪律。

---

## 十三、部署顺序

1. **Shadow phase**：历史真实提交重放，只产 calibration evidence；
2. **Public audit phase**：发布 schema/source/fixture，取得 external green builds、genesis audit 与 release review；
3. **Genesis phase**：只接受 genesis 后新 occurrence，启动 mint 与 derived portfolio；
4. **Spend phase**：闭合 transfer/spend/split/merge/burn/no-replay；
5. **Challenge phase**：闭合 coalition no-go、consumer liability、reward/abuse disposition；
6. **Federation phase**：多参与者 demand/consumer，baseline 与 capture tests；
7. **Market phase**：只有前六阶段通过后才允许单独审计外部接口。

每一阶段都必须保留停止/拒绝的 typed residual；没有 `pending but authoritative` 状态。

---

## 十四、时间锁定的 empirical seal

authoritative mint 启用前必须登记：

- epoch start \(t_0\)；
- 最小成熟发行量 \(N_{\min}\)；
- maturity / spend window；
- independent-spend threshold \(\theta\)；
- coalition exclusion 与 denominator rule。

初始试点可以预登记 \(\theta=50\%\)，但它只是该 epoch 的经验协议参数，不是货币根法常数。

\[
\operatorname{IndependentSpendRate}_{90}
=
\frac{\#\text{进入非封闭联盟 consumer 的成熟 spend}}
{\#\text{具有完整消费窗口的成熟 issuance}}.
\]

- 若 volume \(\ge N_{\min}\) 且 rate \(<\theta\)：`currency-has-action` claim 判负，登记 residual 并进入 revision；
- 若 volume \(<N_{\min}\)：结论是 insufficient volume，不得冒充成功；
- 自转账、自产自花、封闭互评、wallet migration 与只生成 quote 均不计 independent spend；
- 禁止空投、回购、事后改分母或关联市场制造通过。

Lean 可以预先验证 metric compiler 与 disposition grammar，不能预先证明真实 90 天结果。

---

## 十五、试点验收

试点通过必须同时满足：

- genesis private portfolio 与 retrospective mint authority 为空；
- 每枚 issuance/spend 回到 exact occurrence、whole ledger 与 next；
- result 可复制而 settlement claim 不可重放；
- mint 不受封闭 coalition 控制；
- false acceptance 由 consumer 承担责任；
- challenge reward 与 abuse debit 都有 source；
- baseline 有真实 budget/service source 且未被 capture；
- bounded audit 与 challenge recoverability 同时成立；
- fiat/custody/quote 不取得底层 authority；
- 90 天 verdict 按预登记 metric 如实给出 success / failure / insufficient volume。

币价、market cap、社交热度与内部自花均不是验收指标。

---

## 十六、实现责任

启动试点前仍需在既有 Society root 上闭合：

1. source-generated result/capability common carrier；
2. exact mint/spend/no-replay 与 split conservation；
3. result-copy / claim-spend direct consumers；
4. coalition authority-closure no-go；
5. challenge settlement / consumer-liability disposition；
6. derived wallet readout；
7. genesis/release compiler；
8. empirical metric consumer。

这些都是 generated-money application responsibilities，不重开已闭合 M∞ 根法，也不构成 Society 定稿前置条件。
