# Klyshko 效率、发对率与共同收集参考面

本卡保存稳定的输入语义。当前状态、数值结果和下一责任只见 [README.md](README.md)。
来源：[Dixon 等，2014，p.2 Eq.(1)–(5)](https://arxiv.org/pdf/1407.8487v2#page=2)；
NIST 主文 p.4 明确采用 Klyshko 方法。版本及获取哈希见
[additional-source-review.json](additional-source-review.json)。

## 条件效率不能按字段名解释为绝对损失

以下 sA/sB/j 指未做偏振筛选或已校正筛选的单对、无背景校准率。
令 Q 为每脉冲全源发对概率；Pa/Pb 为各光子入收集模式的概率，Pp 为两光子同时入模的
概率；uA/uB 为入模后的传输与检测效率。提取这些 scalar 以共同参考面固定、后续损失对
设置与偏振独立为假设；跨 r 保持数值也须来源确认，一般情形应使用相应 effect/channel。则

```text
sA = Q Pa uA             sB = Q Pb uB
j  = Q Pp uA uB
ηA^K = j/sB = uA Pp/Pb   ηB^K = j/sA = uB Pp/Pa
ηc = Pp/√(Pa Pb)
```

要求有效模型 `sA=q ηA^K, sB=q ηB^K, j=q ηA^K ηB^K` 同时再现这三个率，
在非零分母下唯一给出

```text
q_eff = sA sB/j = Q Pa Pb/Pp = Q Pp/ηc².
```

因此，Q、同时入模的对率 QPp、q_eff 是不同的输入身份；必须绑定实际采用的定义。
若公布的 q 本来按 singles/coincidences 与 Klyshko 效率推算，它可能已经是 q_eff。
这条恒等式**没有证明旧重放存在第二个数值 bug**，也没有给出替换 q 的数值。
将 q_eff 解释为 Bernoulli 真空/单对混合权重还需其落在 [0,1]，并支付单对近似。

## 偏振分辨的共同载体

同一全模式源在共同收集参考面生成三个非归一正对象：

- Ω_AB(r)：两光子同时入模后的双侧对象，trace=Pp(r)；
- Ω_A(r)：Alice 入模的对象，含 Bob 失模分支，trace=Pa(r)；
- Ω_B(r)：Bob 入模的对象，含 Alice 失模分支，trace=Pb(r)。

测量 effect Πa/Πb 在这三个对象上生成

```text
sA(a)  = Q uA tr[Πa Ω_A(r)]
sB(b)  = Q uB tr[Πb Ω_B(r)]
j(a,b) = Q uA uB tr[(Πa⊗Πb) Ω_AB(r)].
```

Ω_A 一般不等于 Ω_AB 的 Bob 偏迹：后者不包含伙伴失模分支。
用一个条件双光子态 `ρ=Ω_AB/Pp` 加两枚 scalar η 表达所有设置，一个充分归约条件是
`Ω_A=Pa tr_B ρ, Ω_B=Pb tr_A ρ`，并说明这些身份如何随 r 变化。
若仅消费所用 effects，可按它们的读出恒等支付归约。角分辨的 coincidence/single 比率
另含相应 effect 读出，不能直接解释成同一常数 η。
最大态可见度及校准时的 Klyshko 比率不能单独生成这些非最大态对象。
原设计若已用有效 q、η 和信道完成上述归约，交付其公式与参数定义即可；不要求重建全部模式。

## 设计目标

官方 SI p.1 Eq.(S1) 支撑已冻结的 CH 线性违反目标；在模型无信号条件下，
`P(++|ab)−P(+0|ab′)−P(0+|a′b)−P(++|a′b′)` 正好等于现行 LHS−RHS 展开。
[Bierhorst，2015，Eq.(2),(5)](https://arxiv.org/pdf/1312.2999v3#page=3)
区分每试次统计量与在非零步上的条件统计量；这是检验方法，不能据此换成 ratio 或显著性优化。
原实现仍需把其标量、控制自由度与同一输入表一并绑定。
