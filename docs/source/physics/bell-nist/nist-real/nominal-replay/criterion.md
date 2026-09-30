# 独立名义装置重放判据（criterion）— NIST 2015 漏洞无关 Bell 测试

版本 `nominal-replay-r0002`（见 §10 修订史：r0001 → r0002 只改一处**归一化映射错误**，
由与目标值无关的公开阈值检验（D3b）判定；r0001 的输出保留为
`replay-r0001-superseded.json`）。本文件是本次重放的**唯一冻结输入**：`replay.py` 与
`independent_replay.py` 只从本文件末尾的 FROZEN-INSTRUMENT JSON 块读取数值，代码里不留任何
可调旋钮；本文件的 sha256 计入 `replay.json` 的绑定表。

**A-priori integrity statement (verbatim, required):**

> No model choice or parameter in this file is adjusted after observing replay output; any change
> requires rewriting this criterion first.

作者身份：r0001 在**任何优化输出存在之前**写成（写作时刻该目录内不存在 `replay.json`、
`independent_replay.json` 或任何 `*.opt` 输出）；r0001 不含任何来自优化输出的数字。
r0002 的修订动机、依据与披露见 §10。

---

## 0. 这份东西是什么 / 不是什么

- 是：一个**独立重放**。按公开文档（Christensen 博士论文 Appendix A）实现装置模型，用 2015
  论文正文 p.4 公布的**全局**信道值做输入，在**预先声明**的容差带方法下，检验论文公布的
  （态，两个 Alice 角，两个 Bob 角）是否落在重放最优的带内。
- 是：名义装置最优门禁的**候选输入**，供后续 gate review 复核。
- 不是：门禁通过。本文件与 `replay.json` 都不签收 `ready`。
- 不是：对 2015 仿真代码的复原。该代码在任何公开渠道均不存在；本文重放的是**同一模型族的
  公开方法**，不是原程序的复刻。

---

## 1. 文档化目标值（冻结，只读）

目标值不在此重打一遍，只从 `../instrument.json`（`revision: r0003-NIST-design`，只读、不改）
读取并哈希绑定：

| 量 | 文档值 | 来源 |
|---|---|---|
| 态 | `0.961\|H_A H_B⟩ + 0.276\|V_A V_B⟩` | arXiv:1511.03189v2 p.4, Eq.(2) → `instrument.json.preparation.amplitudes` |
| r（HH 归一约定） | 0.276/0.961 = 0.2872008324661811 | 同上；`instrument.json.preparation.normalization = "radial"` |
| Alice 角 | 4.2°, −25.9°（相对垂直偏振片） | 论文 p.4 → `instrument.json.controls.alice` |
| Bob 角 | −4.2°, 25.9° | 论文 p.4 → `instrument.json.controls.bob` |
| 公布舍入分辨率 | 角 0.1°，振幅 0.001 | 论文 p.4 的十进制位数 |

角度-设置的对应（**由模型推出，不是选择**）：论文 Eq.(1) 的 unprimed (a,b) 对应论文角
{4.2°, −4.2°}，primed (a′,b′) 对应 {−25.9°, 25.9°}；在定理式的对称归约下即
`θ0A = −θ0B = θ0 = 4.2°`，`θ1A = −θ1B = θ1 = −25.9°`（论文 p.2 Eq.(1) 与 p.4 的角度赋值、
论文 p.4「calibrated to maximize violation」的 SI 表述；符号约定见 F4，镜像自由度见 F13）。

---

## 2. 一手来源与哈希

| 文件 | 来源 | 说明 |
|---|---|---|
| `../instrument.json` | 仓库 | 冻结目标值 |
| `christensen-appendix-a.txt` | https://research.physics.illinois.edu/QI/Photonics/theses/christensen-thesis.pdf | App. A 逐页原文（PDF p.85–87 = 论文 p.76–78）+ §4.6.2 证据（PDF p.55–56 = 论文 p.46–47），含 PDF sha256 |
| `shalm2015-channel-inputs.txt` | https://arxiv.org/pdf/1511.03189v2 | 不等式、源结构、信道输入、最优态/角、多对陈述的逐字节选，含 PDF sha256 |

模型方程**页码引用一律指论文（thesis）页**，PDF 页与论文页的对应写在提取文件头部。

引用的非附录证据：
- §4.6.2（论文 p.46–47，PDF p.55–56）：倾斜 δ 的物理来源与「周期极化晶体不出现该效应」的陈述。
- §4.3 + Table 4.1（论文 p.40，PDF p.50）：作者自己源的 CH 最优设置 `(x=0)=3.8°、(x=1)=−25.2°、r=0.26`，
  仅用于说明搜索域的合理量级（F12），**不作为任何拟合目标**。

---

## 3. 模型规格（逐式引用）

记号：偏振片角 θ 相对垂直方向；`|θ⟩ = cosθ|V⟩ + sinθ|H⟩`（F4）。所有概率都是**单次试次
（一次 sync、一个 pulse slot、一个本地时间窗）的条件概率**，条件是「源发出一对光子进入目标模式」。

### M1 态族（论文 p.76）

> `|ψr⟩ = (|HH⟩ + r|VV⟩) / √(1+r²)`，优化变量之一（论文 p.76 原句）。

论文 p.76 同时给出倾斜细化「`|ψr⟩ ∝ |H+δ, H−δ⟩ + r|VV⟩`，δ ≈ 3°」并印出 Eq.(A.2)。本重放的
主实例取 **δ = 0**（F2 给出证据），实现时保留一般 δ：
`|ψr⟩ ∝ c²|HH⟩ − sc|HV⟩ + sc|VH⟩ + (r − s²)|VV⟩`，`s=sinδ, c=cosδ`，
归一因子 `N(δ,r) = √(1 + r² − 2r s²)`。

- 一般式由 `|H+δ⟩=c|H⟩+s|V⟩`、`|H−δ⟩=c|H⟩−s|V⟩` 直接展开得到（论文 p.76–77 §4.6.2 的
  `|H ± 1.5°⟩` 记号）。
- 印出的 Eq.(A.2) 两处写成 `|V Hi`（同为 VH），且其参数化等价于把上述 r 换成 1/r；在 δ=0 时
  两种读法生成**同一族** `{|HH⟩ + r|VV⟩}`（r↔1/r 只重命名参数），故该印刷问题对主实例无效。
  见 F1/F2。

### M2 联合与边际概率（论文 p.76）

> `p(1,1|θA,θB) = tr(ρJ)`，`ρ = |ψ⟩⟨ψ|`；`p(1|θ) = tr(ρ_A S)`，`ρ_A = tr_B(ρ)`。

本重放取 `J = |θA⟩⟨θA| ⊗ |θB⟩⟨θB|`、`S = |θ⟩⟨θ|`（单透射端口的 click=1 读出，与
`instrument.json.detector_geometry = "single_transmitted_port"`、`../protocol.md` 的端口约定一致）。
实幅态下 `p(1,1|θA,θB) = A(θA,θB)²`，
`A(θA,θB) = ((r−s²)cosθAcosθB + c² sinθA sinθB + sc·sin(θB−θA)) / N(δ,r)`。

### M3 噪声装配（论文 p.77）

> `N pm(1|θ) = N ε p(1|θ) + dcr + N flr`
> `N pm(1,1|θA,θB) = N ε² p(1,1|θA,θB) + acc`，`acc = acc_u = N² pm(1|θA) pm(1|θB)`
> 「we typically set acc = acc_u」

论文这三行是**计数式**（「putting in the noise terms is easiest by writing all terms as counts,
i.e., multiplying the probabilities terms by N」），其中 `N pm(1|θ) = S(1|θ)` 是**逐试次**实测
singles。r0002 一律用**逐试次概率**表示（CH 不等式要求同一归一化下的逐试次概率）：

```
s_A(θA)         = N εA · p(1|θA) + bA          （Alice 单边逐试次点击概率；N 项 = N pm 的 ε 部分）
s_B(θB)         = N εB · p(1|θB) + bB
joint(θA,θB)    = N εA εB · p(1,1|θA,θB) + N² · pm_A(1|θA) · pm_B(1|θB)
                = N εA εB · p(1,1|θA,θB) + s_A(θA) · s_B(θB)
bA              := dcrA + N flrA（逐试次、与泵浦无关 + 随泵浦线性的背景之和）
N               = 每试次平均对数（= 论文的 N，= 2015 每脉冲对概率，F9）
pm_A(1|θA)      := s_A(θA)/N = εA p(1|θA) + bA/N      （论文的「pm」，条件归一化）
```

- **关键**：`acc_u = N² pm pm` 里的 `N pm(1|θ)` 正是**逐试次** singles（论文原句
  `N pm(1|θ) = S(1|θ)`），所以 accidental 上界 = 两只探测器逐试次 singles 概率之积
  `s_A·s_B`——这是「随机光子源」的物理含义（一次试次内两次独立点击），量纲也唯一自洽。
- 论文的 `pm` 是**条件归一化**（除以 N 后）的实测概率，故背景在 `pm` 中以 **b/N** 出现，
  与论文自己印出的 `flr + dcr/N` 结构一致（那正是同一件事的逐对写法）。
- 由此得到论文的等价形式：`joint/N = εA εB p(1,1) + N pm_A pm_B`，`S_逐试次 = N · S_条件`
  （N 固定 ⇒ 两种归一化的**最优点完全相同**，只有数值尺度差 N 倍）。判据只用逐试次形式。
- 论文的 `ε²` 是等效率特例；不等效率见 F5。
- 背景只进**边际**，accidental 只进**联合**（论文 p.77 原句：「the accidental counts only affect
  the joint probability distribution」）→ F6。
- `acc = acc_u` 是原文声明的**上界**（保守方向：噪声取大）→ F7。
- **r0001 的错误**（见 §10）：r0001 把公布的每窗背景概率直接当成条件归一化下的 `flr+dcr/N`
  使用，等价于把背景缩小了 N = 5×10⁻⁴ 倍。该错误由 D3b（论文公布的 72.5% 效率阈值）判定：
  r0001 归一化给出阈值 ≈2/3，r0002 给出 ≈72.5%。

### M4 多对统计（论文 p.77, Eq.(A.3)）

> `p_n = m^m ⟨n⟩^n Γ(m+n) / ((m+⟨n⟩)^{m+n} Γ(m) Γ(1+n))`；m=1 为热分布，m=∞ 为泊松。
> 「due to the (typically) low probability of even a single pair …… we only consider accidentals
> from two-pair events」

取 m = 1（F8）。本模型消费 `acc = acc_u`（与 m 无关），Eq.(A.3) 只用于**声明性一致性检查**：
`p₂/p₁ = ⟨n⟩(m+1) / (2(m+⟨n⟩))`，在 m=1、⟨n⟩=N=5×10⁻⁴ 时为 4.9975×10⁻⁴ ≪ 1%，
与论文 p.6「chance of getting a second event in the same Pockels cell window is negligible」一致。

### M5 目标函数（论文 p.76 Eq.(A.1) + p.78）

> `S_CH = p(1,1|0,0) + p(1,1|0,1) + p(1,1|1,0) − p(1,1|1,1) − p(a=1|x=0) − p(b=1|y=0) ≤ 0`
> 「We can then insert the expected **measured** probabilities (pm) into S_CH, and then maximize」

代入 M3 的 pm，并在定理式对称归约下展开为显式三参数目标：

```
S_CH(r,θ0,θ1) = pm(1,1|θ0,−θ0) + pm(1,1|θ0,−θ1) + pm(1,1|θ1,−θ0)
                − pm(1,1|θ1,−θ1) − pm_A(1|θ0) − pm_B(1|−θ0)
```

（(0,1) 项为 `pm(1,1|θ0A,θ1B) = pm(1,1|θ0,−θ1)`，(1,0) 项为 `pm(1,1|θ1,−θ0)`；边际在 x=0/y=0，
即 `θ0A=θ0`、`θ0B=−θ0`。不等效率时 (0,1) 与 (1,0) 不再相等，代码逐项计算。）

**与论文 Eq.(1) 的等价性（推出，非选择）**：论文 p.2 Eq.(1) 为
`P(++|ab) ≤ P(+0|ab′) + P(0+|a′b) + P(++|a′b′)`。用同一伙伴设置上的边际化
`P(+0|ab′) = P(1|a) − P(++|ab′)`、`P(0+|a′b) = P(1|b) − P(++|a′b)`（模型里单边 singles 与对侧
设置无关，即单边无信号，成立），并令 x=0↔a、x=1↔a′、y=0↔b、y=1↔b′，则论文 Eq.(1) 等价于
`P(++|ab) + P(++|ab′) + P(++|a′b) − P(++|a′b′) − P(1|a) − P(1|b) ≤ 0`，正是 Eq.(A.1)；
且 `S_CH = 论文 RHS − 论文 LHS`。故「最大化 CH 违反」= 最大化 S_CH（违反 ⟺ S_CH > 0）。
这一等价还有一个后果：目标只需边际与联合点击两项，**不需要**为「一响一不响」的联合另立约定，
模型的混合联合缺口因此不影响目标（F11）。

### M6 优化的自由变量与域

论文 p.78：「maximize over (r, θ0, θ1, N)」，其中 N 受源能力限制。本重放把 N 当**输入**而非自由
变量（F9），把 (r, θ0, θ1) 作为优化变量，域见 F12。

---

## 4. 全部自由选择（逐项引证 + 未公开部分的处置）

以下 F1–F16 覆盖本重放中每一处可自由选择的地方。凡公开来源未给出者，一律**显式登记缺口**并
给出这次采用的读法；读法只依据公开文献与量纲/对称性，**不依据任何优化输出**。

**F1 r 的约定与域。** `|ψr⟩ = (|HH⟩ + r|VV⟩)/√(1+r²)`（论文 p.76）；`r ∈ (0, 1]`。
依据：论文 Eq.(2) 把态写成 HH 主导、VV 系数 0.276/0.961，故 r 是 **VV/HH 振幅比**；
`r∈(0,1]` 是因为 θ → θ+180° 下偏振片设置等价（`A` 整体变号、概率不变），且 r↔1/r 与
`(θA,θB) → (90°−θA, 90°−θB)` 给出同一族/同一目标值（此恒等式由测试 T4 数值验证），
故 r>1 的解在 r<1 侧有同值代表。域只影响覆盖面，不影响带的方法。

**F2 δ（非共线倾斜）：主实例 δ = 0。** 证据链：
1. 该效应的**物理来源**在论文 §4.6.2（p.46–47）：3° 非共线收集角 + 切割角 141.8° 的 I 型 BiBO，
   使一个晶体的本征偏振旋转，得 `|H+δ⟩ = |H+1.5°⟩`、`|H−δ⟩ = |H−1.5°⟩`，态为
   `|V,V⟩ + |H+1.5°, H−1.5°⟩`，可见度 99.7%。
2. 同一节明确写：**「periodically-poled crystals do not observe this effect, as the crystal axis is
   not at an angle」**（另有共线几何「completely eliminates it」）。
3. 2015 NIST 源是 **PPKTP（周期极化）**：「a periodically poled potassium titanyl phosphate (PPKTP)
   crystal designed for Type-II phasematching is placed in a polarization-based Mach-Zehnder
   interferometer formed using … three beam displacers」（论文 p.3；论文 §5 同述）。
   ⇒ 按文档自身给出的机制判据，**δ≠0 对 2015 装置没有公开依据，且被文档排除**。
4. 论文 p.4 公布的源可见度是 0.999/0.996（与该效应无关的另一实测事实），见 F10。
5. App. A 印出的「δ ≈ 3°」与 §4.6.2 的逐光子 1.5°（3° 为收集角）是**来源内部的一处不一致**；
   因主实例取 δ=0，该不一致对判定无效。
6. 声明性变体（只作诊断，不进带）：δ = 1.5°、δ = 3°。

**F3 概率求值。** `p(1,1) = ⟨θA|⟨θB|ψr⟩²`（实幅，Born），`p(1|θ) = ⟨θ|ρ_A|θ⟩`，`ρ_A = tr_B ρ`
（论文 p.76 的 tr(ρJ)/tr(ρ_A S)）。`independent_replay.py` 走密度矩阵张量收缩的独立代码路径。

**F4 角度约定。** `|θ⟩ = cosθ|V⟩ + sinθ|H⟩`，θ 相对垂直偏振片（论文 p.4「relative to a vertical
polarizer」；与 `instrument.json.controls.bloch_map = "(sin(2φ), cos(2φ)) in V,H basis"` 一致）。
对称归约 `θ0A=−θ0B=θ0`、`θ1A=−θ1B=θ1`（论文 p.76 原句），与文档角集合 {4.2,−4.2}/{−25.9,25.9}
相容。全局角符号约定（θ 的正方向）对目标无影响：S 在 (θ0,θ1)→(−θ0,−θ1) 下不变（测试 T2）。

**F5 效率与不等效率延拓。** `εA = 74.7% ± 0.3%`、`εB = 75.6% ± 0.3%`，取论文 p.4 的
**system detection efficiency（Klyshko 法）**；论文 §4.2/§4.6.2 的「system efficiency ε」（论文 p.77）
即此量，故 εA/εB 分别赋给 Alice/Bob 的单边与联合项（联合用 εAεB，等于论文 ε² 在等效率时的形式）。
**缺口登记：**文档未印不等效率下的联合式；本重放采用**唯一使等效率退化到 ε² 的乘法延拓**，
物理依据是两只探测器事件的独立性。SNSPD 探测器效率 91±2%（论文 p.4）**不**赋给 ε——它只是
系统效率中的探测器分量；仅作诊断（ε/0.91 给出耦合份额 82.1%/83.1% < 1）。

**F6 背景：公布的每窗背景概率 = 模型的逐试次背景；dcr/flr 拆分不改变目标。** 取
`bA = 8.9×10⁻⁷`、`bB = 3.2×10⁻⁷`（论文 p.4：「the probability of observing a background count
during a single window is … for Alice … for Bob」，窗口 ≈625 ps / ≈781 ps）。映射依据：一次试次 =
一个 pulse slot + 一个本地窗（`instrument.json.trial_policy`），故论文的每窗背景概率就是模型的
**逐试次**加性背景 `b = dcr + N flr`（M3 的逐试次式）。**在条件归一化的 pm 中它以 b/N 出现**——
这正是论文 p.77 自己印出的 `flr + dcr/N` 结构；r0001 曾把每窗概率直接用作 `flr + dcr/N`
（漏掉 1/N），已被 D3b 判定为错（§10）。
论文 p.77 把背景拆成 dcr（不随泵浦标度）与 flr（随泵浦线性）：两者在本模型中**只以和
`dcr + N flr` 出现**，进入 s、acc 与 S_CH 的全部路径都是如此，故拆分对目标**恒等无影响**；
声明代表取 `flr = b/N, dcr = 0`，其不变性由测试 T3 数值验证。
**缺口登记：**2015 的 dcr/flr 逐项值、逐 epoch 值、每探测器 cps 暗计数均未公开。

**F7 偶然符合取上界 `acc_u`。** 论文 p.77：「As we are interested in ensuring the violation …… it is
acceptable to overestimate the noise, and therefore we typically set `acc = acc_u`」。
本重放照此取上界（噪声取大 = 违反取小，方向保守）。取法见 M3：逐试次 accidental 概率
`= s_A(θA)·s_B(θB) = N² pm_A pm_B`，即论文的 `acc_u`。未公开部分的处置：不引入任何
「精确两对偶然符合」公式；`acc_u` 是论文给出的实用形式。

**F8 m（模式数）= 1，⟨n⟩ = N = 每试次对概率。** 论文 p.77：Eq.(A.3) 的 m=1 为热分布、m=∞ 为泊松；
本文取 m = 1（热分布是「通常」情形，也是 p₂/p₁ 最大、多对占比最高的保守端）。
**关键：**模型消费 `acc = acc_u`（与 m 无关），故 m 的选择**不进入目标函数**；m 只用于
M4 的声明性检查（p₂/p₁ = 5.0×10⁻⁴ ≪ 1%，与论文 p.6 的 multi-pair 可忽略陈述一致）。
⟨n⟩ 的映射：论文 p.77「N can be interpreted as the number of pairs emitted from the source into our
desired mode」⇒ ⟨n⟩ = N = 论文的每脉冲对概率（F9）。

**F9 N = 每试次对概率，按 2015 值固定（偏离论文的 N 自由优化）。** 取 `N = q = 5×10⁻⁴`，带内
`q ∈ [4×10⁻⁴, 6×10⁻⁴]`（论文 p.4：「the probability that a single pump pulse downconverts into a
photon pair is ≈ 5×10⁻⁴」，一位有效数字；`≈` 的读法即 ±1×10⁻⁴）。依据：论文 p.77 的 N 是
**源发到目标模式的每试次对数**，而论文 p.4 公布的正是运行点的每脉冲对概率；一次试次一个
pulse slot（`instrument.json.trial_policy`）。
**对论文的显式偏离：**论文 p.78 把 N 也作为优化变量（受源能力上界约束），本重放把 N 当**输入**。
理由：论文只公开运行点对概率而不公开当年源的能力上界，故「N ≤ 上界」无法从公开值唯一确定；
把 N 固定为公布值可在不引入未公开上界的前提下完成重放，且判据带正是对 q 的整箱扫描。
**声明性变体（只作诊断）V4：**在其余输入取中心值时把 N 放开在 (0, 6×10⁻⁴] 内联合优化。

**F10 可见度维度：声明为**不消耗**（模型无该参数）。** 依据：论文 App. A 的态族只有参数 (r, δ)
与三类噪声，**没有**去极化/可见度参数（论文 p.76–77 全文无该参数）；论文 p.4 的 0.999（H/V）与
0.996（D/A）是对源的**实测**，公开渠道没有任何「可见度 → 态参数」的映射。按纪律，不自行发明
映射。后果显式登记：(i) 论文 p.4 自述 2015 的优化用到了「entanglement visibility」，故本主实例
在该处可能存在缺口；(ii) 该缺口的敏感度以**声明性变体**报告：V1 δ=1.5°、V2 δ=3°（把可见度
缺口归因到文档给出的唯一纯度机制）、V3 在联合态上插入 Werner 型混合 `ρ → vρ + (1−v)I/4`
（`v = 0.996, 0.999`）。V3 **不是**对 2015 仿真做法的声称，只是对已登记缺口的敏感度界；
三个变体都不进入判定。
另注：盒中可见度维度在模型中方差为零，故「中心 + 16 个角点」中可见度轴上的点成对重合；
脚本仍按 16 个角点逐一求值并全部登记（F14）。

**F11 目标函数 = 论文 Eq.(A.1) 代入 pm 后最大化。** 依据见 M5；等价性由边际化恒等式推出，
故无需为「一响一不响」另设联合约定（模型的 accidental 只进联合、不进边际，是论文自身的声明，
其与边际化恒等式之间的一致性不是本重放的目标）。

**F12 搜索域。** `r ∈ (0,1]`，`θ0, θ1 ∈ [−90°, 90°]`。依据：偏振片轴 180° 周期
（`A(θ+180)=−A(θ)`，概率不变；测试 T1），故 [−90°,90°] 覆盖全部不同设置；r 域见 F1。
两个公开的同类最优（论文 Table 4.1 p.40：3.8°、−25.2°、r=0.26；论文 p.4：4.2°、−25.9°、r=0.287）
只用于确认量级与网格分辨率足够，**不作为目标或拟合**：网格覆盖全域，不靠先验收窄。

**F13 确定性优化器与退化处置。** 见 §5。目标在 `(θ0,θ1)→(−θ0,−θ1)` 下不变（F4/T2），
故最优点总以 ± 成对出现；**规范代表**取 `θ0 ≥ 0`（若 θ0 = 0 则取 θ1 ≥ 0），对文档角做同一
规范化后逐分量比较（文档自身 `(θ0A,θ0B,θ1A,θ1B) = (4.2,−4.2,−25.9,25.9)` 已是规范代表）。
平局处理：网格与邻域搜索都按固定枚举顺序、只用严格 `>` 更新，故结果与并列项顺序无关且可复现。

**F14 容差带方法（verbatim，required）：**

> Pass-band method: compute the optimum (r*, θ0*, θ1*) at the center and at every corner of the
> input uncertainty box: ηA ∈ 74.7 ± 0.3 %, ηB ∈ 75.6 ± 0.3 %, visibility ∈ [0.996, 0.999]
> (in this model the visibility dimension is inert — see F10 — so its corners coincide pairwise and
> all 16 corners are still evaluated and recorded), pair probability ∈ [4×10⁻⁴, 6×10⁻⁴].
> Band = componentwise [min, max] of the optima over all evaluated box points, widened by
> ±0.05° (angles) and ±0.0005 (r). PASS iff each documented value (r, and the four angles
> 4.2°, −25.9°, −4.2°, 25.9°) lies componentwise inside the band after the same canonicalization
> as F13.

中心点取 `ηA=74.7%、ηB=75.6%、q=5×10⁻⁴、visibility=0.9975（inert）`。角带按规范代表比较：
`θ0*=band` 对 4.2°、`−θ0*` 对 −4.2°、`θ1*` 对 −25.9°、`−θ1*` 对 25.9°。
备注（**不进入判定**）：按半 LSB 传播，振幅 0.001 的舍入对应 r 的 ≈±0.0007 而非 ±0.0005；
本判据严格遵守门禁合同给定的 ±0.0005，不采用该更大的传播值。

**F15 独立实现与数值一致性容差。** `independent_replay.py` 必须：(i) 用**不同**的概率求值
代码路径（4×4 密度矩阵 + `Tr(ρJ)` 张量收缩，不用振幅直接平方）；(ii) 用**不同**的优化器
（从另一组偏移网格出发的坐标上升 + 黄金分割线搜索）；(iii) 重读 `replay.json` 并复算。
一致性容差（预先声明，S 为 M3 的**逐试次**量纲）：`|Δθ| ≤ 1.0×10⁻³°`、`|Δr| ≤ 1.0×10⁻⁵`、
`|ΔS| ≤ 1.0×10⁻¹⁰`（绝对），带逐分量在同样容差内一致，判定字符串必须完全相同。
任一项超差即 `REFUTED_…`。

**F16 判定字符串。** 只允许：
`REPLAY_CONSISTENT_WITHIN_PREDECLARED_BAND` /
`REPLAY_DEVIATION_EXCEEDS_PREDECLARED_BAND` /
`REPLAY_MODEL_INADEQUATE_<reason>`。
真值表：所有 5 个文档值都在带内 → CONSISTENT；任一在带外 → DEVIATION；
若模型无法按公开值忠实实例化（例如判据 JSON 块缺失、必需公开值缺项）→ MODEL_INADEQUATE。
输出是**候选输入**，不是 gate 通过。

---

## 5. 优化器规格（确定性）

1. **粗网格**：`r = 0.02, 0.04, …, 1.00`（步 0.02）；`θ = −90°, −88.5°, …, 90°`（步 1.5°，
   121 点）；同一网格再取 θ 与 r 各偏移半步的副本。在固定枚举顺序（r↑, θ0↑, θ1↑）下取严格最大。
   目的是不漏掉任何宽度 ≥1.5° 的局部盆地。
2. **模式搜索细化**：起点 = 粗网格最优；步长初值 = 网格步长；每步在 26 个全邻域点中按固定顺序取
   严格改进的第一个最好者；若无改进则所有步长 ×0.5；直到 max(step) < 1e-9 或 400 次迭代。
3. **规范代表**：按 F13。
4. 目标在 (r,θ0,θ1) 上光滑，Q=17 个盒点各独立做上述搜索。全部过程无随机数、无网络。
5. **D3b 阈值检验**（模型适当性验证，见 §6）：在 ηA=ηB=η 上对 `max S_CH = 0` 做 24 轮二分
   （区间 [0.60, 0.80]，每轮用同一优化器），分别取 (i) 无背景理想化 `bA=bB=0` 且 `N = q`
   （**保留信号**；`N=0` 会使逐试次式恒为零，属退化参数化，不用——见 §10 修订 r0002.1）与
   (ii) 公布的 b、N，比较论文 p.4 公布的 2/3 与 72.5%。二分点的最优点一并输出（用于 D7）。

---

## 6. 诊断输出（明确**不**作为判定依据）

- D1 重放中心最优处的含噪 `S_CH`，与文档点处的含噪 `S_CH`（差值即目标空间距离）。
- D2 三个纯度变体 V1/V2/V3（F10）与 N 自由变体 V4（F9）的最优与带（只报告）。
- D3 `ηA=ηB=72.5%`、其余取中心值时模型的最大 `S_CH`（对应论文 p.4「background raises the
  efficiency needed to violate … from 2/3 to 72.5%」的量级自检；只报告符号/量级）。
- D3b 阈值检验（F15/§5.5）：模型在 (i) 无背景、(ii) 公布背景下的对称效率阈值，与论文 p.4 的
  2/3 与 72.5% 对照。这是**模型适当性**检验（用与目标值无关的公开数字），不是通过判据。
- D4 源自身可见度自检：模型态按三种**教科书**定义算出的可见度，与论文 p.4 公布的 0.999/0.996
  并列。三个数字的含义：`coherence` = 2|ρ_HH,VV|/(ρ_HH,HH+ρ_VV,VV)（对非最大纠缠态本身 <1，
  不是论文口径）、`hv_contrast` = H/V 平行/交叉符合对比度、`scanned_fringe` = 扫描相对角的
  条纹对比度（后两者才是论文「how well the |HH⟩ and |VV⟩ terms interfere」口径；模型 δ=0 为纯态，
  在本族内取 1）。差异即 F10 缺口的量化。
- D5 耦合自检：`ε/0.91`（应 < 1）。
- D6 多对自检：p₂/p₁（F8）。
- D7 归因（**事后声明、明确不进判定**）：在其余取中心值时，把效率按共同因子 κ 缩放
  （`ηA = κ·74.7%、ηB = κ·75.6%`，κ ∈ {0.96, 0.97, 0.98, 0.99, 1.00}），报告模型最优如何随 κ 移动。
  用途只有一个：把「文档值与重放最优的偏离」在**输入空间**里量化（偏离相当于多大的效率差），
  供 gate review 判断该偏离是否落在「公布全局值 vs 设计期值」的合理范围内。
  本项不改变任何模型选择、不带、不参与判定，其声明时刻见 §10。

---

## 7. 已知缺口（不主张项）

1. 2015 仿真程序代码未公开：本重放是同一模型族的**公开方法重建**，不是原程序复刻。
2. 信道值是**全局**值，没有逐 epoch / 逐设置 / 逐探测器的值；盒只按公开 ± 与 `≈` 构造。
3. `acc` 取上界、N 取输入、不等效率用乘法延拓、背景拆分取代表——四处缺口已在 F5–F9 登记。
4. 可见度未作为模型参数（F10），且其敏感度只在诊断变体中报告。
5. 本目录不接触任何 Bell 试次事件数据（原始 uint64/HDF5/计数表）；不修改仓库既有文件；
   `../instrument.json`、`../readiness.py`、`../request.json`、`../checks.py`、`../real_family.py`、
   `../access-record.md` 与 `Lean/` 下的任何文件均未改动。
6. 重放脚本离线可跑（`replay.py`、`independent_replay.py` 无网络调用）。
7. 判据本身的 r0001→r0002 修订见 §10：修订由公开阈值检验驱动，与文档 (r,θ) 无关，
   且不改变判定结论。

---

## 8. 输出契约

`replay.py` → `replay.json`，键：`root`, `scope`, `verdict`, `bindings`（每个输入文件的相对路径 +
sha256，含 `criterion.md`、`../instrument.json`、`christensen-appendix-a.txt`、
`shalm2015-channel-inputs.txt`、`replay.py` 自身）、`fixed_choices`（F1–F16 的机读摘要，直接来自本
文件 JSON 块）、`documented`（从 `../instrument.json` 读出）、`box_points`（中心 + 16 角点，
含输入值与最优 `(r*,θ0*,θ1*)`、规范化代表、`S_CH*`）、`band`（含加宽前后）、`comparison`
（5 个文档值的逐个 in/out + 余量）、`diagnostics`（D1–D7 + 变体）、`elapsed_seconds`。

`independent_replay.py` → `independent_replay.json`，键：`root`, `scope`, `verdict`
（`CERTIFIED_…` / `REFUTED_…`）、`bindings`（含 `replay.json` 与自身）、`agreement`（逐盒点的
Δθ/Δr/ΔS 与容差判定）、`recomputed`（重算的中心最优、带、比较、判定）、`elapsed_seconds`。

---

## 9. FROZEN-INSTRUMENT（机读，唯一数值来源）

`replay.py` 解析下面两个哨兵之间的 JSON；上文的文字与下面的数值冲突时以**本块**为准（但任何
实质性改动都必须先改本文件再重跑，见文件头 A-priori integrity statement）。

<!-- FROZEN-INSTRUMENT-BEGIN -->
```json
{
  "criterion_version": "nominal-replay-r0002",
  "documented_source": "../instrument.json",
  "documented_values": {
    "r": 0.2872008324661811,
    "alice_angles_deg": [4.2, -25.9],
    "bob_angles_deg": [-4.2, 25.9],
    "published_angle_resolution_deg": 0.1,
    "published_amplitude_resolution": 0.001
  },
  "channel": {
    "eta_A": {"center": 0.747, "half_width": 0.0003},
    "eta_B": {"center": 0.756, "half_width": 0.0003},
    "background_A_per_trial": 8.9e-07,
    "background_B_per_trial": 3.2e-07,
    "background_normalisation": "per_trial (M3): b = dcr + N*flr; enters pm as b/N",
    "pair_probability": {"center": 0.0005, "box_low": 0.0004, "box_high": 0.0006},
    "visibility": {"box_low": 0.996, "box_high": 0.999, "center": 0.9975, "consumed": false},
    "snspd_efficiency": 0.91,
    "snspd_half_width": 0.02,
    "published_threshold": {"no_background": 0.6666666666666666, "with_background": 0.725}
  },
  "model": {
    "state_family": "normalized (|HH> + r|VV>)",
    "delta_deg": 0.0,
    "r_domain": [1e-06, 1.0],
    "angle_domain_deg": [-90.0, 90.0],
    "joint_efficiency": "eta_A * eta_B",
    "single_efficiency": "per side",
    "accidentals": "upper_bound_acc_u = s_A*s_B (product of per-trial singles)",
    "normalisation": "per-trial probabilities (M3 r0002)",
    "background_representative": {"flr_share": 1.0, "dcr_over_N": 0.0},
    "modes_m": 1,
    "N_rule": "N = pair probability input",
    "N_free_variant_max": 0.0006,
    "objective": "S_CH = joint(t0,-t0)+joint(t0,-t1)+joint(t1,-t0)-joint(t1,-t1)-s_A(t0)-s_B(-t0)"
  },
  "optimizer": {
    "grid_r_step": 0.02,
    "grid_r_start": 0.02,
    "grid_angle_step_deg": 1.5,
    "second_grid_offsets": [0.5, 0.5],
    "pattern_shrink": 0.5,
    "pattern_stop": 1e-09,
    "pattern_max_iter": 400
  },
  "band": {"angle_widen_deg": 0.05, "r_widen": 0.0005},
  "tolerance": {"angle_deg": 0.001, "r": 1e-05, "S_abs": 1e-10},
  "variants": {
    "delta_deg": [1.5, 3.0],
    "werner_visibility": [0.996, 0.999],
    "N_free": true
  },
  "diagnostics": {
    "threshold_check": {"eta_lo": 0.6, "eta_hi": 0.8, "iterations": 24,
                        "zero_background": {"b": 0.0, "N": 0.0005,
                                            "note": "N = q keeps the signal; N = 0 is degenerate",
                                            "published": 0.6666666666666666},
                        "published_background": {"published": 0.725}},
    "attribution_kappa": {"enabled": true, "values": [0.96, 0.97, 0.98, 0.99, 1.0],
                          "post_hoc_declared": true,
                          "note": "declared after the r0001 primary run; sizes the deviation in input space only"}
  },
  "verdicts": {
    "pass": "REPLAY_CONSISTENT_WITHIN_PREDECLARED_BAND",
    "fail": "REPLAY_DEVIATION_EXCEEDS_PREDECLARED_BAND",
    "inadequate_prefix": "REPLAY_MODEL_INADEQUATE_"
  }
}
```
<!-- FROZEN-INSTRUMENT-END -->

---

## 10. 修订史（r0001 → r0002，唯一一处实质修订）

**修订内容**：M3 的归一化映射。r0001 把论文 p.4 公布的**每窗（即逐试次）**背景概率直接当作
条件归一化下的 `flr + dcr/N` 使用；r0002 按论文自己的式子
`N pm(1|θ) = N ε p(1|θ) + dcr + N flr` 与 `acc_u = N² pm(1|θA) pm(1|θB)` 把整套噪声写成
**逐试次概率**（M3），于是背景在条件归一化的 pm 中以 `b/N` 出现（`b/N = 1.78×10⁻³`，而不是
r0001 的 `8.9×10⁻⁷`）。这是纯粹的归一化/映射错误修正，不引入任何新参数、不新增任何未公开输入。

**判定依据（与被检验的 (r,θ) 无关）**：论文 p.4 自述「These background counts in our system raise
the efficiency needed to violate a Bell inequality from 2/3 to 72.5 %」。把该陈述当作**外部检验**：
- r0001 归一化：模型在公布背景下的对称效率阈值 ≈ **2/3**（= 无背景阈值），无法产生 72.5% 的位移；
- r0002 归一化：阈值 ≈ **0.727**（与公布的 72.5% 差 0.2 个百分点），无背景时 ≈ **2/3** ✓。
所以修订由**一个与目标值完全无关的公开数字**判定。判据在 r0001 时并未预先声明这一检验，
因此在 r0002 中才把它写成常规诊断 D3b（§5.5、§6）。

**披露（必读）**：
1. 修订发生在 r0001 的 `replay.json` **已经存在**之后。r0001 的输出原样保留为
   `replay-r0001-superseded.json`，未删除、未覆盖，供复核比对。
2. 修订**不是**为了把文档值放进带内；事实上修订**不改变判定结论**：r0001 与 r0002 的最优点
   在 4 位小数内相同（r* = 0.31546，θ0* = 4.9547°，θ1* = −27.2328°），文档值在两者中都在带外。
3. D7（§6）是在 r0001 输出存在之后**新声明**的归因诊断，已在上文与 JSON 块中标注
   `post_hoc_declared`；它不改变任何模型选择、不带、不参与判定。
4. `criterion.md` 的 sha256 变化被 `replay.json` 的绑定表记录；两个版本的重放输出都留在目录内。

**r0002.1（同一轮内的第二条小修订，仅涉及退化诊断参数化）**：§5.5 的 D3b「无背景」分支原本写作
`b = 0 且 N = 0`；在逐试次形式（M3 r0002）下 `N = 0` 使所有逐试次概率恒为零（S ≡ 0），是退化
参数化而非物理情形。改为 `b = 0 且 N = q`（保留信号，accidental 随之处于公布量级、相对贡献
~4×10⁻⁵）遂使该分支成为真正可判读的「无背景理想化」。此项修改只改一个**诊断**的定义：
不触及任何模型选择、公开输入、目标函数、带或判定；其触发原因是 r0002 首次运行时 D3b 的零背景
分支返回了退化值（恰为二分上界 0.8），即模型在这一参数化下 S 恒等于 0。
