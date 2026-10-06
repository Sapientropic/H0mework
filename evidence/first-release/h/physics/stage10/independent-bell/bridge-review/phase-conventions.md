# 相位／编码桥诊断

**旧名义矩阵计算自洽，但它没有通过官方控制定义的闭环检查。**
本次只构造一般数学桥，不选一个 flip 使数据通过，不改 r0002 的 34 个冻结输入或原结果。
未读取 cap 外事件、fig2 或 fig5 数据；已见试次也没有用于估计本文参数。

## 揭盲前本可检查的矛盾

独立 custodian 核实：[官方 SI](https://media.springernature.com/original/springer-static/esm/art:10.1038%2Fs41586-023-05885-0/MediaObjects/41586_2023_5885_MOESM1_ESM.pdf)
Eq.7（印刷 p.2／PDF p.3）为 `S=E00−E01+E10+E11`。
旧条件 `γ=0, θ_geo=−π/4` 及已用脉冲约定给出 `E=(1,1,−1,1)/√2`，所以 **S=0**。
这与 [Methods](https://www.nature.com/articles/s41586-023-05885-0) 将该名义几何角描述为最优设置不相容。
此检查只用控制／理论定义；无需 100000 次数据。它要求补全映射，不能指定哪一个符号应翻转。

## 明确约定的一般模型

计算基 `gg,ge,eg,ee`；`Y=[[0,−i],[i,0]]`；`R_φ(t)=exp[−it(cosφ X+sinφ Y)/2]`。
按 Eq.14 的顺序取 `ψγ=(|eg⟩+exp(−iγ)|ge⟩)/√2`。直接矩阵计算得到

```text
Txy = [[cosγ, −sinγ], [sinγ, cosγ]],  Tzz=−1
C(α,β) = cos(β−α+γ)                    # γ 是正号
```

交换 Eq.14 两个基矢的定义会改变 γ 的号；这不是可混用的简写。
这里 γ 指硬件准备／相位参考中的相对相位，不给固定 SpinPair 源偷偷增加一个拟合槽。
从固定源到该准备的 phase operation 必须进入 instrument map。

令两站 fixed 轴的物理方位为 φA、φB；optional 轴为 `φi+hi π/2`，`hi=±1`。
fixed／optional 的 Bloch 角分别为 `fi π/2`、`oi π/2`，先 fixed 后 optional：

```text
δ = γ + φB − φA
C00 = fA fB cosδ        C01 = −fA oB hB sinδ
C10 = oA hA fB sinδ     C11 = oA oB hA hB cosδ
```

`pulse_model.py` 还接受一般角度、顺序、setting bijection 和逐 setting 读出符号，直接算四结局概率。
drive register 到物理轴使用显式 `φphysical=φzero+h·φcontrol`；函数不推断 offset。

## 两格反号不能唯一定位原因

| 数学改动（默认其余条件固定） | 对四相关系数的作用／独立约束 |
|---|---|
| δ→−δ | 只反转 C01、C10；可来自准备相位或几何相位改变 |
| γ→γ+t，Bob 两脉冲物理轴同时减 t | 全部概率不变；源相位和 Bob 相位不能由此测量分别识别 |
| 两站 optional 相对 fixed 都反转符号 | 同样只反转两格；应由已知输入态的脉冲校准判别 |
| 两个 setting bit 同时互补 | 同样两格反号；官方 0=block、1=pass 已明确，不授权这样改 parser |
| x→(−1)^a x、y→(−1)^b y | 同样两格反号；官方 g=+1/e=−1 与已解包编码已明确，不授权修改 |
| 全部脉冲角统一反号／两站常数读出符号同时反号 | 在此 quarter-turn 模型中不改变表，不能用作两格修复 |
| 两站顺序都改为 optional→fixed | 理想 quarter-turn 下 settings 失去区别；不是同一 CHSH 装置 |

完整复共轭同时改变 γ、所有脉冲相位与角度，概率不变。只翻某个角度不是完整 convention change。
已有表头／SIV 说明可固定原始编码；仍需 controller-to-record 的独立 truth table 来验证实际转换链。

## θ_geo、Eq.16 与 Eq.15

在上述默认 signs 和官方 Eq.7 下，`S=2(cosδ+sinδ)=2√2 cos(δ−π/4)`。
因此 Eq.15 的 `S=2√2 cosθ_SI` 使用相对最优点的有效相位；它不能单独给出 `θ_SI=θ_geo`。
只由 cos 还存在正负／周期分支，不能拿已观测 S 消除分支。
Eq.16 为 `θ_SI=Γ+ΦgeA−ΦgeB`，Γ 是 Eq.14 的四个准备脉冲相位组合。
[控制 packet](../custody/r0002-storz2023-metadata.json) 没有把合并的 Φge 逐 `(a,b)` 展开成
这里的 signed pulse matrices；所以不能直接把 Φge 当作本模型的 observable azimuth。
官方还报道 Fig.5 相位轴已作 160° offset 修正，且约每小时重新校准。这个已核实的方法信息
没有本批次 uncertainty 或 record join；本文不将 160° 当 γ、θ_geo 或可用校准参数。

## 可检验的独立校准合同

1. 固定 Eq.14 的基序／γ 符号、Eq.7 mask、每个 setting 的完整 ordered unitary，以及
   drive phases→共同物理轴的转换；先通过“名义最优设置→理想 S”闭环，再冻结预测。
2. 用与 evaluation 分离的原始 phase-reference／两正交 quadrature 记录固定有向有效 δ 及
   置信域、时间有效期和每次校准对应的试次范围。只需识别可观察组合 δ，不强迫分别识别 γ/θ。
3. 以已知准备态独立检查 signed π/2、pulse order、0/1 switch 与 g/e 解码；保存原 controller
   settings、四 packed codes→CSV 的 truth table、raw records 与 epoch join。
   不可忽略的 pulse-angle 误差要通过完整矩阵传播，不能自动当作 scalar visibility。
4. 分别提供独立制备／噪声与 g/e assignment 记录，并给共同 coverage 的 nuisance region。
   若只采用 depolarization＋独立非对称 assignment，模型明确为
   `qxy=¼[1+xηA+yηB+xy(ηAηB+κAκB v C)]`，其中 `η=F0−F1, κ=F0+F1−1`。
   此式已用完整四概率 channel 独立核对；不覆盖任意相关噪声，也不从 test 拟合 v 或 phase。

该 ansatz 下官方 `Sobs=2ηAηB+κAκB v Sideal`。旧表若给 `Sideal=0`，增加 visibility／
assignment 参数不会恢复名义最大违背；必须先解决控制映射，而不是用噪声参数吸收符号错误。

旧 100000 试次可作 L0 桥诊断；修订后的确认性检验必须另登记未被此诊断使用的裁决面。
复跑：`python3 -m unittest discover -s Verification/physics/stage10/independent-bell/bridge-review -p 'test_pulse_model.py' -v`。
**12 个纯合成测试通过**，包括全部 64 组 signs/handedness、每格四结局及官方 Eq.7 检查。
