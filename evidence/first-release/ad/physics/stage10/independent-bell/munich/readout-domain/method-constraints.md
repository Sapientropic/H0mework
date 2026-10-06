# Munich：完整读出联合域的公开方法约束

原 `positiveSmoothUnifiedSource / SpinPair.visit 10 / tick16→17`、whole-ledger及原Born族保持。
本接口是完整source/effect的从属仪器输运；方法字节与页码见[来源绑定](sources.json)。
主域使用全部合法XZ轴，以及每run、每侧、每local setting的合法非对称读出通道；
同一local setting跨两个herald共享通道。所有率保留`[0,1]`，不从公开结果缩窄先验范围。

## 直接改变域选择的事实

| 原方法 | 支付的结构 | 数值角色 |
|---|---|---|
| PRL p3、Fig2b：795nm态选择、473nm电离，F=2再用780nm激发；自发回F=1会降低测量fidelity | 态选择与碎片探测是不同环节；完整读出须容纳两种误分类 | 不提供F0/F1置信界 |
| PRL p3/p4：离子η约0.90–0.94、电子η约0.75–0.90；至少一个碎片点击记up、无点击记down，总碎片探测效率≥0.98 | 固定binary读出规则及检测对象；不按无点击删event-ready试次 | 器件描述范围，不是95%联合CI；不映为F0/F1≥0.98 |
| PRL p3/p4：两个setting切换不同AOM和偏振readout beam；γ是spin角、激光线偏振角γ/2 | 每local setting可有自己的assignment通道；原XZ轴族直接消费半角投影 | 不把名义最优角例子变成逐run角度误差带 |
| PRL p4：碎片探测效率在两侧及不同run间有差别 | 两侧、两run分开参数化 | 不跨run借用校准或合并通道 |
| SI §I.B、Fig1：任一成功BSM都触发同一state-measurement序列；QRNG选择local AOM | 跨herald共享readout有同一控制序列的名义依据；herald改变源态而不另选readout命令 | 不是跨herald误分类率相等的独立实测CI |
| SI §I.C、§IV：run开始固定CEM窗口；激光/CEM故障整段排除，日常维护检查激光、磁场、BSM偏振 | 固定选择及维护责任沿用原官方valid pairs | 整run固定通道是具名条件模型；方法未支付零漂移数值界 |

`F0=P(recorded 0 | ideal 0)`、`F1=P(recorded 1 | ideal 1)`是完整态读出正确率。
碎片η条件于产生了对应电离碎片；态选择、漏电离、误电离及背景仍在其上游。
因此高碎片η既不确定F0/F1，也不证明其对称。方法中的timing误差、单点误差条和器件范围
不承担新统计域的95%覆盖预算。

## 制备与几何

SI §I.B规定光抽运到`52S1/2,F=1,mF=0`，再激发到`52P3/2,F'=0,mF'=0`；
四类BSM coincidence在固定120ns窗口生成两个herald。原Ψ±及spin投影由
[原控制桥](../source-methods.md)固定。正文所述时间重合、重相位及偏振补偿是制备方法，
这里不将它们变成完美制备率或visibility置信下界。

这些绑定方法没有给出与两个指定run匹配的独立conditional F0/F1或source-visibility联合置信域。
主域保持原pure Ψ±的具名制备合同；额外herald-dependent source noise会改变域，须另行命名，
不能把depolarizing模型描述为已经校准的实际机制。
缺少误分类的数值校准不妨碍现在生成和裁决整个合法读出联合域。

## 全合法率仍留下完整联合约束

对每个local通道，令`u=F0−F1`、`v=F0+F1−1`，其合法域精确等于`|u|+|v|≤1`。
`u`生成记录边缘偏置，`v`生成对原source相关的读出收缩。全部四outcome由同一口生成：

```text
P_h(s,t | a,b) = [1+s u_Aa+t u_Bb+s t(u_Aa u_Bb+v_Aa v_Bb C_h(a,b))]/4,
C_minus = −a_x b_x−a_z b_z,
C_plus  =  a_x b_x−a_z b_z,
s,t in {−1,+1}.
```

两个herald及remote setting共享各自local边缘。记centered相关`D_h=E_h−u_A u_B`，则
`−(D_minus+D_plus)/2`与`(D_plus−D_minus)/2`分别为Z、X坐标的outer product。
每个2×2矩阵都具有零determinant，并共同满足各local setting的长度界。
完整域因此不是任意32格概率表；未知连续角与raw二元编码不取消这些联合约束。
跨herald共享、两侧local通道乘积和整run固定率均登记为受裁决的名义仪器合同。

## 共同visibility的精确吸收

两侧合法readout矩阵为`R_A,R_B`，`m_A=R_A(1/2,1/2)`，`T_A`两列均为`m_A`。
原两herald的概率表`P_h`均有half边缘。对任意`w∈[0,1]`，

```text
R'_A = w R_A+(1−w)T_A
(R_A tensor R_B)[w P_h+(1−w)U4] = (R'_A tensor R_B)P_h.
```

新通道仍合法；正确率写成`F'0=wF0+(1−w)(1+u)/2`、
`F'1=wF1+(1−w)(1−u)/2`，保持`u'=u`并给`v'=w v`。
这保持全部outcome、两个herald及原current/next，不是相关函数的近似。
每run共同depolarizing visibility不扩大当前全合法readout像，主域无需这个冗余参数。

原blind理论构造、旧裁决和封存ETH材料保持。公开统计曝光已知；
新合同不声明认知未曝光，也不以未公开校准或新实验作为执行前提。
