# Munich：运行、AOM控制与实际响应锚

[硬件来源绑定](hardware-anchor-sources.json)认证两次指定运行的具名控制表。
原source、`SpinPair.visit 10`、current16→17及完整joint置信域保持；
控制身份与实际effect身份分别消费证据。

## 两run的具名控制表

[Garthoff 2021官方论文](https://xqp.physik.uni-muenchen.de/publications/files/theses_phd/phd_garthoff.pdf)
第3章开头（正文p39／PDF51）明确介绍2016-04-15与2016-06-14两次Bell运行。
Table3.1（p40／PDF52）给出下表；Fig3.1（p43／PDF55）与§3.3.2（p44／PDF56）
将随机输入经两条AOM接到该控制表。表中α是激光偏振参数，以弧度表示，φ均为0。

| 输入 | 原文readout polarization χ | α |
| --- | --- | --- |
| A=0 | V | 0 |
| A=1 | cos(π/4)V−sin(π/4)H | π/4 |
| B=0 | cos(−π/8)V−sin(−π/8)H | −π/8 |
| B=1 | cos(π/8)V−sin(π/8)H | π/8 |

这是两run的名义setting／AOM身份。原子处实际偏振、有效gain和完整误判率仍由响应生成责任决定。
同文pp19–20／PDF31–32明确允许光学双折射和对准误差改变实际响应。

## 基底与结果符号

AppendixB TableB.2（p142／PDF154）定义
`u_x=(u_z+d_z)/√2`、`d_x=−i(d_z−u_z)/√2`，其中`u_z=|F=1,mF=+1⟩`、
`d_z=|F=1,mF=−1⟩`。这是原source基底`0=u_x,1=d_x`使用的形式定义。
Eq2.9–2.11（p17／PDF29）保留该文自己的控制读口：

```text
χ = cosα V − exp(−iφ) sinα H
B = cosα d_x + exp(−iφ) sinα u_x
D = sinα d_x − exp(−iφ) cosα u_x
```

该文p40把至少一个片段点击记为`+1`，无片段记为`−1`。
原source的bool谱标签对click用`True (−1)`、dark用`False (+1)`；两种符号约定相反，
须沿各自具名谱投影运输。以上公式与旧[控制桥](../source-methods.md)的光学H/V角chart分别保存；
同名ket的形式表达不代付不同文献中实际光学参考系的身份。

官方CSV说明把`setting`称为选择测量基底的随机数输入，把`result`称为测量结果，
没有给出序列化token到上述bit／click的完整字典。新控制表不认证这一尚未绑定的序列化映射，
也不修改冻结程序的编码分支。

## 公开档案的实际载荷

2026-10-04核对[Zenodo记录API](https://zenodo.org/api/records/22936124)、
[versions](https://zenodo.org/api/records/22936124/versions)与
[latest](https://zenodo.org/api/records/22936124/versions/latest)：versions总数为1，
latest仍为22936124，updated为2026-09-24。载荷为两个原ZIP、`README.txt`、`Bell_website.pdf`；
相关identifier仅指向PRL DOI。原CSV字段及档案字节沿[原来源绑定](../sources.json)消费。

[原SI §I.E](https://journals.aps.org/prl/supplemental/10.1103/PhysRevLett.119.010402/BellTest-supplement.pdf)
另述TDC记录全部光子、随机bit、CEM点击及序列位置；此TDC流未列入上述inventory。
ZIP的`local timestamp`用于识别所用随机数，不是ion／electron到达时刻或两个独立片段bit。

## 原始参数生成绝对锚

[Garthoff 2015](https://xqp.physik.uni-muenchen.de/publications/files/theses_master/master_garthoff.pdf)
§3.3.4（pp56–58／PDF56–58）将模拟功率轴乘3.1以匹配bright校准曲线，
解释为原子处有效功率偏离名义聚焦估计。这是该校准比较的角色，不是2016两run的功率修正证书。
§3.3的12态生成器仍可从原始脉冲参数λ产生`J_i`；两个setting不必使用目标F0／F1。

若同一侧两setting共用背景d和片段注册率η，令`k=(1−d)η`，
`E_D,i=(1−d)I−kJ_i`、`τ_i=Tr(J_i)`。完整law读出的偏置满足

```text
μ_i = 1 − 2d − kτ_i
τ_0 ≠ τ_1  ⇒  k = (μ_1−μ_0)/(τ_0−τ_1)
d = (1−μ_i−kτ_i)/2
η = k/(1−d),  d ≠ 1
u_i = −k Tr(J_i X),  z_i = −k Tr(J_i Z)
```

不同trace的原始响应可把已识别的两个偏置转成绝对尺度。
该机制要求`J_i`由独立原始λ生成、共用d／η成立、恢复值在物理域内；
置信区间输入生成参数域，不被替换为精确点。
若两setting仅改变角而共用同一旋转协变脉冲，`J_1=UJ_0U†`使trace相等，
该除法退化；角度表本身不生成这枚绝对锚。
上述公开材料没有绑定两run各AOM在原子处的完整场幅、偏振、频偏、脉冲波形与器件参数；
这些量保留为前向生成域的原始变量。名义140ns／1.24µW与contrast0.938在Garthoff2021 p20
引自Ortegel2016，不提供这一缺失的逐run参数盒。
