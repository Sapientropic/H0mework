# cal0001：源生发对量与具名Klyshko读出

2026-10-01。科学合同、来源与各程序/Lean候选先提交，再执行。
gw0001与全部旧criterion/程序/结果保持。本版生成校准读出，不重新拟合成员或最优点。
属于从属optical producer/readout，root、whole-ledger、tick及原最优门禁保持。

## 共同源与校准端口

消费gw0001的raw两偏振几何pair源及pure-loss透射；phase不改变inclusive number测量。
公共OR七坐标种子按原固定N=5转换生成raw参数，不能读取held-out或CI后调整。
三种校准制备分别为原dual-pol、同H增益的pure-H变体、同V增益的pure-V变体；
变体是具名候选校准支路，不赋予公开实验身份。
端口为每侧包含H/V的local bucket，无偏振分析器；接受1或5个fresh-vacuum pulses。
分别报告signal-only与原每pulse独立OR背景；未公开的扣背景规则不能默认为已核身份。

PGF G(zH,zV)从原numberMass生成。
pair-at-least-one=1−G(0,0)=tH+tV−tHtV，
exactly-one=(1−tH)(1−tV)(tH+tV)，mean-pair=tH/(1−tH)+tV/(1−tV)。
三个量分别报告，不能自动把实验的近似q或历史coincidence倒推q当作同一量。
公开q≈0.0005没有测量参考面、估计式或误差带；只登记来源角色，不生成验收带。

single-pulse signal无点击读出为
A0=G(1−TAH,1−TAV)，B0同，
AB0=G((1−TAH)(1−TBH),(1−TAV)(1−TBV))。
先加入指定OR背景再取窗口次幂；S_A=1−A0^N、S_B=1−B0^N、
J=1−A0^N−B0^N+AB0^N。K_A=J/S_B、K_B=J/S_A。
herald为零时报告UNDEFINED_ZERO_HERALD，不能输出伪效率或NaN。

## 独立源求和与条件约束

主路径以精确有理PGF生成读出。独立路径直接求h+v≤6的原numberMass，
逐占据数乘真实无点击loss权重，保留原质量并加[0,tail]，再生成窗口与条件ratio。
不调用主程序/概率或以有限态重新归一。三支、两窗口与两背景语义全部报告，不选最吻合支路。

matched单偏振、单pulse、signal-only支路另从同源PGF生成精确bucket Klyshko式。
n=t/(1−t)，U=TA+TB−TA TB：
K_A=1−(1−TA)(1+n TB)/[(1+n TA)(1+n U)]，
0≤K_A−TA≤2n。Bob交换A/B。
该条件下与公开ηA∈[.744,.750]、ηB∈[.753,.759]的包络交集另列，
只裁决指定校准身份，不外推为实际NIST身份、另一数值bug或理论否定。

公开η是Klyshko系统效率，制备、端口、calibration pump及扣背景规则未绑定。
最大态HV=.999±.001、DA=.996±.001是k=1测量区间；.995是DA下端，非独立Γ字段。
本版登记这些角色，不以cosφ=.995替代最大态完整fringe读出。
单对Gram的完整扫角与固定D/A对比定义不同，不外推为完整Fock visibility定理。

正控覆盖vacuum、纯H/V、unit/zero losses、双偏振、1/5窗口及背景OR。
反控覆盖漏尾/前缀重归一、mean与at-least-one混同、零herald伪效率、
把pure-loss透射直接等同bucket条件效率、以window计数和替代any-click、错误校准身份。
双方数学包络须相交，主精确值须落入独立包络，且全部读出在[0,1]。
不修改旧统计域，不优化目标，不读取trial/count archives或发送外联。
