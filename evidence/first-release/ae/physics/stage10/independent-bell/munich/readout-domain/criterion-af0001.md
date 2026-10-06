# af0001：原始脉冲自产原子响应与全域读出面积约束

固定原source、visit10、material row及current16→17；本项是从属物理producer，
直接消费者为独立响应锚逆读与原置信域的参数约束。原统计预算、编码、全部冻结输出保持。

## 登记的动力学域

Garthoff2015 Eq3.5–3.13定义12态、7条Hamilton边、18条公式列明的自然衰变和7条电离jump。
文字的20条与公式18条分别保存，不补造跃迁。每个pulse段只改变R/C/A与长度，
同一instrument的bright/dark控制chart保持；任意有限矩形序列覆盖，不增加未登记的ground外流或横场。
原子常数使用该具名模型的名义中心，不作为两run实际输入的置信界。

```text
tau=Gamma_D1*T， R=Omega12/Gamma_D1， C=Omega56/Gamma_D1， A=Gamma_ion/Gamma_D1
Delta/Gamma_D1=3258/23， Gamma_D2/Gamma_D1=30333/28750.
```

普通频率与角频率的2pi转换显式保留；H非对角为Omega/2，失谐对角为−Delta。
原qubit的两个初态为1／4，电离态为3。Hamilton图与rank1 jump自产32-real Hermitian闭包，
原qubit的offblock coherence不产生电离population，故J在bright/dark基底对角。
全部概率、谱宽与响应均由原始控制生成，不以目标F0/F1、gain或概率表作输入。

## 误差证书

主实现用Directed Decimal80的32维稀疏Taylor，独立实现用240bit整数的完整144复坐标action。
默认阶80、步长乘induced norm≤4；每段尾界
`input_norm*Rstep^(n+1)/(n+1)!/(1-Rstep/(n+2))`，必须核Rstep<n+2。
Hermitian误差由exact Lindblad CPTP的trace-norm收缩逐段相加；失谐不造成全局指数放大。
主32坐标向trace-norm用保守因子32；独立端用entrywise norm。
独立平方根系数替代的Hamilton误差由Duhamel界支付。

输出保留未经剪裁的主数值包络；交叉验收核两包络与精确物理域的共同交集，
正确的零边界包络不因微小负端点被拒，也不以epsilon替换0。
所有p_bright/p_dark包络宽度≤10^-50，trace包络含1。
独立全144action逐列核32闭包和3072个符号系数。

## 原置信域反推原始控制

同一生成器对初态i=1／4有P=1−rho_ii，原jump没有从i流出，
positivity与Hamilton row自产`Pdot≤sqrt(7)R sqrt(P(1-P))`。
对sqrt(P+epsilon)积分再令epsilon趋0，得

```text
p_ion≤P≤7/4 (integral R dtau)^2
gain=(1-d)eta|p_bright-p_dark|≤min(1,7/4 area^2)
原整个CS gain≥G ⇒ area^2≥4G/7.
```

该界对所有登记cycling／ion强度与有限段成立，不以有限样本代付全域。
cp0002逐项下界与cp0003共同max界共同消费；沿用原1/20，不增加alpha。
这是登记12态动力学域的必要参数约束，不识别唯一实际波形或器件值。

## 冻结的首次样本与验收

程序及合同先提交，再独占生成primary／independent first。所有样本为理论控制，
不用当前公开统计选择pulse或调节原子参数：

| id | 固定pulse (tau,R,C,A) |
|---|---|
| no_readout | (1/5,0,4,3) |
| weak_readout | (1/5,1/4,25,83/25) |
| response_0 | (1,5,25,83/25) |
| response_1 | (1,6,25,83/25) |

双实现验收四个响应、12个概率／trace包络、每pulse3072个restriction系数。
response_0／1的trace是否严格不同按实际区间登记，作为前向锚的构造控制。
原剂量约束另从已冻原置信证书生成，两run八个individual及六个joint-max界按source绑定消费。
理论pulse不成为实际控制盒；独立实际锚可用性、实际唯一硬件及新内核GKSL证明字段保持false。
