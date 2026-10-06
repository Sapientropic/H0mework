# id0001：最大可识别量、完整等价族与原置信域投影

原source／visit10／whole-ledger／tick16→17和rd0001/c0002完整joint相容证书保持。
本合同是同源逆读与参数域生成，不改原经验检验，不读取原事件档案或重新拟合。

## 最大可识别量与完整规律纤维

完整joint law唯一给出四个local bias，以及
`X_ab=(C_1ab-C_0ab)/2=u_Aa*u_Bb`、
`Z_ab=mu_Aa*mu_Bb-(C_0ab+C_1ab)/2=z_Aa*z_Bb`。
两套合法compact effects给出同一个完整law，当且仅当这些量全部相同。

在X00、Z00非零的regular层，所有同law参数由两个非零实尺度生成：

```text
u_A'=s*u_A, u_B'=u_B/s,
z_A'=t*z_A, z_B'=z_B/t, mu'=mu.
```

合法尺度域完整由四个cone给出。令S=s²>0、T=t²>0，Alice的约束为
`u²*S+z²*T<=(1-|mu|)²`，Bob的约束为
`u²/S+z²/T<=(1-|mu|)²`，并保全部四种尺度sign分支。
这生成完整regular纤维，不以几个替代点代付覆盖。
原通道的signed gain／ideal-label分解沿旧完整source image保存；canonical positive-gain
通道是有固定规范的代表，不宣称实际通道标签已被识别。

两run的已签primitive law逐项恢复上述quotient，生成(s,t)连续矩形[19/20,21/20]²。
四个worst-case平方不等式支付整个矩形的合法性。
同时生成isotropic (s=t=21/20)及anisotropic (s=21/20,t=19/20)替代证人；
原八维Born独立核其全部32格不变。isotropic族连全部测量轴也保持，而通道gain平方改变。
相同q使全部既有forecaster分母、factor序列及prefix财富恒等，无需重跑事件。
给定law的完整纤维不是实际概率已知的声明；经验不确定性仍由原整个置信域承担。

## 原整个置信域的bias外包

parent财富`E=E_full/2+E_A/6+E_B/6+E_complement/6<40`蕴含E_A<240、E_B<240。
每侧按own setting汇总全部已冻结四outcome计数，保全部原分母。
该侧global pooled Jeffreys numerator为`B(N0+1/2,N1+1/2)/B(1/2,1/2)`。
对一个setting的p=(1+mu)/2固定，另setting的likelihood上界取其exact binomial MLE。

```text
profile_E(p) = pooled_Jeffreys_numerator /
               [p^n0 (1-p)^n1 * other_setting_MLE_likelihood].
```

所有parent置信点必满足profile_E<240。其log在p_MLE=n0/(n0+n1)左侧下降、右侧上升；
导数为n1/(1-p)-n0/p，符号由(n0+n1)p-n0给出。
主Decimal和独立integer atanh／factorial各核两个rational外端logE>=log240及MLE内部。
36次确定性bisect只选端点，精确向外区间决定端点是否可签；zero-support端点沿原规则排除，
不epsilon平滑。初始positive边界固定尝试2^-80、2^-160、2^-320、2^-640、2^-1280。
八个bias区间是同一个parent置信域的同时必要投影，预算仍1/20；不另选择新检验。
它们覆盖整个parent域，不把两枚拟合证人或固定law纤维当作经验区间。

## 输出与验收

科学代码及本合同先提交，再计算新的bias统计输出。主／独立首次输出独占创建。
冻结parent输入为primitive-witness-c0002、两套c0002 first、verification与原criterion。
内核证明核完整quotient、尺度生成及regular converse；独立source contraction核全部替代law；
两区间算法交叉核全部八个端点。consumer只读冻结回执，直接登记已识别量及未消去的尺度。
原仪器相容门不因参数非唯一重开；ETH／publish／私有校准／新实验不进入本合同。
