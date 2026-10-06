# cp0001：原完整置信域的响应参数外包

消费rd0001/c0002原完整置信域与id0001偏置外包，从官方原四outcome计数生成每run八个
相关量区间、四个canonical gain与双误判率区间。覆盖整个原置信域，固定law证人不充当误差条。
source、公开试次选择、fixed-run合同、四个过程、全部prefix、阈值40与联合预算1/20保持。

## 由原full component生成profile

原混合过程E=E_full/2+E_A/6+E_B/6+E_comp/6，故原E<40蕴含E_full<80。
E_full的原Dirichlet(1/2,1/2,1/2,1/2) numerator为

```text
J = product_context [product_cell (2n)!/(4^n n!) / (N+1)!].
```

在一个context固定p=q00+q11=(1+C)/2，分别在even／odd组内按exact经验频率
最大化likelihood；其他context按四cell的exact MLE最大化。该无约束最大值覆盖
source全joint的分母，不假定各格参数可独立实现。

令logE_MLE=logJ−sum_context,cell n log(n/N)，n_e=n00+n11、n_o=n01+n10，则

```text
log profile(p)=logE_MLE+n_e log(n_e/N)+n_o log(n_o/N)
               −n_e log p−n_o log(1−p).
```

profile≤E_full，且导数为(Np−n_e)/(p(1−p))。
MLE左侧严格递减、右侧严格递增，两枚外端profile≥80支付外侧整段排除。
每个具名context要求两parity计数均正；零cell按0log0=0处理，观测零mass源点仍排除。
八个相关区间均为整个同一个CS的必要外包，不另分配alpha，不由Cartesian外包宣称联合可达。

## 同源响应运输

内核从原SettingFamily的完整32格joint恢复C，生成
`|C−mu_A mu_B|≤gain_A gain_B≤gain_A,gain_B`及canonical channel的误率运输。
两bias区间的四corner乘积生成[ML,MU]，相关区间[CL,CU]生成
`K∈[CL−MU,CU−ML]`。故两侧gain均至少为
`max(0,CL−MU,ML−CU)`；每个own-setting取其全部四context下界的最大值。

gain上界为`1−dist(0,bias_interval)`。
canonical e0/e1分别外包于
`[max(0,−mu_upper),(1−gain_lower−mu_lower)/2]`与
`[max(0,mu_lower),(1−gain_lower+mu_upper)/2]`。
完整effect像的负gain与ideal-label分支保持；canonical代表不选择实际标签身份。

## 程序与首次裁决

主程序使用原Directed80位向外log，外端初始化2^-80、2^-160、2^-320、2^-640、2^-1280，
36步有理数二分只提议端点；两端明确达到log80后才签收。
独立程序从原计数重建Dirichlet numerator和MLE，使用已签整数atanh／显式尾界240bit；
按需升至320、384bit，仅核端点和MLE及精确导数，不运行二分或调用主公式。
Fraction独立重算所有corner乘积、16个相关区间及八组响应范围。

程序、合同、同源response证明和独立证书先提交，随后独占生成主／独立首次结果与attempt。
结果无论成功或失败均保存。最终consumer及readiness不打开事件档案、拟合或生成新统计量。
`parent_confidence_hardware_envelopes_certified`登记整个原CS的必要外包；
硬件唯一身份仍沿id0001完整等价纤维裁决，fb0001固定law范围单独消费。
