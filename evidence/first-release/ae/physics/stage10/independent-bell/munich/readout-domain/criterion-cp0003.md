# cp0003：完整联合响应资格域

原source、固定run仪器合同、全部原序试次、四个财富过程及联合预算1/20保持。
cp0003使用原source的乘积强口，将四个局部effect的响应放进同一资格域。
所有旧criterion、source、首次结果和门禁保持字节身份。

## 同源四响应的共同限制

`ReadoutResponseBounds.centered_correlation_product_bound`由原32格概率生成
`|C_hab−mu_Aa mu_Bb|≤g_Aa g_Bb`。effect仅依赖side与ownsetting，两个herald共享。
四cap的固定顺序为Alice0、Alice1、Bob0、Bob1。对于任意`c∈[0,1]^4`，
假设各`g_i≤c_i`，全部八个context同时满足：

```text
radius_ab = c_Aa c_Bb
C_hab ∈ [product_mu_lower−radius_ab, product_mu_upper+radius_ab]
p_even ∈ [max(0,(1+product_mu_lower−radius_ab)/2),
          min(1,(1+product_mu_upper+radius_ab)/2)].
```

偏置乘积来自id0001同一个原置信域的四corner外包，没有新统计预算。
资格域同时保留cp0002逐项界；不能把其Cartesian盒当成共同合格集合。

## 全八context likelihood

使用cp0001已签全局Dirichlet numerator。每个context的parity质量在允许区间上
取exact经验MLE的clamp；其两个parity组内分布各取MLE。全局常数只计一次：

```text
log joint_profile(c) = log E_full_at_unconstrained_MLE
                    + sum_all_eight [parity_MLE_loglikelihood−clipped_loglikelihood].
```

放宽分母覆盖每枚`g≤c` source的真实分母，故joint_profile≤实际E_full。
原E<40与full权重1/2蕴含E_full<80。核joint_profile(c)≥80即排除整个向下矩形
`0≤g_i≤c_i`，覆盖任意同域source。增大任意cap时允许域嵌套扩张，profile非增。
profile<80表示通过本项必要检查；完整source相容性由原joint消费者承担。
两parity观测计数均正；观测概率0作无限财富，不加epsilon。

## 预声明结果与控制

每run只生成三条ray的36步有理阈值bracket，顺序固定：

```text
uniform(t) = [t,t,t,t]
alice(t)   = [t,t,1,1]
bob(t)     = [1,1,t,t].
```

起始0、1须分居log80两侧。主程序Directed80位区间；必要时160／320位。
独立整数atanh／显式尾界核六bracket、十二端点及九十六项context likelihood，
不重做二分。gap≤2^-36定位放宽profile的阈值，不宣称真实source参数极值锐性。
每ray下端同时认证：uniform中至少一项gain更大；alice／bob中至少一个本侧setting更大。

两种控制在同一profile中如实保存：原合法primitive证人的gain用48bit平方根向上外包，
该cap须通过必要profile；将四cap设为cp0002四个下界最大值向上取整至10^-6，
逐项通过旧gain投影，其joint profile是否拒绝按实际结果登记。
该形似控制用于展示共同资格与逐项资格的差别，不把它充当实际硬件。

科学合同、程序及独立源／数学审查先提交，再独占生成主／独立first与attempt。
成功、拒绝或执行失败均记录；source binding涵盖旧置信输入与全部新科学文件。
readiness消费联合必要资格、原完整joint非空及原identification等价纤维。
硬件唯一性仍按原纤维事实登记false，原law的身份不由canonical代表选择。
intake不打开事件、不拟合、不生成新端点；override只移动同字节回执。
