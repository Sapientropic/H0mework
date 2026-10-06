# cp0002：共享局部响应的四context联合profile

原source、仪器合同、完整置信域、试次选择、四个过程与联合预算1/20保持。
修订消费同一side／ownsetting的effect跨两个herald及两个partner setting共享的结构，
将四context的likelihood一起用于响应下界，不相乘四个单context profile。
cp0001及所有旧source／首结果／门禁字节保持。

## 同一源生成共享约束

旧SettingFamily只按ownsetting存储local effect。ReadoutResponseBounds的原32格correlation
对所有h,a,b满足`|C−mu_A mu_B|≤gain_A,gain_B`。
因此假设某side／ownsetting的gain≤G，会同时约束对应四context：

```text
C_context ∈ [product_mu_lower−G, product_mu_upper+G]
p_even ∈ [max(0,(1+product_mu_lower−G)/2), min(1,(1+product_mu_upper+G)/2)].
```

product_mu由id0001整个parent置信域的四corner区间生成。旧source强口已支付共享责任，
不增加source参数、经验假设或新Lean wrapper。

## 联合likelihood下界

完整E_full的原Dirichlet numerator及全部context MLE与cp0001相同。
对选中的四context，parity质量在上述区间内取exact MLE的clamp，
组内两个cell按经验频率最大化；其余四context取原四cell MLE。
这个不要求source可独立实现的最大分母覆盖每枚低gain source的真实分母。

```text
log profile(G)=log E_full_at_unconstrained_MLE
             +sum_selected_four[log parity_MLE_likelihood−log clipped_parity_likelihood].
```

全局常数只出现一次。G增大时约束区间嵌套扩张，最大likelihood非减，profile非增。
核profile(Glo)≥80后，整个`0≤gain≤Glo`从原CS排除；原E<40仍蕴含E_full<80。
每context要求两parity计数正；观测mass0作无限财富，不以epsilon代替。

## 确切验收

主程序Directed80位，初始Glo=0、Ghi=1，36步有理二分只提端点。
两端必须分别达到log80与严格低于log80，bracket gap≤2^-36。
此gap描述profile阈值定位，不宣称实际gain在完整source域的极值达到该界。
最终gain下界取max(新Glo,cp0001旧界)，canonical两误率从同一µ区间运输。
每role逐项核gain下界不降、e0/e1上界不升，严格改进的数量如实登记。

独立程序复用原已签整数atanh／显式尾界，用自己的四context区间、clamp和likelihood总和，
240bit起，必要时320／384bit。核16端点、每端四context、eight误率组及所有源绑定，
不重做二分、不调用主公式、不打开事件、不拟合。

科学合同、程序、数学审查先提交，再独占生成主／独立first与attempt。
正或负结果均保存；最终consumer只消费已冻端点。
readiness登记`shared_response_profile_certified`与whole-parent-CS必要外包，
硬件唯一性、实际ideal标签身份及profile极值sharpness均保持独立字段。
