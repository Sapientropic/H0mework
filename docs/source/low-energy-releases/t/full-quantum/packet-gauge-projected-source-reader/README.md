# 原均值与connected三项的整球读数

本包补齐已经闭合的两source腿与reader接触的固定P分解，供最后两条传播项逐sector相加。
保持原ψ、P=|ψ〉〈ψ|、S01/dx1、z=w=6c(1−i)、p_out=0、R=B和物理measure。
它是源输出的从属consumer；不改root、准备、frame、原作用或已签结果。

## 同一个投影逐项消费

令Q依次取I、P、I−P，分别生成raw、mean、connected。Q只作用于量子Hilbert因子，
原场矩阵／reader作用于字段因子，故二者交换。Q与所有实际参数、时间微分和积分交换，
且||Qv||≤||v||。正交性同时给每个原有序核及其导数的精确身份

`raw = mean + connected`。

原CosineCurvature已经生成各sector在两个probe均为零的真实外q Hessian，包括mean的
非零二阶项。其实际两probe运输证明由向量差、Cauchy–Schwarz及全时间位置矩组成；
把各向量同时作用固定Q，所有界保持。因此原整轻球的统一复误差δ分别控制三个sector，
不是用raw减connected后重新猜一个mean。

设H_Q(0)为上述实际零probe Hessian，C(k)为已签原native系数。对每个单位外方向n，
整个原轻球都满足

`|H_Q(k)[n,n]−H_Q(0)[n,n]|≤δ`，`0<C_min≤C(k)≤C_max`。

原source腿的窗口固定，真正二次系数是

`S_Q(n)=½∫ball C(k) H_Q(k)[n,n] d³k/(2π)³`。

除二来自Hessian到Taylor系数，cos半幅没有再乘一次。零probe矩阵的mixed项为零，
方向式为`(1−n1²)H_perp+n1² H_parallel`。正C区间与真实球measure直接生成receipt的
各对角及任意单位方向界。

## 同一reader余项也保持投影

原reader接触使用`A(k)=F_coframe(k)⊗Bhat_k ψ`。三个sector分别为
`A_Q=(I_field⊗Q)A`，所以A及其所有mixed导数的整个向量范数均收缩。
这也保持已付的D²A(0)精确范数估计；不把投影后的交叉误认成独立正交项。

原coframe F(0)=0、Q0自伴、Qj反自伴、真正球体／flux相消和球上奇项消去，全部逐项
适用于A_Q。因此每个sector的reader二次系数都满足同一个已签界

`|R_Q(n)|≤3.686515414428545…×10⁻²⁶`。

这里仅消费这个完整向量上界，未复用raw的数值mean或将任何均值删掉。
真实尖窗一次项仍属于各sector原展开，本包处理其二次系数的归并。

## 直接可用的结果

receipt.json保存三个sector每个对角的source Hessian、实际Taylor系数以及加reader后的
严格有理区间。raw及mean在全部单位方向仍严格负；connected在e1方向严格正，e2/e3
方向严格负。对一般n，使用同一张量方向式及δ即可，不声称所有connected方向同号。

任意mixed项由真实对称Hessian的polarization和上述单位方向误差界控制，再加原reader
统一界。所有显示小数向外舍入；raw／mean／connected的精确和身份不因各自的区间误差
而改变。最后两条传播腿必须按相同sector加入，这三项不替代总响应。

本包无新Lean声明或公理，精确有理计算消费已签源多项式、完整半轴积分和向量投影论证。
