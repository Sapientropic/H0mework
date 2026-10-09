# RHA0032：原完整自由流的 Chebyshev 连续曲线

目标是RHA0031登记层级的完整局部TP自由流，最终供同源动态响应锚使用。
原source/root、row0、whole-ledger及tick16→17保持；旧冻结输出不改。

先由原构造器恢复已签RHA0027入口，选择Alice原bank的第一枚factor，读取它的真实
retarded-cut终态和原Gaussian source。起点由原gate减flight／emission origin生成，
终点为原完整gate末端的相同限制，覆盖120ns。该非空完整factor是声明源的计算样本，
不作为已识别实际硬件输入，也不重算已付pump／入口残差。

科学代码与合同提交后才生成新曲线。节点只收到raw source和完整初值的handoff，
只生产不可信数值曲线，不构造或伪装source-issued类型。Mac恢复原closed owner，逐字段
认回同一factor、source和时域，再检查完整残差。新误差与原整份入口E分别保存。

曲线在每个1ns片段使用degree64 shifted Chebyshev basis `T_n(2u-1)`，u在[0,1]。
NumPy提案用40阶Taylor时间步取Lobatto样本；步长不超过1/16ns且数值column-norm相位
不超过3。该数值预算不支付数学误差。全部自然recycling、完整33坐标及原H／R／Gaussian
保持；不重归一trace，不假定提案PSD。输出gzip JSONL，完整row预算为12,000,000。

检查器直接在Chebyshev基中计算 `dC/du-Delta*(L_quiet+g L_drive)C`，不将量子曲线
转成单项式。所有系数Hermitian，整数／有理source列、量化价、原phase价和Gamma价
沿用原完整density源。`|T_n(2u-1)|<=1`使整个片段的Duhamel残差价不超过各系数范数之和。
首／末读口为交替和／同号和；拼接差单独计入。导数65列和Gaussian degree40与curve
degree64的2665个product列由独立整数多项式递推核验。

Gaussian原场不在远端切零。令 `g=g0 exp(-b u-c u^2)`、r=|b|+c，使用20阶指数
Taylor polynomial。`exp(r)<=3^ceil(r)`给完整余项界；原g0幅值与scalar误差共同乘入，
因此原短片段r<=1/2的表示限制不再阻止远端完整门。转入Chebyshev后，绝对值小于2^-96
的scalar系数可移入明确支付的uniform余项，量子矩阵系数不据此删除。
Lean核验基的统一界、首末读口、残差系数范数界与指数growth majorant；原CP收缩及
标准Taylor余项沿原source数学合同使用，不登记为新kernel-checked全局演化定理。

首样本的验收为全120ns新trace-norm误差不超过初值entry-norm的10^-8。
超限仍保存已核误差与全部片段，不能登记为通过；数学检查失败也保存首失败回执。
样本通过后才铺开完整因子银行。完整登记instrument、实际响应差和唯一参数仍由
同发生下游生成，不能以一枚自由流曲线代付。

ComputeNode使用已有锁定Python3.12.14／NumPy2.3.5环境；首单元独立state、低并发、
真实内存申报，不重启或改动其他负载。归还产物再经领域检查，传输hash不代替残差。
不读事件档案、ETH或publish，不push、不发布、不外联。
