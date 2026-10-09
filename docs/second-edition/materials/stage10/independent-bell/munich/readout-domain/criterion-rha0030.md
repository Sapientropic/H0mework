# RHA0030：共享 CEM 背景的完整历史域

实际仪器的两侧 cutoff 背景 `a=d_A,b=d_B` 各作一次独立 Bernoulli OR，与同一
源的真实出生 effect 组合。参数在每个原 run 内共享；量子态、APD 队列、控制和真实
出生概率可以依赖全部过去。原 paired-source 的 pre-outcome context／准入合同保持。

把同一历史条件态的真实出生 joint 写成 `r00,r01,r10,r11>=0,sum r=1`，则

```
q00=(1-a)(1-b)r00
q01=(1-a)(r01+b r00)
q10=(1-b)(r10+a r00)
q11=r11+a r01+b r10+ab r00
p_A-a=(1-a)(r10+r11)>=0
p_B-b=(1-b)(r01+r11)>=0
q11-b p_A-a p_B+ab=(1-a)(1-b)r11>=0
```

这些等式来自原 `C_s=d_s I+(1-d_s)B_s` 的同一次作用，不要求固定 reduced state。
三个逐拍变量为 `Z_A=X-a,Z_B=Y-b,Z_AB=(X-a)(Y-b)`。八个固定 tilt
`t=1/128,1/64,...,1` 分别给 `F=1-t Z>=0`，其每拍源条件均值不大于1。
在 current outcome 之前按原 `(herald,setting_A,setting_B)` 选择 context，其余拍 factor=1，
故乘积是非负 supermartingale。全部原序 prefix 可由 Ville 同时覆盖。

每个固定真参数／真编码有 `2 run * 8 context * 3 face * 8 tilt=384` 个过程。
本合同独立 family alpha=`1/20`，capital threshold=`7680`。四种未知局部 binary
双射编码是置信反演的四个参数分支：每个固定真编码的误排概率均不超过1/20；不把
错误编码的过程一并宣称为真源 supermartingale，也不额外把四分支 union 读成四次测试。
对连续参数反演同理，不对参数点作 union。旧统计合同和预算保持，域的交集不另称为同一95%域。

背景域初值为 `[0,1]^2`。默认 quadtree 最大深度7；各节点以四角的 exact rational
factor 最小值给整片双线性 rectangle 下界。源 Bernstein 恒等式核验该下界。
factor 不严格正时跳过该测试族。Decimal80 log 下界向下量化为192-bit dyadic；
threshold log 向上量化。同一实际 prefix 的四种 raw outcome 计数与这些系数作 exact
integer dot；达到 threshold 才排除整个节点。其余子域保留，四个未决 sibling 可以合并。
每个 branch 必须完整覆盖初始正方形，不把保留叶登记成 source membership。

每个 context 的前128个 prefix 和覆盖整段的至多256个等距索引作为搜索提议；浮点矩阵
乘积只提议实际 prefix／face／tilt，不支付排除证明或最大值声明。
独立消费者不导入主 factor、tree、Decimal 或搜索：从另一原 parser 重建全部
原 prefix 计数／时钟／行地址，另以 interval product 求整片 factor 下界、整数 atanh
显式尾界核 log，再核每枚排除与完整 quadtree 覆盖。完整记录 commitment 与 RHA0029 保持。

Lean 认证有限 source joint、全部 factor 的非负／supermean 与连续 rectangle 下界；
概率论中的条件乘积和 Ville／有限 union 使用上述标准论证，不登记为已 kernel 应用的全局概率定理。
实际硬件唯一参数、完整 source membership 和动态响应锚仍由同发生恢复链生成。
原 source/root、row0、whole-ledger 与 tick16→17 保持；不读 ETH，不改 publish，不外联。

科学文件、数学认证和合成控制先提交冻结，随后才对两枚原 ZIP 执行本合同；首 attempt
及结果独占创建，失败也保留。原冻结输出不修改。
