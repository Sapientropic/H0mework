# 完整探测器实现与微硬件共同资格

同一局部读出 `O=mu I+uX+zZ` 的点击效应为 `E=(I−O)/2`。
原子电离效应写为 `J=(trace I+xX+zZ)/2`；Lean 以 `CompactReadoutEffect`
表示其 `trace−1,x,z`。认证范围是原 compact XZ carrier，合法锥恰为 `0≤J≤I`；
正 k 的源 XZ effect 迫使逆像也在 XZ 中，不增加独立目标概率字段。
探测器前向作用 `E=dI+kJ` 由原子效应、背景 d 和检测因子 k 构造源 effect；
`k=(1−d)eta`，`d≥0,k≥0,d+k≤1`。该生成 effect 直接进入原 source/current/next Born 口。

## 完整逆像与退化层

令 `g=sqrt(u²+z²)>0`、`m=(1−mu−g)/2`、`M=(1−mu+g)/2`。
全部实现恰为 `0≤d≤m`、`M−d≤k≤1−d`。
此域自身保证 `k>0,d<1`，显式逆像
`J=(E−dI)/k`、`eta=k/(1−d)` 生成合法原子 effect，并恢复同一输入 effect。
任何已有同坐标实现的原子 effect 与该逆像相等。该逆读认证完整分解集合，
不选择实际唯一硬件，也不宣称所有合法 J 都有登记 12 态 pulse 实现。

`k=0` 时源 effect 精确退化为 `mu=1−2d,u=z=0`，原子 effect 任意。
`g=0,k>0` 时原子 effect 精确为 scalar；`g>0` 的非空控制拒绝 k=0。

## 共同下界与原始控制 cap

完整纤维给出

```text
eta lambda_max(J)=(M−d)/(1−d)≥g/(1−m)=2g/(1+mu+g)。
```

交叉相乘后的非负余量为 `(1−M)(m−d)`，两分母由原合法锥及 g>0 保证为正。
效率和原子最大响应各自不超过 1，因而二者也分别不低于同一下界。
效率最小与原子响应最小可由不同分解达到；不能把两投影最小值当作共同实现。

原整个置信域的 gain 下界 G 和 bias 区间给 `B=max(|L|,|U|)`。
`H=2G/(1+B+G)` 对两个 raw-to-click polarity 都成立，直接生成
`eta lambda_max(J)≥H`、`d≤(1+B−G)/2`。
原 CSV 点击字典未被选择，名义光学控制不代付该字典。

独立前向域 `lambda_max(J)≤min(1,7 area²/4)` 沿用 af0001 的固定 chart 12 态模型。
它与上述乘积界共同给出 `eta min(1,7 area²/4)≥H`、`eta area²≥4H/7`。
Lean 认证该运输；前向动力学包络继续由原 af0001 来源与算术证书承担。
其证明责任不被改写为已经完成新的 Lindblad 内核形式化。

反向使用原始控制盒上界时，`s=eta_U min(1,7 area²_U/4)∈[0,1]`，
源 gain 由这些控制上界生成 `min(1,(1+B)s/(2−s))`。
分母至少为 1，零响应及饱和 cap 都保留。四个 cap 直接消费旧 cp0003 联合资格。
原控制 cap 的有理 pullback 用来核这个 commuting 关系；profile 通过不会被读作实际 pulse 会员。

## 数值消费者与来源

主实现以平方锥核逆像，独立端自行重建原子锥；二者各以 exact Fraction 运算。
主端枚举半平面边界交点，独立端裁剪闭合探测器三角形。
退化线段与点保留，两极性分支皆空才排除整个原子响应盒。
trace 与 contrast 的盒外包可放宽相关性，非空域保持必要资格口径。

八项逐角色与六项严格 joint-maximum 约束只消费已冻 cp0002/id0001/cp0003 结果；
run、角色顺序及已提供的 factor sequence 保同一来源。
cp0003 ray 由各自角色组的最大 B 运输，Alice/Bob 的原 gain 对称阈值不强迫新硬件界相同。
32 个理论原子响应盒、64 个极性分支消费 af0001 已核 pb/pd；原包络与精确概率域相交后使用。
理论样本不成为 actual 运行参数，未新增事件、拟合、量子传播或置信预算。

## 独立内核认证

`DetectorCertification.lean` 直接消费完整 fibre、生成逆像与唯一逆读、共同产品界、
polarity-free 域运输、原始控制 cap、原 source/current/next、非空与退化控制。
`detector_certify.py` 核所有 candidate-owned 声明及独立 consumer 的 type/value 依赖闭包，
只复用已有 source-certified 声明与完整 paid base graph。已付原 source 不重编。
候选及独立消费者使用 trust0、warning-as-error、asyncoff、单线程；只接受标准三公理。
具体声明数、依赖闭包及源绑定由 `detector-certification-first.json` 保存。

默认 `--check-only` 读取已冻回执、旧 source 证书及当前源码哈希；不启动 proof build 或数值 producer。
override 仅接受相同回执的另一位置。actual 独立锚、actual 唯一参数、任意 J 的 pulse 实现、
新置信覆盖与 controller 推进各保持原 scope。
