# 原始原子响应到同源读出的忠实物理实现

rf0001 消费已签合法 source effect，连接独立原子前向响应与探测器实现域。
原子谱 `(b,r)` 从登记的原始 pulse 生成；读出目标不进入原子传播器。
源 effect 用来生成实现它所需的控制轴和探测器参数。该逆构造认证源模型的物理实现，
不把已签相容证人当作实际精确参数。

## 原始响应与原生可行条件

`O=mu I+uX+zZ`，`g=sqrt(u²+z²)>0`。原子响应满足 `0≤r<b≤1`，令 `delta=b−r`。
其原子效应的谱为 b、r，trace 为 `b+r`；控制轴由 source 坐标生成：

```text
axis=(-u/g,-z/g)
k=g/delta
d=(1−mu−k(b+r))/2
eta=k/(1−d)。
```

source 的 `u²+z²=g²` 支付轴的单位长度，精确符号轴不被近似角度替代。
坐标恒等 `E_click=dI+kJ` 保留同一局部 source effect；原子 effect 的构造自身合法。
生成的探测器参数合法，当且仅当两条原生谱条件成立：

```text
g(b+r)≤(1−mu)(b−r)
g(2−b−r)≤(1+mu)(b−r)。
```

这两式直接消费原始谱和源坐标，不把已完成 realization 或合法 detector witness 作为输入。
它们等价于 `d≥0,k≥0,d+k≤1`；正 source gain 与正谱差再生成 `k>0,d<1,0<eta≤1`。
两式相加还给 `g≤b−r`，低 contrast 谱被拒绝。

## 完整响应包络的精确验收

给定严格分离的包络 `b_lo>r_hi`，两条可行 slack 都随 b 增大而增大、随 r 增大而减小。
系数分别为 `1−mu−g,−(1−mu+g)` 及 `1+mu+g,−(1+mu−g)`；
其符号由原 compact effect 锥自产。因此检查同一最坏角 `(b_lo,r_hi)`
可支付包络内全部响应的可行性。最优角仍失败才排除整个盒；最坏角失败而最优角通过时保留未定。

两条 native 条件的左右边均非负，平方不会改变等价性：

```text
(u²+z²)(b+r)²≤(1−mu)²(b−r)²
(u²+z²)(2−b−r)²≤(1+mu)²(b−r)²。
```

由此用 source 的有理坐标和响应包络端点完成 exact Fraction 验收，不以 sqrt 的数值近似决定可行性。
检测因子、背景和效率的显示区间另由有理 gain 平方的向外根包络运输。
完整可行性已支付的物理锥允许与 `d≥0,d+k≤1,eta≤1` 相交；交集保所有生成实现。
这些显示区间不替代精确生成公式，也不被当作共同 Cartesian 会员证书。

## 不同物理谱保持同一 joint law

同一控制轴下，原子 effect 的最大和最小谱恰为 b、r。
原子 effect 相同遂推出两响应分别相同；不同响应谱必给不同原子 effect。
两个分别可行的谱，各自生成合法 detector 实现，并精确恢复相同 source effect。
双侧每个局部 effect 的恢复使原完整 joint 概率和 source/current/next 权重恒等。
原所有 prefix 统计因子随之保留，既有非空 source 证书不重拟合。

不同 raw pulse 字段本身不能证明响应不同。数值证书要求已生成的 bright 或 dark 包络严格分离，
再消费上述谱的 injectivity。理论 raw pulse 的实际响应由首次双传播及已付 af0001 数值误差机制承担。
所有脉冲谱的来源绑定、包络宽度和符号顺序先于 realizer 验收。

## 独立认证与来源消费

`ReadoutPulseRealization.lean` 认证 native 充要条件、正检测因子和合法效率、
坐标恢复、完整包络最坏角、平方等价式，以及不同可行谱的忠实实现。
`PulseCertification.lean` 直接消费这些口，独立核两侧完整概率、同源 current/next、
非空不同谱控制与低 contrast 反控。`pulse_certify.py` 核所有 owned 声明与 consumer 的
完整 type/value 新依赖闭包，复用原 source 与 df0001 已付边界；已付源不重编。
严格 trust0、warning-as-error、asyncoff、单线程及标准三公理的具体证据由
`pulse-certification-first.json` 保存。

默认 `--check-only` 消费冻结回执与当前 source 哈希，不启动 proof build 或原子传播。
override 仅接受相同回执的其他位置。数学响应控制、登记 raw pulse 与旧相容证人各保来源身份；
正式数值首次结果只在新科学合同冻结后生成，成功、拒绝或失败均保原输出。

探测器参数按各 role 生成；同一侧两 setting 的共用 CEM 背景／效率身份不由本构造认证。
actual 唯一参数、实际 raw pulse 输入身份、额外统计覆盖与 controller 推进字段保持 false。
