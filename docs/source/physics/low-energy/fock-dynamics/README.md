# 原有限CAR、物理时间消费者与因果变换

五个Lean模块把已存在的占据算子接到实际规范脉冲和有限源Hamiltonian，保留原prepared及其电流密度。它们是原[占据响应](../occupied-response/README.md)与其因果谱的通用严格消费者；原12维系数和完整Euler回写由对应精确源程序支付。

## 原占据算子

`Algebra`从已有完整CAR直接生成

`[a_i,dΓ(H)]=Σj H_ij a_j`。

对由源框架W、V生成的字段，还证明`{a(W)_i,a†(V)_j}=(WV†)_ij`及其原时间交换子。两腿可不同，没有将带Q插入的交叉相关函数误作同一字段的正自相关。

`Response`把真正的波函数`HasDerivAt`送入原oneParticle，证明原Schr方程和电流导数：

```text
ψ̇=−iHψ  →  d_t oneParticle(ψ)=−i dΓ(H) oneParticle(ψ)，
d_t〈dΓ(B)〉=i〈[dΓ(H),dΓ(B)]〉。
```

其中H的Hermitian条件用于原电流的两侧导数；B一直是原source读数，没有将它改名为H。

## 实际时间与原脉冲

`Hamiltonian`从有限H生成`exp(−itH)`，证明H自伴时幺正、原配对保持、全部t的实际导数，再把这个真实演化送入同一Fock Schr和电流交换子消费者。没有把所需轨道本身作为premise。

`Pulse`直接消费正式`YangMills.Response.Action.pulse`、同一`Stage10.Runtime.configuration`和`FullPairing.prepared`。它保持原振幅`2 ψpulse(0)=actual.matter`，证明全部插入参数t的旧Fock范数恰为1，并从原规范力生成t=0的Fock导数。原`Exchange.current`精确等于旧CAR电流读数；其双侧导数仍是原current的导数。

该pulse的参数是原规范插入参数；完整背景物理时间使用Hamiltonian消费者及[原H12系数／轨道桥](../occupied-response/README.md)。两者没有混称一个全场传播定理。

## 正阻尼的因果边界

`Retarded`证明任意实E、rate与正damping下，真实半轴积分存在且

```text
∫₀∞ exp([−damping+i(E−rate)]t) dt = i/(E−rate+i damping)。
```

同一定理消费任意有限复谱权重，实际积分与求和交换由可积性支付。因此源生成的有限时间谱能够给出因果Fourier–Laplace响应，不需任意指定普通矩阵逆的极点一侧。

## 验收

五正式模块在`Lean/SaturationMonoid/PhysicsCore/LowEnergy/FockDynamics/`。[独立认证](audit/certification.md)签收45个公开口及6个独立Lean消费者，共51项标准公理，并从原48规范插入和非零原时间谱消费到同一原Schur响应。正式迁移后五模块、原axiom检查和独立消费者再次trust0／werror通过，见`promotion.json`与`promotion-*.log`。

本组消费原有限CAR和原prepared；全场量子真空、统计测度及真空圈积分不由有限演化或单次电流响应自动供应。原source／action／controller及已签收的有符号kinetic配对均不变。
