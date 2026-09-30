# 原准备态与π边界的完整有序词

五正式模块已独立认证；默认 trust=0／warnings-as-errors 的全部模块、公开声明、
七个原消费者与六个独立声明通过，精确源实验及正式迁移复验通过。原source、action、clock及Stage10保持。

## 由原源生成的加权读数

原归一准备位于Λ²；P6输出与该准备实有的完整正配对正交。原π边界
`K_C=−i Vol(C) spinScale S C0(C)`保留外幂分级。因此，正式ClosedLoops产生的
`Expansion(A,A0)`可直接给出实际准备态读数相等，包括在左侧乘入K_C。
这份结果消费原态，未以裸trace替代它。

`Words.fullWord_oneParticle`从完整dΓ算子乘积生成实际一粒子作用。
`weightedWord_native`在完整Fock词作用之后才返回Mother和同一Stage10。
`Native.SourceStep`只输入原正阻尼谱参数及规范方向；实际可逆域由Retarded支付。
任意有限有序原规范传播词的K加权读数等于自由对角词；在这些词间插入原单向
scalar箭头，准备态读数为零。

`Transfer`保留正式StateResponse的共同incoming0／中间两通道载体。
两条完整connected词相减后才读取；源分级同样简化最终读数。
`sourceReader_original`直接从原χ、ψ和C0证明规范reader的源幅度4。
`Scalar`将原raw scalar Hamiltonian force及raw independent-dual reader接入同一
箭头类，证明相应共同transfer标量腿的读数为零。

这些是所述分级算子类的完整词与谱读数；物理响应的具体p／−p分母仍由原
方程生成。本包没有指定连续圈测度、平稳真空或一般观测不可检测性。

## 可区分的原算子

- 单位完整词的原态读数为1，裸trace为252。
- K加权exchange词读数为`−N spinScale`；原幅度与体积没有被丢掉。
- 70个raw scalar插入读数为零，但原标量方向仍产生非零开放输出。
- 换用canonical real scalar reader，原70×70矩阵保留36个非零项。
  该reader含反向项，不能消费前述raw箭头定理。
- 原`Contact.ReturnChannel`的source-generated完整返回复合仍可检测开放输出；
  Lean直接消费者保留其已证非零原读口，未将暂时不可见提升为理想商。
- 在中途插入准备态投影会改变完整词，不能把压缩当乘法同态。

## 验证

源码 `Lean/SaturationMonoid/PhysicsCore/LowEnergy/FullQuantum/PreparedLoops/{Source,Words,Native,Transfer,Scalar}.lean`。
`check.py`、`Audit.lean`、`Consumer.lean`、`focused.json`及`logs/`保存默认限额
严格回执。`compute.py`检查原源hash，重建K、原C0／Y／规范顶点和真实完整逆，
逐词作用于完整Fock态，保存85个有序词、70个scalar词及上述正反控制。

```sh
python Verification/physics/low-energy-phenomenology/full-quantum/prepared-loops/check.py
uv run --offline --with sympy python Verification/physics/low-energy-phenomenology/full-quantum/prepared-loops/compute.py
```

[独立认证](audit/certification.md)签收 53 项标准公理声明、348 个完整加权词、三组全 252 双逆、全部 2,304 个 transfer 条目和 16 个完整共同载体响应。原 ReturnChannel 的完整读数为 −1；错误中间投影使其变零。
