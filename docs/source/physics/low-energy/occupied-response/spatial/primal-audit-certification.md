# 独立认证：原 holonomic primal 物质算子

Verdict: **certified**。`PrimalLift / PrimalSymbol` 两个冻结候选未发现声明或来源缺陷。

两文件与 17 个公开口 fresh 默认预算 `--trust=0 / warningAsError` 全部 EXIT 0。独立 `Consumer.lean` 的 9 个构造／消费者同样通过；26 个口的公理集合均包含于 `propext / Classical.choice / Quot.sound`。未修改候选或根文档，未提交。

## 真实场与普通导数

`tripletField` 将普通 `BasePoint → MatterFiber` 系数函数通过原 `tripletLift` 写入原 configuration 的 matter 字段。coframe、spin/gauge 连接、scalar 和其余字段保留实际值。

源 holonomic 导数使用原 `matterCoordinateEquiv`，其底层是原 `Module.Free.chooseBasis` 坐标。`tripletCoordinateMap` 使用这个**同一**等价，而非把自然物理 Gram 坐标偷换成原存储坐标；复线性映射转为实线性后，真实 `HasFDerivAt.comp` 生成原字段的坐标导数。

因此唯一微分前提是输入系数函数的普通 `HasFDerivAt`。协变导数由该链式法则、原 spin lift 与已认证 P286 外幂作用相加生成，没有接受协变导数或方程成立凭证。

独立消费者构造实际 affine profile 及其连续实线性导数，支付全部四个坐标方向，再将它交给原 holonomic 字段和完整物质算子。另对每个方向单独放入原 sourcePrepared，证明原字段导数非零；时间及三个空间方向均非空。

## 原 scalar 与完整 Yukawa

`tripletField_yukawa_zero` 读取 `actual.scalar`、原零 chart 的 scalar/matter frame 及修复后的 right-chiral Yukawa，最后消费原联合标量在完整 triplet 上的外幂零作用。它没有把 scalar、Yukawa 矩阵或其零性当作 premise。

`original_primal_differential` 的左侧是修复后的完整 `generatedContinuumDiracDualMatterVector`，即原 kinetic 加原 Yukawa；两个块生成后才得到 triplet jet 的嵌入。

独立程序从原四个 scalar wedge 项重新生成 Λ²→Λ⁶ 的完整映射，再放入原 right-chiral 252 维位置。内部秩为 5、完整 right-chiral 秩为 10；其在原 triplet 上为零，但完整算子非零，保存了一个值为 1 的外部矩阵元见证。此零性没有推广成整个理论 Yukawa 为零，也没有加入 Y†。

## 原时间、连接与 Hamiltonian

`PrimalSymbol` 从实际连接证明时间连接为零、空间连接等于已付的 `occupiedConnection`。`originalDiracConstant` 直接由原 spin/gauge 连接总和生成。

原共转常项含 `+(ω/N)γ0Q`，而 `Nγ0` 相乘给出 `−ωQ`。移去这项恰好恢复

`Nγ0 originalDiracConstant = H_original(0) = h0+ωQ`。

同一原 `γ0²=−I` 与真实时间 inverse gamma `γ0/N` 给出时间系数 **−i**；空间系数为 **−i Hj**。主口准确为

**`Nγ0 D_original ψ = tripletLift[−i ∂t f + H_original(0)f − i Σ Hj∂j f]`**。

它对任意给定普通可微系数函数和任意点成立。独立 affine 消费者把全部 12 个值和四组导数作为独立普通 jet 输入交回原物质算子，未补目标微分方程。

## 独立全 252 维检查

`independent_check.py` 从原 Gamma、原颜色 Pauli、原 spinScale/gaugeScale/lapse 及原外幂 slot 作用重建完整 B、四个 Cμ 和 right-chiral Y，逐项吻合已认证 FullPhase 源系数。

它同时检查完整 **252×60** 个场值／导数列：

`NΓ0 [(B+Y)F, C0F, C1F, C2F, C3F]`

`= F [H_original(0), −iI, −iH1, −iH2, −iH3]`。

原实际 seed 在四个独立导数方向的原 Dirac 输出均非零，其范数平方分别为 `250/27, 4, 4, 4`。原实际时间速度 `−iωQ ψ0` 与原连接常项精确相消；把共转零速度直接当作原时间速度则不能相消。换成 h0、翻转时间或空间 i 号均触发反控制。

## 精确责任与证据

该包签收固定 actual 其余字段时的完整原物质微分算子身份；没有将这份身份签成九类方程的全部反作用解。原时间、原 scalar、原独立 dual 字段及 Stage10 root/current/next 保持。

证据见 `focused.json`、strict 日志、`trust-summary.json`；`Consumer.lean` 支付真实 affine 配置和各方向非空 jet；`independent_check.py`、`independent-check.log`、`independent-receipt.json` 支付完整 252 维系数、Yukawa 与原相位反控制。
