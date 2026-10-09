# 实际 Yukawa 严格正谱 excess 独立认证

Verdict：certified。固定同一原 root、实际 mixed-spectator CAR 源与 N3 half-density 输入；已有 charged 三粒子、actual first-Y 和 scalar61 签收保持。

## 最强机器口

`LowEnergy.YukawaResolventDetection.actual_generated_candidate_Y_excess dual` 原生生成 `f : ScalarTest`，`f(sourcePoint)=1`，随后对所有有限 `F`、两种 cause、所有 `μ>0` 同时成立：

- 实际 unforced `correctionMeasure F (candidateTest dual f) … univ > 0`；
- fullY 频率积分严格大于 `(π/μ) × 2‖scalarLp 3 f‖²`。

`f` 与 `q = candidateTest dual f` 均先于这些选择，不随频率重设；最终口没有调用方非零证书或 correction 预算前提。

## 证明链与源身份

1. 已验收的原四项 vacuum／γ₀Pᵣ／mother CAR witness 内部生成 `bounded (embed q) ≠ 0`。
2. 每枚实际自伴 bounded compression 的 `z R_F(z) → -id` 使非零 bounded reader 在该频率线上至少有一处非零，无有限 Y 扩张或附加价。
3. `correction_zero_bounded_resolvent` 由实际 compressed 57-word full 右逆、bottom 投影身份和 base 右逆相减生成；零 correction 必迫使该频率的 bounded-Y base 读数零，适用于每个 `F`。
4. 实际 correction 的连续性和已付 whole／bottom L1 价把存在非零频率提升为严格正积分及正总测度；原正谱余额随即给出严格 excess。

结论为每个 `F／cause／μ` 的积分严格正；不声称逐频率全正、统一正下界或物理 width。

## 独立验收

三个候选源码与成功 receipt／olean hash 匹配。`ActualYukawaPositiveSpectrumIndependentAudit` 使用 `-j1 --trust=0 -DwarningAsError=true` 新鲜共同导入，十个公开口全部 PASS，精确公理集合为 `propext / Classical.choice / Quot.sound`。

`check_yukawa_correction_detection.py` 独立重放 192 项／2 组非零反控 PASS；保留 `Yq≠0` 但单频 correction 为零的反例，验证存在频率量词不能升级为逐频率全正。命令、完整 LEAN_PATH、源码／olean hash 和日志保存于本地 `ActualYukawaPositiveSpectrumIndependentAudit.strict.json`，控制输出为 `ActualYukawaPositiveSpectrumIndependentControls.json`。

权威生产入口位于 `Verification/physics/low-energy-phenomenology/external-composite-decay/`：`SourceYukawaResolventDetection.lean`、`SourceYukawaCorrectionDetection.lean`、`SourceYukawaPositiveCorrection.lean`，与认证候选源字节相同；[生产依赖重放](../FirstCurrentNeutralNativePayment/actual-yukawa-positive-spectrum-dependency-closure.json)同时验收实际Y源链及 Contact／scalar61 消费者。源生成与其他独验见 [charged 三粒子认证](clock-phi-charged-three-particle-source-certification.md)。

## 原 Y optical 消费者

`SourceGeneralThreeParticleYukawaOptical` 在同一固定输入上生成逐频率身份：`Im(sourcePair r (originalAction r)) = direction × μ × ‖correction‖²`。原 full／base 右逆、实际压缩自伴性和源投影内部支付该式；Y 保持原 `originalAction`，配对为右槽复线性约定。

已付 correction L1 价生成 current 可积性；任意频带积分保持该身份。对 Borel band，`ofReal(direction × ∫current) = ofReal μ × correctionMeasure band`。`actual_generated_candidate_signed_current` 直接消费上述同源严格 excess，自产同一 `f(sourcePoint)=1`，随后对全部 `F／cause／μ>0` 给出 signed 总 current 严格正。

`OriginalYukawaOpticalIndependentAudit` 新鲜 strict0 导入五个公开口 PASS／Std3，成功 receipt 绑定当前源码与 olean hash；独立实际 vacuum CAR 控制244项／5组反控 PASS。命令、完整 LEAN_PATH 和日志保存在同名 `.strict.json`；不把该原 Y optical 身份扩写为全部四块 optical 或 width。
