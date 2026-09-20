# 完整载体复合与原非线性量子响应

正式入口：`Lean/SaturationMonoid/PhysicsCore/LowEnergy/Quantum/`。

五模块保留原外幂物质与独立 dual，读取同一 `Evolution` 九场配置：

| 模块 | 已认证的实际能力 |
| --- | --- |
| Carrier | 原 Λ⁶／Λ²／Λ⁴ 基 × 四 Dirac 分量，252坐标；End→Matrix 代数等价及完整配对 |
| Compression | 原八维 C 的精确复合 `C(AB)=C(A)C(B)+C(AQB)`；原 Yukawa 返回全部来自补空间项 |
| Preparation | 原全载体 Hermitian 配对、spin exchange、自伴与involution；实际prepared independent dual身份 |
| Readout | 同一九场配置的 `χ(Aψ)=(4s/a³)⟨ψ̂θ,S A ψ̂θ⟩`；252坐标中先B再A，最后S／dual读出 |
| Density | 原字段 `ρ=Re χ(Sψ)=4s/a³`，`a³ρ=4s`；径向seed的真实 `ρ′(0)=0`、`ρ″(0)=2sqπ²`及非恒定 |

S 是原 `diracAdjointSpinSwap`。一般 End 给出复响应；归一化读数 `normalizedRead θ S=1`，实际种子密度 `ρ(0)=4s>1`，两者没有混同为概率。原 independent dual 的身份在这族实际准备上证明，没有把任意 dual 变分限制为 adjoint。

[完整载体与返回审计](certification.md)共32项传递公理检查；[同一非线性配置审计](evolution-audit/certification.md)共49项。所有候选与源消费者 fresh `--trust=0 -DwarningAsError=true` 全通过，仅标准三公理。正式迁移只改 import，两组 Audit 已更新；复验见 [promotion.log](promotion.log)。历史认证中的 scratch 路径仅记录认证时位置。

原 source/action、visit 10/tick 16、整账与 tick 17 保持。本组提供完整算子复合与同源响应消费者；物理传播外态及其经验单位由 [Physics active](../../../../Lean/docs/handoffs/physics-cauchy-safe-active-route.md)中的后续责任生成。
