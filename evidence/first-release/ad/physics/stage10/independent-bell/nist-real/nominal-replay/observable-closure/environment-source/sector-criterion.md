# sp0001：实际 paired-sector 与二模 symmetric-power

原 RawKernel 的两条 squeezing branch 和 EV0001 的六端口共同生成任意 n 的计数项。
输入只含合法 RawKernel、两站 EnvironmentPrim 与分析角；不提供 sector/trace 等式、
Born determinant、normalizer certificate 或 occupation endpoint。

令 D=diag(sqrt(tH),phase*sqrt(tV))，XA/XB 为两站源生 noClickGram。
原 occupation O 与 wordTensor 生成 SP_n(A)=O† A^⊗n O。
首先从原归一化 occupation 列证明 symmetric image 在 wordTensor 下不变，
再生成 SP_n(A B)=SP_n(A)SP_n(B) 及普通 transpose / conjugate-transpose 自然性。

原 RawKernel.sectorVector 在证明内部拆为 sqrt((1−tH)(1−tV)) 与 SP_n(D) 的 diagonal。
原 pairedBlock(ΓA,ΓB) 因而生成

```
sectorBorn_n = Re(((1−tH)(1−tV)) * trace SP_n(D† XA D XBᵀ)).
```

Bob 的 transpose 是普通转置，不能改为共轭转置。
直接消费者同时保留源生 NumberConservingEffect 的正性、上界与旧 sectorMass 价格。
零/单光子 symmetric trace 读回 h0=1、h1=tr M。

本 checkpoint 以任意 n 的直接身份为验收；
h(n+2)=tr(M) h(n+1)−det(M) h(n) 作为下游 source-derived 递推责任，
没有本版未编译的递推或无限求和身份声明。
已有 EV0001/DetectorGamma、双数值首回执、root/current/whole-ledger 不变。

<!-- SECTOR-FROZEN-BEGIN -->
```json
{
  "version": "p23-environment-sector-sp0001",
  "status": "frozen_before_compilation",
  "primitive": "RawKernel, two EnvironmentPrim, two real analyzer angles",
  "all_n_actual_sector_trace_identity_required": true,
  "bob_transpose": "ordinary",
  "completed_sector_trace_as_primitive": false,
  "completed_normalizer_as_primitive": false,
  "recurrence_claim": false,
  "new_infinite_Born_or_determinant_claim": false,
  "controller_advance": false,
  "numeric_count_programs_or_outputs_read": false
}
```
<!-- SECTOR-FROZEN-END -->
