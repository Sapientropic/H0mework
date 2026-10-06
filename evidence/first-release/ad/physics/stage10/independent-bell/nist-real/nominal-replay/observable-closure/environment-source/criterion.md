# ev0001：固定环境端口生成校准作用

双branch的不可区分性由同一局部环境mode生成，公开fringe是该源的读出。
本合同先生成光学端口及全部光子数效果，不把visibility直接赋名scalar phase probability。
合同、来源、候选和每次修复先提交再编译/执行；旧源和重放保持。

## 原生局部carrier

沿用原DetectorPrim的H/V透射TH、TV∈[0,1]，另取ξ∈ℂ、normSq ξ≤1。
环境为ℂ²，uH=(1,0)、uV=(ξ,sqrt(1−normSq ξ))；occupied源列为
|H>⊗uH、|V>⊗uV。两列因偏振正交而等距，不接受完成的isometry/PSD/Gram等式。
固定real有效分析角a，s=sin a、c=cos a；六个输出端口由实际rows生成：

```
clicked:       [sqrt(TH)*s, sqrt(TV)*ξ*c]
               [0, sqrt(TV)*sqrt(1−|ξ|²)*c]
perpendicular: [sqrt(TH)*c, −sqrt(TV)*ξ*s]
               [0, −sqrt(TV)*sqrt(1−|ξ|²)*s]
lost:          [sqrt(1−TH),0]
               [0,sqrt(1−TV)]
```

由sixPort†sixPort=I生成clicked Gram E、NoClick Gram X=I−E及0≤X≤I。
全部n效果直接消费原wordTensor/occupation：Γn=O†X⊗n O；
wordTensor(noClickRows)O的Gram是同一Γn，归一化与上下界由原消费者产生。
ξ=1时E严格退回原rank1点击效果、X退回onePhotonEffect、所有Γn退回原gamma。
general complex density/finitePhi只消费同源效果；不新增完整无限Born或Gaussian determinant内核旗标。

实际source polarization rotation作用在Pol⊗Env，不能对ξ<1的occupied两列直接用旧Γ(R)。
回拉实际分析效果仍生成E(a−δ;ξ)；该δ必须来自同source作用，不增加拟合offset。

## 后续数值口

两branch的TMSV pair D=diag(sqrt(tH),phase*sqrt(tV))，Z=(1−tH)(1−tV)。
joint无点击是Z/det(I−D†XA D XBᵀ)，Bob用普通transpose；
各局部是Z/det(I−D†X D)。必须由独立number-sector/原质量尾核对，不用式子作完成的Born证书。
实接收角的完整forward只依赖uA=|ξA|²、uB=|ξB|²、c=Re(phase ξAξB)，
合法域0≤uA,uB≤1、c²≤uAuB。raw HV/DA用完整fringe极值读回，生成整个calibration fiber。
一般fringe的q=tan a导数安全次数上界14，不能消费旧rank1六次root cap。

ξ<1改变bucket singles的二阶项；ef旧rank1 inverse不作为新gain的回收证据。
纯H/V单branch matched校准仍消费原K逆读；其他source量按新law重生。
本版数学口不读取新数据，不改变已冻结pd条件轨道或原五控制最优判决。

## 强制反控

ξA=ξB=i、η=1、a=b=45°、balanced D=dI时，single-pair joint为0；错误Bob转置给1/2。
ξsplit=(1,c)与(sqrt c,sqrt c)有相同单pair coherence，却有不同DA bucket singles二阶项。
ξ=1退回原rank1，ξ=0产生两环境点击端口；TH/TV边界、完整six-port质量和no-click Gram分别验收。

<!-- ENV-FROZEN-BEGIN -->
```json
{
  "version": "p23-fixed-environment-ev0001",
  "status": "frozen_before_execution",
  "primitive": "DetectorPrim(TH,TV) and complex xi with normSq(xi)<=1",
  "environment_dimension_per_party": 2,
  "output_ports_per_party": 6,
  "completed_Gram_or_PSD_as_primitive": false,
  "all_number_sectors_required": true,
  "rank_one_limit_required": true,
  "full_fringe_derivative_degree_cap": 14,
  "old_rank_one_gain_inverse_admitted_for_new_source": false,
  "new_full_Born_kernel_claim": false,
  "actual_source_identity_verified": false,
  "apparatus_optimum_verified": false,
  "controller_advance": false,
  "retrospective": true,
  "event_files_read": 0
}
```
<!-- ENV-FROZEN-END -->
