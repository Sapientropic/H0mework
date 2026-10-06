# evg0001：同源完整计数与Gaussian读出

六端口已生成全部n的实际Γ。这里从同一paired RawKernel生成number-sector Born，
独立核对Gaussian determinant；模型校准先消费这个新law，不借旧rank1 inverse的gain。
合同、来源、每个程序和修复先提交再运行。没有新事件、实际装置身份或参数优化。

## 两条路径

paired源振幅为sqrt(Z) dH^h dV^v，dH=sqrt(tH)、dV=phase sqrt(tV)，
Z=(1−tH)(1−tV)。每站本地phase/环境字段由原生六端口生成E和X=I−E。
主路径直接六rows形成Grams，再算
`PA0=Z/det(I−D†XA D)`、`PB0=Z/det(I−D†D XBᵀ)`、
`PAB0=Z/det(I−D†XA D XBᵀ)`。三者来自同source，Bob用普通transpose。

独立路径从Pol⊗Env实际embedding/retarder/输出投影生成X，
wordTensor/occupation或独立显式normalized occupation多项式生成Γn。
对每n=0..6，完整paired amplitudes直接收缩ΓA(h,k)ΓB(h,k)，不能只算对角population。
total-pair prefix6不是H/V分别截断的rectangle。
原numberMass生成tail=1−Σ_{h+v≤6}(1−tH)(1−tV)tH^h tV^v，tail不重归一。
局部/联合无点击、完整(++,+0,0+,00)及N1/N5 fresh pulse OR由同三个读出生成。
正项质量尾给予外包；超出precision/tol则如实unresolved。

两边precision40、旧π区间和trig12/14、1e−12容差；不互读新source/output到各自首回执冻结。
这一数值消费者不授新的无限Born/closed-form内核身份；该身份由actual-sector求和证明另消费。

## 反控及完整fringe口

ξ=1 scalar losses时退原fixed-phase rank1 Gaussian读出；ξ=0有两个环境点击端口。
balanced dH=dV=1/10、ξA=ξB=i、η=1、a=b=45°，normalized single-pair joint必须0；
错误Bobtranspose/adjoint给1/2，fullGaussian原J=t²、错误式J=t。
两ξsplit具有相同single-pair product，局部DA无点击的二阶项必须区分。
source phase=i、zero source、zero transmissions及不等TH/TV都保持直接source身份。

同balanced source/固定Bob时，以q=tan a生成全部fringe rational coefficients。
通用QA/QAB各degree≤4；joint的分子/分母degree≤8，导数degree≤14。
若程序支付该口，必须检查完整表达式和度数，不授全fringe extrema已枚举的旗标。
校准fiber与五控制重放在来源/field角色闭合后另冻结，不把本版fixtures当实测校准值。

<!-- EVG-FROZEN-BEGIN -->
```json
{
  "version": "p23-environment-count-evg0001",
  "status": "frozen_before_execution",
  "precision_digits": 40,
  "implementation_tolerance": "1e-12",
  "total_pair_prefix": 6,
  "prefix_renormalized": false,
  "fixture_semantics": "tH,tV,phase,[TH_A,TV_A],[TH_B,TV_B],xiA,xiB,[a,b] degrees",
  "fixtures": [
    {"id":"vacuum","tH":"0","tV":"0","phase":["1","0"],"TA":[".747",".747"],"TB":[".756",".756"],"xiA":["0","0"],"xiB":["0","0"],"angles":["4.2","-4.2"]},
    {"id":"rank_one","tH":"1/2500","tV":"1/40000","phase":["1","0"],"TA":[".747",".747"],"TB":[".756",".756"],"xiA":["1","0"],"xiB":["1","0"],"angles":["4.2","-4.2"]},
    {"id":"two_environment_ports","tH":"1/2500","tV":"1/40000","phase":["1","0"],"TA":[".747",".747"],"TB":[".756",".756"],"xiA":["3/5","0"],"xiB":["4/5","0"],"angles":["-25.9","25.9"]},
    {"id":"complex_transpose","tH":"1/100","tV":"1/100","phase":["1","0"],"TA":["1","1"],"TB":["1","1"],"xiA":["0","1"],"xiB":["0","1"],"angles":["45","45"]},
    {"id":"same_product_one_side","tH":"1/2500","tV":"1/2500","phase":["1","0"],"TA":[".747",".747"],"TB":[".756",".756"],"xiA":["1","0"],"xiB":["9/25","0"],"angles":["45","45"]},
    {"id":"same_product_split","tH":"1/2500","tV":"1/2500","phase":["1","0"],"TA":[".747",".747"],"TB":[".756",".756"],"xiA":["3/5","0"],"xiB":["3/5","0"],"angles":["45","45"]},
    {"id":"unequal_polarization_losses","tH":"1/2500","tV":"1/40000","phase":["0","1"],"TA":["3/4","7/10"],"TB":["4/5","2/3"],"xiA":["3/5","4/5"],"xiB":["4/5","0"],"angles":["-25.9","25.9"]},
    {"id":"all_lost","tH":"1/2500","tV":"1/40000","phase":["1","0"],"TA":["0","0"],"TB":["0","0"],"xiA":["0","0"],"xiB":["0","0"],"angles":["4.2","-4.2"]}
  ],
  "window_pulse_probes": [1,5],
  "background_per_pulse": ["0","0"],
  "full_fringe_derivative_degree_cap": 14,
  "source_mapping_identified": false,
  "new_full_Born_or_Gaussian_determinant_kernel_claim": false,
  "full_fringe_extrema_certified": false,
  "apparatus_optimum_verified": false,
  "controller_advance": false,
  "retrospective": true,
  "event_files_read": 0
}
```
<!-- EVG-FROZEN-END -->
