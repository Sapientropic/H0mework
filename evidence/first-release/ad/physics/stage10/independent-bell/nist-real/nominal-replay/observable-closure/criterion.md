# ef0001：公开六观测的源消元与两格预言

合同与来源先提交，程序及所有修复各自提交后执行。公开四格及旧结果已经暴露；
这是回顾性训练/留出划分。旧冻结输出、实际装置门禁与publish保持原身份。

## 源与输入

消费fw0001的同源作用顺序：两偏振TMSV，每pulse的V-number phase flip先于双方共同实Jones旋转Rδ；
两侧各有未知scalar transmission ηA/ηB；五fresh-vacuum pulses作本地any-click，
每pulse独立OR背景bA=89/10^8、bB=32/10^8。同一固定源和效果生成四格。
phase权重λ覆盖完整[0,1]；没有visibility输入，不另假定φ=0支占多数。
该源族的stationary/window/background/共同R资格不由公开表自动支付。
这里的stationary指定整个具名epoch内、给定past/settings仍由同一固定
`(tH,tV,R,ηA,ηB,λ)`生成conditional window law；五pulse各自独立抽取phase。
无条件平稳或平均TMSV不替代这个条件源合同。

生成器只接收Table S-II的00、11两个完整四outcome计数；分别产生
`(sA0,sB0,j00,sA1,sB1,j11)`。signed angles固定为
`(a0,a1,b0,b1)=(4.2,−25.9,−4.2,25.9)°`。
01/10计数、统计域、公开效率/visibility、tcal、印刷r、泵强、κ和optimizer不进入生成器。
训练率是印刷计数的精确有理中心，不是未知真实概率。

## 四single消元

设`αi=(1−bA)/(1−sAi)^(1/5)−1`，`βi=(1−bB)/(1−sBi)^(1/5)−1`；
`ci=cos(2ai)`、`si=sin(2ai)`。
源生mean满足`αi=m−z ci−x si`、`r βi=m−z ci+x si`，其中
`r=ηA/ηB`、`(m,z,x)=ηA(M,Z,X)`。

非退化口固定生成

```
r=(s1 α0−s0 α1)/(s1 β0−s0 β1)
ui=(αi+r βi)/2
z=(u1−u0)/(c0−c1), m=u0+z c0
x=−(α0−r β0)/(2s0)
C=sqrt(z²+x²), h=m+C, v=m−C
cos(2δ)=z/C, sin(2δ)=x/C
```

未知绝对损耗仅留下`e=ηA∈(0,min(1,r)]`；同一源给
`ηB=e/r`、`nH=h/e`、`nV=v/e`、`tH/V=nH/V/(1+nH/V)`。
不拟合、截值或投影负布居/非法loss。两实现分别重建四个single。

## 两joint的二次闭包

训练pulse双无点击为
`wi=(1−sAi−sBi+jii)^(1/5)/[(1−bA)(1−bB)]`。
mirror几何给`Ui=(ci−z/C)/2`、`Vi=(ci+z/C)/2`，
`Di=(1+αi)(1+βi)`。定义

```
T²(e)=hv(h+e)(v+e)
gi=2UiVi/r
Li(e)=Di−[h(h+e)Ui²+v(v+e)Vi²]/r
Hi(e)=wi[Li(e)²−gi²T²(e)]−Li(e)
F(e)=g1 H0(e)−g0 H1(e)
```

由同一两branch pulse law，`Hi=(1−2λ)gi T`。Li为一次、T²和Hi为至多二次；
故F为至多二次，不含λ或未记录泵响应。
**全部实根都进入合法性检查**；非零F的非退化口最多生成两个合法分支。
合法性须包括e域、h/v正性、两phase真空分母正性，以及
`c=Hi/(gi sqrt(T²))∈[−1,1]`，再生成`λ=(1−c)/2`。
选择gi时固定优先i=0，只有其严格为0才用i=1；不得为接近留出观测选分支。

零leading coefficient必须识别一次/常数方程；负discriminant记无实中心分支。
F恒零、两个gi都零、T=0、C=0、four-single ratio分母为零或边界无法判定，
记`DEGENERATE_OR_UNRESOLVED_FIBER`并保留原因，禁止制造唯一源。
不把“无合法中心分支”写成整个统计域内的源族拒绝。

## 同一根生成01/10完整outcome

对每个保留的根，
`Uxy=sin(ax−δ)sin(by−δ)`、`Vxy=cos(ax−δ)cos(by−δ)`；
对应gxy/Lxy复用同一个h/v/r/e和四local means。
取同一个训练i，直接生成

```
wxy=[Lxy+(gxy/gi)Hi]/[Lxy²−gxy²T²]
P0Awin=[(1−bA)/(1+αx)]^5
P0Bwin=[(1−bB)/(1+βy)]^5
P00win=[(1−bA)(1−bB)wxy]^5
(++,+0,0+,00)=(1−P0Awin−P0Bwin+P00win,
               P0Bwin−P00win, P0Awin−P00win, P00win)
```

一般R不强制j01=j10；两格联合消费同一个根/phase/source，不能各格挑最合适分支。
源参数及两格预言首回执形成后才读留出率和原CI作比较。

参数无关必要关系另读出：设`Hxy=wxy(Lxy²−gxy²T²)−Lxy`，
`Gxy=gxy H0−g0 Hxy`。同一源根给`F(e)=G01(e)=G10(e)=0`，
因此`Res_e(F,G01)=Res_e(F,G10)=0`。对两个二次式，resultant为其4×4 Sylvester行列式。
这两个等式是消去e/λ的必要关系；退化时可空真，两个零resultant也不自动支付同一个合法根。
完整预测以原共同branch为准。

## 数值与独立性

主路径：已有有理向外算术、整数第五根、带显式余项的trig，直接构造F三个系数、
discriminant与全部根包络，按同源Gaussian vacuum law前向重建。
独立路径：自行读取criterion/两训练行；用两侧single比值的2×2方程生成归一化covariance，
在e=0,1,2的多项式读出独立恢复F系数。自行求全根、source和λ，
以相干Fock/Γ前缀h+v≤6与原质量尾产生三项no-click，再作phase mixture和五窗口。
独立路径不得导入主生成器、读取主源点或主根；两科学首回执完成后才比较。

源保持精确real-root descriptor；有理外包络只作数学计算，不把midpoint当作实际源。
precision=40 decimal，π使用已核20位界，主/独立trig各12/14项，
根/概率数值容差1e−12。未解析结果记录unresolved，不放宽精度或改分支规则。
所有源分支先形成后才比较留出；回执列完整branch count、拒绝理由、重构残差和尾。
每个合法分支必须从原源law重建全部六训练概率：数学包络包含六个印刷中心，
对应residual包含0且宽≤1e−12。只重建four singles或比较两个优化结果不满足该口。

## 统计消费者

原po0003的12项共同平均概率CI原样绑定，alpha=.05、ε=.003、
6runs×32767slot masks×16features×40固定赌注保持。
全部12个数学概率包络进入原CI才记`EXHIBITED_CALIBRATION_FREE_SOURCE_MEMBER`。
它表示具名stationary源族的回顾性相容成员；不能把CI中的一般漂移平均率非线性反演成实际固定源。

真实训练概率的完整不确定性fiber是六维训练域每一点的所有合法根及所有退化fiber。
本版中心求解器不提供这整个fiber的不可行性证明；不以中心两根外包络冒充统计覆盖。
中心成员不存在、留出不包含或无法闭合分别记录，不拒整个统计fiber。
actual source、硬件资格、历史最优性、global optimum和root activation不由相容成员支付。

正控：不同η、共同R与两λ；完整root/source读回、两格共同branch、完整四outcome和原尾。
反控：修改全部01/10仍不改源，未知参数偷入、共同R丢失、窗口后混合、丢根、
两格不同分支、prefix重归一、负布居、η>1、退化fiber假唯一、CI作为source输入。
source law与消元的Lean代数范围、数值概率、统计覆盖及实际资格分别登记。

<!-- EF-FROZEN-BEGIN -->
```json
{
  "version": "p23-observable-closure-ef0001",
  "status": "frozen_before_execution",
  "training_rows": [0, 3],
  "training_quantities": ["sA0", "sB0", "j00", "sA1", "sB1", "j11"],
  "held_out_rows": [1, 2],
  "angles_deg": ["21/5", "-259/10", "-21/5", "259/10"],
  "window_pulses": 5,
  "background_per_pulse": ["89/100000000", "32/100000000"],
  "loss_ratio": "generated_from_four_local_single_means",
  "absolute_loss_domain": "0<etaA<=min(1,etaA_over_etaB)",
  "lambda_domain": ["0", "1"],
  "all_real_branches_required": true,
  "degenerate_fiber_rule": "preserve_unresolved_never_select_a_unique_member",
  "pi": ["3.14159265358979323846", "3.14159265358979323847"],
  "primary_terms": 12,
  "independent_terms": 14,
  "precision_digits": 40,
  "source_pair_cutoff": 6,
  "implementation_tolerance": "1/1000000000000",
  "public_counts": "../observable-prediction/public-observables.json",
  "public_confidence_report": "../observable-prediction/public-comparison-po0003.json",
  "alpha": "1/20",
  "features_in_global_union": 16,
  "runs_covered": 6,
  "pulse_subsets_covered": 32767,
  "settings_predictability": "3/1000",
  "full_statistical_fiber_certified": false,
  "source_mapping_identified": false,
  "publication_configuration_identified": false,
  "production_admitted": false,
  "actual_window_model_identified": false,
  "calibration_protocol_identified": false,
  "noise_channel_identified": false,
  "actual_pump_actuator_identified": false,
  "global_optimum_kernel_proof": false,
  "controller_advance": false,
  "bell_event_files_read": 0,
  "retrospective": true
}
```
<!-- EF-FROZEN-END -->
