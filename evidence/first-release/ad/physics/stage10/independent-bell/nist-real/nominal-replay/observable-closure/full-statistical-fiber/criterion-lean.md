# pf0001：完整相位纤维的生成与同源窗口消费

原ef0003合同保持。这里从基本raw source fields构造相位纤维，完整lambda范围为[0,1]，
包含pure-mode、T=0与任意实共同旋转；不修改已冻结源码和数值首回执。

## 生成合同

RawSource仅含nH、nV、etaA、etaB、delta及nH≥nV≥0、losses∈(0,1]的基本物理界。
它不携带完成的Snapshot、观察概率、相位端点、训练资格或coverage证书。
baseline由这些字段内部构造为lambda=0的原Snapshot。

合法相位坐标为k∈[-T,T]，其中T由baseline内部读出且T²=T2。
T>0时生成lambda=(1-k/T)/2；T=0时k=0并生成lambda=0，
同时证明全部lambda∈[0,1]的同源读出相同，不将物理相位纤维误报为唯一相位。
每个生成源在所有cell读回w=(L+gk)/E，E的严格正性直接消费原物理源定理。
构造不除以g，不要求v>0，不把源轴、相位端点或目标读回等式作为输入。

对任意两个training cells及其joint pulse区间，所有合法相位的训练资格
与同一k的physical interval及两线性slab双向等价。
该完整刻画保留g=0、T=0、零或退化训练消元式。
consumer直接消费同一个生成源，给出所有N5/独立OR四outcome配方、
共享相位关系与双方只依赖本地setting的single restriction。

## 协方差图谱

m,z,x,R2与T2先由同一个原Snapshot生成。
证明R2=((h-v)/2)²、T2=(m²-R2)((m+e)²-R2)，
并将ell/gamma的无平方根形式接到原L/g；R2=0不通过除法图谱。
这些是同源坐标读出，不赋予数值cover或实际发表configuration新增内核身份。

## 验收

合同与来源先提交；每次Lean候选或修复提交后才首次编译。
focused trust0/werror检查原GaussianSource、ObservableClosure、ClosureConsumer及两候选文件。
独立certify检查生成对象、两训练双向刻画、T=0/g=0分支、直接consumer与传递依赖。
只有标准三公理可接受；不新增一般无限Born/determinant、统计覆盖或controller推进claim。
原positiveSmoothUnifiedSource、SpinPair.visit10、whole-ledger与tick16→17保持。
新science实现和数值输出不参与本证明构造。

<!-- PHASE-FIBER-FROZEN-BEGIN -->
```json
{
  "version": "p23-complete-phase-fiber-pf0001",
  "status": "frozen_before_compilation",
  "parent": "criterion.md",
  "source_fields": ["nH", "nV", "etaA", "etaB", "delta"],
  "lambda_domain": ["0", "1"],
  "phase_coordinate": "k=(1-2lambda)*T",
  "legal_phase_interval": "-T<=k<=T",
  "pure_mode_preserved": true,
  "zero_T_all_phase_readout_equivalent": true,
  "zero_g_no_division": true,
  "two_training_qualification_iff_slabs": true,
  "same_source_all_cells": true,
  "new_full_Born_kernel_claim": false,
  "new_statistical_coverage_kernel_claim": false,
  "controller_advance": false
}
```
<!-- PHASE-FIBER-FROZEN-END -->
