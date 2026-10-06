# r0006：同源角度响应、连续校准域与固定改善步

版本 `nominal-response-r0006`，2026-10-01。必须先提交本文件和sources.json，之后才
编译新候选或执行任何新的数值/区间/矩阵控制。旧r0001/r0002/r0002.1/r0003/r0004/r0005
的冻结源、实现、输出均不改。已见全部旧输出及公开复现/讨论；本版没有看过新响应结果。

## 来源与生成合同

本轮是 bounded subordinate harmonic-response producer / conditional apparatus readout。
消费同一RealFamily.Preparation及VisibilityCarrier的局域Pauli凸混合，联合与两边缘由
同一Born effect生成。原positiveSmoothUnifiedSource、SpinPair.visit10、material row、
整账、tick16→17与runtime后继保持。直接消费者是新双实现/verifier与readiness研究字段；
不把本轮结果升级为NIST实际信道或生产最优性准入。

令mA=shrinkZ(l)、mB=shrinkZ(r)、ξ=shrinkX(l)shrinkX(r)、ζ=mA mB。
原源生成Δ、χ。在r=V/H坐标中Δ=(r²−1)/(1+r²)、χ=2r/(1+r²)。
沿用r0004的M3：sA=qηA PA+bA，sB=qηB PB+bB，j=qηAηB P+++sA sB。
rawCH=j00+j01+j10−j11−sA(a0)−sB(b0)。所有参数对测量角度保持不变。
这不是r0005完整四模计数合同，也不覆盖独立ΩA/ΩB、设置依赖损失或任意制备依赖通道。

固定其它控制，a1(u)=(sin2u,cos2u)。其谐波响应的cos/sin系数分别为

C_A=qηAηB ζ(1+qΔ²)(cos2b0−cos2b1)/4，
D_A=qηAηB ξχ(sin2b0−sin2b1)/4。

它们必须从生成的joint/singles求差导出，不以闭式概率为primitive。
∂a1 S=2[−C_A sin2a1+D_A cos2a1]；Bob交换A/B同理，导数对弧度。
背景相消、效率仅给正prefactor；只要分母非零，stationarity所需

ξ/ζ=(1+qΔ²)/χ · sin2a1(cos2b0−cos2b1)/[cos2a1(sin2b0−sin2b1)]。

独立路径必须通过4×4态/Pauli共轭/Π与dΠ收缩推导，而非复制这个主闭式。
Lean mouth生成谐波与导数；候选编译后再由独立certify检查精确口径。

## 预声明连续域与更新

效率使用正确公开单位：ηA=0.747±0.003、ηB=0.756±0.003。
q∈[0.0004,0.0006]；在calibrated local-Pauli解释中ξ∈[0.995,0.997]、ζ∈[0.998,1]。
pure reference另固定ξ=ζ=1。mode-overlap是ζ=1的校准子域；左右/平衡放置均在同一类中。
可见度区间按r0004的条件解释，不能声称这是原实验唯一映射。

目标从instrument.json读取；两幅各±0.0005的独立十进制半末位生成
r∈[0.2755/0.9615,0.2765/0.9605]，四角各±0.05°。
这个研究域包含原r±0.0005比较邻域；原门禁舍入规则与容差不变，本域不能代作新的通过带。
各角独立变化，不假设未知真实控制恰好mirror。

先计算整个连续域的必要比值与两方向导数，再检查固定一步a1−0.1°、b1+0.1°以及
二者同时更新。0.1°来自公开角的一个十进制单位，预先固定，不按响应选择步长。
从覆盖整个更新路径的导数界积分得到严格改善下界。若任一范围不能证成，记录NOT_CERTIFIED。

另在明确orientation-preserving分支mA,mB≥0中计算公布控制的CH下界；此分支条件必须
随结果保留，不把最大态校准误称能支付它。both-flipped-z为合法校准look-alike负控制，
检验相同最大态calibration并不自动确定非最大态的margin/CH，不能视为NIST实际设置。
不优化或反推任何损失/可见度/背景以逼近论文最优值，不读取Bell试次或计数档案。

## 精确数值与回执

主路径stdlib Fraction区间+Taylor余项，独立路径另写区间及端点/单调性算法；π使用
Mathlib已证的3.1415<π<3.1416，来源绑定见sources。主/独立各自读frozen criterion和instrument，
不从对方输出取得数据；所有authoritative界为有理数，十进制展示不承担证明。
如需要细分，按固定split_order、max_depth/max_leaves实施，仅缩小计算包络，不换物理输入。
回执绑定冻结commit、所有来源、程序与生成的连续域/更新路径、条件分支及未决项。
verifier重算输入与计算证书。readiness只签收研究结构，保留r0003/r0005生产判决。

<!-- FROZEN-RESPONSE-BEGIN -->
```json
{
  "criterion_version": "nominal-response-r0006",
  "scope": "same-preparation-local-Pauli-M3-continuous-angle-response-and-fixed-update",
  "source_mapping_identified": false,
  "production_admitted": false,
  "target_instrument": "Verification/physics/stage10/independent-bell/nist-real/instrument.json",
  "rounding": {
    "amplitude_half_width": "1/2000",
    "angle_half_width_deg": "1/20",
    "state_ratio": "r=V/H; interval obtained from independent printed-amplitude rounding, not by fitting",
    "original_gate_tolerances_modified": false
  },
  "channel": {
    "eta_A": {
      "center": "747/1000",
      "half_width": "3/1000"
    },
    "eta_B": {
      "center": "756/1000",
      "half_width": "3/1000"
    },
    "pair_probability": [
      "1/2500",
      "3/5000"
    ],
    "background_A_per_trial": "89/100000000",
    "background_B_per_trial": "32/100000000"
  },
  "cases": {
    "calibrated_local_pauli": {
      "xi": [
        "199/200",
        "997/1000"
      ],
      "zeta": [
        "499/500",
        "1"
      ]
    },
    "pure_reference": {
      "xi": [
        "1",
        "1"
      ],
      "zeta": [
        "1",
        "1"
      ]
    }
  },
  "fixed_updates_deg": {
    "alice_only": {
      "a1": "-1/10",
      "b1": "0"
    },
    "bob_only": {
      "a1": "0",
      "b1": "1/10"
    },
    "paired": {
      "a1": "-1/10",
      "b1": "1/10"
    }
  },
  "interval": {
    "arithmetic": "exact rational enclosures",
    "pi": [
      "6283/2000",
      "3927/1250"
    ],
    "primary_trig_terms": 12,
    "independent_trig_terms": 14,
    "max_depth": 12,
    "max_leaves": 4096,
    "split_order": [
      "a0",
      "a1",
      "b0",
      "b1",
      "r",
      "q",
      "xi",
      "zeta"
    ],
    "inconclusive_policy": "report NOT_CERTIFIED; do not adjust physical inputs, control update or tolerance"
  },
  "robust_positive_branch": {
    "restriction": "shrinkZ_A and shrinkZ_B are nonnegative; given positive zeta, mA in[zeta,1], mB=zeta/mA",
    "controls": "target rounding box before update",
    "background": "frozen public values",
    "claim_is_conditional": true
  },
  "matrix_controls": {
    "r": [
      "1",
      "276/961"
    ],
    "placements": [
      "left",
      "right",
      "balanced",
      "both-flipped-z"
    ],
    "xi": "249/250",
    "zeta": "999/1000",
    "finite_difference_step_radians": "1/1000000",
    "derivative_absolute_tolerance": "1/10000000000",
    "probability_tolerance": "1/1000000000000",
    "purpose": "same maximum-preparation calibration, differing nonmaximum margins; finite difference checks actual source contraction"
  },
  "comparison": {
    "enclosures_need_not_be_identical": true,
    "require_sign_agreement": true,
    "require_center_inside_both_enclosures": true,
    "require_source_bindings_match": true
  },
  "outputs": {
    "primary": "response.json",
    "independent": "independent_response.json",
    "verification": "verification.json"
  }
}
```
<!-- FROZEN-RESPONSE-END -->
