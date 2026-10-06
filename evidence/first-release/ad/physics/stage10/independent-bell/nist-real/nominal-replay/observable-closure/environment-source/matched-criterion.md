# mc0001：实际 V/V matched 校准

合法 RawKernel、两站 EnvironmentPrim 与每pulse独立OR背景生成 matched 校准读出。
源phase取任意unit，ξ取任意合法环境重叠；没有预装Born、normalizer、PSD或校准等式。

实际EV端口在a=b=0产生XA/XB的对角形式。
原Γ/SP/occupation生成每个n的numberMass加权项，原geometric HasSum与Cauchy和生成
原NumberConservingEffect的真实fullBorn。H branch质量在该证明内部消去：

```
QAB = (1−tV)/(1−tV*(1−TA)*(1−TB))
    = 1/(1+nV*(TA+TB−TA*TB)).
```

源码内部构造TV=0的silent探测器，生成QA=1/(1+nV*TA)、QB=1/(1+nV*TB)。
独立背景OR生成SA、SB与J；Option KA=J/SB、KB=J/SA。
正herald资格由raw tV、TV和background输入验收；零输入分支保留None。
nV>0时从同源singles生成TV=(S−b)/(nV*(1−S))。

源生正branch进一步生成nec0001的cubic P(SA)=0，
这是forward生成的必要恒等式，不宣称unknown参数反演、Sturm/grid、环境逆读或一般角度determinant内核。
本版只消费旧源，不读取两份新校准数值代码或输出，不修改root/current/whole-ledger。

<!-- MATCHED-FROZEN-BEGIN -->
```json
{
  "version": "p23-environment-matched-mc0001",
  "status": "frozen_before_compilation",
  "primitive": "RawKernel, two EnvironmentPrim, local bA/bB in [0,1)",
  "matched_angles": [0,0],
  "arbitrary_legal_environment_overlap": true,
  "arbitrary_unit_source_phase": true,
  "actual_EV_fullBorn_required": true,
  "background_raw_K_required": true,
  "completed_Born_or_calibration_as_primitive": false,
  "numerical_inverse_or_general_angle_determinant_claim": false,
  "controller_advance": false,
  "new_numeric_programs_or_outputs_read": false
}
```
<!-- MATCHED-FROZEN-END -->
