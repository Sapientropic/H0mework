import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B046
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B047

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1121_pa : Scalar.QComplex := ((999999939039576656604590902455 : Int)/10^30,(-349171652587402352531271627 : Int)/10^30)
theorem v1121_pa_checked : Scalar.distance (sourceCoefficient 12 36 1 0) v1121_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1121_pb : Scalar.QComplex := ((-150659714464188979236327 : Int)/10^30,(-431477481529508921845673500 : Int)/10^30)
theorem v1121_pb_checked : Scalar.distance (sourceCoefficient 12 36 1 1) v1121_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1121_pg : Scalar.QComplex := ((-93086422801953959678288 : Int)/10^30,(32503142064613216921 : Int)/10^30)
theorem v1121_pg_checked : Scalar.distance (sourceCoefficient 12 36 1 2) v1121_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1121_mb : Scalar.QComplex := ((-523005291902277679713962 : Int)/10^30,(-431477190858174932396983552 : Int)/10^30)
theorem v1121_mb_checked : Scalar.distance (sourceCoefficient 12 36 3 1) v1121_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1121_mg : Scalar.QComplex := ((-93086360092876776239425 : Int)/10^30,(112832520383442540334 : Int)/10^30)
theorem v1121_mg_checked : Scalar.distance (sourceCoefficient 12 36 3 2) v1121_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1121_upper : Scalar.QComplex := ((999997847018539940711079093948 : Int)/10^30,(-2075080308033742216685203503 : Int)/10^30)
theorem v1121_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 36 5) 1) 14) v1121_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1121 : Material (12 : Basis) (36 : Basis) where
  plus := ![v1121_pa,v1121_pb,v1121_pg]
  minus := ![(Primitive.Addresses.material1121 1).one,v1121_mb,v1121_mg]
  upper := v1121_upper
  lower := (Primitive.Addresses.material1121 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1121_pa_checked.trans (by decide +kernel)
    · exact v1121_pb_checked.trans (by decide +kernel)
    · exact v1121_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 36 Primitive.Addresses.material1121
    · exact v1121_mb_checked.trans (by decide +kernel)
    · exact v1121_mg_checked.trans (by decide +kernel)
  upper_error := v1121_upper_checked
  lower_error := reuse_lower_error 12 36 Primitive.Addresses.material1121

def v1122_pa : Scalar.QComplex := ((999999936608603432332844528761 : Int)/10^30,(-356065708987632158005815814 : Int)/10^30)
theorem v1122_pa_checked : Scalar.distance (sourceCoefficient 12 37 1 0) v1122_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1122_pb : Scalar.QComplex := ((-153634344586322723027845 : Int)/10^30,(-431477480052884014843386691 : Int)/10^30)
theorem v1122_pb_checked : Scalar.distance (sourceCoefficient 12 37 1 1) v1122_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1122_pg : Scalar.QComplex := ((-93086422529526029516466 : Int)/10^30,(33144885136198538827 : Int)/10^30)
theorem v1122_pg_checked : Scalar.distance (sourceCoefficient 12 37 1 2) v1122_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1122_mb : Scalar.QComplex := ((-525979919642559891696639 : Int)/10^30,(-431477186814578752175626673 : Int)/10^30)
theorem v1122_mb_checked : Scalar.distance (sourceCoefficient 12 37 3 1) v1122_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1122_mg : Scalar.QComplex := ((-93086359266653579771851 : Int)/10^30,(113474262980984553550 : Int)/10^30)
theorem v1122_mg_checked : Scalar.distance (sourceCoefficient 12 37 3 2) v1122_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1122_upper : Scalar.QComplex := ((999997832689054414202829214706 : Int)/10^30,(-2081974349970445597845009237 : Int)/10^30)
theorem v1122_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 37 5) 1) 14) v1122_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1122 : Material (12 : Basis) (37 : Basis) where
  plus := ![v1122_pa,v1122_pb,v1122_pg]
  minus := ![(Primitive.Addresses.material1122 1).one,v1122_mb,v1122_mg]
  upper := v1122_upper
  lower := (Primitive.Addresses.material1122 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1122_pa_checked.trans (by decide +kernel)
    · exact v1122_pb_checked.trans (by decide +kernel)
    · exact v1122_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 37 Primitive.Addresses.material1122
    · exact v1122_mb_checked.trans (by decide +kernel)
    · exact v1122_mg_checked.trans (by decide +kernel)
  upper_error := v1122_upper_checked
  lower_error := reuse_lower_error 12 37 Primitive.Addresses.material1122

def v1123_pa : Scalar.QComplex := ((999999928040441990972306762895 : Int)/10^30,(-379366723421911898215673019 : Int)/10^30)
theorem v1123_pa_checked : Scalar.distance (sourceCoefficient 12 38 1 0) v1123_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1123_pb : Scalar.QComplex := ((-163688207646815452371521 : Int)/10^30,(-431477474859699010451617007 : Int)/10^30)
theorem v1123_pb_checked : Scalar.distance (sourceCoefficient 12 38 1 1) v1123_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1123_pg : Scalar.QComplex := ((-93086421570550576246149 : Int)/10^30,(35313893287462706783 : Int)/10^30)
theorem v1123_pg_checked : Scalar.distance (sourceCoefficient 12 38 1 2) v1123_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1123_mb : Scalar.QComplex := ((-536033774478055152958032 : Int)/10^30,(-431477172945364669421926576 : Int)/10^30)
theorem v1123_mb_checked : Scalar.distance (sourceCoefficient 12 38 3 1) v1123_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1123_mg : Scalar.QComplex := ((-93086356435922137531712 : Int)/10^30,(115643269497075232700 : Int)/10^30)
theorem v1123_mg_checked : Scalar.distance (sourceCoefficient 12 38 3 2) v1123_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1123_upper : Scalar.QComplex := ((999997783905468672062415795347 : Int)/10^30,(-2105275314912732117369256314 : Int)/10^30)
theorem v1123_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 38 5) 1) 14) v1123_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1123 : Material (12 : Basis) (38 : Basis) where
  plus := ![v1123_pa,v1123_pb,v1123_pg]
  minus := ![(Primitive.Addresses.material1123 1).one,v1123_mb,v1123_mg]
  upper := v1123_upper
  lower := (Primitive.Addresses.material1123 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1123_pa_checked.trans (by decide +kernel)
    · exact v1123_pb_checked.trans (by decide +kernel)
    · exact v1123_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 38 Primitive.Addresses.material1123
    · exact v1123_mb_checked.trans (by decide +kernel)
    · exact v1123_mg_checked.trans (by decide +kernel)
  upper_error := v1123_upper_checked
  lower_error := reuse_lower_error 12 38 Primitive.Addresses.material1123

def v1124_pa : Scalar.QComplex := ((999999922821032677311054706265 : Int)/10^30,(-392884116106498881185921112 : Int)/10^30)
theorem v1124_pa_checked : Scalar.distance (sourceCoefficient 12 39 1 0) v1124_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1124_pb : Scalar.QComplex := ((-169520658173669474352422 : Int)/10^30,(-431477471703865647377486279 : Int)/10^30)
theorem v1124_pb_checked : Scalar.distance (sourceCoefficient 12 39 1 1) v1124_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1124_pg : Scalar.QComplex := ((-93086420987204681969626 : Int)/10^30,(36572179053678370579 : Int)/10^30)
theorem v1124_pg_checked : Scalar.distance (sourceCoefficient 12 39 1 2) v1124_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1124_mb : Scalar.QComplex := ((-541866220109879228759419 : Int)/10^30,(-431477164756390360554212388 : Int)/10^30)
theorem v1124_mb_checked : Scalar.distance (sourceCoefficient 12 39 3 1) v1124_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1124_mg : Scalar.QComplex := ((-93086354766732515304588 : Int)/10^30,(116901554291372365396 : Int)/10^30)
theorem v1124_mg_checked : Scalar.distance (sourceCoefficient 12 39 3 2) v1124_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1124_upper : Scalar.QComplex := ((999997755356273646786196284578 : Int)/10^30,(-2118792678456523586868147956 : Int)/10^30)
theorem v1124_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 39 5) 1) 14) v1124_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1124 : Material (12 : Basis) (39 : Basis) where
  plus := ![v1124_pa,v1124_pb,v1124_pg]
  minus := ![(Primitive.Addresses.material1124 1).one,v1124_mb,v1124_mg]
  upper := v1124_upper
  lower := (Primitive.Addresses.material1124 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1124_pa_checked.trans (by decide +kernel)
    · exact v1124_pb_checked.trans (by decide +kernel)
    · exact v1124_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 39 Primitive.Addresses.material1124
    · exact v1124_mb_checked.trans (by decide +kernel)
    · exact v1124_mg_checked.trans (by decide +kernel)
  upper_error := v1124_upper_checked
  lower_error := reuse_lower_error 12 39 Primitive.Addresses.material1124

def v1125_pa : Scalar.QComplex := ((999999913630164957991669568258 : Int)/10^30,(-415619612896538191845447737 : Int)/10^30)
theorem v1125_pa_checked : Scalar.distance (sourceCoefficient 12 40 1 0) v1125_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1125_pb : Scalar.QComplex := ((-179330512947263222195600 : Int)/10^30,(-431477466158840390837076383 : Int)/10^30)
theorem v1125_pb_checked : Scalar.distance (sourceCoefficient 12 40 1 1) v1125_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1125_pg : Scalar.QComplex := ((-93086419961293684672769 : Int)/10^30,(38688545171760731379 : Int)/10^30)
theorem v1125_pg_checked : Scalar.distance (sourceCoefficient 12 40 1 2) v1125_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1125_mb : Scalar.QComplex := ((-551676066445708654154861 : Int)/10^30,(-431477150745904318526614732 : Int)/10^30)
theorem v1125_mb_checked : Scalar.distance (sourceCoefficient 12 40 3 1) v1125_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1125_mg : Scalar.QComplex := ((-93086351914493257687808 : Int)/10^30,(119017918736119912374 : Int)/10^30)
theorem v1125_mg_checked : Scalar.distance (sourceCoefficient 12 40 3 2) v1125_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1125_upper : Scalar.QComplex := ((999997706926014704733844061774 : Int)/10^30,(-2141528125522107233284491582 : Int)/10^30)
theorem v1125_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 40 5) 1) 14) v1125_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1125 : Material (12 : Basis) (40 : Basis) where
  plus := ![v1125_pa,v1125_pb,v1125_pg]
  minus := ![(Primitive.Addresses.material1125 1).one,v1125_mb,v1125_mg]
  upper := v1125_upper
  lower := (Primitive.Addresses.material1125 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1125_pa_checked.trans (by decide +kernel)
    · exact v1125_pb_checked.trans (by decide +kernel)
    · exact v1125_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 40 Primitive.Addresses.material1125
    · exact v1125_mb_checked.trans (by decide +kernel)
    · exact v1125_mg_checked.trans (by decide +kernel)
  upper_error := v1125_upper_checked
  lower_error := reuse_lower_error 12 40 Primitive.Addresses.material1125

def v1126_pa : Scalar.QComplex := ((999999907505439792820673060090 : Int)/10^30,(-430103605959209537479016929 : Int)/10^30)
theorem v1126_pa_checked : Scalar.distance (sourceCoefficient 12 41 1 0) v1126_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1126_pb : Scalar.QComplex := ((-185580029664148195719820 : Int)/10^30,(-431477462471228697303041048 : Int)/10^30)
theorem v1126_pb_checked : Scalar.distance (sourceCoefficient 12 41 1 1) v1126_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1126_pg : Scalar.QComplex := ((-93086419278448878414746 : Int)/10^30,(40036808300678718466 : Int)/10^30)
theorem v1126_pg_checked : Scalar.distance (sourceCoefficient 12 41 1 2) v1126_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1126_mb : Scalar.QComplex := ((-557925577653370129304558 : Int)/10^30,(-431477141665242539171566132 : Int)/10^30)
theorem v1126_mb_checked : Scalar.distance (sourceCoefficient 12 41 3 1) v1126_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1126_mg : Scalar.QComplex := ((-93086350068158348945055 : Int)/10^30,(120366180773753604284 : Int)/10^30)
theorem v1126_mg_checked : Scalar.distance (sourceCoefficient 12 41 3 2) v1126_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1126_upper : Scalar.QComplex := ((999997675803240613037193678805 : Int)/10^30,(-2156012086441852317053215782 : Int)/10^30)
theorem v1126_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 41 5) 1) 14) v1126_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1126 : Material (12 : Basis) (41 : Basis) where
  plus := ![v1126_pa,v1126_pb,v1126_pg]
  minus := ![(Primitive.Addresses.material1126 1).one,v1126_mb,v1126_mg]
  upper := v1126_upper
  lower := (Primitive.Addresses.material1126 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1126_pa_checked.trans (by decide +kernel)
    · exact v1126_pb_checked.trans (by decide +kernel)
    · exact v1126_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 41 Primitive.Addresses.material1126
    · exact v1126_mb_checked.trans (by decide +kernel)
    · exact v1126_mg_checked.trans (by decide +kernel)
  upper_error := v1126_upper_checked
  lower_error := reuse_lower_error 12 41 Primitive.Addresses.material1126

def v1127_pa : Scalar.QComplex := ((999999902412005989209491585921 : Int)/10^30,(-441787254793712266253038783 : Int)/10^30)
theorem v1127_pa_checked : Scalar.distance (sourceCoefficient 12 42 1 0) v1127_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1127_pb : Scalar.QComplex := ((-190621260899853784506681 : Int)/10^30,(-431477459408637364938739021 : Int)/10^30)
theorem v1127_pb_checked : Scalar.distance (sourceCoefficient 12 42 1 1) v1127_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1127_pg : Scalar.QComplex := ((-93086418711024249754241 : Int)/10^30,(41124397394168901778 : Int)/10^30)
theorem v1127_pg_checked : Scalar.distance (sourceCoefficient 12 42 1 2) v1127_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1127_mb : Scalar.QComplex := ((-562966804369116547551847 : Int)/10^30,(-431477134252296839362476345 : Int)/10^30)
theorem v1127_mb_checked : Scalar.distance (sourceCoefficient 12 42 3 1) v1127_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1127_mg : Scalar.QComplex := ((-93086348562193527075073 : Int)/10^30,(121453768972622764135 : Int)/10^30)
theorem v1127_mg_checked : Scalar.distance (sourceCoefficient 12 42 3 2) v1127_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1127_upper : Scalar.QComplex := ((999997650544896439488165061866 : Int)/10^30,(-2167695709084127892309676563 : Int)/10^30)
theorem v1127_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 42 5) 1) 14) v1127_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1127 : Material (12 : Basis) (42 : Basis) where
  plus := ![v1127_pa,v1127_pb,v1127_pg]
  minus := ![(Primitive.Addresses.material1127 1).one,v1127_mb,v1127_mg]
  upper := v1127_upper
  lower := (Primitive.Addresses.material1127 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1127_pa_checked.trans (by decide +kernel)
    · exact v1127_pb_checked.trans (by decide +kernel)
    · exact v1127_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 42 Primitive.Addresses.material1127
    · exact v1127_mb_checked.trans (by decide +kernel)
    · exact v1127_mg_checked.trans (by decide +kernel)
  upper_error := v1127_upper_checked
  lower_error := reuse_lower_error 12 42 Primitive.Addresses.material1127

def v1128_pa : Scalar.QComplex := ((999999895454335342570739013817 : Int)/10^30,(-457265041726417703317309404 : Int)/10^30)
theorem v1128_pa_checked : Scalar.distance (sourceCoefficient 12 43 1 0) v1128_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1128_pb : Scalar.QComplex := ((-197299577196832509259879 : Int)/10^30,(-431477455230574279841916225 : Int)/10^30)
theorem v1128_pb_checked : Scalar.distance (sourceCoefficient 12 43 1 1) v1128_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1128_pg : Scalar.QComplex := ((-93086417936506792695687 : Int)/10^30,(42565169231903444492 : Int)/10^30)
theorem v1128_pg_checked : Scalar.distance (sourceCoefficient 12 43 1 2) v1128_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1128_mb : Scalar.QComplex := ((-569645114573972631344696 : Int)/10^30,(-431477124311149125857377624 : Int)/10^30)
theorem v1128_mb_checked : Scalar.distance (sourceCoefficient 12 43 3 1) v1128_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1128_mg : Scalar.QComplex := ((-93086346544355152394597 : Int)/10^30,(122894539605518422663 : Int)/10^30)
theorem v1128_mg_checked : Scalar.distance (sourceCoefficient 12 43 3 2) v1128_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1128_upper : Scalar.QComplex := ((999997616873980043494994118676 : Int)/10^30,(-2183173460956179500532237208 : Int)/10^30)
theorem v1128_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 43 5) 1) 14) v1128_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1128 : Material (12 : Basis) (43 : Basis) where
  plus := ![v1128_pa,v1128_pb,v1128_pg]
  minus := ![(Primitive.Addresses.material1128 1).one,v1128_mb,v1128_mg]
  upper := v1128_upper
  lower := (Primitive.Addresses.material1128 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1128_pa_checked.trans (by decide +kernel)
    · exact v1128_pb_checked.trans (by decide +kernel)
    · exact v1128_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 43 Primitive.Addresses.material1128
    · exact v1128_mb_checked.trans (by decide +kernel)
    · exact v1128_mg_checked.trans (by decide +kernel)
  upper_error := v1128_upper_checked
  lower_error := reuse_lower_error 12 43 Primitive.Addresses.material1128

def v1129_pa : Scalar.QComplex := ((999999892759547044713291319109 : Int)/10^30,(-463120820531811835865958624 : Int)/10^30)
theorem v1129_pa_checked : Scalar.distance (sourceCoefficient 12 44 1 0) v1129_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1129_pb : Scalar.QComplex := ((-199826213788115858628273 : Int)/10^30,(-431477453613934616261851757 : Int)/10^30)
theorem v1129_pb_checked : Scalar.distance (sourceCoefficient 12 44 1 1) v1129_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1129_pg : Scalar.QComplex := ((-93086417636696754974859 : Int)/10^30,(43110262739438025112 : Int)/10^30)
theorem v1129_pg_checked : Scalar.distance (sourceCoefficient 12 44 1 2) v1129_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1129_mb : Scalar.QComplex := ((-572171748829386485859585 : Int)/10^30,(-431477120514136481436397816 : Int)/10^30)
theorem v1129_mb_checked : Scalar.distance (sourceCoefficient 12 44 3 1) v1129_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1129_mg : Scalar.QComplex := ((-93086345774154079404642 : Int)/10^30,(123439632651367218814 : Int)/10^30)
theorem v1129_mg_checked : Scalar.distance (sourceCoefficient 12 44 3 2) v1129_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1129_upper : Scalar.QComplex := ((999997604072652773201359129059 : Int)/10^30,(-2189029226389118837727643722 : Int)/10^30)
theorem v1129_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 44 5) 1) 14) v1129_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1129 : Material (12 : Basis) (44 : Basis) where
  plus := ![v1129_pa,v1129_pb,v1129_pg]
  minus := ![(Primitive.Addresses.material1129 1).one,v1129_mb,v1129_mg]
  upper := v1129_upper
  lower := (Primitive.Addresses.material1129 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1129_pa_checked.trans (by decide +kernel)
    · exact v1129_pb_checked.trans (by decide +kernel)
    · exact v1129_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 44 Primitive.Addresses.material1129
    · exact v1129_mb_checked.trans (by decide +kernel)
    · exact v1129_mg_checked.trans (by decide +kernel)
  upper_error := v1129_upper_checked
  lower_error := reuse_lower_error 12 44 Primitive.Addresses.material1129

def v1130_pa : Scalar.QComplex := ((999999891406082575621563976380 : Int)/10^30,(-466034143659150762093451799 : Int)/10^30)
theorem v1130_pa_checked : Scalar.distance (sourceCoefficient 12 45 1 0) v1130_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1130_pb : Scalar.QComplex := ((-201083247061363212216597 : Int)/10^30,(-431477452802287478684288922 : Int)/10^30)
theorem v1130_pb_checked : Scalar.distance (sourceCoefficient 12 45 1 1) v1130_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1130_pg : Scalar.QComplex := ((-93086417486150289464476 : Int)/10^30,(43381453570418234322 : Int)/10^30)
theorem v1130_pg_checked : Scalar.distance (sourceCoefficient 12 45 1 2) v1130_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1130_mb : Scalar.QComplex := ((-573428780934167978059927 : Int)/10^30,(-431477118617726545936683723 : Int)/10^30)
theorem v1130_mb_checked : Scalar.distance (sourceCoefficient 12 45 3 1) v1130_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1130_mg : Scalar.QComplex := ((-93086345389582196795292 : Int)/10^30,(123710823251455868243 : Int)/10^30)
theorem v1130_mg_checked : Scalar.distance (sourceCoefficient 12 45 3 2) v1130_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1130_upper : Scalar.QComplex := ((999997597691058896758538721948 : Int)/10^30,(-2191942542841448300443364481 : Int)/10^30)
theorem v1130_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 45 5) 1) 14) v1130_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1130 : Material (12 : Basis) (45 : Basis) where
  plus := ![v1130_pa,v1130_pb,v1130_pg]
  minus := ![(Primitive.Addresses.material1130 1).one,v1130_mb,v1130_mg]
  upper := v1130_upper
  lower := (Primitive.Addresses.material1130 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1130_pa_checked.trans (by decide +kernel)
    · exact v1130_pb_checked.trans (by decide +kernel)
    · exact v1130_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 45 Primitive.Addresses.material1130
    · exact v1130_mb_checked.trans (by decide +kernel)
    · exact v1130_mg_checked.trans (by decide +kernel)
  upper_error := v1130_upper_checked
  lower_error := reuse_lower_error 12 45 Primitive.Addresses.material1130

def v1131_pa : Scalar.QComplex := ((999999883645892278688599803164 : Int)/10^30,(-482398385055696902642027819 : Int)/10^30)
theorem v1131_pa_checked : Scalar.distance (sourceCoefficient 12 46 1 0) v1131_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1131_pb : Scalar.QComplex := ((-208144048395130722198490 : Int)/10^30,(-431477448152492749866103081 : Int)/10^30)
theorem v1131_pb_checked : Scalar.distance (sourceCoefficient 12 46 1 1) v1131_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1131_pg : Scalar.QComplex := ((-93086416623395585276010 : Int)/10^30,(44904742274599028454 : Int)/10^30)
theorem v1131_pg_checked : Scalar.distance (sourceCoefficient 12 46 1 2) v1131_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1131_mb : Scalar.QComplex := ((-580489575626313024928282 : Int)/10^30,(-431477107874780004095330190 : Int)/10^30)
theorem v1131_mb_checked : Scalar.distance (sourceCoefficient 12 46 3 1) v1131_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1131_mg : Scalar.QComplex := ((-93086343212298268518254 : Int)/10^30,(125234110643928207390 : Int)/10^30)
theorem v1131_mg_checked : Scalar.distance (sourceCoefficient 12 46 3 2) v1131_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1131_upper : Scalar.QComplex := ((999997561687684059661615115433 : Int)/10^30,(-2208306746471994706121728667 : Int)/10^30)
theorem v1131_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 46 5) 1) 14) v1131_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1131 : Material (12 : Basis) (46 : Basis) where
  plus := ![v1131_pa,v1131_pb,v1131_pg]
  minus := ![(Primitive.Addresses.material1131 1).one,v1131_mb,v1131_mg]
  upper := v1131_upper
  lower := (Primitive.Addresses.material1131 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1131_pa_checked.trans (by decide +kernel)
    · exact v1131_pb_checked.trans (by decide +kernel)
    · exact v1131_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 46 Primitive.Addresses.material1131
    · exact v1131_mb_checked.trans (by decide +kernel)
    · exact v1131_mg_checked.trans (by decide +kernel)
  upper_error := v1131_upper_checked
  lower_error := reuse_lower_error 12 46 Primitive.Addresses.material1131

def v1132_pa : Scalar.QComplex := ((999999881738432748971760845570 : Int)/10^30,(-486336427297254991091820034 : Int)/10^30)
theorem v1132_pa_checked : Scalar.distance (sourceCoefficient 12 47 1 0) v1132_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1132_pb : Scalar.QComplex := ((-209843224854828067348995 : Int)/10^30,(-431477447010525070826475753 : Int)/10^30)
theorem v1132_pb_checked : Scalar.distance (sourceCoefficient 12 47 1 1) v1132_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1132_pg : Scalar.QComplex := ((-93086416411432934798393 : Int)/10^30,(45271320541298176079 : Int)/10^30)
theorem v1132_pg_checked : Scalar.distance (sourceCoefficient 12 47 1 2) v1132_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1132_mb : Scalar.QComplex := ((-582188750467862643236771 : Int)/10^30,(-431477105266499993610540794 : Int)/10^30)
theorem v1132_mb_checked : Scalar.distance (sourceCoefficient 12 47 3 1) v1132_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1132_mg : Scalar.QComplex := ((-93086342683995162874904 : Int)/10^30,(125600688591219291950 : Int)/10^30)
theorem v1132_mg_checked : Scalar.distance (sourceCoefficient 12 47 3 2) v1132_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1132_upper : Scalar.QComplex := ((999997552983523718353839363468 : Int)/10^30,(-2212244779556199365793494727 : Int)/10^30)
theorem v1132_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 47 5) 1) 14) v1132_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1132 : Material (12 : Basis) (47 : Basis) where
  plus := ![v1132_pa,v1132_pb,v1132_pg]
  minus := ![(Primitive.Addresses.material1132 1).one,v1132_mb,v1132_mg]
  upper := v1132_upper
  lower := (Primitive.Addresses.material1132 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1132_pa_checked.trans (by decide +kernel)
    · exact v1132_pb_checked.trans (by decide +kernel)
    · exact v1132_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 47 Primitive.Addresses.material1132
    · exact v1132_mb_checked.trans (by decide +kernel)
    · exact v1132_mg_checked.trans (by decide +kernel)
  upper_error := v1132_upper_checked
  lower_error := reuse_lower_error 12 47 Primitive.Addresses.material1132

def v1133_pa : Scalar.QComplex := ((999999868021730415749269142408 : Int)/10^30,(-513766991690044076601509922 : Int)/10^30)
theorem v1133_pa_checked : Scalar.distance (sourceCoefficient 12 48 1 0) v1133_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1133_pb : Scalar.QComplex := ((-221678894975615827029851 : Int)/10^30,(-431477438808598768000953202 : Int)/10^30)
theorem v1133_pb_checked : Scalar.distance (sourceCoefficient 12 48 1 1) v1133_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1133_pg : Scalar.QComplex := ((-93086414888276760937754 : Int)/10^30,(47824733656186873119 : Int)/10^30)
theorem v1133_pg_checked : Scalar.distance (sourceCoefficient 12 48 1 2) v1133_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1133_mb : Scalar.QComplex := ((-594024409103796501811432 : Int)/10^30,(-431477086850926489291358426 : Int)/10^30)
theorem v1133_mb_checked : Scalar.distance (sourceCoefficient 12 48 3 1) v1133_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1133_mg : Scalar.QComplex := ((-93086338957359039463615 : Int)/10^30,(128154099440940411938 : Int)/10^30)
theorem v1133_mg_checked : Scalar.distance (sourceCoefficient 12 48 3 2) v1133_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1133_upper : Scalar.QComplex := ((999997491924176153956998561589 : Int)/10^30,(-2239675279420601151059227486 : Int)/10^30)
theorem v1133_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 48 5) 1) 14) v1133_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1133 : Material (12 : Basis) (48 : Basis) where
  plus := ![v1133_pa,v1133_pb,v1133_pg]
  minus := ![(Primitive.Addresses.material1133 1).one,v1133_mb,v1133_mg]
  upper := v1133_upper
  lower := (Primitive.Addresses.material1133 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1133_pa_checked.trans (by decide +kernel)
    · exact v1133_pb_checked.trans (by decide +kernel)
    · exact v1133_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 48 Primitive.Addresses.material1133
    · exact v1133_mb_checked.trans (by decide +kernel)
    · exact v1133_mg_checked.trans (by decide +kernel)
  upper_error := v1133_upper_checked
  lower_error := reuse_lower_error 12 48 Primitive.Addresses.material1133

def v1134_pa : Scalar.QComplex := ((999999856456290979535377465156 : Int)/10^30,(-535805372720480328814974640 : Int)/10^30)
theorem v1134_pa_checked : Scalar.distance (sourceCoefficient 12 49 1 0) v1134_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1134_pb : Scalar.QComplex := ((-231187959408109504517515 : Int)/10^30,(-431477431905369788247357238 : Int)/10^30)
theorem v1134_pb_checked : Scalar.distance (sourceCoefficient 12 49 1 1) v1134_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1134_pg : Scalar.QComplex := ((-93086413605336960269644 : Int)/10^30,(49876207696436205687 : Int)/10^30)
theorem v1134_pg_checked : Scalar.distance (sourceCoefficient 12 49 1 2) v1134_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1134_mb : Scalar.QComplex := ((-603533464038455205732542 : Int)/10^30,(-431477071741805747047183170 : Int)/10^30)
theorem v1134_mb_checked : Scalar.distance (sourceCoefficient 12 49 3 1) v1134_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1134_mg : Scalar.QComplex := ((-93086335904090014718363 : Int)/10^30,(130205571610212935813 : Int)/10^30)
theorem v1134_mg_checked : Scalar.distance (sourceCoefficient 12 49 3 2) v1134_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1134_upper : Scalar.QComplex := ((999997442322507590882961217495 : Int)/10^30,(-2261713607666558410092229303 : Int)/10^30)
theorem v1134_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 49 5) 1) 14) v1134_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1134 : Material (12 : Basis) (49 : Basis) where
  plus := ![v1134_pa,v1134_pb,v1134_pg]
  minus := ![(Primitive.Addresses.material1134 1).one,v1134_mb,v1134_mg]
  upper := v1134_upper
  lower := (Primitive.Addresses.material1134 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1134_pa_checked.trans (by decide +kernel)
    · exact v1134_pb_checked.trans (by decide +kernel)
    · exact v1134_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 49 Primitive.Addresses.material1134
    · exact v1134_mb_checked.trans (by decide +kernel)
    · exact v1134_mg_checked.trans (by decide +kernel)
  upper_error := v1134_upper_checked
  lower_error := reuse_lower_error 12 49 Primitive.Addresses.material1134

def v1135_pa : Scalar.QComplex := ((999999855073125493871695822397 : Int)/10^30,(-538380653449265071416213243 : Int)/10^30)
theorem v1135_pa_checked : Scalar.distance (sourceCoefficient 12 50 1 0) v1135_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1135_pb : Scalar.QComplex := ((-232299134960098041640790 : Int)/10^30,(-431477431080464034630995434 : Int)/10^30)
theorem v1135_pb_checked : Scalar.distance (sourceCoefficient 12 50 1 1) v1135_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1135_pg : Scalar.QComplex := ((-93086413451977915130152 : Int)/10^30,(50115931364669623922 : Int)/10^30)
theorem v1135_pg_checked : Scalar.distance (sourceCoefficient 12 50 1 2) v1135_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1135_mb : Scalar.QComplex := ((-604644638464845788624078 : Int)/10^30,(-431477069958005844703911639 : Int)/10^30)
theorem v1135_mb_checked : Scalar.distance (sourceCoefficient 12 50 3 1) v1135_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1135_mg : Scalar.QComplex := ((-93086335543860297749235 : Int)/10^30,(130445295056844327532 : Int)/10^30)
theorem v1135_mg_checked : Scalar.distance (sourceCoefficient 12 50 3 2) v1135_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1135_upper : Scalar.QComplex := ((999997436494643255042043069604 : Int)/10^30,(-2264288882172546872430577541 : Int)/10^30)
theorem v1135_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 50 5) 1) 14) v1135_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1135 : Material (12 : Basis) (50 : Basis) where
  plus := ![v1135_pa,v1135_pb,v1135_pg]
  minus := ![(Primitive.Addresses.material1135 1).one,v1135_mb,v1135_mg]
  upper := v1135_upper
  lower := (Primitive.Addresses.material1135 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1135_pa_checked.trans (by decide +kernel)
    · exact v1135_pb_checked.trans (by decide +kernel)
    · exact v1135_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 50 Primitive.Addresses.material1135
    · exact v1135_mb_checked.trans (by decide +kernel)
    · exact v1135_mg_checked.trans (by decide +kernel)
  upper_error := v1135_upper_checked
  lower_error := reuse_lower_error 12 50 Primitive.Addresses.material1135

def v1136_pa : Scalar.QComplex := ((999999848925991098473030505642 : Int)/10^30,(-549679902288320682795254136 : Int)/10^30)
theorem v1136_pa_checked : Scalar.distance (sourceCoefficient 12 51 1 0) v1136_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1136_pb : Scalar.QComplex := ((-237174505972562128147859 : Int)/10^30,(-431477427416028820261318664 : Int)/10^30)
theorem v1136_pb_checked : Scalar.distance (sourceCoefficient 12 51 1 1) v1136_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1136_pg : Scalar.QComplex := ((-93086412770590143314038 : Int)/10^30,(51167738006223583571 : Int)/10^30)
theorem v1136_pg_checked : Scalar.distance (sourceCoefficient 12 51 1 2) v1136_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1136_mb : Scalar.QComplex := ((-609520004499743881762640 : Int)/10^30,(-431477062086346389573693601 : Int)/10^30)
theorem v1136_mb_checked : Scalar.distance (sourceCoefficient 12 51 3 1) v1136_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1136_mg : Scalar.QComplex := ((-93086333954811019596481 : Int)/10^30,(131497100718755646081 : Int)/10^30)
theorem v1136_mg_checked : Scalar.distance (sourceCoefficient 12 51 3 2) v1136_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1136_upper : Scalar.QComplex := ((999997410846039578715332355419 : Int)/10^30,(-2275588103573302338260896289 : Int)/10^30)
theorem v1136_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 51 5) 1) 14) v1136_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1136 : Material (12 : Basis) (51 : Basis) where
  plus := ![v1136_pa,v1136_pb,v1136_pg]
  minus := ![(Primitive.Addresses.material1136 1).one,v1136_mb,v1136_mg]
  upper := v1136_upper
  lower := (Primitive.Addresses.material1136 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1136_pa_checked.trans (by decide +kernel)
    · exact v1136_pb_checked.trans (by decide +kernel)
    · exact v1136_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 51 Primitive.Addresses.material1136
    · exact v1136_mb_checked.trans (by decide +kernel)
    · exact v1136_mg_checked.trans (by decide +kernel)
  upper_error := v1136_upper_checked
  lower_error := reuse_lower_error 12 51 Primitive.Addresses.material1136

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
