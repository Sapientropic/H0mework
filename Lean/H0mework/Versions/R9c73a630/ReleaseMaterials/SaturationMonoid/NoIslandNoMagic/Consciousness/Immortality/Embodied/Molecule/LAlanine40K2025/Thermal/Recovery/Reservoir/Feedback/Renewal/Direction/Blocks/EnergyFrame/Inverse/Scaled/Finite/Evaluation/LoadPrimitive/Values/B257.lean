import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B171
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B172

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4113_pa : Scalar.QComplex := ((999998079442839657642882303159 : Int)/10^30,(-1959875157285511411279585135 : Int)/10^30)
theorem v4113_pa_checked : Scalar.distance (sourceCoefficient 61 88 1 0) v4113_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4113_pb : Scalar.QComplex := ((-845642030052259640852602 : Int)/10^30,(-431476669728107699377465646 : Int)/10^30)
theorem v4113_pb_checked : Scalar.distance (sourceCoefficient 61 88 1 1) v4113_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4113_pg : Scalar.QComplex := ((-93086248681825201263877 : Int)/10^30,(182437776658588674198 : Int)/10^30)
theorem v4113_pg_checked : Scalar.distance (sourceCoefficient 61 88 1 2) v4113_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4113_mb : Scalar.QComplex := ((-1217986648168622909850787 : Int)/10^30,(-431475779318638469738857448 : Int)/10^30)
theorem v4113_mb_checked : Scalar.distance (sourceCoefficient 61 88 3 1) v4113_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4113_mg : Scalar.QComplex := ((-93086056585976001372012 : Int)/10^30,(262766948892072147936 : Int)/10^30)
theorem v4113_mg_checked : Scalar.distance (sourceCoefficient 61 88 3 2) v4113_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4113_upper : Scalar.QComplex := ((999993207496445364214039919787 : Int)/10^30,(-3685778204282920790245776546 : Int)/10^30)
theorem v4113_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 88 5) 1) 14) v4113_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4113 : Material (61 : Basis) (88 : Basis) where
  plus := ![v4113_pa,v4113_pb,v4113_pg]
  minus := ![(Primitive.Addresses.material4113 1).one,v4113_mb,v4113_mg]
  upper := v4113_upper
  lower := (Primitive.Addresses.material4113 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4113_pa_checked.trans (by decide +kernel)
    · exact v4113_pb_checked.trans (by decide +kernel)
    · exact v4113_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 88 Primitive.Addresses.material4113
    · exact v4113_mb_checked.trans (by decide +kernel)
    · exact v4113_mg_checked.trans (by decide +kernel)
  upper_error := v4113_upper_checked
  lower_error := reuse_lower_error 61 88 Primitive.Addresses.material4113

def v4114_pa : Scalar.QComplex := ((999998047780023132651168717701 : Int)/10^30,(-1975964610657756588611156619 : Int)/10^30)
theorem v4114_pa_checked : Scalar.distance (sourceCoefficient 61 89 1 0) v4114_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4114_pb : Scalar.QComplex := ((-852584264544147590913161 : Int)/10^30,(-431476654750566495509071150 : Int)/10^30)
theorem v4114_pb_checked : Scalar.distance (sourceCoefficient 61 89 1 1) v4114_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4114_pg : Scalar.QComplex := ((-93086245592517763129415 : Int)/10^30,(183935486112342115409 : Int)/10^30)
theorem v4114_pg_checked : Scalar.distance (sourceCoefficient 61 89 1 2) v4114_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4114_mb : Scalar.QComplex := ((-1224928867150656187267868 : Int)/10^30,(-431475758350267142829043270 : Int)/10^30)
theorem v4114_mb_checked : Scalar.distance (sourceCoefficient 61 89 3 1) v4114_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4114_mg : Scalar.QComplex := ((-93086052204213909268452 : Int)/10^30,(264264655122226728943 : Int)/10^30)
theorem v4114_mg_checked : Scalar.distance (sourceCoefficient 61 89 3 2) v4114_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4114_upper : Scalar.QComplex := ((999993148064739100580963149838 : Int)/10^30,(-3701867579044666275717787446 : Int)/10^30)
theorem v4114_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 89 5) 1) 14) v4114_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4114 : Material (61 : Basis) (89 : Basis) where
  plus := ![v4114_pa,v4114_pb,v4114_pg]
  minus := ![(Primitive.Addresses.material4114 1).one,v4114_mb,v4114_mg]
  upper := v4114_upper
  lower := (Primitive.Addresses.material4114 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4114_pa_checked.trans (by decide +kernel)
    · exact v4114_pb_checked.trans (by decide +kernel)
    · exact v4114_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 89 Primitive.Addresses.material4114
    · exact v4114_mb_checked.trans (by decide +kernel)
    · exact v4114_mg_checked.trans (by decide +kernel)
  upper_error := v4114_upper_checked
  lower_error := reuse_lower_error 61 89 Primitive.Addresses.material4114

def v4115_pa : Scalar.QComplex := ((999997995660641274679510243152 : Int)/10^30,(-2002167500503985316870521785 : Int)/10^30)
theorem v4115_pa_checked : Scalar.distance (sourceCoefficient 61 90 1 0) v4115_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4115_pb : Scalar.QComplex := ((-863890217421709077858068 : Int)/10^30,(-431476630039737831944231205 : Int)/10^30)
theorem v4115_pb_checked : Scalar.distance (sourceCoefficient 61 90 1 1) v4115_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4115_pg : Scalar.QComplex := ((-93086240501172272312962 : Int)/10^30,(186374619033529330282 : Int)/10^30)
theorem v4115_pg_checked : Scalar.distance (sourceCoefficient 61 90 1 2) v4115_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4115_mb : Scalar.QComplex := ((-1236234794494162508076739 : Int)/10^30,(-431475723882919548114659942 : Int)/10^30)
theorem v4115_mb_checked : Scalar.distance (sourceCoefficient 61 90 3 1) v4115_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4115_mg : Scalar.QComplex := ((-93086045008008457676826 : Int)/10^30,(266703782741611430490 : Int)/10^30)
theorem v4115_mg_checked : Scalar.distance (sourceCoefficient 61 90 3 2) v4115_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4115_upper : Scalar.QComplex := ((999993050721624101313328831405 : Int)/10^30,(-3728070339911443732207185487 : Int)/10^30)
theorem v4115_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 90 5) 1) 14) v4115_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4115 : Material (61 : Basis) (90 : Basis) where
  plus := ![v4115_pa,v4115_pb,v4115_pg]
  minus := ![(Primitive.Addresses.material4115 1).one,v4115_mb,v4115_mg]
  upper := v4115_upper
  lower := (Primitive.Addresses.material4115 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4115_pa_checked.trans (by decide +kernel)
    · exact v4115_pb_checked.trans (by decide +kernel)
    · exact v4115_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 90 Primitive.Addresses.material4115
    · exact v4115_mb_checked.trans (by decide +kernel)
    · exact v4115_mg_checked.trans (by decide +kernel)
  upper_error := v4115_upper_checked
  lower_error := reuse_lower_error 61 90 Primitive.Addresses.material4115

def v4116_pa : Scalar.QComplex := ((999997965997560281209493242890 : Int)/10^30,(-2016928541687001917449250831 : Int)/10^30)
theorem v4116_pa_checked : Scalar.distance (sourceCoefficient 61 91 1 0) v4116_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4116_pb : Scalar.QComplex := ((-870259271880066161566810 : Int)/10^30,(-431476615945293773858638601 : Int)/10^30)
theorem v4116_pb_checked : Scalar.distance (sourceCoefficient 61 91 1 1) v4116_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4116_pg : Scalar.QComplex := ((-93086237600198100886869 : Int)/10^30,(187748671335352870721 : Int)/10^30)
theorem v4116_pg_checked : Scalar.distance (sourceCoefficient 61 91 1 2) v4116_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4116_mb : Scalar.QComplex := ((-1242603834418159104838730 : Int)/10^30,(-431475704292273592036948637 : Int)/10^30)
theorem v4116_mb_checked : Scalar.distance (sourceCoefficient 61 91 3 1) v4116_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4116_mg : Scalar.QComplex := ((-93086040921290114960677 : Int)/10^30,(268077832028402446754 : Int)/10^30)
theorem v4116_mg_checked : Scalar.distance (sourceCoefficient 61 91 3 2) v4116_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4116_upper : Scalar.QComplex := ((999992995582369316826889406799 : Int)/10^30,(-3742831307913836663341082182 : Int)/10^30)
theorem v4116_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 91 5) 1) 14) v4116_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4116 : Material (61 : Basis) (91 : Basis) where
  plus := ![v4116_pa,v4116_pb,v4116_pg]
  minus := ![(Primitive.Addresses.material4116 1).one,v4116_mb,v4116_mg]
  upper := v4116_upper
  lower := (Primitive.Addresses.material4116 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4116_pa_checked.trans (by decide +kernel)
    · exact v4116_pb_checked.trans (by decide +kernel)
    · exact v4116_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 91 Primitive.Addresses.material4116
    · exact v4116_mb_checked.trans (by decide +kernel)
    · exact v4116_mg_checked.trans (by decide +kernel)
  upper_error := v4116_upper_checked
  lower_error := reuse_lower_error 61 91 Primitive.Addresses.material4116

def v4117_pa : Scalar.QComplex := ((999997901033785491798297672594 : Int)/10^30,(-2048884580291733699728342206 : Int)/10^30)
theorem v4117_pa_checked : Scalar.distance (sourceCoefficient 61 92 1 0) v4117_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4117_pb : Scalar.QComplex := ((-884047577355435339305280 : Int)/10^30,(-431476585002929834110760056 : Int)/10^30)
theorem v4117_pb_checked : Scalar.distance (sourceCoefficient 61 92 1 1) v4117_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4117_pg : Scalar.QComplex := ((-93086231238841388712018 : Int)/10^30,(190723344144588486543 : Int)/10^30)
theorem v4117_pg_checked : Scalar.distance (sourceCoefficient 61 92 1 2) v4117_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4117_mb : Scalar.QComplex := ((-1256392108057645509743506 : Int)/10^30,(-431475661451234550527624765 : Int)/10^30)
theorem v4117_mb_checked : Scalar.distance (sourceCoefficient 61 92 3 1) v4117_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4117_mg : Scalar.QComplex := ((-93086031992927111329290 : Int)/10^30,(271052498240467088698 : Int)/10^30)
theorem v4117_mg_checked : Scalar.distance (sourceCoefficient 61 92 3 2) v4117_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4117_upper : Scalar.QComplex := ((999992875465467680736253519784 : Int)/10^30,(-3774787186802220944946096835 : Int)/10^30)
theorem v4117_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 92 5) 1) 14) v4117_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4117 : Material (61 : Basis) (92 : Basis) where
  plus := ![v4117_pa,v4117_pb,v4117_pg]
  minus := ![(Primitive.Addresses.material4117 1).one,v4117_mb,v4117_mg]
  upper := v4117_upper
  lower := (Primitive.Addresses.material4117 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4117_pa_checked.trans (by decide +kernel)
    · exact v4117_pb_checked.trans (by decide +kernel)
    · exact v4117_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 92 Primitive.Addresses.material4117
    · exact v4117_mb_checked.trans (by decide +kernel)
    · exact v4117_mg_checked.trans (by decide +kernel)
  upper_error := v4117_upper_checked
  lower_error := reuse_lower_error 61 92 Primitive.Addresses.material4117

def v4118_pa : Scalar.QComplex := ((999997822609409998378995780342 : Int)/10^30,(-2086810110904550074279131911 : Int)/10^30)
theorem v4118_pa_checked : Scalar.distance (sourceCoefficient 61 93 1 0) v4118_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4118_pb : Scalar.QComplex := ((-900411582526594475742155 : Int)/10^30,(-431476547518065939770714232 : Int)/10^30)
theorem v4118_pb_checked : Scalar.distance (sourceCoefficient 61 93 1 1) v4118_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4118_pg : Scalar.QComplex := ((-93086223545249595477780 : Int)/10^30,(194253695446316586589 : Int)/10^30)
theorem v4118_pg_checked : Scalar.distance (sourceCoefficient 61 93 1 2) v4118_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4118_mb : Scalar.QComplex := ((-1272756074787988363759235 : Int)/10^30,(-431475609844985158239122009 : Int)/10^30)
theorem v4118_mb_checked : Scalar.distance (sourceCoefficient 61 93 3 1) v4118_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4118_mg : Scalar.QComplex := ((-93086021252804010499772 : Int)/10^30,(274582841588460843036 : Int)/10^30)
theorem v4118_mg_checked : Scalar.distance (sourceCoefficient 61 93 3 2) v4118_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4118_upper : Scalar.QComplex := ((999992731585183730751692389878 : Int)/10^30,(-3812712525576057019609388275 : Int)/10^30)
theorem v4118_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 93 5) 1) 14) v4118_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4118 : Material (61 : Basis) (93 : Basis) where
  plus := ![v4118_pa,v4118_pb,v4118_pg]
  minus := ![(Primitive.Addresses.material4118 1).one,v4118_mb,v4118_mg]
  upper := v4118_upper
  lower := (Primitive.Addresses.material4118 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4118_pa_checked.trans (by decide +kernel)
    · exact v4118_pb_checked.trans (by decide +kernel)
    · exact v4118_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 93 Primitive.Addresses.material4118
    · exact v4118_mb_checked.trans (by decide +kernel)
    · exact v4118_mg_checked.trans (by decide +kernel)
  upper_error := v4118_upper_checked
  lower_error := reuse_lower_error 61 93 Primitive.Addresses.material4118

def v4119_pa : Scalar.QComplex := ((999997728119874099513038018463 : Int)/10^30,(-2131608568748415277947611494 : Int)/10^30)
theorem v4119_pa_checked : Scalar.distance (sourceCoefficient 61 94 1 0) v4119_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4119_pb : Scalar.QComplex := ((-919741098789466244629563 : Int)/10^30,(-431476502174117422041751622 : Int)/10^30)
theorem v4119_pb_checked : Scalar.distance (sourceCoefficient 61 94 1 1) v4119_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4119_pg : Scalar.QComplex := ((-93086214256178959694960 : Int)/10^30,(198423822735961341374 : Int)/10^30)
theorem v4119_pg_checked : Scalar.distance (sourceCoefficient 61 94 1 2) v4119_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4119_mb : Scalar.QComplex := ((-1292085544723812470275836 : Int)/10^30,(-431475547820551558371612667 : Int)/10^30)
theorem v4119_mb_checked : Scalar.distance (sourceCoefficient 61 94 3 1) v4119_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4119_mg : Scalar.QComplex := ((-93086008365104798060142 : Int)/10^30,(278752959309327029185 : Int)/10^30)
theorem v4119_mg_checked : Scalar.distance (sourceCoefficient 61 94 3 2) v4119_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4119_upper : Scalar.QComplex := ((999992559777714408787304608678 : Int)/10^30,(-3857510753617514723655308368 : Int)/10^30)
theorem v4119_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 94 5) 1) 14) v4119_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4119 : Material (61 : Basis) (94 : Basis) where
  plus := ![v4119_pa,v4119_pb,v4119_pg]
  minus := ![(Primitive.Addresses.material4119 1).one,v4119_mb,v4119_mg]
  upper := v4119_upper
  lower := (Primitive.Addresses.material4119 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4119_pa_checked.trans (by decide +kernel)
    · exact v4119_pb_checked.trans (by decide +kernel)
    · exact v4119_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 94 Primitive.Addresses.material4119
    · exact v4119_mb_checked.trans (by decide +kernel)
    · exact v4119_mg_checked.trans (by decide +kernel)
  upper_error := v4119_upper_checked
  lower_error := reuse_lower_error 61 94 Primitive.Addresses.material4119

def v4120_pa : Scalar.QComplex := ((999997632764458358060793633638 : Int)/10^30,(-2175882689733012421698191730 : Int)/10^30)
theorem v4120_pa_checked : Scalar.distance (sourceCoefficient 61 95 1 0) v4120_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4120_pb : Scalar.QComplex := ((-938844374596353378976991 : Int)/10^30,(-431476456226498413861130413 : Int)/10^30)
theorem v4120_pb_checked : Scalar.distance (sourceCoefficient 61 95 1 1) v4120_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4120_pg : Scalar.QComplex := ((-93086204861689926255463 : Int)/10^30,(202545141283549327583 : Int)/10^30)
theorem v4120_pg_checked : Scalar.distance (sourceCoefficient 61 95 1 2) v4120_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4120_mb : Scalar.QComplex := ((-1311188773766951158764997 : Int)/10^30,(-431475485387683016849411206 : Int)/10^30)
theorem v4120_mb_checked : Scalar.distance (sourceCoefficient 61 95 3 1) v4120_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4120_mg : Scalar.QComplex := ((-93085995414106973346774 : Int)/10^30,(282874268215338842785 : Int)/10^30)
theorem v4120_mg_checked : Scalar.distance (sourceCoefficient 61 95 3 2) v4120_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4120_upper : Scalar.QComplex := ((999992388009324385491317636219 : Int)/10^30,(-3901784644086212470430721217 : Int)/10^30)
theorem v4120_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 95 5) 1) 14) v4120_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4120 : Material (61 : Basis) (95 : Basis) where
  plus := ![v4120_pa,v4120_pb,v4120_pg]
  minus := ![(Primitive.Addresses.material4120 1).one,v4120_mb,v4120_mg]
  upper := v4120_upper
  lower := (Primitive.Addresses.material4120 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4120_pa_checked.trans (by decide +kernel)
    · exact v4120_pb_checked.trans (by decide +kernel)
    · exact v4120_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 95 Primitive.Addresses.material4120
    · exact v4120_mb_checked.trans (by decide +kernel)
    · exact v4120_mg_checked.trans (by decide +kernel)
  upper_error := v4120_upper_checked
  lower_error := reuse_lower_error 61 95 Primitive.Addresses.material4120

def v4121_pa : Scalar.QComplex := ((999997586270198182400441860285 : Int)/10^30,(-2197146735551279227271792228 : Int)/10^30)
theorem v4121_pa_checked : Scalar.distance (sourceCoefficient 61 96 1 0) v4121_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4121_pb : Scalar.QComplex := ((-948019326160817322144898 : Int)/10^30,(-431476433757826863463000964 : Int)/10^30)
theorem v4121_pb_checked : Scalar.distance (sourceCoefficient 61 96 1 1) v4121_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4121_pg : Scalar.QComplex := ((-93086200274015790089394 : Int)/10^30,(204524534723891053024 : Int)/10^30)
theorem v4121_pg_checked : Scalar.distance (sourceCoefficient 61 96 1 2) v4121_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4121_mb : Scalar.QComplex := ((-1320363702525709721889494 : Int)/10^30,(-431475455001449856911035791 : Int)/10^30)
theorem v4121_mb_checked : Scalar.distance (sourceCoefficient 61 96 3 1) v4121_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4121_mg : Scalar.QComplex := ((-93085989118307154937747 : Int)/10^30,(284853656959705769300 : Int)/10^30)
theorem v4121_mg_checked : Scalar.distance (sourceCoefficient 61 96 3 2) v4121_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4121_upper : Scalar.QComplex := ((999992304815319434409041540735 : Int)/10^30,(-3923048577989305743126877338 : Int)/10^30)
theorem v4121_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 96 5) 1) 14) v4121_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4121 : Material (61 : Basis) (96 : Basis) where
  plus := ![v4121_pa,v4121_pb,v4121_pg]
  minus := ![(Primitive.Addresses.material4121 1).one,v4121_mb,v4121_mg]
  upper := v4121_upper
  lower := (Primitive.Addresses.material4121 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4121_pa_checked.trans (by decide +kernel)
    · exact v4121_pb_checked.trans (by decide +kernel)
    · exact v4121_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 96 Primitive.Addresses.material4121
    · exact v4121_mb_checked.trans (by decide +kernel)
    · exact v4121_mg_checked.trans (by decide +kernel)
  upper_error := v4121_upper_checked
  lower_error := reuse_lower_error 61 96 Primitive.Addresses.material4121

def v4122_pa : Scalar.QComplex := ((999997422845709232710864299872 : Int)/10^30,(-2270308776314433369184208339 : Int)/10^30)
theorem v4122_pa_checked : Scalar.distance (sourceCoefficient 61 97 1 0) v4122_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4122_pb : Scalar.QComplex := ((-979587078858526589602397 : Int)/10^30,(-431476354463870761735705015 : Int)/10^30)
theorem v4122_pb_checked : Scalar.distance (sourceCoefficient 61 97 1 1) v4122_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4122_pg : Scalar.QComplex := ((-93086184114324359472670 : Int)/10^30,(211334925391081543728 : Int)/10^30)
theorem v4122_pg_checked : Scalar.distance (sourceCoefficient 61 97 1 2) v4122_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4122_mb : Scalar.QComplex := ((-1351931375042189093840348 : Int)/10^30,(-431475348465974460627748703 : Int)/10^30)
theorem v4122_mb_checked : Scalar.distance (sourceCoefficient 61 97 3 1) v4122_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4122_mg : Scalar.QComplex := ((-93085967081561324136633 : Int)/10^30,(291664031145990665241 : Int)/10^30)
theorem v4122_mg_checked : Scalar.distance (sourceCoefficient 61 97 3 2) v4122_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4122_upper : Scalar.QComplex := ((999992015120028737585522494582 : Int)/10^30,(-3996210227730352212000929134 : Int)/10^30)
theorem v4122_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 97 5) 1) 14) v4122_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4122 : Material (61 : Basis) (97 : Basis) where
  plus := ![v4122_pa,v4122_pb,v4122_pg]
  minus := ![(Primitive.Addresses.material4122 1).one,v4122_mb,v4122_mg]
  upper := v4122_upper
  lower := (Primitive.Addresses.material4122 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4122_pa_checked.trans (by decide +kernel)
    · exact v4122_pb_checked.trans (by decide +kernel)
    · exact v4122_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 97 Primitive.Addresses.material4122
    · exact v4122_mb_checked.trans (by decide +kernel)
    · exact v4122_mg_checked.trans (by decide +kernel)
  upper_error := v4122_upper_checked
  lower_error := reuse_lower_error 61 97 Primitive.Addresses.material4122

def v4123_pa : Scalar.QComplex := ((999998961530471877253711089657 : Int)/10^30,(-1441158554020525438431710514 : Int)/10^30)
theorem v4123_pa_checked : Scalar.distance (sourceCoefficient 62 63 1 0) v4123_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4123_pb : Scalar.QComplex := ((-621827520193944845787598 : Int)/10^30,(-431477072880182980997737401 : Int)/10^30)
theorem v4123_pb_checked : Scalar.distance (sourceCoefficient 62 63 1 1) v4123_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4123_pg : Scalar.QComplex := ((-93086333224785992439766 : Int)/10^30,(134152304702385936491 : Int)/10^30)
theorem v4123_pg_checked : Scalar.distance (sourceCoefficient 62 63 1 2) v4123_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4123_mb : Scalar.QComplex := ((-994172569548762636049383 : Int)/10^30,(-431476375612405415813967576 : Int)/10^30)
theorem v4123_mb_checked : Scalar.distance (sourceCoefficient 62 63 3 1) v4123_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4123_mg : Scalar.QComplex := ((-93086182797092914614394 : Int)/10^30,(214481567871524863786 : Int)/10^30)
theorem v4123_mg_checked : Scalar.distance (sourceCoefficient 62 63 3 2) v4123_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4123_upper : Scalar.QComplex := ((999994984840563450625378180833 : Int)/10^30,(-3167063895988613494237735239 : Int)/10^30)
theorem v4123_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 63 5) 1) 14) v4123_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4123 : Material (62 : Basis) (63 : Basis) where
  plus := ![v4123_pa,v4123_pb,v4123_pg]
  minus := ![(Primitive.Addresses.material4123 1).one,v4123_mb,v4123_mg]
  upper := v4123_upper
  lower := (Primitive.Addresses.material4123 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4123_pa_checked.trans (by decide +kernel)
    · exact v4123_pb_checked.trans (by decide +kernel)
    · exact v4123_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 63 Primitive.Addresses.material4123
    · exact v4123_mb_checked.trans (by decide +kernel)
    · exact v4123_mg_checked.trans (by decide +kernel)
  upper_error := v4123_upper_checked
  lower_error := reuse_lower_error 62 63 Primitive.Addresses.material4123

def v4124_pa : Scalar.QComplex := ((999998909831845545829958403907 : Int)/10^30,(-1476595787763779006907622882 : Int)/10^30)
theorem v4124_pa_checked : Scalar.distance (sourceCoefficient 62 64 1 0) v4124_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4124_pb : Scalar.QComplex := ((-637117889639082858828624 : Int)/10^30,(-431477050356703901545944933 : Int)/10^30)
theorem v4124_pb_checked : Scalar.distance (sourceCoefficient 62 64 1 1) v4124_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4124_pg : Scalar.QComplex := ((-93086328388971872311582 : Int)/10^30,(137451030242287714430 : Int)/10^30)
theorem v4124_pg_checked : Scalar.distance (sourceCoefficient 62 64 1 2) v4124_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4124_mb : Scalar.QComplex := ((-1009462913863849274534052 : Int)/10^30,(-431476339894034544404525025 : Int)/10^30)
theorem v4124_mb_checked : Scalar.distance (sourceCoefficient 62 64 3 1) v4124_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4124_mg : Scalar.QComplex := ((-93086175114629023228754 : Int)/10^30,(217780288010070575326 : Int)/10^30)
theorem v4124_mg_checked : Scalar.distance (sourceCoefficient 62 64 3 2) v4124_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4124_upper : Scalar.QComplex := ((999994871980563518109170033435 : Int)/10^30,(-3202500987725131166736801056 : Int)/10^30)
theorem v4124_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 64 5) 1) 14) v4124_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4124 : Material (62 : Basis) (64 : Basis) where
  plus := ![v4124_pa,v4124_pb,v4124_pg]
  minus := ![(Primitive.Addresses.material4124 1).one,v4124_mb,v4124_mg]
  upper := v4124_upper
  lower := (Primitive.Addresses.material4124 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4124_pa_checked.trans (by decide +kernel)
    · exact v4124_pb_checked.trans (by decide +kernel)
    · exact v4124_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 64 Primitive.Addresses.material4124
    · exact v4124_mb_checked.trans (by decide +kernel)
    · exact v4124_mg_checked.trans (by decide +kernel)
  upper_error := v4124_upper_checked
  lower_error := reuse_lower_error 62 64 Primitive.Addresses.material4124

def v4125_pa : Scalar.QComplex := ((999998856076889494805524183894 : Int)/10^30,(-1512562366466357050541395950 : Int)/10^30)
theorem v4125_pa_checked : Scalar.distance (sourceCoefficient 62 65 1 0) v4125_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4125_pb : Scalar.QComplex := ((-652636659235172918292812 : Int)/10^30,(-431477026758044635033513743 : Int)/10^30)
theorem v4125_pb_checked : Scalar.distance (sourceCoefficient 62 65 1 1) v4125_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4125_pg : Scalar.QComplex := ((-93086323341470530386513 : Int)/10^30,(140799030582292174372 : Int)/10^30)
theorem v4125_pg_checked : Scalar.distance (sourceCoefficient 62 65 1 2) v4125_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4125_mb : Scalar.QComplex := ((-1024981657317012067724570 : Int)/10^30,(-431476302903384842762485856 : Int)/10^30)
theorem v4125_mb_checked : Scalar.distance (sourceCoefficient 62 65 3 1) v4125_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4125_mg : Scalar.QComplex := ((-93086167177956055633055 : Int)/10^30,(221128282747695170450 : Int)/10^30)
theorem v4125_mg_checked : Scalar.distance (sourceCoefficient 62 65 3 2) v4125_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4125_upper : Scalar.QComplex := ((999994756150635550659384321782 : Int)/10^30,(-3238467420083537631450983821 : Int)/10^30)
theorem v4125_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 65 5) 1) 14) v4125_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4125 : Material (62 : Basis) (65 : Basis) where
  plus := ![v4125_pa,v4125_pb,v4125_pg]
  minus := ![(Primitive.Addresses.material4125 1).one,v4125_mb,v4125_mg]
  upper := v4125_upper
  lower := (Primitive.Addresses.material4125 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4125_pa_checked.trans (by decide +kernel)
    · exact v4125_pb_checked.trans (by decide +kernel)
    · exact v4125_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 65 Primitive.Addresses.material4125
    · exact v4125_mb_checked.trans (by decide +kernel)
    · exact v4125_mg_checked.trans (by decide +kernel)
  upper_error := v4125_upper_checked
  lower_error := reuse_lower_error 62 65 Primitive.Addresses.material4125

def v4126_pa : Scalar.QComplex := ((999998829319937189317943459370 : Int)/10^30,(-1530149912632600404403575707 : Int)/10^30)
theorem v4126_pa_checked : Scalar.distance (sourceCoefficient 62 66 1 0) v4126_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4126_pb : Scalar.QComplex := ((-660225289637379818484848 : Int)/10^30,(-431477014947437217151369561 : Int)/10^30)
theorem v4126_pb_checked : Scalar.distance (sourceCoefficient 62 66 1 1) v4126_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4126_pg : Scalar.QComplex := ((-93086320822112986280719 : Int)/10^30,(142436192420457087103 : Int)/10^30)
theorem v4126_pg_checked : Scalar.distance (sourceCoefficient 62 66 1 2) v4126_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4126_mb : Scalar.QComplex := ((-1032570274701602780012103 : Int)/10^30,(-431476284544135564630574065 : Int)/10^30)
theorem v4126_mb_checked : Scalar.distance (sourceCoefficient 62 66 3 1) v4126_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4126_mg : Scalar.QComplex := ((-93086163245802518294913 : Int)/10^30,(222765441802177815929 : Int)/10^30)
theorem v4126_mg_checked : Scalar.distance (sourceCoefficient 62 66 3 2) v4126_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4126_upper : Scalar.QComplex := ((999994699039213943297748817315 : Int)/10^30,(-3256054893875124641473437017 : Int)/10^30)
theorem v4126_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 66 5) 1) 14) v4126_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4126 : Material (62 : Basis) (66 : Basis) where
  plus := ![v4126_pa,v4126_pb,v4126_pg]
  minus := ![(Primitive.Addresses.material4126 1).one,v4126_mb,v4126_mg]
  upper := v4126_upper
  lower := (Primitive.Addresses.material4126 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4126_pa_checked.trans (by decide +kernel)
    · exact v4126_pb_checked.trans (by decide +kernel)
    · exact v4126_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 66 Primitive.Addresses.material4126
    · exact v4126_mb_checked.trans (by decide +kernel)
    · exact v4126_mg_checked.trans (by decide +kernel)
  upper_error := v4126_upper_checked
  lower_error := reuse_lower_error 62 66 Primitive.Addresses.material4126

def v4127_pa : Scalar.QComplex := ((999998783718634345471057144592 : Int)/10^30,(-1559667032404255651119468132 : Int)/10^30)
theorem v4127_pa_checked : Scalar.distance (sourceCoefficient 62 67 1 0) v4127_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4127_pb : Scalar.QComplex := ((-672961262424913543307309 : Int)/10^30,(-431476994725784032018756708 : Int)/10^30)
theorem v4127_pb_checked : Scalar.distance (sourceCoefficient 62 67 1 1) v4127_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4127_pg : Scalar.QComplex := ((-93086316518384448364985 : Int)/10^30,(145183835626065781745 : Int)/10^30)
theorem v4127_pg_checked : Scalar.distance (sourceCoefficient 62 67 1 2) v4127_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4127_mb : Scalar.QComplex := ((-1045306225296575824006291 : Int)/10^30,(-431476253331919000223073431 : Int)/10^30)
theorem v4127_mb_checked : Scalar.distance (sourceCoefficient 62 67 3 1) v4127_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4127_mg : Scalar.QComplex := ((-93086156570983245669893 : Int)/10^30,(225513080270789476141 : Int)/10^30)
theorem v4127_mg_checked : Scalar.distance (sourceCoefficient 62 67 3 2) v4127_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4127_upper : Scalar.QComplex := ((999994602494108063545863416208 : Int)/10^30,(-3285571890980785522161915543 : Int)/10^30)
theorem v4127_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 67 5) 1) 14) v4127_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4127 : Material (62 : Basis) (67 : Basis) where
  plus := ![v4127_pa,v4127_pb,v4127_pg]
  minus := ![(Primitive.Addresses.material4127 1).one,v4127_mb,v4127_mg]
  upper := v4127_upper
  lower := (Primitive.Addresses.material4127 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4127_pa_checked.trans (by decide +kernel)
    · exact v4127_pb_checked.trans (by decide +kernel)
    · exact v4127_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 67 Primitive.Addresses.material4127
    · exact v4127_mb_checked.trans (by decide +kernel)
    · exact v4127_mg_checked.trans (by decide +kernel)
  upper_error := v4127_upper_checked
  lower_error := reuse_lower_error 62 67 Primitive.Addresses.material4127

def v4128_pa : Scalar.QComplex := ((999998705840296628809047451450 : Int)/10^30,(-1608824953776216163551023987 : Int)/10^30)
theorem v4128_pa_checked : Scalar.distance (sourceCoefficient 62 68 1 0) v4128_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4128_pb : Scalar.QComplex := ((-694171798493820108922435 : Int)/10^30,(-431476959936070739830095249 : Int)/10^30)
theorem v4128_pb_checked : Scalar.distance (sourceCoefficient 62 68 1 1) v4128_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4128_pg : Scalar.QComplex := ((-93086309140931250682353 : Int)/10^30,(149759770813917860993 : Int)/10^30)
theorem v4128_pg_checked : Scalar.distance (sourceCoefficient 62 68 1 2) v4128_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4128_mb : Scalar.QComplex := ((-1066516723445874741144231 : Int)/10^30,(-431476200238481321450893114 : Int)/10^30)
theorem v4128_mb_checked : Scalar.distance (sourceCoefficient 62 68 3 1) v4128_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4128_mg : Scalar.QComplex := ((-93086145244706820304258 : Int)/10^30,(230089007388401912941 : Int)/10^30)
theorem v4128_mg_checked : Scalar.distance (sourceCoefficient 62 68 3 2) v4128_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4128_upper : Scalar.QComplex := ((999994439773773621306407245390 : Int)/10^30,(-3334729604726850814788541410 : Int)/10^30)
theorem v4128_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 68 5) 1) 14) v4128_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4128 : Material (62 : Basis) (68 : Basis) where
  plus := ![v4128_pa,v4128_pb,v4128_pg]
  minus := ![(Primitive.Addresses.material4128 1).one,v4128_mb,v4128_mg]
  upper := v4128_upper
  lower := (Primitive.Addresses.material4128 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4128_pa_checked.trans (by decide +kernel)
    · exact v4128_pb_checked.trans (by decide +kernel)
    · exact v4128_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 68 Primitive.Addresses.material4128
    · exact v4128_mb_checked.trans (by decide +kernel)
    · exact v4128_mg_checked.trans (by decide +kernel)
  upper_error := v4128_upper_checked
  lower_error := reuse_lower_error 62 68 Primitive.Addresses.material4128

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
