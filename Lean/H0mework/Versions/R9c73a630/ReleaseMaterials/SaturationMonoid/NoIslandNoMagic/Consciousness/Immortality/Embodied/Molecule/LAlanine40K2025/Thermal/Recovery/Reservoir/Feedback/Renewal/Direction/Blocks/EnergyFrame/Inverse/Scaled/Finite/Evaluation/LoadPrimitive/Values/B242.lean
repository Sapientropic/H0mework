import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B161
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B162

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3873_pa : Scalar.QComplex := ((999998564473301926285959127507 : Int)/10^30,(-1694417698033907812536222760 : Int)/10^30)
theorem v3873_pa_checked : Scalar.distance (sourceCoefficient 55 79 1 0) v3873_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3873_pb : Scalar.QComplex := ((-731103125766104705933772 : Int)/10^30,(-431476888547830893876561251 : Int)/10^30)
theorem v3873_pb_checked : Scalar.distance (sourceCoefficient 55 79 1 1) v3873_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3873_pg : Scalar.QComplex := ((-93086294860651288227800 : Int)/10^30,(157727291878028844991 : Int)/10^30)
theorem v3873_pg_checked : Scalar.distance (sourceCoefficient 55 79 1 2) v3873_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3873_mb : Scalar.QComplex := ((-1103447975362102569557103 : Int)/10^30,(-431476096980195945854858889 : Int)/10^30)
theorem v3873_mb_checked : Scalar.distance (sourceCoefficient 55 79 3 1) v3873_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3873_mg : Scalar.QComplex := ((-93086124088820340550615 : Int)/10^30,(238056513162602223405 : Int)/10^30)
theorem v3873_mg_checked : Scalar.distance (sourceCoefficient 55 79 3 2) v3873_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3873_upper : Scalar.QComplex := ((999994150681677792642893805922 : Int)/10^30,(-3420321977517596178991122697 : Int)/10^30)
theorem v3873_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 79 5) 1) 14) v3873_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3873 : Material (55 : Basis) (79 : Basis) where
  plus := ![v3873_pa,v3873_pb,v3873_pg]
  minus := ![(Primitive.Addresses.material3873 1).one,v3873_mb,v3873_mg]
  upper := v3873_upper
  lower := (Primitive.Addresses.material3873 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3873_pa_checked.trans (by decide +kernel)
    · exact v3873_pb_checked.trans (by decide +kernel)
    · exact v3873_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 79 Primitive.Addresses.material3873
    · exact v3873_mb_checked.trans (by decide +kernel)
    · exact v3873_mg_checked.trans (by decide +kernel)
  upper_error := v3873_upper_checked
  lower_error := reuse_lower_error 55 79 Primitive.Addresses.material3873

def v3874_pa : Scalar.QComplex := ((999998549673667480464470724773 : Int)/10^30,(-1703129637341972937514904993 : Int)/10^30)
theorem v3874_pa_checked : Scalar.distance (sourceCoefficient 55 80 1 0) v3874_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3874_pb : Scalar.QComplex := ((-734862130709558185921477 : Int)/10^30,(-431476881622785024530751552 : Int)/10^30)
theorem v3874_pb_checked : Scalar.distance (sourceCoefficient 55 80 1 1) v3874_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3874_pg : Scalar.QComplex := ((-93086293424828280341020 : Int)/10^30,(158538255094342344114 : Int)/10^30)
theorem v3874_pg_checked : Scalar.distance (sourceCoefficient 55 80 1 2) v3874_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3874_mb : Scalar.QComplex := ((-1107206972929904021326843 : Int)/10^30,(-431476086811300688117731139 : Int)/10^30)
theorem v3874_mb_checked : Scalar.distance (sourceCoefficient 55 80 3 1) v3874_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3874_mg : Scalar.QComplex := ((-93086121953173136035223 : Int)/10^30,(238867474837906465505 : Int)/10^30)
theorem v3874_mg_checked : Scalar.distance (sourceCoefficient 55 80 3 2) v3874_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3874_upper : Scalar.QComplex := ((999994120846048484378242452369 : Int)/10^30,(-3429033878307424639747313170 : Int)/10^30)
theorem v3874_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 80 5) 1) 14) v3874_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3874 : Material (55 : Basis) (80 : Basis) where
  plus := ![v3874_pa,v3874_pb,v3874_pg]
  minus := ![(Primitive.Addresses.material3874 1).one,v3874_mb,v3874_mg]
  upper := v3874_upper
  lower := (Primitive.Addresses.material3874 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3874_pa_checked.trans (by decide +kernel)
    · exact v3874_pb_checked.trans (by decide +kernel)
    · exact v3874_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 80 Primitive.Addresses.material3874
    · exact v3874_mb_checked.trans (by decide +kernel)
    · exact v3874_mg_checked.trans (by decide +kernel)
  upper_error := v3874_upper_checked
  lower_error := reuse_lower_error 55 80 Primitive.Addresses.material3874

def v3875_pa : Scalar.QComplex := ((999998504652871293764302308450 : Int)/10^30,(-1729361738141975912439064902 : Int)/10^30)
theorem v3875_pa_checked : Scalar.distance (sourceCoefficient 55 81 1 0) v3875_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3875_pb : Scalar.QComplex := ((-746180689254331088629610 : Int)/10^30,(-431476860507434561477981063 : Int)/10^30)
theorem v3875_pb_checked : Scalar.distance (sourceCoefficient 55 81 1 1) v3875_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3875_pg : Scalar.QComplex := ((-93086289051715812522170 : Int)/10^30,(160980107352802949085 : Int)/10^30)
theorem v3875_pg_checked : Scalar.distance (sourceCoefficient 55 81 1 2) v3875_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3875_mb : Scalar.QComplex := ((-1118525509038663844603729 : Int)/10^30,(-431476055928551832089285713 : Int)/10^30)
theorem v3875_mb_checked : Scalar.distance (sourceCoefficient 55 81 3 1) v3875_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3875_mg : Scalar.QComplex := ((-93086115472853774417689 : Int)/10^30,(241309322413354774437 : Int)/10^30)
theorem v3875_mg_checked : Scalar.distance (sourceCoefficient 55 81 3 2) v3875_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3875_upper : Scalar.QComplex := ((999994030551093127655275297061 : Int)/10^30,(-3455265862335984948567415072 : Int)/10^30)
theorem v3875_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 81 5) 1) 14) v3875_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3875 : Material (55 : Basis) (81 : Basis) where
  plus := ![v3875_pa,v3875_pb,v3875_pg]
  minus := ![(Primitive.Addresses.material3875 1).one,v3875_mb,v3875_mg]
  upper := v3875_upper
  lower := (Primitive.Addresses.material3875 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3875_pa_checked.trans (by decide +kernel)
    · exact v3875_pb_checked.trans (by decide +kernel)
    · exact v3875_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 81 Primitive.Addresses.material3875
    · exact v3875_mb_checked.trans (by decide +kernel)
    · exact v3875_mg_checked.trans (by decide +kernel)
  upper_error := v3875_upper_checked
  lower_error := reuse_lower_error 55 81 Primitive.Addresses.material3875

def v3876_pa : Scalar.QComplex := ((999998487413163578341228464347 : Int)/10^30,(-1739301982096375300680852985 : Int)/10^30)
theorem v3876_pa_checked : Scalar.distance (sourceCoefficient 55 82 1 0) v3876_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3876_pb : Scalar.QComplex := ((-750469679763234969691730 : Int)/10^30,(-431476852402674094611397563 : Int)/10^30)
theorem v3876_pb_checked : Scalar.distance (sourceCoefficient 55 82 1 1) v3876_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3876_pg : Scalar.QComplex := ((-93086287375068861495263 : Int)/10^30,(161905409033440516567 : Int)/10^30)
theorem v3876_pg_checked : Scalar.distance (sourceCoefficient 55 82 1 2) v3876_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3876_mb : Scalar.QComplex := ((-1122814490956537284606469 : Int)/10^30,(-431476044122588742773132627 : Int)/10^30)
theorem v3876_mb_checked : Scalar.distance (sourceCoefficient 55 82 3 1) v3876_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3876_mg : Scalar.QComplex := ((-93086112997713771333531 : Int)/10^30,(242234622302589432481 : Int)/10^30)
theorem v3876_mg_checked : Scalar.distance (sourceCoefficient 55 82 3 2) v3876_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3876_upper : Scalar.QComplex := ((999993996155451795345668851657 : Int)/10^30,(-3465206061731387087056678470 : Int)/10^30)
theorem v3876_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 82 5) 1) 14) v3876_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3876 : Material (55 : Basis) (82 : Basis) where
  plus := ![v3876_pa,v3876_pb,v3876_pg]
  minus := ![(Primitive.Addresses.material3876 1).one,v3876_mb,v3876_mg]
  upper := v3876_upper
  lower := (Primitive.Addresses.material3876 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3876_pa_checked.trans (by decide +kernel)
    · exact v3876_pb_checked.trans (by decide +kernel)
    · exact v3876_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 82 Primitive.Addresses.material3876
    · exact v3876_mb_checked.trans (by decide +kernel)
    · exact v3876_mg_checked.trans (by decide +kernel)
  upper_error := v3876_upper_checked
  lower_error := reuse_lower_error 55 82 Primitive.Addresses.material3876

def v3877_pa : Scalar.QComplex := ((999998463721180898484347950927 : Int)/10^30,(-1752870582230879155714356995 : Int)/10^30)
theorem v3877_pa_checked : Scalar.distance (sourceCoefficient 55 83 1 0) v3877_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3877_pb : Scalar.QComplex := ((-756324223862028755635389 : Int)/10^30,(-431476841247783719260285152 : Int)/10^30)
theorem v3877_pb_checked : Scalar.distance (sourceCoefficient 55 83 1 1) v3877_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3877_pg : Scalar.QComplex := ((-93086285069096651689955 : Int)/10^30,(163168461379028202952 : Int)/10^30)
theorem v3877_pg_checked : Scalar.distance (sourceCoefficient 55 83 1 2) v3877_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3877_mb : Scalar.QComplex := ((-1128669023249248740370484 : Int)/10^30,(-431476027915494642516462987 : Int)/10^30)
theorem v3877_mb_checked : Scalar.distance (sourceCoefficient 55 83 3 1) v3877_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3877_mg : Scalar.QComplex := ((-93086109601785131670837 : Int)/10^30,(243497672187934846331 : Int)/10^30)
theorem v3877_mg_checked : Scalar.distance (sourceCoefficient 55 83 3 2) v3877_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3877_upper : Scalar.QComplex := ((999993949045331503548955529906 : Int)/10^30,(-3478774600766842135928609324 : Int)/10^30)
theorem v3877_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 83 5) 1) 14) v3877_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3877 : Material (55 : Basis) (83 : Basis) where
  plus := ![v3877_pa,v3877_pb,v3877_pg]
  minus := ![(Primitive.Addresses.material3877 1).one,v3877_mb,v3877_mg]
  upper := v3877_upper
  lower := (Primitive.Addresses.material3877 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3877_pa_checked.trans (by decide +kernel)
    · exact v3877_pb_checked.trans (by decide +kernel)
    · exact v3877_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 83 Primitive.Addresses.material3877
    · exact v3877_mb_checked.trans (by decide +kernel)
    · exact v3877_mg_checked.trans (by decide +kernel)
  upper_error := v3877_upper_checked
  lower_error := reuse_lower_error 55 83 Primitive.Addresses.material3877

def v3878_pa : Scalar.QComplex := ((999998401509585560174671423906 : Int)/10^30,(-1788009584344571012385837105 : Int)/10^30)
theorem v3878_pa_checked : Scalar.distance (sourceCoefficient 55 84 1 0) v3878_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3878_pb : Scalar.QComplex := ((-771485908254016139184222 : Int)/10^30,(-431476811867308490808834485 : Int)/10^30)
theorem v3878_pb_checked : Scalar.distance (sourceCoefficient 55 84 1 1) v3878_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3878_pg : Scalar.QComplex := ((-93086279004315195959993 : Int)/10^30,(166439425082513960403 : Int)/10^30)
theorem v3878_pg_checked : Scalar.distance (sourceCoefficient 55 84 1 2) v3878_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3878_mb : Scalar.QComplex := ((-1143830676641821226904032 : Int)/10^30,(-431475985451179580389756772 : Int)/10^30)
theorem v3878_mb_checked : Scalar.distance (sourceCoefficient 55 84 3 1) v3878_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3878_mg : Scalar.QComplex := ((-93086100714311576764454 : Int)/10^30,(246768629439858077870 : Int)/10^30)
theorem v3878_mg_checked : Scalar.distance (sourceCoefficient 55 84 3 2) v3878_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3878_upper : Scalar.QComplex := ((999993826187098959240644834788 : Int)/10^30,(-3513913443173548299320365241 : Int)/10^30)
theorem v3878_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 84 5) 1) 14) v3878_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3878 : Material (55 : Basis) (84 : Basis) where
  plus := ![v3878_pa,v3878_pb,v3878_pg]
  minus := ![(Primitive.Addresses.material3878 1).one,v3878_mb,v3878_mg]
  upper := v3878_upper
  lower := (Primitive.Addresses.material3878 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3878_pa_checked.trans (by decide +kernel)
    · exact v3878_pb_checked.trans (by decide +kernel)
    · exact v3878_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 84 Primitive.Addresses.material3878
    · exact v3878_mb_checked.trans (by decide +kernel)
    · exact v3878_mg_checked.trans (by decide +kernel)
  upper_error := v3878_upper_checked
  lower_error := reuse_lower_error 55 84 Primitive.Addresses.material3878

def v3879_pa : Scalar.QComplex := ((999998257030253211263065954929 : Int)/10^30,(-1867066269748863426051108872 : Int)/10^30)
theorem v3879_pa_checked : Scalar.distance (sourceCoefficient 55 85 1 0) v3879_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3879_pb : Scalar.QComplex := ((-805597077484022022613327 : Int)/10^30,(-431476743169404189150267169 : Int)/10^30)
theorem v3879_pb_checked : Scalar.distance (sourceCoefficient 55 85 1 1) v3879_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3879_pg : Scalar.QComplex := ((-93086264869381867621402 : Int)/10^30,(173798528240108234061 : Int)/10^30)
theorem v3879_pg_checked : Scalar.distance (sourceCoefficient 55 85 1 2) v3879_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3879_mb : Scalar.QComplex := ((-1177941773887482474976360 : Int)/10^30,(-431475887316898122637143242 : Int)/10^30)
theorem v3879_mb_checked : Scalar.distance (sourceCoefficient 55 85 3 1) v3879_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3879_mg : Scalar.QComplex := ((-93086080228808928206204 : Int)/10^30,(254127717659511069735 : Int)/10^30)
theorem v3879_mg_checked : Scalar.distance (sourceCoefficient 55 85 3 2) v3879_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3879_upper : Scalar.QComplex := ((999993545263314753989682332094 : Int)/10^30,(-3592969761473973882333808481 : Int)/10^30)
theorem v3879_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 85 5) 1) 14) v3879_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3879 : Material (55 : Basis) (85 : Basis) where
  plus := ![v3879_pa,v3879_pb,v3879_pg]
  minus := ![(Primitive.Addresses.material3879 1).one,v3879_mb,v3879_mg]
  upper := v3879_upper
  lower := (Primitive.Addresses.material3879 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3879_pa_checked.trans (by decide +kernel)
    · exact v3879_pb_checked.trans (by decide +kernel)
    · exact v3879_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 85 Primitive.Addresses.material3879
    · exact v3879_mb_checked.trans (by decide +kernel)
    · exact v3879_mg_checked.trans (by decide +kernel)
  upper_error := v3879_upper_checked
  lower_error := reuse_lower_error 55 85 Primitive.Addresses.material3879

def v3880_pa : Scalar.QComplex := ((999998229693400419309304655754 : Int)/10^30,(-1881650888229781287592321673 : Int)/10^30)
theorem v3880_pa_checked : Scalar.distance (sourceCoefficient 55 86 1 0) v3880_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3880_pb : Scalar.QComplex := ((-811890009742942256731639 : Int)/10^30,(-431476730102951274221976515 : Int)/10^30)
theorem v3880_pb_checked : Scalar.distance (sourceCoefficient 55 86 1 1) v3880_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3880_pg : Scalar.QComplex := ((-93086262187566608105308 : Int)/10^30,(175156158007327489453 : Int)/10^30)
theorem v3880_pg_checked : Scalar.distance (sourceCoefficient 55 86 1 2) v3880_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3880_mb : Scalar.QComplex := ((-1184234692527496053497002 : Int)/10^30,(-431475868819932956646057140 : Int)/10^30)
theorem v3880_mb_checked : Scalar.distance (sourceCoefficient 55 86 3 1) v3880_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3880_mg : Scalar.QComplex := ((-93086076375421323517172 : Int)/10^30,(255485344606936931559 : Int)/10^30)
theorem v3880_mg_checked : Scalar.distance (sourceCoefficient 55 86 3 2) v3880_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3880_upper : Scalar.QComplex := ((999993492754774285255763340926 : Int)/10^30,(-3607554311051887807183007108 : Int)/10^30)
theorem v3880_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 86 5) 1) 14) v3880_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3880 : Material (55 : Basis) (86 : Basis) where
  plus := ![v3880_pa,v3880_pb,v3880_pg]
  minus := ![(Primitive.Addresses.material3880 1).one,v3880_mb,v3880_mg]
  upper := v3880_upper
  lower := (Primitive.Addresses.material3880 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3880_pa_checked.trans (by decide +kernel)
    · exact v3880_pb_checked.trans (by decide +kernel)
    · exact v3880_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 86 Primitive.Addresses.material3880
    · exact v3880_mb_checked.trans (by decide +kernel)
    · exact v3880_mg_checked.trans (by decide +kernel)
  upper_error := v3880_upper_checked
  lower_error := reuse_lower_error 55 86 Primitive.Addresses.material3880

def v3881_pa : Scalar.QComplex := ((999998227875717613462188372179 : Int)/10^30,(-1882616642959634360422576148 : Int)/10^30)
theorem v3881_pa_checked : Scalar.distance (sourceCoefficient 55 87 1 0) v3881_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3881_pb : Scalar.QComplex := ((-812306711013044347663477 : Int)/10^30,(-431476729233405512840668207 : Int)/10^30)
theorem v3881_pb_checked : Scalar.distance (sourceCoefficient 55 87 1 1) v3881_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3881_pg : Scalar.QComplex := ((-93086262009168439789721 : Int)/10^30,(175246056647154013745 : Int)/10^30)
theorem v3881_pg_checked : Scalar.distance (sourceCoefficient 55 87 1 2) v3881_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3881_mb : Scalar.QComplex := ((-1184651392892062388196214 : Int)/10^30,(-431475867590793090466793517 : Int)/10^30)
theorem v3881_mb_checked : Scalar.distance (sourceCoefficient 55 87 3 1) v3881_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3881_mg : Scalar.QComplex := ((-93086076119444744341522 : Int)/10^30,(255575243059340499172 : Int)/10^30)
theorem v3881_mg_checked : Scalar.distance (sourceCoefficient 55 87 3 2) v3881_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3881_upper : Scalar.QComplex := ((999993489270289135491962957691 : Int)/10^30,(-3608520061206207031420695513 : Int)/10^30)
theorem v3881_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 87 5) 1) 14) v3881_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3881 : Material (55 : Basis) (87 : Basis) where
  plus := ![v3881_pa,v3881_pb,v3881_pg]
  minus := ![(Primitive.Addresses.material3881 1).one,v3881_mb,v3881_mg]
  upper := v3881_upper
  lower := (Primitive.Addresses.material3881 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3881_pa_checked.trans (by decide +kernel)
    · exact v3881_pb_checked.trans (by decide +kernel)
    · exact v3881_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 87 Primitive.Addresses.material3881
    · exact v3881_mb_checked.trans (by decide +kernel)
    · exact v3881_mg_checked.trans (by decide +kernel)
  upper_error := v3881_upper_checked
  lower_error := reuse_lower_error 55 87 Primitive.Addresses.material3881

def v3882_pa : Scalar.QComplex := ((999998205667767174292670999345 : Int)/10^30,(-1894376215545173302710549927 : Int)/10^30)
theorem v3882_pa_checked : Scalar.distance (sourceCoefficient 55 88 1 0) v3882_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3882_pb : Scalar.QComplex := ((-817380699934176616087979 : Int)/10^30,(-431476718602281778983509373 : Int)/10^30)
theorem v3882_pb_checked : Scalar.distance (sourceCoefficient 55 88 1 1) v3882_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3882_pg : Scalar.QComplex := ((-93086259828766246628216 : Int)/10^30,(176340713027498238823 : Int)/10^30)
theorem v3882_pg_checked : Scalar.distance (sourceCoefficient 55 88 1 2) v3882_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3882_mb : Scalar.QComplex := ((-1189725370749735714253797 : Int)/10^30,(-431475852581049400103518489 : Int)/10^30)
theorem v3882_mb_checked : Scalar.distance (sourceCoefficient 55 88 3 1) v3882_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3882_mg : Scalar.QComplex := ((-93086072994404208299549 : Int)/10^30,(256669897150505234551 : Int)/10^30)
theorem v3882_mg_checked : Scalar.distance (sourceCoefficient 55 88 3 2) v3882_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3882_upper : Scalar.QComplex := ((999993446766416309907100097016 : Int)/10^30,(-3620279577948336215500077585 : Int)/10^30)
theorem v3882_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 88 5) 1) 14) v3882_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3882 : Material (55 : Basis) (88 : Basis) where
  plus := ![v3882_pa,v3882_pb,v3882_pg]
  minus := ![(Primitive.Addresses.material3882 1).one,v3882_mb,v3882_mg]
  upper := v3882_upper
  lower := (Primitive.Addresses.material3882 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3882_pa_checked.trans (by decide +kernel)
    · exact v3882_pb_checked.trans (by decide +kernel)
    · exact v3882_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 88 Primitive.Addresses.material3882
    · exact v3882_mb_checked.trans (by decide +kernel)
    · exact v3882_mg_checked.trans (by decide +kernel)
  upper_error := v3882_upper_checked
  lower_error := reuse_lower_error 55 88 Primitive.Addresses.material3882

def v3883_pa : Scalar.QComplex := ((999998175058794842609190078023 : Int)/10^30,(-1910465670956790403257686751 : Int)/10^30)
theorem v3883_pa_checked : Scalar.distance (sourceCoefficient 55 89 1 0) v3883_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3883_pb : Scalar.QComplex := ((-824322935012693302503711 : Int)/10^30,(-431476703927880615627182043 : Int)/10^30)
theorem v3883_pb_checked : Scalar.distance (sourceCoefficient 55 89 1 1) v3883_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3883_pg : Scalar.QComplex := ((-93086256821207634686466 : Int)/10^30,(177838422639449886139 : Int)/10^30)
theorem v3883_pg_checked : Scalar.distance (sourceCoefficient 55 89 1 2) v3883_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3883_mb : Scalar.QComplex := ((-1196667590579993711638672 : Int)/10^30,(-431475831915817494598701513 : Int)/10^30)
theorem v3883_mb_checked : Scalar.distance (sourceCoefficient 55 89 3 1) v3883_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3883_mg : Scalar.QComplex := ((-93086068694390775431951 : Int)/10^30,(258167603609403517932 : Int)/10^30)
theorem v3883_mg_checked : Scalar.distance (sourceCoefficient 55 89 3 2) v3883_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3883_upper : Scalar.QComplex := ((999993388388549150234194199123 : Int)/10^30,(-3636368956568290060434345755 : Int)/10^30)
theorem v3883_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 89 5) 1) 14) v3883_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3883 : Material (55 : Basis) (89 : Basis) where
  plus := ![v3883_pa,v3883_pb,v3883_pg]
  minus := ![(Primitive.Addresses.material3883 1).one,v3883_mb,v3883_mg]
  upper := v3883_upper
  lower := (Primitive.Addresses.material3883 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3883_pa_checked.trans (by decide +kernel)
    · exact v3883_pb_checked.trans (by decide +kernel)
    · exact v3883_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 89 Primitive.Addresses.material3883
    · exact v3883_mb_checked.trans (by decide +kernel)
    · exact v3883_mg_checked.trans (by decide +kernel)
  upper_error := v3883_upper_checked
  lower_error := reuse_lower_error 55 89 Primitive.Addresses.material3883

def v3884_pa : Scalar.QComplex := ((999998124655677837929652468688 : Int)/10^30,(-1936668564160582958045510290 : Int)/10^30)
theorem v3884_pa_checked : Scalar.distance (sourceCoefficient 55 90 1 0) v3884_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3884_pb : Scalar.QComplex := ((-835628888856063623658154 : Int)/10^30,(-431476679710738399368107948 : Int)/10^30)
theorem v3884_pb_checked : Scalar.distance (sourceCoefficient 55 90 1 1) v3884_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3884_pg : Scalar.QComplex := ((-93086251862996280647714 : Int)/10^30,(180277555821090119594 : Int)/10^30)
theorem v3884_pg_checked : Scalar.distance (sourceCoefficient 55 90 1 2) v3884_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3884_mb : Scalar.QComplex := ((-1207973519315337676254995 : Int)/10^30,(-431475797942155329918531611 : Int)/10^30)
theorem v3884_mb_checked : Scalar.distance (sourceCoefficient 55 90 3 1) v3884_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3884_mg : Scalar.QComplex := ((-93086061631319186286877 : Int)/10^30,(260606731604129904983 : Int)/10^30)
theorem v3884_mg_checked : Scalar.distance (sourceCoefficient 55 90 3 2) v3884_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3884_upper : Scalar.QComplex := ((999993292761690653233219621903 : Int)/10^30,(-3662571723754743781206248278 : Int)/10^30)
theorem v3884_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 90 5) 1) 14) v3884_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3884 : Material (55 : Basis) (90 : Basis) where
  plus := ![v3884_pa,v3884_pb,v3884_pg]
  minus := ![(Primitive.Addresses.material3884 1).one,v3884_mb,v3884_mg]
  upper := v3884_upper
  lower := (Primitive.Addresses.material3884 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3884_pa_checked.trans (by decide +kernel)
    · exact v3884_pb_checked.trans (by decide +kernel)
    · exact v3884_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 90 Primitive.Addresses.material3884
    · exact v3884_mb_checked.trans (by decide +kernel)
    · exact v3884_mg_checked.trans (by decide +kernel)
  upper_error := v3884_upper_checked
  lower_error := reuse_lower_error 55 90 Primitive.Addresses.material3884

def v3885_pa : Scalar.QComplex := ((999998095959431279366384811523 : Int)/10^30,(-1951429607254840206316012646 : Int)/10^30)
theorem v3885_pa_checked : Scalar.distance (sourceCoefficient 55 91 1 0) v3885_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3885_pb : Scalar.QComplex := ((-841997943864192265686899 : Int)/10^30,(-431476665894405878176801247 : Int)/10^30)
theorem v3885_pb_checked : Scalar.distance (sourceCoefficient 55 91 1 1) v3885_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3885_pg : Scalar.QComplex := ((-93086249037021412185547 : Int)/10^30,(181651608271172463403 : Int)/10^30)
theorem v3885_pg_checked : Scalar.distance (sourceCoefficient 55 91 1 2) v3885_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3885_mb : Scalar.QComplex := ((-1214342560029103357293035 : Int)/10^30,(-431475778629620332753376660 : Int)/10^30)
theorem v3885_mb_checked : Scalar.distance (sourceCoefficient 55 91 3 1) v3885_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3885_mg : Scalar.QComplex := ((-93086057619599990668316 : Int)/10^30,(261980781103900690028 : Int)/10^30)
theorem v3885_mg_checked : Scalar.distance (sourceCoefficient 55 91 3 2) v3885_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3885_upper : Scalar.QComplex := ((999993238589265565039239578675 : Int)/10^30,(-3677332695337043037577755367 : Int)/10^30)
theorem v3885_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 91 5) 1) 14) v3885_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3885 : Material (55 : Basis) (91 : Basis) where
  plus := ![v3885_pa,v3885_pb,v3885_pg]
  minus := ![(Primitive.Addresses.material3885 1).one,v3885_mb,v3885_mg]
  upper := v3885_upper
  lower := (Primitive.Addresses.material3885 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3885_pa_checked.trans (by decide +kernel)
    · exact v3885_pb_checked.trans (by decide +kernel)
    · exact v3885_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 91 Primitive.Addresses.material3885
    · exact v3885_mb_checked.trans (by decide +kernel)
    · exact v3885_mg_checked.trans (by decide +kernel)
  upper_error := v3885_upper_checked
  lower_error := reuse_lower_error 55 91 Primitive.Addresses.material3885

def v3886_pa : Scalar.QComplex := ((999998033088747225685069276997 : Int)/10^30,(-1983385650046090650907673539 : Int)/10^30)
theorem v3886_pa_checked : Scalar.distance (sourceCoefficient 55 92 1 0) v3886_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3886_pb : Scalar.QComplex := ((-855786250543820511811943 : Int)/10^30,(-431476635554122975855979292 : Int)/10^30)
theorem v3886_pb_checked : Scalar.distance (sourceCoefficient 55 92 1 1) v3886_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3886_pg : Scalar.QComplex := ((-93086242838029982279988 : Int)/10^30,(184626281405164800343 : Int)/10^30)
theorem v3886_pg_checked : Scalar.distance (sourceCoefficient 55 92 1 2) v3886_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3886_mb : Scalar.QComplex := ((-1228130835392417200759941 : Int)/10^30,(-431475736390661065267484477 : Int)/10^30)
theorem v3886_mb_checked : Scalar.distance (sourceCoefficient 55 92 3 1) v3886_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3886_mg : Scalar.QComplex := ((-93086048853601928599782 : Int)/10^30,(264955447780835858106 : Int)/10^30)
theorem v3886_mg_checked : Scalar.distance (sourceCoefficient 55 92 3 2) v3886_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3886_upper : Scalar.QComplex := ((999993120565444321714291421869 : Int)/10^30,(-3709288582024424472329092707 : Int)/10^30)
theorem v3886_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 92 5) 1) 14) v3886_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3886 : Material (55 : Basis) (92 : Basis) where
  plus := ![v3886_pa,v3886_pb,v3886_pg]
  minus := ![(Primitive.Addresses.material3886 1).one,v3886_mb,v3886_mg]
  upper := v3886_upper
  lower := (Primitive.Addresses.material3886 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3886_pa_checked.trans (by decide +kernel)
    · exact v3886_pb_checked.trans (by decide +kernel)
    · exact v3886_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 92 Primitive.Addresses.material3886
    · exact v3886_mb_checked.trans (by decide +kernel)
    · exact v3886_mg_checked.trans (by decide +kernel)
  upper_error := v3886_upper_checked
  lower_error := reuse_lower_error 55 92 Primitive.Addresses.material3886

def v3887_pa : Scalar.QComplex := ((999997957148458631960781854935 : Int)/10^30,(-2021311185714277485434853523 : Int)/10^30)
theorem v3887_pa_checked : Scalar.distance (sourceCoefficient 55 93 1 0) v3887_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3887_pb : Scalar.QComplex := ((-872150257169165376873815 : Int)/10^30,(-431476598783810813528568595 : Int)/10^30)
theorem v3887_pb_checked : Scalar.distance (sourceCoefficient 55 93 1 1) v3887_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3887_pg : Scalar.QComplex := ((-93086235337133834107012 : Int)/10^30,(188156633099048211839 : Int)/10^30)
theorem v3887_pg_checked : Scalar.distance (sourceCoefficient 55 93 1 2) v3887_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3887_mb : Scalar.QComplex := ((-1244494804193571204452414 : Int)/10^30,(-431475685498961884034560684 : Int)/10^30)
theorem v3887_mb_checked : Scalar.distance (sourceCoefficient 55 93 3 1) v3887_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3887_mg : Scalar.QComplex := ((-93086038306174062669759 : Int)/10^30,(268485791687272440874 : Int)/10^30)
theorem v3887_mg_checked : Scalar.distance (sourceCoefficient 55 93 3 2) v3887_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3887_upper : Scalar.QComplex := ((999992979169234846558314717933 : Int)/10^30,(-3747213930140932111858748018 : Int)/10^30)
theorem v3887_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 93 5) 1) 14) v3887_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3887 : Material (55 : Basis) (93 : Basis) where
  plus := ![v3887_pa,v3887_pb,v3887_pg]
  minus := ![(Primitive.Addresses.material3887 1).one,v3887_mb,v3887_mg]
  upper := v3887_upper
  lower := (Primitive.Addresses.material3887 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3887_pa_checked.trans (by decide +kernel)
    · exact v3887_pb_checked.trans (by decide +kernel)
    · exact v3887_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 93 Primitive.Addresses.material3887
    · exact v3887_mb_checked.trans (by decide +kernel)
    · exact v3887_mg_checked.trans (by decide +kernel)
  upper_error := v3887_upper_checked
  lower_error := reuse_lower_error 55 93 Primitive.Addresses.material3887

def v3888_pa : Scalar.QComplex := ((999997865593179963226288514846 : Int)/10^30,(-2066109649651023241519636404 : Int)/10^30)
theorem v3888_pa_checked : Scalar.distance (sourceCoefficient 55 94 1 0) v3888_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3888_pb : Scalar.QComplex := ((-891479775184664369167640 : Int)/10^30,(-431476554283906267726161024 : Int)/10^30)
theorem v3888_pb_checked : Scalar.distance (sourceCoefficient 55 94 1 1) v3888_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3888_pg : Scalar.QComplex := ((-93086226275679465604368 : Int)/10^30,(192326760861330032692 : Int)/10^30)
theorem v3888_pg_checked : Scalar.distance (sourceCoefficient 55 94 1 2) v3888_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3888_mb : Scalar.QComplex := ((-1263824276610393815235497 : Int)/10^30,(-431475624318570429379102518 : Int)/10^30)
theorem v3888_mb_checked : Scalar.distance (sourceCoefficient 55 94 3 1) v3888_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3888_mg : Scalar.QComplex := ((-93086025646090624893865 : Int)/10^30,(272655910077198104313 : Int)/10^30)
theorem v3888_mg_checked : Scalar.distance (sourceCoefficient 55 94 3 2) v3888_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3888_upper : Scalar.QComplex := ((999992810296007868734837479947 : Int)/10^30,(-3792012169339523079161490033 : Int)/10^30)
theorem v3888_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 94 5) 1) 14) v3888_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3888 : Material (55 : Basis) (94 : Basis) where
  plus := ![v3888_pa,v3888_pb,v3888_pg]
  minus := ![(Primitive.Addresses.material3888 1).one,v3888_mb,v3888_mg]
  upper := v3888_upper
  lower := (Primitive.Addresses.material3888 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3888_pa_checked.trans (by decide +kernel)
    · exact v3888_pb_checked.trans (by decide +kernel)
    · exact v3888_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 94 Primitive.Addresses.material3888
    · exact v3888_mb_checked.trans (by decide +kernel)
    · exact v3888_mg_checked.trans (by decide +kernel)
  upper_error := v3888_upper_checked
  lower_error := reuse_lower_error 55 94 Primitive.Addresses.material3888

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
