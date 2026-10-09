import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B194
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B195

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4673_pa : Scalar.QComplex := ((999996485250665829263427106081 : Int)/10^30,(-2651317844936474434121974285 : Int)/10^30)
theorem v4673_pa_checked : Scalar.distance (sourceCoefficient 84 96 1 0) v4673_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4673_pb : Scalar.QComplex := ((-1143984028602909295254218 : Int)/10^30,(-431475995973321794629605959 : Int)/10^30)
theorem v4673_pb_checked : Scalar.distance (sourceCoefficient 84 96 1 1) v4673_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4673_pg : Scalar.QComplex := ((-93086101805481603600006 : Int)/10^30,(246801710278593621037 : Int)/10^30)
theorem v4673_pg_checked : Scalar.distance (sourceCoefficient 84 96 1 2) v4673_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4673_mb : Scalar.QComplex := ((-1516327954212876154242128 : Int)/10^30,(-431474848108395510295591083 : Int)/10^30)
theorem v4673_mb_checked : Scalar.distance (sourceCoefficient 84 96 3 1) v4673_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4673_mg : Scalar.QComplex := ((-93085854166511222379272 : Int)/10^30,(327130731798773571133 : Int)/10^30)
theorem v4673_mg_checked : Scalar.distance (sourceCoefficient 84 96 3 2) v4673_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4673_upper : Scalar.QComplex := ((999990419939294202874129637676 : Int)/10^30,(-4377217110680155077130336455 : Int)/10^30)
theorem v4673_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 96 5) 1) 14) v4673_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4673 : Material (84 : Basis) (96 : Basis) where
  plus := ![v4673_pa,v4673_pb,v4673_pg]
  minus := ![(Primitive.Addresses.material4673 1).one,v4673_mb,v4673_mg]
  upper := v4673_upper
  lower := (Primitive.Addresses.material4673 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4673_pa_checked.trans (by decide +kernel)
    · exact v4673_pb_checked.trans (by decide +kernel)
    · exact v4673_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 96 Primitive.Addresses.material4673
    · exact v4673_mb_checked.trans (by decide +kernel)
    · exact v4673_mg_checked.trans (by decide +kernel)
  upper_error := v4673_upper_checked
  lower_error := reuse_lower_error 84 96 Primitive.Addresses.material4673

def v4674_pa : Scalar.QComplex := ((999996288598011733504197632824 : Int)/10^30,(-2724479803931068433831443123 : Int)/10^30)
theorem v4674_pa_checked : Scalar.distance (sourceCoefficient 84 97 1 0) v4674_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4674_pb : Scalar.QComplex := ((-1175551757779755847583497 : Int)/10^30,(-431475907121228571847190762 : Int)/10^30)
theorem v4674_pb_checked : Scalar.distance (sourceCoefficient 84 97 1 1) v4674_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4674_pg : Scalar.QComplex := ((-93086083068214179787807 : Int)/10^30,(253612094602831475063 : Int)/10^30)
theorem v4674_pg_checked : Scalar.distance (sourceCoefficient 84 97 1 2) v4674_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4674_mb : Scalar.QComplex := ((-1547895594960259716002010 : Int)/10^30,(-431474732014806849333646187 : Int)/10^30)
theorem v4674_mb_checked : Scalar.distance (sourceCoefficient 84 97 3 1) v4674_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4674_mg : Scalar.QComplex := ((-93085829552195831814476 : Int)/10^30,(333941097417776199753 : Int)/10^30)
theorem v4674_mg_checked : Scalar.distance (sourceCoefficient 84 97 3 2) v4674_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4674_upper : Scalar.QComplex := ((999990097016028974546508895008 : Int)/10^30,(-4450378621303964581944916605 : Int)/10^30)
theorem v4674_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 97 5) 1) 14) v4674_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4674 : Material (84 : Basis) (97 : Basis) where
  plus := ![v4674_pa,v4674_pb,v4674_pg]
  minus := ![(Primitive.Addresses.material4674 1).one,v4674_mb,v4674_mg]
  upper := v4674_upper
  lower := (Primitive.Addresses.material4674 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4674_pa_checked.trans (by decide +kernel)
    · exact v4674_pb_checked.trans (by decide +kernel)
    · exact v4674_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 97 Primitive.Addresses.material4674
    · exact v4674_mb_checked.trans (by decide +kernel)
    · exact v4674_mg_checked.trans (by decide +kernel)
  upper_error := v4674_upper_checked
  lower_error := reuse_lower_error 84 97 Primitive.Addresses.material4674

def v4675_pa : Scalar.QComplex := ((999996923858293143736047027809 : Int)/10^30,(-2480377783940326950890774082 : Int)/10^30)
theorem v4675_pa_checked : Scalar.distance (sourceCoefficient 85 86 1 0) v4675_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4675_pb : Scalar.QComplex := ((-1070227257321723094647852 : Int)/10^30,(-431476193699358070448127566 : Int)/10^30)
theorem v4675_pb_checked : Scalar.distance (sourceCoefficient 85 86 1 1) v4675_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4675_pg : Scalar.QComplex := ((-93086143548276658129864 : Int)/10^30,(230889512698685308441 : Int)/10^30)
theorem v4675_pg_checked : Scalar.distance (sourceCoefficient 85 86 1 2) v4675_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4675_mb : Scalar.QComplex := ((-1442571381023370808528295 : Int)/10^30,(-431475109483129897673511240 : Int)/10^30)
theorem v4675_mb_checked : Scalar.distance (sourceCoefficient 85 86 3 1) v4675_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4675_mg : Scalar.QComplex := ((-93085909640800586844290 : Int)/10^30,(311218576165855747251 : Int)/10^30)
theorem v4675_mg_checked : Scalar.distance (sourceCoefficient 85 86 3 2) v4675_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4675_upper : Scalar.QComplex := ((999991153573305980963741545268 : Int)/10^30,(-4206278061276122989204571040 : Int)/10^30)
theorem v4675_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 86 5) 1) 14) v4675_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4675 : Material (85 : Basis) (86 : Basis) where
  plus := ![v4675_pa,v4675_pb,v4675_pg]
  minus := ![(Primitive.Addresses.material4675 1).one,v4675_mb,v4675_mg]
  upper := v4675_upper
  lower := (Primitive.Addresses.material4675 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4675_pa_checked.trans (by decide +kernel)
    · exact v4675_pb_checked.trans (by decide +kernel)
    · exact v4675_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 86 Primitive.Addresses.material4675
    · exact v4675_mb_checked.trans (by decide +kernel)
    · exact v4675_mg_checked.trans (by decide +kernel)
  upper_error := v4675_upper_checked
  lower_error := reuse_lower_error 85 86 Primitive.Addresses.material4675

def v4676_pa : Scalar.QComplex := ((999996921462385982915418408315 : Int)/10^30,(-2481343537408782146801186146 : Int)/10^30)
theorem v4676_pa_checked : Scalar.distance (sourceCoefficient 85 87 1 0) v4676_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4676_pb : Scalar.QComplex := ((-1070643958228981972904295 : Int)/10^30,(-431476192663485104729527320 : Int)/10^30)
theorem v4676_pb_checked : Scalar.distance (sourceCoefficient 85 87 1 1) v4676_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4676_pg : Scalar.QComplex := ((-93086143325024456118612 : Int)/10^30,(230979411240662645963 : Int)/10^30)
theorem v4676_pg_checked : Scalar.distance (sourceCoefficient 85 87 1 2) v4676_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4676_mb : Scalar.QComplex := ((-1442988080881561179411341 : Int)/10^30,(-431475108087663202205526069 : Int)/10^30)
theorem v4676_mb_checked : Scalar.distance (sourceCoefficient 85 87 3 1) v4676_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4676_mg : Scalar.QComplex := ((-93085909339970075113623 : Int)/10^30,(311308474481703153599 : Int)/10^30)
theorem v4676_mg_checked : Scalar.distance (sourceCoefficient 85 87 3 2) v4676_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4676_upper : Scalar.QComplex := ((999991149510599514481984997251 : Int)/10^30,(-4207243809171083434645816814 : Int)/10^30)
theorem v4676_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 87 5) 1) 14) v4676_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4676 : Material (85 : Basis) (87 : Basis) where
  plus := ![v4676_pa,v4676_pb,v4676_pg]
  minus := ![(Primitive.Addresses.material4676 1).one,v4676_mb,v4676_mg]
  upper := v4676_upper
  lower := (Primitive.Addresses.material4676 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4676_pa_checked.trans (by decide +kernel)
    · exact v4676_pb_checked.trans (by decide +kernel)
    · exact v4676_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 87 Primitive.Addresses.material4676
    · exact v4676_mb_checked.trans (by decide +kernel)
    · exact v4676_mg_checked.trans (by decide +kernel)
  upper_error := v4676_upper_checked
  lower_error := reuse_lower_error 85 87 Primitive.Addresses.material4676

def v4677_pa : Scalar.QComplex := ((999996892213650704804276770454 : Int)/10^30,(-2493103094590032909515669197 : Int)/10^30)
theorem v4677_pa_checked : Scalar.distance (sourceCoefficient 85 88 1 0) v4677_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4677_pb : Scalar.QComplex := ((-1075717942719044939453790 : Int)/10^30,(-431476180007067818198444776 : Int)/10^30)
theorem v4677_pb_checked : Scalar.distance (sourceCoefficient 85 88 1 1) v4677_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4677_pg : Scalar.QComplex := ((-93086140598454330706174 : Int)/10^30,(232074066426065054226 : Int)/10^30)
theorem v4677_pg_checked : Scalar.distance (sourceCoefficient 85 88 1 2) v4677_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4677_mb : Scalar.QComplex := ((-1448062052560429733361454 : Int)/10^30,(-431475091052630537090917045 : Int)/10^30)
theorem v4677_mb_checked : Scalar.distance (sourceCoefficient 85 88 3 1) v4677_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4677_mg : Scalar.QComplex := ((-93085905668762841364971 : Int)/10^30,(312403126906608190052 : Int)/10^30)
theorem v4677_mg_checked : Scalar.distance (sourceCoefficient 85 88 3 2) v4677_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4677_upper : Scalar.QComplex := ((999991099965978922781378626110 : Int)/10^30,(-4219003298357191485027258044 : Int)/10^30)
theorem v4677_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 88 5) 1) 14) v4677_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4677 : Material (85 : Basis) (88 : Basis) where
  plus := ![v4677_pa,v4677_pb,v4677_pg]
  minus := ![(Primitive.Addresses.material4677 1).one,v4677_mb,v4677_mg]
  upper := v4677_upper
  lower := (Primitive.Addresses.material4677 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4677_pa_checked.trans (by decide +kernel)
    · exact v4677_pb_checked.trans (by decide +kernel)
    · exact v4677_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 88 Primitive.Addresses.material4677
    · exact v4677_mb_checked.trans (by decide +kernel)
    · exact v4677_mg_checked.trans (by decide +kernel)
  upper_error := v4677_upper_checked
  lower_error := reuse_lower_error 85 88 Primitive.Addresses.material4677

def v4678_pa : Scalar.QComplex := ((999996851971471687018380139821 : Int)/10^30,(-2509192528791353660267474950 : Int)/10^30)
theorem v4678_pa_checked : Scalar.distance (sourceCoefficient 85 89 1 0) v4678_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4678_pb : Scalar.QComplex := ((-1082660171696384352323364 : Int)/10^30,(-431476162561658617896698088 : Int)/10^30)
theorem v4678_pb_checked : Scalar.distance (sourceCoefficient 85 89 1 1) v4678_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4678_pg : Scalar.QComplex := ((-93086136843628376534339 : Int)/10^30,(233571774392691078795 : Int)/10^30)
theorem v4678_pg_checked : Scalar.distance (sourceCoefficient 85 89 1 2) v4678_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4678_mb : Scalar.QComplex := ((-1455004263898257594632542 : Int)/10^30,(-431475067616396891454814435 : Int)/10^30)
theorem v4678_mb_checked : Scalar.distance (sourceCoefficient 85 89 3 1) v4678_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4678_mg : Scalar.QComplex := ((-93085900621483764350979 : Int)/10^30,(313900831075323402644 : Int)/10^30)
theorem v4678_mg_checked : Scalar.distance (sourceCoefficient 85 89 3 2) v4678_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4678_upper : Scalar.QComplex := ((999991031954956031583136713606 : Int)/10^30,(-4235092639140839747882195120 : Int)/10^30)
theorem v4678_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 89 5) 1) 14) v4678_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4678 : Material (85 : Basis) (89 : Basis) where
  plus := ![v4678_pa,v4678_pb,v4678_pg]
  minus := ![(Primitive.Addresses.material4678 1).one,v4678_mb,v4678_mg]
  upper := v4678_upper
  lower := (Primitive.Addresses.material4678 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4678_pa_checked.trans (by decide +kernel)
    · exact v4678_pb_checked.trans (by decide +kernel)
    · exact v4678_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 89 Primitive.Addresses.material4678
    · exact v4678_mb_checked.trans (by decide +kernel)
    · exact v4678_mg_checked.trans (by decide +kernel)
  upper_error := v4678_upper_checked
  lower_error := reuse_lower_error 85 89 Primitive.Addresses.material4678

def v4679_pa : Scalar.QComplex := ((999996785879950199373522547642 : Int)/10^30,(-2535395387120825071042161893 : Int)/10^30)
theorem v4679_pa_checked : Scalar.distance (sourceCoefficient 85 90 1 0) v4679_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4679_pb : Scalar.QComplex := ((-1093966115508097794021579 : Int)/10^30,(-431476133831720583789634057 : Int)/10^30)
theorem v4679_pb_checked : Scalar.distance (sourceCoefficient 85 90 1 1) v4679_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4679_pg : Scalar.QComplex := ((-93086130668435731267600 : Int)/10^30,(236010904869059629146 : Int)/10^30)
theorem v4679_pg_checked : Scalar.distance (sourceCoefficient 85 90 1 2) v4679_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4679_mb : Scalar.QComplex := ((-1466310178707608873012834 : Int)/10^30,(-431475029129949246114860456 : Int)/10^30)
theorem v4679_mb_checked : Scalar.distance (sourceCoefficient 85 90 3 1) v4679_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4679_mg : Scalar.QComplex := ((-93085892341433671643294 : Int)/10^30,(316339955314579070360 : Int)/10^30)
theorem v4679_mg_checked : Scalar.distance (sourceCoefficient 85 90 3 2) v4679_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4679_upper : Scalar.QComplex := ((999990920639776607566950950428 : Int)/10^30,(-4261295344376261369184483769 : Int)/10^30)
theorem v4679_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 90 5) 1) 14) v4679_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4679 : Material (85 : Basis) (90 : Basis) where
  plus := ![v4679_pa,v4679_pb,v4679_pg]
  minus := ![(Primitive.Addresses.material4679 1).one,v4679_mb,v4679_mg]
  upper := v4679_upper
  lower := (Primitive.Addresses.material4679 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4679_pa_checked.trans (by decide +kernel)
    · exact v4679_pb_checked.trans (by decide +kernel)
    · exact v4679_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 90 Primitive.Addresses.material4679
    · exact v4679_mb_checked.trans (by decide +kernel)
    · exact v4679_mg_checked.trans (by decide +kernel)
  upper_error := v4679_upper_checked
  lower_error := reuse_lower_error 85 90 Primitive.Addresses.material4679

def v4680_pa : Scalar.QComplex := ((999996748345854650923459631570 : Int)/10^30,(-2550156410388090708277940979 : Int)/10^30)
theorem v4680_pa_checked : Scalar.distance (sourceCoefficient 85 91 1 0) v4680_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4680_pb : Scalar.QComplex := ((-1100335164812959104071180 : Int)/10^30,(-431476117473166006558079927 : Int)/10^30)
theorem v4680_pb_checked : Scalar.distance (sourceCoefficient 85 91 1 1) v4680_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4680_pg : Scalar.QComplex := ((-93086127156891028255596 : Int)/10^30,(237384955781122101590 : Int)/10^30)
theorem v4680_pg_checked : Scalar.distance (sourceCoefficient 85 91 1 2) v4680_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4680_mb : Scalar.QComplex := ((-1472679211524286208727135 : Int)/10^30,(-431475007275198061157756701 : Int)/10^30)
theorem v4680_mb_checked : Scalar.distance (sourceCoefficient 85 91 3 1) v4680_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4680_mg : Scalar.QComplex := ((-93085887644146223985756 : Int)/10^30,(317714002684714666417 : Int)/10^30)
theorem v4680_mg_checked : Scalar.distance (sourceCoefficient 85 91 3 2) v4680_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4680_upper : Scalar.QComplex := ((999990857629549912012909432670 : Int)/10^30,(-4276056280878272951348952143 : Int)/10^30)
theorem v4680_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 91 5) 1) 14) v4680_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4680 : Material (85 : Basis) (91 : Basis) where
  plus := ![v4680_pa,v4680_pb,v4680_pg]
  minus := ![(Primitive.Addresses.material4680 1).one,v4680_mb,v4680_mg]
  upper := v4680_upper
  lower := (Primitive.Addresses.material4680 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4680_pa_checked.trans (by decide +kernel)
    · exact v4680_pb_checked.trans (by decide +kernel)
    · exact v4680_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 91 Primitive.Addresses.material4680
    · exact v4680_mb_checked.trans (by decide +kernel)
    · exact v4680_mg_checked.trans (by decide +kernel)
  upper_error := v4680_upper_checked
  lower_error := reuse_lower_error 85 91 Primitive.Addresses.material4680

def v4681_pa : Scalar.QComplex := ((999996666342194917603675747533 : Int)/10^30,(-2582112409809152995335355747 : Int)/10^30)
theorem v4681_pa_checked : Scalar.distance (sourceCoefficient 85 92 1 0) v4681_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4681_pb : Scalar.QComplex := ((-1114123459017080136836147 : Int)/10^30,(-431476081629250632397147525 : Int)/10^30)
theorem v4681_pb_checked : Scalar.distance (sourceCoefficient 85 92 1 1) v4681_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4681_pg : Scalar.QComplex := ((-93086119473715950063414 : Int)/10^30,(240359625550801160507 : Int)/10^30)
theorem v4681_pg_checked : Scalar.distance (sourceCoefficient 85 92 1 2) v4681_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4681_mb : Scalar.QComplex := ((-1486467469662710535242444 : Int)/10^30,(-431474959532619136886500909 : Int)/10^30)
theorem v4681_mb_checked : Scalar.distance (sourceCoefficient 85 92 3 1) v4681_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4681_mg : Scalar.QComplex := ((-93085877393967969510839 : Int)/10^30,(320688664716554165839 : Int)/10^30)
theorem v4681_mg_checked : Scalar.distance (sourceCoefficient 85 92 3 2) v4681_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4681_upper : Scalar.QComplex := ((999990720472856338379497714233 : Int)/10^30,(-4308012091173750530305565620 : Int)/10^30)
theorem v4681_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 92 5) 1) 14) v4681_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4681 : Material (85 : Basis) (92 : Basis) where
  plus := ![v4681_pa,v4681_pb,v4681_pg]
  minus := ![(Primitive.Addresses.material4681 1).one,v4681_mb,v4681_mg]
  upper := v4681_upper
  lower := (Primitive.Addresses.material4681 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4681_pa_checked.trans (by decide +kernel)
    · exact v4681_pb_checked.trans (by decide +kernel)
    · exact v4681_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 92 Primitive.Addresses.material4681
    · exact v4681_mb_checked.trans (by decide +kernel)
    · exact v4681_mg_checked.trans (by decide +kernel)
  upper_error := v4681_upper_checked
  lower_error := reuse_lower_error 85 92 Primitive.Addresses.material4681

def v4682_pa : Scalar.QComplex := ((999996567694828707084481617120 : Int)/10^30,(-2620037893212050884187470868 : Int)/10^30)
theorem v4682_pa_checked : Scalar.distance (sourceCoefficient 85 93 1 0) v4682_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4682_pb : Scalar.QComplex := ((-1130487450608227201642107 : Int)/10^30,(-431476038327209614081134450 : Int)/10^30)
theorem v4682_pb_checked : Scalar.distance (sourceCoefficient 85 93 1 1) v4682_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4682_pg : Scalar.QComplex := ((-93086110211385835501850 : Int)/10^30,(243889973190360328798 : Int)/10^30)
theorem v4682_pg_checked : Scalar.distance (sourceCoefficient 85 93 1 2) v4682_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4682_mb : Scalar.QComplex := ((-1502831417793084512027048 : Int)/10^30,(-431474902109206505561729065 : Int)/10^30)
theorem v4682_mb_checked : Scalar.distance (sourceCoefficient 85 93 3 1) v4682_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4682_mg : Scalar.QComplex := ((-93085865085110291753817 : Int)/10^30,(324219003048629834061 : Int)/10^30)
theorem v4682_mg_checked : Scalar.distance (sourceCoefficient 85 93 3 2) v4682_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4682_upper : Scalar.QComplex := ((999990556369693271100614069562 : Int)/10^30,(-4345937347834691070570312711 : Int)/10^30)
theorem v4682_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 93 5) 1) 14) v4682_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4682 : Material (85 : Basis) (93 : Basis) where
  plus := ![v4682_pa,v4682_pb,v4682_pg]
  minus := ![(Primitive.Addresses.material4682 1).one,v4682_mb,v4682_mg]
  upper := v4682_upper
  lower := (Primitive.Addresses.material4682 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4682_pa_checked.trans (by decide +kernel)
    · exact v4682_pb_checked.trans (by decide +kernel)
    · exact v4682_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 93 Primitive.Addresses.material4682
    · exact v4682_mb_checked.trans (by decide +kernel)
    · exact v4682_mg_checked.trans (by decide +kernel)
  upper_error := v4682_upper_checked
  lower_error := reuse_lower_error 85 93 Primitive.Addresses.material4682

def v4683_pa : Scalar.QComplex := ((999996449317458610850780957318 : Int)/10^30,(-2664836294302482797895747787 : Int)/10^30)
theorem v4683_pa_checked : Scalar.distance (sourceCoefficient 85 94 1 0) v4683_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4683_pb : Scalar.QComplex := ((-1149816950545878947733286 : Int)/10^30,(-431475986111885636028555486 : Int)/10^30)
theorem v4683_pb_checked : Scalar.distance (sourceCoefficient 85 94 1 1) v4683_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4683_pg : Scalar.QComplex := ((-93086099069287555863569 : Int)/10^30,(248060096077526401067 : Int)/10^30)
theorem v4683_pg_checked : Scalar.distance (sourceCoefficient 85 94 1 2) v4683_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4683_mb : Scalar.QComplex := ((-1522160865474007127376124 : Int)/10^30,(-431474833213414091827343678 : Int)/10^30)
theorem v4683_mb_checked : Scalar.distance (sourceCoefficient 85 94 3 1) v4683_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4683_mg : Scalar.QComplex := ((-93085850344387924566428 : Int)/10^30,(328389114767939577557 : Int)/10^30)
theorem v4683_mg_checked : Scalar.distance (sourceCoefficient 85 94 3 2) v4683_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4683_upper : Scalar.QComplex := ((999990360674523281168685471901 : Int)/10^30,(-4390735477894565274961492219 : Int)/10^30)
theorem v4683_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 94 5) 1) 14) v4683_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4683 : Material (85 : Basis) (94 : Basis) where
  plus := ![v4683_pa,v4683_pb,v4683_pg]
  minus := ![(Primitive.Addresses.material4683 1).one,v4683_mb,v4683_mg]
  upper := v4683_upper
  lower := (Primitive.Addresses.material4683 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4683_pa_checked.trans (by decide +kernel)
    · exact v4683_pb_checked.trans (by decide +kernel)
    · exact v4683_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 94 Primitive.Addresses.material4683
    · exact v4683_mb_checked.trans (by decide +kernel)
    · exact v4683_mg_checked.trans (by decide +kernel)
  upper_error := v4683_upper_checked
  lower_error := reuse_lower_error 85 94 Primitive.Addresses.material4683

def v4684_pa : Scalar.QComplex := ((999996330353800540117726552987 : Int)/10^30,(-2709110358146477453413969885 : Int)/10^30)
theorem v4684_pa_checked : Scalar.distance (sourceCoefficient 85 95 1 0) v4684_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4684_pb : Scalar.QComplex := ((-1168920209916176258735317 : Int)/10^30,(-431475933373316264165779787 : Int)/10^30)
theorem v4684_pb_checked : Scalar.distance (sourceCoefficient 85 95 1 1) v4684_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4684_pg : Scalar.QComplex := ((-93086087843459390181303 : Int)/10^30,(252181410192602217304 : Int)/10^30)
theorem v4684_pg_checked : Scalar.distance (sourceCoefficient 85 95 1 2) v4684_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4684_mb : Scalar.QComplex := ((-1541264072220277801806351 : Int)/10^30,(-431474763989611899240910911 : Int)/10^30)
theorem v4684_mb_checked : Scalar.distance (sourceCoefficient 85 95 3 1) v4684_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4684_mg : Scalar.QComplex := ((-93085835562055474559917 : Int)/10^30,(332510417661077680940 : Int)/10^30)
theorem v4684_mg_checked : Scalar.distance (sourceCoefficient 85 95 3 2) v4684_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4684_upper : Scalar.QComplex := ((999990165298024709791758716288 : Int)/10^30,(-4435009270477061100394958682 : Int)/10^30)
theorem v4684_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 95 5) 1) 14) v4684_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4684 : Material (85 : Basis) (95 : Basis) where
  plus := ![v4684_pa,v4684_pb,v4684_pg]
  minus := ![(Primitive.Addresses.material4684 1).one,v4684_mb,v4684_mg]
  upper := v4684_upper
  lower := (Primitive.Addresses.material4684 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4684_pa_checked.trans (by decide +kernel)
    · exact v4684_pb_checked.trans (by decide +kernel)
    · exact v4684_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 95 Primitive.Addresses.material4684
    · exact v4684_mb_checked.trans (by decide +kernel)
    · exact v4684_mg_checked.trans (by decide +kernel)
  upper_error := v4684_upper_checked
  lower_error := reuse_lower_error 85 95 Primitive.Addresses.material4684

def v4685_pa : Scalar.QComplex := ((999996272520935982739770595981 : Int)/10^30,(-2730374376149605563796734116 : Int)/10^30)
theorem v4685_pa_checked : Scalar.distance (sourceCoefficient 85 96 1 0) v4685_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4685_pb : Scalar.QComplex := ((-1178095153479569085669966 : Int)/10^30,(-431475907643076223312610216 : Int)/10^30)
theorem v4685_pb_checked : Scalar.distance (sourceCoefficient 85 96 1 1) v4685_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4685_pg : Scalar.QComplex := ((-93086082376226768524213 : Int)/10^30,(254160801475267349086 : Int)/10^30)
theorem v4685_pg_checked : Scalar.distance (sourceCoefficient 85 96 1 2) v4685_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4685_mb : Scalar.QComplex := ((-1550438990163381516191122 : Int)/10^30,(-431474730341818367842523857 : Int)/10^30)
theorem v4685_mb_checked : Scalar.distance (sourceCoefficient 85 96 3 1) v4685_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4685_mg : Scalar.QComplex := ((-93085828386699360137412 : Int)/10^30,(334489803488749458061 : Int)/10^30)
theorem v4685_mg_checked : Scalar.distance (sourceCoefficient 85 96 3 2) v4685_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4685_upper : Scalar.QComplex := ((999990070765480270917197200583 : Int)/10^30,(-4456273156995654572591676104 : Int)/10^30)
theorem v4685_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 96 5) 1) 14) v4685_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4685 : Material (85 : Basis) (96 : Basis) where
  plus := ![v4685_pa,v4685_pb,v4685_pg]
  minus := ![(Primitive.Addresses.material4685 1).one,v4685_mb,v4685_mg]
  upper := v4685_upper
  lower := (Primitive.Addresses.material4685 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4685_pa_checked.trans (by decide +kernel)
    · exact v4685_pb_checked.trans (by decide +kernel)
    · exact v4685_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 96 Primitive.Addresses.material4685
    · exact v4685_mb_checked.trans (by decide +kernel)
    · exact v4685_mg_checked.trans (by decide +kernel)
  upper_error := v4685_upper_checked
  lower_error := reuse_lower_error 85 96 Primitive.Addresses.material4685

def v4686_pa : Scalar.QComplex := ((999996070084330871336204223820 : Int)/10^30,(-2803536319368836200445710284 : Int)/10^30)
theorem v4686_pa_checked : Scalar.distance (sourceCoefficient 85 97 1 0) v4686_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4686_pb : Scalar.QComplex := ((-1209662878118605934742228 : Int)/10^30,(-431475817127219799781125916 : Int)/10^30)
theorem v4686_pb_checked : Scalar.distance (sourceCoefficient 85 97 1 1) v4686_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4686_pg : Scalar.QComplex := ((-93086063190286555853381 : Int)/10^30,(260971184575778332634 : Int)/10^30)
theorem v4686_pg_checked : Scalar.distance (sourceCoefficient 85 97 1 2) v4686_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4686_mb : Scalar.QComplex := ((-1582006624937204355194395 : Int)/10^30,(-431474612584471041551985780 : Int)/10^30)
theorem v4686_mb_checked : Scalar.distance (sourceCoefficient 85 97 3 1) v4686_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4686_mg : Scalar.QComplex := ((-93085803323712403796541 : Int)/10^30,(341300167496841262540 : Int)/10^30)
theorem v4686_mg_checked : Scalar.distance (sourceCoefficient 85 97 3 2) v4686_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4686_upper : Scalar.QComplex := ((999989742058299868306881605041 : Int)/10^30,(-4529434641861549472831546312 : Int)/10^30)
theorem v4686_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 85 97 5) 1) 14) v4686_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4686 : Material (85 : Basis) (97 : Basis) where
  plus := ![v4686_pa,v4686_pb,v4686_pg]
  minus := ![(Primitive.Addresses.material4686 1).one,v4686_mb,v4686_mg]
  upper := v4686_upper
  lower := (Primitive.Addresses.material4686 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4686_pa_checked.trans (by decide +kernel)
    · exact v4686_pb_checked.trans (by decide +kernel)
    · exact v4686_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 85 97 Primitive.Addresses.material4686
    · exact v4686_mb_checked.trans (by decide +kernel)
    · exact v4686_mg_checked.trans (by decide +kernel)
  upper_error := v4686_upper_checked
  lower_error := reuse_lower_error 85 97 Primitive.Addresses.material4686

def v4687_pa : Scalar.QComplex := ((999996885166518005414733037207 : Int)/10^30,(-2495928136345585968284027528 : Int)/10^30)
theorem v4687_pa_checked : Scalar.distance (sourceCoefficient 86 87 1 0) v4687_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4687_pb : Scalar.QComplex := ((-1076936884866005054205553 : Int)/10^30,(-431476177019956461678478510 : Int)/10^30)
theorem v4687_pb_checked : Scalar.distance (sourceCoefficient 86 87 1 1) v4687_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4687_pg : Scalar.QComplex := ((-93086139948240252891163 : Int)/10^30,(232337039491805411260 : Int)/10^30)
theorem v4687_pg_checked : Scalar.distance (sourceCoefficient 86 87 1 2) v4687_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4687_mb : Scalar.QComplex := ((-1449280991675779412216410 : Int)/10^30,(-431475087013628119098795603 : Int)/10^30)
theorem v4687_mb_checked : Scalar.distance (sourceCoefficient 86 87 3 1) v4687_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4687_mg : Scalar.QComplex := ((-93085904791615093787665 : Int)/10^30,(312666099313326191649 : Int)/10^30)
theorem v4687_mg_checked : Scalar.distance (sourceCoefficient 86 87 3 2) v4687_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4687_upper : Scalar.QComplex := ((999991088043090934969665920712 : Int)/10^30,(-4221828323742464973353438033 : Int)/10^30)
theorem v4687_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 86 87 5) 1) 14) v4687_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4687 : Material (86 : Basis) (87 : Basis) where
  plus := ![v4687_pa,v4687_pb,v4687_pg]
  minus := ![(Primitive.Addresses.material4687 1).one,v4687_mb,v4687_mg]
  upper := v4687_upper
  lower := (Primitive.Addresses.material4687 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4687_pa_checked.trans (by decide +kernel)
    · exact v4687_pb_checked.trans (by decide +kernel)
    · exact v4687_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 86 87 Primitive.Addresses.material4687
    · exact v4687_mb_checked.trans (by decide +kernel)
    · exact v4687_mg_checked.trans (by decide +kernel)
  upper_error := v4687_upper_checked
  lower_error := reuse_lower_error 86 87 Primitive.Addresses.material4687

def v4688_pa : Scalar.QComplex := ((999996855746273774151228237389 : Int)/10^30,(-2507687693099003638046059345 : Int)/10^30)
theorem v4688_pa_checked : Scalar.distance (sourceCoefficient 86 88 1 0) v4688_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4688_pb : Scalar.QComplex := ((-1082010869233001113288814 : Int)/10^30,(-431476164314204336830954161 : Int)/10^30)
theorem v4688_pb_checked : Scalar.distance (sourceCoefficient 86 88 1 1) v4688_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4688_pg : Scalar.QComplex := ((-93086137208365830700231 : Int)/10^30,(233431694644019940198 : Int)/10^30)
theorem v4688_pg_checked : Scalar.distance (sourceCoefficient 86 88 1 2) v4688_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4688_mb : Scalar.QComplex := ((-1454354963189007361015269 : Int)/10^30,(-431475069929260740238558209 : Int)/10^30)
theorem v4688_mb_checked : Scalar.distance (sourceCoefficient 86 88 3 1) v4688_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4688_mg : Scalar.QComplex := ((-93085901107103596853960 : Int)/10^30,(313760751693562352218 : Int)/10^30)
theorem v4688_mg_checked : Scalar.distance (sourceCoefficient 86 88 3 2) v4688_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4688_upper : Scalar.QComplex := ((999991038326962383960240972109 : Int)/10^30,(-4233587812204731674019272770 : Int)/10^30)
theorem v4688_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 86 88 5) 1) 14) v4688_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4688 : Material (86 : Basis) (88 : Basis) where
  plus := ![v4688_pa,v4688_pb,v4688_pg]
  minus := ![(Primitive.Addresses.material4688 1).one,v4688_mb,v4688_mg]
  upper := v4688_upper
  lower := (Primitive.Addresses.material4688 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4688_pa_checked.trans (by decide +kernel)
    · exact v4688_pb_checked.trans (by decide +kernel)
    · exact v4688_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 86 88 Primitive.Addresses.material4688
    · exact v4688_mb_checked.trans (by decide +kernel)
    · exact v4688_mg_checked.trans (by decide +kernel)
  upper_error := v4688_upper_checked
  lower_error := reuse_lower_error 86 88 Primitive.Addresses.material4688

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
