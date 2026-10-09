import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B126

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3025_pa : Scalar.QComplex := ((999998854005600539271083057749 : Int)/10^30,(-1513931136352738548341527849 : Int)/10^30)
theorem v3025_pa_checked : Scalar.distance (sourceCoefficient 38 81 1 0) v3025_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3025_pb : Scalar.QComplex := ((-653227203860735473385535 : Int)/10^30,(-431476993623189281720033499 : Int)/10^30)
theorem v3025_pb_checked : Scalar.distance (sourceCoefficient 38 81 1 1) v3025_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3025_pg : Scalar.QComplex := ((-93086319670829610625223 : Int)/10^30,(140926439219063432737 : Int)/10^30)
theorem v3025_pg_checked : Scalar.distance (sourceCoefficient 38 81 1 2) v3025_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3025_mb : Scalar.QComplex := ((-1025572173128800038075043 : Int)/10^30,(-431476269258928412352109299 : Int)/10^30)
theorem v3025_mb_checked : Scalar.distance (sourceCoefficient 38 81 3 1) v3025_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3025_mg : Scalar.QComplex := ((-93086163397368587357526 : Int)/10^30,(221255688169428576260 : Int)/10^30)
theorem v3025_mg_checked : Scalar.distance (sourceCoefficient 38 81 3 2) v3025_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3025_upper : Scalar.QComplex := ((999994751716977030006166337934 : Int)/10^30,(-3239836184356440339105160853 : Int)/10^30)
theorem v3025_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 81 5) 1) 14) v3025_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3025 : Material (38 : Basis) (81 : Basis) where
  plus := ![v3025_pa,v3025_pb,v3025_pg]
  minus := ![(Primitive.Addresses.material3025 1).one,v3025_mb,v3025_mg]
  upper := v3025_upper
  lower := (Primitive.Addresses.material3025 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3025_pa_checked.trans (by decide +kernel)
    · exact v3025_pb_checked.trans (by decide +kernel)
    · exact v3025_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 81 Primitive.Addresses.material3025
    · exact v3025_mb_checked.trans (by decide +kernel)
    · exact v3025_mg_checked.trans (by decide +kernel)
  upper_error := v3025_upper_checked
  lower_error := reuse_lower_error 38 81 Primitive.Addresses.material3025

def v3026_pa : Scalar.QComplex := ((999998838907328764212622691242 : Int)/10^30,(-1523871383790437728016739210 : Int)/10^30)
theorem v3026_pa_checked : Scalar.distance (sourceCoefficient 38 82 1 0) v3026_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3026_pb : Scalar.QComplex := ((-657516195371616354407953 : Int)/10^30,(-431476986134416437804098648 : Int)/10^30)
theorem v3026_pb_checked : Scalar.distance (sourceCoefficient 38 82 1 1) v3026_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3026_pg : Scalar.QComplex := ((-93086318160298178294075 : Int)/10^30,(141851741169907612901 : Int)/10^30)
theorem v3026_pg_checked : Scalar.distance (sourceCoefficient 38 82 1 2) v3026_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3026_mb : Scalar.QComplex := ((-1029861156580219680509994 : Int)/10^30,(-431476258068951851965237217 : Int)/10^30)
theorem v3026_mb_checked : Scalar.distance (sourceCoefficient 38 82 3 1) v3026_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3026_mg : Scalar.QComplex := ((-93086161088343807940589 : Int)/10^30,(222180988472219957445 : Int)/10^30)
theorem v3026_mg_checked : Scalar.distance (sourceCoefficient 38 82 3 2) v3026_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3026_upper : Scalar.QComplex := ((999994719462762436784453407579 : Int)/10^30,(-3249776390931061244580348762 : Int)/10^30)
theorem v3026_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 82 5) 1) 14) v3026_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3026 : Material (38 : Basis) (82 : Basis) where
  plus := ![v3026_pa,v3026_pb,v3026_pg]
  minus := ![(Primitive.Addresses.material3026 1).one,v3026_mb,v3026_mg]
  upper := v3026_upper
  lower := (Primitive.Addresses.material3026 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3026_pa_checked.trans (by decide +kernel)
    · exact v3026_pb_checked.trans (by decide +kernel)
    · exact v3026_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 82 Primitive.Addresses.material3026
    · exact v3026_mb_checked.trans (by decide +kernel)
    · exact v3026_mg_checked.trans (by decide +kernel)
  upper_error := v3026_upper_checked
  lower_error := reuse_lower_error 38 82 Primitive.Addresses.material3026

def v3027_pa : Scalar.QComplex := ((999998818138442153078696227505 : Int)/10^30,(-1537439988714063821619355679 : Int)/10^30)
theorem v3027_pa_checked : Scalar.distance (sourceCoefficient 38 83 1 0) v3027_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3027_pb : Scalar.QComplex := ((-663370740848009145271889 : Int)/10^30,(-431476975820359525006994369 : Int)/10^30)
theorem v3027_pb_checked : Scalar.distance (sourceCoefficient 38 83 1 1) v3027_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3027_pg : Scalar.QComplex := ((-93086316081076444701281 : Int)/10^30,(143114793886997200998 : Int)/10^30)
theorem v3027_pg_checked : Scalar.distance (sourceCoefficient 38 83 1 2) v3027_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3027_mb : Scalar.QComplex := ((-1035715690976131036701962 : Int)/10^30,(-431476242702689712375953122 : Int)/10^30)
theorem v3027_mb_checked : Scalar.distance (sourceCoefficient 38 83 3 1) v3027_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3027_mg : Scalar.QComplex := ((-93086157919165239471436 : Int)/10^30,(223444038924742583188 : Int)/10^30)
theorem v3027_mg_checked : Scalar.distance (sourceCoefficient 38 83 3 2) v3027_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3027_upper : Scalar.QComplex := ((999994675275725594511952762733 : Int)/10^30,(-3263344939800630032598333572 : Int)/10^30)
theorem v3027_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 83 5) 1) 14) v3027_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3027 : Material (38 : Basis) (83 : Basis) where
  plus := ![v3027_pa,v3027_pb,v3027_pg]
  minus := ![(Primitive.Addresses.material3027 1).one,v3027_mb,v3027_mg]
  upper := v3027_upper
  lower := (Primitive.Addresses.material3027 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3027_pa_checked.trans (by decide +kernel)
    · exact v3027_pb_checked.trans (by decide +kernel)
    · exact v3027_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 83 Primitive.Addresses.material3027
    · exact v3027_mb_checked.trans (by decide +kernel)
    · exact v3027_mg_checked.trans (by decide +kernel)
  upper_error := v3027_upper_checked
  lower_error := reuse_lower_error 38 83 Primitive.Addresses.material3027

def v3028_pa : Scalar.QComplex := ((999998763496874539709908304110 : Int)/10^30,(-1572579003414645909256728489 : Int)/10^30)
theorem v3028_pa_checked : Scalar.distance (sourceCoefficient 38 84 1 0) v3028_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3028_pb : Scalar.QComplex := ((-678532428860636500580431 : Int)/10^30,(-431476948617415398976090353 : Int)/10^30)
theorem v3028_pb_checked : Scalar.distance (sourceCoefficient 38 84 1 1) v3028_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3028_pg : Scalar.QComplex := ((-93086310603517354644428 : Int)/10^30,(146385758566873498574 : Int)/10^30)
theorem v3028_pg_checked : Scalar.distance (sourceCoefficient 38 84 1 2) v3028_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3028_mb : Scalar.QComplex := ((-1050877349868453415894181 : Int)/10^30,(-431476202415901817426217981 : Int)/10^30)
theorem v3028_mb_checked : Scalar.distance (sourceCoefficient 38 84 3 1) v3028_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3028_mg : Scalar.QComplex := ((-93086149618912989007375 : Int)/10^30,(226714997659802445360 : Int)/10^30)
theorem v3028_mg_checked : Scalar.distance (sourceCoefficient 38 84 3 2) v3028_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3028_upper : Scalar.QComplex := ((999994559987487776646807408711 : Int)/10^30,(-3298483807859388785958887713 : Int)/10^30)
theorem v3028_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 84 5) 1) 14) v3028_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3028 : Material (38 : Basis) (84 : Basis) where
  plus := ![v3028_pa,v3028_pb,v3028_pg]
  minus := ![(Primitive.Addresses.material3028 1).one,v3028_mb,v3028_mg]
  upper := v3028_upper
  lower := (Primitive.Addresses.material3028 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3028_pa_checked.trans (by decide +kernel)
    · exact v3028_pb_checked.trans (by decide +kernel)
    · exact v3028_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 84 Primitive.Addresses.material3028
    · exact v3028_mb_checked.trans (by decide +kernel)
    · exact v3028_mg_checked.trans (by decide +kernel)
  upper_error := v3028_upper_checked
  lower_error := reuse_lower_error 38 84 Primitive.Addresses.material3028

def v3029_pa : Scalar.QComplex := ((999998636048797150653273401542 : Int)/10^30,(-1651635718109719767820223006 : Int)/10^30)
theorem v3029_pa_checked : Scalar.distance (sourceCoefficient 38 85 1 0) v3029_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3029_pb : Scalar.QComplex := ((-712643606516184466141841 : Int)/10^30,(-431476884818579959938480514 : Int)/10^30)
theorem v3029_pb_checked : Scalar.distance (sourceCoefficient 38 85 1 1) v3029_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3029_pg : Scalar.QComplex := ((-93086297789732923946227 : Int)/10^30,(153744863996612937940 : Int)/10^30)
theorem v3029_pg_checked : Scalar.distance (sourceCoefficient 38 85 1 2) v3029_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3029_mb : Scalar.QComplex := ((-1084988459767329391455505 : Int)/10^30,(-431476109180680127283981315 : Int)/10^30)
theorem v3029_mb_checked : Scalar.distance (sourceCoefficient 38 85 3 1) v3029_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3029_mg : Scalar.QComplex := ((-93086130454556785406458 : Int)/10^30,(234074089291691753236 : Int)/10^30)
theorem v3029_mg_checked : Scalar.distance (sourceCoefficient 38 85 3 2) v3029_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3029_upper : Scalar.QComplex := ((999994296094882611965649553884 : Int)/10^30,(-3377540184844953186021422351 : Int)/10^30)
theorem v3029_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 85 5) 1) 14) v3029_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3029 : Material (38 : Basis) (85 : Basis) where
  plus := ![v3029_pa,v3029_pb,v3029_pg]
  minus := ![(Primitive.Addresses.material3029 1).one,v3029_mb,v3029_mg]
  upper := v3029_upper
  lower := (Primitive.Addresses.material3029 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3029_pa_checked.trans (by decide +kernel)
    · exact v3029_pb_checked.trans (by decide +kernel)
    · exact v3029_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 85 Primitive.Addresses.material3029
    · exact v3029_mb_checked.trans (by decide +kernel)
    · exact v3029_mg_checked.trans (by decide +kernel)
  upper_error := v3029_upper_checked
  lower_error := reuse_lower_error 38 85 Primitive.Addresses.material3029

def v3030_pa : Scalar.QComplex := ((999998611853922242330506615904 : Int)/10^30,(-1666220342141400514946539784 : Int)/10^30)
theorem v3030_pa_checked : Scalar.distance (sourceCoefficient 38 86 1 0) v3030_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3030_pb : Scalar.QComplex := ((-718936540371790881912686 : Int)/10^30,(-431476872655922211854557449 : Int)/10^30)
theorem v3030_pb_checked : Scalar.distance (sourceCoefficient 38 86 1 1) v3030_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3030_pg : Scalar.QComplex := ((-93086295351647243441153 : Int)/10^30,(155102494194416096737 : Int)/10^30)
theorem v3030_pg_checked : Scalar.distance (sourceCoefficient 38 86 1 2) v3030_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3030_mb : Scalar.QComplex := ((-1091281380783963080672873 : Int)/10^30,(-431476091587508413744754017 : Int)/10^30)
theorem v3030_mb_checked : Scalar.distance (sourceCoefficient 38 86 3 1) v3030_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3030_mg : Scalar.QComplex := ((-93086126844898297402268 : Int)/10^30,(235431716880029007653 : Int)/10^30)
theorem v3030_mg_checked : Scalar.distance (sourceCoefficient 38 86 3 2) v3030_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3030_upper : Scalar.QComplex := ((999994246728305767142570812225 : Int)/10^30,(-3392124745396390518386533532 : Int)/10^30)
theorem v3030_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 86 5) 1) 14) v3030_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3030 : Material (38 : Basis) (86 : Basis) where
  plus := ![v3030_pa,v3030_pb,v3030_pg]
  minus := ![(Primitive.Addresses.material3030 1).one,v3030_mb,v3030_mg]
  upper := v3030_upper
  lower := (Primitive.Addresses.material3030 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3030_pa_checked.trans (by decide +kernel)
    · exact v3030_pb_checked.trans (by decide +kernel)
    · exact v3030_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 86 Primitive.Addresses.material3030
    · exact v3030_mb_checked.trans (by decide +kernel)
    · exact v3030_mg_checked.trans (by decide +kernel)
  upper_error := v3030_upper_checked
  lower_error := reuse_lower_error 38 86 Primitive.Addresses.material3030

def v3031_pa : Scalar.QComplex := ((999998610244292873652268938903 : Int)/10^30,(-1667186097240428037473485180 : Int)/10^30)
theorem v3031_pa_checked : Scalar.distance (sourceCoefficient 38 87 1 0) v3031_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3031_pb : Scalar.QComplex := ((-719353241748086617564230 : Int)/10^30,(-431476871846223367833399758 : Int)/10^30)
theorem v3031_pb_checked : Scalar.distance (sourceCoefficient 38 87 1 1) v3031_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3031_pg : Scalar.QComplex := ((-93086295189388201019242 : Int)/10^30,(155192392862880229725 : Int)/10^30)
theorem v3031_pg_checked : Scalar.distance (sourceCoefficient 38 87 1 2) v3031_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3031_mb : Scalar.QComplex := ((-1091698081306368214827755 : Int)/10^30,(-431476090418215351001565929 : Int)/10^30)
theorem v3031_mb_checked : Scalar.distance (sourceCoefficient 38 87 3 1) v3031_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3031_mg : Scalar.QComplex := ((-93086126605060813397994 : Int)/10^30,(235521615374997512065 : Int)/10^30)
theorem v3031_mg_checked : Scalar.distance (sourceCoefficient 38 87 3 2) v3031_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3031_upper : Scalar.QComplex := ((999994243451873107514885114012 : Int)/10^30,(-3393090496278965000572040020 : Int)/10^30)
theorem v3031_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 87 5) 1) 14) v3031_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3031 : Material (38 : Basis) (87 : Basis) where
  plus := ![v3031_pa,v3031_pb,v3031_pg]
  minus := ![(Primitive.Addresses.material3031 1).one,v3031_mb,v3031_mg]
  upper := v3031_upper
  lower := (Primitive.Addresses.material3031 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3031_pa_checked.trans (by decide +kernel)
    · exact v3031_pb_checked.trans (by decide +kernel)
    · exact v3031_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 87 Primitive.Addresses.material3031
    · exact v3031_mb_checked.trans (by decide +kernel)
    · exact v3031_mg_checked.trans (by decide +kernel)
  upper_error := v3031_upper_checked
  lower_error := reuse_lower_error 38 87 Primitive.Addresses.material3031

def v3032_pa : Scalar.QComplex := ((999998590569718065070998461914 : Int)/10^30,(-1678945674337361747116573421 : Int)/10^30)
theorem v3032_pa_checked : Scalar.distance (sourceCoefficient 38 88 1 0) v3032_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3032_pb : Scalar.QComplex := ((-724427231966929096070836 : Int)/10^30,(-431476861943829348462886299 : Int)/10^30)
theorem v3032_pb_checked : Scalar.distance (sourceCoefficient 38 88 1 1) v3032_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3032_pg : Scalar.QComplex := ((-93086293205505078975972 : Int)/10^30,(156287049593182470738 : Int)/10^30)
theorem v3032_pg_checked : Scalar.distance (sourceCoefficient 38 88 1 2) v3032_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3032_mb : Scalar.QComplex := ((-1096772061090612190604621 : Int)/10^30,(-431476076137199983920094376 : Int)/10^30)
theorem v3032_mb_checked : Scalar.distance (sourceCoefficient 38 88 3 1) v3032_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3032_mg : Scalar.QComplex := ((-93086123676538973303219 : Int)/10^30,(236616269985707240558 : Int)/10^30)
theorem v3032_mg_checked : Scalar.distance (sourceCoefficient 38 88 3 2) v3032_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3032_upper : Scalar.QComplex := ((999994203481364353094760675520 : Int)/10^30,(-3404850021904858745167385926 : Int)/10^30)
theorem v3032_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 88 5) 1) 14) v3032_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3032 : Material (38 : Basis) (88 : Basis) where
  plus := ![v3032_pa,v3032_pb,v3032_pg]
  minus := ![(Primitive.Addresses.material3032 1).one,v3032_mb,v3032_mg]
  upper := v3032_upper
  lower := (Primitive.Addresses.material3032 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3032_pa_checked.trans (by decide +kernel)
    · exact v3032_pb_checked.trans (by decide +kernel)
    · exact v3032_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 88 Primitive.Addresses.material3032
    · exact v3032_mb_checked.trans (by decide +kernel)
    · exact v3032_mg_checked.trans (by decide +kernel)
  upper_error := v3032_upper_checked
  lower_error := reuse_lower_error 38 88 Primitive.Addresses.material3032

def v3033_pa : Scalar.QComplex := ((999998563426912042908662358152 : Int)/10^30,(-1695035135969737245821285290 : Int)/10^30)
theorem v3033_pa_checked : Scalar.distance (sourceCoefficient 38 89 1 0) v3033_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3033_pb : Scalar.QComplex := ((-731369468834857281043839 : Int)/10^30,(-431476848266476688072696825 : Int)/10^30)
theorem v3033_pb_checked : Scalar.distance (sourceCoefficient 38 89 1 1) v3033_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3033_pg : Scalar.QComplex := ((-93086290466823997246138 : Int)/10^30,(157784759687690927248 : Int)/10^30)
theorem v3033_pg_checked : Scalar.distance (sourceCoefficient 38 89 1 2) v3033_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3033_mb : Scalar.QComplex := ((-1103714283570688972929256 : Int)/10^30,(-431476056469014665953159081 : Int)/10^30)
theorem v3033_mb_checked : Scalar.distance (sourceCoefficient 38 89 3 1) v3033_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3033_mg : Scalar.QComplex := ((-93086119645402554107350 : Int)/10^30,(238113977159191352234 : Int)/10^30)
theorem v3033_mg_checked : Scalar.distance (sourceCoefficient 38 89 3 2) v3033_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3033_upper : Scalar.QComplex := ((999994148569647604030793633407 : Int)/10^30,(-3420939412727850325252567054 : Int)/10^30)
theorem v3033_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 89 5) 1) 14) v3033_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3033 : Material (38 : Basis) (89 : Basis) where
  plus := ![v3033_pa,v3033_pb,v3033_pg]
  minus := ![(Primitive.Addresses.material3033 1).one,v3033_mb,v3033_mg]
  upper := v3033_upper
  lower := (Primitive.Addresses.material3033 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3033_pa_checked.trans (by decide +kernel)
    · exact v3033_pb_checked.trans (by decide +kernel)
    · exact v3033_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 89 Primitive.Addresses.material3033
    · exact v3033_mb_checked.trans (by decide +kernel)
    · exact v3033_mg_checked.trans (by decide +kernel)
  upper_error := v3033_upper_checked
  lower_error := reuse_lower_error 38 89 Primitive.Addresses.material3033

def v3034_pa : Scalar.QComplex := ((999998518668708648932510534613 : Int)/10^30,(-1721238039423873598208896343 : Int)/10^30)
theorem v3034_pa_checked : Scalar.distance (sourceCoefficient 38 90 1 0) v3034_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3034_pb : Scalar.QComplex := ((-742675425626756032853130 : Int)/10^30,(-431476825673103253921942403 : Int)/10^30)
theorem v3034_pb_checked : Scalar.distance (sourceCoefficient 38 90 1 1) v3034_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3034_pg : Scalar.QComplex := ((-93086285946500006786965 : Int)/10^30,(160223893664471056851 : Int)/10^30)
theorem v3034_pg_checked : Scalar.distance (sourceCoefficient 38 90 1 2) v3034_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3034_mb : Scalar.QComplex := ((-1115020216655799597456853 : Int)/10^30,(-431476024119118134330742510 : Int)/10^30)
theorem v3034_mb_checked : Scalar.distance (sourceCoefficient 38 90 3 1) v3034_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3034_mg : Scalar.QComplex := ((-93086113020217479326459 : Int)/10^30,(240553106326934412420 : Int)/10^30)
theorem v3034_mg_checked : Scalar.distance (sourceCoefficient 38 90 3 2) v3034_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3034_upper : Scalar.QComplex := ((999994058587676619133989100180 : Int)/10^30,(-3447142199907241366452867074 : Int)/10^30)
theorem v3034_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 90 5) 1) 14) v3034_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3034 : Material (38 : Basis) (90 : Basis) where
  plus := ![v3034_pa,v3034_pb,v3034_pg]
  minus := ![(Primitive.Addresses.material3034 1).one,v3034_mb,v3034_mg]
  upper := v3034_upper
  lower := (Primitive.Addresses.material3034 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3034_pa_checked.trans (by decide +kernel)
    · exact v3034_pb_checked.trans (by decide +kernel)
    · exact v3034_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 90 Primitive.Addresses.material3034
    · exact v3034_mb_checked.trans (by decide +kernel)
    · exact v3034_mg_checked.trans (by decide +kernel)
  upper_error := v3034_upper_checked
  lower_error := reuse_lower_error 38 90 Primitive.Addresses.material3034

def v3035_pa : Scalar.QComplex := ((999998493152447315921584204199 : Int)/10^30,(-1735999088357655158361237695 : Int)/10^30)
theorem v3035_pa_checked : Scalar.distance (sourceCoefficient 38 91 1 0) v3035_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3035_pb : Scalar.QComplex := ((-749044482314633543870134 : Int)/10^30,(-431476812771498765183181768 : Int)/10^30)
theorem v3035_pb_checked : Scalar.distance (sourceCoefficient 38 91 1 1) v3035_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3035_pg : Scalar.QComplex := ((-93086283367203022173345 : Int)/10^30,(161597946567537109088 : Int)/10^30)
theorem v3035_pg_checked : Scalar.distance (sourceCoefficient 38 91 1 2) v3035_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3035_mb : Scalar.QComplex := ((-1121389259838682616221180 : Int)/10^30,(-431476005721309379475461150 : Int)/10^30)
theorem v3035_mb_checked : Scalar.distance (sourceCoefficient 38 91 3 1) v3035_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3035_mg : Scalar.QComplex := ((-93086109255175684802457 : Int)/10^30,(241927156492560641029 : Int)/10^30)
theorem v3035_mg_checked : Scalar.distance (sourceCoefficient 38 91 3 2) v3035_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3035_upper : Scalar.QComplex := ((999994007595221941788699427633 : Int)/10^30,(-3461903182817422250717917354 : Int)/10^30)
theorem v3035_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 91 5) 1) 14) v3035_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3035 : Material (38 : Basis) (91 : Basis) where
  plus := ![v3035_pa,v3035_pb,v3035_pg]
  minus := ![(Primitive.Addresses.material3035 1).one,v3035_mb,v3035_mg]
  upper := v3035_upper
  lower := (Primitive.Addresses.material3035 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3035_pa_checked.trans (by decide +kernel)
    · exact v3035_pb_checked.trans (by decide +kernel)
    · exact v3035_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 91 Primitive.Addresses.material3035
    · exact v3035_mb_checked.trans (by decide +kernel)
    · exact v3035_mg_checked.trans (by decide +kernel)
  upper_error := v3035_upper_checked
  lower_error := reuse_lower_error 38 91 Primitive.Addresses.material3035

def v3036_pa : Scalar.QComplex := ((999998437166083262533076656391 : Int)/10^30,(-1767955143951645211455993556 : Int)/10^30)
theorem v3036_pa_checked : Scalar.distance (sourceCoefficient 38 92 1 0) v3036_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3036_pb : Scalar.QComplex := ((-762832792676991092713388 : Int)/10^30,(-431476784411501939227474246 : Int)/10^30)
theorem v3036_pb_checked : Scalar.distance (sourceCoefficient 38 92 1 1) v3036_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3036_pg : Scalar.QComplex := ((-93086277702242213533288 : Int)/10^30,(164572620694663842466 : Int)/10^30)
theorem v3036_pg_checked : Scalar.distance (sourceCoefficient 38 92 1 2) v3036_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3036_mb : Scalar.QComplex := ((-1135177540593622086286924 : Int)/10^30,(-431475965462632272974149350 : Int)/10^30)
theorem v3036_mb_checked : Scalar.distance (sourceCoefficient 38 92 3 1) v3036_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3036_mg : Scalar.QComplex := ((-93086101023207188125163 : Int)/10^30,(244901824623474210061 : Int)/10^30)
theorem v3036_mg_checked : Scalar.distance (sourceCoefficient 38 92 3 2) v3036_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3036_upper : Scalar.QComplex := ((999993896455688349003499044098 : Int)/10^30,(-3493859094189236005669221940 : Int)/10^30)
theorem v3036_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 92 5) 1) 14) v3036_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3036 : Material (38 : Basis) (92 : Basis) where
  plus := ![v3036_pa,v3036_pb,v3036_pg]
  minus := ![(Primitive.Addresses.material3036 1).one,v3036_mb,v3036_mg]
  upper := v3036_upper
  lower := (Primitive.Addresses.material3036 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3036_pa_checked.trans (by decide +kernel)
    · exact v3036_pb_checked.trans (by decide +kernel)
    · exact v3036_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 92 Primitive.Addresses.material3036
    · exact v3036_mb_checked.trans (by decide +kernel)
    · exact v3036_mg_checked.trans (by decide +kernel)
  upper_error := v3036_upper_checked
  lower_error := reuse_lower_error 38 92 Primitive.Addresses.material3036

def v3037_pa : Scalar.QComplex := ((999998369396128098718630184637 : Int)/10^30,(-1805880695099644637701377764 : Int)/10^30)
theorem v3037_pa_checked : Scalar.distance (sourceCoefficient 38 93 1 0) v3037_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3037_pb : Scalar.QComplex := ((-779196803755129722787262 : Int)/10^30,(-431476749991399737589185860 : Int)/10^30)
theorem v3037_pb_checked : Scalar.distance (sourceCoefficient 38 93 1 1) v3037_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3037_pg : Scalar.QComplex := ((-93086270835135346254723 : Int)/10^30,(168102973589347610155 : Int)/10^30)
theorem v3037_pg_checked : Scalar.distance (sourceCoefficient 38 93 1 2) v3037_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3037_mb : Scalar.QComplex := ((-1151541515875693543560181 : Int)/10^30,(-431475916921138334779296782 : Int)/10^30)
theorem v3037_mb_checked : Scalar.distance (sourceCoefficient 38 93 3 1) v3037_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3037_mg : Scalar.QComplex := ((-93086091109567330864210 : Int)/10^30,(248432170277642306512 : Int)/10^30)
theorem v3037_mg_checked : Scalar.distance (sourceCoefficient 38 93 3 2) v3037_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3037_upper : Scalar.QComplex := ((999993763229773418253258546307 : Int)/10^30,(-3531784471886787474720226927 : Int)/10^30)
theorem v3037_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 93 5) 1) 14) v3037_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3037 : Material (38 : Basis) (93 : Basis) where
  plus := ![v3037_pa,v3037_pb,v3037_pg]
  minus := ![(Primitive.Addresses.material3037 1).one,v3037_mb,v3037_mg]
  upper := v3037_upper
  lower := (Primitive.Addresses.material3037 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3037_pa_checked.trans (by decide +kernel)
    · exact v3037_pb_checked.trans (by decide +kernel)
    · exact v3037_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 93 Primitive.Addresses.material3037
    · exact v3037_mb_checked.trans (by decide +kernel)
    · exact v3037_mg_checked.trans (by decide +kernel)
  upper_error := v3037_upper_checked
  lower_error := reuse_lower_error 38 93 Primitive.Addresses.material3037

def v3038_pa : Scalar.QComplex := ((999998287491824233453380457934 : Int)/10^30,(-1850679177720666195267685373 : Int)/10^30)
theorem v3038_pa_checked : Scalar.distance (sourceCoefficient 38 94 1 0) v3038_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3038_pb : Scalar.QComplex := ((-798526327145191598584870 : Int)/10^30,(-431476708267614079238295889 : Int)/10^30)
theorem v3038_pb_checked : Scalar.distance (sourceCoefficient 38 94 1 1) v3038_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3038_pg : Scalar.QComplex := ((-93086262522326599977120 : Int)/10^30,(172273102801006470209 : Int)/10^30)
theorem v3038_pg_checked : Scalar.distance (sourceCoefficient 38 94 1 2) v3038_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3038_mb : Scalar.QComplex := ((-1170870996062742604769021 : Int)/10^30,(-431475858516860095893712381 : Int)/10^30)
theorem v3038_mb_checked : Scalar.distance (sourceCoefficient 38 94 3 1) v3038_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3038_mg : Scalar.QComplex := ((-93086079198127985811270 : Int)/10^30,(252602290762991923715 : Int)/10^30)
theorem v3038_mg_checked : Scalar.distance (sourceCoefficient 38 94 3 2) v3038_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3038_upper : Scalar.QComplex := ((999993604007474622540729194377 : Int)/10^30,(-3576582746426333396663502191 : Int)/10^30)
theorem v3038_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 94 5) 1) 14) v3038_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3038 : Material (38 : Basis) (94 : Basis) where
  plus := ![v3038_pa,v3038_pb,v3038_pg]
  minus := ![(Primitive.Addresses.material3038 1).one,v3038_mb,v3038_mg]
  upper := v3038_upper
  lower := (Primitive.Addresses.material3038 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3038_pa_checked.trans (by decide +kernel)
    · exact v3038_pb_checked.trans (by decide +kernel)
    · exact v3038_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 94 Primitive.Addresses.material3038
    · exact v3038_mb_checked.trans (by decide +kernel)
    · exact v3038_mg_checked.trans (by decide +kernel)
  upper_error := v3038_upper_checked
  lower_error := reuse_lower_error 38 94 Primitive.Addresses.material3038

def v3039_pa : Scalar.QComplex := ((999998204574338634654880047271 : Int)/10^30,(-1894953323746362030881927486 : Int)/10^30)
theorem v3039_pa_checked : Scalar.distance (sourceCoefficient 38 95 1 0) v3039_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3039_pb : Scalar.QComplex := ((-817629610155192235122154 : Int)/10^30,(-431476665897786269487546878 : Int)/10^30)
theorem v3039_pb_checked : Scalar.distance (sourceCoefficient 38 95 1 1) v3039_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3039_pg : Scalar.QComplex := ((-93086254092672946096534 : Int)/10^30,(176394423291083093361 : Int)/10^30)
theorem v3039_pg_checked : Scalar.distance (sourceCoefficient 38 95 1 2) v3039_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3039_mb : Scalar.QComplex := ((-1189974235396464779910800 : Int)/10^30,(-431475799661775204663670606 : Int)/10^30)
theorem v3039_mb_checked : Scalar.distance (sourceCoefficient 38 95 3 1) v3039_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3039_mg : Scalar.QComplex := ((-93086067211963505124300 : Int)/10^30,(256723602444101128969 : Int)/10^30)
theorem v3039_mg_checked : Scalar.distance (sourceCoefficient 38 95 3 2) v3039_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3039_upper : Scalar.QComplex := ((999993444676952998397969192900 : Int)/10^30,(-3620856683402831605539696254 : Int)/10^30)
theorem v3039_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 95 5) 1) 14) v3039_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3039 : Material (38 : Basis) (95 : Basis) where
  plus := ![v3039_pa,v3039_pb,v3039_pg]
  minus := ![(Primitive.Addresses.material3039 1).one,v3039_mb,v3039_mg]
  upper := v3039_upper
  lower := (Primitive.Addresses.material3039 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3039_pa_checked.trans (by decide +kernel)
    · exact v3039_pb_checked.trans (by decide +kernel)
    · exact v3039_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 95 Primitive.Addresses.material3039
    · exact v3039_mb_checked.trans (by decide +kernel)
    · exact v3039_mg_checked.trans (by decide +kernel)
  upper_error := v3039_upper_checked
  lower_error := reuse_lower_error 38 95 Primitive.Addresses.material3039

def v3040_pa : Scalar.QComplex := ((999998164053787519129046391475 : Int)/10^30,(-1916217381787162159328642146 : Int)/10^30)
theorem v3040_pa_checked : Scalar.distance (sourceCoefficient 38 96 1 0) v3040_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3040_pb : Scalar.QComplex := ((-826804565235488106019139 : Int)/10^30,(-431476645147462010385244946 : Int)/10^30)
theorem v3040_pb_checked : Scalar.distance (sourceCoefficient 38 96 1 1) v3040_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3040_pg : Scalar.QComplex := ((-93086249968391493575977 : Int)/10^30,(178373817679551428658 : Int)/10^30)
theorem v3040_pg_checked : Scalar.distance (sourceCoefficient 38 96 1 2) v3040_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3040_mb : Scalar.QComplex := ((-1199149169153910282558672 : Int)/10^30,(-431475770993885662197287369 : Int)/10^30)
theorem v3040_mb_checked : Scalar.distance (sourceCoefficient 38 96 3 1) v3040_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3040_mg : Scalar.QComplex := ((-93086061379555379627948 : Int)/10^30,(258702992536481327862 : Int)/10^30)
theorem v3040_mg_checked : Scalar.distance (sourceCoefficient 38 96 3 2) v3040_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3040_upper : Scalar.QComplex := ((999993367456627115328591586467 : Int)/10^30,(-3642120639838519904220914547 : Int)/10^30)
theorem v3040_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 96 5) 1) 14) v3040_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3040 : Material (38 : Basis) (96 : Basis) where
  plus := ![v3040_pa,v3040_pb,v3040_pg]
  minus := ![(Primitive.Addresses.material3040 1).one,v3040_mb,v3040_mg]
  upper := v3040_upper
  lower := (Primitive.Addresses.material3040 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3040_pa_checked.trans (by decide +kernel)
    · exact v3040_pb_checked.trans (by decide +kernel)
    · exact v3040_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 96 Primitive.Addresses.material3040
    · exact v3040_mb_checked.trans (by decide +kernel)
    · exact v3040_mg_checked.trans (by decide +kernel)
  upper_error := v3040_upper_checked
  lower_error := reuse_lower_error 38 96 Primitive.Addresses.material3040

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
