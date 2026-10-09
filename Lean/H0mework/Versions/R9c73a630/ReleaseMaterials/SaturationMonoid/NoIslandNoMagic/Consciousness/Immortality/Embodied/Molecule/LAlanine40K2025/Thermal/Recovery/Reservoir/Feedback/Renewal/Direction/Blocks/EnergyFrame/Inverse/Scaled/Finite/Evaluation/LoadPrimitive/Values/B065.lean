import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B043
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B044

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1041_pa : Scalar.QComplex := ((999999909609998166966730337106 : Int)/10^30,(-425182308540364962290523746 : Int)/10^30)
theorem v1041_pa_checked : Scalar.distance (sourceCoefficient 11 41 1 0) v1041_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1041_pb : Scalar.QComplex := ((-183456600391516048048250 : Int)/10^30,(-431477463017389470834850053 : Int)/10^30)
theorem v1041_pb_checked : Scalar.distance (sourceCoefficient 11 41 1 1) v1041_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1041_pg : Scalar.QComplex := ((-93086419435315818117326 : Int)/10^30,(39578702286783248035 : Int)/10^30)
theorem v1041_pg_checked : Scalar.distance (sourceCoefficient 11 41 1 2) v1041_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1041_mb : Scalar.QComplex := ((-555802149642699894735681 : Int)/10^30,(-431477144043826935920026679 : Int)/10^30)
theorem v1041_mb_checked : Scalar.distance (sourceCoefficient 11 41 3 1) v1041_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1041_mg : Scalar.QComplex := ((-93086350620350087901737 : Int)/10^30,(119908075065801043244 : Int)/10^30)
theorem v1041_mg_checked : Scalar.distance (sourceCoefficient 11 41 3 2) v1041_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1041_upper : Scalar.QComplex := ((999997686401508741002198334628 : Int)/10^30,(-2151090799984978980761665532 : Int)/10^30)
theorem v1041_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 41 5) 1) 14) v1041_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1041 : Material (11 : Basis) (41 : Basis) where
  plus := ![v1041_pa,v1041_pb,v1041_pg]
  minus := ![(Primitive.Addresses.material1041 1).one,v1041_mb,v1041_mg]
  upper := v1041_upper
  lower := (Primitive.Addresses.material1041 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1041_pa_checked.trans (by decide +kernel)
    · exact v1041_pb_checked.trans (by decide +kernel)
    · exact v1041_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 41 Primitive.Addresses.material1041
    · exact v1041_mb_checked.trans (by decide +kernel)
    · exact v1041_mg_checked.trans (by decide +kernel)
  upper_error := v1041_upper_checked
  lower_error := reuse_lower_error 11 41 Primitive.Addresses.material1041

def v1042_pa : Scalar.QComplex := ((999999904574063079526618561750 : Int)/10^30,(-436865957399792511832755699 : Int)/10^30)
theorem v1042_pa_checked : Scalar.distance (sourceCoefficient 11 42 1 0) v1042_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1042_pb : Scalar.QComplex := ((-188497831634391303183146 : Int)/10^30,(-431477459971337740268352156 : Int)/10^30)
theorem v1042_pb_checked : Scalar.distance (sourceCoefficient 11 42 1 1) v1042_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1042_pg : Scalar.QComplex := ((-93086418872351481225831 : Int)/10^30,(40666291382206900133 : Int)/10^30)
theorem v1042_pg_checked : Scalar.distance (sourceCoefficient 11 42 1 2) v1042_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1042_mb : Scalar.QComplex := ((-560843376379888908096902 : Int)/10^30,(-431477136647420825563192227 : Int)/10^30)
theorem v1042_mb_checked : Scalar.distance (sourceCoefficient 11 42 3 1) v1042_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1042_mg : Scalar.QComplex := ((-93086349118845554471498 : Int)/10^30,(120995663270452702073 : Int)/10^30)
theorem v1042_mg_checked : Scalar.distance (sourceCoefficient 11 42 3 2) v1042_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1042_upper : Scalar.QComplex := ((999997661200663154968676469502 : Int)/10^30,(-2162774422751416907532226065 : Int)/10^30)
theorem v1042_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 42 5) 1) 14) v1042_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1042 : Material (11 : Basis) (42 : Basis) where
  plus := ![v1042_pa,v1042_pb,v1042_pg]
  minus := ![(Primitive.Addresses.material1042 1).one,v1042_mb,v1042_mg]
  upper := v1042_upper
  lower := (Primitive.Addresses.material1042 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1042_pa_checked.trans (by decide +kernel)
    · exact v1042_pb_checked.trans (by decide +kernel)
    · exact v1042_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 42 Primitive.Addresses.material1042
    · exact v1042_mb_checked.trans (by decide +kernel)
    · exact v1042_mg_checked.trans (by decide +kernel)
  upper_error := v1042_upper_checked
  lower_error := reuse_lower_error 11 42 Primitive.Addresses.material1042

def v1043_pa : Scalar.QComplex := ((999999897692563232818240551837 : Int)/10^30,(-452343744366551289024871036 : Int)/10^30)
theorem v1043_pa_checked : Scalar.distance (sourceCoefficient 11 43 1 0) v1043_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1043_pb : Scalar.QComplex := ((-195176147941165528119681 : Int)/10^30,(-431477455815185313036070250 : Int)/10^30)
theorem v1043_pb_checked : Scalar.distance (sourceCoefficient 11 43 1 1) v1043_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1043_pg : Scalar.QComplex := ((-93086418103742747253671 : Int)/10^30,(42107063222583029348 : Int)/10^30)
theorem v1043_pg_checked : Scalar.distance (sourceCoefficient 11 43 1 2) v1043_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1043_mb : Scalar.QComplex := ((-567521686613448399343476 : Int)/10^30,(-431477126728183753311219621 : Int)/10^30)
theorem v1043_mb_checked : Scalar.distance (sourceCoefficient 11 43 3 1) v1043_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1043_mg : Scalar.QComplex := ((-93086347106915898397759 : Int)/10^30,(122436433911088908025 : Int)/10^30)
theorem v1043_mg_checked : Scalar.distance (sourceCoefficient 11 43 3 2) v1043_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1043_upper : Scalar.QComplex := ((999997627605917386685445477134 : Int)/10^30,(-2178252174788985695683017520 : Int)/10^30)
theorem v1043_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 43 5) 1) 14) v1043_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1043 : Material (11 : Basis) (43 : Basis) where
  plus := ![v1043_pa,v1043_pb,v1043_pg]
  minus := ![(Primitive.Addresses.material1043 1).one,v1043_mb,v1043_mg]
  upper := v1043_upper
  lower := (Primitive.Addresses.material1043 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1043_pa_checked.trans (by decide +kernel)
    · exact v1043_pb_checked.trans (by decide +kernel)
    · exact v1043_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 43 Primitive.Addresses.material1043
    · exact v1043_mb_checked.trans (by decide +kernel)
    · exact v1043_mg_checked.trans (by decide +kernel)
  upper_error := v1043_upper_checked
  lower_error := reuse_lower_error 11 43 Primitive.Addresses.material1043

def v1044_pa : Scalar.QComplex := ((999999895026592966748748614219 : Int)/10^30,(-458199523185136366421581643 : Int)/10^30)
theorem v1044_pa_checked : Scalar.distance (sourceCoefficient 11 44 1 0) v1044_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1044_pb : Scalar.QComplex := ((-197702784536243274808439 : Int)/10^30,(-431477454206835204438906079 : Int)/10^30)
theorem v1044_pb_checked : Scalar.distance (sourceCoefficient 11 44 1 1) v1044_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1044_pg : Scalar.QComplex := ((-93086417806168182571973 : Int)/10^30,(42652156731140858252 : Int)/10^30)
theorem v1044_pg_checked : Scalar.distance (sourceCoefficient 11 44 1 2) v1044_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1044_mb : Scalar.QComplex := ((-570048320879810162368448 : Int)/10^30,(-431477122939460657512165944 : Int)/10^30)
theorem v1044_mb_checked : Scalar.distance (sourceCoefficient 11 44 3 1) v1044_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1044_mg : Scalar.QComplex := ((-93086346338950296731548 : Int)/10^30,(122981526959890064629 : Int)/10^30)
theorem v1044_mg_checked : Scalar.distance (sourceCoefficient 11 44 3 2) v1044_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1044_upper : Scalar.QComplex := ((999997614833408082492318965672 : Int)/10^30,(-2184107940284853266594712612 : Int)/10^30)
theorem v1044_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 44 5) 1) 14) v1044_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1044 : Material (11 : Basis) (44 : Basis) where
  plus := ![v1044_pa,v1044_pb,v1044_pg]
  minus := ![(Primitive.Addresses.material1044 1).one,v1044_mb,v1044_mg]
  upper := v1044_upper
  lower := (Primitive.Addresses.material1044 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1044_pa_checked.trans (by decide +kernel)
    · exact v1044_pb_checked.trans (by decide +kernel)
    · exact v1044_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 44 Primitive.Addresses.material1044
    · exact v1044_mb_checked.trans (by decide +kernel)
    · exact v1044_mg_checked.trans (by decide +kernel)
  upper_error := v1044_upper_checked
  lower_error := reuse_lower_error 11 44 Primitive.Addresses.material1044

def v1045_pa : Scalar.QComplex := ((999999893687465828571195861111 : Int)/10^30,(-461112846319100815318356160 : Int)/10^30)
theorem v1045_pa_checked : Scalar.distance (sourceCoefficient 11 45 1 0) v1045_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1045_pb : Scalar.QComplex := ((-198959817811396471059282 : Int)/10^30,(-431477453399312224046641754 : Int)/10^30)
theorem v1045_pb_checked : Scalar.distance (sourceCoefficient 11 45 1 1) v1045_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1045_pg : Scalar.QComplex := ((-93086417656733892831899 : Int)/10^30,(42923347562635022662 : Int)/10^30)
theorem v1045_pg_checked : Scalar.distance (sourceCoefficient 11 45 1 2) v1045_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1045_mb : Scalar.QComplex := ((-571305352990056458427444 : Int)/10^30,(-431477121047174876017481777 : Int)/10^30)
theorem v1045_mb_checked : Scalar.distance (sourceCoefficient 11 45 3 1) v1045_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1045_mg : Scalar.QComplex := ((-93086345955490589034872 : Int)/10^30,(123252717561452426666 : Int)/10^30)
theorem v1045_mg_checked : Scalar.distance (sourceCoefficient 11 45 3 2) v1045_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1045_upper : Scalar.QComplex := ((999997608466151504174851868257 : Int)/10^30,(-2187021256768553174597142090 : Int)/10^30)
theorem v1045_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 45 5) 1) 14) v1045_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1045 : Material (11 : Basis) (45 : Basis) where
  plus := ![v1045_pa,v1045_pb,v1045_pg]
  minus := ![(Primitive.Addresses.material1045 1).one,v1045_mb,v1045_mg]
  upper := v1045_upper
  lower := (Primitive.Addresses.material1045 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1045_pa_checked.trans (by decide +kernel)
    · exact v1045_pb_checked.trans (by decide +kernel)
    · exact v1045_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 45 Primitive.Addresses.material1045
    · exact v1045_mb_checked.trans (by decide +kernel)
    · exact v1045_mg_checked.trans (by decide +kernel)
  upper_error := v1045_upper_checked
  lower_error := reuse_lower_error 11 45 Primitive.Addresses.material1045

def v1046_pa : Scalar.QComplex := ((999999886007808838042038064896 : Int)/10^30,(-477477087753638999642582202 : Int)/10^30)
theorem v1046_pa_checked : Scalar.distance (sourceCoefficient 11 46 1 0) v1046_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1046_pb : Scalar.QComplex := ((-206020619156092455880186 : Int)/10^30,(-431477448772683035306734468 : Int)/10^30)
theorem v1046_pb_checked : Scalar.distance (sourceCoefficient 11 46 1 1) v1046_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1046_pg : Scalar.QComplex := ((-93086416800226320174690 : Int)/10^30,(44446636269762936504 : Int)/10^30)
theorem v1046_pg_checked : Scalar.distance (sourceCoefficient 11 46 1 2) v1046_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1046_mb : Scalar.QComplex := ((-578366147713120793815999 : Int)/10^30,(-431477110327393856198035924 : Int)/10^30)
theorem v1046_mb_checked : Scalar.distance (sourceCoefficient 11 46 3 1) v1046_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1046_mg : Scalar.QComplex := ((-93086343784453787419767 : Int)/10^30,(124776004962262877576 : Int)/10^30)
theorem v1046_mg_checked : Scalar.distance (sourceCoefficient 11 46 3 2) v1046_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1046_upper : Scalar.QComplex := ((999997572543309787966013911496 : Int)/10^30,(-2203385460576084748394953556 : Int)/10^30)
theorem v1046_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 46 5) 1) 14) v1046_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1046 : Material (11 : Basis) (46 : Basis) where
  plus := ![v1046_pa,v1046_pb,v1046_pg]
  minus := ![(Primitive.Addresses.material1046 1).one,v1046_mb,v1046_mg]
  upper := v1046_upper
  lower := (Primitive.Addresses.material1046 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1046_pa_checked.trans (by decide +kernel)
    · exact v1046_pb_checked.trans (by decide +kernel)
    · exact v1046_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 46 Primitive.Addresses.material1046
    · exact v1046_mb_checked.trans (by decide +kernel)
    · exact v1046_mg_checked.trans (by decide +kernel)
  upper_error := v1046_upper_checked
  lower_error := reuse_lower_error 11 46 Primitive.Addresses.material1046

def v1047_pa : Scalar.QComplex := ((999999884119729587239037943959 : Int)/10^30,(-481415130004536576548246930 : Int)/10^30)
theorem v1047_pa_checked : Scalar.distance (sourceCoefficient 11 47 1 0) v1047_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1047_pb : Scalar.QComplex := ((-207719795618476320478987 : Int)/10^30,(-431477447636290125855551518 : Int)/10^30)
theorem v1047_pb_checked : Scalar.distance (sourceCoefficient 11 47 1 1) v1047_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1047_pg : Scalar.QComplex := ((-93086416589767037146034 : Int)/10^30,(44813214537186567146 : Int)/10^30)
theorem v1047_pg_checked : Scalar.distance (sourceCoefficient 11 47 1 2) v1047_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1047_mb : Scalar.QComplex := ((-580065322562167705648996 : Int)/10^30,(-431477107724688610907604122 : Int)/10^30)
theorem v1047_mb_checked : Scalar.distance (sourceCoefficient 11 47 3 1) v1047_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1047_mg : Scalar.QComplex := ((-93086343257654048040409 : Int)/10^30,(125142582911575783283 : Int)/10^30)
theorem v1047_mg_checked : Scalar.distance (sourceCoefficient 11 47 3 2) v1047_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1047_upper : Scalar.QComplex := ((999997563858529680588318318444 : Int)/10^30,(-2207323493703077485852637969 : Int)/10^30)
theorem v1047_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 47 5) 1) 14) v1047_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1047 : Material (11 : Basis) (47 : Basis) where
  plus := ![v1047_pa,v1047_pb,v1047_pg]
  minus := ![(Primitive.Addresses.material1047 1).one,v1047_mb,v1047_mg]
  upper := v1047_upper
  lower := (Primitive.Addresses.material1047 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1047_pa_checked.trans (by decide +kernel)
    · exact v1047_pb_checked.trans (by decide +kernel)
    · exact v1047_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 47 Primitive.Addresses.material1047
    · exact v1047_mb_checked.trans (by decide +kernel)
    · exact v1047_mg_checked.trans (by decide +kernel)
  upper_error := v1047_upper_checked
  lower_error := reuse_lower_error 11 47 Primitive.Addresses.material1047

def v1048_pa : Scalar.QComplex := ((999999870538021232269672590376 : Int)/10^30,(-508845694464497467229458778 : Int)/10^30)
theorem v1048_pa_checked : Scalar.distance (sourceCoefficient 11 48 1 0) v1048_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1048_pb : Scalar.QComplex := ((-219555465758586162037754 : Int)/10^30,(-431477439473195066201302651 : Int)/10^30)
theorem v1048_pb_checked : Scalar.distance (sourceCoefficient 11 48 1 1) v1048_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1048_pg : Scalar.QComplex := ((-93086415077082619310889 : Int)/10^30,(47366627657285917022 : Int)/10^30)
theorem v1048_pg_checked : Scalar.distance (sourceCoefficient 11 48 1 2) v1048_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1048_mb : Scalar.QComplex := ((-591900981250933252869612 : Int)/10^30,(-431477089347946318626962502 : Int)/10^30)
theorem v1048_mb_checked : Scalar.distance (sourceCoefficient 11 48 3 1) v1048_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1048_mg : Scalar.QComplex := ((-93086339541489672258942 : Int)/10^30,(127695993775544207986 : Int)/10^30)
theorem v1048_mg_checked : Scalar.distance (sourceCoefficient 11 48 3 2) v1048_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1048_upper : Scalar.QComplex := ((999997502934175777454488817244 : Int)/10^30,(-2234753993867638336152233256 : Int)/10^30)
theorem v1048_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 48 5) 1) 14) v1048_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1048 : Material (11 : Basis) (48 : Basis) where
  plus := ![v1048_pa,v1048_pb,v1048_pg]
  minus := ![(Primitive.Addresses.material1048 1).one,v1048_mb,v1048_mg]
  upper := v1048_upper
  lower := (Primitive.Addresses.material1048 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1048_pa_checked.trans (by decide +kernel)
    · exact v1048_pb_checked.trans (by decide +kernel)
    · exact v1048_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 48 Primitive.Addresses.material1048
    · exact v1048_mb_checked.trans (by decide +kernel)
    · exact v1048_mg_checked.trans (by decide +kernel)
  upper_error := v1048_upper_checked
  lower_error := reuse_lower_error 11 48 Primitive.Addresses.material1048

def v1049_pa : Scalar.QComplex := ((999999859081039233793371578199 : Int)/10^30,(-530884075551583816214183999 : Int)/10^30)
theorem v1049_pa_checked : Scalar.distance (sourceCoefficient 11 49 1 0) v1049_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1049_pb : Scalar.QComplex := ((-229064530207375334371873 : Int)/10^30,(-431477432601164049354366299 : Int)/10^30)
theorem v1049_pb_checked : Scalar.distance (sourceCoefficient 11 49 1 1) v1049_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1049_pg : Scalar.QComplex := ((-93086413802556081514468 : Int)/10^30,(49418101701929712208 : Int)/10^30)
theorem v1049_pg_checked : Scalar.distance (sourceCoefficient 11 49 1 2) v1049_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1049_mb : Scalar.QComplex := ((-601410036228809882453979 : Int)/10^30,(-431477074270023513610741320 : Int)/10^30)
theorem v1049_mb_checked : Scalar.distance (sourceCoefficient 11 49 3 1) v1049_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1049_mg : Scalar.QComplex := ((-93086336496633903460513 : Int)/10^30,(129747465956471459782 : Int)/10^30)
theorem v1049_mg_checked : Scalar.distance (sourceCoefficient 11 49 3 2) v1049_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1049_upper : Scalar.QComplex := ((999997453440964392810501163116 : Int)/10^30,(-2256792322357433305936020428 : Int)/10^30)
theorem v1049_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 49 5) 1) 14) v1049_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1049 : Material (11 : Basis) (49 : Basis) where
  plus := ![v1049_pa,v1049_pb,v1049_pg]
  minus := ![(Primitive.Addresses.material1049 1).one,v1049_mb,v1049_mg]
  upper := v1049_upper
  lower := (Primitive.Addresses.material1049 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1049_pa_checked.trans (by decide +kernel)
    · exact v1049_pb_checked.trans (by decide +kernel)
    · exact v1049_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 49 Primitive.Addresses.material1049
    · exact v1049_mb_checked.trans (by decide +kernel)
    · exact v1049_mg_checked.trans (by decide +kernel)
  upper_error := v1049_upper_checked
  lower_error := reuse_lower_error 11 49 Primitive.Addresses.material1049

def v1050_pa : Scalar.QComplex := ((999999857710547471708645482361 : Int)/10^30,(-533459356287144342587879173 : Int)/10^30)
theorem v1050_pa_checked : Scalar.distance (sourceCoefficient 11 50 1 0) v1050_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1050_pb : Scalar.QComplex := ((-230175705761312936998525 : Int)/10^30,(-431477431779903913463807588 : Int)/10^30)
theorem v1050_pb_checked : Scalar.distance (sourceCoefficient 11 50 1 1) v1050_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1050_pg : Scalar.QComplex := ((-93086413650180162753037 : Int)/10^30,(49657825370688741698 : Int)/10^30)
theorem v1050_pg_checked : Scalar.distance (sourceCoefficient 11 50 1 2) v1050_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1050_mb : Scalar.QComplex := ((-602521210660295534028006 : Int)/10^30,(-431477072489869225953887043 : Int)/10^30)
theorem v1050_mb_checked : Scalar.distance (sourceCoefficient 11 50 3 1) v1050_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1050_mg : Scalar.QComplex := ((-93086336137387312049805 : Int)/10^30,(129987189404476856346 : Int)/10^30)
theorem v1050_mg_checked : Scalar.distance (sourceCoefficient 11 50 3 2) v1050_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1050_upper : Scalar.QComplex := ((999997447625773749978127954485 : Int)/10^30,(-2259367596892071239101146803 : Int)/10^30)
theorem v1050_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 50 5) 1) 14) v1050_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1050 : Material (11 : Basis) (50 : Basis) where
  plus := ![v1050_pa,v1050_pb,v1050_pg]
  minus := ![(Primitive.Addresses.material1050 1).one,v1050_mb,v1050_mg]
  upper := v1050_upper
  lower := (Primitive.Addresses.material1050 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1050_pa_checked.trans (by decide +kernel)
    · exact v1050_pb_checked.trans (by decide +kernel)
    · exact v1050_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 50 Primitive.Addresses.material1050
    · exact v1050_mb_checked.trans (by decide +kernel)
    · exact v1050_mg_checked.trans (by decide +kernel)
  upper_error := v1050_upper_checked
  lower_error := reuse_lower_error 11 50 Primitive.Addresses.material1050

def v1051_pa : Scalar.QComplex := ((999999851619020045615437781904 : Int)/10^30,(-544758605156315004136818748 : Int)/10^30)
theorem v1051_pa_checked : Scalar.distance (sourceCoefficient 11 51 1 0) v1051_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1051_pb : Scalar.QComplex := ((-235051076782439667907914 : Int)/10^30,(-431477428131464136547074272 : Int)/10^30)
theorem v1051_pb_checked : Scalar.distance (sourceCoefficient 11 51 1 1) v1051_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1051_pg : Scalar.QComplex := ((-93086412973105936041431 : Int)/10^30,(50709632014578786714 : Int)/10^30)
theorem v1051_pg_checked : Scalar.distance (sourceCoefficient 11 51 1 2) v1051_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1051_mb : Scalar.QComplex := ((-607396576717659610457521 : Int)/10^30,(-431477064634205194845308100 : Int)/10^30)
theorem v1051_mb_checked : Scalar.distance (sourceCoefficient 11 51 3 1) v1051_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1051_mg : Scalar.QComplex := ((-93086334552651575379492 : Int)/10^30,(131038995072446654542 : Int)/10^30)
theorem v1051_mg_checked : Scalar.distance (sourceCoefficient 11 51 3 2) v1051_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1051_upper : Scalar.QComplex := ((999997422032776908160981552350 : Int)/10^30,(-2270666818418914294644905468 : Int)/10^30)
theorem v1051_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 51 5) 1) 14) v1051_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1051 : Material (11 : Basis) (51 : Basis) where
  plus := ![v1051_pa,v1051_pb,v1051_pg]
  minus := ![(Primitive.Addresses.material1051 1).one,v1051_mb,v1051_mg]
  upper := v1051_upper
  lower := (Primitive.Addresses.material1051 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1051_pa_checked.trans (by decide +kernel)
    · exact v1051_pb_checked.trans (by decide +kernel)
    · exact v1051_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 51 Primitive.Addresses.material1051
    · exact v1051_mb_checked.trans (by decide +kernel)
    · exact v1051_mg_checked.trans (by decide +kernel)
  upper_error := v1051_upper_checked
  lower_error := reuse_lower_error 11 51 Primitive.Addresses.material1051

def v1052_pa : Scalar.QComplex := ((999999838149338954328108549790 : Int)/10^30,(-568947533517553182458026519 : Int)/10^30)
theorem v1052_pa_checked : Scalar.distance (sourceCoefficient 11 52 1 0) v1052_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1052_pb : Scalar.QComplex := ((-245488053652091859800670 : Int)/10^30,(-431477420074120587629114180 : Int)/10^30)
theorem v1052_pb_checked : Scalar.distance (sourceCoefficient 11 52 1 1) v1052_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1052_pg : Scalar.QComplex := ((-93086411477042977075028 : Int)/10^30,(52961292785683903642 : Int)/10^30)
theorem v1052_pg_checked : Scalar.distance (sourceCoefficient 11 52 1 2) v1052_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1052_mb : Scalar.QComplex := ((-617833542748023726938030 : Int)/10^30,(-431477047570223671523362109 : Int)/10^30)
theorem v1052_mb_checked : Scalar.distance (sourceCoefficient 11 52 3 1) v1052_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1052_mg : Scalar.QComplex := ((-93086331113507339038562 : Int)/10^30,(133290653714120606993 : Int)/10^30)
theorem v1052_mg_checked : Scalar.distance (sourceCoefficient 11 52 3 2) v1052_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1052_upper : Scalar.QComplex := ((999997366815219929323482504762 : Int)/10^30,(-2294855687506137506388051983 : Int)/10^30)
theorem v1052_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 52 5) 1) 14) v1052_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1052 : Material (11 : Basis) (52 : Basis) where
  plus := ![v1052_pa,v1052_pb,v1052_pg]
  minus := ![(Primitive.Addresses.material1052 1).one,v1052_mb,v1052_mg]
  upper := v1052_upper
  lower := (Primitive.Addresses.material1052 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1052_pa_checked.trans (by decide +kernel)
    · exact v1052_pb_checked.trans (by decide +kernel)
    · exact v1052_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 52 Primitive.Addresses.material1052
    · exact v1052_mb_checked.trans (by decide +kernel)
    · exact v1052_mg_checked.trans (by decide +kernel)
  upper_error := v1052_upper_checked
  lower_error := reuse_lower_error 11 52 Primitive.Addresses.material1052

def v1053_pa : Scalar.QComplex := ((999999836035847725941866618505 : Int)/10^30,(-572650222792127302436460451 : Int)/10^30)
theorem v1053_pa_checked : Scalar.distance (sourceCoefficient 11 53 1 0) v1053_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1053_pb : Scalar.QComplex := ((-247085680525111706084339 : Int)/10^30,(-431477418811046083730676123 : Int)/10^30)
theorem v1053_pb_checked : Scalar.distance (sourceCoefficient 11 53 1 1) v1053_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1053_pg : Scalar.QComplex := ((-93086411242427230057441 : Int)/10^30,(53305962877162551249 : Int)/10^30)
theorem v1053_pg_checked : Scalar.distance (sourceCoefficient 11 53 1 2) v1053_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1053_mb : Scalar.QComplex := ((-619431167936197663140859 : Int)/10^30,(-431477044928469600952446192 : Int)/10^30)
theorem v1053_mb_checked : Scalar.distance (sourceCoefficient 11 53 3 1) v1053_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1053_mg : Scalar.QComplex := ((-93086330581456913797734 : Int)/10^30,(133635323474800004366 : Int)/10^30)
theorem v1053_mg_checked : Scalar.distance (sourceCoefficient 11 53 3 2) v1053_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1053_upper : Scalar.QComplex := ((999997358311226066166266843596 : Int)/10^30,(-2298558367618296774555825337 : Int)/10^30)
theorem v1053_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 53 5) 1) 14) v1053_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1053 : Material (11 : Basis) (53 : Basis) where
  plus := ![v1053_pa,v1053_pb,v1053_pg]
  minus := ![(Primitive.Addresses.material1053 1).one,v1053_mb,v1053_mg]
  upper := v1053_upper
  lower := (Primitive.Addresses.material1053 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1053_pa_checked.trans (by decide +kernel)
    · exact v1053_pb_checked.trans (by decide +kernel)
    · exact v1053_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 53 Primitive.Addresses.material1053
    · exact v1053_mb_checked.trans (by decide +kernel)
    · exact v1053_mg_checked.trans (by decide +kernel)
  upper_error := v1053_upper_checked
  lower_error := reuse_lower_error 11 53 Primitive.Addresses.material1053

def v1054_pa : Scalar.QComplex := ((999999834956079013714302649822 : Int)/10^30,(-574532692484140140051985540 : Int)/10^30)
theorem v1054_pa_checked : Scalar.distance (sourceCoefficient 11 54 1 0) v1054_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1054_pb : Scalar.QComplex := ((-247897923718986144423507 : Int)/10^30,(-431477418165867003130931650 : Int)/10^30)
theorem v1054_pb_checked : Scalar.distance (sourceCoefficient 11 54 1 1) v1054_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1054_pg : Scalar.QComplex := ((-93086411122576251873099 : Int)/10^30,(53481195242685505968 : Int)/10^30)
theorem v1054_pg_checked : Scalar.distance (sourceCoefficient 11 54 1 2) v1054_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1054_mb : Scalar.QComplex := ((-620243410270876350282317 : Int)/10^30,(-431477043582361466344180911 : Int)/10^30)
theorem v1054_mb_checked : Scalar.distance (sourceCoefficient 11 54 3 1) v1054_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1054_mg : Scalar.QComplex := ((-93086330310388340965850 : Int)/10^30,(133810555671649944600 : Int)/10^30)
theorem v1054_mg_checked : Scalar.distance (sourceCoefficient 11 54 3 2) v1054_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1054_upper : Scalar.QComplex := ((999997353982487050029631500801 : Int)/10^30,(-2300440832643009294889426407 : Int)/10^30)
theorem v1054_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 54 5) 1) 14) v1054_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1054 : Material (11 : Basis) (54 : Basis) where
  plus := ![v1054_pa,v1054_pb,v1054_pg]
  minus := ![(Primitive.Addresses.material1054 1).one,v1054_mb,v1054_mg]
  upper := v1054_upper
  lower := (Primitive.Addresses.material1054 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1054_pa_checked.trans (by decide +kernel)
    · exact v1054_pb_checked.trans (by decide +kernel)
    · exact v1054_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 54 Primitive.Addresses.material1054
    · exact v1054_mb_checked.trans (by decide +kernel)
    · exact v1054_mg_checked.trans (by decide +kernel)
  upper_error := v1054_upper_checked
  lower_error := reuse_lower_error 11 54 Primitive.Addresses.material1054

def v1055_pa : Scalar.QComplex := ((999999826022968524288787185665 : Int)/10^30,(-589876285913762551662080267 : Int)/10^30)
theorem v1055_pa_checked : Scalar.distance (sourceCoefficient 11 55 1 0) v1055_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1055_pb : Scalar.QComplex := ((-254518338016848799872287 : Int)/10^30,(-431477412831126095934091383 : Int)/10^30)
theorem v1055_pb_checked : Scalar.distance (sourceCoefficient 11 55 1 1) v1055_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1055_pg : Scalar.QComplex := ((-93086410131345347058225 : Int)/10^30,(54909475430310766275 : Int)/10^30)
theorem v1055_pg_checked : Scalar.distance (sourceCoefficient 11 55 1 2) v1055_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1055_mb : Scalar.QComplex := ((-626863817500015059656688 : Int)/10^30,(-431477032534503178851014726 : Int)/10^30)
theorem v1055_mb_checked : Scalar.distance (sourceCoefficient 11 55 3 1) v1055_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1055_mg : Scalar.QComplex := ((-93086328086616330662651 : Int)/10^30,(135238834472073587953 : Int)/10^30)
theorem v1055_mg_checked : Scalar.distance (sourceCoefficient 11 55 3 2) v1055_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1055_upper : Scalar.QComplex := ((999997318567739565817091870209 : Int)/10^30,(-2315784387802413378876450875 : Int)/10^30)
theorem v1055_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 55 5) 1) 14) v1055_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1055 : Material (11 : Basis) (55 : Basis) where
  plus := ![v1055_pa,v1055_pb,v1055_pg]
  minus := ![(Primitive.Addresses.material1055 1).one,v1055_mb,v1055_mg]
  upper := v1055_upper
  lower := (Primitive.Addresses.material1055 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1055_pa_checked.trans (by decide +kernel)
    · exact v1055_pb_checked.trans (by decide +kernel)
    · exact v1055_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 55 Primitive.Addresses.material1055
    · exact v1055_mb_checked.trans (by decide +kernel)
    · exact v1055_mg_checked.trans (by decide +kernel)
  upper_error := v1055_upper_checked
  lower_error := reuse_lower_error 11 55 Primitive.Addresses.material1055

def v1056_pa : Scalar.QComplex := ((999999823868325180566714822638 : Int)/10^30,(-593517749200897694312908012 : Int)/10^30)
theorem v1056_pa_checked : Scalar.distance (sourceCoefficient 11 56 1 0) v1056_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1056_pb : Scalar.QComplex := ((-256089547236791711533430 : Int)/10^30,(-431477411545156732691760385 : Int)/10^30)
theorem v1056_pb_checked : Scalar.distance (sourceCoefficient 11 56 1 1) v1056_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1056_pg : Scalar.QComplex := ((-93086409892344593848952 : Int)/10^30,(55248446211497903195 : Int)/10^30)
theorem v1056_pg_checked : Scalar.distance (sourceCoefficient 11 56 1 2) v1056_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1056_mb : Scalar.QComplex := ((-628435025025191328356330 : Int)/10^30,(-431477029892651502259476051 : Int)/10^30)
theorem v1056_mb_checked : Scalar.distance (sourceCoefficient 11 56 3 1) v1056_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1056_mg : Scalar.QComplex := ((-93086327555099148957041 : Int)/10^30,(135577804920799525482 : Int)/10^30)
theorem v1056_mg_checked : Scalar.distance (sourceCoefficient 11 56 3 2) v1056_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1056_upper : Scalar.QComplex := ((999997310128264148556770327752 : Int)/10^30,(-2319425841947297768118369113 : Int)/10^30)
theorem v1056_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 56 5) 1) 14) v1056_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1056 : Material (11 : Basis) (56 : Basis) where
  plus := ![v1056_pa,v1056_pb,v1056_pg]
  minus := ![(Primitive.Addresses.material1056 1).one,v1056_mb,v1056_mg]
  upper := v1056_upper
  lower := (Primitive.Addresses.material1056 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1056_pa_checked.trans (by decide +kernel)
    · exact v1056_pb_checked.trans (by decide +kernel)
    · exact v1056_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 56 Primitive.Addresses.material1056
    · exact v1056_mb_checked.trans (by decide +kernel)
    · exact v1056_mg_checked.trans (by decide +kernel)
  upper_error := v1056_upper_checked
  lower_error := reuse_lower_error 11 56 Primitive.Addresses.material1056

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
