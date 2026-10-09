import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B163
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B164

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3921_pa : Scalar.QComplex := ((999998222834806473152285319911 : Int)/10^30,(-1885292345695375263022812863 : Int)/10^30)
theorem v3921_pa_checked : Scalar.distance (sourceCoefficient 56 86 1 0) v3921_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3921_pb : Scalar.QComplex := ((-813461217288309100151255 : Int)/10^30,(-431476727463882641787246371 : Int)/10^30)
theorem v3921_pb_checked : Scalar.distance (sourceCoefficient 56 86 1 1) v3921_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3921_pg : Scalar.QComplex := ((-93086261583670884865880 : Int)/10^30,(175495128336925893781 : Int)/10^30)
theorem v3921_pg_checked : Scalar.distance (sourceCoefficient 56 86 1 2) v3921_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3921_mb : Scalar.QComplex := ((-1185805897210433149492114 : Int)/10^30,(-431475864824983959766543718 : Int)/10^30)
theorem v3921_mb_checked : Scalar.distance (sourceCoefficient 56 86 3 1) v3921_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3921_mg : Scalar.QComplex := ((-93086075479009697349218 : Int)/10^30,(255824314289186379767 : Int)/10^30)
theorem v3921_mg_checked : Scalar.distance (sourceCoefficient 56 86 3 2) v3921_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3921_upper : Scalar.QComplex := ((999993479611365318994280832285 : Int)/10^30,(-3611195751256647698968742886 : Int)/10^30)
theorem v3921_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 86 5) 1) 14) v3921_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3921 : Material (56 : Basis) (86 : Basis) where
  plus := ![v3921_pa,v3921_pb,v3921_pg]
  minus := ![(Primitive.Addresses.material3921 1).one,v3921_mb,v3921_mg]
  upper := v3921_upper
  lower := (Primitive.Addresses.material3921 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3921_pa_checked.trans (by decide +kernel)
    · exact v3921_pb_checked.trans (by decide +kernel)
    · exact v3921_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 86 Primitive.Addresses.material3921
    · exact v3921_mb_checked.trans (by decide +kernel)
    · exact v3921_mg_checked.trans (by decide +kernel)
  upper_error := v3921_upper_checked
  lower_error := reuse_lower_error 56 86 Primitive.Addresses.material3921

def v3922_pa : Scalar.QComplex := ((999998221013606906308470761653 : Int)/10^30,(-1886258100418602906410078450 : Int)/10^30)
theorem v3922_pa_checked : Scalar.distance (sourceCoefficient 56 87 1 0) v3922_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3922_pb : Scalar.QComplex := ((-813877918556505375251877 : Int)/10^30,(-431476726593325278238897048 : Int)/10^30)
theorem v3922_pb_checked : Scalar.distance (sourceCoefficient 56 87 1 1) v3922_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3922_pg : Scalar.QComplex := ((-93086261404999914284939 : Int)/10^30,(175585026976238470107 : Int)/10^30)
theorem v3922_pg_checked : Scalar.distance (sourceCoefficient 56 87 1 2) v3922_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3922_mb : Scalar.QComplex := ((-1186222597572220701960448 : Int)/10^30,(-431475863594832493441538026 : Int)/10^30)
theorem v3922_mb_checked : Scalar.distance (sourceCoefficient 56 87 3 1) v3922_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3922_mg : Scalar.QComplex := ((-93086075222760316453305 : Int)/10^30,(255914212740840583536 : Int)/10^30)
theorem v3922_mg_checked : Scalar.distance (sourceCoefficient 56 87 3 2) v3922_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3922_upper : Scalar.QComplex := ((999993476123363424906474735519 : Int)/10^30,(-3612161501398271893189005491 : Int)/10^30)
theorem v3922_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 87 5) 1) 14) v3922_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3922 : Material (56 : Basis) (87 : Basis) where
  plus := ![v3922_pa,v3922_pb,v3922_pg]
  minus := ![(Primitive.Addresses.material3922 1).one,v3922_mb,v3922_mg]
  upper := v3922_upper
  lower := (Primitive.Addresses.material3922 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3922_pa_checked.trans (by decide +kernel)
    · exact v3922_pb_checked.trans (by decide +kernel)
    · exact v3922_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 87 Primitive.Addresses.material3922
    · exact v3922_mb_checked.trans (by decide +kernel)
    · exact v3922_mg_checked.trans (by decide +kernel)
  upper_error := v3922_upper_checked
  lower_error := reuse_lower_error 56 87 Primitive.Addresses.material3922

def v3923_pa : Scalar.QComplex := ((999998198762834407947508096506 : Int)/10^30,(-1898017672923194430842889205 : Int)/10^30)
theorem v3923_pa_checked : Scalar.distance (sourceCoefficient 56 88 1 0) v3923_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3923_pb : Scalar.QComplex := ((-818951907454352983919493 : Int)/10^30,(-431476715949883707633112179 : Int)/10^30)
theorem v3923_pb_checked : Scalar.distance (sourceCoefficient 56 88 1 1) v3923_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3923_pg : Scalar.QComplex := ((-93086259221275927359228 : Int)/10^30,(176679683350303440219 : Int)/10^30)
theorem v3923_pg_checked : Scalar.distance (sourceCoefficient 56 88 1 2) v3923_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3923_mb : Scalar.QComplex := ((-1191296575395979638591797 : Int)/10^30,(-431475848572770991009743206 : Int)/10^30)
theorem v3923_mb_checked : Scalar.distance (sourceCoefficient 56 88 3 1) v3923_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3923_mg : Scalar.QComplex := ((-93086072094397993302696 : Int)/10^30,(257008866822859507876 : Int)/10^30)
theorem v3923_mg_checked : Scalar.distance (sourceCoefficient 56 88 3 2) v3923_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3923_upper : Scalar.QComplex := ((999993433576668743616493241389 : Int)/10^30,(-3623921017985546790597323665 : Int)/10^30)
theorem v3923_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 88 5) 1) 14) v3923_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3923 : Material (56 : Basis) (88 : Basis) where
  plus := ![v3923_pa,v3923_pb,v3923_pg]
  minus := ![(Primitive.Addresses.material3923 1).one,v3923_mb,v3923_mg]
  upper := v3923_upper
  lower := (Primitive.Addresses.material3923 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3923_pa_checked.trans (by decide +kernel)
    · exact v3923_pb_checked.trans (by decide +kernel)
    · exact v3923_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 88 Primitive.Addresses.material3923
    · exact v3923_mb_checked.trans (by decide +kernel)
    · exact v3923_mg_checked.trans (by decide +kernel)
  upper_error := v3923_upper_checked
  lower_error := reuse_lower_error 56 88 Primitive.Addresses.material3923

def v3924_pa : Scalar.QComplex := ((999998168095272905019471834549 : Int)/10^30,(-1914107128223243387698720681 : Int)/10^30)
theorem v3924_pa_checked : Scalar.distance (sourceCoefficient 56 89 1 0) v3924_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3924_pb : Scalar.QComplex := ((-825894142500776907775716 : Int)/10^30,(-431476701258629271477740641 : Int)/10^30)
theorem v3924_pb_checked : Scalar.distance (sourceCoefficient 56 89 1 1) v3924_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3924_pg : Scalar.QComplex := ((-93086256209172434877833 : Int)/10^30,(178177392953600520926 : Int)/10^30)
theorem v3924_pg_checked : Scalar.distance (sourceCoefficient 56 89 1 2) v3924_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3924_mb : Scalar.QComplex := ((-1198238795179601269984419 : Int)/10^30,(-431475827890685846675734401 : Int)/10^30)
theorem v3924_mb_checked : Scalar.distance (sourceCoefficient 56 89 3 1) v3924_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3924_mg : Scalar.QComplex := ((-93086067789839689056221 : Int)/10^30,(258506573269181200659 : Int)/10^30)
theorem v3924_mg_checked : Scalar.distance (sourceCoefficient 56 89 3 2) v3924_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3924_upper : Scalar.QComplex := ((999993375140212692517214832374 : Int)/10^30,(-3640010396392813063607923775 : Int)/10^30)
theorem v3924_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 89 5) 1) 14) v3924_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3924 : Material (56 : Basis) (89 : Basis) where
  plus := ![v3924_pa,v3924_pb,v3924_pg]
  minus := ![(Primitive.Addresses.material3924 1).one,v3924_mb,v3924_mg]
  upper := v3924_upper
  lower := (Primitive.Addresses.material3924 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3924_pa_checked.trans (by decide +kernel)
    · exact v3924_pb_checked.trans (by decide +kernel)
    · exact v3924_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 89 Primitive.Addresses.material3924
    · exact v3924_mb_checked.trans (by decide +kernel)
    · exact v3924_mg_checked.trans (by decide +kernel)
  upper_error := v3924_upper_checked
  lower_error := reuse_lower_error 56 89 Primitive.Addresses.material3924

def v3925_pa : Scalar.QComplex := ((999998117596739010352954203847 : Int)/10^30,(-1940310021243321081645810437 : Int)/10^30)
theorem v3925_pa_checked : Scalar.distance (sourceCoefficient 56 90 1 0) v3925_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3925_pb : Scalar.QComplex := ((-837200096291301343030474 : Int)/10^30,(-431476677014040227792194736 : Int)/10^30)
theorem v3925_pb_checked : Scalar.distance (sourceCoefficient 56 90 1 1) v3925_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3925_pg : Scalar.QComplex := ((-93086251243559399666006 : Int)/10^30,(180616526120989620992 : Int)/10^30)
theorem v3925_pg_checked : Scalar.distance (sourceCoefficient 56 90 1 2) v3925_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3925_mb : Scalar.QComplex := ((-1209544723838413992468170 : Int)/10^30,(-431475793889576910392420362 : Int)/10^30)
theorem v3925_mb_checked : Scalar.distance (sourceCoefficient 56 90 3 1) v3925_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3925_mg : Scalar.QComplex := ((-93086060719366433792142 : Int)/10^30,(260945701243269142135 : Int)/10^30)
theorem v3925_mg_checked : Scalar.distance (sourceCoefficient 56 90 3 2) v3925_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3925_upper : Scalar.QComplex := ((999993279417937764716692743266 : Int)/10^30,(-3666213163230871301195911022 : Int)/10^30)
theorem v3925_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 90 5) 1) 14) v3925_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3925 : Material (56 : Basis) (90 : Basis) where
  plus := ![v3925_pa,v3925_pb,v3925_pg]
  minus := ![(Primitive.Addresses.material3925 1).one,v3925_mb,v3925_mg]
  upper := v3925_upper
  lower := (Primitive.Addresses.material3925 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3925_pa_checked.trans (by decide +kernel)
    · exact v3925_pb_checked.trans (by decide +kernel)
    · exact v3925_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 90 Primitive.Addresses.material3925
    · exact v3925_mb_checked.trans (by decide +kernel)
    · exact v3925_mg_checked.trans (by decide +kernel)
  upper_error := v3925_upper_checked
  lower_error := reuse_lower_error 56 90 Primitive.Addresses.material3925

def v3926_pa : Scalar.QComplex := ((999998088846740646063079463702 : Int)/10^30,(-1955071064232984115671468624 : Int)/10^30)
theorem v3926_pa_checked : Scalar.distance (sourceCoefficient 56 91 1 0) v3926_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3926_pb : Scalar.QComplex := ((-843569151269343285096762 : Int)/10^30,(-431476663182245910142884217 : Int)/10^30)
theorem v3926_pb_checked : Scalar.distance (sourceCoefficient 56 91 1 1) v3926_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3926_pg : Scalar.QComplex := ((-93086248413414894907039 : Int)/10^30,(181990578562958380034 : Int)/10^30)
theorem v3926_pg_checked : Scalar.distance (sourceCoefficient 56 91 1 2) v3926_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3926_mb : Scalar.QComplex := ((-1215913764508750150776610 : Int)/10^30,(-431475774561580148489862067 : Int)/10^30)
theorem v3926_mb_checked : Scalar.distance (sourceCoefficient 56 91 3 1) v3926_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3926_mg : Scalar.QComplex := ((-93086056703477610430986 : Int)/10^30,(262319750731328137103 : Int)/10^30)
theorem v3926_mg_checked : Scalar.distance (sourceCoefficient 56 91 3 2) v3926_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3926_upper : Scalar.QComplex := ((999993225191761131373231189803 : Int)/10^30,(-3680974134615805758744969487 : Int)/10^30)
theorem v3926_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 91 5) 1) 14) v3926_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3926 : Material (56 : Basis) (91 : Basis) where
  plus := ![v3926_pa,v3926_pb,v3926_pg]
  minus := ![(Primitive.Addresses.material3926 1).one,v3926_mb,v3926_mg]
  upper := v3926_upper
  lower := (Primitive.Addresses.material3926 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3926_pa_checked.trans (by decide +kernel)
    · exact v3926_pb_checked.trans (by decide +kernel)
    · exact v3926_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 91 Primitive.Addresses.material3926
    · exact v3926_mb_checked.trans (by decide +kernel)
    · exact v3926_mg_checked.trans (by decide +kernel)
  upper_error := v3926_upper_checked
  lower_error := reuse_lower_error 56 91 Primitive.Addresses.material3926

def v3927_pa : Scalar.QComplex := ((999998025859689815802021487572 : Int)/10^30,(-1987027106795081359657932160 : Int)/10^30)
theorem v3927_pa_checked : Scalar.distance (sourceCoefficient 56 92 1 0) v3927_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3927_pb : Scalar.QComplex := ((-857357457883055231552060 : Int)/10^30,(-431476632808489910800416834 : Int)/10^30)
theorem v3927_pb_checked : Scalar.distance (sourceCoefficient 56 92 1 1) v3927_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3927_pg : Scalar.QComplex := ((-93086242205396658778412 : Int)/10^30,(184965251679174839717 : Int)/10^30)
theorem v3927_pg_checked : Scalar.distance (sourceCoefficient 56 92 1 2) v3927_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3927_mb : Scalar.QComplex := ((-1229702039777261943960067 : Int)/10^30,(-431475732289147853328686129 : Int)/10^30)
theorem v3927_mb_checked : Scalar.distance (sourceCoefficient 56 92 3 1) v3927_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3927_mg : Scalar.QComplex := ((-93086047928452760840259 : Int)/10^30,(265294417382697707325 : Int)/10^30)
theorem v3927_mg_checked : Scalar.distance (sourceCoefficient 56 92 3 2) v3927_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3927_upper : Scalar.QComplex := ((999993107051573680280820533723 : Int)/10^30,(-3712930020873195834522754901 : Int)/10^30)
theorem v3927_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 92 5) 1) 14) v3927_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3927 : Material (56 : Basis) (92 : Basis) where
  plus := ![v3927_pa,v3927_pb,v3927_pg]
  minus := ![(Primitive.Addresses.material3927 1).one,v3927_mb,v3927_mg]
  upper := v3927_upper
  lower := (Primitive.Addresses.material3927 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3927_pa_checked.trans (by decide +kernel)
    · exact v3927_pb_checked.trans (by decide +kernel)
    · exact v3927_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 92 Primitive.Addresses.material3927
    · exact v3927_mb_checked.trans (by decide +kernel)
    · exact v3927_mg_checked.trans (by decide +kernel)
  upper_error := v3927_upper_checked
  lower_error := reuse_lower_error 56 92 Primitive.Addresses.material3927

def v3928_pa : Scalar.QComplex := ((999997949781296752625260473729 : Int)/10^30,(-2024952642186482921626500443 : Int)/10^30)
theorem v3928_pa_checked : Scalar.distance (sourceCoefficient 56 93 1 0) v3928_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3928_pb : Scalar.QComplex := ((-873721464428782352542613 : Int)/10^30,(-431476595998451768104092867 : Int)/10^30)
theorem v3928_pb_checked : Scalar.distance (sourceCoefficient 56 93 1 1) v3928_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3928_pg : Scalar.QComplex := ((-93086234693787467611637 : Int)/10^30,(188495603351587457859 : Int)/10^30)
theorem v3928_pg_checked : Scalar.distance (sourceCoefficient 56 93 1 2) v3928_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3928_mb : Scalar.QComplex := ((-1246066008464516501359912 : Int)/10^30,(-431475681357722775225174408 : Int)/10^30)
theorem v3928_mb_checked : Scalar.distance (sourceCoefficient 56 93 3 1) v3928_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3928_mg : Scalar.QComplex := ((-93086037370311874433719 : Int)/10^30,(268824761258418631127 : Int)/10^30)
theorem v3928_mg_checked : Scalar.distance (sourceCoefficient 56 93 3 2) v3928_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3928_upper : Scalar.QComplex := ((999992965517260419069025269270 : Int)/10^30,(-3750855368474562828197578671 : Int)/10^30)
theorem v3928_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 93 5) 1) 14) v3928_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3928 : Material (56 : Basis) (93 : Basis) where
  plus := ![v3928_pa,v3928_pb,v3928_pg]
  minus := ![(Primitive.Addresses.material3928 1).one,v3928_mb,v3928_mg]
  upper := v3928_upper
  lower := (Primitive.Addresses.material3928 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3928_pa_checked.trans (by decide +kernel)
    · exact v3928_pb_checked.trans (by decide +kernel)
    · exact v3928_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 93 Primitive.Addresses.material3928
    · exact v3928_mb_checked.trans (by decide +kernel)
    · exact v3928_mg_checked.trans (by decide +kernel)
  upper_error := v3928_upper_checked
  lower_error := reuse_lower_error 56 93 Primitive.Addresses.material3928

def v3929_pa : Scalar.QComplex := ((999997858062886094195658919969 : Int)/10^30,(-2069751105789536413705659960 : Int)/10^30)
theorem v3929_pa_checked : Scalar.distance (sourceCoefficient 56 94 1 0) v3929_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3929_pb : Scalar.QComplex := ((-893050982348294210611811 : Int)/10^30,(-431476551451622034395238427 : Int)/10^30)
theorem v3929_pb_checked : Scalar.distance (sourceCoefficient 56 94 1 1) v3929_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3929_pg : Scalar.QComplex := ((-93086225619678620802384 : Int)/10^30,(192665731087984095040 : Int)/10^30)
theorem v3929_pg_checked : Scalar.distance (sourceCoefficient 56 94 1 2) v3929_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3929_mb : Scalar.QComplex := ((-1265395480744857689927510 : Int)/10^30,(-431475620130406232968235153 : Int)/10^30)
theorem v3929_mb_checked : Scalar.distance (sourceCoefficient 56 94 3 1) v3929_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3929_mg : Scalar.QComplex := ((-93086024697573985400804 : Int)/10^30,(272994879611538875691 : Int)/10^30)
theorem v3929_mg_checked : Scalar.distance (sourceCoefficient 56 94 3 2) v3929_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3929_upper : Scalar.QComplex := ((999992796480902270438950986842 : Int)/10^30,(-3795653607057911013494869524 : Int)/10^30)
theorem v3929_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 94 5) 1) 14) v3929_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3929 : Material (56 : Basis) (94 : Basis) where
  plus := ![v3929_pa,v3929_pb,v3929_pg]
  minus := ![(Primitive.Addresses.material3929 1).one,v3929_mb,v3929_mg]
  upper := v3929_upper
  lower := (Primitive.Addresses.material3929 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3929_pa_checked.trans (by decide +kernel)
    · exact v3929_pb_checked.trans (by decide +kernel)
    · exact v3929_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 94 Primitive.Addresses.material3929
    · exact v3929_mb_checked.trans (by decide +kernel)
    · exact v3929_mg_checked.trans (by decide +kernel)
  upper_error := v3929_upper_checked
  lower_error := reuse_lower_error 56 94 Primitive.Addresses.material3929

def v3930_pa : Scalar.QComplex := ((999997765446161375437874806026 : Int)/10^30,(-2114025232587886245786470509 : Int)/10^30)
theorem v3930_pa_checked : Scalar.distance (sourceCoefficient 56 95 1 0) v3930_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3930_pb : Scalar.QComplex := ((-912154259827516963158275 : Int)/10^30,(-431476506291792048206300678 : Int)/10^30)
theorem v3930_pb_checked : Scalar.distance (sourceCoefficient 56 95 1 1) v3930_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3930_pg : Scalar.QComplex := ((-93086216437635387607856 : Int)/10^30,(196787050086556632654 : Int)/10^30)
theorem v3930_pg_checked : Scalar.distance (sourceCoefficient 56 95 1 2) v3930_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3930_mb : Scalar.QComplex := ((-1284498712140157819207105 : Int)/10^30,(-431475558485324976957541221 : Int)/10^30)
theorem v3930_mb_checked : Scalar.distance (sourceCoefficient 56 95 3 1) v3930_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3930_mg : Scalar.QComplex := ((-93086011959021492649769 : Int)/10^30,(277116189151866230182 : Int)/10^30)
theorem v3930_mg_checked : Scalar.distance (sourceCoefficient 56 95 3 2) v3930_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3930_upper : Scalar.QComplex := ((999992627451189156869134694167 : Int)/10^30,(-3839927508067085042760675733 : Int)/10^30)
theorem v3930_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 95 5) 1) 14) v3930_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3930 : Material (56 : Basis) (95 : Basis) where
  plus := ![v3930_pa,v3930_pb,v3930_pg]
  minus := ![(Primitive.Addresses.material3930 1).one,v3930_mb,v3930_mg]
  upper := v3930_upper
  lower := (Primitive.Addresses.material3930 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3930_pa_checked.trans (by decide +kernel)
    · exact v3930_pb_checked.trans (by decide +kernel)
    · exact v3930_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 95 Primitive.Addresses.material3930
    · exact v3930_mb_checked.trans (by decide +kernel)
    · exact v3930_mg_checked.trans (by decide +kernel)
  upper_error := v3930_upper_checked
  lower_error := reuse_lower_error 56 95 Primitive.Addresses.material3930

def v3931_pa : Scalar.QComplex := ((999997720267244116871997977192 : Int)/10^30,(-2135289281241494397429517362 : Int)/10^30)
theorem v3931_pa_checked : Scalar.distance (sourceCoefficient 56 96 1 0) v3931_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3931_pb : Scalar.QComplex := ((-921329212207571550127392 : Int)/10^30,(-431476484201481070878751801 : Int)/10^30)
theorem v3931_pb_checked : Scalar.distance (sourceCoefficient 56 96 1 1) v3931_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3931_pg : Scalar.QComplex := ((-93086211951995060814305 : Int)/10^30,(198766443746841518662 : Int)/10^30)
theorem v3931_pg_checked : Scalar.distance (sourceCoefficient 56 96 1 2) v3931_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3931_mb : Scalar.QComplex := ((-1293673642041014856283422 : Int)/10^30,(-431475528477451545390820330 : Int)/10^30)
theorem v3931_mb_checked : Scalar.distance (sourceCoefficient 56 96 3 1) v3931_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3931_mg : Scalar.QComplex := ((-93086005765255255820367 : Int)/10^30,(279095578204226817424 : Int)/10^30)
theorem v3931_mg_checked : Scalar.distance (sourceCoefficient 56 96 3 2) v3931_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3931_upper : Scalar.QComplex := ((999992545572520270290626405588 : Int)/10^30,(-3861191447075677986546161967 : Int)/10^30)
theorem v3931_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 96 5) 1) 14) v3931_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3931 : Material (56 : Basis) (96 : Basis) where
  plus := ![v3931_pa,v3931_pb,v3931_pg]
  minus := ![(Primitive.Addresses.material3931 1).one,v3931_mb,v3931_mg]
  upper := v3931_upper
  lower := (Primitive.Addresses.material3931 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3931_pa_checked.trans (by decide +kernel)
    · exact v3931_pb_checked.trans (by decide +kernel)
    · exact v3931_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 96 Primitive.Addresses.material3931
    · exact v3931_mb_checked.trans (by decide +kernel)
    · exact v3931_mg_checked.trans (by decide +kernel)
  upper_error := v3931_upper_checked
  lower_error := reuse_lower_error 56 96 Primitive.Addresses.material3931

def v3932_pa : Scalar.QComplex := ((999997561368383689664632891316 : Int)/10^30,(-2208451331973722862609576687 : Int)/10^30)
theorem v3932_pa_checked : Scalar.distance (sourceCoefficient 56 97 1 0) v3932_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3932_pb : Scalar.QComplex := ((-952896967772901568602324 : Int)/10^30,(-431476406209329514063526997 : Int)/10^30)
theorem v3932_pb_checked : Scalar.distance (sourceCoefficient 56 97 1 1) v3932_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3932_pg : Scalar.QComplex := ((-93086196143365782689653 : Int)/10^30,(205576835187353255878 : Int)/10^30)
theorem v3932_pg_checked : Scalar.distance (sourceCoefficient 56 97 1 2) v3932_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3932_mb : Scalar.QComplex := ((-1325241318548512602664350 : Int)/10^30,(-431475423243777734670721627 : Int)/10^30)
theorem v3932_mb_checked : Scalar.distance (sourceCoefficient 56 97 3 1) v3932_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3932_mg : Scalar.QComplex := ((-93085984079570779453434 : Int)/10^30,(285905953466783498283 : Int)/10^30)
theorem v3932_mg_checked : Scalar.distance (sourceCoefficient 56 97 3 2) v3932_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3932_upper : Scalar.QComplex := ((999992260402834149839358665040 : Int)/10^30,(-3934353114596608198914574222 : Int)/10^30)
theorem v3932_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 97 5) 1) 14) v3932_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3932 : Material (56 : Basis) (97 : Basis) where
  plus := ![v3932_pa,v3932_pb,v3932_pg]
  minus := ![(Primitive.Addresses.material3932 1).one,v3932_mb,v3932_mg]
  upper := v3932_upper
  lower := (Primitive.Addresses.material3932 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3932_pa_checked.trans (by decide +kernel)
    · exact v3932_pb_checked.trans (by decide +kernel)
    · exact v3932_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 97 Primitive.Addresses.material3932
    · exact v3932_mb_checked.trans (by decide +kernel)
    · exact v3932_mg_checked.trans (by decide +kernel)
  upper_error := v3932_upper_checked
  lower_error := reuse_lower_error 56 97 Primitive.Addresses.material3932

def v3933_pa : Scalar.QComplex := ((999999147745936871680087957106 : Int)/10^30,(-1305567845774263737996703762 : Int)/10^30)
theorem v3933_pa_checked : Scalar.distance (sourceCoefficient 57 58 1 0) v3933_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3933_pb : Scalar.QComplex := ((-563323177589007482320019 : Int)/10^30,(-431477153269245394276575889 : Int)/10^30)
theorem v3933_pb_checked : Scalar.distance (sourceCoefficient 57 58 1 1) v3933_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3933_pg : Scalar.QComplex := ((-93086350563371151379040 : Int)/10^30,(121530649750998440698 : Int)/10^30)
theorem v3933_pg_checked : Scalar.distance (sourceCoefficient 57 58 1 2) v3933_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3933_mb : Scalar.QComplex := ((-935668318099806078635591 : Int)/10^30,(-431476506488050626854414307 : Int)/10^30)
theorem v3933_mb_checked : Scalar.distance (sourceCoefficient 57 58 3 1) v3933_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3933_mg : Scalar.QComplex := ((-93086211027591382416560 : Int)/10^30,(201859932582174435799 : Int)/10^30)
theorem v3933_mg_checked : Scalar.distance (sourceCoefficient 57 58 3 2) v3933_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3933_upper : Scalar.QComplex := ((999995405073012839074385347931 : Int)/10^30,(-3031473711079783368524930726 : Int)/10^30)
theorem v3933_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 58 5) 1) 14) v3933_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3933 : Material (57 : Basis) (58 : Basis) where
  plus := ![v3933_pa,v3933_pb,v3933_pg]
  minus := ![(Primitive.Addresses.material3933 1).one,v3933_mb,v3933_mg]
  upper := v3933_upper
  lower := (Primitive.Addresses.material3933 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3933_pa_checked.trans (by decide +kernel)
    · exact v3933_pb_checked.trans (by decide +kernel)
    · exact v3933_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 58 Primitive.Addresses.material3933
    · exact v3933_mb_checked.trans (by decide +kernel)
    · exact v3933_mg_checked.trans (by decide +kernel)
  upper_error := v3933_upper_checked
  lower_error := reuse_lower_error 57 58 Primitive.Addresses.material3933

def v3934_pa : Scalar.QComplex := ((999999124658146606347117167208 : Int)/10^30,(-1323133757623901553756909111 : Int)/10^30)
theorem v3934_pa_checked : Scalar.distance (sourceCoefficient 57 59 1 0) v3934_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3934_pb : Scalar.QComplex := ((-570902473637231427669652 : Int)/10^30,(-431477143269048033923216211 : Int)/10^30)
theorem v3934_pb_checked : Scalar.distance (sourceCoefficient 57 59 1 1) v3934_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3934_pg : Scalar.QComplex := ((-93086348410076024564983 : Int)/10^30,(123165797767489276947 : Int)/10^30)
theorem v3934_pg_checked : Scalar.distance (sourceCoefficient 57 59 1 2) v3934_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3934_mb : Scalar.QComplex := ((-943247602696191784474804 : Int)/10^30,(-431476489947265859236475531 : Int)/10^30)
theorem v3934_mb_checked : Scalar.distance (sourceCoefficient 57 59 3 1) v3934_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3934_mg : Scalar.QComplex := ((-93086207463237963473955 : Int)/10^30,(203495078131628221924 : Int)/10^30)
theorem v3934_mg_checked : Scalar.distance (sourceCoefficient 57 59 3 2) v3934_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3934_upper : Scalar.QComplex := ((999995351668086674892798706862 : Int)/10^30,(-3049039556919627431210773333 : Int)/10^30)
theorem v3934_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 59 5) 1) 14) v3934_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3934 : Material (57 : Basis) (59 : Basis) where
  plus := ![v3934_pa,v3934_pb,v3934_pg]
  minus := ![(Primitive.Addresses.material3934 1).one,v3934_mb,v3934_mg]
  upper := v3934_upper
  lower := (Primitive.Addresses.material3934 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3934_pa_checked.trans (by decide +kernel)
    · exact v3934_pb_checked.trans (by decide +kernel)
    · exact v3934_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 59 Primitive.Addresses.material3934
    · exact v3934_mb_checked.trans (by decide +kernel)
    · exact v3934_mg_checked.trans (by decide +kernel)
  upper_error := v3934_upper_checked
  lower_error := reuse_lower_error 57 59 Primitive.Addresses.material3934

def v3935_pa : Scalar.QComplex := ((999999097640943244492739394649 : Int)/10^30,(-1343397669813055471685826289 : Int)/10^30)
theorem v3935_pa_checked : Scalar.distance (sourceCoefficient 57 60 1 0) v3935_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3935_pb : Scalar.QComplex := ((-579645896100079616482697 : Int)/10^30,(-431477131512382218321865294 : Int)/10^30)
theorem v3935_pb_checked : Scalar.distance (sourceCoefficient 57 60 1 1) v3935_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3935_pg : Scalar.QComplex := ((-93086345884424206923917 : Int)/10^30,(125052092994436265611 : Int)/10^30)
theorem v3935_pg_checked : Scalar.distance (sourceCoefficient 57 60 1 2) v3935_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3935_mb : Scalar.QComplex := ((-951991011757991097930949 : Int)/10^30,(-431476470645424624870714048 : Int)/10^30)
theorem v3935_mb_checked : Scalar.distance (sourceCoefficient 57 60 3 1) v3935_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3935_mg : Scalar.QComplex := ((-93086203309799260976559 : Int)/10^30,(205381370476697522156 : Int)/10^30)
theorem v3935_mg_checked : Scalar.distance (sourceCoefficient 57 60 3 2) v3935_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3935_upper : Scalar.QComplex := ((999995289677249441263074125254 : Int)/10^30,(-3069303392298822488714597288 : Int)/10^30)
theorem v3935_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 60 5) 1) 14) v3935_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3935 : Material (57 : Basis) (60 : Basis) where
  plus := ![v3935_pa,v3935_pb,v3935_pg]
  minus := ![(Primitive.Addresses.material3935 1).one,v3935_mb,v3935_mg]
  upper := v3935_upper
  lower := (Primitive.Addresses.material3935 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3935_pa_checked.trans (by decide +kernel)
    · exact v3935_pb_checked.trans (by decide +kernel)
    · exact v3935_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 60 Primitive.Addresses.material3935
    · exact v3935_mb_checked.trans (by decide +kernel)
    · exact v3935_mg_checked.trans (by decide +kernel)
  upper_error := v3935_upper_checked
  lower_error := reuse_lower_error 57 60 Primitive.Addresses.material3935

def v3936_pa : Scalar.QComplex := ((999999089752359580086267145306 : Int)/10^30,(-1349257000088960285431502019 : Int)/10^30)
theorem v3936_pa_checked : Scalar.distance (sourceCoefficient 57 61 1 0) v3936_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3936_pb : Scalar.QComplex := ((-582174065347815102287443 : Int)/10^30,(-431477128068901237718172270 : Int)/10^30)
theorem v3936_pb_checked : Scalar.distance (sourceCoefficient 57 61 1 1) v3936_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3936_pg : Scalar.QComplex := ((-93086345145817985262650 : Int)/10^30,(125597517125535531294 : Int)/10^30)
theorem v3936_pg_checked : Scalar.distance (sourceCoefficient 57 61 1 2) v3936_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3936_mb : Scalar.QComplex := ((-954519177092804632126429 : Int)/10^30,(-431476465020248730152709195 : Int)/10^30)
theorem v3936_mb_checked : Scalar.distance (sourceCoefficient 57 61 3 1) v3936_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3936_mg : Scalar.QComplex := ((-93086202100516854184448 : Int)/10^30,(205926793767326553013 : Int)/10^30)
theorem v3936_mg_checked : Scalar.distance (sourceCoefficient 57 61 3 2) v3936_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3936_upper : Scalar.QComplex := ((999995271676005024053959191485 : Int)/10^30,(-3075162700232963383737803315 : Int)/10^30)
theorem v3936_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 61 5) 1) 14) v3936_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3936 : Material (57 : Basis) (61 : Basis) where
  plus := ![v3936_pa,v3936_pb,v3936_pg]
  minus := ![(Primitive.Addresses.material3936 1).one,v3936_mb,v3936_mg]
  upper := v3936_upper
  lower := (Primitive.Addresses.material3936 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3936_pa_checked.trans (by decide +kernel)
    · exact v3936_pb_checked.trans (by decide +kernel)
    · exact v3936_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 61 Primitive.Addresses.material3936
    · exact v3936_mb_checked.trans (by decide +kernel)
    · exact v3936_mg_checked.trans (by decide +kernel)
  upper_error := v3936_upper_checked
  lower_error := reuse_lower_error 57 61 Primitive.Addresses.material3936

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
