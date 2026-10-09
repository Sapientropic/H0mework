import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B156
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B157

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3761_pa : Scalar.QComplex := ((999997772429923998228465521813 : Int)/10^30,(-2110719116778710461494625153 : Int)/10^30)
theorem v3761_pa_checked : Scalar.distance (sourceCoefficient 52 96 1 0) v3761_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3761_pb : Scalar.QComplex := ((-910727733356551590733699 : Int)/10^30,(-431476503627169553476176853 : Int)/10^30)
theorem v3761_pb_checked : Scalar.distance (sourceCoefficient 52 96 1 1) v3761_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3761_pg : Scalar.QComplex := ((-93086216475250952568996 : Int)/10^30,(196479294294310061026 : Int)/10^30)
theorem v3761_pg_checked : Scalar.distance (sourceCoefficient 52 96 1 2) v3761_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3761_mb : Scalar.QComplex := ((-1283072183900904244593462 : Int)/10^30,(-431475557051731570464027070 : Int)/10^30)
theorem v3761_mb_checked : Scalar.distance (sourceCoefficient 52 96 3 1) v3761_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3761_mg : Scalar.QComplex := ((-93086012262216431507360 : Int)/10^30,(276808433506671743561 : Int)/10^30)
theorem v3761_mg_checked : Scalar.distance (sourceCoefficient 52 96 3 2) v3761_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3761_upper : Scalar.QComplex := ((999992640140997336319777145716 : Int)/10^30,(-3836621409235321117532691976 : Int)/10^30)
theorem v3761_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 96 5) 1) 14) v3761_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3761 : Material (52 : Basis) (96 : Basis) where
  plus := ![v3761_pa,v3761_pb,v3761_pg]
  minus := ![(Primitive.Addresses.material3761 1).one,v3761_mb,v3761_mg]
  upper := v3761_upper
  lower := (Primitive.Addresses.material3761 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3761_pa_checked.trans (by decide +kernel)
    · exact v3761_pb_checked.trans (by decide +kernel)
    · exact v3761_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 96 Primitive.Addresses.material3761
    · exact v3761_mb_checked.trans (by decide +kernel)
    · exact v3761_mg_checked.trans (by decide +kernel)
  upper_error := v3761_upper_checked
  lower_error := reuse_lower_error 52 96 Primitive.Addresses.material3761

def v3762_pa : Scalar.QComplex := ((999997615328671288819544347675 : Int)/10^30,(-2183881171393035050578607274 : Int)/10^30)
theorem v3762_pa_checked : Scalar.distance (sourceCoefficient 52 97 1 0) v3762_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3762_pb : Scalar.QComplex := ((-942295490038572984562552 : Int)/10^30,(-431476426152102831949200813 : Int)/10^30)
theorem v3762_pb_checked : Scalar.distance (sourceCoefficient 52 97 1 1) v3762_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3762_pg : Scalar.QComplex := ((-93086200806065738118448 : Int)/10^30,(203289686035963840368 : Int)/10^30)
theorem v3762_pg_checked : Scalar.distance (sourceCoefficient 52 97 1 2) v3762_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3762_mb : Scalar.QComplex := ((-1314639861971313874750369 : Int)/10^30,(-431475452335141438843497991 : Int)/10^30)
theorem v3762_mb_checked : Scalar.distance (sourceCoefficient 52 97 3 1) v3762_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3762_mg : Scalar.QComplex := ((-93085990715975707021115 : Int)/10^30,(283618809190704301040 : Int)/10^30)
theorem v3762_mg_checked : Scalar.distance (sourceCoefficient 52 97 3 2) v3762_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3762_upper : Scalar.QComplex := ((999992356768909556195690643069 : Int)/10^30,(-3909783083740849515100722104 : Int)/10^30)
theorem v3762_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 97 5) 1) 14) v3762_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3762 : Material (52 : Basis) (97 : Basis) where
  plus := ![v3762_pa,v3762_pb,v3762_pg]
  minus := ![(Primitive.Addresses.material3762 1).one,v3762_mb,v3762_mg]
  upper := v3762_upper
  lower := (Primitive.Addresses.material3762 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3762_pa_checked.trans (by decide +kernel)
    · exact v3762_pb_checked.trans (by decide +kernel)
    · exact v3762_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 97 Primitive.Addresses.material3762
    · exact v3762_mb_checked.trans (by decide +kernel)
    · exact v3762_mg_checked.trans (by decide +kernel)
  upper_error := v3762_upper_checked
  lower_error := reuse_lower_error 52 97 Primitive.Addresses.material3762

def v3763_pa : Scalar.QComplex := ((999999236437136971919289948994 : Int)/10^30,(-1235769049227207188861567771 : Int)/10^30)
theorem v3763_pa_checked : Scalar.distance (sourceCoefficient 53 54 1 0) v3763_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3763_pb : Scalar.QComplex := ((-533206565889573958410497 : Int)/10^30,(-431477191540186569803557467 : Int)/10^30)
theorem v3763_pb_checked : Scalar.distance (sourceCoefficient 53 54 1 1) v3763_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3763_pg : Scalar.QComplex := ((-93086358819607640018317 : Int)/10^30,(115033328969707197528 : Int)/10^30)
theorem v3763_pg_checked : Scalar.distance (sourceCoefficient 53 54 1 2) v3763_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3763_mb : Scalar.QComplex := ((-905551750640262062849710 : Int)/10^30,(-431476570748257047133119544 : Int)/10^30)
theorem v3763_mb_checked : Scalar.distance (sourceCoefficient 53 54 3 1) v3763_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3763_mg : Scalar.QComplex := ((-93086224890720002670897 : Int)/10^30,(195362621344892904341 : Int)/10^30)
theorem v3763_mg_checked : Scalar.distance (sourceCoefficient 53 54 3 2) v3763_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3763_upper : Scalar.QComplex := ((999995614230471587049923172102 : Int)/10^30,(-2961675171562800503821447094 : Int)/10^30)
theorem v3763_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 54 5) 1) 14) v3763_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3763 : Material (53 : Basis) (54 : Basis) where
  plus := ![v3763_pa,v3763_pb,v3763_pg]
  minus := ![(Primitive.Addresses.material3763 1).one,v3763_mb,v3763_mg]
  upper := v3763_upper
  lower := (Primitive.Addresses.material3763 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3763_pa_checked.trans (by decide +kernel)
    · exact v3763_pb_checked.trans (by decide +kernel)
    · exact v3763_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 54 Primitive.Addresses.material3763
    · exact v3763_mb_checked.trans (by decide +kernel)
    · exact v3763_mg_checked.trans (by decide +kernel)
  upper_error := v3763_upper_checked
  lower_error := reuse_lower_error 53 54 Primitive.Addresses.material3763

def v3764_pa : Scalar.QComplex := ((999999217358283014984155759085 : Int)/10^30,(-1251112633395560642569150458 : Int)/10^30)
theorem v3764_pa_checked : Scalar.distance (sourceCoefficient 53 55 1 0) v3764_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3764_pb : Scalar.QComplex := ((-539826977523417082849389 : Int)/10^30,(-431477183287005565082286180 : Int)/10^30)
theorem v3764_pb_checked : Scalar.distance (sourceCoefficient 53 55 1 1) v3764_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3764_pg : Scalar.QComplex := ((-93086357041350877843509 : Int)/10^30,(116461608438917077332 : Int)/10^30)
theorem v3764_pg_checked : Scalar.distance (sourceCoefficient 53 55 1 2) v3764_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3764_mb : Scalar.QComplex := ((-912172152686899870649481 : Int)/10^30,(-431476556781962047713022226 : Int)/10^30)
theorem v3764_mb_checked : Scalar.distance (sourceCoefficient 53 55 3 1) v3764_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3764_mg : Scalar.QComplex := ((-93086221879923048013577 : Int)/10^30,(196790898747733566116 : Int)/10^30)
theorem v3764_mg_checked : Scalar.distance (sourceCoefficient 53 55 3 2) v3764_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3764_upper : Scalar.QComplex := ((999995568670011730330902507032 : Int)/10^30,(-2977018699950316613214053061 : Int)/10^30)
theorem v3764_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 55 5) 1) 14) v3764_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3764 : Material (53 : Basis) (55 : Basis) where
  plus := ![v3764_pa,v3764_pb,v3764_pg]
  minus := ![(Primitive.Addresses.material3764 1).one,v3764_mb,v3764_mg]
  upper := v3764_upper
  lower := (Primitive.Addresses.material3764 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3764_pa_checked.trans (by decide +kernel)
    · exact v3764_pb_checked.trans (by decide +kernel)
    · exact v3764_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 55 Primitive.Addresses.material3764
    · exact v3764_mb_checked.trans (by decide +kernel)
    · exact v3764_mg_checked.trans (by decide +kernel)
  upper_error := v3764_upper_checked
  lower_error := reuse_lower_error 53 55 Primitive.Addresses.material3764

def v3765_pa : Scalar.QComplex := ((999999212795771370323459004355 : Int)/10^30,(-1254754094461881207989866417 : Int)/10^30)
theorem v3765_pa_checked : Scalar.distance (sourceCoefficient 53 56 1 0) v3765_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3765_pb : Scalar.QComplex := ((-541398186104538961258117 : Int)/10^30,(-431477181308408853540404405 : Int)/10^30)
theorem v3765_pb_checked : Scalar.distance (sourceCoefficient 53 56 1 1) v3765_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3765_pg : Scalar.QComplex := ((-93086356615566906698338 : Int)/10^30,(116800579047831131999 : Int)/10^30)
theorem v3765_pg_checked : Scalar.distance (sourceCoefficient 53 56 1 2) v3765_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3765_mb : Scalar.QComplex := ((-913743358975549137154225 : Int)/10^30,(-431476553447483831992529444 : Int)/10^30)
theorem v3765_mb_checked : Scalar.distance (sourceCoefficient 53 56 3 1) v3765_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3765_mg : Scalar.QComplex := ((-93086221161622866583908 : Int)/10^30,(197129868863000980862 : Int)/10^30)
theorem v3765_mg_checked : Scalar.distance (sourceCoefficient 53 56 3 2) v3765_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3765_upper : Scalar.QComplex := ((999995557822675431293432315860 : Int)/10^30,(-2980660147718627485554132078 : Int)/10^30)
theorem v3765_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 56 5) 1) 14) v3765_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3765 : Material (53 : Basis) (56 : Basis) where
  plus := ![v3765_pa,v3765_pb,v3765_pg]
  minus := ![(Primitive.Addresses.material3765 1).one,v3765_mb,v3765_mg]
  upper := v3765_upper
  lower := (Primitive.Addresses.material3765 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3765_pa_checked.trans (by decide +kernel)
    · exact v3765_pb_checked.trans (by decide +kernel)
    · exact v3765_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 56 Primitive.Addresses.material3765
    · exact v3765_mb_checked.trans (by decide +kernel)
    · exact v3765_mg_checked.trans (by decide +kernel)
  upper_error := v3765_upper_checked
  lower_error := reuse_lower_error 53 56 Primitive.Addresses.material3765

def v3766_pa : Scalar.QComplex := ((999999197948098990744307246053 : Int)/10^30,(-1266531941457166516789014478 : Int)/10^30)
theorem v3766_pa_checked : Scalar.distance (sourceCoefficient 53 57 1 0) v3766_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3766_pb : Scalar.QComplex := ((-546480062271016065915318 : Int)/10^30,(-431477174856647646667819002 : Int)/10^30)
theorem v3766_pb_checked : Scalar.distance (sourceCoefficient 53 57 1 1) v3766_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3766_pg : Scalar.QComplex := ((-93086355228560984397220 : Int)/10^30,(117896936770263066743 : Int)/10^30)
theorem v3766_pg_checked : Scalar.distance (sourceCoefficient 53 57 1 2) v3766_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3766_mb : Scalar.QComplex := ((-918825227682232146824659 : Int)/10^30,(-431476542610294774941902715 : Int)/10^30)
theorem v3766_mb_checked : Scalar.distance (sourceCoefficient 53 57 3 1) v3766_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3766_mg : Scalar.QComplex := ((-93086218828510124388541 : Int)/10^30,(198226224980285187004 : Int)/10^30)
theorem v3766_mg_checked : Scalar.distance (sourceCoefficient 53 57 3 2) v3766_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3766_upper : Scalar.QComplex := ((999995522647529729648637550479 : Int)/10^30,(-2992437951546457661133780406 : Int)/10^30)
theorem v3766_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 57 5) 1) 14) v3766_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3766 : Material (53 : Basis) (57 : Basis) where
  plus := ![v3766_pa,v3766_pb,v3766_pg]
  minus := ![(Primitive.Addresses.material3766 1).one,v3766_mb,v3766_mg]
  upper := v3766_upper
  lower := (Primitive.Addresses.material3766 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3766_pa_checked.trans (by decide +kernel)
    · exact v3766_pb_checked.trans (by decide +kernel)
    · exact v3766_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 57 Primitive.Addresses.material3766
    · exact v3766_mb_checked.trans (by decide +kernel)
    · exact v3766_mg_checked.trans (by decide +kernel)
  upper_error := v3766_upper_checked
  lower_error := reuse_lower_error 53 57 Primitive.Addresses.material3766

def v3767_pa : Scalar.QComplex := ((999999189833843374677384673859 : Int)/10^30,(-1272922486595882196259054310 : Int)/10^30)
theorem v3767_pa_checked : Scalar.distance (sourceCoefficient 53 58 1 0) v3767_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3767_pb : Scalar.QComplex := ((-549237438802889381694346 : Int)/10^30,(-431477171322586682264229691 : Int)/10^30)
theorem v3767_pb_checked : Scalar.distance (sourceCoefficient 53 58 1 1) v3767_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3767_pg : Scalar.QComplex := ((-93086354469680457404992 : Int)/10^30,(118491809797745496227 : Int)/10^30)
theorem v3767_pg_checked : Scalar.distance (sourceCoefficient 53 58 1 2) v3767_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3767_mb : Scalar.QComplex := ((-921582600137672717371252 : Int)/10^30,(-431476536696743367052987590 : Int)/10^30)
theorem v3767_mb_checked : Scalar.distance (sourceCoefficient 53 58 3 1) v3767_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3767_mg : Scalar.QComplex := ((-93086217556281249331468 : Int)/10^30,(198821097131389485231 : Int)/10^30)
theorem v3767_mg_checked : Scalar.distance (sourceCoefficient 53 58 3 2) v3767_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3767_upper : Scalar.QComplex := ((999995503503785035115284125706 : Int)/10^30,(-2998828473162737968839367274 : Int)/10^30)
theorem v3767_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 58 5) 1) 14) v3767_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3767 : Material (53 : Basis) (58 : Basis) where
  plus := ![v3767_pa,v3767_pb,v3767_pg]
  minus := ![(Primitive.Addresses.material3767 1).one,v3767_mb,v3767_mg]
  upper := v3767_upper
  lower := (Primitive.Addresses.material3767 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3767_pa_checked.trans (by decide +kernel)
    · exact v3767_pb_checked.trans (by decide +kernel)
    · exact v3767_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 58 Primitive.Addresses.material3767
    · exact v3767_mb_checked.trans (by decide +kernel)
    · exact v3767_mg_checked.trans (by decide +kernel)
  upper_error := v3767_upper_checked
  lower_error := reuse_lower_error 53 58 Primitive.Addresses.material3767

def v3768_pa : Scalar.QComplex := ((999999167319499099775514381244 : Int)/10^30,(-1290488399189869661413636217 : Int)/10^30)
theorem v3768_pa_checked : Scalar.distance (sourceCoefficient 53 59 1 0) v3768_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3768_pb : Scalar.QComplex := ((-556816735065226753343876 : Int)/10^30,(-431477161487342023788277002 : Int)/10^30)
theorem v3768_pb_checked : Scalar.distance (sourceCoefficient 53 59 1 1) v3768_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3768_pg : Scalar.QComplex := ((-93086352360868697217016 : Int)/10^30,(120126957871977041984 : Int)/10^30)
theorem v3768_pg_checked : Scalar.distance (sourceCoefficient 53 59 1 2) v3768_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3768_mb : Scalar.QComplex := ((-929161885090518522312441 : Int)/10^30,(-431476520320911055122782597 : Int)/10^30)
theorem v3768_mb_checked : Scalar.distance (sourceCoefficient 53 59 3 1) v3768_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3768_mg : Scalar.QComplex := ((-93086214036411130624121 : Int)/10^30,(200456242776971101307 : Int)/10^30)
theorem v3768_mg_checked : Scalar.distance (sourceCoefficient 53 59 3 2) v3768_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3768_upper : Scalar.QComplex := ((999995450672302722604388950742 : Int)/10^30,(-3016394320736646329168427026 : Int)/10^30)
theorem v3768_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 59 5) 1) 14) v3768_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3768 : Material (53 : Basis) (59 : Basis) where
  plus := ![v3768_pa,v3768_pb,v3768_pg]
  minus := ![(Primitive.Addresses.material3768 1).one,v3768_mb,v3768_mg]
  upper := v3768_upper
  lower := (Primitive.Addresses.material3768 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3768_pa_checked.trans (by decide +kernel)
    · exact v3768_pb_checked.trans (by decide +kernel)
    · exact v3768_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 59 Primitive.Addresses.material3768
    · exact v3768_mb_checked.trans (by decide +kernel)
    · exact v3768_mg_checked.trans (by decide +kernel)
  upper_error := v3768_upper_checked
  lower_error := reuse_lower_error 53 59 Primitive.Addresses.material3768

def v3769_pa : Scalar.QComplex := ((999999140963818993780210421252 : Int)/10^30,(-1310752312250212779080751362 : Int)/10^30)
theorem v3769_pa_checked : Scalar.distance (sourceCoefficient 53 60 1 0) v3769_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3769_pb : Scalar.QComplex := ((-565560157778673978018821 : Int)/10^30,(-431477149920964483303579334 : Int)/10^30)
theorem v3769_pb_checked : Scalar.distance (sourceCoefficient 53 60 1 1) v3769_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3769_pg : Scalar.QComplex := ((-93086349886532578020688 : Int)/10^30,(122013253166503940902 : Int)/10^30)
theorem v3769_pg_checked : Scalar.distance (sourceCoefficient 53 60 1 2) v3769_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3769_mb : Scalar.QComplex := ((-937905294567126989480915 : Int)/10^30,(-431476501209357808764971547 : Int)/10^30)
theorem v3769_mb_checked : Scalar.distance (sourceCoefficient 53 60 3 1) v3769_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3769_mg : Scalar.QComplex := ((-93086209934288049145865 : Int)/10^30,(202342535233903423215 : Int)/10^30)
theorem v3769_mg_checked : Scalar.distance (sourceCoefficient 53 60 3 2) v3769_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3769_upper : Scalar.QComplex := ((999995389342986255979031478624 : Int)/10^30,(-3036658158128758415568258087 : Int)/10^30)
theorem v3769_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 60 5) 1) 14) v3769_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3769 : Material (53 : Basis) (60 : Basis) where
  plus := ![v3769_pa,v3769_pb,v3769_pg]
  minus := ![(Primitive.Addresses.material3769 1).one,v3769_mb,v3769_mg]
  upper := v3769_upper
  lower := (Primitive.Addresses.material3769 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3769_pa_checked.trans (by decide +kernel)
    · exact v3769_pb_checked.trans (by decide +kernel)
    · exact v3769_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 60 Primitive.Addresses.material3769
    · exact v3769_mb_checked.trans (by decide +kernel)
    · exact v3769_mg_checked.trans (by decide +kernel)
  upper_error := v3769_upper_checked
  lower_error := reuse_lower_error 53 60 Primitive.Addresses.material3769

def v3770_pa : Scalar.QComplex := ((999999133266515433921922295982 : Int)/10^30,(-1316611642780521247564252503 : Int)/10^30)
theorem v3770_pa_checked : Scalar.distance (sourceCoefficient 53 61 1 0) v3770_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3770_pb : Scalar.QComplex := ((-568088327099589102192526 : Int)/10^30,(-431477146532505545887225064 : Int)/10^30)
theorem v3770_pb_checked : Scalar.distance (sourceCoefficient 53 61 1 1) v3770_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3770_pg : Scalar.QComplex := ((-93086349162764341382138 : Int)/10^30,(122558677317337813212 : Int)/10^30)
theorem v3770_pg_checked : Scalar.distance (sourceCoefficient 53 61 1 2) v3770_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3770_mb : Scalar.QComplex := ((-940433460022601679967070 : Int)/10^30,(-431476495639203873596352112 : Int)/10^30)
theorem v3770_mb_checked : Scalar.distance (sourceCoefficient 53 61 3 1) v3770_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3770_mg : Scalar.QComplex := ((-93086208739843604821534 : Int)/10^30,(202887958557071566146 : Int)/10^30)
theorem v3770_mg_checked : Scalar.distance (sourceCoefficient 53 61 3 2) v3770_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3770_upper : Scalar.QComplex := ((999995371533021219351225525658 : Int)/10^30,(-3042517466647434694079563932 : Int)/10^30)
theorem v3770_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 61 5) 1) 14) v3770_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3770 : Material (53 : Basis) (61 : Basis) where
  plus := ![v3770_pa,v3770_pb,v3770_pg]
  minus := ![(Primitive.Addresses.material3770 1).one,v3770_mb,v3770_mg]
  upper := v3770_upper
  lower := (Primitive.Addresses.material3770 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3770_pa_checked.trans (by decide +kernel)
    · exact v3770_pb_checked.trans (by decide +kernel)
    · exact v3770_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 61 Primitive.Addresses.material3770
    · exact v3770_mb_checked.trans (by decide +kernel)
    · exact v3770_mg_checked.trans (by decide +kernel)
  upper_error := v3770_upper_checked
  lower_error := reuse_lower_error 53 61 Primitive.Addresses.material3770

def v3771_pa : Scalar.QComplex := ((999999122021483623772524432958 : Int)/10^30,(-1325124998596803973573658383 : Int)/10^30)
theorem v3771_pa_checked : Scalar.distance (sourceCoefficient 53 62 1 0) v3771_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3771_pb : Scalar.QComplex := ((-571761648617274250572458 : Int)/10^30,(-431477141574023044846775553 : Int)/10^30)
theorem v3771_pb_checked : Scalar.distance (sourceCoefficient 53 62 1 1) v3771_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3771_pg : Scalar.QComplex := ((-93086348104515949580797 : Int)/10^30,(123351155201042540619 : Int)/10^30)
theorem v3771_pg_checked : Scalar.distance (sourceCoefficient 53 62 1 2) v3771_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3771_mb : Scalar.QComplex := ((-944106775893594271589913 : Int)/10^30,(-431476487510812189322993949 : Int)/10^30)
theorem v3771_mb_checked : Scalar.distance (sourceCoefficient 53 62 3 1) v3771_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3771_mg : Scalar.QComplex := ((-93086206997722885296191 : Int)/10^30,(203680435232479859035 : Int)/10^30)
theorem v3771_mg_checked : Scalar.distance (sourceCoefficient 53 62 3 2) v3771_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3771_upper : Scalar.QComplex := ((999995345594726344058366176801 : Int)/10^30,(-3051030790376169217758691788 : Int)/10^30)
theorem v3771_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 62 5) 1) 14) v3771_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3771 : Material (53 : Basis) (62 : Basis) where
  plus := ![v3771_pa,v3771_pb,v3771_pg]
  minus := ![(Primitive.Addresses.material3771 1).one,v3771_mb,v3771_mg]
  upper := v3771_upper
  lower := (Primitive.Addresses.material3771 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3771_pa_checked.trans (by decide +kernel)
    · exact v3771_pb_checked.trans (by decide +kernel)
    · exact v3771_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 62 Primitive.Addresses.material3771
    · exact v3771_mb_checked.trans (by decide +kernel)
    · exact v3771_mg_checked.trans (by decide +kernel)
  upper_error := v3771_upper_checked
  lower_error := reuse_lower_error 53 62 Primitive.Addresses.material3771

def v3772_pa : Scalar.QComplex := ((999999088857378891579449109251 : Int)/10^30,(-1349920150244437643737274722 : Int)/10^30)
theorem v3772_pa_checked : Scalar.distance (sourceCoefficient 53 63 1 0) v3772_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3772_pb : Scalar.QComplex := ((-582460198669276126913593 : Int)/10^30,(-431477126894872091385007592 : Int)/10^30)
theorem v3772_pb_checked : Scalar.distance (sourceCoefficient 53 63 1 1) v3772_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3772_pg : Scalar.QComplex := ((-93086344977520905166314 : Int)/10^30,(125659247291256517227 : Int)/10^30)
theorem v3772_pg_checked : Scalar.distance (sourceCoefficient 53 63 1 2) v3772_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3772_mb : Scalar.QComplex := ((-954805309294590867258203 : Int)/10^30,(-431476463599299851509799151 : Int)/10^30)
theorem v3772_mb_checked : Scalar.distance (sourceCoefficient 53 63 3 1) v3772_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3772_mg : Scalar.QComplex := ((-93086201878949483959053 : Int)/10^30,(205988523764829776736 : Int)/10^30)
theorem v3772_mg_checked : Scalar.distance (sourceCoefficient 53 63 3 2) v3772_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3772_upper : Scalar.QComplex := ((999995269636488660673981208766 : Int)/10^30,(-3075825847856101008200481965 : Int)/10^30)
theorem v3772_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 63 5) 1) 14) v3772_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3772 : Material (53 : Basis) (63 : Basis) where
  plus := ![v3772_pa,v3772_pb,v3772_pg]
  minus := ![(Primitive.Addresses.material3772 1).one,v3772_mb,v3772_mg]
  upper := v3772_upper
  lower := (Primitive.Addresses.material3772 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3772_pa_checked.trans (by decide +kernel)
    · exact v3772_pb_checked.trans (by decide +kernel)
    · exact v3772_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 63 Primitive.Addresses.material3772
    · exact v3772_mb_checked.trans (by decide +kernel)
    · exact v3772_mg_checked.trans (by decide +kernel)
  upper_error := v3772_upper_checked
  lower_error := reuse_lower_error 53 63 Primitive.Addresses.material3772

def v3773_pa : Scalar.QComplex := ((999999040391992561364952430756 : Int)/10^30,(-1385357388557097982026524159 : Int)/10^30)
theorem v3773_pa_checked : Scalar.distance (sourceCoefficient 53 64 1 0) v3773_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3773_pb : Scalar.QComplex := ((-597750569428811667669990 : Int)/10^30,(-431477105301439925712851046 : Int)/10^30)
theorem v3773_pb_checked : Scalar.distance (sourceCoefficient 53 64 1 1) v3773_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3773_pg : Scalar.QComplex := ((-93086340392515758680802 : Int)/10^30,(128957973185616430556 : Int)/10^30)
theorem v3773_pg_checked : Scalar.distance (sourceCoefficient 53 64 1 2) v3773_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3773_mb : Scalar.QComplex := ((-970095655726663142881749 : Int)/10^30,(-431476428810974413315153125 : Int)/10^30)
theorem v3773_mb_checked : Scalar.distance (sourceCoefficient 53 64 3 1) v3773_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3773_mg : Scalar.QComplex := ((-93086194447294166947034 : Int)/10^30,(209287244474270339923 : Int)/10^30)
theorem v3773_mg_checked : Scalar.distance (sourceCoefficient 53 64 3 2) v3773_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3773_upper : Scalar.QComplex := ((999995160009716027454298963868 : Int)/10^30,(-3111262949742297569763796154 : Int)/10^30)
theorem v3773_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 64 5) 1) 14) v3773_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3773 : Material (53 : Basis) (64 : Basis) where
  plus := ![v3773_pa,v3773_pb,v3773_pg]
  minus := ![(Primitive.Addresses.material3773 1).one,v3773_mb,v3773_mg]
  upper := v3773_upper
  lower := (Primitive.Addresses.material3773 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3773_pa_checked.trans (by decide +kernel)
    · exact v3773_pb_checked.trans (by decide +kernel)
    · exact v3773_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 64 Primitive.Addresses.material3773
    · exact v3773_mb_checked.trans (by decide +kernel)
    · exact v3773_mg_checked.trans (by decide +kernel)
  upper_error := v3773_upper_checked
  lower_error := reuse_lower_error 53 64 Primitive.Addresses.material3773

def v3774_pa : Scalar.QComplex := ((999998989918573156223720790021 : Int)/10^30,(-1421323972014495963085316887 : Int)/10^30)
theorem v3774_pa_checked : Scalar.distance (sourceCoefficient 53 65 1 0) v3774_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3774_pb : Scalar.QComplex := ((-613269340392633662722751 : Int)/10^30,(-431477082646720183178344177 : Int)/10^30)
theorem v3774_pb_checked : Scalar.distance (sourceCoefficient 53 65 1 1) v3774_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3774_pg : Scalar.QComplex := ((-93086335599569858802439 : Int)/10^30,(132305973894461900563 : Int)/10^30)
theorem v3774_pg_checked : Scalar.distance (sourceCoefficient 53 65 1 2) v3774_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3774_mb : Scalar.QComplex := ((-985614401362134658126695 : Int)/10^30,(-431476392764262703888153280 : Int)/10^30)
theorem v3774_mb_checked : Scalar.distance (sourceCoefficient 53 65 3 1) v3774_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3774_mg : Scalar.QComplex := ((-93086186765176228322238 : Int)/10^30,(212635239800405689510 : Int)/10^30)
theorem v3774_mg_checked : Scalar.distance (sourceCoefficient 53 65 3 2) v3774_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3774_upper : Scalar.QComplex := ((999995047461311612036500060714 : Int)/10^30,(-3147229392519151442272629758 : Int)/10^30)
theorem v3774_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 65 5) 1) 14) v3774_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3774 : Material (53 : Basis) (65 : Basis) where
  plus := ![v3774_pa,v3774_pb,v3774_pg]
  minus := ![(Primitive.Addresses.material3774 1).one,v3774_mb,v3774_mg]
  upper := v3774_upper
  lower := (Primitive.Addresses.material3774 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3774_pa_checked.trans (by decide +kernel)
    · exact v3774_pb_checked.trans (by decide +kernel)
    · exact v3774_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 65 Primitive.Addresses.material3774
    · exact v3774_mb_checked.trans (by decide +kernel)
    · exact v3774_mg_checked.trans (by decide +kernel)
  upper_error := v3774_upper_checked
  lower_error := reuse_lower_error 53 65 Primitive.Addresses.material3774

def v3775_pa : Scalar.QComplex := ((999998964766282161545062271833 : Int)/10^30,(-1438911520548799875313187726 : Int)/10^30)
theorem v3775_pa_checked : Scalar.distance (sourceCoefficient 53 66 1 0) v3775_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3775_pb : Scalar.QComplex := ((-620857971476017156638030 : Int)/10^30,(-431477071297696284307117151 : Int)/10^30)
theorem v3775_pb_checked : Scalar.distance (sourceCoefficient 53 66 1 1) v3775_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3775_pg : Scalar.QComplex := ((-93086333204689141625443 : Int)/10^30,(133943135916322065555 : Int)/10^30)
theorem v3775_pg_checked : Scalar.distance (sourceCoefficient 53 66 1 2) v3775_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3775_mb : Scalar.QComplex := ((-993203019826227498460741 : Int)/10^30,(-431476374866596185073797781 : Int)/10^30)
theorem v3775_mb_checked : Scalar.distance (sourceCoefficient 53 66 3 1) v3775_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3775_mg : Scalar.QComplex := ((-93086182957499313043753 : Int)/10^30,(214272399146001414263 : Int)/10^30)
theorem v3775_mg_checked : Scalar.distance (sourceCoefficient 53 66 3 2) v3775_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3775_upper : Scalar.QComplex := ((999994991954544838471566107958 : Int)/10^30,(-3164816871448295332431987055 : Int)/10^30)
theorem v3775_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 66 5) 1) 14) v3775_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3775 : Material (53 : Basis) (66 : Basis) where
  plus := ![v3775_pa,v3775_pb,v3775_pg]
  minus := ![(Primitive.Addresses.material3775 1).one,v3775_mb,v3775_mg]
  upper := v3775_upper
  lower := (Primitive.Addresses.material3775 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3775_pa_checked.trans (by decide +kernel)
    · exact v3775_pb_checked.trans (by decide +kernel)
    · exact v3775_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 66 Primitive.Addresses.material3775
    · exact v3775_mb_checked.trans (by decide +kernel)
    · exact v3775_mg_checked.trans (by decide +kernel)
  upper_error := v3775_upper_checked
  lower_error := reuse_lower_error 53 66 Primitive.Addresses.material3775

def v3776_pa : Scalar.QComplex := ((999998921858077019177942306761 : Int)/10^30,(-1468428644358192171874214447 : Int)/10^30)
theorem v3776_pa_checked : Scalar.distance (sourceCoefficient 53 67 1 0) v3776_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3776_pb : Scalar.QComplex := ((-633593945425012719137176 : Int)/10^30,(-431477051850717171989221804 : Int)/10^30)
theorem v3776_pb_checked : Scalar.distance (sourceCoefficient 53 67 1 1) v3776_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3776_pg : Scalar.QComplex := ((-93086329109869645185666 : Int)/10^30,(136690779435146198448 : Int)/10^30)
theorem v3776_pg_checked : Scalar.distance (sourceCoefficient 53 67 1 2) v3776_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3776_mb : Scalar.QComplex := ((-1005938972251170782480331 : Int)/10^30,(-431476344429052402745197373 : Int)/10^30)
theorem v3776_mb_checked : Scalar.distance (sourceCoefficient 53 67 3 1) v3776_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3776_mg : Scalar.QComplex := ((-93086176491588733817490 : Int)/10^30,(217020038108107489982 : Int)/10^30)
theorem v3776_mg_checked : Scalar.distance (sourceCoefficient 53 67 3 2) v3776_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3776_upper : Scalar.QComplex := ((999994898102525680378926792157 : Int)/10^30,(-3194333877239729566069659712 : Int)/10^30)
theorem v3776_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 67 5) 1) 14) v3776_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3776 : Material (53 : Basis) (67 : Basis) where
  plus := ![v3776_pa,v3776_pb,v3776_pg]
  minus := ![(Primitive.Addresses.material3776 1).one,v3776_mb,v3776_mg]
  upper := v3776_upper
  lower := (Primitive.Addresses.material3776 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3776_pa_checked.trans (by decide +kernel)
    · exact v3776_pb_checked.trans (by decide +kernel)
    · exact v3776_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 67 Primitive.Addresses.material3776
    · exact v3776_mb_checked.trans (by decide +kernel)
    · exact v3776_mg_checked.trans (by decide +kernel)
  upper_error := v3776_upper_checked
  lower_error := reuse_lower_error 53 67 Primitive.Addresses.material3776

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
