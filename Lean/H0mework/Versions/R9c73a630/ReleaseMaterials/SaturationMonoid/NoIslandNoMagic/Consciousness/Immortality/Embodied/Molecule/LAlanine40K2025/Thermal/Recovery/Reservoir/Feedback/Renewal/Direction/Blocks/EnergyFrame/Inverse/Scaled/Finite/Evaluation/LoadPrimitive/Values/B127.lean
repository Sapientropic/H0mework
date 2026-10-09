import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B084
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B085

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2033_pa : Scalar.QComplex := ((999999242942894207801354630341 : Int)/10^30,(-1230493250062321902324609291 : Int)/10^30)
theorem v2033_pa_checked : Scalar.distance (sourceCoefficient 23 79 1 0) v2033_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2033_pb : Scalar.QComplex := ((-530930107052598582118536 : Int)/10^30,(-431477137384782795781011279 : Int)/10^30)
theorem v2033_pb_checked : Scalar.distance (sourceCoefficient 23 79 1 1) v2033_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2033_pg : Scalar.QComplex := ((-93086353280696359335639 : Int)/10^30,(114542216099812155627 : Int)/10^30)
theorem v2033_pg_checked : Scalar.distance (sourceCoefficient 23 79 1 2) v2033_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2033_mb : Scalar.QComplex := ((-903275245917241962734211 : Int)/10^30,(-431476518557354886052169567 : Int)/10^30)
theorem v2033_mb_checked : Scalar.distance (sourceCoefficient 23 79 3 1) v2033_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2033_mg : Scalar.QComplex := ((-93086219775619072194883 : Int)/10^30,(194871503878030656944 : Int)/10^30)
theorem v2033_mg_checked : Scalar.distance (sourceCoefficient 23 79 3 2) v2033_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2033_upper : Scalar.QComplex := ((999995629841769875201320069385 : Int)/10^30,(-2956399391483945125923307622 : Int)/10^30)
theorem v2033_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 79 5) 1) 14) v2033_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2033 : Material (23 : Basis) (79 : Basis) where
  plus := ![v2033_pa,v2033_pb,v2033_pg]
  minus := ![(Primitive.Addresses.material2033 1).one,v2033_mb,v2033_mg]
  upper := v2033_upper
  lower := (Primitive.Addresses.material2033 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2033_pa_checked.trans (by decide +kernel)
    · exact v2033_pb_checked.trans (by decide +kernel)
    · exact v2033_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 79 Primitive.Addresses.material2033
    · exact v2033_mb_checked.trans (by decide +kernel)
    · exact v2033_mg_checked.trans (by decide +kernel)
  upper_error := v2033_upper_checked
  lower_error := reuse_lower_error 23 79 Primitive.Addresses.material2033

def v2034_pa : Scalar.QComplex := ((999999232184947202269983389067 : Int)/10^30,(-1239205195298786959713988270 : Int)/10^30)
theorem v2034_pa_checked : Scalar.distance (sourceCoefficient 23 80 1 0) v2034_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2034_pb : Scalar.QComplex := ((-534689113701366180625707 : Int)/10^30,(-431477131622335051053603112 : Int)/10^30)
theorem v2034_pb_checked : Scalar.distance (sourceCoefficient 23 80 1 1) v2034_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2034_pg : Scalar.QComplex := ((-93086352158395221476304 : Int)/10^30,(115353179776003629567 : Int)/10^30)
theorem v2034_pg_checked : Scalar.distance (sourceCoefficient 23 80 1 2) v2034_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2034_mb : Scalar.QComplex := ((-907034246193626718126932 : Int)/10^30,(-431476509551055848435748409 : Int)/10^30)
theorem v2034_mb_checked : Scalar.distance (sourceCoefficient 23 80 3 1) v2034_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2034_mg : Scalar.QComplex := ((-93086217953493224114436 : Int)/10^30,(195682466283767955961 : Int)/10^30)
theorem v2034_mg_checked : Scalar.distance (sourceCoefficient 23 80 3 2) v2034_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2034_upper : Scalar.QComplex := ((999995604047811755727650422455 : Int)/10^30,(-2965111305177750552355236478 : Int)/10^30)
theorem v2034_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 80 5) 1) 14) v2034_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2034 : Material (23 : Basis) (80 : Basis) where
  plus := ![v2034_pa,v2034_pb,v2034_pg]
  minus := ![(Primitive.Addresses.material2034 1).one,v2034_mb,v2034_mg]
  upper := v2034_upper
  lower := (Primitive.Addresses.material2034 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2034_pa_checked.trans (by decide +kernel)
    · exact v2034_pb_checked.trans (by decide +kernel)
    · exact v2034_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 80 Primitive.Addresses.material2034
    · exact v2034_mb_checked.trans (by decide +kernel)
    · exact v2034_mg_checked.trans (by decide +kernel)
  upper_error := v2034_upper_checked
  lower_error := reuse_lower_error 23 80 Primitive.Addresses.material2034

def v2035_pa : Scalar.QComplex := ((999999199333881429937953418338 : Int)/10^30,(-1265437314162140023274348718 : Int)/10^30)
theorem v2035_pa_checked : Scalar.distance (sourceCoefficient 23 81 1 0) v2035_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2035_pb : Scalar.QComplex := ((-546007677442091821555384 : Int)/10^30,(-431477114007627805128683111 : Int)/10^30)
theorem v2035_pb_checked : Scalar.distance (sourceCoefficient 23 81 1 1) v2035_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2035_pg : Scalar.QComplex := ((-93086348729313356773103 : Int)/10^30,(117795033435674837781 : Int)/10^30)
theorem v2035_pg_checked : Scalar.distance (sourceCoefficient 23 81 1 2) v2035_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2035_mb : Scalar.QComplex := ((-918352790519234778198256 : Int)/10^30,(-431476482168944422212500374 : Int)/10^30)
theorem v2035_mb_checked : Scalar.distance (sourceCoefficient 23 81 3 1) v2035_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2035_mg : Scalar.QComplex := ((-93086212417202904925171 : Int)/10^30,(198124316075082239329 : Int)/10^30)
theorem v2035_mg_checked : Scalar.distance (sourceCoefficient 23 81 3 2) v2035_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2035_upper : Scalar.QComplex := ((999995525922537512285367799951 : Int)/10^30,(-2991343328273484712453871286 : Int)/10^30)
theorem v2035_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 81 5) 1) 14) v2035_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2035 : Material (23 : Basis) (81 : Basis) where
  plus := ![v2035_pa,v2035_pb,v2035_pg]
  minus := ![(Primitive.Addresses.material2035 1).one,v2035_mb,v2035_mg]
  upper := v2035_upper
  lower := (Primitive.Addresses.material2035 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2035_pa_checked.trans (by decide +kernel)
    · exact v2035_pb_checked.trans (by decide +kernel)
    · exact v2035_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 81 Primitive.Addresses.material2035
    · exact v2035_mb_checked.trans (by decide +kernel)
    · exact v2035_mg_checked.trans (by decide +kernel)
  upper_error := v2035_upper_checked
  lower_error := reuse_lower_error 23 81 Primitive.Addresses.material2035

def v2036_pa : Scalar.QComplex := ((999999186705702566431651097245 : Int)/10^30,(-1275377565044768403481350658 : Int)/10^30)
theorem v2036_pa_checked : Scalar.distance (sourceCoefficient 23 82 1 0) v2036_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2036_pb : Scalar.QComplex := ((-550296669943912306495315 : Int)/10^30,(-431477107229381287728310246 : Int)/10^30)
theorem v2036_pb_checked : Scalar.distance (sourceCoefficient 23 82 1 1) v2036_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2036_pg : Scalar.QComplex := ((-93086347410392025676449 : Int)/10^30,(118720335653749141155 : Int)/10^30)
theorem v2036_pg_checked : Scalar.distance (sourceCoefficient 23 82 1 2) v2036_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2036_mb : Scalar.QComplex := ((-922641775574745874443731 : Int)/10^30,(-431476471689493068643518341 : Int)/10^30)
theorem v2036_mb_checked : Scalar.distance (sourceCoefficient 23 82 3 1) v2036_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2036_mg : Scalar.QComplex := ((-93086210299787924789970 : Int)/10^30,(199049616810454531789 : Int)/10^30)
theorem v2036_mg_checked : Scalar.distance (sourceCoefficient 23 82 3 2) v2036_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2036_upper : Scalar.QComplex := ((999995496138406206067300071831 : Int)/10^30,(-3001283542556185967904020738 : Int)/10^30)
theorem v2036_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 82 5) 1) 14) v2036_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2036 : Material (23 : Basis) (82 : Basis) where
  plus := ![v2036_pa,v2036_pb,v2036_pg]
  minus := ![(Primitive.Addresses.material2036 1).one,v2036_mb,v2036_mg]
  upper := v2036_upper
  lower := (Primitive.Addresses.material2036 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2036_pa_checked.trans (by decide +kernel)
    · exact v2036_pb_checked.trans (by decide +kernel)
    · exact v2036_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 82 Primitive.Addresses.material2036
    · exact v2036_mb_checked.trans (by decide +kernel)
    · exact v2036_mg_checked.trans (by decide +kernel)
  upper_error := v2036_upper_checked
  lower_error := reuse_lower_error 23 82 Primitive.Addresses.material2036

def v2037_pa : Scalar.QComplex := ((999999169308534325540479479216 : Int)/10^30,(-1288946174710413536692464617 : Int)/10^30)
theorem v2037_pa_checked : Scalar.distance (sourceCoefficient 23 83 1 0) v2037_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2037_pb : Scalar.QComplex := ((-556151216784354744358742 : Int)/10^30,(-431477097885204759542269199 : Int)/10^30)
theorem v2037_pb_checked : Scalar.distance (sourceCoefficient 23 83 1 1) v2037_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2037_pg : Scalar.QComplex := ((-93086345592721302774433 : Int)/10^30,(119983388738686733378 : Int)/10^30)
theorem v2037_pg_checked : Scalar.distance (sourceCoefficient 23 83 1 2) v2037_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2037_mb : Scalar.QComplex := ((-928496312171669459865536 : Int)/10^30,(-431476457293109775421093719 : Int)/10^30)
theorem v2037_mb_checked : Scalar.distance (sourceCoefficient 23 83 3 1) v2037_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2037_mg : Scalar.QComplex := ((-93086207392159952187939 : Int)/10^30,(200312667856531767097 : Int)/10^30)
theorem v2037_mg_checked : Scalar.distance (sourceCoefficient 23 83 3 2) v2037_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2037_upper : Scalar.QComplex := ((999995455323074527964441900795 : Int)/10^30,(-3014852101987046759988029330 : Int)/10^30)
theorem v2037_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 83 5) 1) 14) v2037_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2037 : Material (23 : Basis) (83 : Basis) where
  plus := ![v2037_pa,v2037_pb,v2037_pg]
  minus := ![(Primitive.Addresses.material2037 1).one,v2037_mb,v2037_mg]
  upper := v2037_upper
  lower := (Primitive.Addresses.material2037 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2037_pa_checked.trans (by decide +kernel)
    · exact v2037_pb_checked.trans (by decide +kernel)
    · exact v2037_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 83 Primitive.Addresses.material2037
    · exact v2037_mb_checked.trans (by decide +kernel)
    · exact v2037_mg_checked.trans (by decide +kernel)
  upper_error := v2037_upper_checked
  lower_error := reuse_lower_error 23 83 Primitive.Addresses.material2037

def v2038_pa : Scalar.QComplex := ((999999123398804834334764143335 : Int)/10^30,(-1324085201904195856208745513 : Int)/10^30)
theorem v2038_pa_checked : Scalar.distance (sourceCoefficient 23 84 1 0) v2038_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2038_pb : Scalar.QComplex := ((-571312908390671866576037 : Int)/10^30,(-431477073193988349779752562 : Int)/10^30)
theorem v2038_pb_checked : Scalar.distance (sourceCoefficient 23 84 1 1) v2038_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2038_pg : Scalar.QComplex := ((-93086340792508547644864 : Int)/10^30,(123254354387685828835 : Int)/10^30)
theorem v2038_pg_checked : Scalar.distance (sourceCoefficient 23 84 1 2) v2038_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2038_mb : Scalar.QComplex := ((-943657976825188162994207 : Int)/10^30,(-431476419518045560316310500 : Int)/10^30)
theorem v2038_mb_checked : Scalar.distance (sourceCoefficient 23 84 3 1) v2038_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2038_mg : Scalar.QComplex := ((-93086199769252948134839 : Int)/10^30,(203583628145233446797 : Int)/10^30)
theorem v2038_mg_checked : Scalar.distance (sourceCoefficient 23 84 3 2) v2038_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2038_upper : Scalar.QComplex := ((999995348766640265084973979288 : Int)/10^30,(-3049990997609347590760227485 : Int)/10^30)
theorem v2038_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 84 5) 1) 14) v2038_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2038 : Material (23 : Basis) (84 : Basis) where
  plus := ![v2038_pa,v2038_pb,v2038_pg]
  minus := ![(Primitive.Addresses.material2038 1).one,v2038_mb,v2038_mg]
  upper := v2038_upper
  lower := (Primitive.Addresses.material2038 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2038_pa_checked.trans (by decide +kernel)
    · exact v2038_pb_checked.trans (by decide +kernel)
    · exact v2038_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 84 Primitive.Addresses.material2038
    · exact v2038_mb_checked.trans (by decide +kernel)
    · exact v2038_mg_checked.trans (by decide +kernel)
  upper_error := v2038_upper_checked
  lower_error := reuse_lower_error 23 84 Primitive.Addresses.material2038

def v2039_pa : Scalar.QComplex := ((999999015595855402529188450441 : Int)/10^30,(-1403141945828511578967323921 : Int)/10^30)
theorem v2039_pa_checked : Scalar.distance (sourceCoefficient 23 85 1 0) v2039_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2039_pb : Scalar.QComplex := ((-605424094454059647417587 : Int)/10^30,(-431477015046106489708473209 : Int)/10^30)
theorem v2039_pb_checked : Scalar.distance (sourceCoefficient 23 85 1 1) v2039_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2039_pg : Scalar.QComplex := ((-93086329502636396946747 : Int)/10^30,(130613462084796634975 : Int)/10^30)
theorem v2039_pg_checked : Scalar.distance (sourceCoefficient 23 85 1 2) v2039_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2039_mb : Scalar.QComplex := ((-977769100008419252359233 : Int)/10^30,(-431476331933768089445039995 : Int)/10^30)
theorem v2039_mb_checked : Scalar.distance (sourceCoefficient 23 85 3 1) v2039_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2039_mg : Scalar.QComplex := ((-93086182128806500472447 : Int)/10^30,(210942723359560940379 : Int)/10^30)
theorem v2039_mg_checked : Scalar.distance (sourceCoefficient 23 85 3 2) v2039_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2039_upper : Scalar.QComplex := ((999995104519083351524660351742 : Int)/10^30,(-3129047437729818983624364193 : Int)/10^30)
theorem v2039_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 85 5) 1) 14) v2039_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2039 : Material (23 : Basis) (85 : Basis) where
  plus := ![v2039_pa,v2039_pb,v2039_pg]
  minus := ![(Primitive.Addresses.material2039 1).one,v2039_mb,v2039_mg]
  upper := v2039_upper
  lower := (Primitive.Addresses.material2039 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2039_pa_checked.trans (by decide +kernel)
    · exact v2039_pb_checked.trans (by decide +kernel)
    · exact v2039_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 85 Primitive.Addresses.material2039
    · exact v2039_mb_checked.trans (by decide +kernel)
    · exact v2039_mg_checked.trans (by decide +kernel)
  upper_error := v2039_upper_checked
  lower_error := reuse_lower_error 23 85 Primitive.Addresses.material2039

def v2040_pa : Scalar.QComplex := ((999998995025173683648295627228 : Int)/10^30,(-1417726575422179874136179283 : Int)/10^30)
theorem v2040_pa_checked : Scalar.distance (sourceCoefficient 23 86 1 0) v2040_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2040_pb : Scalar.QComplex := ((-611717029909580976400971 : Int)/10^30,(-431477003925953903385914623 : Int)/10^30)
theorem v2040_pb_checked : Scalar.distance (sourceCoefficient 23 86 1 1) v2040_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2040_pg : Scalar.QComplex := ((-93086327345686705479206 : Int)/10^30,(131971092714054407031 : Int)/10^30)
theorem v2040_pg_checked : Scalar.distance (sourceCoefficient 23 86 1 2) v2040_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2040_mb : Scalar.QComplex := ((-984062023524602260978236 : Int)/10^30,(-431476315383099768840348002 : Int)/10^30)
theorem v2040_mb_checked : Scalar.distance (sourceCoefficient 23 86 3 1) v2040_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2040_mg : Scalar.QComplex := ((-93086178800283524500113 : Int)/10^30,(212300351621960344049 : Int)/10^30)
theorem v2040_mg_checked : Scalar.distance (sourceCoefficient 23 86 3 2) v2040_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2040_upper : Scalar.QComplex := ((999995058776684698847499183983 : Int)/10^30,(-3143632010098264240843767915 : Int)/10^30)
theorem v2040_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 86 5) 1) 14) v2040_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2040 : Material (23 : Basis) (86 : Basis) where
  plus := ![v2040_pa,v2040_pb,v2040_pg]
  minus := ![(Primitive.Addresses.material2040 1).one,v2040_mb,v2040_mg]
  upper := v2040_upper
  lower := (Primitive.Addresses.material2040 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2040_pa_checked.trans (by decide +kernel)
    · exact v2040_pb_checked.trans (by decide +kernel)
    · exact v2040_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 86 Primitive.Addresses.material2040
    · exact v2040_mb_checked.trans (by decide +kernel)
    · exact v2040_mg_checked.trans (by decide +kernel)
  upper_error := v2040_upper_checked
  lower_error := reuse_lower_error 23 86 Primitive.Addresses.material2040

def v2041_pa : Scalar.QComplex := ((999998993655528770403579663608 : Int)/10^30,(-1418692330891373383791473581 : Int)/10^30)
theorem v2041_pa_checked : Scalar.distance (sourceCoefficient 23 87 1 0) v2041_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2041_pb : Scalar.QComplex := ((-612133731392355570047821 : Int)/10^30,(-431477003185286984564492817 : Int)/10^30)
theorem v2041_pb_checked : Scalar.distance (sourceCoefficient 23 87 1 1) v2041_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2041_pg : Scalar.QComplex := ((-93086327202043742180445 : Int)/10^30,(132060991411233063612 : Int)/10^30)
theorem v2041_pg_checked : Scalar.distance (sourceCoefficient 23 87 1 2) v2041_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2041_mb : Scalar.QComplex := ((-984478724213057655846354 : Int)/10^30,(-431476314282838513706696313 : Int)/10^30)
theorem v2041_mb_checked : Scalar.distance (sourceCoefficient 23 87 3 1) v2041_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2041_mg : Scalar.QComplex := ((-93086178579062087908031 : Int)/10^30,(212390250161708199210 : Int)/10^30)
theorem v2041_mg_checked : Scalar.distance (sourceCoefficient 23 87 3 2) v2041_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2041_upper : Scalar.QComplex := ((999995055740235498351766797833 : Int)/10^30,(-3144597761765195557697397213 : Int)/10^30)
theorem v2041_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 87 5) 1) 14) v2041_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2041 : Material (23 : Basis) (87 : Basis) where
  plus := ![v2041_pa,v2041_pb,v2041_pg]
  minus := ![(Primitive.Addresses.material2041 1).one,v2041_mb,v2041_mg]
  upper := v2041_upper
  lower := (Primitive.Addresses.material2041 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2041_pa_checked.trans (by decide +kernel)
    · exact v2041_pb_checked.trans (by decide +kernel)
    · exact v2041_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 87 Primitive.Addresses.material2041
    · exact v2041_mb_checked.trans (by decide +kernel)
    · exact v2041_mg_checked.trans (by decide +kernel)
  upper_error := v2041_upper_checked
  lower_error := reuse_lower_error 23 87 Primitive.Addresses.material2041

def v2042_pa : Scalar.QComplex := ((999998976903139628570453894019 : Int)/10^30,(-1430451912514249250089822152 : Int)/10^30)
theorem v2042_pa_checked : Scalar.distance (sourceCoefficient 23 88 1 0) v2042_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2042_pb : Scalar.QComplex := ((-617207722913092788654450 : Int)/10^30,(-431476994123464500364817968 : Int)/10^30)
theorem v2042_pb_checked : Scalar.distance (sourceCoefficient 23 88 1 1) v2042_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2042_pg : Scalar.QComplex := ((-93086325444840466740891 : Int)/10^30,(133155648492621782761 : Int)/10^30)
theorem v2042_pg_checked : Scalar.distance (sourceCoefficient 23 88 1 2) v2042_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2042_mb : Scalar.QComplex := ((-989552706024571263884175 : Int)/10^30,(-431476300842393245336339265 : Int)/10^30)
theorem v2042_mb_checked : Scalar.distance (sourceCoefficient 23 88 3 1) v2042_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2042_mg : Scalar.QComplex := ((-93086175877219707041887 : Int)/10^30,(213484905319118773451 : Int)/10^30)
theorem v2042_mg_checked : Scalar.distance (sourceCoefficient 23 88 3 2) v2042_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2042_upper : Scalar.QComplex := ((999995018691900247061928364897 : Int)/10^30,(-3156357296960452080283262717 : Int)/10^30)
theorem v2042_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 88 5) 1) 14) v2042_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2042 : Material (23 : Basis) (88 : Basis) where
  plus := ![v2042_pa,v2042_pb,v2042_pg]
  minus := ![(Primitive.Addresses.material2042 1).one,v2042_mb,v2042_mg]
  upper := v2042_upper
  lower := (Primitive.Addresses.material2042 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2042_pa_checked.trans (by decide +kernel)
    · exact v2042_pb_checked.trans (by decide +kernel)
    · exact v2042_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 88 Primitive.Addresses.material2042
    · exact v2042_mb_checked.trans (by decide +kernel)
    · exact v2042_mg_checked.trans (by decide +kernel)
  upper_error := v2042_upper_checked
  lower_error := reuse_lower_error 23 88 Primitive.Addresses.material2042

def v2043_pa : Scalar.QComplex := ((999998953758470092236659802752 : Int)/10^30,(-1446541380394694335153226176 : Int)/10^30)
theorem v2043_pa_checked : Scalar.distance (sourceCoefficient 23 89 1 0) v2043_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2043_pb : Scalar.QComplex := ((-624149961578288509715323 : Int)/10^30,(-431476981596182402877420011 : Int)/10^30)
theorem v2043_pb_checked : Scalar.distance (sourceCoefficient 23 89 1 1) v2043_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2043_pg : Scalar.QComplex := ((-93086323016302910166401 : Int)/10^30,(134653359071805621050 : Int)/10^30)
theorem v2043_pg_checked : Scalar.distance (sourceCoefficient 23 89 1 2) v2043_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2043_mb : Scalar.QComplex := ((-996494931294374011621597 : Int)/10^30,(-431476282324276511087426378 : Int)/10^30)
theorem v2043_mb_checked : Scalar.distance (sourceCoefficient 23 89 3 1) v2043_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2043_mg : Scalar.QComplex := ((-93086172156226279267729 : Int)/10^30,(214982613244917980303 : Int)/10^30)
theorem v2043_mg_checked : Scalar.distance (sourceCoefficient 23 89 3 2) v2043_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2043_upper : Scalar.QComplex := ((999994967778303245470576186706 : Int)/10^30,(-3172446700931924807392826333 : Int)/10^30)
theorem v2043_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 89 5) 1) 14) v2043_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2043 : Material (23 : Basis) (89 : Basis) where
  plus := ![v2043_pa,v2043_pb,v2043_pg]
  minus := ![(Primitive.Addresses.material2043 1).one,v2043_mb,v2043_mg]
  upper := v2043_upper
  lower := (Primitive.Addresses.material2043 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2043_pa_checked.trans (by decide +kernel)
    · exact v2043_pb_checked.trans (by decide +kernel)
    · exact v2043_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 89 Primitive.Addresses.material2043
    · exact v2043_mb_checked.trans (by decide +kernel)
    · exact v2043_mg_checked.trans (by decide +kernel)
  upper_error := v2043_upper_checked
  lower_error := reuse_lower_error 23 89 Primitive.Addresses.material2043

def v2044_pa : Scalar.QComplex := ((999998915511533949059592223613 : Int)/10^30,(-1472744294161972918159821649 : Int)/10^30)
theorem v2044_pa_checked : Scalar.distance (sourceCoefficient 23 90 1 0) v2044_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2044_pb : Scalar.QComplex := ((-635455921336779645418687 : Int)/10^30,(-431476960875785738699113138 : Int)/10^30)
theorem v2044_pb_checked : Scalar.distance (sourceCoefficient 23 90 1 1) v2044_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2044_pg : Scalar.QComplex := ((-93086319001071074640118 : Int)/10^30,(137092493848597028757 : Int)/10^30)
theorem v2044_pg_checked : Scalar.distance (sourceCoefficient 23 90 1 2) v2044_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2044_mb : Scalar.QComplex := ((-1007800868962370512189277 : Int)/10^30,(-431476251847353492006989689 : Int)/10^30)
theorem v2044_mb_checked : Scalar.distance (sourceCoefficient 23 90 3 1) v2044_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2044_mg : Scalar.QComplex := ((-93086166036132480977133 : Int)/10^30,(217421743648543801913 : Int)/10^30)
theorem v2044_mg_checked : Scalar.distance (sourceCoefficient 23 90 3 2) v2044_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2044_upper : Scalar.QComplex := ((999994884307572014057263919192 : Int)/10^30,(-3198649509662299296326728009 : Int)/10^30)
theorem v2044_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 90 5) 1) 14) v2044_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2044 : Material (23 : Basis) (90 : Basis) where
  plus := ![v2044_pa,v2044_pb,v2044_pg]
  minus := ![(Primitive.Addresses.material2044 1).one,v2044_mb,v2044_mg]
  upper := v2044_upper
  lower := (Primitive.Addresses.material2044 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2044_pa_checked.trans (by decide +kernel)
    · exact v2044_pb_checked.trans (by decide +kernel)
    · exact v2044_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 90 Primitive.Addresses.material2044
    · exact v2044_mb_checked.trans (by decide +kernel)
    · exact v2044_mg_checked.trans (by decide +kernel)
  upper_error := v2044_upper_checked
  lower_error := reuse_lower_error 23 90 Primitive.Addresses.material2044

def v2045_pa : Scalar.QComplex := ((999998893663306386535060088689 : Int)/10^30,(-1487505348980651647138531881 : Int)/10^30)
theorem v2045_pa_checked : Scalar.distance (sourceCoefficient 23 91 1 0) v2045_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2045_pb : Scalar.QComplex := ((-641824979717457532790785 : Int)/10^30,(-431476949029297212907722985 : Int)/10^30)
theorem v2045_pb_checked : Scalar.distance (sourceCoefficient 23 91 1 1) v2045_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2045_pg : Scalar.QComplex := ((-93086316706310879190158 : Int)/10^30,(138466547208166442306 : Int)/10^30)
theorem v2045_pg_checked : Scalar.distance (sourceCoefficient 23 91 1 2) v2045_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2045_mb : Scalar.QComplex := ((-1014169914748570832366412 : Int)/10^30,(-431476234504658846420700729 : Int)/10^30)
theorem v2045_mb_checked : Scalar.distance (sourceCoefficient 23 91 3 1) v2045_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2045_mg : Scalar.QComplex := ((-93086162555626975728898 : Int)/10^30,(218795794516215655843 : Int)/10^30)
theorem v2045_mg_checked : Scalar.distance (sourceCoefficient 23 91 3 2) v2045_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2045_upper : Scalar.QComplex := ((999994836983135487294305123277 : Int)/10^30,(-3213410504788062110990350235 : Int)/10^30)
theorem v2045_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 91 5) 1) 14) v2045_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2045 : Material (23 : Basis) (91 : Basis) where
  plus := ![v2045_pa,v2045_pb,v2045_pg]
  minus := ![(Primitive.Addresses.material2045 1).one,v2045_mb,v2045_mg]
  upper := v2045_upper
  lower := (Primitive.Addresses.material2045 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2045_pa_checked.trans (by decide +kernel)
    · exact v2045_pb_checked.trans (by decide +kernel)
    · exact v2045_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 91 Primitive.Addresses.material2045
    · exact v2045_mb_checked.trans (by decide +kernel)
    · exact v2045_mg_checked.trans (by decide +kernel)
  upper_error := v2045_upper_checked
  lower_error := reuse_lower_error 23 91 Primitive.Addresses.material2045

def v2046_pa : Scalar.QComplex := ((999998845617834064914306212442 : Int)/10^30,(-1519461417500288606323034403 : Int)/10^30)
theorem v2046_pa_checked : Scalar.distance (sourceCoefficient 23 92 1 0) v2046_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2046_pb : Scalar.QComplex := ((-655613293797898714083233 : Int)/10^30,(-431476922953510977754736864 : Int)/10^30)
theorem v2046_pb_checked : Scalar.distance (sourceCoefficient 23 92 1 1) v2046_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2046_pg : Scalar.QComplex := ((-93086311657341081352582 : Int)/10^30,(141441222337961714053 : Int)/10^30)
theorem v2046_pg_checked : Scalar.distance (sourceCoefficient 23 92 1 2) v2046_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2046_mb : Scalar.QComplex := ((-1027958201192763413305603 : Int)/10^30,(-431476196530188271667395259 : Int)/10^30)
theorem v2046_mb_checked : Scalar.distance (sourceCoefficient 23 92 3 1) v2046_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2046_mg : Scalar.QComplex := ((-93086154939648395234691 : Int)/10^30,(221770464181369889023 : Int)/10^30)
theorem v2046_mg_checked : Scalar.distance (sourceCoefficient 23 92 3 2) v2046_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2046_upper : Scalar.QComplex := ((999994733784459490757472228386 : Int)/10^30,(-3245366442790762257759318904 : Int)/10^30)
theorem v2046_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 92 5) 1) 14) v2046_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2046 : Material (23 : Basis) (92 : Basis) where
  plus := ![v2046_pa,v2046_pb,v2046_pg]
  minus := ![(Primitive.Addresses.material2046 1).one,v2046_mb,v2046_mg]
  upper := v2046_upper
  lower := (Primitive.Addresses.material2046 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2046_pa_checked.trans (by decide +kernel)
    · exact v2046_pb_checked.trans (by decide +kernel)
    · exact v2046_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 92 Primitive.Addresses.material2046
    · exact v2046_mb_checked.trans (by decide +kernel)
    · exact v2046_mg_checked.trans (by decide +kernel)
  upper_error := v2046_upper_checked
  lower_error := reuse_lower_error 23 92 Primitive.Addresses.material2046

def v2047_pa : Scalar.QComplex := ((999998787272155184370686077495 : Int)/10^30,(-1557386984317781254996969109 : Int)/10^30)
theorem v2047_pa_checked : Scalar.distance (sourceCoefficient 23 93 1 0) v2047_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2047_pb : Scalar.QComplex := ((-671977309383392857759924 : Int)/10^30,(-431476891244317357304132185 : Int)/10^30)
theorem v2047_pb_checked : Scalar.distance (sourceCoefficient 23 93 1 1) v2047_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2047_pg : Scalar.QComplex := ((-93086305521294357466763 : Int)/10^30,(144971576448159715644 : Int)/10^30)
theorem v2047_pg_checked : Scalar.distance (sourceCoefficient 23 93 1 2) v2047_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2047_mb : Scalar.QComplex := ((-1044322183321580716662069 : Int)/10^30,(-431476150699598015620262497 : Int)/10^30)
theorem v2047_mb_checked : Scalar.distance (sourceCoefficient 23 93 3 1) v2047_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2047_mg : Scalar.QComplex := ((-93086145757067360225343 : Int)/10^30,(225300811681923744805 : Int)/10^30)
theorem v2047_mg_checked : Scalar.distance (sourceCoefficient 23 93 3 2) v2047_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2047_upper : Scalar.QComplex := ((999994609982779762801810803105 : Int)/10^30,(-3283291852423229512629025130 : Int)/10^30)
theorem v2047_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 93 5) 1) 14) v2047_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2047 : Material (23 : Basis) (93 : Basis) where
  plus := ![v2047_pa,v2047_pb,v2047_pg]
  minus := ![(Primitive.Addresses.material2047 1).one,v2047_mb,v2047_mg]
  upper := v2047_upper
  lower := (Primitive.Addresses.material2047 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2047_pa_checked.trans (by decide +kernel)
    · exact v2047_pb_checked.trans (by decide +kernel)
    · exact v2047_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 93 Primitive.Addresses.material2047
    · exact v2047_mb_checked.trans (by decide +kernel)
    · exact v2047_mg_checked.trans (by decide +kernel)
  upper_error := v2047_upper_checked
  lower_error := reuse_lower_error 23 93 Primitive.Addresses.material2047

def v2048_pa : Scalar.QComplex := ((999998716500010686123399828688 : Int)/10^30,(-1602185485908398382412036776 : Int)/10^30)
theorem v2048_pa_checked : Scalar.distance (sourceCoefficient 23 94 1 0) v2048_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2048_pb : Scalar.QComplex := ((-691306838230090069148957 : Int)/10^30,(-431476852722715630616877057 : Int)/10^30)
theorem v2048_pb_checked : Scalar.distance (sourceCoefficient 23 94 1 1) v2048_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2048_pg : Scalar.QComplex := ((-93086298072029689723913 : Int)/10^30,(149141707131328405271 : Int)/10^30)
theorem v2048_pg_checked : Scalar.distance (sourceCoefficient 23 94 1 2) v2048_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2048_mb : Scalar.QComplex := ((-1063651671728603593722789 : Int)/10^30,(-431476095497497807248351262 : Int)/10^30)
theorem v2048_mb_checked : Scalar.distance (sourceCoefficient 23 94 3 1) v2048_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2048_mg : Scalar.QComplex := ((-93086134709170502323519 : Int)/10^30,(229470934383982290866 : Int)/10^30)
theorem v2048_mg_checked : Scalar.distance (sourceCoefficient 23 94 3 2) v2048_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2048_upper : Scalar.QComplex := ((999994461892591014262497762383 : Int)/10^30,(-3328090165145439917300931920 : Int)/10^30)
theorem v2048_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 94 5) 1) 14) v2048_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2048 : Material (23 : Basis) (94 : Basis) where
  plus := ![v2048_pa,v2048_pb,v2048_pg]
  minus := ![(Primitive.Addresses.material2048 1).one,v2048_mb,v2048_mg]
  upper := v2048_upper
  lower := (Primitive.Addresses.material2048 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2048_pa_checked.trans (by decide +kernel)
    · exact v2048_pb_checked.trans (by decide +kernel)
    · exact v2048_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 94 Primitive.Addresses.material2048
    · exact v2048_mb_checked.trans (by decide +kernel)
    · exact v2048_mg_checked.trans (by decide +kernel)
  upper_error := v2048_upper_checked
  lower_error := reuse_lower_error 23 94 Primitive.Addresses.material2048

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
