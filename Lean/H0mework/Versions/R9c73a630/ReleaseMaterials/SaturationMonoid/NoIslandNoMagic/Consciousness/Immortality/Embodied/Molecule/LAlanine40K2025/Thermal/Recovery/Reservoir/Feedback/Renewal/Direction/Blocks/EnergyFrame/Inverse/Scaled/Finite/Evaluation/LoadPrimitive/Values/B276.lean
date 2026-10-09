import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B184

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4417_pa : Scalar.QComplex := ((999997559603525871092050709755 : Int)/10^30,(-2209250323689659428036479419 : Int)/10^30)
theorem v4417_pa_checked : Scalar.distance (sourceCoefficient 71 87 1 0) v4417_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4417_pb : Scalar.QComplex := ((-953241839790412903887506 : Int)/10^30,(-431476462074423006507377516 : Int)/10^30)
theorem v4417_pb_checked : Scalar.distance (sourceCoefficient 71 87 1 1) v4417_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4417_pg : Scalar.QComplex := ((-93086202087356959160460 : Int)/10^30,(205651223963056272868 : Int)/10^30)
theorem v4417_pg_checked : Scalar.distance (sourceCoefficient 71 87 1 2) v4417_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4417_mb : Scalar.QComplex := ((-1325586238646671937969299 : Int)/10^30,(-431475478811241407333898383 : Int)/10^30)
theorem v4417_mb_checked : Scalar.distance (sourceCoefficient 71 87 3 1) v4417_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4417_mg : Scalar.QComplex := ((-93085989959365579619055 : Int)/10^30,(285980347344184852214 : Int)/10^30)
theorem v4417_mg_checked : Scalar.distance (sourceCoefficient 71 87 3 2) v4417_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4417_upper : Scalar.QComplex := ((999992257258991742070926683033 : Int)/10^30,(-3935152102076555971408291845 : Int)/10^30)
theorem v4417_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 87 5) 1) 14) v4417_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4417 : Material (71 : Basis) (87 : Basis) where
  plus := ![v4417_pa,v4417_pb,v4417_pg]
  minus := ![(Primitive.Addresses.material4417 1).one,v4417_mb,v4417_mg]
  upper := v4417_upper
  lower := (Primitive.Addresses.material4417 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4417_pa_checked.trans (by decide +kernel)
    · exact v4417_pb_checked.trans (by decide +kernel)
    · exact v4417_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 87 Primitive.Addresses.material4417
    · exact v4417_mb_checked.trans (by decide +kernel)
    · exact v4417_mg_checked.trans (by decide +kernel)
  upper_error := v4417_upper_checked
  lower_error := reuse_lower_error 71 87 Primitive.Addresses.material4417

def v4418_pa : Scalar.QComplex := ((999997533554496151314675363508 : Int)/10^30,(-2221009888394004245361227583 : Int)/10^30)
theorem v4418_pa_checked : Scalar.distance (sourceCoefficient 71 88 1 0) v4418_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4418_pb : Scalar.QComplex := ((-958315826444506499107172 : Int)/10^30,(-431476450338406392907664109 : Int)/10^30)
theorem v4418_pb_checked : Scalar.distance (sourceCoefficient 71 88 1 1) v4418_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4418_pg : Scalar.QComplex := ((-93086199608994472421620 : Int)/10^30,(206745879732040319148 : Int)/10^30)
theorem v4418_pg_checked : Scalar.distance (sourceCoefficient 71 88 1 2) v4418_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4418_mb : Scalar.QComplex := ((-1330660213283834642254361 : Int)/10^30,(-431475462696607204982455354 : Int)/10^30)
theorem v4418_mb_checked : Scalar.distance (sourceCoefficient 71 88 3 1) v4418_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4418_mg : Scalar.QComplex := ((-93085986536365388520283 : Int)/10^30,(287075000566863322708 : Int)/10^30)
theorem v4418_mg_checked : Scalar.distance (sourceCoefficient 71 88 3 2) v4418_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4418_upper : Scalar.QComplex := ((999992210914058958940672787236 : Int)/10^30,(-3946911604308148390298461157 : Int)/10^30)
theorem v4418_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 88 5) 1) 14) v4418_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4418 : Material (71 : Basis) (88 : Basis) where
  plus := ![v4418_pa,v4418_pb,v4418_pg]
  minus := ![(Primitive.Addresses.material4418 1).one,v4418_mb,v4418_mg]
  upper := v4418_upper
  lower := (Primitive.Addresses.material4418 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4418_pa_checked.trans (by decide +kernel)
    · exact v4418_pb_checked.trans (by decide +kernel)
    · exact v4418_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 88 Primitive.Addresses.material4418
    · exact v4418_mb_checked.trans (by decide +kernel)
    · exact v4418_mg_checked.trans (by decide +kernel)
  upper_error := v4418_upper_checked
  lower_error := reuse_lower_error 71 88 Primitive.Addresses.material4418

def v4419_pa : Scalar.QComplex := ((999997497690156481426942478694 : Int)/10^30,(-2237099332949387195158237875 : Int)/10^30)
theorem v4419_pa_checked : Scalar.distance (sourceCoefficient 71 89 1 0) v4419_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4419_pb : Scalar.QComplex := ((-965258058400209276452242 : Int)/10^30,(-431476434152290026425251757 : Int)/10^30)
theorem v4419_pb_checked : Scalar.distance (sourceCoefficient 71 89 1 1) v4419_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4419_pg : Scalar.QComplex := ((-93086196193766380279562 : Int)/10^30,(208243588501851912415 : Int)/10^30)
theorem v4419_pg_checked : Scalar.distance (sourceCoefficient 71 89 1 2) v4419_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4419_mb : Scalar.QComplex := ((-1337602428686737758162410 : Int)/10^30,(-431475440519663354079969488 : Int)/10^30)
theorem v4419_mb_checked : Scalar.distance (sourceCoefficient 71 89 3 1) v4419_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4419_mg : Scalar.QComplex := ((-93085981828683353975293 : Int)/10^30,(288572705831821464947 : Int)/10^30)
theorem v4419_mg_checked : Scalar.distance (sourceCoefficient 71 89 3 2) v4419_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4419_upper : Scalar.QComplex := ((999992147280851025191100693796 : Int)/10^30,(-3963000963001596991028220752 : Int)/10^30)
theorem v4419_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 89 5) 1) 14) v4419_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4419 : Material (71 : Basis) (89 : Basis) where
  plus := ![v4419_pa,v4419_pb,v4419_pg]
  minus := ![(Primitive.Addresses.material4419 1).one,v4419_mb,v4419_mg]
  upper := v4419_upper
  lower := (Primitive.Addresses.material4419 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4419_pa_checked.trans (by decide +kernel)
    · exact v4419_pb_checked.trans (by decide +kernel)
    · exact v4419_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 89 Primitive.Addresses.material4419
    · exact v4419_mb_checked.trans (by decide +kernel)
    · exact v4419_mg_checked.trans (by decide +kernel)
  upper_error := v4419_upper_checked
  lower_error := reuse_lower_error 71 89 Primitive.Addresses.material4419

def v4420_pa : Scalar.QComplex := ((999997438728276913866433629324 : Int)/10^30,(-2263302208291996442934682440 : Int)/10^30)
theorem v4420_pa_checked : Scalar.distance (sourceCoefficient 71 90 1 0) v4420_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4420_pb : Scalar.QComplex := ((-976564007105780359306551 : Int)/10^30,(-431476407473205451577456646 : Int)/10^30)
theorem v4420_pb_checked : Scalar.distance (sourceCoefficient 71 90 1 1) v4420_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4420_pg : Scalar.QComplex := ((-93086190571634493886433 : Int)/10^30,(210682720297964010756 : Int)/10^30)
theorem v4420_pg_checked : Scalar.distance (sourceCoefficient 71 90 1 2) v4420_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4420_mb : Scalar.QComplex := ((-1348908350159739023821705 : Int)/10^30,(-431475404084064181194079761 : Int)/10^30)
theorem v4420_mb_checked : Scalar.distance (sourceCoefficient 71 90 3 1) v4420_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4420_mg : Scalar.QComplex := ((-93085974101692675332178 : Int)/10^30,(291011831868086715228 : Int)/10^30)
theorem v4420_mg_checked : Scalar.distance (sourceCoefficient 71 90 3 2) v4420_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4420_upper : Scalar.QComplex := ((999992043095273539362643422355 : Int)/10^30,(-3989203697555246268265051812 : Int)/10^30)
theorem v4420_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 90 5) 1) 14) v4420_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4420 : Material (71 : Basis) (90 : Basis) where
  plus := ![v4420_pa,v4420_pb,v4420_pg]
  minus := ![(Primitive.Addresses.material4420 1).one,v4420_mb,v4420_mg]
  upper := v4420_upper
  lower := (Primitive.Addresses.material4420 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4420_pa_checked.trans (by decide +kernel)
    · exact v4420_pb_checked.trans (by decide +kernel)
    · exact v4420_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 90 Primitive.Addresses.material4420
    · exact v4420_mb_checked.trans (by decide +kernel)
    · exact v4420_mg_checked.trans (by decide +kernel)
  upper_error := v4420_upper_checked
  lower_error := reuse_lower_error 71 90 Primitive.Addresses.material4420

def v4421_pa : Scalar.QComplex := ((999997405210568022154724961300 : Int)/10^30,(-2278063241225645659570508975 : Int)/10^30)
theorem v4421_pa_checked : Scalar.distance (sourceCoefficient 71 91 1 0) v4421_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4421_pb : Scalar.QComplex := ((-982933059191193120651638 : Int)/10^30,(-431476392269971233238037900 : Int)/10^30)
theorem v4421_pb_checked : Scalar.distance (sourceCoefficient 71 91 1 1) v4421_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4421_pg : Scalar.QComplex := ((-93086187371649035518418 : Int)/10^30,(212056771959867428314 : Int)/10^30)
theorem v4421_pg_checked : Scalar.distance (sourceCoefficient 71 91 1 2) v4421_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4421_mb : Scalar.QComplex := ((-1355277386753956211531639 : Int)/10^30,(-431475383384630525459869945 : Int)/10^30)
theorem v4421_mb_checked : Scalar.distance (sourceCoefficient 71 91 3 1) v4421_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4421_mg : Scalar.QComplex := ((-93085969715963709231920 : Int)/10^30,(292385880256924573220 : Int)/10^30)
theorem v4421_mg_checked : Scalar.distance (sourceCoefficient 71 91 3 2) v4421_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4421_upper : Scalar.QComplex := ((999991984101410835309698283224 : Int)/10^30,(-4003964650655546038665872852 : Int)/10^30)
theorem v4421_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 91 5) 1) 14) v4421_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4421 : Material (71 : Basis) (91 : Basis) where
  plus := ![v4421_pa,v4421_pb,v4421_pg]
  minus := ![(Primitive.Addresses.material4421 1).one,v4421_mb,v4421_mg]
  upper := v4421_upper
  lower := (Primitive.Addresses.material4421 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4421_pa_checked.trans (by decide +kernel)
    · exact v4421_pb_checked.trans (by decide +kernel)
    · exact v4421_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 91 Primitive.Addresses.material4421
    · exact v4421_mb_checked.trans (by decide +kernel)
    · exact v4421_mg_checked.trans (by decide +kernel)
  upper_error := v4421_upper_checked
  lower_error := reuse_lower_error 71 91 Primitive.Addresses.material4421

def v4422_pa : Scalar.QComplex := ((999997331901945737220631674313 : Int)/10^30,(-2310019261776475225723085634 : Int)/10^30)
theorem v4422_pa_checked : Scalar.distance (sourceCoefficient 71 92 1 0) v4422_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4422_pb : Scalar.QComplex := ((-996721359473327148588575 : Int)/10^30,(-431476358927197963506489043 : Int)/10^30)
theorem v4422_pb_checked : Scalar.distance (sourceCoefficient 71 92 1 1) v4422_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4422_pg : Scalar.QComplex := ((-93086180362965615968735 : Int)/10^30,(215031443368625314024 : Int)/10^30)
theorem v4422_pg_checked : Scalar.distance (sourceCoefficient 71 92 1 2) v4422_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4422_mb : Scalar.QComplex := ((-1369065653128764258960738 : Int)/10^30,(-431475338143187529277013090 : Int)/10^30)
theorem v4422_mb_checked : Scalar.distance (sourceCoefficient 71 92 3 1) v4422_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4422_mg : Scalar.QComplex := ((-93085960140275447804225 : Int)/10^30,(295360544509898212562 : Int)/10^30)
theorem v4422_mg_checked : Scalar.distance (sourceCoefficient 71 92 3 2) v4422_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4422_upper : Scalar.QComplex := ((999991855639705291763642434317 : Int)/10^30,(-4035920497087605254689574348 : Int)/10^30)
theorem v4422_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 92 5) 1) 14) v4422_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4422 : Material (71 : Basis) (92 : Basis) where
  plus := ![v4422_pa,v4422_pb,v4422_pg]
  minus := ![(Primitive.Addresses.material4422 1).one,v4422_mb,v4422_mg]
  upper := v4422_upper
  lower := (Primitive.Addresses.material4422 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4422_pa_checked.trans (by decide +kernel)
    · exact v4422_pb_checked.trans (by decide +kernel)
    · exact v4422_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 92 Primitive.Addresses.material4422
    · exact v4422_mb_checked.trans (by decide +kernel)
    · exact v4422_mg_checked.trans (by decide +kernel)
  upper_error := v4422_upper_checked
  lower_error := reuse_lower_error 71 92 Primitive.Addresses.material4422

def v4423_pa : Scalar.QComplex := ((999997243573878124089451463075 : Int)/10^30,(-2347944770616816646164405671 : Int)/10^30)
theorem v4423_pa_checked : Scalar.distance (sourceCoefficient 71 93 1 0) v4423_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4423_pb : Scalar.QComplex := ((-1013085358381597494226368 : Int)/10^30,(-431476318593520487893919873 : Int)/10^30)
theorem v4423_pb_checked : Scalar.distance (sourceCoefficient 71 93 1 1) v4423_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4423_pg : Scalar.QComplex := ((-93086171901124384965529 : Int)/10^30,(218561792981418475173 : Int)/10^30)
theorem v4423_pg_checked : Scalar.distance (sourceCoefficient 71 93 1 2) v4423_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4423_mb : Scalar.QComplex := ((-1385429611137822839299688 : Int)/10^30,(-431475283688131021050436928 : Int)/10^30)
theorem v4423_mb_checked : Scalar.distance (sourceCoefficient 71 93 3 1) v4423_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4423_mg : Scalar.QComplex := ((-93085948631904652734900 : Int)/10^30,(298890885505992992746 : Int)/10^30)
theorem v4423_mg_checked : Scalar.distance (sourceCoefficient 71 93 3 2) v4423_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4423_upper : Scalar.QComplex := ((999991701855781549769833192037 : Int)/10^30,(-4073845796996124660095311406 : Int)/10^30)
theorem v4423_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 93 5) 1) 14) v4423_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4423 : Material (71 : Basis) (93 : Basis) where
  plus := ![v4423_pa,v4423_pb,v4423_pg]
  minus := ![(Primitive.Addresses.material4423 1).one,v4423_mb,v4423_mg]
  upper := v4423_upper
  lower := (Primitive.Addresses.material4423 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4423_pa_checked.trans (by decide +kernel)
    · exact v4423_pb_checked.trans (by decide +kernel)
    · exact v4423_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 93 Primitive.Addresses.material4423
    · exact v4423_mb_checked.trans (by decide +kernel)
    · exact v4423_mg_checked.trans (by decide +kernel)
  upper_error := v4423_upper_checked
  lower_error := reuse_lower_error 71 93 Primitive.Addresses.material4423

def v4424_pa : Scalar.QComplex := ((999997137385886742638185976568 : Int)/10^30,(-2392743202258688312793721521 : Int)/10^30)
theorem v4424_pa_checked : Scalar.distance (sourceCoefficient 71 94 1 0) v4424_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4424_pb : Scalar.QComplex := ((-1032414867107422087327738 : Int)/10^30,(-431476269884491725172049072 : Int)/10^30)
theorem v4424_pb_checked : Scalar.distance (sourceCoefficient 71 94 1 1) v4424_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4424_pg : Scalar.QComplex := ((-93086161704580888184870 : Int)/10^30,(222731918238521577056 : Int)/10^30)
theorem v4424_pg_checked : Scalar.distance (sourceCoefficient 71 94 1 2) v4424_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4424_mb : Scalar.QComplex := ((-1404759070632689882576646 : Int)/10^30,(-431475218298624933295443071 : Int)/10^30)
theorem v4424_mb_checked : Scalar.distance (sourceCoefficient 71 94 3 1) v4424_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4424_mg : Scalar.QComplex := ((-93085934836734671182955 : Int)/10^30,(303061000411210074820 : Int)/10^30)
theorem v4424_mg_checked : Scalar.distance (sourceCoefficient 71 94 3 2) v4424_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4424_upper : Scalar.QComplex := ((999991518349919390959200528185 : Int)/10^30,(-4118643978645154964542447857 : Int)/10^30)
theorem v4424_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 94 5) 1) 14) v4424_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4424 : Material (71 : Basis) (94 : Basis) where
  plus := ![v4424_pa,v4424_pb,v4424_pg]
  minus := ![(Primitive.Addresses.material4424 1).one,v4424_mb,v4424_mg]
  upper := v4424_upper
  lower := (Primitive.Addresses.material4424 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4424_pa_checked.trans (by decide +kernel)
    · exact v4424_pb_checked.trans (by decide +kernel)
    · exact v4424_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 94 Primitive.Addresses.material4424
    · exact v4424_mb_checked.trans (by decide +kernel)
    · exact v4424_mg_checked.trans (by decide +kernel)
  upper_error := v4424_upper_checked
  lower_error := reuse_lower_error 71 94 Primitive.Addresses.material4424

def v4425_pa : Scalar.QComplex := ((999997030468938410884994204312 : Int)/10^30,(-2437017296833057824206975323 : Int)/10^30)
theorem v4425_pa_checked : Scalar.distance (sourceCoefficient 71 95 1 0) v4425_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4425_pb : Scalar.QComplex := ((-1051518135317363201385966 : Int)/10^30,(-431476220611178588315746458 : Int)/10^30)
theorem v4425_pb_checked : Scalar.distance (sourceCoefficient 71 95 1 1) v4425_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4425_pg : Scalar.QComplex := ((-93086151413240382418143 : Int)/10^30,(226853234737414776839 : Int)/10^30)
theorem v4425_pg_checked : Scalar.distance (sourceCoefficient 71 95 1 2) v4425_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4425_mb : Scalar.QComplex := ((-1423862289208961130123019 : Int)/10^30,(-431475152540070057227737802 : Int)/10^30)
theorem v4425_mb_checked : Scalar.distance (sourceCoefficient 71 95 3 1) v4425_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4425_mg : Scalar.QComplex := ((-93085920988887476012480 : Int)/10^30,(307182306494585436890 : Int)/10^30)
theorem v4425_mg_checked : Scalar.distance (sourceCoefficient 71 95 3 2) v4425_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4425_upper : Scalar.QComplex := ((999991335020059578563922680561 : Int)/10^30,(-4162917822749508017096188124 : Int)/10^30)
theorem v4425_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 95 5) 1) 14) v4425_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4425 : Material (71 : Basis) (95 : Basis) where
  plus := ![v4425_pa,v4425_pb,v4425_pg]
  minus := ![(Primitive.Addresses.material4425 1).one,v4425_mb,v4425_mg]
  upper := v4425_upper
  lower := (Primitive.Addresses.material4425 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4425_pa_checked.trans (by decide +kernel)
    · exact v4425_pb_checked.trans (by decide +kernel)
    · exact v4425_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 95 Primitive.Addresses.material4425
    · exact v4425_mb_checked.trans (by decide +kernel)
    · exact v4425_mg_checked.trans (by decide +kernel)
  upper_error := v4425_upper_checked
  lower_error := reuse_lower_error 71 95 Primitive.Addresses.material4425

def v4426_pa : Scalar.QComplex := ((999996978421886848057464120925 : Int)/10^30,(-2458281329785016935563408624 : Int)/10^30)
theorem v4426_pa_checked : Scalar.distance (sourceCoefficient 71 96 1 0) v4426_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4426_pb : Scalar.QComplex := ((-1060693083180812295798027 : Int)/10^30,(-431476196545237342695645056 : Int)/10^30)
theorem v4426_pb_checked : Scalar.distance (sourceCoefficient 71 96 1 1) v4426_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4426_pg : Scalar.QComplex := ((-93086146394824985981387 : Int)/10^30,(228832627179690987860 : Int)/10^30)
theorem v4426_pg_checked : Scalar.distance (sourceCoefficient 71 96 1 2) v4426_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4426_mb : Scalar.QComplex := ((-1433037212888334413928676 : Int)/10^30,(-431475120556570990613023751 : Int)/10^30)
theorem v4426_mb_checked : Scalar.distance (sourceCoefficient 71 96 3 1) v4426_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4426_mg : Scalar.QComplex := ((-93085914262347419003011 : Int)/10^30,(309161693869176912862 : Int)/10^30)
theorem v4426_mg_checked : Scalar.distance (sourceCoefficient 71 96 3 2) v4426_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4426_upper : Scalar.QComplex := ((999991246273293716624820666931 : Int)/10^30,(-4184181734202698569478156627 : Int)/10^30)
theorem v4426_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 96 5) 1) 14) v4426_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4426 : Material (71 : Basis) (96 : Basis) where
  plus := ![v4426_pa,v4426_pb,v4426_pg]
  minus := ![(Primitive.Addresses.material4426 1).one,v4426_mb,v4426_mg]
  upper := v4426_upper
  lower := (Primitive.Addresses.material4426 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4426_pa_checked.trans (by decide +kernel)
    · exact v4426_pb_checked.trans (by decide +kernel)
    · exact v4426_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 96 Primitive.Addresses.material4426
    · exact v4426_mb_checked.trans (by decide +kernel)
    · exact v4426_mg_checked.trans (by decide +kernel)
  upper_error := v4426_upper_checked
  lower_error := reuse_lower_error 71 96 Primitive.Addresses.material4426

def v4427_pa : Scalar.QComplex := ((999996795892212046865534472585 : Int)/10^30,(-2531443325377748232618172680 : Int)/10^30)
theorem v4427_pa_checked : Scalar.distance (sourceCoefficient 71 97 1 0) v4427_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4427_pb : Scalar.QComplex := ((-1092260822885174243685096 : Int)/10^30,(-431476111755642731036218077 : Int)/10^30)
theorem v4427_pb_checked : Scalar.distance (sourceCoefficient 71 97 1 1) v4427_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4427_pg : Scalar.QComplex := ((-93086128753105648016281 : Int)/10^30,(235643014342920419212 : Int)/10^30)
theorem v4427_pg_checked : Scalar.distance (sourceCoefficient 71 97 1 2) v4427_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4427_mb : Scalar.QComplex := ((-1464604867668982784625026 : Int)/10^30,(-431475008525470343348524120 : Int)/10^30)
theorem v4427_mb_checked : Scalar.distance (sourceCoefficient 71 97 3 1) v4427_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4427_mg : Scalar.QComplex := ((-93085890743577256440817 : Int)/10^30,(315972063272578718154 : Int)/10^30)
theorem v4427_mg_checked : Scalar.distance (sourceCoefficient 71 97 3 2) v4427_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4427_upper : Scalar.QComplex := ((999990937472923583281024039630 : Int)/10^30,(-4257343305799571898761596682 : Int)/10^30)
theorem v4427_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 97 5) 1) 14) v4427_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4427 : Material (71 : Basis) (97 : Basis) where
  plus := ![v4427_pa,v4427_pb,v4427_pg]
  minus := ![(Primitive.Addresses.material4427 1).one,v4427_mb,v4427_mg]
  upper := v4427_upper
  lower := (Primitive.Addresses.material4427 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4427_pa_checked.trans (by decide +kernel)
    · exact v4427_pb_checked.trans (by decide +kernel)
    · exact v4427_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 97 Primitive.Addresses.material4427
    · exact v4427_mb_checked.trans (by decide +kernel)
    · exact v4427_mg_checked.trans (by decide +kernel)
  upper_error := v4427_upper_checked
  lower_error := reuse_lower_error 71 97 Primitive.Addresses.material4427

def v4428_pa : Scalar.QComplex := ((999998032303839324449764801400 : Int)/10^30,(-1983781351238820304355043241 : Int)/10^30)
theorem v4428_pa_checked : Scalar.distance (sourceCoefficient 72 73 1 0) v4428_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4428_pb : Scalar.QComplex := ((-855957059627112339816958 : Int)/10^30,(-431476671977569678389015998 : Int)/10^30)
theorem v4428_pb_checked : Scalar.distance (sourceCoefficient 72 73 1 1) v4428_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4428_pg : Scalar.QComplex := ((-93086246730472647246947 : Int)/10^30,(184663123681646733530 : Int)/10^30)
theorem v4428_pg_checked : Scalar.distance (sourceCoefficient 72 73 1 2) v4428_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4428_mb : Scalar.QComplex := ((-1228301675843903053837597 : Int)/10^30,(-431475772666693659761368044 : Int)/10^30)
theorem v4428_mb_checked : Scalar.distance (sourceCoefficient 72 73 3 1) v4428_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4428_mg : Scalar.QComplex := ((-93086052714249918943072 : Int)/10^30,(264992293402602438740 : Int)/10^30)
theorem v4428_mg_checked : Scalar.distance (sourceCoefficient 72 73 3 2) v4428_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4428_upper : Scalar.QComplex := ((999993119097593228587508969513 : Int)/10^30,(-3709684281273123850289378569 : Int)/10^30)
theorem v4428_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 73 5) 1) 14) v4428_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4428 : Material (72 : Basis) (73 : Basis) where
  plus := ![v4428_pa,v4428_pb,v4428_pg]
  minus := ![(Primitive.Addresses.material4428 1).one,v4428_mb,v4428_mg]
  upper := v4428_upper
  lower := (Primitive.Addresses.material4428 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4428_pa_checked.trans (by decide +kernel)
    · exact v4428_pb_checked.trans (by decide +kernel)
    · exact v4428_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 73 Primitive.Addresses.material4428
    · exact v4428_mb_checked.trans (by decide +kernel)
    · exact v4428_mg_checked.trans (by decide +kernel)
  upper_error := v4428_upper_checked
  lower_error := reuse_lower_error 72 73 Primitive.Addresses.material4428

def v4429_pa : Scalar.QComplex := ((999998011153421457799424792032 : Int)/10^30,(-1994414500943494486855203058 : Int)/10^30)
theorem v4429_pa_checked : Scalar.distance (sourceCoefficient 72 74 1 0) v4429_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4429_pb : Scalar.QComplex := ((-860545024657007115479961 : Int)/10^30,(-431476662829057496469179682 : Int)/10^30)
theorem v4429_pb_checked : Scalar.distance (sourceCoefficient 72 74 1 1) v4429_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4429_pg : Scalar.QComplex := ((-93086244759219817046083 : Int)/10^30,(185652925621349288907 : Int)/10^30)
theorem v4429_pg_checked : Scalar.distance (sourceCoefficient 72 74 1 2) v4429_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4429_mb : Scalar.QComplex := ((-1232889631270734789206933 : Int)/10^30,(-431475759558977697725854958 : Int)/10^30)
theorem v4429_mb_checked : Scalar.distance (sourceCoefficient 72 74 3 1) v4429_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4429_mg : Scalar.QComplex := ((-93086049888843327790935 : Int)/10^30,(265982093272654085250 : Int)/10^30)
theorem v4429_mg_checked : Scalar.distance (sourceCoefficient 72 74 3 2) v4429_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4429_upper : Scalar.QComplex := ((999993079595355104538357629751 : Int)/10^30,(-3720317378637268118265074829 : Int)/10^30)
theorem v4429_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 74 5) 1) 14) v4429_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4429 : Material (72 : Basis) (74 : Basis) where
  plus := ![v4429_pa,v4429_pb,v4429_pg]
  minus := ![(Primitive.Addresses.material4429 1).one,v4429_mb,v4429_mg]
  upper := v4429_upper
  lower := (Primitive.Addresses.material4429 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4429_pa_checked.trans (by decide +kernel)
    · exact v4429_pb_checked.trans (by decide +kernel)
    · exact v4429_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 74 Primitive.Addresses.material4429
    · exact v4429_mb_checked.trans (by decide +kernel)
    · exact v4429_mg_checked.trans (by decide +kernel)
  upper_error := v4429_upper_checked
  lower_error := reuse_lower_error 72 74 Primitive.Addresses.material4429

def v4430_pa : Scalar.QComplex := ((999997981496169660537679352106 : Int)/10^30,(-2009229600200338365056627823 : Int)/10^30)
theorem v4430_pa_checked : Scalar.distance (sourceCoefficient 72 75 1 0) v4430_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4430_pb : Scalar.QComplex := ((-866937406839605485216527 : Int)/10^30,(-431476649974043677385682832 : Int)/10^30)
theorem v4430_pb_checked : Scalar.distance (sourceCoefficient 72 75 1 1) v4430_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4430_pg : Scalar.QComplex := ((-93086241992213533611796 : Int)/10^30,(187032010306996347545 : Int)/10^30)
theorem v4430_pg_checked : Scalar.distance (sourceCoefficient 72 75 1 2) v4430_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4430_mb : Scalar.QComplex := ((-1239281999979859168525101 : Int)/10^30,(-431475741187630743775184999 : Int)/10^30)
theorem v4430_mb_checked : Scalar.distance (sourceCoefficient 72 75 3 1) v4430_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4430_mg : Scalar.QComplex := ((-93086045931750102594682 : Int)/10^30,(267361175057003086872 : Int)/10^30)
theorem v4430_mg_checked : Scalar.distance (sourceCoefficient 72 75 3 2) v4430_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4430_upper : Scalar.QComplex := ((999993024368630176262554386444 : Int)/10^30,(-3735132404643035839998287311 : Int)/10^30)
theorem v4430_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 75 5) 1) 14) v4430_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4430 : Material (72 : Basis) (75 : Basis) where
  plus := ![v4430_pa,v4430_pb,v4430_pg]
  minus := ![(Primitive.Addresses.material4430 1).one,v4430_mb,v4430_mg]
  upper := v4430_upper
  lower := (Primitive.Addresses.material4430 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4430_pa_checked.trans (by decide +kernel)
    · exact v4430_pb_checked.trans (by decide +kernel)
    · exact v4430_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 75 Primitive.Addresses.material4430
    · exact v4430_mb_checked.trans (by decide +kernel)
    · exact v4430_mg_checked.trans (by decide +kernel)
  upper_error := v4430_upper_checked
  lower_error := reuse_lower_error 72 75 Primitive.Addresses.material4430

def v4431_pa : Scalar.QComplex := ((999997956443819493753919628588 : Int)/10^30,(-2021659759922680282131112428 : Int)/10^30)
theorem v4431_pa_checked : Scalar.distance (sourceCoefficient 72 76 1 0) v4431_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4431_pb : Scalar.QComplex := ((-872300741192560809939075 : Int)/10^30,(-431476639091016748388741575 : Int)/10^30)
theorem v4431_pb_checked : Scalar.distance (sourceCoefficient 72 76 1 1) v4431_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4431_pg : Scalar.QComplex := ((-93086239652251190191805 : Int)/10^30,(188189089482452138544 : Int)/10^30)
theorem v4431_pg_checked : Scalar.distance (sourceCoefficient 72 76 1 2) v4431_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4431_mb : Scalar.QComplex := ((-1244645322944237910766626 : Int)/10^30,(-431475725676291876038394357 : Int)/10^30)
theorem v4431_mb_checked : Scalar.distance (sourceCoefficient 72 76 3 1) v4431_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4431_mg : Scalar.QComplex := ((-93086042593281414942806 : Int)/10^30,(268518251782343305338 : Int)/10^30)
theorem v4431_mg_checked : Scalar.distance (sourceCoefficient 72 76 3 2) v4431_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4431_upper : Scalar.QComplex := ((999992977862989296530614653983 : Int)/10^30,(-3747562502614031343360112359 : Int)/10^30)
theorem v4431_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 76 5) 1) 14) v4431_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4431 : Material (72 : Basis) (76 : Basis) where
  plus := ![v4431_pa,v4431_pb,v4431_pg]
  minus := ![(Primitive.Addresses.material4431 1).one,v4431_mb,v4431_mg]
  upper := v4431_upper
  lower := (Primitive.Addresses.material4431 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4431_pa_checked.trans (by decide +kernel)
    · exact v4431_pb_checked.trans (by decide +kernel)
    · exact v4431_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 76 Primitive.Addresses.material4431
    · exact v4431_mb_checked.trans (by decide +kernel)
    · exact v4431_mg_checked.trans (by decide +kernel)
  upper_error := v4431_upper_checked
  lower_error := reuse_lower_error 72 76 Primitive.Addresses.material4431

def v4432_pa : Scalar.QComplex := ((999997950621961929663467295339 : Int)/10^30,(-2024537447465551361859015578 : Int)/10^30)
theorem v4432_pa_checked : Scalar.distance (sourceCoefficient 72 77 1 0) v4432_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4432_pb : Scalar.QComplex := ((-873542398638446474816392 : Int)/10^30,(-431476636558832120303491930 : Int)/10^30)
theorem v4432_pb_checked : Scalar.distance (sourceCoefficient 72 77 1 1) v4432_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4432_pg : Scalar.QComplex := ((-93086239108138022983355 : Int)/10^30,(188456963137719111234 : Int)/10^30)
theorem v4432_pg_checked : Scalar.distance (sourceCoefficient 72 77 1 2) v4432_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4432_mb : Scalar.QComplex := ((-1245886977742636473316612 : Int)/10^30,(-431475722072613737177313472 : Int)/10^30)
theorem v4432_mb_checked : Scalar.distance (sourceCoefficient 72 77 3 1) v4432_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4432_mg : Scalar.QComplex := ((-93086041818005550418733 : Int)/10^30,(268786124868323516388 : Int)/10^30)
theorem v4432_mg_checked : Scalar.distance (sourceCoefficient 72 77 3 2) v4432_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4432_upper : Scalar.QComplex := ((999992967074512766192223588365 : Int)/10^30,(-3750440175822926864078501445 : Int)/10^30)
theorem v4432_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 77 5) 1) 14) v4432_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4432 : Material (72 : Basis) (77 : Basis) where
  plus := ![v4432_pa,v4432_pb,v4432_pg]
  minus := ![(Primitive.Addresses.material4432 1).one,v4432_mb,v4432_mg]
  upper := v4432_upper
  lower := (Primitive.Addresses.material4432 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4432_pa_checked.trans (by decide +kernel)
    · exact v4432_pb_checked.trans (by decide +kernel)
    · exact v4432_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 77 Primitive.Addresses.material4432
    · exact v4432_mb_checked.trans (by decide +kernel)
    · exact v4432_mg_checked.trans (by decide +kernel)
  upper_error := v4432_upper_checked
  lower_error := reuse_lower_error 72 77 Primitive.Addresses.material4432

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
