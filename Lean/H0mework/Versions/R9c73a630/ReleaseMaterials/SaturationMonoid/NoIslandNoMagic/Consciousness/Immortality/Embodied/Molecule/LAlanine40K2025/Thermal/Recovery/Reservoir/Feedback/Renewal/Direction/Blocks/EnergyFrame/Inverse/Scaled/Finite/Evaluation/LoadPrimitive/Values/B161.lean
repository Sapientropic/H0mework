import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B107
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B108

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2577_pa : Scalar.QComplex := ((999999344575643752317139446400 : Int)/10^30,(-1144922828366296030514439728 : Int)/10^30)
theorem v2577_pa_checked : Scalar.distance (sourceCoefficient 31 67 1 0) v2577_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2577_pb : Scalar.QComplex := ((-494008438080025144532707 : Int)/10^30,(-431477215804814264391801915 : Int)/10^30)
theorem v2577_pb_checked : Scalar.distance (sourceCoefficient 31 67 1 1) v2577_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2577_pg : Scalar.QComplex := ((-93086366470131888494334 : Int)/10^30,(106576775834339638017 : Int)/10^30)
theorem v2577_pg_checked : Scalar.distance (sourceCoefficient 31 67 1 2) v2577_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2577_mb : Scalar.QComplex := ((-866353658365248537573271 : Int)/10^30,(-431476628839094588391011244 : Int)/10^30)
theorem v2577_mb_checked : Scalar.distance (sourceCoefficient 31 67 3 1) v2577_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2577_mg : Scalar.QComplex := ((-93086239838865889314600 : Int)/10^30,(186906077960344420311 : Int)/10^30)
theorem v2577_mg_checked : Scalar.distance (sourceCoefficient 31 67 3 2) v2577_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2577_upper : Scalar.QComplex := ((999995879161153009000024345613 : Int)/10^30,(-2870829272643916225328922565 : Int)/10^30)
theorem v2577_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 67 5) 1) 14) v2577_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2577 : Material (31 : Basis) (67 : Basis) where
  plus := ![v2577_pa,v2577_pb,v2577_pg]
  minus := ![(Primitive.Addresses.material2577 1).one,v2577_mb,v2577_mg]
  upper := v2577_upper
  lower := (Primitive.Addresses.material2577 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2577_pa_checked.trans (by decide +kernel)
    · exact v2577_pb_checked.trans (by decide +kernel)
    · exact v2577_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 67 Primitive.Addresses.material2577
    · exact v2577_mb_checked.trans (by decide +kernel)
    · exact v2577_mg_checked.trans (by decide +kernel)
  upper_error := v2577_upper_checked
  lower_error := reuse_lower_error 31 67 Primitive.Addresses.material2577

def v2578_pa : Scalar.QComplex := ((999999287085293908676938975993 : Int)/10^30,(-1194080777809972100871705361 : Int)/10^30)
theorem v2578_pa_checked : Scalar.distance (sourceCoefficient 31 68 1 0) v2578_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2578_pb : Scalar.QComplex := ((-515218982223807700258901 : Int)/10^30,(-431477186879739821795353669 : Int)/10^30)
theorem v2578_pb_checked : Scalar.distance (sourceCoefficient 31 68 1 1) v2578_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2578_pg : Scalar.QComplex := ((-93086360674216178323889 : Int)/10^30,(111152713199771515265 : Int)/10^30)
theorem v2578_pg_checked : Scalar.distance (sourceCoefficient 31 68 1 2) v2578_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2578_mb : Scalar.QComplex := ((-887564169650339631846301 : Int)/10^30,(-431476581610286607283672649 : Int)/10^30)
theorem v2578_mb_checked : Scalar.distance (sourceCoefficient 31 68 3 1) v2578_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2578_mg : Scalar.QComplex := ((-93086230094124483429173 : Int)/10^30,(191482008620331466217 : Int)/10^30)
theorem v2578_mg_checked : Scalar.distance (sourceCoefficient 31 68 3 2) v2578_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2578_upper : Scalar.QComplex := ((999995736828727625034974984891 : Int)/10^30,(-2919987049649472751382428054 : Int)/10^30)
theorem v2578_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 68 5) 1) 14) v2578_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2578 : Material (31 : Basis) (68 : Basis) where
  plus := ![v2578_pa,v2578_pb,v2578_pg]
  minus := ![(Primitive.Addresses.material2578 1).one,v2578_mb,v2578_mg]
  upper := v2578_upper
  lower := (Primitive.Addresses.material2578 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2578_pa_checked.trans (by decide +kernel)
    · exact v2578_pb_checked.trans (by decide +kernel)
    · exact v2578_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 68 Primitive.Addresses.material2578
    · exact v2578_mb_checked.trans (by decide +kernel)
    · exact v2578_mg_checked.trans (by decide +kernel)
  upper_error := v2578_upper_checked
  lower_error := reuse_lower_error 31 68 Primitive.Addresses.material2578

def v2579_pa : Scalar.QComplex := ((999999261016848420966057098280 : Int)/10^30,(-1215716149872974899653116893 : Int)/10^30)
theorem v2579_pa_checked : Scalar.distance (sourceCoefficient 31 69 1 0) v2579_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2579_pb : Scalar.QComplex := ((-524554156015861828320316 : Int)/10^30,(-431477173708671117946576998 : Int)/10^30)
theorem v2579_pb_checked : Scalar.distance (sourceCoefficient 31 69 1 1) v2579_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2579_pg : Scalar.QComplex := ((-93086358040151831462494 : Int)/10^30,(113166672430534872419 : Int)/10^30)
theorem v2579_pg_checked : Scalar.distance (sourceCoefficient 31 69 1 2) v2579_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2579_mb : Scalar.QComplex := ((-896899328600442830099496 : Int)/10^30,(-431476560383388265703114144 : Int)/10^30)
theorem v2579_mb_checked : Scalar.distance (sourceCoefficient 31 69 3 1) v2579_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2579_mg : Scalar.QComplex := ((-93086225722105006558153 : Int)/10^30,(193495964828126861787 : Int)/10^30)
theorem v2579_mg_checked : Scalar.distance (sourceCoefficient 31 69 3 2) v2579_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2579_upper : Scalar.QComplex := ((999995673419631528090029861776 : Int)/10^30,(-2941622344497358330764167260 : Int)/10^30)
theorem v2579_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 69 5) 1) 14) v2579_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2579 : Material (31 : Basis) (69 : Basis) where
  plus := ![v2579_pa,v2579_pb,v2579_pg]
  minus := ![(Primitive.Addresses.material2579 1).one,v2579_mb,v2579_mg]
  upper := v2579_upper
  lower := (Primitive.Addresses.material2579 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2579_pa_checked.trans (by decide +kernel)
    · exact v2579_pb_checked.trans (by decide +kernel)
    · exact v2579_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 69 Primitive.Addresses.material2579
    · exact v2579_mb_checked.trans (by decide +kernel)
    · exact v2579_mg_checked.trans (by decide +kernel)
  upper_error := v2579_upper_checked
  lower_error := reuse_lower_error 31 69 Primitive.Addresses.material2579

def v2580_pa : Scalar.QComplex := ((999999243613542955311422847173 : Int)/10^30,(-1229948105396688984098143355 : Int)/10^30)
theorem v2580_pa_checked : Scalar.distance (sourceCoefficient 31 70 1 0) v2580_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2580_pb : Scalar.QComplex := ((-530694922898411879873279 : Int)/10^30,(-431477164897780088806671586 : Int)/10^30)
theorem v2580_pb_checked : Scalar.distance (sourceCoefficient 31 70 1 1) v2580_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2580_pg : Scalar.QComplex := ((-93086356279720644773261 : Int)/10^30,(114491474144324078923 : Int)/10^30)
theorem v2580_pg_checked : Scalar.distance (sourceCoefficient 31 70 1 2) v2580_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2580_mb : Scalar.QComplex := ((-903040085593102594021577 : Int)/10^30,(-431476546273295267493555755 : Int)/10^30)
theorem v2580_mb_checked : Scalar.distance (sourceCoefficient 31 70 3 1) v2580_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2580_mg : Scalar.QComplex := ((-93086222818430263212072 : Int)/10^30,(194820764529459016582 : Int)/10^30)
theorem v2580_mg_checked : Scalar.distance (sourceCoefficient 31 70 3 2) v2580_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2580_upper : Scalar.QComplex := ((999995631453287861603531781688 : Int)/10^30,(-2955854248787720047389546550 : Int)/10^30)
theorem v2580_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 70 5) 1) 14) v2580_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2580 : Material (31 : Basis) (70 : Basis) where
  plus := ![v2580_pa,v2580_pb,v2580_pg]
  minus := ![(Primitive.Addresses.material2580 1).one,v2580_mb,v2580_mg]
  upper := v2580_upper
  lower := (Primitive.Addresses.material2580 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2580_pa_checked.trans (by decide +kernel)
    · exact v2580_pb_checked.trans (by decide +kernel)
    · exact v2580_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 70 Primitive.Addresses.material2580
    · exact v2580_mb_checked.trans (by decide +kernel)
    · exact v2580_mg_checked.trans (by decide +kernel)
  upper_error := v2580_upper_checked
  lower_error := reuse_lower_error 31 70 Primitive.Addresses.material2580

def v2581_pa : Scalar.QComplex := ((999999213439569076517084828760 : Int)/10^30,(-1254240903164003153539493830 : Int)/10^30)
theorem v2581_pa_checked : Scalar.distance (sourceCoefficient 31 71 1 0) v2581_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2581_pb : Scalar.QComplex := ((-541176715463446818047895 : Int)/10^30,(-431477149589095073668811888 : Int)/10^30)
theorem v2581_pb_checked : Scalar.distance (sourceCoefficient 31 71 1 1) v2581_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2581_pg : Scalar.QComplex := ((-93086353223988449559609 : Int)/10^30,(116752803573034179648 : Int)/10^30)
theorem v2581_pg_checked : Scalar.distance (sourceCoefficient 31 71 1 2) v2581_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2581_mb : Scalar.QComplex := ((-913521861044581428162827 : Int)/10^30,(-431476521919301051266223287 : Int)/10^30)
theorem v2581_mb_checked : Scalar.distance (sourceCoefficient 31 71 3 1) v2581_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2581_mg : Scalar.QComplex := ((-93086217811273755307102 : Int)/10^30,(197082090479213563738 : Int)/10^30)
theorem v2581_mg_checked : Scalar.distance (sourceCoefficient 31 71 3 2) v2581_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2581_upper : Scalar.QComplex := ((999995559352193802412657294976 : Int)/10^30,(-2980146958296224021627101073 : Int)/10^30)
theorem v2581_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 71 5) 1) 14) v2581_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2581 : Material (31 : Basis) (71 : Basis) where
  plus := ![v2581_pa,v2581_pb,v2581_pg]
  minus := ![(Primitive.Addresses.material2581 1).one,v2581_mb,v2581_mg]
  upper := v2581_upper
  lower := (Primitive.Addresses.material2581 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2581_pa_checked.trans (by decide +kernel)
    · exact v2581_pb_checked.trans (by decide +kernel)
    · exact v2581_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 71 Primitive.Addresses.material2581
    · exact v2581_mb_checked.trans (by decide +kernel)
    · exact v2581_mg_checked.trans (by decide +kernel)
  upper_error := v2581_upper_checked
  lower_error := reuse_lower_error 31 71 Primitive.Addresses.material2581

def v2582_pa : Scalar.QComplex := ((999999180026991264150131108286 : Int)/10^30,(-1280603508161665424094389872 : Int)/10^30)
theorem v2582_pa_checked : Scalar.distance (sourceCoefficient 31 72 1 0) v2582_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2582_pb : Scalar.QComplex := ((-552551582766156486828462 : Int)/10^30,(-431477132591938636700696827 : Int)/10^30)
theorem v2582_pb_checked : Scalar.distance (sourceCoefficient 31 72 1 1) v2582_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2582_pg : Scalar.QComplex := ((-93086349835386840541257 : Int)/10^30,(119206803907522116593 : Int)/10^30)
theorem v2582_pg_checked : Scalar.distance (sourceCoefficient 31 72 1 2) v2582_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2582_mb : Scalar.QComplex := ((-924896709444127661432257 : Int)/10^30,(-431476495106152765883472277 : Int)/10^30)
theorem v2582_mb_checked : Scalar.distance (sourceCoefficient 31 72 3 1) v2582_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2582_mg : Scalar.QComplex := ((-93086212304981643429126 : Int)/10^30,(199536086975754451166 : Int)/10^30)
theorem v2582_mg_checked : Scalar.distance (sourceCoefficient 31 72 3 2) v2582_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2582_upper : Scalar.QComplex := ((999995480440201125033617643949 : Int)/10^30,(-3006509466362804778518847683 : Int)/10^30)
theorem v2582_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 72 5) 1) 14) v2582_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2582 : Material (31 : Basis) (72 : Basis) where
  plus := ![v2582_pa,v2582_pb,v2582_pg]
  minus := ![(Primitive.Addresses.material2582 1).one,v2582_mb,v2582_mg]
  upper := v2582_upper
  lower := (Primitive.Addresses.material2582 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2582_pa_checked.trans (by decide +kernel)
    · exact v2582_pb_checked.trans (by decide +kernel)
    · exact v2582_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 72 Primitive.Addresses.material2582
    · exact v2582_mb_checked.trans (by decide +kernel)
    · exact v2582_mg_checked.trans (by decide +kernel)
  upper_error := v2582_upper_checked
  lower_error := reuse_lower_error 31 72 Primitive.Addresses.material2582

def v2583_pa : Scalar.QComplex := ((999999167881097924877342259322 : Int)/10^30,(-1290053142986124476956369699 : Int)/10^30)
theorem v2583_pa_checked : Scalar.distance (sourceCoefficient 31 73 1 0) v2583_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2583_pb : Scalar.QComplex := ((-556628886222925130213900 : Int)/10^30,(-431477126401989188367305805 : Int)/10^30)
theorem v2583_pb_checked : Scalar.distance (sourceCoefficient 31 73 1 1) v2583_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2583_pg : Scalar.QComplex := ((-93086348602371873549322 : Int)/10^30,(120086436509785573589 : Int)/10^30)
theorem v2583_pg_checked : Scalar.distance (sourceCoefficient 31 73 1 2) v2583_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2583_mb : Scalar.QComplex := ((-928974006041082296951726 : Int)/10^30,(-431476485397676374090660091 : Int)/10^30)
theorem v2583_mb_checked : Scalar.distance (sourceCoefficient 31 73 3 1) v2583_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2583_mg : Scalar.QComplex := ((-93086210312883816973398 : Int)/10^30,(200415718186454105561 : Int)/10^30)
theorem v2583_mg_checked : Scalar.distance (sourceCoefficient 31 73 3 2) v2583_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2583_upper : Scalar.QComplex := ((999995451985113432800570236304 : Int)/10^30,(-3015959066150432755682643996 : Int)/10^30)
theorem v2583_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 73 5) 1) 14) v2583_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2583 : Material (31 : Basis) (73 : Basis) where
  plus := ![v2583_pa,v2583_pb,v2583_pg]
  minus := ![(Primitive.Addresses.material2583 1).one,v2583_mb,v2583_mg]
  upper := v2583_upper
  lower := (Primitive.Addresses.material2583 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2583_pa_checked.trans (by decide +kernel)
    · exact v2583_pb_checked.trans (by decide +kernel)
    · exact v2583_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 73 Primitive.Addresses.material2583
    · exact v2583_mb_checked.trans (by decide +kernel)
    · exact v2583_mg_checked.trans (by decide +kernel)
  upper_error := v2583_upper_checked
  lower_error := reuse_lower_error 31 73 Primitive.Addresses.material2583

def v2584_pa : Scalar.QComplex := ((999999154107210479307230278656 : Int)/10^30,(-1300686304804803492301530577 : Int)/10^30)
theorem v2584_pa_checked : Scalar.distance (sourceCoefficient 31 74 1 0) v2584_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2584_pb : Scalar.QComplex := ((-561216854737433680633809 : Int)/10^30,(-431477119375348330134432483 : Int)/10^30)
theorem v2584_pb_checked : Scalar.distance (sourceCoefficient 31 74 1 1) v2584_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2584_pg : Scalar.QComplex := ((-93086347203331438730185 : Int)/10^30,(121076239389196004446 : Int)/10^30)
theorem v2584_pg_checked : Scalar.distance (sourceCoefficient 31 74 1 2) v2584_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2584_mb : Scalar.QComplex := ((-933561966783605896401996 : Int)/10^30,(-431476474411827938607695443 : Int)/10^30)
theorem v2584_mb_checked : Scalar.distance (sourceCoefficient 31 74 3 1) v2584_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2584_mg : Scalar.QComplex := ((-93086208059688597216589 : Int)/10^30,(201405519490006803381 : Int)/10^30)
theorem v2584_mg_checked : Scalar.distance (sourceCoefficient 31 74 3 2) v2584_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2584_upper : Scalar.QComplex := ((999995419859373835682725301630 : Int)/10^30,(-3026592188359786127288280567 : Int)/10^30)
theorem v2584_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 74 5) 1) 14) v2584_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2584 : Material (31 : Basis) (74 : Basis) where
  plus := ![v2584_pa,v2584_pb,v2584_pg]
  minus := ![(Primitive.Addresses.material2584 1).one,v2584_mb,v2584_mg]
  upper := v2584_upper
  lower := (Primitive.Addresses.material2584 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2584_pa_checked.trans (by decide +kernel)
    · exact v2584_pb_checked.trans (by decide +kernel)
    · exact v2584_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 74 Primitive.Addresses.material2584
    · exact v2584_mb_checked.trans (by decide +kernel)
    · exact v2584_mg_checked.trans (by decide +kernel)
  upper_error := v2584_upper_checked
  lower_error := reuse_lower_error 31 74 Primitive.Addresses.material2584

def v2585_pa : Scalar.QComplex := ((999999134727631232233047374950 : Int)/10^30,(-1315501421070787651115203748 : Int)/10^30)
theorem v2585_pa_checked : Scalar.distance (sourceCoefficient 31 75 1 0) v2585_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2585_pb : Scalar.QComplex := ((-567609241812739729102752 : Int)/10^30,(-431477109476724221818519208 : Int)/10^30)
theorem v2585_pb_checked : Scalar.distance (sourceCoefficient 31 75 1 1) v2585_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2585_pg : Scalar.QComplex := ((-93086345233585017300646 : Int)/10^30,(122455325394276503047 : Int)/10^30)
theorem v2585_pg_checked : Scalar.distance (sourceCoefficient 31 75 1 2) v2585_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2585_mb : Scalar.QComplex := ((-939954342936667302216508 : Int)/10^30,(-431476458996865372439238683 : Int)/10^30)
theorem v2585_mb_checked : Scalar.distance (sourceCoefficient 31 75 3 1) v2585_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2585_mg : Scalar.QComplex := ((-93086204899853798557167 : Int)/10^30,(202784603281788107338 : Int)/10^30)
theorem v2585_mg_checked : Scalar.distance (sourceCoefficient 31 75 3 2) v2585_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2585_upper : Scalar.QComplex := ((999995374910276793975454131946 : Int)/10^30,(-3041407249112999234970685003 : Int)/10^30)
theorem v2585_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 75 5) 1) 14) v2585_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2585 : Material (31 : Basis) (75 : Basis) where
  plus := ![v2585_pa,v2585_pb,v2585_pg]
  minus := ![(Primitive.Addresses.material2585 1).one,v2585_mb,v2585_mg]
  upper := v2585_upper
  lower := (Primitive.Addresses.material2585 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2585_pa_checked.trans (by decide +kernel)
    · exact v2585_pb_checked.trans (by decide +kernel)
    · exact v2585_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 75 Primitive.Addresses.material2585
    · exact v2585_mb_checked.trans (by decide +kernel)
    · exact v2585_mg_checked.trans (by decide +kernel)
  upper_error := v2585_upper_checked
  lower_error := reuse_lower_error 31 75 Primitive.Addresses.material2585

def v2586_pa : Scalar.QComplex := ((999999118298450560409497500660 : Int)/10^30,(-1327931595181603742846048384 : Int)/10^30)
theorem v2586_pa_checked : Scalar.distance (sourceCoefficient 31 76 1 0) v2586_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2586_pb : Scalar.QComplex := ((-572972580304563735526961 : Int)/10^30,(-431477101074166428042166898 : Int)/10^30)
theorem v2586_pb_checked : Scalar.distance (sourceCoefficient 31 76 1 1) v2586_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2586_pg : Scalar.QComplex := ((-93086343562539384715985 : Int)/10^30,(123612405685875358987 : Int)/10^30)
theorem v2586_pg_checked : Scalar.distance (sourceCoefficient 31 76 1 2) v2586_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2586_mb : Scalar.QComplex := ((-945317672180446332582345 : Int)/10^30,(-431476445965991144673750323 : Int)/10^30)
theorem v2586_mb_checked : Scalar.distance (sourceCoefficient 31 76 3 1) v2586_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2586_mg : Scalar.QComplex := ((-93086202230300609491163 : Int)/10^30,(203941681700515969715 : Int)/10^30)
theorem v2586_mg_checked : Scalar.distance (sourceCoefficient 31 76 3 2) v2586_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2586_upper : Scalar.QComplex := ((999995337027767732804596873827 : Int)/10^30,(-3053837376355255743522412385 : Int)/10^30)
theorem v2586_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 76 5) 1) 14) v2586_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2586 : Material (31 : Basis) (76 : Basis) where
  plus := ![v2586_pa,v2586_pb,v2586_pg]
  minus := ![(Primitive.Addresses.material2586 1).one,v2586_mb,v2586_mg]
  upper := v2586_upper
  lower := (Primitive.Addresses.material2586 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2586_pa_checked.trans (by decide +kernel)
    · exact v2586_pb_checked.trans (by decide +kernel)
    · exact v2586_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 76 Primitive.Addresses.material2586
    · exact v2586_mb_checked.trans (by decide +kernel)
    · exact v2586_mg_checked.trans (by decide +kernel)
  upper_error := v2586_upper_checked
  lower_error := reuse_lower_error 31 76 Primitive.Addresses.material2586

def v2587_pa : Scalar.QComplex := ((999999114472929974756371112280 : Int)/10^30,(-1330809286070808686210840100 : Int)/10^30)
theorem v2587_pa_checked : Scalar.distance (sourceCoefficient 31 77 1 0) v2587_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2587_pb : Scalar.QComplex := ((-574214238713027937274217 : Int)/10^30,(-431477099116231472127164850 : Int)/10^30)
theorem v2587_pb_checked : Scalar.distance (sourceCoefficient 31 77 1 1) v2587_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2587_pg : Scalar.QComplex := ((-93086343173286117412799 : Int)/10^30,(123880279600724222589 : Int)/10^30)
theorem v2587_pg_checked : Scalar.distance (sourceCoefficient 31 77 1 2) v2587_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2587_mb : Scalar.QComplex := ((-946559328436974677428068 : Int)/10^30,(-431476442936561633501595189 : Int)/10^30)
theorem v2587_mb_checked : Scalar.distance (sourceCoefficient 31 77 3 1) v2587_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2587_mg : Scalar.QComplex := ((-93086201609884363203454 : Int)/10^30,(204209555179715094010 : Int)/10^30)
theorem v2587_mg_checked : Scalar.distance (sourceCoefficient 31 77 3 2) v2587_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2587_upper : Scalar.QComplex := ((999995328235619432125436984757 : Int)/10^30,(-3056715056355976662413353475 : Int)/10^30)
theorem v2587_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 77 5) 1) 14) v2587_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2587 : Material (31 : Basis) (77 : Basis) where
  plus := ![v2587_pa,v2587_pb,v2587_pg]
  minus := ![(Primitive.Addresses.material2587 1).one,v2587_mb,v2587_mg]
  upper := v2587_upper
  lower := (Primitive.Addresses.material2587 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2587_pa_checked.trans (by decide +kernel)
    · exact v2587_pb_checked.trans (by decide +kernel)
    · exact v2587_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 77 Primitive.Addresses.material2587
    · exact v2587_mb_checked.trans (by decide +kernel)
    · exact v2587_mg_checked.trans (by decide +kernel)
  upper_error := v2587_upper_checked
  lower_error := reuse_lower_error 31 77 Primitive.Addresses.material2587

def v2588_pa : Scalar.QComplex := ((999999091300838191300146039190 : Int)/10^30,(-1348108859804442141285866542 : Int)/10^30)
theorem v2588_pa_checked : Scalar.distance (sourceCoefficient 31 78 1 0) v2588_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2588_pb : Scalar.QComplex := ((-581678612689100506340160 : Int)/10^30,(-431477087245470257478392848 : Int)/10^30)
theorem v2588_pb_checked : Scalar.distance (sourceCoefficient 31 78 1 1) v2588_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2588_pg : Scalar.QComplex := ((-93086340814290751875568 : Int)/10^30,(125490634811755880019 : Int)/10^30)
theorem v2588_pg_checked : Scalar.distance (sourceCoefficient 31 78 1 2) v2588_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2588_mb : Scalar.QComplex := ((-954023689389787387455367 : Int)/10^30,(-431476424624386280453302435 : Int)/10^30)
theorem v2588_mb_checked : Scalar.distance (sourceCoefficient 31 78 3 1) v2588_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2588_mg : Scalar.QComplex := ((-93086197861225856614039 : Int)/10^30,(205819907755431154252 : Int)/10^30)
theorem v2588_mg_checked : Scalar.distance (sourceCoefficient 31 78 3 2) v2588_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2588_upper : Scalar.QComplex := ((999995275206067301596190406387 : Int)/10^30,(-3074014564330998929422911861 : Int)/10^30)
theorem v2588_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 78 5) 1) 14) v2588_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2588 : Material (31 : Basis) (78 : Basis) where
  plus := ![v2588_pa,v2588_pb,v2588_pg]
  minus := ![(Primitive.Addresses.material2588 1).one,v2588_mb,v2588_mg]
  upper := v2588_upper
  lower := (Primitive.Addresses.material2588 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2588_pa_checked.trans (by decide +kernel)
    · exact v2588_pb_checked.trans (by decide +kernel)
    · exact v2588_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 78 Primitive.Addresses.material2588
    · exact v2588_mb_checked.trans (by decide +kernel)
    · exact v2588_mg_checked.trans (by decide +kernel)
  upper_error := v2588_upper_checked
  lower_error := reuse_lower_error 31 78 Primitive.Addresses.material2588

def v2589_pa : Scalar.QComplex := ((999999083766773886648565283248 : Int)/10^30,(-1353685935785468015421452801 : Int)/10^30)
theorem v2589_pa_checked : Scalar.distance (sourceCoefficient 31 79 1 0) v2589_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2589_pb : Scalar.QComplex := ((-584084994545819067386587 : Int)/10^30,(-431477083381847165227235517 : Int)/10^30)
theorem v2589_pb_checked : Scalar.distance (sourceCoefficient 31 79 1 1) v2589_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2589_pg : Scalar.QComplex := ((-93086340046864528958485 : Int)/10^30,(126009784789535736046 : Int)/10^30)
theorem v2589_pg_checked : Scalar.distance (sourceCoefficient 31 79 1 2) v2589_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2589_mb : Scalar.QComplex := ((-956430067016367288673373 : Int)/10^30,(-431476418684165463873074048 : Int)/10^30)
theorem v2589_mb_checked : Scalar.distance (sourceCoefficient 31 79 3 1) v2589_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2589_mg : Scalar.QComplex := ((-93086196645796870267828 : Int)/10^30,(206339056877653480443 : Int)/10^30)
theorem v2589_mg_checked : Scalar.distance (sourceCoefficient 31 79 3 2) v2589_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2589_upper : Scalar.QComplex := ((999995258046487023178466119060 : Int)/10^30,(-3079591619002513754331515759 : Int)/10^30)
theorem v2589_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 79 5) 1) 14) v2589_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2589 : Material (31 : Basis) (79 : Basis) where
  plus := ![v2589_pa,v2589_pb,v2589_pg]
  minus := ![(Primitive.Addresses.material2589 1).one,v2589_mb,v2589_mg]
  upper := v2589_upper
  lower := (Primitive.Addresses.material2589 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2589_pa_checked.trans (by decide +kernel)
    · exact v2589_pb_checked.trans (by decide +kernel)
    · exact v2589_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 79 Primitive.Addresses.material2589
    · exact v2589_mb_checked.trans (by decide +kernel)
    · exact v2589_mg_checked.trans (by decide +kernel)
  upper_error := v2589_upper_checked
  lower_error := reuse_lower_error 31 79 Primitive.Addresses.material2589

def v2590_pa : Scalar.QComplex := ((999999071935578137341472820783 : Int)/10^30,(-1362397879630523326618544836 : Int)/10^30)
theorem v2590_pa_checked : Scalar.distance (sourceCoefficient 31 80 1 0) v2590_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2590_pb : Scalar.QComplex := ((-587844000794345344131505 : Int)/10^30,(-431477077310677638943709299 : Int)/10^30)
theorem v2590_pb_checked : Scalar.distance (sourceCoefficient 31 80 1 1) v2590_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2590_pg : Scalar.QComplex := ((-93086338841309316330100 : Int)/10^30,(126820748357792743045 : Int)/10^30)
theorem v2590_pg_checked : Scalar.distance (sourceCoefficient 31 80 1 2) v2590_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2590_mb : Scalar.QComplex := ((-960189066626097878161936 : Int)/10^30,(-431476409369145105041997876 : Int)/10^30)
theorem v2590_mb_checked : Scalar.distance (sourceCoefficient 31 80 3 1) v2590_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2590_mg : Scalar.QComplex := ((-93086194740417071560211 : Int)/10^30,(207150019103611835806 : Int)/10^30)
theorem v2590_mg_checked : Scalar.distance (sourceCoefficient 31 80 3 2) v2590_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2590_upper : Scalar.QComplex := ((999995231179284159854000673061 : Int)/10^30,(-3088303529452581539521099974 : Int)/10^30)
theorem v2590_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 80 5) 1) 14) v2590_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2590 : Material (31 : Basis) (80 : Basis) where
  plus := ![v2590_pa,v2590_pb,v2590_pg]
  minus := ![(Primitive.Addresses.material2590 1).one,v2590_mb,v2590_mg]
  upper := v2590_upper
  lower := (Primitive.Addresses.material2590 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2590_pa_checked.trans (by decide +kernel)
    · exact v2590_pb_checked.trans (by decide +kernel)
    · exact v2590_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 80 Primitive.Addresses.material2590
    · exact v2590_mb_checked.trans (by decide +kernel)
    · exact v2590_mg_checked.trans (by decide +kernel)
  upper_error := v2590_upper_checked
  lower_error := reuse_lower_error 31 80 Primitive.Addresses.material2590

def v2591_pa : Scalar.QComplex := ((999999035852904747857655172633 : Int)/10^30,(-1388629994247806605583691064 : Int)/10^30)
theorem v2591_pa_checked : Scalar.distance (sourceCoefficient 31 81 1 0) v2591_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2591_pb : Scalar.QComplex := ((-599162563313681971137226 : Int)/10^30,(-431477058766393103779372593 : Int)/10^30)
theorem v2591_pb_checked : Scalar.distance (sourceCoefficient 31 81 1 1) v2591_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2591_pg : Scalar.QComplex := ((-93086335161545116085023 : Int)/10^30,(129262601688087734627 : Int)/10^30)
theorem v2591_pg_checked : Scalar.distance (sourceCoefficient 31 81 1 2) v2591_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2591_mb : Scalar.QComplex := ((-971507608928134045081583 : Int)/10^30,(-431476381057457789707151397 : Int)/10^30)
theorem v2591_mb_checked : Scalar.distance (sourceCoefficient 31 81 3 1) v2591_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2591_mg : Scalar.QComplex := ((-93086188953444794406400 : Int)/10^30,(209591868349222459925 : Int)/10^30)
theorem v2591_mg_checked : Scalar.distance (sourceCoefficient 31 81 3 2) v2591_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2591_upper : Scalar.QComplex := ((999995149822414440691112593275 : Int)/10^30,(-3114535542724790660995617058 : Int)/10^30)
theorem v2591_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 81 5) 1) 14) v2591_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2591 : Material (31 : Basis) (81 : Basis) where
  plus := ![v2591_pa,v2591_pb,v2591_pg]
  minus := ![(Primitive.Addresses.material2591 1).one,v2591_mb,v2591_mg]
  upper := v2591_upper
  lower := (Primitive.Addresses.material2591 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2591_pa_checked.trans (by decide +kernel)
    · exact v2591_pb_checked.trans (by decide +kernel)
    · exact v2591_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 81 Primitive.Addresses.material2591
    · exact v2591_mb_checked.trans (by decide +kernel)
    · exact v2591_mg_checked.trans (by decide +kernel)
  upper_error := v2591_upper_checked
  lower_error := reuse_lower_error 31 81 Primitive.Addresses.material2591

def v2592_pa : Scalar.QComplex := ((999999022000158757301933213526 : Int)/10^30,(-1398570243499305494511733179 : Int)/10^30)
theorem v2592_pa_checked : Scalar.distance (sourceCoefficient 31 82 1 0) v2592_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2592_pb : Scalar.QComplex := ((-603451555346305354796370 : Int)/10^30,(-431477051635897822983339926 : Int)/10^30)
theorem v2592_pb_checked : Scalar.distance (sourceCoefficient 31 82 1 1) v2592_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2592_pg : Scalar.QComplex := ((-93086333747631637663402 : Int)/10^30,(130187903779632026265 : Int)/10^30)
theorem v2592_pg_checked : Scalar.distance (sourceCoefficient 31 82 1 2) v2592_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2592_mb : Scalar.QComplex := ((-975796593210473396634719 : Int)/10^30,(-431476370225758208796789291 : Int)/10^30)
theorem v2592_mb_checked : Scalar.distance (sourceCoefficient 31 82 3 1) v2592_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2592_mg : Scalar.QComplex := ((-93086186741037811505852 : Int)/10^30,(210517168876090842908 : Int)/10^30)
theorem v2592_mg_checked : Scalar.distance (sourceCoefficient 31 82 3 2) v2592_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2592_upper : Scalar.QComplex := ((999995118813720646454040243708 : Int)/10^30,(-3124475753262873085117243641 : Int)/10^30)
theorem v2592_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 82 5) 1) 14) v2592_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2592 : Material (31 : Basis) (82 : Basis) where
  plus := ![v2592_pa,v2592_pb,v2592_pg]
  minus := ![(Primitive.Addresses.material2592 1).one,v2592_mb,v2592_mg]
  upper := v2592_upper
  lower := (Primitive.Addresses.material2592 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2592_pa_checked.trans (by decide +kernel)
    · exact v2592_pb_checked.trans (by decide +kernel)
    · exact v2592_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 82 Primitive.Addresses.material2592
    · exact v2592_mb_checked.trans (by decide +kernel)
    · exact v2592_mg_checked.trans (by decide +kernel)
  upper_error := v2592_upper_checked
  lower_error := reuse_lower_error 31 82 Primitive.Addresses.material2592

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
