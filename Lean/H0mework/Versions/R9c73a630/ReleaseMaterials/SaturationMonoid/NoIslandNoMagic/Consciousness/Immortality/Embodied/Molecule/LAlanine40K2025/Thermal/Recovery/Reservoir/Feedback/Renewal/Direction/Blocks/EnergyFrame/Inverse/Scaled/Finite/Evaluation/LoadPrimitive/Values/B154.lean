import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B102
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B103

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2465_pa : Scalar.QComplex := ((999998818302592787372999180631 : Int)/10^30,(-1537333216325104903115501546 : Int)/10^30)
theorem v2465_pa_checked : Scalar.distance (sourceCoefficient 29 88 1 0) v2465_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2465_pb : Scalar.QComplex := ((-663324618286898643800973 : Int)/10^30,(-431476941624633318638898293 : Int)/10^30)
theorem v2465_pb_checked : Scalar.distance (sourceCoefficient 29 88 1 1) v2465_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2465_pg : Scalar.QComplex := ((-93086312400044522875248 : Int)/10^30,(143104849144433135000 : Int)/10^30)
theorem v2465_pg_checked : Scalar.distance (sourceCoefficient 29 88 1 2) v2465_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2465_mb : Scalar.QComplex := ((-1035669538922822474878449 : Int)/10^30,(-431476208546777931594868293 : Int)/10^30)
theorem v2465_mb_checked : Scalar.distance (sourceCoefficient 29 88 3 1) v2465_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2465_mg : Scalar.QComplex := ((-93086154246716553200030 : Int)/10^30,(223434091009316638332 : Int)/10^30)
theorem v2465_mg_checked : Scalar.distance (sourceCoefficient 29 88 3 2) v2465_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2465_upper : Scalar.QComplex := ((999994675624155441350800751075 : Int)/10^30,(-3263238167854005148245679030 : Int)/10^30)
theorem v2465_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 88 5) 1) 14) v2465_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2465 : Material (29 : Basis) (88 : Basis) where
  plus := ![v2465_pa,v2465_pb,v2465_pg]
  minus := ![(Primitive.Addresses.material2465 1).one,v2465_mb,v2465_mg]
  upper := v2465_upper
  lower := (Primitive.Addresses.material2465 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2465_pa_checked.trans (by decide +kernel)
    · exact v2465_pb_checked.trans (by decide +kernel)
    · exact v2465_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 88 Primitive.Addresses.material2465
    · exact v2465_mb_checked.trans (by decide +kernel)
    · exact v2465_mg_checked.trans (by decide +kernel)
  upper_error := v2465_upper_checked
  lower_error := reuse_lower_error 29 88 Primitive.Addresses.material2465

def v2466_pa : Scalar.QComplex := ((999998793438258187709736638123 : Int)/10^30,(-1553422681639914681471833591 : Int)/10^30)
theorem v2466_pa_checked : Scalar.distance (sourceCoefficient 29 89 1 0) v2466_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2466_pb : Scalar.QComplex := ((-670266856214085141990042 : Int)/10^30,(-431476928602686732592087141 : Int)/10^30)
theorem v2466_pb_checked : Scalar.distance (sourceCoefficient 29 89 1 1) v2466_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2466_pg : Scalar.QComplex := ((-93086309838109073987947 : Int)/10^30,(144602559524595460506 : Int)/10^30)
theorem v2466_pg_checked : Scalar.distance (sourceCoefficient 29 89 1 2) v2466_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2466_mb : Scalar.QComplex := ((-1042611763027743099773391 : Int)/10^30,(-431476189533997529841459222 : Int)/10^30)
theorem v2466_mb_checked : Scalar.distance (sourceCoefficient 29 89 3 1) v2466_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2466_mg : Scalar.QComplex := ((-93086150392325454529794 : Int)/10^30,(224931798620978033457 : Int)/10^30)
theorem v2466_mg_checked : Scalar.distance (sourceCoefficient 29 89 3 2) v2466_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2466_upper : Scalar.QComplex := ((999994622990900365722872661941 : Int)/10^30,(-3279327566291860497349803806 : Int)/10^30)
theorem v2466_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 89 5) 1) 14) v2466_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2466 : Material (29 : Basis) (89 : Basis) where
  plus := ![v2466_pa,v2466_pb,v2466_pg]
  minus := ![(Primitive.Addresses.material2466 1).one,v2466_mb,v2466_mg]
  upper := v2466_upper
  lower := (Primitive.Addresses.material2466 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2466_pa_checked.trans (by decide +kernel)
    · exact v2466_pb_checked.trans (by decide +kernel)
    · exact v2466_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 89 Primitive.Addresses.material2466
    · exact v2466_mb_checked.trans (by decide +kernel)
    · exact v2466_mg_checked.trans (by decide +kernel)
  upper_error := v2466_upper_checked
  lower_error := reuse_lower_error 29 89 Primitive.Addresses.material2466

def v2467_pa : Scalar.QComplex := ((999998752390717596521803743628 : Int)/10^30,(-1579625591169640063827680955 : Int)/10^30)
theorem v2467_pa_checked : Scalar.distance (sourceCoefficient 29 90 1 0) v2467_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2467_pb : Scalar.QComplex := ((-681572814753637123584240 : Int)/10^30,(-431476907076691588635823433 : Int)/10^30)
theorem v2467_pb_checked : Scalar.distance (sourceCoefficient 29 90 1 1) v2467_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2467_pg : Scalar.QComplex := ((-93086305605628695398210 : Int)/10^30,(147041693972671308356 : Int)/10^30)
theorem v2467_pg_checked : Scalar.distance (sourceCoefficient 29 90 1 2) v2467_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2467_mb : Scalar.QComplex := ((-1053917698781605694858932 : Int)/10^30,(-431476158251477382833788402 : Int)/10^30)
theorem v2467_mb_checked : Scalar.distance (sourceCoefficient 29 90 3 1) v2467_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2467_mg : Scalar.QComplex := ((-93086144054983477734028 : Int)/10^30,(227370928508412709454 : Int)/10^30)
theorem v2467_mg_checked : Scalar.distance (sourceCoefficient 29 90 3 2) v2467_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2467_upper : Scalar.QComplex := ((999994536719576171102434782874 : Int)/10^30,(-3305530365951098888554764839 : Int)/10^30)
theorem v2467_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 90 5) 1) 14) v2467_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2467 : Material (29 : Basis) (90 : Basis) where
  plus := ![v2467_pa,v2467_pb,v2467_pg]
  minus := ![(Primitive.Addresses.material2467 1).one,v2467_mb,v2467_mg]
  upper := v2467_upper
  lower := (Primitive.Addresses.material2467 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2467_pa_checked.trans (by decide +kernel)
    · exact v2467_pb_checked.trans (by decide +kernel)
    · exact v2467_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 90 Primitive.Addresses.material2467
    · exact v2467_mb_checked.trans (by decide +kernel)
    · exact v2467_mg_checked.trans (by decide +kernel)
  upper_error := v2467_upper_checked
  lower_error := reuse_lower_error 29 90 Primitive.Addresses.material2467

def v2468_pa : Scalar.QComplex := ((999998728964807639419525958461 : Int)/10^30,(-1594386643568836702071423168 : Int)/10^30)
theorem v2468_pa_checked : Scalar.distance (sourceCoefficient 29 91 1 0) v2468_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2468_pb : Scalar.QComplex := ((-687941872438347007618693 : Int)/10^30,(-431476894776380126888565998 : Int)/10^30)
theorem v2468_pb_checked : Scalar.distance (sourceCoefficient 29 91 1 1) v2468_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2468_pg : Scalar.QComplex := ((-93086303188484490675998 : Int)/10^30,(148415747144556610281 : Int)/10^30)
theorem v2468_pg_checked : Scalar.distance (sourceCoefficient 29 91 1 2) v2468_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2468_mb : Scalar.QComplex := ((-1060286743480209516535491 : Int)/10^30,(-431476140454960570859693594 : Int)/10^30)
theorem v2468_mb_checked : Scalar.distance (sourceCoefficient 29 91 3 1) v2468_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2468_mg : Scalar.QComplex := ((-93086140452094170745637 : Int)/10^30,(228744979082788633613 : Int)/10^30)
theorem v2468_mg_checked : Scalar.distance (sourceCoefficient 29 91 3 2) v2468_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2468_upper : Scalar.QComplex := ((999994487817463775340924375521 : Int)/10^30,(-3320291355934446529205387224 : Int)/10^30)
theorem v2468_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 91 5) 1) 14) v2468_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2468 : Material (29 : Basis) (91 : Basis) where
  plus := ![v2468_pa,v2468_pb,v2468_pg]
  minus := ![(Primitive.Addresses.material2468 1).one,v2468_mb,v2468_mg]
  upper := v2468_upper
  lower := (Primitive.Addresses.material2468 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2468_pa_checked.trans (by decide +kernel)
    · exact v2468_pb_checked.trans (by decide +kernel)
    · exact v2468_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 91 Primitive.Addresses.material2468
    · exact v2468_mb_checked.trans (by decide +kernel)
    · exact v2468_mg_checked.trans (by decide +kernel)
  upper_error := v2468_upper_checked
  lower_error := reuse_lower_error 29 91 Primitive.Addresses.material2468

def v2469_pa : Scalar.QComplex := ((999998677503825568683898497430 : Int)/10^30,(-1626342706770778007518231464 : Int)/10^30)
theorem v2469_pa_checked : Scalar.distance (sourceCoefficient 29 92 1 0) v2469_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2469_pb : Scalar.QComplex := ((-701730184989144294615651 : Int)/10^30,(-431476867718116899220492235 : Int)/10^30)
theorem v2469_pb_checked : Scalar.distance (sourceCoefficient 29 92 1 1) v2469_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2469_pg : Scalar.QComplex := ((-93086297874566705237292 : Int)/10^30,(151390421861847493013 : Int)/10^30)
theorem v2469_pg_checked : Scalar.distance (sourceCoefficient 29 92 1 2) v2469_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2469_mb : Scalar.QComplex := ((-1074075027546925377316140 : Int)/10^30,(-431476101498014689426174387 : Int)/10^30)
theorem v2469_mb_checked : Scalar.distance (sourceCoefficient 29 92 3 1) v2469_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2469_mg : Scalar.QComplex := ((-93086132571168057275253 : Int)/10^30,(231719648106800450885 : Int)/10^30)
theorem v2469_mg_checked : Scalar.distance (sourceCoefficient 29 92 3 2) v2469_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2469_upper : Scalar.QComplex := ((999994381203292294550056013569 : Int)/10^30,(-3352247282724598967971409523 : Int)/10^30)
theorem v2469_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 92 5) 1) 14) v2469_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2469 : Material (29 : Basis) (92 : Basis) where
  plus := ![v2469_pa,v2469_pb,v2469_pg]
  minus := ![(Primitive.Addresses.material2469 1).one,v2469_mb,v2469_mg]
  upper := v2469_upper
  lower := (Primitive.Addresses.material2469 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2469_pa_checked.trans (by decide +kernel)
    · exact v2469_pb_checked.trans (by decide +kernel)
    · exact v2469_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 92 Primitive.Addresses.material2469
    · exact v2469_mb_checked.trans (by decide +kernel)
    · exact v2469_mg_checked.trans (by decide +kernel)
  upper_error := v2469_upper_checked
  lower_error := reuse_lower_error 29 92 Primitive.Addresses.material2469

def v2470_pa : Scalar.QComplex := ((999998615104608535148223013013 : Int)/10^30,(-1664268267135577590860399416 : Int)/10^30)
theorem v2470_pa_checked : Scalar.distance (sourceCoefficient 29 93 1 0) v2470_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2470_pb : Scalar.QComplex := ((-718094198718510687844648 : Int)/10^30,(-431476834842916376506055296 : Int)/10^30)
theorem v2470_pb_checked : Scalar.distance (sourceCoefficient 29 93 1 1) v2470_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2470_pg : Scalar.QComplex := ((-93086291424078843685084 : Int)/10^30,(154920775471497067022 : Int)/10^30)
theorem v2470_pg_checked : Scalar.distance (sourceCoefficient 29 93 1 2) v2470_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2470_mb : Scalar.QComplex := ((-1090439006813404179693844 : Int)/10^30,(-431476054501419567027519972 : Int)/10^30)
theorem v2470_mb_checked : Scalar.distance (sourceCoefficient 29 93 3 1) v2470_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2470_mg : Scalar.QComplex := ((-93086123074146433631071 : Int)/10^30,(235249994835457525561 : Int)/10^30)
theorem v2470_mg_checked : Scalar.distance (sourceCoefficient 29 93 3 2) v2470_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2470_upper : Scalar.QComplex := ((999994253348091587634103100984 : Int)/10^30,(-3390172678908343650082053924 : Int)/10^30)
theorem v2470_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 93 5) 1) 14) v2470_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2470 : Material (29 : Basis) (93 : Basis) where
  plus := ![v2470_pa,v2470_pb,v2470_pg]
  minus := ![(Primitive.Addresses.material2470 1).one,v2470_mb,v2470_mg]
  upper := v2470_upper
  lower := (Primitive.Addresses.material2470 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2470_pa_checked.trans (by decide +kernel)
    · exact v2470_pb_checked.trans (by decide +kernel)
    · exact v2470_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 93 Primitive.Addresses.material2470
    · exact v2470_mb_checked.trans (by decide +kernel)
    · exact v2470_mg_checked.trans (by decide +kernel)
  upper_error := v2470_upper_checked
  lower_error := reuse_lower_error 29 93 Primitive.Addresses.material2470

def v2471_pa : Scalar.QComplex := ((999998539544336917617162105797 : Int)/10^30,(-1709066760906086385286927138 : Int)/10^30)
theorem v2471_pa_checked : Scalar.distance (sourceCoefficient 29 94 1 0) v2471_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2471_pb : Scalar.QComplex := ((-737423725315740924538691 : Int)/10^30,(-431476794944002039096083156 : Int)/10^30)
theorem v2471_pb_checked : Scalar.distance (sourceCoefficient 29 94 1 1) v2471_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2471_pg : Scalar.QComplex := ((-93086283603389491347604 : Int)/10^30,(159090905548044169771 : Int)/10^30)
theorem v2471_pg_checked : Scalar.distance (sourceCoefficient 29 94 1 2) v2471_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2471_mb : Scalar.QComplex := ((-1109768491782402168442486 : Int)/10^30,(-431475997922009201958009922 : Int)/10^30)
theorem v2471_mb_checked : Scalar.distance (sourceCoefficient 29 94 3 1) v2471_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2471_mg : Scalar.QComplex := ((-93086111654825552920113 : Int)/10^30,(239420116610371936158 : Int)/10^30)
theorem v2471_mg_checked : Scalar.distance (sourceCoefficient 29 94 3 2) v2471_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2471_upper : Scalar.QComplex := ((999994100469796347961454705492 : Int)/10^30,(-3434970975546584336513479476 : Int)/10^30)
theorem v2471_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 94 5) 1) 14) v2471_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2471 : Material (29 : Basis) (94 : Basis) where
  plus := ![v2471_pa,v2471_pb,v2471_pg]
  minus := ![(Primitive.Addresses.material2471 1).one,v2471_mb,v2471_mg]
  upper := v2471_upper
  lower := (Primitive.Addresses.material2471 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2471_pa_checked.trans (by decide +kernel)
    · exact v2471_pb_checked.trans (by decide +kernel)
    · exact v2471_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 94 Primitive.Addresses.material2471
    · exact v2471_mb_checked.trans (by decide +kernel)
    · exact v2471_mg_checked.trans (by decide +kernel)
  upper_error := v2471_upper_checked
  lower_error := reuse_lower_error 29 94 Primitive.Addresses.material2471

def v2472_pa : Scalar.QComplex := ((999998462896630886795408798725 : Int)/10^30,(-1753340918230006358405527391 : Int)/10^30)
theorem v2472_pa_checked : Scalar.distance (sourceCoefficient 29 95 1 0) v2472_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2472_pb : Scalar.QComplex := ((-756527011575694304968463 : Int)/10^30,(-431476754377686627292507844 : Int)/10^30)
theorem v2472_pb_checked : Scalar.distance (sourceCoefficient 29 95 1 1) v2472_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2472_pg : Scalar.QComplex := ((-93086275660095298259564 : Int)/10^30,(163212226914546852319 : Int)/10^30)
theorem v2472_pg_checked : Scalar.distance (sourceCoefficient 29 95 1 2) v2472_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2472_mb : Scalar.QComplex := ((-1128871735922425849616118 : Int)/10^30,(-431475940870433232582205960 : Int)/10^30)
theorem v2472_mb_checked : Scalar.distance (sourceCoefficient 29 95 3 1) v2472_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2472_mg : Scalar.QComplex := ((-93086100155019595615616 : Int)/10^30,(243541429587613184320 : Int)/10^30)
theorem v2472_mg_checked : Scalar.distance (sourceCoefficient 29 95 3 2) v2472_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2472_upper : Scalar.QComplex := ((999993947409025453985380905233 : Int)/10^30,(-3479244934642360599884963483 : Int)/10^30)
theorem v2472_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 95 5) 1) 14) v2472_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2472 : Material (29 : Basis) (95 : Basis) where
  plus := ![v2472_pa,v2472_pb,v2472_pg]
  minus := ![(Primitive.Addresses.material2472 1).one,v2472_mb,v2472_mg]
  upper := v2472_upper
  lower := (Primitive.Addresses.material2472 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2472_pa_checked.trans (by decide +kernel)
    · exact v2472_pb_checked.trans (by decide +kernel)
    · exact v2472_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 95 Primitive.Addresses.material2472
    · exact v2472_mb_checked.trans (by decide +kernel)
    · exact v2472_mg_checked.trans (by decide +kernel)
  upper_error := v2472_upper_checked
  lower_error := reuse_lower_error 29 95 Primitive.Addresses.material2472

def v2473_pa : Scalar.QComplex := ((999998425387339590226767495658 : Int)/10^30,(-1774604981795812535993193935 : Int)/10^30)
theorem v2473_pa_checked : Scalar.distance (sourceCoefficient 29 96 1 0) v2473_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2473_pb : Scalar.QComplex := ((-765701968245267235635076 : Int)/10^30,(-431476734493556198158643931 : Int)/10^30)
theorem v2473_pb_checked : Scalar.distance (sourceCoefficient 29 96 1 1) v2473_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2473_pg : Scalar.QComplex := ((-93086271769403349089473 : Int)/10^30,(165191621731601060896 : Int)/10^30)
theorem v2473_pg_checked : Scalar.distance (sourceCoefficient 29 96 1 2) v2473_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2473_mb : Scalar.QComplex := ((-1138046672016634083613987 : Int)/10^30,(-431475913068735826086186632 : Int)/10^30)
theorem v2473_mb_checked : Scalar.distance (sourceCoefficient 29 96 3 1) v2473_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2473_mg : Scalar.QComplex := ((-93086094556200516643377 : Int)/10^30,(245520820310156317823 : Int)/10^30)
theorem v2473_mg_checked : Scalar.distance (sourceCoefficient 29 96 3 2) v2473_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2473_upper : Scalar.QComplex := ((999993873199945369296206557265 : Int)/10^30,(-3500508901800207987022934498 : Int)/10^30)
theorem v2473_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 96 5) 1) 14) v2473_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2473 : Material (29 : Basis) (96 : Basis) where
  plus := ![v2473_pa,v2473_pb,v2473_pg]
  minus := ![(Primitive.Addresses.material2473 1).one,v2473_mb,v2473_mg]
  upper := v2473_upper
  lower := (Primitive.Addresses.material2473 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2473_pa_checked.trans (by decide +kernel)
    · exact v2473_pb_checked.trans (by decide +kernel)
    · exact v2473_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 96 Primitive.Addresses.material2473
    · exact v2473_mb_checked.trans (by decide +kernel)
    · exact v2473_mg_checked.trans (by decide +kernel)
  upper_error := v2473_upper_checked
  lower_error := reuse_lower_error 29 96 Primitive.Addresses.material2473

def v2474_pa : Scalar.QComplex := ((999998292876942510115371756086 : Int)/10^30,(-1847767085081514228799363318 : Int)/10^30)
theorem v2474_pa_checked : Scalar.distance (sourceCoefficient 29 97 1 0) v2474_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2474_pb : Scalar.QComplex := ((-797269738927690306894877 : Int)/10^30,(-431476664092089537884435259 : Int)/10^30)
theorem v2474_pb_checked : Scalar.distance (sourceCoefficient 29 97 1 1) v2474_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2474_pg : Scalar.QComplex := ((-93086258007780462160010 : Int)/10^30,(172002017248791846604 : Int)/10^30)
theorem v2474_pg_checked : Scalar.distance (sourceCoefficient 29 97 1 2) v2474_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2474_mb : Scalar.QComplex := ((-1169614370191638447953188 : Int)/10^30,(-431475815425731040177749684 : Int)/10^30)
theorem v2474_mb_checked : Scalar.distance (sourceCoefficient 29 97 3 1) v2474_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2474_mg : Scalar.QComplex := ((-93086074917518151287189 : Int)/10^30,(252331201415864851096 : Int)/10^30)
theorem v2474_mg_checked : Scalar.distance (sourceCoefficient 29 97 3 2) v2474_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2474_upper : Scalar.QComplex := ((999993614418592590897382283855 : Int)/10^30,(-3573670667418626949185697505 : Int)/10^30)
theorem v2474_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 97 5) 1) 14) v2474_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2474 : Material (29 : Basis) (97 : Basis) where
  plus := ![v2474_pa,v2474_pb,v2474_pg]
  minus := ![(Primitive.Addresses.material2474 1).one,v2474_mb,v2474_mg]
  upper := v2474_upper
  lower := (Primitive.Addresses.material2474 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2474_pa_checked.trans (by decide +kernel)
    · exact v2474_pb_checked.trans (by decide +kernel)
    · exact v2474_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 97 Primitive.Addresses.material2474
    · exact v2474_mb_checked.trans (by decide +kernel)
    · exact v2474_mg_checked.trans (by decide +kernel)
  upper_error := v2474_upper_checked
  lower_error := reuse_lower_error 29 97 Primitive.Addresses.material2474

def v2475_pa : Scalar.QComplex := ((999999834238909326483121725805 : Int)/10^30,(-575779605292072302725275638 : Int)/10^30)
theorem v2475_pa_checked : Scalar.distance (sourceCoefficient 30 31 1 0) v2475_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2475_pb : Scalar.QComplex := ((-248435956729060533526618 : Int)/10^30,(-431477449469615672403470027 : Int)/10^30)
theorem v2475_pb_checked : Scalar.distance (sourceCoefficient 30 31 1 1) v2475_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2475_pg : Scalar.QComplex := ((-93086414465912987845764 : Int)/10^30,(53597267863579207719 : Int)/10^30)
theorem v2475_pg_checked : Scalar.distance (sourceCoefficient 30 31 1 2) v2475_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2475_mb : Scalar.QComplex := ((-620781470094341693490350 : Int)/10^30,(-431477074421800224213475579 : Int)/10^30)
theorem v2475_mb_checked : Scalar.distance (sourceCoefficient 30 31 3 1) v2475_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2475_mg : Scalar.QComplex := ((-93086333553558387946968 : Int)/10^30,(133926631134473529660 : Int)/10^30)
theorem v2475_mg_checked : Scalar.distance (sourceCoefficient 30 31 3 2) v2475_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2475_upper : Scalar.QComplex := ((999997351113260043493840372923 : Int)/10^30,(-2301687742356041483780101341 : Int)/10^30)
theorem v2475_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 31 5) 1) 14) v2475_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2475 : Material (30 : Basis) (31 : Basis) where
  plus := ![v2475_pa,v2475_pb,v2475_pg]
  minus := ![(Primitive.Addresses.material2475 1).one,v2475_mb,v2475_mg]
  upper := v2475_upper
  lower := (Primitive.Addresses.material2475 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2475_pa_checked.trans (by decide +kernel)
    · exact v2475_pb_checked.trans (by decide +kernel)
    · exact v2475_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 31 Primitive.Addresses.material2475
    · exact v2475_mb_checked.trans (by decide +kernel)
    · exact v2475_mg_checked.trans (by decide +kernel)
  upper_error := v2475_upper_checked
  lower_error := reuse_lower_error 30 31 Primitive.Addresses.material2475

def v2476_pa : Scalar.QComplex := ((999999831477528556655728487904 : Int)/10^30,(-580555694560707208684283125 : Int)/10^30)
theorem v2476_pa_checked : Scalar.distance (sourceCoefficient 30 32 1 0) v2476_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2476_pb : Scalar.QComplex := ((-250496731881349619148331 : Int)/10^30,(-431477448268880054070165035 : Int)/10^30)
theorem v2476_pb_checked : Scalar.distance (sourceCoefficient 30 32 1 1) v2476_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2476_pg : Scalar.QComplex := ((-93086414207866836108051 : Int)/10^30,(54041856961881111377 : Int)/10^30)
theorem v2476_pg_checked : Scalar.distance (sourceCoefficient 30 32 1 2) v2476_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2476_mb : Scalar.QComplex := ((-622842243443129248340784 : Int)/10^30,(-431477071442708910410883117 : Int)/10^30)
theorem v2476_mb_checked : Scalar.distance (sourceCoefficient 30 32 3 1) v2476_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2476_mg : Scalar.QComplex := ((-93086332911851964006767 : Int)/10^30,(134371219844552386312 : Int)/10^30)
theorem v2476_mg_checked : Scalar.distance (sourceCoefficient 30 32 3 2) v2476_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2476_upper : Scalar.QComplex := ((999997340108786592188707652746 : Int)/10^30,(-2306463819745359764748217715 : Int)/10^30)
theorem v2476_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 32 5) 1) 14) v2476_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2476 : Material (30 : Basis) (32 : Basis) where
  plus := ![v2476_pa,v2476_pb,v2476_pg]
  minus := ![(Primitive.Addresses.material2476 1).one,v2476_mb,v2476_mg]
  upper := v2476_upper
  lower := (Primitive.Addresses.material2476 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2476_pa_checked.trans (by decide +kernel)
    · exact v2476_pb_checked.trans (by decide +kernel)
    · exact v2476_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 32 Primitive.Addresses.material2476
    · exact v2476_mb_checked.trans (by decide +kernel)
    · exact v2476_mg_checked.trans (by decide +kernel)
  upper_error := v2476_upper_checked
  lower_error := reuse_lower_error 30 32 Primitive.Addresses.material2476

def v2477_pa : Scalar.QComplex := ((999999827591129639527653900231 : Int)/10^30,(-587211811015519435988607632 : Int)/10^30)
theorem v2477_pa_checked : Scalar.distance (sourceCoefficient 30 33 1 0) v2477_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2477_pb : Scalar.QComplex := ((-253368696497850227657767 : Int)/10^30,(-431477446573606458241720586 : Int)/10^30)
theorem v2477_pb_checked : Scalar.distance (sourceCoefficient 30 33 1 1) v2477_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2477_pg : Scalar.QComplex := ((-93086413844113215303268 : Int)/10^30,(54661451078460874190 : Int)/10^30)
theorem v2477_pg_checked : Scalar.distance (sourceCoefficient 30 33 1 2) v2477_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2477_mb : Scalar.QComplex := ((-625714205527321413948407 : Int)/10^30,(-431477067269059830254936814 : Int)/10^30)
theorem v2477_mb_checked : Scalar.distance (sourceCoefficient 30 33 3 1) v2477_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2477_mg : Scalar.QComplex := ((-93086332013416661518856 : Int)/10^30,(134990813416525950773 : Int)/10^30)
theorem v2477_mg_checked : Scalar.distance (sourceCoefficient 30 33 3 2) v2477_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2477_upper : Scalar.QComplex := ((999997324734540300557242969116 : Int)/10^30,(-2313119919579096455365321082 : Int)/10^30)
theorem v2477_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 33 5) 1) 14) v2477_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2477 : Material (30 : Basis) (33 : Basis) where
  plus := ![v2477_pa,v2477_pb,v2477_pg]
  minus := ![(Primitive.Addresses.material2477 1).one,v2477_mb,v2477_mg]
  upper := v2477_upper
  lower := (Primitive.Addresses.material2477 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2477_pa_checked.trans (by decide +kernel)
    · exact v2477_pb_checked.trans (by decide +kernel)
    · exact v2477_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 33 Primitive.Addresses.material2477
    · exact v2477_mb_checked.trans (by decide +kernel)
    · exact v2477_mg_checked.trans (by decide +kernel)
  upper_error := v2477_upper_checked
  lower_error := reuse_lower_error 30 33 Primitive.Addresses.material2477

def v2478_pa : Scalar.QComplex := ((999999817967011353080689654449 : Int)/10^30,(-603378773373599599452655806 : Int)/10^30)
theorem v2478_pa_checked : Scalar.distance (sourceCoefficient 30 34 1 0) v2478_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2478_pb : Scalar.QComplex := ((-260344377294688844617879 : Int)/10^30,(-431477442349838794560561186 : Int)/10^30)
theorem v2478_pb_checked : Scalar.distance (sourceCoefficient 30 34 1 1) v2478_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2478_pg : Scalar.QComplex := ((-93086412940560587870943 : Int)/10^30,(56166375881957079290 : Int)/10^30)
theorem v2478_pg_checked : Scalar.distance (sourceCoefficient 30 34 1 2) v2478_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2478_mb : Scalar.QComplex := ((-632689880081874003560839 : Int)/10^30,(-431477057025595384604227512 : Int)/10^30)
theorem v2478_mb_checked : Scalar.distance (sourceCoefficient 30 34 3 1) v2478_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2478_mg : Scalar.QComplex := ((-93086329811182044400307 : Int)/10^30,(136495736879944650095 : Int)/10^30)
theorem v2478_mg_checked : Scalar.distance (sourceCoefficient 30 34 3 2) v2478_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2478_upper : Scalar.QComplex := ((999997287207725973425817928960 : Int)/10^30,(-2329286841248030222055638672 : Int)/10^30)
theorem v2478_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 34 5) 1) 14) v2478_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2478 : Material (30 : Basis) (34 : Basis) where
  plus := ![v2478_pa,v2478_pb,v2478_pg]
  minus := ![(Primitive.Addresses.material2478 1).one,v2478_mb,v2478_mg]
  upper := v2478_upper
  lower := (Primitive.Addresses.material2478 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2478_pa_checked.trans (by decide +kernel)
    · exact v2478_pb_checked.trans (by decide +kernel)
    · exact v2478_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 34 Primitive.Addresses.material2478
    · exact v2478_mb_checked.trans (by decide +kernel)
    · exact v2478_mg_checked.trans (by decide +kernel)
  upper_error := v2478_upper_checked
  lower_error := reuse_lower_error 30 34 Primitive.Addresses.material2478

def v2479_pa : Scalar.QComplex := ((999999785657175371252329124039 : Int)/10^30,(-654740867301445352448859582 : Int)/10^30)
theorem v2479_pa_checked : Scalar.distance (sourceCoefficient 30 35 1 0) v2479_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2479_pb : Scalar.QComplex := ((-282505965939184178064345 : Int)/10^30,(-431477427933317928739800888 : Int)/10^30)
theorem v2479_pb_checked : Scalar.distance (sourceCoefficient 30 35 1 1) v2479_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2479_pg : Scalar.QComplex := ((-93086409881655703748567 : Int)/10^30,(60947489803550207028 : Int)/10^30)
theorem v2479_pg_checked : Scalar.distance (sourceCoefficient 30 35 1 2) v2479_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2479_mb : Scalar.QComplex := ((-654851448033788838819074 : Int)/10^30,(-431477023484627007414138944 : Int)/10^30)
theorem v2479_mb_checked : Scalar.distance (sourceCoefficient 30 35 3 1) v2479_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2479_mg : Scalar.QComplex := ((-93086322626392318290628 : Int)/10^30,(141276846381613410087 : Int)/10^30)
theorem v2479_mg_checked : Scalar.distance (sourceCoefficient 30 35 3 2) v2479_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2479_upper : Scalar.QComplex := ((999997166251623526603864416991 : Int)/10^30,(-2380648802914224705690498273 : Int)/10^30)
theorem v2479_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 35 5) 1) 14) v2479_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2479 : Material (30 : Basis) (35 : Basis) where
  plus := ![v2479_pa,v2479_pb,v2479_pg]
  minus := ![(Primitive.Addresses.material2479 1).one,v2479_mb,v2479_mg]
  upper := v2479_upper
  lower := (Primitive.Addresses.material2479 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2479_pa_checked.trans (by decide +kernel)
    · exact v2479_pb_checked.trans (by decide +kernel)
    · exact v2479_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 35 Primitive.Addresses.material2479
    · exact v2479_mb_checked.trans (by decide +kernel)
    · exact v2479_mg_checked.trans (by decide +kernel)
  upper_error := v2479_upper_checked
  lower_error := reuse_lower_error 30 35 Primitive.Addresses.material2479

def v2480_pa : Scalar.QComplex := ((999999774956104351418061729709 : Int)/10^30,(-670885788083492574926758020 : Int)/10^30)
theorem v2480_pa_checked : Scalar.distance (sourceCoefficient 30 36 1 0) v2480_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2480_pb : Scalar.QComplex := ((-289472136172689204269877 : Int)/10^30,(-431477423088185670695280475 : Int)/10^30)
theorem v2480_pb_checked : Scalar.distance (sourceCoefficient 30 36 1 1) v2480_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2480_pg : Scalar.QComplex := ((-93086408860952017083492 : Int)/10^30,(62450362822614934646 : Int)/10^30)
theorem v2480_pg_checked : Scalar.distance (sourceCoefficient 30 36 1 2) v2480_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2480_mb : Scalar.QComplex := ((-661817611492339395347129 : Int)/10^30,(-431477012628005386579521875 : Int)/10^30)
theorem v2480_mb_checked : Scalar.distance (sourceCoefficient 30 36 3 1) v2480_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2480_mg : Scalar.QComplex := ((-93086320308777283115447 : Int)/10^30,(142779717960268517214 : Int)/10^30)
theorem v2480_mg_checked : Scalar.distance (sourceCoefficient 30 36 3 2) v2480_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2480_upper : Scalar.QComplex := ((999997127685899830716423275598 : Int)/10^30,(-2396793681181231152272624650 : Int)/10^30)
theorem v2480_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 36 5) 1) 14) v2480_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2480 : Material (30 : Basis) (36 : Basis) where
  plus := ![v2480_pa,v2480_pb,v2480_pg]
  minus := ![(Primitive.Addresses.material2480 1).one,v2480_mb,v2480_mg]
  upper := v2480_upper
  lower := (Primitive.Addresses.material2480 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2480_pa_checked.trans (by decide +kernel)
    · exact v2480_pb_checked.trans (by decide +kernel)
    · exact v2480_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 36 Primitive.Addresses.material2480
    · exact v2480_mb_checked.trans (by decide +kernel)
    · exact v2480_mg_checked.trans (by decide +kernel)
  upper_error := v2480_upper_checked
  lower_error := reuse_lower_error 30 36 Primitive.Addresses.material2480

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
