import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B009
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B010

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v225_pa : Scalar.QComplex := ((999984810041266212976176391574 : Int)/10^30,(5511777093889747778189141104 : Int)/10^30)
theorem v225_pa_checked : Scalar.distance (sourceCoefficient 2 35 1 0) v225_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v225_pb : Scalar.QComplex := ((2378192400956601438407790 : Int)/10^30,(-431468151886720733945246166 : Int)/10^30)
theorem v225_pb_checked : Scalar.distance (sourceCoefficient 2 35 1 1) v225_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v225_pg : Scalar.QComplex := ((-93084712266705994076497 : Int)/10^30,(-513069978374747178050 : Int)/10^30)
theorem v225_pg_checked : Scalar.distance (sourceCoefficient 2 35 1 2) v225_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v225_mb : Scalar.QComplex := ((2005853932972830608831553 : Int)/10^30,(-431470043504340933747124548 : Int)/10^30)
theorem v225_mb_checked : Scalar.distance (sourceCoefficient 2 35 3 1) v225_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v225_mg : Scalar.QComplex := ((-93085120363296959053630 : Int)/10^30,(-432741873028990538290 : Int)/10^30)
theorem v225_mg_checked : Scalar.distance (sourceCoefficient 2 35 3 2) v225_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v225_upper : Scalar.QComplex := ((999992833508597665590999343632 : Int)/10^30,(3785885820527317259138920849 : Int)/10^30)
theorem v225_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 35 5) 1) 14) v225_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material225 : Material (2 : Basis) (35 : Basis) where
  plus := ![v225_pa,v225_pb,v225_pg]
  minus := ![(Primitive.Addresses.material225 1).one,v225_mb,v225_mg]
  upper := v225_upper
  lower := (Primitive.Addresses.material225 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v225_pa_checked.trans (by decide +kernel)
    · exact v225_pb_checked.trans (by decide +kernel)
    · exact v225_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 35 Primitive.Addresses.material225
    · exact v225_mb_checked.trans (by decide +kernel)
    · exact v225_mg_checked.trans (by decide +kernel)
  upper_error := v225_upper_checked
  lower_error := reuse_lower_error 2 35 Primitive.Addresses.material225

def v226_pa : Scalar.QComplex := ((999984898898162995142859319768 : Int)/10^30,(5495632414084208260683940640 : Int)/10^30)
theorem v226_pa_checked : Scalar.distance (sourceCoefficient 2 36 1 0) v226_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v226_pb : Scalar.QComplex := ((2371226300040243558831031 : Int)/10^30,(-431468175679566999923445412 : Int)/10^30)
theorem v226_pb_checked : Scalar.distance (sourceCoefficient 2 36 1 1) v226_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v226_pg : Scalar.QComplex := ((-93084718968909303043693 : Int)/10^30,(-511567124048693849336 : Int)/10^30)
theorem v226_pg_checked : Scalar.distance (sourceCoefficient 2 36 1 2) v226_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v226_mb : Scalar.QComplex := ((1998887814118115729431679 : Int)/10^30,(-431470061285746991283061493 : Int)/10^30)
theorem v226_mb_checked : Scalar.distance (sourceCoefficient 2 36 3 1) v226_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v226_mg : Scalar.QComplex := ((-93085125768602175146427 : Int)/10^30,(-431239013478818959395 : Int)/10^30)
theorem v226_mg_checked : Scalar.distance (sourceCoefficient 2 36 3 2) v226_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v226_upper : Scalar.QComplex := ((999992894501109395397448638663 : Int)/10^30,(3769741011408439013360941469 : Int)/10^30)
theorem v226_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 36 5) 1) 14) v226_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material226 : Material (2 : Basis) (36 : Basis) where
  plus := ![v226_pa,v226_pb,v226_pg]
  minus := ![(Primitive.Addresses.material226 1).one,v226_mb,v226_mg]
  upper := v226_upper
  lower := (Primitive.Addresses.material226 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v226_pa_checked.trans (by decide +kernel)
    · exact v226_pb_checked.trans (by decide +kernel)
    · exact v226_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 36 Primitive.Addresses.material226
    · exact v226_mb_checked.trans (by decide +kernel)
    · exact v226_mg_checked.trans (by decide +kernel)
  upper_error := v226_upper_checked
  lower_error := reuse_lower_error 2 36 Primitive.Addresses.material226

def v227_pa : Scalar.QComplex := ((999984936761601517074708262370 : Int)/10^30,(5488738461232672093061597637 : Int)/10^30)
theorem v227_pa_checked : Scalar.distance (sourceCoefficient 2 37 1 0) v227_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v227_pb : Scalar.QComplex := ((2368251699704001270841372 : Int)/10^30,(-431468185793680944565131506 : Int)/10^30)
theorem v227_pb_checked : Scalar.distance (sourceCoefficient 2 37 1 1) v227_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v227_pg : Scalar.QComplex := ((-93084721822197839471920 : Int)/10^30,(-510925389009579991050 : Int)/10^30)
theorem v227_pg_checked : Scalar.distance (sourceCoefficient 2 37 1 2) v227_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v227_mb : Scalar.QComplex := ((1995913206161428281132748 : Int)/10^30,(-431470068832911050826699721 : Int)/10^30)
theorem v227_mb_checked : Scalar.distance (sourceCoefficient 2 37 3 1) v227_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v227_mg : Scalar.QComplex := ((-93085128068101213082915 : Int)/10^30,(-430597276216392885319 : Int)/10^30)
theorem v227_mg_checked : Scalar.distance (sourceCoefficient 2 37 3 2) v227_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v227_upper : Scalar.QComplex := ((999992920466154316951167033264 : Int)/10^30,(3762847003475775852969010977 : Int)/10^30)
theorem v227_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 37 5) 1) 14) v227_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material227 : Material (2 : Basis) (37 : Basis) where
  plus := ![v227_pa,v227_pb,v227_pg]
  minus := ![(Primitive.Addresses.material227 1).one,v227_mb,v227_mg]
  upper := v227_upper
  lower := (Primitive.Addresses.material227 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v227_pa_checked.trans (by decide +kernel)
    · exact v227_pb_checked.trans (by decide +kernel)
    · exact v227_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 37 Primitive.Addresses.material227
    · exact v227_mb_checked.trans (by decide +kernel)
    · exact v227_mg_checked.trans (by decide +kernel)
  upper_error := v227_upper_checked
  lower_error := reuse_lower_error 2 37 Primitive.Addresses.material227

def v228_pa : Scalar.QComplex := ((999985064383319681773655894796 : Int)/10^30,(5465437794723386227205071206 : Int)/10^30)
theorem v228_pa_checked : Scalar.distance (sourceCoefficient 2 38 1 0) v228_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v228_pb : Scalar.QComplex := ((2358197936724499935316114 : Int)/10^30,(-431468219775687841848883652 : Int)/10^30)
theorem v228_pb_checked : Scalar.distance (sourceCoefficient 2 38 1 1) v228_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v228_pg : Scalar.QComplex := ((-93084731427738114968500 : Int)/10^30,(-508756407847526952467 : Int)/10^30)
theorem v228_pg_checked : Scalar.distance (sourceCoefficient 2 38 1 2) v228_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v228_mb : Scalar.QComplex := ((1985859417600460922962969 : Int)/10^30,(-431470094138960648422274081 : Int)/10^30)
theorem v228_mb_checked : Scalar.distance (sourceCoefficient 2 38 3 1) v228_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v228_mg : Scalar.QComplex := ((-93085135801904856431299 : Int)/10^30,(-428428287572802020425 : Int)/10^30)
theorem v228_mg_checked : Scalar.distance (sourceCoefficient 2 38 3 2) v228_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v228_upper : Scalar.QComplex := ((999993007872845829018471092586 : Int)/10^30,(3739546151406587863696700294 : Int)/10^30)
theorem v228_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 38 5) 1) 14) v228_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material228 : Material (2 : Basis) (38 : Basis) where
  plus := ![v228_pa,v228_pb,v228_pg]
  minus := ![(Primitive.Addresses.material228 1).one,v228_mb,v228_mg]
  upper := v228_upper
  lower := (Primitive.Addresses.material228 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v228_pa_checked.trans (by decide +kernel)
    · exact v228_pb_checked.trans (by decide +kernel)
    · exact v228_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 38 Primitive.Addresses.material228
    · exact v228_mb_checked.trans (by decide +kernel)
    · exact v228_mg_checked.trans (by decide +kernel)
  upper_error := v228_upper_checked
  lower_error := reuse_lower_error 2 38 Primitive.Addresses.material228

def v229_pa : Scalar.QComplex := ((999985138170435450323017250075 : Int)/10^30,(5451920602422723125937389834 : Int)/10^30)
theorem v229_pa_checked : Scalar.distance (sourceCoefficient 2 39 1 0) v229_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v229_pb : Scalar.QComplex := ((2352365543838291664147186 : Int)/10^30,(-431468239346181516046550544 : Int)/10^30)
theorem v229_pb_checked : Scalar.distance (sourceCoefficient 2 39 1 1) v229_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v229_pg : Scalar.QComplex := ((-93084736973083082989159 : Int)/10^30,(-507498137625477566820 : Int)/10^30)
theorem v229_pg_checked : Scalar.distance (sourceCoefficient 2 39 1 2) v229_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v229_mb : Scalar.QComplex := ((1980027009997464458334857 : Int)/10^30,(-431470108676354656057401717 : Int)/10^30)
theorem v229_mb_checked : Scalar.distance (sourceCoefficient 2 39 3 1) v229_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v229_mg : Scalar.QComplex := ((-93085140261417228425069 : Int)/10^30,(-427170013033881189901 : Int)/10^30)
theorem v229_mg_checked : Scalar.distance (sourceCoefficient 2 39 3 2) v229_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v229_upper : Scalar.QComplex := ((999993058330404059488445663088 : Int)/10^30,(3726028851888326951655661224 : Int)/10^30)
theorem v229_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 39 5) 1) 14) v229_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material229 : Material (2 : Basis) (39 : Basis) where
  plus := ![v229_pa,v229_pb,v229_pg]
  minus := ![(Primitive.Addresses.material229 1).one,v229_mb,v229_mg]
  upper := v229_upper
  lower := (Primitive.Addresses.material229 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v229_pa_checked.trans (by decide +kernel)
    · exact v229_pb_checked.trans (by decide +kernel)
    · exact v229_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 39 Primitive.Addresses.material229
    · exact v229_mb_checked.trans (by decide +kernel)
    · exact v229_mg_checked.trans (by decide +kernel)
  upper_error := v229_upper_checked
  lower_error := reuse_lower_error 2 39 Primitive.Addresses.material229

def v230_pa : Scalar.QComplex := ((999985261864121318028133800684 : Int)/10^30,(5429185440258489203447881618 : Int)/10^30)
theorem v230_pa_checked : Scalar.distance (sourceCoefficient 2 40 1 0) v230_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v230_pb : Scalar.QComplex := ((2342555785320159491270536 : Int)/10^30,(-431468272025565986240499090 : Int)/10^30)
theorem v230_pb_checked : Scalar.distance (sourceCoefficient 2 40 1 1) v230_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v230_pg : Scalar.QComplex := ((-93084746255287047638487 : Int)/10^30,(-505381797464962015114 : Int)/10^30)
theorem v230_pg_checked : Scalar.distance (sourceCoefficient 2 40 1 2) v230_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v230_mb : Scalar.QComplex := ((1970217226931116736933405 : Int)/10^30,(-431470132890347172197633551 : Int)/10^30)
theorem v230_mb_checked : Scalar.distance (sourceCoefficient 2 40 3 1) v230_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v230_mg : Scalar.QComplex := ((-93085147717311494783241 : Int)/10^30,(-425053665651251834934 : Int)/10^30)
theorem v230_mg_checked : Scalar.distance (sourceCoefficient 2 40 3 2) v230_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v230_upper : Scalar.QComplex := ((999993142785078322310827495625 : Int)/10^30,(3703293510101366008907247450 : Int)/10^30)
theorem v230_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 40 5) 1) 14) v230_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material230 : Material (2 : Basis) (40 : Basis) where
  plus := ![v230_pa,v230_pb,v230_pg]
  minus := ![(Primitive.Addresses.material230 1).one,v230_mb,v230_mg]
  upper := v230_upper
  lower := (Primitive.Addresses.material230 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v230_pa_checked.trans (by decide +kernel)
    · exact v230_pb_checked.trans (by decide +kernel)
    · exact v230_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 40 Primitive.Addresses.material230
    · exact v230_mb_checked.trans (by decide +kernel)
    · exact v230_mg_checked.trans (by decide +kernel)
  upper_error := v230_upper_checked
  lower_error := reuse_lower_error 2 40 Primitive.Addresses.material230

def v231_pa : Scalar.QComplex := ((999985340395521098832593203793 : Int)/10^30,(5414701658798835150686919585 : Int)/10^30)
theorem v231_pa_checked : Scalar.distance (sourceCoefficient 2 41 1 0) v231_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v231_pb : Scalar.QComplex := ((2336306329471101535742890 : Int)/10^30,(-431468292689395279223557132 : Int)/10^30)
theorem v231_pb_checked : Scalar.distance (sourceCoefficient 2 41 1 1) v231_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v231_pg : Scalar.QComplex := ((-93084752139383529642149 : Int)/10^30,(-504033550750496515491 : Int)/10^30)
theorem v231_pg_checked : Scalar.distance (sourceCoefficient 2 41 1 2) v231_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v231_mb : Scalar.QComplex := ((1963967755577062792731061 : Int)/10^30,(-431470148161169838398614583 : Int)/10^30)
theorem v231_mb_checked : Scalar.distance (sourceCoefficient 2 41 3 1) v231_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v231_mg : Scalar.QComplex := ((-93085152437929594063024 : Int)/10^30,(-423705414361089950924 : Int)/10^30)
theorem v231_mg_checked : Scalar.distance (sourceCoefficient 2 41 3 2) v231_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v231_upper : Scalar.QComplex := ((999993196318668298847304710087 : Int)/10^30,(3688809614675531347082543554 : Int)/10^30)
theorem v231_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 41 5) 1) 14) v231_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material231 : Material (2 : Basis) (41 : Basis) where
  plus := ![v231_pa,v231_pb,v231_pg]
  minus := ![(Primitive.Addresses.material231 1).one,v231_mb,v231_mg]
  upper := v231_upper
  lower := (Primitive.Addresses.material231 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v231_pa_checked.trans (by decide +kernel)
    · exact v231_pb_checked.trans (by decide +kernel)
    · exact v231_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 41 Primitive.Addresses.material231
    · exact v231_mb_checked.trans (by decide +kernel)
    · exact v231_mg_checked.trans (by decide +kernel)
  upper_error := v231_upper_checked
  lower_error := reuse_lower_error 2 41 Primitive.Addresses.material231

def v232_pa : Scalar.QComplex := ((999985403590746996879168679765 : Int)/10^30,(5403018179762415023695159246 : Int)/10^30)
theorem v232_pa_checked : Scalar.distance (sourceCoefficient 2 42 1 0) v232_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v232_pb : Scalar.QComplex := ((2331265147077989430945231 : Int)/10^30,(-431468309270122760559198172 : Int)/10^30)
theorem v232_pb_checked : Scalar.distance (sourceCoefficient 2 42 1 1) v232_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v232_pg : Scalar.QComplex := ((-93084756869243849776459 : Int)/10^30,(-502945974828569611848 : Int)/10^30)
theorem v232_pg_checked : Scalar.distance (sourceCoefficient 2 42 1 2) v232_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v232_mb : Scalar.QComplex := ((1958926560752592238157830 : Int)/10^30,(-431470160391577787142517435 : Int)/10^30)
theorem v232_mb_checked : Scalar.distance (sourceCoefficient 2 42 3 1) v232_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v232_mg : Scalar.QComplex := ((-93085156229259115032457 : Int)/10^30,(-422617834762460836415 : Int)/10^30)
theorem v232_mg_checked : Scalar.distance (sourceCoefficient 2 42 3 2) v232_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v232_upper : Scalar.QComplex := ((999993239349175175105765841477 : Int)/10^30,(3677126043971053933063582549 : Int)/10^30)
theorem v232_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 42 5) 1) 14) v232_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material232 : Material (2 : Basis) (42 : Basis) where
  plus := ![v232_pa,v232_pb,v232_pg]
  minus := ![(Primitive.Addresses.material232 1).one,v232_mb,v232_mg]
  upper := v232_upper
  lower := (Primitive.Addresses.material232 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v232_pa_checked.trans (by decide +kernel)
    · exact v232_pb_checked.trans (by decide +kernel)
    · exact v232_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 42 Primitive.Addresses.material232
    · exact v232_mb_checked.trans (by decide +kernel)
    · exact v232_mg_checked.trans (by decide +kernel)
  upper_error := v232_upper_checked
  lower_error := reuse_lower_error 2 42 Primitive.Addresses.material232

def v233_pa : Scalar.QComplex := ((999985487097740403660432586836 : Int)/10^30,(5387540616539302020734565427 : Int)/10^30)
theorem v233_pa_checked : Scalar.distance (sourceCoefficient 2 43 1 0) v233_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v233_pb : Scalar.QComplex := ((2324586895131304482874368 : Int)/10^30,(-431468331114333776536927089 : Int)/10^30)
theorem v233_pb_checked : Scalar.distance (sourceCoefficient 2 43 1 1) v233_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v233_pg : Scalar.QComplex := ((-93084763112247349956547 : Int)/10^30,(-501505220344417501632 : Int)/10^30)
theorem v233_pg_checked : Scalar.distance (sourceCoefficient 2 43 1 2) v233_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v233_mb : Scalar.QComplex := ((1952248292441955420983489 : Int)/10^30,(-431470176472750016835345552 : Int)/10^30)
theorem v233_mb_checked : Scalar.distance (sourceCoefficient 2 43 3 1) v233_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v233_mg : Scalar.QComplex := ((-93085161228954060006918 : Int)/10^30,(-421177075427336620166 : Int)/10^30)
theorem v233_mg_checked : Scalar.distance (sourceCoefficient 2 43 3 2) v233_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v233_upper : Scalar.QComplex := ((999993296143174198503995306257 : Int)/10^30,(3661648359674458303796812469 : Int)/10^30)
theorem v233_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 43 5) 1) 14) v233_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material233 : Material (2 : Basis) (43 : Basis) where
  plus := ![v233_pa,v233_pb,v233_pg]
  minus := ![(Primitive.Addresses.material233 1).one,v233_mb,v233_mg]
  upper := v233_upper
  lower := (Primitive.Addresses.material233 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v233_pa_checked.trans (by decide +kernel)
    · exact v233_pb_checked.trans (by decide +kernel)
    · exact v233_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 43 Primitive.Addresses.material233
    · exact v233_mb_checked.trans (by decide +kernel)
    · exact v233_mg_checked.trans (by decide +kernel)
  upper_error := v233_upper_checked
  lower_error := reuse_lower_error 2 43 Primitive.Addresses.material233

def v234_pa : Scalar.QComplex := ((999985518628845072146529097398 : Int)/10^30,(5381684922005856351890352827 : Int)/10^30)
theorem v234_pa_checked : Scalar.distance (sourceCoefficient 2 44 1 0) v234_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v234_pb : Scalar.QComplex := ((2322060282780933245172953 : Int)/10^30,(-431468339342815087851946220 : Int)/10^30)
theorem v234_pb_checked : Scalar.distance (sourceCoefficient 2 44 1 1) v234_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v234_pg : Scalar.QComplex := ((-93084765467406770448029 : Int)/10^30,(-500960133374019647441 : Int)/10^30)
theorem v234_pg_checked : Scalar.distance (sourceCoefficient 2 44 1 2) v234_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v234_mb : Scalar.QComplex := ((1949721673931548658590317 : Int)/10^30,(-431470182520875600336348348 : Int)/10^30)
theorem v234_mb_checked : Scalar.distance (sourceCoefficient 2 44 3 1) v234_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v234_mg : Scalar.QComplex := ((-93085163113727097917379 : Int)/10^30,(-420631986627503049318 : Int)/10^30)
theorem v234_mg_checked : Scalar.distance (sourceCoefficient 2 44 3 2) v234_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v234_upper : Scalar.QComplex := ((999993317567834364844743872051 : Int)/10^30,(3655792619442555605984305101 : Int)/10^30)
theorem v234_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 44 5) 1) 14) v234_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material234 : Material (2 : Basis) (44 : Basis) where
  plus := ![v234_pa,v234_pb,v234_pg]
  minus := ![(Primitive.Addresses.material234 1).one,v234_mb,v234_mg]
  upper := v234_upper
  lower := (Primitive.Addresses.material234 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v234_pa_checked.trans (by decide +kernel)
    · exact v234_pb_checked.trans (by decide +kernel)
    · exact v234_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 44 Primitive.Addresses.material234
    · exact v234_mb_checked.trans (by decide +kernel)
    · exact v234_mg_checked.trans (by decide +kernel)
  upper_error := v234_upper_checked
  lower_error := reuse_lower_error 2 44 Primitive.Addresses.material234

def v235_pa : Scalar.QComplex := ((999985534303190246150188278732 : Int)/10^30,(5378771640730205595807858289 : Int)/10^30)
theorem v235_pa_checked : Scalar.distance (sourceCoefficient 2 45 1 0) v235_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v235_pb : Scalar.QComplex := ((2320803261546366705207472 : Int)/10^30,(-431468343429238704176543238 : Int)/10^30)
theorem v235_pb_checked : Scalar.distance (sourceCoefficient 2 45 1 1) v235_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v235_pg : Scalar.QComplex := ((-93084766637740800437026 : Int)/10^30,(-500688945789555175531 : Int)/10^30)
theorem v235_pg_checked : Scalar.distance (sourceCoefficient 2 45 1 2) v235_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v235_mb : Scalar.QComplex := ((1948464649638629037761857 : Int)/10^30,(-431470185522544983802539640 : Int)/10^30)
theorem v235_mb_checked : Scalar.distance (sourceCoefficient 2 45 3 1) v235_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v235_mg : Scalar.QComplex := ((-93085164050038020580096 : Int)/10^30,(-420360798134068550997 : Int)/10^30)
theorem v235_mg_checked : Scalar.distance (sourceCoefficient 2 45 3 2) v235_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v235_upper : Scalar.QComplex := ((999993328214097002792099805487 : Int)/10^30,(3652879315453397287081551438 : Int)/10^30)
theorem v235_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 45 5) 1) 14) v235_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material235 : Material (2 : Basis) (45 : Basis) where
  plus := ![v235_pa,v235_pb,v235_pg]
  minus := ![(Primitive.Addresses.material235 1).one,v235_mb,v235_mg]
  upper := v235_upper
  lower := (Primitive.Addresses.material235 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v235_pa_checked.trans (by decide +kernel)
    · exact v235_pb_checked.trans (by decide +kernel)
    · exact v235_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 45 Primitive.Addresses.material235
    · exact v235_mb_checked.trans (by decide +kernel)
    · exact v235_mg_checked.trans (by decide +kernel)
  upper_error := v235_upper_checked
  lower_error := reuse_lower_error 2 45 Primitive.Addresses.material235

def v236_pa : Scalar.QComplex := ((999985622188825394493424893990 : Int)/10^30,(5362407633494197589285647326 : Int)/10^30)
theorem v236_pa_checked : Scalar.distance (sourceCoefficient 2 46 1 0) v236_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v236_pb : Scalar.QComplex := ((2313742527569116146290989 : Int)/10^30,(-431468366292085179975896331 : Int)/10^30)
theorem v236_pb_checked : Scalar.distance (sourceCoefficient 2 46 1 1) v236_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v236_pg : Scalar.QComplex := ((-93084773194419801893886 : Int)/10^30,(-499165675249656393207 : Int)/10^30)
theorem v236_pg_checked : Scalar.distance (sourceCoefficient 2 46 1 2) v236_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v236_mb : Scalar.QComplex := ((1941403898560805625825805 : Int)/10^30,(-431470202292287528005518601 : Int)/10^30)
theorem v236_mb_checked : Scalar.distance (sourceCoefficient 2 46 3 1) v236_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v236_mg : Scalar.QComplex := ((-93085169292200710311419 : Int)/10^30,(-418837522503234331182 : Int)/10^30)
theorem v236_mg_checked : Scalar.distance (sourceCoefficient 2 46 3 2) v236_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v236_upper : Scalar.QComplex := ((999993387856809297595665395735 : Int)/10^30,(3636515180907022463771712493 : Int)/10^30)
theorem v236_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 46 5) 1) 14) v236_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material236 : Material (2 : Basis) (46 : Basis) where
  plus := ![v236_pa,v236_pb,v236_pg]
  minus := ![(Primitive.Addresses.material236 1).one,v236_mb,v236_mg]
  upper := v236_upper
  lower := (Primitive.Addresses.material236 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v236_pa_checked.trans (by decide +kernel)
    · exact v236_pb_checked.trans (by decide +kernel)
    · exact v236_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 46 Primitive.Addresses.material236
    · exact v236_mb_checked.trans (by decide +kernel)
    · exact v236_mg_checked.trans (by decide +kernel)
  upper_error := v236_upper_checked
  lower_error := reuse_lower_error 2 46 Primitive.Addresses.material236

def v237_pa : Scalar.QComplex := ((999985643298461670120125613486 : Int)/10^30,(5358469647369545291566080983 : Int)/10^30)
theorem v237_pa_checked : Scalar.distance (sourceCoefficient 2 47 1 0) v237_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v237_pb : Scalar.QComplex := ((2312043367251503619748759 : Int)/10^30,(-431468371771013823836197968 : Int)/10^30)
theorem v237_pb_checked : Scalar.distance (sourceCoefficient 2 47 1 1) v237_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v237_pg : Scalar.QComplex := ((-93084774767938273100274 : Int)/10^30,(-498799101336053214286 : Int)/10^30)
theorem v237_pg_checked : Scalar.distance (sourceCoefficient 2 47 1 2) v237_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v237_mb : Scalar.QComplex := ((1939704734147799483127943 : Int)/10^30,(-431470206304915305050553191 : Int)/10^30)
theorem v237_mb_checked : Scalar.distance (sourceCoefficient 2 47 3 1) v237_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v237_mg : Scalar.QComplex := ((-93085170549381818061616 : Int)/10^30,(-418470947368247801541 : Int)/10^30)
theorem v237_mg_checked : Scalar.distance (sourceCoefficient 2 47 3 2) v237_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v237_upper : Scalar.QComplex := ((999993402169807333059514139852 : Int)/10^30,(3632577164214220749888163074 : Int)/10^30)
theorem v237_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 47 5) 1) 14) v237_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material237 : Material (2 : Basis) (47 : Basis) where
  plus := ![v237_pa,v237_pb,v237_pg]
  minus := ![(Primitive.Addresses.material237 1).one,v237_mb,v237_mg]
  upper := v237_upper
  lower := (Primitive.Addresses.material237 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v237_pa_checked.trans (by decide +kernel)
    · exact v237_pb_checked.trans (by decide +kernel)
    · exact v237_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 47 Primitive.Addresses.material237
    · exact v237_mb_checked.trans (by decide +kernel)
    · exact v237_mg_checked.trans (by decide +kernel)
  upper_error := v237_upper_checked
  lower_error := reuse_lower_error 2 47 Primitive.Addresses.material237

def v238_pa : Scalar.QComplex := ((999985789908114118028815932176 : Int)/10^30,(5331039471346328079023460306 : Int)/10^30)
theorem v238_pa_checked : Scalar.distance (sourceCoefficient 2 48 1 0) v238_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v238_pb : Scalar.QComplex := ((2300207808845614552829012 : Int)/10^30,(-431468409687162979913185110 : Int)/10^30)
theorem v238_pb_checked : Scalar.distance (sourceCoefficient 2 48 1 1) v238_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v238_pg : Scalar.QComplex := ((-93084785681610807250320 : Int)/10^30,(-496245718347736424162 : Int)/10^30)
theorem v238_pg_checked : Scalar.distance (sourceCoefficient 2 48 1 2) v238_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v238_mb : Scalar.QComplex := ((1927869147428900680732916 : Int)/10^30,(-431470234007496492692806588 : Int)/10^30)
theorem v238_mb_checked : Scalar.distance (sourceCoefficient 2 48 3 1) v238_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v238_mg : Scalar.QComplex := ((-93085179259595769735998 : Int)/10^30,(-415917555912664329928 : Int)/10^30)
theorem v238_mg_checked : Scalar.distance (sourceCoefficient 2 48 3 2) v238_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v238_upper : Scalar.QComplex := ((999993501437246053170105864550 : Int)/10^30,(3605146776010068747789704554 : Int)/10^30)
theorem v238_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 48 5) 1) 14) v238_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material238 : Material (2 : Basis) (48 : Basis) where
  plus := ![v238_pa,v238_pb,v238_pg]
  minus := ![(Primitive.Addresses.material238 1).one,v238_mb,v238_mg]
  upper := v238_upper
  lower := (Primitive.Addresses.material238 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v238_pa_checked.trans (by decide +kernel)
    · exact v238_pb_checked.trans (by decide +kernel)
    · exact v238_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 48 Primitive.Addresses.material238
    · exact v238_mb_checked.trans (by decide +kernel)
    · exact v238_mg_checked.trans (by decide +kernel)
  upper_error := v238_upper_checked
  lower_error := reuse_lower_error 2 48 Primitive.Addresses.material238

def v239_pa : Scalar.QComplex := ((999985907152767711533959414037 : Int)/10^30,(5309001399155383483208446856 : Int)/10^30)
theorem v239_pa_checked : Scalar.distance (sourceCoefficient 2 49 1 0) v239_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v239_pb : Scalar.QComplex := ((2290698833251109034230769 : Int)/10^30,(-431468439836316904282690192 : Int)/10^30)
theorem v239_pb_checked : Scalar.distance (sourceCoefficient 2 49 1 1) v239_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v239_pg : Scalar.QComplex := ((-93084794390721585888482 : Int)/10^30,(-494194268264757819504 : Int)/10^30)
theorem v239_pg_checked : Scalar.distance (sourceCoefficient 2 49 1 2) v239_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v239_mb : Scalar.QComplex := ((1918360149357659388377976 : Int)/10^30,(-431470255950821521458866283 : Int)/10^30)
theorem v239_mb_checked : Scalar.distance (sourceCoefficient 2 49 3 1) v239_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v239_mg : Scalar.QComplex := ((-93085186198394277845570 : Int)/10^30,(-413866099077963988887 : Int)/10^30)
theorem v239_mg_checked : Scalar.distance (sourceCoefficient 2 49 3 2) v239_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v239_upper : Scalar.QComplex := ((999993580646011701257531464808 : Int)/10^30,(3583108534288608156073180296 : Int)/10^30)
theorem v239_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 49 5) 1) 14) v239_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material239 : Material (2 : Basis) (49 : Basis) where
  plus := ![v239_pa,v239_pb,v239_pg]
  minus := ![(Primitive.Addresses.material239 1).one,v239_mb,v239_mg]
  upper := v239_upper
  lower := (Primitive.Addresses.material239 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v239_pa_checked.trans (by decide +kernel)
    · exact v239_pb_checked.trans (by decide +kernel)
    · exact v239_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 49 Primitive.Addresses.material239
    · exact v239_mb_checked.trans (by decide +kernel)
    · exact v239_mg_checked.trans (by decide +kernel)
  upper_error := v239_upper_checked
  lower_error := reuse_lower_error 2 49 Primitive.Addresses.material239

def v240_pa : Scalar.QComplex := ((999985920821622686216748513594 : Int)/10^30,(5306426154330594873561360364 : Int)/10^30)
theorem v240_pa_checked : Scalar.distance (sourceCoefficient 2 50 1 0) v240_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v240_pb : Scalar.QComplex := ((2289587668026940670962936 : Int)/10^30,(-431468443341143453571792106 : Int)/10^30)
theorem v240_pb_checked : Scalar.distance (sourceCoefficient 2 50 1 1) v240_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v240_pg : Scalar.QComplex := ((-93084795404977169686984 : Int)/10^30,(-493954547381666102937 : Int)/10^30)
theorem v240_pg_checked : Scalar.distance (sourceCoefficient 2 50 1 2) v240_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v240_mb : Scalar.QComplex := ((1917248981522721160319049 : Int)/10^30,(-431470258496761222307505840 : Int)/10^30)
theorem v240_mb_checked : Scalar.distance (sourceCoefficient 2 50 3 1) v240_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v240_mg : Scalar.QComplex := ((-93085187005781158509998 : Int)/10^30,(-413626377408874424439 : Int)/10^30)
theorem v240_mg_checked : Scalar.distance (sourceCoefficient 2 50 3 2) v240_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v240_upper : Scalar.QComplex := ((999993589870207374586883294531 : Int)/10^30,(3580533269708140545975709881 : Int)/10^30)
theorem v240_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 50 5) 1) 14) v240_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material240 : Material (2 : Basis) (50 : Basis) where
  plus := ![v240_pa,v240_pb,v240_pg]
  minus := ![(Primitive.Addresses.material240 1).one,v240_mb,v240_mg]
  upper := v240_upper
  lower := (Primitive.Addresses.material240 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v240_pa_checked.trans (by decide +kernel)
    · exact v240_pb_checked.trans (by decide +kernel)
    · exact v240_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 50 Primitive.Addresses.material240
    · exact v240_mb_checked.trans (by decide +kernel)
    · exact v240_mg_checked.trans (by decide +kernel)
  upper_error := v240_upper_checked
  lower_error := reuse_lower_error 2 50 Primitive.Addresses.material240

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
