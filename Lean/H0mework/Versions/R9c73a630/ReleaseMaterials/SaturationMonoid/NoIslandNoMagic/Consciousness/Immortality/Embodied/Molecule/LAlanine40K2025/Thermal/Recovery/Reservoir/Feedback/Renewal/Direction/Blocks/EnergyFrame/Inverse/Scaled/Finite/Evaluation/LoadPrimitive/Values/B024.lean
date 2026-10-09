import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B016

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v385_pa : Scalar.QComplex := ((999991222433018386605867563250 : Int)/10^30,(4189875525304382065158167600 : Int)/10^30)
theorem v385_pa_checked : Scalar.distance (sourceCoefficient 4 8 1 0) v385_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v385_pb : Scalar.QComplex := ((1807832386661966769514339 : Int)/10^30,(-431472607568877309486477178 : Int)/10^30)
theorem v385_pb_checked : Scalar.distance (sourceCoefficient 4 8 1 1) v385_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v385_pg : Scalar.QComplex := ((-93085491351893549364001 : Int)/10^30,(-390020045403304198379 : Int)/10^30)
theorem v385_pg_checked : Scalar.distance (sourceCoefficient 4 8 1 2) v385_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v385_mb : Scalar.QComplex := ((1435490285996271352386123 : Int)/10^30,(-431474006989834180375174249 : Int)/10^30)
theorem v385_mb_checked : Scalar.distance (sourceCoefficient 4 8 3 1) v385_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v385_mg : Scalar.QComplex := ((-93085793261644234218251 : Int)/10^30,(-309691313559233097720 : Int)/10^30)
theorem v385_mg_checked : Scalar.distance (sourceCoefficient 4 8 3 2) v385_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v385_upper : Scalar.QComplex := ((999996964408613930140071654042 : Int)/10^30,(2463975153552619871701510287 : Int)/10^30)
theorem v385_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 8 5) 1) 14) v385_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material385 : Material (4 : Basis) (8 : Basis) where
  plus := ![v385_pa,v385_pb,v385_pg]
  minus := ![(Primitive.Addresses.material385 1).one,v385_mb,v385_mg]
  upper := v385_upper
  lower := (Primitive.Addresses.material385 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v385_pa_checked.trans (by decide +kernel)
    · exact v385_pb_checked.trans (by decide +kernel)
    · exact v385_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 8 Primitive.Addresses.material385
    · exact v385_mb_checked.trans (by decide +kernel)
    · exact v385_mg_checked.trans (by decide +kernel)
  upper_error := v385_upper_checked
  lower_error := reuse_lower_error 4 8 Primitive.Addresses.material385

def v386_pa : Scalar.QComplex := ((999991310862666610232117621048 : Int)/10^30,(4168716728883354729126054286 : Int)/10^30)
theorem v386_pa_checked : Scalar.distance (sourceCoefficient 4 9 1 0) v386_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v386_pb : Scalar.QComplex := ((1798702815125833489244723 : Int)/10^30,(-431472633649505079700514480 : Int)/10^30)
theorem v386_pb_checked : Scalar.distance (sourceCoefficient 4 9 1 1) v386_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v386_pg : Scalar.QComplex := ((-93085498280994288103234 : Int)/10^30,(-388050445724038827694 : Int)/10^30)
theorem v386_pg_checked : Scalar.distance (sourceCoefficient 4 9 1 2) v386_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v386_mb : Scalar.QComplex := ((1426360695353087659226124 : Int)/10^30,(-431474025192043184534772928 : Int)/10^30)
theorem v386_mb_checked : Scalar.distance (sourceCoefficient 4 9 3 1) v386_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v386_mg : Scalar.QComplex := ((-93085798491066577207167 : Int)/10^30,(-307721708633837840358 : Int)/10^30)
theorem v386_mg_checked : Scalar.distance (sourceCoefficient 4 9 3 2) v386_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v386_upper : Scalar.QComplex := ((999997016319967336516705208066 : Int)/10^30,(2442816236023583759007439846 : Int)/10^30)
theorem v386_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 9 5) 1) 14) v386_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material386 : Material (4 : Basis) (9 : Basis) where
  plus := ![v386_pa,v386_pb,v386_pg]
  minus := ![(Primitive.Addresses.material386 1).one,v386_mb,v386_mg]
  upper := v386_upper
  lower := (Primitive.Addresses.material386 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v386_pa_checked.trans (by decide +kernel)
    · exact v386_pb_checked.trans (by decide +kernel)
    · exact v386_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 9 Primitive.Addresses.material386
    · exact v386_mb_checked.trans (by decide +kernel)
    · exact v386_mg_checked.trans (by decide +kernel)
  upper_error := v386_upper_checked
  lower_error := reuse_lower_error 4 9 Primitive.Addresses.material386

def v387_pa : Scalar.QComplex := ((999991484550975610612809914958 : Int)/10^30,(4126842077897661376175575065 : Int)/10^30)
theorem v387_pa_checked : Scalar.distance (sourceCoefficient 4 10 1 0) v387_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v387_pb : Scalar.QComplex := ((1780634792785607837996281 : Int)/10^30,(-431472684505509478510149298 : Int)/10^30)
theorem v387_pb_checked : Scalar.distance (sourceCoefficient 4 10 1 1) v387_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v387_pg : Scalar.QComplex := ((-93085511850811158698292 : Int)/10^30,(-384152478379416137732 : Int)/10^30)
theorem v387_pg_checked : Scalar.distance (sourceCoefficient 4 10 1 2) v387_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v387_mb : Scalar.QComplex := ((1408292635853971147896674 : Int)/10^30,(-431474060456139121233252050 : Int)/10^30)
theorem v387_mb_checked : Scalar.distance (sourceCoefficient 4 10 3 1) v387_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v387_mg : Scalar.QComplex := ((-93085808697108134662036 : Int)/10^30,(-303823731030465741248 : Int)/10^30)
theorem v387_mg_checked : Scalar.distance (sourceCoefficient 4 10 3 2) v387_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v387_upper : Scalar.QComplex := ((999997117736168885919799220550 : Int)/10^30,(2400941347634999652855043416 : Int)/10^30)
theorem v387_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 10 5) 1) 14) v387_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material387 : Material (4 : Basis) (10 : Basis) where
  plus := ![v387_pa,v387_pb,v387_pg]
  minus := ![(Primitive.Addresses.material387 1).one,v387_mb,v387_mg]
  upper := v387_upper
  lower := (Primitive.Addresses.material387 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v387_pa_checked.trans (by decide +kernel)
    · exact v387_pb_checked.trans (by decide +kernel)
    · exact v387_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 10 Primitive.Addresses.material387
    · exact v387_mb_checked.trans (by decide +kernel)
    · exact v387_mg_checked.trans (by decide +kernel)
  upper_error := v387_upper_checked
  lower_error := reuse_lower_error 4 10 Primitive.Addresses.material387

def v388_pa : Scalar.QComplex := ((999991521705605829726560327967 : Int)/10^30,(4117829149790543782057623618 : Int)/10^30)
theorem v388_pa_checked : Scalar.distance (sourceCoefficient 4 11 1 0) v388_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v388_pb : Scalar.QComplex := ((1776745905900654263052421 : Int)/10^30,(-431472695319613986281649075 : Int)/10^30)
theorem v388_pb_checked : Scalar.distance (sourceCoefficient 4 11 1 1) v388_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v388_pg : Scalar.QComplex := ((-93085514746617606186851 : Int)/10^30,(-383313495891542929874 : Int)/10^30)
theorem v388_pg_checked : Scalar.distance (sourceCoefficient 4 11 1 2) v388_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v388_mb : Scalar.QComplex := ((1404403741084942750111869 : Int)/10^30,(-431474067914305369667942579 : Int)/10^30)
theorem v388_mb_checked : Scalar.distance (sourceCoefficient 4 11 3 1) v388_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v388_mg : Scalar.QComplex := ((-93085810868909403243489 : Int)/10^30,(-302984746356033515117 : Int)/10^30)
theorem v388_mg_checked : Scalar.distance (sourceCoefficient 4 11 3 2) v388_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v388_upper : Scalar.QComplex := ((999997139335247501142134418903 : Int)/10^30,(2391928368826058624914492578 : Int)/10^30)
theorem v388_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 11 5) 1) 14) v388_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material388 : Material (4 : Basis) (11 : Basis) where
  plus := ![v388_pa,v388_pb,v388_pg]
  minus := ![(Primitive.Addresses.material388 1).one,v388_mb,v388_mg]
  upper := v388_upper
  lower := (Primitive.Addresses.material388 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v388_pa_checked.trans (by decide +kernel)
    · exact v388_pb_checked.trans (by decide +kernel)
    · exact v388_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 11 Primitive.Addresses.material388
    · exact v388_mb_checked.trans (by decide +kernel)
    · exact v388_mg_checked.trans (by decide +kernel)
  upper_error := v388_upper_checked
  lower_error := reuse_lower_error 4 11 Primitive.Addresses.material388

def v389_pa : Scalar.QComplex := ((999991541958560165106366900118 : Int)/10^30,(4112907893596061227248574935 : Int)/10^30)
theorem v389_pa_checked : Scalar.distance (sourceCoefficient 4 12 1 0) v389_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v389_pb : Scalar.QComplex := ((1774622488486269453834131 : Int)/10^30,(-431472701204626180584735920 : Int)/10^30)
theorem v389_pb_checked : Scalar.distance (sourceCoefficient 4 12 1 1) v389_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v389_pg : Scalar.QComplex := ((-93085516324067696949615 : Int)/10^30,(-382855393075503140632 : Int)/10^30)
theorem v389_pg_checked : Scalar.distance (sourceCoefficient 4 12 1 2) v389_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v389_mb : Scalar.QComplex := ((1402280319382702816665506 : Int)/10^30,(-431474071966901779268140284 : Int)/10^30)
theorem v389_mb_checked : Scalar.distance (sourceCoefficient 4 12 3 1) v389_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v389_mg : Scalar.QComplex := ((-93085812051036808592085 : Int)/10^30,(-302526642349297958007 : Int)/10^30)
theorem v389_mg_checked : Scalar.distance (sourceCoefficient 4 12 3 2) v389_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v389_upper : Scalar.QComplex := ((999997151094529933323112970199 : Int)/10^30,(2387007085006447231225198652 : Int)/10^30)
theorem v389_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 12 5) 1) 14) v389_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material389 : Material (4 : Basis) (12 : Basis) where
  plus := ![v389_pa,v389_pb,v389_pg]
  minus := ![(Primitive.Addresses.material389 1).one,v389_mb,v389_mg]
  upper := v389_upper
  lower := (Primitive.Addresses.material389 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v389_pa_checked.trans (by decide +kernel)
    · exact v389_pb_checked.trans (by decide +kernel)
    · exact v389_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 12 Primitive.Addresses.material389
    · exact v389_mb_checked.trans (by decide +kernel)
    · exact v389_mg_checked.trans (by decide +kernel)
  upper_error := v389_upper_checked
  lower_error := reuse_lower_error 4 12 Primitive.Addresses.material389

def v390_pa : Scalar.QComplex := ((999991752508872869607458389448 : Int)/10^30,(4061393139447459719248333497 : Int)/10^30)
theorem v390_pa_checked : Scalar.distance (sourceCoefficient 4 13 1 0) v390_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v390_pb : Scalar.QComplex := ((1752394968191394055439556 : Int)/10^30,(-431472761971486648546177025 : Int)/10^30)
theorem v390_pb_checked : Scalar.distance (sourceCoefficient 4 13 1 1) v390_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v390_pg : Scalar.QComplex := ((-93085532678638289467981 : Int)/10^30,(-378060061849839495945 : Int)/10^30)
theorem v390_pg_checked : Scalar.distance (sourceCoefficient 4 13 1 2) v390_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v390_mb : Scalar.QComplex := ((1380052754925085325862979 : Int)/10^30,(-431474113552390696824638135 : Int)/10^30)
theorem v390_mb_checked : Scalar.distance (sourceCoefficient 4 13 3 1) v390_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v390_mg : Scalar.QComplex := ((-93085824267446437509736 : Int)/10^30,(-297731298795897447271 : Int)/10^30)
theorem v390_mg_checked : Scalar.distance (sourceCoefficient 4 13 3 2) v390_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v390_upper : Scalar.QComplex := ((999997272734736769370109863173 : Int)/10^30,(2335492044192281926651627701 : Int)/10^30)
theorem v390_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 13 5) 1) 14) v390_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material390 : Material (4 : Basis) (13 : Basis) where
  plus := ![v390_pa,v390_pb,v390_pg]
  minus := ![(Primitive.Addresses.material390 1).one,v390_mb,v390_mg]
  upper := v390_upper
  lower := (Primitive.Addresses.material390 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v390_pa_checked.trans (by decide +kernel)
    · exact v390_pb_checked.trans (by decide +kernel)
    · exact v390_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 13 Primitive.Addresses.material390
    · exact v390_mb_checked.trans (by decide +kernel)
    · exact v390_mg_checked.trans (by decide +kernel)
  upper_error := v390_upper_checked
  lower_error := reuse_lower_error 4 13 Primitive.Addresses.material390

def v391_pa : Scalar.QComplex := ((999991818618533401162301035500 : Int)/10^30,(4045082940830134992274276712 : Int)/10^30)
theorem v391_pa_checked : Scalar.distance (sourceCoefficient 4 14 1 0) v391_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v391_pb : Scalar.QComplex := ((1745357464857205739482443 : Int)/10^30,(-431472780892796604356947818 : Int)/10^30)
theorem v391_pb_checked : Scalar.distance (sourceCoefficient 4 14 1 1) v391_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v391_pg : Scalar.QComplex := ((-93085537796623934130380 : Int)/10^30,(-376541801611239329676 : Int)/10^30)
theorem v391_pg_checked : Scalar.distance (sourceCoefficient 4 14 1 2) v391_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v391_mb : Scalar.QComplex := ((1373015237883042823316535 : Int)/10^30,(-431474126400645187346609800 : Int)/10^30)
theorem v391_mb_checked : Scalar.distance (sourceCoefficient 4 14 3 1) v391_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v391_mg : Scalar.QComplex := ((-93085828075239970502998 : Int)/10^30,(-296213034706023849926 : Int)/10^30)
theorem v391_mg_checked : Scalar.distance (sourceCoefficient 4 14 3 2) v391_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v391_upper : Scalar.QComplex := ((999997310694375674509073103562 : Int)/10^30,(2319181755767805453756860650 : Int)/10^30)
theorem v391_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 14 5) 1) 14) v391_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material391 : Material (4 : Basis) (14 : Basis) where
  plus := ![v391_pa,v391_pb,v391_pg]
  minus := ![(Primitive.Addresses.material391 1).one,v391_mb,v391_mg]
  upper := v391_upper
  lower := (Primitive.Addresses.material391 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v391_pa_checked.trans (by decide +kernel)
    · exact v391_pb_checked.trans (by decide +kernel)
    · exact v391_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 14 Primitive.Addresses.material391
    · exact v391_mb_checked.trans (by decide +kernel)
    · exact v391_mg_checked.trans (by decide +kernel)
  upper_error := v391_upper_checked
  lower_error := reuse_lower_error 4 14 Primitive.Addresses.material391

def v392_pa : Scalar.QComplex := ((999991924570681294546699421908 : Int)/10^30,(4018804974722240137872997444 : Int)/10^30)
theorem v392_pa_checked : Scalar.distance (sourceCoefficient 4 15 1 0) v392_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v392_pb : Scalar.QComplex := ((1734019082476552105324655 : Int)/10^30,(-431472811055694512261479250 : Int)/10^30)
theorem v392_pb_checked : Scalar.distance (sourceCoefficient 4 15 1 1) v392_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v392_pg : Scalar.QComplex := ((-93085545981629851679738 : Int)/10^30,(-374095676248901859447 : Int)/10^30)
theorem v392_pg_checked : Scalar.distance (sourceCoefficient 4 15 1 2) v392_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v392_mb : Scalar.QComplex := ((1361676833694964731120752 : Int)/10^30,(-431474146779018531507419393 : Int)/10^30)
theorem v392_mb_checked : Scalar.distance (sourceCoefficient 4 15 3 1) v392_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v392_mg : Scalar.QComplex := ((-93085834149346822099982 : Int)/10^30,(-293766903191199177684 : Int)/10^30)
theorem v392_mg_checked : Scalar.distance (sourceCoefficient 4 15 3 2) v392_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v392_upper : Scalar.QComplex := ((999997371292980180851838314201 : Int)/10^30,(2292903645934058930119526515 : Int)/10^30)
theorem v392_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 15 5) 1) 14) v392_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material392 : Material (4 : Basis) (15 : Basis) where
  plus := ![v392_pa,v392_pb,v392_pg]
  minus := ![(Primitive.Addresses.material392 1).one,v392_mb,v392_mg]
  upper := v392_upper
  lower := (Primitive.Addresses.material392 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v392_pa_checked.trans (by decide +kernel)
    · exact v392_pb_checked.trans (by decide +kernel)
    · exact v392_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 15 Primitive.Addresses.material392
    · exact v392_mb_checked.trans (by decide +kernel)
    · exact v392_mg_checked.trans (by decide +kernel)
  upper_error := v392_upper_checked
  lower_error := reuse_lower_error 4 15 Primitive.Addresses.material392

def v393_pa : Scalar.QComplex := ((999991937957627061629094704943 : Int)/10^30,(4015472543717553394476896114 : Int)/10^30)
theorem v393_pa_checked : Scalar.distance (sourceCoefficient 4 16 1 0) v393_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v393_pb : Scalar.QComplex := ((1732581209543494630795593 : Int)/10^30,(-431472814852407260354029587 : Int)/10^30)
theorem v393_pb_checked : Scalar.distance (sourceCoefficient 4 16 1 1) v393_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v393_pg : Scalar.QComplex := ((-93085547014250296797340 : Int)/10^30,(-373785471726962998289 : Int)/10^30)
theorem v393_pg_checked : Scalar.distance (sourceCoefficient 4 16 1 2) v393_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v393_mb : Scalar.QComplex := ((1360238958020900959598942 : Int)/10^30,(-431474149334910284074617995 : Int)/10^30)
theorem v393_mb_checked : Scalar.distance (sourceCoefficient 4 16 3 1) v393_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v393_mg : Scalar.QComplex := ((-93085834914274351385600 : Int)/10^30,(-293456697893658700453 : Int)/10^30)
theorem v393_mg_checked : Scalar.distance (sourceCoefficient 4 16 3 2) v393_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v393_upper : Scalar.QComplex := ((999997378928432411340919454186 : Int)/10^30,(2289571196787982773609295576 : Int)/10^30)
theorem v393_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 16 5) 1) 14) v393_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material393 : Material (4 : Basis) (16 : Basis) where
  plus := ![v393_pa,v393_pb,v393_pg]
  minus := ![(Primitive.Addresses.material393 1).one,v393_mb,v393_mg]
  upper := v393_upper
  lower := (Primitive.Addresses.material393 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v393_pa_checked.trans (by decide +kernel)
    · exact v393_pb_checked.trans (by decide +kernel)
    · exact v393_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 16 Primitive.Addresses.material393
    · exact v393_mb_checked.trans (by decide +kernel)
    · exact v393_mg_checked.trans (by decide +kernel)
  upper_error := v393_upper_checked
  lower_error := reuse_lower_error 4 16 Primitive.Addresses.material393

def v394_pa : Scalar.QComplex := ((999991964804546374412118325540 : Int)/10^30,(4008781154276845504492119526 : Int)/10^30)
theorem v394_pa_checked : Scalar.distance (sourceCoefficient 4 17 1 0) v394_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v394_pb : Scalar.QComplex := ((1729694017676813406315290 : Int)/10^30,(-431472822456761902597810622 : Int)/10^30)
theorem v394_pb_checked : Scalar.distance (sourceCoefficient 4 17 1 1) v394_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v394_pg : Scalar.QComplex := ((-93085549084069053062507 : Int)/10^30,(-373162593338101750798 : Int)/10^30)
theorem v394_pg_checked : Scalar.distance (sourceCoefficient 4 17 1 2) v394_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v394_mb : Scalar.QComplex := ((1357351760667037649433860 : Int)/10^30,(-431474154447745548218308229 : Int)/10^30)
theorem v394_mb_checked : Scalar.distance (sourceCoefficient 4 17 3 1) v394_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v394_mg : Scalar.QComplex := ((-93085836446576340776635 : Int)/10^30,(-292833817950563178603 : Int)/10^30)
theorem v394_mg_checked : Scalar.distance (sourceCoefficient 4 17 3 2) v394_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v394_upper : Scalar.QComplex := ((999997394226580602237608793820 : Int)/10^30,(2282879770977966229371126637 : Int)/10^30)
theorem v394_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 17 5) 1) 14) v394_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material394 : Material (4 : Basis) (17 : Basis) where
  plus := ![v394_pa,v394_pb,v394_pg]
  minus := ![(Primitive.Addresses.material394 1).one,v394_mb,v394_mg]
  upper := v394_upper
  lower := (Primitive.Addresses.material394 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v394_pa_checked.trans (by decide +kernel)
    · exact v394_pb_checked.trans (by decide +kernel)
    · exact v394_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 17 Primitive.Addresses.material394
    · exact v394_mb_checked.trans (by decide +kernel)
    · exact v394_mg_checked.trans (by decide +kernel)
  upper_error := v394_upper_checked
  lower_error := reuse_lower_error 4 17 Primitive.Addresses.material394

def v395_pa : Scalar.QComplex := ((999992054031887557920649481984 : Int)/10^30,(3986461223500727186609826416 : Int)/10^30)
theorem v395_pa_checked : Scalar.distance (sourceCoefficient 4 18 1 0) v395_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v395_pb : Scalar.QComplex := ((1720063443662550929798327 : Int)/10^30,(-431472847635730288592462422 : Int)/10^30)
theorem v395_pb_checked : Scalar.distance (sourceCoefficient 4 18 1 1) v395_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v395_pg : Scalar.QComplex := ((-93085555953035403289981 : Int)/10^30,(-371084907903628123643 : Int)/10^30)
theorem v395_pg_checked : Scalar.distance (sourceCoefficient 4 18 1 2) v395_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v395_mb : Scalar.QComplex := ((1347721168510362318928545 : Int)/10^30,(-431474171315952929576009890 : Int)/10^30)
theorem v395_mb_checked : Scalar.distance (sourceCoefficient 4 18 3 1) v395_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v395_mg : Scalar.QComplex := ((-93085841522591178901553 : Int)/10^30,(-290756127362098200132 : Int)/10^30)
theorem v395_mg_checked : Scalar.distance (sourceCoefficient 4 18 3 2) v395_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v395_upper : Scalar.QComplex := ((999997444931613220825372759336 : Int)/10^30,(2260559719446466677695428846 : Int)/10^30)
theorem v395_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 18 5) 1) 14) v395_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material395 : Material (4 : Basis) (18 : Basis) where
  plus := ![v395_pa,v395_pb,v395_pg]
  minus := ![(Primitive.Addresses.material395 1).one,v395_mb,v395_mg]
  upper := v395_upper
  lower := (Primitive.Addresses.material395 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v395_pa_checked.trans (by decide +kernel)
    · exact v395_pb_checked.trans (by decide +kernel)
    · exact v395_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 18 Primitive.Addresses.material395
    · exact v395_mb_checked.trans (by decide +kernel)
    · exact v395_mg_checked.trans (by decide +kernel)
  upper_error := v395_upper_checked
  lower_error := reuse_lower_error 4 18 Primitive.Addresses.material395

def v396_pa : Scalar.QComplex := ((999992116304104159345814488071 : Int)/10^30,(3970809695643991735145872357 : Int)/10^30)
theorem v396_pa_checked : Scalar.distance (sourceCoefficient 4 19 1 0) v396_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v396_pb : Scalar.QComplex := ((1713310143446535242529620 : Int)/10^30,(-431472865121158643650258674 : Int)/10^30)
theorem v396_pb_checked : Scalar.distance (sourceCoefficient 4 19 1 1) v396_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v396_pg : Scalar.QComplex := ((-93085560737526396897818 : Int)/10^30,(-369627961135467690532 : Int)/10^30)
theorem v396_pg_checked : Scalar.distance (sourceCoefficient 4 19 1 2) v396_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v396_mb : Scalar.QComplex := ((1340967855719771787193851 : Int)/10^30,(-431474182973580844939045638 : Int)/10^30)
theorem v396_mb_checked : Scalar.distance (sourceCoefficient 4 19 3 1) v396_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v396_mg : Scalar.QComplex := ((-93085845049800948548844 : Int)/10^30,(-289299177007625392555 : Int)/10^30)
theorem v396_mg_checked : Scalar.distance (sourceCoefficient 4 19 3 2) v396_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v396_upper : Scalar.QComplex := ((999997480190619889889077091861 : Int)/10^30,(2244908107424646848525653517 : Int)/10^30)
theorem v396_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 19 5) 1) 14) v396_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material396 : Material (4 : Basis) (19 : Basis) where
  plus := ![v396_pa,v396_pb,v396_pg]
  minus := ![(Primitive.Addresses.material396 1).one,v396_mb,v396_mg]
  upper := v396_upper
  lower := (Primitive.Addresses.material396 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v396_pa_checked.trans (by decide +kernel)
    · exact v396_pb_checked.trans (by decide +kernel)
    · exact v396_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 19 Primitive.Addresses.material396
    · exact v396_mb_checked.trans (by decide +kernel)
    · exact v396_mg_checked.trans (by decide +kernel)
  upper_error := v396_upper_checked
  lower_error := reuse_lower_error 4 19 Primitive.Addresses.material396

def v397_pa : Scalar.QComplex := ((999992127440009924640005607844 : Int)/10^30,(3968004284643594314856571894 : Int)/10^30)
theorem v397_pa_checked : Scalar.distance (sourceCoefficient 4 20 1 0) v397_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v397_pb : Scalar.QComplex := ((1712099668492665491528029 : Int)/10^30,(-431472868240386912311075120 : Int)/10^30)
theorem v397_pb_checked : Scalar.distance (sourceCoefficient 4 20 1 1) v397_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v397_pg : Scalar.QComplex := ((-93085561592296384347027 : Int)/10^30,(-369366815099097463441 : Int)/10^30)
theorem v397_pg_checked : Scalar.distance (sourceCoefficient 4 20 1 2) v397_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v397_mb : Scalar.QComplex := ((1339757378524863671928189 : Int)/10^30,(-431474185048222584747154384 : Int)/10^30)
theorem v397_mb_checked : Scalar.distance (sourceCoefficient 4 20 3 1) v397_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v397_mg : Scalar.QComplex := ((-93085845679213349921483 : Int)/10^30,(-289038030330863768010 : Int)/10^30)
theorem v397_mg_checked : Scalar.distance (sourceCoefficient 4 20 3 2) v397_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v397_upper : Scalar.QComplex := ((999997486484624187771671662480 : Int)/10^30,(2242102681383016457184489285 : Int)/10^30)
theorem v397_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 20 5) 1) 14) v397_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material397 : Material (4 : Basis) (20 : Basis) where
  plus := ![v397_pa,v397_pb,v397_pg]
  minus := ![(Primitive.Addresses.material397 1).one,v397_mb,v397_mg]
  upper := v397_upper
  lower := (Primitive.Addresses.material397 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v397_pa_checked.trans (by decide +kernel)
    · exact v397_pb_checked.trans (by decide +kernel)
    · exact v397_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 20 Primitive.Addresses.material397
    · exact v397_mb_checked.trans (by decide +kernel)
    · exact v397_mg_checked.trans (by decide +kernel)
  upper_error := v397_upper_checked
  lower_error := reuse_lower_error 4 20 Primitive.Addresses.material397

def v398_pa : Scalar.QComplex := ((999992336374288807034051817440 : Int)/10^30,(3914995873717734921218504706 : Int)/10^30)
theorem v398_pa_checked : Scalar.distance (sourceCoefficient 4 21 1 0) v398_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v398_pb : Scalar.QComplex := ((1689227671801031498948758 : Int)/10^30,(-431472926327330163994071558 : Int)/10^30)
theorem v398_pb_checked : Scalar.distance (sourceCoefficient 4 21 1 1) v398_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v398_pg : Scalar.QComplex := ((-93085577582570290304754 : Int)/10^30,(-364432445012250361767 : Int)/10^30)
theorem v398_pg_checked : Scalar.distance (sourceCoefficient 4 21 1 2) v398_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v398_mb : Scalar.QComplex := ((1316885340223103462138015 : Int)/10^30,(-431474223397641179617607738 : Int)/10^30)
theorem v398_mb_checked : Scalar.distance (sourceCoefficient 4 21 3 1) v398_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v398_mg : Scalar.QComplex := ((-93085857411342152799326 : Int)/10^30,(-284103648282421955884 : Int)/10^30)
theorem v398_mg_checked : Scalar.distance (sourceCoefficient 4 21 3 2) v398_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v398_upper : Scalar.QComplex := ((999997603930883514541395729764 : Int)/10^30,(2189093988805347350962094410 : Int)/10^30)
theorem v398_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 21 5) 1) 14) v398_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material398 : Material (4 : Basis) (21 : Basis) where
  plus := ![v398_pa,v398_pb,v398_pg]
  minus := ![(Primitive.Addresses.material398 1).one,v398_mb,v398_mg]
  upper := v398_upper
  lower := (Primitive.Addresses.material398 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v398_pa_checked.trans (by decide +kernel)
    · exact v398_pb_checked.trans (by decide +kernel)
    · exact v398_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 21 Primitive.Addresses.material398
    · exact v398_mb_checked.trans (by decide +kernel)
    · exact v398_mg_checked.trans (by decide +kernel)
  upper_error := v398_upper_checked
  lower_error := reuse_lower_error 4 21 Primitive.Addresses.material398

def v399_pa : Scalar.QComplex := ((999992341831205316451936222084 : Int)/10^30,(3913601786311147965450115826 : Int)/10^30)
theorem v399_pa_checked : Scalar.distance (sourceCoefficient 4 22 1 0) v399_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v399_pb : Scalar.QComplex := ((1688626152896878791738393 : Int)/10^30,(-431472927833163265704136017 : Int)/10^30)
theorem v399_pb_checked : Scalar.distance (sourceCoefficient 4 22 1 1) v399_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v399_pg : Scalar.QComplex := ((-93085577998985965538118 : Int)/10^30,(-364302674228008761829 : Int)/10^30)
theorem v399_pg_checked : Scalar.distance (sourceCoefficient 4 22 1 2) v399_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v399_mb : Scalar.QComplex := ((1316283820243457587145205 : Int)/10^30,(-431474224384389997759164919 : Int)/10^30)
theorem v399_mb_checked : Scalar.distance (sourceCoefficient 4 22 3 1) v399_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v399_mg : Scalar.QComplex := ((-93085857715771330840761 : Int)/10^30,(-283973877187151976677 : Int)/10^30)
theorem v399_mg_checked : Scalar.distance (sourceCoefficient 4 22 3 2) v399_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v399_upper : Scalar.QComplex := ((999997606981723503375659431235 : Int)/10^30,(2187699894056946978637981175 : Int)/10^30)
theorem v399_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 22 5) 1) 14) v399_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material399 : Material (4 : Basis) (22 : Basis) where
  plus := ![v399_pa,v399_pb,v399_pg]
  minus := ![(Primitive.Addresses.material399 1).one,v399_mb,v399_mg]
  upper := v399_upper
  lower := (Primitive.Addresses.material399 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v399_pa_checked.trans (by decide +kernel)
    · exact v399_pb_checked.trans (by decide +kernel)
    · exact v399_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 22 Primitive.Addresses.material399
    · exact v399_mb_checked.trans (by decide +kernel)
    · exact v399_mg_checked.trans (by decide +kernel)
  upper_error := v399_upper_checked
  lower_error := reuse_lower_error 4 22 Primitive.Addresses.material399

def v400_pa : Scalar.QComplex := ((999992382122400920479208724716 : Int)/10^30,(3903293118137546050028356976 : Int)/10^30)
theorem v400_pa_checked : Scalar.distance (sourceCoefficient 4 23 1 0) v400_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v400_pb : Scalar.QComplex := ((1684178183064728408514477 : Int)/10^30,(-431472938933439172688635344 : Int)/10^30)
theorem v400_pb_checked : Scalar.distance (sourceCoefficient 4 23 1 1) v400_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v400_pg : Scalar.QComplex := ((-93085581071647281827220 : Int)/10^30,(-363343075897874117136 : Int)/10^30)
theorem v400_pg_checked : Scalar.distance (sourceCoefficient 4 23 1 2) v400_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v400_mb : Scalar.QComplex := ((1311835842488451484835215 : Int)/10^30,(-431474231646264135582529069 : Int)/10^30)
theorem v400_mb_checked : Scalar.distance (sourceCoefficient 4 23 3 1) v400_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v400_mg : Scalar.QComplex := ((-93085859960341362835864 : Int)/10^30,(-283014276562751317674 : Int)/10^30)
theorem v400_mg_checked : Scalar.distance (sourceCoefficient 4 23 3 2) v400_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v400_upper : Scalar.QComplex := ((999997629481033025834476197305 : Int)/10^30,(2177391171697946942729980061 : Int)/10^30)
theorem v400_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 23 5) 1) 14) v400_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material400 : Material (4 : Basis) (23 : Basis) where
  plus := ![v400_pa,v400_pb,v400_pg]
  minus := ![(Primitive.Addresses.material400 1).one,v400_mb,v400_mg]
  upper := v400_upper
  lower := (Primitive.Addresses.material400 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v400_pa_checked.trans (by decide +kernel)
    · exact v400_pb_checked.trans (by decide +kernel)
    · exact v400_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 23 Primitive.Addresses.material400
    · exact v400_mb_checked.trans (by decide +kernel)
    · exact v400_mg_checked.trans (by decide +kernel)
  upper_error := v400_upper_checked
  lower_error := reuse_lower_error 4 23 Primitive.Addresses.material400

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
