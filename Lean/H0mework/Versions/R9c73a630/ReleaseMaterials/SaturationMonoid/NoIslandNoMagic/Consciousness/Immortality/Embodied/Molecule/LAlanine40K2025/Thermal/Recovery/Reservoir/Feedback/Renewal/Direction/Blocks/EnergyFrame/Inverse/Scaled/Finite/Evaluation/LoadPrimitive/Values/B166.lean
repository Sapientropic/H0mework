import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B110
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B111

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2657_pa : Scalar.QComplex := ((999999015309055802465355551463 : Int)/10^30,(-1403346328879230618363701836 : Int)/10^30)
theorem v2657_pa_checked : Scalar.distance (sourceCoefficient 32 82 1 0) v2657_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2657_pb : Scalar.QComplex := ((-605512329380000572007031 : Int)/10^30,(-431477049304771044867615011 : Int)/10^30)
theorem v2657_pb_checked : Scalar.distance (sourceCoefficient 32 82 1 1) v2657_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2657_pg : Scalar.QComplex := ((-93086333184748982801503 : Int)/10^30,(130632492576278842717 : Int)/10^30)
theorem v2657_pg_checked : Scalar.distance (sourceCoefficient 32 82 1 2) v2657_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2657_mb : Scalar.QComplex := ((-977857364465190839613426 : Int)/10^30,(-431476366116277121404195962 : Int)/10^30)
theorem v2657_mb_checked : Scalar.distance (sourceCoefficient 32 82 3 1) v2657_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2657_mg : Scalar.QComplex := ((-93086185794495258260780 : Int)/10^30,(210961757021454551804 : Int)/10^30)
theorem v2657_mg_checked : Scalar.distance (sourceCoefficient 32 82 3 2) v2657_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2657_upper : Scalar.QComplex := ((999995103879537574559602996920 : Int)/10^30,(-3129251819981143386040675648 : Int)/10^30)
theorem v2657_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 82 5) 1) 14) v2657_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2657 : Material (32 : Basis) (82 : Basis) where
  plus := ![v2657_pa,v2657_pb,v2657_pg]
  minus := ![(Primitive.Addresses.material2657 1).one,v2657_mb,v2657_mg]
  upper := v2657_upper
  lower := (Primitive.Addresses.material2657 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2657_pa_checked.trans (by decide +kernel)
    · exact v2657_pb_checked.trans (by decide +kernel)
    · exact v2657_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 82 Primitive.Addresses.material2657
    · exact v2657_mb_checked.trans (by decide +kernel)
    · exact v2657_mg_checked.trans (by decide +kernel)
  upper_error := v2657_upper_checked
  lower_error := reuse_lower_error 32 82 Primitive.Addresses.material2657

def v2658_pa : Scalar.QComplex := ((999998996175527944291603081100 : Int)/10^30,(-1416914936207479639368084313 : Int)/10^30)
theorem v2658_pa_checked : Scalar.distance (sourceCoefficient 32 83 1 0) v2658_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2658_pb : Scalar.QComplex := ((-611366875548087145750494 : Int)/10^30,(-431477039461127796172043400 : Int)/10^30)
theorem v2658_pb_checked : Scalar.distance (sourceCoefficient 32 83 1 1) v2658_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2658_pg : Scalar.QComplex := ((-93086331232385334728004 : Int)/10^30,(131895545479899893978 : Int)/10^30)
theorem v2658_pg_checked : Scalar.distance (sourceCoefficient 32 83 1 2) v2658_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2658_mb : Scalar.QComplex := ((-983711899958741526610391 : Int)/10^30,(-431476351220427873859356530 : Int)/10^30)
theorem v2658_mb_checked : Scalar.distance (sourceCoefficient 32 83 3 1) v2658_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2658_mg : Scalar.QComplex := ((-93086182752174567107607 : Int)/10^30,(212224807769981385585 : Int)/10^30)
theorem v2658_mg_checked : Scalar.distance (sourceCoefficient 32 83 3 2) v2658_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2658_upper : Scalar.QComplex := ((999995061327852899411489537338 : Int)/10^30,(-3142820374077812369079148401 : Int)/10^30)
theorem v2658_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 83 5) 1) 14) v2658_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2658 : Material (32 : Basis) (83 : Basis) where
  plus := ![v2658_pa,v2658_pb,v2658_pg]
  minus := ![(Primitive.Addresses.material2658 1).one,v2658_mb,v2658_mg]
  upper := v2658_upper
  lower := (Primitive.Addresses.material2658 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2658_pa_checked.trans (by decide +kernel)
    · exact v2658_pb_checked.trans (by decide +kernel)
    · exact v2658_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 83 Primitive.Addresses.material2658
    · exact v2658_mb_checked.trans (by decide +kernel)
    · exact v2658_mg_checked.trans (by decide +kernel)
  upper_error := v2658_upper_checked
  lower_error := reuse_lower_error 32 83 Primitive.Addresses.material2658

def v2659_pa : Scalar.QComplex := ((999998945769096932569351971518 : Int)/10^30,(-1452053957238526420209918720 : Int)/10^30)
theorem v2659_pa_checked : Scalar.distance (sourceCoefficient 32 84 1 0) v2659_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2659_pb : Scalar.QComplex := ((-626528565381683187970905 : Int)/10^30,(-431477013476427750039781422 : Int)/10^30)
theorem v2659_pb_checked : Scalar.distance (sourceCoefficient 32 84 1 1) v2659_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2659_pg : Scalar.QComplex := ((-93086326083354354494227 : Int)/10^30,(135166510650843138320 : Int)/10^30)
theorem v2659_pg_checked : Scalar.distance (sourceCoefficient 32 84 1 2) v2659_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2659_mb : Scalar.QComplex := ((-998873561723321687960568 : Int)/10^30,(-431476312151882033786352557 : Int)/10^30)
theorem v2659_mb_checked : Scalar.distance (sourceCoefficient 32 84 3 1) v2659_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2659_mg : Scalar.QComplex := ((-93086174780449880371935 : Int)/10^30,(215495767279612974096 : Int)/10^30)
theorem v2659_mg_checked : Scalar.distance (sourceCoefficient 32 84 3 2) v2659_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2659_upper : Scalar.QComplex := ((999994950274734449646641736813 : Int)/10^30,(-3177959255776487953011326207 : Int)/10^30)
theorem v2659_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 84 5) 1) 14) v2659_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2659 : Material (32 : Basis) (84 : Basis) where
  plus := ![v2659_pa,v2659_pb,v2659_pg]
  minus := ![(Primitive.Addresses.material2659 1).one,v2659_mb,v2659_mg]
  upper := v2659_upper
  lower := (Primitive.Addresses.material2659 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2659_pa_checked.trans (by decide +kernel)
    · exact v2659_pb_checked.trans (by decide +kernel)
    · exact v2659_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 84 Primitive.Addresses.material2659
    · exact v2659_mb_checked.trans (by decide +kernel)
    · exact v2659_mg_checked.trans (by decide +kernel)
  upper_error := v2659_upper_checked
  lower_error := reuse_lower_error 32 84 Primitive.Addresses.material2659

def v2660_pa : Scalar.QComplex := ((999998827849345537170973326998 : Int)/10^30,(-1531110686720101661934664491 : Int)/10^30)
theorem v2660_pa_checked : Scalar.distance (sourceCoefficient 32 85 1 0) v2660_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2660_pb : Scalar.QComplex := ((-660639747290592804289651 : Int)/10^30,(-431476952418431088489117473 : Int)/10^30)
theorem v2660_pb_checked : Scalar.distance (sourceCoefficient 32 85 1 1) v2660_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2660_pg : Scalar.QComplex := ((-93086314008701433718163 : Int)/10^30,(142525617227601382622 : Int)/10^30)
theorem v2660_pg_checked : Scalar.distance (sourceCoefficient 32 85 1 2) v2660_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2660_mb : Scalar.QComplex := ((-1032984678240778152733405 : Int)/10^30,(-431476221657494430131982095 : Int)/10^30)
theorem v2660_mb_checked : Scalar.distance (sourceCoefficient 32 85 3 1) v2660_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2660_mg : Scalar.QComplex := ((-93086156355223921655144 : Int)/10^30,(222854860696357863636 : Int)/10^30)
theorem v2660_mg_checked : Scalar.distance (sourceCoefficient 32 85 3 2) v2660_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2660_upper : Scalar.QComplex := ((999994695910415567141481972669 : Int)/10^30,(-3257015663993557975550597506 : Int)/10^30)
theorem v2660_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 85 5) 1) 14) v2660_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2660 : Material (32 : Basis) (85 : Basis) where
  plus := ![v2660_pa,v2660_pb,v2660_pg]
  minus := ![(Primitive.Addresses.material2660 1).one,v2660_mb,v2660_mg]
  upper := v2660_upper
  lower := (Primitive.Addresses.material2660 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2660_pa_checked.trans (by decide +kernel)
    · exact v2660_pb_checked.trans (by decide +kernel)
    · exact v2660_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 85 Primitive.Addresses.material2660
    · exact v2660_mb_checked.trans (by decide +kernel)
    · exact v2660_mg_checked.trans (by decide +kernel)
  upper_error := v2660_upper_checked
  lower_error := reuse_lower_error 32 85 Primitive.Addresses.material2660

def v2661_pa : Scalar.QComplex := ((999998805412285296418217455112 : Int)/10^30,(-1545695313561943696289092830 : Int)/10^30)
theorem v2661_pa_checked : Scalar.distance (sourceCoefficient 32 86 1 0) v2661_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2661_pb : Scalar.QComplex := ((-666932681954546769425403 : Int)/10^30,(-431476940761411641323688958 : Int)/10^30)
theorem v2661_pb_checked : Scalar.distance (sourceCoefficient 32 86 1 1) v2661_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2661_pg : Scalar.QComplex := ((-93086311706972989945204 : Int)/10^30,(143883247643394432503 : Int)/10^30)
theorem v2661_pg_checked : Scalar.distance (sourceCoefficient 32 86 1 2) v2661_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2661_mb : Scalar.QComplex := ((-1039277600502102170919910 : Int)/10^30,(-431476204569960131671472624 : Int)/10^30)
theorem v2661_mb_checked : Scalar.distance (sourceCoefficient 32 86 3 1) v2661_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2661_mg : Scalar.QComplex := ((-93086152881922431495580 : Int)/10^30,(224212488620355081967 : Int)/10^30)
theorem v2661_mg_checked : Scalar.distance (sourceCoefficient 32 86 3 2) v2661_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2661_upper : Scalar.QComplex := ((999994648301645921746508299841 : Int)/10^30,(-3271600230388981058263577860 : Int)/10^30)
theorem v2661_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 86 5) 1) 14) v2661_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2661 : Material (32 : Basis) (86 : Basis) where
  plus := ![v2661_pa,v2661_pb,v2661_pg]
  minus := ![(Primitive.Addresses.material2661 1).one,v2661_mb,v2661_mg]
  upper := v2661_upper
  lower := (Primitive.Addresses.material2661 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2661_pa_checked.trans (by decide +kernel)
    · exact v2661_pb_checked.trans (by decide +kernel)
    · exact v2661_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 86 Primitive.Addresses.material2661
    · exact v2661_mb_checked.trans (by decide +kernel)
    · exact v2661_mg_checked.trans (by decide +kernel)
  upper_error := v2661_upper_checked
  lower_error := reuse_lower_error 32 86 Primitive.Addresses.material2661

def v2662_pa : Scalar.QComplex := ((999998803919053750231595954008 : Int)/10^30,(-1546661068847957660505222408 : Int)/10^30)
theorem v2662_pa_checked : Scalar.distance (sourceCoefficient 32 87 1 0) v2662_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2662_pb : Scalar.QComplex := ((-667349383384629464702134 : Int)/10^30,(-431476939985194823707331922 : Int)/10^30)
theorem v2662_pb_checked : Scalar.distance (sourceCoefficient 32 87 1 1) v2662_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2662_pg : Scalar.QComplex := ((-93086311553743161874676 : Int)/10^30,(143973146326363481706 : Int)/10^30)
theorem v2662_pg_checked : Scalar.distance (sourceCoefficient 32 87 1 2) v2662_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2662_mb : Scalar.QComplex := ((-1039694301107187725485488 : Int)/10^30,(-431476203434149036450472874 : Int)/10^30)
theorem v2662_mb_checked : Scalar.distance (sourceCoefficient 32 87 3 1) v2662_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2662_mg : Scalar.QComplex := ((-93086152651114145963610 : Int)/10^30,(224302387137620302518 : Int)/10^30)
theorem v2662_mg_checked : Scalar.distance (sourceCoefficient 32 87 3 2) v2662_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2662_upper : Scalar.QComplex := ((999994645141610588527920146920 : Int)/10^30,(-3272565981659433785736488191 : Int)/10^30)
theorem v2662_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 87 5) 1) 14) v2662_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2662 : Material (32 : Basis) (87 : Basis) where
  plus := ![v2662_pa,v2662_pb,v2662_pg]
  minus := ![(Primitive.Addresses.material2662 1).one,v2662_mb,v2662_mg]
  upper := v2662_upper
  lower := (Primitive.Addresses.material2662 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2662_pa_checked.trans (by decide +kernel)
    · exact v2662_pb_checked.trans (by decide +kernel)
    · exact v2662_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 87 Primitive.Addresses.material2662
    · exact v2662_mb_checked.trans (by decide +kernel)
    · exact v2662_mg_checked.trans (by decide +kernel)
  upper_error := v2662_upper_checked
  lower_error := reuse_lower_error 32 87 Primitive.Addresses.material2662

def v2663_pa : Scalar.QComplex := ((999998785661804275379880689231 : Int)/10^30,(-1558420648230761424961075903 : Int)/10^30)
theorem v2663_pa_checked : Scalar.distance (sourceCoefficient 32 88 1 0) v2663_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2663_pb : Scalar.QComplex := ((-672423374261006249418487 : Int)/10^30,(-431476930490496783336622828 : Int)/10^30)
theorem v2663_pb_checked : Scalar.distance (sourceCoefficient 32 88 1 1) v2663_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2663_pg : Scalar.QComplex := ((-93086309679804830560459 : Int)/10^30,(145067803233985282914 : Int)/10^30)
theorem v2663_pg_checked : Scalar.distance (sourceCoefficient 32 88 1 2) v2663_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2663_mb : Scalar.QComplex := ((-1044768281900789030573592 : Int)/10^30,(-431476189560828929142468066 : Int)/10^30)
theorem v2663_mb_checked : Scalar.distance (sourceCoefficient 32 88 3 1) v2663_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2663_mg : Scalar.QComplex := ((-93086149832536902641623 : Int)/10^30,(225397042020526927851 : Int)/10^30)
theorem v2663_mg_checked : Scalar.distance (sourceCoefficient 32 88 3 2) v2663_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2663_upper : Scalar.QComplex := ((999994606588421111693414964137 : Int)/10^30,(-3284325512017369127877008292 : Int)/10^30)
theorem v2663_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 88 5) 1) 14) v2663_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2663 : Material (32 : Basis) (88 : Basis) where
  plus := ![v2663_pa,v2663_pb,v2663_pg]
  minus := ![(Primitive.Addresses.material2663 1).one,v2663_mb,v2663_mg]
  upper := v2663_upper
  lower := (Primitive.Addresses.material2663 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2663_pa_checked.trans (by decide +kernel)
    · exact v2663_pb_checked.trans (by decide +kernel)
    · exact v2663_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 88 Primitive.Addresses.material2663
    · exact v2663_mb_checked.trans (by decide +kernel)
    · exact v2663_mg_checked.trans (by decide +kernel)
  upper_error := v2663_upper_checked
  lower_error := reuse_lower_error 32 88 Primitive.Addresses.material2663

def v2664_pa : Scalar.QComplex := ((999998760458183770587648878475 : Int)/10^30,(-1574510113017668273919964530 : Int)/10^30)
theorem v2664_pa_checked : Scalar.distance (sourceCoefficient 32 89 1 0) v2664_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2664_pb : Scalar.QComplex := ((-679365612036340598281482 : Int)/10^30,(-431476917370954046443323406 : Int)/10^30)
theorem v2664_pb_checked : Scalar.distance (sourceCoefficient 32 89 1 1) v2664_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2664_pg : Scalar.QComplex := ((-93086307091550288522316 : Int)/10^30,(146565513573197111616 : Int)/10^30)
theorem v2664_pg_checked : Scalar.distance (sourceCoefficient 32 89 1 2) v2664_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2664_mb : Scalar.QComplex := ((-1051710505769636480070898 : Int)/10^30,(-431476170450452543923643751 : Int)/10^30)
theorem v2664_mb_checked : Scalar.distance (sourceCoefficient 32 89 3 1) v2664_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2664_mg : Scalar.QComplex := ((-93086145951826755958781 : Int)/10^30,(226894749568525649399 : Int)/10^30)
theorem v2664_mg_checked : Scalar.distance (sourceCoefficient 32 89 3 2) v2664_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2664_upper : Scalar.QComplex := ((999994553615881547375583134593 : Int)/10^30,(-3300414909341745641357365074 : Int)/10^30)
theorem v2664_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 89 5) 1) 14) v2664_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2664 : Material (32 : Basis) (89 : Basis) where
  plus := ![v2664_pa,v2664_pb,v2664_pg]
  minus := ![(Primitive.Addresses.material2664 1).one,v2664_mb,v2664_mg]
  upper := v2664_upper
  lower := (Primitive.Addresses.material2664 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2664_pa_checked.trans (by decide +kernel)
    · exact v2664_pb_checked.trans (by decide +kernel)
    · exact v2664_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 89 Primitive.Addresses.material2664
    · exact v2664_mb_checked.trans (by decide +kernel)
    · exact v2664_mg_checked.trans (by decide +kernel)
  upper_error := v2664_upper_checked
  lower_error := reuse_lower_error 32 89 Primitive.Addresses.material2664

def v2665_pa : Scalar.QComplex := ((999998718858090456181498975684 : Int)/10^30,(-1600713021675979436232141631 : Int)/10^30)
theorem v2665_pa_checked : Scalar.distance (sourceCoefficient 32 90 1 0) v2665_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2665_pb : Scalar.QComplex := ((-690671570325228841634605 : Int)/10^30,(-431476895686016199933298565 : Int)/10^30)
theorem v2665_pb_checked : Scalar.distance (sourceCoefficient 32 90 1 1) v2665_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2665_pg : Scalar.QComplex := ((-93086302816207278928217 : Int)/10^30,(149004647953675597990 : Int)/10^30)
theorem v2665_pg_checked : Scalar.distance (sourceCoefficient 32 90 1 2) v2665_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2665_mb : Scalar.QComplex := ((-1063016441135675036458621 : Int)/10^30,(-431476139008989969855360626 : Int)/10^30)
theorem v2665_mb_checked : Scalar.distance (sourceCoefficient 32 90 3 1) v2665_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2665_mg : Scalar.QComplex := ((-93086139571622222451849 : Int)/10^30,(229333879351374468995 : Int)/10^30)
theorem v2665_mg_checked : Scalar.distance (sourceCoefficient 32 90 3 2) v2665_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2665_upper : Scalar.QComplex := ((999994466792006956481191793267 : Int)/10^30,(-3326617707175915237304608763 : Int)/10^30)
theorem v2665_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 90 5) 1) 14) v2665_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2665 : Material (32 : Basis) (90 : Basis) where
  plus := ![v2665_pa,v2665_pb,v2665_pg]
  minus := ![(Primitive.Addresses.material2665 1).one,v2665_mb,v2665_mg]
  upper := v2665_upper
  lower := (Primitive.Addresses.material2665 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2665_pa_checked.trans (by decide +kernel)
    · exact v2665_pb_checked.trans (by decide +kernel)
    · exact v2665_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 90 Primitive.Addresses.material2665
    · exact v2665_mb_checked.trans (by decide +kernel)
    · exact v2665_mg_checked.trans (by decide +kernel)
  upper_error := v2665_upper_checked
  lower_error := reuse_lower_error 32 90 Primitive.Addresses.material2665

def v2666_pa : Scalar.QComplex := ((999998695120907444087798038602 : Int)/10^30,(-1615474073577901223007725530 : Int)/10^30)
theorem v2666_pa_checked : Scalar.distance (sourceCoefficient 32 91 1 0) v2666_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2666_pb : Scalar.QComplex := ((-697040627866896794725561 : Int)/10^30,(-431476883296166530683509118 : Int)/10^30)
theorem v2666_pb_checked : Scalar.distance (sourceCoefficient 32 91 1 1) v2666_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2666_pg : Scalar.QComplex := ((-93086300374916994558009 : Int)/10^30,(150378701086986285191 : Int)/10^30)
theorem v2666_pg_checked : Scalar.distance (sourceCoefficient 32 91 1 2) v2666_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2666_mb : Scalar.QComplex := ((-1069385485613969540029213 : Int)/10^30,(-431476121122935107156644593 : Int)/10^30)
theorem v2666_mb_checked : Scalar.distance (sourceCoefficient 32 91 3 1) v2666_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2666_mg : Scalar.QComplex := ((-93086135944586878094306 : Int)/10^30,(230707929866338813555 : Int)/10^30)
theorem v2666_mg_checked : Scalar.distance (sourceCoefficient 32 91 3 2) v2666_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2666_upper : Scalar.QComplex := ((999994417578622827584190154069 : Int)/10^30,(-3341378696124759712675315720 : Int)/10^30)
theorem v2666_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 91 5) 1) 14) v2666_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2666 : Material (32 : Basis) (91 : Basis) where
  plus := ![v2666_pa,v2666_pb,v2666_pg]
  minus := ![(Primitive.Addresses.material2666 1).one,v2666_mb,v2666_mg]
  upper := v2666_upper
  lower := (Primitive.Addresses.material2666 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2666_pa_checked.trans (by decide +kernel)
    · exact v2666_pb_checked.trans (by decide +kernel)
    · exact v2666_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 91 Primitive.Addresses.material2666
    · exact v2666_mb_checked.trans (by decide +kernel)
    · exact v2666_mg_checked.trans (by decide +kernel)
  upper_error := v2666_upper_checked
  lower_error := reuse_lower_error 32 91 Primitive.Addresses.material2666

def v2667_pa : Scalar.QComplex := ((999998642986053270814359756259 : Int)/10^30,(-1647430135687556148623463953 : Int)/10^30)
theorem v2667_pa_checked : Scalar.distance (sourceCoefficient 32 92 1 0) v2667_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2667_pb : Scalar.QComplex := ((-710828940103496105098578 : Int)/10^30,(-431476856044062882562001475 : Int)/10^30)
theorem v2667_pb_checked : Scalar.distance (sourceCoefficient 32 92 1 1) v2667_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2667_pg : Scalar.QComplex := ((-93086295008725589053896 : Int)/10^30,(153353375719546307264 : Int)/10^30)
theorem v2667_pg_checked : Scalar.distance (sourceCoefficient 32 92 1 2) v2667_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2667_mb : Scalar.QComplex := ((-1083173769199211988573329 : Int)/10^30,(-431476081972149148584041859 : Int)/10^30)
theorem v2667_mb_checked : Scalar.distance (sourceCoefficient 32 92 3 1) v2667_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2667_mg : Scalar.QComplex := ((-93086128011387237141289 : Int)/10^30,(233682598760510021919 : Int)/10^30)
theorem v2667_mg_checked : Scalar.distance (sourceCoefficient 32 92 3 2) v2667_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2667_upper : Scalar.QComplex := ((999994310290582133096049265231 : Int)/10^30,(-3373334620659585282661856337 : Int)/10^30)
theorem v2667_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 92 5) 1) 14) v2667_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2667 : Material (32 : Basis) (92 : Basis) where
  plus := ![v2667_pa,v2667_pb,v2667_pg]
  minus := ![(Primitive.Addresses.material2667 1).one,v2667_mb,v2667_mg]
  upper := v2667_upper
  lower := (Primitive.Addresses.material2667 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2667_pa_checked.trans (by decide +kernel)
    · exact v2667_pb_checked.trans (by decide +kernel)
    · exact v2667_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 92 Primitive.Addresses.material2667
    · exact v2667_mb_checked.trans (by decide +kernel)
    · exact v2667_mg_checked.trans (by decide +kernel)
  upper_error := v2667_upper_checked
  lower_error := reuse_lower_error 32 92 Primitive.Addresses.material2667

def v2668_pa : Scalar.QComplex := ((999998579787082621445799065400 : Int)/10^30,(-1685355694728082530344206971 : Int)/10^30)
theorem v2668_pa_checked : Scalar.distance (sourceCoefficient 32 93 1 0) v2668_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2668_pb : Scalar.QComplex := ((-727192953451933133066440 : Int)/10^30,(-431476822938811916423352538 : Int)/10^30)
theorem v2668_pb_checked : Scalar.distance (sourceCoefficient 32 93 1 1) v2668_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2668_pg : Scalar.QComplex := ((-93086288496199224474013 : Int)/10^30,(156883729226469334745 : Int)/10^30)
theorem v2668_pg_checked : Scalar.distance (sourceCoefficient 32 93 1 2) v2668_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2668_mb : Scalar.QComplex := ((-1099537747886238395939567 : Int)/10^30,(-431476034745503997144355156 : Int)/10^30)
theorem v2668_mb_checked : Scalar.distance (sourceCoefficient 32 93 3 1) v2668_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2668_mg : Scalar.QComplex := ((-93086118452327222217585 : Int)/10^30,(237212945332904154313 : Int)/10^30)
theorem v2668_mg_checked : Scalar.distance (sourceCoefficient 32 93 3 2) v2668_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2668_upper : Scalar.QComplex := ((999994181635631287061685142436 : Int)/10^30,(-3411260014138756547654164487 : Int)/10^30)
theorem v2668_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 93 5) 1) 14) v2668_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2668 : Material (32 : Basis) (93 : Basis) where
  plus := ![v2668_pa,v2668_pb,v2668_pg]
  minus := ![(Primitive.Addresses.material2668 1).one,v2668_mb,v2668_mg]
  upper := v2668_upper
  lower := (Primitive.Addresses.material2668 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2668_pa_checked.trans (by decide +kernel)
    · exact v2668_pb_checked.trans (by decide +kernel)
    · exact v2668_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 93 Primitive.Addresses.material2668
    · exact v2668_mb_checked.trans (by decide +kernel)
    · exact v2668_mg_checked.trans (by decide +kernel)
  upper_error := v2668_upper_checked
  lower_error := reuse_lower_error 32 93 Primitive.Addresses.material2668

def v2669_pa : Scalar.QComplex := ((999998503282124702207253442554 : Int)/10^30,(-1730154186895256817410124207 : Int)/10^30)
theorem v2669_pa_checked : Scalar.distance (sourceCoefficient 32 94 1 0) v2669_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2669_pb : Scalar.QComplex := ((-746522479587961564972894 : Int)/10^30,(-431476782768157012517163656 : Int)/10^30)
theorem v2669_pb_checked : Scalar.distance (sourceCoefficient 32 94 1 1) v2669_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2669_pg : Scalar.QComplex := ((-93086280602228648384699 : Int)/10^30,(161053859178642542616 : Int)/10^30)
theorem v2669_pg_checked : Scalar.distance (sourceCoefficient 32 94 1 2) v2669_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2669_mb : Scalar.QComplex := ((-1118867232159534881481685 : Int)/10^30,(-431475977894353564756446202 : Int)/10^30)
theorem v2669_mb_checked : Scalar.distance (sourceCoefficient 32 94 3 1) v2669_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2669_mg : Scalar.QComplex := ((-93086106959725252369811 : Int)/10^30,(241383066920206320708 : Int)/10^30)
theorem v2669_mg_checked : Scalar.distance (sourceCoefficient 32 94 3 2) v2669_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2669_upper : Scalar.QComplex := ((999994027812653919890734110477 : Int)/10^30,(-3456058307543222259228098053 : Int)/10^30)
theorem v2669_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 94 5) 1) 14) v2669_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2669 : Material (32 : Basis) (94 : Basis) where
  plus := ![v2669_pa,v2669_pb,v2669_pg]
  minus := ![(Primitive.Addresses.material2669 1).one,v2669_mb,v2669_mg]
  upper := v2669_upper
  lower := (Primitive.Addresses.material2669 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2669_pa_checked.trans (by decide +kernel)
    · exact v2669_pb_checked.trans (by decide +kernel)
    · exact v2669_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 94 Primitive.Addresses.material2669
    · exact v2669_mb_checked.trans (by decide +kernel)
    · exact v2669_mg_checked.trans (by decide +kernel)
  upper_error := v2669_upper_checked
  lower_error := reuse_lower_error 32 94 Primitive.Addresses.material2669

def v2670_pa : Scalar.QComplex := ((999998425700789292278052342262 : Int)/10^30,(-1774428342593027637744834793 : Int)/10^30)
theorem v2670_pa_checked : Scalar.distance (sourceCoefficient 32 95 1 0) v2670_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2670_pb : Scalar.QComplex := ((-765625765380150475148947 : Int)/10^30,(-431476741933281578903012403 : Int)/10^30)
theorem v2670_pb_checked : Scalar.distance (sourceCoefficient 32 95 1 1) v2670_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2670_pg : Scalar.QComplex := ((-93086272586510939797746 : Int)/10^30,(165175180419001552948 : Int)/10^30)
theorem v2670_pg_checked : Scalar.distance (sourceCoefficient 32 95 1 2) v2670_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2670_mb : Scalar.QComplex := ((-1137970475600039063243537 : Int)/10^30,(-431475920574218077226906718 : Int)/10^30)
theorem v2670_mb_checked : Scalar.distance (sourceCoefficient 32 95 3 1) v2670_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2670_mg : Scalar.QComplex := ((-93086095387495915389295 : Int)/10^30,(245504379708805711582 : Int)/10^30)
theorem v2670_mg_checked : Scalar.distance (sourceCoefficient 32 95 3 2) v2670_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2670_upper : Scalar.QComplex := ((999993873818257843924415492887 : Int)/10^30,(-3500332263401492181630026308 : Int)/10^30)
theorem v2670_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 95 5) 1) 14) v2670_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2670 : Material (32 : Basis) (95 : Basis) where
  plus := ![v2670_pa,v2670_pb,v2670_pg]
  minus := ![(Primitive.Addresses.material2670 1).one,v2670_mb,v2670_mg]
  upper := v2670_upper
  lower := (Primitive.Addresses.material2670 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2670_pa_checked.trans (by decide +kernel)
    · exact v2670_pb_checked.trans (by decide +kernel)
    · exact v2670_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 95 Primitive.Addresses.material2670
    · exact v2670_mb_checked.trans (by decide +kernel)
    · exact v2670_mg_checked.trans (by decide +kernel)
  upper_error := v2670_upper_checked
  lower_error := reuse_lower_error 32 95 Primitive.Addresses.material2670

def v2671_pa : Scalar.QComplex := ((999998387743092974420394684413 : Int)/10^30,(-1795692405363130380843502780 : Int)/10^30)
theorem v2671_pa_checked : Scalar.distance (sourceCoefficient 32 96 1 0) v2671_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2671_pb : Scalar.QComplex := ((-774800721820838009908723 : Int)/10^30,(-431476721920166711125535057 : Int)/10^30)
theorem v2671_pb_checked : Scalar.distance (sourceCoefficient 32 96 1 1) v2671_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2671_pg : Scalar.QComplex := ((-93086268661035308167533 : Int)/10^30,(167154575174331440246 : Int)/10^30)
theorem v2671_pg_checked : Scalar.distance (sourceCoefficient 32 96 1 2) v2671_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2671_mb : Scalar.QComplex := ((-1147145411354054225253092 : Int)/10^30,(-431475892643536477631863396 : Int)/10^30)
theorem v2671_mb_checked : Scalar.distance (sourceCoefficient 32 96 3 1) v2671_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2671_mg : Scalar.QComplex := ((-93086089753893220173797 : Int)/10^30,(247483770339607795424 : Int)/10^30)
theorem v2671_mg_checked : Scalar.distance (sourceCoefficient 32 96 3 2) v2671_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2671_upper : Scalar.QComplex := ((999993799160774779104772922543 : Int)/10^30,(-3521596228989730931626716857 : Int)/10^30)
theorem v2671_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 96 5) 1) 14) v2671_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2671 : Material (32 : Basis) (96 : Basis) where
  plus := ![v2671_pa,v2671_pb,v2671_pg]
  minus := ![(Primitive.Addresses.material2671 1).one,v2671_mb,v2671_mg]
  upper := v2671_upper
  lower := (Primitive.Addresses.material2671 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2671_pa_checked.trans (by decide +kernel)
    · exact v2671_pb_checked.trans (by decide +kernel)
    · exact v2671_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 96 Primitive.Addresses.material2671
    · exact v2671_mb_checked.trans (by decide +kernel)
    · exact v2671_mg_checked.trans (by decide +kernel)
  upper_error := v2671_upper_checked
  lower_error := reuse_lower_error 32 96 Primitive.Addresses.material2671

def v2672_pa : Scalar.QComplex := ((999998253689893204525964899177 : Int)/10^30,(-1868854505838257857981041858 : Int)/10^30)
theorem v2672_pa_checked : Scalar.distance (sourceCoefficient 32 97 1 0) v2672_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2672_pb : Scalar.QComplex := ((-806368491694794815087824 : Int)/10^30,(-431476651074910335915360543 : Int)/10^30)
theorem v2672_pb_checked : Scalar.distance (sourceCoefficient 32 97 1 1) v2672_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2672_pg : Scalar.QComplex := ((-93086254779734103781501 : Int)/10^30,(173964970473500313343 : Int)/10^30)
theorem v2672_pg_checked : Scalar.distance (sourceCoefficient 32 97 1 2) v2672_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2672_mb : Scalar.QComplex := ((-1178713108337622088097582 : Int)/10^30,(-431475794556742839700629328 : Int)/10^30)
theorem v2672_mb_checked : Scalar.distance (sourceCoefficient 32 97 3 1) v2672_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2672_mg : Scalar.QComplex := ((-93086069995532770065838 : Int)/10^30,(254294151124017499412 : Int)/10^30)
theorem v2672_mg_checked : Scalar.distance (sourceCoefficient 32 97 3 2) v2672_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2672_upper : Scalar.QComplex := ((999993538836626459542413643572 : Int)/10^30,(-3594757989134842383542168029 : Int)/10^30)
theorem v2672_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 97 5) 1) 14) v2672_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2672 : Material (32 : Basis) (97 : Basis) where
  plus := ![v2672_pa,v2672_pb,v2672_pg]
  minus := ![(Primitive.Addresses.material2672 1).one,v2672_mb,v2672_mg]
  upper := v2672_upper
  lower := (Primitive.Addresses.material2672 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2672_pa_checked.trans (by decide +kernel)
    · exact v2672_pb_checked.trans (by decide +kernel)
    · exact v2672_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 97 Primitive.Addresses.material2672
    · exact v2672_mb_checked.trans (by decide +kernel)
    · exact v2672_mg_checked.trans (by decide +kernel)
  upper_error := v2672_upper_checked
  lower_error := reuse_lower_error 32 97 Primitive.Addresses.material2672

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
