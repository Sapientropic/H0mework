import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B150

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3601_pa : Scalar.QComplex := ((999998747963270825768496969152 : Int)/10^30,(-1582425951111928587722347571 : Int)/10^30)
theorem v3601_pa_checked : Scalar.distance (sourceCoefficient 49 74 1 0) v3601_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3601_pb : Scalar.QComplex := ((-682781205308565491482984 : Int)/10^30,(-431476967349813038876931858 : Int)/10^30)
theorem v3601_pb_checked : Scalar.distance (sourceCoefficient 49 74 1 1) v3601_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3601_pg : Scalar.QComplex := ((-93086311901185723832213 : Int)/10^30,(147302380073725603577 : Int)/10^30)
theorem v3601_pg_checked : Scalar.distance (sourceCoefficient 49 74 1 2) v3601_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3601_mb : Scalar.QComplex := ((-1055126140899584243919925 : Int)/10^30,(-431476217481789765624265876 : Int)/10^30)
theorem v3601_mb_checked : Scalar.distance (sourceCoefficient 49 74 3 1) v3601_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3601_mg : Scalar.QComplex := ((-93086150125577797700722 : Int)/10^30,(227631619945183829485 : Int)/10^30)
theorem v3601_mg_checked : Scalar.distance (sourceCoefficient 49 74 3 2) v3601_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3601_upper : Scalar.QComplex := ((999994527458968780790477111051 : Int)/10^30,(-3308330714081208760310491271 : Int)/10^30)
theorem v3601_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 74 5) 1) 14) v3601_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3601 : Material (49 : Basis) (74 : Basis) where
  plus := ![v3601_pa,v3601_pb,v3601_pg]
  minus := ![(Primitive.Addresses.material3601 1).one,v3601_mb,v3601_mg]
  upper := v3601_upper
  lower := (Primitive.Addresses.material3601 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3601_pa_checked.trans (by decide +kernel)
    · exact v3601_pb_checked.trans (by decide +kernel)
    · exact v3601_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 74 Primitive.Addresses.material3601
    · exact v3601_mb_checked.trans (by decide +kernel)
    · exact v3601_mg_checked.trans (by decide +kernel)
  upper_error := v3601_upper_checked
  lower_error := reuse_lower_error 49 74 Primitive.Addresses.material3601

def v3602_pa : Scalar.QComplex := ((999998724409682435508360934779 : Int)/10^30,(-1597241061329918669909829314 : Int)/10^30)
theorem v3602_pa_checked : Scalar.distance (sourceCoefficient 49 75 1 0) v3602_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3602_pb : Scalar.QComplex := ((-689173590644155948771263 : Int)/10^30,(-431476956250528234090080406 : Int)/10^30)
theorem v3602_pb_checked : Scalar.distance (sourceCoefficient 49 75 1 1) v3602_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3602_pg : Scalar.QComplex := ((-93086309607652968028557 : Int)/10^30,(148681465609650964795 : Int)/10^30)
theorem v3602_pg_checked : Scalar.distance (sourceCoefficient 49 75 1 2) v3602_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3602_mb : Scalar.QComplex := ((-1061518514276814601025359 : Int)/10^30,(-431476200866168451341922447 : Int)/10^30)
theorem v3602_mb_checked : Scalar.distance (sourceCoefficient 49 75 3 1) v3602_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3602_mg : Scalar.QComplex := ((-93086146641957190087387 : Int)/10^30,(229010702988397146977 : Int)/10^30)
theorem v3602_mg_checked : Scalar.distance (sourceCoefficient 49 75 3 2) v3602_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3602_upper : Scalar.QComplex := ((999994478335879250882664549717 : Int)/10^30,(-3323145761582475681155994639 : Int)/10^30)
theorem v3602_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 75 5) 1) 14) v3602_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3602 : Material (49 : Basis) (75 : Basis) where
  plus := ![v3602_pa,v3602_pb,v3602_pg]
  minus := ![(Primitive.Addresses.material3602 1).one,v3602_mb,v3602_mg]
  upper := v3602_upper
  lower := (Primitive.Addresses.material3602 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3602_pa_checked.trans (by decide +kernel)
    · exact v3602_pb_checked.trans (by decide +kernel)
    · exact v3602_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 75 Primitive.Addresses.material3602
    · exact v3602_mb_checked.trans (by decide +kernel)
    · exact v3602_mg_checked.trans (by decide +kernel)
  upper_error := v3602_upper_checked
  lower_error := reuse_lower_error 49 75 Primitive.Addresses.material3602

def v3603_pa : Scalar.QComplex := ((999998704478425954161830581531 : Int)/10^30,(-1609671230318641037191568473 : Int)/10^30)
theorem v3603_pa_checked : Scalar.distance (sourceCoefficient 49 76 1 0) v3603_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3603_pb : Scalar.QComplex := ((-694536927662601148134406 : Int)/10^30,(-431476946840592490340643737 : Int)/10^30)
theorem v3603_pb_checked : Scalar.distance (sourceCoefficient 49 76 1 1) v3603_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3603_pg : Scalar.QComplex := ((-93086307664944229523580 : Int)/10^30,(149838545503918647417 : Int)/10^30)
theorem v3603_pg_checked : Scalar.distance (sourceCoefficient 49 76 1 2) v3603_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3603_mb : Scalar.QComplex := ((-1066881841177893572728256 : Int)/10^30,(-431476186827917920155751925 : Int)/10^30)
theorem v3603_mb_checked : Scalar.distance (sourceCoefficient 49 76 3 1) v3603_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3603_mg : Scalar.QComplex := ((-93086143700741339132563 : Int)/10^30,(230167780775360958824 : Int)/10^30)
theorem v3603_mg_checked : Scalar.distance (sourceCoefficient 49 76 3 2) v3603_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3603_upper : Scalar.QComplex := ((999994436951308436388458060771 : Int)/10^30,(-3335575877658380952614529541 : Int)/10^30)
theorem v3603_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 76 5) 1) 14) v3603_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3603 : Material (49 : Basis) (76 : Basis) where
  plus := ![v3603_pa,v3603_pb,v3603_pg]
  minus := ![(Primitive.Addresses.material3603 1).one,v3603_mb,v3603_mg]
  upper := v3603_upper
  lower := (Primitive.Addresses.material3603 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3603_pa_checked.trans (by decide +kernel)
    · exact v3603_pb_checked.trans (by decide +kernel)
    · exact v3603_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 76 Primitive.Addresses.material3603
    · exact v3603_mb_checked.trans (by decide +kernel)
    · exact v3603_mg_checked.trans (by decide +kernel)
  upper_error := v3603_upper_checked
  lower_error := reuse_lower_error 49 76 Primitive.Addresses.material3603

def v3604_pa : Scalar.QComplex := ((999998699842145072662651383929 : Int)/10^30,(-1612548920015832253937666914 : Int)/10^30)
theorem v3604_pa_checked : Scalar.distance (sourceCoefficient 49 77 1 0) v3604_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3604_pb : Scalar.QComplex := ((-695778585728180612621485 : Int)/10^30,(-431476944649440982750305899 : Int)/10^30)
theorem v3604_pb_checked : Scalar.distance (sourceCoefficient 49 77 1 1) v3604_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3604_pg : Scalar.QComplex := ((-93086307212798645781463 : Int)/10^30,(150106419326300594593 : Int)/10^30)
theorem v3604_pg_checked : Scalar.distance (sourceCoefficient 49 77 1 2) v3604_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3604_mb : Scalar.QComplex := ((-1068123496890281927573216 : Int)/10^30,(-431476183565272240039527012 : Int)/10^30)
theorem v3604_mb_checked : Scalar.distance (sourceCoefficient 49 77 3 1) v3604_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3604_mg : Scalar.QComplex := ((-93086143017432879618393 : Int)/10^30,(230435654107819964600 : Int)/10^30)
theorem v3604_mg_checked : Scalar.distance (sourceCoefficient 49 77 3 2) v3604_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3604_upper : Scalar.QComplex := ((999994427348403104703020933997 : Int)/10^30,(-3338453555067791201220397827 : Int)/10^30)
theorem v3604_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 77 5) 1) 14) v3604_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3604 : Material (49 : Basis) (77 : Basis) where
  plus := ![v3604_pa,v3604_pb,v3604_pg]
  minus := ![(Primitive.Addresses.material3604 1).one,v3604_mb,v3604_mg]
  upper := v3604_upper
  lower := (Primitive.Addresses.material3604 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3604_pa_checked.trans (by decide +kernel)
    · exact v3604_pb_checked.trans (by decide +kernel)
    · exact v3604_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 77 Primitive.Addresses.material3604
    · exact v3604_mb_checked.trans (by decide +kernel)
    · exact v3604_mg_checked.trans (by decide +kernel)
  upper_error := v3604_upper_checked
  lower_error := reuse_lower_error 49 77 Primitive.Addresses.material3604

def v3605_pa : Scalar.QComplex := ((999998671796073407985401436986 : Int)/10^30,(-1629848486534364513436980096 : Int)/10^30)
theorem v3605_pa_checked : Scalar.distance (sourceCoefficient 49 78 1 0) v3605_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3605_pb : Scalar.QComplex := ((-703242957628817287385998 : Int)/10^30,(-431476931376671325824548437 : Int)/10^30)
theorem v3605_pb_checked : Scalar.distance (sourceCoefficient 49 78 1 1) v3605_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3605_pg : Scalar.QComplex := ((-93086304475718800340998 : Int)/10^30,(151716773977642255274 : Int)/10^30)
theorem v3605_pg_checked : Scalar.distance (sourceCoefficient 49 78 1 2) v3605_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3605_mb : Scalar.QComplex := ((-1075587854557789374509904 : Int)/10^30,(-431476163851090757753769429 : Int)/10^30)
theorem v3605_mb_checked : Scalar.distance (sourceCoefficient 49 78 3 1) v3605_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3605_mg : Scalar.QComplex := ((-93086138890690516891134 : Int)/10^30,(232046005797576358628 : Int)/10^30)
theorem v3605_mg_checked : Scalar.distance (sourceCoefficient 49 78 3 2) v3605_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3605_upper : Scalar.QComplex := ((999994369444890804783359361322 : Int)/10^30,(-3355753047415675907713268255 : Int)/10^30)
theorem v3605_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 78 5) 1) 14) v3605_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3605 : Material (49 : Basis) (78 : Basis) where
  plus := ![v3605_pa,v3605_pb,v3605_pg]
  minus := ![(Primitive.Addresses.material3605 1).one,v3605_mb,v3605_mg]
  upper := v3605_upper
  lower := (Primitive.Addresses.material3605 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3605_pa_checked.trans (by decide +kernel)
    · exact v3605_pb_checked.trans (by decide +kernel)
    · exact v3605_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 78 Primitive.Addresses.material3605
    · exact v3605_mb_checked.trans (by decide +kernel)
    · exact v3605_mg_checked.trans (by decide +kernel)
  upper_error := v3605_upper_checked
  lower_error := reuse_lower_error 49 78 Primitive.Addresses.material3605

def v3606_pa : Scalar.QComplex := ((999998662690724370987291331027 : Int)/10^30,(-1635425560171396713988585448 : Int)/10^30)
theorem v3606_pa_checked : Scalar.distance (sourceCoefficient 49 79 1 0) v3606_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3606_pb : Scalar.QComplex := ((-705649338811282159193514 : Int)/10^30,(-431476927061065560162730235 : Int)/10^30)
theorem v3606_pb_checked : Scalar.distance (sourceCoefficient 49 79 1 1) v3606_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3606_pg : Scalar.QComplex := ((-93086303586404841983032 : Int)/10^30,(152235923773593780017 : Int)/10^30)
theorem v3606_pg_checked : Scalar.distance (sourceCoefficient 49 79 1 2) v3606_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3606_mb : Scalar.QComplex := ((-1077994231120075146935002 : Int)/10^30,(-431476157458888017907252665 : Int)/10^30)
theorem v3606_mb_checked : Scalar.distance (sourceCoefficient 49 79 3 1) v3606_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3606_mg : Scalar.QComplex := ((-93086137553373997398075 : Int)/10^30,(232565154632786795172 : Int)/10^30)
theorem v3606_mg_checked : Scalar.distance (sourceCoefficient 49 79 3 2) v3606_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3606_upper : Scalar.QComplex := ((999994350714032179783573644690 : Int)/10^30,(-3361330097031305647948425054 : Int)/10^30)
theorem v3606_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 79 5) 1) 14) v3606_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3606 : Material (49 : Basis) (79 : Basis) where
  plus := ![v3606_pa,v3606_pb,v3606_pg]
  minus := ![(Primitive.Addresses.material3606 1).one,v3606_mb,v3606_mg]
  upper := v3606_upper
  lower := (Primitive.Addresses.material3606 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3606_pa_checked.trans (by decide +kernel)
    · exact v3606_pb_checked.trans (by decide +kernel)
    · exact v3606_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 79 Primitive.Addresses.material3606
    · exact v3606_mb_checked.trans (by decide +kernel)
    · exact v3606_mg_checked.trans (by decide +kernel)
  upper_error := v3606_upper_checked
  lower_error := reuse_lower_error 49 79 Primitive.Addresses.material3606

def v3607_pa : Scalar.QComplex := ((999998648405026587712843441492 : Int)/10^30,(-1644137500337365992698899765 : Int)/10^30)
theorem v3607_pa_checked : Scalar.distance (sourceCoefficient 49 80 1 0) v3607_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3607_pb : Scalar.QComplex := ((-709408344001513204098252 : Int)/10^30,(-431476920283854431505957255 : Int)/10^30)
theorem v3607_pb_checked : Scalar.distance (sourceCoefficient 49 80 1 1) v3607_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3607_pg : Scalar.QComplex := ((-93086302190448941156193 : Int)/10^30,(153046887056456640640 : Int)/10^30)
theorem v3607_pg_checked : Scalar.distance (sourceCoefficient 49 80 1 2) v3607_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3607_mb : Scalar.QComplex := ((-1081753229062228794720293 : Int)/10^30,(-431476147437827232855607220 : Int)/10^30)
theorem v3607_mb_checked : Scalar.distance (sourceCoefficient 49 80 3 1) v3607_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3607_mg : Scalar.QComplex := ((-93086135457593827669177 : Int)/10^30,(233376116409043891838 : Int)/10^30)
theorem v3607_mg_checked : Scalar.distance (sourceCoefficient 49 80 3 2) v3607_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3607_upper : Scalar.QComplex := ((999994321392337287952934297818 : Int)/10^30,(-3370041999566045040275159252 : Int)/10^30)
theorem v3607_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 80 5) 1) 14) v3607_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3607 : Material (49 : Basis) (80 : Basis) where
  plus := ![v3607_pa,v3607_pb,v3607_pg]
  minus := ![(Primitive.Addresses.material3607 1).one,v3607_mb,v3607_mg]
  upper := v3607_upper
  lower := (Primitive.Addresses.material3607 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3607_pa_checked.trans (by decide +kernel)
    · exact v3607_pb_checked.trans (by decide +kernel)
    · exact v3607_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 80 Primitive.Addresses.material3607
    · exact v3607_mb_checked.trans (by decide +kernel)
    · exact v3607_mg_checked.trans (by decide +kernel)
  upper_error := v3607_upper_checked
  lower_error := reuse_lower_error 49 80 Primitive.Addresses.material3607

def v3608_pa : Scalar.QComplex := ((999998604931720330289186675245 : Int)/10^30,(-1670369603747600732196794457 : Int)/10^30)
theorem v3608_pa_checked : Scalar.distance (sourceCoefficient 49 81 1 0) v3608_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3608_pb : Scalar.QComplex := ((-720726903297123639028309 : Int)/10^30,(-431476899613642034501777470 : Int)/10^30)
theorem v3608_pb_checked : Scalar.distance (sourceCoefficient 49 81 1 1) v3608_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3608_pg : Scalar.QComplex := ((-93086297937378398967019 : Int)/10^30,(155488739517398206187 : Int)/10^30)
theorem v3608_pg_checked : Scalar.distance (sourceCoefficient 49 81 1 2) v3608_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3608_mb : Scalar.QComplex := ((-1093071766305959973373640 : Int)/10^30,(-431476117000215629191532852 : Int)/10^30)
theorem v3608_mb_checked : Scalar.distance (sourceCoefficient 49 81 3 1) v3608_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3608_mg : Scalar.QComplex := ((-93086129097316172252274 : Int)/10^30,(235817964290563861284 : Int)/10^30)
theorem v3608_mg_checked : Scalar.distance (sourceCoefficient 49 81 3 2) v3608_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3608_upper : Scalar.QComplex := ((999994232644865050678782793378 : Int)/10^30,(-3396273988875660456776921653 : Int)/10^30)
theorem v3608_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 81 5) 1) 14) v3608_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3608 : Material (49 : Basis) (81 : Basis) where
  plus := ![v3608_pa,v3608_pb,v3608_pg]
  minus := ![(Primitive.Addresses.material3608 1).one,v3608_mb,v3608_mg]
  upper := v3608_upper
  lower := (Primitive.Addresses.material3608 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3608_pa_checked.trans (by decide +kernel)
    · exact v3608_pb_checked.trans (by decide +kernel)
    · exact v3608_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 81 Primitive.Addresses.material3608
    · exact v3608_mb_checked.trans (by decide +kernel)
    · exact v3608_mg_checked.trans (by decide +kernel)
  upper_error := v3608_upper_checked
  lower_error := reuse_lower_error 49 81 Primitive.Addresses.material3608

def v3609_pa : Scalar.QComplex := ((999998588278409699090078743957 : Int)/10^30,(-1680309848701712311897823315 : Int)/10^30)
theorem v3609_pa_checked : Scalar.distance (sourceCoefficient 49 82 1 0) v3609_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3609_pb : Scalar.QComplex := ((-725015894093596403298513 : Int)/10^30,(-431476891677559669257480100 : Int)/10^30)
theorem v3609_pb_checked : Scalar.distance (sourceCoefficient 49 82 1 1) v3609_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3609_pg : Scalar.QComplex := ((-93086296306219456468008 : Int)/10^30,(156414041275585471501 : Int)/10^30)
theorem v3609_pg_checked : Scalar.distance (sourceCoefficient 49 82 1 2) v3609_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3609_mb : Scalar.QComplex := ((-1097360748656963794229775 : Int)/10^30,(-431476105362930330532105106 : Int)/10^30)
theorem v3609_mb_checked : Scalar.distance (sourceCoefficient 49 82 3 1) v3609_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3609_mg : Scalar.QComplex := ((-93086126667664093836851 : Int)/10^30,(236743264296602290940 : Int)/10^30)
theorem v3609_mg_checked : Scalar.distance (sourceCoefficient 49 82 3 2) v3609_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3609_upper : Scalar.QComplex := ((999994198835618203811019072377 : Int)/10^30,(-3406214190282841467614191741 : Int)/10^30)
theorem v3609_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 82 5) 1) 14) v3609_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3609 : Material (49 : Basis) (82 : Basis) where
  plus := ![v3609_pa,v3609_pb,v3609_pg]
  minus := ![(Primitive.Addresses.material3609 1).one,v3609_mb,v3609_mg]
  upper := v3609_upper
  lower := (Primitive.Addresses.material3609 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3609_pa_checked.trans (by decide +kernel)
    · exact v3609_pb_checked.trans (by decide +kernel)
    · exact v3609_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 82 Primitive.Addresses.material3609
    · exact v3609_mb_checked.trans (by decide +kernel)
    · exact v3609_mg_checked.trans (by decide +kernel)
  upper_error := v3609_upper_checked
  lower_error := reuse_lower_error 49 82 Primitive.Addresses.material3609

def v3610_pa : Scalar.QComplex := ((999998565386868899244720117215 : Int)/10^30,(-1693878450210248891533069845 : Int)/10^30)
theorem v3610_pa_checked : Scalar.distance (sourceCoefficient 49 83 1 0) v3610_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3610_pb : Scalar.QComplex := ((-730870438587632999137555 : Int)/10^30,(-431476880752917738607901404 : Int)/10^30)
theorem v3610_pb_checked : Scalar.distance (sourceCoefficient 49 83 1 1) v3610_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3610_pg : Scalar.QComplex := ((-93086294062339143123047 : Int)/10^30,(157677093727759656920 : Int)/10^30)
theorem v3610_pg_checked : Scalar.distance (sourceCoefficient 49 83 1 2) v3610_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3610_mb : Scalar.QComplex := ((-1103215281543611950494639 : Int)/10^30,(-431476089386084248168206480 : Int)/10^30)
theorem v3610_mb_checked : Scalar.distance (sourceCoefficient 49 83 3 1) v3610_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3610_mg : Scalar.QComplex := ((-93086123333827235535505 : Int)/10^30,(238006314342116674266 : Int)/10^30)
theorem v3610_mg_checked : Scalar.distance (sourceCoefficient 49 83 3 2) v3610_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3610_upper : Scalar.QComplex := ((999994152525936228405842480816 : Int)/10^30,(-3419782732073817264007300489 : Int)/10^30)
theorem v3610_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 83 5) 1) 14) v3610_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3610 : Material (49 : Basis) (83 : Basis) where
  plus := ![v3610_pa,v3610_pb,v3610_pg]
  minus := ![(Primitive.Addresses.material3610 1).one,v3610_mb,v3610_mg]
  upper := v3610_upper
  lower := (Primitive.Addresses.material3610 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3610_pa_checked.trans (by decide +kernel)
    · exact v3610_pb_checked.trans (by decide +kernel)
    · exact v3610_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 83 Primitive.Addresses.material3610
    · exact v3610_mb_checked.trans (by decide +kernel)
    · exact v3610_mg_checked.trans (by decide +kernel)
  upper_error := v3610_upper_checked
  lower_error := reuse_lower_error 49 83 Primitive.Addresses.material3610

def v3611_pa : Scalar.QComplex := ((999998505248201398368550388725 : Int)/10^30,(-1729017455932797538050375378 : Int)/10^30)
theorem v3611_pa_checked : Scalar.distance (sourceCoefficient 49 84 1 0) v3611_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3611_pb : Scalar.QComplex := ((-746032124017714067765166 : Int)/10^30,(-431476851968723665921313293 : Int)/10^30)
theorem v3611_pb_checked : Scalar.distance (sourceCoefficient 49 84 1 1) v3611_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3611_pg : Scalar.QComplex := ((-93086288158358894413614 : Int)/10^30,(160948057711191738259 : Int)/10^30)
theorem v3611_pg_checked : Scalar.distance (sourceCoefficient 49 84 1 2) v3611_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3611_mb : Scalar.QComplex := ((-1118376936488841517495986 : Int)/10^30,(-431476047518049223955540916 : Int)/10^30)
theorem v3611_mb_checked : Scalar.distance (sourceCoefficient 49 84 3 1) v3611_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3611_mg : Scalar.QComplex := ((-93086114607154586194942 : Int)/10^30,(241277272012750324898 : Int)/10^30)
theorem v3611_mg_checked : Scalar.distance (sourceCoefficient 49 84 3 2) v3611_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3611_upper : Scalar.QComplex := ((999994031740622205589101592600 : Int)/10^30,(-3454921581667060235142441702 : Int)/10^30)
theorem v3611_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 84 5) 1) 14) v3611_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3611 : Material (49 : Basis) (84 : Basis) where
  plus := ![v3611_pa,v3611_pb,v3611_pg]
  minus := ![(Primitive.Addresses.material3611 1).one,v3611_mb,v3611_mg]
  upper := v3611_upper
  lower := (Primitive.Addresses.material3611 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3611_pa_checked.trans (by decide +kernel)
    · exact v3611_pb_checked.trans (by decide +kernel)
    · exact v3611_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 84 Primitive.Addresses.material3611
    · exact v3611_mb_checked.trans (by decide +kernel)
    · exact v3611_mg_checked.trans (by decide +kernel)
  upper_error := v3611_upper_checked
  lower_error := reuse_lower_error 49 84 Primitive.Addresses.material3611

def v3612_pa : Scalar.QComplex := ((999998365432598647000808986962 : Int)/10^30,(-1808074149722684580179532869 : Int)/10^30)
theorem v3612_pa_checked : Scalar.distance (sourceCoefficient 49 85 1 0) v3612_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3612_pb : Scalar.QComplex := ((-780143295659850240668259 : Int)/10^30,(-431476784612348966246698371 : Int)/10^30)
theorem v3612_pb_checked : Scalar.distance (sourceCoefficient 49 85 1 1) v3612_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3612_pg : Scalar.QComplex := ((-93086274385200506843760 : Int)/10^30,(168307161519273553389 : Int)/10^30)
theorem v3612_pg_checked : Scalar.distance (sourceCoefficient 49 85 1 2) v3612_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3612_mb : Scalar.QComplex := ((-1152488037304311783157739 : Int)/10^30,(-431475950725294787114296529 : Int)/10^30)
theorem v3612_mb_checked : Scalar.distance (sourceCoefficient 49 85 3 1) v3612_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3612_mg : Scalar.QComplex := ((-93086094483426182358635 : Int)/10^30,(248636361195086096174 : Int)/10^30)
theorem v3612_mg_checked : Scalar.distance (sourceCoefficient 49 85 3 2) v3612_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3612_upper : Scalar.QComplex := ((999993755480546179029014251224 : Int)/10^30,(-3533977916402242152378232523 : Int)/10^30)
theorem v3612_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 85 5) 1) 14) v3612_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3612 : Material (49 : Basis) (85 : Basis) where
  plus := ![v3612_pa,v3612_pb,v3612_pg]
  minus := ![(Primitive.Addresses.material3612 1).one,v3612_mb,v3612_mg]
  upper := v3612_upper
  lower := (Primitive.Addresses.material3612 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3612_pa_checked.trans (by decide +kernel)
    · exact v3612_pb_checked.trans (by decide +kernel)
    · exact v3612_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 85 Primitive.Addresses.material3612
    · exact v3612_mb_checked.trans (by decide +kernel)
    · exact v3612_mg_checked.trans (by decide +kernel)
  upper_error := v3612_upper_checked
  lower_error := reuse_lower_error 49 85 Primitive.Addresses.material3612

def v3613_pa : Scalar.QComplex := ((999998338956124918809122936200 : Int)/10^30,(-1822658769790886230817913543 : Int)/10^30)
theorem v3613_pa_checked : Scalar.distance (sourceCoefficient 49 86 1 0) v3613_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3613_pb : Scalar.QComplex := ((-786436228375355303136456 : Int)/10^30,(-431476771793385523481235626 : Int)/10^30)
theorem v3613_pb_checked : Scalar.distance (sourceCoefficient 49 86 1 1) v3613_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3613_pg : Scalar.QComplex := ((-93086271770126591837442 : Int)/10^30,(169664791409621623354 : Int)/10^30)
theorem v3613_pg_checked : Scalar.distance (sourceCoefficient 49 86 1 2) v3613_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3613_mb : Scalar.QComplex := ((-1158780956614482287985338 : Int)/10^30,(-431475932475818607122253974 : Int)/10^30)
theorem v3613_mb_checked : Scalar.distance (sourceCoefficient 49 86 3 1) v3613_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3613_mg : Scalar.QComplex := ((-93086090696779791073904 : Int)/10^30,(249993988323235501118 : Int)/10^30)
theorem v3613_mg_checked : Scalar.distance (sourceCoefficient 49 86 3 2) v3613_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3613_upper : Scalar.QComplex := ((999993703832380753115799538063 : Int)/10^30,(-3548562469052373713326244410 : Int)/10^30)
theorem v3613_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 86 5) 1) 14) v3613_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3613 : Material (49 : Basis) (86 : Basis) where
  plus := ![v3613_pa,v3613_pb,v3613_pg]
  minus := ![(Primitive.Addresses.material3613 1).one,v3613_mb,v3613_mg]
  upper := v3613_upper
  lower := (Primitive.Addresses.material3613 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3613_pa_checked.trans (by decide +kernel)
    · exact v3613_pb_checked.trans (by decide +kernel)
    · exact v3613_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 86 Primitive.Addresses.material3613
    · exact v3613_mb_checked.trans (by decide +kernel)
    · exact v3613_mg_checked.trans (by decide +kernel)
  upper_error := v3613_upper_checked
  lower_error := reuse_lower_error 49 86 Primitive.Addresses.material3613

def v3614_pa : Scalar.QComplex := ((999998337195414131227173606437 : Int)/10^30,(-1823624524626287994077717882 : Int)/10^30)
theorem v3614_pa_checked : Scalar.distance (sourceCoefficient 49 87 1 0) v3614_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3614_pb : Scalar.QComplex := ((-786852929675818650817457 : Int)/10^30,(-431476770940227858124543721 : Int)/10^30)
theorem v3614_pb_checked : Scalar.distance (sourceCoefficient 49 87 1 1) v3614_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3614_pg : Scalar.QComplex := ((-93086271596147858229578 : Int)/10^30,(169754690057635773081 : Int)/10^30)
theorem v3614_pg_checked : Scalar.distance (sourceCoefficient 49 87 1 2) v3614_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3614_mb : Scalar.QComplex := ((-1159197657023552056905629 : Int)/10^30,(-431475931263066804665172476 : Int)/10^30)
theorem v3614_mb_checked : Scalar.distance (sourceCoefficient 49 87 3 1) v3614_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3614_mg : Scalar.QComplex := ((-93086090445222637894867 : Int)/10^30,(250083886787640464225 : Int)/10^30)
theorem v3614_mg_checked : Scalar.distance (sourceCoefficient 49 87 3 2) v3614_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3614_upper : Scalar.QComplex := ((999993700404867354596572927050 : Int)/10^30,(-3549528219410570005855661853 : Int)/10^30)
theorem v3614_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 87 5) 1) 14) v3614_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3614 : Material (49 : Basis) (87 : Basis) where
  plus := ![v3614_pa,v3614_pb,v3614_pg]
  minus := ![(Primitive.Addresses.material3614 1).one,v3614_mb,v3614_mg]
  upper := v3614_upper
  lower := (Primitive.Addresses.material3614 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3614_pa_checked.trans (by decide +kernel)
    · exact v3614_pb_checked.trans (by decide +kernel)
    · exact v3614_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 87 Primitive.Addresses.material3614
    · exact v3614_mb_checked.trans (by decide +kernel)
    · exact v3614_mg_checked.trans (by decide +kernel)
  upper_error := v3614_upper_checked
  lower_error := reuse_lower_error 49 87 Primitive.Addresses.material3614

def v3615_pa : Scalar.QComplex := ((999998315681187019057611865801 : Int)/10^30,(-1835384098501461087216566299 : Int)/10^30)
theorem v3615_pa_checked : Scalar.distance (sourceCoefficient 49 88 1 0) v3615_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3615_pb : Scalar.QComplex := ((-791926918967916332217177 : Int)/10^30,(-431476760508654795530455135 : Int)/10^30)
theorem v3615_pb_checked : Scalar.distance (sourceCoefficient 49 88 1 1) v3615_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3615_pg : Scalar.QComplex := ((-93086269469559186876545 : Int)/10^30,(170849346538019528043 : Int)/10^30)
theorem v3615_pg_checked : Scalar.distance (sourceCoefficient 49 88 1 2) v3615_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3615_mb : Scalar.QComplex := ((-1164271635424393899682478 : Int)/10^30,(-431475916452873391136689133 : Int)/10^30)
theorem v3615_mb_checked : Scalar.distance (sourceCoefficient 49 88 3 1) v3615_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3615_mg : Scalar.QComplex := ((-93086087373995517294525 : Int)/10^30,(251178541025283337889 : Int)/10^30)
theorem v3615_mg_checked : Scalar.distance (sourceCoefficient 49 88 3 2) v3615_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3615_upper : Scalar.QComplex := ((999993658594714597000710926165 : Int)/10^30,(-3561287738639634948340654045 : Int)/10^30)
theorem v3615_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 88 5) 1) 14) v3615_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3615 : Material (49 : Basis) (88 : Basis) where
  plus := ![v3615_pa,v3615_pb,v3615_pg]
  minus := ![(Primitive.Addresses.material3615 1).one,v3615_mb,v3615_mg]
  upper := v3615_upper
  lower := (Primitive.Addresses.material3615 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3615_pa_checked.trans (by decide +kernel)
    · exact v3615_pb_checked.trans (by decide +kernel)
    · exact v3615_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 88 Primitive.Addresses.material3615
    · exact v3615_mb_checked.trans (by decide +kernel)
    · exact v3615_mg_checked.trans (by decide +kernel)
  upper_error := v3615_upper_checked
  lower_error := reuse_lower_error 49 88 Primitive.Addresses.material3615

def v3616_pa : Scalar.QComplex := ((999998286021367427506414856564 : Int)/10^30,(-1851473555690773093363123146 : Int)/10^30)
theorem v3616_pa_checked : Scalar.distance (sourceCoefficient 49 89 1 0) v3616_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3616_pb : Scalar.QComplex := ((-798869154557789920245408 : Int)/10^30,(-431476746107278999357800312 : Int)/10^30)
theorem v3616_pb_checked : Scalar.distance (sourceCoefficient 49 89 1 1) v3616_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3616_pg : Scalar.QComplex := ((-93086266535628272947338 : Int)/10^30,(172347056287870565136 : Int)/10^30)
theorem v3616_pg_checked : Scalar.distance (sourceCoefficient 49 89 1 2) v3616_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3616_mb : Scalar.QComplex := ((-1171213856001617203551750 : Int)/10^30,(-431475896060666309877747154 : Int)/10^30)
theorem v3616_mb_checked : Scalar.distance (sourceCoefficient 49 89 3 1) v3616_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3616_mg : Scalar.QComplex := ((-93086083147609636023550 : Int)/10^30,(252676247685618347017 : Int)/10^30)
theorem v3616_mg_checked : Scalar.distance (sourceCoefficient 49 89 3 2) v3616_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3616_upper : Scalar.QComplex := ((999993601165995695668441983750 : Int)/10^30,(-3577377120675432574210967077 : Int)/10^30)
theorem v3616_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 89 5) 1) 14) v3616_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3616 : Material (49 : Basis) (89 : Basis) where
  plus := ![v3616_pa,v3616_pb,v3616_pg]
  minus := ![(Primitive.Addresses.material3616 1).one,v3616_mb,v3616_mg]
  upper := v3616_upper
  lower := (Primitive.Addresses.material3616 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3616_pa_checked.trans (by decide +kernel)
    · exact v3616_pb_checked.trans (by decide +kernel)
    · exact v3616_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 89 Primitive.Addresses.material3616
    · exact v3616_mb_checked.trans (by decide +kernel)
    · exact v3616_mg_checked.trans (by decide +kernel)
  upper_error := v3616_upper_checked
  lower_error := reuse_lower_error 49 89 Primitive.Addresses.material3616

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
