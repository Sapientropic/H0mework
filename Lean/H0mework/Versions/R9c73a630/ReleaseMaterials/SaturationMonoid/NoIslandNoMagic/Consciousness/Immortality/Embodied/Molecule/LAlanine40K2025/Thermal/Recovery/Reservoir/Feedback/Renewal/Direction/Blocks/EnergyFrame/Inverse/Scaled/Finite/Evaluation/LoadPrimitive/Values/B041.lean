import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B027
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B028

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v657_pa : Scalar.QComplex := ((999999079938028977717869618072 : Int)/10^30,(-1356511369480747750417864062 : Int)/10^30)
theorem v657_pa_checked : Scalar.distance (sourceCoefficient 6 97 1 0) v657_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v657_pb : Scalar.QComplex := ((-585303852173557580108773 : Int)/10^30,(-431476894942492852612462437 : Int)/10^30)
theorem v657_pb_checked : Scalar.distance (sourceCoefficient 6 97 1 1) v657_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v657_pg : Scalar.QComplex := ((-93086319541824041564488 : Int)/10^30,(126272766980373096494 : Int)/10^30)
theorem v657_pg_checked : Scalar.distance (sourceCoefficient 6 97 1 2) v657_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v657_mb : Scalar.QComplex := ((-957648761575593623722747 : Int)/10^30,(-431476229193062078413422670 : Int)/10^30)
theorem v657_mb_checked : Scalar.distance (sourceCoefficient 6 97 3 1) v657_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v657_mg : Scalar.QComplex := ((-93086175913822231423084 : Int)/10^30,(206602021275644124482 : Int)/10^30)
theorem v657_mg_checked : Scalar.distance (sourceCoefficient 6 97 3 2) v657_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v657_upper : Scalar.QComplex := ((999995249341305580003297062659 : Int)/10^30,(-3082417041881575527175703617 : Int)/10^30)
theorem v657_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 97 5) 1) 14) v657_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material657 : Material (6 : Basis) (97 : Basis) where
  plus := ![v657_pa,v657_pb,v657_pg]
  minus := ![(Primitive.Addresses.material657 1).one,v657_mb,v657_mg]
  upper := v657_upper
  lower := (Primitive.Addresses.material657 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v657_pa_checked.trans (by decide +kernel)
    · exact v657_pb_checked.trans (by decide +kernel)
    · exact v657_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 97 Primitive.Addresses.material657
    · exact v657_mb_checked.trans (by decide +kernel)
    · exact v657_mg_checked.trans (by decide +kernel)
  upper_error := v657_upper_checked
  lower_error := reuse_lower_error 6 97 Primitive.Addresses.material657

def v658_pa : Scalar.QComplex := ((999999963276134365473736816424 : Int)/10^30,(271012416542877642420811317 : Int)/10^30)
theorem v658_pa_checked : Scalar.distance (sourceCoefficient 7 8 1 0) v658_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v658_pb : Scalar.QComplex := ((116935765621680614997815 : Int)/10^30,(-431477505049465260432544583 : Int)/10^30)
theorem v658_pb_checked : Scalar.distance (sourceCoefficient 7 8 1 1) v658_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v658_pg : Scalar.QComplex := ((-93086426467084497790367 : Int)/10^30,(-25227578310639650129 : Int)/10^30)
theorem v658_pg_checked : Scalar.distance (sourceCoefficient 7 8 1 2) v658_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v658_mb : Scalar.QComplex := ((-255409931751098059739327 : Int)/10^30,(-431477445300969774504825299 : Int)/10^30)
theorem v658_mb_checked : Scalar.distance (sourceCoefficient 7 8 3 1) v658_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v658_mg : Scalar.QComplex := ((-93086413577017538373490 : Int)/10^30,(55101824666817876292 : Int)/10^30)
theorem v658_mg_checked : Scalar.distance (sourceCoefficient 7 8 3 2) v658_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v658_upper : Scalar.QComplex := ((999998941636502211686091028512 : Int)/10^30,(-1454897204424881135123863950 : Int)/10^30)
theorem v658_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 8 5) 1) 14) v658_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material658 : Material (7 : Basis) (8 : Basis) where
  plus := ![v658_pa,v658_pb,v658_pg]
  minus := ![(Primitive.Addresses.material658 1).one,v658_mb,v658_mg]
  upper := v658_upper
  lower := (Primitive.Addresses.material658 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v658_pa_checked.trans (by decide +kernel)
    · exact v658_pb_checked.trans (by decide +kernel)
    · exact v658_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 8 Primitive.Addresses.material658
    · exact v658_mb_checked.trans (by decide +kernel)
    · exact v658_mg_checked.trans (by decide +kernel)
  upper_error := v658_upper_checked
  lower_error := reuse_lower_error 7 8 Primitive.Addresses.material658

def v659_pa : Scalar.QComplex := ((999999968786629759427933047182 : Int)/10^30,(249853436051757455374610609 : Int)/10^30)
theorem v659_pa_checked : Scalar.distance (sourceCoefficient 7 9 1 0) v659_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v659_pb : Scalar.QComplex := ((107806141137516487898307 : Int)/10^30,(-431477507278272180885813689 : Int)/10^30)
theorem v659_pb_checked : Scalar.distance (sourceCoefficient 7 9 1 1) v659_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v659_pg : Scalar.QComplex := ((-93086426963980701928441 : Int)/10^30,(-23257964352690995587 : Int)/10^30)
theorem v659_pg_checked : Scalar.distance (sourceCoefficient 7 9 1 2) v659_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v659_mb : Scalar.QComplex := ((-264539554759245737547130 : Int)/10^30,(-431477439651321118260710183 : Int)/10^30)
theorem v659_mb_checked : Scalar.distance (sourceCoefficient 7 9 3 1) v659_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v659_mg : Scalar.QComplex := ((-93086412374225419904375 : Int)/10^30,(57071438320188283282 : Int)/10^30)
theorem v659_mg_checked : Scalar.distance (sourceCoefficient 7 9 3 2) v659_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v659_upper : Scalar.QComplex := ((999998910628508598446890167098 : Int)/10^30,(-1476056162912800530820350567 : Int)/10^30)
theorem v659_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 9 5) 1) 14) v659_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material659 : Material (7 : Basis) (9 : Basis) where
  plus := ![v659_pa,v659_pb,v659_pg]
  minus := ![(Primitive.Addresses.material659 1).one,v659_mb,v659_mg]
  upper := v659_upper
  lower := (Primitive.Addresses.material659 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v659_pa_checked.trans (by decide +kernel)
    · exact v659_pb_checked.trans (by decide +kernel)
    · exact v659_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 9 Primitive.Addresses.material659
    · exact v659_mb_checked.trans (by decide +kernel)
    · exact v659_mg_checked.trans (by decide +kernel)
  upper_error := v659_upper_checked
  lower_error := reuse_lower_error 7 9 Primitive.Addresses.material659

def v660_pa : Scalar.QComplex := ((999999978372486935535749149210 : Int)/10^30,(207978425951297122389119214 : Int)/10^30)
theorem v660_pa_checked : Scalar.distance (sourceCoefficient 7 10 1 0) v660_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v660_pb : Scalar.QComplex := ((89738015497406052682996 : Int)/10^30,(-431477510929956487604249708 : Int)/10^30)
theorem v660_pb_checked : Scalar.distance (sourceCoefficient 7 10 1 1) v660_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v660_pg : Scalar.QComplex := ((-93086427804042254784462 : Int)/10^30,(-19359969150821753424 : Int)/10^30)
theorem v660_pg_checked : Scalar.distance (sourceCoefficient 7 10 1 2) v660_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v660_mb : Scalar.QComplex := ((-282607676823006333756582 : Int)/10^30,(-431477427711025396045590335 : Int)/10^30)
theorem v660_mb_checked : Scalar.distance (sourceCoefficient 7 10 3 1) v660_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v660_mg : Scalar.QComplex := ((-93086409850492359940760 : Int)/10^30,(60969432795591049754 : Int)/10^30)
theorem v660_mg_checked : Scalar.distance (sourceCoefficient 7 10 3 2) v660_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v660_upper : Scalar.QComplex := ((999998847941882935393101757201 : Int)/10^30,(-1517931127189672167188561374 : Int)/10^30)
theorem v660_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 10 5) 1) 14) v660_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material660 : Material (7 : Basis) (10 : Basis) where
  plus := ![v660_pa,v660_pb,v660_pg]
  minus := ![(Primitive.Addresses.material660 1).one,v660_mb,v660_mg]
  upper := v660_upper
  lower := (Primitive.Addresses.material660 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v660_pa_checked.trans (by decide +kernel)
    · exact v660_pb_checked.trans (by decide +kernel)
    · exact v660_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 10 Primitive.Addresses.material660
    · exact v660_mb_checked.trans (by decide +kernel)
    · exact v660_mg_checked.trans (by decide +kernel)
  upper_error := v660_upper_checked
  lower_error := reuse_lower_error 7 10 Primitive.Addresses.material660

def v661_pa : Scalar.QComplex := ((999999980206380338016818091652 : Int)/10^30,(198965421448499398526887890 : Int)/10^30)
theorem v661_pa_checked : Scalar.distance (sourceCoefficient 7 11 1 0) v661_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v661_pb : Scalar.QComplex := ((85849106637124386045806 : Int)/10^30,(-431477511583997384782901229 : Int)/10^30)
theorem v661_pb_checked : Scalar.distance (sourceCoefficient 7 11 1 1) v661_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v661_pg : Scalar.QComplex := ((-93086427959948539261611 : Int)/10^30,(-18520980736783787674 : Int)/10^30)
theorem v661_pg_checked : Scalar.distance (sourceCoefficient 7 11 1 2) v661_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v661_mb : Scalar.QComplex := ((-286496584799677337152517 : Int)/10^30,(-431477425009112853225041584 : Int)/10^30)
theorem v661_mb_checked : Scalar.distance (sourceCoefficient 7 11 3 1) v661_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v661_mg : Scalar.QComplex := ((-93086409282389371687572 : Int)/10^30,(61808421031775387038 : Int)/10^30)
theorem v661_mg_checked : Scalar.distance (sourceCoefficient 7 11 3 2) v661_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v661_upper : Scalar.QComplex := ((999998834220145488057836681113 : Int)/10^30,(-1526944121433792069187501611 : Int)/10^30)
theorem v661_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 11 5) 1) 14) v661_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material661 : Material (7 : Basis) (11 : Basis) where
  plus := ![v661_pa,v661_pb,v661_pg]
  minus := ![(Primitive.Addresses.material661 1).one,v661_mb,v661_mg]
  upper := v661_upper
  lower := (Primitive.Addresses.material661 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v661_pa_checked.trans (by decide +kernel)
    · exact v661_pb_checked.trans (by decide +kernel)
    · exact v661_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 11 Primitive.Addresses.material661
    · exact v661_mb_checked.trans (by decide +kernel)
    · exact v661_mg_checked.trans (by decide +kernel)
  upper_error := v661_upper_checked
  lower_error := reuse_lower_error 7 11 Primitive.Addresses.material661

def v662_pa : Scalar.QComplex := ((999999981173438856444824014317 : Int)/10^30,(194044123674670827377142341 : Int)/10^30)
theorem v662_pa_checked : Scalar.distance (sourceCoefficient 7 12 1 0) v662_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v662_pb : Scalar.QComplex := ((83725677262380497839438 : Int)/10^30,(-431477511921392360906638238 : Int)/10^30)
theorem v662_pb_checked : Scalar.distance (sourceCoefficient 7 12 1 1) v662_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v662_pg : Scalar.QComplex := ((-93086428041353140497019 : Int)/10^30,(-18062874695351490186 : Int)/10^30)
theorem v662_pg_checked : Scalar.distance (sourceCoefficient 7 12 1 2) v662_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v662_mb : Scalar.QComplex := ((-288620013674928092314315 : Int)/10^30,(-431477423514083789026107822 : Int)/10^30)
theorem v662_mb_checked : Scalar.distance (sourceCoefficient 7 12 3 1) v662_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v662_mg : Scalar.QComplex := ((-93086408968469061186452 : Int)/10^30,(62266526972882373360 : Int)/10^30)
theorem v662_mg_checked : Scalar.distance (sourceCoefficient 7 12 3 2) v662_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v662_upper : Scalar.QComplex := ((999998826693489065184178069580 : Int)/10^30,(-1531865413546980974408413040 : Int)/10^30)
theorem v662_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 12 5) 1) 14) v662_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material662 : Material (7 : Basis) (12 : Basis) where
  plus := ![v662_pa,v662_pb,v662_pg]
  minus := ![(Primitive.Addresses.material662 1).one,v662_mb,v662_mg]
  upper := v662_upper
  lower := (Primitive.Addresses.material662 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v662_pa_checked.trans (by decide +kernel)
    · exact v662_pb_checked.trans (by decide +kernel)
    · exact v662_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 12 Primitive.Addresses.material662
    · exact v662_mb_checked.trans (by decide +kernel)
    · exact v662_mg_checked.trans (by decide +kernel)
  upper_error := v662_upper_checked
  lower_error := reuse_lower_error 7 12 Primitive.Addresses.material662

def v663_pa : Scalar.QComplex := ((999999989842750582742401670590 : Int)/10^30,(142528939978326790804629579 : Int)/10^30)
theorem v663_pa_checked : Scalar.distance (sourceCoefficient 7 13 1 0) v663_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v663_pb : Scalar.QComplex := ((61498033407477349019566 : Int)/10^30,(-431477514616877017862956425 : Int)/10^30)
theorem v663_pb_checked : Scalar.distance (sourceCoefficient 7 13 1 1) v663_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v663_pg : Scalar.QComplex := ((-93086428735611053554320 : Int)/10^30,(-13267510148816111800 : Int)/10^30)
theorem v663_pg_checked : Scalar.distance (sourceCoefficient 7 13 1 2) v663_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v663_mb : Scalar.QComplex := ((-310847651579545439276333 : Int)/10^30,(-431477407028111891465678629 : Int)/10^30)
theorem v663_mb_checked : Scalar.distance (sourceCoefficient 7 13 3 1) v663_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v663_mg : Scalar.QComplex := ((-93086405524543087281571 : Int)/10^30,(67061890332997682837 : Int)/10^30)
theorem v663_mg_checked : Scalar.distance (sourceCoefficient 7 13 3 2) v663_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v663_upper : Scalar.QComplex := ((999998746452254240628672411419 : Int)/10^30,(-1583380535479955859614425769 : Int)/10^30)
theorem v663_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 13 5) 1) 14) v663_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material663 : Material (7 : Basis) (13 : Basis) where
  plus := ![v663_pa,v663_pb,v663_pg]
  minus := ![(Primitive.Addresses.material663 1).one,v663_mb,v663_mg]
  upper := v663_upper
  lower := (Primitive.Addresses.material663 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v663_pa_checked.trans (by decide +kernel)
    · exact v663_pb_checked.trans (by decide +kernel)
    · exact v663_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 13 Primitive.Addresses.material663
    · exact v663_mb_checked.trans (by decide +kernel)
    · exact v663_mg_checked.trans (by decide +kernel)
  upper_error := v663_upper_checked
  lower_error := reuse_lower_error 7 13 Primitive.Addresses.material663

def v664_pa : Scalar.QComplex := ((999999992034431525044399385770 : Int)/10^30,(126218607528608554600140060 : Int)/10^30)
theorem v664_pa_checked : Scalar.distance (sourceCoefficient 7 14 1 0) v664_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v664_pb : Scalar.QComplex := ((54460491576208860965251 : Int)/10^30,(-431477515152083563307060295 : Int)/10^30)
theorem v664_pb_checked : Scalar.distance (sourceCoefficient 7 14 1 1) v664_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v664_pg : Scalar.QComplex := ((-93086428895351332167189 : Int)/10^30,(-11749239528571448546 : Int)/10^30)
theorem v664_pg_checked : Scalar.distance (sourceCoefficient 7 14 1 2) v664_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v664_mb : Scalar.QComplex := ((-317885191252274615909047 : Int)/10^30,(-431477401490236596361225095 : Int)/10^30)
theorem v664_mb_checked : Scalar.distance (sourceCoefficient 7 14 3 1) v664_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v664_mg : Scalar.QComplex := ((-93086404374084141515026 : Int)/10^30,(68580160525769471786 : Int)/10^30)
theorem v664_mg_checked : Scalar.distance (sourceCoefficient 7 14 3 2) v664_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v664_upper : Scalar.QComplex := ((999998720493777772267038564584 : Int)/10^30,(-1599690847419992336872348426 : Int)/10^30)
theorem v664_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 14 5) 1) 14) v664_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material664 : Material (7 : Basis) (14 : Basis) where
  plus := ![v664_pa,v664_pb,v664_pg]
  minus := ![(Primitive.Addresses.material664 1).one,v664_mb,v664_mg]
  upper := v664_upper
  lower := (Primitive.Addresses.material664 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v664_pa_checked.trans (by decide +kernel)
    · exact v664_pb_checked.trans (by decide +kernel)
    · exact v664_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 14 Primitive.Addresses.material664
    · exact v664_mb_checked.trans (by decide +kernel)
    · exact v664_mg_checked.trans (by decide +kernel)
  upper_error := v664_upper_checked
  lower_error := reuse_lower_error 7 14 Primitive.Addresses.material664

def v665_pa : Scalar.QComplex := ((999999995005955413988291037329 : Int)/10^30,(99940427991293576400295490 : Int)/10^30)
theorem v665_pa_checked : Scalar.distance (sourceCoefficient 7 15 1 0) v665_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v665_pb : Scalar.QComplex := ((43122047802276936828758 : Int)/10^30,(-431477515692449640994389503 : Int)/10^30)
theorem v665_pb_checked : Scalar.distance (sourceCoefficient 7 15 1 1) v665_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v665_pg : Scalar.QComplex := ((-93086429091944564517805 : Int)/10^30,(-9303097610090225500 : Int)/10^30)
theorem v665_pg_checked : Scalar.distance (sourceCoefficient 7 15 1 2) v665_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v665_mb : Scalar.QComplex := ((-329223631270697318390452 : Int)/10^30,(-431477392246036160493135798 : Int)/10^30)
theorem v665_mb_checked : Scalar.distance (sourceCoefficient 7 15 3 1) v665_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v665_mg : Scalar.QComplex := ((-93086402459766995158002 : Int)/10^30,(71026301703091369662 : Int)/10^30)
theorem v665_mg_checked : Scalar.distance (sourceCoefficient 7 15 3 2) v665_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v665_upper : Scalar.QComplex := ((999998678111543291894829862655 : Int)/10^30,(-1625968992947626403825251501 : Int)/10^30)
theorem v665_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 15 5) 1) 14) v665_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material665 : Material (7 : Basis) (15 : Basis) where
  plus := ![v665_pa,v665_pb,v665_pg]
  minus := ![(Primitive.Addresses.material665 1).one,v665_mb,v665_mg]
  upper := v665_upper
  lower := (Primitive.Addresses.material665 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v665_pa_checked.trans (by decide +kernel)
    · exact v665_pb_checked.trans (by decide +kernel)
    · exact v665_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 15 Primitive.Addresses.material665
    · exact v665_mb_checked.trans (by decide +kernel)
    · exact v665_mg_checked.trans (by decide +kernel)
  upper_error := v665_upper_checked
  lower_error := reuse_lower_error 7 15 Primitive.Addresses.material665

def v666_pa : Scalar.QComplex := ((999999995333450044339719579122 : Int)/10^30,(96607970113981136028894436 : Int)/10^30)
theorem v666_pa_checked : Scalar.distance (sourceCoefficient 7 16 1 0) v666_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v666_pb : Scalar.QComplex := ((41684167139270282547185 : Int)/10^30,(-431477515732591594850417267 : Int)/10^30)
theorem v666_pb_checked : Scalar.distance (sourceCoefficient 7 16 1 1) v666_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v666_pg : Scalar.QComplex := ((-93086429111517305464118 : Int)/10^30,(-8992891003588462554 : Int)/10^30)
theorem v666_pg_checked : Scalar.distance (sourceCoefficient 7 16 1 2) v666_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v666_mb : Scalar.QComplex := ((-330661511432955985693256 : Int)/10^30,(-431477391045351846968804149 : Int)/10^30)
theorem v666_mb_checked : Scalar.distance (sourceCoefficient 7 16 3 1) v666_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v666_mg : Scalar.QComplex := ((-93086402211645398592390 : Int)/10^30,(71336508210979429778 : Int)/10^30)
theorem v666_mg_checked : Scalar.distance (sourceCoefficient 7 16 3 2) v666_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v666_upper : Scalar.QComplex := ((999998672687517456457254109352 : Int)/10^30,(-1629301446426860315846249081 : Int)/10^30)
theorem v666_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 16 5) 1) 14) v666_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material666 : Material (7 : Basis) (16 : Basis) where
  plus := ![v666_pa,v666_pb,v666_pg]
  minus := ![(Primitive.Addresses.material666 1).one,v666_mb,v666_mg]
  upper := v666_upper
  lower := (Primitive.Addresses.material666 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v666_pa_checked.trans (by decide +kernel)
    · exact v666_pb_checked.trans (by decide +kernel)
    · exact v666_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 16 Primitive.Addresses.material666
    · exact v666_mb_checked.trans (by decide +kernel)
    · exact v666_mg_checked.trans (by decide +kernel)
  upper_error := v666_upper_checked
  lower_error := reuse_lower_error 7 16 Primitive.Addresses.material666

def v667_pa : Scalar.QComplex := ((999999995957509091847298246761 : Int)/10^30,(89916526845534190506052717 : Int)/10^30)
theorem v667_pa_checked : Scalar.distance (sourceCoefficient 7 17 1 0) v667_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v667_pb : Scalar.QComplex := ((38796959788963058445912 : Int)/10^30,(-431477515793900992090204309 : Int)/10^30)
theorem v667_pb_checked : Scalar.distance (sourceCoefficient 7 17 1 1) v667_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v667_pg : Scalar.QComplex := ((-93086429147176427018281 : Int)/10^30,(-8370008439202688559 : Int)/10^30)
theorem v667_pg_checked : Scalar.distance (sourceCoefficient 7 17 1 2) v667_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v667_mb : Scalar.QComplex := ((-333548717761131209925872 : Int)/10^30,(-431477388615131313057098257 : Int)/10^30)
theorem v667_mb_checked : Scalar.distance (sourceCoefficient 7 17 3 1) v667_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v667_mg : Scalar.QComplex := ((-93086401709784907393411 : Int)/10^30,(71959390574209773786 : Int)/10^30)
theorem v667_mg_checked : Scalar.distance (sourceCoefficient 7 17 3 2) v667_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v667_upper : Scalar.QComplex := ((999998661762751536154114556848 : Int)/10^30,(-1635992880806257846962960364 : Int)/10^30)
theorem v667_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 17 5) 1) 14) v667_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material667 : Material (7 : Basis) (17 : Basis) where
  plus := ![v667_pa,v667_pb,v667_pg]
  minus := ![(Primitive.Addresses.material667 1).one,v667_mb,v667_mg]
  upper := v667_upper
  lower := (Primitive.Addresses.material667 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v667_pa_checked.trans (by decide +kernel)
    · exact v667_pb_checked.trans (by decide +kernel)
    · exact v667_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 17 Primitive.Addresses.material667
    · exact v667_mb_checked.trans (by decide +kernel)
    · exact v667_mg_checked.trans (by decide +kernel)
  upper_error := v667_upper_checked
  lower_error := reuse_lower_error 7 17 Primitive.Addresses.material667

def v668_pa : Scalar.QComplex := ((999999997715362148412714086846 : Int)/10^30,(67596417789369591070909446 : Int)/10^30)
theorem v668_pa_checked : Scalar.distance (sourceCoefficient 7 18 1 0) v668_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v668_pb : Scalar.QComplex := ((29166334492191221020346 : Int)/10^30,(-431477515812139555185435054 : Int)/10^30)
theorem v668_pb_checked : Scalar.distance (sourceCoefficient 7 18 1 1) v668_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v668_pg : Scalar.QComplex := ((-93086429230959942868597 : Int)/10^30,(-6292309175192201900 : Int)/10^30)
theorem v668_pg_checked : Scalar.distance (sourceCoefficient 7 18 1 2) v668_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v668_mb : Scalar.QComplex := ((-343179339487720166560594 : Int)/10^30,(-431477380322573985509094106 : Int)/10^30)
theorem v668_mb_checked : Scalar.distance (sourceCoefficient 7 18 3 1) v668_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v668_mg : Scalar.QComplex := ((-93086400000607503307388 : Int)/10^30,(74037089136899269616 : Int)/10^30)
theorem v668_mg_checked : Scalar.distance (sourceCoefficient 7 18 3 2) v668_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v668_upper : Scalar.QComplex := ((999998624998118608139997939348 : Int)/10^30,(-1658312959653136815877730376 : Int)/10^30)
theorem v668_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 18 5) 1) 14) v668_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material668 : Material (7 : Basis) (18 : Basis) where
  plus := ![v668_pa,v668_pb,v668_pg]
  minus := ![(Primitive.Addresses.material668 1).one,v668_mb,v668_mg]
  upper := v668_upper
  lower := (Primitive.Addresses.material668 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v668_pa_checked.trans (by decide +kernel)
    · exact v668_pb_checked.trans (by decide +kernel)
    · exact v668_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 18 Primitive.Addresses.material668
    · exact v668_mb_checked.trans (by decide +kernel)
    · exact v668_mg_checked.trans (by decide +kernel)
  upper_error := v668_upper_checked
  lower_error := reuse_lower_error 7 18 Primitive.Addresses.material668

def v669_pa : Scalar.QComplex := ((999999998650870637491395389032 : Int)/10^30,(51944766080877283946297857 : Int)/10^30)
theorem v669_pa_checked : Scalar.distance (sourceCoefficient 7 19 1 0) v669_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v669_pb : Scalar.QComplex := ((22412998650041661695426 : Int)/10^30,(-431477515653971712276075404 : Int)/10^30)
theorem v669_pb_checked : Scalar.distance (sourceCoefficient 7 19 1 1) v669_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v669_pg : Scalar.QComplex := ((-93086429257440048015870 : Int)/10^30,(-4835352799605371064 : Int)/10^30)
theorem v669_pg_checked : Scalar.distance (sourceCoefficient 7 19 1 2) v669_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v669_mb : Scalar.QComplex := ((-349932672678802424342414 : Int)/10^30,(-431477374336581528673200558 : Int)/10^30)
theorem v669_mb_checked : Scalar.distance (sourceCoefficient 7 19 3 1) v669_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v669_mg : Scalar.QComplex := ((-93086398769799865342742 : Int)/10^30,(75494044992845793748 : Int)/10^30)
theorem v669_mg_checked : Scalar.distance (sourceCoefficient 7 19 3 2) v669_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v669_upper : Scalar.QComplex := ((999998598920294761782246784237 : Int)/10^30,(-1673964589664935258848012591 : Int)/10^30)
theorem v669_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 19 5) 1) 14) v669_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material669 : Material (7 : Basis) (19 : Basis) where
  plus := ![v669_pa,v669_pb,v669_pg]
  minus := ![(Primitive.Addresses.material669 1).one,v669_mb,v669_mg]
  upper := v669_upper
  lower := (Primitive.Addresses.material669 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v669_pa_checked.trans (by decide +kernel)
    · exact v669_pb_checked.trans (by decide +kernel)
    · exact v669_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 19 Primitive.Addresses.material669
    · exact v669_mb_checked.trans (by decide +kernel)
    · exact v669_mg_checked.trans (by decide +kernel)
  upper_error := v669_upper_checked
  lower_error := reuse_lower_error 7 19 Primitive.Addresses.material669

def v670_pa : Scalar.QComplex := ((999999998792662976288419305561 : Int)/10^30,(49139332982504948731667994 : Int)/10^30)
theorem v670_pa_checked : Scalar.distance (sourceCoefficient 7 20 1 0) v670_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v670_pb : Scalar.QComplex := ((21202517339658063399622 : Int)/10^30,(-431477515610726756838730897 : Int)/10^30)
theorem v670_pb_checked : Scalar.distance (sourceCoefficient 7 20 1 1) v670_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v670_pg : Scalar.QComplex := ((-93086429259374712639167 : Int)/10^30,(-4574205049051412634 : Int)/10^30)
theorem v670_pg_checked : Scalar.distance (sourceCoefficient 7 20 1 2) v670_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v670_mb : Scalar.QComplex := ((-351143153501150060191634 : Int)/10^30,(-431477373248745736531298391 : Int)/10^30)
theorem v670_mb_checked : Scalar.distance (sourceCoefficient 7 20 3 1) v670_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v670_mg : Scalar.QComplex := ((-93086398546375782175680 : Int)/10^30,(75755192647832038041 : Int)/10^30)
theorem v670_mg_checked : Scalar.distance (sourceCoefficient 7 20 3 2) v670_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v670_upper : Scalar.QComplex := ((999998594220163868508173099207 : Int)/10^30,(-1676770018829665256821531379 : Int)/10^30)
theorem v670_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 20 5) 1) 14) v670_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material670 : Material (7 : Basis) (20 : Basis) where
  plus := ![v670_pa,v670_pb,v670_pg]
  minus := ![(Primitive.Addresses.material670 1).one,v670_mb,v670_mg]
  upper := v670_upper
  lower := (Primitive.Addresses.material670 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v670_pa_checked.trans (by decide +kernel)
    · exact v670_pb_checked.trans (by decide +kernel)
    · exact v670_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 20 Primitive.Addresses.material670
    · exact v670_mb_checked.trans (by decide +kernel)
    · exact v670_mg_checked.trans (by decide +kernel)
  upper_error := v670_upper_checked
  lower_error := reuse_lower_error 7 20 Primitive.Addresses.material670

def v671_pa : Scalar.QComplex := ((999999999992513524774831099412 : Int)/10^30,(-3869489688612925334275954 : Int)/10^30)
theorem v671_pa_checked : Scalar.distance (sourceCoefficient 7 21 1 0) v671_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v671_pb : Scalar.QComplex := ((-1669597791081539187674 : Int)/10^30,(-431477513942550732986712153 : Int)/10^30)
theorem v671_pb_checked : Scalar.distance (sourceCoefficient 7 21 1 1) v671_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v671_pg : Scalar.QComplex := ((-93086429135274493950389 : Int)/10^30,(360196977691439048 : Int)/10^30)
theorem v671_pg_checked : Scalar.distance (sourceCoefficient 7 21 1 2) v671_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v671_mb : Scalar.QComplex := ((-374015258675995115578669 : Int)/10^30,(-431477351842965097814744568 : Int)/10^30)
theorem v671_mb_checked : Scalar.distance (sourceCoefficient 7 21 3 1) v671_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v671_mg : Scalar.QComplex := ((-93086394164108897833455 : Int)/10^30,(80689592730178602391 : Int)/10^30)
theorem v671_mg_checked : Scalar.distance (sourceCoefficient 7 21 3 2) v671_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v671_upper : Scalar.QComplex := ((999998503931593622436166836348 : Int)/10^30,(-1729778764621201813077042774 : Int)/10^30)
theorem v671_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 21 5) 1) 14) v671_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material671 : Material (7 : Basis) (21 : Basis) where
  plus := ![v671_pa,v671_pb,v671_pg]
  minus := ![(Primitive.Addresses.material671 1).one,v671_mb,v671_mg]
  upper := v671_upper
  lower := (Primitive.Addresses.material671 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v671_pa_checked.trans (by decide +kernel)
    · exact v671_pb_checked.trans (by decide +kernel)
    · exact v671_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 21 Primitive.Addresses.material671
    · exact v671_mb_checked.trans (by decide +kernel)
    · exact v671_mg_checked.trans (by decide +kernel)
  upper_error := v671_upper_checked
  lower_error := reuse_lower_error 7 21 Primitive.Addresses.material671

def v672_pa : Scalar.QComplex := ((999999999986147321866143392616 : Int)/10^30,(-5263587775227208850027179 : Int)/10^30)
theorem v672_pa_checked : Scalar.distance (sourceCoefficient 7 22 1 0) v672_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v672_pb : Scalar.QComplex := ((-2271119767359142403779 : Int)/10^30,(-431477513876862403590751379 : Int)/10^30)
theorem v672_pb_checked : Scalar.distance (sourceCoefficient 7 22 1 1) v672_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v672_pg : Scalar.QComplex := ((-93086429127892430729499 : Int)/10^30,(489968590403915948 : Int)/10^30)
theorem v672_pg_checked : Scalar.distance (sourceCoefficient 7 22 1 2) v672_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v672_mb : Scalar.QComplex := ((-374616780371612526338046 : Int)/10^30,(-431477351258190418894105510 : Int)/10^30)
theorem v672_mb_checked : Scalar.distance (sourceCoefficient 7 22 3 1) v672_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v672_mg : Scalar.QComplex := ((-93086394044739780286848 : Int)/10^30,(80819364288200788939 : Int)/10^30)
theorem v672_mg_checked : Scalar.distance (sourceCoefficient 7 22 3 2) v672_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v672_upper : Scalar.QComplex := ((999998501519140603103412986794 : Int)/10^30,(-1731172860620483270162765518 : Int)/10^30)
theorem v672_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 22 5) 1) 14) v672_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material672 : Material (7 : Basis) (22 : Basis) where
  plus := ![v672_pa,v672_pb,v672_pg]
  minus := ![(Primitive.Addresses.material672 1).one,v672_mb,v672_mg]
  upper := v672_upper
  lower := (Primitive.Addresses.material672 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v672_pa_checked.trans (by decide +kernel)
    · exact v672_pb_checked.trans (by decide +kernel)
    · exact v672_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 22 Primitive.Addresses.material672
    · exact v672_mb_checked.trans (by decide +kernel)
    · exact v672_mg_checked.trans (by decide +kernel)
  upper_error := v672_upper_checked
  lower_error := reuse_lower_error 7 22 Primitive.Addresses.material672

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
