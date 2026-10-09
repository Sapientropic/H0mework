import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B165
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B166

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3969_pa : Scalar.QComplex := ((999997833616296080310893561268 : Int)/10^30,(-2081528936772445064748693772 : Int)/10^30)
theorem v3969_pa_checked : Scalar.distance (sourceCoefficient 57 94 1 0) v3969_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3969_pb : Scalar.QComplex := ((-898132853908784390681112 : Int)/10^30,(-431476542238716109878104766 : Int)/10^30)
theorem v3969_pb_checked : Scalar.distance (sourceCoefficient 57 94 1 1) v3969_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3969_pg : Scalar.QComplex := ((-93086223488065230036110 : Int)/10^30,(193762087568303566338 : Int)/10^30)
theorem v3969_pg_checked : Scalar.distance (sourceCoefficient 57 94 1 2) v3969_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3969_mb : Scalar.QComplex := ((-1270477342462811956043956 : Int)/10^30,(-431475606532077461132699061 : Int)/10^30)
theorem v3969_mb_checked : Scalar.distance (sourceCoefficient 57 94 3 1) v3969_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3969_mg : Scalar.QComplex := ((-93086021619855123878785 : Int)/10^30,(274091233844148371471 : Int)/10^30)
theorem v3969_mg_checked : Scalar.distance (sourceCoefficient 57 94 3 2) v3969_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3969_upper : Scalar.QComplex := ((999992751706880866858270670606 : Int)/10^30,(-3807431378306527350066413546 : Int)/10^30)
theorem v3969_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 94 5) 1) 14) v3969_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3969 : Material (57 : Basis) (94 : Basis) where
  plus := ![v3969_pa,v3969_pb,v3969_pg]
  minus := ![(Primitive.Addresses.material3969 1).one,v3969_mb,v3969_mg]
  upper := v3969_upper
  lower := (Primitive.Addresses.material3969 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3969_pa_checked.trans (by decide +kernel)
    · exact v3969_pb_checked.trans (by decide +kernel)
    · exact v3969_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 94 Primitive.Addresses.material3969
    · exact v3969_mb_checked.trans (by decide +kernel)
    · exact v3969_mg_checked.trans (by decide +kernel)
  upper_error := v3969_upper_checked
  lower_error := reuse_lower_error 57 94 Primitive.Addresses.material3969

def v3970_pa : Scalar.QComplex := ((999997740478117062351940878041 : Int)/10^30,(-2125803062476897610170519813 : Int)/10^30)
theorem v3970_pa_checked : Scalar.distance (sourceCoefficient 57 95 1 0) v3970_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3970_pb : Scalar.QComplex := ((-917236131073345772869093 : Int)/10^30,(-431476496928888928916859334 : Int)/10^30)
theorem v3970_pb_checked : Scalar.distance (sourceCoefficient 57 95 1 1) v3970_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3970_pg : Scalar.QComplex := ((-93086214265571732571742 : Int)/10^30,(197883406482020279775 : Int)/10^30)
theorem v3970_pg_checked : Scalar.distance (sourceCoefficient 57 95 1 2) v3970_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3970_mb : Scalar.QComplex := ((-1289580573414010008662248 : Int)/10^30,(-431475544736999337739099068 : Int)/10^30)
theorem v3970_mb_checked : Scalar.distance (sourceCoefficient 57 95 3 1) v3970_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3970_mg : Scalar.QComplex := ((-93086008840852455146146 : Int)/10^30,(278212543264713177129 : Int)/10^30)
theorem v3970_mg_checked : Scalar.distance (sourceCoefficient 57 95 3 2) v3970_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3970_upper : Scalar.QComplex := ((999992582155716118699689330685 : Int)/10^30,(-3851705277321822907448018189 : Int)/10^30)
theorem v3970_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 95 5) 1) 14) v3970_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3970 : Material (57 : Basis) (95 : Basis) where
  plus := ![v3970_pa,v3970_pb,v3970_pg]
  minus := ![(Primitive.Addresses.material3970 1).one,v3970_mb,v3970_mg]
  upper := v3970_upper
  lower := (Primitive.Addresses.material3970 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3970_pa_checked.trans (by decide +kernel)
    · exact v3970_pb_checked.trans (by decide +kernel)
    · exact v3970_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 95 Primitive.Addresses.material3970
    · exact v3970_mb_checked.trans (by decide +kernel)
    · exact v3970_mg_checked.trans (by decide +kernel)
  upper_error := v3970_upper_checked
  lower_error := reuse_lower_error 57 95 Primitive.Addresses.material3970

def v3971_pa : Scalar.QComplex := ((999997695048754896375257615576 : Int)/10^30,(-2147067110596920112027274231 : Int)/10^30)
theorem v3971_pa_checked : Scalar.distance (sourceCoefficient 57 96 1 0) v3971_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3971_pb : Scalar.QComplex := ((-926411083299913562762265 : Int)/10^30,(-431476474766537058626875308 : Int)/10^30)
theorem v3971_pb_checked : Scalar.distance (sourceCoefficient 57 96 1 1) v3971_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3971_pg : Scalar.QComplex := ((-93086209760503888021672 : Int)/10^30,(199862800100913848255 : Int)/10^30)
theorem v3971_pg_checked : Scalar.distance (sourceCoefficient 57 96 1 2) v3971_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3971_mb : Scalar.QComplex := ((-1298755503099212259787561 : Int)/10^30,(-431475514657085172486252997 : Int)/10^30)
theorem v3971_mb_checked : Scalar.distance (sourceCoefficient 57 96 3 1) v3971_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3971_mg : Scalar.QComplex := ((-93086002627658743512821 : Int)/10^30,(280191932258917389414 : Int)/10^30)
theorem v3971_mg_checked : Scalar.distance (sourceCoefficient 57 96 3 2) v3971_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3971_upper : Scalar.QComplex := ((999992500026603618639069890575 : Int)/10^30,(-3872969215364585806153826033 : Int)/10^30)
theorem v3971_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 96 5) 1) 14) v3971_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3971 : Material (57 : Basis) (96 : Basis) where
  plus := ![v3971_pa,v3971_pb,v3971_pg]
  minus := ![(Primitive.Addresses.material3971 1).one,v3971_mb,v3971_mg]
  upper := v3971_upper
  lower := (Primitive.Addresses.material3971 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3971_pa_checked.trans (by decide +kernel)
    · exact v3971_pb_checked.trans (by decide +kernel)
    · exact v3971_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 96 Primitive.Addresses.material3971
    · exact v3971_mb_checked.trans (by decide +kernel)
    · exact v3971_mg_checked.trans (by decide +kernel)
  upper_error := v3971_upper_checked
  lower_error := reuse_lower_error 57 96 Primitive.Addresses.material3971

def v3972_pa : Scalar.QComplex := ((999997535288202356108600292320 : Int)/10^30,(-2220229159452586181269016217 : Int)/10^30)
theorem v3972_pa_checked : Scalar.distance (sourceCoefficient 57 97 1 0) v3972_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3972_pb : Scalar.QComplex := ((-957978838325447300354557 : Int)/10^30,(-431476396526518338471602242 : Int)/10^30)
theorem v3972_pb_checked : Scalar.distance (sourceCoefficient 57 97 1 1) v3972_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3972_pg : Scalar.QComplex := ((-93086193885031411057146 : Int)/10^30,(206673191395856847562 : Int)/10^30)
theorem v3972_pg_checked : Scalar.distance (sourceCoefficient 57 97 1 2) v3972_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3972_mb : Scalar.QComplex := ((-1330323178853015727836840 : Int)/10^30,(-431475409175544756538257912 : Int)/10^30)
theorem v3972_mb_checked : Scalar.distance (sourceCoefficient 57 97 3 1) v3972_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3972_mg : Scalar.QComplex := ((-93085980875131218814057 : Int)/10^30,(287002307318222716473 : Int)/10^30)
theorem v3972_mg_checked : Scalar.distance (sourceCoefficient 57 97 3 2) v3972_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3972_upper : Scalar.QComplex := ((999992213995229907294145827264 : Int)/10^30,(-3946130879521754002460684616 : Int)/10^30)
theorem v3972_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 97 5) 1) 14) v3972_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3972 : Material (57 : Basis) (97 : Basis) where
  plus := ![v3972_pa,v3972_pb,v3972_pg]
  minus := ![(Primitive.Addresses.material3972 1).one,v3972_mb,v3972_mg]
  upper := v3972_upper
  lower := (Primitive.Addresses.material3972 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3972_pa_checked.trans (by decide +kernel)
    · exact v3972_pb_checked.trans (by decide +kernel)
    · exact v3972_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 97 Primitive.Addresses.material3972
    · exact v3972_mb_checked.trans (by decide +kernel)
    · exact v3972_mg_checked.trans (by decide +kernel)
  upper_error := v3972_upper_checked
  lower_error := reuse_lower_error 57 97 Primitive.Addresses.material3972

def v3973_pa : Scalar.QComplex := ((999999116182174239050489305852 : Int)/10^30,(-1329524302293098322203620971 : Int)/10^30)
theorem v3973_pa_checked : Scalar.distance (sourceCoefficient 58 59 1 0) v3973_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3973_pb : Scalar.QComplex := ((-573659850034046840430349 : Int)/10^30,(-431477139630938638752062835 : Int)/10^30)
theorem v3973_pb_checked : Scalar.distance (sourceCoefficient 58 59 1 1) v3973_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3973_pg : Scalar.QComplex := ((-93086347623136396752464 : Int)/10^30,(123760670758550173790 : Int)/10^30)
theorem v3973_pg_checked : Scalar.distance (sourceCoefficient 58 59 1 2) v3973_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3973_mb : Scalar.QComplex := ((-946004974926785392706250 : Int)/10^30,(-431476483929666175870869887 : Int)/10^30)
theorem v3973_mb_checked : Scalar.distance (sourceCoefficient 58 59 3 1) v3973_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3973_mg : Scalar.QComplex := ((-93086206162950029474419 : Int)/10^30,(204089950222097260800 : Int)/10^30)
theorem v3973_mg_checked : Scalar.distance (sourceCoefficient 58 59 3 2) v3973_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3973_upper : Scalar.QComplex := ((999995332162626578211396718583 : Int)/10^30,(-3055430077442099229251162593 : Int)/10^30)
theorem v3973_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 59 5) 1) 14) v3973_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3973 : Material (58 : Basis) (59 : Basis) where
  plus := ![v3973_pa,v3973_pb,v3973_pg]
  minus := ![(Primitive.Addresses.material3973 1).one,v3973_mb,v3973_mg]
  upper := v3973_upper
  lower := (Primitive.Addresses.material3973 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3973_pa_checked.trans (by decide +kernel)
    · exact v3973_pb_checked.trans (by decide +kernel)
    · exact v3973_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 59 Primitive.Addresses.material3973
    · exact v3973_mb_checked.trans (by decide +kernel)
    · exact v3973_mg_checked.trans (by decide +kernel)
  upper_error := v3973_upper_checked
  lower_error := reuse_lower_error 58 59 Primitive.Addresses.material3973

def v3974_pa : Scalar.QComplex := ((999999089035473327828210082602 : Int)/10^30,(-1349788214309183663047309832 : Int)/10^30)
theorem v3974_pa_checked : Scalar.distance (sourceCoefficient 58 60 1 0) v3974_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3974_pb : Scalar.QComplex := ((-582403272447111562488054 : Int)/10^30,(-431477127837022635667625144 : Int)/10^30)
theorem v3974_pb_checked : Scalar.distance (sourceCoefficient 58 60 1 1) v3974_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3974_pg : Scalar.QComplex := ((-93086345087439191992342 : Int)/10^30,(125646965972071882490 : Int)/10^30)
theorem v3974_pg_checked : Scalar.distance (sourceCoefficient 58 60 1 2) v3974_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3974_mb : Scalar.QComplex := ((-954748383906656023831976 : Int)/10^30,(-431476464590574810852858493 : Int)/10^30)
theorem v3974_mb_checked : Scalar.distance (sourceCoefficient 58 60 3 1) v3974_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3974_mg : Scalar.QComplex := ((-93086201999465955183736 : Int)/10^30,(205976242545072569410 : Int)/10^30)
theorem v3974_mg_checked : Scalar.distance (sourceCoefficient 58 60 3 2) v3974_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3974_upper : Scalar.QComplex := ((999995270042292286785822009488 : Int)/10^30,(-3075693912424724945151984726 : Int)/10^30)
theorem v3974_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 60 5) 1) 14) v3974_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3974 : Material (58 : Basis) (60 : Basis) where
  plus := ![v3974_pa,v3974_pb,v3974_pg]
  minus := ![(Primitive.Addresses.material3974 1).one,v3974_mb,v3974_mg]
  upper := v3974_upper
  lower := (Primitive.Addresses.material3974 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3974_pa_checked.trans (by decide +kernel)
    · exact v3974_pb_checked.trans (by decide +kernel)
    · exact v3974_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 60 Primitive.Addresses.material3974
    · exact v3974_mb_checked.trans (by decide +kernel)
    · exact v3974_mg_checked.trans (by decide +kernel)
  upper_error := v3974_upper_checked
  lower_error := reuse_lower_error 58 60 Primitive.Addresses.material3974

def v3975_pa : Scalar.QComplex := ((999999081109445318788164064827 : Int)/10^30,(-1355647544534556441183445471 : Int)/10^30)
theorem v3975_pa_checked : Scalar.distance (sourceCoefficient 58 61 1 0) v3975_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3975_pb : Scalar.QComplex := ((-584931441680311423415208 : Int)/10^30,(-431477124382770726467535992 : Int)/10^30)
theorem v3975_pb_checked : Scalar.distance (sourceCoefficient 58 61 1 1) v3975_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3975_pg : Scalar.QComplex := ((-93086344345928336698406 : Int)/10^30,(126192390099251275850 : Int)/10^30)
theorem v3975_pg_checked : Scalar.distance (sourceCoefficient 58 61 1 2) v3975_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3975_mb : Scalar.QComplex := ((-957276549217639112288067 : Int)/10^30,(-431476458954628004092556092 : Int)/10^30)
theorem v3975_mb_checked : Scalar.distance (sourceCoefficient 58 61 3 1) v3975_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3975_mg : Scalar.QComplex := ((-93086200787278919223157 : Int)/10^30,(206521665829275161398 : Int)/10^30)
theorem v3975_mg_checked : Scalar.distance (sourceCoefficient 58 61 3 2) v3975_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3975_upper : Scalar.QComplex := ((999995252003603667925795348900 : Int)/10^30,(-3081553220243708337914043309 : Int)/10^30)
theorem v3975_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 61 5) 1) 14) v3975_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3975 : Material (58 : Basis) (61 : Basis) where
  plus := ![v3975_pa,v3975_pb,v3975_pg]
  minus := ![(Primitive.Addresses.material3975 1).one,v3975_mb,v3975_mg]
  upper := v3975_upper
  lower := (Primitive.Addresses.material3975 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3975_pa_checked.trans (by decide +kernel)
    · exact v3975_pb_checked.trans (by decide +kernel)
    · exact v3975_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 61 Primitive.Addresses.material3975
    · exact v3975_mb_checked.trans (by decide +kernel)
    · exact v3975_mg_checked.trans (by decide +kernel)
  upper_error := v3975_upper_checked
  lower_error := reuse_lower_error 58 61 Primitive.Addresses.material3975

def v3976_pa : Scalar.QComplex := ((999999069532086699386046548316 : Int)/10^30,(-1364160899905392474192586731 : Int)/10^30)
theorem v3976_pa_checked : Scalar.distance (sourceCoefficient 58 62 1 0) v3976_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3976_pb : Scalar.QComplex := ((-588604763069863082761044 : Int)/10^30,(-431477119328693860852822382 : Int)/10^30)
theorem v3976_pb_checked : Scalar.distance (sourceCoefficient 58 62 1 1) v3976_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3976_pg : Scalar.QComplex := ((-93086343261900681393319 : Int)/10^30,(126984867948401801321 : Int)/10^30)
theorem v3976_pg_checked : Scalar.distance (sourceCoefficient 58 62 1 2) v3976_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3976_mb : Scalar.QComplex := ((-960949864878004631369535 : Int)/10^30,(-431476450730642101412514758 : Int)/10^30)
theorem v3976_mb_checked : Scalar.distance (sourceCoefficient 58 62 3 1) v3976_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3976_mg : Scalar.QComplex := ((-93086199019378975611585 : Int)/10^30,(207314142447882921868 : Int)/10^30)
theorem v3976_mg_checked : Scalar.distance (sourceCoefficient 58 62 3 2) v3976_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3976_upper : Scalar.QComplex := ((999995225732983247142542389347 : Int)/10^30,(-3090066542953430907715864422 : Int)/10^30)
theorem v3976_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 62 5) 1) 14) v3976_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3976 : Material (58 : Basis) (62 : Basis) where
  plus := ![v3976_pa,v3976_pb,v3976_pg]
  minus := ![(Primitive.Addresses.material3976 1).one,v3976_mb,v3976_mg]
  upper := v3976_upper
  lower := (Primitive.Addresses.material3976 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3976_pa_checked.trans (by decide +kernel)
    · exact v3976_pb_checked.trans (by decide +kernel)
    · exact v3976_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 62 Primitive.Addresses.material3976
    · exact v3976_mb_checked.trans (by decide +kernel)
    · exact v3976_mg_checked.trans (by decide +kernel)
  upper_error := v3976_upper_checked
  lower_error := reuse_lower_error 58 62 Primitive.Addresses.material3976

def v3977_pa : Scalar.QComplex := ((999999035400080024981555475570 : Int)/10^30,(-1388956050239542775014188475 : Int)/10^30)
theorem v3977_pa_checked : Scalar.distance (sourceCoefficient 58 63 1 0) v3977_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3977_pb : Scalar.QComplex := ((-599303312744039263001079 : Int)/10^30,(-431477104371124288922755326 : Int)/10^30)
theorem v3977_pb_checked : Scalar.distance (sourceCoefficient 58 63 1 1) v3977_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3977_pg : Scalar.QComplex := ((-93086340059823523482434 : Int)/10^30,(129292959936726213386 : Int)/10^30)
theorem v3977_pg_checked : Scalar.distance (sourceCoefficient 58 63 1 2) v3977_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3977_mb : Scalar.QComplex := ((-971648397660912943389445 : Int)/10^30,(-431476426540711574845555978 : Int)/10^30)
theorem v3977_mb_checked : Scalar.distance (sourceCoefficient 58 63 3 1) v3977_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3977_mg : Scalar.QComplex := ((-93086193825523576660653 : Int)/10^30,(209622230813550830590 : Int)/10^30)
theorem v3977_mg_checked : Scalar.distance (sourceCoefficient 58 63 3 2) v3977_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3977_upper : Scalar.QComplex := ((999995148806847330076124051076 : Int)/10^30,(-3114861597449370340216206283 : Int)/10^30)
theorem v3977_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 63 5) 1) 14) v3977_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3977 : Material (58 : Basis) (63 : Basis) where
  plus := ![v3977_pa,v3977_pb,v3977_pg]
  minus := ![(Primitive.Addresses.material3977 1).one,v3977_mb,v3977_mg]
  upper := v3977_upper
  lower := (Primitive.Addresses.material3977 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3977_pa_checked.trans (by decide +kernel)
    · exact v3977_pb_checked.trans (by decide +kernel)
    · exact v3977_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 63 Primitive.Addresses.material3977
    · exact v3977_mb_checked.trans (by decide +kernel)
    · exact v3977_mg_checked.trans (by decide +kernel)
  upper_error := v3977_upper_checked
  lower_error := reuse_lower_error 58 63 Primitive.Addresses.material3977

def v3978_pa : Scalar.QComplex := ((999998985551367943962689746178 : Int)/10^30,(-1424393286633311656785354651 : Int)/10^30)
theorem v3978_pa_checked : Scalar.distance (sourceCoefficient 58 64 1 0) v3978_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3978_pb : Scalar.QComplex := ((-614593682951602455430594 : Int)/10^30,(-431477082379776149119490383 : Int)/10^30)
theorem v3978_pb_checked : Scalar.distance (sourceCoefficient 58 64 1 1) v3978_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3978_pg : Scalar.QComplex := ((-93086335367510997543246 : Int)/10^30,(132591685682233831054 : Int)/10^30)
theorem v3978_pg_checked : Scalar.distance (sourceCoefficient 58 64 1 2) v3978_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3978_mb : Scalar.QComplex := ((-986938743197629512005693 : Int)/10^30,(-431476391354470787009381076 : Int)/10^30)
theorem v3978_mb_checked : Scalar.distance (sourceCoefficient 58 64 3 1) v3978_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3978_mg : Scalar.QComplex := ((-93086186286561048603228 : Int)/10^30,(212920951281537718016 : Int)/10^30)
theorem v3978_mg_checked : Scalar.distance (sourceCoefficient 58 64 3 2) v3978_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3978_upper : Scalar.QComplex := ((999995037796754318185855198036 : Int)/10^30,(-3150298695029183551668316940 : Int)/10^30)
theorem v3978_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 64 5) 1) 14) v3978_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3978 : Material (58 : Basis) (64 : Basis) where
  plus := ![v3978_pa,v3978_pb,v3978_pg]
  minus := ![(Primitive.Addresses.material3978 1).one,v3978_mb,v3978_mg]
  upper := v3978_upper
  lower := (Primitive.Addresses.material3978 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3978_pa_checked.trans (by decide +kernel)
    · exact v3978_pb_checked.trans (by decide +kernel)
    · exact v3978_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 64 Primitive.Addresses.material3978
    · exact v3978_mb_checked.trans (by decide +kernel)
    · exact v3978_mg_checked.trans (by decide +kernel)
  upper_error := v3978_upper_checked
  lower_error := reuse_lower_error 58 64 Primitive.Addresses.material3978

def v3979_pa : Scalar.QComplex := ((999998933673959306042324984257 : Int)/10^30,(-1460359868093029420324686487 : Int)/10^30)
theorem v3979_pa_checked : Scalar.distance (sourceCoefficient 58 65 1 0) v3979_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3979_pb : Scalar.QComplex := ((-630112453340788383349607 : Int)/10^30,(-431477059321196547561204142 : Int)/10^30)
theorem v3979_pb_checked : Scalar.distance (sourceCoefficient 58 65 1 1) v3979_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3979_pg : Scalar.QComplex := ((-93086330465654810136572 : Int)/10^30,(135939686236115201764 : Int)/10^30)
theorem v3979_pg_checked : Scalar.distance (sourceCoefficient 58 65 1 2) v3979_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3979_mb : Scalar.QComplex := ((-1002457487909952304915475 : Int)/10^30,(-431476354903899864819129970 : Int)/10^30)
theorem v3979_mb_checked : Scalar.distance (sourceCoefficient 58 65 3 1) v3979_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3979_mg : Scalar.QComplex := ((-93086178495532996729435 : Int)/10^30,(216268946358724353007 : Int)/10^30)
theorem v3979_mg_checked : Scalar.distance (sourceCoefficient 58 65 3 2) v3979_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3979_upper : Scalar.QComplex := ((999994923844366208880788542575 : Int)/10^30,(-3186265133385202135099172289 : Int)/10^30)
theorem v3979_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 65 5) 1) 14) v3979_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3979 : Material (58 : Basis) (65 : Basis) where
  plus := ![v3979_pa,v3979_pb,v3979_pg]
  minus := ![(Primitive.Addresses.material3979 1).one,v3979_mb,v3979_mg]
  upper := v3979_upper
  lower := (Primitive.Addresses.material3979 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3979_pa_checked.trans (by decide +kernel)
    · exact v3979_pb_checked.trans (by decide +kernel)
    · exact v3979_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 65 Primitive.Addresses.material3979
    · exact v3979_mb_checked.trans (by decide +kernel)
    · exact v3979_mg_checked.trans (by decide +kernel)
  upper_error := v3979_upper_checked
  lower_error := reuse_lower_error 58 65 Primitive.Addresses.material3979

def v3980_pa : Scalar.QComplex := ((999998907835121901152474645563 : Int)/10^30,(-1477947415632090104720966004 : Int)/10^30)
theorem v3980_pa_checked : Scalar.distance (sourceCoefficient 58 66 1 0) v3980_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3980_pb : Scalar.QComplex := ((-637701084137888492780847 : Int)/10^30,(-431477047774686421782034094 : Int)/10^30)
theorem v3980_pb_checked : Scalar.distance (sourceCoefficient 58 66 1 1) v3980_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3980_pg : Scalar.QComplex := ((-93086328017517297855278 : Int)/10^30,(137576848180772334485 : Int)/10^30)
theorem v3980_pg_checked : Scalar.distance (sourceCoefficient 58 66 1 2) v3980_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3980_mb : Scalar.QComplex := ((-1010046105917340147989797 : Int)/10^30,(-431476336808747439679646378 : Int)/10^30)
theorem v3980_mb_checked : Scalar.distance (sourceCoefficient 58 66 3 1) v3980_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3980_mg : Scalar.QComplex := ((-93086174634599372799332 : Int)/10^30,(217906105581158858657 : Int)/10^30)
theorem v3980_mg_checked : Scalar.distance (sourceCoefficient 58 66 3 2) v3980_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3980_upper : Scalar.QComplex := ((999994867651055765334416849354 : Int)/10^30,(-3203852610134187458704105788 : Int)/10^30)
theorem v3980_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 66 5) 1) 14) v3980_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3980 : Material (58 : Basis) (66 : Basis) where
  plus := ![v3980_pa,v3980_pb,v3980_pg]
  minus := ![(Primitive.Addresses.material3980 1).one,v3980_mb,v3980_mg]
  upper := v3980_upper
  lower := (Primitive.Addresses.material3980 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3980_pa_checked.trans (by decide +kernel)
    · exact v3980_pb_checked.trans (by decide +kernel)
    · exact v3980_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 66 Primitive.Addresses.material3980
    · exact v3980_mb_checked.trans (by decide +kernel)
    · exact v3980_mg_checked.trans (by decide +kernel)
  upper_error := v3980_upper_checked
  lower_error := reuse_lower_error 58 66 Primitive.Addresses.material3980

def v3981_pa : Scalar.QComplex := ((999998863774688218107501371894 : Int)/10^30,(-1507464537744031265341737247 : Int)/10^30)
theorem v3981_pa_checked : Scalar.distance (sourceCoefficient 58 67 1 0) v3981_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3981_pb : Scalar.QComplex := ((-650437057598609388173929 : Int)/10^30,(-431477027996266836618295384 : Int)/10^30)
theorem v3981_pb_checked : Scalar.distance (sourceCoefficient 58 67 1 1) v3981_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3981_pg : Scalar.QComplex := ((-93086323833317100622871 : Int)/10^30,(140324491567921745970 : Int)/10^30)
theorem v3981_pg_checked : Scalar.distance (sourceCoefficient 58 67 1 2) v3981_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3981_mb : Scalar.QComplex := ((-1022782057567990746169096 : Int)/10^30,(-431476306039763729274684864 : Int)/10^30)
theorem v3981_mb_checked : Scalar.distance (sourceCoefficient 58 67 3 1) v3981_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3981_mg : Scalar.QComplex := ((-93086168079308239690311 : Int)/10^30,(220653744334458742770 : Int)/10^30)
theorem v3981_mg_checked : Scalar.distance (sourceCoefficient 58 67 3 2) v3981_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3981_upper : Scalar.QComplex := ((999994772646812712319654361139 : Int)/10^30,(-3233369612239531152702290295 : Int)/10^30)
theorem v3981_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 67 5) 1) 14) v3981_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3981 : Material (58 : Basis) (67 : Basis) where
  plus := ![v3981_pa,v3981_pb,v3981_pg]
  minus := ![(Primitive.Addresses.material3981 1).one,v3981_mb,v3981_mg]
  upper := v3981_upper
  lower := (Primitive.Addresses.material3981 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3981_pa_checked.trans (by decide +kernel)
    · exact v3981_pb_checked.trans (by decide +kernel)
    · exact v3981_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 67 Primitive.Addresses.material3981
    · exact v3981_mb_checked.trans (by decide +kernel)
    · exact v3981_mg_checked.trans (by decide +kernel)
  upper_error := v3981_upper_checked
  lower_error := reuse_lower_error 58 67 Primitive.Addresses.material3981

def v3982_pa : Scalar.QComplex := ((999998788462519752203141506105 : Int)/10^30,(-1556622463114459771480866290 : Int)/10^30)
theorem v3982_pa_checked : Scalar.distance (sourceCoefficient 58 68 1 0) v3982_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3982_pb : Scalar.QComplex := ((-671647594817681980758399 : Int)/10^30,(-431476993944716434896124697 : Int)/10^30)
theorem v3982_pb_checked : Scalar.distance (sourceCoefficient 58 68 1 1) v3982_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3982_pg : Scalar.QComplex := ((-93086316654926847415835 : Int)/10^30,(144900427065943083144 : Int)/10^30)
theorem v3982_pg_checked : Scalar.distance (sourceCoefficient 58 68 1 2) v3982_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3982_mb : Scalar.QComplex := ((-1043992557504456590867133 : Int)/10^30,(-431476253684487673575735768 : Int)/10^30)
theorem v3982_mb_checked : Scalar.distance (sourceCoefficient 58 68 3 1) v3982_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3982_mg : Scalar.QComplex := ((-93086156952094417017940 : Int)/10^30,(225229671934022677625 : Int)/10^30)
theorem v3982_mg_checked : Scalar.distance (sourceCoefficient 58 68 3 2) v3982_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3982_upper : Scalar.QComplex := ((999994612492636797837173473154 : Int)/10^30,(-3282527334413033809539922684 : Int)/10^30)
theorem v3982_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 68 5) 1) 14) v3982_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3982 : Material (58 : Basis) (68 : Basis) where
  plus := ![v3982_pa,v3982_pb,v3982_pg]
  minus := ![(Primitive.Addresses.material3982 1).one,v3982_mb,v3982_mg]
  upper := v3982_upper
  lower := (Primitive.Addresses.material3982 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3982_pa_checked.trans (by decide +kernel)
    · exact v3982_pb_checked.trans (by decide +kernel)
    · exact v3982_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 68 Primitive.Addresses.material3982
    · exact v3982_mb_checked.trans (by decide +kernel)
    · exact v3982_mg_checked.trans (by decide +kernel)
  upper_error := v3982_upper_checked
  lower_error := reuse_lower_error 58 68 Primitive.Addresses.material3982

def v3983_pa : Scalar.QComplex := ((999998754550344438052304831761 : Int)/10^30,(-1578257824304714432662136316 : Int)/10^30)
theorem v3983_pa_checked : Scalar.distance (sourceCoefficient 58 69 1 0) v3983_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3983_pb : Scalar.QComplex := ((-680982765482171913924080 : Int)/10^30,(-431476978517385723294071404 : Int)/10^30)
theorem v3983_pb_checked : Scalar.distance (sourceCoefficient 58 69 1 1) v3983_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3983_pg : Scalar.QComplex := ((-93086313412408502780761 : Int)/10^30,(146914385453285361267 : Int)/10^30)
theorem v3983_pg_checked : Scalar.distance (sourceCoefficient 58 69 1 2) v3983_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3983_mb : Scalar.QComplex := ((-1053327711379944264337186 : Int)/10^30,(-431476230201330863298402328 : Int)/10^30)
theorem v3983_mb_checked : Scalar.distance (sourceCoefficient 58 69 3 1) v3983_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3983_mg : Scalar.QComplex := ((-93086151971621896762875 : Int)/10^30,(227243626773328911881 : Int)/10^30)
theorem v3983_mg_checked : Scalar.distance (sourceCoefficient 58 69 3 2) v3983_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3983_upper : Scalar.QComplex := ((999994541239841322143378298129 : Int)/10^30,(-3304162604850621342178622024 : Int)/10^30)
theorem v3983_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 69 5) 1) 14) v3983_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3983 : Material (58 : Basis) (69 : Basis) where
  plus := ![v3983_pa,v3983_pb,v3983_pg]
  minus := ![(Primitive.Addresses.material3983 1).one,v3983_mb,v3983_mg]
  upper := v3983_upper
  lower := (Primitive.Addresses.material3983 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3983_pa_checked.trans (by decide +kernel)
    · exact v3983_pb_checked.trans (by decide +kernel)
    · exact v3983_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 69 Primitive.Addresses.material3983
    · exact v3983_mb_checked.trans (by decide +kernel)
    · exact v3983_mg_checked.trans (by decide +kernel)
  upper_error := v3983_upper_checked
  lower_error := reuse_lower_error 58 69 Primitive.Addresses.material3983

def v3984_pa : Scalar.QComplex := ((999998731987358180130738456791 : Int)/10^30,(-1592489772583698167620525990 : Int)/10^30)
theorem v3984_pa_checked : Scalar.distance (sourceCoefficient 58 70 1 0) v3984_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3984_pb : Scalar.QComplex := ((-687123530280763161293622 : Int)/10^30,(-431476968222303884075667857 : Int)/10^30)
theorem v3984_pb_checked : Scalar.distance (sourceCoefficient 58 70 1 1) v3984_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3984_pg : Scalar.QComplex := ((-93086311251730434601400 : Int)/10^30,(148239186605086172056 : Int)/10^30)
theorem v3984_pg_checked : Scalar.distance (sourceCoefficient 58 70 1 2) v3984_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3984_mb : Scalar.QComplex := ((-1059468465007856176403873 : Int)/10^30,(-431476214607049406005005257 : Int)/10^30)
theorem v3984_mb_checked : Scalar.distance (sourceCoefficient 58 70 3 1) v3984_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3984_mg : Scalar.QComplex := ((-93086148667700905927549 : Int)/10^30,(228568425567277847939 : Int)/10^30)
theorem v3984_mg_checked : Scalar.distance (sourceCoefficient 58 70 3 2) v3984_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3984_upper : Scalar.QComplex := ((999994494113837051875735904485 : Int)/10^30,(-3318394492991122534624483394 : Int)/10^30)
theorem v3984_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 70 5) 1) 14) v3984_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3984 : Material (58 : Basis) (70 : Basis) where
  plus := ![v3984_pa,v3984_pb,v3984_pg]
  minus := ![(Primitive.Addresses.material3984 1).one,v3984_mb,v3984_mg]
  upper := v3984_upper
  lower := (Primitive.Addresses.material3984 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3984_pa_checked.trans (by decide +kernel)
    · exact v3984_pb_checked.trans (by decide +kernel)
    · exact v3984_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 70 Primitive.Addresses.material3984
    · exact v3984_mb_checked.trans (by decide +kernel)
    · exact v3984_mg_checked.trans (by decide +kernel)
  upper_error := v3984_upper_checked
  lower_error := reuse_lower_error 58 70 Primitive.Addresses.material3984

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
