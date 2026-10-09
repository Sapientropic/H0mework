import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B168
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B169

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4049_pa : Scalar.QComplex := ((999997481812377178274813209465 : Int)/10^30,(-2244185577080145714269371792 : Int)/10^30)
theorem v4049_pa_checked : Scalar.distance (sourceCoefficient 59 97 1 0) v4049_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4049_pb : Scalar.QComplex := ((-968315499583346442144234 : Int)/10^30,(-431476376585170176652486667 : Int)/10^30)
theorem v4049_pb_checked : Scalar.distance (sourceCoefficient 59 97 1 1) v4049_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4049_pg : Scalar.QComplex := ((-93086189245033623736005 : Int)/10^30,(208903209386533681298 : Int)/10^30)
theorem v4049_pg_checked : Scalar.distance (sourceCoefficient 59 97 1 2) v4049_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4049_mb : Scalar.QComplex := ((-1340659819053618135885060 : Int)/10^30,(-431475380314130900168646349 : Int)/10^30)
theorem v4049_mb_checked : Scalar.distance (sourceCoefficient 59 97 3 1) v4049_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4049_mg : Scalar.QComplex := ((-93085974310730069503973 : Int)/10^30,(289232320474452822708 : Int)/10^30)
theorem v4049_mg_checked : Scalar.distance (sourceCoefficient 59 97 3 2) v4049_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4049_upper : Scalar.QComplex := ((999992119172880859482707640324 : Int)/10^30,(-3970087169174620629729518298 : Int)/10^30)
theorem v4049_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 97 5) 1) 14) v4049_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4049 : Material (59 : Basis) (97 : Basis) where
  plus := ![v4049_pa,v4049_pb,v4049_pg]
  minus := ![(Primitive.Addresses.material4049 1).one,v4049_mb,v4049_mg]
  upper := v4049_upper
  lower := (Primitive.Addresses.material4049 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4049_pa_checked.trans (by decide +kernel)
    · exact v4049_pb_checked.trans (by decide +kernel)
    · exact v4049_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 97 Primitive.Addresses.material4049
    · exact v4049_mb_checked.trans (by decide +kernel)
    · exact v4049_mg_checked.trans (by decide +kernel)
  upper_error := v4049_upper_checked
  lower_error := reuse_lower_error 59 97 Primitive.Addresses.material4049

def v4050_pa : Scalar.QComplex := ((999999029109943885878562550326 : Int)/10^30,(-1393477366016664733403784764 : Int)/10^30)
theorem v4050_pa_checked : Scalar.distance (sourceCoefficient 60 61 1 0) v4050_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4050_pb : Scalar.QComplex := ((-601254159455949273293715 : Int)/10^30,(-431477102080949199559650602 : Int)/10^30)
theorem v4050_pb_checked : Scalar.distance (sourceCoefficient 60 61 1 1) v4050_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4050_pg : Scalar.QComplex := ((-93086339520020585631847 : Int)/10^30,(129713833144361989271 : Int)/10^30)
theorem v4050_pg_checked : Scalar.distance (sourceCoefficient 60 61 1 2) v4050_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4050_mb : Scalar.QComplex := ((-973599241670115608275469 : Int)/10^30,(-431476422567044488715245533 : Int)/10^30)
theorem v4050_mb_checked : Scalar.distance (sourceCoefficient 60 61 3 1) v4050_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4050_mg : Scalar.QComplex := ((-93086192922526217039309 : Int)/10^30,(210043103398650652873 : Int)/10^30)
theorem v4050_mg_checked : Scalar.distance (sourceCoefficient 60 61 3 2) v4050_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4050_upper : Scalar.QComplex := ((999995134713339698642742742845 : Int)/10^30,(-3119382895636319220243547791 : Int)/10^30)
theorem v4050_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 61 5) 1) 14) v4050_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4050 : Material (60 : Basis) (61 : Basis) where
  plus := ![v4050_pa,v4050_pb,v4050_pg]
  minus := ![(Primitive.Addresses.material4050 1).one,v4050_mb,v4050_mg]
  upper := v4050_upper
  lower := (Primitive.Addresses.material4050 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4050_pa_checked.trans (by decide +kernel)
    · exact v4050_pb_checked.trans (by decide +kernel)
    · exact v4050_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 61 Primitive.Addresses.material4050
    · exact v4050_mb_checked.trans (by decide +kernel)
    · exact v4050_mg_checked.trans (by decide +kernel)
  upper_error := v4050_upper_checked
  lower_error := reuse_lower_error 60 61 Primitive.Addresses.material4050

def v4051_pa : Scalar.QComplex := ((999999017210526256672918458133 : Int)/10^30,(-1401990720943439219593359622 : Int)/10^30)
theorem v4051_pa_checked : Scalar.distance (sourceCoefficient 60 62 1 0) v4051_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4051_pb : Scalar.QComplex := ((-604927480717765883182269 : Int)/10^30,(-431477096934231519084845334 : Int)/10^30)
theorem v4051_pb_checked : Scalar.distance (sourceCoefficient 60 62 1 1) v4051_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4051_pg : Scalar.QComplex := ((-93086338411010160811409 : Int)/10^30,(130506310959065761392 : Int)/10^30)
theorem v4051_pg_checked : Scalar.distance (sourceCoefficient 60 62 1 2) v4051_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4051_mb : Scalar.QComplex := ((-977272557122801274624407 : Int)/10^30,(-431476414250417915899116516 : Int)/10^30)
theorem v4051_mb_checked : Scalar.distance (sourceCoefficient 60 62 3 1) v4051_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4051_mg : Scalar.QComplex := ((-93086191129643542940611 : Int)/10^30,(210835579961252667909 : Int)/10^30)
theorem v4051_mg_checked : Scalar.distance (sourceCoefficient 60 62 3 2) v4051_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4051_upper : Scalar.QComplex := ((999995108120661514134971462870 : Int)/10^30,(-3127896217346136270647565456 : Int)/10^30)
theorem v4051_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 62 5) 1) 14) v4051_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4051 : Material (60 : Basis) (62 : Basis) where
  plus := ![v4051_pa,v4051_pb,v4051_pg]
  minus := ![(Primitive.Addresses.material4051 1).one,v4051_mb,v4051_mg]
  upper := v4051_upper
  lower := (Primitive.Addresses.material4051 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4051_pa_checked.trans (by decide +kernel)
    · exact v4051_pb_checked.trans (by decide +kernel)
    · exact v4051_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 62 Primitive.Addresses.material4051
    · exact v4051_mb_checked.trans (by decide +kernel)
    · exact v4051_mg_checked.trans (by decide +kernel)
  upper_error := v4051_upper_checked
  lower_error := reuse_lower_error 60 62 Primitive.Addresses.material4051

def v4052_pa : Scalar.QComplex := ((999998982140522609959931048445 : Int)/10^30,(-1426785869968638435274325904 : Int)/10^30)
theorem v4052_pa_checked : Scalar.distance (sourceCoefficient 60 63 1 0) v4052_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4052_pb : Scalar.QComplex := ((-615626030015420086292017 : Int)/10^30,(-431477081706845543344917398 : Int)/10^30)
theorem v4052_pb_checked : Scalar.distance (sourceCoefficient 60 63 1 1) v4052_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4052_pg : Scalar.QComplex := ((-93086335136170678450226 : Int)/10^30,(132814402845852187346 : Int)/10^30)
theorem v4052_pg_checked : Scalar.distance (sourceCoefficient 60 63 1 2) v4052_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4052_mb : Scalar.QComplex := ((-987971089296348345302180 : Int)/10^30,(-431476389790671410908783555 : Int)/10^30)
theorem v4052_mb_checked : Scalar.distance (sourceCoefficient 60 63 3 1) v4052_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4052_mg : Scalar.QComplex := ((-93086185863025934254828 : Int)/10^30,(213143668162592019420 : Int)/10^30)
theorem v4052_mg_checked : Scalar.distance (sourceCoefficient 60 63 3 2) v4052_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4052_upper : Scalar.QComplex := ((999995030256532280927188014626 : Int)/10^30,(-3152691268914228887752294991 : Int)/10^30)
theorem v4052_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 63 5) 1) 14) v4052_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4052 : Material (60 : Basis) (63 : Basis) where
  plus := ![v4052_pa,v4052_pb,v4052_pg]
  minus := ![(Primitive.Addresses.material4052 1).one,v4052_mb,v4052_mg]
  upper := v4052_upper
  lower := (Primitive.Addresses.material4052 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4052_pa_checked.trans (by decide +kernel)
    · exact v4052_pb_checked.trans (by decide +kernel)
    · exact v4052_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 63 Primitive.Addresses.material4052
    · exact v4052_mb_checked.trans (by decide +kernel)
    · exact v4052_mg_checked.trans (by decide +kernel)
  upper_error := v4052_upper_checked
  lower_error := reuse_lower_error 60 63 Primitive.Addresses.material4052

def v4053_pa : Scalar.QComplex := ((999998930951224971788012700121 : Int)/10^30,(-1462223104451280575948107061 : Int)/10^30)
theorem v4053_pa_checked : Scalar.distance (sourceCoefficient 60 64 1 0) v4053_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4053_pb : Scalar.QComplex := ((-630916399673244463416671 : Int)/10^30,(-431477059329875717571817461 : Int)/10^30)
theorem v4053_pb_checked : Scalar.distance (sourceCoefficient 60 64 1 1) v4053_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4053_pg : Scalar.QComplex := ((-93086330339866216373800 : Int)/10^30,(136113128443109833984 : Int)/10^30)
theorem v4053_pg_checked : Scalar.distance (sourceCoefficient 60 64 1 2) v4053_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4053_mb : Scalar.QComplex := ((-1003261433950552156070501 : Int)/10^30,(-431476354218809555087189420 : Int)/10^30)
theorem v4053_mb_checked : Scalar.distance (sourceCoefficient 60 64 3 1) v4053_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4053_mg : Scalar.QComplex := ((-93086178220071636714163 : Int)/10^30,(216442388392588633753 : Int)/10^30)
theorem v4053_mg_checked : Scalar.distance (sourceCoefficient 60 64 3 2) v4053_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4053_upper : Scalar.QComplex := ((999994917905859006959956750953 : Int)/10^30,(-3188128362269189149831361232 : Int)/10^30)
theorem v4053_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 64 5) 1) 14) v4053_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4053 : Material (60 : Basis) (64 : Basis) where
  plus := ![v4053_pa,v4053_pb,v4053_pg]
  minus := ![(Primitive.Addresses.material4053 1).one,v4053_mb,v4053_mg]
  upper := v4053_upper
  lower := (Primitive.Addresses.material4053 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4053_pa_checked.trans (by decide +kernel)
    · exact v4053_pb_checked.trans (by decide +kernel)
    · exact v4053_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 64 Primitive.Addresses.material4053
    · exact v4053_mb_checked.trans (by decide +kernel)
    · exact v4053_mg_checked.trans (by decide +kernel)
  upper_error := v4053_upper_checked
  lower_error := reuse_lower_error 60 64 Primitive.Addresses.material4053

def v4054_pa : Scalar.QComplex := ((999998877713205729904636650248 : Int)/10^30,(-1498189683922747524954317319 : Int)/10^30)
theorem v4054_pa_checked : Scalar.distance (sourceCoefficient 60 65 1 0) v4054_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4054_pb : Scalar.QComplex := ((-646435169490506707220680 : Int)/10^30,(-431477035879914191974405730 : Int)/10^30)
theorem v4054_pb_checked : Scalar.distance (sourceCoefficient 60 65 1 1) v4054_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4054_pg : Scalar.QComplex := ((-93086325332464709443727 : Int)/10^30,(139461128842758563186 : Int)/10^30)
theorem v4054_pg_checked : Scalar.distance (sourceCoefficient 60 65 1 2) v4054_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4054_mb : Scalar.QComplex := ((-1018780177753206504560346 : Int)/10^30,(-431476317376857348131571086 : Int)/10^30)
theorem v4054_mb_checked : Scalar.distance (sourceCoefficient 60 65 3 1) v4054_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4054_mg : Scalar.QComplex := ((-93086170323498437712141 : Int)/10^30,(219790383224461827501 : Int)/10^30)
theorem v4054_mg_checked : Scalar.distance (sourceCoefficient 60 65 3 2) v4054_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4054_upper : Scalar.QComplex := ((999994802592865751702078040828 : Int)/10^30,(-3224094796288669411184750344 : Int)/10^30)
theorem v4054_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 65 5) 1) 14) v4054_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4054 : Material (60 : Basis) (65 : Basis) where
  plus := ![v4054_pa,v4054_pb,v4054_pg]
  minus := ![(Primitive.Addresses.material4054 1).one,v4054_mb,v4054_mg]
  upper := v4054_upper
  lower := (Primitive.Addresses.material4054 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4054_pa_checked.trans (by decide +kernel)
    · exact v4054_pb_checked.trans (by decide +kernel)
    · exact v4054_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 65 Primitive.Addresses.material4054
    · exact v4054_mb_checked.trans (by decide +kernel)
    · exact v4054_mg_checked.trans (by decide +kernel)
  upper_error := v4054_upper_checked
  lower_error := reuse_lower_error 60 65 Primitive.Addresses.material4054

def v4055_pa : Scalar.QComplex := ((999998851209033931362986726538 : Int)/10^30,(-1515777230471743926847372070 : Int)/10^30)
theorem v4055_pa_checked : Scalar.distance (sourceCoefficient 60 66 1 0) v4055_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4055_pb : Scalar.QComplex := ((-654023800002813164136964 : Int)/10^30,(-431477024142019511212087016 : Int)/10^30)
theorem v4055_pb_checked : Scalar.distance (sourceCoefficient 60 66 1 1) v4055_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4055_pg : Scalar.QComplex := ((-93086322832715861093528 : Int)/10^30,(141098290710614404854 : Int)/10^30)
theorem v4055_pg_checked : Scalar.distance (sourceCoefficient 60 66 1 2) v4055_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4055_mb : Scalar.QComplex := ((-1026368795310644549851327 : Int)/10^30,(-431476299090320685034250844 : Int)/10^30)
theorem v4055_mb_checked : Scalar.distance (sourceCoefficient 60 66 3 1) v4055_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4055_mg : Scalar.QComplex := ((-93086166410953563206446 : Int)/10^30,(221427542325556812155 : Int)/10^30)
theorem v4055_mg_checked : Scalar.distance (sourceCoefficient 60 66 3 2) v4055_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4055_upper : Scalar.QComplex := ((999994745734223614202464109410 : Int)/10^30,(-3241682270899285122092596739 : Int)/10^30)
theorem v4055_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 66 5) 1) 14) v4055_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4055 : Material (60 : Basis) (66 : Basis) where
  plus := ![v4055_pa,v4055_pb,v4055_pg]
  minus := ![(Primitive.Addresses.material4055 1).one,v4055_mb,v4055_mg]
  upper := v4055_upper
  lower := (Primitive.Addresses.material4055 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4055_pa_checked.trans (by decide +kernel)
    · exact v4055_pb_checked.trans (by decide +kernel)
    · exact v4055_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 66 Primitive.Addresses.material4055
    · exact v4055_mb_checked.trans (by decide +kernel)
    · exact v4055_mg_checked.trans (by decide +kernel)
  upper_error := v4055_upper_checked
  lower_error := reuse_lower_error 60 66 Primitive.Addresses.material4055

def v4056_pa : Scalar.QComplex := ((999998806031971764993131900671 : Int)/10^30,(-1545294350895764223821211661 : Int)/10^30)
theorem v4056_pa_checked : Scalar.distance (sourceCoefficient 60 67 1 0) v4056_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4056_pb : Scalar.QComplex := ((-666759772978000790562480 : Int)/10^30,(-431477004042399868979861810 : Int)/10^30)
theorem v4056_pb_checked : Scalar.distance (sourceCoefficient 60 67 1 1) v4056_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4056_pg : Scalar.QComplex := ((-93086318561896531523660 : Int)/10^30,(143845933966828377340 : Int)/10^30)
theorem v4056_pg_checked : Scalar.distance (sourceCoefficient 60 67 1 2) v4056_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4056_mb : Scalar.QComplex := ((-1039104746198580876912738 : Int)/10^30,(-431476268000137456151607161 : Int)/10^30)
theorem v4056_mb_checked : Scalar.distance (sourceCoefficient 60 67 3 1) v4056_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4056_mg : Scalar.QComplex := ((-93086159769043443003614 : Int)/10^30,(224175180873172895996 : Int)/10^30)
theorem v4056_mg_checked : Scalar.distance (sourceCoefficient 60 67 3 2) v4056_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4056_upper : Scalar.QComplex := ((999994649613356654148061255694 : Int)/10^30,(-3271199269389511003929650377 : Int)/10^30)
theorem v4056_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 67 5) 1) 14) v4056_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4056 : Material (60 : Basis) (67 : Basis) where
  plus := ![v4056_pa,v4056_pb,v4056_pg]
  minus := ![(Primitive.Addresses.material4056 1).one,v4056_mb,v4056_mg]
  upper := v4056_upper
  lower := (Primitive.Addresses.material4056 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4056_pa_checked.trans (by decide +kernel)
    · exact v4056_pb_checked.trans (by decide +kernel)
    · exact v4056_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 67 Primitive.Addresses.material4056
    · exact v4056_mb_checked.trans (by decide +kernel)
    · exact v4056_mg_checked.trans (by decide +kernel)
  upper_error := v4056_upper_checked
  lower_error := reuse_lower_error 60 67 Primitive.Addresses.material4056

def v4057_pa : Scalar.QComplex := ((999998728860166055296286088575 : Int)/10^30,(-1594452273381969243712827669 : Int)/10^30)
theorem v4057_pa_checked : Scalar.distance (sourceCoefficient 60 68 1 0) v4057_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4057_pb : Scalar.QComplex := ((-687970309367421658442877 : Int)/10^30,(-431476969455921694151259501 : Int)/10^30)
theorem v4057_pb_checked : Scalar.distance (sourceCoefficient 60 68 1 1) v4057_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4057_pg : Scalar.QComplex := ((-93086311239250452152453 : Int)/10^30,(148421869241114659068 : Int)/10^30)
theorem v4057_pg_checked : Scalar.distance (sourceCoefficient 60 68 1 2) v4057_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4057_mb : Scalar.QComplex := ((-1060315244843776729885660 : Int)/10^30,(-431476215109934542476356071 : Int)/10^30)
theorem v4057_mb_checked : Scalar.distance (sourceCoefficient 60 68 3 1) v4057_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4057_mg : Scalar.QComplex := ((-93086148497574040953385 : Int)/10^30,(228751108124515577773 : Int)/10^30)
theorem v4057_mg_checked : Scalar.distance (sourceCoefficient 60 68 3 2) v4057_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4057_upper : Scalar.QComplex := ((999994487599551243492403266966 : Int)/10^30,(-3320356985469229292418922991 : Int)/10^30)
theorem v4057_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 68 5) 1) 14) v4057_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4057 : Material (60 : Basis) (68 : Basis) where
  plus := ![v4057_pa,v4057_pb,v4057_pg]
  minus := ![(Primitive.Addresses.material4057 1).one,v4057_mb,v4057_mg]
  upper := v4057_upper
  lower := (Primitive.Addresses.material4057 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4057_pa_checked.trans (by decide +kernel)
    · exact v4057_pb_checked.trans (by decide +kernel)
    · exact v4057_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 68 Primitive.Addresses.material4057
    · exact v4057_mb_checked.trans (by decide +kernel)
    · exact v4057_mg_checked.trans (by decide +kernel)
  upper_error := v4057_upper_checked
  lower_error := reuse_lower_error 60 68 Primitive.Addresses.material4057

def v4058_pa : Scalar.QComplex := ((999998694129528140818431877799 : Int)/10^30,(-1616087633273849992838812958 : Int)/10^30)
theorem v4058_pa_checked : Scalar.distance (sourceCoefficient 60 69 1 0) v4058_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4058_pb : Scalar.QComplex := ((-697305479658432158084417 : Int)/10^30,(-431476953793158842784307345 : Int)/10^30)
theorem v4058_pb_checked : Scalar.distance (sourceCoefficient 60 69 1 1) v4058_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4058_pg : Scalar.QComplex := ((-93086307933242306546706 : Int)/10^30,(150435827527739444139 : Int)/10^30)
theorem v4058_pg_checked : Scalar.distance (sourceCoefficient 60 69 1 2) v4058_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4058_mb : Scalar.QComplex := ((-1069650398142617775747881 : Int)/10^30,(-431476191391346002392199425 : Int)/10^30)
theorem v4058_mb_checked : Scalar.distance (sourceCoefficient 60 69 3 1) v4058_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4058_mg : Scalar.QComplex := ((-93086143453611830282462 : Int)/10^30,(230765062808315517714 : Int)/10^30)
theorem v4058_mg_checked : Scalar.distance (sourceCoefficient 60 69 3 2) v4058_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4058_upper : Scalar.QComplex := ((999994415528296627351075018089 : Int)/10^30,(-3341992253195852648960419404 : Int)/10^30)
theorem v4058_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 69 5) 1) 14) v4058_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4058 : Material (60 : Basis) (69 : Basis) where
  plus := ![v4058_pa,v4058_pb,v4058_pg]
  minus := ![(Primitive.Addresses.material4058 1).one,v4058_mb,v4058_mg]
  upper := v4058_upper
  lower := (Primitive.Addresses.material4058 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4058_pa_checked.trans (by decide +kernel)
    · exact v4058_pb_checked.trans (by decide +kernel)
    · exact v4058_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 69 Primitive.Addresses.material4058
    · exact v4058_mb_checked.trans (by decide +kernel)
    · exact v4058_mg_checked.trans (by decide +kernel)
  upper_error := v4058_upper_checked
  lower_error := reuse_lower_error 60 69 Primitive.Addresses.material4058

def v4059_pa : Scalar.QComplex := ((999998671028149327775937696358 : Int)/10^30,(-1630319580689095522295149966 : Int)/10^30)
theorem v4059_pa_checked : Scalar.distance (sourceCoefficient 60 70 1 0) v4059_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4059_pb : Scalar.QComplex := ((-703446244208567662138604 : Int)/10^30,(-431476943343207482193005287 : Int)/10^30)
theorem v4059_pb_checked : Scalar.distance (sourceCoefficient 60 70 1 1) v4059_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4059_pg : Scalar.QComplex := ((-93086305730800037856479 : Int)/10^30,(151760628612538333633 : Int)/10^30)
theorem v4059_pg_checked : Scalar.distance (sourceCoefficient 60 70 1 2) v4059_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4059_mb : Scalar.QComplex := ((-1075791151388428615130146 : Int)/10^30,(-431476175642195295797020987 : Int)/10^30)
theorem v4059_mb_checked : Scalar.distance (sourceCoefficient 60 70 3 1) v4059_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4059_mg : Scalar.QComplex := ((-93086140107926712306629 : Int)/10^30,(232089861499221933375 : Int)/10^30)
theorem v4059_mg_checked : Scalar.distance (sourceCoefficient 60 70 3 2) v4059_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4059_upper : Scalar.QComplex := ((999994367863902094568756617058 : Int)/10^30,(-3356224139543400214793165181 : Int)/10^30)
theorem v4059_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 70 5) 1) 14) v4059_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4059 : Material (60 : Basis) (70 : Basis) where
  plus := ![v4059_pa,v4059_pb,v4059_pg]
  minus := ![(Primitive.Addresses.material4059 1).one,v4059_mb,v4059_mg]
  upper := v4059_upper
  lower := (Primitive.Addresses.material4059 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4059_pa_checked.trans (by decide +kernel)
    · exact v4059_pb_checked.trans (by decide +kernel)
    · exact v4059_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 70 Primitive.Addresses.material4059
    · exact v4059_mb_checked.trans (by decide +kernel)
    · exact v4059_mg_checked.trans (by decide +kernel)
  upper_error := v4059_upper_checked
  lower_error := reuse_lower_error 60 70 Primitive.Addresses.material4059

def v4060_pa : Scalar.QComplex := ((999998631128024834822892882992 : Int)/10^30,(-1654612364428559992749184591 : Int)/10^30)
theorem v4060_pa_checked : Scalar.distance (sourceCoefficient 60 71 1 0) v4060_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4060_pb : Scalar.QComplex := ((-713928032738468168866416 : Int)/10^30,(-431476925236778975513175339 : Int)/10^30)
theorem v4060_pb_checked : Scalar.distance (sourceCoefficient 60 71 1 1) v4060_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4060_pg : Scalar.QComplex := ((-93086301920590655330852 : Int)/10^30,(154021956953079742538 : Int)/10^30)
theorem v4060_pg_checked : Scalar.distance (sourceCoefficient 60 71 1 2) v4060_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4060_mb : Scalar.QComplex := ((-1086272920390447892778143 : Int)/10^30,(-431476148490462111894761994 : Int)/10^30)
theorem v4060_mb_checked : Scalar.distance (sourceCoefficient 60 71 3 1) v4060_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4060_mg : Scalar.QComplex := ((-93086134346294237056595 : Int)/10^30,(234351185709728361626 : Int)/10^30)
theorem v4060_mg_checked : Scalar.distance (sourceCoefficient 60 71 3 2) v4060_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4060_upper : Scalar.QComplex := ((999994286036696117973985084817 : Int)/10^30,(-3380516818237621772330956093 : Int)/10^30)
theorem v4060_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 71 5) 1) 14) v4060_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4060 : Material (60 : Basis) (71 : Basis) where
  plus := ![v4060_pa,v4060_pb,v4060_pg]
  minus := ![(Primitive.Addresses.material4060 1).one,v4060_mb,v4060_mg]
  upper := v4060_upper
  lower := (Primitive.Addresses.material4060 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4060_pa_checked.trans (by decide +kernel)
    · exact v4060_pb_checked.trans (by decide +kernel)
    · exact v4060_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 71 Primitive.Addresses.material4060
    · exact v4060_mb_checked.trans (by decide +kernel)
    · exact v4060_mg_checked.trans (by decide +kernel)
  upper_error := v4060_upper_checked
  lower_error := reuse_lower_error 60 71 Primitive.Addresses.material4060

def v4061_pa : Scalar.QComplex := ((999998587160604062630997519439 : Int)/10^30,(-1680974953935834016087092014 : Int)/10^30)
theorem v4061_pa_checked : Scalar.distance (sourceCoefficient 60 72 1 0) v4061_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4061_pb : Scalar.QComplex := ((-725302895585341756716753 : Int)/10^30,(-431476905203504314946480982 : Int)/10^30)
theorem v4061_pb_checked : Scalar.distance (sourceCoefficient 60 72 1 1) v4061_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4061_pg : Scalar.QComplex := ((-93086297713228517770850 : Int)/10^30,(156475956085946914161 : Int)/10^30)
theorem v4061_pg_checked : Scalar.distance (sourceCoefficient 60 72 1 2) v4061_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4061_mb : Scalar.QComplex := ((-1097647761714126418951885 : Int)/10^30,(-431476118641200578584858226 : Int)/10^30)
theorem v4061_mb_checked : Scalar.distance (sourceCoefficient 60 72 3 1) v4061_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4061_mg : Scalar.QComplex := ((-93086128021242938443534 : Int)/10^30,(236805180298095470625 : Int)/10^30)
theorem v4061_mg_checked : Scalar.distance (sourceCoefficient 60 72 3 2) v4061_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4061_upper : Scalar.QComplex := ((999994196569902935973571152717 : Int)/10^30,(-3406879292597135932335048262 : Int)/10^30)
theorem v4061_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 72 5) 1) 14) v4061_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4061 : Material (60 : Basis) (72 : Basis) where
  plus := ![v4061_pa,v4061_pb,v4061_pg]
  minus := ![(Primitive.Addresses.material4061 1).one,v4061_mb,v4061_mg]
  upper := v4061_upper
  lower := (Primitive.Addresses.material4061 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4061_pa_checked.trans (by decide +kernel)
    · exact v4061_pb_checked.trans (by decide +kernel)
    · exact v4061_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 72 Primitive.Addresses.material4061
    · exact v4061_mb_checked.trans (by decide +kernel)
    · exact v4061_mg_checked.trans (by decide +kernel)
  upper_error := v4061_upper_checked
  lower_error := reuse_lower_error 60 72 Primitive.Addresses.material4061

def v4062_pa : Scalar.QComplex := ((999998571231343667971212753882 : Int)/10^30,(-1690424583140041849072435148 : Int)/10^30)
theorem v4062_pa_checked : Scalar.distance (sourceCoefficient 60 73 1 0) v4062_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4062_pb : Scalar.QComplex := ((-729380197425435741816262 : Int)/10^30,(-431476897925263009777859134 : Int)/10^30)
theorem v4062_pb_checked : Scalar.distance (sourceCoefficient 60 73 1 1) v4062_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4062_pg : Scalar.QComplex := ((-93086296186730112088363 : Int)/10^30,(157355588252236110385 : Int)/10^30)
theorem v4062_pg_checked : Scalar.distance (sourceCoefficient 60 73 1 2) v4062_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4062_mb : Scalar.QComplex := ((-1101725055755260140544197 : Int)/10^30,(-431476107844434130295028685 : Int)/10^30)
theorem v4062_mb_checked : Scalar.distance (sourceCoefficient 60 73 3 1) v4062_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4062_mg : Scalar.QComplex := ((-93086125735662158800702 : Int)/10^30,(237684810819558036995 : Int)/10^30)
theorem v4062_mg_checked : Scalar.distance (sourceCoefficient 60 73 3 2) v4062_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4062_upper : Scalar.QComplex := ((999994164331463523278071613149 : Int)/10^30,(-3416328880234772747106386852 : Int)/10^30)
theorem v4062_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 73 5) 1) 14) v4062_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4062 : Material (60 : Basis) (73 : Basis) where
  plus := ![v4062_pa,v4062_pb,v4062_pg]
  minus := ![(Primitive.Addresses.material4062 1).one,v4062_mb,v4062_mg]
  upper := v4062_upper
  lower := (Primitive.Addresses.material4062 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4062_pa_checked.trans (by decide +kernel)
    · exact v4062_pb_checked.trans (by decide +kernel)
    · exact v4062_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 73 Primitive.Addresses.material4062
    · exact v4062_mb_checked.trans (by decide +kernel)
    · exact v4062_mg_checked.trans (by decide +kernel)
  upper_error := v4062_upper_checked
  lower_error := reuse_lower_error 60 73 Primitive.Addresses.material4062

def v4063_pa : Scalar.QComplex := ((999998553200238373686480097497 : Int)/10^30,(-1701057738591808293310602064 : Int)/10^30)
theorem v4063_pa_checked : Scalar.distance (sourceCoefficient 60 74 1 0) v4063_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4063_pb : Scalar.QComplex := ((-733968164108491249969477 : Int)/10^30,(-431476889674026323273702759 : Int)/10^30)
theorem v4063_pb_checked : Scalar.distance (sourceCoefficient 60 74 1 1) v4063_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4063_pg : Scalar.QComplex := ((-93086294457448673833227 : Int)/10^30,(158345390637752248741 : Int)/10^30)
theorem v4063_pg_checked : Scalar.distance (sourceCoefficient 60 74 1 2) v4063_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4063_mb : Scalar.QComplex := ((-1106313013609560333612027 : Int)/10^30,(-431476095633991902975264537 : Int)/10^30)
theorem v4063_mb_checked : Scalar.distance (sourceCoefficient 60 74 3 1) v4063_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4063_mg : Scalar.QComplex := ((-93086123152226484780242 : Int)/10^30,(238674611344233513750 : Int)/10^30)
theorem v4063_mg_checked : Scalar.distance (sourceCoefficient 60 74 3 2) v4063_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4063_upper : Scalar.QComplex := ((999994127948523406784999659611 : Int)/10^30,(-3426961988729651235278273230 : Int)/10^30)
theorem v4063_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 74 5) 1) 14) v4063_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4063 : Material (60 : Basis) (74 : Basis) where
  plus := ![v4063_pa,v4063_pb,v4063_pg]
  minus := ![(Primitive.Addresses.material4063 1).one,v4063_mb,v4063_mg]
  upper := v4063_upper
  lower := (Primitive.Addresses.material4063 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4063_pa_checked.trans (by decide +kernel)
    · exact v4063_pb_checked.trans (by decide +kernel)
    · exact v4063_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 74 Primitive.Addresses.material4063
    · exact v4063_mb_checked.trans (by decide +kernel)
    · exact v4063_mg_checked.trans (by decide +kernel)
  upper_error := v4063_upper_checked
  lower_error := reuse_lower_error 60 74 Primitive.Addresses.material4063

def v4064_pa : Scalar.QComplex := ((999998527889104776815841863403 : Int)/10^30,(-1715872845911339807244856692 : Int)/10^30)
theorem v4064_pa_checked : Scalar.distance (sourceCoefficient 60 75 1 0) v4064_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4064_pb : Scalar.QComplex := ((-740360548610335246034383 : Int)/10^30,(-431476878069180696461125015 : Int)/10^30)
theorem v4064_pb_checked : Scalar.distance (sourceCoefficient 60 75 1 1) v4064_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4064_pg : Scalar.QComplex := ((-93086292027579578751228 : Int)/10^30,(159724475948838311788 : Int)/10^30)
theorem v4064_pg_checked : Scalar.distance (sourceCoefficient 60 75 1 2) v4064_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4064_mb : Scalar.QComplex := ((-1112705385716768320141973 : Int)/10^30,(-431476078512810674396239618 : Int)/10^30)
theorem v4064_mb_checked : Scalar.distance (sourceCoefficient 60 75 3 1) v4064_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4064_mg : Scalar.QComplex := ((-93086119532269782679002 : Int)/10^30,(240053694044955496353 : Int)/10^30)
theorem v4064_mg_checked : Scalar.distance (sourceCoefficient 60 75 3 2) v4064_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4064_upper : Scalar.QComplex := ((999994077067896290400357079984 : Int)/10^30,(-3441777030299100321430024581 : Int)/10^30)
theorem v4064_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 75 5) 1) 14) v4064_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4064 : Material (60 : Basis) (75 : Basis) where
  plus := ![v4064_pa,v4064_pb,v4064_pg]
  minus := ![(Primitive.Addresses.material4064 1).one,v4064_mb,v4064_mg]
  upper := v4064_upper
  lower := (Primitive.Addresses.material4064 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4064_pa_checked.trans (by decide +kernel)
    · exact v4064_pb_checked.trans (by decide +kernel)
    · exact v4064_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 75 Primitive.Addresses.material4064
    · exact v4064_mb_checked.trans (by decide +kernel)
    · exact v4064_mg_checked.trans (by decide +kernel)
  upper_error := v4064_upper_checked
  lower_error := reuse_lower_error 60 75 Primitive.Addresses.material4064

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
