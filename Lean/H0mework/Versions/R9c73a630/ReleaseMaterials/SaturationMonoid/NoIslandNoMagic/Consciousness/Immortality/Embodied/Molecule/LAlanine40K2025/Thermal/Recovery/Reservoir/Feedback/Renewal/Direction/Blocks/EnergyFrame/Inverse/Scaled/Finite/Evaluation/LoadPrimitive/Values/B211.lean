import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B140
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B141

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3377_pa : Scalar.QComplex := ((999999439741331214181999780068 : Int)/10^30,(-1058544766971080940491821023 : Int)/10^30)
theorem v3377_pa_checked : Scalar.distance (sourceCoefficient 45 48 1 0) v3377_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3377_pb : Scalar.QComplex := ((-456738271747454891365987 : Int)/10^30,(-431477279097783018667908445 : Int)/10^30)
theorem v3377_pb_checked : Scalar.distance (sourceCoefficient 45 48 1 1) v3377_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3377_pg : Scalar.QComplex := ((-93086377726822557452209 : Int)/10^30,(98536153224755436209 : Int)/10^30)
theorem v3377_pg_checked : Scalar.distance (sourceCoefficient 45 48 1 2) v3377_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3377_mb : Scalar.QComplex := ((-829083560529045966217287 : Int)/10^30,(-431476724294514734830769070 : Int)/10^30)
theorem v3377_mb_checked : Scalar.distance (sourceCoefficient 45 48 3 1) v3377_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3377_mg : Scalar.QComplex := ((-93086258034247542764040 : Int)/10^30,(178865468058668555441 : Int)/10^30)
theorem v3377_mg_checked : Scalar.distance (sourceCoefficient 45 48 3 2) v3377_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3377_upper : Scalar.QComplex := ((999996123407396544376524082275 : Int)/10^30,(-2784451504146020099074658802 : Int)/10^30)
theorem v3377_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 48 5) 1) 14) v3377_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3377 : Material (45 : Basis) (48 : Basis) where
  plus := ![v3377_pa,v3377_pb,v3377_pg]
  minus := ![(Primitive.Addresses.material3377 1).one,v3377_mb,v3377_mg]
  upper := v3377_upper
  lower := (Primitive.Addresses.material3377 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3377_pa_checked.trans (by decide +kernel)
    · exact v3377_pb_checked.trans (by decide +kernel)
    · exact v3377_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 48 Primitive.Addresses.material3377
    · exact v3377_mb_checked.trans (by decide +kernel)
    · exact v3377_mg_checked.trans (by decide +kernel)
  upper_error := v3377_upper_checked
  lower_error := reuse_lower_error 45 48 Primitive.Addresses.material3377

def v3378_pa : Scalar.QComplex := ((999999416169870040913430793447 : Int)/10^30,(-1080583138430612607886060539 : Int)/10^30)
theorem v3378_pa_checked : Scalar.distance (sourceCoefficient 45 49 1 0) v3378_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3378_pb : Scalar.QComplex := ((-466247333426861827972298 : Int)/10^30,(-431477268741001775981694326 : Int)/10^30)
theorem v3378_pb_checked : Scalar.distance (sourceCoefficient 45 49 1 1) v3378_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3378_pg : Scalar.QComplex := ((-93086375512551347567222 : Int)/10^30,(100587626522570325407 : Int)/10^30)
theorem v3378_pg_checked : Scalar.distance (sourceCoefficient 45 49 1 2) v3378_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3378_mb : Scalar.QComplex := ((-838592609730358893666134 : Int)/10^30,(-431476705731845391359181241 : Int)/10^30)
theorem v3378_mb_checked : Scalar.distance (sourceCoefficient 45 49 3 1) v3378_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3378_mg : Scalar.QComplex := ((-93086254049648096266645 : Int)/10^30,(180916938681809851844 : Int)/10^30)
theorem v3378_mg_checked : Scalar.distance (sourceCoefficient 45 49 3 2) v3378_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3378_upper : Scalar.QComplex := ((999996061799740644319908105062 : Int)/10^30,(-2806489802099782687653959710 : Int)/10^30)
theorem v3378_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 49 5) 1) 14) v3378_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3378 : Material (45 : Basis) (49 : Basis) where
  plus := ![v3378_pa,v3378_pb,v3378_pg]
  minus := ![(Primitive.Addresses.material3378 1).one,v3378_mb,v3378_mg]
  upper := v3378_upper
  lower := (Primitive.Addresses.material3378 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3378_pa_checked.trans (by decide +kernel)
    · exact v3378_pb_checked.trans (by decide +kernel)
    · exact v3378_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 49 Primitive.Addresses.material3378
    · exact v3378_mb_checked.trans (by decide +kernel)
    · exact v3378_mg_checked.trans (by decide +kernel)
  upper_error := v3378_upper_checked
  lower_error := reuse_lower_error 45 49 Primitive.Addresses.material3378

def v3379_pa : Scalar.QComplex := ((999999413383748672852616610166 : Int)/10^30,(-1083158418023729549071445912 : Int)/10^30)
theorem v3379_pa_checked : Scalar.distance (sourceCoefficient 45 50 1 0) v3379_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3379_pb : Scalar.QComplex := ((-467358508652173619341816 : Int)/10^30,(-431477267512533413154805254 : Int)/10^30)
theorem v3379_pb_checked : Scalar.distance (sourceCoefficient 45 50 1 1) v3379_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3379_pg : Scalar.QComplex := ((-93086375250362174764239 : Int)/10^30,(100827350102707693354 : Int)/10^30)
theorem v3379_pg_checked : Scalar.distance (sourceCoefficient 45 50 1 2) v3379_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3379_mb : Scalar.QComplex := ((-839703783481816496477112 : Int)/10^30,(-431476703544483311977504184 : Int)/10^30)
theorem v3379_mb_checked : Scalar.distance (sourceCoefficient 45 50 3 1) v3379_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3379_mg : Scalar.QComplex := ((-93086253580588368179381 : Int)/10^30,(181156661946429727431 : Int)/10^30)
theorem v3379_mg_checked : Scalar.distance (sourceCoefficient 45 50 3 2) v3379_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3379_upper : Scalar.QComplex := ((999996054568924475679439738088 : Int)/10^30,(-2809065073048730462166221304 : Int)/10^30)
theorem v3379_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 50 5) 1) 14) v3379_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3379 : Material (45 : Basis) (50 : Basis) where
  plus := ![v3379_pa,v3379_pb,v3379_pg]
  minus := ![(Primitive.Addresses.material3379 1).one,v3379_mb,v3379_mg]
  upper := v3379_upper
  lower := (Primitive.Addresses.material3379 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3379_pa_checked.trans (by decide +kernel)
    · exact v3379_pb_checked.trans (by decide +kernel)
    · exact v3379_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 50 Primitive.Addresses.material3379
    · exact v3379_mb_checked.trans (by decide +kernel)
    · exact v3379_mg_checked.trans (by decide +kernel)
  upper_error := v3379_upper_checked
  lower_error := reuse_lower_error 45 50 Primitive.Addresses.material3379

def v3380_pa : Scalar.QComplex := ((999999401081033870906392129729 : Int)/10^30,(-1094457661837249521019698086 : Int)/10^30)
theorem v3380_pa_checked : Scalar.distance (sourceCoefficient 45 51 1 0) v3380_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3380_pb : Scalar.QComplex := ((-472233878219033960142220 : Int)/10^30,(-431477262077435186468013593 : Int)/10^30)
theorem v3380_pb_checked : Scalar.distance (sourceCoefficient 45 51 1 1) v3380_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3380_pg : Scalar.QComplex := ((-93086374091473570812945 : Int)/10^30,(101879156354420680371 : Int)/10^30)
theorem v3380_pg_checked : Scalar.distance (sourceCoefficient 45 51 1 2) v3380_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3380_mb : Scalar.QComplex := ((-844579146543108950245383 : Int)/10^30,(-431476693902162751319859008 : Int)/10^30)
theorem v3380_mb_checked : Scalar.distance (sourceCoefficient 45 51 3 1) v3380_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3380_mg : Scalar.QComplex := ((-93086251514038772102031 : Int)/10^30,(182208466806438506209 : Int)/10^30)
theorem v3380_mg_checked : Scalar.distance (sourceCoefficient 45 51 3 2) v3380_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3380_upper : Scalar.QComplex := ((999996022764758234437700770018 : Int)/10^30,(-2820364278799984421701925331 : Int)/10^30)
theorem v3380_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 51 5) 1) 14) v3380_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3380 : Material (45 : Basis) (51 : Basis) where
  plus := ![v3380_pa,v3380_pb,v3380_pg]
  minus := ![(Primitive.Addresses.material3380 1).one,v3380_mb,v3380_mg]
  upper := v3380_upper
  lower := (Primitive.Addresses.material3380 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3380_pa_checked.trans (by decide +kernel)
    · exact v3380_pb_checked.trans (by decide +kernel)
    · exact v3380_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 51 Primitive.Addresses.material3380
    · exact v3380_mb_checked.trans (by decide +kernel)
    · exact v3380_mg_checked.trans (by decide +kernel)
  upper_error := v3380_upper_checked
  lower_error := reuse_lower_error 45 51 Primitive.Addresses.material3380

def v3381_pa : Scalar.QComplex := ((999999374314719748556436858021 : Int)/10^30,(-1118646579139639260424978994 : Int)/10^30)
theorem v3381_pa_checked : Scalar.distance (sourceCoefficient 45 52 1 0) v3381_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3381_pb : Scalar.QComplex := ((-482670851907589876668530 : Int)/10^30,(-431477250195292884865355053 : Int)/10^30)
theorem v3381_pb_checked : Scalar.distance (sourceCoefficient 45 52 1 1) v3381_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3381_pg : Scalar.QComplex := ((-93086371563963873787492 : Int)/10^30,(104130816267668538421 : Int)/10^30)
theorem v3381_pg_checked : Scalar.distance (sourceCoefficient 45 52 1 2) v3381_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3381_mb : Scalar.QComplex := ((-855016106091748914801213 : Int)/10^30,(-431476673013386644603406516 : Int)/10^30)
theorem v3381_mb_checked : Scalar.distance (sourceCoefficient 45 52 3 1) v3381_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3381_mg : Scalar.QComplex := ((-93086247043448922048988 : Int)/10^30,(184460123700163438893 : Int)/10^30)
theorem v3381_mg_checked : Scalar.distance (sourceCoefficient 45 52 3 2) v3381_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3381_upper : Scalar.QComplex := ((999995954250607114879697890511 : Int)/10^30,(-2844553113879593314896521806 : Int)/10^30)
theorem v3381_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 52 5) 1) 14) v3381_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3381 : Material (45 : Basis) (52 : Basis) where
  plus := ![v3381_pa,v3381_pb,v3381_pg]
  minus := ![(Primitive.Addresses.material3381 1).one,v3381_mb,v3381_mg]
  upper := v3381_upper
  lower := (Primitive.Addresses.material3381 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3381_pa_checked.trans (by decide +kernel)
    · exact v3381_pb_checked.trans (by decide +kernel)
    · exact v3381_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 52 Primitive.Addresses.material3381
    · exact v3381_mb_checked.trans (by decide +kernel)
    · exact v3381_mg_checked.trans (by decide +kernel)
  upper_error := v3381_upper_checked
  lower_error := reuse_lower_error 45 52 Primitive.Addresses.material3381

def v3382_pa : Scalar.QComplex := ((999999370165863431312160345042 : Int)/10^30,(-1122349266693009468054986720 : Int)/10^30)
theorem v3382_pa_checked : Scalar.distance (sourceCoefficient 45 53 1 0) v3382_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3382_pb : Scalar.QComplex := ((-484268478285502535300940 : Int)/10^30,(-431477248346742206150727096 : Int)/10^30)
theorem v3382_pb_checked : Scalar.distance (sourceCoefficient 45 53 1 1) v3382_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3382_pg : Scalar.QComplex := ((-93086371171460737124947 : Int)/10^30,(104475486225629914542 : Int)/10^30)
theorem v3382_pg_checked : Scalar.distance (sourceCoefficient 45 53 1 2) v3382_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3382_mb : Scalar.QComplex := ((-856613730279576277705500 : Int)/10^30,(-431476669786157044471042308 : Int)/10^30)
theorem v3382_mb_checked : Scalar.distance (sourceCoefficient 45 53 3 1) v3382_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3382_mg : Scalar.QComplex := ((-93086246353511281171285 : Int)/10^30,(184804793191075908216 : Int)/10^30)
theorem v3382_mg_checked : Scalar.distance (sourceCoefficient 45 53 3 2) v3382_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3382_upper : Scalar.QComplex := ((999995943711254164943463037348 : Int)/10^30,(-2848255788757695737756420837 : Int)/10^30)
theorem v3382_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 53 5) 1) 14) v3382_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3382 : Material (45 : Basis) (53 : Basis) where
  plus := ![v3382_pa,v3382_pb,v3382_pg]
  minus := ![(Primitive.Addresses.material3382 1).one,v3382_mb,v3382_mg]
  upper := v3382_upper
  lower := (Primitive.Addresses.material3382 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3382_pa_checked.trans (by decide +kernel)
    · exact v3382_pb_checked.trans (by decide +kernel)
    · exact v3382_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 53 Primitive.Addresses.material3382
    · exact v3382_mb_checked.trans (by decide +kernel)
    · exact v3382_mg_checked.trans (by decide +kernel)
  upper_error := v3382_upper_checked
  lower_error := reuse_lower_error 45 53 Primitive.Addresses.material3382

def v3383_pa : Scalar.QComplex := ((999999368051302759811663832787 : Int)/10^30,(-1124231735507062053138934247 : Int)/10^30)
theorem v3383_pa_checked : Scalar.distance (sourceCoefficient 45 54 1 0) v3383_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3383_pb : Scalar.QComplex := ((-485080721226830236851836 : Int)/10^30,(-431477247403903486387649114 : Int)/10^30)
theorem v3383_pb_checked : Scalar.distance (sourceCoefficient 45 54 1 1) v3383_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3383_pg : Scalar.QComplex := ((-93086370971338852188569 : Int)/10^30,(104650718523047715342 : Int)/10^30)
theorem v3383_pg_checked : Scalar.distance (sourceCoefficient 45 54 1 2) v3383_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3383_mb : Scalar.QComplex := ((-857425972104841459587911 : Int)/10^30,(-431476668142389599468190462 : Int)/10^30)
theorem v3383_mb_checked : Scalar.distance (sourceCoefficient 45 54 3 1) v3383_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3383_mg : Scalar.QComplex := ((-93086246002171890247573 : Int)/10^30,(184980025250550542631 : Int)/10^30)
theorem v3383_mg_checked : Scalar.distance (sourceCoefficient 45 54 3 2) v3383_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3383_upper : Scalar.QComplex := ((999995938347726246014711223260 : Int)/10^30,(-2850138251118492267065255815 : Int)/10^30)
theorem v3383_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 54 5) 1) 14) v3383_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3383 : Material (45 : Basis) (54 : Basis) where
  plus := ![v3383_pa,v3383_pb,v3383_pg]
  minus := ![(Primitive.Addresses.material3383 1).one,v3383_mb,v3383_mg]
  upper := v3383_upper
  lower := (Primitive.Addresses.material3383 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3383_pa_checked.trans (by decide +kernel)
    · exact v3383_pb_checked.trans (by decide +kernel)
    · exact v3383_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 54 Primitive.Addresses.material3383
    · exact v3383_mb_checked.trans (by decide +kernel)
    · exact v3383_mg_checked.trans (by decide +kernel)
  upper_error := v3383_upper_checked
  lower_error := reuse_lower_error 45 54 Primitive.Addresses.material3383

def v3384_pa : Scalar.QComplex := ((999999350683832271334691298781 : Int)/10^30,(-1139575321707979486886844913 : Int)/10^30)
theorem v3384_pa_checked : Scalar.distance (sourceCoefficient 45 55 1 0) v3384_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3384_pb : Scalar.QComplex := ((-491701133445343802279712 : Int)/10^30,(-431477239643004809317212143 : Int)/10^30)
theorem v3384_pb_checked : Scalar.distance (sourceCoefficient 45 55 1 1) v3384_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3384_pg : Scalar.QComplex := ((-93086369325837570941869 : Int)/10^30,(106078998149927698699 : Int)/10^30)
theorem v3384_pg_checked : Scalar.distance (sourceCoefficient 45 55 1 2) v3384_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3384_mb : Scalar.QComplex := ((-864046375160966967866821 : Int)/10^30,(-431476654668376239855460466 : Int)/10^30)
theorem v3384_mb_checked : Scalar.distance (sourceCoefficient 45 55 3 1) v3384_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3384_mg : Scalar.QComplex := ((-93086243124130231025230 : Int)/10^30,(186408302925623250207 : Int)/10^30)
theorem v3384_mg_checked : Scalar.distance (sourceCoefficient 45 55 3 2) v3384_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3384_upper : Scalar.QComplex := ((999995894498643800828172383946 : Int)/10^30,(-2865481784492261940296221096 : Int)/10^30)
theorem v3384_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 55 5) 1) 14) v3384_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3384 : Material (45 : Basis) (55 : Basis) where
  plus := ![v3384_pa,v3384_pb,v3384_pg]
  minus := ![(Primitive.Addresses.material3384 1).one,v3384_mb,v3384_mg]
  upper := v3384_upper
  lower := (Primitive.Addresses.material3384 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3384_pa_checked.trans (by decide +kernel)
    · exact v3384_pb_checked.trans (by decide +kernel)
    · exact v3384_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 55 Primitive.Addresses.material3384
    · exact v3384_mb_checked.trans (by decide +kernel)
    · exact v3384_mg_checked.trans (by decide +kernel)
  upper_error := v3384_upper_checked
  lower_error := reuse_lower_error 45 55 Primitive.Addresses.material3384

def v3385_pa : Scalar.QComplex := ((999999346527479722544676606639 : Int)/10^30,(-1143216783260539736998237490 : Int)/10^30)
theorem v3385_pa_checked : Scalar.distance (sourceCoefficient 45 56 1 0) v3385_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3385_pb : Scalar.QComplex := ((-493272342166333342237775 : Int)/10^30,(-431477237781240443518208467 : Int)/10^30)
theorem v3385_pb_checked : Scalar.distance (sourceCoefficient 45 56 1 1) v3385_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3385_pg : Scalar.QComplex := ((-93086368931560183268590 : Int)/10^30,(106417968796560350263 : Int)/10^30)
theorem v3385_pg_checked : Scalar.distance (sourceCoefficient 45 56 1 2) v3385_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3385_mb : Scalar.QComplex := ((-865617581690304896284361 : Int)/10^30,(-431476651450730205676331451 : Int)/10^30)
theorem v3385_mb_checked : Scalar.distance (sourceCoefficient 45 56 3 1) v3385_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3385_mg : Scalar.QComplex := ((-93086242437336588786662 : Int)/10^30,(186747273105798010338 : Int)/10^30)
theorem v3385_mg_checked : Scalar.distance (sourceCoefficient 45 56 3 2) v3385_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3385_upper : Scalar.QComplex := ((999995884057465153529537298392 : Int)/10^30,(-2869123233447805526137532754 : Int)/10^30)
theorem v3385_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 56 5) 1) 14) v3385_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3385 : Material (45 : Basis) (56 : Basis) where
  plus := ![v3385_pa,v3385_pb,v3385_pg]
  minus := ![(Primitive.Addresses.material3385 1).one,v3385_mb,v3385_mg]
  upper := v3385_upper
  lower := (Primitive.Addresses.material3385 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3385_pa_checked.trans (by decide +kernel)
    · exact v3385_pb_checked.trans (by decide +kernel)
    · exact v3385_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 56 Primitive.Addresses.material3385
    · exact v3385_mb_checked.trans (by decide +kernel)
    · exact v3385_mg_checked.trans (by decide +kernel)
  upper_error := v3385_upper_checked
  lower_error := reuse_lower_error 45 56 Primitive.Addresses.material3385

def v3386_pa : Scalar.QComplex := ((999999332993477763118789798636 : Int)/10^30,(-1154994631838634007537786361 : Int)/10^30)
theorem v3386_pa_checked : Scalar.distance (sourceCoefficient 45 57 1 0) v3386_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3386_pb : Scalar.QComplex := ((-498354218788108101737674 : Int)/10^30,(-431477231707358738203373829 : Int)/10^30)
theorem v3386_pb_checked : Scalar.distance (sourceCoefficient 45 57 1 1) v3386_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3386_pg : Scalar.QComplex := ((-93086367646458335417290 : Int)/10^30,(107514326641773981088 : Int)/10^30)
theorem v3386_pg_checked : Scalar.distance (sourceCoefficient 45 57 1 2) v3386_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3386_mb : Scalar.QComplex := ((-870699451178378382052733 : Int)/10^30,(-431476640991420116580276826 : Int)/10^30)
theorem v3386_mb_checked : Scalar.distance (sourceCoefficient 45 57 3 1) v3386_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3386_mg : Scalar.QComplex := ((-93086240206127777142495 : Int)/10^30,(187843629433802493505 : Int)/10^30)
theorem v3386_mg_checked : Scalar.distance (sourceCoefficient 45 57 3 2) v3386_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3386_upper : Scalar.QComplex := ((999995850195985183695554575982 : Int)/10^30,(-2880901041125718275984528142 : Int)/10^30)
theorem v3386_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 57 5) 1) 14) v3386_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3386 : Material (45 : Basis) (57 : Basis) where
  plus := ![v3386_pa,v3386_pb,v3386_pg]
  minus := ![(Primitive.Addresses.material3386 1).one,v3386_mb,v3386_mg]
  upper := v3386_upper
  lower := (Primitive.Addresses.material3386 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3386_pa_checked.trans (by decide +kernel)
    · exact v3386_pb_checked.trans (by decide +kernel)
    · exact v3386_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 57 Primitive.Addresses.material3386
    · exact v3386_mb_checked.trans (by decide +kernel)
    · exact v3386_mg_checked.trans (by decide +kernel)
  upper_error := v3386_upper_checked
  lower_error := reuse_lower_error 45 57 Primitive.Addresses.material3386

def v3387_pa : Scalar.QComplex := ((999999325592006930637412160137 : Int)/10^30,(-1161385177842641515014043230 : Int)/10^30)
theorem v3387_pa_checked : Scalar.distance (sourceCoefficient 45 58 1 0) v3387_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3387_pb : Scalar.QComplex := ((-501111595568884064334676 : Int)/10^30,(-431477228378331513286316407 : Int)/10^30)
theorem v3387_pb_checked : Scalar.distance (sourceCoefficient 45 58 1 1) v3387_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3387_pg : Scalar.QComplex := ((-93086366942869967350179 : Int)/10^30,(108109199736378849733 : Int)/10^30)
theorem v3387_pg_checked : Scalar.distance (sourceCoefficient 45 58 1 2) v3387_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3387_mb : Scalar.QComplex := ((-873456824059656389539515 : Int)/10^30,(-431476635282902157042687829 : Int)/10^30)
theorem v3387_mb_checked : Scalar.distance (sourceCoefficient 45 58 3 1) v3387_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3387_mg : Scalar.QComplex := ((-93086238989190982499099 : Int)/10^30,(188438501699743848786 : Int)/10^30)
theorem v3387_mg_checked : Scalar.distance (sourceCoefficient 45 58 3 2) v3387_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3387_upper : Scalar.QComplex := ((999995831765022717723344039306 : Int)/10^30,(-2887291564837490996084004442 : Int)/10^30)
theorem v3387_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 58 5) 1) 14) v3387_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3387 : Material (45 : Basis) (58 : Basis) where
  plus := ![v3387_pa,v3387_pb,v3387_pg]
  minus := ![(Primitive.Addresses.material3387 1).one,v3387_mb,v3387_mg]
  upper := v3387_upper
  lower := (Primitive.Addresses.material3387 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3387_pa_checked.trans (by decide +kernel)
    · exact v3387_pb_checked.trans (by decide +kernel)
    · exact v3387_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 58 Primitive.Addresses.material3387
    · exact v3387_mb_checked.trans (by decide +kernel)
    · exact v3387_mg_checked.trans (by decide +kernel)
  upper_error := v3387_upper_checked
  lower_error := reuse_lower_error 45 58 Primitive.Addresses.material3387

def v3388_pa : Scalar.QComplex := ((999999305036918860546302642777 : Int)/10^30,(-1178951092838555049732447716 : Int)/10^30)
theorem v3388_pa_checked : Scalar.distance (sourceCoefficient 45 59 1 0) v3388_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3388_pb : Scalar.QComplex := ((-508690892522139501641710 : Int)/10^30,(-431477219106670190819538589 : Int)/10^30)
theorem v3388_pb_checked : Scalar.distance (sourceCoefficient 45 59 1 1) v3388_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3388_pg : Scalar.QComplex := ((-93086364986041678093123 : Int)/10^30,(109744347996932664154 : Int)/10^30)
theorem v3388_pg_checked : Scalar.distance (sourceCoefficient 45 59 1 2) v3388_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3388_mb : Scalar.QComplex := ((-881036110189767039002556 : Int)/10^30,(-431476619470652375042651813 : Int)/10^30)
theorem v3388_mb_checked : Scalar.distance (sourceCoefficient 45 59 3 1) v3388_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3388_mg : Scalar.QComplex := ((-93086235621304117344554 : Int)/10^30,(190073647662802554482 : Int)/10^30)
theorem v3388_mg_checked : Scalar.distance (sourceCoefficient 45 59 3 2) v3388_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3388_upper : Scalar.QComplex := ((999995780892789546434747938694 : Int)/10^30,(-2904857418194820315759075801 : Int)/10^30)
theorem v3388_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 59 5) 1) 14) v3388_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3388 : Material (45 : Basis) (59 : Basis) where
  plus := ![v3388_pa,v3388_pb,v3388_pg]
  minus := ![(Primitive.Addresses.material3388 1).one,v3388_mb,v3388_mg]
  upper := v3388_upper
  lower := (Primitive.Addresses.material3388 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3388_pa_checked.trans (by decide +kernel)
    · exact v3388_pb_checked.trans (by decide +kernel)
    · exact v3388_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 59 Primitive.Addresses.material3388
    · exact v3388_mb_checked.trans (by decide +kernel)
    · exact v3388_mg_checked.trans (by decide +kernel)
  upper_error := v3388_upper_checked
  lower_error := reuse_lower_error 45 59 Primitive.Addresses.material3388

def v3389_pa : Scalar.QComplex := ((999999280941422916727284589475 : Int)/10^30,(-1199215008712494455911842460 : Int)/10^30)
theorem v3389_pa_checked : Scalar.distance (sourceCoefficient 45 60 1 0) v3389_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3389_pb : Scalar.QComplex := ((-517434316044922421118121 : Int)/10^30,(-431477208190438418122073239 : Int)/10^30)
theorem v3389_pb_checked : Scalar.distance (sourceCoefficient 45 60 1 1) v3389_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3389_pg : Scalar.QComplex := ((-93086362687032620757758 : Int)/10^30,(111630643509715924120 : Int)/10^30)
theorem v3389_pg_checked : Scalar.distance (sourceCoefficient 45 60 1 2) v3389_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3389_mb : Scalar.QComplex := ((-889779521036757415741809 : Int)/10^30,(-431476601009243955972837117 : Int)/10^30)
theorem v3389_mb_checked : Scalar.distance (sourceCoefficient 45 60 3 1) v3389_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3389_mg : Scalar.QComplex := ((-93086231694507844099573 : Int)/10^30,(191959940489290514119 : Int)/10^30)
theorem v3389_mg_checked : Scalar.distance (sourceCoefficient 45 60 3 2) v3389_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3389_upper : Scalar.QComplex := ((999995721823649019694920182943 : Int)/10^30,(-2925121262301397321760802392 : Int)/10^30)
theorem v3389_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 60 5) 1) 14) v3389_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3389 : Material (45 : Basis) (60 : Basis) where
  plus := ![v3389_pa,v3389_pb,v3389_pg]
  minus := ![(Primitive.Addresses.material3389 1).one,v3389_mb,v3389_mg]
  upper := v3389_upper
  lower := (Primitive.Addresses.material3389 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3389_pa_checked.trans (by decide +kernel)
    · exact v3389_pb_checked.trans (by decide +kernel)
    · exact v3389_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 60 Primitive.Addresses.material3389
    · exact v3389_mb_checked.trans (by decide +kernel)
    · exact v3389_mg_checked.trans (by decide +kernel)
  upper_error := v3389_upper_checked
  lower_error := reuse_lower_error 45 60 Primitive.Addresses.material3389

def v3390_pa : Scalar.QComplex := ((999999273897653846272381118667 : Int)/10^30,(-1205074340064893319283012171 : Int)/10^30)
theorem v3390_pa_checked : Scalar.distance (sourceCoefficient 45 61 1 0) v3390_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3390_pb : Scalar.QComplex := ((-519962485602313227120134 : Int)/10^30,(-431477204989969773424870872 : Int)/10^30)
theorem v3390_pb_checked : Scalar.distance (sourceCoefficient 45 61 1 1) v3390_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3390_pg : Scalar.QComplex := ((-93086362013960377722938 : Int)/10^30,(112176067724321012911 : Int)/10^30)
theorem v3390_pg_checked : Scalar.distance (sourceCoefficient 45 61 1 2) v3390_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3390_mb : Scalar.QComplex := ((-892307686890934855853712 : Int)/10^30,(-431476595627080039458129076 : Int)/10^30)
theorem v3390_mb_checked : Scalar.distance (sourceCoefficient 45 61 3 1) v3390_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3390_mg : Scalar.QComplex := ((-93086230550759319470849 : Int)/10^30,(192505363919978209003 : Int)/10^30)
theorem v3390_mg_checked : Scalar.distance (sourceCoefficient 45 61 3 2) v3390_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3390_upper : Scalar.QComplex := ((999995704667216080254204353914 : Int)/10^30,(-2930980572770104011277200273 : Int)/10^30)
theorem v3390_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 61 5) 1) 14) v3390_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3390 : Material (45 : Basis) (61 : Basis) where
  plus := ![v3390_pa,v3390_pb,v3390_pg]
  minus := ![(Primitive.Addresses.material3390 1).one,v3390_mb,v3390_mg]
  upper := v3390_upper
  lower := (Primitive.Addresses.material3390 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3390_pa_checked.trans (by decide +kernel)
    · exact v3390_pb_checked.trans (by decide +kernel)
    · exact v3390_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 61 Primitive.Addresses.material3390
    · exact v3390_mb_checked.trans (by decide +kernel)
    · exact v3390_mg_checked.trans (by decide +kernel)
  upper_error := v3390_upper_checked
  lower_error := reuse_lower_error 45 61 Primitive.Addresses.material3390

def v3391_pa : Scalar.QComplex := ((999999263602179604168316372017 : Int)/10^30,(-1213587697082461974117058217 : Int)/10^30)
theorem v3391_pa_checked : Scalar.distance (sourceCoefficient 45 62 1 0) v3391_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3391_pb : Scalar.QComplex := ((-523635807465550289011650 : Int)/10^30,(-431477200304629100442691596 : Int)/10^30)
theorem v3391_pb_checked : Scalar.distance (sourceCoefficient 45 62 1 1) v3391_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3391_pg : Scalar.QComplex := ((-93086361029371089107047 : Int)/10^30,(112968545701211922141 : Int)/10^30)
theorem v3391_pg_checked : Scalar.distance (sourceCoefficient 45 62 1 2) v3391_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3391_mb : Scalar.QComplex := ((-895981003343188328086388 : Int)/10^30,(-431476587771829783344117084 : Int)/10^30)
theorem v3391_mb_checked : Scalar.distance (sourceCoefficient 45 62 3 1) v3391_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3391_mg : Scalar.QComplex := ((-93086228882297595288827 : Int)/10^30,(193297840752137137584 : Int)/10^30)
theorem v3391_mg_checked : Scalar.distance (sourceCoefficient 45 62 3 2) v3391_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3391_upper : Scalar.QComplex := ((999995679678475285441690042140 : Int)/10^30,(-2939493899338972893863275824 : Int)/10^30)
theorem v3391_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 62 5) 1) 14) v3391_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3391 : Material (45 : Basis) (62 : Basis) where
  plus := ![v3391_pa,v3391_pb,v3391_pg]
  minus := ![(Primitive.Addresses.material3391 1).one,v3391_mb,v3391_mg]
  upper := v3391_upper
  lower := (Primitive.Addresses.material3391 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3391_pa_checked.trans (by decide +kernel)
    · exact v3391_pb_checked.trans (by decide +kernel)
    · exact v3391_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 62 Primitive.Addresses.material3391
    · exact v3391_mb_checked.trans (by decide +kernel)
    · exact v3391_mg_checked.trans (by decide +kernel)
  upper_error := v3391_upper_checked
  lower_error := reuse_lower_error 45 62 Primitive.Addresses.material3391

def v3392_pa : Scalar.QComplex := ((999999233203661607429051073108 : Int)/10^30,(-1238382852274900213784629475 : Int)/10^30)
theorem v3392_pa_checked : Scalar.distance (sourceCoefficient 45 63 1 0) v3392_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3392_pb : Scalar.QComplex := ((-534334358537221148402288 : Int)/10^30,(-431477186421003812420041779 : Int)/10^30)
theorem v3392_pb_checked : Scalar.distance (sourceCoefficient 45 63 1 1) v3392_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3392_pg : Scalar.QComplex := ((-93086358116908207363209 : Int)/10^30,(115276638066403566527 : Int)/10^30)
theorem v3392_pg_checked : Scalar.distance (sourceCoefficient 45 63 1 2) v3392_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3392_mb : Scalar.QComplex := ((-906679538450356347262846 : Int)/10^30,(-431476564655841934831069682 : Int)/10^30)
theorem v3392_mb_checked : Scalar.distance (sourceCoefficient 45 63 3 1) v3392_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3392_mg : Scalar.QComplex := ((-93086223978056039448863 : Int)/10^30,(195605929744596214891 : Int)/10^30)
theorem v3392_mg_checked : Scalar.distance (sourceCoefficient 45 63 3 2) v3392_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3392_upper : Scalar.QComplex := ((999995606485814100483436473833 : Int)/10^30,(-2964288965136855787563513660 : Int)/10^30)
theorem v3392_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 63 5) 1) 14) v3392_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3392 : Material (45 : Basis) (63 : Basis) where
  plus := ![v3392_pa,v3392_pb,v3392_pg]
  minus := ![(Primitive.Addresses.material3392 1).one,v3392_mb,v3392_mg]
  upper := v3392_upper
  lower := (Primitive.Addresses.material3392 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3392_pa_checked.trans (by decide +kernel)
    · exact v3392_pb_checked.trans (by decide +kernel)
    · exact v3392_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 63 Primitive.Addresses.material3392
    · exact v3392_mb_checked.trans (by decide +kernel)
    · exact v3392_mg_checked.trans (by decide +kernel)
  upper_error := v3392_upper_checked
  lower_error := reuse_lower_error 45 63 Primitive.Addresses.material3392

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
