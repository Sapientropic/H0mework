import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B054
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B055

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1313_pa : Scalar.QComplex := ((999999734919043811797147060179 : Int)/10^30,(-728122134060277261276120045 : Int)/10^30)
theorem v1313_pa_checked : Scalar.distance (sourceCoefficient 14 61 1 0) v1313_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1313_pb : Scalar.QComplex := ((-314168309799682432667931 : Int)/10^30,(-431477374225294725782444792 : Int)/10^30)
theorem v1313_pb_checked : Scalar.distance (sourceCoefficient 14 61 1 1) v1313_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1313_pg : Scalar.QComplex := ((-93086401726688499194899 : Int)/10^30,(67778287443961952589 : Int)/10^30)
theorem v1313_pg_checked : Scalar.distance (sourceCoefficient 14 61 1 2) v1313_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1313_mb : Scalar.QComplex := ((-686513733757344328977826 : Int)/10^30,(-431476942453447069829567617 : Int)/10^30)
theorem v1313_mb_checked : Scalar.distance (sourceCoefficient 14 61 3 1) v1313_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1313_mg : Scalar.QComplex := ((-93086308576757434233918 : Int)/10^30,(148107634441237599808 : Int)/10^30)
theorem v1313_mg_checked : Scalar.distance (sourceCoefficient 14 61 3 2) v1313_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1313_upper : Scalar.QComplex := ((999996988864158206409622956748 : Int)/10^30,(-2454029872810867602070261565 : Int)/10^30)
theorem v1313_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 61 5) 1) 14) v1313_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1313 : Material (14 : Basis) (61 : Basis) where
  plus := ![v1313_pa,v1313_pb,v1313_pg]
  minus := ![(Primitive.Addresses.material1313 1).one,v1313_mb,v1313_mg]
  upper := v1313_upper
  lower := (Primitive.Addresses.material1313 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1313_pa_checked.trans (by decide +kernel)
    · exact v1313_pb_checked.trans (by decide +kernel)
    · exact v1313_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 61 Primitive.Addresses.material1313
    · exact v1313_mb_checked.trans (by decide +kernel)
    · exact v1313_mg_checked.trans (by decide +kernel)
  upper_error := v1313_upper_checked
  lower_error := reuse_lower_error 14 61 Primitive.Addresses.material1313

def v1314_pa : Scalar.QComplex := ((999999728684036932164062199237 : Int)/10^30,(-736635495019972588460329625 : Int)/10^30)
theorem v1314_pa_checked : Scalar.distance (sourceCoefficient 14 62 1 0) v1314_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1314_pb : Scalar.QComplex := ((-317841632796878828356068 : Int)/10^30,(-431477370707954282141026818 : Int)/10^30)
theorem v1314_pb_checked : Scalar.distance (sourceCoefficient 14 62 1 1) v1314_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1314_pg : Scalar.QComplex := ((-93086401057077881820847 : Int)/10^30,(68570765726651606534 : Int)/10^30)
theorem v1314_pg_checked : Scalar.distance (sourceCoefficient 14 62 1 2) v1314_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1314_mb : Scalar.QComplex := ((-690187052351488305925767 : Int)/10^30,(-431476935766195629600617862 : Int)/10^30)
theorem v1314_mb_checked : Scalar.distance (sourceCoefficient 14 62 3 1) v1314_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1314_mg : Scalar.QComplex := ((-93086307223274000122237 : Int)/10^30,(148900111851007566409 : Int)/10^30)
theorem v1314_mg_checked : Scalar.distance (sourceCoefficient 14 62 3 2) v1314_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1314_upper : Scalar.QComplex := ((999996967935871922725918593995 : Int)/10^30,(-2462543210329855590575176498 : Int)/10^30)
theorem v1314_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 62 5) 1) 14) v1314_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1314 : Material (14 : Basis) (62 : Basis) where
  plus := ![v1314_pa,v1314_pb,v1314_pg]
  minus := ![(Primitive.Addresses.material1314 1).one,v1314_mb,v1314_mg]
  upper := v1314_upper
  lower := (Primitive.Addresses.material1314 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1314_pa_checked.trans (by decide +kernel)
    · exact v1314_pb_checked.trans (by decide +kernel)
    · exact v1314_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 62 Primitive.Addresses.material1314
    · exact v1314_mb_checked.trans (by decide +kernel)
    · exact v1314_mg_checked.trans (by decide +kernel)
  upper_error := v1314_upper_checked
  lower_error := reuse_lower_error 14 62 Primitive.Addresses.material1314

def v1315_pa : Scalar.QComplex := ((999999710111631548627204173222 : Int)/10^30,(-761430661890811583998677787 : Int)/10^30)
theorem v1315_pa_checked : Scalar.distance (sourceCoefficient 14 63 1 0) v1315_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1315_pb : Scalar.QComplex := ((-328540187227861202145541 : Int)/10^30,(-431477360226130065479072702 : Int)/10^30)
theorem v1315_pb_checked : Scalar.distance (sourceCoefficient 14 63 1 1) v1315_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1315_pg : Scalar.QComplex := ((-93086399061990489402644 : Int)/10^30,(70878858997760433474 : Int)/10^30)
theorem v1315_pg_checked : Scalar.distance (sourceCoefficient 14 63 1 2) v1315_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1315_mb : Scalar.QComplex := ((-700885593753567701827357 : Int)/10^30,(-431476916052004686867718152 : Int)/10^30)
theorem v1315_mb_checked : Scalar.distance (sourceCoefficient 14 63 3 1) v1315_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1315_mg : Scalar.QComplex := ((-93086303236406810261360 : Int)/10^30,(151208202541037219186 : Int)/10^30)
theorem v1315_mg_checked : Scalar.distance (sourceCoefficient 14 63 3 2) v1315_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1315_upper : Scalar.QComplex := ((999996906569285581504279314206 : Int)/10^30,(-2487338308216919360371887411 : Int)/10^30)
theorem v1315_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 63 5) 1) 14) v1315_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1315 : Material (14 : Basis) (63 : Basis) where
  plus := ![v1315_pa,v1315_pb,v1315_pg]
  minus := ![(Primitive.Addresses.material1315 1).one,v1315_mb,v1315_mg]
  upper := v1315_upper
  lower := (Primitive.Addresses.material1315 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1315_pa_checked.trans (by decide +kernel)
    · exact v1315_pb_checked.trans (by decide +kernel)
    · exact v1315_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 63 Primitive.Addresses.material1315
    · exact v1315_mb_checked.trans (by decide +kernel)
    · exact v1315_mg_checked.trans (by decide +kernel)
  upper_error := v1315_upper_checked
  lower_error := reuse_lower_error 14 63 Primitive.Addresses.material1315

def v1316_pa : Scalar.QComplex := ((999999682500706571811549042999 : Int)/10^30,(-796867922588540123320909171 : Int)/10^30)
theorem v1316_pa_checked : Scalar.distance (sourceCoefficient 14 64 1 0) v1316_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1316_pb : Scalar.QComplex := ((-343830564426499070979826 : Int)/10^30,(-431477344631518593029186429 : Int)/10^30)
theorem v1316_pb_checked : Scalar.distance (sourceCoefficient 14 64 1 1) v1316_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1316_pg : Scalar.QComplex := ((-93086396094708116998540 : Int)/10^30,(74177586628575394207 : Int)/10^30)
theorem v1316_pg_checked : Scalar.distance (sourceCoefficient 14 64 1 2) v1316_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1316_mb : Scalar.QComplex := ((-716175951801451989352945 : Int)/10^30,(-431476887262492151604935935 : Int)/10^30)
theorem v1316_mb_checked : Scalar.distance (sourceCoefficient 14 64 3 1) v1316_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1316_mg : Scalar.QComplex := ((-93086297422472166496128 : Int)/10^30,(154506926382954077719 : Int)/10^30)
theorem v1316_mg_checked : Scalar.distance (sourceCoefficient 14 64 3 2) v1316_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1316_upper : Scalar.QComplex := ((999996817796904606816032386086 : Int)/10^30,(-2522775468481059177049780146 : Int)/10^30)
theorem v1316_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 64 5) 1) 14) v1316_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1316 : Material (14 : Basis) (64 : Basis) where
  plus := ![v1316_pa,v1316_pb,v1316_pg]
  minus := ![(Primitive.Addresses.material1316 1).one,v1316_mb,v1316_mg]
  upper := v1316_upper
  lower := (Primitive.Addresses.material1316 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1316_pa_checked.trans (by decide +kernel)
    · exact v1316_pb_checked.trans (by decide +kernel)
    · exact v1316_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 64 Primitive.Addresses.material1316
    · exact v1316_mb_checked.trans (by decide +kernel)
    · exact v1316_mg_checked.trans (by decide +kernel)
  upper_error := v1316_upper_checked
  lower_error := reuse_lower_error 14 64 Primitive.Addresses.material1316

def v1317_pa : Scalar.QComplex := ((999999653193263081267767401658 : Int)/10^30,(-832834529521051794495446066 : Int)/10^30)
theorem v1317_pa_checked : Scalar.distance (sourceCoefficient 14 65 1 0) v1317_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1317_pb : Scalar.QComplex := ((-359349342142976782420451 : Int)/10^30,(-431477328065227208956314991 : Int)/10^30)
theorem v1317_pb_checked : Scalar.distance (sourceCoefficient 14 65 1 1) v1317_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1317_pg : Scalar.QComplex := ((-93086392943649803044910 : Int)/10^30,(77525589158432943085 : Int)/10^30)
theorem v1317_pg_checked : Scalar.distance (sourceCoefficient 14 65 1 2) v1317_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1317_mb : Scalar.QComplex := ((-731694709443616167381797 : Int)/10^30,(-431476857304200706401683825 : Int)/10^30)
theorem v1317_mb_checked : Scalar.distance (sourceCoefficient 14 65 3 1) v1317_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1317_mg : Scalar.QComplex := ((-93086291382239630994869 : Int)/10^30,(157854924946975866912 : Int)/10^30)
theorem v1317_mg_checked : Scalar.distance (sourceCoefficient 14 65 3 2) v1317_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1317_upper : Scalar.QComplex := ((999996726414404065844305413836 : Int)/10^30,(-2558741971263546042509808487 : Int)/10^30)
theorem v1317_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 65 5) 1) 14) v1317_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1317 : Material (14 : Basis) (65 : Basis) where
  plus := ![v1317_pa,v1317_pb,v1317_pg]
  minus := ![(Primitive.Addresses.material1317 1).one,v1317_mb,v1317_mg]
  upper := v1317_upper
  lower := (Primitive.Addresses.material1317 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1317_pa_checked.trans (by decide +kernel)
    · exact v1317_pb_checked.trans (by decide +kernel)
    · exact v1317_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 65 Primitive.Addresses.material1317
    · exact v1317_mb_checked.trans (by decide +kernel)
    · exact v1317_mg_checked.trans (by decide +kernel)
  upper_error := v1317_upper_checked
  lower_error := reuse_lower_error 14 65 Primitive.Addresses.material1317

def v1318_pa : Scalar.QComplex := ((999999638391069199590031299929 : Int)/10^30,(-850422089811759947786059075 : Int)/10^30)
theorem v1318_pa_checked : Scalar.distance (sourceCoefficient 14 66 1 0) v1318_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1318_pb : Scalar.QComplex := ((-366937976608109611191852 : Int)/10^30,(-431477319693426041009486688 : Int)/10^30)
theorem v1318_pb_checked : Scalar.distance (sourceCoefficient 14 66 1 1) v1318_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1318_pg : Scalar.QComplex := ((-93086391351647063502950 : Int)/10^30,(79162752092261176819 : Int)/10^30)
theorem v1318_pg_checked : Scalar.distance (sourceCoefficient 14 66 1 2) v1318_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1318_mb : Scalar.QComplex := ((-739283333858666211045712 : Int)/10^30,(-431476842383752891658270881 : Int)/10^30)
theorem v1318_mb_checked : Scalar.distance (sourceCoefficient 14 66 3 1) v1318_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1318_mg : Scalar.QComplex := ((-93086288377439607415886 : Int)/10^30,(159492085897386855256 : Int)/10^30)
theorem v1318_mg_checked : Scalar.distance (sourceCoefficient 14 66 3 2) v1318_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1318_upper : Scalar.QComplex := ((999996681257698699539264462559 : Int)/10^30,(-2576329479812405327512997824 : Int)/10^30)
theorem v1318_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 66 5) 1) 14) v1318_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1318 : Material (14 : Basis) (66 : Basis) where
  plus := ![v1318_pa,v1318_pb,v1318_pg]
  minus := ![(Primitive.Addresses.material1318 1).one,v1318_mb,v1318_mg]
  upper := v1318_upper
  lower := (Primitive.Addresses.material1318 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1318_pa_checked.trans (by decide +kernel)
    · exact v1318_pb_checked.trans (by decide +kernel)
    · exact v1318_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 66 Primitive.Addresses.material1318
    · exact v1318_mb_checked.trans (by decide +kernel)
    · exact v1318_mg_checked.trans (by decide +kernel)
  upper_error := v1318_upper_checked
  lower_error := reuse_lower_error 14 66 Primitive.Addresses.material1318

def v1319_pa : Scalar.QComplex := ((999999612853397502802790532023 : Int)/10^30,(-879939233761003859134669960 : Int)/10^30)
theorem v1319_pa_checked : Scalar.distance (sourceCoefficient 14 67 1 0) v1319_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1319_pb : Scalar.QComplex := ((-379673956350367148072625 : Int)/10^30,(-431477305243109890907428355 : Int)/10^30)
theorem v1319_pb_checked : Scalar.distance (sourceCoefficient 14 67 1 1) v1319_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1319_pg : Scalar.QComplex := ((-93086388604294995738250 : Int)/10^30,(81910397173374354884 : Int)/10^30)
theorem v1319_pg_checked : Scalar.distance (sourceCoefficient 14 67 1 2) v1319_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1319_mb : Scalar.QComplex := ((-752019296388764407397108 : Int)/10^30,(-431476816942865211735362817 : Int)/10^30)
theorem v1319_mb_checked : Scalar.distance (sourceCoefficient 14 67 3 1) v1319_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1319_mg : Scalar.QComplex := ((-93086283258994606955911 : Int)/10^30,(162239727584585097703 : Int)/10^30)
theorem v1319_mg_checked : Scalar.distance (sourceCoefficient 14 67 3 2) v1319_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1319_upper : Scalar.QComplex := ((999996604776152356100609290362 : Int)/10^30,(-2605846535723626064581562011 : Int)/10^30)
theorem v1319_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 67 5) 1) 14) v1319_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1319 : Material (14 : Basis) (67 : Basis) where
  plus := ![v1319_pa,v1319_pb,v1319_pg]
  minus := ![(Primitive.Addresses.material1319 1).one,v1319_mb,v1319_mg]
  upper := v1319_upper
  lower := (Primitive.Addresses.material1319 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1319_pa_checked.trans (by decide +kernel)
    · exact v1319_pb_checked.trans (by decide +kernel)
    · exact v1319_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 67 Primitive.Addresses.material1319
    · exact v1319_mb_checked.trans (by decide +kernel)
    · exact v1319_mg_checked.trans (by decide +kernel)
  upper_error := v1319_upper_checked
  lower_error := reuse_lower_error 14 67 Primitive.Addresses.material1319

def v1320_pa : Scalar.QComplex := ((999999568389106386188850429304 : Int)/10^30,(-929097196712840595269993359 : Int)/10^30)
theorem v1320_pa_checked : Scalar.distance (sourceCoefficient 14 68 1 0) v1320_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1320_pb : Scalar.QComplex := ((-400884504379794599883561 : Int)/10^30,(-431477280065002916469473673 : Int)/10^30)
theorem v1320_pb_checked : Scalar.distance (sourceCoefficient 14 68 1 1) v1320_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1320_pg : Scalar.QComplex := ((-93086383818837005675182 : Int)/10^30,(86486335586661575150 : Int)/10^30)
theorem v1320_pg_checked : Scalar.distance (sourceCoefficient 14 68 1 2) v1320_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1320_mb : Scalar.QComplex := ((-773229814792963118822276 : Int)/10^30,(-431476773461019950482742147 : Int)/10^30)
theorem v1320_mb_checked : Scalar.distance (sourceCoefficient 14 68 3 1) v1320_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1320_mg : Scalar.QComplex := ((-93086274524709640686304 : Int)/10^30,(166815660164406599587 : Int)/10^30)
theorem v1320_mg_checked : Scalar.distance (sourceCoefficient 14 68 3 2) v1320_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1320_upper : Scalar.QComplex := ((999996475469742984517636366825 : Int)/10^30,(-2655004348719118785625252741 : Int)/10^30)
theorem v1320_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 68 5) 1) 14) v1320_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1320 : Material (14 : Basis) (68 : Basis) where
  plus := ![v1320_pa,v1320_pb,v1320_pg]
  minus := ![(Primitive.Addresses.material1320 1).one,v1320_mb,v1320_mg]
  upper := v1320_upper
  lower := (Primitive.Addresses.material1320 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1320_pa_checked.trans (by decide +kernel)
    · exact v1320_pb_checked.trans (by decide +kernel)
    · exact v1320_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 68 Primitive.Addresses.material1320
    · exact v1320_mb_checked.trans (by decide +kernel)
    · exact v1320_mg_checked.trans (by decide +kernel)
  upper_error := v1320_upper_checked
  lower_error := reuse_lower_error 14 68 Primitive.Addresses.material1320

def v1321_pa : Scalar.QComplex := ((999999548053683361474204360556 : Int)/10^30,(-950732574923978539991905880 : Int)/10^30)
theorem v1321_pa_checked : Scalar.distance (sourceCoefficient 14 69 1 0) v1321_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1321_pb : Scalar.QComplex := ((-410219679940370025449030 : Int)/10^30,(-431477268543047655308114686 : Int)/10^30)
theorem v1321_pb_checked : Scalar.distance (sourceCoefficient 14 69 1 1) v1321_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1321_pg : Scalar.QComplex := ((-93086381629494804683506 : Int)/10^30,(88500295294348208670 : Int)/10^30)
theorem v1321_pg_checked : Scalar.distance (sourceCoefficient 14 69 1 2) v1321_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1321_mb : Scalar.QComplex := ((-782564976934697583805158 : Int)/10^30,(-431476753883232911395069902 : Int)/10^30)
theorem v1321_mb_checked : Scalar.distance (sourceCoefficient 14 69 3 1) v1321_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1321_mg : Scalar.QComplex := ((-93086270597411732531315 : Int)/10^30,(168829617232900276287 : Int)/10^30)
theorem v1321_mg_checked : Scalar.distance (sourceCoefficient 14 69 3 2) v1321_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1321_upper : Scalar.QComplex := ((999996417793650200781909115631 : Int)/10^30,(-2676639659609807029418828658 : Int)/10^30)
theorem v1321_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 69 5) 1) 14) v1321_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1321 : Material (14 : Basis) (69 : Basis) where
  plus := ![v1321_pa,v1321_pb,v1321_pg]
  minus := ![(Primitive.Addresses.material1321 1).one,v1321_mb,v1321_mg]
  upper := v1321_upper
  lower := (Primitive.Addresses.material1321 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1321_pa_checked.trans (by decide +kernel)
    · exact v1321_pb_checked.trans (by decide +kernel)
    · exact v1321_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 69 Primitive.Addresses.material1321
    · exact v1321_mb_checked.trans (by decide +kernel)
    · exact v1321_mg_checked.trans (by decide +kernel)
  upper_error := v1321_upper_checked
  lower_error := reuse_lower_error 14 69 Primitive.Addresses.material1321

def v1322_pa : Scalar.QComplex := ((999999534421615139444789403016 : Int)/10^30,(-964964534559627207769233575 : Int)/10^30)
theorem v1322_pa_checked : Scalar.distance (sourceCoefficient 14 70 1 0) v1322_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1322_pb : Scalar.QComplex := ((-416360448005724893782772 : Int)/10^30,(-431477260816959286063551554 : Int)/10^30)
theorem v1322_pb_checked : Scalar.distance (sourceCoefficient 14 70 1 1) v1322_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1322_pg : Scalar.QComplex := ((-93086380161606116764338 : Int)/10^30,(89825097327108495664 : Int)/10^30)
theorem v1322_pg_checked : Scalar.distance (sourceCoefficient 14 70 1 2) v1322_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1322_mb : Scalar.QComplex := ((-788705736046297561887290 : Int)/10^30,(-431476740857941148451960253 : Int)/10^30)
theorem v1322_mb_checked : Scalar.distance (sourceCoefficient 14 70 3 1) v1322_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1322_mg : Scalar.QComplex := ((-93086267986279103770681 : Int)/10^30,(170154417505654393618 : Int)/10^30)
theorem v1322_mg_checked : Scalar.distance (sourceCoefficient 14 70 3 2) v1322_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1322_upper : Scalar.QComplex := ((999996379598531064279697554964 : Int)/10^30,(-2690871574520910563659881687 : Int)/10^30)
theorem v1322_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 70 5) 1) 14) v1322_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1322 : Material (14 : Basis) (70 : Basis) where
  plus := ![v1322_pa,v1322_pb,v1322_pg]
  minus := ![(Primitive.Addresses.material1322 1).one,v1322_mb,v1322_mg]
  upper := v1322_upper
  lower := (Primitive.Addresses.material1322 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1322_pa_checked.trans (by decide +kernel)
    · exact v1322_pb_checked.trans (by decide +kernel)
    · exact v1322_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 70 Primitive.Addresses.material1322
    · exact v1322_mb_checked.trans (by decide +kernel)
    · exact v1322_mg_checked.trans (by decide +kernel)
  upper_error := v1322_upper_checked
  lower_error := reuse_lower_error 14 70 Primitive.Addresses.material1322

def v1323_pa : Scalar.QComplex := ((999999510684838438024117687367 : Int)/10^30,(-989257339469677338922480808 : Int)/10^30)
theorem v1323_pa_checked : Scalar.distance (sourceCoefficient 14 71 1 0) v1323_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1323_pb : Scalar.QComplex := ((-426842242625379696147788 : Int)/10^30,(-431477247359944730304798094 : Int)/10^30)
theorem v1323_pb_checked : Scalar.distance (sourceCoefficient 14 71 1 1) v1323_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1323_pg : Scalar.QComplex := ((-93086377605220322294151 : Int)/10^30,(92086427309895067471 : Int)/10^30)
theorem v1323_pg_checked : Scalar.distance (sourceCoefficient 14 71 1 2) v1323_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1323_mb : Scalar.QComplex := ((-799187515150303705492552 : Int)/10^30,(-431476718355614929097790323 : Int)/10^30)
theorem v1323_mb_checked : Scalar.distance (sourceCoefficient 14 71 3 1) v1323_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1323_mg : Scalar.QComplex := ((-93086263478468332536650 : Int)/10^30,(172415744440398659663 : Int)/10^30)
theorem v1323_mg_checked : Scalar.distance (sourceCoefficient 14 71 3 2) v1323_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1323_upper : Scalar.QComplex := ((999996313934612267299174001120 : Int)/10^30,(-2715164302282158211523964931 : Int)/10^30)
theorem v1323_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 71 5) 1) 14) v1323_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1323 : Material (14 : Basis) (71 : Basis) where
  plus := ![v1323_pa,v1323_pb,v1323_pg]
  minus := ![(Primitive.Addresses.material1323 1).one,v1323_mb,v1323_mg]
  upper := v1323_upper
  lower := (Primitive.Addresses.material1323 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1323_pa_checked.trans (by decide +kernel)
    · exact v1323_pb_checked.trans (by decide +kernel)
    · exact v1323_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 71 Primitive.Addresses.material1323
    · exact v1323_mb_checked.trans (by decide +kernel)
    · exact v1323_mg_checked.trans (by decide +kernel)
  upper_error := v1323_upper_checked
  lower_error := reuse_lower_error 14 71 Primitive.Addresses.material1323

def v1324_pa : Scalar.QComplex := ((999999484257923153049170062035 : Int)/10^30,(-1015619952395585732503070462 : Int)/10^30)
theorem v1324_pa_checked : Scalar.distance (sourceCoefficient 14 72 1 0) v1324_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1324_pb : Scalar.QComplex := ((-438217112208662522598244 : Int)/10^30,(-431477232372225713426096473 : Int)/10^30)
theorem v1324_pb_checked : Scalar.distance (sourceCoefficient 14 72 1 1) v1324_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1324_pg : Scalar.QComplex := ((-93086374758510678871529 : Int)/10^30,(94540428259393085511 : Int)/10^30)
theorem v1324_pg_checked : Scalar.distance (sourceCoefficient 14 72 1 2) v1324_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1324_mb : Scalar.QComplex := ((-810562367564476239105602 : Int)/10^30,(-431476693551901347567143559 : Int)/10^30)
theorem v1324_mb_checked : Scalar.distance (sourceCoefficient 14 72 3 1) v1324_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1324_mg : Scalar.QComplex := ((-93086258514067453757258 : Int)/10^30,(174869742019577759590 : Int)/10^30)
theorem v1324_mg_checked : Scalar.distance (sourceCoefficient 14 72 3 2) v1324_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1324_upper : Scalar.QComplex := ((999996242008258029554835986364 : Int)/10^30,(-2741526830333593071174700735 : Int)/10^30)
theorem v1324_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 72 5) 1) 14) v1324_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1324 : Material (14 : Basis) (72 : Basis) where
  plus := ![v1324_pa,v1324_pb,v1324_pg]
  minus := ![(Primitive.Addresses.material1324 1).one,v1324_mb,v1324_mg]
  upper := v1324_upper
  lower := (Primitive.Addresses.material1324 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1324_pa_checked.trans (by decide +kernel)
    · exact v1324_pb_checked.trans (by decide +kernel)
    · exact v1324_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 72 Primitive.Addresses.material1324
    · exact v1324_mb_checked.trans (by decide +kernel)
    · exact v1324_mg_checked.trans (by decide +kernel)
  upper_error := v1324_upper_checked
  lower_error := reuse_lower_error 14 72 Primitive.Addresses.material1324

def v1325_pa : Scalar.QComplex := ((999999474616029705032345978857 : Int)/10^30,(-1025069590106749320857053844 : Int)/10^30)
theorem v1325_pa_checked : Scalar.distance (sourceCoefficient 14 73 1 0) v1325_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1325_pb : Scalar.QComplex := ((-442294416495796514932969 : Int)/10^30,(-431477226902555987577612282 : Int)/10^30)
theorem v1325_pb_checked : Scalar.distance (sourceCoefficient 14 73 1 1) v1325_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1325_pg : Scalar.QComplex := ((-93086373719736045593261 : Int)/10^30,(95420061085584049273 : Int)/10^30)
theorem v1325_pg_checked : Scalar.distance (sourceCoefficient 14 73 1 2) v1325_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1325_mb : Scalar.QComplex := ((-814639665613364874701399 : Int)/10^30,(-431476684563703693498281237 : Int)/10^30)
theorem v1325_mb_checked : Scalar.distance (sourceCoefficient 14 73 3 1) v1325_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1325_mg : Scalar.QComplex := ((-93086256716209695451291 : Int)/10^30,(175749373621825497108 : Int)/10^30)
theorem v1325_mg_checked : Scalar.distance (sourceCoefficient 14 73 3 2) v1325_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1325_upper : Scalar.QComplex := ((999996216057161516973907338783 : Int)/10^30,(-2750976437329597935635336665 : Int)/10^30)
theorem v1325_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 73 5) 1) 14) v1325_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1325 : Material (14 : Basis) (73 : Basis) where
  plus := ![v1325_pa,v1325_pb,v1325_pg]
  minus := ![(Primitive.Addresses.material1325 1).one,v1325_mb,v1325_mg]
  upper := v1325_upper
  lower := (Primitive.Addresses.material1325 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1325_pa_checked.trans (by decide +kernel)
    · exact v1325_pb_checked.trans (by decide +kernel)
    · exact v1325_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 73 Primitive.Addresses.material1325
    · exact v1325_mb_checked.trans (by decide +kernel)
    · exact v1325_mg_checked.trans (by decide +kernel)
  upper_error := v1325_upper_checked
  lower_error := reuse_lower_error 14 73 Primitive.Addresses.material1325

def v1326_pa : Scalar.QComplex := ((999999463659757603092845718370 : Int)/10^30,(-1035702755201973330248284015 : Int)/10^30)
theorem v1326_pa_checked : Scalar.distance (sourceCoefficient 14 74 1 0) v1326_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1326_pb : Scalar.QComplex := ((-446882385952808667407192 : Int)/10^30,(-431477220686406855585961487 : Int)/10^30)
theorem v1326_pb_checked : Scalar.distance (sourceCoefficient 14 74 1 1) v1326_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1326_pg : Scalar.QComplex := ((-93086372539263728921159 : Int)/10^30,(96409864219162699136 : Int)/10^30)
theorem v1326_pg_checked : Scalar.distance (sourceCoefficient 14 74 1 2) v1326_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1326_mb : Scalar.QComplex := ((-819227627997809581822705 : Int)/10^30,(-431476674388345869135268349 : Int)/10^30)
theorem v1326_mb_checked : Scalar.distance (sourceCoefficient 14 74 3 1) v1326_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1326_mg : Scalar.QComplex := ((-93086254681582293122891 : Int)/10^30,(176739175368160761314 : Int)/10^30)
theorem v1326_mg_checked : Scalar.distance (sourceCoefficient 14 74 3 2) v1326_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1326_upper : Scalar.QComplex := ((999996186749027411960186251244 : Int)/10^30,(-2761609567678439892297357461 : Int)/10^30)
theorem v1326_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 74 5) 1) 14) v1326_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1326 : Material (14 : Basis) (74 : Basis) where
  plus := ![v1326_pa,v1326_pb,v1326_pg]
  minus := ![(Primitive.Addresses.material1326 1).one,v1326_mb,v1326_mg]
  upper := v1326_upper
  lower := (Primitive.Addresses.material1326 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1326_pa_checked.trans (by decide +kernel)
    · exact v1326_pb_checked.trans (by decide +kernel)
    · exact v1326_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 74 Primitive.Addresses.material1326
    · exact v1326_mb_checked.trans (by decide +kernel)
    · exact v1326_mg_checked.trans (by decide +kernel)
  upper_error := v1326_upper_checked
  lower_error := reuse_lower_error 14 74 Primitive.Addresses.material1326

def v1327_pa : Scalar.QComplex := ((999999448205943776587348602289 : Int)/10^30,(-1050517876083098749336196513 : Int)/10^30)
theorem v1327_pa_checked : Scalar.distance (sourceCoefficient 14 75 1 0) v1327_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1327_pb : Scalar.QComplex := ((-453274774355667751261938 : Int)/10^30,(-431477211917035678428140624 : Int)/10^30)
theorem v1327_pb_checked : Scalar.distance (sourceCoefficient 14 75 1 1) v1327_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1327_pg : Scalar.QComplex := ((-93086370874046866889945 : Int)/10^30,(97788950582249034740 : Int)/10^30)
theorem v1327_pg_checked : Scalar.distance (sourceCoefficient 14 75 1 2) v1327_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1327_mb : Scalar.QComplex := ((-825620006452917948639766 : Int)/10^30,(-431476660102634668033949554 : Int)/10^30)
theorem v1327_mb_checked : Scalar.distance (sourceCoefficient 14 75 3 1) v1327_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1327_mg : Scalar.QComplex := ((-93086251826276631528609 : Int)/10^30,(178118259780743063230 : Int)/10^30)
theorem v1327_mg_checked : Scalar.distance (sourceCoefficient 14 75 3 2) v1327_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1327_upper : Scalar.QComplex := ((999996145725681978540026843872 : Int)/10^30,(-2776424639822302359787858062 : Int)/10^30)
theorem v1327_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 75 5) 1) 14) v1327_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1327 : Material (14 : Basis) (75 : Basis) where
  plus := ![v1327_pa,v1327_pb,v1327_pg]
  minus := ![(Primitive.Addresses.material1327 1).one,v1327_mb,v1327_mg]
  upper := v1327_upper
  lower := (Primitive.Addresses.material1327 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1327_pa_checked.trans (by decide +kernel)
    · exact v1327_pb_checked.trans (by decide +kernel)
    · exact v1327_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 75 Primitive.Addresses.material1327
    · exact v1327_mb_checked.trans (by decide +kernel)
    · exact v1327_mg_checked.trans (by decide +kernel)
  upper_error := v1327_upper_checked
  lower_error := reuse_lower_error 14 75 Primitive.Addresses.material1327

def v1328_pa : Scalar.QComplex := ((999999435070557558203643736754 : Int)/10^30,(-1062948054110979486733824025 : Int)/10^30)
theorem v1328_pa_checked : Scalar.distance (sourceCoefficient 14 76 1 0) v1328_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1328_pb : Scalar.QComplex := ((-458638113974241894838511 : Int)/10^30,(-431477204461943317245543645 : Int)/10^30)
theorem v1328_pb_checked : Scalar.distance (sourceCoefficient 14 76 1 1) v1328_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1328_pg : Scalar.QComplex := ((-93086369458507527928577 : Int)/10^30,(98946031177702513109 : Int)/10^30)
theorem v1328_pg_checked : Scalar.distance (sourceCoefficient 14 76 1 2) v1328_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1328_mb : Scalar.QComplex := ((-830983337641066692686792 : Int)/10^30,(-431476648019224547742913241 : Int)/10^30)
theorem v1328_mb_checked : Scalar.distance (sourceCoefficient 14 76 3 1) v1328_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1328_mg : Scalar.QComplex := ((-93086249412229378736373 : Int)/10^30,(179275338723815858718 : Int)/10^30)
theorem v1328_mg_checked : Scalar.distance (sourceCoefficient 14 76 3 2) v1328_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1328_upper : Scalar.QComplex := ((999996111136955704590867379666 : Int)/10^30,(-2788854776666408095937246839 : Int)/10^30)
theorem v1328_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 76 5) 1) 14) v1328_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1328 : Material (14 : Basis) (76 : Basis) where
  plus := ![v1328_pa,v1328_pb,v1328_pg]
  minus := ![(Primitive.Addresses.material1328 1).one,v1328_mb,v1328_mg]
  upper := v1328_upper
  lower := (Primitive.Addresses.material1328 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1328_pa_checked.trans (by decide +kernel)
    · exact v1328_pb_checked.trans (by decide +kernel)
    · exact v1328_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 76 Primitive.Addresses.material1328
    · exact v1328_mb_checked.trans (by decide +kernel)
    · exact v1328_mg_checked.trans (by decide +kernel)
  upper_error := v1328_upper_checked
  lower_error := reuse_lower_error 14 76 Primitive.Addresses.material1328

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
