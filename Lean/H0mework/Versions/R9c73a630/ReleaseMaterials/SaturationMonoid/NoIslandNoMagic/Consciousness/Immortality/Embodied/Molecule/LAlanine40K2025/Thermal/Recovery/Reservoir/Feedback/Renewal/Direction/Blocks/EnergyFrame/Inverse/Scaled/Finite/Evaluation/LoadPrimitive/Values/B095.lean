import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B063
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B064

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1521_pa : Scalar.QComplex := ((999999949985216309986405791370 : Int)/10^30,(-316274508739715855176084057 : Int)/10^30)
theorem v1521_pa_checked : Scalar.distance (sourceCoefficient 17 26 1 0) v1521_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1521_pb : Scalar.QComplex := ((-136465340193382903234133 : Int)/10^30,(-431477496912042265070701367 : Int)/10^30)
theorem v1521_pb_checked : Scalar.distance (sourceCoefficient 17 26 1 1) v1521_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1521_pg : Scalar.QComplex := ((-93086424970703627928890 : Int)/10^30,(29440864800424193430 : Int)/10^30)
theorem v1521_pg_checked : Scalar.distance (sourceCoefficient 17 26 1 2) v1521_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1521_mb : Scalar.QComplex := ((-508810936191119331303713 : Int)/10^30,(-431477218489808252821910901 : Int)/10^30)
theorem v1521_mb_checked : Scalar.distance (sourceCoefficient 17 26 3 1) v1521_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1521_mg : Scalar.QComplex := ((-93086364904232996112382 : Int)/10^30,(109770246131012582126 : Int)/10^30)
theorem v1521_mg_checked : Scalar.distance (sourceCoefficient 17 26 3 2) v1521_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1521_upper : Scalar.QComplex := ((999997914741649167378324733396 : Int)/10^30,(-2042183232073668171549916563 : Int)/10^30)
theorem v1521_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 26 5) 1) 14) v1521_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1521 : Material (17 : Basis) (26 : Basis) where
  plus := ![v1521_pa,v1521_pb,v1521_pg]
  minus := ![(Primitive.Addresses.material1521 1).one,v1521_mb,v1521_mg]
  upper := v1521_upper
  lower := (Primitive.Addresses.material1521 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1521_pa_checked.trans (by decide +kernel)
    · exact v1521_pb_checked.trans (by decide +kernel)
    · exact v1521_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 26 Primitive.Addresses.material1521
    · exact v1521_mb_checked.trans (by decide +kernel)
    · exact v1521_mg_checked.trans (by decide +kernel)
  upper_error := v1521_upper_checked
  lower_error := reuse_lower_error 17 26 Primitive.Addresses.material1521

def v1522_pa : Scalar.QComplex := ((999999948376810379711301621275 : Int)/10^30,(-321319741963707686196030523 : Int)/10^30)
theorem v1522_pa_checked : Scalar.distance (sourceCoefficient 17 27 1 0) v1522_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1522_pb : Scalar.QComplex := ((-138642244860951772115550 : Int)/10^30,(-431477496080698934966940685 : Int)/10^30)
theorem v1522_pb_checked : Scalar.distance (sourceCoefficient 17 27 1 1) v1522_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1522_pg : Scalar.QComplex := ((-93086424806166751144661 : Int)/10^30,(29910507543117381284 : Int)/10^30)
theorem v1522_pg_checked : Scalar.distance (sourceCoefficient 17 27 1 2) v1522_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1522_mb : Scalar.QComplex := ((-510987839330715251425171 : Int)/10^30,(-431477215779894548299989938 : Int)/10^30)
theorem v1522_mb_checked : Scalar.distance (sourceCoefficient 17 27 3 1) v1522_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1522_mg : Scalar.QComplex := ((-93086364334415645572465 : Int)/10^30,(110239888556848398943 : Int)/10^30)
theorem v1522_mg_checked : Scalar.distance (sourceCoefficient 17 27 3 2) v1522_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1522_upper : Scalar.QComplex := ((999997904425630788007741218651 : Int)/10^30,(-2047228455007415047951596134 : Int)/10^30)
theorem v1522_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 27 5) 1) 14) v1522_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1522 : Material (17 : Basis) (27 : Basis) where
  plus := ![v1522_pa,v1522_pb,v1522_pg]
  minus := ![(Primitive.Addresses.material1522 1).one,v1522_mb,v1522_mg]
  upper := v1522_upper
  lower := (Primitive.Addresses.material1522 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1522_pa_checked.trans (by decide +kernel)
    · exact v1522_pb_checked.trans (by decide +kernel)
    · exact v1522_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 27 Primitive.Addresses.material1522
    · exact v1522_mb_checked.trans (by decide +kernel)
    · exact v1522_mg_checked.trans (by decide +kernel)
  upper_error := v1522_upper_checked
  lower_error := reuse_lower_error 17 27 Primitive.Addresses.material1522

def v1523_pa : Scalar.QComplex := ((999999946169836805478270728401 : Int)/10^30,(-328116326157899355744682578 : Int)/10^30)
theorem v1523_pa_checked : Scalar.distance (sourceCoefficient 17 28 1 0) v1523_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1523_pb : Scalar.QComplex := ((-141574818079741118700172 : Int)/10^30,(-431477494937620198648701229 : Int)/10^30)
theorem v1523_pb_checked : Scalar.distance (sourceCoefficient 17 28 1 1) v1523_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1523_pg : Scalar.QComplex := ((-93086424580143905256236 : Int)/10^30,(30543177292555415351 : Int)/10^30)
theorem v1523_pg_checked : Scalar.distance (sourceCoefficient 17 28 1 2) v1523_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1523_mb : Scalar.QComplex := ((-513920410471148096349969 : Int)/10^30,(-431477212106137627981800404 : Int)/10^30)
theorem v1523_mb_checked : Scalar.distance (sourceCoefficient 17 28 3 1) v1523_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1523_mg : Scalar.QComplex := ((-93086363562427384465406 : Int)/10^30,(110872557875667034548 : Int)/10^30)
theorem v1523_mg_checked : Scalar.distance (sourceCoefficient 17 28 3 2) v1523_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1523_upper : Scalar.QComplex := ((999997890488372762929406437603 : Int)/10^30,(-2054025025269856769066992128 : Int)/10^30)
theorem v1523_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 28 5) 1) 14) v1523_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1523 : Material (17 : Basis) (28 : Basis) where
  plus := ![v1523_pa,v1523_pb,v1523_pg]
  minus := ![(Primitive.Addresses.material1523 1).one,v1523_mb,v1523_mg]
  upper := v1523_upper
  lower := (Primitive.Addresses.material1523 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1523_pa_checked.trans (by decide +kernel)
    · exact v1523_pb_checked.trans (by decide +kernel)
    · exact v1523_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 28 Primitive.Addresses.material1523
    · exact v1523_mb_checked.trans (by decide +kernel)
    · exact v1523_mg_checked.trans (by decide +kernel)
  upper_error := v1523_upper_checked
  lower_error := reuse_lower_error 17 28 Primitive.Addresses.material1523

def v1524_pa : Scalar.QComplex := ((999999941558455862921000434589 : Int)/10^30,(-341881682543455255536805340 : Int)/10^30)
theorem v1524_pa_checked : Scalar.distance (sourceCoefficient 17 29 1 0) v1524_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1524_pb : Scalar.QComplex := ((-147514259750538688736151 : Int)/10^30,(-431477492541085765774408172 : Int)/10^30)
theorem v1524_pb_checked : Scalar.distance (sourceCoefficient 17 29 1 1) v1524_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1524_pg : Scalar.QComplex := ((-93086424107002715129760 : Int)/10^30,(31824545155531302977 : Int)/10^30)
theorem v1524_pg_checked : Scalar.distance (sourceCoefficient 17 29 1 2) v1524_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1524_mb : Scalar.QComplex := ((-519859847862318806787531 : Int)/10^30,(-431477204584133428071193109 : Int)/10^30)
theorem v1524_mb_checked : Scalar.distance (sourceCoefficient 17 29 3 1) v1524_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1524_mg : Scalar.QComplex := ((-93086361983523615429055 : Int)/10^30,(112153924853231567792 : Int)/10^30)
theorem v1524_mg_checked : Scalar.distance (sourceCoefficient 17 29 3 2) v1524_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1524_upper : Scalar.QComplex := ((999997862119242350389213416237 : Int)/10^30,(-2067790353194706159279524863 : Int)/10^30)
theorem v1524_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 29 5) 1) 14) v1524_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1524 : Material (17 : Basis) (29 : Basis) where
  plus := ![v1524_pa,v1524_pb,v1524_pg]
  minus := ![(Primitive.Addresses.material1524 1).one,v1524_mb,v1524_mg]
  upper := v1524_upper
  lower := (Primitive.Addresses.material1524 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1524_pa_checked.trans (by decide +kernel)
    · exact v1524_pb_checked.trans (by decide +kernel)
    · exact v1524_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 29 Primitive.Addresses.material1524
    · exact v1524_mb_checked.trans (by decide +kernel)
    · exact v1524_mg_checked.trans (by decide +kernel)
  upper_error := v1524_upper_checked
  lower_error := reuse_lower_error 17 29 Primitive.Addresses.material1524

def v1525_pa : Scalar.QComplex := ((999999939761494378876226041936 : Int)/10^30,(-347097979846570107418121882 : Int)/10^30)
theorem v1525_pa_checked : Scalar.distance (sourceCoefficient 17 30 1 0) v1525_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1525_pb : Scalar.QComplex := ((-149764974706789050592190 : Int)/10^30,(-431477491604452221410758873 : Int)/10^30)
theorem v1525_pb_checked : Scalar.distance (sourceCoefficient 17 30 1 1) v1525_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1525_pg : Scalar.QComplex := ((-93086423922332266004382 : Int)/10^30,(32310111640895808095 : Int)/10^30)
theorem v1525_pg_checked : Scalar.distance (sourceCoefficient 17 30 1 2) v1525_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1525_mb : Scalar.QComplex := ((-522110561172252563299586 : Int)/10^30,(-431477201705234593653612556 : Int)/10^30)
theorem v1525_mb_checked : Scalar.distance (sourceCoefficient 17 30 3 1) v1525_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1525_mg : Scalar.QComplex := ((-93086361379831227298038 : Int)/10^30,(112639490998435198578 : Int)/10^30)
theorem v1525_mg_checked : Scalar.distance (sourceCoefficient 17 30 3 2) v1525_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1525_upper : Scalar.QComplex := ((999997851319427616326005454450 : Int)/10^30,(-2073006639627366425106902631 : Int)/10^30)
theorem v1525_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 30 5) 1) 14) v1525_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1525 : Material (17 : Basis) (30 : Basis) where
  plus := ![v1525_pa,v1525_pb,v1525_pg]
  minus := ![(Primitive.Addresses.material1525 1).one,v1525_mb,v1525_mg]
  upper := v1525_upper
  lower := (Primitive.Addresses.material1525 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1525_pa_checked.trans (by decide +kernel)
    · exact v1525_pb_checked.trans (by decide +kernel)
    · exact v1525_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 30 Primitive.Addresses.material1525
    · exact v1525_mb_checked.trans (by decide +kernel)
    · exact v1525_mg_checked.trans (by decide +kernel)
  upper_error := v1525_upper_checked
  lower_error := reuse_lower_error 17 30 Primitive.Addresses.material1525

def v1526_pa : Scalar.QComplex := ((999999935848867893479214603740 : Int)/10^30,(-358193048645103971738835744 : Int)/10^30)
theorem v1526_pa_checked : Scalar.distance (sourceCoefficient 17 31 1 0) v1526_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1526_pb : Scalar.QComplex := ((-154552247321996345125510 : Int)/10^30,(-431477489560173897013431103 : Int)/10^30)
theorem v1526_pb_checked : Scalar.distance (sourceCoefficient 17 31 1 1) v1526_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1526_pg : Scalar.QComplex := ((-93086423519711004600091 : Int)/10^30,(33342911966980144754 : Int)/10^30)
theorem v1526_pg_checked : Scalar.distance (sourceCoefficient 17 31 1 2) v1526_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1526_mb : Scalar.QComplex := ((-526897830240819350947317 : Int)/10^30,(-431477195529756374265379408 : Int)/10^30)
theorem v1526_mb_checked : Scalar.distance (sourceCoefficient 17 31 3 1) v1526_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1526_mg : Scalar.QComplex := ((-93086360085949949997208 : Int)/10^30,(113672290592516757326 : Int)/10^30)
theorem v1526_mg_checked : Scalar.distance (sourceCoefficient 17 31 3 2) v1526_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1526_upper : Scalar.QComplex := ((999997828257724748835853969898 : Int)/10^30,(-2084101685148260269252411663 : Int)/10^30)
theorem v1526_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 31 5) 1) 14) v1526_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1526 : Material (17 : Basis) (31 : Basis) where
  plus := ![v1526_pa,v1526_pb,v1526_pg]
  minus := ![(Primitive.Addresses.material1526 1).one,v1526_mb,v1526_mg]
  upper := v1526_upper
  lower := (Primitive.Addresses.material1526 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1526_pa_checked.trans (by decide +kernel)
    · exact v1526_pb_checked.trans (by decide +kernel)
    · exact v1526_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 31 Primitive.Addresses.material1526
    · exact v1526_mb_checked.trans (by decide +kernel)
    · exact v1526_mg_checked.trans (by decide +kernel)
  upper_error := v1526_upper_checked
  lower_error := reuse_lower_error 17 31 Primitive.Addresses.material1526

def v1527_pa : Scalar.QComplex := ((999999934126700114383697632926 : Int)/10^30,(-362969138401518878930959119 : Int)/10^30)
theorem v1527_pa_checked : Scalar.distance (sourceCoefficient 17 32 1 0) v1527_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1527_pb : Scalar.QComplex := ((-156613022614596166790654 : Int)/10^30,(-431477488658369639615195802 : Int)/10^30)
theorem v1527_pb_checked : Scalar.distance (sourceCoefficient 17 32 1 1) v1527_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1527_pg : Scalar.QComplex := ((-93086423342278708729099 : Int)/10^30,(33787501103120130759 : Int)/10^30)
theorem v1527_pg_checked : Scalar.distance (sourceCoefficient 17 32 1 2) v1527_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1527_mb : Scalar.QComplex := ((-528958603987881890715334 : Int)/10^30,(-431477192849596189010203279 : Int)/10^30)
theorem v1527_mb_checked : Scalar.distance (sourceCoefficient 17 32 3 1) v1527_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1527_mg : Scalar.QComplex := ((-93086359524857319254943 : Int)/10^30,(114116879409999809135 : Int)/10^30)
theorem v1527_mg_checked : Scalar.distance (sourceCoefficient 17 32 3 2) v1527_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1527_upper : Scalar.QComplex := ((999997818292461898612891282522 : Int)/10^30,(-2088877764818945170299778893 : Int)/10^30)
theorem v1527_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 32 5) 1) 14) v1527_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1527 : Material (17 : Basis) (32 : Basis) where
  plus := ![v1527_pa,v1527_pb,v1527_pg]
  minus := ![(Primitive.Addresses.material1527 1).one,v1527_mb,v1527_mg]
  upper := v1527_upper
  lower := (Primitive.Addresses.material1527 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1527_pa_checked.trans (by decide +kernel)
    · exact v1527_pb_checked.trans (by decide +kernel)
    · exact v1527_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 32 Primitive.Addresses.material1527
    · exact v1527_mb_checked.trans (by decide +kernel)
    · exact v1527_mg_checked.trans (by decide +kernel)
  upper_error := v1527_upper_checked
  lower_error := reuse_lower_error 17 32 Primitive.Addresses.material1527

def v1528_pa : Scalar.QComplex := ((999999931688582898645113026507 : Int)/10^30,(-369625255544396029236879772 : Int)/10^30)
theorem v1528_pa_checked : Scalar.distance (sourceCoefficient 17 33 1 0) v1528_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1528_pb : Scalar.QComplex := ((-159484987429019805220951 : Int)/10^30,(-431477487379696705838528082 : Int)/10^30)
theorem v1528_pb_checked : Scalar.distance (sourceCoefficient 17 33 1 1) v1528_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1528_pg : Scalar.QComplex := ((-93086423090871231940438 : Int)/10^30,(34407095273074482830 : Int)/10^30)
theorem v1528_pg_checked : Scalar.distance (sourceCoefficient 17 33 1 2) v1528_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1528_mb : Scalar.QComplex := ((-531830566629504620901408 : Int)/10^30,(-431477189092547444987906934 : Int)/10^30)
theorem v1528_mb_checked : Scalar.distance (sourceCoefficient 17 33 3 1) v1528_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1528_mg : Scalar.QComplex := ((-93086358738768072891684 : Int)/10^30,(114736473132297605384 : Int)/10^30)
theorem v1528_mg_checked : Scalar.distance (sourceCoefficient 17 33 3 2) v1528_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1528_upper : Scalar.QComplex := ((999997804366493963787813141379 : Int)/10^30,(-2095533867840348588635250652 : Int)/10^30)
theorem v1528_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 33 5) 1) 14) v1528_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1528 : Material (17 : Basis) (33 : Basis) where
  plus := ![v1528_pa,v1528_pb,v1528_pg]
  minus := ![(Primitive.Addresses.material1528 1).one,v1528_mb,v1528_mg]
  upper := v1528_upper
  lower := (Primitive.Addresses.material1528 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1528_pa_checked.trans (by decide +kernel)
    · exact v1528_pb_checked.trans (by decide +kernel)
    · exact v1528_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 33 Primitive.Addresses.material1528
    · exact v1528_mb_checked.trans (by decide +kernel)
    · exact v1528_mg_checked.trans (by decide +kernel)
  upper_error := v1528_upper_checked
  lower_error := reuse_lower_error 17 33 Primitive.Addresses.material1528

def v1529_pa : Scalar.QComplex := ((999999925582178873702843561218 : Int)/10^30,(-385792219613851481430722619 : Int)/10^30)
theorem v1529_pa_checked : Scalar.distance (sourceCoefficient 17 34 1 0) v1529_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1529_pb : Scalar.QComplex := ((-166460668718138396140089 : Int)/10^30,(-431477484167805452938511217 : Int)/10^30)
theorem v1529_pb_checked : Scalar.distance (sourceCoefficient 17 34 1 1) v1529_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1529_pg : Scalar.QComplex := ((-93086422460194822289935 : Int)/10^30,(35912020209325534213 : Int)/10^30)
theorem v1529_pg_checked : Scalar.distance (sourceCoefficient 17 34 1 2) v1529_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1529_mb : Scalar.QComplex := ((-538806242549540770456876 : Int)/10^30,(-431477179860958608535061336 : Int)/10^30)
theorem v1529_mb_checked : Scalar.distance (sourceCoefficient 17 34 3 1) v1529_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1529_mg : Scalar.QComplex := ((-93086356809409457389218 : Int)/10^30,(116241396963950987616 : Int)/10^30)
theorem v1529_mg_checked : Scalar.distance (sourceCoefficient 17 34 3 2) v1529_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1529_upper : Scalar.QComplex := ((999997770357385705260416520517 : Int)/10^30,(-2111700797291910785975066241 : Int)/10^30)
theorem v1529_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 34 5) 1) 14) v1529_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1529 : Material (17 : Basis) (34 : Basis) where
  plus := ![v1529_pa,v1529_pb,v1529_pg]
  minus := ![(Primitive.Addresses.material1529 1).one,v1529_mb,v1529_mg]
  upper := v1529_upper
  lower := (Primitive.Addresses.material1529 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1529_pa_checked.trans (by decide +kernel)
    · exact v1529_pb_checked.trans (by decide +kernel)
    · exact v1529_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 34 Primitive.Addresses.material1529
    · exact v1529_mb_checked.trans (by decide +kernel)
    · exact v1529_mg_checked.trans (by decide +kernel)
  upper_error := v1529_upper_checked
  lower_error := reuse_lower_error 17 34 Primitive.Addresses.material1529

def v1530_pa : Scalar.QComplex := ((999999904448045969089649985509 : Int)/10^30,(-437154319356042484595710736 : Int)/10^30)
theorem v1530_pa_checked : Scalar.distance (sourceCoefficient 17 35 1 0) v1530_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1530_pb : Scalar.QComplex := ((-188622259035139897099966 : Int)/10^30,(-431477472965994328986424880 : Int)/10^30)
theorem v1530_pb_checked : Scalar.distance (sourceCoefficient 17 35 1 1) v1530_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1530_pg : Scalar.QComplex := ((-93086420268211853391955 : Int)/10^30,(40693134581949195420 : Int)/10^30)
theorem v1530_pg_checked : Scalar.distance (sourceCoefficient 17 35 1 2) v1530_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1530_mb : Scalar.QComplex := ((-560967814948110872558606 : Int)/10^30,(-431477149534697332932794656 : Int)/10^30)
theorem v1530_mb_checked : Scalar.distance (sourceCoefficient 17 35 3 1) v1530_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1530_mg : Scalar.QComplex := ((-93086350491540934490248 : Int)/10^30,(121022507664764681263 : Int)/10^30)
theorem v1530_mg_checked : Scalar.distance (sourceCoefficient 17 35 3 2) v1530_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1530_upper : Scalar.QComplex := ((999997660576959655724258242575 : Int)/10^30,(-2163062784060691519404450364 : Int)/10^30)
theorem v1530_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 35 5) 1) 14) v1530_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1530 : Material (17 : Basis) (35 : Basis) where
  plus := ![v1530_pa,v1530_pb,v1530_pg]
  minus := ![(Primitive.Addresses.material1530 1).one,v1530_mb,v1530_mg]
  upper := v1530_upper
  lower := (Primitive.Addresses.material1530 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1530_pa_checked.trans (by decide +kernel)
    · exact v1530_pb_checked.trans (by decide +kernel)
    · exact v1530_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 35 Primitive.Addresses.material1530
    · exact v1530_mb_checked.trans (by decide +kernel)
    · exact v1530_mg_checked.trans (by decide +kernel)
  upper_error := v1530_upper_checked
  lower_error := reuse_lower_error 17 35 Primitive.Addresses.material1530

def v1531_pa : Scalar.QComplex := ((999999897259893285127020286118 : Int)/10^30,(-453299242084317224202602506 : Int)/10^30)
theorem v1531_pa_checked : Scalar.distance (sourceCoefficient 17 36 1 0) v1531_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1531_pb : Scalar.QComplex := ((-195588429828480533638963 : Int)/10^30,(-431477469131358923303267413 : Int)/10^30)
theorem v1531_pb_checked : Scalar.distance (sourceCoefficient 17 36 1 1) v1531_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1531_pg : Scalar.QComplex := ((-93086419520012354464441 : Int)/10^30,(42196007751986731995 : Int)/10^30)
theorem v1531_pg_checked : Scalar.distance (sourceCoefficient 17 36 1 2) v1531_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1531_mb : Scalar.QComplex := ((-567933979838510103466820 : Int)/10^30,(-431477139688571705092462753 : Int)/10^30)
theorem v1531_mb_checked : Scalar.distance (sourceCoefficient 17 36 3 1) v1531_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1531_mg : Scalar.QComplex := ((-93086348446429855304131 : Int)/10^30,(122525379629551382016 : Int)/10^30)
theorem v1531_mg_checked : Scalar.distance (sourceCoefficient 17 36 3 2) v1531_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1531_upper : Scalar.QComplex := ((999997625524145704617115707075 : Int)/10^30,(-2179207670336900942690785099 : Int)/10^30)
theorem v1531_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 36 5) 1) 14) v1531_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1531 : Material (17 : Basis) (36 : Basis) where
  plus := ![v1531_pa,v1531_pb,v1531_pg]
  minus := ![(Primitive.Addresses.material1531 1).one,v1531_mb,v1531_mg]
  upper := v1531_upper
  lower := (Primitive.Addresses.material1531 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1531_pa_checked.trans (by decide +kernel)
    · exact v1531_pb_checked.trans (by decide +kernel)
    · exact v1531_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 36 Primitive.Addresses.material1531
    · exact v1531_mb_checked.trans (by decide +kernel)
    · exact v1531_mg_checked.trans (by decide +kernel)
  upper_error := v1531_upper_checked
  lower_error := reuse_lower_error 17 36 Primitive.Addresses.material1531

def v1532_pa : Scalar.QComplex := ((999999894111058542411255315740 : Int)/10^30,(-460193298194041029170108205 : Int)/10^30)
theorem v1532_pa_checked : Scalar.distance (sourceCoefficient 17 37 1 0) v1532_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1532_pb : Scalar.QComplex := ((-198563059867049739855049 : Int)/10^30,(-431477467448239948305291908 : Int)/10^30)
theorem v1532_pb_checked : Scalar.distance (sourceCoefficient 17 37 1 1) v1532_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1532_pg : Scalar.QComplex := ((-93086419191898453227246 : Int)/10^30,(42837750801036915399 : Int)/10^30)
theorem v1532_pg_checked : Scalar.distance (sourceCoefficient 17 37 1 2) v1532_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1532_mb : Scalar.QComplex := ((-570908607317032728456267 : Int)/10^30,(-431477135438481605875028259 : Int)/10^30)
theorem v1532_mb_checked : Scalar.distance (sourceCoefficient 17 37 3 1) v1532_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1532_mg : Scalar.QComplex := ((-93086347564520727942426 : Int)/10^30,(123167122156503780087 : Int)/10^30)
theorem v1532_mg_checked : Scalar.distance (sourceCoefficient 17 37 3 2) v1532_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1532_upper : Scalar.QComplex := ((999997610476800230222255392636 : Int)/10^30,(-2186101710744134899071972113 : Int)/10^30)
theorem v1532_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 37 5) 1) 14) v1532_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1532 : Material (17 : Basis) (37 : Basis) where
  plus := ![v1532_pa,v1532_pb,v1532_pg]
  minus := ![(Primitive.Addresses.material1532 1).one,v1532_mb,v1532_mg]
  upper := v1532_upper
  lower := (Primitive.Addresses.material1532 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1532_pa_checked.trans (by decide +kernel)
    · exact v1532_pb_checked.trans (by decide +kernel)
    · exact v1532_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 37 Primitive.Addresses.material1532
    · exact v1532_mb_checked.trans (by decide +kernel)
    · exact v1532_mg_checked.trans (by decide +kernel)
  upper_error := v1532_upper_checked
  lower_error := reuse_lower_error 17 37 Primitive.Addresses.material1532

def v1533_pa : Scalar.QComplex := ((999999883116618489611950756967 : Int)/10^30,(-483494311609817417077391304 : Int)/10^30)
theorem v1533_pa_checked : Scalar.distance (sourceCoefficient 17 38 1 0) v1533_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1533_pb : Scalar.QComplex := ((-208616922634568274499652 : Int)/10^30,(-431477461557131838819962908 : Int)/10^30)
theorem v1533_pb_checked : Scalar.distance (sourceCoefficient 17 38 1 1) v1533_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1533_pg : Scalar.QComplex := ((-93086418044711656945812 : Int)/10^30,(45006758873293716719 : Int)/10^30)
theorem v1533_pg_checked : Scalar.distance (sourceCoefficient 17 38 1 2) v1533_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1533_mb : Scalar.QComplex := ((-580962461257277697700324 : Int)/10^30,(-431477120871344930719972492 : Int)/10^30)
theorem v1533_mb_checked : Scalar.distance (sourceCoefficient 17 38 3 1) v1533_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1533_mg : Scalar.QComplex := ((-93086344545578080950652 : Int)/10^30,(125336128431169209724 : Int)/10^30)
theorem v1533_mg_checked : Scalar.distance (sourceCoefficient 17 38 3 2) v1533_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1533_upper : Scalar.QComplex := ((999997559266941248144444383698 : Int)/10^30,(-2209402670480382810167657652 : Int)/10^30)
theorem v1533_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 38 5) 1) 14) v1533_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1533 : Material (17 : Basis) (38 : Basis) where
  plus := ![v1533_pa,v1533_pb,v1533_pg]
  minus := ![(Primitive.Addresses.material1533 1).one,v1533_mb,v1533_mg]
  upper := v1533_upper
  lower := (Primitive.Addresses.material1533 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1533_pa_checked.trans (by decide +kernel)
    · exact v1533_pb_checked.trans (by decide +kernel)
    · exact v1533_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 38 Primitive.Addresses.material1533
    · exact v1533_mb_checked.trans (by decide +kernel)
    · exact v1533_mg_checked.trans (by decide +kernel)
  upper_error := v1533_upper_checked
  lower_error := reuse_lower_error 17 38 Primitive.Addresses.material1533

def v1534_pa : Scalar.QComplex := ((999999876489675576325610793135 : Int)/10^30,(-497011703677638298703439450 : Int)/10^30)
theorem v1534_pa_checked : Scalar.distance (sourceCoefficient 17 39 1 0) v1534_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1534_pb : Scalar.QComplex := ((-214449372984008494961271 : Int)/10^30,(-431477457996419079667526366 : Int)/10^30)
theorem v1534_pb_checked : Scalar.distance (sourceCoefficient 17 39 1 1) v1534_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1534_pg : Scalar.QComplex := ((-93086417352180532401814 : Int)/10^30,(46265044591665585652 : Int)/10^30)
theorem v1534_pg_checked : Scalar.distance (sourceCoefficient 17 39 1 2) v1534_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1534_mb : Scalar.QComplex := ((-586794906362295354317197 : Int)/10^30,(-431477112277491529629175842 : Int)/10^30)
theorem v1534_mb_checked : Scalar.distance (sourceCoefficient 17 39 3 1) v1534_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1534_mg : Scalar.QComplex := ((-93086342767203310397745 : Int)/10^30,(126594413083400629171 : Int)/10^30)
theorem v1534_mg_checked : Scalar.distance (sourceCoefficient 17 39 3 2) v1534_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1534_upper : Scalar.QComplex := ((999997529310215784081431432599 : Int)/10^30,(-2222920030978133794420800061 : Int)/10^30)
theorem v1534_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 39 5) 1) 14) v1534_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1534 : Material (17 : Basis) (39 : Basis) where
  plus := ![v1534_pa,v1534_pb,v1534_pg]
  minus := ![(Primitive.Addresses.material1534 1).one,v1534_mb,v1534_mg]
  upper := v1534_upper
  lower := (Primitive.Addresses.material1534 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1534_pa_checked.trans (by decide +kernel)
    · exact v1534_pb_checked.trans (by decide +kernel)
    · exact v1534_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 39 Primitive.Addresses.material1534
    · exact v1534_mb_checked.trans (by decide +kernel)
    · exact v1534_mg_checked.trans (by decide +kernel)
  upper_error := v1534_upper_checked
  lower_error := reuse_lower_error 17 39 Primitive.Addresses.material1534

def v1535_pa : Scalar.QComplex := ((999999864931415242716268228412 : Int)/10^30,(-519747199387399176784748509 : Int)/10^30)
theorem v1535_pa_checked : Scalar.distance (sourceCoefficient 17 40 1 0) v1535_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1535_pb : Scalar.QComplex := ((-224259227446858343762803 : Int)/10^30,(-431477451770409375764253800 : Int)/10^30)
theorem v1535_pb_checked : Scalar.distance (sourceCoefficient 17 40 1 1) v1535_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1535_pg : Scalar.QComplex := ((-93086416142626098418265 : Int)/10^30,(48381410625948561949 : Int)/10^30)
theorem v1535_pg_checked : Scalar.distance (sourceCoefficient 17 40 1 2) v1535_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1535_mb : Scalar.QComplex := ((-596604751799722088701970 : Int)/10^30,(-431477097586021561958337283 : Int)/10^30)
theorem v1535_mb_checked : Scalar.distance (sourceCoefficient 17 40 3 1) v1535_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1535_mg : Scalar.QComplex := ((-93086339731320756788212 : Int)/10^30,(128710777285872807980 : Int)/10^30)
theorem v1535_mg_checked : Scalar.distance (sourceCoefficient 17 40 3 2) v1535_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1535_upper : Scalar.QComplex := ((999997478512569618154899832646 : Int)/10^30,(-2245655472877535733122577938 : Int)/10^30)
theorem v1535_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 40 5) 1) 14) v1535_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1535 : Material (17 : Basis) (40 : Basis) where
  plus := ![v1535_pa,v1535_pb,v1535_pg]
  minus := ![(Primitive.Addresses.material1535 1).one,v1535_mb,v1535_mg]
  upper := v1535_upper
  lower := (Primitive.Addresses.material1535 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1535_pa_checked.trans (by decide +kernel)
    · exact v1535_pb_checked.trans (by decide +kernel)
    · exact v1535_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 40 Primitive.Addresses.material1535
    · exact v1535_mb_checked.trans (by decide +kernel)
    · exact v1535_mg_checked.trans (by decide +kernel)
  upper_error := v1535_upper_checked
  lower_error := reuse_lower_error 17 40 Primitive.Addresses.material1535

def v1536_pa : Scalar.QComplex := ((999999857298506707486036200029 : Int)/10^30,(-534231191733795846588895128 : Int)/10^30)
theorem v1536_pa_checked : Scalar.distance (sourceCoefficient 17 41 1 0) v1536_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1536_pb : Scalar.QComplex := ((-230508743957705708392208 : Int)/10^30,(-431477447648966212577916930 : Int)/10^30)
theorem v1536_pb_checked : Scalar.distance (sourceCoefficient 17 41 1 1) v1536_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1536_pg : Scalar.QComplex := ((-93086415342788455700542 : Int)/10^30,(49729673699303672742 : Int)/10^30)
theorem v1536_pg_checked : Scalar.distance (sourceCoefficient 17 41 1 2) v1536_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1536_mb : Scalar.QComplex := ((-602854262426969012408203 : Int)/10^30,(-431477088071528652287447264 : Int)/10^30)
theorem v1536_mb_checked : Scalar.distance (sourceCoefficient 17 41 3 1) v1536_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1536_mg : Scalar.QComplex := ((-93086337767993103095798 : Int)/10^30,(130059039166984095582 : Int)/10^30)
theorem v1536_mg_checked : Scalar.distance (sourceCoefficient 17 41 3 2) v1536_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1536_upper : Scalar.QComplex := ((999997445881615638886090519566 : Int)/10^30,(-2260139430478019532473171396 : Int)/10^30)
theorem v1536_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 41 5) 1) 14) v1536_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1536 : Material (17 : Basis) (41 : Basis) where
  plus := ![v1536_pa,v1536_pb,v1536_pg]
  minus := ![(Primitive.Addresses.material1536 1).one,v1536_mb,v1536_mg]
  upper := v1536_upper
  lower := (Primitive.Addresses.material1536 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1536_pa_checked.trans (by decide +kernel)
    · exact v1536_pb_checked.trans (by decide +kernel)
    · exact v1536_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 41 Primitive.Addresses.material1536
    · exact v1536_mb_checked.trans (by decide +kernel)
    · exact v1536_mg_checked.trans (by decide +kernel)
  upper_error := v1536_upper_checked
  lower_error := reuse_lower_error 17 41 Primitive.Addresses.material1536

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
