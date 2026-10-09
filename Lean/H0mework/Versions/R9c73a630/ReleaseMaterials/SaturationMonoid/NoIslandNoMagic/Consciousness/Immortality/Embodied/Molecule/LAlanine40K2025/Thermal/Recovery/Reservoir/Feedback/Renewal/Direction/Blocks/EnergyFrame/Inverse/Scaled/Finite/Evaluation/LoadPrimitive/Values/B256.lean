import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B170
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B171

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4097_pa : Scalar.QComplex := ((999998577294041813037419215007 : Int)/10^30,(-1686834281214868392231974910 : Int)/10^30)
theorem v4097_pa_checked : Scalar.distance (sourceCoefficient 61 72 1 0) v4097_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4097_pb : Scalar.QComplex := ((-727831063971022431979592 : Int)/10^30,(-431476901191054474903398982 : Int)/10^30)
theorem v4097_pb_checked : Scalar.distance (sourceCoefficient 61 72 1 1) v4097_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4097_pg : Scalar.QComplex := ((-93086296821186492338687 : Int)/10^30,(157021379984572872099 : Int)/10^30)
theorem v4097_pg_checked : Scalar.distance (sourceCoefficient 61 72 1 2) v4097_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4097_mb : Scalar.QComplex := ((-1100175925695890963297838 : Int)/10^30,(-431476112447056780195049916 : Int)/10^30)
theorem v4097_mb_checked : Scalar.distance (sourceCoefficient 61 72 3 1) v4097_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4097_mg : Scalar.QComplex := ((-93086126658524985625682 : Int)/10^30,(237350603223843092133 : Int)/10^30)
theorem v4097_mg_checked : Scalar.distance (sourceCoefficient 61 72 3 2) v4097_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4097_upper : Scalar.QComplex := ((999994176590688051870604450392 : Int)/10^30,(-3412738594120599256026529527 : Int)/10^30)
theorem v4097_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 72 5) 1) 14) v4097_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4097 : Material (61 : Basis) (72 : Basis) where
  plus := ![v4097_pa,v4097_pb,v4097_pg]
  minus := ![(Primitive.Addresses.material4097 1).one,v4097_mb,v4097_mg]
  upper := v4097_upper
  lower := (Primitive.Addresses.material4097 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4097_pa_checked.trans (by decide +kernel)
    · exact v4097_pb_checked.trans (by decide +kernel)
    · exact v4097_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 72 Primitive.Addresses.material4097
    · exact v4097_mb_checked.trans (by decide +kernel)
    · exact v4097_mg_checked.trans (by decide +kernel)
  upper_error := v4097_upper_checked
  lower_error := reuse_lower_error 61 72 Primitive.Addresses.material4097

def v4098_pa : Scalar.QComplex := ((999998561309412869978559537376 : Int)/10^30,(-1696283910325579131471403559 : Int)/10^30)
theorem v4098_pa_checked : Scalar.distance (sourceCoefficient 61 73 1 0) v4098_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4098_pb : Scalar.QComplex := ((-731908365784221821326824 : Int)/10^30,(-431476893896886313969286883 : Int)/10^30)
theorem v4098_pb_checked : Scalar.distance (sourceCoefficient 61 73 1 1) v4098_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4098_pg : Scalar.QComplex := ((-93086295290393036265444 : Int)/10^30,(157901012143609309480 : Int)/10^30)
theorem v4098_pg_checked : Scalar.distance (sourceCoefficient 61 73 1 2) v4098_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4098_mb : Scalar.QComplex := ((-1104253219696385939945298 : Int)/10^30,(-431476101634363505278851266 : Int)/10^30)
theorem v4098_mb_checked : Scalar.distance (sourceCoefficient 61 73 3 1) v4098_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4098_mg : Scalar.QComplex := ((-93086124368649163450143 : Int)/10^30,(238230233734346467316 : Int)/10^30)
theorem v4098_mg_checked : Scalar.distance (sourceCoefficient 61 73 3 2) v4098_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4098_upper : Scalar.QComplex := ((999994144296880334608480607955 : Int)/10^30,(-3422188181569178024763561806 : Int)/10^30)
theorem v4098_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 73 5) 1) 14) v4098_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4098 : Material (61 : Basis) (73 : Basis) where
  plus := ![v4098_pa,v4098_pb,v4098_pg]
  minus := ![(Primitive.Addresses.material4098 1).one,v4098_mb,v4098_mg]
  upper := v4098_upper
  lower := (Primitive.Addresses.material4098 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4098_pa_checked.trans (by decide +kernel)
    · exact v4098_pb_checked.trans (by decide +kernel)
    · exact v4098_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 73 Primitive.Addresses.material4098
    · exact v4098_mb_checked.trans (by decide +kernel)
    · exact v4098_mg_checked.trans (by decide +kernel)
  upper_error := v4098_upper_checked
  lower_error := reuse_lower_error 61 73 Primitive.Addresses.material4098

def v4099_pa : Scalar.QComplex := ((999998543216004349871321972941 : Int)/10^30,(-1706917065671512751045422813 : Int)/10^30)
theorem v4099_pa_checked : Scalar.distance (sourceCoefficient 61 74 1 0) v4099_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4099_pb : Scalar.QComplex := ((-736496332436834340068173 : Int)/10^30,(-431476885627728000124472269 : Int)/10^30)
theorem v4099_pb_checked : Scalar.distance (sourceCoefficient 61 74 1 1) v4099_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4099_pg : Scalar.QComplex := ((-93086293556278610654585 : Int)/10^30,(158890814520915781375 : Int)/10^30)
theorem v4099_pg_checked : Scalar.distance (sourceCoefficient 61 74 1 2) v4099_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4099_mb : Scalar.QComplex := ((-1108841177504777597701722 : Int)/10^30,(-431476089405999683562398558 : Int)/10^30)
theorem v4099_mb_checked : Scalar.distance (sourceCoefficient 61 74 3 1) v4099_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4099_mg : Scalar.QComplex := ((-93086121780380510958075 : Int)/10^30,(239220034246641630249 : Int)/10^30)
theorem v4099_mg_checked : Scalar.distance (sourceCoefficient 61 74 3 2) v4099_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4099_upper : Scalar.QComplex := ((999994107851637267744094249442 : Int)/10^30,(-3432821289850694130231712190 : Int)/10^30)
theorem v4099_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 74 5) 1) 14) v4099_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4099 : Material (61 : Basis) (74 : Basis) where
  plus := ![v4099_pa,v4099_pb,v4099_pg]
  minus := ![(Primitive.Addresses.material4099 1).one,v4099_mb,v4099_mg]
  upper := v4099_upper
  lower := (Primitive.Addresses.material4099 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4099_pa_checked.trans (by decide +kernel)
    · exact v4099_pb_checked.trans (by decide +kernel)
    · exact v4099_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 74 Primitive.Addresses.material4099
    · exact v4099_mb_checked.trans (by decide +kernel)
    · exact v4099_mg_checked.trans (by decide +kernel)
  upper_error := v4099_upper_checked
  lower_error := reuse_lower_error 61 74 Primitive.Addresses.material4099

def v4100_pa : Scalar.QComplex := ((999998517818064067904617567818 : Int)/10^30,(-1721732172842483524417898006 : Int)/10^30)
theorem v4100_pa_checked : Scalar.distance (sourceCoefficient 61 75 1 0) v4100_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4100_pb : Scalar.QComplex := ((-742888716895944590126562 : Int)/10^30,(-431476873997912284858259764 : Int)/10^30)
theorem v4100_pb_checked : Scalar.distance (sourceCoefficient 61 75 1 1) v4100_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4100_pg : Scalar.QComplex := ((-93086291119675745278623 : Int)/10^30,(160269899820477687030 : Int)/10^30)
theorem v4100_pg_checked : Scalar.distance (sourceCoefficient 61 75 1 2) v4100_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4100_mb : Scalar.QComplex := ((-1115233549547703792412428 : Int)/10^30,(-431476072259848412704542145 : Int)/10^30)
theorem v4100_mb_checked : Scalar.distance (sourceCoefficient 61 75 3 1) v4100_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4100_mg : Scalar.QComplex := ((-93086118153690051014990 : Int)/10^30,(240599116930028519266 : Int)/10^30)
theorem v4100_mg_checked : Scalar.distance (sourceCoefficient 61 75 3 2) v4100_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4100_upper : Scalar.QComplex := ((999994056884203851954106804369 : Int)/10^30,(-3447636331121762233650601263 : Int)/10^30)
theorem v4100_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 75 5) 1) 14) v4100_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4100 : Material (61 : Basis) (75 : Basis) where
  plus := ![v4100_pa,v4100_pb,v4100_pg]
  minus := ![(Primitive.Addresses.material4100 1).one,v4100_mb,v4100_mg]
  upper := v4100_upper
  lower := (Primitive.Addresses.material4100 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4100_pa_checked.trans (by decide +kernel)
    · exact v4100_pb_checked.trans (by decide +kernel)
    · exact v4100_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 75 Primitive.Addresses.material4100
    · exact v4100_mb_checked.trans (by decide +kernel)
    · exact v4100_mg_checked.trans (by decide +kernel)
  upper_error := v4100_upper_checked
  lower_error := reuse_lower_error 61 75 Primitive.Addresses.material4100

def v4101_pa : Scalar.QComplex := ((999998496339360059552593217776 : Int)/10^30,(-1734162339253616332970170429 : Int)/10^30)
theorem v4101_pa_checked : Scalar.distance (sourceCoefficient 61 76 1 0) v4101_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4101_pb : Scalar.QComplex := ((-748252053172941836831690 : Int)/10^30,(-431476864142850668842087739 : Int)/10^30)
theorem v4101_pb_checked : Scalar.distance (sourceCoefficient 61 76 1 1) v4101_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4101_pg : Scalar.QComplex := ((-93086289056928369839618 : Int)/10^30,(161426979514796530149 : Int)/10^30)
theorem v4101_pg_checked : Scalar.distance (sourceCoefficient 61 76 1 2) v4101_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4101_mb : Scalar.QComplex := ((-1120596875323211507491157 : Int)/10^30,(-431476057776472814828531338 : Int)/10^30)
theorem v4101_mb_checked : Scalar.distance (sourceCoefficient 61 76 3 1) v4101_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4101_mg : Scalar.QComplex := ((-93086115092435780368853 : Int)/10^30,(241756194413455628725 : Int)/10^30)
theorem v4101_mg_checked : Scalar.distance (sourceCoefficient 61 76 3 2) v4101_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4101_upper : Scalar.QComplex := ((999994013952192263881463106653 : Int)/10^30,(-3460066441949327737128085023 : Int)/10^30)
theorem v4101_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 76 5) 1) 14) v4101_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4101 : Material (61 : Basis) (76 : Basis) where
  plus := ![v4101_pa,v4101_pb,v4101_pg]
  minus := ![(Primitive.Addresses.material4101 1).one,v4101_mb,v4101_mg]
  upper := v4101_upper
  lower := (Primitive.Addresses.material4101 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4101_pa_checked.trans (by decide +kernel)
    · exact v4101_pb_checked.trans (by decide +kernel)
    · exact v4101_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 76 Primitive.Addresses.material4101
    · exact v4101_mb_checked.trans (by decide +kernel)
    · exact v4101_mg_checked.trans (by decide +kernel)
  upper_error := v4101_upper_checked
  lower_error := reuse_lower_error 61 76 Primitive.Addresses.material4101

def v4102_pa : Scalar.QComplex := ((999998491344831932394375952109 : Int)/10^30,(-1737040028351331663980795649 : Int)/10^30)
theorem v4102_pa_checked : Scalar.distance (sourceCoefficient 61 77 1 0) v4102_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4102_pb : Scalar.QComplex := ((-749493711066081059087899 : Int)/10^30,(-431476861848648741232940584 : Int)/10^30)
theorem v4102_pb_checked : Scalar.distance (sourceCoefficient 61 77 1 1) v4102_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4102_pg : Scalar.QComplex := ((-93086288576992822116015 : Int)/10^30,(161694853290675919455 : Int)/10^30)
theorem v4102_pg_checked : Scalar.distance (sourceCoefficient 61 77 1 2) v4102_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4102_mb : Scalar.QComplex := ((-1121838530774231813055025 : Int)/10^30,(-431476054410776901872040742 : Int)/10^30)
theorem v4102_mb_checked : Scalar.distance (sourceCoefficient 61 77 3 1) v4102_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4102_mg : Scalar.QComplex := ((-93086114381337407350283 : Int)/10^30,(242024067675430606644 : Int)/10^30)
theorem v4102_mg_checked : Scalar.distance (sourceCoefficient 61 77 3 2) v4102_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4102_upper : Scalar.QComplex := ((999994003991041254745172395227 : Int)/10^30,(-3462944118140960746776143418 : Int)/10^30)
theorem v4102_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 77 5) 1) 14) v4102_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4102 : Material (61 : Basis) (77 : Basis) where
  plus := ![v4102_pa,v4102_pb,v4102_pg]
  minus := ![(Primitive.Addresses.material4102 1).one,v4102_mb,v4102_mg]
  upper := v4102_upper
  lower := (Primitive.Addresses.material4102 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4102_pa_checked.trans (by decide +kernel)
    · exact v4102_pb_checked.trans (by decide +kernel)
    · exact v4102_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 77 Primitive.Addresses.material4102
    · exact v4102_mb_checked.trans (by decide +kernel)
    · exact v4102_mg_checked.trans (by decide +kernel)
  upper_error := v4102_upper_checked
  lower_error := reuse_lower_error 61 77 Primitive.Addresses.material4102

def v4103_pa : Scalar.QComplex := ((999998461145115259182423545782 : Int)/10^30,(-1754339591244317458709679567 : Int)/10^30)
theorem v4103_pa_checked : Scalar.distance (sourceCoefficient 61 78 1 0) v4103_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4103_pb : Scalar.QComplex := ((-756958081923823223881124 : Int)/10^30,(-431476847956379492310632331 : Int)/10^30)
theorem v4103_pb_checked : Scalar.distance (sourceCoefficient 61 78 1 1) v4103_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4103_pg : Scalar.QComplex := ((-93086285672850374207638 : Int)/10^30,(163305207660776602448 : Int)/10^30)
theorem v4103_pg_checked : Scalar.distance (sourceCoefficient 61 78 1 2) v4103_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4103_mb : Scalar.QComplex := ((-1129302886864244891670570 : Int)/10^30,(-431476034077096958228734878 : Int)/10^30)
theorem v4103_mb_checked : Scalar.distance (sourceCoefficient 61 78 3 1) v4103_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4103_mg : Scalar.QComplex := ((-93086110087532747058452 : Int)/10^30,(243634418939778625992 : Int)/10^30)
theorem v4103_mg_checked : Scalar.distance (sourceCoefficient 61 78 3 2) v4103_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4103_upper : Scalar.QComplex := ((999993943933893411256354849441 : Int)/10^30,(-3480243603146308480742232545 : Int)/10^30)
theorem v4103_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 78 5) 1) 14) v4103_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4103 : Material (61 : Basis) (78 : Basis) where
  plus := ![v4103_pa,v4103_pb,v4103_pg]
  minus := ![(Primitive.Addresses.material4103 1).one,v4103_mb,v4103_mg]
  upper := v4103_upper
  lower := (Primitive.Addresses.material4103 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4103_pa_checked.trans (by decide +kernel)
    · exact v4103_pb_checked.trans (by decide +kernel)
    · exact v4103_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 78 Primitive.Addresses.material4103
    · exact v4103_mb_checked.trans (by decide +kernel)
    · exact v4103_mg_checked.trans (by decide +kernel)
  upper_error := v4103_upper_checked
  lower_error := reuse_lower_error 61 78 Primitive.Addresses.material4103

def v4104_pa : Scalar.QComplex := ((999998451345469242013956792100 : Int)/10^30,(-1759916663704596112935776103 : Int)/10^30)
theorem v4104_pa_checked : Scalar.distance (sourceCoefficient 61 79 1 0) v4104_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4104_pb : Scalar.QComplex := ((-759364462767792968452056 : Int)/10^30,(-431476843441058038209565216 : Int)/10^30)
theorem v4104_pb_checked : Scalar.distance (sourceCoefficient 61 79 1 1) v4104_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4104_pg : Scalar.QComplex := ((-93086284729678393813821 : Int)/10^30,(163824357365444972804 : Int)/10^30)
theorem v4104_pg_checked : Scalar.distance (sourceCoefficient 61 79 1 2) v4104_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4104_mb : Scalar.QComplex := ((-1131709262915690018633921 : Int)/10^30,(-431476027485178896412297015 : Int)/10^30)
theorem v4104_mb_checked : Scalar.distance (sourceCoefficient 61 79 3 1) v4104_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4104_mg : Scalar.QComplex := ((-93086108696358304356595 : Int)/10^30,(244153567637228894796 : Int)/10^30)
theorem v4104_mg_checked : Scalar.distance (sourceCoefficient 61 79 3 2) v4104_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4104_upper : Scalar.QComplex := ((999993924508740871129873306439 : Int)/10^30,(-3485820650386892825644041432 : Int)/10^30)
theorem v4104_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 79 5) 1) 14) v4104_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4104 : Material (61 : Basis) (79 : Basis) where
  plus := ![v4104_pa,v4104_pb,v4104_pg]
  minus := ![(Primitive.Addresses.material4104 1).one,v4104_mb,v4104_mg]
  upper := v4104_upper
  lower := (Primitive.Addresses.material4104 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4104_pa_checked.trans (by decide +kernel)
    · exact v4104_pb_checked.trans (by decide +kernel)
    · exact v4104_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 79 Primitive.Addresses.material4104
    · exact v4104_mb_checked.trans (by decide +kernel)
    · exact v4104_mg_checked.trans (by decide +kernel)
  upper_error := v4104_upper_checked
  lower_error := reuse_lower_error 61 79 Primitive.Addresses.material4104

def v4105_pa : Scalar.QComplex := ((999998435975210963464047477839 : Int)/10^30,(-1768628602024611379733562919 : Int)/10^30)
theorem v4105_pa_checked : Scalar.distance (sourceCoefficient 61 80 1 0) v4105_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4105_pb : Scalar.QComplex := ((-763123467427032252415620 : Int)/10^30,(-431476836351871267971269184 : Int)/10^30)
theorem v4105_pb_checked : Scalar.distance (sourceCoefficient 61 80 1 1) v4105_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4105_pg : Scalar.QComplex := ((-93086283249590940206498 : Int)/10^30,(164635320505113444487 : Int)/10^30)
theorem v4105_pg_checked : Scalar.distance (sourceCoefficient 61 80 1 2) v4105_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4105_mb : Scalar.QComplex := ((-1135468260057631175366989 : Int)/10^30,(-431476017152143044163892581 : Int)/10^30)
theorem v4105_mb_checked : Scalar.distance (sourceCoefficient 61 80 3 1) v4105_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4105_mg : Scalar.QComplex := ((-93086106516446736743544 : Int)/10^30,(244964529197689914935 : Int)/10^30)
theorem v4105_mg_checked : Scalar.distance (sourceCoefficient 61 80 3 2) v4105_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4105_upper : Scalar.QComplex := ((999993894102490285298389743619 : Int)/10^30,(-3494532549203827931104007980 : Int)/10^30)
theorem v4105_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 80 5) 1) 14) v4105_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4105 : Material (61 : Basis) (80 : Basis) where
  plus := ![v4105_pa,v4105_pb,v4105_pg]
  minus := ![(Primitive.Addresses.material4105 1).one,v4105_mb,v4105_mg]
  upper := v4105_upper
  lower := (Primitive.Addresses.material4105 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4105_pa_checked.trans (by decide +kernel)
    · exact v4105_pb_checked.trans (by decide +kernel)
    · exact v4105_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 80 Primitive.Addresses.material4105
    · exact v4105_mb_checked.trans (by decide +kernel)
    · exact v4105_mg_checked.trans (by decide +kernel)
  upper_error := v4105_upper_checked
  lower_error := reuse_lower_error 61 80 Primitive.Addresses.material4105

def v4106_pa : Scalar.QComplex := ((999998389236236841732405562391 : Int)/10^30,(-1794860699819524848100765244 : Int)/10^30)
theorem v4106_pa_checked : Scalar.distance (sourceCoefficient 61 81 1 0) v4106_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4106_pb : Scalar.QComplex := ((-774442025107386128294287 : Int)/10^30,(-431476814742284045827658757 : Int)/10^30)
theorem v4106_pb_checked : Scalar.distance (sourceCoefficient 61 81 1 1) v4106_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4106_pg : Scalar.QComplex := ((-93086278743195932268803 : Int)/10^30,(167077172530463173945 : Int)/10^30)
theorem v4106_pg_checked : Scalar.distance (sourceCoefficient 61 81 1 2) v4106_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4106_mb : Scalar.QComplex := ((-1146786794875468230179038 : Int)/10^30,(-431475985775158359026228528 : Int)/10^30)
theorem v4106_mb_checked : Scalar.distance (sourceCoefficient 61 81 3 1) v4106_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4106_mg : Scalar.QComplex := ((-93086099902845085798532 : Int)/10^30,(247406376425010605852 : Int)/10^30)
theorem v4106_mg_checked : Scalar.distance (sourceCoefficient 61 81 3 2) v4106_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4106_upper : Scalar.QComplex := ((999993802089364739080020687299 : Int)/10^30,(-3520764527261883965115308157 : Int)/10^30)
theorem v4106_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 81 5) 1) 14) v4106_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4106 : Material (61 : Basis) (81 : Basis) where
  plus := ![v4106_pa,v4106_pb,v4106_pg]
  minus := ![(Primitive.Addresses.material4106 1).one,v4106_mb,v4106_mg]
  upper := v4106_upper
  lower := (Primitive.Addresses.material4106 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4106_pa_checked.trans (by decide +kernel)
    · exact v4106_pb_checked.trans (by decide +kernel)
    · exact v4106_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 81 Primitive.Addresses.material4106
    · exact v4106_mb_checked.trans (by decide +kernel)
    · exact v4106_mg_checked.trans (by decide +kernel)
  upper_error := v4106_upper_checked
  lower_error := reuse_lower_error 61 81 Primitive.Addresses.material4106

def v4107_pa : Scalar.QComplex := ((999998371345452494995043020222 : Int)/10^30,(-1804800942623417072894695797 : Int)/10^30)
theorem v4107_pa_checked : Scalar.distance (sourceCoefficient 61 82 1 0) v4107_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4107_pb : Scalar.QComplex := ((-778731015285344698443156 : Int)/10^30,(-431476806450240296404847358 : Int)/10^30)
theorem v4107_pb_checked : Scalar.distance (sourceCoefficient 61 82 1 1) v4107_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4107_pg : Scalar.QComplex := ((-93086277016043649177809 : Int)/10^30,(168002474121853572142 : Int)/10^30)
theorem v4107_pg_checked : Scalar.distance (sourceCoefficient 61 82 1 2) v4107_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4107_mb : Scalar.QComplex := ((-1151075776300779444574494 : Int)/10^30,(-431475973781912342478871004 : Int)/10^30)
theorem v4107_mb_checked : Scalar.distance (sourceCoefficient 61 82 3 1) v4107_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4107_mg : Scalar.QComplex := ((-93086097377199846472018 : Int)/10^30,(248331676181414300946 : Int)/10^30)
theorem v4107_mg_checked : Scalar.distance (sourceCoefficient 61 82 3 2) v4107_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4107_upper : Scalar.QComplex := ((999993767042649730829277969315 : Int)/10^30,(-3530704724383081453264124351 : Int)/10^30)
theorem v4107_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 82 5) 1) 14) v4107_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4107 : Material (61 : Basis) (82 : Basis) where
  plus := ![v4107_pa,v4107_pb,v4107_pg]
  minus := ![(Primitive.Addresses.material4107 1).one,v4107_mb,v4107_mg]
  upper := v4107_upper
  lower := (Primitive.Addresses.material4107 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4107_pa_checked.trans (by decide +kernel)
    · exact v4107_pb_checked.trans (by decide +kernel)
    · exact v4107_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 82 Primitive.Addresses.material4107
    · exact v4107_mb_checked.trans (by decide +kernel)
    · exact v4107_mg_checked.trans (by decide +kernel)
  upper_error := v4107_upper_checked
  lower_error := reuse_lower_error 61 82 Primitive.Addresses.material4107

def v4108_pa : Scalar.QComplex := ((999998346764739266436412854569 : Int)/10^30,(-1818369541177012743001493268 : Int)/10^30)
theorem v4108_pa_checked : Scalar.distance (sourceCoefficient 61 83 1 0) v4108_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4108_pb : Scalar.QComplex := ((-784585558929387599848665 : Int)/10^30,(-431476795039705091717859242 : Int)/10^30)
theorem v4108_pb_checked : Scalar.distance (sourceCoefficient 61 83 1 1) v4108_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4108_pg : Scalar.QComplex := ((-93086274641130811970083 : Int)/10^30,(169265526344807010954 : Int)/10^30)
theorem v4108_pg_checked : Scalar.distance (sourceCoefficient 61 83 1 2) v4108_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4108_mb : Scalar.QComplex := ((-1156930307918130211223736 : Int)/10^30,(-431475957319173900504111303 : Int)/10^30)
theorem v4108_mb_checked : Scalar.distance (sourceCoefficient 61 83 3 1) v4108_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4108_mg : Scalar.QComplex := ((-93086093912330710904485 : Int)/10^30,(249594725884632856408 : Int)/10^30)
theorem v4108_mg_checked : Scalar.distance (sourceCoefficient 61 83 3 2) v4108_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4108_upper : Scalar.QComplex := ((999993719043802942494677976089 : Int)/10^30,(-3544273260303762369732733936 : Int)/10^30)
theorem v4108_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 83 5) 1) 14) v4108_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4108 : Material (61 : Basis) (83 : Basis) where
  plus := ![v4108_pa,v4108_pb,v4108_pg]
  minus := ![(Primitive.Addresses.material4108 1).one,v4108_mb,v4108_mg]
  upper := v4108_upper
  lower := (Primitive.Addresses.material4108 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4108_pa_checked.trans (by decide +kernel)
    · exact v4108_pb_checked.trans (by decide +kernel)
    · exact v4108_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 83 Primitive.Addresses.material4108
    · exact v4108_mb_checked.trans (by decide +kernel)
    · exact v4108_mg_checked.trans (by decide +kernel)
  upper_error := v4108_upper_checked
  lower_error := reuse_lower_error 61 83 Primitive.Addresses.material4108

def v4109_pa : Scalar.QComplex := ((999998282251572336742557823239 : Int)/10^30,(-1853508539140527980524342099 : Int)/10^30)
theorem v4109_pa_checked : Scalar.distance (sourceCoefficient 61 84 1 0) v4109_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4109_pb : Scalar.QComplex := ((-799747242127569737580238 : Int)/10^30,(-431476764997178945552539677 : Int)/10^30)
theorem v4109_pb_checked : Scalar.distance (sourceCoefficient 61 84 1 1) v4109_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4109_pg : Scalar.QComplex := ((-93086268397811789887124 : Int)/10^30,(172536489726355168768 : Int)/10^30)
theorem v4109_pg_checked : Scalar.distance (sourceCoefficient 61 84 1 2) v4109_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4109_mb : Scalar.QComplex := ((-1172091959545577772127657 : Int)/10^30,(-431475914192809197375510224 : Int)/10^30)
theorem v4109_mb_checked : Scalar.distance (sourceCoefficient 61 84 3 1) v4109_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4109_mg : Scalar.QComplex := ((-93086084846319933940449 : Int)/10^30,(252865682660548729452 : Int)/10^30)
theorem v4109_mg_checked : Scalar.distance (sourceCoefficient 61 84 3 2) v4109_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4109_upper : Scalar.QComplex := ((999993593884009397551056121120 : Int)/10^30,(-3579412094587994325391064863 : Int)/10^30)
theorem v4109_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 84 5) 1) 14) v4109_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4109 : Material (61 : Basis) (84 : Basis) where
  plus := ![v4109_pa,v4109_pb,v4109_pg]
  minus := ![(Primitive.Addresses.material4109 1).one,v4109_mb,v4109_mg]
  upper := v4109_upper
  lower := (Primitive.Addresses.material4109 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4109_pa_checked.trans (by decide +kernel)
    · exact v4109_pb_checked.trans (by decide +kernel)
    · exact v4109_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 84 Primitive.Addresses.material4109
    · exact v4109_mb_checked.trans (by decide +kernel)
    · exact v4109_mg_checked.trans (by decide +kernel)
  upper_error := v4109_upper_checked
  lower_error := reuse_lower_error 61 84 Primitive.Addresses.material4109

def v4110_pa : Scalar.QComplex := ((999998132594101453715503966075 : Int)/10^30,(-1932565214911977832428262430 : Int)/10^30)
theorem v4110_pa_checked : Scalar.distance (sourceCoefficient 61 85 1 0) v4110_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4110_pb : Scalar.QComplex := ((-833858408586672362777250 : Int)/10^30,(-431476694809774442484395229 : Int)/10^30)
theorem v4110_pb_checked : Scalar.distance (sourceCoefficient 61 85 1 1) v4110_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4110_pg : Scalar.QComplex := ((-93086253861199777121182 : Int)/10^30,(179895592136710352164 : Int)/10^30)
theorem v4110_pg_checked : Scalar.distance (sourceCoefficient 61 85 1 2) v4110_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4110_mb : Scalar.QComplex := ((-1206203052734965204484121 : Int)/10^30,(-431475814569030483987033073 : Int)/10^30)
theorem v4110_mb_checked : Scalar.distance (sourceCoefficient 61 85 3 1) v4110_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4110_mg : Scalar.QComplex := ((-93086063959139395351862 : Int)/10^30,(260224769786332295562 : Int)/10^30)
theorem v4110_mg_checked : Scalar.distance (sourceCoefficient 61 85 3 2) v4110_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4110_upper : Scalar.QComplex := ((999993307782110995826101863866 : Int)/10^30,(-3658468394318594340805609510 : Int)/10^30)
theorem v4110_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 85 5) 1) 14) v4110_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4110 : Material (61 : Basis) (85 : Basis) where
  plus := ![v4110_pa,v4110_pb,v4110_pg]
  minus := ![(Primitive.Addresses.material4110 1).one,v4110_mb,v4110_mg]
  upper := v4110_upper
  lower := (Primitive.Addresses.material4110 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4110_pa_checked.trans (by decide +kernel)
    · exact v4110_pb_checked.trans (by decide +kernel)
    · exact v4110_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 85 Primitive.Addresses.material4110
    · exact v4110_mb_checked.trans (by decide +kernel)
    · exact v4110_mg_checked.trans (by decide +kernel)
  upper_error := v4110_upper_checked
  lower_error := reuse_lower_error 61 85 Primitive.Addresses.material4110

def v4111_pa : Scalar.QComplex := ((999998104301969870861266651935 : Int)/10^30,(-1947149831571072506713793918 : Int)/10^30)
theorem v4111_pa_checked : Scalar.distance (sourceCoefficient 61 86 1 0) v4111_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4111_pb : Scalar.QComplex := ((-840151340321542115686646 : Int)/10^30,(-431476681468533988594134805 : Int)/10^30)
theorem v4111_pb_checked : Scalar.distance (sourceCoefficient 61 86 1 1) v4111_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4111_pg : Scalar.QComplex := ((-93086251105281608946246 : Int)/10^30,(181253221762607096761 : Int)/10^30)
theorem v4111_pg_checked : Scalar.distance (sourceCoefficient 61 86 1 2) v4111_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4111_mb : Scalar.QComplex := ((-1212495970613799226770948 : Int)/10^30,(-431475795797278333581899293 : Int)/10^30)
theorem v4111_mb_checked : Scalar.distance (sourceCoefficient 61 86 3 1) v4111_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4111_mg : Scalar.QComplex := ((-93086060031649031550848 : Int)/10^30,(261582396528488226511 : Int)/10^30)
theorem v4111_mg_checked : Scalar.distance (sourceCoefficient 61 86 3 2) v4111_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4111_upper : Scalar.QComplex := ((999993254318296303268797669356 : Int)/10^30,(-3673052940425963260911478674 : Int)/10^30)
theorem v4111_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 86 5) 1) 14) v4111_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4111 : Material (61 : Basis) (86 : Basis) where
  plus := ![v4111_pa,v4111_pb,v4111_pg]
  minus := ![(Primitive.Addresses.material4111 1).one,v4111_mb,v4111_mg]
  upper := v4111_upper
  lower := (Primitive.Addresses.material4111 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4111_pa_checked.trans (by decide +kernel)
    · exact v4111_pb_checked.trans (by decide +kernel)
    · exact v4111_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 86 Primitive.Addresses.material4111
    · exact v4111_mb_checked.trans (by decide +kernel)
    · exact v4111_mg_checked.trans (by decide +kernel)
  upper_error := v4111_upper_checked
  lower_error := reuse_lower_error 61 86 Primitive.Addresses.material4111

def v4112_pa : Scalar.QComplex := ((999998102421031038700359431883 : Int)/10^30,(-1948115586179797452961531347 : Int)/10^30)
theorem v4112_pa_checked : Scalar.distance (sourceCoefficient 61 87 1 0) v4112_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4112_pb : Scalar.QComplex := ((-840568041556801498824021 : Int)/10^30,(-431476680580792525659224859 : Int)/10^30)
theorem v4112_pb_checked : Scalar.distance (sourceCoefficient 61 87 1 1) v4112_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4112_pg : Scalar.QComplex := ((-93086250921976542684024 : Int)/10^30,(181343120393037467196 : Int)/10^30)
theorem v4112_pg_checked : Scalar.distance (sourceCoefficient 61 87 1 2) v4112_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4112_mb : Scalar.QComplex := ((-1212912670927820795712449 : Int)/10^30,(-431475794549942802691812874 : Int)/10^30)
theorem v4112_mb_checked : Scalar.distance (sourceCoefficient 61 87 3 1) v4112_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4112_mg : Scalar.QComplex := ((-93086059770765564364083 : Int)/10^30,(261672294967261211835 : Int)/10^30)
theorem v4112_mg_checked : Scalar.distance (sourceCoefficient 61 87 3 2) v4112_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4112_upper : Scalar.QComplex := ((999993250770555430459784792834 : Int)/10^30,(-3674018690349980376097042870 : Int)/10^30)
theorem v4112_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 87 5) 1) 14) v4112_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4112 : Material (61 : Basis) (87 : Basis) where
  plus := ![v4112_pa,v4112_pb,v4112_pg]
  minus := ![(Primitive.Addresses.material4112 1).one,v4112_mb,v4112_mg]
  upper := v4112_upper
  lower := (Primitive.Addresses.material4112 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4112_pa_checked.trans (by decide +kernel)
    · exact v4112_pb_checked.trans (by decide +kernel)
    · exact v4112_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 87 Primitive.Addresses.material4112
    · exact v4112_mb_checked.trans (by decide +kernel)
    · exact v4112_mg_checked.trans (by decide +kernel)
  upper_error := v4112_upper_checked
  lower_error := reuse_lower_error 61 87 Primitive.Addresses.material4112

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
