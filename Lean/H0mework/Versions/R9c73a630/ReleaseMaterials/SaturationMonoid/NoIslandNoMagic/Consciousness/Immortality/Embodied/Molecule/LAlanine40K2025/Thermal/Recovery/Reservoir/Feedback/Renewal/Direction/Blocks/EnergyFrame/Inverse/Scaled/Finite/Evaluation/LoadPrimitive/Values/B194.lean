import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B129
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B130

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3105_pa : Scalar.QComplex := ((999999522968212921730460810778 : Int)/10^30,(-976761663148801717594037449 : Int)/10^30)
theorem v3105_pa_checked : Scalar.distance (sourceCoefficient 40 46 1 0) v3105_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3105_pb : Scalar.QComplex := ((-421450700710682940336411 : Int)/10^30,(-431477314851471038311669875 : Int)/10^30)
theorem v3105_pb_checked : Scalar.distance (sourceCoefficient 40 46 1 1) v3105_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3105_pg : Scalar.QComplex := ((-93086385457197550255802 : Int)/10^30,(90923256048966028561 : Int)/10^30)
theorem v3105_pg_checked : Scalar.distance (sourceCoefficient 40 46 1 2) v3105_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3105_mb : Scalar.QComplex := ((-793796033485271908465155 : Int)/10^30,(-431476790499773953274490909 : Int)/10^30)
theorem v3105_mb_checked : Scalar.distance (sourceCoefficient 40 46 3 1) v3105_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3105_mg : Scalar.QComplex := ((-93086272334207047741203 : Int)/10^30,(171252580388474148554 : Int)/10^30)
theorem v3105_mg_checked : Scalar.distance (sourceCoefficient 40 46 3 2) v3105_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3105_upper : Scalar.QComplex := ((999996347784372187292811399272 : Int)/10^30,(-2702668665772114644737329577 : Int)/10^30)
theorem v3105_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 46 5) 1) 14) v3105_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3105 : Material (40 : Basis) (46 : Basis) where
  plus := ![v3105_pa,v3105_pb,v3105_pg]
  minus := ![(Primitive.Addresses.material3105 1).one,v3105_mb,v3105_mg]
  upper := v3105_upper
  lower := (Primitive.Addresses.material3105 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3105_pa_checked.trans (by decide +kernel)
    · exact v3105_pb_checked.trans (by decide +kernel)
    · exact v3105_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 46 Primitive.Addresses.material3105
    · exact v3105_mb_checked.trans (by decide +kernel)
    · exact v3105_mg_checked.trans (by decide +kernel)
  upper_error := v3105_upper_checked
  lower_error := reuse_lower_error 40 46 Primitive.Addresses.material3105

def v3106_pa : Scalar.QComplex := ((999999519113929694634443660552 : Int)/10^30,(-980699703966162365100890046 : Int)/10^30)
theorem v3106_pa_checked : Scalar.distance (sourceCoefficient 40 47 1 0) v3106_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3106_pb : Scalar.QComplex := ((-423149876760707504743027 : Int)/10^30,(-431477313149496260963762309 : Int)/10^30)
theorem v3106_pb_checked : Scalar.distance (sourceCoefficient 40 47 1 1) v3106_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3106_pg : Scalar.QComplex := ((-93086385094215844604314 : Int)/10^30,(91289834205187297564 : Int)/10^30)
theorem v3106_pg_checked : Scalar.distance (sourceCoefficient 40 47 1 2) v3106_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3106_mb : Scalar.QComplex := ((-795495207433887994513040 : Int)/10^30,(-431476787331487406526816370 : Int)/10^30)
theorem v3106_mb_checked : Scalar.distance (sourceCoefficient 40 47 3 1) v3106_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3106_mg : Scalar.QComplex := ((-93086271654885038492711 : Int)/10^30,(171619158094964752657 : Int)/10^30)
theorem v3106_mg_checked : Scalar.distance (sourceCoefficient 40 47 3 2) v3106_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3106_upper : Scalar.QComplex := ((999996337133393506206645609817 : Int)/10^30,(-2706606694072082897430674500 : Int)/10^30)
theorem v3106_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 47 5) 1) 14) v3106_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3106 : Material (40 : Basis) (47 : Basis) where
  plus := ![v3106_pa,v3106_pb,v3106_pg]
  minus := ![(Primitive.Addresses.material3106 1).one,v3106_mb,v3106_mg]
  upper := v3106_upper
  lower := (Primitive.Addresses.material3106 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3106_pa_checked.trans (by decide +kernel)
    · exact v3106_pb_checked.trans (by decide +kernel)
    · exact v3106_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 47 Primitive.Addresses.material3106
    · exact v3106_mb_checked.trans (by decide +kernel)
    · exact v3106_mg_checked.trans (by decide +kernel)
  upper_error := v3106_upper_checked
  lower_error := reuse_lower_error 40 47 Primitive.Addresses.material3106

def v3107_pa : Scalar.QComplex := ((999999491836562109582692611706 : Int)/10^30,(-1008130258225967050637576329 : Int)/10^30)
theorem v3107_pa_checked : Scalar.distance (sourceCoefficient 40 48 1 0) v3107_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3107_pb : Scalar.QComplex := ((-434985543966725322441428 : Int)/10^30,(-431477301046821882557169902 : Int)/10^30)
theorem v3107_pb_checked : Scalar.distance (sourceCoefficient 40 48 1 1) v3107_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3107_pg : Scalar.QComplex := ((-93086382519131416859253 : Int)/10^30,(93843246534039882062 : Int)/10^30)
theorem v3107_pg_checked : Scalar.distance (sourceCoefficient 40 48 1 2) v3107_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3107_mb : Scalar.QComplex := ((-807330859788883090352501 : Int)/10^30,(-431476765015169794368529243 : Int)/10^30)
theorem v3107_mb_checked : Scalar.distance (sourceCoefficient 40 48 3 1) v3107_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3107_mg : Scalar.QComplex := ((-93086266876321731191727 : Int)/10^30,(174172567250883346769 : Int)/10^30)
theorem v3107_mg_checked : Scalar.distance (sourceCoefficient 40 48 3 2) v3107_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3107_upper : Scalar.QComplex := ((999996262513418375610307612469 : Int)/10^30,(-2734037160399037363897803834 : Int)/10^30)
theorem v3107_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 48 5) 1) 14) v3107_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3107 : Material (40 : Basis) (48 : Basis) where
  plus := ![v3107_pa,v3107_pb,v3107_pg]
  minus := ![(Primitive.Addresses.material3107 1).one,v3107_mb,v3107_mg]
  upper := v3107_upper
  lower := (Primitive.Addresses.material3107 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3107_pa_checked.trans (by decide +kernel)
    · exact v3107_pb_checked.trans (by decide +kernel)
    · exact v3107_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 48 Primitive.Addresses.material3107
    · exact v3107_mb_checked.trans (by decide +kernel)
    · exact v3107_mg_checked.trans (by decide +kernel)
  upper_error := v3107_upper_checked
  lower_error := reuse_lower_error 40 48 Primitive.Addresses.material3107

def v3108_pa : Scalar.QComplex := ((999999469376155229775161382049 : Int)/10^30,(-1030168630845836345154868729 : Int)/10^30)
theorem v3108_pa_checked : Scalar.distance (sourceCoefficient 40 49 1 0) v3108_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3108_pb : Scalar.QComplex := ((-444494605979905325316862 : Int)/10^30,(-431477291009637272480730240 : Int)/10^30)
theorem v3108_pb_checked : Scalar.distance (sourceCoefficient 40 49 1 1) v3108_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3108_pg : Scalar.QComplex := ((-93086380391046938216352 : Int)/10^30,(95894719921864510485 : Int)/10^30)
theorem v3108_pg_checked : Scalar.distance (sourceCoefficient 40 49 1 2) v3108_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3108_mb : Scalar.QComplex := ((-816839909599766459635742 : Int)/10^30,(-431476746772096676475159654 : Int)/10^30)
theorem v3108_mb_checked : Scalar.distance (sourceCoefficient 40 49 3 1) v3108_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3108_mg : Scalar.QComplex := ((-93086262977908906170808 : Int)/10^30,(176224038038409616238 : Int)/10^30)
theorem v3108_mg_checked : Scalar.distance (sourceCoefficient 40 49 3 2) v3108_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3108_upper : Scalar.QComplex := ((999996202016813111592393480253 : Int)/10^30,(-2756075461430714767869173215 : Int)/10^30)
theorem v3108_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 49 5) 1) 14) v3108_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3108 : Material (40 : Basis) (49 : Basis) where
  plus := ![v3108_pa,v3108_pb,v3108_pg]
  minus := ![(Primitive.Addresses.material3108 1).one,v3108_mb,v3108_mg]
  upper := v3108_upper
  lower := (Primitive.Addresses.material3108 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3108_pa_checked.trans (by decide +kernel)
    · exact v3108_pb_checked.trans (by decide +kernel)
    · exact v3108_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 49 Primitive.Addresses.material3108
    · exact v3108_mb_checked.trans (by decide +kernel)
    · exact v3108_mg_checked.trans (by decide +kernel)
  upper_error := v3108_upper_checked
  lower_error := reuse_lower_error 40 49 Primitive.Addresses.material3108

def v3109_pa : Scalar.QComplex := ((999999466719865390098232908224 : Int)/10^30,(-1032743910576141603341269570 : Int)/10^30)
theorem v3109_pa_checked : Scalar.distance (sourceCoefficient 40 50 1 0) v3109_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3109_pb : Scalar.QComplex := ((-445605781244679566357462 : Int)/10^30,(-431477289818515166729879948 : Int)/10^30)
theorem v3109_pb_checked : Scalar.distance (sourceCoefficient 40 50 1 1) v3109_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3109_pg : Scalar.QComplex := ((-93086380138929059955828 : Int)/10^30,(96134443512643853965 : Int)/10^30)
theorem v3109_pg_checked : Scalar.distance (sourceCoefficient 40 50 1 2) v3109_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3109_mb : Scalar.QComplex := ((-817951083422914635267771 : Int)/10^30,(-431476744622080806209486317 : Int)/10^30)
theorem v3109_mb_checked : Scalar.distance (sourceCoefficient 40 50 3 1) v3109_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3109_mg : Scalar.QComplex := ((-93086262518920459692454 : Int)/10^30,(176463761322362536989 : Int)/10^30)
theorem v3109_mg_checked : Scalar.distance (sourceCoefficient 40 50 3 2) v3109_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3109_upper : Scalar.QComplex := ((999996194915828041192410860738 : Int)/10^30,(-2758650732740928094822905563 : Int)/10^30)
theorem v3109_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 50 5) 1) 14) v3109_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3109 : Material (40 : Basis) (50 : Basis) where
  plus := ![v3109_pa,v3109_pb,v3109_pg]
  minus := ![(Primitive.Addresses.material3109 1).one,v3109_mb,v3109_mg]
  upper := v3109_upper
  lower := (Primitive.Addresses.material3109 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3109_pa_checked.trans (by decide +kernel)
    · exact v3109_pb_checked.trans (by decide +kernel)
    · exact v3109_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 50 Primitive.Addresses.material3109
    · exact v3109_mb_checked.trans (by decide +kernel)
    · exact v3109_mg_checked.trans (by decide +kernel)
  upper_error := v3109_upper_checked
  lower_error := reuse_lower_error 40 50 Primitive.Addresses.material3109

def v3110_pa : Scalar.QComplex := ((999999454986796733785633884147 : Int)/10^30,(-1044043154995538006631434940 : Int)/10^30)
theorem v3110_pa_checked : Scalar.distance (sourceCoefficient 40 51 1 0) v3110_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3110_pb : Scalar.QComplex := ((-450481150985821279639583 : Int)/10^30,(-431477284547276610025092177 : Int)/10^30)
theorem v3110_pb_checked : Scalar.distance (sourceCoefficient 40 51 1 1) v3110_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3110_pg : Scalar.QComplex := ((-93086379024229060949622 : Int)/10^30,(97186249811355902548 : Int)/10^30)
theorem v3110_pg_checked : Scalar.distance (sourceCoefficient 40 51 1 2) v3110_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3110_mb : Scalar.QComplex := ((-822826446799891911853728 : Int)/10^30,(-431476735143619704124426029 : Int)/10^30)
theorem v3110_mb_checked : Scalar.distance (sourceCoefficient 40 51 3 1) v3110_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3110_mg : Scalar.QComplex := ((-93086260496559411548681 : Int)/10^30,(177515566267503135722 : Int)/10^30)
theorem v3110_mg_checked : Scalar.distance (sourceCoefficient 40 51 3 2) v3110_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3110_upper : Scalar.QComplex := ((999996163681306051475522948902 : Int)/10^30,(-2769949940081215152787740761 : Int)/10^30)
theorem v3110_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 51 5) 1) 14) v3110_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3110 : Material (40 : Basis) (51 : Basis) where
  plus := ![v3110_pa,v3110_pb,v3110_pg]
  minus := ![(Primitive.Addresses.material3110 1).one,v3110_mb,v3110_mg]
  upper := v3110_upper
  lower := (Primitive.Addresses.material3110 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3110_pa_checked.trans (by decide +kernel)
    · exact v3110_pb_checked.trans (by decide +kernel)
    · exact v3110_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 51 Primitive.Addresses.material3110
    · exact v3110_mb_checked.trans (by decide +kernel)
    · exact v3110_mg_checked.trans (by decide +kernel)
  upper_error := v3110_upper_checked
  lower_error := reuse_lower_error 40 51 Primitive.Addresses.material3110

def v3111_pa : Scalar.QComplex := ((999999429439955679007928086035 : Int)/10^30,(-1068232073616599460066622422 : Int)/10^30)
theorem v3111_pa_checked : Scalar.distance (sourceCoefficient 40 52 1 0) v3111_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3111_pb : Scalar.QComplex := ((-460918125053695328037426 : Int)/10^30,(-431477273015917783138701942 : Int)/10^30)
theorem v3111_pb_checked : Scalar.distance (sourceCoefficient 40 52 1 1) v3111_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3111_pg : Scalar.QComplex := ((-93086376591316358960803 : Int)/10^30,(99437909826895795498 : Int)/10^30)
theorem v3111_pg_checked : Scalar.distance (sourceCoefficient 40 52 1 2) v3111_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3111_mb : Scalar.QComplex := ((-833263407030560207022530 : Int)/10^30,(-431476714605626614177058657 : Int)/10^30)
theorem v3111_mb_checked : Scalar.distance (sourceCoefficient 40 52 3 1) v3111_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3111_mg : Scalar.QComplex := ((-93086256120566433036069 : Int)/10^30,(179767223345153011444 : Int)/10^30)
theorem v3111_mg_checked : Scalar.distance (sourceCoefficient 40 52 3 2) v3111_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3111_upper : Scalar.QComplex := ((999996096386623907320135311150 : Int)/10^30,(-2794138778584193680902832305 : Int)/10^30)
theorem v3111_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 52 5) 1) 14) v3111_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3111 : Material (40 : Basis) (52 : Basis) where
  plus := ![v3111_pa,v3111_pb,v3111_pg]
  minus := ![(Primitive.Addresses.material3111 1).one,v3111_mb,v3111_mg]
  upper := v3111_upper
  lower := (Primitive.Addresses.material3111 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3111_pa_checked.trans (by decide +kernel)
    · exact v3111_pb_checked.trans (by decide +kernel)
    · exact v3111_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 52 Primitive.Addresses.material3111
    · exact v3111_mb_checked.trans (by decide +kernel)
    · exact v3111_mg_checked.trans (by decide +kernel)
  upper_error := v3111_upper_checked
  lower_error := reuse_lower_error 40 52 Primitive.Addresses.material3111

def v3112_pa : Scalar.QComplex := ((999999425477768640678056088441 : Int)/10^30,(-1071934761374426910010744337 : Int)/10^30)
theorem v3112_pa_checked : Scalar.distance (sourceCoefficient 40 53 1 0) v3112_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3112_pb : Scalar.QComplex := ((-462515751490420455573113 : Int)/10^30,(-431477271221062835800646203 : Int)/10^30)
theorem v3112_pb_checked : Scalar.distance (sourceCoefficient 40 53 1 1) v3112_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3112_pg : Scalar.QComplex := ((-93086376213293536227932 : Int)/10^30,(99782579800717333887 : Int)/10^30)
theorem v3112_pg_checked : Scalar.distance (sourceCoefficient 40 53 1 2) v3112_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3112_mb : Scalar.QComplex := ((-834861031323537014743537 : Int)/10^30,(-431476711432092674675380012 : Int)/10^30)
theorem v3112_mb_checked : Scalar.distance (sourceCoefficient 40 53 3 1) v3112_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3112_mg : Scalar.QComplex := ((-93086255445109087009751 : Int)/10^30,(180111892864421495880 : Int)/10^30)
theorem v3112_mg_checked : Scalar.distance (sourceCoefficient 40 53 3 2) v3112_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3112_upper : Scalar.QComplex := ((999996086033939605401689726176 : Int)/10^30,(-2797841453988927282463364504 : Int)/10^30)
theorem v3112_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 53 5) 1) 14) v3112_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3112 : Material (40 : Basis) (53 : Basis) where
  plus := ![v3112_pa,v3112_pb,v3112_pg]
  minus := ![(Primitive.Addresses.material3112 1).one,v3112_mb,v3112_mg]
  upper := v3112_upper
  lower := (Primitive.Addresses.material3112 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3112_pa_checked.trans (by decide +kernel)
    · exact v3112_pb_checked.trans (by decide +kernel)
    · exact v3112_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 53 Primitive.Addresses.material3112
    · exact v3112_mb_checked.trans (by decide +kernel)
    · exact v3112_mg_checked.trans (by decide +kernel)
  upper_error := v3112_upper_checked
  lower_error := reuse_lower_error 40 53 Primitive.Addresses.material3112

def v3113_pa : Scalar.QComplex := ((999999423458111762991580146565 : Int)/10^30,(-1073817230292691824159914913 : Int)/10^30)
theorem v3113_pa_checked : Scalar.distance (sourceCoefficient 40 54 1 0) v3113_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3113_pb : Scalar.QComplex := ((-463327994461725008482519 : Int)/10^30,(-431477270305523351608111492 : Int)/10^30)
theorem v3113_pb_checked : Scalar.distance (sourceCoefficient 40 54 1 1) v3113_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3113_pg : Scalar.QComplex := ((-93086376020533530736706 : Int)/10^30,(99957812106219096059 : Int)/10^30)
theorem v3113_pg_checked : Scalar.distance (sourceCoefficient 40 54 1 2) v3113_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3113_mb : Scalar.QComplex := ((-835673273202337047608157 : Int)/10^30,(-431476709815624429209645782 : Int)/10^30)
theorem v3113_mb_checked : Scalar.distance (sourceCoefficient 40 54 3 1) v3113_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3113_mg : Scalar.QComplex := ((-93086255101131565813932 : Int)/10^30,(180287124938333059052 : Int)/10^30)
theorem v3113_mg_checked : Scalar.distance (sourceCoefficient 40 54 3 2) v3113_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3113_upper : Scalar.QComplex := ((999996080765315159077879881289 : Int)/10^30,(-2799723916617731324143479267 : Int)/10^30)
theorem v3113_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 54 5) 1) 14) v3113_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3113 : Material (40 : Basis) (54 : Basis) where
  plus := ![v3113_pa,v3113_pb,v3113_pg]
  minus := ![(Primitive.Addresses.material3113 1).one,v3113_mb,v3113_mg]
  upper := v3113_upper
  lower := (Primitive.Addresses.material3113 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3113_pa_checked.trans (by decide +kernel)
    · exact v3113_pb_checked.trans (by decide +kernel)
    · exact v3113_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 54 Primitive.Addresses.material3113
    · exact v3113_mb_checked.trans (by decide +kernel)
    · exact v3113_mg_checked.trans (by decide +kernel)
  upper_error := v3113_upper_checked
  lower_error := reuse_lower_error 40 54 Primitive.Addresses.material3113

def v3114_pa : Scalar.QComplex := ((999999406864181070034955847635 : Int)/10^30,(-1089160817349683393660944004 : Int)/10^30)
theorem v3114_pa_checked : Scalar.distance (sourceCoefficient 40 55 1 0) v3114_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3114_pb : Scalar.QComplex := ((-469948406926489735775732 : Int)/10^30,(-431477262767134694919748735 : Int)/10^30)
theorem v3114_pb_checked : Scalar.distance (sourceCoefficient 40 55 1 1) v3114_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3114_pg : Scalar.QComplex := ((-93086374435037297665065 : Int)/10^30,(101386091799506483475 : Int)/10^30)
theorem v3114_pg_checked : Scalar.distance (sourceCoefficient 40 55 1 2) v3114_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3114_mb : Scalar.QComplex := ((-842293676696729752172269 : Int)/10^30,(-431476696564120794624678253 : Int)/10^30)
theorem v3114_mb_checked : Scalar.distance (sourceCoefficient 40 55 3 1) v3114_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3114_mg : Scalar.QComplex := ((-93086252283094875117427 : Int)/10^30,(181715402731594800009 : Int)/10^30)
theorem v3114_mg_checked : Scalar.distance (sourceCoefficient 40 55 3 2) v3114_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3114_upper : Scalar.QComplex := ((999996037689769879808734345935 : Int)/10^30,(-2815067452182633370191747626 : Int)/10^30)
theorem v3114_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 55 5) 1) 14) v3114_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3114 : Material (40 : Basis) (55 : Basis) where
  plus := ![v3114_pa,v3114_pb,v3114_pg]
  minus := ![(Primitive.Addresses.material3114 1).one,v3114_mb,v3114_mg]
  upper := v3114_upper
  lower := (Primitive.Addresses.material3114 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3114_pa_checked.trans (by decide +kernel)
    · exact v3114_pb_checked.trans (by decide +kernel)
    · exact v3114_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 55 Primitive.Addresses.material3114
    · exact v3114_mb_checked.trans (by decide +kernel)
    · exact v3114_mg_checked.trans (by decide +kernel)
  upper_error := v3114_upper_checked
  lower_error := reuse_lower_error 40 55 Primitive.Addresses.material3114

def v3115_pa : Scalar.QComplex := ((999999402891411119768632531080 : Int)/10^30,(-1092802279107156611898498043 : Int)/10^30)
theorem v3115_pa_checked : Scalar.distance (sourceCoefficient 40 56 1 0) v3115_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3115_pb : Scalar.QComplex := ((-471519615706422834896010 : Int)/10^30,(-431477260958178171670311649 : Int)/10^30)
theorem v3115_pb_checked : Scalar.distance (sourceCoefficient 40 56 1 1) v3115_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3115_pg : Scalar.QComplex := ((-93086374055000783868511 : Int)/10^30,(101725062462034648875 : Int)/10^30)
theorem v3115_pg_checked : Scalar.distance (sourceCoefficient 40 56 1 2) v3115_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3115_mb : Scalar.QComplex := ((-843864883330582007547980 : Int)/10^30,(-431476693399282532466705771 : Int)/10^30)
theorem v3115_mb_checked : Scalar.distance (sourceCoefficient 40 56 3 1) v3115_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3115_mg : Scalar.QComplex := ((-93086251610542087735945 : Int)/10^30,(182054372939954300828 : Int)/10^30)
theorem v3115_mg_checked : Scalar.distance (sourceCoefficient 40 56 3 2) v3115_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3115_upper : Scalar.QComplex := ((999996027432173203947881835321 : Int)/10^30,(-2818708901659936529534076418 : Int)/10^30)
theorem v3115_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 56 5) 1) 14) v3115_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3115 : Material (40 : Basis) (56 : Basis) where
  plus := ![v3115_pa,v3115_pb,v3115_pg]
  minus := ![(Primitive.Addresses.material3115 1).one,v3115_mb,v3115_mg]
  upper := v3115_upper
  lower := (Primitive.Addresses.material3115 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3115_pa_checked.trans (by decide +kernel)
    · exact v3115_pb_checked.trans (by decide +kernel)
    · exact v3115_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 56 Primitive.Addresses.material3115
    · exact v3115_mb_checked.trans (by decide +kernel)
    · exact v3115_mg_checked.trans (by decide +kernel)
  upper_error := v3115_upper_checked
  lower_error := reuse_lower_error 40 56 Primitive.Addresses.material3115

def v3116_pa : Scalar.QComplex := ((999999389951183944504643777820 : Int)/10^30,(-1104580128352593867055531494 : Int)/10^30)
theorem v3116_pa_checked : Scalar.distance (sourceCoefficient 40 57 1 0) v3116_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3116_pb : Scalar.QComplex := ((-476601492520159923794920 : Int)/10^30,(-431477255055096779437037516 : Int)/10^30)
theorem v3116_pb_checked : Scalar.distance (sourceCoefficient 40 57 1 1) v3116_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3116_pg : Scalar.QComplex := ((-93086372815959248264530 : Int)/10^30,(102821420359015426214 : Int)/10^30)
theorem v3116_pg_checked : Scalar.distance (sourceCoefficient 40 57 1 2) v3116_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3116_mb : Scalar.QComplex := ((-848946753158010728867863 : Int)/10^30,(-431476683110772527200604521 : Int)/10^30)
theorem v3116_mb_checked : Scalar.distance (sourceCoefficient 40 57 3 1) v3116_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3116_mg : Scalar.QComplex := ((-93086249425393526516021 : Int)/10^30,(183150729359473886223 : Int)/10^30)
theorem v3116_mg_checked : Scalar.distance (sourceCoefficient 40 57 3 2) v3116_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3116_upper : Scalar.QComplex := ((999995994164465982144555277170 : Int)/10^30,(-2830486711029992680705373852 : Int)/10^30)
theorem v3116_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 57 5) 1) 14) v3116_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3116 : Material (40 : Basis) (57 : Basis) where
  plus := ![v3116_pa,v3116_pb,v3116_pg]
  minus := ![(Primitive.Addresses.material3116 1).one,v3116_mb,v3116_mg]
  upper := v3116_upper
  lower := (Primitive.Addresses.material3116 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3116_pa_checked.trans (by decide +kernel)
    · exact v3116_pb_checked.trans (by decide +kernel)
    · exact v3116_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 57 Primitive.Addresses.material3116
    · exact v3116_mb_checked.trans (by decide +kernel)
    · exact v3116_mg_checked.trans (by decide +kernel)
  upper_error := v3116_upper_checked
  lower_error := reuse_lower_error 40 57 Primitive.Addresses.material3116

def v3117_pa : Scalar.QComplex := ((999999382871889530739724553854 : Int)/10^30,(-1110970674721621902601201764 : Int)/10^30)
theorem v3117_pa_checked : Scalar.distance (sourceCoefficient 40 58 1 0) v3117_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3117_pb : Scalar.QComplex := ((-479358869405934653803146 : Int)/10^30,(-431477251818744141981928715 : Int)/10^30)
theorem v3117_pb_checked : Scalar.distance (sourceCoefficient 40 58 1 1) v3117_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3117_pg : Scalar.QComplex := ((-93086372137362757316347 : Int)/10^30,(103416293481935676288 : Int)/10^30)
theorem v3117_pg_checked : Scalar.distance (sourceCoefficient 40 58 1 2) v3117_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3117_mb : Scalar.QComplex := ((-851704126224261459741214 : Int)/10^30,(-431476677494929030008772489 : Int)/10^30)
theorem v3117_mb_checked : Scalar.distance (sourceCoefficient 40 58 3 1) v3117_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3117_mg : Scalar.QComplex := ((-93086248233448575251036 : Int)/10^30,(183745601675297476752 : Int)/10^30)
theorem v3117_mg_checked : Scalar.distance (sourceCoefficient 40 58 3 2) v3117_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3117_upper : Scalar.QComplex := ((999995976055678825052555933330 : Int)/10^30,(-2836877235662832656307280195 : Int)/10^30)
theorem v3117_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 58 5) 1) 14) v3117_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3117 : Material (40 : Basis) (58 : Basis) where
  plus := ![v3117_pa,v3117_pb,v3117_pg]
  minus := ![(Primitive.Addresses.material3117 1).one,v3117_mb,v3117_mg]
  upper := v3117_upper
  lower := (Primitive.Addresses.material3117 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3117_pa_checked.trans (by decide +kernel)
    · exact v3117_pb_checked.trans (by decide +kernel)
    · exact v3117_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 58 Primitive.Addresses.material3117
    · exact v3117_mb_checked.trans (by decide +kernel)
    · exact v3117_mg_checked.trans (by decide +kernel)
  upper_error := v3117_upper_checked
  lower_error := reuse_lower_error 40 58 Primitive.Addresses.material3117

def v3118_pa : Scalar.QComplex := ((999999363202378934470252094825 : Int)/10^30,(-1128536590731487669601062328 : Int)/10^30)
theorem v3118_pa_checked : Scalar.distance (sourceCoefficient 40 59 1 0) v3118_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3118_pb : Scalar.QComplex := ((-486938166650855152033399 : Int)/10^30,(-431477242801820665766246635 : Int)/10^30)
theorem v3118_pb_checked : Scalar.distance (sourceCoefficient 40 59 1 1) v3118_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3118_pg : Scalar.QComplex := ((-93086370249230505737978 : Int)/10^30,(105051441821143818323 : Int)/10^30)
theorem v3118_pg_checked : Scalar.distance (sourceCoefficient 40 59 1 2) v3118_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3118_mb : Scalar.QComplex := ((-859283412865864349875239 : Int)/10^30,(-431476661937416747715478486 : Int)/10^30)
theorem v3118_mb_checked : Scalar.distance (sourceCoefficient 40 59 3 1) v3118_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3118_mg : Scalar.QComplex := ((-93086244934257654321361 : Int)/10^30,(185380747776292067337 : Int)/10^30)
theorem v3118_mg_checked : Scalar.distance (sourceCoefficient 40 59 3 2) v3118_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3118_upper : Scalar.QComplex := ((999995926069020058632408981480 : Int)/10^30,(-2854443091562539078956358830 : Int)/10^30)
theorem v3118_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 59 5) 1) 14) v3118_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3118 : Material (40 : Basis) (59 : Basis) where
  plus := ![v3118_pa,v3118_pb,v3118_pg]
  minus := ![(Primitive.Addresses.material3118 1).one,v3118_mb,v3118_mg]
  upper := v3118_upper
  lower := (Primitive.Addresses.material3118 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3118_pa_checked.trans (by decide +kernel)
    · exact v3118_pb_checked.trans (by decide +kernel)
    · exact v3118_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 59 Primitive.Addresses.material3118
    · exact v3118_mb_checked.trans (by decide +kernel)
    · exact v3118_mg_checked.trans (by decide +kernel)
  upper_error := v3118_upper_checked
  lower_error := reuse_lower_error 40 59 Primitive.Addresses.material3118

def v3119_pa : Scalar.QComplex := ((999999340128478930407765258282 : Int)/10^30,(-1148800507794438673221700876 : Int)/10^30)
theorem v3119_pa_checked : Scalar.distance (sourceCoefficient 40 60 1 0) v3119_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3119_pb : Scalar.QComplex := ((-495681590515659252301579 : Int)/10^30,(-431477232179452679054857493 : Int)/10^30)
theorem v3119_pb_checked : Scalar.distance (sourceCoefficient 40 60 1 1) v3119_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3119_pg : Scalar.QComplex := ((-93086368029468713846382 : Int)/10^30,(106937737426161115261 : Int)/10^30)
theorem v3119_pg_checked : Scalar.distance (sourceCoefficient 40 60 1 2) v3119_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3119_mb : Scalar.QComplex := ((-868026824308466992228518 : Int)/10^30,(-431476643769871710063947275 : Int)/10^30)
theorem v3119_mb_checked : Scalar.distance (sourceCoefficient 40 60 3 1) v3119_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3119_mg : Scalar.QComplex := ((-93086241086708537418951 : Int)/10^30,(187267040763400850516 : Int)/10^30)
theorem v3119_mg_checked : Scalar.distance (sourceCoefficient 40 60 3 2) v3119_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3119_upper : Scalar.QComplex := ((999995868021471897975814370045 : Int)/10^30,(-2874706938621307825066308515 : Int)/10^30)
theorem v3119_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 60 5) 1) 14) v3119_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3119 : Material (40 : Basis) (60 : Basis) where
  plus := ![v3119_pa,v3119_pb,v3119_pg]
  minus := ![(Primitive.Addresses.material3119 1).one,v3119_mb,v3119_mg]
  upper := v3119_upper
  lower := (Primitive.Addresses.material3119 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3119_pa_checked.trans (by decide +kernel)
    · exact v3119_pb_checked.trans (by decide +kernel)
    · exact v3119_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 60 Primitive.Addresses.material3119
    · exact v3119_mb_checked.trans (by decide +kernel)
    · exact v3119_mg_checked.trans (by decide +kernel)
  upper_error := v3119_upper_checked
  lower_error := reuse_lower_error 40 60 Primitive.Addresses.material3119

def v3120_pa : Scalar.QComplex := ((999999333380105338226034251970 : Int)/10^30,(-1154659839494499770757555396 : Int)/10^30)
theorem v3120_pa_checked : Scalar.distance (sourceCoefficient 40 61 1 0) v3120_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3120_pb : Scalar.QComplex := ((-498209760173055683174631 : Int)/10^30,(-431477229063955039216835811 : Int)/10^30)
theorem v3120_pb_checked : Scalar.distance (sourceCoefficient 40 61 1 1) v3120_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3120_pg : Scalar.QComplex := ((-93086367379310896132713 : Int)/10^30,(107483161667735067449 : Int)/10^30)
theorem v3120_pg_checked : Scalar.distance (sourceCoefficient 40 61 1 2) v3120_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3120_mb : Scalar.QComplex := ((-870554990335976170216274 : Int)/10^30,(-431476638472678680469481267 : Int)/10^30)
theorem v3120_mb_checked : Scalar.distance (sourceCoefficient 40 61 3 1) v3120_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3120_mg : Scalar.QComplex := ((-93086239965874406306375 : Int)/10^30,(187812464240831515781 : Int)/10^30)
theorem v3120_mg_checked : Scalar.distance (sourceCoefficient 40 61 3 2) v3120_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3120_upper : Scalar.QComplex := ((999995851160433396817929211276 : Int)/10^30,(-2880566249947502028376374445 : Int)/10^30)
theorem v3120_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 61 5) 1) 14) v3120_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3120 : Material (40 : Basis) (61 : Basis) where
  plus := ![v3120_pa,v3120_pb,v3120_pg]
  minus := ![(Primitive.Addresses.material3120 1).one,v3120_mb,v3120_mg]
  upper := v3120_upper
  lower := (Primitive.Addresses.material3120 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3120_pa_checked.trans (by decide +kernel)
    · exact v3120_pb_checked.trans (by decide +kernel)
    · exact v3120_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 61 Primitive.Addresses.material3120
    · exact v3120_mb_checked.trans (by decide +kernel)
    · exact v3120_mg_checked.trans (by decide +kernel)
  upper_error := v3120_upper_checked
  lower_error := reuse_lower_error 40 61 Primitive.Addresses.material3120

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
