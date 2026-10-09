import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B088

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2113_pa : Scalar.QComplex := ((999998921499964164969164346628 : Int)/10^30,(-1468672498723842236276422481 : Int)/10^30)
theorem v2113_pa_checked : Scalar.distance (sourceCoefficient 24 86 1 0) v2113_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2113_pb : Scalar.QComplex := ((-633699057667937022888301 : Int)/10^30,(-431476979908123367987555770 : Int)/10^30)
theorem v2113_pb_checked : Scalar.distance (sourceCoefficient 24 86 1 1) v2113_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2113_pg : Scalar.QComplex := ((-93086321332798482261272 : Int)/10^30,(136713467594331346891 : Int)/10^30)
theorem v2113_pg_checked : Scalar.distance (sourceCoefficient 24 86 1 2) v2113_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2113_mb : Scalar.QComplex := ((-1006044022371738715614496 : Int)/10^30,(-431476272395778254695153408 : Int)/10^30)
theorem v2113_mb_checked : Scalar.distance (sourceCoefficient 24 86 3 1) v2113_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2113_mg : Scalar.QComplex := ((-93086168694941607112093 : Int)/10^30,(217042719547582652539 : Int)/10^30)
theorem v2113_mg_checked : Scalar.distance (sourceCoefficient 24 86 3 2) v2113_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2113_upper : Scalar.QComplex := ((999994897323542846720409013837 : Int)/10^30,(-3194577730624116899362100563 : Int)/10^30)
theorem v2113_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 86 5) 1) 14) v2113_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2113 : Material (24 : Basis) (86 : Basis) where
  plus := ![v2113_pa,v2113_pb,v2113_pg]
  minus := ![(Primitive.Addresses.material2113 1).one,v2113_mb,v2113_mg]
  upper := v2113_upper
  lower := (Primitive.Addresses.material2113 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2113_pa_checked.trans (by decide +kernel)
    · exact v2113_pb_checked.trans (by decide +kernel)
    · exact v2113_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 86 Primitive.Addresses.material2113
    · exact v2113_mb_checked.trans (by decide +kernel)
    · exact v2113_mg_checked.trans (by decide +kernel)
  upper_error := v2113_upper_checked
  lower_error := reuse_lower_error 24 86 Primitive.Addresses.material2113

def v2114_pa : Scalar.QComplex := ((999998920081117898217238391043 : Int)/10^30,(-1469638254122004543044118509 : Int)/10^30)
theorem v2114_pa_checked : Scalar.distance (sourceCoefficient 24 87 1 0) v2114_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2114_pb : Scalar.QComplex := ((-634115759130279374033633 : Int)/10^30,(-431476979153303598793864015 : Int)/10^30)
theorem v2114_pb_checked : Scalar.distance (sourceCoefficient 24 87 1 1) v2114_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2114_pg : Scalar.QComplex := ((-93086321185338870598412 : Int)/10^30,(136803366285999969602 : Int)/10^30)
theorem v2114_pg_checked : Scalar.distance (sourceCoefficient 24 87 1 2) v2114_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2114_mb : Scalar.QComplex := ((-1006460723027548603138404 : Int)/10^30,(-431476271281364172091089825 : Int)/10^30)
theorem v2114_mb_checked : Scalar.distance (sourceCoefficient 24 87 3 1) v2114_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2114_mg : Scalar.QComplex := ((-93086168469903528331935 : Int)/10^30,(217132618078526880238 : Int)/10^30)
theorem v2114_mg_checked : Scalar.distance (sourceCoefficient 24 87 3 2) v2114_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2114_upper : Scalar.QComplex := ((999994894237892488590515371339 : Int)/10^30,(-3195543482135100046479243067 : Int)/10^30)
theorem v2114_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 87 5) 1) 14) v2114_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2114 : Material (24 : Basis) (87 : Basis) where
  plus := ![v2114_pa,v2114_pb,v2114_pg]
  minus := ![(Primitive.Addresses.material2114 1).one,v2114_mb,v2114_mg]
  upper := v2114_upper
  lower := (Primitive.Addresses.material2114 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2114_pa_checked.trans (by decide +kernel)
    · exact v2114_pb_checked.trans (by decide +kernel)
    · exact v2114_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 87 Primitive.Addresses.material2114
    · exact v2114_mb_checked.trans (by decide +kernel)
    · exact v2114_mg_checked.trans (by decide +kernel)
  upper_error := v2114_upper_checked
  lower_error := reuse_lower_error 24 87 Primitive.Addresses.material2114

def v2115_pa : Scalar.QComplex := ((999998902729625410986129813324 : Int)/10^30,(-1481397834876152635474588359 : Int)/10^30)
theorem v2115_pa_checked : Scalar.distance (sourceCoefficient 24 88 1 0) v2115_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2115_pb : Scalar.QComplex := ((-639189750401125617998151 : Int)/10^30,(-431476969919148050783172959 : Int)/10^30)
theorem v2115_pb_checked : Scalar.distance (sourceCoefficient 24 88 1 1) v2115_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2115_pg : Scalar.QComplex := ((-93086319381661938677832 : Int)/10^30,(137898023299999720806 : Int)/10^30)
theorem v2115_pg_checked : Scalar.distance (sourceCoefficient 24 88 1 2) v2115_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2115_mb : Scalar.QComplex := ((-1011534704440455657104107 : Int)/10^30,(-431476257668586119721848683 : Int)/10^30)
theorem v2115_mb_checked : Scalar.distance (sourceCoefficient 24 88 3 1) v2115_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2115_mg : Scalar.QComplex := ((-93086165721587566442676 : Int)/10^30,(218227273128443839179 : Int)/10^30)
theorem v2115_mg_checked : Scalar.distance (sourceCoefficient 24 88 3 2) v2115_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2115_upper : Scalar.QComplex := ((999994856590456283542078805946 : Int)/10^30,(-3207303015427632065139216566 : Int)/10^30)
theorem v2115_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 88 5) 1) 14) v2115_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2115 : Material (24 : Basis) (88 : Basis) where
  plus := ![v2115_pa,v2115_pb,v2115_pg]
  minus := ![(Primitive.Addresses.material2115 1).one,v2115_mb,v2115_mg]
  upper := v2115_upper
  lower := (Primitive.Addresses.material2115 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2115_pa_checked.trans (by decide +kernel)
    · exact v2115_pb_checked.trans (by decide +kernel)
    · exact v2115_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 88 Primitive.Addresses.material2115
    · exact v2115_mb_checked.trans (by decide +kernel)
    · exact v2115_mg_checked.trans (by decide +kernel)
  upper_error := v2115_upper_checked
  lower_error := reuse_lower_error 24 88 Primitive.Addresses.material2115

def v2116_pa : Scalar.QComplex := ((999998878765262254712847939226 : Int)/10^30,(-1497487301556589887258382451 : Int)/10^30)
theorem v2116_pa_checked : Scalar.distance (sourceCoefficient 24 89 1 0) v2116_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2116_pb : Scalar.QComplex := ((-646131988721137110850579 : Int)/10^30,(-431476957156079734480153604 : Int)/10^30)
theorem v2116_pb_checked : Scalar.distance (sourceCoefficient 24 89 1 1) v2116_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2116_pg : Scalar.QComplex := ((-93086316889539092624445 : Int)/10^30,(139395733786096528037 : Int)/10^30)
theorem v2116_pg_checked : Scalar.distance (sourceCoefficient 24 89 1 2) v2116_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2116_mb : Scalar.QComplex := ((-1018476929161601417740150 : Int)/10^30,(-431476238914683552329742049 : Int)/10^30)
theorem v2116_mb_checked : Scalar.distance (sourceCoefficient 24 89 3 1) v2116_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2116_mg : Scalar.QComplex := ((-93086161937008953195246 : Int)/10^30,(219724980906284808587 : Int)/10^30)
theorem v2116_mg_checked : Scalar.distance (sourceCoefficient 24 89 3 2) v2116_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2116_upper : Scalar.QComplex := ((999994804857168953953254148701 : Int)/10^30,(-3223392416784381920248635840 : Int)/10^30)
theorem v2116_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 89 5) 1) 14) v2116_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2116 : Material (24 : Basis) (89 : Basis) where
  plus := ![v2116_pa,v2116_pb,v2116_pg]
  minus := ![(Primitive.Addresses.material2116 1).one,v2116_mb,v2116_mg]
  upper := v2116_upper
  lower := (Primitive.Addresses.material2116 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2116_pa_checked.trans (by decide +kernel)
    · exact v2116_pb_checked.trans (by decide +kernel)
    · exact v2116_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 89 Primitive.Addresses.material2116
    · exact v2116_mb_checked.trans (by decide +kernel)
    · exact v2116_mg_checked.trans (by decide +kernel)
  upper_error := v2116_upper_checked
  lower_error := reuse_lower_error 24 89 Primitive.Addresses.material2116

def v2117_pa : Scalar.QComplex := ((999998839183393136319252273950 : Int)/10^30,(-1523690213341336233228940736 : Int)/10^30)
theorem v2117_pa_checked : Scalar.distance (sourceCoefficient 24 90 1 0) v2117_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2117_pb : Scalar.QComplex := ((-657437947909349588348309 : Int)/10^30,(-431476936051687404727576315 : Int)/10^30)
theorem v2117_pb_checked : Scalar.distance (sourceCoefficient 24 90 1 1) v2117_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2117_pg : Scalar.QComplex := ((-93086312770753810583769 : Int)/10^30,(141834868409098906792 : Int)/10^30)
theorem v2117_pg_checked : Scalar.distance (sourceCoefficient 24 90 1 2) v2117_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2117_mb : Scalar.QComplex := ((-1029782865927948507575184 : Int)/10^30,(-431476208053765502778968339 : Int)/10^30)
theorem v2117_mb_checked : Scalar.distance (sourceCoefficient 24 90 3 1) v2117_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2117_mg : Scalar.QComplex := ((-93086155713361879660942 : Int)/10^30,(222164111066759698042 : Int)/10^30)
theorem v2117_mg_checked : Scalar.distance (sourceCoefficient 24 90 3 2) v2117_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2117_upper : Scalar.QComplex := ((999994720051510157220055341939 : Int)/10^30,(-3249595221228253913845153076 : Int)/10^30)
theorem v2117_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 90 5) 1) 14) v2117_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2117 : Material (24 : Basis) (90 : Basis) where
  plus := ![v2117_pa,v2117_pb,v2117_pg]
  minus := ![(Primitive.Addresses.material2117 1).one,v2117_mb,v2117_mg]
  upper := v2117_upper
  lower := (Primitive.Addresses.material2117 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2117_pa_checked.trans (by decide +kernel)
    · exact v2117_pb_checked.trans (by decide +kernel)
    · exact v2117_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 90 Primitive.Addresses.material2117
    · exact v2117_mb_checked.trans (by decide +kernel)
    · exact v2117_mg_checked.trans (by decide +kernel)
  upper_error := v2117_upper_checked
  lower_error := reuse_lower_error 24 90 Primitive.Addresses.material2117

def v2118_pa : Scalar.QComplex := ((999998816583149252588518026401 : Int)/10^30,(-1538451267027779574127141251 : Int)/10^30)
theorem v2118_pa_checked : Scalar.distance (sourceCoefficient 24 91 1 0) v2118_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2118_pb : Scalar.QComplex := ((-663807005964338105877287 : Int)/10^30,(-431476923988880148452564054 : Int)/10^30)
theorem v2118_pb_checked : Scalar.distance (sourceCoefficient 24 91 1 1) v2118_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2118_pg : Scalar.QComplex := ((-93086310417658190711293 : Int)/10^30,(143208921680838535204 : Int)/10^30)
theorem v2118_pg_checked : Scalar.distance (sourceCoefficient 24 91 1 2) v2118_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2118_mb : Scalar.QComplex := ((-1036151911201786257404827 : Int)/10^30,(-431476190494752488309664554 : Int)/10^30)
theorem v2118_mb_checked : Scalar.distance (sourceCoefficient 24 91 3 1) v2118_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2118_mg : Scalar.QComplex := ((-93086152174521047504286 : Int)/10^30,(223538161796260955590 : Int)/10^30)
theorem v2118_mg_checked : Scalar.distance (sourceCoefficient 24 91 3 2) v2118_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2118_upper : Scalar.QComplex := ((999994671975060383426431062463 : Int)/10^30,(-3264356213923871078745705353 : Int)/10^30)
theorem v2118_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 91 5) 1) 14) v2118_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2118 : Material (24 : Basis) (91 : Basis) where
  plus := ![v2118_pa,v2118_pb,v2118_pg]
  minus := ![(Primitive.Addresses.material2118 1).one,v2118_mb,v2118_mg]
  upper := v2118_upper
  lower := (Primitive.Addresses.material2118 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2118_pa_checked.trans (by decide +kernel)
    · exact v2118_pb_checked.trans (by decide +kernel)
    · exact v2118_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 91 Primitive.Addresses.material2118
    · exact v2118_mb_checked.trans (by decide +kernel)
    · exact v2118_mg_checked.trans (by decide +kernel)
  upper_error := v2118_upper_checked
  lower_error := reuse_lower_error 24 91 Primitive.Addresses.material2118

def v2119_pa : Scalar.QComplex := ((999998766909643882567859564228 : Int)/10^30,(-1570407333058222168927091784 : Int)/10^30)
theorem v2119_pa_checked : Scalar.distance (sourceCoefficient 24 92 1 0) v2119_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2119_pb : Scalar.QComplex := ((-677595319328758441848449 : Int)/10^30,(-431476897444787534262859858 : Int)/10^30)
theorem v2119_pb_checked : Scalar.distance (sourceCoefficient 24 92 1 1) v2119_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2119_pg : Scalar.QComplex := ((-93086305242398582567650 : Int)/10^30,(146183596617541974814 : Int)/10^30)
theorem v2119_pg_checked : Scalar.distance (sourceCoefficient 24 92 1 2) v2119_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2119_mb : Scalar.QComplex := ((-1049940196525830946257679 : Int)/10^30,(-431476152051976326785249715 : Int)/10^30)
theorem v2119_mb_checked : Scalar.distance (sourceCoefficient 24 92 3 1) v2119_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2119_mg : Scalar.QComplex := ((-93086144432252870357033 : Int)/10^30,(226512831159341010117 : Int)/10^30)
theorem v2119_mg_checked : Scalar.distance (sourceCoefficient 24 92 3 2) v2119_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2119_upper : Scalar.QComplex := ((999994567148358059377331956399 : Int)/10^30,(-3296312146627543220958919750 : Int)/10^30)
theorem v2119_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 92 5) 1) 14) v2119_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2119 : Material (24 : Basis) (92 : Basis) where
  plus := ![v2119_pa,v2119_pb,v2119_pg]
  minus := ![(Primitive.Addresses.material2119 1).one,v2119_mb,v2119_mg]
  upper := v2119_upper
  lower := (Primitive.Addresses.material2119 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2119_pa_checked.trans (by decide +kernel)
    · exact v2119_pb_checked.trans (by decide +kernel)
    · exact v2119_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 92 Primitive.Addresses.material2119
    · exact v2119_mb_checked.trans (by decide +kernel)
    · exact v2119_mg_checked.trans (by decide +kernel)
  upper_error := v2119_upper_checked
  lower_error := reuse_lower_error 24 92 Primitive.Addresses.material2119

def v2120_pa : Scalar.QComplex := ((999998706631810047941578986711 : Int)/10^30,(-1608332896854019479507479619 : Int)/10^30)
theorem v2120_pa_checked : Scalar.distance (sourceCoefficient 24 93 1 0) v2120_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2120_pb : Scalar.QComplex := ((-693959334045056967954876 : Int)/10^30,(-431476865179806373831264298 : Int)/10^30)
theorem v2120_pb_checked : Scalar.distance (sourceCoefficient 24 93 1 1) v2120_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2120_pg : Scalar.QComplex := ((-93086298956470698903992 : Int)/10^30,(149713950493340969836 : Int)/10^30)
theorem v2120_pg_checked : Scalar.distance (sourceCoefficient 24 93 1 2) v2120_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2120_mb : Scalar.QComplex := ((-1066304177305833340423117 : Int)/10^30,(-431476105665599487778898798 : Int)/10^30)
theorem v2120_mb_checked : Scalar.distance (sourceCoefficient 24 93 3 1) v2120_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2120_mg : Scalar.QComplex := ((-93086135099790933653238 : Int)/10^30,(230043178296155256118 : Int)/10^30)
theorem v2120_mg_checked : Scalar.distance (sourceCoefficient 24 93 3 2) v2120_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2120_upper : Scalar.QComplex := ((999994441414531470228874819957 : Int)/10^30,(-3334237549903595471176853039 : Int)/10^30)
theorem v2120_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 93 5) 1) 14) v2120_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2120 : Material (24 : Basis) (93 : Basis) where
  plus := ![v2120_pa,v2120_pb,v2120_pg]
  minus := ![(Primitive.Addresses.material2120 1).one,v2120_mb,v2120_mg]
  upper := v2120_upper
  lower := (Primitive.Addresses.material2120 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2120_pa_checked.trans (by decide +kernel)
    · exact v2120_pb_checked.trans (by decide +kernel)
    · exact v2120_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 93 Primitive.Addresses.material2120
    · exact v2120_mb_checked.trans (by decide +kernel)
    · exact v2120_mg_checked.trans (by decide +kernel)
  upper_error := v2120_upper_checked
  lower_error := reuse_lower_error 24 93 Primitive.Addresses.material2120

def v2121_pa : Scalar.QComplex := ((999998633577362239393639324466 : Int)/10^30,(-1653131394780943520115597022 : Int)/10^30)
theorem v2121_pa_checked : Scalar.distance (sourceCoefficient 24 94 1 0) v2121_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2121_pb : Scalar.QComplex := ((-713288861837886867321826 : Int)/10^30,(-431476826001696364971259869 : Int)/10^30)
theorem v2121_pb_checked : Scalar.distance (sourceCoefficient 24 94 1 1) v2121_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2121_pg : Scalar.QComplex := ((-93086291330163157677788 : Int)/10^30,(153884080892309593361 : Int)/10^30)
theorem v2121_pg_checked : Scalar.distance (sourceCoefficient 24 94 1 2) v2121_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2121_mb : Scalar.QComplex := ((-1085633664092452218385048 : Int)/10^30,(-431476049806992151122301478 : Int)/10^30)
theorem v2121_mb_checked : Scalar.distance (sourceCoefficient 24 94 3 1) v2121_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2121_mg : Scalar.QComplex := ((-93086123874851513441072 : Int)/10^30,(234213300561233815796 : Int)/10^30)
theorem v2121_mg_checked : Scalar.distance (sourceCoefficient 24 94 3 2) v2121_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2121_upper : Scalar.QComplex := ((999994291042049133813491067197 : Int)/10^30,(-3379035855023069781042299873 : Int)/10^30)
theorem v2121_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 94 5) 1) 14) v2121_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2121 : Material (24 : Basis) (94 : Basis) where
  plus := ![v2121_pa,v2121_pb,v2121_pg]
  minus := ![(Primitive.Addresses.material2121 1).one,v2121_mb,v2121_mg]
  upper := v2121_upper
  lower := (Primitive.Addresses.material2121 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2121_pa_checked.trans (by decide +kernel)
    · exact v2121_pb_checked.trans (by decide +kernel)
    · exact v2121_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 94 Primitive.Addresses.material2121
    · exact v2121_mb_checked.trans (by decide +kernel)
    · exact v2121_mg_checked.trans (by decide +kernel)
  upper_error := v2121_upper_checked
  lower_error := reuse_lower_error 24 94 Primitive.Addresses.material2121

def v2122_pa : Scalar.QComplex := ((999998559406151026711668009554 : Int)/10^30,(-1697405556322925132514158817 : Int)/10^30)
theorem v2122_pa_checked : Scalar.distance (sourceCoefficient 24 95 1 0) v2122_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2122_pb : Scalar.QComplex := ((-732392149311172583727871 : Int)/10^30,(-431476786147748741894026720 : Int)/10^30)
theorem v2122_pb_checked : Scalar.distance (sourceCoefficient 24 95 1 1) v2122_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2122_pg : Scalar.QComplex := ((-93086283578975665463722 : Int)/10^30,(158005402586015829769 : Int)/10^30)
theorem v2122_pg_checked : Scalar.distance (sourceCoefficient 24 95 1 2) v2122_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2122_mb : Scalar.QComplex := ((-1104736910060549101572509 : Int)/10^30,(-431475993467782658174595632 : Int)/10^30)
theorem v2122_mb_checked : Scalar.distance (sourceCoefficient 24 95 3 1) v2122_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2122_mg : Scalar.QComplex := ((-93086112567151903118515 : Int)/10^30,(238334614031457926675 : Int)/10^30)
theorem v2122_mg_checked : Scalar.distance (sourceCoefficient 24 95 3 2) v2122_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2122_upper : Scalar.QComplex := ((999994140457762089537347322040 : Int)/10^30,(-3423309822611106791640777465 : Int)/10^30)
theorem v2122_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 95 5) 1) 14) v2122_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2122 : Material (24 : Basis) (95 : Basis) where
  plus := ![v2122_pa,v2122_pb,v2122_pg]
  minus := ![(Primitive.Addresses.material2122 1).one,v2122_mb,v2122_mg]
  upper := v2122_upper
  lower := (Primitive.Addresses.material2122 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2122_pa_checked.trans (by decide +kernel)
    · exact v2122_pb_checked.trans (by decide +kernel)
    · exact v2122_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 95 Primitive.Addresses.material2122
    · exact v2122_mb_checked.trans (by decide +kernel)
    · exact v2122_mg_checked.trans (by decide +kernel)
  upper_error := v2122_upper_checked
  lower_error := reuse_lower_error 24 95 Primitive.Addresses.material2122

def v2123_pa : Scalar.QComplex := ((999998523086274649918933842376 : Int)/10^30,(-1718669621953564990880604165 : Int)/10^30)
theorem v2123_pa_checked : Scalar.distance (sourceCoefficient 24 96 1 0) v2123_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2123_pb : Scalar.QComplex := ((-741567106574698298297588 : Int)/10^30,(-431476766605755458899636881 : Int)/10^30)
theorem v2123_pb_checked : Scalar.distance (sourceCoefficient 24 96 1 1) v2123_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2123_pg : Scalar.QComplex := ((-93086279780549031544497 : Int)/10^30,(159984797563243353255 : Int)/10^30)
theorem v2123_pg_checked : Scalar.distance (sourceCoefficient 24 96 1 2) v2123_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2123_mb : Scalar.QComplex := ((-1113911847043958846151038 : Int)/10^30,(-431475966008221757870252563 : Int)/10^30)
theorem v2123_mb_checked : Scalar.distance (sourceCoefficient 24 96 3 1) v2123_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2123_mg : Scalar.QComplex := ((-93086107060597966820191 : Int)/10^30,(240314004993795127032 : Int)/10^30)
theorem v2123_mg_checked : Scalar.distance (sourceCoefficient 24 96 3 2) v2123_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2123_upper : Scalar.QComplex := ((999994067438091589414662818996 : Int)/10^30,(-3444573793886607032884896843 : Int)/10^30)
theorem v2123_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 96 5) 1) 14) v2123_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2123 : Material (24 : Basis) (96 : Basis) where
  plus := ![v2123_pa,v2123_pb,v2123_pg]
  minus := ![(Primitive.Addresses.material2123 1).one,v2123_mb,v2123_mg]
  upper := v2123_upper
  lower := (Primitive.Addresses.material2123 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2123_pa_checked.trans (by decide +kernel)
    · exact v2123_pb_checked.trans (by decide +kernel)
    · exact v2123_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 96 Primitive.Addresses.material2123
    · exact v2123_mb_checked.trans (by decide +kernel)
    · exact v2123_mg_checked.trans (by decide +kernel)
  upper_error := v2123_upper_checked
  lower_error := reuse_lower_error 24 96 Primitive.Addresses.material2123

def v2124_pa : Scalar.QComplex := ((999998394668232591969828253244 : Int)/10^30,(-1791831732536840886188590044 : Int)/10^30)
theorem v2124_pa_checked : Scalar.distance (sourceCoefficient 24 97 1 0) v2124_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2124_pb : Scalar.QComplex := ((-773134879356280493902612 : Int)/10^30,(-431476697381461396900117357 : Int)/10^30)
theorem v2124_pb_checked : Scalar.distance (sourceCoefficient 24 97 1 1) v2124_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2124_pg : Scalar.QComplex := ((-93086266336378378694928 : Int)/10^30,(166795193646521690352 : Int)/10^30)
theorem v2124_pg_checked : Scalar.distance (sourceCoefficient 24 97 1 2) v2124_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2124_mb : Scalar.QComplex := ((-1145479548333968487647932 : Int)/10^30,(-431475869542387320441565288 : Int)/10^30)
theorem v2124_mb_checked : Scalar.distance (sourceCoefficient 24 97 3 1) v2124_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2124_mg : Scalar.QComplex := ((-93086087739367228833861 : Int)/10^30,(247124386939537981407 : Int)/10^30)
theorem v2124_mg_checked : Scalar.distance (sourceCoefficient 24 97 3 2) v2124_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2124_upper : Scalar.QComplex := ((999993812749075143145002217076 : Int)/10^30,(-3517735573865622841374526426 : Int)/10^30)
theorem v2124_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 97 5) 1) 14) v2124_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2124 : Material (24 : Basis) (97 : Basis) where
  plus := ![v2124_pa,v2124_pb,v2124_pg]
  minus := ![(Primitive.Addresses.material2124 1).one,v2124_mb,v2124_mg]
  upper := v2124_upper
  lower := (Primitive.Addresses.material2124 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2124_pa_checked.trans (by decide +kernel)
    · exact v2124_pb_checked.trans (by decide +kernel)
    · exact v2124_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 97 Primitive.Addresses.material2124
    · exact v2124_mb_checked.trans (by decide +kernel)
    · exact v2124_mg_checked.trans (by decide +kernel)
  upper_error := v2124_upper_checked
  lower_error := reuse_lower_error 24 97 Primitive.Addresses.material2124

def v2125_pa : Scalar.QComplex := ((999999877143884797433518725728 : Int)/10^30,(-495693670840679505929050111 : Int)/10^30)
theorem v2125_pa_checked : Scalar.distance (sourceCoefficient 25 26 1 0) v2125_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2125_pb : Scalar.QComplex := ((-213880676268127356569054 : Int)/10^30,(-431477467987122144937297566 : Int)/10^30)
theorem v2125_pb_checked : Scalar.distance (sourceCoefficient 25 26 1 1) v2125_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2125_pg : Scalar.QComplex := ((-93086418460320523484201 : Int)/10^30,(46142354140878249991 : Int)/10^30)
theorem v2125_pg_checked : Scalar.distance (sourceCoefficient 25 26 1 2) v2125_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2125_mb : Scalar.QComplex := ((-586226218479692774736634 : Int)/10^30,(-431477122758950527559742096 : Int)/10^30)
theorem v2125_mb_checked : Scalar.distance (sourceCoefficient 25 26 3 1) v2125_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2125_mg : Scalar.QComplex := ((-93086343981219222125663 : Int)/10^30,(126471723634571459101 : Int)/10^30)
theorem v2125_mg_checked : Scalar.distance (sourceCoefficient 25 26 3 2) v2125_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2125_upper : Scalar.QComplex := ((999997532239229136407498197378 : Int)/10^30,(-2221602001233335851518821137 : Int)/10^30)
theorem v2125_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 26 5) 1) 14) v2125_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2125 : Material (25 : Basis) (26 : Basis) where
  plus := ![v2125_pa,v2125_pb,v2125_pg]
  minus := ![(Primitive.Addresses.material2125 1).one,v2125_mb,v2125_mg]
  upper := v2125_upper
  lower := (Primitive.Addresses.material2125 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2125_pa_checked.trans (by decide +kernel)
    · exact v2125_pb_checked.trans (by decide +kernel)
    · exact v2125_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 26 Primitive.Addresses.material2125
    · exact v2125_mb_checked.trans (by decide +kernel)
    · exact v2125_mg_checked.trans (by decide +kernel)
  upper_error := v2125_upper_checked
  lower_error := reuse_lower_error 25 26 Primitive.Addresses.material2125

def v2126_pa : Scalar.QComplex := ((999999874630267304436748298277 : Int)/10^30,(-500738903694886310604468840 : Int)/10^30)
theorem v2126_pa_checked : Scalar.distance (sourceCoefficient 25 27 1 0) v2126_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2126_pb : Scalar.QComplex := ((-216057580829326941917168 : Int)/10^30,(-431477466895393189401336571 : Int)/10^30)
theorem v2126_pb_checked : Scalar.distance (sourceCoefficient 25 27 1 1) v2126_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2126_pg : Scalar.QComplex := ((-93086418225564552900616 : Int)/10^30,(46611996854886464607 : Int)/10^30)
theorem v2126_pg_checked : Scalar.distance (sourceCoefficient 25 27 1 2) v2126_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2126_mb : Scalar.QComplex := ((-588403121288218383516177 : Int)/10^30,(-431477119788651386350990374 : Int)/10^30)
theorem v2126_mb_checked : Scalar.distance (sourceCoefficient 25 27 3 1) v2126_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2126_mg : Scalar.QComplex := ((-93086343341182828686008 : Int)/10^30,(126941365971126397961 : Int)/10^30)
theorem v2126_mg_checked : Scalar.distance (sourceCoefficient 25 27 3 2) v2126_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2126_upper : Scalar.QComplex := ((999997521018001180736946314629 : Int)/10^30,(-2226647222234985215221218441 : Int)/10^30)
theorem v2126_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 27 5) 1) 14) v2126_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2126 : Material (25 : Basis) (27 : Basis) where
  plus := ![v2126_pa,v2126_pb,v2126_pg]
  minus := ![(Primitive.Addresses.material2126 1).one,v2126_mb,v2126_mg]
  upper := v2126_upper
  lower := (Primitive.Addresses.material2126 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2126_pa_checked.trans (by decide +kernel)
    · exact v2126_pb_checked.trans (by decide +kernel)
    · exact v2126_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 27 Primitive.Addresses.material2126
    · exact v2126_mb_checked.trans (by decide +kernel)
    · exact v2126_mg_checked.trans (by decide +kernel)
  upper_error := v2126_upper_checked
  lower_error := reuse_lower_error 25 27 Primitive.Addresses.material2126

def v2127_pa : Scalar.QComplex := ((999999871203856228866973557178 : Int)/10^30,(-507535487383709359641332079 : Int)/10^30)
theorem v2127_pa_checked : Scalar.distance (sourceCoefficient 25 28 1 0) v2127_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2127_pb : Scalar.QComplex := ((-218990153902746156538310 : Int)/10^30,(-431477465401541209016538039 : Int)/10^30)
theorem v2127_pb_checked : Scalar.distance (sourceCoefficient 25 28 1 1) v2127_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2127_pg : Scalar.QComplex := ((-93086417904947470914371 : Int)/10^30,(47244666565122031506 : Int)/10^30)
theorem v2127_pg_checked : Scalar.distance (sourceCoefficient 25 28 1 2) v2127_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2127_mb : Scalar.QComplex := ((-591335691980579639216453 : Int)/10^30,(-431477115764121478023028316 : Int)/10^30)
theorem v2127_mb_checked : Scalar.distance (sourceCoefficient 25 28 3 1) v2127_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2127_mg : Scalar.QComplex := ((-93086342474600400532849 : Int)/10^30,(127574035169112015609 : Int)/10^30)
theorem v2127_mg_checked : Scalar.distance (sourceCoefficient 25 28 3 2) v2127_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2127_upper : Scalar.QComplex := ((999997505861308342751173055332 : Int)/10^30,(-2233443789887420567710755649 : Int)/10^30)
theorem v2127_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 28 5) 1) 14) v2127_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2127 : Material (25 : Basis) (28 : Basis) where
  plus := ![v2127_pa,v2127_pb,v2127_pg]
  minus := ![(Primitive.Addresses.material2127 1).one,v2127_mb,v2127_mg]
  upper := v2127_upper
  lower := (Primitive.Addresses.material2127 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2127_pa_checked.trans (by decide +kernel)
    · exact v2127_pb_checked.trans (by decide +kernel)
    · exact v2127_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 28 Primitive.Addresses.material2127
    · exact v2127_mb_checked.trans (by decide +kernel)
    · exact v2127_mg_checked.trans (by decide +kernel)
  upper_error := v2127_upper_checked
  lower_error := reuse_lower_error 25 28 Primitive.Addresses.material2127

def v2128_pa : Scalar.QComplex := ((999999864122706458215796747085 : Int)/10^30,(-521300842720333137066714156 : Int)/10^30)
theorem v2128_pa_checked : Scalar.distance (sourceCoefficient 25 29 1 0) v2128_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2128_pb : Scalar.QComplex := ((-224929595271816640984232 : Int)/10^30,(-431477462294573627434600071 : Int)/10^30)
theorem v2128_pb_checked : Scalar.distance (sourceCoefficient 25 29 1 1) v2128_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2128_pg : Scalar.QComplex := ((-93086417240221312026809 : Int)/10^30,(48526034346730130524 : Int)/10^30)
theorem v2128_pg_checked : Scalar.distance (sourceCoefficient 25 29 1 2) v2128_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2128_mb : Scalar.QComplex := ((-597275128456951565797287 : Int)/10^30,(-431477107531684654308391353 : Int)/10^30)
theorem v2128_mb_checked : Scalar.distance (sourceCoefficient 25 29 3 1) v2128_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2128_mg : Scalar.QComplex := ((-93086340704111804287989 : Int)/10^30,(128855401899979591169 : Int)/10^30)
theorem v2128_mg_checked : Scalar.distance (sourceCoefficient 25 29 3 2) v2128_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2128_upper : Scalar.QComplex := ((999997475022414590909308363422 : Int)/10^30,(-2247209112500742456205502869 : Int)/10^30)
theorem v2128_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 29 5) 1) 14) v2128_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2128 : Material (25 : Basis) (29 : Basis) where
  plus := ![v2128_pa,v2128_pb,v2128_pg]
  minus := ![(Primitive.Addresses.material2128 1).one,v2128_mb,v2128_mg]
  upper := v2128_upper
  lower := (Primitive.Addresses.material2128 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2128_pa_checked.trans (by decide +kernel)
    · exact v2128_pb_checked.trans (by decide +kernel)
    · exact v2128_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 29 Primitive.Addresses.material2128
    · exact v2128_mb_checked.trans (by decide +kernel)
    · exact v2128_mg_checked.trans (by decide +kernel)
  upper_error := v2128_upper_checked
  lower_error := reuse_lower_error 25 29 Primitive.Addresses.material2128

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
