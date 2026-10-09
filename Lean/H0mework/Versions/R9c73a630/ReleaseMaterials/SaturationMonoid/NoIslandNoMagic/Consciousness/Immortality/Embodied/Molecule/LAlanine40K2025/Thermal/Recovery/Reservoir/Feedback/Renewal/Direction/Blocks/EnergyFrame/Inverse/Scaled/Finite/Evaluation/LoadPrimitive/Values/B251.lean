import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B167
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B168

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4017_pa : Scalar.QComplex := ((999998907867103706144600208088 : Int)/10^30,(-1477925776158413048868029128 : Int)/10^30)
theorem v4017_pa_checked : Scalar.distance (sourceCoefficient 59 65 1 0) v4017_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4017_pb : Scalar.QComplex := ((-637691748300465259090841 : Int)/10^30,(-431477048538855479191437196 : Int)/10^30)
theorem v4017_pb_checked : Scalar.distance (sourceCoefficient 59 65 1 1) v4017_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4017_pg : Scalar.QComplex := ((-93086328101436279651952 : Int)/10^30,(137574833959053778209 : Int)/10^30)
theorem v4017_pg_checked : Scalar.distance (sourceCoefficient 59 65 1 2) v4017_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4017_mb : Scalar.QComplex := ((-1010036770742836552888893 : Int)/10^30,(-431476337580972619779726887 : Int)/10^30)
theorem v4017_mb_checked : Scalar.distance (sourceCoefficient 59 65 3 1) v4017_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4017_mg : Scalar.QComplex := ((-93086174720256505975068 : Int)/10^30,(217904091432608590902 : Int)/10^30)
theorem v4017_mg_checked : Scalar.distance (sourceCoefficient 59 65 3 2) v4017_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4017_upper : Scalar.QComplex := ((999994867720385291142282176532 : Int)/10^30,(-3203830970747937550991727237 : Int)/10^30)
theorem v4017_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 65 5) 1) 14) v4017_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4017 : Material (59 : Basis) (65 : Basis) where
  plus := ![v4017_pa,v4017_pb,v4017_pg]
  minus := ![(Primitive.Addresses.material4017 1).one,v4017_mb,v4017_mg]
  upper := v4017_upper
  lower := (Primitive.Addresses.material4017 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4017_pa_checked.trans (by decide +kernel)
    · exact v4017_pb_checked.trans (by decide +kernel)
    · exact v4017_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 65 Primitive.Addresses.material4017
    · exact v4017_mb_checked.trans (by decide +kernel)
    · exact v4017_mg_checked.trans (by decide +kernel)
  upper_error := v4017_upper_checked
  lower_error := reuse_lower_error 59 65 Primitive.Addresses.material4017

def v4018_pa : Scalar.QComplex := ((999998881719324728679463191555 : Int)/10^30,(-1495513323240877178490444447 : Int)/10^30)
theorem v4018_pa_checked : Scalar.distance (sourceCoefficient 59 66 1 0) v4018_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4018_pb : Scalar.QComplex := ((-645280378966224603259610 : Int)/10^30,(-431477036903477791580739015 : Int)/10^30)
theorem v4018_pb_checked : Scalar.distance (sourceCoefficient 59 66 1 1) v4018_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4018_pg : Scalar.QComplex := ((-93086325629333544052450 : Int)/10^30,(139211995868291791677 : Int)/10^30)
theorem v4018_pg_checked : Scalar.distance (sourceCoefficient 59 66 1 2) v4018_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4018_mb : Scalar.QComplex := ((-1017625388542194976190713 : Int)/10^30,(-431476319396952779239334933 : Int)/10^30)
theorem v4018_mb_checked : Scalar.distance (sourceCoefficient 59 66 3 1) v4018_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4018_mg : Scalar.QComplex := ((-93086170835357698215209 : Int)/10^30,(219541250598943082116 : Int)/10^30)
theorem v4018_mg_checked : Scalar.distance (sourceCoefficient 59 66 3 2) v4018_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4018_upper : Scalar.QComplex := ((999994811218134523197036753769 : Int)/10^30,(-3221418446507121872565313899 : Int)/10^30)
theorem v4018_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 66 5) 1) 14) v4018_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4018 : Material (59 : Basis) (66 : Basis) where
  plus := ![v4018_pa,v4018_pb,v4018_pg]
  minus := ![(Primitive.Addresses.material4018 1).one,v4018_mb,v4018_mg]
  upper := v4018_upper
  lower := (Primitive.Addresses.material4018 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4018_pa_checked.trans (by decide +kernel)
    · exact v4018_pb_checked.trans (by decide +kernel)
    · exact v4018_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 66 Primitive.Addresses.material4018
    · exact v4018_mb_checked.trans (by decide +kernel)
    · exact v4018_mg_checked.trans (by decide +kernel)
  upper_error := v4018_upper_checked
  lower_error := reuse_lower_error 59 66 Primitive.Addresses.material4018

def v4019_pa : Scalar.QComplex := ((999998837140395439523364636091 : Int)/10^30,(-1525030444574302048441566213 : Int)/10^30)
theorem v4019_pa_checked : Scalar.distance (sourceCoefficient 59 67 1 0) v4019_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4019_pb : Scalar.QComplex := ((-658016352203003981269257 : Int)/10^30,(-431477016975912075268712667 : Int)/10^30)
theorem v4019_pb_checked : Scalar.distance (sourceCoefficient 59 67 1 1) v4019_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4019_pg : Scalar.QComplex := ((-93086321404912592841476 : Int)/10^30,(141959639195050118211 : Int)/10^30)
theorem v4019_pg_checked : Scalar.distance (sourceCoefficient 59 67 1 2) v4019_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4019_mb : Scalar.QComplex := ((-1030361339840197746481655 : Int)/10^30,(-431476288478823186471450273 : Int)/10^30)
theorem v4019_mb_checked : Scalar.distance (sourceCoefficient 59 67 3 1) v4019_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4019_mg : Scalar.QComplex := ((-93086164239845878218433 : Int)/10^30,(222288889257143204556 : Int)/10^30)
theorem v4019_mg_checked : Scalar.distance (sourceCoefficient 59 67 3 2) v4019_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4019_upper : Scalar.QComplex := ((999994715695397979957938763547 : Int)/10^30,(-3250935446939074056808559891 : Int)/10^30)
theorem v4019_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 67 5) 1) 14) v4019_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4019 : Material (59 : Basis) (67 : Basis) where
  plus := ![v4019_pa,v4019_pb,v4019_pg]
  minus := ![(Primitive.Addresses.material4019 1).one,v4019_mb,v4019_mg]
  upper := v4019_upper
  lower := (Primitive.Addresses.material4019 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4019_pa_checked.trans (by decide +kernel)
    · exact v4019_pb_checked.trans (by decide +kernel)
    · exact v4019_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 67 Primitive.Addresses.material4019
    · exact v4019_mb_checked.trans (by decide +kernel)
    · exact v4019_mg_checked.trans (by decide +kernel)
  upper_error := v4019_upper_checked
  lower_error := reuse_lower_error 59 67 Primitive.Addresses.material4019

def v4020_pa : Scalar.QComplex := ((999998760964722455643373552645 : Int)/10^30,(-1574188368614218370687576567 : Int)/10^30)
theorem v4020_pa_checked : Scalar.distance (sourceCoefficient 59 68 1 0) v4020_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4020_pb : Scalar.QComplex := ((-679226889039352512103258 : Int)/10^30,(-431476982675973150343319081 : Int)/10^30)
theorem v4020_pb_checked : Scalar.distance (sourceCoefficient 59 68 1 1) v4020_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4020_pg : Scalar.QComplex := ((-93086314159538545874482 : Int)/10^30,(146535574589860931450 : Int)/10^30)
theorem v4020_pg_checked : Scalar.distance (sourceCoefficient 59 68 1 2) v4020_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4020_mb : Scalar.QComplex := ((-1051571839179591563414306 : Int)/10^30,(-431476235875159030329305421 : Int)/10^30)
theorem v4020_mb_checked : Scalar.distance (sourceCoefficient 59 68 3 1) v4020_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4020_mg : Scalar.QComplex := ((-93086153045648375793265 : Int)/10^30,(226864816695692656729 : Int)/10^30)
theorem v4020_mg_checked : Scalar.distance (sourceCoefficient 59 68 3 2) v4020_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4020_upper : Scalar.QComplex := ((999994554677721129931698093632 : Int)/10^30,(-3300093166291736049886678531 : Int)/10^30)
theorem v4020_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 68 5) 1) 14) v4020_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4020 : Material (59 : Basis) (68 : Basis) where
  plus := ![v4020_pa,v4020_pb,v4020_pg]
  minus := ![(Primitive.Addresses.material4020 1).one,v4020_mb,v4020_mg]
  upper := v4020_upper
  lower := (Primitive.Addresses.material4020 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4020_pa_checked.trans (by decide +kernel)
    · exact v4020_pb_checked.trans (by decide +kernel)
    · exact v4020_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 68 Primitive.Addresses.material4020
    · exact v4020_mb_checked.trans (by decide +kernel)
    · exact v4020_mg_checked.trans (by decide +kernel)
  upper_error := v4020_upper_checked
  lower_error := reuse_lower_error 59 68 Primitive.Addresses.material4020

def v4021_pa : Scalar.QComplex := ((999998726672501970968519168019 : Int)/10^30,(-1595823729205436312242161324 : Int)/10^30)
theorem v4021_pa_checked : Scalar.distance (sourceCoefficient 59 69 1 0) v4021_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4021_pb : Scalar.QComplex := ((-688562059531528528206251 : Int)/10^30,(-431476967139321808055072183 : Int)/10^30)
theorem v4021_pb_checked : Scalar.distance (sourceCoefficient 59 69 1 1) v4021_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4021_pg : Scalar.QComplex := ((-93086310887539327929080 : Int)/10^30,(148549532930734718433 : Int)/10^30)
theorem v4021_pg_checked : Scalar.distance (sourceCoefficient 59 69 1 2) v4021_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4021_mb : Scalar.QComplex := ((-1060906992788426603318265 : Int)/10^30,(-431476212282681778769995074 : Int)/10^30)
theorem v4021_mb_checked : Scalar.distance (sourceCoefficient 59 69 3 1) v4021_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4021_mg : Scalar.QComplex := ((-93086148035695033305165 : Int)/10^30,(228878771463089751249 : Int)/10^30)
theorem v4021_mg_checked : Scalar.distance (sourceCoefficient 59 69 3 2) v4021_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4021_upper : Scalar.QComplex := ((999994483044882083629557351070 : Int)/10^30,(-3321728435474364268197611168 : Int)/10^30)
theorem v4021_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 69 5) 1) 14) v4021_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4021 : Material (59 : Basis) (69 : Basis) where
  plus := ![v4021_pa,v4021_pb,v4021_pg]
  minus := ![(Primitive.Addresses.material4021 1).one,v4021_mb,v4021_mg]
  upper := v4021_upper
  lower := (Primitive.Addresses.material4021 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4021_pa_checked.trans (by decide +kernel)
    · exact v4021_pb_checked.trans (by decide +kernel)
    · exact v4021_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 69 Primitive.Addresses.material4021
    · exact v4021_mb_checked.trans (by decide +kernel)
    · exact v4021_mg_checked.trans (by decide +kernel)
  upper_error := v4021_upper_checked
  lower_error := reuse_lower_error 59 69 Primitive.Addresses.material4021

def v4022_pa : Scalar.QComplex := ((999998703859518351682829190812 : Int)/10^30,(-1610055677085884559468988636 : Int)/10^30)
theorem v4022_pa_checked : Scalar.distance (sourceCoefficient 59 70 1 0) v4022_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4022_pb : Scalar.QComplex := ((-694702824215480374239032 : Int)/10^30,(-431476956772327808628118107 : Int)/10^30)
theorem v4022_pb_checked : Scalar.distance (sourceCoefficient 59 70 1 1) v4022_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4022_pg : Scalar.QComplex := ((-93086308707468458299081 : Int)/10^30,(149874334051620324587 : Int)/10^30)
theorem v4022_pg_checked : Scalar.distance (sourceCoefficient 59 70 1 2) v4022_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4022_mb : Scalar.QComplex := ((-1067047746239642201277165 : Int)/10^30,(-431476196616488286972871455 : Int)/10^30)
theorem v4022_mb_checked : Scalar.distance (sourceCoefficient 59 70 3 1) v4022_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4022_mg : Scalar.QComplex := ((-93086144712381274918454 : Int)/10^30,(230203570209388379952 : Int)/10^30)
theorem v4022_mg_checked : Scalar.distance (sourceCoefficient 59 70 3 2) v4022_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4022_upper : Scalar.QComplex := ((999994435668881512175591321741 : Int)/10^30,(-3335960322784857800352686319 : Int)/10^30)
theorem v4022_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 70 5) 1) 14) v4022_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4022 : Material (59 : Basis) (70 : Basis) where
  plus := ![v4022_pa,v4022_pb,v4022_pg]
  minus := ![(Primitive.Addresses.material4022 1).one,v4022_mb,v4022_mg]
  upper := v4022_upper
  lower := (Primitive.Addresses.material4022 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4022_pa_checked.trans (by decide +kernel)
    · exact v4022_pb_checked.trans (by decide +kernel)
    · exact v4022_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 70 Primitive.Addresses.material4022
    · exact v4022_mb_checked.trans (by decide +kernel)
    · exact v4022_mg_checked.trans (by decide +kernel)
  upper_error := v4022_upper_checked
  lower_error := reuse_lower_error 59 70 Primitive.Addresses.material4022

def v4023_pa : Scalar.QComplex := ((999998664451661140949886156025 : Int)/10^30,(-1634348461628894732726246068 : Int)/10^30)
theorem v4023_pa_checked : Scalar.distance (sourceCoefficient 59 71 1 0) v4023_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4023_pb : Scalar.QComplex := ((-705184612976522149811623 : Int)/10^30,(-431476938807500811142152740 : Int)/10^30)
theorem v4023_pb_checked : Scalar.distance (sourceCoefficient 59 71 1 1) v4023_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4023_pg : Scalar.QComplex := ((-93086304935445245469489 : Int)/10^30,(152135662454494400467 : Int)/10^30)
theorem v4023_pg_checked : Scalar.distance (sourceCoefficient 59 71 1 2) v4023_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4023_mb : Scalar.QComplex := ((-1077529515594998386644558 : Int)/10^30,(-431476169606356360075258865 : Int)/10^30)
theorem v4023_mb_checked : Scalar.distance (sourceCoefficient 59 71 3 1) v4023_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4023_mg : Scalar.QComplex := ((-93086138988934901355715 : Int)/10^30,(232464894515180396575 : Int)/10^30)
theorem v4023_mg_checked : Scalar.distance (sourceCoefficient 59 71 3 2) v4023_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4023_upper : Scalar.QComplex := ((999994354333940697779644536601 : Int)/10^30,(-3360253003132232534879669721 : Int)/10^30)
theorem v4023_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 71 5) 1) 14) v4023_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4023 : Material (59 : Basis) (71 : Basis) where
  plus := ![v4023_pa,v4023_pb,v4023_pg]
  minus := ![(Primitive.Addresses.material4023 1).one,v4023_mb,v4023_mg]
  upper := v4023_upper
  lower := (Primitive.Addresses.material4023 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4023_pa_checked.trans (by decide +kernel)
    · exact v4023_pb_checked.trans (by decide +kernel)
    · exact v4023_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 71 Primitive.Addresses.material4023
    · exact v4023_mb_checked.trans (by decide +kernel)
    · exact v4023_mg_checked.trans (by decide +kernel)
  upper_error := v4023_upper_checked
  lower_error := reuse_lower_error 59 71 Primitive.Addresses.material4023

def v4024_pa : Scalar.QComplex := ((999998621018450051416875527687 : Int)/10^30,(-1660711052021708907838201187 : Int)/10^30)
theorem v4024_pa_checked : Scalar.distance (sourceCoefficient 59 72 1 0) v4024_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4024_pb : Scalar.QComplex := ((-716559476078122846887825 : Int)/10^30,(-431476918927892461370813782 : Int)/10^30)
theorem v4024_pb_checked : Scalar.distance (sourceCoefficient 59 72 1 1) v4024_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4024_pg : Scalar.QComplex := ((-93086300769522834486586 : Int)/10^30,(154589661656054714416 : Int)/10^30)
theorem v4024_pg_checked : Scalar.distance (sourceCoefficient 59 72 1 2) v4024_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4024_mb : Scalar.QComplex := ((-1088904357306011032540289 : Int)/10^30,(-431476139910760860525697311 : Int)/10^30)
theorem v4024_mb_checked : Scalar.distance (sourceCoefficient 59 72 3 1) v4024_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4024_mg : Scalar.QComplex := ((-93086132705323254610760 : Int)/10^30,(234918889208001239982 : Int)/10^30)
theorem v4024_mg_checked : Scalar.distance (sourceCoefficient 59 72 3 2) v4024_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4024_upper : Scalar.QComplex := ((999994265401354874433579309782 : Int)/10^30,(-3386615479299282976895173759 : Int)/10^30)
theorem v4024_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 72 5) 1) 14) v4024_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4024 : Material (59 : Basis) (72 : Basis) where
  plus := ![v4024_pa,v4024_pb,v4024_pg]
  minus := ![(Primitive.Addresses.material4024 1).one,v4024_mb,v4024_mg]
  upper := v4024_upper
  lower := (Primitive.Addresses.material4024 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4024_pa_checked.trans (by decide +kernel)
    · exact v4024_pb_checked.trans (by decide +kernel)
    · exact v4024_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 72 Primitive.Addresses.material4024
    · exact v4024_mb_checked.trans (by decide +kernel)
    · exact v4024_mg_checked.trans (by decide +kernel)
  upper_error := v4024_upper_checked
  lower_error := reuse_lower_error 59 72 Primitive.Addresses.material4024

def v4025_pa : Scalar.QComplex := ((999998605280676286625031673172 : Int)/10^30,(-1670160681546766025759609922 : Int)/10^30)
theorem v4025_pa_checked : Scalar.distance (sourceCoefficient 59 73 1 0) v4025_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4025_pb : Scalar.QComplex := ((-720636778010509666590246 : Int)/10^30,(-431476911704732606243681324 : Int)/10^30)
theorem v4025_pb_checked : Scalar.distance (sourceCoefficient 59 73 1 1) v4025_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4025_pg : Scalar.QComplex := ((-93086299257878434333021 : Int)/10^30,(155469293847232839207 : Int)/10^30)
theorem v4025_pg_checked : Scalar.distance (sourceCoefficient 59 73 1 2) v4025_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4025_mb : Scalar.QComplex := ((-1092981651486970364980059 : Int)/10^30,(-431476129169075762123456416 : Int)/10^30)
theorem v4025_mb_checked : Scalar.distance (sourceCoefficient 59 73 3 1) v4025_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4025_mg : Scalar.QComplex := ((-93086130434596453488002 : Int)/10^30,(235798519767171063424 : Int)/10^30)
theorem v4025_mg_checked : Scalar.distance (sourceCoefficient 59 73 3 2) v4025_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4025_upper : Scalar.QComplex := ((999994233354401252652420512699 : Int)/10^30,(-3396065067588257150355960992 : Int)/10^30)
theorem v4025_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 73 5) 1) 14) v4025_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4025 : Material (59 : Basis) (73 : Basis) where
  plus := ![v4025_pa,v4025_pb,v4025_pg]
  minus := ![(Primitive.Addresses.material4025 1).one,v4025_mb,v4025_mg]
  upper := v4025_upper
  lower := (Primitive.Addresses.material4025 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4025_pa_checked.trans (by decide +kernel)
    · exact v4025_pb_checked.trans (by decide +kernel)
    · exact v4025_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 73 Primitive.Addresses.material4025
    · exact v4025_mb_checked.trans (by decide +kernel)
    · exact v4025_mg_checked.trans (by decide +kernel)
  upper_error := v4025_upper_checked
  lower_error := reuse_lower_error 59 73 Primitive.Addresses.material4025

def v4026_pa : Scalar.QComplex := ((999998587465040515908607054080 : Int)/10^30,(-1680793837361730399430682321 : Int)/10^30)
theorem v4026_pa_checked : Scalar.distance (sourceCoefficient 59 74 1 0) v4026_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4026_pb : Scalar.QComplex := ((-725224744798039667852760 : Int)/10^30,(-431476903515476089313808088 : Int)/10^30)
theorem v4026_pb_checked : Scalar.distance (sourceCoefficient 59 74 1 1) v4026_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4026_pg : Scalar.QComplex := ((-93086297545311403216372 : Int)/10^30,(156459096260922976205 : Int)/10^30)
theorem v4026_pg_checked : Scalar.distance (sourceCoefficient 59 74 1 2) v4026_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4026_mb : Scalar.QComplex := ((-1097569609499231107115952 : Int)/10^30,(-431476117020613591143143444 : Int)/10^30)
theorem v4026_mb_checked : Scalar.distance (sourceCoefficient 59 74 3 1) v4026_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4026_mg : Scalar.QComplex := ((-93086127867875156069599 : Int)/10^30,(236788320334444308902 : Int)/10^30)
theorem v4026_mg_checked : Scalar.distance (sourceCoefficient 59 74 3 2) v4026_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4026_upper : Scalar.QComplex := ((999994197186929711964434927266 : Int)/10^30,(-3406698176818213877456517422 : Int)/10^30)
theorem v4026_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 74 5) 1) 14) v4026_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4026 : Material (59 : Basis) (74 : Basis) where
  plus := ![v4026_pa,v4026_pb,v4026_pg]
  minus := ![(Primitive.Addresses.material4026 1).one,v4026_mb,v4026_mg]
  upper := v4026_upper
  lower := (Primitive.Addresses.material4026 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4026_pa_checked.trans (by decide +kernel)
    · exact v4026_pb_checked.trans (by decide +kernel)
    · exact v4026_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 74 Primitive.Addresses.material4026
    · exact v4026_mb_checked.trans (by decide +kernel)
    · exact v4026_mg_checked.trans (by decide +kernel)
  upper_error := v4026_upper_checked
  lower_error := reuse_lower_error 59 74 Primitive.Addresses.material4026

def v4027_pa : Scalar.QComplex := ((999998562454119224843583873391 : Int)/10^30,(-1695608945191123217268844922 : Int)/10^30)
theorem v4027_pa_checked : Scalar.distance (sourceCoefficient 59 75 1 0) v4027_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4027_pb : Scalar.QComplex := ((-731617129446546122375263 : Int)/10^30,(-431476891996987035340784927 : Int)/10^30)
theorem v4027_pb_checked : Scalar.distance (sourceCoefficient 59 75 1 1) v4027_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4027_pg : Scalar.QComplex := ((-93086295138730384432265 : Int)/10^30,(157838181611560012736 : Int)/10^30)
theorem v4027_pg_checked : Scalar.distance (sourceCoefficient 59 75 1 2) v4027_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4027_mb : Scalar.QComplex := ((-1103961981827623330499234 : Int)/10^30,(-431476099985788776686078131 : Int)/10^30)
theorem v4027_mb_checked : Scalar.distance (sourceCoefficient 59 75 3 1) v4027_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4027_mg : Scalar.QComplex := ((-93086124271206487464327 : Int)/10^30,(238167403094813811252 : Int)/10^30)
theorem v4027_mg_checked : Scalar.distance (sourceCoefficient 59 75 3 2) v4027_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4027_upper : Scalar.QComplex := ((999994146606513574280087036307 : Int)/10^30,(-3421513219415662712906514510 : Int)/10^30)
theorem v4027_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 75 5) 1) 14) v4027_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4027 : Material (59 : Basis) (75 : Basis) where
  plus := ![v4027_pa,v4027_pb,v4027_pg]
  minus := ![(Primitive.Addresses.material4027 1).one,v4027_mb,v4027_mg]
  upper := v4027_upper
  lower := (Primitive.Addresses.material4027 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4027_pa_checked.trans (by decide +kernel)
    · exact v4027_pb_checked.trans (by decide +kernel)
    · exact v4027_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 75 Primitive.Addresses.material4027
    · exact v4027_mb_checked.trans (by decide +kernel)
    · exact v4027_mg_checked.trans (by decide +kernel)
  upper_error := v4027_upper_checked
  lower_error := reuse_lower_error 59 75 Primitive.Addresses.material4027

def v4028_pa : Scalar.QComplex := ((999998541300131764709236572935 : Int)/10^30,(-1708039112159108591060817534 : Int)/10^30)
theorem v4028_pa_checked : Scalar.distance (sourceCoefficient 59 76 1 0) v4028_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4028_pb : Scalar.QComplex := ((-736980465883722942490566 : Int)/10^30,(-431476882235330678489130874 : Int)/10^30)
theorem v4028_pb_checked : Scalar.distance (sourceCoefficient 59 76 1 1) v4028_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4028_pg : Scalar.QComplex := ((-93086293101171928969467 : Int)/10^30,(158995261349075036590 : Int)/10^30)
theorem v4028_pg_checked : Scalar.distance (sourceCoefficient 59 76 1 2) v4028_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4028_mb : Scalar.QComplex := ((-1109325307843915091188233 : Int)/10^30,(-431476085595818264967780844 : Int)/10^30)
theorem v4028_mb_checked : Scalar.distance (sourceCoefficient 59 76 3 1) v4028_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4028_mg : Scalar.QComplex := ((-93086121235141090139052 : Int)/10^30,(239324480643173988835 : Int)/10^30)
theorem v4028_mg_checked : Scalar.distance (sourceCoefficient 59 76 3 2) v4028_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4028_upper : Scalar.QComplex := ((999994103999217089720955369539 : Int)/10^30,(-3433943331360511256425785011 : Int)/10^30)
theorem v4028_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 76 5) 1) 14) v4028_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4028 : Material (59 : Basis) (76 : Basis) where
  plus := ![v4028_pa,v4028_pb,v4028_pg]
  minus := ![(Primitive.Addresses.material4028 1).one,v4028_mb,v4028_mg]
  upper := v4028_upper
  lower := (Primitive.Addresses.material4028 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4028_pa_checked.trans (by decide +kernel)
    · exact v4028_pb_checked.trans (by decide +kernel)
    · exact v4028_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 76 Primitive.Addresses.material4028
    · exact v4028_mb_checked.trans (by decide +kernel)
    · exact v4028_mg_checked.trans (by decide +kernel)
  upper_error := v4028_upper_checked
  lower_error := reuse_lower_error 59 76 Primitive.Addresses.material4028

def v4029_pa : Scalar.QComplex := ((999998536380778276396584343768 : Int)/10^30,(-1710916801386315404286174683 : Int)/10^30)
theorem v4029_pa_checked : Scalar.distance (sourceCoefficient 59 77 1 0) v4029_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4029_pb : Scalar.QComplex := ((-738222123814110606552093 : Int)/10^30,(-431476879962752861689257411 : Int)/10^30)
theorem v4029_pb_checked : Scalar.distance (sourceCoefficient 59 77 1 1) v4029_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4029_pg : Scalar.QComplex := ((-93086292627067830156969 : Int)/10^30,(159263135134999342301 : Int)/10^30)
theorem v4029_pg_checked : Scalar.distance (sourceCoefficient 59 77 1 2) v4029_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4029_mb : Scalar.QComplex := ((-1110566963350844458402728 : Int)/10^30,(-431476082251746422625191547 : Int)/10^30)
theorem v4029_mb_checked : Scalar.distance (sourceCoefficient 59 77 3 1) v4029_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4029_mg : Scalar.QComplex := ((-93086120529874155191961 : Int)/10^30,(239592353920226157190 : Int)/10^30)
theorem v4029_mg_checked : Scalar.distance (sourceCoefficient 59 77 3 2) v4029_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4029_upper : Scalar.QComplex := ((999994094113240383975884840415 : Int)/10^30,(-3436821007811380162283706174 : Int)/10^30)
theorem v4029_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 77 5) 1) 14) v4029_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4029 : Material (59 : Basis) (77 : Basis) where
  plus := ![v4029_pa,v4029_pb,v4029_pg]
  minus := ![(Primitive.Addresses.material4029 1).one,v4029_mb,v4029_mg]
  upper := v4029_upper
  lower := (Primitive.Addresses.material4029 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4029_pa_checked.trans (by decide +kernel)
    · exact v4029_pb_checked.trans (by decide +kernel)
    · exact v4029_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 77 Primitive.Addresses.material4029
    · exact v4029_mb_checked.trans (by decide +kernel)
    · exact v4029_mg_checked.trans (by decide +kernel)
  upper_error := v4029_upper_checked
  lower_error := reuse_lower_error 59 77 Primitive.Addresses.material4029

def v4030_pa : Scalar.QComplex := ((999998506632982692877818990749 : Int)/10^30,(-1728216365062313597014242641 : Int)/10^30)
theorem v4030_pa_checked : Scalar.distance (sourceCoefficient 59 78 1 0) v4030_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4030_pb : Scalar.QComplex := ((-745686494897087599304095 : Int)/10^30,(-431476866200479471259038554 : Int)/10^30)
theorem v4030_pb_checked : Scalar.distance (sourceCoefficient 59 78 1 1) v4030_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4030_pg : Scalar.QComplex := ((-93086289757981815983859 : Int)/10^30,(160873489565839882030 : Int)/10^30)
theorem v4030_pg_checked : Scalar.distance (sourceCoefficient 59 78 1 2) v4030_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4030_mb : Scalar.QComplex := ((-1118031319778272852194378 : Int)/10^30,(-431476062048062094703063529 : Int)/10^30)
theorem v4030_mb_checked : Scalar.distance (sourceCoefficient 59 78 3 1) v4030_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4030_mg : Scalar.QComplex := ((-93086116271125863166524 : Int)/10^30,(241202705275566134090 : Int)/10^30)
theorem v4030_mg_checked : Scalar.distance (sourceCoefficient 59 78 3 2) v4030_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4030_upper : Scalar.QComplex := ((999994034508011605688513013510 : Int)/10^30,(-3454120494379713930893434001 : Int)/10^30)
theorem v4030_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 78 5) 1) 14) v4030_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4030 : Material (59 : Basis) (78 : Basis) where
  plus := ![v4030_pa,v4030_pb,v4030_pg]
  minus := ![(Primitive.Addresses.material4030 1).one,v4030_mb,v4030_mg]
  upper := v4030_upper
  lower := (Primitive.Addresses.material4030 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4030_pa_checked.trans (by decide +kernel)
    · exact v4030_pb_checked.trans (by decide +kernel)
    · exact v4030_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 78 Primitive.Addresses.material4030
    · exact v4030_mb_checked.trans (by decide +kernel)
    · exact v4030_mg_checked.trans (by decide +kernel)
  upper_error := v4030_upper_checked
  lower_error := reuse_lower_error 59 78 Primitive.Addresses.material4030

def v4031_pa : Scalar.QComplex := ((999998496979028025225787645438 : Int)/10^30,(-1733793437776688041849725473 : Int)/10^30)
theorem v4031_pa_checked : Scalar.distance (sourceCoefficient 59 79 1 0) v4031_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4031_pb : Scalar.QComplex := ((-748092875814148423635163 : Int)/10^30,(-431476861727066377868334265 : Int)/10^30)
theorem v4031_pb_checked : Scalar.distance (sourceCoefficient 59 79 1 1) v4031_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4031_pg : Scalar.QComplex := ((-93086288826111408484193 : Int)/10^30,(161392639290218977211 : Int)/10^30)
theorem v4031_pg_checked : Scalar.distance (sourceCoefficient 59 79 1 2) v4031_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4031_mb : Scalar.QComplex := ((-1120437695938974059513258 : Int)/10^30,(-431476055498052314918280560 : Int)/10^30)
theorem v4031_mb_checked : Scalar.distance (sourceCoefficient 59 79 3 1) v4031_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4031_mg : Scalar.QComplex := ((-93086114891252972141258 : Int)/10^30,(241721854002479868783 : Int)/10^30)
theorem v4031_mg_checked : Scalar.distance (sourceCoefficient 59 79 3 2) v4031_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4031_upper : Scalar.QComplex := ((999994015228549759542032680519 : Int)/10^30,(-3459697542125843740208182308 : Int)/10^30)
theorem v4031_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 79 5) 1) 14) v4031_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4031 : Material (59 : Basis) (79 : Basis) where
  plus := ![v4031_pa,v4031_pb,v4031_pg]
  minus := ![(Primitive.Addresses.material4031 1).one,v4031_mb,v4031_mg]
  upper := v4031_upper
  lower := (Primitive.Addresses.material4031 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4031_pa_checked.trans (by decide +kernel)
    · exact v4031_pb_checked.trans (by decide +kernel)
    · exact v4031_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 79 Primitive.Addresses.material4031
    · exact v4031_mb_checked.trans (by decide +kernel)
    · exact v4031_mg_checked.trans (by decide +kernel)
  upper_error := v4031_upper_checked
  lower_error := reuse_lower_error 59 79 Primitive.Addresses.material4031

def v4032_pa : Scalar.QComplex := ((999998481836354032142020539035 : Int)/10^30,(-1742505376495252028495616679 : Int)/10^30)
theorem v4032_pa_checked : Scalar.distance (sourceCoefficient 59 80 1 0) v4032_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4032_pb : Scalar.QComplex := ((-751851880588030914340782 : Int)/10^30,(-431476854703344608495741191 : Int)/10^30)
theorem v4032_pb_checked : Scalar.distance (sourceCoefficient 59 80 1 1) v4032_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4032_pg : Scalar.QComplex := ((-93086287363678128576747 : Int)/10^30,(162203602460803679835 : Int)/10^30)
theorem v4032_pg_checked : Scalar.distance (sourceCoefficient 59 80 1 2) v4032_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4032_mb : Scalar.QComplex := ((-1124196693252051727614389 : Int)/10^30,(-431476045230481340228043284 : Int)/10^30)
theorem v4032_mb_checked : Scalar.distance (sourceCoefficient 59 80 3 1) v4032_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4032_mg : Scalar.QComplex := ((-93086112728995544975313 : Int)/10^30,(242532815609091865140 : Int)/10^30)
theorem v4032_mg_checked : Scalar.distance (sourceCoefficient 59 80 3 2) v4032_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4032_upper : Scalar.QComplex := ((999993985049882432357697651466 : Int)/10^30,(-3468409441734116802354215744 : Int)/10^30)
theorem v4032_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 80 5) 1) 14) v4032_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4032 : Material (59 : Basis) (80 : Basis) where
  plus := ![v4032_pa,v4032_pb,v4032_pg]
  minus := ![(Primitive.Addresses.material4032 1).one,v4032_mb,v4032_mg]
  upper := v4032_upper
  lower := (Primitive.Addresses.material4032 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4032_pa_checked.trans (by decide +kernel)
    · exact v4032_pb_checked.trans (by decide +kernel)
    · exact v4032_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 80 Primitive.Addresses.material4032
    · exact v4032_mb_checked.trans (by decide +kernel)
    · exact v4032_mg_checked.trans (by decide +kernel)
  upper_error := v4032_upper_checked
  lower_error := reuse_lower_error 59 80 Primitive.Addresses.material4032

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
