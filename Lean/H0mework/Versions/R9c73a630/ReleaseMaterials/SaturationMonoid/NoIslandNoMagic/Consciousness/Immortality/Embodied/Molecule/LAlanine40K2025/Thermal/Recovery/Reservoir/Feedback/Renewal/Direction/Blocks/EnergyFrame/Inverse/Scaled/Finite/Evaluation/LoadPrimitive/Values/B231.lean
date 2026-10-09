import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B154

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3697_pa : Scalar.QComplex := ((999998677372532919021169720022 : Int)/10^30,(-1626423433432555097823382346 : Int)/10^30)
theorem v3697_pa_checked : Scalar.distance (sourceCoefficient 51 77 1 0) v3697_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3697_pb : Scalar.QComplex := ((-701765127646737209855267 : Int)/10^30,(-431476935862781802708312334 : Int)/10^30)
theorem v3697_pb_checked : Scalar.distance (sourceCoefficient 51 77 1 1) v3697_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3697_pg : Scalar.QComplex := ((-93086305219179132935603 : Int)/10^30,(151397948383213090037 : Int)/10^30)
theorem v3697_pg_checked : Scalar.distance (sourceCoefficient 51 77 1 2) v3697_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3697_mb : Scalar.QComplex := ((-1074110028997284234109461 : Int)/10^30,(-431476169612500279797077336 : Int)/10^30)
theorem v3697_mb_checked : Scalar.distance (sourceCoefficient 51 77 3 1) v3697_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3697_mg : Scalar.QComplex := ((-93086139909282701282121 : Int)/10^30,(231727180963433316066 : Int)/10^30)
theorem v3697_mg_checked : Scalar.distance (sourceCoefficient 51 77 3 2) v3697_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3697_upper : Scalar.QComplex := ((999994380932672945670596968326 : Int)/10^30,(-3352328009039543975837674148 : Int)/10^30)
theorem v3697_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 77 5) 1) 14) v3697_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3697 : Material (51 : Basis) (77 : Basis) where
  plus := ![v3697_pa,v3697_pb,v3697_pg]
  minus := ![(Primitive.Addresses.material3697 1).one,v3697_mb,v3697_mg]
  upper := v3697_upper
  lower := (Primitive.Addresses.material3697 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3697_pa_checked.trans (by decide +kernel)
    · exact v3697_pb_checked.trans (by decide +kernel)
    · exact v3697_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 77 Primitive.Addresses.material3697
    · exact v3697_mb_checked.trans (by decide +kernel)
    · exact v3697_mg_checked.trans (by decide +kernel)
  upper_error := v3697_upper_checked
  lower_error := reuse_lower_error 51 77 Primitive.Addresses.material3697

def v3698_pa : Scalar.QComplex := ((999998649086437874525174846490 : Int)/10^30,(-1643722999560296143442219601 : Int)/10^30)
theorem v3698_pa_checked : Scalar.distance (sourceCoefficient 51 78 1 0) v3698_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3698_pb : Scalar.QComplex := ((-709229499434962138274459 : Int)/10^30,(-431476922520969019092921682 : Int)/10^30)
theorem v3698_pb_checked : Scalar.distance (sourceCoefficient 51 78 1 1) v3698_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3698_pg : Scalar.QComplex := ((-93086302463480188147882 : Int)/10^30,(153008303004240285349 : Int)/10^30)
theorem v3698_pg_checked : Scalar.distance (sourceCoefficient 51 78 1 2) v3698_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3698_mb : Scalar.QComplex := ((-1081574386492798867810697 : Int)/10^30,(-431476149829275793535872315 : Int)/10^30)
theorem v3698_mb_checked : Scalar.distance (sourceCoefficient 51 78 3 1) v3698_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3698_mg : Scalar.QComplex := ((-93086135763921272300366 : Int)/10^30,(233337532606807811849 : Int)/10^30)
theorem v3698_mg_checked : Scalar.distance (sourceCoefficient 51 78 3 2) v3698_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3698_upper : Scalar.QComplex := ((999994322789138297889002438005 : Int)/10^30,(-3369627500582379471671444558 : Int)/10^30)
theorem v3698_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 78 5) 1) 14) v3698_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3698 : Material (51 : Basis) (78 : Basis) where
  plus := ![v3698_pa,v3698_pb,v3698_pg]
  minus := ![(Primitive.Addresses.material3698 1).one,v3698_mb,v3698_mg]
  upper := v3698_upper
  lower := (Primitive.Addresses.material3698 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3698_pa_checked.trans (by decide +kernel)
    · exact v3698_pb_checked.trans (by decide +kernel)
    · exact v3698_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 78 Primitive.Addresses.material3698
    · exact v3698_mb_checked.trans (by decide +kernel)
    · exact v3698_mg_checked.trans (by decide +kernel)
  upper_error := v3698_upper_checked
  lower_error := reuse_lower_error 51 78 Primitive.Addresses.material3698

def v3699_pa : Scalar.QComplex := ((999998639903709553929510163749 : Int)/10^30,(-1649300073070459090286416693 : Int)/10^30)
theorem v3699_pa_checked : Scalar.distance (sourceCoefficient 51 79 1 0) v3699_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3699_pb : Scalar.QComplex := ((-711635880580932857079170 : Int)/10^30,(-431476918183104973096555819 : Int)/10^30)
theorem v3699_pb_checked : Scalar.distance (sourceCoefficient 51 79 1 1) v3699_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3699_pg : Scalar.QComplex := ((-93086301568163762159957 : Int)/10^30,(153527452790350305323 : Int)/10^30)
theorem v3699_pg_checked : Scalar.distance (sourceCoefficient 51 79 1 2) v3699_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3699_mb : Scalar.QComplex := ((-1083980762999382607368450 : Int)/10^30,(-431476143414814813135393317 : Int)/10^30)
theorem v3699_mb_checked : Scalar.distance (sourceCoefficient 51 79 3 1) v3699_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3699_mg : Scalar.QComplex := ((-93086134420602295905116 : Int)/10^30,(233856681426996888064 : Int)/10^30)
theorem v3699_mg_checked : Scalar.distance (sourceCoefficient 51 79 3 2) v3699_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3699_upper : Scalar.QComplex := ((999994303980900723503837864185 : Int)/10^30,(-3375204549937590523460436535 : Int)/10^30)
theorem v3699_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 79 5) 1) 14) v3699_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3699 : Material (51 : Basis) (79 : Basis) where
  plus := ![v3699_pa,v3699_pb,v3699_pg]
  minus := ![(Primitive.Addresses.material3699 1).one,v3699_mb,v3699_mg]
  upper := v3699_upper
  lower := (Primitive.Addresses.material3699 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3699_pa_checked.trans (by decide +kernel)
    · exact v3699_pb_checked.trans (by decide +kernel)
    · exact v3699_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 79 Primitive.Addresses.material3699
    · exact v3699_mb_checked.trans (by decide +kernel)
    · exact v3699_mg_checked.trans (by decide +kernel)
  upper_error := v3699_upper_checked
  lower_error := reuse_lower_error 51 79 Primitive.Addresses.material3699

def v3700_pa : Scalar.QComplex := ((999998625497137682804075677198 : Int)/10^30,(-1658012013037382467831296577 : Int)/10^30)
theorem v3700_pa_checked : Scalar.distance (sourceCoefficient 51 80 1 0) v3700_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3700_pb : Scalar.QComplex := ((-715394885713908015672085 : Int)/10^30,(-431476911371124210945620139 : Int)/10^30)
theorem v3700_pb_checked : Scalar.distance (sourceCoefficient 51 80 1 1) v3700_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3700_pg : Scalar.QComplex := ((-93086300162831413715666 : Int)/10^30,(154338416057772772567 : Int)/10^30)
theorem v3700_pg_checked : Scalar.distance (sourceCoefficient 51 80 1 2) v3700_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3700_mb : Scalar.QComplex := ((-1087739760854275762421600 : Int)/10^30,(-431476133358984456945159950 : Int)/10^30)
theorem v3700_mb_checked : Scalar.distance (sourceCoefficient 51 80 3 1) v3700_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3700_mg : Scalar.QComplex := ((-93086132315445695374410 : Int)/10^30,(234667643179722145106 : Int)/10^30)
theorem v3700_mg_checked : Scalar.distance (sourceCoefficient 51 80 3 2) v3700_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3700_upper : Scalar.QComplex := ((999994274538332267385135015008 : Int)/10^30,(-3383916452064666601058012830 : Int)/10^30)
theorem v3700_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 80 5) 1) 14) v3700_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3700 : Material (51 : Basis) (80 : Basis) where
  plus := ![v3700_pa,v3700_pb,v3700_pg]
  minus := ![(Primitive.Addresses.material3700 1).one,v3700_mb,v3700_mg]
  upper := v3700_upper
  lower := (Primitive.Addresses.material3700 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3700_pa_checked.trans (by decide +kernel)
    · exact v3700_pb_checked.trans (by decide +kernel)
    · exact v3700_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 80 Primitive.Addresses.material3700
    · exact v3700_mb_checked.trans (by decide +kernel)
    · exact v3700_mg_checked.trans (by decide +kernel)
  upper_error := v3700_upper_checked
  lower_error := reuse_lower_error 51 80 Primitive.Addresses.material3700

def v3701_pa : Scalar.QComplex := ((999998581659873281576090306360 : Int)/10^30,(-1684244115841920571010472567 : Int)/10^30)
theorem v3701_pa_checked : Scalar.distance (sourceCoefficient 51 81 1 0) v3701_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3701_pb : Scalar.QComplex := ((-726713444835288800628678 : Int)/10^30,(-431476890596218645451052000 : Int)/10^30)
theorem v3701_pb_checked : Scalar.distance (sourceCoefficient 51 81 1 1) v3701_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3701_pg : Scalar.QComplex := ((-93086295881527901768672 : Int)/10^30,(156780268471729224285 : Int)/10^30)
theorem v3701_pg_checked : Scalar.distance (sourceCoefficient 51 81 1 2) v3701_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3701_mb : Scalar.QComplex := ((-1099058297833431866773212 : Int)/10^30,(-431476102816679874125089487 : Int)/10^30)
theorem v3701_mb_checked : Scalar.distance (sourceCoefficient 51 81 3 1) v3701_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3701_mg : Scalar.QComplex := ((-93086125926935121258150 : Int)/10^30,(237109490989893236882 : Int)/10^30)
theorem v3701_mg_checked : Scalar.distance (sourceCoefficient 51 81 3 2) v3701_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3701_upper : Scalar.QComplex := ((999994185426903473757002492176 : Int)/10^30,(-3410148440140427545173658302 : Int)/10^30)
theorem v3701_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 81 5) 1) 14) v3701_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3701 : Material (51 : Basis) (81 : Basis) where
  plus := ![v3701_pa,v3701_pb,v3701_pg]
  minus := ![(Primitive.Addresses.material3701 1).one,v3701_mb,v3701_mg]
  upper := v3701_upper
  lower := (Primitive.Addresses.material3701 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3701_pa_checked.trans (by decide +kernel)
    · exact v3701_pb_checked.trans (by decide +kernel)
    · exact v3701_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 81 Primitive.Addresses.material3701
    · exact v3701_mb_checked.trans (by decide +kernel)
    · exact v3701_mg_checked.trans (by decide +kernel)
  upper_error := v3701_upper_checked
  lower_error := reuse_lower_error 51 81 Primitive.Addresses.material3701

def v3702_pa : Scalar.QComplex := ((999998564868646409142841350162 : Int)/10^30,(-1694184360564018504295389530 : Int)/10^30)
theorem v3702_pa_checked : Scalar.distance (sourceCoefficient 51 82 1 0) v3702_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3702_pb : Scalar.QComplex := ((-731002435565022451774989 : Int)/10^30,(-431476882620464442935445452 : Int)/10^30)
theorem v3702_pb_checked : Scalar.distance (sourceCoefficient 51 82 1 1) v3702_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3702_pg : Scalar.QComplex := ((-93086294239670517347507 : Int)/10^30,(157705570211918721540 : Int)/10^30)
theorem v3702_pg_checked : Scalar.distance (sourceCoefficient 51 82 1 2) v3702_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3702_mb : Scalar.QComplex := ((-1103347280083461590543559 : Int)/10^30,(-431476091139722810558839480 : Int)/10^30)
theorem v3702_mb_checked : Scalar.distance (sourceCoefficient 51 82 3 1) v3702_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3702_mg : Scalar.QComplex := ((-93086123486584620435354 : Int)/10^30,(238034790968701631641 : Int)/10^30)
theorem v3702_mg_checked : Scalar.distance (sourceCoefficient 51 82 3 2) v3702_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3702_upper : Scalar.QComplex := ((999994151479740991499643885406 : Int)/10^30,(-3420088641077564334445430194 : Int)/10^30)
theorem v3702_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 82 5) 1) 14) v3702_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3702 : Material (51 : Basis) (82 : Basis) where
  plus := ![v3702_pa,v3702_pb,v3702_pg]
  minus := ![(Primitive.Addresses.material3702 1).one,v3702_mb,v3702_mg]
  upper := v3702_upper
  lower := (Primitive.Addresses.material3702 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3702_pa_checked.trans (by decide +kernel)
    · exact v3702_pb_checked.trans (by decide +kernel)
    · exact v3702_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 82 Primitive.Addresses.material3702
    · exact v3702_mb_checked.trans (by decide +kernel)
    · exact v3702_mg_checked.trans (by decide +kernel)
  upper_error := v3702_upper_checked
  lower_error := reuse_lower_error 51 82 Primitive.Addresses.material3702

def v3703_pa : Scalar.QComplex := ((999998541788847620953379853365 : Int)/10^30,(-1707752961753639681757862607 : Int)/10^30)
theorem v3703_pa_checked : Scalar.distance (sourceCoefficient 51 83 1 0) v3703_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3703_pb : Scalar.QComplex := ((-736856979967322499332953 : Int)/10^30,(-431476871641669787395926844 : Int)/10^30)
theorem v3703_pb_checked : Scalar.distance (sourceCoefficient 51 83 1 1) v3703_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3703_pg : Scalar.QComplex := ((-93086291981186650895465 : Int)/10^30,(158968622639353993867 : Int)/10^30)
theorem v3703_pg_checked : Scalar.distance (sourceCoefficient 51 83 1 2) v3703_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3703_mb : Scalar.QComplex := ((-1109201812831641870053227 : Int)/10^30,(-431476075108724102633044826 : Int)/10^30)
theorem v3703_mb_checked : Scalar.distance (sourceCoefficient 51 83 3 1) v3703_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3703_mg : Scalar.QComplex := ((-93086120138144235813066 : Int)/10^30,(239297840976874902477 : Int)/10^30)
theorem v3703_mg_checked : Scalar.distance (sourceCoefficient 51 83 3 2) v3703_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3703_upper : Scalar.QComplex := ((999994104981801858557576096498 : Int)/10^30,(-3433657182224708994402164667 : Int)/10^30)
theorem v3703_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 83 5) 1) 14) v3703_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3703 : Material (51 : Basis) (83 : Basis) where
  plus := ![v3703_pa,v3703_pb,v3703_pg]
  minus := ![(Primitive.Addresses.material3703 1).one,v3703_mb,v3703_mg]
  upper := v3703_upper
  lower := (Primitive.Addresses.material3703 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3703_pa_checked.trans (by decide +kernel)
    · exact v3703_pb_checked.trans (by decide +kernel)
    · exact v3703_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 83 Primitive.Addresses.material3703
    · exact v3703_mb_checked.trans (by decide +kernel)
    · exact v3703_mg_checked.trans (by decide +kernel)
  upper_error := v3703_upper_checked
  lower_error := reuse_lower_error 51 83 Primitive.Addresses.material3703

def v3704_pa : Scalar.QComplex := ((999998481162642880188530964066 : Int)/10^30,(-1742891966638410309526488574 : Int)/10^30)
theorem v3704_pa_checked : Scalar.distance (sourceCoefficient 51 84 1 0) v3704_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3704_pb : Scalar.QComplex := ((-752018665156415321741789 : Int)/10^30,(-431476842717234813446186618 : Int)/10^30)
theorem v3704_pb_checked : Scalar.distance (sourceCoefficient 51 84 1 1) v3704_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3704_pg : Scalar.QComplex := ((-93086286039387151987387 : Int)/10^30,(162239586557797939102 : Int)/10^30)
theorem v3704_pg_checked : Scalar.distance (sourceCoefficient 51 84 1 2) v3704_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3704_mb : Scalar.QComplex := ((-1124363467414861698992361 : Int)/10^30,(-431476033100448437337326791 : Int)/10^30)
theorem v3704_mb_checked : Scalar.distance (sourceCoefficient 51 84 3 1) v3704_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3704_mg : Scalar.QComplex := ((-93086111373652406437528 : Int)/10^30,(242568798549884131597 : Int)/10^30)
theorem v3704_mg_checked : Scalar.distance (sourceCoefficient 51 84 3 2) v3704_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3704_upper : Scalar.QComplex := ((999993983708952767910462446515 : Int)/10^30,(-3468796030138730147545617146 : Int)/10^30)
theorem v3704_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 84 5) 1) 14) v3704_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3704 : Material (51 : Basis) (84 : Basis) where
  plus := ![v3704_pa,v3704_pb,v3704_pg]
  minus := ![(Primitive.Addresses.material3704 1).one,v3704_mb,v3704_mg]
  upper := v3704_upper
  lower := (Primitive.Addresses.material3704 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3704_pa_checked.trans (by decide +kernel)
    · exact v3704_pb_checked.trans (by decide +kernel)
    · exact v3704_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 84 Primitive.Addresses.material3704
    · exact v3704_mb_checked.trans (by decide +kernel)
    · exact v3704_mg_checked.trans (by decide +kernel)
  upper_error := v3704_upper_checked
  lower_error := reuse_lower_error 51 84 Primitive.Addresses.material3704

def v3705_pa : Scalar.QComplex := ((999998340250165545228178834328 : Int)/10^30,(-1821948658480812040933400095 : Int)/10^30)
theorem v3705_pa_checked : Scalar.distance (sourceCoefficient 51 85 1 0) v3705_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3705_pb : Scalar.QComplex := ((-786129836238354096397931 : Int)/10^30,(-431476775045342310083869262 : Int)/10^30)
theorem v3705_pb_checked : Scalar.distance (sourceCoefficient 51 85 1 1) v3705_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3705_pg : Scalar.QComplex := ((-93086272181141983854408 : Int)/10^30,(169598690214809378677 : Int)/10^30)
theorem v3705_pg_checked : Scalar.distance (sourceCoefficient 51 85 1 2) v3705_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3705_mb : Scalar.QComplex := ((-1158474567397857120806132 : Int)/10^30,(-431475935992176797715202492 : Int)/10^30)
theorem v3705_mb_checked : Scalar.distance (sourceCoefficient 51 85 3 1) v3705_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3705_mg : Scalar.QComplex := ((-93086091164837384086723 : Int)/10^30,(249927887507723524108 : Int)/10^30)
theorem v3705_mg_checked : Scalar.distance (sourceCoefficient 51 85 3 2) v3705_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3705_upper : Scalar.QComplex := ((999993706352007152606580518008 : Int)/10^30,(-3547852361033323631013830653 : Int)/10^30)
theorem v3705_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 85 5) 1) 14) v3705_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3705 : Material (51 : Basis) (85 : Basis) where
  plus := ![v3705_pa,v3705_pb,v3705_pg]
  minus := ![(Primitive.Addresses.material3705 1).one,v3705_mb,v3705_mg]
  upper := v3705_upper
  lower := (Primitive.Addresses.material3705 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3705_pa_checked.trans (by decide +kernel)
    · exact v3705_pb_checked.trans (by decide +kernel)
    · exact v3705_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 85 Primitive.Addresses.material3705
    · exact v3705_mb_checked.trans (by decide +kernel)
    · exact v3705_mg_checked.trans (by decide +kernel)
  upper_error := v3705_upper_checked
  lower_error := reuse_lower_error 51 85 Primitive.Addresses.material3705

def v3706_pa : Scalar.QComplex := ((999998313571337047413994421765 : Int)/10^30,(-1836533278180261231040172252 : Int)/10^30)
theorem v3706_pa_checked : Scalar.distance (sourceCoefficient 51 86 1 0) v3706_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3706_pb : Scalar.QComplex := ((-792422768847786899096314 : Int)/10^30,(-431476762168171180627672862 : Int)/10^30)
theorem v3706_pb_checked : Scalar.distance (sourceCoefficient 51 86 1 1) v3706_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3706_pg : Scalar.QComplex := ((-93086269550371000035080 : Int)/10^30,(170956320076552574348 : Int)/10^30)
theorem v3706_pg_checked : Scalar.distance (sourceCoefficient 51 86 1 2) v3706_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3706_mb : Scalar.QComplex := ((-1164767486551724793322257 : Int)/10^30,(-431475917684493044241391125 : Int)/10^30)
theorem v3706_mb_checked : Scalar.distance (sourceCoefficient 51 86 3 1) v3706_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3706_mg : Scalar.QComplex := ((-93086087362493954518436 : Int)/10^30,(251285514593722201992 : Int)/10^30)
theorem v3706_mg_checked : Scalar.distance (sourceCoefficient 51 86 3 2) v3706_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3706_upper : Scalar.QComplex := ((999993654501487894887820450404 : Int)/10^30,(-3562436912965457305756574482 : Int)/10^30)
theorem v3706_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 86 5) 1) 14) v3706_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3706 : Material (51 : Basis) (86 : Basis) where
  plus := ![v3706_pa,v3706_pb,v3706_pg]
  minus := ![(Primitive.Addresses.material3706 1).one,v3706_mb,v3706_mg]
  upper := v3706_upper
  lower := (Primitive.Addresses.material3706 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3706_pa_checked.trans (by decide +kernel)
    · exact v3706_pb_checked.trans (by decide +kernel)
    · exact v3706_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 86 Primitive.Addresses.material3706
    · exact v3706_mb_checked.trans (by decide +kernel)
    · exact v3706_mg_checked.trans (by decide +kernel)
  upper_error := v3706_upper_checked
  lower_error := reuse_lower_error 51 86 Primitive.Addresses.material3706

def v3707_pa : Scalar.QComplex := ((999998311797226864009244380041 : Int)/10^30,(-1837499032991141001648181279 : Int)/10^30)
theorem v3707_pa_checked : Scalar.distance (sourceCoefficient 51 87 1 0) v3707_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3707_pb : Scalar.QComplex := ((-792839470141196454734233 : Int)/10^30,(-431476761311159156737439840 : Int)/10^30)
theorem v3707_pb_checked : Scalar.distance (sourceCoefficient 51 87 1 1) v3707_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3707_pg : Scalar.QComplex := ((-93086269375352848188911 : Int)/10^30,(171046218722664503501 : Int)/10^30)
theorem v3707_pg_checked : Scalar.distance (sourceCoefficient 51 87 1 2) v3707_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3707_mb : Scalar.QComplex := ((-1165184186950414635005332 : Int)/10^30,(-431475916467886890773027186 : Int)/10^30)
theorem v3707_mb_checked : Scalar.distance (sourceCoefficient 51 87 3 1) v3707_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3707_mg : Scalar.QComplex := ((-93086087109897385129648 : Int)/10^30,(251375413055327974109 : Int)/10^30)
theorem v3707_mg_checked : Scalar.distance (sourceCoefficient 51 87 3 2) v3707_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3707_upper : Scalar.QComplex := ((999993651060575162825353901093 : Int)/10^30,(-3563402663276005500550363510 : Int)/10^30)
theorem v3707_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 87 5) 1) 14) v3707_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3707 : Material (51 : Basis) (87 : Basis) where
  plus := ![v3707_pa,v3707_pb,v3707_pg]
  minus := ![(Primitive.Addresses.material3707 1).one,v3707_mb,v3707_mg]
  upper := v3707_upper
  lower := (Primitive.Addresses.material3707 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3707_pa_checked.trans (by decide +kernel)
    · exact v3707_pb_checked.trans (by decide +kernel)
    · exact v3707_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 87 Primitive.Addresses.material3707
    · exact v3707_mb_checked.trans (by decide +kernel)
    · exact v3707_mg_checked.trans (by decide +kernel)
  upper_error := v3707_upper_checked
  lower_error := reuse_lower_error 51 87 Primitive.Addresses.material3707

def v3708_pa : Scalar.QComplex := ((999998290119841174447311152090 : Int)/10^30,(-1849258606566682396198458278 : Int)/10^30)
theorem v3708_pa_checked : Scalar.distance (sourceCoefficient 51 88 1 0) v3708_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3708_pb : Scalar.QComplex := ((-797913459347104578883549 : Int)/10^30,(-431476750832653257553324299 : Int)/10^30)
theorem v3708_pb_checked : Scalar.distance (sourceCoefficient 51 88 1 1) v3708_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3708_pg : Scalar.QComplex := ((-93086267236107635956464 : Int)/10^30,(172140875179805221520 : Int)/10^30)
theorem v3708_pg_checked : Scalar.distance (sourceCoefficient 51 88 1 2) v3708_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3708_mb : Scalar.QComplex := ((-1170258165224566028423388 : Int)/10^30,(-431475901610760732507462961 : Int)/10^30)
theorem v3708_mb_checked : Scalar.distance (sourceCoefficient 51 88 3 1) v3708_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3708_mg : Scalar.QComplex := ((-93086084026013748420194 : Int)/10^30,(252470067258805794734 : Int)/10^30)
theorem v3708_mg_checked : Scalar.distance (sourceCoefficient 51 88 3 2) v3708_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3708_upper : Scalar.QComplex := ((999993609087264587979784874511 : Int)/10^30,(-3575162181923842287764285977 : Int)/10^30)
theorem v3708_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 88 5) 1) 14) v3708_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3708 : Material (51 : Basis) (88 : Basis) where
  plus := ![v3708_pa,v3708_pb,v3708_pg]
  minus := ![(Primitive.Addresses.material3708 1).one,v3708_mb,v3708_mg]
  upper := v3708_upper
  lower := (Primitive.Addresses.material3708 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3708_pa_checked.trans (by decide +kernel)
    · exact v3708_pb_checked.trans (by decide +kernel)
    · exact v3708_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 88 Primitive.Addresses.material3708
    · exact v3708_mb_checked.trans (by decide +kernel)
    · exact v3708_mg_checked.trans (by decide +kernel)
  upper_error := v3708_upper_checked
  lower_error := reuse_lower_error 51 88 Primitive.Addresses.material3708

def v3709_pa : Scalar.QComplex := ((999998260236787903373743991469 : Int)/10^30,(-1865348063342929666453597050 : Int)/10^30)
theorem v3709_pa_checked : Scalar.distance (sourceCoefficient 51 89 1 0) v3709_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3709_pb : Scalar.QComplex := ((-804855694818159407739971 : Int)/10^30,(-431476736367063921706373731 : Int)/10^30)
theorem v3709_pb_checked : Scalar.distance (sourceCoefficient 51 89 1 1) v3709_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3709_pg : Scalar.QComplex := ((-93086264284860033977603 : Int)/10^30,(173638584897613991555 : Int)/10^30)
theorem v3709_pg_checked : Scalar.distance (sourceCoefficient 51 89 1 2) v3709_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3709_mb : Scalar.QComplex := ((-1177200385627557224694057 : Int)/10^30,(-431475881154340238019098528 : Int)/10^30)
theorem v3709_mb_checked : Scalar.distance (sourceCoefficient 51 89 3 1) v3709_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3709_mg : Scalar.QComplex := ((-93086079782311213198393 : Int)/10^30,(253967773872155026863 : Int)/10^30)
theorem v3709_mg_checked : Scalar.distance (sourceCoefficient 51 89 3 2) v3709_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3709_upper : Scalar.QComplex := ((999993551435313052517749767699 : Int)/10^30,(-3591251563161294713700181611 : Int)/10^30)
theorem v3709_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 89 5) 1) 14) v3709_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3709 : Material (51 : Basis) (89 : Basis) where
  plus := ![v3709_pa,v3709_pb,v3709_pg]
  minus := ![(Primitive.Addresses.material3709 1).one,v3709_mb,v3709_mg]
  upper := v3709_upper
  lower := (Primitive.Addresses.material3709 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3709_pa_checked.trans (by decide +kernel)
    · exact v3709_pb_checked.trans (by decide +kernel)
    · exact v3709_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 89 Primitive.Addresses.material3709
    · exact v3709_mb_checked.trans (by decide +kernel)
    · exact v3709_mg_checked.trans (by decide +kernel)
  upper_error := v3709_upper_checked
  lower_error := reuse_lower_error 51 89 Primitive.Addresses.material3709

def v3710_pa : Scalar.QComplex := ((999998211015884910431289195573 : Int)/10^30,(-1891550958794124948488697325 : Int)/10^30)
theorem v3710_pa_checked : Scalar.distance (sourceCoefficient 51 90 1 0) v3710_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3710_pb : Scalar.QComplex := ((-816161649307998866803022 : Int)/10^30,(-431476712489987535091072187 : Int)/10^30)
theorem v3710_pb_checked : Scalar.distance (sourceCoefficient 51 90 1 1) v3710_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3710_pg : Scalar.QComplex := ((-93086259418355412125227 : Int)/10^30,(176077718253589800444 : Int)/10^30)
theorem v3710_pg_checked : Scalar.distance (sourceCoefficient 51 90 1 2) v3710_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3710_mb : Scalar.QComplex := ((-1188506315302831581495148 : Int)/10^30,(-431475847520743218486900898 : Int)/10^30)
theorem v3710_mb_checked : Scalar.distance (sourceCoefficient 51 90 3 1) v3710_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3710_mg : Scalar.QComplex := ((-93086072810946171649338 : Int)/10^30,(256406902120355703995 : Int)/10^30)
theorem v3710_mg_checked : Scalar.distance (sourceCoefficient 51 90 3 2) v3710_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3710_upper : Scalar.QComplex := ((999993456990662927671735688593 : Int)/10^30,(-3617454334635541949117845288 : Int)/10^30)
theorem v3710_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 90 5) 1) 14) v3710_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3710 : Material (51 : Basis) (90 : Basis) where
  plus := ![v3710_pa,v3710_pb,v3710_pg]
  minus := ![(Primitive.Addresses.material3710 1).one,v3710_mb,v3710_mg]
  upper := v3710_upper
  lower := (Primitive.Addresses.material3710 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3710_pa_checked.trans (by decide +kernel)
    · exact v3710_pb_checked.trans (by decide +kernel)
    · exact v3710_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 90 Primitive.Addresses.material3710
    · exact v3710_mb_checked.trans (by decide +kernel)
    · exact v3710_mg_checked.trans (by decide +kernel)
  upper_error := v3710_upper_checked
  lower_error := reuse_lower_error 51 90 Primitive.Addresses.material3710

def v3711_pa : Scalar.QComplex := ((999998182985622518052509146287 : Int)/10^30,(-1906312003168066663684016735 : Int)/10^30)
theorem v3711_pa_checked : Scalar.distance (sourceCoefficient 51 91 1 0) v3711_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3711_pb : Scalar.QComplex := ((-822530704684230876231025 : Int)/10^30,(-431476698865226468067303442 : Int)/10^30)
theorem v3711_pb_checked : Scalar.distance (sourceCoefficient 51 91 1 1) v3711_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3711_pg : Scalar.QComplex := ((-93086256644042282450751 : Int)/10^30,(177451770802939856637 : Int)/10^30)
theorem v3711_pg_checked : Scalar.distance (sourceCoefficient 51 91 1 2) v3711_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3711_mb : Scalar.QComplex := ((-1194875356550018029759316 : Int)/10^30,(-431475828399779286501848963 : Int)/10^30)
theorem v3711_mb_checked : Scalar.distance (sourceCoefficient 51 91 3 1) v3711_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3711_mg : Scalar.QComplex := ((-93086068850888609918876 : Int)/10^30,(257780951763975918277 : Int)/10^30)
theorem v3711_mg_checked : Scalar.distance (sourceCoefficient 51 91 3 2) v3711_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3711_upper : Scalar.QComplex := ((999993403484218805137761872852 : Int)/10^30,(-3632215308646952019697304079 : Int)/10^30)
theorem v3711_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 91 5) 1) 14) v3711_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3711 : Material (51 : Basis) (91 : Basis) where
  plus := ![v3711_pa,v3711_pb,v3711_pg]
  minus := ![(Primitive.Addresses.material3711 1).one,v3711_mb,v3711_mg]
  upper := v3711_upper
  lower := (Primitive.Addresses.material3711 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3711_pa_checked.trans (by decide +kernel)
    · exact v3711_pb_checked.trans (by decide +kernel)
    · exact v3711_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 91 Primitive.Addresses.material3711
    · exact v3711_mb_checked.trans (by decide +kernel)
    · exact v3711_mg_checked.trans (by decide +kernel)
  upper_error := v3711_upper_checked
  lower_error := reuse_lower_error 51 91 Primitive.Addresses.material3711

def v3712_pa : Scalar.QComplex := ((999998121556721296939515771955 : Int)/10^30,(-1938268048763372063586116156 : Int)/10^30)
theorem v3712_pa_checked : Scalar.distance (sourceCoefficient 51 92 1 0) v3712_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3712_pb : Scalar.QComplex := ((-836319012170450195909961 : Int)/10^30,(-431476668939674796510398810 : Int)/10^30)
theorem v3712_pb_checked : Scalar.distance (sourceCoefficient 51 92 1 1) v3712_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3712_pg : Scalar.QComplex := ((-93086250556892862788365 : Int)/10^30,(180426444154448407498 : Int)/10^30)
theorem v3712_pg_checked : Scalar.distance (sourceCoefficient 51 92 1 2) v3712_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3712_mb : Scalar.QComplex := ((-1208663633077817019797411 : Int)/10^30,(-431475786575550399304713773 : Int)/10^30)
theorem v3712_mb_checked : Scalar.distance (sourceCoefficient 51 92 3 1) v3712_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3712_mg : Scalar.QComplex := ((-93086060196732328742927 : Int)/10^30,(260755618754941836947 : Int)/10^30)
theorem v3712_mg_checked : Scalar.distance (sourceCoefficient 51 92 3 2) v3712_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3712_upper : Scalar.QComplex := ((999993286902173407470499486996 : Int)/10^30,(-3664171200626770604944699026 : Int)/10^30)
theorem v3712_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 92 5) 1) 14) v3712_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3712 : Material (51 : Basis) (92 : Basis) where
  plus := ![v3712_pa,v3712_pb,v3712_pg]
  minus := ![(Primitive.Addresses.material3712 1).one,v3712_mb,v3712_mg]
  upper := v3712_upper
  lower := (Primitive.Addresses.material3712 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3712_pa_checked.trans (by decide +kernel)
    · exact v3712_pb_checked.trans (by decide +kernel)
    · exact v3712_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 92 Primitive.Addresses.material3712
    · exact v3712_mb_checked.trans (by decide +kernel)
    · exact v3712_mg_checked.trans (by decide +kernel)
  upper_error := v3712_upper_checked
  lower_error := reuse_lower_error 51 92 Primitive.Addresses.material3712

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
