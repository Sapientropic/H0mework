import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B158

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3793_pa : Scalar.QComplex := ((999998432161588285956847216350 : Int)/10^30,(-1770783545583931909705214308 : Int)/10^30)
theorem v3793_pa_checked : Scalar.distance (sourceCoefficient 53 84 1 0) v3793_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3793_pb : Scalar.QComplex := ((-764053257769760408883328 : Int)/10^30,(-431476823784106936963870443 : Int)/10^30)
theorem v3793_pb_checked : Scalar.distance (sourceCoefficient 53 84 1 1) v3793_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3793_pg : Scalar.QComplex := ((-93086281716415670210374 : Int)/10^30,(164835914419097531709 : Int)/10^30)
theorem v3793_pg_checked : Scalar.distance (sourceCoefficient 53 84 1 2) v3793_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3793_mb : Scalar.QComplex := ((-1136398039208741307153141 : Int)/10^30,(-431476003782016203137649215 : Int)/10^30)
theorem v3793_mb_checked : Scalar.distance (sourceCoefficient 53 84 3 1) v3793_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3793_mg : Scalar.QComplex := ((-93086104810168524264888 : Int)/10^30,(245165121713922514030 : Int)/10^30)
theorem v3793_mg_checked : Scalar.distance (sourceCoefficient 53 84 3 2) v3793_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3793_upper : Scalar.QComplex := ((999993886569636199299532104459 : Int)/10^30,(-3496687482971646394689457085 : Int)/10^30)
theorem v3793_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 84 5) 1) 14) v3793_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3793 : Material (53 : Basis) (84 : Basis) where
  plus := ![v3793_pa,v3793_pb,v3793_pg]
  minus := ![(Primitive.Addresses.material3793 1).one,v3793_mb,v3793_mg]
  upper := v3793_upper
  lower := (Primitive.Addresses.material3793 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3793_pa_checked.trans (by decide +kernel)
    · exact v3793_pb_checked.trans (by decide +kernel)
    · exact v3793_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 84 Primitive.Addresses.material3793
    · exact v3793_mb_checked.trans (by decide +kernel)
    · exact v3793_mg_checked.trans (by decide +kernel)
  upper_error := v3793_upper_checked
  lower_error := reuse_lower_error 53 84 Primitive.Addresses.material3793

def v3794_pa : Scalar.QComplex := ((999998289044091641452204666977 : Int)/10^30,(-1849840233465305306835689395 : Int)/10^30)
theorem v3794_pa_checked : Scalar.distance (sourceCoefficient 53 85 1 0) v3794_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3794_pb : Scalar.QComplex := ((-798164427712302772898941 : Int)/10^30,(-431476755477936949388083822 : Int)/10^30)
theorem v3794_pb_checked : Scalar.distance (sourceCoefficient 53 85 1 1) v3794_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3794_pg : Scalar.QComplex := ((-93086267687122692950417 : Int)/10^30,(172195017768843989284 : Int)/10^30)
theorem v3794_pg_checked : Scalar.distance (sourceCoefficient 53 85 1 2) v3794_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3794_mb : Scalar.QComplex := ((-1170509137504987840496956 : Int)/10^30,(-431475906039468298720336809 : Int)/10^30)
theorem v3794_mb_checked : Scalar.distance (sourceCoefficient 53 85 3 1) v3794_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3794_mg : Scalar.QComplex := ((-93086084430306021631862 : Int)/10^30,(252524210216890483382 : Int)/10^30)
theorem v3794_mg_checked : Scalar.distance (sourceCoefficient 53 85 3 2) v3794_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3794_upper : Scalar.QComplex := ((999993607007681394944164836960 : Int)/10^30,(-3575743806099554152883350127 : Int)/10^30)
theorem v3794_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 85 5) 1) 14) v3794_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3794 : Material (53 : Basis) (85 : Basis) where
  plus := ![v3794_pa,v3794_pb,v3794_pg]
  minus := ![(Primitive.Addresses.material3794 1).one,v3794_mb,v3794_mg]
  upper := v3794_upper
  lower := (Primitive.Addresses.material3794 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3794_pa_checked.trans (by decide +kernel)
    · exact v3794_pb_checked.trans (by decide +kernel)
    · exact v3794_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 85 Primitive.Addresses.material3794
    · exact v3794_mb_checked.trans (by decide +kernel)
    · exact v3794_mg_checked.trans (by decide +kernel)
  upper_error := v3794_upper_checked
  lower_error := reuse_lower_error 53 85 Primitive.Addresses.material3794

def v3795_pa : Scalar.QComplex := ((999998261958474454544425548229 : Int)/10^30,(-1864424852414965699126189186 : Int)/10^30)
theorem v3795_pa_checked : Scalar.distance (sourceCoefficient 53 86 1 0) v3795_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3795_pb : Scalar.QComplex := ((-804457360106057577856468 : Int)/10^30,(-431476742483752375315784972 : Int)/10^30)
theorem v3795_pb_checked : Scalar.distance (sourceCoefficient 53 86 1 1) v3795_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3795_pg : Scalar.QComplex := ((-93086265024796287594384 : Int)/10^30,(173552647572424551103 : Int)/10^30)
theorem v3795_pg_checked : Scalar.distance (sourceCoefficient 53 86 1 2) v3795_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3795_mb : Scalar.QComplex := ((-1176802056342200262965213 : Int)/10^30,(-431475887614771330320274475 : Int)/10^30)
theorem v3795_mb_checked : Scalar.distance (sourceCoefficient 53 86 3 1) v3795_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3795_mg : Scalar.QComplex := ((-93086080596407232468129 : Int)/10^30,(253881837217495641489 : Int)/10^30)
theorem v3795_mg_checked : Scalar.distance (sourceCoefficient 53 86 3 2) v3795_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3795_upper : Scalar.QComplex := ((999993554750375348063222434458 : Int)/10^30,(-3590328356579819772738214707 : Int)/10^30)
theorem v3795_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 86 5) 1) 14) v3795_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3795 : Material (53 : Basis) (86 : Basis) where
  plus := ![v3795_pa,v3795_pb,v3795_pg]
  minus := ![(Primitive.Addresses.material3795 1).one,v3795_mb,v3795_mg]
  upper := v3795_upper
  lower := (Primitive.Addresses.material3795 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3795_pa_checked.trans (by decide +kernel)
    · exact v3795_pb_checked.trans (by decide +kernel)
    · exact v3795_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 86 Primitive.Addresses.material3795
    · exact v3795_mb_checked.trans (by decide +kernel)
    · exact v3795_mg_checked.trans (by decide +kernel)
  upper_error := v3795_upper_checked
  lower_error := reuse_lower_error 53 86 Primitive.Addresses.material3795

def v3796_pa : Scalar.QComplex := ((999998260157427803713250057628 : Int)/10^30,(-1865390607175987008243389536 : Int)/10^30)
theorem v3796_pa_checked : Scalar.distance (sourceCoefficient 53 87 1 0) v3796_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3796_pb : Scalar.QComplex := ((-804874061385125263936707 : Int)/10^30,(-431476741618992031669557780 : Int)/10^30)
theorem v3796_pb_checked : Scalar.distance (sourceCoefficient 53 87 1 1) v3796_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3796_pg : Scalar.QComplex := ((-93086264847688619479371 : Int)/10^30,(173642546214668858539 : Int)/10^30)
theorem v3796_pg_checked : Scalar.distance (sourceCoefficient 53 87 1 2) v3796_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3796_mb : Scalar.QComplex := ((-1177218756719861789452688 : Int)/10^30,(-431475886390416872357357422 : Int)/10^30)
theorem v3796_mb_checked : Scalar.distance (sourceCoefficient 53 87 3 1) v3796_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3796_mg : Scalar.QComplex := ((-93086080341721150926102 : Int)/10^30,(253971735673430634896 : Int)/10^30)
theorem v3796_mg_checked : Scalar.distance (sourceCoefficient 53 87 3 2) v3796_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3796_upper : Scalar.QComplex := ((999993551282526274744215897037 : Int)/10^30,(-3591294106794019681178742460 : Int)/10^30)
theorem v3796_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 87 5) 1) 14) v3796_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3796 : Material (53 : Basis) (87 : Basis) where
  plus := ![v3796_pa,v3796_pb,v3796_pg]
  minus := ![(Primitive.Addresses.material3796 1).one,v3796_mb,v3796_mg]
  upper := v3796_upper
  lower := (Primitive.Addresses.material3796 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3796_pa_checked.trans (by decide +kernel)
    · exact v3796_pb_checked.trans (by decide +kernel)
    · exact v3796_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 87 Primitive.Addresses.material3796
    · exact v3796_mb_checked.trans (by decide +kernel)
    · exact v3796_mg_checked.trans (by decide +kernel)
  upper_error := v3796_upper_checked
  lower_error := reuse_lower_error 53 87 Primitive.Addresses.material3796

def v3797_pa : Scalar.QComplex := ((999998238152048541694185664576 : Int)/10^30,(-1877150180142336819002373684 : Int)/10^30)
theorem v3797_pa_checked : Scalar.distance (sourceCoefficient 53 88 1 0) v3797_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3797_pb : Scalar.QComplex := ((-809948050415798413682370 : Int)/10^30,(-431476731046138234708895879 : Int)/10^30)
theorem v3797_pb_checked : Scalar.distance (sourceCoefficient 53 88 1 1) v3797_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3797_pg : Scalar.QComplex := ((-93086262683000282336131 : Int)/10^30,(174737202624553353075 : Int)/10^30)
theorem v3797_pg_checked : Scalar.distance (sourceCoefficient 53 88 1 2) v3797_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3797_mb : Scalar.QComplex := ((-1182292734737360287205496 : Int)/10^30,(-431475871438943002665171712 : Int)/10^30)
theorem v3797_mb_checked : Scalar.distance (sourceCoefficient 53 88 3 1) v3797_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3797_mg : Scalar.QComplex := ((-93086077232394439559487 : Int)/10^30,(255066389807695978751 : Int)/10^30)
theorem v3797_mg_checked : Scalar.distance (sourceCoefficient 53 88 3 2) v3797_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3797_upper : Scalar.QComplex := ((999993508981223667358821243727 : Int)/10^30,(-3603053624266578641204124388 : Int)/10^30)
theorem v3797_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 88 5) 1) 14) v3797_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3797 : Material (53 : Basis) (88 : Basis) where
  plus := ![v3797_pa,v3797_pb,v3797_pg]
  minus := ![(Primitive.Addresses.material3797 1).one,v3797_mb,v3797_mg]
  upper := v3797_upper
  lower := (Primitive.Addresses.material3797 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3797_pa_checked.trans (by decide +kernel)
    · exact v3797_pb_checked.trans (by decide +kernel)
    · exact v3797_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 88 Primitive.Addresses.material3797
    · exact v3797_mb_checked.trans (by decide +kernel)
    · exact v3797_mg_checked.trans (by decide +kernel)
  upper_error := v3797_upper_checked
  lower_error := reuse_lower_error 53 88 Primitive.Addresses.material3797

def v3798_pa : Scalar.QComplex := ((999998207820234235876363575467 : Int)/10^30,(-1893239636078838926889492554 : Int)/10^30)
theorem v3798_pa_checked : Scalar.distance (sourceCoefficient 53 89 1 0) v3798_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3798_pb : Scalar.QComplex := ((-816890285645299147442254 : Int)/10^30,(-431476716451462039514972130 : Int)/10^30)
theorem v3798_pb_checked : Scalar.distance (sourceCoefficient 53 89 1 1) v3798_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3798_pg : Scalar.QComplex := ((-93086259696941379135748 : Int)/10^30,(176234912277221392222 : Int)/10^30)
theorem v3798_pg_checked : Scalar.distance (sourceCoefficient 53 89 1 2) v3798_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3798_mb : Scalar.QComplex := ((-1189234954787401332561142 : Int)/10^30,(-431475850853435905345076268 : Int)/10^30)
theorem v3798_mb_checked : Scalar.distance (sourceCoefficient 53 89 3 1) v3798_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3798_mg : Scalar.QComplex := ((-93086072953880672291519 : Int)/10^30,(256564096325863919137 : Int)/10^30)
theorem v3798_mg_checked : Scalar.distance (sourceCoefficient 53 89 3 2) v3798_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3798_upper : Scalar.QComplex := ((999993450880513214853346446981 : Int)/10^30,(-3619143003889766320788244973 : Int)/10^30)
theorem v3798_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 89 5) 1) 14) v3798_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3798 : Material (53 : Basis) (89 : Basis) where
  plus := ![v3798_pa,v3798_pb,v3798_pg]
  minus := ![(Primitive.Addresses.material3798 1).one,v3798_mb,v3798_mg]
  upper := v3798_upper
  lower := (Primitive.Addresses.material3798 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3798_pa_checked.trans (by decide +kernel)
    · exact v3798_pb_checked.trans (by decide +kernel)
    · exact v3798_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 89 Primitive.Addresses.material3798
    · exact v3798_mb_checked.trans (by decide +kernel)
    · exact v3798_mg_checked.trans (by decide +kernel)
  upper_error := v3798_upper_checked
  lower_error := reuse_lower_error 53 89 Primitive.Addresses.material3798

def v3799_pa : Scalar.QComplex := ((999998157868490007208306579381 : Int)/10^30,(-1919442530146991214812987754 : Int)/10^30)
theorem v3799_pa_checked : Scalar.distance (sourceCoefficient 53 90 1 0) v3799_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3799_pb : Scalar.QComplex := ((-828196239737303986031585 : Int)/10^30,(-431476692364157954354374301 : Int)/10^30)
theorem v3799_pb_checked : Scalar.distance (sourceCoefficient 53 90 1 1) v3799_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3799_pg : Scalar.QComplex := ((-93086254773743924375615 : Int)/10^30,(178674045525911758616 : Int)/10^30)
theorem v3799_pg_checked : Scalar.distance (sourceCoefficient 53 90 1 2) v3799_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3799_mb : Scalar.QComplex := ((-1200540883883424181479996 : Int)/10^30,(-431475817009611608858322066 : Int)/10^30)
theorem v3799_mb_checked : Scalar.distance (sourceCoefficient 53 90 3 1) v3799_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3799_mg : Scalar.QComplex := ((-93086065925822911526545 : Int)/10^30,(259003224417855832271 : Int)/10^30)
theorem v3799_mg_checked : Scalar.distance (sourceCoefficient 53 90 3 2) v3799_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3799_upper : Scalar.QComplex := ((999993355705025329790639295054 : Int)/10^30,(-3645345772719606950510977184 : Int)/10^30)
theorem v3799_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 90 5) 1) 14) v3799_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3799 : Material (53 : Basis) (90 : Basis) where
  plus := ![v3799_pa,v3799_pb,v3799_pg]
  minus := ![(Primitive.Addresses.material3799 1).one,v3799_mb,v3799_mg]
  upper := v3799_upper
  lower := (Primitive.Addresses.material3799 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3799_pa_checked.trans (by decide +kernel)
    · exact v3799_pb_checked.trans (by decide +kernel)
    · exact v3799_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 90 Primitive.Addresses.material3799
    · exact v3799_mb_checked.trans (by decide +kernel)
    · exact v3799_mg_checked.trans (by decide +kernel)
  upper_error := v3799_upper_checked
  lower_error := reuse_lower_error 53 90 Primitive.Addresses.material3799

def v3800_pa : Scalar.QComplex := ((999998129426518155931600339766 : Int)/10^30,(-1934203573733381824732397833 : Int)/10^30)
theorem v3800_pa_checked : Scalar.distance (sourceCoefficient 53 91 1 0) v3800_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3800_pb : Scalar.QComplex := ((-834565294886995609142550 : Int)/10^30,(-431476678620967976185699657 : Int)/10^30)
theorem v3800_pb_checked : Scalar.distance (sourceCoefficient 53 91 1 1) v3800_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3800_pg : Scalar.QComplex := ((-93086251967493659275606 : Int)/10^30,(180048098014169882719 : Int)/10^30)
theorem v3800_pg_checked : Scalar.distance (sourceCoefficient 53 91 1 2) v3800_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3800_mb : Scalar.QComplex := ((-1206909924801871511300569 : Int)/10^30,(-431475797770219005319010711 : Int)/10^30)
theorem v3800_mb_checked : Scalar.distance (sourceCoefficient 53 91 3 1) v3800_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3800_mg : Scalar.QComplex := ((-93086061933828278981790 : Int)/10^30,(260377273972823827733 : Int)/10^30)
theorem v3800_mg_checked : Scalar.distance (sourceCoefficient 53 91 3 2) v3800_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3800_upper : Scalar.QComplex := ((999993301786873720793377155158 : Int)/10^30,(-3660106745232893912711914204 : Int)/10^30)
theorem v3800_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 91 5) 1) 14) v3800_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3800 : Material (53 : Basis) (91 : Basis) where
  plus := ![v3800_pa,v3800_pb,v3800_pg]
  minus := ![(Primitive.Addresses.material3800 1).one,v3800_mb,v3800_mg]
  upper := v3800_upper
  lower := (Primitive.Addresses.material3800 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3800_pa_checked.trans (by decide +kernel)
    · exact v3800_pb_checked.trans (by decide +kernel)
    · exact v3800_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 91 Primitive.Addresses.material3800
    · exact v3800_mb_checked.trans (by decide +kernel)
    · exact v3800_mg_checked.trans (by decide +kernel)
  upper_error := v3800_upper_checked
  lower_error := reuse_lower_error 53 91 Primitive.Addresses.material3800

def v3801_pa : Scalar.QComplex := ((999998067106311014791653552108 : Int)/10^30,(-1966159617602905548508413708 : Int)/10^30)
theorem v3801_pa_checked : Scalar.distance (sourceCoefficient 53 92 1 0) v3801_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3801_pb : Scalar.QComplex := ((-848353601876790958780181 : Int)/10^30,(-431476648439030674011258349 : Int)/10^30)
theorem v3801_pb_checked : Scalar.distance (sourceCoefficient 53 92 1 1) v3801_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3801_pg : Scalar.QComplex := ((-93086245811203836834451 : Int)/10^30,(183022771231806058770 : Int)/10^30)
theorem v3801_pg_checked : Scalar.distance (sourceCoefficient 53 92 1 2) v3801_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3801_mb : Scalar.QComplex := ((-1220698200611997464095907 : Int)/10^30,(-431475755689605011359954566 : Int)/10^30)
theorem v3801_mb_checked : Scalar.distance (sourceCoefficient 53 92 3 1) v3801_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3801_mg : Scalar.QComplex := ((-93086053210531736297035 : Int)/10^30,(263351940770252367811 : Int)/10^30)
theorem v3801_mg_checked : Scalar.distance (sourceCoefficient 53 92 3 2) v3801_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3801_upper : Scalar.QComplex := ((999993184313526709137240390926 : Int)/10^30,(-3692062633948620232857217848 : Int)/10^30)
theorem v3801_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 92 5) 1) 14) v3801_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3801 : Material (53 : Basis) (92 : Basis) where
  plus := ![v3801_pa,v3801_pb,v3801_pg]
  minus := ![(Primitive.Addresses.material3801 1).one,v3801_mb,v3801_mg]
  upper := v3801_upper
  lower := (Primitive.Addresses.material3801 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3801_pa_checked.trans (by decide +kernel)
    · exact v3801_pb_checked.trans (by decide +kernel)
    · exact v3801_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 92 Primitive.Addresses.material3801
    · exact v3801_mb_checked.trans (by decide +kernel)
    · exact v3801_mg_checked.trans (by decide +kernel)
  upper_error := v3801_upper_checked
  lower_error := reuse_lower_error 53 92 Primitive.Addresses.material3801

def v3802_pa : Scalar.QComplex := ((999997991819330214017879003985 : Int)/10^30,(-2004085154573617847275173352 : Int)/10^30)
theorem v3802_pa_checked : Scalar.distance (sourceCoefficient 53 93 1 0) v3802_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3802_pb : Scalar.QComplex := ((-864717608876809439746178 : Int)/10^30,(-431476611856643584786160676 : Int)/10^30)
theorem v3802_pb_checked : Scalar.distance (sourceCoefficient 53 93 1 1) v3802_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3802_pg : Scalar.QComplex := ((-93086238360986095344030 : Int)/10^30,(186553123026729004622 : Int)/10^30)
theorem v3802_pg_checked : Scalar.distance (sourceCoefficient 53 93 1 2) v3802_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3802_mb : Scalar.QComplex := ((-1237062169949995818440591 : Int)/10^30,(-431475704985830509929794629 : Int)/10^30)
theorem v3802_mb_checked : Scalar.distance (sourceCoefficient 53 93 3 1) v3802_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3802_mg : Scalar.QComplex := ((-93086042713782170987112 : Int)/10^30,(266882284821461629810 : Int)/10^30)
theorem v3802_mg_checked : Scalar.distance (sourceCoefficient 53 93 3 2) v3802_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3802_upper : Scalar.QComplex := ((999993043570621805865774794949 : Int)/10^30,(-3729987984495201379680361213 : Int)/10^30)
theorem v3802_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 93 5) 1) 14) v3802_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3802 : Material (53 : Basis) (93 : Basis) where
  plus := ![v3802_pa,v3802_pb,v3802_pg]
  minus := ![(Primitive.Addresses.material3802 1).one,v3802_mb,v3802_mg]
  upper := v3802_upper
  lower := (Primitive.Addresses.material3802 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3802_pa_checked.trans (by decide +kernel)
    · exact v3802_pb_checked.trans (by decide +kernel)
    · exact v3802_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 93 Primitive.Addresses.material3802
    · exact v3802_mb_checked.trans (by decide +kernel)
    · exact v3802_mg_checked.trans (by decide +kernel)
  upper_error := v3802_upper_checked
  lower_error := reuse_lower_error 53 93 Primitive.Addresses.material3802

def v3803_pa : Scalar.QComplex := ((999997901035752856731580737597 : Int)/10^30,(-2048883620080854190442178262 : Int)/10^30)
theorem v3803_pa_checked : Scalar.distance (sourceCoefficient 53 94 1 0) v3803_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3803_pb : Scalar.QComplex := ((-884047127344062658302611 : Int)/10^30,(-431476567578720203169295630 : Int)/10^30)
theorem v3803_pb_checked : Scalar.distance (sourceCoefficient 53 94 1 1) v3803_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3803_pg : Scalar.QComplex := ((-93086229359394157953878 : Int)/10^30,(190723250910836955853 : Int)/10^30)
theorem v3803_pg_checked : Scalar.distance (sourceCoefficient 53 94 1 2) v3803_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3803_mb : Scalar.QComplex := ((-1256391643010132234309157 : Int)/10^30,(-431475644027419746962595512 : Int)/10^30)
theorem v3803_mb_checked : Scalar.distance (sourceCoefficient 53 94 3 1) v3803_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3803_mg : Scalar.QComplex := ((-93086030113561036903728 : Int)/10^30,(271052403384871960212 : Int)/10^30)
theorem v3803_mg_checked : Scalar.distance (sourceCoefficient 53 94 3 2) v3803_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3803_upper : Scalar.QComplex := ((999992875469092279607760121666 : Int)/10^30,(-3774786226596167050367562715 : Int)/10^30)
theorem v3803_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 94 5) 1) 14) v3803_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3803 : Material (53 : Basis) (94 : Basis) where
  plus := ![v3803_pa,v3803_pb,v3803_pg]
  minus := ![(Primitive.Addresses.material3803 1).one,v3803_mb,v3803_mg]
  upper := v3803_upper
  lower := (Primitive.Addresses.material3803 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3803_pa_checked.trans (by decide +kernel)
    · exact v3803_pb_checked.trans (by decide +kernel)
    · exact v3803_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 94 Primitive.Addresses.material3803
    · exact v3803_mb_checked.trans (by decide +kernel)
    · exact v3803_mg_checked.trans (by decide +kernel)
  upper_error := v3803_upper_checked
  lower_error := reuse_lower_error 53 94 Primitive.Addresses.material3803

def v3804_pa : Scalar.QComplex := ((999997809342919825334035654828 : Int)/10^30,(-2093157748802246631402451104 : Int)/10^30)
theorem v3804_pa_checked : Scalar.distance (sourceCoefficient 53 95 1 0) v3804_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3804_pb : Scalar.QComplex := ((-903150405376451808032904 : Int)/10^30,(-431476522684649193786442750 : Int)/10^30)
theorem v3804_pb_checked : Scalar.distance (sourceCoefficient 53 95 1 1) v3804_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3804_pg : Scalar.QComplex := ((-93086220249019070765065 : Int)/10^30,(194844570058583796422 : Int)/10^30)
theorem v3804_pg_checked : Scalar.distance (sourceCoefficient 53 95 1 2) v3804_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3804_mb : Scalar.QComplex := ((-1275494875187936582447109 : Int)/10^30,(-431475582648096891446086519 : Int)/10^30)
theorem v3804_mb_checked : Scalar.distance (sourceCoefficient 53 95 3 1) v3804_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3804_mg : Scalar.QComplex := ((-93086017446676534742376 : Int)/10^30,(275173713136219944303 : Int)/10^30)
theorem v3804_mg_checked : Scalar.distance (sourceCoefficient 53 95 3 2) v3804_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3804_upper : Scalar.QComplex := ((999992707363266158372956615099 : Int)/10^30,(-3819060131122934061951382273 : Int)/10^30)
theorem v3804_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 95 5) 1) 14) v3804_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3804 : Material (53 : Basis) (95 : Basis) where
  plus := ![v3804_pa,v3804_pb,v3804_pg]
  minus := ![(Primitive.Addresses.material3804 1).one,v3804_mb,v3804_mg]
  upper := v3804_upper
  lower := (Primitive.Addresses.material3804 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3804_pa_checked.trans (by decide +kernel)
    · exact v3804_pb_checked.trans (by decide +kernel)
    · exact v3804_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 95 Primitive.Addresses.material3804
    · exact v3804_mb_checked.trans (by decide +kernel)
    · exact v3804_mg_checked.trans (by decide +kernel)
  upper_error := v3804_upper_checked
  lower_error := reuse_lower_error 53 95 Primitive.Addresses.material3804

def v3805_pa : Scalar.QComplex := ((999997764607730748848115271116 : Int)/10^30,(-2114421798393997436808540125 : Int)/10^30)
theorem v3805_pa_checked : Scalar.distance (sourceCoefficient 53 96 1 0) v3805_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3805_pb : Scalar.QComplex := ((-912325358026364684451593 : Int)/10^30,(-431476500721977363571934221 : Int)/10^30)
theorem v3805_pb_checked : Scalar.distance (sourceCoefficient 53 96 1 1) v3805_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3805_pg : Scalar.QComplex := ((-93086215797799636019833 : Int)/10^30,(196823963791642304469 : Int)/10^30)
theorem v3805_pg_checked : Scalar.distance (sourceCoefficient 53 96 1 2) v3805_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3805_mb : Scalar.QComplex := ((-1284669805468798643797192 : Int)/10^30,(-431475552767862326590968279 : Int)/10^30)
theorem v3805_mb_checked : Scalar.distance (sourceCoefficient 53 96 3 1) v3805_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3805_mg : Scalar.QComplex := ((-93086011287331114344465 : Int)/10^30,(277153102291057806066 : Int)/10^30)
theorem v3805_mg_checked : Scalar.distance (sourceCoefficient 53 96 3 2) v3805_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3805_upper : Scalar.QComplex := ((999992625928323173844288779038 : Int)/10^30,(-3840324071835502849810408910 : Int)/10^30)
theorem v3805_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 96 5) 1) 14) v3805_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3805 : Material (53 : Basis) (96 : Basis) where
  plus := ![v3805_pa,v3805_pb,v3805_pg]
  minus := ![(Primitive.Addresses.material3805 1).one,v3805_mb,v3805_mg]
  upper := v3805_upper
  lower := (Primitive.Addresses.material3805 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3805_pa_checked.trans (by decide +kernel)
    · exact v3805_pb_checked.trans (by decide +kernel)
    · exact v3805_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 96 Primitive.Addresses.material3805
    · exact v3805_mb_checked.trans (by decide +kernel)
    · exact v3805_mg_checked.trans (by decide +kernel)
  upper_error := v3805_upper_checked
  lower_error := reuse_lower_error 53 96 Primitive.Addresses.material3805

def v3806_pa : Scalar.QComplex := ((999997607235581641459749285415 : Int)/10^30,(-2187583852426123285025088766 : Int)/10^30)
theorem v3806_pa_checked : Scalar.distance (sourceCoefficient 53 97 1 0) v3806_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3806_pb : Scalar.QComplex := ((-943893114540915647183745 : Int)/10^30,(-431476423168986844947263691 : Int)/10^30)
theorem v3806_pb_checked : Scalar.distance (sourceCoefficient 53 97 1 1) v3806_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3806_pg : Scalar.QComplex := ((-93086200107600440514460 : Int)/10^30,(203634355488133750898 : Int)/10^30)
theorem v3806_pg_checked : Scalar.distance (sourceCoefficient 53 97 1 2) v3806_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3806_mb : Scalar.QComplex := ((-1316237483304493177876523 : Int)/10^30,(-431475447973348571406775111 : Int)/10^30)
theorem v3806_mb_checked : Scalar.distance (sourceCoefficient 53 97 3 1) v3806_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3806_mg : Scalar.QComplex := ((-93085989720076455600918 : Int)/10^30,(283963477911793928233 : Int)/10^30)
theorem v3806_mg_checked : Scalar.distance (sourceCoefficient 53 97 3 2) v3806_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3806_upper : Scalar.QComplex := ((999992342285340404031330608950 : Int)/10^30,(-3913485745291290766244369662 : Int)/10^30)
theorem v3806_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 97 5) 1) 14) v3806_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3806 : Material (53 : Basis) (97 : Basis) where
  plus := ![v3806_pa,v3806_pb,v3806_pg]
  minus := ![(Primitive.Addresses.material3806 1).one,v3806_mb,v3806_mg]
  upper := v3806_upper
  lower := (Primitive.Addresses.material3806 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3806_pa_checked.trans (by decide +kernel)
    · exact v3806_pb_checked.trans (by decide +kernel)
    · exact v3806_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 97 Primitive.Addresses.material3806
    · exact v3806_mb_checked.trans (by decide +kernel)
    · exact v3806_mg_checked.trans (by decide +kernel)
  upper_error := v3806_upper_checked
  lower_error := reuse_lower_error 53 97 Primitive.Addresses.material3806

def v3807_pa : Scalar.QComplex := ((999999215001329168620882247805 : Int)/10^30,(-1252995101921729392548878162 : Int)/10^30)
theorem v3807_pa_checked : Scalar.distance (sourceCoefficient 54 55 1 0) v3807_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3807_pb : Scalar.QComplex := ((-540639220381934515939240 : Int)/10^30,(-431477182274442041646156500 : Int)/10^30)
theorem v3807_pb_checked : Scalar.distance (sourceCoefficient 54 55 1 1) v3807_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3807_pg : Scalar.QComplex := ((-93086356822426063523494 : Int)/10^30,(116636840714003146122 : Int)/10^30)
theorem v3807_pg_checked : Scalar.distance (sourceCoefficient 54 55 1 2) v3807_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3807_mb : Scalar.QComplex := ((-912984394369185449623636 : Int)/10^30,(-431476555068469896460381716 : Int)/10^30)
theorem v3807_mb_checked : Scalar.distance (sourceCoefficient 54 55 3 1) v3807_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3807_mg : Scalar.QComplex := ((-93086221509780753978697 : Int)/10^30,(196966130768650395630 : Int)/10^30)
theorem v3807_mg_checked : Scalar.distance (sourceCoefficient 54 55 3 2) v3807_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3807_upper : Scalar.QComplex := ((999995563064091494416916921926 : Int)/10^30,(-2978901161604881106111719443 : Int)/10^30)
theorem v3807_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 55 5) 1) 14) v3807_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3807 : Material (54 : Basis) (55 : Basis) where
  plus := ![v3807_pa,v3807_pb,v3807_pg]
  minus := ![(Primitive.Addresses.material3807 1).one,v3807_mb,v3807_mg]
  upper := v3807_upper
  lower := (Primitive.Addresses.material3807 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3807_pa_checked.trans (by decide +kernel)
    · exact v3807_pb_checked.trans (by decide +kernel)
    · exact v3807_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 55 Primitive.Addresses.material3807
    · exact v3807_mb_checked.trans (by decide +kernel)
    · exact v3807_mg_checked.trans (by decide +kernel)
  upper_error := v3807_upper_checked
  lower_error := reuse_lower_error 54 55 Primitive.Addresses.material3807

def v3808_pa : Scalar.QComplex := ((999999210431962582748616921483 : Int)/10^30,(-1256636562979454714555576822 : Int)/10^30)
theorem v3808_pa_checked : Scalar.distance (sourceCoefficient 54 56 1 0) v3808_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3808_pb : Scalar.QComplex := ((-542210428960583958149608 : Int)/10^30,(-431477180293873494756194503 : Int)/10^30)
theorem v3808_pb_checked : Scalar.distance (sourceCoefficient 54 56 1 1) v3808_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3808_pg : Scalar.QComplex := ((-93086356396110340708214 : Int)/10^30,(116975811322250450353 : Int)/10^30)
theorem v3808_pg_checked : Scalar.distance (sourceCoefficient 54 56 1 2) v3808_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3808_mb : Scalar.QComplex := ((-914555600653660675753396 : Int)/10^30,(-431476551732019848259614214 : Int)/10^30)
theorem v3808_mb_checked : Scalar.distance (sourceCoefficient 54 56 3 1) v3808_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3808_mg : Scalar.QComplex := ((-93086220790948821652291 : Int)/10^30,(197305100882792182447 : Int)/10^30)
theorem v3808_mg_checked : Scalar.distance (sourceCoefficient 54 56 3 2) v3808_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3808_upper : Scalar.QComplex := ((999995552209900279212118234037 : Int)/10^30,(-2982542609352765741183628094 : Int)/10^30)
theorem v3808_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 56 5) 1) 14) v3808_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3808 : Material (54 : Basis) (56 : Basis) where
  plus := ![v3808_pa,v3808_pb,v3808_pg]
  minus := ![(Primitive.Addresses.material3808 1).one,v3808_mb,v3808_mg]
  upper := v3808_upper
  lower := (Primitive.Addresses.material3808 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3808_pa_checked.trans (by decide +kernel)
    · exact v3808_pb_checked.trans (by decide +kernel)
    · exact v3808_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 56 Primitive.Addresses.material3808
    · exact v3808_mb_checked.trans (by decide +kernel)
    · exact v3808_mg_checked.trans (by decide +kernel)
  upper_error := v3808_upper_checked
  lower_error := reuse_lower_error 54 56 Primitive.Addresses.material3808

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
