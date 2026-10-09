import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B091
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B092

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2193_pa : Scalar.QComplex := ((999998595317090108890879142539 : Int)/10^30,(-1676115702046890586780904957 : Int)/10^30)
theorem v2193_pa_checked : Scalar.distance (sourceCoefficient 25 94 1 0) v2193_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2193_pb : Scalar.QComplex := ((-723206077980804871669438 : Int)/10^30,(-431476813457687303314032263 : Int)/10^30)
theorem v2193_pb_checked : Scalar.distance (sourceCoefficient 25 94 1 1) v2193_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2193_pg : Scalar.QComplex := ((-93086288196292558131014 : Int)/10^30,(156023608454764421493 : Int)/10^30)
theorem v2193_pg_checked : Scalar.distance (sourceCoefficient 25 94 1 2) v2193_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2193_mb : Scalar.QComplex := ((-1095550865717822554541690 : Int)/10^30,(-431476028704876883669169504 : Int)/10^30)
theorem v2193_mb_checked : Scalar.distance (sourceCoefficient 25 94 3 1) v2193_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2193_mg : Scalar.QComplex := ((-93086118894666155123364 : Int)/10^30,(236352824622655568069 : Int)/10^30)
theorem v2193_mg_checked : Scalar.distance (sourceCoefficient 25 94 3 2) v2193_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2193_upper : Scalar.QComplex := ((999994213113004766534167544715 : Int)/10^30,(-3402020062022832348996777314 : Int)/10^30)
theorem v2193_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 94 5) 1) 14) v2193_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2193 : Material (25 : Basis) (94 : Basis) where
  plus := ![v2193_pa,v2193_pb,v2193_pg]
  minus := ![(Primitive.Addresses.material2193 1).one,v2193_mb,v2193_mg]
  upper := v2193_upper
  lower := (Primitive.Addresses.material2193 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2193_pa_checked.trans (by decide +kernel)
    · exact v2193_pb_checked.trans (by decide +kernel)
    · exact v2193_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 94 Primitive.Addresses.material2193
    · exact v2193_mb_checked.trans (by decide +kernel)
    · exact v2193_mg_checked.trans (by decide +kernel)
  upper_error := v2193_upper_checked
  lower_error := reuse_lower_error 25 94 Primitive.Addresses.material2193

def v2194_pa : Scalar.QComplex := ((999998520128266573156195431938 : Int)/10^30,(-1720389861872401354963457716 : Int)/10^30)
theorem v2194_pa_checked : Scalar.distance (sourceCoefficient 25 95 1 0) v2194_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2194_pb : Scalar.QComplex := ((-742309364960344941660897 : Int)/10^30,(-431476773311021830733634220 : Int)/10^30)
theorem v2194_pb_checked : Scalar.distance (sourceCoefficient 25 95 1 1) v2194_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2194_pg : Scalar.QComplex := ((-93086280366166824555772 : Int)/10^30,(160144930015320550813 : Int)/10^30)
theorem v2194_pg_checked : Scalar.distance (sourceCoefficient 25 95 1 2) v2194_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2194_mb : Scalar.QComplex := ((-1114654110939571654559950 : Int)/10^30,(-431475972072950076290787378 : Int)/10^30)
theorem v2194_mb_checked : Scalar.distance (sourceCoefficient 25 95 3 1) v2194_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2194_mg : Scalar.QComplex := ((-93086107508028447734492 : Int)/10^30,(240474137891609474390 : Int)/10^30)
theorem v2194_mg_checked : Scalar.distance (sourceCoefficient 25 95 3 2) v2194_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2194_upper : Scalar.QComplex := ((999994061511109877292289548631 : Int)/10^30,(-3446294026138094519340761883 : Int)/10^30)
theorem v2194_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 95 5) 1) 14) v2194_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2194 : Material (25 : Basis) (95 : Basis) where
  plus := ![v2194_pa,v2194_pb,v2194_pg]
  minus := ![(Primitive.Addresses.material2194 1).one,v2194_mb,v2194_mg]
  upper := v2194_upper
  lower := (Primitive.Addresses.material2194 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2194_pa_checked.trans (by decide +kernel)
    · exact v2194_pb_checked.trans (by decide +kernel)
    · exact v2194_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 95 Primitive.Addresses.material2194
    · exact v2194_mb_checked.trans (by decide +kernel)
    · exact v2194_mg_checked.trans (by decide +kernel)
  upper_error := v2194_upper_checked
  lower_error := reuse_lower_error 25 95 Primitive.Addresses.material2194

def v2195_pa : Scalar.QComplex := ((999998483319649710667898513185 : Int)/10^30,(-1741653926662636169650679685 : Int)/10^30)
theorem v2195_pa_checked : Scalar.distance (sourceCoefficient 25 96 1 0) v2195_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2195_pb : Scalar.QComplex := ((-751484321982126772501764 : Int)/10^30,(-431476753628441548605815518 : Int)/10^30)
theorem v2195_pb_checked : Scalar.distance (sourceCoefficient 25 96 1 1) v2195_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2195_pg : Scalar.QComplex := ((-93086276529827605105364 : Int)/10^30,(162124324927356159506 : Int)/10^30)
theorem v2195_pg_checked : Scalar.distance (sourceCoefficient 25 96 1 2) v2195_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2195_mb : Scalar.QComplex := ((-1123829047559917356973170 : Int)/10^30,(-431475944472802437814064283 : Int)/10^30)
theorem v2195_mb_checked : Scalar.distance (sourceCoefficient 25 96 3 1) v2195_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2195_mg : Scalar.QComplex := ((-93086101963561996279259 : Int)/10^30,(242453528756037930434 : Int)/10^30)
theorem v2195_mg_checked : Scalar.distance (sourceCoefficient 25 96 3 2) v2195_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2195_upper : Scalar.QComplex := ((999993988002701069858448687504 : Int)/10^30,(-3467557995729669228470219585 : Int)/10^30)
theorem v2195_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 96 5) 1) 14) v2195_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2195 : Material (25 : Basis) (96 : Basis) where
  plus := ![v2195_pa,v2195_pb,v2195_pg]
  minus := ![(Primitive.Addresses.material2195 1).one,v2195_mb,v2195_mg]
  upper := v2195_upper
  lower := (Primitive.Addresses.material2195 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2195_pa_checked.trans (by decide +kernel)
    · exact v2195_pb_checked.trans (by decide +kernel)
    · exact v2195_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 96 Primitive.Addresses.material2195
    · exact v2195_mb_checked.trans (by decide +kernel)
    · exact v2195_mg_checked.trans (by decide +kernel)
  upper_error := v2195_upper_checked
  lower_error := reuse_lower_error 25 96 Primitive.Addresses.material2195

def v2196_pa : Scalar.QComplex := ((999998353220024927068342935488 : Int)/10^30,(-1814816034274983204398996996 : Int)/10^30)
theorem v2196_pa_checked : Scalar.distance (sourceCoefficient 25 97 1 0) v2196_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2196_pb : Scalar.QComplex := ((-783052093909116438352872 : Int)/10^30,(-431476683920437474338112305 : Int)/10^30)
theorem v2196_pb_checked : Scalar.distance (sourceCoefficient 25 97 1 1) v2196_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2196_pg : Scalar.QComplex := ((-93086262955213188506287 : Int)/10^30,(168934720780173552589 : Int)/10^30)
theorem v2196_pg_checked : Scalar.distance (sourceCoefficient 25 97 1 2) v2196_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2196_mb : Scalar.QComplex := ((-1155396747577914831822798 : Int)/10^30,(-431475847523258905699401285 : Int)/10^30)
theorem v2196_mb_checked : Scalar.distance (sourceCoefficient 25 97 3 1) v2196_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2196_mg : Scalar.QComplex := ((-93086082511887741991011 : Int)/10^30,(249263910358752833460 : Int)/10^30)
theorem v2196_mg_checked : Scalar.distance (sourceCoefficient 25 97 3 2) v2196_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2196_upper : Scalar.QComplex := ((999993731632109530011968135640 : Int)/10^30,(-3540719769835501368770252139 : Int)/10^30)
theorem v2196_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 97 5) 1) 14) v2196_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2196 : Material (25 : Basis) (97 : Basis) where
  plus := ![v2196_pa,v2196_pb,v2196_pg]
  minus := ![(Primitive.Addresses.material2196 1).one,v2196_mb,v2196_mg]
  upper := v2196_upper
  lower := (Primitive.Addresses.material2196 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2196_pa_checked.trans (by decide +kernel)
    · exact v2196_pb_checked.trans (by decide +kernel)
    · exact v2196_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 97 Primitive.Addresses.material2196
    · exact v2196_mb_checked.trans (by decide +kernel)
    · exact v2196_mg_checked.trans (by decide +kernel)
  upper_error := v2196_upper_checked
  lower_error := reuse_lower_error 25 97 Primitive.Addresses.material2196

def v2197_pa : Scalar.QComplex := ((999999870925908754891020971982 : Int)/10^30,(-508082833630597017147857370 : Int)/10^30)
theorem v2197_pa_checked : Scalar.distance (sourceCoefficient 26 27 1 0) v2197_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2197_pb : Scalar.QComplex := ((-219226321516986998340621 : Int)/10^30,(-431477465306253259965589379 : Int)/10^30)
theorem v2197_pb_checked : Scalar.distance (sourceCoefficient 26 27 1 1) v2197_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2197_pg : Scalar.QComplex := ((-93086417881732249376158 : Int)/10^30,(47295617074511191433 : Int)/10^30)
theorem v2197_pg_checked : Scalar.distance (sourceCoefficient 26 27 1 2) v2197_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2197_mb : Scalar.QComplex := ((-591571859424655276422668 : Int)/10^30,(-431477115465031549956787947 : Int)/10^30)
theorem v2197_mb_checked : Scalar.distance (sourceCoefficient 26 27 3 1) v2197_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2197_mg : Scalar.QComplex := ((-93086342407417192761638 : Int)/10^30,(127624985639496281724 : Int)/10^30)
theorem v2197_mg_checked : Scalar.distance (sourceCoefficient 26 27 3 2) v2197_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2197_upper : Scalar.QComplex := ((999997504638691315480871237163 : Int)/10^30,(-2233991134839388161400183210 : Int)/10^30)
theorem v2197_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 27 5) 1) 14) v2197_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2197 : Material (26 : Basis) (27 : Basis) where
  plus := ![v2197_pa,v2197_pb,v2197_pg]
  minus := ![(Primitive.Addresses.material2197 1).one,v2197_mb,v2197_mg]
  upper := v2197_upper
  lower := (Primitive.Addresses.material2197 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2197_pa_checked.trans (by decide +kernel)
    · exact v2197_pb_checked.trans (by decide +kernel)
    · exact v2197_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 27 Primitive.Addresses.material2197
    · exact v2197_mb_checked.trans (by decide +kernel)
    · exact v2197_mg_checked.trans (by decide +kernel)
  upper_error := v2197_upper_checked
  lower_error := reuse_lower_error 26 27 Primitive.Addresses.material2197

def v2198_pa : Scalar.QComplex := ((999999867449584038651298594030 : Int)/10^30,(-514879417294073458950191018 : Int)/10^30)
theorem v2198_pa_checked : Scalar.distance (sourceCoefficient 26 28 1 0) v2198_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2198_pb : Scalar.QComplex := ((-222158894583115218836901 : Int)/10^30,(-431477463798043537043190071 : Int)/10^30)
theorem v2198_pb_checked : Scalar.distance (sourceCoefficient 26 28 1 1) v2198_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2198_pg : Scalar.QComplex := ((-93086417557243265214747 : Int)/10^30,(47928286782780570686 : Int)/10^30)
theorem v2198_pg_checked : Scalar.distance (sourceCoefficient 26 28 1 2) v2198_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2198_mb : Scalar.QComplex := ((-594504430097335455551621 : Int)/10^30,(-431477111426143910729068397 : Int)/10^30)
theorem v2198_mb_checked : Scalar.distance (sourceCoefficient 26 28 3 1) v2198_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2198_mg : Scalar.QComplex := ((-93086341536962865571730 : Int)/10^30,(128257654832174435264 : Int)/10^30)
theorem v2198_mg_checked : Scalar.distance (sourceCoefficient 26 28 3 2) v2198_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2198_upper : Scalar.QComplex := ((999997489432084954911599511347 : Int)/10^30,(-2240787702380330528739765026 : Int)/10^30)
theorem v2198_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 28 5) 1) 14) v2198_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2198 : Material (26 : Basis) (28 : Basis) where
  plus := ![v2198_pa,v2198_pb,v2198_pg]
  minus := ![(Primitive.Addresses.material2198 1).one,v2198_mb,v2198_mg]
  upper := v2198_upper
  lower := (Primitive.Addresses.material2198 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2198_pa_checked.trans (by decide +kernel)
    · exact v2198_pb_checked.trans (by decide +kernel)
    · exact v2198_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 28 Primitive.Addresses.material2198
    · exact v2198_mb_checked.trans (by decide +kernel)
    · exact v2198_mg_checked.trans (by decide +kernel)
  upper_error := v2198_upper_checked
  lower_error := reuse_lower_error 26 28 Primitive.Addresses.material2198

def v2199_pa : Scalar.QComplex := ((999999860267342450199018940118 : Int)/10^30,(-528644772578322556318927512 : Int)/10^30)
theorem v2199_pa_checked : Scalar.distance (sourceCoefficient 26 29 1 0) v2199_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2199_pb : Scalar.QComplex := ((-228098335937120038634409 : Int)/10^30,(-431477460661996724351048832 : Int)/10^30)
theorem v2199_pb_checked : Scalar.distance (sourceCoefficient 26 29 1 1) v2199_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2199_pg : Scalar.QComplex := ((-93086416884675209323213 : Int)/10^30,(49209654560325859720 : Int)/10^30)
theorem v2199_pg_checked : Scalar.distance (sourceCoefficient 26 29 1 2) v2199_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2199_mb : Scalar.QComplex := ((-600443866533547656325523 : Int)/10^30,(-431477103164627879732744951 : Int)/10^30)
theorem v2199_mb_checked : Scalar.distance (sourceCoefficient 26 29 3 1) v2199_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2199_mg : Scalar.QComplex := ((-93086339758632378748818 : Int)/10^30,(129539021552211998425 : Int)/10^30)
theorem v2199_mg_checked : Scalar.distance (sourceCoefficient 26 29 3 2) v2199_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2199_upper : Scalar.QComplex := ((999997458492099626226965895175 : Int)/10^30,(-2254553024766802508637167904 : Int)/10^30)
theorem v2199_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 29 5) 1) 14) v2199_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2199 : Material (26 : Basis) (29 : Basis) where
  plus := ![v2199_pa,v2199_pb,v2199_pg]
  minus := ![(Primitive.Addresses.material2199 1).one,v2199_mb,v2199_mg]
  upper := v2199_upper
  lower := (Primitive.Addresses.material2199 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2199_pa_checked.trans (by decide +kernel)
    · exact v2199_pb_checked.trans (by decide +kernel)
    · exact v2199_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 29 Primitive.Addresses.material2199
    · exact v2199_mb_checked.trans (by decide +kernel)
    · exact v2199_mg_checked.trans (by decide +kernel)
  upper_error := v2199_upper_checked
  lower_error := reuse_lower_error 26 29 Primitive.Addresses.material2199

def v2200_pa : Scalar.QComplex := ((999999857496169106586796820728 : Int)/10^30,(-533861069454857877877156786 : Int)/10^30)
theorem v2200_pa_checked : Scalar.distance (sourceCoefficient 26 30 1 0) v2200_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2200_pb : Scalar.QComplex := ((-230349050770664082613647 : Int)/10^30,(-431477459445129503491931369 : Int)/10^30)
theorem v2200_pb_checked : Scalar.distance (sourceCoefficient 26 30 1 1) v2200_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2200_pg : Scalar.QComplex := ((-93086416624433173682943 : Int)/10^30,(49695221012599726937 : Int)/10^30)
theorem v2200_pg_checked : Scalar.distance (sourceCoefficient 26 30 1 2) v2200_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2200_mb : Scalar.QComplex := ((-602694579478946099090625 : Int)/10^30,(-431477100005495579053527145 : Int)/10^30)
theorem v2200_mb_checked : Scalar.distance (sourceCoefficient 26 30 3 1) v2200_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2200_mg : Scalar.QComplex := ((-93086339079368460797395 : Int)/10^30,(130024587599110128085 : Int)/10^30)
theorem v2200_mg_checked : Scalar.distance (sourceCoefficient 26 30 3 2) v2200_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2200_upper : Scalar.QComplex := ((999997446718075219808006413398 : Int)/10^30,(-2259769309091482589677659266 : Int)/10^30)
theorem v2200_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 30 5) 1) 14) v2200_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2200 : Material (26 : Basis) (30 : Basis) where
  plus := ![v2200_pa,v2200_pb,v2200_pg]
  minus := ![(Primitive.Addresses.material2200 1).one,v2200_mb,v2200_mg]
  upper := v2200_upper
  lower := (Primitive.Addresses.material2200 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2200_pa_checked.trans (by decide +kernel)
    · exact v2200_pb_checked.trans (by decide +kernel)
    · exact v2200_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 30 Primitive.Addresses.material2200
    · exact v2200_mb_checked.trans (by decide +kernel)
    · exact v2200_mg_checked.trans (by decide +kernel)
  upper_error := v2200_upper_checked
  lower_error := reuse_lower_error 26 30 Primitive.Addresses.material2200

def v2201_pa : Scalar.QComplex := ((999999851511393169209352188795 : Int)/10^30,(-544956137329156920720151941 : Int)/10^30)
theorem v2201_pa_checked : Scalar.distance (sourceCoefficient 26 31 1 0) v2201_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2201_pb : Scalar.QComplex := ((-235136323120013679548031 : Int)/10^30,(-431477456804793911515381265 : Int)/10^30)
theorem v2201_pb_checked : Scalar.distance (sourceCoefficient 26 31 1 1) v2201_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2201_pg : Scalar.QComplex := ((-93086416061071083654047 : Int)/10^30,(50728021266989297120 : Int)/10^30)
theorem v2201_pg_checked : Scalar.distance (sourceCoefficient 26 31 1 2) v2201_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2201_mb : Scalar.QComplex := ((-607481847767284711632304 : Int)/10^30,(-431477093233960543448652787 : Int)/10^30)
theorem v2201_mb_checked : Scalar.distance (sourceCoefficient 26 31 3 1) v2201_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2201_mg : Scalar.QComplex := ((-93086337624746476592470 : Int)/10^30,(131057386982784851447 : Int)/10^30)
theorem v2201_mg_checked : Scalar.distance (sourceCoefficient 26 31 3 2) v2201_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2201_upper : Scalar.QComplex := ((999997421584227581706074629097 : Int)/10^30,(-2270864350111801018696254032 : Int)/10^30)
theorem v2201_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 31 5) 1) 14) v2201_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2201 : Material (26 : Basis) (31 : Basis) where
  plus := ![v2201_pa,v2201_pb,v2201_pg]
  minus := ![(Primitive.Addresses.material2201 1).one,v2201_mb,v2201_mg]
  upper := v2201_upper
  lower := (Primitive.Addresses.material2201 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2201_pa_checked.trans (by decide +kernel)
    · exact v2201_pb_checked.trans (by decide +kernel)
    · exact v2201_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 31 Primitive.Addresses.material2201
    · exact v2201_mb_checked.trans (by decide +kernel)
    · exact v2201_mg_checked.trans (by decide +kernel)
  upper_error := v2201_upper_checked
  lower_error := reuse_lower_error 26 31 Primitive.Addresses.material2201

def v2202_pa : Scalar.QComplex := ((999999848897228058349797241374 : Int)/10^30,(-549732226680638322814670553 : Int)/10^30)
theorem v2202_pa_checked : Scalar.distance (sourceCoefficient 26 32 1 0) v2202_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2202_pb : Scalar.QComplex := ((-237197098296133698870451 : Int)/10^30,(-431477455646405124638016568 : Int)/10^30)
theorem v2202_pb_checked : Scalar.distance (sourceCoefficient 26 32 1 1) v2202_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2202_pg : Scalar.QComplex := ((-93086415814444748673825 : Int)/10^30,(51172610371717771236 : Int)/10^30)
theorem v2202_pg_checked : Scalar.distance (sourceCoefficient 26 32 1 2) v2202_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2202_mb : Scalar.QComplex := ((-609542621176446599626087 : Int)/10^30,(-431477090297216024769317446 : Int)/10^30)
theorem v2202_mb_checked : Scalar.distance (sourceCoefficient 26 32 3 1) v2202_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2202_mg : Scalar.QComplex := ((-93086336994459859611799 : Int)/10^30,(131501975709145063697 : Int)/10^30)
theorem v2202_mg_checked : Scalar.distance (sourceCoefficient 26 32 3 2) v2202_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2202_upper : Scalar.QComplex := ((999997410726969427122812778413 : Int)/10^30,(-2275640427838046544487990577 : Int)/10^30)
theorem v2202_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 32 5) 1) 14) v2202_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2202 : Material (26 : Basis) (32 : Basis) where
  plus := ![v2202_pa,v2202_pb,v2202_pg]
  minus := ![(Primitive.Addresses.material2202 1).one,v2202_mb,v2202_mg]
  upper := v2202_upper
  lower := (Primitive.Addresses.material2202 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2202_pa_checked.trans (by decide +kernel)
    · exact v2202_pb_checked.trans (by decide +kernel)
    · exact v2202_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 32 Primitive.Addresses.material2202
    · exact v2202_mb_checked.trans (by decide +kernel)
    · exact v2202_mg_checked.trans (by decide +kernel)
  upper_error := v2202_upper_checked
  lower_error := reuse_lower_error 26 32 Primitive.Addresses.material2202

def v2203_pa : Scalar.QComplex := ((999999845215993767557998343132 : Int)/10^30,(-556388343252080918314230413 : Int)/10^30)
theorem v2203_pa_checked : Scalar.distance (sourceCoefficient 26 33 1 0) v2203_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2203_pb : Scalar.QComplex := ((-240069062946183228595607 : Int)/10^30,(-431477454010147478014842136 : Int)/10^30)
theorem v2203_pb_checked : Scalar.distance (sourceCoefficient 26 33 1 1) v2203_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2203_pg : Scalar.QComplex := ((-93086415466606163363602 : Int)/10^30,(51792204497344787870 : Int)/10^30)
theorem v2203_pg_checked : Scalar.distance (sourceCoefficient 26 33 1 2) v2203_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2203_mb : Scalar.QComplex := ((-612414583345115780142097 : Int)/10^30,(-431477086182582842893098087 : Int)/10^30)
theorem v2203_mb_checked : Scalar.distance (sourceCoefficient 26 33 3 1) v2203_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2203_mg : Scalar.QComplex := ((-93086336111939578885180 : Int)/10^30,(132121569303899837455 : Int)/10^30)
theorem v2203_mg_checked : Scalar.distance (sourceCoefficient 26 33 3 2) v2203_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2203_upper : Scalar.QComplex := ((999997395557887254965578305672 : Int)/10^30,(-2282296528142508962259998857 : Int)/10^30)
theorem v2203_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 33 5) 1) 14) v2203_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2203 : Material (26 : Basis) (33 : Basis) where
  plus := ![v2203_pa,v2203_pb,v2203_pg]
  minus := ![(Primitive.Addresses.material2203 1).one,v2203_mb,v2203_mg]
  upper := v2203_upper
  lower := (Primitive.Addresses.material2203 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2203_pa_checked.trans (by decide +kernel)
    · exact v2203_pb_checked.trans (by decide +kernel)
    · exact v2203_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 33 Primitive.Addresses.material2203
    · exact v2203_mb_checked.trans (by decide +kernel)
    · exact v2203_mg_checked.trans (by decide +kernel)
  upper_error := v2203_upper_checked
  lower_error := reuse_lower_error 26 33 Primitive.Addresses.material2203

def v2204_pa : Scalar.QComplex := ((999999836090197410165244048398 : Int)/10^30,(-572555305899129823848344248 : Int)/10^30)
theorem v2204_pa_checked : Scalar.distance (sourceCoefficient 26 34 1 0) v2204_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2204_pb : Scalar.QComplex := ((-247044743826144189338224 : Int)/10^30,(-431477449929722953818036844 : Int)/10^30)
theorem v2204_pb_checked : Scalar.distance (sourceCoefficient 26 34 1 1) v2204_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2204_pg : Scalar.QComplex := ((-93086414601709376998000 : Int)/10^30,(53297129323256883412 : Int)/10^30)
theorem v2204_pg_checked : Scalar.distance (sourceCoefficient 26 34 1 2) v2204_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2204_mb : Scalar.QComplex := ((-619390258106489356026439 : Int)/10^30,(-431477076082461411622701965 : Int)/10^30)
theorem v2204_mb_checked : Scalar.distance (sourceCoefficient 26 34 3 1) v2204_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2204_mg : Scalar.QComplex := ((-93086333948360769096114 : Int)/10^30,(133626492823092668720 : Int)/10^30)
theorem v2204_mg_checked : Scalar.distance (sourceCoefficient 26 34 3 2) v2204_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2204_upper : Scalar.QComplex := ((999997358529393615962553122670 : Int)/10^30,(-2298463450960469482770688950 : Int)/10^30)
theorem v2204_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 34 5) 1) 14) v2204_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2204 : Material (26 : Basis) (34 : Basis) where
  plus := ![v2204_pa,v2204_pb,v2204_pg]
  minus := ![(Primitive.Addresses.material2204 1).one,v2204_mb,v2204_mg]
  upper := v2204_upper
  lower := (Primitive.Addresses.material2204 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2204_pa_checked.trans (by decide +kernel)
    · exact v2204_pb_checked.trans (by decide +kernel)
    · exact v2204_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 34 Primitive.Addresses.material2204
    · exact v2204_mb_checked.trans (by decide +kernel)
    · exact v2204_mg_checked.trans (by decide +kernel)
  upper_error := v2204_upper_checked
  lower_error := reuse_lower_error 26 34 Primitive.Addresses.material2204

def v2205_pa : Scalar.QComplex := ((999999805363519548756100452134 : Int)/10^30,(-623917400798477711962125662 : Int)/10^30)
theorem v2205_pa_checked : Scalar.distance (sourceCoefficient 26 35 1 0) v2205_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2205_pb : Scalar.QComplex := ((-269206332750093742801435 : Int)/10^30,(-431477435968600178968019874 : Int)/10^30)
theorem v2205_pb_checked : Scalar.distance (sourceCoefficient 26 35 1 1) v2205_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2205_pg : Scalar.QComplex := ((-93086411665613273910494 : Int)/10^30,(58078243320211398902 : Int)/10^30)
theorem v2205_pg_checked : Scalar.distance (sourceCoefficient 26 35 1 2) v2205_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2205_mb : Scalar.QComplex := ((-641551826730846349386955 : Int)/10^30,(-431477042996890714681429012 : Int)/10^30)
theorem v2205_mb_checked : Scalar.distance (sourceCoefficient 26 35 3 1) v2205_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2205_mg : Scalar.QComplex := ((-93086326886379713260499 : Int)/10^30,(138407602506101235335 : Int)/10^30)
theorem v2205_mg_checked : Scalar.distance (sourceCoefficient 26 35 3 2) v2205_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2205_upper : Scalar.QComplex := ((999997239156445254907215769281 : Int)/10^30,(-2349825416330551947445621758 : Int)/10^30)
theorem v2205_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 35 5) 1) 14) v2205_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2205 : Material (26 : Basis) (35 : Basis) where
  plus := ![v2205_pa,v2205_pb,v2205_pg]
  minus := ![(Primitive.Addresses.material2205 1).one,v2205_mb,v2205_mg]
  upper := v2205_upper
  lower := (Primitive.Addresses.material2205 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2205_pa_checked.trans (by decide +kernel)
    · exact v2205_pb_checked.trans (by decide +kernel)
    · exact v2205_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 35 Primitive.Addresses.material2205
    · exact v2205_mb_checked.trans (by decide +kernel)
    · exact v2205_mg_checked.trans (by decide +kernel)
  upper_error := v2205_upper_checked
  lower_error := reuse_lower_error 26 35 Primitive.Addresses.material2205

def v2206_pa : Scalar.QComplex := ((999999795160091060568349678628 : Int)/10^30,(-640062321902699570494813583 : Int)/10^30)
theorem v2206_pa_checked : Scalar.distance (sourceCoefficient 26 36 1 0) v2206_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2206_pb : Scalar.QComplex := ((-276172503076272843841107 : Int)/10^30,(-431477431266615630448728174 : Int)/10^30)
theorem v2206_pb_checked : Scalar.distance (sourceCoefficient 26 36 1 1) v2206_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2206_pg : Scalar.QComplex := ((-93086410683512726054593 : Int)/10^30,(59581116364267865381 : Int)/10^30)
theorem v2206_pg_checked : Scalar.distance (sourceCoefficient 26 36 1 2) v2206_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2206_mb : Scalar.QComplex := ((-648517990405600972429120 : Int)/10^30,(-431477032283416670098053530 : Int)/10^30)
theorem v2206_mb_checked : Scalar.distance (sourceCoefficient 26 36 3 1) v2206_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2206_mg : Scalar.QComplex := ((-93086324607367780954035 : Int)/10^30,(139910474143060842187 : Int)/10^30)
theorem v2206_mg_checked : Scalar.distance (sourceCoefficient 26 36 3 2) v2206_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2206_upper : Scalar.QComplex := ((999997201088362793442003183490 : Int)/10^30,(-2365970295778618414085338683 : Int)/10^30)
theorem v2206_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 36 5) 1) 14) v2206_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2206 : Material (26 : Basis) (36 : Basis) where
  plus := ![v2206_pa,v2206_pb,v2206_pg]
  minus := ![(Primitive.Addresses.material2206 1).one,v2206_mb,v2206_mg]
  upper := v2206_upper
  lower := (Primitive.Addresses.material2206 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2206_pa_checked.trans (by decide +kernel)
    · exact v2206_pb_checked.trans (by decide +kernel)
    · exact v2206_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 36 Primitive.Addresses.material2206
    · exact v2206_mb_checked.trans (by decide +kernel)
    · exact v2206_mg_checked.trans (by decide +kernel)
  upper_error := v2206_upper_checked
  lower_error := reuse_lower_error 26 36 Primitive.Addresses.material2206

def v2207_pa : Scalar.QComplex := ((999999790723701034490713801838 : Int)/10^30,(-646956377304103297062502530 : Int)/10^30)
theorem v2207_pa_checked : Scalar.distance (sourceCoefficient 26 37 1 0) v2207_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2207_pb : Scalar.QComplex := ((-279147132911092591442928 : Int)/10^30,(-431477429213129218671560331 : Int)/10^30)
theorem v2207_pb_checked : Scalar.distance (sourceCoefficient 26 37 1 1) v2207_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2207_pg : Scalar.QComplex := ((-93086410255520554705259 : Int)/10^30,(60222859358372226232 : Int)/10^30)
theorem v2207_pg_checked : Scalar.distance (sourceCoefficient 26 37 1 2) v2207_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2207_mb : Scalar.QComplex := ((-651492617360763797459229 : Int)/10^30,(-431477027662959447832756288 : Int)/10^30)
theorem v2207_mb_checked : Scalar.distance (sourceCoefficient 26 37 3 1) v2207_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2207_mg : Scalar.QComplex := ((-93086323625580468085206 : Int)/10^30,(140552216528876989407 : Int)/10^30)
theorem v2207_mg_checked : Scalar.distance (sourceCoefficient 26 37 3 2) v2207_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2207_upper : Scalar.QComplex := ((999997184753465175843816684579 : Int)/10^30,(-2372864333255329734046538804 : Int)/10^30)
theorem v2207_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 37 5) 1) 14) v2207_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2207 : Material (26 : Basis) (37 : Basis) where
  plus := ![v2207_pa,v2207_pb,v2207_pg]
  minus := ![(Primitive.Addresses.material2207 1).one,v2207_mb,v2207_mg]
  upper := v2207_upper
  lower := (Primitive.Addresses.material2207 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2207_pa_checked.trans (by decide +kernel)
    · exact v2207_pb_checked.trans (by decide +kernel)
    · exact v2207_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 37 Primitive.Addresses.material2207
    · exact v2207_mb_checked.trans (by decide +kernel)
    · exact v2207_mg_checked.trans (by decide +kernel)
  upper_error := v2207_upper_checked
  lower_error := reuse_lower_error 26 37 Primitive.Addresses.material2207

def v2208_pa : Scalar.QComplex := ((999999775377491513706354937070 : Int)/10^30,(-670257388260148887298144680 : Int)/10^30)
theorem v2208_pa_checked : Scalar.distance (sourceCoefficient 26 38 1 0) v2208_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2208_pb : Scalar.QComplex := ((-289200994971065436955154 : Int)/10^30,(-431477422070227323740592917 : Int)/10^30)
theorem v2208_pb_checked : Scalar.distance (sourceCoefficient 26 38 1 1) v2208_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2208_pg : Scalar.QComplex := ((-93086408770758190357253 : Int)/10^30,(62391867239822729666 : Int)/10^30)
theorem v2208_pg_checked : Scalar.distance (sourceCoefficient 26 38 1 2) v2208_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2208_mb : Scalar.QComplex := ((-661546469513221682882139 : Int)/10^30,(-431477011844030063912161276 : Int)/10^30)
theorem v2208_mb_checked : Scalar.distance (sourceCoefficient 26 38 3 1) v2208_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2208_mg : Scalar.QComplex := ((-93086320269062543378914 : Int)/10^30,(142721222321423680801 : Int)/10^30)
theorem v2208_mg_checked : Scalar.distance (sourceCoefficient 26 38 3 2) v2208_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2208_upper : Scalar.QComplex := ((999997129191847452502590928603 : Int)/10^30,(-2396165283021091198650672239 : Int)/10^30)
theorem v2208_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 38 5) 1) 14) v2208_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2208 : Material (26 : Basis) (38 : Basis) where
  plus := ![v2208_pa,v2208_pb,v2208_pg]
  minus := ![(Primitive.Addresses.material2208 1).one,v2208_mb,v2208_mg]
  upper := v2208_upper
  lower := (Primitive.Addresses.material2208 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2208_pa_checked.trans (by decide +kernel)
    · exact v2208_pb_checked.trans (by decide +kernel)
    · exact v2208_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 38 Primitive.Addresses.material2208
    · exact v2208_mb_checked.trans (by decide +kernel)
    · exact v2208_mg_checked.trans (by decide +kernel)
  upper_error := v2208_upper_checked
  lower_error := reuse_lower_error 26 38 Primitive.Addresses.material2208

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
