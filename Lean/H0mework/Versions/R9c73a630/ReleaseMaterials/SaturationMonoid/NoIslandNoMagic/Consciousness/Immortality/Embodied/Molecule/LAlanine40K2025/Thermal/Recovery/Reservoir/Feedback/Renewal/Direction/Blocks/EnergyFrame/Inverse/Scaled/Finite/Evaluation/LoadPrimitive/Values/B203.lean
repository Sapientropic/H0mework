import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B135
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B136

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3249_pa : Scalar.QComplex := ((999998812030677351311484722961 : Int)/10^30,(-1541407549620237676929136420 : Int)/10^30)
theorem v3249_pa_checked : Scalar.distance (sourceCoefficient 42 79 1 0) v3249_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3249_pb : Scalar.QComplex := ((-665082671189800342421055 : Int)/10^30,(-431476984302982456264749287 : Int)/10^30)
theorem v3249_pb_checked : Scalar.distance (sourceCoefficient 42 79 1 1) v3249_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3249_pg : Scalar.QComplex := ((-93086316711816761088519 : Int)/10^30,(143484121800669840261 : Int)/10^30)
theorem v3249_pg_checked : Scalar.distance (sourceCoefficient 42 79 1 2) v3249_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3249_mb : Scalar.QComplex := ((-1037427628000613875041284 : Int)/10^30,(-431476249707990702680128238 : Int)/10^30)
theorem v3249_mb_checked : Scalar.distance (sourceCoefficient 42 79 3 1) v3249_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3249_mg : Scalar.QComplex := ((-93086158231191965417492 : Int)/10^30,(223813367245198046625 : Int)/10^30)
theorem v3249_mg_checked : Scalar.distance (sourceCoefficient 42 79 3 2) v3249_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3249_upper : Scalar.QComplex := ((999994662320319699800626304808 : Int)/10^30,(-3267312484256140024849576355 : Int)/10^30)
theorem v3249_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 79 5) 1) 14) v3249_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3249 : Material (42 : Basis) (79 : Basis) where
  plus := ![v3249_pa,v3249_pb,v3249_pg]
  minus := ![(Primitive.Addresses.material3249 1).one,v3249_mb,v3249_mg]
  upper := v3249_upper
  lower := (Primitive.Addresses.material3249 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3249_pa_checked.trans (by decide +kernel)
    · exact v3249_pb_checked.trans (by decide +kernel)
    · exact v3249_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 79 Primitive.Addresses.material3249
    · exact v3249_mb_checked.trans (by decide +kernel)
    · exact v3249_mg_checked.trans (by decide +kernel)
  upper_error := v3249_upper_checked
  lower_error := reuse_lower_error 42 79 Primitive.Addresses.material3249

def v3250_pa : Scalar.QComplex := ((999998798564059946013713237525 : Int)/10^30,(-1550119491090817334000921582 : Int)/10^30)
theorem v3250_pa_checked : Scalar.distance (sourceCoefficient 42 80 1 0) v3250_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3250_pb : Scalar.QComplex := ((-668841676755304742139905 : Int)/10^30,(-431476977761381166674756982 : Int)/10^30)
theorem v3250_pb_checked : Scalar.distance (sourceCoefficient 42 80 1 1) v3250_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3250_pg : Scalar.QComplex := ((-93086315379398582609479 : Int)/10^30,(144295085184733967846 : Int)/10^30)
theorem v3250_pg_checked : Scalar.distance (sourceCoefficient 42 80 1 2) v3250_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3250_mb : Scalar.QComplex := ((-1041186626521361417550663 : Int)/10^30,(-431476239922539345122948961 : Int)/10^30)
theorem v3250_mb_checked : Scalar.distance (sourceCoefficient 42 80 3 1) v3250_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3250_mg : Scalar.QComplex := ((-93086156198949407046260 : Int)/10^30,(224624329177486565325 : Int)/10^30)
theorem v3250_mg_checked : Scalar.distance (sourceCoefficient 42 80 3 2) v3250_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3250_upper : Scalar.QComplex := ((999994633817701714383496582875 : Int)/10^30,(-3276024389509146278470176234 : Int)/10^30)
theorem v3250_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 80 5) 1) 14) v3250_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3250 : Material (42 : Basis) (80 : Basis) where
  plus := ![v3250_pa,v3250_pb,v3250_pg]
  minus := ![(Primitive.Addresses.material3250 1).one,v3250_mb,v3250_mg]
  upper := v3250_upper
  lower := (Primitive.Addresses.material3250 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3250_pa_checked.trans (by decide +kernel)
    · exact v3250_pb_checked.trans (by decide +kernel)
    · exact v3250_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 80 Primitive.Addresses.material3250
    · exact v3250_mb_checked.trans (by decide +kernel)
    · exact v3250_mg_checked.trans (by decide +kernel)
  upper_error := v3250_upper_checked
  lower_error := reuse_lower_error 42 80 Primitive.Addresses.material3250

def v3251_pa : Scalar.QComplex := ((999998757557047164520446659398 : Int)/10^30,(-1576351598472392851252839029 : Int)/10^30)
theorem v3251_pa_checked : Scalar.distance (sourceCoefficient 42 81 1 0) v3251_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3251_pb : Scalar.QComplex := ((-680160237193277984116757 : Int)/10^30,(-431476957800602206814881701 : Int)/10^30)
theorem v3251_pb_checked : Scalar.distance (sourceCoefficient 42 81 1 1) v3251_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3251_pg : Scalar.QComplex := ((-93086311317643415731030 : Int)/10^30,(146736937953740473280 : Int)/10^30)
theorem v3251_pg_checked : Scalar.distance (sourceCoefficient 42 81 1 2) v3251_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3251_mb : Scalar.QComplex := ((-1052505165519664082456552 : Int)/10^30,(-431476210194359928641035369 : Int)/10^30)
theorem v3251_mb_checked : Scalar.distance (sourceCoefficient 42 81 3 1) v3251_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3251_mg : Scalar.QComplex := ((-93086150029986789858456 : Int)/10^30,(227066177532167912318 : Int)/10^30)
theorem v3251_mg_checked : Scalar.distance (sourceCoefficient 42 81 3 2) v3251_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3251_upper : Scalar.QComplex := ((999994547536512425611408868605 : Int)/10^30,(-3302256387046695356939860506 : Int)/10^30)
theorem v3251_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 81 5) 1) 14) v3251_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3251 : Material (42 : Basis) (81 : Basis) where
  plus := ![v3251_pa,v3251_pb,v3251_pg]
  minus := ![(Primitive.Addresses.material3251 1).one,v3251_mb,v3251_mg]
  upper := v3251_upper
  lower := (Primitive.Addresses.material3251 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3251_pa_checked.trans (by decide +kernel)
    · exact v3251_pb_checked.trans (by decide +kernel)
    · exact v3251_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 81 Primitive.Addresses.material3251
    · exact v3251_mb_checked.trans (by decide +kernel)
    · exact v3251_mg_checked.trans (by decide +kernel)
  upper_error := v3251_upper_checked
  lower_error := reuse_lower_error 42 81 Primitive.Addresses.material3251

def v3252_pa : Scalar.QComplex := ((999998741838299839851836755255 : Int)/10^30,(-1586291844948284595642059944 : Int)/10^30)
theorem v3252_pa_checked : Scalar.distance (sourceCoefficient 42 82 1 0) v3252_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3252_pb : Scalar.QComplex := ((-684449228427493353316659 : Int)/10^30,(-431476950133348536900084181 : Int)/10^30)
theorem v3252_pb_checked : Scalar.distance (sourceCoefficient 42 82 1 1) v3252_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3252_pg : Scalar.QComplex := ((-93086309758980439858675 : Int)/10^30,(147662239829975305050 : Int)/10^30)
theorem v3252_pg_checked : Scalar.distance (sourceCoefficient 42 82 1 2) v3252_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3252_mb : Scalar.QComplex := ((-1056794148540397401725184 : Int)/10^30,(-431476198825902847461745264 : Int)/10^30)
theorem v3252_mb_checked : Scalar.distance (sourceCoefficient 42 82 3 1) v3252_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3252_mg : Scalar.QComplex := ((-93086147672830549206394 : Int)/10^30,(227991477718814618578 : Int)/10^30)
theorem v3252_mg_checked : Scalar.distance (sourceCoefficient 42 82 3 2) v3252_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3252_upper : Scalar.QComplex := ((999994514661824866897370181585 : Int)/10^30,(-3312196591588625750103287184 : Int)/10^30)
theorem v3252_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 82 5) 1) 14) v3252_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3252 : Material (42 : Basis) (82 : Basis) where
  plus := ![v3252_pa,v3252_pb,v3252_pg]
  minus := ![(Primitive.Addresses.material3252 1).one,v3252_mb,v3252_mg]
  upper := v3252_upper
  lower := (Primitive.Addresses.material3252 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3252_pa_checked.trans (by decide +kernel)
    · exact v3252_pb_checked.trans (by decide +kernel)
    · exact v3252_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 82 Primitive.Addresses.material3252
    · exact v3252_mb_checked.trans (by decide +kernel)
    · exact v3252_mg_checked.trans (by decide +kernel)
  upper_error := v3252_upper_checked
  lower_error := reuse_lower_error 42 82 Primitive.Addresses.material3252

def v3253_pa : Scalar.QComplex := ((999998720222453668897335772685 : Int)/10^30,(-1599860448549071805947766134 : Int)/10^30)
theorem v3253_pa_checked : Scalar.distance (sourceCoefficient 42 83 1 0) v3253_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3253_pb : Scalar.QComplex := ((-690303773523369335187152 : Int)/10^30,(-431476939575662295459614872 : Int)/10^30)
theorem v3253_pb_checked : Scalar.distance (sourceCoefficient 42 83 1 1) v3253_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3253_pg : Scalar.QComplex := ((-93086307614058339959722 : Int)/10^30,(148925292444449605096 : Int)/10^30)
theorem v3253_pg_checked : Scalar.distance (sourceCoefficient 42 83 1 2) v3253_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3253_mb : Scalar.QComplex := ((-1062648682345550952645922 : Int)/10^30,(-431476183216011798312297924 : Int)/10^30)
theorem v3253_mb_checked : Scalar.distance (sourceCoefficient 42 83 3 1) v3253_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3253_mg : Scalar.QComplex := ((-93086144437951727446702 : Int)/10^30,(229254528012025537392 : Int)/10^30)
theorem v3253_mg_checked : Scalar.distance (sourceCoefficient 42 83 3 2) v3253_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3253_upper : Scalar.QComplex := ((999994469627832009350974076321 : Int)/10^30,(-3325765137673582260358235576 : Int)/10^30)
theorem v3253_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 83 5) 1) 14) v3253_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3253 : Material (42 : Basis) (83 : Basis) where
  plus := ![v3253_pa,v3253_pb,v3253_pg]
  minus := ![(Primitive.Addresses.material3253 1).one,v3253_mb,v3253_mg]
  upper := v3253_upper
  lower := (Primitive.Addresses.material3253 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3253_pa_checked.trans (by decide +kernel)
    · exact v3253_pb_checked.trans (by decide +kernel)
    · exact v3253_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 83 Primitive.Addresses.material3253
    · exact v3253_mb_checked.trans (by decide +kernel)
    · exact v3253_mg_checked.trans (by decide +kernel)
  upper_error := v3253_upper_checked
  lower_error := reuse_lower_error 42 83 Primitive.Addresses.material3253

def v3254_pa : Scalar.QComplex := ((999998663387490008681389214118 : Int)/10^30,(-1634999459770441439848021322 : Int)/10^30)
theorem v3254_pa_checked : Scalar.distance (sourceCoefficient 42 84 1 0) v3254_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3254_pb : Scalar.QComplex := ((-705465460535195434156235 : Int)/10^30,(-431476911741784143846389642 : Int)/10^30)
theorem v3254_pb_checked : Scalar.distance (sourceCoefficient 42 84 1 1) v3254_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3254_pg : Scalar.QComplex := ((-93086301966353082028930 : Int)/10^30,(152196256854436355329 : Int)/10^30)
theorem v3254_pg_checked : Scalar.distance (sourceCoefficient 42 84 1 2) v3254_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3254_mb : Scalar.QComplex := ((-1077810339692604800278839 : Int)/10^30,(-431476142298290976352224209 : Int)/10^30)
theorem v3254_mb_checked : Scalar.distance (sourceCoefficient 42 84 3 1) v3254_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3254_mg : Scalar.QComplex := ((-93086135967553605364420 : Int)/10^30,(232525486330367472936 : Int)/10^30)
theorem v3254_mg_checked : Scalar.distance (sourceCoefficient 42 84 3 2) v3254_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3254_upper : Scalar.QComplex := ((999994352146207416249490929113 : Int)/10^30,(-3360903998467531148336726591 : Int)/10^30)
theorem v3254_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 84 5) 1) 14) v3254_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3254 : Material (42 : Basis) (84 : Basis) where
  plus := ![v3254_pa,v3254_pb,v3254_pg]
  minus := ![(Primitive.Addresses.material3254 1).one,v3254_mb,v3254_mg]
  upper := v3254_upper
  lower := (Primitive.Addresses.material3254 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3254_pa_checked.trans (by decide +kernel)
    · exact v3254_pb_checked.trans (by decide +kernel)
    · exact v3254_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 84 Primitive.Addresses.material3254
    · exact v3254_mb_checked.trans (by decide +kernel)
    · exact v3254_mg_checked.trans (by decide +kernel)
  upper_error := v3254_upper_checked
  lower_error := reuse_lower_error 42 84 Primitive.Addresses.material3254

def v3255_pa : Scalar.QComplex := ((999998531004650314607289989196 : Int)/10^30,(-1714056166356122655372069260 : Int)/10^30)
theorem v3255_pa_checked : Scalar.distance (sourceCoefficient 42 85 1 0) v3255_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3255_pb : Scalar.QComplex := ((-739576635858063120393810 : Int)/10^30,(-431476846523456121458582118 : Int)/10^30)
theorem v3255_pb_checked : Scalar.distance (sourceCoefficient 42 85 1 1) v3255_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3255_pg : Scalar.QComplex := ((-93086288769769159811300 : Int)/10^30,(159555361655113807840 : Int)/10^30)
theorem v3255_pg_checked : Scalar.distance (sourceCoefficient 42 85 1 2) v3255_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3255_mb : Scalar.QComplex := ((-1111921446033843197221286 : Int)/10^30,(-431476047643579244399773691 : Int)/10^30)
theorem v3255_mb_checked : Scalar.distance (sourceCoefficient 42 85 3 1) v3255_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3255_mg : Scalar.QComplex := ((-93086116420398595629983 : Int)/10^30,(239884577002856307653 : Int)/10^30)
theorem v3255_mg_checked : Scalar.distance (sourceCoefficient 42 85 3 2) v3255_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3255_upper : Scalar.QComplex := ((999994083318861292375667707260 : Int)/10^30,(-3439960358826762923026658333 : Int)/10^30)
theorem v3255_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 85 5) 1) 14) v3255_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3255 : Material (42 : Basis) (85 : Basis) where
  plus := ![v3255_pa,v3255_pb,v3255_pg]
  minus := ![(Primitive.Addresses.material3255 1).one,v3255_mb,v3255_mg]
  upper := v3255_upper
  lower := (Primitive.Addresses.material3255 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3255_pa_checked.trans (by decide +kernel)
    · exact v3255_pb_checked.trans (by decide +kernel)
    · exact v3255_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 85 Primitive.Addresses.material3255
    · exact v3255_mb_checked.trans (by decide +kernel)
    · exact v3255_mg_checked.trans (by decide +kernel)
  upper_error := v3255_upper_checked
  lower_error := reuse_lower_error 42 85 Primitive.Addresses.material3255

def v3256_pa : Scalar.QComplex := ((999998505899395395215038684484 : Int)/10^30,(-1728640788849133121787138127 : Int)/10^30)
theorem v3256_pa_checked : Scalar.distance (sourceCoefficient 42 86 1 0) v3256_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3256_pb : Scalar.QComplex := ((-745869569271068474314280 : Int)/10^30,(-431476834098926051132308263 : Int)/10^30)
theorem v3256_pb_checked : Scalar.distance (sourceCoefficient 42 86 1 1) v3256_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3256_pg : Scalar.QComplex := ((-93086286261063461097532 : Int)/10^30,(160912991733559201834 : Int)/10^30)
theorem v3256_pg_checked : Scalar.distance (sourceCoefficient 42 86 1 2) v3256_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3256_mb : Scalar.QComplex := ((-1118214366381891969585302 : Int)/10^30,(-431476029788535688070011695 : Int)/10^30)
theorem v3256_mb_checked : Scalar.distance (sourceCoefficient 42 86 3 1) v3256_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3256_mg : Scalar.QComplex := ((-93086112740120218712534 : Int)/10^30,(241242204410893946602 : Int)/10^30)
theorem v3256_mg_checked : Scalar.distance (sourceCoefficient 42 86 3 2) v3256_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3256_upper : Scalar.QComplex := ((999994033041908447992507616389 : Int)/10^30,(-3454544916268298956272683666 : Int)/10^30)
theorem v3256_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 86 5) 1) 14) v3256_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3256 : Material (42 : Basis) (86 : Basis) where
  plus := ![v3256_pa,v3256_pb,v3256_pg]
  minus := ![(Primitive.Addresses.material3256 1).one,v3256_mb,v3256_mg]
  upper := v3256_upper
  lower := (Primitive.Addresses.material3256 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3256_pa_checked.trans (by decide +kernel)
    · exact v3256_pb_checked.trans (by decide +kernel)
    · exact v3256_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 86 Primitive.Addresses.material3256
    · exact v3256_mb_checked.trans (by decide +kernel)
    · exact v3256_mg_checked.trans (by decide +kernel)
  upper_error := v3256_upper_checked
  lower_error := reuse_lower_error 42 86 Primitive.Addresses.material3256

def v3257_pa : Scalar.QComplex := ((999998504229483078164602683822 : Int)/10^30,(-1729606543845805268297454934 : Int)/10^30)
theorem v3257_pa_checked : Scalar.distance (sourceCoefficient 42 87 1 0) v3257_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3257_pb : Scalar.QComplex := ((-746286270617921516087100 : Int)/10^30,(-431476833271886716908788719 : Int)/10^30)
theorem v3257_pb_checked : Scalar.distance (sourceCoefficient 42 87 1 1) v3257_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3257_pg : Scalar.QComplex := ((-93086286094128148484267 : Int)/10^30,(161002890394083421351 : Int)/10^30)
theorem v3257_pg_checked : Scalar.distance (sourceCoefficient 42 87 1 2) v3257_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3257_mb : Scalar.QComplex := ((-1118631066859890358766369 : Int)/10^30,(-431476028601902166988837524 : Int)/10^30)
theorem v3257_mb_checked : Scalar.distance (sourceCoefficient 42 87 3 1) v3257_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3257_mg : Scalar.QComplex := ((-93086112495606473109883 : Int)/10^30,(241332102893887129937 : Int)/10^30)
theorem v3257_mg_checked : Scalar.distance (sourceCoefficient 42 87 3 2) v3257_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3257_upper : Scalar.QComplex := ((999994029705193106433087259875 : Int)/10^30,(-3455510666944475314823812527 : Int)/10^30)
theorem v3257_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 87 5) 1) 14) v3257_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3257 : Material (42 : Basis) (87 : Basis) where
  plus := ![v3257_pa,v3257_pb,v3257_pg]
  minus := ![(Primitive.Addresses.material3257 1).one,v3257_mb,v3257_mg]
  upper := v3257_upper
  lower := (Primitive.Addresses.material3257 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3257_pa_checked.trans (by decide +kernel)
    · exact v3257_pb_checked.trans (by decide +kernel)
    · exact v3257_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 87 Primitive.Addresses.material3257
    · exact v3257_mb_checked.trans (by decide +kernel)
    · exact v3257_mg_checked.trans (by decide +kernel)
  upper_error := v3257_upper_checked
  lower_error := reuse_lower_error 42 87 Primitive.Addresses.material3257

def v3258_pa : Scalar.QComplex := ((999998483820869195302075595655 : Int)/10^30,(-1741366119691731903289918987 : Int)/10^30)
theorem v3258_pa_checked : Scalar.distance (sourceCoefficient 42 88 1 0) v3258_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3258_pb : Scalar.QComplex := ((-751360260476909732562151 : Int)/10^30,(-431476823158345139125171657 : Int)/10^30)
theorem v3258_pb_checked : Scalar.distance (sourceCoefficient 42 88 1 1) v3258_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3258_pg : Scalar.QComplex := ((-93086284053304131329913 : Int)/10^30,(162097547027342514229 : Int)/10^30)
theorem v3258_pg_checked : Scalar.distance (sourceCoefficient 42 88 1 2) v3258_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3258_mb : Scalar.QComplex := ((-1123705046102069373324373 : Int)/10^30,(-431476014109739630652169185 : Int)/10^30)
theorem v3258_mb_checked : Scalar.distance (sourceCoefficient 42 88 3 1) v3258_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3258_mg : Scalar.QComplex := ((-93086109510143842849588 : Int)/10^30,(242426757358416318470 : Int)/10^30)
theorem v3258_mg_checked : Scalar.distance (sourceCoefficient 42 88 3 2) v3258_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3258_upper : Scalar.QComplex := ((999993989000648530121401437109 : Int)/10^30,(-3467270190052478997291803922 : Int)/10^30)
theorem v3258_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 88 5) 1) 14) v3258_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3258 : Material (42 : Basis) (88 : Basis) where
  plus := ![v3258_pa,v3258_pb,v3258_pg]
  minus := ![(Primitive.Addresses.material3258 1).one,v3258_mb,v3258_mg]
  upper := v3258_upper
  lower := (Primitive.Addresses.material3258 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3258_pa_checked.trans (by decide +kernel)
    · exact v3258_pb_checked.trans (by decide +kernel)
    · exact v3258_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 88 Primitive.Addresses.material3258
    · exact v3258_mb_checked.trans (by decide +kernel)
    · exact v3258_mg_checked.trans (by decide +kernel)
  upper_error := v3258_upper_checked
  lower_error := reuse_lower_error 42 88 Primitive.Addresses.material3258

def v3259_pa : Scalar.QComplex := ((999998455673750397278132373136 : Int)/10^30,(-1757455579598494012316407144 : Int)/10^30)
theorem v3259_pa_checked : Scalar.distance (sourceCoefficient 42 89 1 0) v3259_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3259_pb : Scalar.QComplex := ((-758302496848462362134151 : Int)/10^30,(-431476809192100241990578112 : Int)/10^30)
theorem v3259_pb_checked : Scalar.distance (sourceCoefficient 42 89 1 1) v3259_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3259_pg : Scalar.QComplex := ((-93086281236716477109384 : Int)/10^30,(163595256987991651345 : Int)/10^30)
theorem v3259_pg_checked : Scalar.distance (sourceCoefficient 42 89 1 2) v3259_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3259_mb : Scalar.QComplex := ((-1130647267836469795984232 : Int)/10^30,(-431475994152662611858360972 : Int)/10^30)
theorem v3259_mb_checked : Scalar.distance (sourceCoefficient 42 89 3 1) v3259_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3259_mg : Scalar.QComplex := ((-93086105401100995685766 : Int)/10^30,(243924464330811297316 : Int)/10^30)
theorem v3259_mg_checked : Scalar.distance (sourceCoefficient 42 89 3 2) v3259_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3259_upper : Scalar.QComplex := ((999993933084623479253896216944 : Int)/10^30,(-3483359577416507017203376247 : Int)/10^30)
theorem v3259_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 89 5) 1) 14) v3259_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3259 : Material (42 : Basis) (89 : Basis) where
  plus := ![v3259_pa,v3259_pb,v3259_pg]
  minus := ![(Primitive.Addresses.material3259 1).one,v3259_mb,v3259_mg]
  upper := v3259_upper
  lower := (Primitive.Addresses.material3259 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3259_pa_checked.trans (by decide +kernel)
    · exact v3259_pb_checked.trans (by decide +kernel)
    · exact v3259_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 89 Primitive.Addresses.material3259
    · exact v3259_mb_checked.trans (by decide +kernel)
    · exact v3259_mg_checked.trans (by decide +kernel)
  upper_error := v3259_upper_checked
  lower_error := reuse_lower_error 42 89 Primitive.Addresses.material3259

def v3260_pa : Scalar.QComplex := ((999998409279947796344301217972 : Int)/10^30,(-1783658480207751798629012957 : Int)/10^30)
theorem v3260_pa_checked : Scalar.distance (sourceCoefficient 42 90 1 0) v3260_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3260_pb : Scalar.QComplex := ((-769608452822027075872713 : Int)/10^30,(-431476786128243983152144697 : Int)/10^30)
theorem v3260_pb_checked : Scalar.distance (sourceCoefficient 42 90 1 1) v3260_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3260_pg : Scalar.QComplex := ((-93086276589515749664596 : Int)/10^30,(166034390744088799411 : Int)/10^30)
theorem v3260_pg_checked : Scalar.distance (sourceCoefficient 42 90 1 2) v3260_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3260_mb : Scalar.QComplex := ((-1141953199697241199198619 : Int)/10^30,(-431475961332284136915941624 : Int)/10^30)
theorem v3260_mb_checked : Scalar.distance (sourceCoefficient 42 90 3 1) v3260_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3260_mg : Scalar.QComplex := ((-93086098649039421600741 : Int)/10^30,(246363593168382548434 : Int)/10^30)
theorem v3260_mg_checked : Scalar.distance (sourceCoefficient 42 90 3 2) v3260_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3260_upper : Scalar.QComplex := ((999993841467060633434619814239 : Int)/10^30,(-3509562358928127878633128873 : Int)/10^30)
theorem v3260_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 90 5) 1) 14) v3260_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3260 : Material (42 : Basis) (90 : Basis) where
  plus := ![v3260_pa,v3260_pb,v3260_pg]
  minus := ![(Primitive.Addresses.material3260 1).one,v3260_mb,v3260_mg]
  upper := v3260_upper
  lower := (Primitive.Addresses.material3260 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3260_pa_checked.trans (by decide +kernel)
    · exact v3260_pb_checked.trans (by decide +kernel)
    · exact v3260_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 90 Primitive.Addresses.material3260
    · exact v3260_mb_checked.trans (by decide +kernel)
    · exact v3260_mg_checked.trans (by decide +kernel)
  upper_error := v3260_upper_checked
  lower_error := reuse_lower_error 42 90 Primitive.Addresses.material3260

def v3261_pa : Scalar.QComplex := ((999998382842293917778966930141 : Int)/10^30,(-1798419527520037724145020411 : Int)/10^30)
theorem v3261_pa_checked : Scalar.distance (sourceCoefficient 42 91 1 0) v3261_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3261_pb : Scalar.QComplex := ((-775977509043478679780153 : Int)/10^30,(-431476772961599401383644496 : Int)/10^30)
theorem v3261_pb_checked : Scalar.distance (sourceCoefficient 42 91 1 1) v3261_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3261_pg : Scalar.QComplex := ((-93086273938744482768587 : Int)/10^30,(167408443521372157540 : Int)/10^30)
theorem v3261_pg_checked : Scalar.distance (sourceCoefficient 42 91 1 2) v3261_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3261_mb : Scalar.QComplex := ((-1148322242184980821203067 : Int)/10^30,(-431475942669435790222011057 : Int)/10^30)
theorem v3261_mb_checked : Scalar.distance (sourceCoefficient 42 91 3 1) v3261_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3261_mg : Scalar.QComplex := ((-93086094812523479952291 : Int)/10^30,(247737643146547043241 : Int)/10^30)
theorem v3261_mg_checked : Scalar.distance (sourceCoefficient 42 91 3 2) v3261_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3261_upper : Scalar.QComplex := ((999993789553217581395248863542 : Int)/10^30,(-3524323338626575597740989112 : Int)/10^30)
theorem v3261_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 91 5) 1) 14) v3261_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3261 : Material (42 : Basis) (91 : Basis) where
  plus := ![v3261_pa,v3261_pb,v3261_pg]
  minus := ![(Primitive.Addresses.material3261 1).one,v3261_mb,v3261_mg]
  upper := v3261_upper
  lower := (Primitive.Addresses.material3261 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3261_pa_checked.trans (by decide +kernel)
    · exact v3261_pb_checked.trans (by decide +kernel)
    · exact v3261_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 91 Primitive.Addresses.material3261
    · exact v3261_mb_checked.trans (by decide +kernel)
    · exact v3261_mg_checked.trans (by decide +kernel)
  upper_error := v3261_upper_checked
  lower_error := reuse_lower_error 42 91 Primitive.Addresses.material3261

def v3262_pa : Scalar.QComplex := ((999998324861215835580859767665 : Int)/10^30,(-1830375579557073327109202731 : Int)/10^30)
theorem v3262_pa_checked : Scalar.distance (sourceCoefficient 42 92 1 0) v3262_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3262_pb : Scalar.QComplex := ((-789765818382672389181636 : Int)/10^30,(-431476744027819780941539292 : Int)/10^30)
theorem v3262_pb_checked : Scalar.distance (sourceCoefficient 42 92 1 1) v3262_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3262_pg : Scalar.QComplex := ((-93086268119049675132370 : Int)/10^30,(170383117372578744785 : Int)/10^30)
theorem v3262_pg_checked : Scalar.distance (sourceCoefficient 42 92 1 2) v3262_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3262_mb : Scalar.QComplex := ((-1162110521421608123373694 : Int)/10^30,(-431475901836976985824170981 : Int)/10^30)
theorem v3262_mb_checked : Scalar.distance (sourceCoefficient 42 92 3 1) v3262_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3262_mg : Scalar.QComplex := ((-93086086425821280000036 : Int)/10^30,(250712310868012096705 : Int)/10^30)
theorem v3262_mg_checked : Scalar.distance (sourceCoefficient 42 92 3 2) v3262_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3262_upper : Scalar.QComplex := ((999993676418979069673375745967 : Int)/10^30,(-3556279242998744745545294607 : Int)/10^30)
theorem v3262_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 92 5) 1) 14) v3262_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3262 : Material (42 : Basis) (92 : Basis) where
  plus := ![v3262_pa,v3262_pb,v3262_pg]
  minus := ![(Primitive.Addresses.material3262 1).one,v3262_mb,v3262_mg]
  upper := v3262_upper
  lower := (Primitive.Addresses.material3262 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3262_pa_checked.trans (by decide +kernel)
    · exact v3262_pb_checked.trans (by decide +kernel)
    · exact v3262_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 92 Primitive.Addresses.material3262
    · exact v3262_mb_checked.trans (by decide +kernel)
    · exact v3262_mg_checked.trans (by decide +kernel)
  upper_error := v3262_upper_checked
  lower_error := reuse_lower_error 42 92 Primitive.Addresses.material3262

def v3263_pa : Scalar.QComplex := ((999998254723927550184921298244 : Int)/10^30,(-1868301126400950680417932594 : Int)/10^30)
theorem v3263_pa_checked : Scalar.distance (sourceCoefficient 42 93 1 0) v3263_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3263_pb : Scalar.QComplex := ((-806129828222723183280851 : Int)/10^30,(-431476708926750289853312194 : Int)/10^30)
theorem v3263_pb_checked : Scalar.distance (sourceCoefficient 42 93 1 1) v3263_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3263_pg : Scalar.QComplex := ((-93086261068303993375352 : Int)/10^30,(173913469933383064900 : Int)/10^30)
theorem v3263_pg_checked : Scalar.distance (sourceCoefficient 42 93 1 2) v3263_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3263_mb : Scalar.QComplex := ((-1178474494877948104501885 : Int)/10^30,(-431475852614517080148664347 : Int)/10^30)
theorem v3263_mb_checked : Scalar.distance (sourceCoefficient 42 93 3 1) v3263_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3263_mg : Scalar.QComplex := ((-93086076328542964760679 : Int)/10^30,(254242656029828843791 : Int)/10^30)
theorem v3263_mg_checked : Scalar.distance (sourceCoefficient 42 93 3 2) v3263_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3263_upper : Scalar.QComplex := ((999993540825741971730472347541 : Int)/10^30,(-3594204612306378347077375083 : Int)/10^30)
theorem v3263_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 93 5) 1) 14) v3263_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3263 : Material (42 : Basis) (93 : Basis) where
  plus := ![v3263_pa,v3263_pb,v3263_pg]
  minus := ![(Primitive.Addresses.material3263 1).one,v3263_mb,v3263_mg]
  upper := v3263_upper
  lower := (Primitive.Addresses.material3263 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3263_pa_checked.trans (by decide +kernel)
    · exact v3263_pb_checked.trans (by decide +kernel)
    · exact v3263_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 93 Primitive.Addresses.material3263
    · exact v3263_mb_checked.trans (by decide +kernel)
    · exact v3263_mg_checked.trans (by decide +kernel)
  upper_error := v3263_upper_checked
  lower_error := reuse_lower_error 42 93 Primitive.Addresses.material3263

def v3264_pa : Scalar.QComplex := ((999998170023278520295083489806 : Int)/10^30,(-1913099603822186952734131784 : Int)/10^30)
theorem v3264_pa_checked : Scalar.distance (sourceCoefficient 42 94 1 0) v3264_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3264_pb : Scalar.QComplex := ((-825459350117058229729060 : Int)/10^30,(-431476666398591324272428346 : Int)/10^30)
theorem v3264_pb_checked : Scalar.distance (sourceCoefficient 42 94 1 1) v3264_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3264_pg : Scalar.QComplex := ((-93086252538577102444502 : Int)/10^30,(178083598741684073802 : Int)/10^30)
theorem v3264_pg_checked : Scalar.distance (sourceCoefficient 42 94 1 2) v3264_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3264_mb : Scalar.QComplex := ((-1197803972875132956778224 : Int)/10^30,(-431475793405867124282918718 : Int)/10^30)
theorem v3264_mb_checked : Scalar.distance (sourceCoefficient 42 94 3 1) v3264_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3264_mg : Scalar.QComplex := ((-93086064200185903902691 : Int)/10^30,(258412775924630170826 : Int)/10^30)
theorem v3264_mg_checked : Scalar.distance (sourceCoefficient 42 94 3 2) v3264_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3264_upper : Scalar.QComplex := ((999993378807111150578677350067 : Int)/10^30,(-3639002876819908656549551773 : Int)/10^30)
theorem v3264_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 94 5) 1) 14) v3264_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3264 : Material (42 : Basis) (94 : Basis) where
  plus := ![v3264_pa,v3264_pb,v3264_pg]
  minus := ![(Primitive.Addresses.material3264 1).one,v3264_mb,v3264_mg]
  upper := v3264_upper
  lower := (Primitive.Addresses.material3264 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3264_pa_checked.trans (by decide +kernel)
    · exact v3264_pb_checked.trans (by decide +kernel)
    · exact v3264_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 94 Primitive.Addresses.material3264
    · exact v3264_mb_checked.trans (by decide +kernel)
    · exact v3264_mg_checked.trans (by decide +kernel)
  upper_error := v3264_upper_checked
  lower_error := reuse_lower_error 42 94 Primitive.Addresses.material3264

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
