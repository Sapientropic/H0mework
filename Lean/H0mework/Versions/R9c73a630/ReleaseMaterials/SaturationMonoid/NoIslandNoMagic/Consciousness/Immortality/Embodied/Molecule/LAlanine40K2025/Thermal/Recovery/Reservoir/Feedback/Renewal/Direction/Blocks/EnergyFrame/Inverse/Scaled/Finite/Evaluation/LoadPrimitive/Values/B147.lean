import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B098

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2353_pa : Scalar.QComplex := ((999999706734329023444963963395 : Int)/10^30,(-765853286177160892088141686 : Int)/10^30)
theorem v2353_pa_checked : Scalar.distance (sourceCoefficient 28 44 1 0) v2353_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2353_pb : Scalar.QComplex := ((-330448474220521524032315 : Int)/10^30,(-431477390350829008758480528 : Int)/10^30)
theorem v2353_pb_checked : Scalar.distance (sourceCoefficient 28 44 1 1) v2353_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2353_pg : Scalar.QComplex := ((-93086402154332728222193 : Int)/10^30,(71290547895374831917 : Int)/10^30)
theorem v2353_pg_checked : Scalar.distance (sourceCoefficient 28 44 1 2) v2353_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2353_mb : Scalar.QComplex := ((-702793906031943985297965 : Int)/10^30,(-431476944529926684734766717 : Int)/10^30)
theorem v2353_mb_checked : Scalar.distance (sourceCoefficient 28 44 3 1) v2353_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2353_mg : Scalar.QComplex := ((-93086305973478920798986 : Int)/10^30,(151619893953913104112 : Int)/10^30)
theorem v2353_mg_checked : Scalar.distance (sourceCoefficient 28 44 3 2) v2353_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2353_upper : Scalar.QComplex := ((999996895558939785519638514681 : Int)/10^30,(-2491760920087371539914054540 : Int)/10^30)
theorem v2353_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 44 5) 1) 14) v2353_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2353 : Material (28 : Basis) (44 : Basis) where
  plus := ![v2353_pa,v2353_pb,v2353_pg]
  minus := ![(Primitive.Addresses.material2353 1).one,v2353_mb,v2353_mg]
  upper := v2353_upper
  lower := (Primitive.Addresses.material2353 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2353_pa_checked.trans (by decide +kernel)
    · exact v2353_pb_checked.trans (by decide +kernel)
    · exact v2353_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 44 Primitive.Addresses.material2353
    · exact v2353_mb_checked.trans (by decide +kernel)
    · exact v2353_mg_checked.trans (by decide +kernel)
  upper_error := v2353_upper_checked
  lower_error := reuse_lower_error 28 44 Primitive.Addresses.material2353

def v2354_pa : Scalar.QComplex := ((999999704498906966405235414281 : Int)/10^30,(-768766608761263476042320405 : Int)/10^30)
theorem v2354_pa_checked : Scalar.distance (sourceCoefficient 28 45 1 0) v2354_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2354_pb : Scalar.QComplex := ((-331705507337506034104129 : Int)/10^30,(-431477389285485294396233689 : Int)/10^30)
theorem v2354_pb_checked : Scalar.distance (sourceCoefficient 28 45 1 1) v2354_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2354_pg : Scalar.QComplex := ((-93086401935371027430730 : Int)/10^30,(71561738684215098459 : Int)/10^30)
theorem v2354_pg_checked : Scalar.distance (sourceCoefficient 28 45 1 2) v2354_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2354_mb : Scalar.QComplex := ((-704050937761533972470076 : Int)/10^30,(-431476942379820401760994801 : Int)/10^30)
theorem v2354_mb_checked : Scalar.distance (sourceCoefficient 28 45 3 1) v2354_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2354_mg : Scalar.QComplex := ((-93086305520491864747546 : Int)/10^30,(151891084452822559823 : Int)/10^30)
theorem v2354_mg_checked : Scalar.distance (sourceCoefficient 28 45 3 2) v2354_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2354_upper : Scalar.QComplex := ((999996888295390572277686881547 : Int)/10^30,(-2494674234474286683212299943 : Int)/10^30)
theorem v2354_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 45 5) 1) 14) v2354_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2354 : Material (28 : Basis) (45 : Basis) where
  plus := ![v2354_pa,v2354_pb,v2354_pg]
  minus := ![(Primitive.Addresses.material2354 1).one,v2354_mb,v2354_mg]
  upper := v2354_upper
  lower := (Primitive.Addresses.material2354 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2354_pa_checked.trans (by decide +kernel)
    · exact v2354_pb_checked.trans (by decide +kernel)
    · exact v2354_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 45 Primitive.Addresses.material2354
    · exact v2354_mb_checked.trans (by decide +kernel)
    · exact v2354_mg_checked.trans (by decide +kernel)
  upper_error := v2354_upper_checked
  lower_error := reuse_lower_error 28 45 Primitive.Addresses.material2354

def v2355_pa : Scalar.QComplex := ((999999691784729000132391498300 : Int)/10^30,(-785130847058681002555313378 : Int)/10^30)
theorem v2355_pa_checked : Scalar.distance (sourceCoefficient 28 46 1 0) v2355_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2355_pb : Scalar.QComplex := ((-338766307779804009376087 : Int)/10^30,(-431477383210667719405617261 : Int)/10^30)
theorem v2355_pb_checked : Scalar.distance (sourceCoefficient 28 46 1 1) v2355_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2355_pg : Scalar.QComplex := ((-93086400688325472465597 : Int)/10^30,(73085027147990212976 : Int)/10^30)
theorem v2355_pg_checked : Scalar.distance (sourceCoefficient 28 46 1 2) v2355_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2355_mb : Scalar.QComplex := ((-711111730332479280963031 : Int)/10^30,(-431476930211852313646401229 : Int)/10^30)
theorem v2355_mb_checked : Scalar.distance (sourceCoefficient 28 46 3 1) v2355_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2355_mg : Scalar.QComplex := ((-93086302958917436242163 : Int)/10^30,(153414371273263612467 : Int)/10^30)
theorem v2355_mg_checked : Scalar.distance (sourceCoefficient 28 46 3 2) v2355_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2355_upper : Scalar.QComplex := ((999996847338040793038417817364 : Int)/10^30,(-2511038426455575795613138585 : Int)/10^30)
theorem v2355_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 46 5) 1) 14) v2355_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2355 : Material (28 : Basis) (46 : Basis) where
  plus := ![v2355_pa,v2355_pb,v2355_pg]
  minus := ![(Primitive.Addresses.material2355 1).one,v2355_mb,v2355_mg]
  upper := v2355_upper
  lower := (Primitive.Addresses.material2355 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2355_pa_checked.trans (by decide +kernel)
    · exact v2355_pb_checked.trans (by decide +kernel)
    · exact v2355_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 46 Primitive.Addresses.material2355
    · exact v2355_mb_checked.trans (by decide +kernel)
    · exact v2355_mg_checked.trans (by decide +kernel)
  upper_error := v2355_upper_checked
  lower_error := reuse_lower_error 28 46 Primitive.Addresses.material2355

def v2356_pa : Scalar.QComplex := ((999999688685096108797973931288 : Int)/10^30,(-789068888542334222062841335 : Int)/10^30)
theorem v2356_pa_checked : Scalar.distance (sourceCoefficient 28 47 1 0) v2356_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2356_pb : Scalar.QComplex := ((-340465484021488750189448 : Int)/10^30,(-431477381725769377454077885 : Int)/10^30)
theorem v2356_pb_checked : Scalar.distance (sourceCoefficient 28 47 1 1) v2356_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2356_pg : Scalar.QComplex := ((-93086400383883521319077 : Int)/10^30,(73451605355897145851 : Int)/10^30)
theorem v2356_pg_checked : Scalar.distance (sourceCoefficient 28 47 1 2) v2356_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2356_mb : Scalar.QComplex := ((-712810904660082659041164 : Int)/10^30,(-431476927260641956073516913 : Int)/10^30)
theorem v2356_mb_checked : Scalar.distance (sourceCoefficient 28 47 3 1) v2356_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2356_mg : Scalar.QComplex := ((-93086302338135115099213 : Int)/10^30,(153780949081957032804 : Int)/10^30)
theorem v2356_mg_checked : Scalar.distance (sourceCoefficient 28 47 3 2) v2356_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2356_upper : Scalar.QComplex := ((999996837441710173790290266594 : Int)/10^30,(-2514976456724293646123492354 : Int)/10^30)
theorem v2356_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 47 5) 1) 14) v2356_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2356 : Material (28 : Basis) (47 : Basis) where
  plus := ![v2356_pa,v2356_pb,v2356_pg]
  minus := ![(Primitive.Addresses.material2356 1).one,v2356_mb,v2356_mg]
  upper := v2356_upper
  lower := (Primitive.Addresses.material2356 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2356_pa_checked.trans (by decide +kernel)
    · exact v2356_pb_checked.trans (by decide +kernel)
    · exact v2356_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 47 Primitive.Addresses.material2356
    · exact v2356_mb_checked.trans (by decide +kernel)
    · exact v2356_mg_checked.trans (by decide +kernel)
  upper_error := v2356_upper_checked
  lower_error := reuse_lower_error 28 47 Primitive.Addresses.material2356

def v2357_pa : Scalar.QComplex := ((999999666664270538785804461425 : Int)/10^30,(-816499447525667255204547989 : Int)/10^30)
theorem v2357_pa_checked : Scalar.distance (sourceCoefficient 28 48 1 0) v2357_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2357_pb : Scalar.QComplex := ((-352301152586237422647836 : Int)/10^30,(-431477371135148129402676394 : Int)/10^30)
theorem v2357_pb_checked : Scalar.distance (sourceCoefficient 28 48 1 1) v2357_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2357_pg : Scalar.QComplex := ((-93086398216559700602606 : Int)/10^30,(76005018051163388029 : Int)/10^30)
theorem v2357_pg_checked : Scalar.distance (sourceCoefficient 28 48 1 2) v2357_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2357_mb : Scalar.QComplex := ((-724646559678641854874561 : Int)/10^30,(-431476906456375738740403338 : Int)/10^30)
theorem v2357_mb_checked : Scalar.distance (sourceCoefficient 28 48 3 1) v2357_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2357_mg : Scalar.QComplex := ((-93086297967331946800425 : Int)/10^30,(156334358956168187172 : Int)/10^30)
theorem v2357_mg_checked : Scalar.distance (sourceCoefficient 28 48 3 2) v2357_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2357_upper : Scalar.QComplex := ((999996768078261076850266425291 : Int)/10^30,(-2542406936847084073246848521 : Int)/10^30)
theorem v2357_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 48 5) 1) 14) v2357_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2357 : Material (28 : Basis) (48 : Basis) where
  plus := ![v2357_pa,v2357_pb,v2357_pg]
  minus := ![(Primitive.Addresses.material2357 1).one,v2357_mb,v2357_mg]
  upper := v2357_upper
  lower := (Primitive.Addresses.material2357 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2357_pa_checked.trans (by decide +kernel)
    · exact v2357_pb_checked.trans (by decide +kernel)
    · exact v2357_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 48 Primitive.Addresses.material2357
    · exact v2357_mb_checked.trans (by decide +kernel)
    · exact v2357_mg_checked.trans (by decide +kernel)
  upper_error := v2357_upper_checked
  lower_error := reuse_lower_error 28 48 Primitive.Addresses.material2357

def v2358_pa : Scalar.QComplex := ((999999648427097021190829236422 : Int)/10^30,(-838537824044993352964102633 : Int)/10^30)
theorem v2358_pa_checked : Scalar.distance (sourceCoefficient 28 49 1 0) v2358_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2358_pb : Scalar.QComplex := ((-361810215721102716793298 : Int)/10^30,(-431477362312783680796105458 : Int)/10^30)
theorem v2358_pb_checked : Scalar.distance (sourceCoefficient 28 49 1 1) v2358_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2358_pg : Scalar.QComplex := ((-93086396416079984461351 : Int)/10^30,(78056491741476775763 : Int)/10^30)
theorem v2358_pg_checked : Scalar.distance (sourceCoefficient 28 49 1 2) v2358_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2358_mb : Scalar.QComplex := ((-734155611659545183652615 : Int)/10^30,(-431476889428121362019948800 : Int)/10^30)
theorem v2358_mb_checked : Scalar.distance (sourceCoefficient 28 49 3 1) v2358_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2358_mg : Scalar.QComplex := ((-93086294396523501264752 : Int)/10^30,(158385830328891258589 : Int)/10^30)
theorem v2358_mg_checked : Scalar.distance (sourceCoefficient 28 49 3 2) v2358_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2358_upper : Scalar.QComplex := ((999996711804876154926224683339 : Int)/10^30,(-2564445249067130127118723288 : Int)/10^30)
theorem v2358_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 49 5) 1) 14) v2358_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2358 : Material (28 : Basis) (49 : Basis) where
  plus := ![v2358_pa,v2358_pb,v2358_pg]
  minus := ![(Primitive.Addresses.material2358 1).one,v2358_mb,v2358_mg]
  upper := v2358_upper
  lower := (Primitive.Addresses.material2358 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2358_pa_checked.trans (by decide +kernel)
    · exact v2358_pb_checked.trans (by decide +kernel)
    · exact v2358_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 49 Primitive.Addresses.material2358
    · exact v2358_mb_checked.trans (by decide +kernel)
    · exact v2358_mg_checked.trans (by decide +kernel)
  upper_error := v2358_upper_checked
  lower_error := reuse_lower_error 28 49 Primitive.Addresses.material2358

def v2359_pa : Scalar.QComplex := ((999999646264310375895603553066 : Int)/10^30,(-841113104237040572249223874 : Int)/10^30)
theorem v2359_pa_checked : Scalar.distance (sourceCoefficient 28 50 1 0) v2359_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2359_pb : Scalar.QComplex := ((-362921391118697807505330 : Int)/10^30,(-431477361263618596729092061 : Int)/10^30)
theorem v2359_pb_checked : Scalar.distance (sourceCoefficient 28 50 1 1) v2359_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2359_pg : Scalar.QComplex := ((-93086396202244148151380 : Int)/10^30,(78296215368074378025 : Int)/10^30)
theorem v2359_pg_checked : Scalar.distance (sourceCoefficient 28 50 1 2) v2359_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2359_mb : Scalar.QComplex := ((-735266785738016675707035 : Int)/10^30,(-431476887420062345962614190 : Int)/10^30)
theorem v2359_mb_checked : Scalar.distance (sourceCoefficient 28 50 3 1) v2359_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2359_mg : Scalar.QComplex := ((-93086293975817051573252 : Int)/10^30,(158625553681698102831 : Int)/10^30)
theorem v2359_mg_checked : Scalar.distance (sourceCoefficient 28 50 3 2) v2359_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2359_upper : Scalar.QComplex := ((999996705197392746968171827297 : Int)/10^30,(-2567020521690826470703515788 : Int)/10^30)
theorem v2359_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 50 5) 1) 14) v2359_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2359 : Material (28 : Basis) (50 : Basis) where
  plus := ![v2359_pa,v2359_pb,v2359_pg]
  minus := ![(Primitive.Addresses.material2359 1).one,v2359_mb,v2359_mg]
  upper := v2359_upper
  lower := (Primitive.Addresses.material2359 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2359_pa_checked.trans (by decide +kernel)
    · exact v2359_pb_checked.trans (by decide +kernel)
    · exact v2359_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 50 Primitive.Addresses.material2359
    · exact v2359_mb_checked.trans (by decide +kernel)
    · exact v2359_mg_checked.trans (by decide +kernel)
  upper_error := v2359_upper_checked
  lower_error := reuse_lower_error 28 50 Primitive.Addresses.material2359

def v2360_pa : Scalar.QComplex := ((999999636696526194569836303645 : Int)/10^30,(-852412350697387683210760550 : Int)/10^30)
theorem v2360_pa_checked : Scalar.distance (sourceCoefficient 28 51 1 0) v2360_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2360_pb : Scalar.QComplex := ((-367796761446922415317732 : Int)/10^30,(-431477356615227751188624526 : Int)/10^30)
theorem v2360_pb_checked : Scalar.distance (sourceCoefficient 28 51 1 1) v2360_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2360_pg : Scalar.QComplex := ((-93086395255509649743193 : Int)/10^30,(79348021825107105161 : Int)/10^30)
theorem v2360_pg_checked : Scalar.distance (sourceCoefficient 28 51 1 2) v2360_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2360_mb : Scalar.QComplex := ((-740142150239566150940720 : Int)/10^30,(-431476878564448216501108977 : Int)/10^30)
theorem v2360_mb_checked : Scalar.distance (sourceCoefficient 28 51 3 1) v2360_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2360_mg : Scalar.QComplex := ((-93086292121421304862651 : Int)/10^30,(159677358930105983297 : Int)/10^30)
theorem v2360_mg_checked : Scalar.distance (sourceCoefficient 28 51 3 2) v2360_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2360_upper : Scalar.QComplex := ((999996676128148484805474540003 : Int)/10^30,(-2578319734809145767337541924 : Int)/10^30)
theorem v2360_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 51 5) 1) 14) v2360_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2360 : Material (28 : Basis) (51 : Basis) where
  plus := ![v2360_pa,v2360_pb,v2360_pg]
  minus := ![(Primitive.Addresses.material2360 1).one,v2360_mb,v2360_mg]
  upper := v2360_upper
  lower := (Primitive.Addresses.material2360 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2360_pa_checked.trans (by decide +kernel)
    · exact v2360_pb_checked.trans (by decide +kernel)
    · exact v2360_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 51 Primitive.Addresses.material2360
    · exact v2360_mb_checked.trans (by decide +kernel)
    · exact v2360_mg_checked.trans (by decide +kernel)
  upper_error := v2360_upper_checked
  lower_error := reuse_lower_error 28 51 Primitive.Addresses.material2360

def v2361_pa : Scalar.QComplex := ((999999615785029601944185155091 : Int)/10^30,(-876601273769875463161803697 : Int)/10^30)
theorem v2361_pa_checked : Scalar.distance (sourceCoefficient 28 52 1 0) v2361_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2361_pb : Scalar.QComplex := ((-378233736795256712256600 : Int)/10^30,(-431477346417233532815339619 : Int)/10^30)
theorem v2361_pb_checked : Scalar.distance (sourceCoefficient 28 52 1 1) v2361_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2361_pg : Scalar.QComplex := ((-93086393182170002304697 : Int)/10^30,(81599682185953150555 : Int)/10^30)
theorem v2361_pg_checked : Scalar.distance (sourceCoefficient 28 52 1 2) v2361_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2361_mb : Scalar.QComplex := ((-750579112901327822510771 : Int)/10^30,(-431476859359818133614740710 : Int)/10^30)
theorem v2361_mb_checked : Scalar.distance (sourceCoefficient 28 52 3 1) v2361_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2361_mg : Scalar.QComplex := ((-93086288105000949031224 : Int)/10^30,(161929016663357234397 : Int)/10^30)
theorem v2361_mg_checked : Scalar.distance (sourceCoefficient 28 52 3 2) v2361_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2361_upper : Scalar.QComplex := ((999996613468796216243061661721 : Int)/10^30,(-2602508585763728018601601144 : Int)/10^30)
theorem v2361_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 52 5) 1) 14) v2361_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2361 : Material (28 : Basis) (52 : Basis) where
  plus := ![v2361_pa,v2361_pb,v2361_pg]
  minus := ![(Primitive.Addresses.material2361 1).one,v2361_mb,v2361_mg]
  upper := v2361_upper
  lower := (Primitive.Addresses.material2361 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2361_pa_checked.trans (by decide +kernel)
    · exact v2361_pb_checked.trans (by decide +kernel)
    · exact v2361_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 52 Primitive.Addresses.material2361
    · exact v2361_mb_checked.trans (by decide +kernel)
    · exact v2361_mg_checked.trans (by decide +kernel)
  upper_error := v2361_upper_checked
  lower_error := reuse_lower_error 28 52 Primitive.Addresses.material2361

def v2362_pa : Scalar.QComplex := ((999999612532391985195875112418 : Int)/10^30,(-880303962218994552823166656 : Int)/10^30)
theorem v2362_pa_checked : Scalar.distance (sourceCoefficient 28 53 1 0) v2362_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2362_pb : Scalar.QComplex := ((-379831363430833039222789 : Int)/10^30,(-431477344826481666445759347 : Int)/10^30)
theorem v2362_pb_checked : Scalar.distance (sourceCoefficient 28 53 1 1) v2362_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2362_pg : Scalar.QComplex := ((-93086392859188364720014 : Int)/10^30,(81944352213399580994 : Int)/10^30)
theorem v2362_pg_checked : Scalar.distance (sourceCoefficient 28 53 1 2) v2362_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2362_mb : Scalar.QComplex := ((-752176737569287522035160 : Int)/10^30,(-431476856390387027485003333 : Int)/10^30)
theorem v2362_mb_checked : Scalar.distance (sourceCoefficient 28 53 3 1) v2362_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2362_mg : Scalar.QComplex := ((-93086287484584721382878 : Int)/10^30,(162273686283748654737 : Int)/10^30)
theorem v2362_mg_checked : Scalar.distance (sourceCoefficient 28 53 3 2) v2362_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2362_upper : Scalar.QComplex := ((999996603825659086009007451682 : Int)/10^30,(-2606211263084370162110761347 : Int)/10^30)
theorem v2362_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 53 5) 1) 14) v2362_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2362 : Material (28 : Basis) (53 : Basis) where
  plus := ![v2362_pa,v2362_pb,v2362_pg]
  minus := ![(Primitive.Addresses.material2362 1).one,v2362_mb,v2362_mg]
  upper := v2362_upper
  lower := (Primitive.Addresses.material2362 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2362_pa_checked.trans (by decide +kernel)
    · exact v2362_pb_checked.trans (by decide +kernel)
    · exact v2362_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 53 Primitive.Addresses.material2362
    · exact v2362_mb_checked.trans (by decide +kernel)
    · exact v2362_mg_checked.trans (by decide +kernel)
  upper_error := v2362_upper_checked
  lower_error := reuse_lower_error 28 53 Primitive.Addresses.material2362

def v2363_pa : Scalar.QComplex := ((999999610873474337987007805912 : Int)/10^30,(-882186431489723724485109231 : Int)/10^30)
theorem v2363_pa_checked : Scalar.distance (sourceCoefficient 28 54 1 0) v2363_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2363_pb : Scalar.QComplex := ((-380643606503524526858458 : Int)/10^30,(-431477344014709426812437295 : Int)/10^30)
theorem v2363_pb_checked : Scalar.distance (sourceCoefficient 28 54 1 1) v2363_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2363_pg : Scalar.QComplex := ((-93086392694411631668027 : Int)/10^30,(82119584546242709203 : Int)/10^30)
theorem v2363_pg_checked : Scalar.distance (sourceCoefficient 28 54 1 2) v2363_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2363_mb : Scalar.QComplex := ((-752988979639020910426448 : Int)/10^30,(-431476854877685900448835844 : Int)/10^30)
theorem v2363_mb_checked : Scalar.distance (sourceCoefficient 28 54 3 1) v2363_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2363_mg : Scalar.QComplex := ((-93086287168590438612479 : Int)/10^30,(162448918409149877559 : Int)/10^30)
theorem v2363_mg_checked : Scalar.distance (sourceCoefficient 28 54 3 2) v2363_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2363_upper : Scalar.QComplex := ((999996598917772724562764693108 : Int)/10^30,(-2608093726688241122146545020 : Int)/10^30)
theorem v2363_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 54 5) 1) 14) v2363_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2363 : Material (28 : Basis) (54 : Basis) where
  plus := ![v2363_pa,v2363_pb,v2363_pg]
  minus := ![(Primitive.Addresses.material2363 1).one,v2363_mb,v2363_mg]
  upper := v2363_upper
  lower := (Primitive.Addresses.material2363 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2363_pa_checked.trans (by decide +kernel)
    · exact v2363_pb_checked.trans (by decide +kernel)
    · exact v2363_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 54 Primitive.Addresses.material2363
    · exact v2363_mb_checked.trans (by decide +kernel)
    · exact v2363_mg_checked.trans (by decide +kernel)
  upper_error := v2363_upper_checked
  lower_error := reuse_lower_error 28 54 Primitive.Addresses.material2363

def v2364_pa : Scalar.QComplex := ((999999597219849186635220611040 : Int)/10^30,(-897530021444898337469153260 : Int)/10^30)
theorem v2364_pa_checked : Scalar.distance (sourceCoefficient 28 55 1 0) v2364_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2364_pb : Scalar.QComplex := ((-387264019801956466240197 : Int)/10^30,(-431477337322104589288235396 : Int)/10^30)
theorem v2364_pb_checked : Scalar.distance (sourceCoefficient 28 55 1 1) v2364_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2364_pg : Scalar.QComplex := ((-93086391337000852163317 : Int)/10^30,(83547864464348022751 : Int)/10^30)
theorem v2364_pg_checked : Scalar.distance (sourceCoefficient 28 55 1 2) v2364_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2364_mb : Scalar.QComplex := ((-759609384696953859916205 : Int)/10^30,(-431476842471965050686802012 : Int)/10^30)
theorem v2364_mb_checked : Scalar.distance (sourceCoefficient 28 55 3 1) v2364_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2364_mg : Scalar.QComplex := ((-93086284578638922548522 : Int)/10^30,(163877196624056934779 : Int)/10^30)
theorem v2364_mg_checked : Scalar.distance (sourceCoefficient 28 55 3 2) v2364_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2364_upper : Scalar.QComplex := ((999996558782523605657732653023 : Int)/10^30,(-2623437270226022517549521550 : Int)/10^30)
theorem v2364_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 55 5) 1) 14) v2364_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2364 : Material (28 : Basis) (55 : Basis) where
  plus := ![v2364_pa,v2364_pb,v2364_pg]
  minus := ![(Primitive.Addresses.material2364 1).one,v2364_mb,v2364_mg]
  upper := v2364_upper
  lower := (Primitive.Addresses.material2364 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2364_pa_checked.trans (by decide +kernel)
    · exact v2364_pb_checked.trans (by decide +kernel)
    · exact v2364_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 55 Primitive.Addresses.material2364
    · exact v2364_mb_checked.trans (by decide +kernel)
    · exact v2364_mg_checked.trans (by decide +kernel)
  upper_error := v2364_upper_checked
  lower_error := reuse_lower_error 28 55 Primitive.Addresses.material2364

def v2365_pa : Scalar.QComplex := ((999999593944895865232102233580 : Int)/10^30,(-901171483896815391034384044 : Int)/10^30)
theorem v2365_pa_checked : Scalar.distance (sourceCoefficient 28 56 1 0) v2365_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2365_pb : Scalar.QComplex := ((-388835228781647498923916 : Int)/10^30,(-431477335713876189283529321 : Int)/10^30)
theorem v2365_pb_checked : Scalar.distance (sourceCoefficient 28 56 1 1) v2365_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2365_pg : Scalar.QComplex := ((-93086391011095386994040 : Int)/10^30,(83886835180745602360 : Int)/10^30)
theorem v2365_pg_checked : Scalar.distance (sourceCoefficient 28 56 1 2) v2365_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2365_mb : Scalar.QComplex := ((-761180591703783304377478 : Int)/10^30,(-431476839507854664651206627 : Int)/10^30)
theorem v2365_mb_checked : Scalar.distance (sourceCoefficient 28 56 3 1) v2365_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2365_mg : Scalar.QComplex := ((-93086283960217117151974 : Int)/10^30,(164216166932998486743 : Int)/10^30)
theorem v2365_mg_checked : Scalar.distance (sourceCoefficient 28 56 3 2) v2365_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2365_upper : Scalar.QComplex := ((999996549222741320797127366200 : Int)/10^30,(-2627078721602136673914845605 : Int)/10^30)
theorem v2365_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 56 5) 1) 14) v2365_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2365 : Material (28 : Basis) (56 : Basis) where
  plus := ![v2365_pa,v2365_pb,v2365_pg]
  minus := ![(Primitive.Addresses.material2365 1).one,v2365_mb,v2365_mg]
  upper := v2365_upper
  lower := (Primitive.Addresses.material2365 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2365_pa_checked.trans (by decide +kernel)
    · exact v2365_pb_checked.trans (by decide +kernel)
    · exact v2365_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 56 Primitive.Addresses.material2365
    · exact v2365_mb_checked.trans (by decide +kernel)
    · exact v2365_mg_checked.trans (by decide +kernel)
  upper_error := v2365_upper_checked
  lower_error := reuse_lower_error 28 56 Primitive.Addresses.material2365

def v2366_pa : Scalar.QComplex := ((999999583261668655686350123027 : Int)/10^30,(-912949335405744456205975517 : Int)/10^30)
theorem v2366_pa_checked : Scalar.distance (sourceCoefficient 28 57 1 0) v2366_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2366_pb : Scalar.QComplex := ((-393917106246481801750928 : Int)/10^30,(-431477330460024620970540317 : Int)/10^30)
theorem v2366_pb_checked : Scalar.distance (sourceCoefficient 28 57 1 1) v2366_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2366_pg : Scalar.QComplex := ((-93086389947133907970659 : Int)/10^30,(84983193253310021803 : Int)/10^30)
theorem v2366_pg_checked : Scalar.distance (sourceCoefficient 28 57 1 2) v2366_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2366_mb : Scalar.QComplex := ((-766262462742565095009598 : Int)/10^30,(-431476829868573679699884502 : Int)/10^30)
theorem v2366_mb_checked : Scalar.distance (sourceCoefficient 28 57 3 1) v2366_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2366_mg : Scalar.QComplex := ((-93086281950148395801569 : Int)/10^30,(165312523679187852380 : Int)/10^30)
theorem v2366_mg_checked : Scalar.distance (sourceCoefficient 28 57 3 2) v2366_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2366_upper : Scalar.QComplex := ((999996518212026796594192641323 : Int)/10^30,(-2638856537131058451287771037 : Int)/10^30)
theorem v2366_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 57 5) 1) 14) v2366_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2366 : Material (28 : Basis) (57 : Basis) where
  plus := ![v2366_pa,v2366_pb,v2366_pg]
  minus := ![(Primitive.Addresses.material2366 1).one,v2366_mb,v2366_mg]
  upper := v2366_upper
  lower := (Primitive.Addresses.material2366 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2366_pa_checked.trans (by decide +kernel)
    · exact v2366_pb_checked.trans (by decide +kernel)
    · exact v2366_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 57 Primitive.Addresses.material2366
    · exact v2366_mb_checked.trans (by decide +kernel)
    · exact v2366_mg_checked.trans (by decide +kernel)
  upper_error := v2366_upper_checked
  lower_error := reuse_lower_error 28 57 Primitive.Addresses.material2366

def v2367_pa : Scalar.QComplex := ((999999577407000457438583298047 : Int)/10^30,(-919339883014045883629088545 : Int)/10^30)
theorem v2367_pa_checked : Scalar.distance (sourceCoefficient 28 58 1 0) v2367_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2367_pb : Scalar.QComplex := ((-396674483488735600407464 : Int)/10^30,(-431477327575937767267203659 : Int)/10^30)
theorem v2367_pb_checked : Scalar.distance (sourceCoefficient 28 58 1 1) v2367_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2367_pg : Scalar.QComplex := ((-93086389363534151755320 : Int)/10^30,(85578066472363217742 : Int)/10^30)
theorem v2367_pg_checked : Scalar.distance (sourceCoefficient 28 58 1 2) v2367_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2367_mb : Scalar.QComplex := ((-769019836469284267713643 : Int)/10^30,(-431476824604995527469792958 : Int)/10^30)
theorem v2367_mb_checked : Scalar.distance (sourceCoefficient 28 58 3 1) v2367_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2367_mg : Scalar.QComplex := ((-93086280853200060939400 : Int)/10^30,(165907396173122256560 : Int)/10^30)
theorem v2367_mg_checked : Scalar.distance (sourceCoefficient 28 58 3 2) v2367_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2367_upper : Scalar.QComplex := ((999996501327861892209004007606 : Int)/10^30,(-2645247065116763723775155414 : Int)/10^30)
theorem v2367_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 58 5) 1) 14) v2367_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2367 : Material (28 : Basis) (58 : Basis) where
  plus := ![v2367_pa,v2367_pb,v2367_pg]
  minus := ![(Primitive.Addresses.material2367 1).one,v2367_mb,v2367_mg]
  upper := v2367_upper
  lower := (Primitive.Addresses.material2367 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2367_pa_checked.trans (by decide +kernel)
    · exact v2367_pb_checked.trans (by decide +kernel)
    · exact v2367_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 58 Primitive.Addresses.material2367
    · exact v2367_mb_checked.trans (by decide +kernel)
    · exact v2367_mg_checked.trans (by decide +kernel)
  upper_error := v2367_upper_checked
  lower_error := reuse_lower_error 28 58 Primitive.Addresses.material2367

def v2368_pa : Scalar.QComplex := ((999999561103662333400912043164 : Int)/10^30,(-936905802470666182585333462 : Int)/10^30)
theorem v2368_pa_checked : Scalar.distance (sourceCoefficient 28 59 1 0) v2368_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2368_pb : Scalar.QComplex := ((-404253781725120817064154 : Int)/10^30,(-431477319527299444754445614 : Int)/10^30)
theorem v2368_pb_checked : Scalar.distance (sourceCoefficient 28 59 1 1) v2368_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2368_pg : Scalar.QComplex := ((-93086387736522713384783 : Int)/10^30,(87213215078943086519 : Int)/10^30)
theorem v2368_pg_checked : Scalar.distance (sourceCoefficient 28 59 1 2) v2368_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2368_mb : Scalar.QComplex := ((-776599124937937984807656 : Int)/10^30,(-431476810015767182753209360 : Int)/10^30)
theorem v2368_mb_checked : Scalar.distance (sourceCoefficient 28 59 3 1) v2368_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2368_mg : Scalar.QComplex := ((-93086277815129625260586 : Int)/10^30,(167542542766823975685 : Int)/10^30)
theorem v2368_mg_checked : Scalar.distance (sourceCoefficient 28 59 3 2) v2368_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2368_upper : Scalar.QComplex := ((999996454707364635716544237693 : Int)/10^30,(-2662812930272927855135507795 : Int)/10^30)
theorem v2368_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 59 5) 1) 14) v2368_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2368 : Material (28 : Basis) (59 : Basis) where
  plus := ![v2368_pa,v2368_pb,v2368_pg]
  minus := ![(Primitive.Addresses.material2368 1).one,v2368_mb,v2368_mg]
  upper := v2368_upper
  lower := (Primitive.Addresses.material2368 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2368_pa_checked.trans (by decide +kernel)
    · exact v2368_pb_checked.trans (by decide +kernel)
    · exact v2368_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 59 Primitive.Addresses.material2368
    · exact v2368_mb_checked.trans (by decide +kernel)
    · exact v2368_mg_checked.trans (by decide +kernel)
  upper_error := v2368_upper_checked
  lower_error := reuse_lower_error 28 59 Primitive.Addresses.material2368

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
