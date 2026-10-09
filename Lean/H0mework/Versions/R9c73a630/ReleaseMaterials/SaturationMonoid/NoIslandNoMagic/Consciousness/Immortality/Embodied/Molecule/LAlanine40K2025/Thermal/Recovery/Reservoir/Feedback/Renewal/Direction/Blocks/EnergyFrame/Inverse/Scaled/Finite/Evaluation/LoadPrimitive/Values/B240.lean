import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B160

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3841_pa : Scalar.QComplex := ((999998204254495571478607864905 : Int)/10^30,(-1895122102703444833901951018 : Int)/10^30)
theorem v3841_pa_checked : Scalar.distance (sourceCoefficient 54 89 1 0) v3841_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3841_pb : Scalar.QComplex := ((-817702527956828845163474 : Int)/10^30,(-431476715091189538915979868 : Int)/10^30)
theorem v3841_pb_checked : Scalar.distance (sourceCoefficient 54 89 1 1) v3841_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3841_pg : Scalar.QComplex := ((-93086259384248679687097 : Int)/10^30,(176410144404799382315 : Int)/10^30)
theorem v3841_pg_checked : Scalar.distance (sourceCoefficient 54 89 1 2) v3841_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3841_mb : Scalar.QComplex := ((-1190047195622642192774644 : Int)/10^30,(-431475848792235378423296670 : Int)/10^30)
theorem v3841_mb_checked : Scalar.distance (sourceCoefficient 54 89 3 1) v3841_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3841_mg : Scalar.QComplex := ((-93086072489970655334900 : Int)/10^30,(256739328118355263161 : Int)/10^30)
theorem v3841_mg_checked : Scalar.distance (sourceCoefficient 54 89 3 2) v3841_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3841_upper : Scalar.QComplex := ((999993444065813243172829813660 : Int)/10^30,(-3621025461556517867047681557 : Int)/10^30)
theorem v3841_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 89 5) 1) 14) v3841_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3841 : Material (54 : Basis) (89 : Basis) where
  plus := ![v3841_pa,v3841_pb,v3841_pg]
  minus := ![(Primitive.Addresses.material3841 1).one,v3841_mb,v3841_mg]
  upper := v3841_upper
  lower := (Primitive.Addresses.material3841 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3841_pa_checked.trans (by decide +kernel)
    · exact v3841_pb_checked.trans (by decide +kernel)
    · exact v3841_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 89 Primitive.Addresses.material3841
    · exact v3841_mb_checked.trans (by decide +kernel)
    · exact v3841_mg_checked.trans (by decide +kernel)
  upper_error := v3841_upper_checked
  lower_error := reuse_lower_error 54 89 Primitive.Addresses.material3841

def v3842_pa : Scalar.QComplex := ((999998154253425180858428984570 : Int)/10^30,(-1921324996677518034272962664 : Int)/10^30)
theorem v3842_pa_checked : Scalar.distance (sourceCoefficient 54 90 1 0) v3842_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3842_pb : Scalar.QComplex := ((-829008482021771677491221 : Int)/10^30,(-431476690989696701096945310 : Int)/10^30)
theorem v3842_pb_checked : Scalar.distance (sourceCoefficient 54 90 1 1) v3842_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3842_pg : Scalar.QComplex := ((-93086254457224894769008 : Int)/10^30,(178849277646191843587 : Int)/10^30)
theorem v3842_pg_checked : Scalar.distance (sourceCoefficient 54 90 1 2) v3842_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3842_mb : Scalar.QComplex := ((-1201353124679358791001803 : Int)/10^30,(-431475814934222357914519386 : Int)/10^30)
theorem v3842_mb_checked : Scalar.distance (sourceCoefficient 54 90 3 1) v3842_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3842_mg : Scalar.QComplex := ((-93086065458086572134450 : Int)/10^30,(259178456199747323296 : Int)/10^30)
theorem v3842_mg_checked : Scalar.distance (sourceCoefficient 54 90 3 2) v3842_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3842_upper : Scalar.QComplex := ((999993348840999431995495074596 : Int)/10^30,(-3647228230207147068642774254 : Int)/10^30)
theorem v3842_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 90 5) 1) 14) v3842_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3842 : Material (54 : Basis) (90 : Basis) where
  plus := ![v3842_pa,v3842_pb,v3842_pg]
  minus := ![(Primitive.Addresses.material3842 1).one,v3842_mb,v3842_mg]
  upper := v3842_upper
  lower := (Primitive.Addresses.material3842 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3842_pa_checked.trans (by decide +kernel)
    · exact v3842_pb_checked.trans (by decide +kernel)
    · exact v3842_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 90 Primitive.Addresses.material3842
    · exact v3842_mb_checked.trans (by decide +kernel)
    · exact v3842_mg_checked.trans (by decide +kernel)
  upper_error := v3842_upper_checked
  lower_error := reuse_lower_error 54 90 Primitive.Addresses.material3842

def v3843_pa : Scalar.QComplex := ((999998125783666107887171227717 : Int)/10^30,(-1936086040210341331087890230 : Int)/10^30)
theorem v3843_pa_checked : Scalar.distance (sourceCoefficient 54 91 1 0) v3843_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3843_pb : Scalar.QComplex := ((-835377537156054573792392 : Int)/10^30,(-431476677238513682339134889 : Int)/10^30)
theorem v3843_pb_checked : Scalar.distance (sourceCoefficient 54 91 1 1) v3843_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3843_pg : Scalar.QComplex := ((-93086251648819118678684 : Int)/10^30,(180223330130294642865 : Int)/10^30)
theorem v3843_pg_checked : Scalar.distance (sourceCoefficient 54 91 1 2) v3843_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3843_mb : Scalar.QComplex := ((-1207722165575499765714715 : Int)/10^30,(-431475795686836730059283820 : Int)/10^30)
theorem v3843_mb_checked : Scalar.distance (sourceCoefficient 54 91 3 1) v3843_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3843_mg : Scalar.QComplex := ((-93086061463936432987836 : Int)/10^30,(260552505748699886577 : Int)/10^30)
theorem v3843_mg_checked : Scalar.distance (sourceCoefficient 54 91 3 2) v3843_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3843_upper : Scalar.QComplex := ((999993294895060735141806844796 : Int)/10^30,(-3661989202618908573713713684 : Int)/10^30)
theorem v3843_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 91 5) 1) 14) v3843_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3843 : Material (54 : Basis) (91 : Basis) where
  plus := ![v3843_pa,v3843_pb,v3843_pg]
  minus := ![(Primitive.Addresses.material3843 1).one,v3843_mb,v3843_mg]
  upper := v3843_upper
  lower := (Primitive.Addresses.material3843 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3843_pa_checked.trans (by decide +kernel)
    · exact v3843_pb_checked.trans (by decide +kernel)
    · exact v3843_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 91 Primitive.Addresses.material3843
    · exact v3843_mb_checked.trans (by decide +kernel)
    · exact v3843_mg_checked.trans (by decide +kernel)
  upper_error := v3843_upper_checked
  lower_error := reuse_lower_error 54 91 Primitive.Addresses.material3843

def v3844_pa : Scalar.QComplex := ((999998063403302672900735347878 : Int)/10^30,(-1968042083962492513212516338 : Int)/10^30)
theorem v3844_pa_checked : Scalar.distance (sourceCoefficient 54 92 1 0) v3844_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3844_pb : Scalar.QComplex := ((-849165844112087516497583 : Int)/10^30,(-431476647039272322130084272 : Int)/10^30)
theorem v3844_pb_checked : Scalar.distance (sourceCoefficient 54 92 1 1) v3844_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3844_pg : Scalar.QComplex := ((-93086245487862850858725 : Int)/10^30,(183198003338825993477 : Int)/10^30)
theorem v3844_pg_checked : Scalar.distance (sourceCoefficient 54 92 1 2) v3844_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3844_mb : Scalar.QComplex := ((-1221510441336930701410876 : Int)/10^30,(-431475753588918713644146587 : Int)/10^30)
theorem v3844_mb_checked : Scalar.distance (sourceCoefficient 54 92 3 1) v3844_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3844_mg : Scalar.QComplex := ((-93086052735973454518862 : Int)/10^30,(263527172532996672411 : Int)/10^30)
theorem v3844_mg_checked : Scalar.distance (sourceCoefficient 54 92 3 2) v3844_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3844_upper : Scalar.QComplex := ((999993177361557721809273154561 : Int)/10^30,(-3693945091113438221177548011 : Int)/10^30)
theorem v3844_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 92 5) 1) 14) v3844_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3844 : Material (54 : Basis) (92 : Basis) where
  plus := ![v3844_pa,v3844_pb,v3844_pg]
  minus := ![(Primitive.Addresses.material3844 1).one,v3844_mb,v3844_mg]
  upper := v3844_upper
  lower := (Primitive.Addresses.material3844 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3844_pa_checked.trans (by decide +kernel)
    · exact v3844_pb_checked.trans (by decide +kernel)
    · exact v3844_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 92 Primitive.Addresses.material3844
    · exact v3844_mb_checked.trans (by decide +kernel)
    · exact v3844_mg_checked.trans (by decide +kernel)
  upper_error := v3844_upper_checked
  lower_error := reuse_lower_error 54 92 Primitive.Addresses.material3844

def v3845_pa : Scalar.QComplex := ((999997988044928186615193287992 : Int)/10^30,(-2005967620791412130868610049 : Int)/10^30)
theorem v3845_pa_checked : Scalar.distance (sourceCoefficient 54 93 1 0) v3845_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3845_pb : Scalar.QComplex := ((-865529851071319096985847 : Int)/10^30,(-431476610436348720562289165 : Int)/10^30)
theorem v3845_pb_checked : Scalar.distance (sourceCoefficient 54 93 1 1) v3845_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3845_pg : Scalar.QComplex := ((-93086238032106956807609 : Int)/10^30,(186728355122749794316 : Int)/10^30)
theorem v3845_pg_checked : Scalar.distance (sourceCoefficient 54 93 1 2) v3845_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3845_mb : Scalar.QComplex := ((-1237874410616420085243087 : Int)/10^30,(-431475702864607742715229464 : Int)/10^30)
theorem v3845_mb_checked : Scalar.distance (sourceCoefficient 54 93 3 1) v3845_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3845_mg : Scalar.QComplex := ((-93086042233685748202118 : Int)/10^30,(267057516568427617262 : Int)/10^30)
theorem v3845_mg_checked : Scalar.distance (sourceCoefficient 54 93 3 2) v3845_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3845_upper : Scalar.QComplex := ((999993036547259484079852390641 : Int)/10^30,(-3731870441395007873664812858 : Int)/10^30)
theorem v3845_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 93 5) 1) 14) v3845_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3845 : Material (54 : Basis) (93 : Basis) where
  plus := ![v3845_pa,v3845_pb,v3845_pg]
  minus := ![(Primitive.Addresses.material3845 1).one,v3845_mb,v3845_mg]
  upper := v3845_upper
  lower := (Primitive.Addresses.material3845 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3845_pa_checked.trans (by decide +kernel)
    · exact v3845_pb_checked.trans (by decide +kernel)
    · exact v3845_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 93 Primitive.Addresses.material3845
    · exact v3845_mb_checked.trans (by decide +kernel)
    · exact v3845_mg_checked.trans (by decide +kernel)
  upper_error := v3845_upper_checked
  lower_error := reuse_lower_error 54 93 Primitive.Addresses.material3845

def v3846_pa : Scalar.QComplex := ((999997897177019062050853222792 : Int)/10^30,(-2050766086127671737003669794 : Int)/10^30)
theorem v3846_pa_checked : Scalar.distance (sourceCoefficient 54 94 1 0) v3846_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3846_pb : Scalar.QComplex := ((-884859369489390573169066 : Int)/10^30,(-431476566134167166025528101 : Int)/10^30)
theorem v3846_pb_checked : Scalar.distance (sourceCoefficient 54 94 1 1) v3846_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3846_pg : Scalar.QComplex := ((-93086229023973233715230 : Int)/10^30,(190898482993594734349 : Int)/10^30)
theorem v3846_pg_checked : Scalar.distance (sourceCoefficient 54 94 1 2) v3846_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3846_mb : Scalar.QComplex := ((-1257203883606441066368730 : Int)/10^30,(-431475641881938858302189365 : Int)/10^30)
theorem v3846_mb_checked : Scalar.distance (sourceCoefficient 54 94 3 1) v3846_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3846_mg : Scalar.QComplex := ((-93086029626922842297693 : Int)/10^30,(271227635112929674974 : Int)/10^30)
theorem v3846_mg_checked : Scalar.distance (sourceCoefficient 54 94 3 2) v3846_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3846_upper : Scalar.QComplex := ((999992868361398611236394202642 : Int)/10^30,(-3776668683179448082166099416 : Int)/10^30)
theorem v3846_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 94 5) 1) 14) v3846_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3846 : Material (54 : Basis) (94 : Basis) where
  plus := ![v3846_pa,v3846_pb,v3846_pg]
  minus := ![(Primitive.Addresses.material3846 1).one,v3846_mb,v3846_mg]
  upper := v3846_upper
  lower := (Primitive.Addresses.material3846 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3846_pa_checked.trans (by decide +kernel)
    · exact v3846_pb_checked.trans (by decide +kernel)
    · exact v3846_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 94 Primitive.Addresses.material3846
    · exact v3846_mb_checked.trans (by decide +kernel)
    · exact v3846_mg_checked.trans (by decide +kernel)
  upper_error := v3846_upper_checked
  lower_error := reuse_lower_error 54 94 Primitive.Addresses.material3846

def v3847_pa : Scalar.QComplex := ((999997805400841311647008524952 : Int)/10^30,(-2095040214676376723446000470 : Int)/10^30)
theorem v3847_pa_checked : Scalar.distance (sourceCoefficient 54 95 1 0) v3847_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3847_pb : Scalar.QComplex := ((-903962647472105890160177 : Int)/10^30,(-431476521216121909971285096 : Int)/10^30)
theorem v3847_pb_checked : Scalar.distance (sourceCoefficient 54 95 1 1) v3847_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3847_pg : Scalar.QComplex := ((-93086219907132928182509 : Int)/10^30,(195019802127945859964 : Int)/10^30)
theorem v3847_pg_checked : Scalar.distance (sourceCoefficient 54 95 1 2) v3847_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3847_mb : Scalar.QComplex := ((-1276307115713882905145915 : Int)/10^30,(-431475580478641807907278387 : Int)/10^30)
theorem v3847_mb_checked : Scalar.distance (sourceCoefficient 54 95 3 1) v3847_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3847_mg : Scalar.QComplex := ((-93086016953573135759629 : Int)/10^30,(275348944845302756851 : Int)/10^30)
theorem v3847_mg_checked : Scalar.distance (sourceCoefficient 54 95 3 2) v3847_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3847_upper : Scalar.QComplex := ((999992700172228193170340096929 : Int)/10^30,(-3820942587389682472398627048 : Int)/10^30)
theorem v3847_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 95 5) 1) 14) v3847_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3847 : Material (54 : Basis) (95 : Basis) where
  plus := ![v3847_pa,v3847_pb,v3847_pg]
  minus := ![(Primitive.Addresses.material3847 1).one,v3847_mb,v3847_mg]
  upper := v3847_upper
  lower := (Primitive.Addresses.material3847 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3847_pa_checked.trans (by decide +kernel)
    · exact v3847_pb_checked.trans (by decide +kernel)
    · exact v3847_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 95 Primitive.Addresses.material3847
    · exact v3847_mb_checked.trans (by decide +kernel)
    · exact v3847_mg_checked.trans (by decide +kernel)
  upper_error := v3847_upper_checked
  lower_error := reuse_lower_error 54 95 Primitive.Addresses.material3847

def v3848_pa : Scalar.QComplex := ((999997760625623299769537187822 : Int)/10^30,(-2116304264183877200760782857 : Int)/10^30)
theorem v3848_pa_checked : Scalar.distance (sourceCoefficient 54 96 1 0) v3848_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3848_pb : Scalar.QComplex := ((-913137600097784020087167 : Int)/10^30,(-431476499241935690157029598 : Int)/10^30)
theorem v3848_pb_checked : Scalar.distance (sourceCoefficient 54 96 1 1) v3848_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3848_pg : Scalar.QComplex := ((-93086215452808368006412 : Int)/10^30,(196999195854468899762 : Int)/10^30)
theorem v3848_pg_checked : Scalar.distance (sourceCoefficient 54 96 1 2) v3848_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3848_mb : Scalar.QComplex := ((-1285482045960573829392278 : Int)/10^30,(-431475550586892878653241390 : Int)/10^30)
theorem v3848_mb_checked : Scalar.distance (sourceCoefficient 54 96 3 1) v3848_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3848_mg : Scalar.QComplex := ((-93086010791122596726847 : Int)/10^30,(277328333990925569401 : Int)/10^30)
theorem v3848_mg_checked : Scalar.distance (sourceCoefficient 54 96 3 2) v3848_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3848_upper : Scalar.QComplex := ((999992618697256478276941599643 : Int)/10^30,(-3842206527948914746558148867 : Int)/10^30)
theorem v3848_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 96 5) 1) 14) v3848_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3848 : Material (54 : Basis) (96 : Basis) where
  plus := ![v3848_pa,v3848_pb,v3848_pg]
  minus := ![(Primitive.Addresses.material3848 1).one,v3848_mb,v3848_mg]
  upper := v3848_upper
  lower := (Primitive.Addresses.material3848 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3848_pa_checked.trans (by decide +kernel)
    · exact v3848_pb_checked.trans (by decide +kernel)
    · exact v3848_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 96 Primitive.Addresses.material3848
    · exact v3848_mb_checked.trans (by decide +kernel)
    · exact v3848_mg_checked.trans (by decide +kernel)
  upper_error := v3848_upper_checked
  lower_error := reuse_lower_error 54 96 Primitive.Addresses.material3848

def v3849_pa : Scalar.QComplex := ((999997603115748820682870365441 : Int)/10^30,(-2189466317919625067241351771 : Int)/10^30)
theorem v3849_pa_checked : Scalar.distance (sourceCoefficient 54 97 1 0) v3849_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3849_pb : Scalar.QComplex := ((-944705356527081365952357 : Int)/10^30,(-431476421649328240465825802 : Int)/10^30)
theorem v3849_pb_checked : Scalar.distance (sourceCoefficient 54 97 1 1) v3849_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3849_pg : Scalar.QComplex := ((-93086199751925537081321 : Int)/10^30,(203809587527969707181 : Int)/10^30)
theorem v3849_pg_checked : Scalar.distance (sourceCoefficient 54 97 1 2) v3849_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3849_mb : Scalar.QComplex := ((-1317049723676827151118387 : Int)/10^30,(-431475445752762280723740651 : Int)/10^30)
theorem v3849_mb_checked : Scalar.distance (sourceCoefficient 54 97 3 1) v3849_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3849_mg : Scalar.QComplex := ((-93085989213184326381474 : Int)/10^30,(284138709579451564925 : Int)/10^30)
theorem v3849_mg_checked : Scalar.distance (sourceCoefficient 54 97 3 2) v3849_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3849_upper : Scalar.QComplex := ((999992334916549053412954654696 : Int)/10^30,(-3915368200870623625473171419 : Int)/10^30)
theorem v3849_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 54 97 5) 1) 14) v3849_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3849 : Material (54 : Basis) (97 : Basis) where
  plus := ![v3849_pa,v3849_pb,v3849_pg]
  minus := ![(Primitive.Addresses.material3849 1).one,v3849_mb,v3849_mg]
  upper := v3849_upper
  lower := (Primitive.Addresses.material3849 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3849_pa_checked.trans (by decide +kernel)
    · exact v3849_pb_checked.trans (by decide +kernel)
    · exact v3849_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 54 97 Primitive.Addresses.material3849
    · exact v3849_mb_checked.trans (by decide +kernel)
    · exact v3849_mg_checked.trans (by decide +kernel)
  upper_error := v3849_upper_checked
  lower_error := reuse_lower_error 54 97 Primitive.Addresses.material3849

def v3850_pa : Scalar.QComplex := ((999999191032925927717611252010 : Int)/10^30,(-1271980146746338900744657335 : Int)/10^30)
theorem v3850_pa_checked : Scalar.distance (sourceCoefficient 55 56 1 0) v3850_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3850_pb : Scalar.QComplex := ((-548830840478943773767929 : Int)/10^30,(-431477171948591399379198036 : Int)/10^30)
theorem v3850_pb_checked : Scalar.distance (sourceCoefficient 55 56 1 1) v3850_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3850_pg : Scalar.QComplex := ((-93086354593016358315133 : Int)/10^30,(118404090760317546154 : Int)/10^30)
theorem v3850_pg_checked : Scalar.distance (sourceCoefficient 55 56 1 2) v3850_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3850_mb : Scalar.QComplex := ((-921176002505336124575558 : Int)/10^30,(-431476537673623892134131332 : Int)/10^30)
theorem v3850_mb_checked : Scalar.distance (sourceCoefficient 55 56 3 1) v3850_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3850_mg : Scalar.QComplex := ((-93086217755314682899549 : Int)/10^30,(198733378233056669394 : Int)/10^30)
theorem v3850_mg_checked : Scalar.distance (sourceCoefficient 55 56 3 2) v3850_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3850_upper : Scalar.QComplex := ((999995506329258894171278330926 : Int)/10^30,(-2997886136786206890833042307 : Int)/10^30)
theorem v3850_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 56 5) 1) 14) v3850_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3850 : Material (55 : Basis) (56 : Basis) where
  plus := ![v3850_pa,v3850_pb,v3850_pg]
  minus := ![(Primitive.Addresses.material3850 1).one,v3850_mb,v3850_mg]
  upper := v3850_upper
  lower := (Primitive.Addresses.material3850 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3850_pa_checked.trans (by decide +kernel)
    · exact v3850_pb_checked.trans (by decide +kernel)
    · exact v3850_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 56 Primitive.Addresses.material3850
    · exact v3850_mb_checked.trans (by decide +kernel)
    · exact v3850_mg_checked.trans (by decide +kernel)
  upper_error := v3850_upper_checked
  lower_error := reuse_lower_error 55 56 Primitive.Addresses.material3850

def v3851_pa : Scalar.QComplex := ((999999175982367580296930708689 : Int)/10^30,(-1283757993484109761167179808 : Int)/10^30)
theorem v3851_pa_checked : Scalar.distance (sourceCoefficient 55 57 1 0) v3851_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3851_pb : Scalar.QComplex := ((-553912716571346415015925 : Int)/10^30,(-431477165438469703237529546 : Int)/10^30)
theorem v3851_pb_checked : Scalar.distance (sourceCoefficient 55 57 1 1) v3851_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3851_pg : Scalar.QComplex := ((-93086353190272160671993 : Int)/10^30,(119500448462773563706 : Int)/10^30)
theorem v3851_pg_checked : Scalar.distance (sourceCoefficient 55 57 1 2) v3851_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3851_mb : Scalar.QComplex := ((-926257871087582224637739 : Int)/10^30,(-431476526778074431467624608 : Int)/10^30)
theorem v3851_mb_checked : Scalar.distance (sourceCoefficient 55 57 3 1) v3851_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3851_mg : Scalar.QComplex := ((-93086215406463688460556 : Int)/10^30,(199829734316783542987 : Int)/10^30)
theorem v3851_mg_checked : Scalar.distance (sourceCoefficient 55 57 3 2) v3851_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3851_upper : Scalar.QComplex := ((999995470951227971306347590336 : Int)/10^30,(-3009663940006360226750332820 : Int)/10^30)
theorem v3851_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 57 5) 1) 14) v3851_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3851 : Material (55 : Basis) (57 : Basis) where
  plus := ![v3851_pa,v3851_pb,v3851_pg]
  minus := ![(Primitive.Addresses.material3851 1).one,v3851_mb,v3851_mg]
  upper := v3851_upper
  lower := (Primitive.Addresses.material3851 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3851_pa_checked.trans (by decide +kernel)
    · exact v3851_pb_checked.trans (by decide +kernel)
    · exact v3851_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 57 Primitive.Addresses.material3851
    · exact v3851_mb_checked.trans (by decide +kernel)
    · exact v3851_mg_checked.trans (by decide +kernel)
  upper_error := v3851_upper_checked
  lower_error := reuse_lower_error 55 57 Primitive.Addresses.material3851

def v3852_pa : Scalar.QComplex := ((999999167758028012899949798499 : Int)/10^30,(-1290148538482100580884259368 : Int)/10^30)
theorem v3852_pa_checked : Scalar.distance (sourceCoefficient 55 58 1 0) v3852_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3852_pb : Scalar.QComplex := ((-556670093062739988629691 : Int)/10^30,(-431477161872742905418320760 : Int)/10^30)
theorem v3852_pb_checked : Scalar.distance (sourceCoefficient 55 58 1 1) v3852_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3852_pg : Scalar.QComplex := ((-93086352422852198670236 : Int)/10^30,(120095321479339680870 : Int)/10^30)
theorem v3852_pg_checked : Scalar.distance (sourceCoefficient 55 58 1 2) v3852_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3852_mb : Scalar.QComplex := ((-929015243475216880030043 : Int)/10^30,(-431476520832857236885921337 : Int)/10^30)
theorem v3852_mb_checked : Scalar.distance (sourceCoefficient 55 58 3 1) v3852_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3852_mg : Scalar.QComplex := ((-93086214125695390993862 : Int)/10^30,(200424606449602385148 : Int)/10^30)
theorem v3852_mg_checked : Scalar.distance (sourceCoefficient 55 58 3 2) v3852_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3852_upper : Scalar.QComplex := ((999995451697399732278391438446 : Int)/10^30,(-3016054461291920971038479170 : Int)/10^30)
theorem v3852_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 58 5) 1) 14) v3852_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3852 : Material (55 : Basis) (58 : Basis) where
  plus := ![v3852_pa,v3852_pb,v3852_pg]
  minus := ![(Primitive.Addresses.material3852 1).one,v3852_mb,v3852_mg]
  upper := v3852_upper
  lower := (Primitive.Addresses.material3852 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3852_pa_checked.trans (by decide +kernel)
    · exact v3852_pb_checked.trans (by decide +kernel)
    · exact v3852_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 58 Primitive.Addresses.material3852
    · exact v3852_mb_checked.trans (by decide +kernel)
    · exact v3852_mg_checked.trans (by decide +kernel)
  upper_error := v3852_upper_checked
  lower_error := reuse_lower_error 55 58 Primitive.Addresses.material3852

def v3853_pa : Scalar.QComplex := ((999999144941092171098718124370 : Int)/10^30,(-1307714450685648233728566827 : Int)/10^30)
theorem v3853_pa_checked : Scalar.distance (sourceCoefficient 55 59 1 0) v3853_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3853_pb : Scalar.QComplex := ((-564249389212766692783627 : Int)/10^30,(-431477151950457274722048699 : Int)/10^30)
theorem v3853_pb_checked : Scalar.distance (sourceCoefficient 55 59 1 1) v3853_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3853_pg : Scalar.QComplex := ((-93086350290567797932734 : Int)/10^30,(121730469523284019801 : Int)/10^30)
theorem v3853_pg_checked : Scalar.distance (sourceCoefficient 55 59 1 2) v3853_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3853_mb : Scalar.QComplex := ((-936594528240639620447762 : Int)/10^30,(-431476504369984082063776663 : Int)/10^30)
theorem v3853_mb_checked : Scalar.distance (sourceCoefficient 55 59 3 1) v3853_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3853_mg : Scalar.QComplex := ((-93086210582352666613421 : Int)/10^30,(202059752044640974048 : Int)/10^30)
theorem v3853_mg_checked : Scalar.distance (sourceCoefficient 55 59 3 2) v3853_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3853_upper : Scalar.QComplex := ((999995398563326977406424500675 : Int)/10^30,(-3033620307953144506995717388 : Int)/10^30)
theorem v3853_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 59 5) 1) 14) v3853_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3853 : Material (55 : Basis) (59 : Basis) where
  plus := ![v3853_pa,v3853_pb,v3853_pg]
  minus := ![(Primitive.Addresses.material3853 1).one,v3853_mb,v3853_mg]
  upper := v3853_upper
  lower := (Primitive.Addresses.material3853 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3853_pa_checked.trans (by decide +kernel)
    · exact v3853_pb_checked.trans (by decide +kernel)
    · exact v3853_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 59 Primitive.Addresses.material3853
    · exact v3853_mb_checked.trans (by decide +kernel)
    · exact v3853_mg_checked.trans (by decide +kernel)
  upper_error := v3853_upper_checked
  lower_error := reuse_lower_error 55 59 Primitive.Addresses.material3853

def v3854_pa : Scalar.QComplex := ((999999118236344564588724561007 : Int)/10^30,(-1327978363288980135655936109 : Int)/10^30)
theorem v3854_pa_checked : Scalar.distance (sourceCoefficient 55 60 1 0) v3854_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3854_pb : Scalar.QComplex := ((-572992811794753874028322 : Int)/10^30,(-431477140283669881705666427 : Int)/10^30)
theorem v3854_pb_checked : Scalar.distance (sourceCoefficient 55 60 1 1) v3854_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3854_pg : Scalar.QComplex := ((-93086347789153805912150 : Int)/10^30,(123616764782359633335 : Int)/10^30)
theorem v3854_pg_checked : Scalar.distance (sourceCoefficient 55 60 1 2) v3854_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3854_mb : Scalar.QComplex := ((-945337937499138912691606 : Int)/10^30,(-431476485158021134005554803 : Int)/10^30)
theorem v3854_mb_checked : Scalar.distance (sourceCoefficient 55 60 3 1) v3854_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3854_mg : Scalar.QComplex := ((-93086206453151752986101 : Int)/10^30,(203946044442755039067 : Int)/10^30)
theorem v3854_mg_checked : Scalar.distance (sourceCoefficient 55 60 3 2) v3854_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3854_upper : Scalar.QComplex := ((999995336884944318921313725983 : Int)/10^30,(-3053884144285787219588246310 : Int)/10^30)
theorem v3854_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 60 5) 1) 14) v3854_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3854 : Material (55 : Basis) (60 : Basis) where
  plus := ![v3854_pa,v3854_pb,v3854_pg]
  minus := ![(Primitive.Addresses.material3854 1).one,v3854_mb,v3854_mg]
  upper := v3854_upper
  lower := (Primitive.Addresses.material3854 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3854_pa_checked.trans (by decide +kernel)
    · exact v3854_pb_checked.trans (by decide +kernel)
    · exact v3854_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 60 Primitive.Addresses.material3854
    · exact v3854_mb_checked.trans (by decide +kernel)
    · exact v3854_mg_checked.trans (by decide +kernel)
  upper_error := v3854_upper_checked
  lower_error := reuse_lower_error 55 60 Primitive.Addresses.material3854

def v3855_pa : Scalar.QComplex := ((999999110438107791259599602123 : Int)/10^30,(-1333837693685825003646348041 : Int)/10^30)
theorem v3855_pa_checked : Scalar.distance (sourceCoefficient 55 61 1 0) v3855_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3855_pb : Scalar.QComplex := ((-575520981077277969470102 : Int)/10^30,(-431477136866177335994261505 : Int)/10^30)
theorem v3855_pb_checked : Scalar.distance (sourceCoefficient 55 61 1 1) v3855_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3855_pg : Scalar.QComplex := ((-93086347057555975530827 : Int)/10^30,(124162188922840463912 : Int)/10^30)
theorem v3855_pg_checked : Scalar.distance (sourceCoefficient 55 61 1 2) v3855_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3855_mb : Scalar.QComplex := ((-947866102891167892407119 : Int)/10^30,(-431476479558833634482152714 : Int)/10^30)
theorem v3855_mb_checked : Scalar.distance (sourceCoefficient 55 61 3 1) v3855_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3855_mg : Scalar.QComplex := ((-93086205250877726768521 : Int)/10^30,(204491467748813557352 : Int)/10^30)
theorem v3855_mg_checked : Scalar.distance (sourceCoefficient 55 61 3 2) v3855_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3855_upper : Scalar.QComplex := ((999995318974046449496902683905 : Int)/10^30,(-3059743452496798526523752491 : Int)/10^30)
theorem v3855_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 61 5) 1) 14) v3855_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3855 : Material (55 : Basis) (61 : Basis) where
  plus := ![v3855_pa,v3855_pb,v3855_pg]
  minus := ![(Primitive.Addresses.material3855 1).one,v3855_mb,v3855_mg]
  upper := v3855_upper
  lower := (Primitive.Addresses.material3855 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3855_pa_checked.trans (by decide +kernel)
    · exact v3855_pb_checked.trans (by decide +kernel)
    · exact v3855_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 61 Primitive.Addresses.material3855
    · exact v3855_mb_checked.trans (by decide +kernel)
    · exact v3855_mg_checked.trans (by decide +kernel)
  upper_error := v3855_upper_checked
  lower_error := reuse_lower_error 55 61 Primitive.Addresses.material3855

def v3856_pa : Scalar.QComplex := ((999999099046424353341452020570 : Int)/10^30,(-1342351049307136953846579201 : Int)/10^30)
theorem v3856_pa_checked : Scalar.distance (sourceCoefficient 55 62 1 0) v3856_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3856_pb : Scalar.QComplex := ((-579194302538879446890203 : Int)/10^30,(-431477131865510248041390595 : Int)/10^30)
theorem v3856_pb_checked : Scalar.distance (sourceCoefficient 55 62 1 1) v3856_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3856_pg : Scalar.QComplex := ((-93086345987931520017782 : Int)/10^30,(124954666791420913455 : Int)/10^30)
theorem v3856_pg_checked : Scalar.distance (sourceCoefficient 55 62 1 2) v3856_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3856_mb : Scalar.QComplex := ((-951539418669673435370491 : Int)/10^30,(-431476471388257427401304914 : Int)/10^30)
theorem v3856_mb_checked : Scalar.distance (sourceCoefficient 55 62 3 1) v3856_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3856_mg : Scalar.QComplex := ((-93086203497380960818873 : Int)/10^30,(205283944399280547384 : Int)/10^30)
theorem v3856_mg_checked : Scalar.distance (sourceCoefficient 55 62 3 2) v3856_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3856_upper : Scalar.QComplex := ((999995292889100501357537703772 : Int)/10^30,(-3068256775777455159382656312 : Int)/10^30)
theorem v3856_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 62 5) 1) 14) v3856_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3856 : Material (55 : Basis) (62 : Basis) where
  plus := ![v3856_pa,v3856_pb,v3856_pg]
  minus := ![(Primitive.Addresses.material3856 1).one,v3856_mb,v3856_mg]
  upper := v3856_upper
  lower := (Primitive.Addresses.material3856 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3856_pa_checked.trans (by decide +kernel)
    · exact v3856_pb_checked.trans (by decide +kernel)
    · exact v3856_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 62 Primitive.Addresses.material3856
    · exact v3856_mb_checked.trans (by decide +kernel)
    · exact v3856_mg_checked.trans (by decide +kernel)
  upper_error := v3856_upper_checked
  lower_error := reuse_lower_error 55 62 Primitive.Addresses.material3856

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
