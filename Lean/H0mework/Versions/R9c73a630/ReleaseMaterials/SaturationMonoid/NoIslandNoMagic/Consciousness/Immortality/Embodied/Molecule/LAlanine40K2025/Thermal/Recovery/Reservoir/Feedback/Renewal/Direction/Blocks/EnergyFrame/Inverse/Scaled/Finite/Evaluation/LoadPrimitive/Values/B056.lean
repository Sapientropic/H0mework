import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B037
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B038

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v897_pa : Scalar.QComplex := ((999999646082059657938357878248 : Int)/10^30,(-841329754273682387917483586 : Int)/10^30)
theorem v897_pa_checked : Scalar.distance (sourceCoefficient 9 70 1 0) v897_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v897_pb : Scalar.QComplex := ((-363014812319929293526458 : Int)/10^30,(-431477291749730353716675607 : Int)/10^30)
theorem v897_pb_checked : Scalar.distance (sourceCoefficient 9 70 1 1) v897_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v897_pg : Scalar.QComplex := ((-93086388695341145769863 : Int)/10^30,(78316376244846427887 : Int)/10^30)
theorem v897_pg_checked : Scalar.distance (sourceCoefficient 9 70 1 2) v897_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v897_mb : Scalar.QComplex := ((-735360146917108414536253 : Int)/10^30,(-431476817825581697019672246 : Int)/10^30)
theorem v897_mb_checked : Scalar.distance (sourceCoefficient 9 70 3 1) v897_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v897_mg : Scalar.QComplex := ((-93086286451518915712709 : Int)/10^30,(158645708072844144178 : Int)/10^30)
theorem v897_mg_checked : Scalar.distance (sourceCoefficient 9 70 3 2) v897_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v897_upper : Scalar.QComplex := ((999996704641223991545980917401 : Int)/10^30,(-2567237171090245300756598165 : Int)/10^30)
theorem v897_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 70 5) 1) 14) v897_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material897 : Material (9 : Basis) (70 : Basis) where
  plus := ![v897_pa,v897_pb,v897_pg]
  minus := ![(Primitive.Addresses.material897 1).one,v897_mb,v897_mg]
  upper := v897_upper
  lower := (Primitive.Addresses.material897 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v897_pa_checked.trans (by decide +kernel)
    · exact v897_pb_checked.trans (by decide +kernel)
    · exact v897_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 70 Primitive.Addresses.material897
    · exact v897_mb_checked.trans (by decide +kernel)
    · exact v897_mg_checked.trans (by decide +kernel)
  upper_error := v897_upper_checked
  lower_error := reuse_lower_error 9 70 Primitive.Addresses.material897

def v898_pa : Scalar.QComplex := ((999999625348719954691562620416 : Int)/10^30,(-865622561932760180970490560 : Int)/10^30)
theorem v898_pa_checked : Scalar.distance (sourceCoefficient 9 71 1 0) v898_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v898_pb : Scalar.QComplex := ((-373496607730346441974771 : Int)/10^30,(-431477279156659409468895789 : Int)/10^30)
theorem v898_pb_checked : Scalar.distance (sourceCoefficient 9 71 1 1) v898_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v898_pg : Scalar.QComplex := ((-93086386371938027306180 : Int)/10^30,(80577706440880629519 : Int)/10^30)
theorem v898_pg_checked : Scalar.distance (sourceCoefficient 9 71 1 2) v898_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v898_mb : Scalar.QComplex := ((-745841927557421035945987 : Int)/10^30,(-431476796187198085098495162 : Int)/10^30)
theorem v898_mb_checked : Scalar.distance (sourceCoefficient 9 71 3 1) v898_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v898_mg : Scalar.QComplex := ((-93086282176690549711984 : Int)/10^30,(160907035421889516889 : Int)/10^30)
theorem v898_mg_checked : Scalar.distance (sourceCoefficient 9 71 3 2) v898_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v898_upper : Scalar.QComplex := ((999996641980732974900378937011 : Int)/10^30,(-2591529906784176305338714963 : Int)/10^30)
theorem v898_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 71 5) 1) 14) v898_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material898 : Material (9 : Basis) (71 : Basis) where
  plus := ![v898_pa,v898_pb,v898_pg]
  minus := ![(Primitive.Addresses.material898 1).one,v898_mb,v898_mg]
  upper := v898_upper
  lower := (Primitive.Addresses.material898 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v898_pa_checked.trans (by decide +kernel)
    · exact v898_pb_checked.trans (by decide +kernel)
    · exact v898_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 71 Primitive.Addresses.material898
    · exact v898_mb_checked.trans (by decide +kernel)
    · exact v898_mg_checked.trans (by decide +kernel)
  upper_error := v898_upper_checked
  lower_error := reuse_lower_error 9 71 Primitive.Addresses.material898

def v899_pa : Scalar.QComplex := ((999999602181142051602175960563 : Int)/10^30,(-891985177924471965107946900 : Int)/10^30)
theorem v899_pa_checked : Scalar.distance (sourceCoefficient 9 72 1 0) v899_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v899_pb : Scalar.QComplex := ((-384871478195512671463975 : Int)/10^30,(-431477265106494167269133299 : Int)/10^30)
theorem v899_pb_checked : Scalar.distance (sourceCoefficient 9 72 1 1) v899_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v899_pg : Scalar.QComplex := ((-93086383778061768903899 : Int)/10^30,(83031707628199209944 : Int)/10^30)
theorem v899_pg_checked : Scalar.distance (sourceCoefficient 9 72 1 2) v899_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v899_mb : Scalar.QComplex := ((-757216781662543325925699 : Int)/10^30,(-431476772321037168127010624 : Int)/10^30)
theorem v899_mb_checked : Scalar.distance (sourceCoefficient 9 72 3 1) v899_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v899_mg : Scalar.QComplex := ((-93086277465122756583074 : Int)/10^30,(163361033457072914729 : Int)/10^30)
theorem v899_mg_checked : Scalar.distance (sourceCoefficient 9 72 3 2) v899_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v899_upper : Scalar.QComplex := ((999996573313705973342915642950 : Int)/10^30,(-2617892443526730625749258076 : Int)/10^30)
theorem v899_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 72 5) 1) 14) v899_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material899 : Material (9 : Basis) (72 : Basis) where
  plus := ![v899_pa,v899_pb,v899_pg]
  minus := ![(Primitive.Addresses.material899 1).one,v899_mb,v899_mg]
  upper := v899_upper
  lower := (Primitive.Addresses.material899 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v899_pa_checked.trans (by decide +kernel)
    · exact v899_pb_checked.trans (by decide +kernel)
    · exact v899_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 72 Primitive.Addresses.material899
    · exact v899_mb_checked.trans (by decide +kernel)
    · exact v899_mg_checked.trans (by decide +kernel)
  upper_error := v899_upper_checked
  lower_error := reuse_lower_error 9 72 Primitive.Addresses.material899

def v900_pa : Scalar.QComplex := ((999999593707553033723781136158 : Int)/10^30,(-901434816755487859541775714 : Int)/10^30)
theorem v900_pa_checked : Scalar.distance (sourceCoefficient 9 73 1 0) v900_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v900_pb : Scalar.QComplex := ((-388948782804774025928086 : Int)/10^30,(-431477259972889136826815043 : Int)/10^30)
theorem v900_pb_checked : Scalar.distance (sourceCoefficient 9 73 1 1) v900_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v900_pg : Scalar.QComplex := ((-93086382829914870208638 : Int)/10^30,(83911340541259379168 : Int)/10^30)
theorem v900_pg_checked : Scalar.distance (sourceCoefficient 9 73 1 2) v900_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v900_mb : Scalar.QComplex := ((-761294080323567900051652 : Int)/10^30,(-431476763668903806350663783 : Int)/10^30)
theorem v900_mb_checked : Scalar.distance (sourceCoefficient 9 73 3 1) v900_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v900_mg : Scalar.QComplex := ((-93086275757892624151055 : Int)/10^30,(164240665224397478588 : Int)/10^30)
theorem v900_mg_checked : Scalar.distance (sourceCoefficient 9 73 3 2) v900_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v900_upper : Scalar.QComplex := ((999996548530910218084718155607 : Int)/10^30,(-2627342053658973587070234235 : Int)/10^30)
theorem v900_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 73 5) 1) 14) v900_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material900 : Material (9 : Basis) (73 : Basis) where
  plus := ![v900_pa,v900_pb,v900_pg]
  minus := ![(Primitive.Addresses.material900 1).one,v900_mb,v900_mg]
  upper := v900_upper
  lower := (Primitive.Addresses.material900 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v900_pa_checked.trans (by decide +kernel)
    · exact v900_pb_checked.trans (by decide +kernel)
    · exact v900_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 73 Primitive.Addresses.material900
    · exact v900_mb_checked.trans (by decide +kernel)
    · exact v900_mg_checked.trans (by decide +kernel)
  upper_error := v900_upper_checked
  lower_error := reuse_lower_error 9 73 Primitive.Addresses.material900

def v901_pa : Scalar.QComplex := ((999999584065910579456252714999 : Int)/10^30,(-912067983124021710922034358 : Int)/10^30)
theorem v901_pa_checked : Scalar.distance (sourceCoefficient 9 74 1 0) v901_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v901_pb : Scalar.QComplex := ((-393536752628055852981222 : Int)/10^30,(-431477254134895389515370155 : Int)/10^30)
theorem v901_pb_checked : Scalar.distance (sourceCoefficient 9 74 1 1) v901_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v901_pg : Scalar.QComplex := ((-93086381751421030689216 : Int)/10^30,(84901143773611245413 : Int)/10^30)
theorem v901_pg_checked : Scalar.distance (sourceCoefficient 9 74 1 2) v901_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v901_mb : Scalar.QComplex := ((-765882043400613210865661 : Int)/10^30,(-431476753871700909789091542 : Int)/10^30)
theorem v901_mb_checked : Scalar.distance (sourceCoefficient 9 74 3 1) v901_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v901_mg : Scalar.QComplex := ((-93086273825243575767250 : Int)/10^30,(165230467157508755240 : Int)/10^30)
theorem v901_mg_checked : Scalar.distance (sourceCoefficient 9 74 3 2) v901_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v901_upper : Scalar.QComplex := ((999996520537401605139262439791 : Int)/10^30,(-2637975187550054998887659663 : Int)/10^30)
theorem v901_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 74 5) 1) 14) v901_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material901 : Material (9 : Basis) (74 : Basis) where
  plus := ![v901_pa,v901_pb,v901_pg]
  minus := ![(Primitive.Addresses.material901 1).one,v901_mb,v901_mg]
  upper := v901_upper
  lower := (Primitive.Addresses.material901 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v901_pa_checked.trans (by decide +kernel)
    · exact v901_pb_checked.trans (by decide +kernel)
    · exact v901_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 74 Primitive.Addresses.material901
    · exact v901_mb_checked.trans (by decide +kernel)
    · exact v901_mg_checked.trans (by decide +kernel)
  upper_error := v901_upper_checked
  lower_error := reuse_lower_error 9 74 Primitive.Addresses.material901

def v902_pa : Scalar.QComplex := ((999999570443761829630439816731 : Int)/10^30,(-926883105802547988855184027 : Int)/10^30)
theorem v902_pa_checked : Scalar.distance (sourceCoefficient 9 75 1 0) v902_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v902_pb : Scalar.QComplex := ((-399929141547940254791263 : Int)/10^30,(-431477245892405688876025529 : Int)/10^30)
theorem v902_pb_checked : Scalar.distance (sourceCoefficient 9 75 1 1) v902_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v902_pg : Scalar.QComplex := ((-93086380228290128157796 : Int)/10^30,(86280230276125595956 : Int)/10^30)
theorem v902_pg_checked : Scalar.distance (sourceCoefficient 9 75 1 2) v902_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v902_mb : Scalar.QComplex := ((-772274422827421687500498 : Int)/10^30,(-431476740112870542854632163 : Int)/10^30)
theorem v902_mb_checked : Scalar.distance (sourceCoefficient 9 75 3 1) v902_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v902_mg : Scalar.QComplex := ((-93086271112023700447568 : Int)/10^30,(166609551832132803914 : Int)/10^30)
theorem v902_mg_checked : Scalar.distance (sourceCoefficient 9 75 3 2) v902_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v902_upper : Scalar.QComplex := ((999996481345715418197994595378 : Int)/10^30,(-2652790264652603403197362465 : Int)/10^30)
theorem v902_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 75 5) 1) 14) v902_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material902 : Material (9 : Basis) (75 : Basis) where
  plus := ![v902_pa,v902_pb,v902_pg]
  minus := ![(Primitive.Addresses.material902 1).one,v902_mb,v902_mg]
  upper := v902_upper
  lower := (Primitive.Addresses.material902 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v902_pa_checked.trans (by decide +kernel)
    · exact v902_pb_checked.trans (by decide +kernel)
    · exact v902_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 75 Primitive.Addresses.material902
    · exact v902_mb_checked.trans (by decide +kernel)
    · exact v902_mg_checked.trans (by decide +kernel)
  upper_error := v902_upper_checked
  lower_error := reuse_lower_error 9 75 Primitive.Addresses.material902

def v903_pa : Scalar.QComplex := ((999999558845178664859351465701 : Int)/10^30,(-939313285359418787896494426 : Int)/10^30)
theorem v903_pa_checked : Scalar.distance (sourceCoefficient 9 76 1 0) v903_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v903_pb : Scalar.QComplex := ((-405292481606330907084171 : Int)/10^30,(-431477238879377256294772881 : Int)/10^30)
theorem v903_pb_checked : Scalar.distance (sourceCoefficient 9 76 1 1) v903_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v903_pg : Scalar.QComplex := ((-93086378931963705814421 : Int)/10^30,(87437310990185921395 : Int)/10^30)
theorem v903_pg_checked : Scalar.distance (sourceCoefficient 9 76 1 2) v903_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v903_mb : Scalar.QComplex := ((-777637754836868037062776 : Int)/10^30,(-431476728471523807022497822 : Int)/10^30)
theorem v903_mb_checked : Scalar.distance (sourceCoefficient 9 76 3 1) v903_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v903_mg : Scalar.QComplex := ((-93086268817189217532541 : Int)/10^30,(167766630996687780201 : Int)/10^30)
theorem v903_mg_checked : Scalar.distance (sourceCoefficient 9 76 3 2) v903_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v903_upper : Scalar.QComplex := ((999996448293787270075691355454 : Int)/10^30,(-2665220405678079576590768648 : Int)/10^30)
theorem v903_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 76 5) 1) 14) v903_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material903 : Material (9 : Basis) (76 : Basis) where
  plus := ![v903_pa,v903_pb,v903_pg]
  minus := ![(Primitive.Addresses.material903 1).one,v903_mb,v903_mg]
  upper := v903_upper
  lower := (Primitive.Addresses.material903 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v903_pa_checked.trans (by decide +kernel)
    · exact v903_pb_checked.trans (by decide +kernel)
    · exact v903_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 76 Primitive.Addresses.material903
    · exact v903_mb_checked.trans (by decide +kernel)
    · exact v903_mg_checked.trans (by decide +kernel)
  upper_error := v903_upper_checked
  lower_error := reuse_lower_error 9 76 Primitive.Addresses.material903

def v904_pa : Scalar.QComplex := ((999999556137982435100730788576 : Int)/10^30,(-942190977517991254532883531 : Int)/10^30)
theorem v904_pa_checked : Scalar.distance (sourceCoefficient 9 77 1 0) v904_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v904_pb : Scalar.QComplex := ((-406534140379930776273265 : Int)/10^30,(-431477237243130150251113842 : Int)/10^30)
theorem v904_pb_checked : Scalar.distance (sourceCoefficient 9 77 1 1) v904_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v904_pg : Scalar.QComplex := ((-93086378629461118621467 : Int)/10^30,(87705185003502188941 : Int)/10^30)
theorem v904_pg_checked : Scalar.distance (sourceCoefficient 9 77 1 2) v904_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v904_mb : Scalar.QComplex := ((-778879411736134039549680 : Int)/10^30,(-431476725763781710846961426 : Int)/10^30)
theorem v904_mb_checked : Scalar.distance (sourceCoefficient 9 77 3 1) v904_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v904_mg : Scalar.QComplex := ((-93086268283523534080887 : Int)/10^30,(168034504649216201605 : Int)/10^30)
theorem v904_mg_checked : Scalar.distance (sourceCoefficient 9 77 3 2) v904_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v904_upper : Scalar.QComplex := ((999996440619959468865087635070 : Int)/10^30,(-2668098088878292512860353684 : Int)/10^30)
theorem v904_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 77 5) 1) 14) v904_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material904 : Material (9 : Basis) (77 : Basis) where
  plus := ![v904_pa,v904_pb,v904_pg]
  minus := ![(Primitive.Addresses.material904 1).one,v904_mb,v904_mg]
  upper := v904_upper
  lower := (Primitive.Addresses.material904 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v904_pa_checked.trans (by decide +kernel)
    · exact v904_pb_checked.trans (by decide +kernel)
    · exact v904_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 77 Primitive.Addresses.material904
    · exact v904_mb_checked.trans (by decide +kernel)
    · exact v904_mg_checked.trans (by decide +kernel)
  upper_error := v904_upper_checked
  lower_error := reuse_lower_error 9 77 Primitive.Addresses.material904

def v905_pa : Scalar.QComplex := ((999999539688827699336118900597 : Int)/10^30,(-959490558950400729469227714 : Int)/10^30)
theorem v905_pa_checked : Scalar.distance (sourceCoefficient 9 78 1 0) v905_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v905_pb : Scalar.QComplex := ((-413998516570568996036417 : Int)/10^30,(-431477227306232888558323772 : Int)/10^30)
theorem v905_pb_checked : Scalar.distance (sourceCoefficient 9 78 1 1) v905_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v905_pg : Scalar.QComplex := ((-93086376791977564470275 : Int)/10^30,(89315540811743459385 : Int)/10^30)
theorem v905_pg_checked : Scalar.distance (sourceCoefficient 9 78 1 2) v905_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v905_mb : Scalar.QComplex := ((-786343776572349069091988 : Int)/10^30,(-431476709385467679618302752 : Int)/10^30)
theorem v905_mb_checked : Scalar.distance (sourceCoefficient 9 78 3 1) v905_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v905_mg : Scalar.QComplex := ((-93086265056376129329830 : Int)/10^30,(169644858272182857700 : Int)/10^30)
theorem v905_mg_checked : Scalar.distance (sourceCoefficient 9 78 3 2) v905_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v905_upper : Scalar.QComplex := ((999996394313321085613470590470 : Int)/10^30,(-2685397616155258777539745767 : Int)/10^30)
theorem v905_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 78 5) 1) 14) v905_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material905 : Material (9 : Basis) (78 : Basis) where
  plus := ![v905_pa,v905_pb,v905_pg]
  minus := ![(Primitive.Addresses.material905 1).one,v905_mb,v905_mg]
  upper := v905_upper
  lower := (Primitive.Addresses.material905 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v905_pa_checked.trans (by decide +kernel)
    · exact v905_pb_checked.trans (by decide +kernel)
    · exact v905_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 78 Primitive.Addresses.material905
    · exact v905_mb_checked.trans (by decide +kernel)
    · exact v905_mg_checked.trans (by decide +kernel)
  upper_error := v905_upper_checked
  lower_error := reuse_lower_error 9 78 Primitive.Addresses.material905

def v906_pa : Scalar.QComplex := ((999999534322119156813423160502 : Int)/10^30,(-965067637438166531267657617 : Int)/10^30)
theorem v906_pa_checked : Scalar.distance (sourceCoefficient 9 79 1 0) v906_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v906_pb : Scalar.QComplex := ((-416404899148355440168545 : Int)/10^30,(-431477224066053261976223982 : Int)/10^30)
theorem v906_pb_checked : Scalar.distance (sourceCoefficient 9 79 1 1) v906_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v906_pg : Scalar.QComplex := ((-93086376192677507235122 : Int)/10^30,(89834690983976196796 : Int)/10^30)
theorem v906_pg_checked : Scalar.distance (sourceCoefficient 9 79 1 2) v906_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v906_mb : Scalar.QComplex := ((-788750155458000216930206 : Int)/10^30,(-431476704068689474321529452 : Int)/10^30)
theorem v906_mb_checked : Scalar.distance (sourceCoefficient 9 79 3 1) v906_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v906_mg : Scalar.QComplex := ((-93086264009073078260415 : Int)/10^30,(170164007733943301731 : Int)/10^30)
theorem v906_mg_checked : Scalar.distance (sourceCoefficient 9 79 3 2) v906_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v906_upper : Scalar.QComplex := ((999996379321089014897113643937 : Int)/10^30,(-2690974677074169221072167413 : Int)/10^30)
theorem v906_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 79 5) 1) 14) v906_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material906 : Material (9 : Basis) (79 : Basis) where
  plus := ![v906_pa,v906_pb,v906_pg]
  minus := ![(Primitive.Addresses.material906 1).one,v906_mb,v906_mg]
  upper := v906_upper
  lower := (Primitive.Addresses.material906 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v906_pa_checked.trans (by decide +kernel)
    · exact v906_pb_checked.trans (by decide +kernel)
    · exact v906_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 79 Primitive.Addresses.material906
    · exact v906_mb_checked.trans (by decide +kernel)
    · exact v906_mg_checked.trans (by decide +kernel)
  upper_error := v906_upper_checked
  lower_error := reuse_lower_error 9 79 Primitive.Addresses.material906

def v907_pa : Scalar.QComplex := ((999999525876547304755694436042 : Int)/10^30,(-973779585223186025417927753 : Int)/10^30)
theorem v907_pa_checked : Scalar.distance (sourceCoefficient 9 80 1 0) v907_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v907_pb : Scalar.QComplex := ((-420163906530218924169814 : Int)/10^30,(-431477218968764041793392613 : Int)/10^30)
theorem v907_pb_checked : Scalar.distance (sourceCoefficient 9 80 1 1) v907_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v907_pg : Scalar.QComplex := ((-93086375249751980864148 : Int)/10^30,(90645654857864186423 : Int)/10^30)
theorem v907_pg_checked : Scalar.distance (sourceCoefficient 9 80 1 2) v907_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v907_mb : Scalar.QComplex := ((-792509157041482433906026 : Int)/10^30,(-431476695727548080952035390 : Int)/10^30)
theorem v907_mb_checked : Scalar.distance (sourceCoefficient 9 80 3 1) v907_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v907_mg : Scalar.QComplex := ((-93086262366322604275401 : Int)/10^30,(170974970492170116762 : Int)/10^30)
theorem v907_mg_checked : Scalar.distance (sourceCoefficient 9 80 3 2) v907_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v907_upper : Scalar.QComplex := ((999996355839498206312171284517 : Int)/10^30,(-2699686597307475026352800230 : Int)/10^30)
theorem v907_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 80 5) 1) 14) v907_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material907 : Material (9 : Basis) (80 : Basis) where
  plus := ![v907_pa,v907_pb,v907_pg]
  minus := ![(Primitive.Addresses.material907 1).one,v907_mb,v907_mg]
  upper := v907_upper
  lower := (Primitive.Addresses.material907 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v907_pa_checked.trans (by decide +kernel)
    · exact v907_pb_checked.trans (by decide +kernel)
    · exact v907_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 80 Primitive.Addresses.material907
    · exact v907_mb_checked.trans (by decide +kernel)
    · exact v907_mg_checked.trans (by decide +kernel)
  upper_error := v907_upper_checked
  lower_error := reuse_lower_error 9 80 Primitive.Addresses.material907

def v908_pa : Scalar.QComplex := ((999999499988163043476251371920 : Int)/10^30,(-1000011711882021110071235156 : Int)/10^30)
theorem v908_pa_checked : Scalar.distance (sourceCoefficient 9 81 1 0) v908_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v908_pb : Scalar.QComplex := ((-431482472513327812603616 : Int)/10^30,(-431477203356883602332672079 : Int)/10^30)
theorem v908_pb_checked : Scalar.distance (sourceCoefficient 9 81 1 1) v908_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v908_pg : Scalar.QComplex := ((-93086372360779383920310 : Int)/10^30,(93087509122246680412 : Int)/10^30)
theorem v908_pg_checked : Scalar.distance (sourceCoefficient 9 81 1 2) v908_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v908_mb : Scalar.QComplex := ((-803827705337822236547480 : Int)/10^30,(-431476670348260780373283665 : Int)/10^30)
theorem v908_mb_checked : Scalar.distance (sourceCoefficient 9 81 3 1) v908_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v908_mg : Scalar.QComplex := ((-93086257370140829899530 : Int)/10^30,(173416821354285433200 : Int)/10^30)
theorem v908_mg_checked : Scalar.distance (sourceCoefficient 9 81 3 2) v908_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v908_upper : Scalar.QComplex := ((999996284676881649531491078180 : Int)/10^30,(-2725918640215636235633890898 : Int)/10^30)
theorem v908_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 81 5) 1) 14) v908_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material908 : Material (9 : Basis) (81 : Basis) where
  plus := ![v908_pa,v908_pb,v908_pg]
  minus := ![(Primitive.Addresses.material908 1).one,v908_mb,v908_mg]
  upper := v908_upper
  lower := (Primitive.Addresses.material908 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v908_pa_checked.trans (by decide +kernel)
    · exact v908_pb_checked.trans (by decide +kernel)
    · exact v908_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 81 Primitive.Addresses.material908
    · exact v908_mb_checked.trans (by decide +kernel)
    · exact v908_mg_checked.trans (by decide +kernel)
  upper_error := v908_upper_checked
  lower_error := reuse_lower_error 9 81 Primitive.Addresses.material908

def v909_pa : Scalar.QComplex := ((999999489998383371524200249937 : Int)/10^30,(-1009951965766344075707620228 : Int)/10^30)
theorem v909_pa_checked : Scalar.distance (sourceCoefficient 9 82 1 0) v909_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v909_pb : Scalar.QComplex := ((-435771465878590687472621 : Int)/10^30,(-431477197337576955799190333 : Int)/10^30)
theorem v909_pb_checked : Scalar.distance (sourceCoefficient 9 82 1 1) v909_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v909_pg : Scalar.QComplex := ((-93086371246524006578806 : Int)/10^30,(94012811573168495102 : Int)/10^30)
theorem v909_pg_checked : Scalar.distance (sourceCoefficient 9 82 1 2) v909_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v909_mb : Scalar.QComplex := ((-808116691911706328398182 : Int)/10^30,(-431476660627748269971299054 : Int)/10^30)
theorem v909_mb_checked : Scalar.distance (sourceCoefficient 9 82 3 1) v909_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v909_mg : Scalar.QComplex := ((-93086255457391526376076 : Int)/10^30,(174342122499122650555 : Int)/10^30)
theorem v909_mg_checked : Scalar.distance (sourceCoefficient 9 82 3 2) v909_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v909_upper : Scalar.QComplex := ((999996257531140424629464023911 : Int)/10^30,(-2735858862053665256759650603 : Int)/10^30)
theorem v909_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 82 5) 1) 14) v909_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material909 : Material (9 : Basis) (82 : Basis) where
  plus := ![v909_pa,v909_pb,v909_pg]
  minus := ![(Primitive.Addresses.material909 1).one,v909_mb,v909_mg]
  upper := v909_upper
  lower := (Primitive.Addresses.material909 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v909_pa_checked.trans (by decide +kernel)
    · exact v909_pb_checked.trans (by decide +kernel)
    · exact v909_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 82 Primitive.Addresses.material909
    · exact v909_mb_checked.trans (by decide +kernel)
    · exact v909_mg_checked.trans (by decide +kernel)
  upper_error := v909_upper_checked
  lower_error := reuse_lower_error 9 82 Primitive.Addresses.material909

def v910_pa : Scalar.QComplex := ((999999476202674414800838641896 : Int)/10^30,(-1023520579571686009638232469 : Int)/10^30)
theorem v910_pa_checked : Scalar.distance (sourceCoefficient 9 83 1 0) v910_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v910_pb : Scalar.QComplex := ((-441626013909823723274430 : Int)/10^30,(-431477189029366116937331723 : Int)/10^30)
theorem v910_pb_checked : Scalar.distance (sourceCoefficient 9 83 1 1) v910_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v910_pg : Scalar.QComplex := ((-93086369708225753374634 : Int)/10^30,(95275864979230728345 : Int)/10^30)
theorem v910_pg_checked : Scalar.distance (sourceCoefficient 9 83 1 2) v910_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v910_mb : Scalar.QComplex := ((-813971230593411800096762 : Int)/10^30,(-431476647267329252737029960 : Int)/10^30)
theorem v910_mb_checked : Scalar.distance (sourceCoefficient 9 83 3 1) v910_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v910_mg : Scalar.QComplex := ((-93086252829135642332648 : Int)/10^30,(175605174107410266195 : Int)/10^30)
theorem v910_mg_checked : Scalar.distance (sourceCoefficient 9 83 3 2) v910_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v910_upper : Scalar.QComplex := ((999996220317255522002741538840 : Int)/10^30,(-2749427431840008686610647031 : Int)/10^30)
theorem v910_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 83 5) 1) 14) v910_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material910 : Material (9 : Basis) (83 : Basis) where
  plus := ![v910_pa,v910_pb,v910_pg]
  minus := ![(Primitive.Addresses.material910 1).one,v910_mb,v910_mg]
  upper := v910_upper
  lower := (Primitive.Addresses.material910 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v910_pa_checked.trans (by decide +kernel)
    · exact v910_pb_checked.trans (by decide +kernel)
    · exact v910_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 83 Primitive.Addresses.material910
    · exact v910_mb_checked.trans (by decide +kernel)
    · exact v910_mg_checked.trans (by decide +kernel)
  upper_error := v910_upper_checked
  lower_error := reuse_lower_error 9 83 Primitive.Addresses.material910

def v911_pa : Scalar.QComplex := ((999999439619749898545373535034 : Int)/10^30,(-1058659617713306635768410856 : Int)/10^30)
theorem v911_pa_checked : Scalar.distance (sourceCoefficient 9 84 1 0) v911_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v911_pb : Scalar.QComplex := ((-456787708665304535860974 : Int)/10^30,(-431477167021020491337563229 : Int)/10^30)
theorem v911_pb_checked : Scalar.distance (sourceCoefficient 9 84 1 1) v911_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v911_pg : Scalar.QComplex := ((-93086365631512093017229 : Int)/10^30,(98546831477475747883 : Int)/10^30)
theorem v911_pg_checked : Scalar.distance (sourceCoefficient 9 84 1 2) v911_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v911_mb : Scalar.QComplex := ((-829132900711289675734945 : Int)/10^30,(-431476612175132105253156966 : Int)/10^30)
theorem v911_mb_checked : Scalar.distance (sourceCoefficient 9 84 3 1) v911_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v911_mg : Scalar.QComplex := ((-93086245929726730798949 : Int)/10^30,(178876135869704687361 : Int)/10^30)
theorem v911_mg_checked : Scalar.distance (sourceCoefficient 9 84 3 2) v911_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v911_upper : Scalar.QComplex := ((999996123087593447917380049548 : Int)/10^30,(-2784566354507350784103948418 : Int)/10^30)
theorem v911_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 84 5) 1) 14) v911_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material911 : Material (9 : Basis) (84 : Basis) where
  plus := ![v911_pa,v911_pb,v911_pg]
  minus := ![(Primitive.Addresses.material911 1).one,v911_mb,v911_mg]
  upper := v911_upper
  lower := (Primitive.Addresses.material911 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v911_pa_checked.trans (by decide +kernel)
    · exact v911_pb_checked.trans (by decide +kernel)
    · exact v911_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 84 Primitive.Addresses.material911
    · exact v911_mb_checked.trans (by decide +kernel)
    · exact v911_mg_checked.trans (by decide +kernel)
  upper_error := v911_upper_checked
  lower_error := reuse_lower_error 9 84 Primitive.Addresses.material911

def v912_pa : Scalar.QComplex := ((999999352800501411497250864698 : Int)/10^30,(-1137716387466496205896528241 : Int)/10^30)
theorem v912_pa_checked : Scalar.distance (sourceCoefficient 9 85 1 0) v912_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v912_pb : Scalar.QComplex := ((-490898902158410252664699 : Int)/10^30,(-431477114909134626940046261 : Int)/10^30)
theorem v912_pb_checked : Scalar.distance (sourceCoefficient 9 85 1 1) v912_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v912_pg : Scalar.QComplex := ((-93086355969387982685977 : Int)/10^30,(105905941178184438208 : Int)/10^30)
theorem v912_pg_checked : Scalar.distance (sourceCoefficient 9 85 1 2) v912_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v912_mb : Scalar.QComplex := ((-863244036533028627737006 : Int)/10^30,(-431476530626841971066524352 : Int)/10^30)
theorem v912_mb_checked : Scalar.distance (sourceCoefficient 9 85 3 1) v912_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v912_mg : Scalar.QComplex := ((-93086229917025988403700 : Int)/10^30,(186235234492302566884 : Int)/10^30)
theorem v912_mg_checked : Scalar.distance (sourceCoefficient 9 85 3 2) v912_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v912_upper : Scalar.QComplex := ((999995899823661648063797464112 : Int)/10^30,(-2863622856672621759436070619 : Int)/10^30)
theorem v912_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 85 5) 1) 14) v912_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material912 : Material (9 : Basis) (85 : Basis) where
  plus := ![v912_pa,v912_pb,v912_pg]
  minus := ![(Primitive.Addresses.material912 1).one,v912_mb,v912_mg]
  upper := v912_upper
  lower := (Primitive.Addresses.material912 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v912_pa_checked.trans (by decide +kernel)
    · exact v912_pb_checked.trans (by decide +kernel)
    · exact v912_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 85 Primitive.Addresses.material912
    · exact v912_mb_checked.trans (by decide +kernel)
    · exact v912_mg_checked.trans (by decide +kernel)
  upper_error := v912_upper_checked
  lower_error := reuse_lower_error 9 85 Primitive.Addresses.material912

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
