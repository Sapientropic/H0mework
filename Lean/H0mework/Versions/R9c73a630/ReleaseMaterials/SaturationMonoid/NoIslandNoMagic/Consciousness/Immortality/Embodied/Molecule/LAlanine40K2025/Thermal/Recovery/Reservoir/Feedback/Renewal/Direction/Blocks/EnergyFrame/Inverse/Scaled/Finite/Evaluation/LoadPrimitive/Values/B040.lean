import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B026
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B027

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v641_pa : Scalar.QComplex := ((999999611864264710036604534926 : Int)/10^30,(-881062608405655688480344539 : Int)/10^30)
theorem v641_pa_checked : Scalar.distance (sourceCoefficient 6 81 1 0) v641_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v641_pb : Scalar.QComplex := ((-380158601501801754888509 : Int)/10^30,(-431477230246539121409689842 : Int)/10^30)
theorem v641_pb_checked : Scalar.distance (sourceCoefficient 6 81 1 1) v641_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v641_pg : Scalar.QComplex := ((-93086380468423343468201 : Int)/10^30,(82014961015487550925 : Int)/10^30)
theorem v641_pg_checked : Scalar.distance (sourceCoefficient 6 81 1 2) v641_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v641_mb : Scalar.QComplex := ((-752503876641080621040309 : Int)/10^30,(-431476741528095428807710456 : Int)/10^30)
theorem v641_mb_checked : Scalar.distance (sourceCoefficient 6 81 3 1) v641_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v641_mg : Scalar.QComplex := ((-93086275032892097679645 : Int)/10^30,(162344284366873586669 : Int)/10^30)
theorem v641_mg_checked : Scalar.distance (sourceCoefficient 6 81 3 2) v641_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v641_upper : Scalar.QComplex := ((999996601848178311614140866091 : Int)/10^30,(-2606969906987989854685405759 : Int)/10^30)
theorem v641_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 81 5) 1) 14) v641_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material641 : Material (6 : Basis) (81 : Basis) where
  plus := ![v641_pa,v641_pb,v641_pg]
  minus := ![(Primitive.Addresses.material641 1).one,v641_mb,v641_mg]
  upper := v641_upper
  lower := (Primitive.Addresses.material641 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v641_pa_checked.trans (by decide +kernel)
    · exact v641_pb_checked.trans (by decide +kernel)
    · exact v641_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 81 Primitive.Addresses.material641
    · exact v641_mb_checked.trans (by decide +kernel)
    · exact v641_mg_checked.trans (by decide +kernel)
  upper_error := v641_upper_checked
  lower_error := reuse_lower_error 6 81 Primitive.Addresses.material641

def v642_pa : Scalar.QComplex := ((999999603056869917508173533466 : Int)/10^30,(-891002863407932675790196052 : Int)/10^30)
theorem v642_pa_checked : Scalar.distance (sourceCoefficient 6 82 1 0) v642_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v642_pb : Scalar.QComplex := ((-384447595188645930431276 : Int)/10^30,(-431477224567347416933216567 : Int)/10^30)
theorem v642_pb_checked : Scalar.distance (sourceCoefficient 6 82 1 1) v642_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v642_pg : Scalar.QComplex := ((-93086379445887946722827 : Int)/10^30,(82940263553131314601 : Int)/10^30)
theorem v642_pg_checked : Scalar.distance (sourceCoefficient 6 82 1 2) v642_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v642_mb : Scalar.QComplex := ((-756792863830049770612205 : Int)/10^30,(-431476732147697456312218371 : Int)/10^30)
theorem v642_mb_checked : Scalar.distance (sourceCoefficient 6 82 3 1) v642_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v642_mg : Scalar.QComplex := ((-93086273211862665763645 : Int)/10^30,(163269585677582933058 : Int)/10^30)
theorem v642_mg_checked : Scalar.distance (sourceCoefficient 6 82 3 2) v642_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v642_upper : Scalar.QComplex := ((999996575884818275625127303673 : Int)/10^30,(-2616910131984660269190256865 : Int)/10^30)
theorem v642_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 82 5) 1) 14) v642_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material642 : Material (6 : Basis) (82 : Basis) where
  plus := ![v642_pa,v642_pb,v642_pg]
  minus := ![(Primitive.Addresses.material642 1).one,v642_mb,v642_mg]
  upper := v642_upper
  lower := (Primitive.Addresses.material642 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v642_pa_checked.trans (by decide +kernel)
    · exact v642_pb_checked.trans (by decide +kernel)
    · exact v642_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 82 Primitive.Addresses.material642
    · exact v642_mb_checked.trans (by decide +kernel)
    · exact v642_mg_checked.trans (by decide +kernel)
  upper_error := v642_upper_checked
  lower_error := reuse_lower_error 6 82 Primitive.Addresses.material642

def v643_pa : Scalar.QComplex := ((999999590875136216959403114367 : Int)/10^30,(-904571478758272053159278529 : Int)/10^30)
theorem v643_pa_checked : Scalar.distance (sourceCoefficient 6 83 1 0) v643_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v643_pb : Scalar.QComplex := ((-390302143664300003495943 : Int)/10^30,(-431477216723399195651136576 : Int)/10^30)
theorem v643_pb_checked : Scalar.distance (sourceCoefficient 6 83 1 1) v643_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v643_pg : Scalar.QComplex := ((-93086378032789010164031 : Int)/10^30,(84203317079042116422 : Int)/10^30)
theorem v643_pg_checked : Scalar.distance (sourceCoefficient 6 83 1 2) v643_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v643_mb : Scalar.QComplex := ((-762647403356813843454634 : Int)/10^30,(-431476719251540500276198342 : Int)/10^30)
theorem v643_mb_checked : Scalar.distance (sourceCoefficient 6 83 3 1) v643_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v643_mg : Scalar.QComplex := ((-93086270708805948324248 : Int)/10^30,(164532637513760444148 : Int)/10^30)
theorem v643_mg_checked : Scalar.distance (sourceCoefficient 6 83 3 2) v643_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v643_upper : Scalar.QComplex := ((999996540284903558821016485502 : Int)/10^30,(-2630478706101573714853383959 : Int)/10^30)
theorem v643_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 83 5) 1) 14) v643_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material643 : Material (6 : Basis) (83 : Basis) where
  plus := ![v643_pa,v643_pb,v643_pg]
  minus := ![(Primitive.Addresses.material643 1).one,v643_mb,v643_mg]
  upper := v643_upper
  lower := (Primitive.Addresses.material643 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v643_pa_checked.trans (by decide +kernel)
    · exact v643_pb_checked.trans (by decide +kernel)
    · exact v643_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 83 Primitive.Addresses.material643
    · exact v643_mb_checked.trans (by decide +kernel)
    · exact v643_mg_checked.trans (by decide +kernel)
  upper_error := v643_upper_checked
  lower_error := reuse_lower_error 6 83 Primitive.Addresses.material643

def v644_pa : Scalar.QComplex := ((999999558471970884812251212644 : Int)/10^30,(-939710521002811271191792702 : Int)/10^30)
theorem v644_pa_checked : Scalar.distance (sourceCoefficient 6 84 1 0) v644_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v644_pb : Scalar.QComplex := ((-405463839599992040860723 : Int)/10^30,(-431477195917368116163534505 : Int)/10^30)
theorem v644_pb_checked : Scalar.distance (sourceCoefficient 6 84 1 1) v644_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v644_pg : Scalar.QComplex := ((-93086374280307700725395 : Int)/10^30,(87474283895558807200 : Int)/10^30)
theorem v644_pg_checked : Scalar.distance (sourceCoefficient 6 84 1 2) v644_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v644_mb : Scalar.QComplex := ((-777809075692445807482269 : Int)/10^30,(-431476685361656432758705523 : Int)/10^30)
theorem v644_mb_checked : Scalar.distance (sourceCoefficient 6 84 3 1) v644_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v644_mg : Scalar.QComplex := ((-93086264133628992328679 : Int)/10^30,(167803599874124334007 : Int)/10^30)
theorem v644_mg_checked : Scalar.distance (sourceCoefficient 6 84 3 2) v644_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v644_upper : Scalar.QComplex := ((999996447234987362318376719530 : Int)/10^30,(-2665617640085713460413536491 : Int)/10^30)
theorem v644_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 84 5) 1) 14) v644_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material644 : Material (6 : Basis) (84 : Basis) where
  plus := ![v644_pa,v644_pb,v644_pg]
  minus := ![(Primitive.Addresses.material644 1).one,v644_mb,v644_mg]
  upper := v644_upper
  lower := (Primitive.Addresses.material644 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v644_pa_checked.trans (by decide +kernel)
    · exact v644_pb_checked.trans (by decide +kernel)
    · exact v644_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 84 Primitive.Addresses.material644
    · exact v644_mb_checked.trans (by decide +kernel)
    · exact v644_mg_checked.trans (by decide +kernel)
  upper_error := v644_upper_checked
  lower_error := reuse_lower_error 6 84 Primitive.Addresses.material644

def v645_pa : Scalar.QComplex := ((999999481056459040531520800001 : Int)/10^30,(-1018767300523793929474424171 : Int)/10^30)
theorem v645_pa_checked : Scalar.distance (sourceCoefficient 6 85 1 0) v645_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v645_pb : Scalar.QComplex := ((-439575035902819327871746 : Int)/10^30,(-431477146510482392817338835 : Int)/10^30)
theorem v645_pb_checked : Scalar.distance (sourceCoefficient 6 85 1 1) v645_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v645_pg : Scalar.QComplex := ((-93086365347650403471874 : Int)/10^30,(94833394353974903232 : Int)/10^30)
theorem v645_pg_checked : Scalar.distance (sourceCoefficient 6 85 1 2) v645_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v645_mb : Scalar.QComplex := ((-811920216658198576547307 : Int)/10^30,(-431476606518363007765047151 : Int)/10^30)
theorem v645_mb_checked : Scalar.distance (sourceCoefficient 6 85 3 1) v645_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v645_mg : Scalar.QComplex := ((-93086248850394137529962 : Int)/10^30,(175162699883926342829 : Int)/10^30)
theorem v645_mg_checked : Scalar.distance (sourceCoefficient 6 85 3 2) v645_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v645_upper : Scalar.QComplex := ((999996233374761341146354604797 : Int)/10^30,(-2744674168248759321012114745 : Int)/10^30)
theorem v645_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 85 5) 1) 14) v645_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material645 : Material (6 : Basis) (85 : Basis) where
  plus := ![v645_pa,v645_pb,v645_pg]
  minus := ![(Primitive.Addresses.material645 1).one,v645_mb,v645_mg]
  upper := v645_upper
  lower := (Primitive.Addresses.material645 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v645_pa_checked.trans (by decide +kernel)
    · exact v645_pb_checked.trans (by decide +kernel)
    · exact v645_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 85 Primitive.Addresses.material645
    · exact v645_mb_checked.trans (by decide +kernel)
    · exact v645_mg_checked.trans (by decide +kernel)
  upper_error := v645_upper_checked
  lower_error := reuse_lower_error 6 85 Primitive.Addresses.material645

def v646_pa : Scalar.QComplex := ((999999466091744675011793507536 : Int)/10^30,(-1033351936946919991020113261 : Int)/10^30)
theorem v646_pa_checked : Scalar.distance (sourceCoefficient 6 86 1 0) v646_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v646_pb : Scalar.QComplex := ((-445867973322845338847752 : Int)/10^30,(-431477137002895468580073776 : Int)/10^30)
theorem v646_pb_checked : Scalar.distance (sourceCoefficient 6 86 1 1) v646_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v646_pg : Scalar.QComplex := ((-93086363625566909051594 : Int)/10^30,(96191025513007492746 : Int)/10^30)
theorem v646_pg_checked : Scalar.distance (sourceCoefficient 6 86 1 2) v646_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v646_mb : Scalar.QComplex := ((-818213143530457074802295 : Int)/10^30,(-431476591580258053534692247 : Int)/10^30)
theorem v646_mb_checked : Scalar.distance (sourceCoefficient 6 86 3 1) v646_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v646_mg : Scalar.QComplex := ((-93086245956736739512523 : Int)/10^30,(176520329051370309102 : Int)/10^30)
theorem v646_mg_checked : Scalar.distance (sourceCoefficient 6 86 3 2) v646_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v646_upper : Scalar.QComplex := ((999996193238309905375968122772 : Int)/10^30,(-2759258757122043255449054445 : Int)/10^30)
theorem v646_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 86 5) 1) 14) v646_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material646 : Material (6 : Basis) (86 : Basis) where
  plus := ![v646_pa,v646_pb,v646_pg]
  minus := ![(Primitive.Addresses.material646 1).one,v646_mb,v646_mg]
  upper := v646_upper
  lower := (Primitive.Addresses.material646 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v646_pa_checked.trans (by decide +kernel)
    · exact v646_pb_checked.trans (by decide +kernel)
    · exact v646_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 86 Primitive.Addresses.material646
    · exact v646_mb_checked.trans (by decide +kernel)
    · exact v646_mg_checked.trans (by decide +kernel)
  upper_error := v646_upper_checked
  lower_error := reuse_lower_error 6 86 Primitive.Addresses.material646

def v647_pa : Scalar.QComplex := ((999999465093312044187286544210 : Int)/10^30,(-1034317692871228325801154287 : Int)/10^30)
theorem v647_pa_checked : Scalar.distance (sourceCoefficient 6 87 1 0) v647_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v647_pb : Scalar.QComplex := ((-446284674936534455086675 : Int)/10^30,(-431477136369008368666946049 : Int)/10^30)
theorem v647_pb_checked : Scalar.distance (sourceCoefficient 6 87 1 1) v647_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v647_pg : Scalar.QComplex := ((-93086363510719631347759 : Int)/10^30,(96280924245490324471 : Int)/10^30)
theorem v647_pg_checked : Scalar.distance (sourceCoefficient 6 87 1 2) v647_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v647_mb : Scalar.QComplex := ((-818629844441973118050366 : Int)/10^30,(-431476590586776464576991152 : Int)/10^30)
theorem v647_mb_checked : Scalar.distance (sourceCoefficient 6 87 3 1) v647_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v647_mg : Scalar.QComplex := ((-93086245764310947327503 : Int)/10^30,(176610227651271706020 : Int)/10^30)
theorem v647_mg_checked : Scalar.distance (sourceCoefficient 6 87 3 2) v647_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v647_upper : Scalar.QComplex := ((999996190573071648936455257213 : Int)/10^30,(-2760224509884767442930442938 : Int)/10^30)
theorem v647_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 87 5) 1) 14) v647_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material647 : Material (6 : Basis) (87 : Basis) where
  plus := ![v647_pa,v647_pb,v647_pg]
  minus := ![(Primitive.Addresses.material647 1).one,v647_mb,v647_mg]
  upper := v647_upper
  lower := (Primitive.Addresses.material647 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v647_pa_checked.trans (by decide +kernel)
    · exact v647_pb_checked.trans (by decide +kernel)
    · exact v647_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 87 Primitive.Addresses.material647
    · exact v647_mb_checked.trans (by decide +kernel)
    · exact v647_mg_checked.trans (by decide +kernel)
  upper_error := v647_upper_checked
  lower_error := reuse_lower_error 6 87 Primitive.Addresses.material647

def v648_pa : Scalar.QComplex := ((999999452861012385790292966882 : Int)/10^30,(-1046077280064598117722115248 : Int)/10^30)
theorem v648_pa_checked : Scalar.distance (sourceCoefficient 6 88 1 0) v648_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v648_pb : Scalar.QComplex := ((-451358668059633344704799 : Int)/10^30,(-431477128607396999685051392 : Int)/10^30)
theorem v648_pb_checked : Scalar.distance (sourceCoefficient 6 88 1 1) v648_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v648_pg : Scalar.QComplex := ((-93086362104148815186596 : Int)/10^30,(97375581758993495044 : Int)/10^30)
theorem v648_pg_checked : Scalar.distance (sourceCoefficient 6 88 1 2) v648_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v648_mb : Scalar.QComplex := ((-823703828977871433565340 : Int)/10^30,(-431476578446540444530439126 : Int)/10^30)
theorem v648_mb_checked : Scalar.distance (sourceCoefficient 6 88 3 1) v648_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v648_mg : Scalar.QComplex := ((-93086243413100522287952 : Int)/10^30,(177704883543376591246 : Int)/10^30)
theorem v648_mg_checked : Scalar.distance (sourceCoefficient 6 88 3 2) v648_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v648_upper : Scalar.QComplex := ((999996158044809534773266084258 : Int)/10^30,(-2771984058451773983638609216 : Int)/10^30)
theorem v648_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 88 5) 1) 14) v648_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material648 : Material (6 : Basis) (88 : Basis) where
  plus := ![v648_pa,v648_pb,v648_pg]
  minus := ![(Primitive.Addresses.material648 1).one,v648_mb,v648_mg]
  upper := v648_upper
  lower := (Primitive.Addresses.material648 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v648_pa_checked.trans (by decide +kernel)
    · exact v648_pb_checked.trans (by decide +kernel)
    · exact v648_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 88 Primitive.Addresses.material648
    · exact v648_mb_checked.trans (by decide +kernel)
    · exact v648_mg_checked.trans (by decide +kernel)
  upper_error := v648_upper_checked
  lower_error := reuse_lower_error 6 88 Primitive.Addresses.material648

def v649_pa : Scalar.QComplex := ((999999435900732489104353187806 : Int)/10^30,(-1062166755652711853078731204 : Int)/10^30)
theorem v649_pa_checked : Scalar.distance (sourceCoefficient 6 89 1 0) v649_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v649_pb : Scalar.QComplex := ((-458300908941952527132597 : Int)/10^30,(-431477117859064666583950390 : Int)/10^30)
theorem v649_pb_checked : Scalar.distance (sourceCoefficient 6 89 1 1) v649_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v649_pg : Scalar.QComplex := ((-93086360155346837250737 : Int)/10^30,(98873292936076738287 : Int)/10^30)
theorem v649_pg_checked : Scalar.distance (sourceCoefficient 6 89 1 2) v649_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v649_mb : Scalar.QComplex := ((-830646057999950342875509 : Int)/10^30,(-431476561707370899005832266 : Int)/10^30)
theorem v649_mb_checked : Scalar.distance (sourceCoefficient 6 89 3 1) v649_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v649_mg : Scalar.QComplex := ((-93086240171841978564685 : Int)/10^30,(179202592481065178303 : Int)/10^30)
theorem v649_mg_checked : Scalar.distance (sourceCoefficient 6 89 3 2) v649_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v649_upper : Scalar.QComplex := ((999996113315579659171013233300 : Int)/10^30,(-2788073480804599355961055089 : Int)/10^30)
theorem v649_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 89 5) 1) 14) v649_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material649 : Material (6 : Basis) (89 : Basis) where
  plus := ![v649_pa,v649_pb,v649_pg]
  minus := ![(Primitive.Addresses.material649 1).one,v649_mb,v649_mg]
  upper := v649_upper
  lower := (Primitive.Addresses.material649 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v649_pa_checked.trans (by decide +kernel)
    · exact v649_pb_checked.trans (by decide +kernel)
    · exact v649_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 89 Primitive.Addresses.material649
    · exact v649_mb_checked.trans (by decide +kernel)
    · exact v649_mg_checked.trans (by decide +kernel)
  upper_error := v649_upper_checked
  lower_error := reuse_lower_error 6 89 Primitive.Addresses.material649

def v650_pa : Scalar.QComplex := ((999999407725542055210213319445 : Int)/10^30,(-1088369682185490703301369919 : Int)/10^30)
theorem v650_pa_checked : Scalar.distance (sourceCoefficient 6 90 1 0) v650_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v650_pb : Scalar.QComplex := ((-469606872372460619792541 : Int)/10^30,(-431477100035822063170323313 : Int)/10^30)
theorem v650_pb_checked : Scalar.distance (sourceCoefficient 6 90 1 1) v650_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v650_pg : Scalar.QComplex := ((-93086356921400629138487 : Int)/10^30,(101312428703113748750 : Int)/10^30)
theorem v650_pg_checked : Scalar.distance (sourceCoefficient 6 90 1 2) v650_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v650_mb : Scalar.QComplex := ((-841952001840075904604814 : Int)/10^30,(-431476534127597693161959719 : Int)/10^30)
theorem v650_mb_checked : Scalar.distance (sourceCoefficient 6 90 3 1) v650_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v650_mg : Scalar.QComplex := ((-93086234833032662242420 : Int)/10^30,(181641724549150542617 : Int)/10^30)
theorem v650_mg_checked : Scalar.distance (sourceCoefficient 6 90 3 2) v650_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v650_upper : Scalar.QComplex := ((999996039916557104263120982574 : Int)/10^30,(-2814276319683374491986925536 : Int)/10^30)
theorem v650_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 90 5) 1) 14) v650_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material650 : Material (6 : Basis) (90 : Basis) where
  plus := ![v650_pa,v650_pb,v650_pg]
  minus := ![(Primitive.Addresses.material650 1).one,v650_mb,v650_mg]
  upper := v650_upper
  lower := (Primitive.Addresses.material650 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v650_pa_checked.trans (by decide +kernel)
    · exact v650_pb_checked.trans (by decide +kernel)
    · exact v650_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 90 Primitive.Addresses.material650
    · exact v650_mb_checked.trans (by decide +kernel)
    · exact v650_mg_checked.trans (by decide +kernel)
  upper_error := v650_upper_checked
  lower_error := reuse_lower_error 6 90 Primitive.Addresses.material650

def v651_pa : Scalar.QComplex := ((999999391551095372176784098080 : Int)/10^30,(-1103130744311650888459329423 : Int)/10^30)
theorem v651_pa_checked : Scalar.distance (sourceCoefficient 6 91 1 0) v651_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v651_pb : Scalar.QComplex := ((-475975932855147446341564 : Int)/10^30,(-431477089821405841471209651 : Int)/10^30)
theorem v651_pb_checked : Scalar.distance (sourceCoefficient 6 91 1 1) v651_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v651_pg : Scalar.QComplex := ((-93086355066767057990482 : Int)/10^30,(102686482629539235643 : Int)/10^30)
theorem v651_pg_checked : Scalar.distance (sourceCoefficient 6 91 1 2) v651_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v651_mb : Scalar.QComplex := ((-848321051136689273908602 : Int)/10^30,(-431476518416972930033795506 : Int)/10^30)
theorem v651_mb_checked : Scalar.distance (sourceCoefficient 6 91 3 1) v651_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v651_mg : Scalar.QComplex := ((-93086231792653128245623 : Int)/10^30,(183015776363487713029 : Int)/10^30)
theorem v651_mg_checked : Scalar.distance (sourceCoefficient 6 91 3 2) v651_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v651_upper : Scalar.QComplex := ((999995998265880394511070392432 : Int)/10^30,(-2829037331909038955815604093 : Int)/10^30)
theorem v651_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 91 5) 1) 14) v651_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material651 : Material (6 : Basis) (91 : Basis) where
  plus := ![v651_pa,v651_pb,v651_pg]
  minus := ![(Primitive.Addresses.material651 1).one,v651_mb,v651_mg]
  upper := v651_upper
  lower := (Primitive.Addresses.material651 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v651_pa_checked.trans (by decide +kernel)
    · exact v651_pb_checked.trans (by decide +kernel)
    · exact v651_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 91 Primitive.Addresses.material651
    · exact v651_mb_checked.trans (by decide +kernel)
    · exact v651_mg_checked.trans (by decide +kernel)
  upper_error := v651_upper_checked
  lower_error := reuse_lower_error 6 91 Primitive.Addresses.material651

def v652_pa : Scalar.QComplex := ((999999355788737881546428453807 : Int)/10^30,(-1135086828938102383636090025 : Int)/10^30)
theorem v652_pa_checked : Scalar.distance (sourceCoefficient 6 92 1 0) v652_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v652_pb : Scalar.QComplex := ((-489764251568740025431303 : Int)/10^30,(-431477067278877556083191337 : Int)/10^30)
theorem v652_pb_checked : Scalar.distance (sourceCoefficient 6 92 1 1) v652_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v652_pg : Scalar.QComplex := ((-93086350970623243552788 : Int)/10^30,(105661159008772588377 : Int)/10^30)
theorem v652_pg_checked : Scalar.distance (sourceCoefficient 6 92 1 2) v652_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v652_mb : Scalar.QComplex := ((-862109345263074006127441 : Int)/10^30,(-431476483975754991251058375 : Int)/10^30)
theorem v652_mb_checked : Scalar.distance (sourceCoefficient 6 92 3 1) v652_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v652_mg : Scalar.QComplex := ((-93086225129499098161846 : Int)/10^30,(185990448100325471958 : Int)/10^30)
theorem v652_mg_checked : Scalar.distance (sourceCoefficient 6 92 3 2) v652_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v652_upper : Scalar.QComplex := ((999995907350273135807280671686 : Int)/10^30,(-2860993307218071532185133508 : Int)/10^30)
theorem v652_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 92 5) 1) 14) v652_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material652 : Material (6 : Basis) (92 : Basis) where
  plus := ![v652_pa,v652_pb,v652_pg]
  minus := ![(Primitive.Addresses.material652 1).one,v652_mb,v652_mg]
  upper := v652_upper
  lower := (Primitive.Addresses.material652 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v652_pa_checked.trans (by decide +kernel)
    · exact v652_pb_checked.trans (by decide +kernel)
    · exact v652_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 92 Primitive.Addresses.material652
    · exact v652_mb_checked.trans (by decide +kernel)
    · exact v652_mg_checked.trans (by decide +kernel)
  upper_error := v652_upper_checked
  lower_error := reuse_lower_error 6 92 Primitive.Addresses.material652

def v653_pa : Scalar.QComplex := ((999999312020700023760066305021 : Int)/10^30,(-1173012415380571609912581545 : Int)/10^30)
theorem v653_pa_checked : Scalar.distance (sourceCoefficient 6 93 1 0) v653_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v653_pb : Scalar.QComplex := ((-506128272799390545977353 : Int)/10^30,(-431477039762966034427128669 : Int)/10^30)
theorem v653_pb_checked : Scalar.distance (sourceCoefficient 6 93 1 1) v653_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v653_pg : Scalar.QComplex := ((-93086345965393519614202 : Int)/10^30,(109191514641319585693 : Int)/10^30)
theorem v653_pg_checked : Scalar.distance (sourceCoefficient 6 93 1 2) v653_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v653_mb : Scalar.QComplex := ((-878473336655659177248265 : Int)/10^30,(-431476442338440401132194949 : Int)/10^30)
theorem v653_mb_checked : Scalar.distance (sourceCoefficient 6 93 3 1) v653_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v653_mg : Scalar.QComplex := ((-93086217077733328326261 : Int)/10^30,(189520798099071897473 : Int)/10^30)
theorem v653_mg_checked : Scalar.distance (sourceCoefficient 6 93 3 2) v653_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v653_upper : Scalar.QComplex := ((999995798126178847995774866072 : Int)/10^30,(-2898918761635172067576132846 : Int)/10^30)
theorem v653_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 93 5) 1) 14) v653_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material653 : Material (6 : Basis) (93 : Basis) where
  plus := ![v653_pa,v653_pb,v653_pg]
  minus := ![(Primitive.Addresses.material653 1).one,v653_mb,v653_mg]
  upper := v653_upper
  lower := (Primitive.Addresses.material653 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v653_pa_checked.trans (by decide +kernel)
    · exact v653_pb_checked.trans (by decide +kernel)
    · exact v653_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 93 Primitive.Addresses.material653
    · exact v653_mb_checked.trans (by decide +kernel)
    · exact v653_mg_checked.trans (by decide +kernel)
  upper_error := v653_upper_checked
  lower_error := reuse_lower_error 6 93 Primitive.Addresses.material653

def v654_pa : Scalar.QComplex := ((999999258467981220043448566244 : Int)/10^30,(-1217810940864869314707288691 : Int)/10^30)
theorem v654_pa_checked : Scalar.distance (sourceCoefficient 6 94 1 0) v654_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v654_pb : Scalar.QComplex := ((-525457808519143690372797 : Int)/10^30,(-431477006194559996990076827 : Int)/10^30)
theorem v654_pb_checked : Scalar.distance (sourceCoefficient 6 94 1 1) v654_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v654_pg : Scalar.QComplex := ((-93086339851874404797112 : Int)/10^30,(113361647177969232725 : Int)/10^30)
theorem v654_pg_checked : Scalar.distance (sourceCoefficient 6 94 1 2) v654_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v654_mb : Scalar.QComplex := ((-897802836210120224332893 : Int)/10^30,(-431476392089528106571640430 : Int)/10^30)
theorem v654_mb_checked : Scalar.distance (sourceCoefficient 6 94 3 1) v654_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v654_mg : Scalar.QComplex := ((-93086207365579926520494 : Int)/10^30,(193690923807298963231 : Int)/10^30)
theorem v654_mg_checked : Scalar.distance (sourceCoefficient 6 94 3 2) v654_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v654_upper : Scalar.QComplex := ((999995667255348909350235375692 : Int)/10^30,(-2943717127970194077460855912 : Int)/10^30)
theorem v654_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 94 5) 1) 14) v654_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material654 : Material (6 : Basis) (94 : Basis) where
  plus := ![v654_pa,v654_pb,v654_pg]
  minus := ![(Primitive.Addresses.material654 1).one,v654_mb,v654_mg]
  upper := v654_upper
  lower := (Primitive.Addresses.material654 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v654_pa_checked.trans (by decide +kernel)
    · exact v654_pb_checked.trans (by decide +kernel)
    · exact v654_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 94 Primitive.Addresses.material654
    · exact v654_mb_checked.trans (by decide +kernel)
    · exact v654_mg_checked.trans (by decide +kernel)
  upper_error := v654_upper_checked
  lower_error := reuse_lower_error 6 94 Primitive.Addresses.material654

def v655_pa : Scalar.QComplex := ((999999203570244535149314105126 : Int)/10^30,(-1262085130500057029329641582 : Int)/10^30)
theorem v655_pa_checked : Scalar.distance (sourceCoefficient 6 95 1 0) v655_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v655_pb : Scalar.QComplex := ((-544561104073485619176644 : Int)/10^30,(-431476971884658504356672168 : Int)/10^30)
theorem v655_pb_checked : Scalar.distance (sourceCoefficient 6 95 1 1) v655_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v655_pg : Scalar.QComplex := ((-93086333595769167728291 : Int)/10^30,(117482971050922078321 : Int)/10^30)
theorem v655_pg_checked : Scalar.distance (sourceCoefficient 6 95 1 2) v655_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v655_mb : Scalar.QComplex := ((-916906095043532426976013 : Int)/10^30,(-431476341294355706178459247 : Int)/10^30)
theorem v655_mb_checked : Scalar.distance (sourceCoefficient 6 95 3 1) v655_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v655_mg : Scalar.QComplex := ((-93086197552960134064056 : Int)/10^30,(197812240746957522051 : Int)/10^30)
theorem v655_mg_checked : Scalar.distance (sourceCoefficient 6 95 3 2) v655_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v655_upper : Scalar.QComplex := ((999995535944459200960504012000 : Int)/10^30,(-2987991156915663907763685221 : Int)/10^30)
theorem v655_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 95 5) 1) 14) v655_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material655 : Material (6 : Basis) (95 : Basis) where
  plus := ![v655_pa,v655_pb,v655_pg]
  minus := ![(Primitive.Addresses.material655 1).one,v655_mb,v655_mg]
  upper := v655_upper
  lower := (Primitive.Addresses.material655 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v655_pa_checked.trans (by decide +kernel)
    · exact v655_pb_checked.trans (by decide +kernel)
    · exact v655_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 95 Primitive.Addresses.material655
    · exact v655_mb_checked.trans (by decide +kernel)
    · exact v655_mg_checked.trans (by decide +kernel)
  upper_error := v655_upper_checked
  lower_error := reuse_lower_error 6 95 Primitive.Addresses.material655

def v656_pa : Scalar.QComplex := ((999999176507063619972331577627 : Int)/10^30,(-1283349209926682063816080803 : Int)/10^30)
theorem v656_pa_checked : Scalar.distance (sourceCoefficient 6 96 1 0) v656_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v656_pb : Scalar.QComplex := ((-553736065305448764503078 : Int)/10^30,(-431476955005368621723956278 : Int)/10^30)
theorem v656_pb_checked : Scalar.distance (sourceCoefficient 6 96 1 1) v656_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v656_pg : Scalar.QComplex := ((-93086330515403048858599 : Int)/10^30,(119462367098331966658 : Int)/10^30)
theorem v656_pg_checked : Scalar.distance (sourceCoefficient 6 96 1 2) v656_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v656_mb : Scalar.QComplex := ((-926081038293171235483388 : Int)/10^30,(-431476316497493790206851658 : Int)/10^30)
theorem v656_mb_checked : Scalar.distance (sourceCoefficient 6 96 3 1) v656_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v656_mg : Scalar.QComplex := ((-93086192764465521929338 : Int)/10^30,(199791633399130573024 : Int)/10^30)
theorem v656_mg_checked : Scalar.distance (sourceCoefficient 6 96 3 2) v656_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v656_upper : Scalar.QComplex := ((999995472181446565074196919720 : Int)/10^30,(-3009255157963345383524830234 : Int)/10^30)
theorem v656_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 96 5) 1) 14) v656_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material656 : Material (6 : Basis) (96 : Basis) where
  plus := ![v656_pa,v656_pb,v656_pg]
  minus := ![(Primitive.Addresses.material656 1).one,v656_mb,v656_mg]
  upper := v656_upper
  lower := (Primitive.Addresses.material656 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v656_pa_checked.trans (by decide +kernel)
    · exact v656_pb_checked.trans (by decide +kernel)
    · exact v656_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 96 Primitive.Addresses.material656
    · exact v656_mb_checked.trans (by decide +kernel)
    · exact v656_mg_checked.trans (by decide +kernel)
  upper_error := v656_upper_checked
  lower_error := reuse_lower_error 6 96 Primitive.Addresses.material656

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
