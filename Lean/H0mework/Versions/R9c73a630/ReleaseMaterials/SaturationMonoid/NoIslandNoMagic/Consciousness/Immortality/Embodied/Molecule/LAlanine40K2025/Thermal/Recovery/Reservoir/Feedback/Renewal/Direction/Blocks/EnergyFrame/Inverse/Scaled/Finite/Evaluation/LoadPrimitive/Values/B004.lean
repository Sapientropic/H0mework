import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B002
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B003

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v65_pa : Scalar.QComplex := ((999975344134120870621378523847 : Int)/10^30,(7022187967189179964284342476 : Int)/10^30)
theorem v65_pa_checked : Scalar.distance (sourceCoefficient 0 66 1 0) v65_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v65_pb : Scalar.QComplex := ((3029878330397612402096768 : Int)/10^30,(-431461481845896616738838423 : Int)/10^30)
theorem v65_pb_checked : Scalar.distance (sourceCoefficient 0 66 1 1) v65_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v65_pg : Scalar.QComplex := ((-93083552199223110168004 : Int)/10^30,(-653666316905649784232 : Int)/10^30)
theorem v65_pg_checked : Scalar.distance (sourceCoefficient 0 66 1 2) v65_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v65_mb : Scalar.QComplex := ((2657545375706210249402037 : Int)/10^30,(-431463935841606640460469533 : Int)/10^30)
theorem v65_mb_checked : Scalar.distance (sourceCoefficient 0 66 3 1) v65_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v65_mg : Scalar.QComplex := ((-93084081624553949431440 : Int)/10^30,(-573339160295440968220 : Int)/10^30)
theorem v65_mg_checked : Scalar.distance (sourceCoefficient 0 66 3 2) v65_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v65_upper : Scalar.QComplex := ((999985974447694590747946978085 : Int)/10^30,(5296310781544171463147616602 : Int)/10^30)
theorem v65_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 66 5) 1) 14) v65_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material65 : Material (0 : Basis) (66 : Basis) where
  plus := ![v65_pa,v65_pb,v65_pg]
  minus := ![(Primitive.Addresses.material65 1).one,v65_mb,v65_mg]
  upper := v65_upper
  lower := (Primitive.Addresses.material65 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v65_pa_checked.trans (by decide +kernel)
    · exact v65_pb_checked.trans (by decide +kernel)
    · exact v65_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 66 Primitive.Addresses.material65
    · exact v65_mb_checked.trans (by decide +kernel)
    · exact v65_mg_checked.trans (by decide +kernel)
  upper_error := v65_upper_checked
  lower_error := reuse_lower_error 0 66 Primitive.Addresses.material65

def v66_pa : Scalar.QComplex := ((999975550973511012119116766141 : Int)/10^30,(6992671536907729125643993195 : Int)/10^30)
theorem v66_pa_checked : Scalar.distance (sourceCoefficient 0 67 1 0) v66_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v66_pb : Scalar.QComplex := ((3017142555942197945702307 : Int)/10^30,(-431461534239047441092570790 : Int)/10^30)
theorem v66_pb_checked : Scalar.distance (sourceCoefficient 0 67 1 1) v66_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v66_pg : Scalar.QComplex := ((-93083567477800328331079 : Int)/10^30,(-650918727185047458632 : Int)/10^30)
theorem v66_pg_checked : Scalar.distance (sourceCoefficient 0 67 1 2) v66_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v66_mb : Scalar.QComplex := ((2644809560779977214904704 : Int)/10^30,(-431463977244338199415502491 : Int)/10^30)
theorem v66_mb_checked : Scalar.distance (sourceCoefficient 0 67 3 1) v66_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v66_mg : Scalar.QComplex := ((-93084094532079296649461 : Int)/10^30,(-570591558413167848952 : Int)/10^30)
theorem v66_mg_checked : Scalar.distance (sourceCoefficient 0 67 3 2) v66_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v66_upper : Scalar.QComplex := ((999986130344095713124996933562 : Int)/10^30,(5266794038237953223936557276 : Int)/10^30)
theorem v66_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 67 5) 1) 14) v66_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material66 : Material (0 : Basis) (67 : Basis) where
  plus := ![v66_pa,v66_pb,v66_pg]
  minus := ![(Primitive.Addresses.material66 1).one,v66_mb,v66_mg]
  upper := v66_upper
  lower := (Primitive.Addresses.material66 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v66_pa_checked.trans (by decide +kernel)
    · exact v66_pb_checked.trans (by decide +kernel)
    · exact v66_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 67 Primitive.Addresses.material66
    · exact v66_mb_checked.trans (by decide +kernel)
    · exact v66_mg_checked.trans (by decide +kernel)
  upper_error := v66_upper_checked
  lower_error := reuse_lower_error 0 67 Primitive.Addresses.material66

def v67_pa : Scalar.QComplex := ((999975893510915763583646067783 : Int)/10^30,(6943514747277265220107409035 : Int)/10^30)
theorem v67_pa_checked : Scalar.distance (sourceCoefficient 0 68 1 0) v67_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v67_pb : Scalar.QComplex := ((2995932345419136407946507 : Int)/10^30,(-431461620382315744448246092 : Int)/10^30)
theorem v67_pb_checked : Scalar.distance (sourceCoefficient 0 68 1 1) v67_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v67_pg : Scalar.QComplex := ((-93083592712796986938861 : Int)/10^30,(-646342879788432751033 : Int)/10^30)
theorem v67_pg_checked : Scalar.distance (sourceCoefficient 0 68 1 2) v67_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v67_mb : Scalar.QComplex := ((2623599283816685612378093 : Int)/10^30,(-431464045084118018713919083 : Int)/10^30)
theorem v67_mb_checked : Scalar.distance (sourceCoefficient 0 68 3 1) v67_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v67_mg : Scalar.QComplex := ((-93084115818316344352577 : Int)/10^30,(-566015690943684679351 : Int)/10^30)
theorem v67_mg_checked : Scalar.distance (sourceCoefficient 0 68 3 2) v67_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v67_upper : Scalar.QComplex := ((999986388040830862301532684389 : Int)/10^30,(5217636730632267260427794298 : Int)/10^30)
theorem v67_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 68 5) 1) 14) v67_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material67 : Material (0 : Basis) (68 : Basis) where
  plus := ![v67_pa,v67_pb,v67_pg]
  minus := ![(Primitive.Addresses.material67 1).one,v67_mb,v67_mg]
  upper := v67_upper
  lower := (Primitive.Addresses.material67 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v67_pa_checked.trans (by decide +kernel)
    · exact v67_pb_checked.trans (by decide +kernel)
    · exact v67_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 68 Primitive.Addresses.material67
    · exact v67_mb_checked.trans (by decide +kernel)
    · exact v67_mg_checked.trans (by decide +kernel)
  upper_error := v67_upper_checked
  lower_error := reuse_lower_error 0 68 Primitive.Addresses.material67

def v68_pa : Scalar.QComplex := ((999976043502510424501541367657 : Int)/10^30,(6921879879438751780230965674 : Int)/10^30)
theorem v68_pa_checked : Scalar.distance (sourceCoefficient 0 69 1 0) v68_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v68_pb : Scalar.QComplex := ((2986597316667442561944362 : Int)/10^30,(-431461657855073979239059418 : Int)/10^30)
theorem v68_pb_checked : Scalar.distance (sourceCoefficient 0 69 1 1) v68_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v68_pg : Scalar.QComplex := ((-93083603736043930206416 : Int)/10^30,(-644328959671277130149 : Int)/10^30)
theorem v68_pg_checked : Scalar.distance (sourceCoefficient 0 69 1 2) v68_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v68_mb : Scalar.QComplex := ((2614264226203546956277232 : Int)/10^30,(-431464074501152922060192172 : Int)/10^30)
theorem v68_mb_checked : Scalar.distance (sourceCoefficient 0 69 3 1) v68_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v68_mg : Scalar.QComplex := ((-93084125103636825651208 : Int)/10^30,(-564001762063837915352 : Int)/10^30)
theorem v68_mg_checked : Scalar.distance (sourceCoefficient 0 69 3 2) v68_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v68_upper : Scalar.QComplex := ((999986500692382938962773585011 : Int)/10^30,(5196001636144462802346760897 : Int)/10^30)
theorem v68_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 69 5) 1) 14) v68_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material68 : Material (0 : Basis) (69 : Basis) where
  plus := ![v68_pa,v68_pb,v68_pg]
  minus := ![(Primitive.Addresses.material68 1).one,v68_mb,v68_mg]
  upper := v68_upper
  lower := (Primitive.Addresses.material68 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v68_pa_checked.trans (by decide +kernel)
    · exact v68_pb_checked.trans (by decide +kernel)
    · exact v68_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 69 Primitive.Addresses.material68
    · exact v68_mb_checked.trans (by decide +kernel)
    · exact v68_mg_checked.trans (by decide +kernel)
  upper_error := v68_upper_checked
  lower_error := reuse_lower_error 0 69 Primitive.Addresses.material68

def v69_pa : Scalar.QComplex := ((999976141913198655801239562756 : Int)/10^30,(6907648253521785763643227271 : Int)/10^30)
theorem v69_pa_checked : Scalar.distance (sourceCoefficient 0 70 1 0) v69_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v69_pb : Scalar.QComplex := ((2980456644596391789067403 : Int)/10^30,(-431461682358180550781289249 : Int)/10^30)
theorem v69_pb_checked : Scalar.distance (sourceCoefficient 0 70 1 1) v69_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v69_pg : Scalar.QComplex := ((-93083610959523836318529 : Int)/10^30,(-643004183525680367822 : Int)/10^30)
theorem v69_pg_checked : Scalar.distance (sourceCoefficient 0 70 1 2) v69_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v69_mb : Scalar.QComplex := ((2608123535273871645742408 : Int)/10^30,(-431464093705126938262663472 : Int)/10^30)
theorem v69_mb_checked : Scalar.distance (sourceCoefficient 0 70 3 1) v69_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v69_mg : Scalar.QComplex := ((-93084131183891894184319 : Int)/10^30,(-562676980177978031775 : Int)/10^30)
theorem v69_mg_checked : Scalar.distance (sourceCoefficient 0 70 3 2) v69_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v69_upper : Scalar.QComplex := ((999986574540429349436938215156 : Int)/10^30,(5181769861575911685537991394 : Int)/10^30)
theorem v69_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 70 5) 1) 14) v69_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material69 : Material (0 : Basis) (70 : Basis) where
  plus := ![v69_pa,v69_pb,v69_pg]
  minus := ![(Primitive.Addresses.material69 1).one,v69_mb,v69_mg]
  upper := v69_upper
  lower := (Primitive.Addresses.material69 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v69_pa_checked.trans (by decide +kernel)
    · exact v69_pb_checked.trans (by decide +kernel)
    · exact v69_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 70 Primitive.Addresses.material69
    · exact v69_mb_checked.trans (by decide +kernel)
    · exact v69_mg_checked.trans (by decide +kernel)
  upper_error := v69_upper_checked
  lower_error := reuse_lower_error 0 70 Primitive.Addresses.material69

def v70_pa : Scalar.QComplex := ((999976309424366732541576685843 : Int)/10^30,(6883356014558674654400746181 : Int)/10^30)
theorem v70_pa_checked : Scalar.distance (sourceCoefficient 0 71 1 0) v70_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v70_pb : Scalar.QComplex := ((2969975012771580122711720 : Int)/10^30,(-431461723913800227508084796 : Int)/10^30)
theorem v70_pb_checked : Scalar.distance (sourceCoefficient 0 71 1 1) v70_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v70_pg : Scalar.QComplex := ((-93083623238602777888078 : Int)/10^30,(-640742897444423435224 : Int)/10^30)
theorem v70_pg_checked : Scalar.distance (sourceCoefficient 0 71 1 2) v70_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v70_mb : Scalar.QComplex := ((2597641871491222356621394 : Int)/10^30,(-431464126215554952293735024 : Int)/10^30)
theorem v70_mb_checked : Scalar.distance (sourceCoefficient 0 71 3 1) v70_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v70_mg : Scalar.QComplex := ((-93084141511578220111316 : Int)/10^30,(-560415684342409155720 : Int)/10^30)
theorem v70_mg_checked : Scalar.distance (sourceCoefficient 0 71 3 2) v70_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v70_upper : Scalar.QComplex := ((999986700125147262343684716499 : Int)/10^30,(5157477369684157339014362708 : Int)/10^30)
theorem v70_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 71 5) 1) 14) v70_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material70 : Material (0 : Basis) (71 : Basis) where
  plus := ![v70_pa,v70_pb,v70_pg]
  minus := ![(Primitive.Addresses.material70 1).one,v70_mb,v70_mg]
  upper := v70_upper
  lower := (Primitive.Addresses.material70 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v70_pa_checked.trans (by decide +kernel)
    · exact v70_pb_checked.trans (by decide +kernel)
    · exact v70_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 71 Primitive.Addresses.material70
    · exact v70_mb_checked.trans (by decide +kernel)
    · exact v70_mg_checked.trans (by decide +kernel)
  upper_error := v70_upper_checked
  lower_error := reuse_lower_error 0 71 Primitive.Addresses.material70

def v71_pa : Scalar.QComplex := ((999976490540222337571092797529 : Int)/10^30,(6856994010543236597236622754 : Int)/10^30)
theorem v71_pa_checked : Scalar.distance (sourceCoefficient 0 72 1 0) v71_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v71_pb : Scalar.QComplex := ((2958600318341607417737576 : Int)/10^30,(-431461768625934582584566066 : Int)/10^30)
theorem v71_pb_checked : Scalar.distance (sourceCoefficient 0 72 1 1) v71_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v71_pg : Scalar.QComplex := ((-93083636491378108079800 : Int)/10^30,(-638288943729212670257 : Int)/10^30)
theorem v71_pg_checked : Scalar.distance (sourceCoefficient 0 72 1 2) v71_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v71_mb : Scalar.QComplex := ((2586267142712010048488683 : Int)/10^30,(-431464161111823663152465272 : Int)/10^30)
theorem v71_mb_checked : Scalar.distance (sourceCoefficient 0 72 3 1) v71_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v71_mg : Scalar.QComplex := ((-93084152646697081434775 : Int)/10^30,(-557961720104369283039 : Int)/10^30)
theorem v71_mg_checked : Scalar.distance (sourceCoefficient 0 72 3 2) v71_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v71_upper : Scalar.QComplex := ((999986835742305728258130521943 : Int)/10^30,(5131115092342291492112307829 : Int)/10^30)
theorem v71_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 72 5) 1) 14) v71_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material71 : Material (0 : Basis) (72 : Basis) where
  plus := ![v71_pa,v71_pb,v71_pg]
  minus := ![(Primitive.Addresses.material71 1).one,v71_mb,v71_mg]
  upper := v71_upper
  lower := (Primitive.Addresses.material71 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v71_pa_checked.trans (by decide +kernel)
    · exact v71_pb_checked.trans (by decide +kernel)
    · exact v71_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 72 Primitive.Addresses.material71
    · exact v71_mb_checked.trans (by decide +kernel)
    · exact v71_mg_checked.trans (by decide +kernel)
  upper_error := v71_upper_checked
  lower_error := reuse_lower_error 0 72 Primitive.Addresses.material71

def v72_pa : Scalar.QComplex := ((999976555291718430581080727232 : Int)/10^30,(6847544589762992550939598818 : Int)/10^30)
theorem v72_pa_checked : Scalar.distance (sourceCoefficient 0 73 1 0) v72_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v72_pb : Scalar.QComplex := ((2954523076454726284380542 : Int)/10^30,(-431461784555585828646109085 : Int)/10^30)
theorem v72_pb_checked : Scalar.distance (sourceCoefficient 0 73 1 1) v72_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v72_pg : Scalar.QComplex := ((-93083641223439237149992 : Int)/10^30,(-637409327730745411787 : Int)/10^30)
theorem v72_pg_checked : Scalar.distance (sourceCoefficient 0 73 1 2) v72_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v72_mb : Scalar.QComplex := ((2582189888596700828285272 : Int)/10^30,(-431464173522992861656249271 : Int)/10^30)
theorem v72_mb_checked : Scalar.distance (sourceCoefficient 0 73 3 1) v72_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v72_mg : Scalar.QComplex := ((-93084156619687458299039 : Int)/10^30,(-557082100349867630970 : Int)/10^30)
theorem v72_mg_checked : Scalar.distance (sourceCoefficient 0 73 3 2) v72_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v72_upper : Scalar.QComplex := ((999986884184862359576464234597 : Int)/10^30,(5121665573880641644353718387 : Int)/10^30)
theorem v72_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 73 5) 1) 14) v72_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material72 : Material (0 : Basis) (73 : Basis) where
  plus := ![v72_pa,v72_pb,v72_pg]
  minus := ![(Primitive.Addresses.material72 1).one,v72_mb,v72_mg]
  upper := v72_upper
  lower := (Primitive.Addresses.material72 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v72_pa_checked.trans (by decide +kernel)
    · exact v72_pb_checked.trans (by decide +kernel)
    · exact v72_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 73 Primitive.Addresses.material72
    · exact v72_mb_checked.trans (by decide +kernel)
    · exact v72_mg_checked.trans (by decide +kernel)
  upper_error := v72_upper_checked
  lower_error := reuse_lower_error 0 73 Primitive.Addresses.material72

def v73_pa : Scalar.QComplex := ((999976628046298366429392365945 : Int)/10^30,(6836911667927801296854467456 : Int)/10^30)
theorem v73_pa_checked : Scalar.distance (sourceCoefficient 0 74 1 0) v73_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v73_pb : Scalar.QComplex := ((2949935176971544011569469 : Int)/10^30,(-431461802418933342726447904 : Int)/10^30)
theorem v73_pb_checked : Scalar.distance (sourceCoefficient 0 74 1 1) v73_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v73_pg : Scalar.QComplex := ((-93083646536575811826776 : Int)/10^30,(-636419543467287170291 : Int)/10^30)
theorem v73_pg_checked : Scalar.distance (sourceCoefficient 0 74 1 2) v73_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v73_mb : Scalar.QComplex := ((2577601975406538841082560 : Int)/10^30,(-431464187427183101731819143 : Int)/10^30)
theorem v73_mb_checked : Scalar.distance (sourceCoefficient 0 74 3 1) v73_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v73_mg : Scalar.QComplex := ((-93084161078682813516196 : Int)/10^30,(-556092311869953736976 : Int)/10^30)
theorem v73_mg_checked : Scalar.distance (sourceCoefficient 0 74 3 2) v73_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v73_upper : Scalar.QComplex := ((999986938587875459617970073530 : Int)/10^30,(5111032542314133707706892595 : Int)/10^30)
theorem v73_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 74 5) 1) 14) v73_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material73 : Material (0 : Basis) (74 : Basis) where
  plus := ![v73_pa,v73_pb,v73_pg]
  minus := ![(Primitive.Addresses.material73 1).one,v73_mb,v73_mg]
  upper := v73_upper
  lower := (Primitive.Addresses.material73 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v73_pa_checked.trans (by decide +kernel)
    · exact v73_pb_checked.trans (by decide +kernel)
    · exact v73_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 74 Primitive.Addresses.material73
    · exact v73_mb_checked.trans (by decide +kernel)
    · exact v73_mg_checked.trans (by decide +kernel)
  upper_error := v73_upper_checked
  lower_error := reuse_lower_error 0 74 Primitive.Addresses.material73

def v74_pa : Scalar.QComplex := ((999976729226284825372991734805 : Int)/10^30,(6822096884495261340675258982 : Int)/10^30)
theorem v74_pa_checked : Scalar.distance (sourceCoefficient 0 75 1 0) v74_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v74_pb : Scalar.QComplex := ((2943542885635881133305350 : Int)/10^30,(-431461827199372008446628587 : Int)/10^30)
theorem v74_pb_checked : Scalar.distance (sourceCoefficient 0 75 1 1) v74_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v74_pg : Scalar.QComplex := ((-93083653918863048044081 : Int)/10^30,(-635040483280697124358 : Int)/10^30)
theorem v74_pg_checked : Scalar.distance (sourceCoefficient 0 75 1 2) v74_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v74_mb : Scalar.QComplex := ((2571209665066615670242425 : Int)/10^30,(-431464206691353015999576530 : Int)/10^30)
theorem v74_mb_checked : Scalar.distance (sourceCoefficient 0 75 3 1) v74_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v74_mg : Scalar.QComplex := ((-93084167270900470508518 : Int)/10^30,(-554713245826269425694 : Int)/10^30)
theorem v74_mg_checked : Scalar.distance (sourceCoefficient 0 75 3 2) v74_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v74_upper : Scalar.QComplex := ((999987014198739004947563026316 : Int)/10^30,(5096217606318995756119565948 : Int)/10^30)
theorem v74_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 75 5) 1) 14) v74_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material74 : Material (0 : Basis) (75 : Basis) where
  plus := ![v74_pa,v74_pb,v74_pg]
  minus := ![(Primitive.Addresses.material74 1).one,v74_mb,v74_mg]
  upper := v74_upper
  lower := (Primitive.Addresses.material74 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v74_pa_checked.trans (by decide +kernel)
    · exact v74_pb_checked.trans (by decide +kernel)
    · exact v74_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 75 Primitive.Addresses.material74
    · exact v74_mb_checked.trans (by decide +kernel)
    · exact v74_mg_checked.trans (by decide +kernel)
  upper_error := v74_upper_checked
  lower_error := reuse_lower_error 0 75 Primitive.Addresses.material74

def v75_pa : Scalar.QComplex := ((999976813948958017465326475718 : Int)/10^30,(6809666988260303168264044441 : Int)/10^30)
theorem v75_pa_checked : Scalar.distance (sourceCoefficient 0 76 1 0) v75_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v75_pb : Scalar.QComplex := ((2938179627075131363067148 : Int)/10^30,(-431461847893231603629013551 : Int)/10^30)
theorem v75_pb_checked : Scalar.distance (sourceCoefficient 0 76 1 1) v75_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v75_pg : Scalar.QComplex := ((-93083660094358077009857 : Int)/10^30,(-633883424544429287523 : Int)/10^30)
theorem v75_pg_checked : Scalar.distance (sourceCoefficient 0 76 1 2) v75_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v75_mb : Scalar.QComplex := ((2565846390644983361392096 : Int)/10^30,(-431464222756954320183963449 : Int)/10^30)
theorem v75_mb_checked : Scalar.distance (sourceCoefficient 0 76 3 1) v75_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v75_mg : Scalar.QComplex := ((-93084172447903622647111 : Int)/10^30,(-553556182191653360543 : Int)/10^30)
theorem v75_mg_checked : Scalar.distance (sourceCoefficient 0 76 3 2) v75_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v75_upper : Scalar.QComplex := ((999987077468412742410459344560 : Int)/10^30,(5083787582373259958820112269 : Int)/10^30)
theorem v75_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 76 5) 1) 14) v75_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material75 : Material (0 : Basis) (76 : Basis) where
  plus := ![v75_pa,v75_pb,v75_pg]
  minus := ![(Primitive.Addresses.material75 1).one,v75_mb,v75_mg]
  upper := v75_upper
  lower := (Primitive.Addresses.material75 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v75_pa_checked.trans (by decide +kernel)
    · exact v75_pb_checked.trans (by decide +kernel)
    · exact v75_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 76 Primitive.Addresses.material75
    · exact v75_mb_checked.trans (by decide +kernel)
    · exact v75_mg_checked.trans (by decide +kernel)
  upper_error := v75_upper_checked
  lower_error := reuse_lower_error 0 76 Primitive.Addresses.material75

def v76_pa : Scalar.QComplex := ((999976833540951519744504419295 : Int)/10^30,(6806789361522484050846154412 : Int)/10^30)
theorem v76_pa_checked : Scalar.distance (sourceCoefficient 0 77 1 0) v76_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v76_pb : Scalar.QComplex := ((2936937987119832326475957 : Int)/10^30,(-431461852671364579968080910 : Int)/10^30)
theorem v76_pb_checked : Scalar.distance (sourceCoefficient 0 77 1 1) v76_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v76_pg : Scalar.QComplex := ((-93083661521645670335718 : Int)/10^30,(-633615555605918973178 : Int)/10^30)
theorem v76_pg_checked : Scalar.distance (sourceCoefficient 0 77 1 2) v76_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v76_mb : Scalar.QComplex := ((2564604747028690066448062 : Int)/10^30,(-431464226463606157370370853 : Int)/10^30)
theorem v76_mb_checked : Scalar.distance (sourceCoefficient 0 77 3 1) v76_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v76_mg : Scalar.QComplex := ((-93084173644031854963309 : Int)/10^30,(-553288312121197983827 : Int)/10^30)
theorem v76_mg_checked : Scalar.distance (sourceCoefficient 0 77 3 2) v76_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v76_upper : Scalar.QComplex := ((999987092093854371499351574982 : Int)/10^30,(5080909926107324424434475656 : Int)/10^30)
theorem v76_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 77 5) 1) 14) v76_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material76 : Material (0 : Basis) (77 : Basis) where
  plus := ![v76_pa,v76_pb,v76_pg]
  minus := ![(Primitive.Addresses.material76 1).one,v76_mb,v76_mg]
  upper := v76_upper
  lower := (Primitive.Addresses.material76 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v76_pa_checked.trans (by decide +kernel)
    · exact v76_pb_checked.trans (by decide +kernel)
    · exact v76_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 77 Primitive.Addresses.material76
    · exact v76_mb_checked.trans (by decide +kernel)
    · exact v76_mg_checked.trans (by decide +kernel)
  upper_error := v76_upper_checked
  lower_error := reuse_lower_error 0 77 Primitive.Addresses.material76

def v77_pa : Scalar.QComplex := ((999976951145977171578769431872 : Int)/10^30,(6789490172022128850298544698 : Int)/10^30)
theorem v77_pa_checked : Scalar.distance (sourceCoefficient 0 78 1 0) v77_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v77_pb : Scalar.QComplex := ((2929473723668573924759698 : Int)/10^30,(-431461881295261063500963411 : Int)/10^30)
theorem v77_pb_checked : Scalar.distance (sourceCoefficient 0 78 1 1) v77_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v77_pg : Scalar.QComplex := ((-93083670082997512065632 : Int)/10^30,(-632005230200554423722 : Int)/10^30)
theorem v77_pg_checked : Scalar.distance (sourceCoefficient 0 78 1 2) v77_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v77_mb : Scalar.QComplex := ((2557140461655584588479785 : Int)/10^30,(-431464248646168802428747865 : Int)/10^30)
theorem v77_mb_checked : Scalar.distance (sourceCoefficient 0 78 3 1) v77_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v77_mg : Scalar.QComplex := ((-93084180815742210445006 : Int)/10^30,(-551677979927370127855 : Int)/10^30)
theorem v77_mg_checked : Scalar.distance (sourceCoefficient 0 78 3 2) v77_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v77_upper : Scalar.QComplex := ((999987179841873157061913682733 : Int)/10^30,(5063610559396474648638786842 : Int)/10^30)
theorem v77_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 78 5) 1) 14) v77_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material77 : Material (0 : Basis) (78 : Basis) where
  plus := ![v77_pa,v77_pb,v77_pg]
  minus := ![(Primitive.Addresses.material77 1).one,v77_mb,v77_mg]
  upper := v77_upper
  lower := (Primitive.Addresses.material77 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v77_pa_checked.trans (by decide +kernel)
    · exact v77_pb_checked.trans (by decide +kernel)
    · exact v77_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 78 Primitive.Addresses.material77
    · exact v77_mb_checked.trans (by decide +kernel)
    · exact v77_mg_checked.trans (by decide +kernel)
  upper_error := v77_upper_checked
  lower_error := reuse_lower_error 0 78 Primitive.Addresses.material77

def v78_pa : Scalar.QComplex := ((999976988995962725926431269372 : Int)/10^30,(6783913219391986274065148939 : Int)/10^30)
theorem v78_pa_checked : Scalar.distance (sourceCoefficient 0 79 1 0) v78_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v78_pb : Scalar.QComplex := ((2927067377293771948333613 : Int)/10^30,(-431461890486398412352760452 : Int)/10^30)
theorem v78_pb_checked : Scalar.distance (sourceCoefficient 0 79 1 1) v78_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v78_pg : Scalar.QComplex := ((-93083672836097834074393 : Int)/10^30,(-631486089791324509632 : Int)/10^30)
theorem v78_pg_checked : Scalar.distance (sourceCoefficient 0 79 1 2) v78_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v78_mb : Scalar.QComplex := ((2554734108245237764255119 : Int)/10^30,(-431464255760734185363495927 : Int)/10^30)
theorem v78_mb_checked : Scalar.distance (sourceCoefficient 0 79 3 1) v78_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v78_mg : Scalar.QComplex := ((-93084183120846715399358 : Int)/10^30,(-551158837335638331153 : Int)/10^30)
theorem v78_mg_checked : Scalar.distance (sourceCoefficient 0 79 3 2) v78_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v78_upper : Scalar.QComplex := ((999987208066488035866619461493 : Int)/10^30,(5058033549746906557190159043 : Int)/10^30)
theorem v78_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 79 5) 1) 14) v78_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material78 : Material (0 : Basis) (79 : Basis) where
  plus := ![v78_pa,v78_pb,v78_pg]
  minus := ![(Primitive.Addresses.material78 1).one,v78_mb,v78_mg]
  upper := v78_upper
  lower := (Primitive.Addresses.material78 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v78_pa_checked.trans (by decide +kernel)
    · exact v78_pb_checked.trans (by decide +kernel)
    · exact v78_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 79 Primitive.Addresses.material78
    · exact v78_mb_checked.trans (by decide +kernel)
    · exact v78_mg_checked.trans (by decide +kernel)
  upper_error := v78_upper_checked
  lower_error := reuse_lower_error 0 79 Primitive.Addresses.material78

def v79_pa : Scalar.QComplex := ((999977048059140062387294666044 : Int)/10^30,(6775201467726696858785765312 : Int)/10^30)
theorem v79_pa_checked : Scalar.distance (sourceCoefficient 0 80 1 0) v79_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v79_pb : Scalar.QComplex := ((2923308426325809038773292 : Int)/10^30,(-431461904808055302749377277 : Int)/10^30)
theorem v79_pb_checked : Scalar.distance (sourceCoefficient 0 80 1 1) v79_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v79_pg : Scalar.QComplex := ((-93083677129953142869002 : Int)/10^30,(-630675141130797565855 : Int)/10^30)
theorem v79_pg_checked : Scalar.distance (sourceCoefficient 0 80 1 2) v79_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v79_mb : Scalar.QComplex := ((2550975146317959219683015 : Int)/10^30,(-431464266838580354667731389 : Int)/10^30)
theorem v79_mb_checked : Scalar.distance (sourceCoefficient 0 80 3 1) v79_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v79_mg : Scalar.QComplex := ((-93084186714888255132489 : Int)/10^30,(-550347885271660892449 : Int)/10^30)
theorem v79_mg_checked : Scalar.distance (sourceCoefficient 0 80 3 2) v79_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v79_upper : Scalar.QComplex := ((999987252093884354310760866673 : Int)/10^30,(5049321709119061979982829844 : Int)/10^30)
theorem v79_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 80 5) 1) 14) v79_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material79 : Material (0 : Basis) (80 : Basis) where
  plus := ![v79_pa,v79_pb,v79_pg]
  minus := ![(Primitive.Addresses.material79 1).one,v79_mb,v79_mg]
  upper := v79_upper
  lower := (Primitive.Addresses.material79 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v79_pa_checked.trans (by decide +kernel)
    · exact v79_pb_checked.trans (by decide +kernel)
    · exact v79_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 80 Primitive.Addresses.material79
    · exact v79_mb_checked.trans (by decide +kernel)
    · exact v79_mg_checked.trans (by decide +kernel)
  upper_error := v79_upper_checked
  lower_error := reuse_lower_error 0 80 Primitive.Addresses.material79

def v80_pa : Scalar.QComplex := ((999977225443114965194338464288 : Int)/10^30,(6748969928042967775748497586 : Int)/10^30)
theorem v80_pa_checked : Scalar.distance (sourceCoefficient 0 81 1 0) v80_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v80_pb : Scalar.QComplex := ((2911990029186263850986894 : Int)/10^30,(-431461947667631766938497877 : Int)/10^30)
theorem v80_pb_checked : Scalar.distance (sourceCoefficient 0 81 1 1) v80_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v80_pg : Scalar.QComplex := ((-93083690009200166734971 : Int)/10^30,(-628233332399131366742 : Int)/10^30)
theorem v80_pg_checked : Scalar.distance (sourceCoefficient 0 81 1 2) v80_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v80_mb : Scalar.QComplex := ((2539656716406886398324289 : Int)/10^30,(-431464299930873890534179815 : Int)/10^30)
theorem v80_mb_checked : Scalar.distance (sourceCoefficient 0 81 3 1) v80_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v80_mg : Scalar.QComplex := ((-93084197486959523021061 : Int)/10^30,(-547906066334981558464 : Int)/10^30)
theorem v80_mg_checked : Scalar.distance (sourceCoefficient 0 81 3 2) v80_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v80_upper : Scalar.QComplex := ((999987384204337277098634403449 : Int)/10^30,(5023089902355481349007385030 : Int)/10^30)
theorem v80_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 81 5) 1) 14) v80_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material80 : Material (0 : Basis) (81 : Basis) where
  plus := ![v80_pa,v80_pb,v80_pg]
  minus := ![(Primitive.Addresses.material80 1).one,v80_mb,v80_mg]
  upper := v80_upper
  lower := (Primitive.Addresses.material80 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v80_pa_checked.trans (by decide +kernel)
    · exact v80_pb_checked.trans (by decide +kernel)
    · exact v80_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 81 Primitive.Addresses.material80
    · exact v80_mb_checked.trans (by decide +kernel)
    · exact v80_mg_checked.trans (by decide +kernel)
  upper_error := v80_upper_checked
  lower_error := reuse_lower_error 0 81 Primitive.Addresses.material80

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
