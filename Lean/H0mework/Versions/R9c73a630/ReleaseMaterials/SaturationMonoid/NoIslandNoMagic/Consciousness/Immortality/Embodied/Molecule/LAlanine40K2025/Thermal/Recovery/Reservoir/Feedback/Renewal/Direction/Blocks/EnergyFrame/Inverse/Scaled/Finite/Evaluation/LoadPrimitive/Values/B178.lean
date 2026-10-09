import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B118
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B119

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2849_pa : Scalar.QComplex := ((999998711511895418303175284687 : Int)/10^30,(-1605295782390833418617984652 : Int)/10^30)
theorem v2849_pa_checked : Scalar.distance (sourceCoefficient 35 85 1 0) v2849_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2849_pb : Scalar.QComplex := ((-692648959179111326063847 : Int)/10^30,(-431476911798508155796460384 : Int)/10^30)
theorem v2849_pb_checked : Scalar.distance (sourceCoefficient 35 85 1 1) v2849_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2849_pg : Scalar.QComplex := ((-93086304212336387956610 : Int)/10^30,(149431244090794138286 : Int)/10^30)
theorem v2849_pg_checked : Scalar.distance (sourceCoefficient 35 85 1 2) v2849_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2849_mb : Scalar.QComplex := ((-1064993843157640157663081 : Int)/10^30,(-431476153415078403688785772 : Int)/10^30)
theorem v2849_mb_checked : Scalar.distance (sourceCoefficient 35 85 3 1) v2849_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2849_mg : Scalar.QComplex := ((-93086140599617558481057 : Int)/10^30,(229760476534448312806 : Int)/10^30)
theorem v2849_mg_checked : Scalar.distance (sourceCoefficient 35 85 3 2) v2849_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2849_upper : Scalar.QComplex := ((999994451536393610863890101595 : Int)/10^30,(-3331200448386419270034447199 : Int)/10^30)
theorem v2849_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 85 5) 1) 14) v2849_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2849 : Material (35 : Basis) (85 : Basis) where
  plus := ![v2849_pa,v2849_pb,v2849_pg]
  minus := ![(Primitive.Addresses.material2849 1).one,v2849_mb,v2849_mg]
  upper := v2849_upper
  lower := (Primitive.Addresses.material2849 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2849_pa_checked.trans (by decide +kernel)
    · exact v2849_pb_checked.trans (by decide +kernel)
    · exact v2849_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 85 Primitive.Addresses.material2849
    · exact v2849_mb_checked.trans (by decide +kernel)
    · exact v2849_mg_checked.trans (by decide +kernel)
  upper_error := v2849_upper_checked
  lower_error := reuse_lower_error 35 85 Primitive.Addresses.material2849

def v2850_pa : Scalar.QComplex := ((999998687992871972035228108656 : Int)/10^30,(-1619880407528045123245790475 : Int)/10^30)
theorem v2850_pa_checked : Scalar.distance (sourceCoefficient 35 86 1 0) v2850_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2850_pb : Scalar.QComplex := ((-698941893352725555128846 : Int)/10^30,(-431476899830260201574725226 : Int)/10^30)
theorem v2850_pb_checked : Scalar.distance (sourceCoefficient 35 86 1 1) v2850_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2850_pg : Scalar.QComplex := ((-93086301826677871627114 : Int)/10^30,(150788874374355568338 : Int)/10^30)
theorem v2850_pg_checked : Scalar.distance (sourceCoefficient 35 86 1 2) v2850_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2850_mb : Scalar.QComplex := ((-1071286764660048437976747 : Int)/10^30,(-431476136016316137197674827 : Int)/10^30)
theorem v2850_mb_checked : Scalar.distance (sourceCoefficient 35 86 3 1) v2850_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2850_mg : Scalar.QComplex := ((-93086137042386141125890 : Int)/10^30,(231118104253786087997 : Int)/10^30)
theorem v2850_mg_checked : Scalar.distance (sourceCoefficient 35 86 3 2) v2850_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2850_upper : Scalar.QComplex := ((999994402845665313448129665992 : Int)/10^30,(-3345785011209844224083481090 : Int)/10^30)
theorem v2850_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 86 5) 1) 14) v2850_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2850 : Material (35 : Basis) (86 : Basis) where
  plus := ![v2850_pa,v2850_pb,v2850_pg]
  minus := ![(Primitive.Addresses.material2850 1).one,v2850_mb,v2850_mg]
  upper := v2850_upper
  lower := (Primitive.Addresses.material2850 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2850_pa_checked.trans (by decide +kernel)
    · exact v2850_pb_checked.trans (by decide +kernel)
    · exact v2850_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 86 Primitive.Addresses.material2850
    · exact v2850_mb_checked.trans (by decide +kernel)
    · exact v2850_mg_checked.trans (by decide +kernel)
  upper_error := v2850_upper_checked
  lower_error := reuse_lower_error 35 86 Primitive.Addresses.material2850

def v2851_pa : Scalar.QComplex := ((999998686427995693622767817887 : Int)/10^30,(-1620846162700625937133268798 : Int)/10^30)
theorem v2851_pa_checked : Scalar.distance (sourceCoefficient 35 87 1 0) v2851_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2851_pb : Scalar.QComplex := ((-699358594750179016990281 : Int)/10^30,(-431476899033434658168097217 : Int)/10^30)
theorem v2851_pb_checked : Scalar.distance (sourceCoefficient 35 87 1 1) v2851_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2851_pg : Scalar.QComplex := ((-93086301667890416884751 : Int)/10^30,(150878773048525378823 : Int)/10^30)
theorem v2851_pg_checked : Scalar.distance (sourceCoefficient 35 87 1 2) v2851_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2851_mb : Scalar.QComplex := ((-1071703465214720369101932 : Int)/10^30,(-431476134859896352017533452 : Int)/10^30)
theorem v2851_mb_checked : Scalar.distance (sourceCoefficient 35 87 3 1) v2851_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2851_mg : Scalar.QComplex := ((-93086136806020238584790 : Int)/10^30,(231208002757456091595 : Int)/10^30)
theorem v2851_mg_checked : Scalar.distance (sourceCoefficient 35 87 3 2) v2851_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2851_upper : Scalar.QComplex := ((999994399613985550485442284594 : Int)/10^30,(-3346750762243211661910630791 : Int)/10^30)
theorem v2851_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 87 5) 1) 14) v2851_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2851 : Material (35 : Basis) (87 : Basis) where
  plus := ![v2851_pa,v2851_pb,v2851_pg]
  minus := ![(Primitive.Addresses.material2851 1).one,v2851_mb,v2851_mg]
  upper := v2851_upper
  lower := (Primitive.Addresses.material2851 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2851_pa_checked.trans (by decide +kernel)
    · exact v2851_pb_checked.trans (by decide +kernel)
    · exact v2851_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 87 Primitive.Addresses.material2851
    · exact v2851_mb_checked.trans (by decide +kernel)
    · exact v2851_mg_checked.trans (by decide +kernel)
  upper_error := v2851_upper_checked
  lower_error := reuse_lower_error 35 87 Primitive.Addresses.material2851

def v2852_pa : Scalar.QComplex := ((999998667298359675335195082750 : Int)/10^30,(-1632605740696653156841448567 : Int)/10^30)
theorem v2852_pa_checked : Scalar.distance (sourceCoefficient 35 88 1 0) v2852_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2852_pb : Scalar.QComplex := ((-704432585227647234065790 : Int)/10^30,(-431476889287793185150513375 : Int)/10^30)
theorem v2852_pb_checked : Scalar.distance (sourceCoefficient 35 88 1 1) v2852_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2852_pg : Scalar.QComplex := ((-93086299726279298361659 : Int)/10^30,(151973429848572120869 : Int)/10^30)
theorem v2852_pg_checked : Scalar.distance (sourceCoefficient 35 88 1 2) v2852_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2852_mb : Scalar.QComplex := ((-1076777445392860374779486 : Int)/10^30,(-431476120735633249740490251 : Int)/10^30)
theorem v2852_mb_checked : Scalar.distance (sourceCoefficient 35 88 3 1) v2852_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2852_mg : Scalar.QComplex := ((-93086133919770326084030 : Int)/10^30,(232302657474389130330 : Int)/10^30)
theorem v2852_mg_checked : Scalar.distance (sourceCoefficient 35 88 3 2) v2852_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2852_upper : Scalar.QComplex := ((999994360188413222982867206201 : Int)/10^30,(-3358510289708712493062943224 : Int)/10^30)
theorem v2852_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 88 5) 1) 14) v2852_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2852 : Material (35 : Basis) (88 : Basis) where
  plus := ![v2852_pa,v2852_pb,v2852_pg]
  minus := ![(Primitive.Addresses.material2852 1).one,v2852_mb,v2852_mg]
  upper := v2852_upper
  lower := (Primitive.Addresses.material2852 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2852_pa_checked.trans (by decide +kernel)
    · exact v2852_pb_checked.trans (by decide +kernel)
    · exact v2852_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 88 Primitive.Addresses.material2852
    · exact v2852_mb_checked.trans (by decide +kernel)
    · exact v2852_mg_checked.trans (by decide +kernel)
  upper_error := v2852_upper_checked
  lower_error := reuse_lower_error 35 88 Primitive.Addresses.material2852

def v2853_pa : Scalar.QComplex := ((999998640901139288521813606714 : Int)/10^30,(-1648695203569550991840969848 : Int)/10^30)
theorem v2853_pa_checked : Scalar.distance (sourceCoefficient 35 89 1 0) v2853_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2853_pb : Scalar.QComplex := ((-711374822452413724587361 : Int)/10^30,(-431476875824909468180987308 : Int)/10^30)
theorem v2853_pb_checked : Scalar.distance (sourceCoefficient 35 89 1 1) v2853_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2853_pg : Scalar.QComplex := ((-93086297045434801433333 : Int)/10^30,(153471140039310402500 : Int)/10^30)
theorem v2853_pg_checked : Scalar.distance (sourceCoefficient 35 89 1 2) v2853_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2853_mb : Scalar.QComplex := ((-1083719668414852368634870 : Int)/10^30,(-431476101281916487402242725 : Int)/10^30)
theorem v2853_mb_checked : Scalar.distance (sourceCoefficient 35 89 3 1) v2853_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2853_mg : Scalar.QComplex := ((-93086129946470387112462 : Int)/10^30,(233800364794013399117 : Int)/10^30)
theorem v2853_mg_checked : Scalar.distance (sourceCoefficient 35 89 3 2) v2853_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2853_upper : Scalar.QComplex := ((999994306022278857776620443018 : Int)/10^30,(-3374599683059037729442459550 : Int)/10^30)
theorem v2853_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 89 5) 1) 14) v2853_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2853 : Material (35 : Basis) (89 : Basis) where
  plus := ![v2853_pa,v2853_pb,v2853_pg]
  minus := ![(Primitive.Addresses.material2853 1).one,v2853_mb,v2853_mg]
  upper := v2853_upper
  lower := (Primitive.Addresses.material2853 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2853_pa_checked.trans (by decide +kernel)
    · exact v2853_pb_checked.trans (by decide +kernel)
    · exact v2853_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 89 Primitive.Addresses.material2853
    · exact v2853_mb_checked.trans (by decide +kernel)
    · exact v2853_mg_checked.trans (by decide +kernel)
  upper_error := v2853_upper_checked
  lower_error := reuse_lower_error 35 89 Primitive.Addresses.material2853

def v2854_pa : Scalar.QComplex := ((999998597357178414015670242604 : Int)/10^30,(-1674898109069648365642304539 : Int)/10^30)
theorem v2854_pa_checked : Scalar.distance (sourceCoefficient 35 90 1 0) v2854_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2854_pb : Scalar.QComplex := ((-722680779832836552108055 : Int)/10^30,(-431476853580814905412425299 : Int)/10^30)
theorem v2854_pb_checked : Scalar.distance (sourceCoefficient 35 90 1 1) v2854_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2854_pg : Scalar.QComplex := ((-93086292619302057371370 : Int)/10^30,(155910274174799863721 : Int)/10^30)
theorem v2854_pg_checked : Scalar.distance (sourceCoefficient 35 90 1 2) v2854_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2854_mb : Scalar.QComplex := ((-1095025602389898784805885 : Int)/10^30,(-431476069281298189239760719 : Int)/10^30)
theorem v2854_mb_checked : Scalar.distance (sourceCoefficient 35 90 3 1) v2854_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2854_mg : Scalar.QComplex := ((-93086123415476386698070 : Int)/10^30,(236239494201748535252 : Int)/10^30)
theorem v2854_mg_checked : Scalar.distance (sourceCoefficient 35 90 3 2) v2854_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2854_upper : Scalar.QComplex := ((999994217254545052735111738423 : Int)/10^30,(-3400802474380059178222230921 : Int)/10^30)
theorem v2854_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 90 5) 1) 14) v2854_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2854 : Material (35 : Basis) (90 : Basis) where
  plus := ![v2854_pa,v2854_pb,v2854_pg]
  minus := ![(Primitive.Addresses.material2854 1).one,v2854_mb,v2854_mg]
  upper := v2854_upper
  lower := (Primitive.Addresses.material2854 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2854_pa_checked.trans (by decide +kernel)
    · exact v2854_pb_checked.trans (by decide +kernel)
    · exact v2854_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 90 Primitive.Addresses.material2854
    · exact v2854_mb_checked.trans (by decide +kernel)
    · exact v2854_mg_checked.trans (by decide +kernel)
  upper_error := v2854_upper_checked
  lower_error := reuse_lower_error 35 90 Primitive.Addresses.material2854

def v2855_pa : Scalar.QComplex := ((999998572524944073939054370795 : Int)/10^30,(-1689659159170004499445525090 : Int)/10^30)
theorem v2855_pa_checked : Scalar.distance (sourceCoefficient 35 91 1 0) v2855_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2855_pb : Scalar.QComplex := ((-729049836856281169723668 : Int)/10^30,(-431476840875971913139341575 : Int)/10^30)
theorem v2855_pb_checked : Scalar.distance (sourceCoefficient 35 91 1 1) v2855_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2855_pg : Scalar.QComplex := ((-93086290093066429000592 : Int)/10^30,(157284327168359463256 : Int)/10^30)
theorem v2855_pg_checked : Scalar.distance (sourceCoefficient 35 91 1 2) v2855_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2855_mb : Scalar.QComplex := ((-1101394646078145094862895 : Int)/10^30,(-431476051080250568007559078 : Int)/10^30)
theorem v2855_mb_checked : Scalar.distance (sourceCoefficient 35 91 3 1) v2855_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2855_mg : Scalar.QComplex := ((-93086119703495850567885 : Int)/10^30,(237613544503657838105 : Int)/10^30)
theorem v2855_mg_checked : Scalar.distance (sourceCoefficient 35 91 3 2) v2855_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2855_upper : Scalar.QComplex := ((999994166946114336144394700996 : Int)/10^30,(-3415563459637381434022931988 : Int)/10^30)
theorem v2855_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 91 5) 1) 14) v2855_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2855 : Material (35 : Basis) (91 : Basis) where
  plus := ![v2855_pa,v2855_pb,v2855_pg]
  minus := ![(Primitive.Addresses.material2855 1).one,v2855_mb,v2855_mg]
  upper := v2855_upper
  lower := (Primitive.Addresses.material2855 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2855_pa_checked.trans (by decide +kernel)
    · exact v2855_pb_checked.trans (by decide +kernel)
    · exact v2855_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 91 Primitive.Addresses.material2855
    · exact v2855_mb_checked.trans (by decide +kernel)
    · exact v2855_mg_checked.trans (by decide +kernel)
  upper_error := v2855_upper_checked
  lower_error := reuse_lower_error 35 91 Primitive.Addresses.material2855

def v2856_pa : Scalar.QComplex := ((999998518019423605846432079237 : Int)/10^30,(-1721615217324091360883008160 : Int)/10^30)
theorem v2856_pa_checked : Scalar.distance (sourceCoefficient 35 92 1 0) v2856_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2856_pb : Scalar.QComplex := ((-742838147955054798827565 : Int)/10^30,(-431476812941942193192236651 : Int)/10^30)
theorem v2856_pb_checked : Scalar.distance (sourceCoefficient 35 92 1 1) v2856_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2856_pg : Scalar.QComplex := ((-93086284542977649720043 : Int)/10^30,(160259001494078079431 : Int)/10^30)
theorem v2856_pg_checked : Scalar.distance (sourceCoefficient 35 92 1 2) v2856_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2856_mb : Scalar.QComplex := ((-1115182927937090798627064 : Int)/10^30,(-431476011247539773413918335 : Int)/10^30)
theorem v2856_mb_checked : Scalar.distance (sourceCoefficient 35 92 3 1) v2856_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2856_mg : Scalar.QComplex := ((-93086111586399169102143 : Int)/10^30,(240588212932292603683 : Int)/10^30)
theorem v2856_mg_checked : Scalar.distance (sourceCoefficient 35 92 3 2) v2856_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2856_upper : Scalar.QComplex := ((999994057287417704617670351154 : Int)/10^30,(-3447519376125089871493552694 : Int)/10^30)
theorem v2856_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 92 5) 1) 14) v2856_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2856 : Material (35 : Basis) (92 : Basis) where
  plus := ![v2856_pa,v2856_pb,v2856_pg]
  minus := ![(Primitive.Addresses.material2856 1).one,v2856_mb,v2856_mg]
  upper := v2856_upper
  lower := (Primitive.Addresses.material2856 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2856_pa_checked.trans (by decide +kernel)
    · exact v2856_pb_checked.trans (by decide +kernel)
    · exact v2856_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 92 Primitive.Addresses.material2856
    · exact v2856_mb_checked.trans (by decide +kernel)
    · exact v2856_mg_checked.trans (by decide +kernel)
  upper_error := v2856_upper_checked
  lower_error := reuse_lower_error 35 92 Primitive.Addresses.material2856

def v2857_pa : Scalar.QComplex := ((999998452006938446945728660365 : Int)/10^30,(-1759540771571829740498298305 : Int)/10^30)
theorem v2857_pa_checked : Scalar.distance (sourceCoefficient 35 93 1 0) v2857_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2857_pb : Scalar.QComplex := ((-759202159924838458566156 : Int)/10^30,(-431476779027379141214384031 : Int)/10^30)
theorem v2857_pb_checked : Scalar.distance (sourceCoefficient 35 93 1 1) v2857_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2857_pg : Scalar.QComplex := ((-93086277812201281623563 : Int)/10^30,(163789354629214860638 : Int)/10^30)
theorem v2857_pg_checked : Scalar.distance (sourceCoefficient 35 93 1 2) v2857_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2857_mb : Scalar.QComplex := ((-1131546904547064471083710 : Int)/10^30,(-431475963211584027194669436 : Int)/10^30)
theorem v2857_mb_checked : Scalar.distance (sourceCoefficient 35 93 3 1) v2857_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2857_mg : Scalar.QComplex := ((-93086101809089552761079 : Int)/10^30,(244118558944560704816 : Int)/10^30)
theorem v2857_mg_checked : Scalar.distance (sourceCoefficient 35 93 3 2) v2857_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2857_upper : Scalar.QComplex := ((999993925818964811367820120839 : Int)/10^30,(-3485444759955609469265137293 : Int)/10^30)
theorem v2857_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 93 5) 1) 14) v2857_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2857 : Material (35 : Basis) (93 : Basis) where
  plus := ![v2857_pa,v2857_pb,v2857_pg]
  minus := ![(Primitive.Addresses.material2857 1).one,v2857_mb,v2857_mg]
  upper := v2857_upper
  lower := (Primitive.Addresses.material2857 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2857_pa_checked.trans (by decide +kernel)
    · exact v2857_pb_checked.trans (by decide +kernel)
    · exact v2857_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 93 Primitive.Addresses.material2857
    · exact v2857_mb_checked.trans (by decide +kernel)
    · exact v2857_mg_checked.trans (by decide +kernel)
  upper_error := v2857_upper_checked
  lower_error := reuse_lower_error 35 93 Primitive.Addresses.material2857

def v2858_pa : Scalar.QComplex := ((999998372178596226649266495245 : Int)/10^30,(-1804339257940196479492597609 : Int)/10^30)
theorem v2858_pa_checked : Scalar.distance (sourceCoefficient 35 94 1 0) v2858_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2858_pb : Scalar.QComplex := ((-778531684392830356289420 : Int)/10^30,(-431476737900747273916805662 : Int)/10^30)
theorem v2858_pb_checked : Scalar.distance (sourceCoefficient 35 94 1 1) v2858_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2858_pg : Scalar.QComplex := ((-93086269660429073752899 : Int)/10^30,(167959484131562856349 : Int)/10^30)
theorem v2858_pg_checked : Scalar.distance (sourceCoefficient 35 94 1 2) v2858_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2858_mb : Scalar.QComplex := ((-1150876386327359979726237 : Int)/10^30,(-431475905404458426809688194 : Int)/10^30)
theorem v2858_mb_checked : Scalar.distance (sourceCoefficient 35 94 3 1) v2858_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2858_mg : Scalar.QComplex := ((-93086090058686435302182 : Int)/10^30,(248288679859566629269 : Int)/10^30)
theorem v2858_mg_checked : Scalar.distance (sourceCoefficient 35 94 3 2) v2858_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2858_upper : Scalar.QComplex := ((999993768672618101145241089054 : Int)/10^30,(-3530243041825416460852797788 : Int)/10^30)
theorem v2858_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 94 5) 1) 14) v2858_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2858 : Material (35 : Basis) (94 : Basis) where
  plus := ![v2858_pa,v2858_pb,v2858_pg]
  minus := ![(Primitive.Addresses.material2858 1).one,v2858_mb,v2858_mg]
  upper := v2858_upper
  lower := (Primitive.Addresses.material2858 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2858_pa_checked.trans (by decide +kernel)
    · exact v2858_pb_checked.trans (by decide +kernel)
    · exact v2858_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 94 Primitive.Addresses.material2858
    · exact v2858_mb_checked.trans (by decide +kernel)
    · exact v2858_mg_checked.trans (by decide +kernel)
  upper_error := v2858_upper_checked
  lower_error := reuse_lower_error 35 94 Primitive.Addresses.material2858

def v2859_pa : Scalar.QComplex := ((999998291312774517573833045527 : Int)/10^30,(-1848613407760751314160170813 : Int)/10^30)
theorem v2859_pa_checked : Scalar.distance (sourceCoefficient 35 95 1 0) v2859_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2859_pb : Scalar.QComplex := ((-797634968494428432682112 : Int)/10^30,(-431476696121083960401668604 : Int)/10^30)
theorem v2859_pb_checked : Scalar.distance (sourceCoefficient 35 95 1 1) v2859_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2859_pg : Scalar.QComplex := ((-93086261389927131440100 : Int)/10^30,(172080804916014356343 : Int)/10^30)
theorem v2859_pg_checked : Scalar.distance (sourceCoefficient 35 95 1 2) v2859_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2859_mb : Scalar.QComplex := ((-1169979627261964568500927 : Int)/10^30,(-431475847139536870070617702 : Int)/10^30)
theorem v2859_mb_checked : Scalar.distance (sourceCoefficient 35 95 3 1) v2859_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2859_mg : Scalar.QComplex := ((-93086078231673352891283 : Int)/10^30,(252409991972391360911 : Int)/10^30)
theorem v2859_mg_checked : Scalar.distance (sourceCoefficient 35 95 3 2) v2859_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2859_upper : Scalar.QComplex := ((999993611393750761430824229284 : Int)/10^30,(-3574516986137753764953489774 : Int)/10^30)
theorem v2859_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 95 5) 1) 14) v2859_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2859 : Material (35 : Basis) (95 : Basis) where
  plus := ![v2859_pa,v2859_pb,v2859_pg]
  minus := ![(Primitive.Addresses.material2859 1).one,v2859_mb,v2859_mg]
  upper := v2859_upper
  lower := (Primitive.Addresses.material2859 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2859_pa_checked.trans (by decide +kernel)
    · exact v2859_pb_checked.trans (by decide +kernel)
    · exact v2859_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 95 Primitive.Addresses.material2859
    · exact v2859_mb_checked.trans (by decide +kernel)
    · exact v2859_mg_checked.trans (by decide +kernel)
  upper_error := v2859_upper_checked
  lower_error := reuse_lower_error 35 95 Primitive.Addresses.material2859

def v2860_pa : Scalar.QComplex := ((999998251777599834584702979587 : Int)/10^30,(-1869877467656442496315843886 : Int)/10^30)
theorem v2860_pa_checked : Scalar.distance (sourceCoefficient 35 96 1 0) v2860_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2860_pb : Scalar.QComplex := ((-806809924108286765777422 : Int)/10^30,(-431476675654204852687954840 : Int)/10^30)
theorem v2860_pb_checked : Scalar.distance (sourceCoefficient 35 96 1 1) v2860_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2860_pg : Scalar.QComplex := ((-93086257342083318583933 : Int)/10^30,(174060199448370336300 : Int)/10^30)
theorem v2860_pg_checked : Scalar.distance (sourceCoefficient 35 96 1 2) v2860_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2860_mb : Scalar.QComplex := ((-1179154561797572734430060 : Int)/10^30,(-431475818755091913012864571 : Int)/10^30)
theorem v2860_mb_checked : Scalar.distance (sourceCoefficient 35 96 3 1) v2860_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2860_mg : Scalar.QComplex := ((-93086072475702714429537 : Int)/10^30,(254389382274621391296 : Int)/10^30)
theorem v2860_mg_checked : Scalar.distance (sourceCoefficient 35 96 3 2) v2860_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2860_upper : Scalar.QComplex := ((999993535158796641922020096321 : Int)/10^30,(-3595780946129000684608020529 : Int)/10^30)
theorem v2860_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 96 5) 1) 14) v2860_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2860 : Material (35 : Basis) (96 : Basis) where
  plus := ![v2860_pa,v2860_pb,v2860_pg]
  minus := ![(Primitive.Addresses.material2860 1).one,v2860_mb,v2860_mg]
  upper := v2860_upper
  lower := (Primitive.Addresses.material2860 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2860_pa_checked.trans (by decide +kernel)
    · exact v2860_pb_checked.trans (by decide +kernel)
    · exact v2860_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 96 Primitive.Addresses.material2860
    · exact v2860_mb_checked.trans (by decide +kernel)
    · exact v2860_mg_checked.trans (by decide +kernel)
  upper_error := v2860_upper_checked
  lower_error := reuse_lower_error 35 96 Primitive.Addresses.material2860

def v2861_pa : Scalar.QComplex := ((999998112296856340203106850523 : Int)/10^30,(-1943039557985486615403986624 : Int)/10^30)
theorem v2861_pa_checked : Scalar.distance (sourceCoefficient 35 97 1 0) v2861_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2861_pb : Scalar.QComplex := ((-838377691063706078594023 : Int)/10^30,(-431476603247706637417396799 : Int)/10^30)
theorem v2861_pb_checked : Scalar.distance (sourceCoefficient 35 97 1 1) v2861_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2861_pg : Scalar.QComplex := ((-93086243039756593764659 : Int)/10^30,(180870593960487046756 : Int)/10^30)
theorem v2861_pg_checked : Scalar.distance (sourceCoefficient 35 97 1 2) v2861_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2861_mb : Scalar.QComplex := ((-1210722254515322799367066 : Int)/10^30,(-431475719107059534909346167 : Int)/10^30)
theorem v2861_mb_checked : Scalar.distance (sourceCoefficient 35 97 3 1) v2861_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2861_mg : Scalar.QComplex := ((-93086052296317579845948 : Int)/10^30,(261199761908653163850 : Int)/10^30)
theorem v2861_mg_checked : Scalar.distance (sourceCoefficient 35 97 3 2) v2861_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2861_upper : Scalar.QComplex := ((999993269407130192780738525986 : Int)/10^30,(-3668942686760595804328946572 : Int)/10^30)
theorem v2861_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 97 5) 1) 14) v2861_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2861 : Material (35 : Basis) (97 : Basis) where
  plus := ![v2861_pa,v2861_pb,v2861_pg]
  minus := ![(Primitive.Addresses.material2861 1).one,v2861_mb,v2861_mg]
  upper := v2861_upper
  lower := (Primitive.Addresses.material2861 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2861_pa_checked.trans (by decide +kernel)
    · exact v2861_pb_checked.trans (by decide +kernel)
    · exact v2861_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 97 Primitive.Addresses.material2861
    · exact v2861_mb_checked.trans (by decide +kernel)
    · exact v2861_mg_checked.trans (by decide +kernel)
  upper_error := v2861_upper_checked
  lower_error := reuse_lower_error 35 97 Primitive.Addresses.material2861

def v2862_pa : Scalar.QComplex := ((999999692686781394737270089644 : Int)/10^30,(-783981085721531377746254074 : Int)/10^30)
theorem v2862_pa_checked : Scalar.distance (sourceCoefficient 36 37 1 0) v2862_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2862_pb : Scalar.QComplex := ((-338270215375846987359232 : Int)/10^30,(-431477388398489062264484636 : Int)/10^30)
theorem v2862_pb_checked : Scalar.distance (sourceCoefficient 36 37 1 1) v2862_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2862_pg : Scalar.QComplex := ((-93086401289916985869280 : Int)/10^30,(72978000376283460526 : Int)/10^30)
theorem v2862_pg_checked : Scalar.distance (sourceCoefficient 36 37 1 2) v2862_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2862_mb : Scalar.QComplex := ((-710615642590096301569728 : Int)/10^30,(-431476935827777126284740834 : Int)/10^30)
theorem v2862_mb_checked : Scalar.distance (sourceCoefficient 36 37 3 1) v2862_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2862_mg : Scalar.QComplex := ((-93086303652868009321899 : Int)/10^30,(153307345060554199879 : Int)/10^30)
theorem v2862_mg_checked : Scalar.distance (sourceCoefficient 36 37 3 2) v2862_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2862_upper : Scalar.QComplex := ((999996850224475606528753483965 : Int)/10^30,(-2509888668387721221568334934 : Int)/10^30)
theorem v2862_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 37 5) 1) 14) v2862_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2862 : Material (36 : Basis) (37 : Basis) where
  plus := ![v2862_pa,v2862_pb,v2862_pg]
  minus := ![(Primitive.Addresses.material2862 1).one,v2862_mb,v2862_mg]
  upper := v2862_upper
  lower := (Primitive.Addresses.material2862 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2862_pa_checked.trans (by decide +kernel)
    · exact v2862_pb_checked.trans (by decide +kernel)
    · exact v2862_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 37 Primitive.Addresses.material2862
    · exact v2862_mb_checked.trans (by decide +kernel)
    · exact v2862_mg_checked.trans (by decide +kernel)
  upper_error := v2862_upper_checked
  lower_error := reuse_lower_error 36 37 Primitive.Addresses.material2862

def v2863_pa : Scalar.QComplex := ((999999674147756976237500121130 : Int)/10^30,(-807282094356019218242324424 : Int)/10^30)
theorem v2863_pa_checked : Scalar.distance (sourceCoefficient 36 38 1 0) v2863_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2863_pb : Scalar.QComplex := ((-348324076768019849126674 : Int)/10^30,(-431477380337168602490122584 : Int)/10^30)
theorem v2863_pb_checked : Scalar.distance (sourceCoefficient 36 38 1 1) v2863_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2863_pg : Scalar.QComplex := ((-93086399557481505019685 : Int)/10^30,(75147008077646028564 : Int)/10^30)
theorem v2863_pg_checked : Scalar.distance (sourceCoefficient 36 38 1 2) v2863_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2863_mb : Scalar.QComplex := ((-720669493282200594477115 : Int)/10^30,(-431476919090430095771266056 : Int)/10^30)
theorem v2863_mb_checked : Scalar.distance (sourceCoefficient 36 38 3 1) v2863_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2863_mg : Scalar.QComplex := ((-93086300048677215741815 : Int)/10^30,(155476350459282278176 : Int)/10^30)
theorem v2863_mg_checked : Scalar.distance (sourceCoefficient 36 38 3 2) v2863_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2863_upper : Scalar.QComplex := ((999996791470051747592918363969 : Int)/10^30,(-2533189610321419530568555765 : Int)/10^30)
theorem v2863_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 38 5) 1) 14) v2863_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2863 : Material (36 : Basis) (38 : Basis) where
  plus := ![v2863_pa,v2863_pb,v2863_pg]
  minus := ![(Primitive.Addresses.material2863 1).one,v2863_mb,v2863_mg]
  upper := v2863_upper
  lower := (Primitive.Addresses.material2863 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2863_pa_checked.trans (by decide +kernel)
    · exact v2863_pb_checked.trans (by decide +kernel)
    · exact v2863_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 38 Primitive.Addresses.material2863
    · exact v2863_mb_checked.trans (by decide +kernel)
    · exact v2863_mg_checked.trans (by decide +kernel)
  upper_error := v2863_upper_checked
  lower_error := reuse_lower_error 36 38 Primitive.Addresses.material2863

def v2864_pa : Scalar.QComplex := ((999999663144047150018048337138 : Int)/10^30,(-820799483569544488572783075 : Int)/10^30)
theorem v2864_pa_checked : Scalar.distance (sourceCoefficient 36 39 1 0) v2864_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2864_pb : Scalar.QComplex := ((-354156526296417148501907 : Int)/10^30,(-431477375517471498837181495 : Int)/10^30)
theorem v2864_pb_checked : Scalar.distance (sourceCoefficient 36 39 1 1) v2864_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2864_pg : Scalar.QComplex := ((-93086398525435709656675 : Int)/10^30,(76405293574604407933 : Int)/10^30)
theorem v2864_pg_checked : Scalar.distance (sourceCoefficient 36 39 1 2) v2864_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2864_mb : Scalar.QComplex := ((-726501936479728848965449 : Int)/10^30,(-431476909237593527480437241 : Int)/10^30)
theorem v2864_mb_checked : Scalar.distance (sourceCoefficient 36 39 3 1) v2864_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2864_mg : Scalar.QComplex := ((-93086297930788091856595 : Int)/10^30,(156734634597114420758 : Int)/10^30)
theorem v2864_mg_checked : Scalar.distance (sourceCoefficient 36 39 3 2) v2864_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2864_upper : Scalar.QComplex := ((999996757136570815532264670299 : Int)/10^30,(-2546706960410976520134282304 : Int)/10^30)
theorem v2864_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 39 5) 1) 14) v2864_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2864 : Material (36 : Basis) (39 : Basis) where
  plus := ![v2864_pa,v2864_pb,v2864_pg]
  minus := ![(Primitive.Addresses.material2864 1).one,v2864_mb,v2864_mg]
  upper := v2864_upper
  lower := (Primitive.Addresses.material2864 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2864_pa_checked.trans (by decide +kernel)
    · exact v2864_pb_checked.trans (by decide +kernel)
    · exact v2864_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 39 Primitive.Addresses.material2864
    · exact v2864_mb_checked.trans (by decide +kernel)
    · exact v2864_mg_checked.trans (by decide +kernel)
  upper_error := v2864_upper_checked
  lower_error := reuse_lower_error 36 39 Primitive.Addresses.material2864

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
