import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B068
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B069

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1649_pa : Scalar.QComplex := ((999999384904005624756865256379 : Int)/10^30,(-1109140031919957333670425460 : Int)/10^30)
theorem v1649_pa_checked : Scalar.distance (sourceCoefficient 18 75 1 0) v1649_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1649_pb : Scalar.QComplex := ((-478568921687609179396108 : Int)/10^30,(-431477192734054162995997289 : Int)/10^30)
theorem v1649_pb_checked : Scalar.distance (sourceCoefficient 18 75 1 1) v1649_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1649_pg : Scalar.QComplex := ((-93086365858514748148721 : Int)/10^30,(103245878305752055934 : Int)/10^30)
theorem v1649_pg_checked : Scalar.distance (sourceCoefficient 18 75 1 2) v1649_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1649_mb : Scalar.QComplex := ((-850914127812643247048995 : Int)/10^30,(-431476619091950353943589641 : Int)/10^30)
theorem v1649_mb_checked : Scalar.distance (sourceCoefficient 18 75 3 1) v1649_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1649_mg : Scalar.QComplex := ((-93086242101663525817328 : Int)/10^30,(183575181144204171754 : Int)/10^30)
theorem v1649_mg_checked : Scalar.distance (sourceCoefficient 18 75 3 2) v1649_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1649_upper : Scalar.QComplex := ((999995981247315293526866406199 : Int)/10^30,(-2835046599094943524188105875 : Int)/10^30)
theorem v1649_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 75 5) 1) 14) v1649_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1649 : Material (18 : Basis) (75 : Basis) where
  plus := ![v1649_pa,v1649_pb,v1649_pg]
  minus := ![(Primitive.Addresses.material1649 1).one,v1649_mb,v1649_mg]
  upper := v1649_upper
  lower := (Primitive.Addresses.material1649 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1649_pa_checked.trans (by decide +kernel)
    · exact v1649_pb_checked.trans (by decide +kernel)
    · exact v1649_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 75 Primitive.Addresses.material1649
    · exact v1649_mb_checked.trans (by decide +kernel)
    · exact v1649_mg_checked.trans (by decide +kernel)
  upper_error := v1649_upper_checked
  lower_error := reuse_lower_error 18 75 Primitive.Addresses.material1649

def v1650_pa : Scalar.QComplex := ((999999371039935170991955682416 : Int)/10^30,(-1121570209156454431066601437 : Int)/10^30)
theorem v1650_pa_checked : Scalar.distance (sourceCoefficient 18 76 1 0) v1650_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1650_pb : Scalar.QComplex := ((-483932261078540511723852 : Int)/10^30,(-431477185069354577880305434 : Int)/10^30)
theorem v1650_pb_checked : Scalar.distance (sourceCoefficient 18 76 1 1) v1650_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1650_pg : Scalar.QComplex := ((-93086364386449900756389 : Int)/10^30,(104402958839816306371 : Int)/10^30)
theorem v1650_pg_checked : Scalar.distance (sourceCoefficient 18 76 1 2) v1650_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1650_mb : Scalar.QComplex := ((-856277458592267670713677 : Int)/10^30,(-431476606798933284211300902 : Int)/10^30)
theorem v1650_mb_checked : Scalar.distance (sourceCoefficient 18 76 3 1) v1650_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1650_mg : Scalar.QComplex := ((-93086239631090838617297 : Int)/10^30,(184732259977108794206 : Int)/10^30)
theorem v1650_mg_checked : Scalar.distance (sourceCoefficient 18 76 3 2) v1650_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1650_upper : Scalar.QComplex := ((999995945929907235342442450208 : Int)/10^30,(-2847476733890023914458497376 : Int)/10^30)
theorem v1650_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 76 5) 1) 14) v1650_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1650 : Material (18 : Basis) (76 : Basis) where
  plus := ![v1650_pa,v1650_pb,v1650_pg]
  minus := ![(Primitive.Addresses.material1650 1).one,v1650_mb,v1650_mg]
  upper := v1650_upper
  lower := (Primitive.Addresses.material1650 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1650_pa_checked.trans (by decide +kernel)
    · exact v1650_pb_checked.trans (by decide +kernel)
    · exact v1650_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 76 Primitive.Addresses.material1650
    · exact v1650_mb_checked.trans (by decide +kernel)
    · exact v1650_mg_checked.trans (by decide +kernel)
  upper_error := v1650_upper_checked
  lower_error := reuse_lower_error 18 76 Primitive.Addresses.material1650

def v1651_pa : Scalar.QComplex := ((999999367808259389469152763985 : Int)/10^30,(-1124447900773826336329368867 : Int)/10^30)
theorem v1651_pa_checked : Scalar.distance (sourceCoefficient 18 77 1 0) v1651_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1651_pb : Scalar.QComplex := ((-485173919696463147615806 : Int)/10^30,(-431477183282240064591557476 : Int)/10^30)
theorem v1651_pb_checked : Scalar.distance (sourceCoefficient 18 77 1 1) v1651_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1651_pg : Scalar.QComplex := ((-93086364043262375379250 : Int)/10^30,(104670832811150553229 : Int)/10^30)
theorem v1651_pg_checked : Scalar.distance (sourceCoefficient 18 77 1 2) v1651_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1651_mb : Scalar.QComplex := ((-857519115205664720232465 : Int)/10^30,(-431476603940323971307947179 : Int)/10^30)
theorem v1651_mb_checked : Scalar.distance (sourceCoefficient 18 77 3 1) v1651_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1651_mg : Scalar.QComplex := ((-93086239056740268358913 : Int)/10^30,(185000133552545941284 : Int)/10^30)
theorem v1651_mg_checked : Scalar.distance (sourceCoefficient 18 77 3 2) v1651_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1651_upper : Scalar.QComplex := ((999995937731601597581410744744 : Int)/10^30,(-2850354415643832969477402725 : Int)/10^30)
theorem v1651_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 77 5) 1) 14) v1651_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1651 : Material (18 : Basis) (77 : Basis) where
  plus := ![v1651_pa,v1651_pb,v1651_pg]
  minus := ![(Primitive.Addresses.material1651 1).one,v1651_mb,v1651_mg]
  upper := v1651_upper
  lower := (Primitive.Addresses.material1651 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1651_pa_checked.trans (by decide +kernel)
    · exact v1651_pb_checked.trans (by decide +kernel)
    · exact v1651_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 77 Primitive.Addresses.material1651
    · exact v1651_mb_checked.trans (by decide +kernel)
    · exact v1651_mg_checked.trans (by decide +kernel)
  upper_error := v1651_upper_checked
  lower_error := reuse_lower_error 18 77 Primitive.Addresses.material1651

def v1652_pa : Scalar.QComplex := ((999999348206134771221551775254 : Int)/10^30,(-1141747478920936416436894968 : Int)/10^30)
theorem v1652_pa_checked : Scalar.distance (sourceCoefficient 18 78 1 0) v1652_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1652_pb : Scalar.QComplex := ((-492638294942079584771369 : Int)/10^30,(-431477172438385822997727296 : Int)/10^30)
theorem v1652_pb_checked : Scalar.distance (sourceCoefficient 18 78 1 1) v1652_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1652_pg : Scalar.QComplex := ((-93086361961196579324725 : Int)/10^30,(106281188364544514144 : Int)/10^30)
theorem v1652_pg_checked : Scalar.distance (sourceCoefficient 18 78 1 2) v1652_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1652_mb : Scalar.QComplex := ((-864983478314195293213417 : Int)/10^30,(-431476586655054113391018183 : Int)/10^30)
theorem v1652_mb_checked : Scalar.distance (sourceCoefficient 18 78 3 1) v1652_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1652_mg : Scalar.QComplex := ((-93086235585010932695420 : Int)/10^30,(186610486709601923553 : Int)/10^30)
theorem v1652_mg_checked : Scalar.distance (sourceCoefficient 18 78 3 2) v1652_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1652_upper : Scalar.QComplex := ((999995888272003697953786139664 : Int)/10^30,(-2867653934193764750423222306 : Int)/10^30)
theorem v1652_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 78 5) 1) 14) v1652_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1652 : Material (18 : Basis) (78 : Basis) where
  plus := ![v1652_pa,v1652_pb,v1652_pg]
  minus := ![(Primitive.Addresses.material1652 1).one,v1652_mb,v1652_mg]
  upper := v1652_upper
  lower := (Primitive.Addresses.material1652 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1652_pa_checked.trans (by decide +kernel)
    · exact v1652_pb_checked.trans (by decide +kernel)
    · exact v1652_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 78 Primitive.Addresses.material1652
    · exact v1652_mb_checked.trans (by decide +kernel)
    · exact v1652_mg_checked.trans (by decide +kernel)
  upper_error := v1652_upper_checked
  lower_error := reuse_lower_error 18 78 Primitive.Addresses.material1652

def v1653_pa : Scalar.QComplex := ((999999341822964613454389233051 : Int)/10^30,(-1147324556337953271871560994 : Int)/10^30)
theorem v1653_pa_checked : Scalar.distance (sourceCoefficient 18 79 1 0) v1653_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1653_pb : Scalar.QComplex := ((-495044677211863331440553 : Int)/10^30,(-431477168905819339298907097 : Int)/10^30)
theorem v1653_pb_checked : Scalar.distance (sourceCoefficient 18 79 1 1) v1653_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1653_pg : Scalar.QComplex := ((-93086361283047541740464 : Int)/10^30,(106800338453717093264 : Int)/10^30)
theorem v1653_pg_checked : Scalar.distance (sourceCoefficient 18 79 1 2) v1653_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1653_mb : Scalar.QComplex := ((-867389856639527169195645 : Int)/10^30,(-431476581045889425638970102 : Int)/10^30)
theorem v1653_mb_checked : Scalar.distance (sourceCoefficient 18 79 3 1) v1653_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1653_mg : Scalar.QComplex := ((-93086234458859002313152 : Int)/10^30,(187129636020259121406 : Int)/10^30)
theorem v1653_mg_checked : Scalar.distance (sourceCoefficient 18 79 3 2) v1653_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1653_upper : Scalar.QComplex := ((999995872263313373908680167039 : Int)/10^30,(-2873230992287607307112116049 : Int)/10^30)
theorem v1653_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 79 5) 1) 14) v1653_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1653 : Material (18 : Basis) (79 : Basis) where
  plus := ![v1653_pa,v1653_pb,v1653_pg]
  minus := ![(Primitive.Addresses.material1653 1).one,v1653_mb,v1653_mg]
  upper := v1653_upper
  lower := (Primitive.Addresses.material1653 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1653_pa_checked.trans (by decide +kernel)
    · exact v1653_pb_checked.trans (by decide +kernel)
    · exact v1653_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 79 Primitive.Addresses.material1653
    · exact v1653_mb_checked.trans (by decide +kernel)
    · exact v1653_mg_checked.trans (by decide +kernel)
  upper_error := v1653_upper_checked
  lower_error := reuse_lower_error 18 79 Primitive.Addresses.material1653

def v1654_pa : Scalar.QComplex := ((999999331789579261703848758280 : Int)/10^30,(-1156036502439012917534997062 : Int)/10^30)
theorem v1654_pa_checked : Scalar.distance (sourceCoefficient 18 80 1 0) v1654_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1654_pb : Scalar.QComplex := ((-498803684109332993038681 : Int)/10^30,(-431477163351792952465371714 : Int)/10^30)
theorem v1654_pb_checked : Scalar.distance (sourceCoefficient 18 80 1 1) v1654_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1654_pg : Scalar.QComplex := ((-93086360216952115549059 : Int)/10^30,(107611302196976916580 : Int)/10^30)
theorem v1654_pg_checked : Scalar.distance (sourceCoefficient 18 80 1 2) v1654_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1654_mb : Scalar.QComplex := ((-871148857344472139989092 : Int)/10^30,(-431476572248011453692945535 : Int)/10^30)
theorem v1654_mb_checked : Scalar.distance (sourceCoefficient 18 80 3 1) v1654_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1654_mg : Scalar.QComplex := ((-93086232692938787095714 : Int)/10^30,(187940598541567742585 : Int)/10^30)
theorem v1654_mg_checked : Scalar.distance (sourceCoefficient 18 80 3 2) v1654_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1654_upper : Scalar.QComplex := ((999995847193914336854547018101 : Int)/10^30,(-2881942908096533716811976097 : Int)/10^30)
theorem v1654_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 80 5) 1) 14) v1654_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1654 : Material (18 : Basis) (80 : Basis) where
  plus := ![v1654_pa,v1654_pb,v1654_pg]
  minus := ![(Primitive.Addresses.material1654 1).one,v1654_mb,v1654_mg]
  upper := v1654_upper
  lower := (Primitive.Addresses.material1654 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1654_pa_checked.trans (by decide +kernel)
    · exact v1654_pb_checked.trans (by decide +kernel)
    · exact v1654_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 80 Primitive.Addresses.material1654
    · exact v1654_mb_checked.trans (by decide +kernel)
    · exact v1654_mg_checked.trans (by decide +kernel)
  upper_error := v1654_upper_checked
  lower_error := reuse_lower_error 18 80 Primitive.Addresses.material1654

def v1655_pa : Scalar.QComplex := ((999999301120206202505567929296 : Int)/10^30,(-1182268623943823811444527718 : Int)/10^30)
theorem v1655_pa_checked : Scalar.distance (sourceCoefficient 18 81 1 0) v1655_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1655_pb : Scalar.QComplex := ((-510122248609878344510380 : Int)/10^30,(-431477146364653221192115553 : Int)/10^30)
theorem v1655_pb_checked : Scalar.distance (sourceCoefficient 18 81 1 1) v1655_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1655_pg : Scalar.QComplex := ((-93086356957108563002326 : Int)/10^30,(110053156061551346119 : Int)/10^30)
theorem v1655_pg_checked : Scalar.distance (sourceCoefficient 18 81 1 2) v1655_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1655_mb : Scalar.QComplex := ((-882467402971462128239591 : Int)/10^30,(-431476545493466652759105196 : Int)/10^30)
theorem v1655_mb_checked : Scalar.distance (sourceCoefficient 18 81 3 1) v1655_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1655_mg : Scalar.QComplex := ((-93086227325886540225507 : Int)/10^30,(190382448683830212164 : Int)/10^30)
theorem v1655_mg_checked : Scalar.distance (sourceCoefficient 18 81 3 2) v1655_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1655_upper : Scalar.QComplex := ((999995771250324998254412953175 : Int)/10^30,(-2908174937599125474370624591 : Int)/10^30)
theorem v1655_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 81 5) 1) 14) v1655_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1655 : Material (18 : Basis) (81 : Basis) where
  plus := ![v1655_pa,v1655_pb,v1655_pg]
  minus := ![(Primitive.Addresses.material1655 1).one,v1655_mb,v1655_mg]
  upper := v1655_upper
  lower := (Primitive.Addresses.material1655 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1655_pa_checked.trans (by decide +kernel)
    · exact v1655_pb_checked.trans (by decide +kernel)
    · exact v1655_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 81 Primitive.Addresses.material1655
    · exact v1655_mb_checked.trans (by decide +kernel)
    · exact v1655_mg_checked.trans (by decide +kernel)
  upper_error := v1655_upper_checked
  lower_error := reuse_lower_error 18 81 Primitive.Addresses.material1655

def v1656_pa : Scalar.QComplex := ((999999289318745647445134886726 : Int)/10^30,(-1192208875842343509813338134 : Int)/10^30)
theorem v1656_pa_checked : Scalar.distance (sourceCoefficient 18 82 1 0) v1656_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1656_pb : Scalar.QComplex := ((-514411241403921645109855 : Int)/10^30,(-431477139824213590720136956 : Int)/10^30)
theorem v1656_pb_checked : Scalar.distance (sourceCoefficient 18 82 1 1) v1656_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1656_pg : Scalar.QComplex := ((-93086355702317441451733 : Int)/10^30,(110978458358430391626 : Int)/10^30)
theorem v1656_pg_checked : Scalar.distance (sourceCoefficient 18 82 1 2) v1656_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1656_mb : Scalar.QComplex := ((-886756388524412564331307 : Int)/10^30,(-431476535251821845397016428 : Int)/10^30)
theorem v1656_mb_checked : Scalar.distance (sourceCoefficient 18 82 3 1) v1656_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1656_mg : Scalar.QComplex := ((-93086225272601677752817 : Int)/10^30,(191307749553348699935 : Int)/10^30)
theorem v1656_mg_checked : Scalar.distance (sourceCoefficient 18 82 3 2) v1656_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1656_upper : Scalar.QComplex := ((999995742292909015846153020973 : Int)/10^30,(-2918115154324557336010289632 : Int)/10^30)
theorem v1656_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 82 5) 1) 14) v1656_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1656 : Material (18 : Basis) (82 : Basis) where
  plus := ![v1656_pa,v1656_pb,v1656_pg]
  minus := ![(Primitive.Addresses.material1656 1).one,v1656_mb,v1656_mg]
  upper := v1656_upper
  lower := (Primitive.Addresses.material1656 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1656_pa_checked.trans (by decide +kernel)
    · exact v1656_pb_checked.trans (by decide +kernel)
    · exact v1656_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 82 Primitive.Addresses.material1656
    · exact v1656_mb_checked.trans (by decide +kernel)
    · exact v1656_mg_checked.trans (by decide +kernel)
  upper_error := v1656_upper_checked
  lower_error := reuse_lower_error 18 82 Primitive.Addresses.material1656

def v1657_pa : Scalar.QComplex := ((999999273050061804853317334785 : Int)/10^30,(-1205777486907962104120118668 : Int)/10^30)
theorem v1657_pa_checked : Scalar.distance (sourceCoefficient 18 83 1 0) v1657_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1657_pb : Scalar.QComplex := ((-520265788647068760526386 : Int)/10^30,(-431477130804647462894662219 : Int)/10^30)
theorem v1657_pb_checked : Scalar.distance (sourceCoefficient 18 83 1 1) v1657_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1657_pg : Scalar.QComplex := ((-93086353972185533274461 : Int)/10^30,(112241511551966753687 : Int)/10^30)
theorem v1657_pg_checked : Scalar.distance (sourceCoefficient 18 83 1 2) v1657_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1657_mb : Scalar.QComplex := ((-892610925804164832962313 : Int)/10^30,(-431476521180048484151871050 : Int)/10^30)
theorem v1657_mb_checked : Scalar.distance (sourceCoefficient 18 83 3 1) v1657_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1657_mg : Scalar.QComplex := ((-93086222452512393564981 : Int)/10^30,(192570800783566719151 : Int)/10^30)
theorem v1657_mg_checked : Scalar.distance (sourceCoefficient 18 83 3 2) v1657_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1657_upper : Scalar.QComplex := ((999995702606057639070509487635 : Int)/10^30,(-2931683717103051200253730327 : Int)/10^30)
theorem v1657_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 83 5) 1) 14) v1657_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1657 : Material (18 : Basis) (83 : Basis) where
  plus := ![v1657_pa,v1657_pb,v1657_pg]
  minus := ![(Primitive.Addresses.material1657 1).one,v1657_mb,v1657_mg]
  upper := v1657_upper
  lower := (Primitive.Addresses.material1657 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1657_pa_checked.trans (by decide +kernel)
    · exact v1657_pb_checked.trans (by decide +kernel)
    · exact v1657_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 83 Primitive.Addresses.material1657
    · exact v1657_mb_checked.trans (by decide +kernel)
    · exact v1657_mg_checked.trans (by decide +kernel)
  upper_error := v1657_upper_checked
  lower_error := reuse_lower_error 18 83 Primitive.Addresses.material1657

def v1658_pa : Scalar.QComplex := ((999999230062801525814578021667 : Int)/10^30,(-1240916517798470297112629083 : Int)/10^30)
theorem v1658_pa_checked : Scalar.distance (sourceCoefficient 18 84 1 0) v1658_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1658_pb : Scalar.QComplex := ((-535427481316755178661819 : Int)/10^30,(-431477106954084143085957017 : Int)/10^30)
theorem v1658_pb_checked : Scalar.distance (sourceCoefficient 18 84 1 1) v1658_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1658_pg : Scalar.QComplex := ((-93086349398674618722051 : Int)/10^30,(115512477487728343056 : Int)/10^30)
theorem v1658_pg_checked : Scalar.distance (sourceCoefficient 18 84 1 2) v1658_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1658_mb : Scalar.QComplex := ((-907772592246498191088592 : Int)/10^30,(-431476484245636128347524130 : Int)/10^30)
theorem v1658_mb_checked : Scalar.distance (sourceCoefficient 18 84 3 1) v1658_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1658_mg : Scalar.QComplex := ((-93086215056306898214467 : Int)/10^30,(195841761554664264135 : Int)/10^30)
theorem v1658_mg_checked : Scalar.distance (sourceCoefficient 18 84 3 2) v1658_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1658_upper : Scalar.QComplex := ((999995598972081855469930146711 : Int)/10^30,(-2966822621465989134527527868 : Int)/10^30)
theorem v1658_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 84 5) 1) 14) v1658_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1658 : Material (18 : Basis) (84 : Basis) where
  plus := ![v1658_pa,v1658_pb,v1658_pg]
  minus := ![(Primitive.Addresses.material1658 1).one,v1658_mb,v1658_mg]
  upper := v1658_upper
  lower := (Primitive.Addresses.material1658 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1658_pa_checked.trans (by decide +kernel)
    · exact v1658_pb_checked.trans (by decide +kernel)
    · exact v1658_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 84 Primitive.Addresses.material1658
    · exact v1658_mb_checked.trans (by decide +kernel)
    · exact v1658_mg_checked.trans (by decide +kernel)
  upper_error := v1658_upper_checked
  lower_error := reuse_lower_error 18 84 Primitive.Addresses.material1658

def v1659_pa : Scalar.QComplex := ((999999128834903230383182714816 : Int)/10^30,(-1319973270415203447560018146 : Int)/10^30)
theorem v1659_pa_checked : Scalar.distance (sourceCoefficient 18 85 1 0) v1659_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1659_pb : Scalar.QComplex := ((-569538669880531142423805 : Int)/10^30,(-431477050697526566518581047 : Int)/10^30)
theorem v1659_pb_checked : Scalar.distance (sourceCoefficient 18 85 1 1) v1659_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1659_pg : Scalar.QComplex := ((-93086338618842463545385 : Int)/10^30,(122871585859127524139 : Int)/10^30)
theorem v1659_pg_checked : Scalar.distance (sourceCoefficient 18 85 1 2) v1659_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1659_mb : Scalar.QComplex := ((-941883719562244206945508 : Int)/10^30,(-431476398552680079031299913 : Int)/10^30)
theorem v1659_mb_checked : Scalar.distance (sourceCoefficient 18 85 3 1) v1659_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1659_mg : Scalar.QComplex := ((-93086197925899674281826 : Int)/10^30,(203200857883421426378 : Int)/10^30)
theorem v1659_mg_checked : Scalar.distance (sourceCoefficient 18 85 3 2) v1659_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1659_upper : Scalar.QComplex := ((999995361299551283193578795841 : Int)/10^30,(-3045879081626806786148020393 : Int)/10^30)
theorem v1659_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 85 5) 1) 14) v1659_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1659 : Material (18 : Basis) (85 : Basis) where
  plus := ![v1659_pa,v1659_pb,v1659_pg]
  minus := ![(Primitive.Addresses.material1659 1).one,v1659_mb,v1659_mg]
  upper := v1659_upper
  lower := (Primitive.Addresses.material1659 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1659_pa_checked.trans (by decide +kernel)
    · exact v1659_pb_checked.trans (by decide +kernel)
    · exact v1659_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 85 Primitive.Addresses.material1659
    · exact v1659_mb_checked.trans (by decide +kernel)
    · exact v1659_mg_checked.trans (by decide +kernel)
  upper_error := v1659_upper_checked
  lower_error := reuse_lower_error 18 85 Primitive.Addresses.material1659

def v1660_pa : Scalar.QComplex := ((999999109477207030637222924712 : Int)/10^30,(-1334557901669268434666476732 : Int)/10^30)
theorem v1660_pa_checked : Scalar.distance (sourceCoefficient 18 86 1 0) v1660_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1660_pb : Scalar.QComplex := ((-575831605813668308458737 : Int)/10^30,(-431477039926291258105319424 : Int)/10^30)
theorem v1660_pb_checked : Scalar.distance (sourceCoefficient 18 86 1 1) v1660_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1660_pg : Scalar.QComplex := ((-93086336555986507951768 : Int)/10^30,(124229216617185620124 : Int)/10^30)
theorem v1660_pg_checked : Scalar.distance (sourceCoefficient 18 86 1 2) v1660_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1660_mb : Scalar.QComplex := ((-948176643857142770962735 : Int)/10^30,(-431476382350928494257099654 : Int)/10^30)
theorem v1660_mb_checked : Scalar.distance (sourceCoefficient 18 86 3 1) v1660_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1660_mg : Scalar.QComplex := ((-93086194691470287999141 : Int)/10^30,(204558486355819762253 : Int)/10^30)
theorem v1660_mg_checked : Scalar.distance (sourceCoefficient 18 86 3 2) v1660_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1660_upper : Scalar.QComplex := ((999995316770133477357846924904 : Int)/10^30,(-3060463657749149227179391665 : Int)/10^30)
theorem v1660_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 86 5) 1) 14) v1660_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1660 : Material (18 : Basis) (86 : Basis) where
  plus := ![v1660_pa,v1660_pb,v1660_pg]
  minus := ![(Primitive.Addresses.material1660 1).one,v1660_mb,v1660_mg]
  upper := v1660_upper
  lower := (Primitive.Addresses.material1660 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1660_pa_checked.trans (by decide +kernel)
    · exact v1660_pb_checked.trans (by decide +kernel)
    · exact v1660_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 86 Primitive.Addresses.material1660
    · exact v1660_mb_checked.trans (by decide +kernel)
    · exact v1660_mg_checked.trans (by decide +kernel)
  upper_error := v1660_upper_checked
  lower_error := reuse_lower_error 18 86 Primitive.Addresses.material1660

def v1661_pa : Scalar.QComplex := ((999999108187882799656828444075 : Int)/10^30,(-1335523657249033517753406297 : Int)/10^30)
theorem v1661_pa_checked : Scalar.distance (sourceCoefficient 18 87 1 0) v1661_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1661_pb : Scalar.QComplex := ((-576248307328248996856160 : Int)/10^30,(-431477039208728715490227368 : Int)/10^30)
theorem v1661_pb_checked : Scalar.distance (sourceCoefficient 18 87 1 1) v1661_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1661_pg : Scalar.QComplex := ((-93086336418574182146294 : Int)/10^30,(124319115322941536905 : Int)/10^30)
theorem v1661_pg_checked : Scalar.distance (sourceCoefficient 18 87 1 2) v1661_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1661_mb : Scalar.QComplex := ((-948593344597342284822151 : Int)/10^30,(-431476381273771579279735254 : Int)/10^30)
theorem v1661_mb_checked : Scalar.distance (sourceCoefficient 18 87 3 1) v1661_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1661_mg : Scalar.QComplex := ((-93086194476479479178605 : Int)/10^30,(204648384909521633959 : Int)/10^30)
theorem v1661_mg_checked : Scalar.distance (sourceCoefficient 18 87 3 2) v1661_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1661_upper : Scalar.QComplex := ((999995313814004648661710150933 : Int)/10^30,(-3061429409665278163734130185 : Int)/10^30)
theorem v1661_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 87 5) 1) 14) v1661_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1661 : Material (18 : Basis) (87 : Basis) where
  plus := ![v1661_pa,v1661_pb,v1661_pg]
  minus := ![(Primitive.Addresses.material1661 1).one,v1661_mb,v1661_mg]
  upper := v1661_upper
  lower := (Primitive.Addresses.material1661 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1661_pa_checked.trans (by decide +kernel)
    · exact v1661_pb_checked.trans (by decide +kernel)
    · exact v1661_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 87 Primitive.Addresses.material1661
    · exact v1661_mb_checked.trans (by decide +kernel)
    · exact v1661_mg_checked.trans (by decide +kernel)
  upper_error := v1661_upper_checked
  lower_error := reuse_lower_error 18 87 Primitive.Addresses.material1661

def v1662_pa : Scalar.QComplex := ((999999092413523448461131533592 : Int)/10^30,(-1347283240224513932810964854 : Int)/10^30)
theorem v1662_pa_checked : Scalar.distance (sourceCoefficient 18 88 1 0) v1662_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1662_pb : Scalar.QComplex := ((-581322299238065135488427 : Int)/10^30,(-431477030428238106899126819 : Int)/10^30)
theorem v1662_pb_checked : Scalar.distance (sourceCoefficient 18 88 1 1) v1662_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1662_pg : Scalar.QComplex := ((-93086334737238652175037 : Int)/10^30,(125413772509254521769 : Int)/10^30)
theorem v1662_pg_checked : Scalar.distance (sourceCoefficient 18 88 1 2) v1662_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1662_mb : Scalar.QComplex := ((-953667327040711405946626 : Int)/10^30,(-431476368114657746007653198 : Int)/10^30)
theorem v1662_mb_checked : Scalar.distance (sourceCoefficient 18 88 3 1) v1662_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1662_mg : Scalar.QComplex := ((-93086191850504724986813 : Int)/10^30,(205743040237326882229 : Int)/10^30)
theorem v1662_mg_checked : Scalar.distance (sourceCoefficient 18 88 3 2) v1662_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1662_upper : Scalar.QComplex := ((999995277743695396876071039993 : Int)/10^30,(-3073188947901127913004304773 : Int)/10^30)
theorem v1662_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 88 5) 1) 14) v1662_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1662 : Material (18 : Basis) (88 : Basis) where
  plus := ![v1662_pa,v1662_pb,v1662_pg]
  minus := ![(Primitive.Addresses.material1662 1).one,v1662_mb,v1662_mg]
  upper := v1662_upper
  lower := (Primitive.Addresses.material1662 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1662_pa_checked.trans (by decide +kernel)
    · exact v1662_pb_checked.trans (by decide +kernel)
    · exact v1662_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 88 Primitive.Addresses.material1662
    · exact v1662_mb_checked.trans (by decide +kernel)
    · exact v1662_mg_checked.trans (by decide +kernel)
  upper_error := v1662_upper_checked
  lower_error := reuse_lower_error 18 88 Primitive.Addresses.material1662

def v1663_pa : Scalar.QComplex := ((999999070606994963087861230607 : Int)/10^30,(-1363372709974226551005384780 : Int)/10^30)
theorem v1663_pa_checked : Scalar.distance (sourceCoefficient 18 89 1 0) v1663_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1663_pb : Scalar.QComplex := ((-588264538440958730921320 : Int)/10^30,(-431477018285874479290191718 : Int)/10^30)
theorem v1663_pb_checked : Scalar.distance (sourceCoefficient 18 89 1 1) v1663_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1663_pg : Scalar.QComplex := ((-93086332412503398387856 : Int)/10^30,(126911483233441216323 : Int)/10^30)
theorem v1663_pg_checked : Scalar.distance (sourceCoefficient 18 89 1 2) v1663_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1663_mb : Scalar.QComplex := ((-960609553180379131267352 : Int)/10^30,(-431476349981458874305416619 : Int)/10^30)
theorem v1663_mb_checked : Scalar.distance (sourceCoefficient 18 89 3 1) v1663_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1663_mg : Scalar.QComplex := ((-93086188233313436218688 : Int)/10^30,(207240748397705603578 : Int)/10^30)
theorem v1663_mg_checked : Scalar.distance (sourceCoefficient 18 89 3 2) v1663_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1663_upper : Scalar.QComplex := ((999995228168234227055152775959 : Int)/10^30,(-3089278356051375447940481526 : Int)/10^30)
theorem v1663_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 89 5) 1) 14) v1663_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1663 : Material (18 : Basis) (89 : Basis) where
  plus := ![v1663_pa,v1663_pb,v1663_pg]
  minus := ![(Primitive.Addresses.material1663 1).one,v1663_mb,v1663_mg]
  upper := v1663_upper
  lower := (Primitive.Addresses.material1663 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1663_pa_checked.trans (by decide +kernel)
    · exact v1663_pb_checked.trans (by decide +kernel)
    · exact v1663_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 89 Primitive.Addresses.material1663
    · exact v1663_mb_checked.trans (by decide +kernel)
    · exact v1663_mg_checked.trans (by decide +kernel)
  upper_error := v1663_upper_checked
  lower_error := reuse_lower_error 18 89 Primitive.Addresses.material1663

def v1664_pa : Scalar.QComplex := ((999999034539322600301095721342 : Int)/10^30,(-1389575626831831777819300054 : Int)/10^30)
theorem v1664_pa_checked : Scalar.distance (sourceCoefficient 18 90 1 0) v1664_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1664_pb : Scalar.QComplex := ((-599570499088387394261061 : Int)/10^30,(-431476998192346615769251158 : Int)/10^30)
theorem v1664_pb_checked : Scalar.distance (sourceCoefficient 18 90 1 1) v1664_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1664_pg : Scalar.QComplex := ((-93086328566321453351373 : Int)/10^30,(129350618249955499912 : Int)/10^30)
theorem v1664_pg_checked : Scalar.distance (sourceCoefficient 18 90 1 2) v1664_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1664_mb : Scalar.QComplex := ((-971915492278272370323930 : Int)/10^30,(-431476320131403655357392347 : Int)/10^30)
theorem v1664_mb_checked : Scalar.distance (sourceCoefficient 18 90 3 1) v1664_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1664_mg : Scalar.QComplex := ((-93086182282269258602846 : Int)/10^30,(209679879186936653579 : Int)/10^30)
theorem v1664_mg_checked : Scalar.distance (sourceCoefficient 18 90 3 2) v1664_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1664_upper : Scalar.QComplex := ((999995146876758196651301024928 : Int)/10^30,(-3115481171633283561691044220 : Int)/10^30)
theorem v1664_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 90 5) 1) 14) v1664_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1664 : Material (18 : Basis) (90 : Basis) where
  plus := ![v1664_pa,v1664_pb,v1664_pg]
  minus := ![(Primitive.Addresses.material1664 1).one,v1664_mb,v1664_mg]
  upper := v1664_upper
  lower := (Primitive.Addresses.material1664 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1664_pa_checked.trans (by decide +kernel)
    · exact v1664_pb_checked.trans (by decide +kernel)
    · exact v1664_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 90 Primitive.Addresses.material1664
    · exact v1664_mb_checked.trans (by decide +kernel)
    · exact v1664_mg_checked.trans (by decide +kernel)
  upper_error := v1664_upper_checked
  lower_error := reuse_lower_error 18 90 Primitive.Addresses.material1664

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
