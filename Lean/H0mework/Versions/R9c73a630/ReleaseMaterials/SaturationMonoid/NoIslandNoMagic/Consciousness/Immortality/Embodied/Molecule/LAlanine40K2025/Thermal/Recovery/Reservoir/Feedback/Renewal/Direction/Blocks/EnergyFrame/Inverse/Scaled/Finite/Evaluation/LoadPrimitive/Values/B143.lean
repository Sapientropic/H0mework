import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B095
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B096

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2289_pa : Scalar.QComplex := ((999999654103193470091074722461 : Int)/10^30,(-831741241862646295797705668 : Int)/10^30)
theorem v2289_pa_checked : Scalar.distance (sourceCoefficient 27 49 1 0) v2289_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2289_pb : Scalar.QComplex := ((-358877643081023848885174 : Int)/10^30,(-431477364453761433734131578 : Int)/10^30)
theorem v2289_pb_checked : Scalar.distance (sourceCoefficient 27 49 1 1) v2289_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2289_pg : Scalar.QComplex := ((-93086396911209715837946 : Int)/10^30,(77423822148101601715 : Int)/10^30)
theorem v2289_pg_checked : Scalar.distance (sourceCoefficient 27 49 1 2) v2289_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2289_mb : Scalar.QComplex := ((-731223041958964509563512 : Int)/10^30,(-431476894099776427993435926 : Int)/10^30)
theorem v2289_mb_checked : Scalar.distance (sourceCoefficient 27 49 3 1) v2289_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2289_mg : Scalar.QComplex := ((-93086295437618412983970 : Int)/10^30,(157753161398362546946 : Int)/10^30)
theorem v2289_mg_checked : Scalar.distance (sourceCoefficient 27 49 3 2) v2289_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2289_upper : Scalar.QComplex := ((999996729211248415559476185486 : Int)/10^30,(-2557648686803921387286212048 : Int)/10^30)
theorem v2289_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 49 5) 1) 14) v2289_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2289 : Material (27 : Basis) (49 : Basis) where
  plus := ![v2289_pa,v2289_pb,v2289_pg]
  minus := ![(Primitive.Addresses.material2289 1).one,v2289_mb,v2289_mg]
  upper := v2289_upper
  lower := (Primitive.Addresses.material2289 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2289_pa_checked.trans (by decide +kernel)
    · exact v2289_pb_checked.trans (by decide +kernel)
    · exact v2289_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 49 Primitive.Addresses.material2289
    · exact v2289_mb_checked.trans (by decide +kernel)
    · exact v2289_mg_checked.trans (by decide +kernel)
  upper_error := v2289_upper_checked
  lower_error := reuse_lower_error 27 49 Primitive.Addresses.material2289

def v2290_pa : Scalar.QComplex := ((999999651957909934417364127804 : Int)/10^30,(-834316522069333596704470714 : Int)/10^30)
theorem v2290_pa_checked : Scalar.distance (sourceCoefficient 27 50 1 0) v2290_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2290_pb : Scalar.QComplex := ((-359988818482830183612455 : Int)/10^30,(-431477363409631148484964993 : Int)/10^30)
theorem v2290_pb_checked : Scalar.distance (sourceCoefficient 27 50 1 1) v2290_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2290_pg : Scalar.QComplex := ((-93086396698731631174607 : Int)/10^30,(77663545775834864746 : Int)/10^30)
theorem v2290_pg_checked : Scalar.distance (sourceCoefficient 27 50 1 2) v2290_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2290_mb : Scalar.QComplex := ((-732334216045992048686024 : Int)/10^30,(-431476892096752205245148509 : Int)/10^30)
theorem v2290_mb_checked : Scalar.distance (sourceCoefficient 27 50 3 1) v2290_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2290_mg : Scalar.QComplex := ((-93086295018269713453525 : Int)/10^30,(157992884753476730054 : Int)/10^30)
theorem v2290_mg_checked : Scalar.distance (sourceCoefficient 27 50 3 2) v2290_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2290_upper : Scalar.QComplex := ((999996722621268065886659955456 : Int)/10^30,(-2560223959472466570025000459 : Int)/10^30)
theorem v2290_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 50 5) 1) 14) v2290_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2290 : Material (27 : Basis) (50 : Basis) where
  plus := ![v2290_pa,v2290_pb,v2290_pg]
  minus := ![(Primitive.Addresses.material2290 1).one,v2290_mb,v2290_mg]
  upper := v2290_upper
  lower := (Primitive.Addresses.material2290 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2290_pa_checked.trans (by decide +kernel)
    · exact v2290_pb_checked.trans (by decide +kernel)
    · exact v2290_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 50 Primitive.Addresses.material2290
    · exact v2290_mb_checked.trans (by decide +kernel)
    · exact v2290_mg_checked.trans (by decide +kernel)
  upper_error := v2290_upper_checked
  lower_error := reuse_lower_error 27 50 Primitive.Addresses.material2290

def v2291_pa : Scalar.QComplex := ((999999642466922037259579175390 : Int)/10^30,(-845615768594447985615632109 : Int)/10^30)
theorem v2291_pa_checked : Scalar.distance (sourceCoefficient 27 51 1 0) v2291_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2291_pb : Scalar.QComplex := ((-364864188829685207468749 : Int)/10^30,(-431477358783330882786188062 : Int)/10^30)
theorem v2291_pb_checked : Scalar.distance (sourceCoefficient 27 51 1 1) v2291_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2291_pg : Scalar.QComplex := ((-93086395757954375994117 : Int)/10^30,(78715352237891720746 : Int)/10^30)
theorem v2291_pg_checked : Scalar.distance (sourceCoefficient 27 51 1 2) v2291_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2291_mb : Scalar.QComplex := ((-737209580585235108507240 : Int)/10^30,(-431476883263228631322791473 : Int)/10^30)
theorem v2291_mb_checked : Scalar.distance (sourceCoefficient 27 51 3 1) v2291_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2291_mg : Scalar.QComplex := ((-93086293169831203416871 : Int)/10^30,(159044690012049570115 : Int)/10^30)
theorem v2291_mg_checked : Scalar.distance (sourceCoefficient 27 51 3 2) v2291_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2291_upper : Scalar.QComplex := ((999996693628819861730454722702 : Int)/10^30,(-2571523172788096467714859103 : Int)/10^30)
theorem v2291_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 51 5) 1) 14) v2291_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2291 : Material (27 : Basis) (51 : Basis) where
  plus := ![v2291_pa,v2291_pb,v2291_pg]
  minus := ![(Primitive.Addresses.material2291 1).one,v2291_mb,v2291_mg]
  upper := v2291_upper
  lower := (Primitive.Addresses.material2291 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2291_pa_checked.trans (by decide +kernel)
    · exact v2291_pb_checked.trans (by decide +kernel)
    · exact v2291_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 51 Primitive.Addresses.material2291
    · exact v2291_mb_checked.trans (by decide +kernel)
    · exact v2291_mg_checked.trans (by decide +kernel)
  upper_error := v2291_upper_checked
  lower_error := reuse_lower_error 27 51 Primitive.Addresses.material2291

def v2292_pa : Scalar.QComplex := ((999999621719827506012380607528 : Int)/10^30,(-869804691808503834023492785 : Int)/10^30)
theorem v2292_pa_checked : Scalar.distance (sourceCoefficient 27 52 1 0) v2292_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2292_pb : Scalar.QComplex := ((-375301164218741796500909 : Int)/10^30,(-431477348632627192829336044 : Int)/10^30)
theorem v2292_pb_checked : Scalar.distance (sourceCoefficient 27 52 1 1) v2292_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2292_pg : Scalar.QComplex := ((-93086393697367729259782 : Int)/10^30,(80967012609719487789 : Int)/10^30)
theorem v2292_pg_checked : Scalar.distance (sourceCoefficient 27 52 1 2) v2292_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2292_mb : Scalar.QComplex := ((-747646543328528653144861 : Int)/10^30,(-431476864105889024102927068 : Int)/10^30)
theorem v2292_mb_checked : Scalar.distance (sourceCoefficient 27 52 3 1) v2292_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2292_mg : Scalar.QComplex := ((-93086289166163834064347 : Int)/10^30,(161296347767287804009 : Int)/10^30)
theorem v2292_mg_checked : Scalar.distance (sourceCoefficient 27 52 3 2) v2292_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2292_upper : Scalar.QComplex := ((999996631133869165355292823011 : Int)/10^30,(-2595712024167989620087433741 : Int)/10^30)
theorem v2292_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 52 5) 1) 14) v2292_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2292 : Material (27 : Basis) (52 : Basis) where
  plus := ![v2292_pa,v2292_pb,v2292_pg]
  minus := ![(Primitive.Addresses.material2292 1).one,v2292_mb,v2292_mg]
  upper := v2292_upper
  lower := (Primitive.Addresses.material2292 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2292_pa_checked.trans (by decide +kernel)
    · exact v2292_pb_checked.trans (by decide +kernel)
    · exact v2292_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 52 Primitive.Addresses.material2292
    · exact v2292_mb_checked.trans (by decide +kernel)
    · exact v2292_mg_checked.trans (by decide +kernel)
  upper_error := v2292_upper_checked
  lower_error := reuse_lower_error 27 52 Primitive.Addresses.material2292

def v2293_pa : Scalar.QComplex := ((999999618492355524455104570297 : Int)/10^30,(-873507380279644230082202779 : Int)/10^30)
theorem v2293_pa_checked : Scalar.distance (sourceCoefficient 27 53 1 0) v2293_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2293_pb : Scalar.QComplex := ((-376898790860652589143580 : Int)/10^30,(-431477347049114263581289715 : Int)/10^30)
theorem v2293_pb_checked : Scalar.distance (sourceCoefficient 27 53 1 1) v2293_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2293_pg : Scalar.QComplex := ((-93086393376338240939134 : Int)/10^30,(81311682638874155543 : Int)/10^30)
theorem v2293_pg_checked : Scalar.distance (sourceCoefficient 27 53 1 2) v2293_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2293_mb : Scalar.QComplex := ((-749244168009069692693379 : Int)/10^30,(-431476861143696846932977922 : Int)/10^30)
theorem v2293_mb_checked : Scalar.distance (sourceCoefficient 27 53 3 1) v2293_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2293_mg : Scalar.QComplex := ((-93086288547699753479030 : Int)/10^30,(161641017391072077921 : Int)/10^30)
theorem v2293_mg_checked : Scalar.distance (sourceCoefficient 27 53 3 2) v2293_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2293_upper : Scalar.QComplex := ((999996621515897594824238080028 : Int)/10^30,(-2599414701554086640526925951 : Int)/10^30)
theorem v2293_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 53 5) 1) 14) v2293_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2293 : Material (27 : Basis) (53 : Basis) where
  plus := ![v2293_pa,v2293_pb,v2293_pg]
  minus := ![(Primitive.Addresses.material2293 1).one,v2293_mb,v2293_mg]
  upper := v2293_upper
  lower := (Primitive.Addresses.material2293 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2293_pa_checked.trans (by decide +kernel)
    · exact v2293_pb_checked.trans (by decide +kernel)
    · exact v2293_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 53 Primitive.Addresses.material2293
    · exact v2293_mb_checked.trans (by decide +kernel)
    · exact v2293_mg_checked.trans (by decide +kernel)
  upper_error := v2293_upper_checked
  lower_error := reuse_lower_error 27 53 Primitive.Addresses.material2293

def v2294_pa : Scalar.QComplex := ((999999616846232238850498735896 : Int)/10^30,(-875389849561604896818903031 : Int)/10^30)
theorem v2294_pa_checked : Scalar.distance (sourceCoefficient 27 54 1 0) v2294_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2294_pb : Scalar.QComplex := ((-377711033936574835152469 : Int)/10^30,(-431477346241022343496507410 : Int)/10^30)
theorem v2294_pb_checked : Scalar.distance (sourceCoefficient 27 54 1 1) v2294_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2294_pg : Scalar.QComplex := ((-93086393212553992416028 : Int)/10^30,(81486914972588533561 : Int)/10^30)
theorem v2294_pg_checked : Scalar.distance (sourceCoefficient 27 54 1 2) v2294_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2294_mb : Scalar.QComplex := ((-750056410085209788269878 : Int)/10^30,(-431476859634676035287000046 : Int)/10^30)
theorem v2294_mb_checked : Scalar.distance (sourceCoefficient 27 54 3 1) v2294_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2294_mg : Scalar.QComplex := ((-93086288232697954116117 : Int)/10^30,(161816249518201019676 : Int)/10^30)
theorem v2294_mg_checked : Scalar.distance (sourceCoefficient 27 54 3 2) v2294_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2294_upper : Scalar.QComplex := ((999996616620805556542016529544 : Int)/10^30,(-2601297165191270986343012149 : Int)/10^30)
theorem v2294_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 54 5) 1) 14) v2294_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2294 : Material (27 : Basis) (54 : Basis) where
  plus := ![v2294_pa,v2294_pb,v2294_pg]
  minus := ![(Primitive.Addresses.material2294 1).one,v2294_mb,v2294_mg]
  upper := v2294_upper
  lower := (Primitive.Addresses.material2294 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2294_pa_checked.trans (by decide +kernel)
    · exact v2294_pb_checked.trans (by decide +kernel)
    · exact v2294_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 54 Primitive.Addresses.material2294
    · exact v2294_mb_checked.trans (by decide +kernel)
    · exact v2294_mg_checked.trans (by decide +kernel)
  upper_error := v2294_upper_checked
  lower_error := reuse_lower_error 27 54 Primitive.Addresses.material2294

def v2295_pa : Scalar.QComplex := ((999999603296891094282908921405 : Int)/10^30,(-890733439609223140058179612 : Int)/10^30)
theorem v2295_pa_checked : Scalar.distance (sourceCoefficient 27 55 1 0) v2295_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2295_pb : Scalar.QComplex := ((-384331447261598339621724 : Int)/10^30,(-431477339578414975201241211 : Int)/10^30)
theorem v2295_pb_checked : Scalar.distance (sourceCoefficient 27 55 1 1) v2295_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2295_pg : Scalar.QComplex := ((-93086391863232734413488 : Int)/10^30,(82915194897864886636 : Int)/10^30)
theorem v2295_pg_checked : Scalar.distance (sourceCoefficient 27 55 1 2) v2295_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2295_mb : Scalar.QComplex := ((-756676815195620757854605 : Int)/10^30,(-431476847258952620637150138 : Int)/10^30)
theorem v2295_mb_checked : Scalar.distance (sourceCoefficient 27 55 3 1) v2295_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2295_mg : Scalar.QComplex := ((-93086285650835950353947 : Int)/10^30,(163244527747260006471 : Int)/10^30)
theorem v2295_mg_checked : Scalar.distance (sourceCoefficient 27 55 3 2) v2295_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2295_upper : Scalar.QComplex := ((999996576589840129553084424828 : Int)/10^30,(-2616640709001480609455624299 : Int)/10^30)
theorem v2295_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 55 5) 1) 14) v2295_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2295 : Material (27 : Basis) (55 : Basis) where
  plus := ![v2295_pa,v2295_pb,v2295_pg]
  minus := ![(Primitive.Addresses.material2295 1).one,v2295_mb,v2295_mg]
  upper := v2295_upper
  lower := (Primitive.Addresses.material2295 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2295_pa_checked.trans (by decide +kernel)
    · exact v2295_pb_checked.trans (by decide +kernel)
    · exact v2295_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 55 Primitive.Addresses.material2295
    · exact v2295_mb_checked.trans (by decide +kernel)
    · exact v2295_mg_checked.trans (by decide +kernel)
  upper_error := v2295_upper_checked
  lower_error := reuse_lower_error 27 55 Primitive.Addresses.material2295

def v2296_pa : Scalar.QComplex := ((999999600046687280404546765184 : Int)/10^30,(-894374902083314584717727891 : Int)/10^30)
theorem v2296_pa_checked : Scalar.distance (sourceCoefficient 27 56 1 0) v2296_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2296_pb : Scalar.QComplex := ((-385902656247667873041717 : Int)/10^30,(-431477337977305812486866651 : Int)/10^30)
theorem v2296_pb_checked : Scalar.distance (sourceCoefficient 27 56 1 1) v2296_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2296_pg : Scalar.QComplex := ((-93086391539247138641055 : Int)/10^30,(83254165615982578648 : Int)/10^30)
theorem v2296_pg_checked : Scalar.distance (sourceCoefficient 27 56 1 2) v2296_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2296_mb : Scalar.QComplex := ((-758248022214972281820157 : Int)/10^30,(-431476844301961463736710001 : Int)/10^30)
theorem v2296_mb_checked : Scalar.distance (sourceCoefficient 27 56 3 1) v2296_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2296_mg : Scalar.QComplex := ((-93086285034334012155008 : Int)/10^30,(163583498059578431019 : Int)/10^30)
theorem v2296_mg_checked : Scalar.distance (sourceCoefficient 27 56 3 2) v2296_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2296_upper : Scalar.QComplex := ((999996567054807277084763798753 : Int)/10^30,(-2620282160442484528619060686 : Int)/10^30)
theorem v2296_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 56 5) 1) 14) v2296_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2296 : Material (27 : Basis) (56 : Basis) where
  plus := ![v2296_pa,v2296_pb,v2296_pg]
  minus := ![(Primitive.Addresses.material2296 1).one,v2296_mb,v2296_mg]
  upper := v2296_upper
  lower := (Primitive.Addresses.material2296 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2296_pa_checked.trans (by decide +kernel)
    · exact v2296_pb_checked.trans (by decide +kernel)
    · exact v2296_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 56 Primitive.Addresses.material2296
    · exact v2296_mb_checked.trans (by decide +kernel)
    · exact v2296_mg_checked.trans (by decide +kernel)
  upper_error := v2296_upper_checked
  lower_error := reuse_lower_error 27 56 Primitive.Addresses.material2296

def v2297_pa : Scalar.QComplex := ((999999589443509234732468509609 : Int)/10^30,(-906152753664581076457817446 : Int)/10^30)
theorem v2297_pa_checked : Scalar.distance (sourceCoefficient 27 57 1 0) v2297_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2297_pb : Scalar.QComplex := ((-390984533733310157760708 : Int)/10^30,(-431477332746480520216132768 : Int)/10^30)
theorem v2297_pb_checked : Scalar.distance (sourceCoefficient 27 57 1 1) v2297_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2297_pg : Scalar.QComplex := ((-93086390481495235293317 : Int)/10^30,(84350523694158358693 : Int)/10^30)
theorem v2297_pg_checked : Scalar.distance (sourceCoefficient 27 57 1 2) v2297_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2297_mb : Scalar.QComplex := ((-763329893294432685755985 : Int)/10^30,(-431476834685706728297556857 : Int)/10^30)
theorem v2297_mb_checked : Scalar.distance (sourceCoefficient 27 57 3 1) v2297_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2297_mg : Scalar.QComplex := ((-93086283030474859325786 : Int)/10^30,(164679854816737739308 : Int)/10^30)
theorem v2297_mg_checked : Scalar.distance (sourceCoefficient 27 57 3 2) v2297_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2297_upper : Scalar.QComplex := ((999996536124141672683840717194 : Int)/10^30,(-2632059976181901219664926787 : Int)/10^30)
theorem v2297_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 57 5) 1) 14) v2297_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2297 : Material (27 : Basis) (57 : Basis) where
  plus := ![v2297_pa,v2297_pb,v2297_pg]
  minus := ![(Primitive.Addresses.material2297 1).one,v2297_mb,v2297_mg]
  upper := v2297_upper
  lower := (Primitive.Addresses.material2297 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2297_pa_checked.trans (by decide +kernel)
    · exact v2297_pb_checked.trans (by decide +kernel)
    · exact v2297_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 57 Primitive.Addresses.material2297
    · exact v2297_mb_checked.trans (by decide +kernel)
    · exact v2297_mg_checked.trans (by decide +kernel)
  upper_error := v2297_upper_checked
  lower_error := reuse_lower_error 27 57 Primitive.Addresses.material2297

def v2298_pa : Scalar.QComplex := ((999999583632274933776359979693 : Int)/10^30,(-912543301312526650239769629 : Int)/10^30)
theorem v2298_pa_checked : Scalar.distance (sourceCoefficient 27 58 1 0) v2298_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2298_pb : Scalar.QComplex := ((-393741910986967661499231 : Int)/10^30,(-431477329874887499796330051 : Int)/10^30)
theorem v2298_pb_checked : Scalar.distance (sourceCoefficient 27 58 1 1) v2298_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2298_pg : Scalar.QComplex := ((-93086389901264734407518 : Int)/10^30,(84945396916286831312 : Int)/10^30)
theorem v2298_pg_checked : Scalar.distance (sourceCoefficient 27 58 1 2) v2298_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2298_mb : Scalar.QComplex := ((-766087267043337174718223 : Int)/10^30,(-431476829434622394858090245 : Int)/10^30)
theorem v2298_mb_checked : Scalar.distance (sourceCoefficient 27 58 3 1) v2298_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2298_mg : Scalar.QComplex := ((-93086281936895775884803 : Int)/10^30,(165274727316654934626 : Int)/10^30)
theorem v2298_mg_checked : Scalar.distance (sourceCoefficient 27 58 3 2) v2298_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2298_upper : Scalar.QComplex := ((999996519283410532478422340103 : Int)/10^30,(-2638450504282213545898871039 : Int)/10^30)
theorem v2298_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 58 5) 1) 14) v2298_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2298 : Material (27 : Basis) (58 : Basis) where
  plus := ![v2298_pa,v2298_pb,v2298_pg]
  minus := ![(Primitive.Addresses.material2298 1).one,v2298_mb,v2298_mg]
  upper := v2298_upper
  lower := (Primitive.Addresses.material2298 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2298_pa_checked.trans (by decide +kernel)
    · exact v2298_pb_checked.trans (by decide +kernel)
    · exact v2298_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 58 Primitive.Addresses.material2298
    · exact v2298_mb_checked.trans (by decide +kernel)
    · exact v2298_mg_checked.trans (by decide +kernel)
  upper_error := v2298_upper_checked
  lower_error := reuse_lower_error 27 58 Primitive.Addresses.material2298

def v2299_pa : Scalar.QComplex := ((999999567448325066944120038536 : Int)/10^30,(-930109220879548249052557797 : Int)/10^30)
theorem v2299_pa_checked : Scalar.distance (sourceCoefficient 27 59 1 0) v2299_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2299_pb : Scalar.QComplex := ((-401321209255109996889875 : Int)/10^30,(-431477321860591409344666997 : Int)/10^30)
theorem v2299_pb_checked : Scalar.distance (sourceCoefficient 27 59 1 1) v2299_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2299_pg : Scalar.QComplex := ((-93086388283514484802560 : Int)/10^30,(86580545531430752382 : Int)/10^30)
theorem v2299_pg_checked : Scalar.distance (sourceCoefficient 27 59 1 2) v2299_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2299_mb : Scalar.QComplex := ((-773666555573383798273573 : Int)/10^30,(-431476814879736242010455944 : Int)/10^30)
theorem v2299_mb_checked : Scalar.distance (sourceCoefficient 27 59 3 1) v2299_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2299_mg : Scalar.QComplex := ((-93086278908086518132813 : Int)/10^30,(166909873926912691652 : Int)/10^30)
theorem v2299_mg_checked : Scalar.distance (sourceCoefficient 27 59 3 2) v2299_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2299_upper : Scalar.QComplex := ((999996472782301164833981081564 : Int)/10^30,(-2656016369754832113804485661 : Int)/10^30)
theorem v2299_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 59 5) 1) 14) v2299_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2299 : Material (27 : Basis) (59 : Basis) where
  plus := ![v2299_pa,v2299_pb,v2299_pg]
  minus := ![(Primitive.Addresses.material2299 1).one,v2299_mb,v2299_mg]
  upper := v2299_upper
  lower := (Primitive.Addresses.material2299 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2299_pa_checked.trans (by decide +kernel)
    · exact v2299_pb_checked.trans (by decide +kernel)
    · exact v2299_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 59 Primitive.Addresses.material2299
    · exact v2299_mb_checked.trans (by decide +kernel)
    · exact v2299_mg_checked.trans (by decide +kernel)
  upper_error := v2299_upper_checked
  lower_error := reuse_lower_error 27 59 Primitive.Addresses.material2299

def v2300_pa : Scalar.QComplex := ((999999548395343393134015612330 : Int)/10^30,(-950373142122064653082913083 : Int)/10^30)
theorem v2300_pa_checked : Scalar.distance (sourceCoefficient 27 60 1 0) v2300_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2300_pb : Scalar.QComplex := ((-410064634322173088504280 : Int)/10^30,(-431477312394847318158540773 : Int)/10^30)
theorem v2300_pb_checked : Scalar.distance (sourceCoefficient 27 60 1 1) v2300_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2300_pg : Scalar.QComplex := ((-93086386375663467535278 : Int)/10^30,(88466841460665398374 : Int)/10^30)
theorem v2300_pg_checked : Scalar.distance (sourceCoefficient 27 60 1 2) v2300_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2300_mb : Scalar.QComplex := ((-782409969216359313748916 : Int)/10^30,(-431476797868813631724889227 : Int)/10^30)
theorem v2300_mb_checked : Scalar.distance (sourceCoefficient 27 60 3 1) v2300_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2300_mg : Scalar.QComplex := ((-93086275372447779931111 : Int)/10^30,(168796167507403653726 : Int)/10^30)
theorem v2300_mg_checked : Scalar.distance (sourceCoefficient 27 60 3 2) v2300_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2300_upper : Scalar.QComplex := ((999996418755658132193532320066 : Int)/10^30,(-2676280227932900298506610802 : Int)/10^30)
theorem v2300_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 60 5) 1) 14) v2300_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2300 : Material (27 : Basis) (60 : Basis) where
  plus := ![v2300_pa,v2300_pb,v2300_pg]
  minus := ![(Primitive.Addresses.material2300 1).one,v2300_mb,v2300_mg]
  upper := v2300_upper
  lower := (Primitive.Addresses.material2300 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2300_pa_checked.trans (by decide +kernel)
    · exact v2300_pb_checked.trans (by decide +kernel)
    · exact v2300_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 60 Primitive.Addresses.material2300
    · exact v2300_mb_checked.trans (by decide +kernel)
    · exact v2300_mg_checked.trans (by decide +kernel)
  upper_error := v2300_upper_checked
  lower_error := reuse_lower_error 27 60 Primitive.Addresses.material2300

def v2301_pa : Scalar.QComplex := ((999999542809622322335269295686 : Int)/10^30,(-956232475045837386646385485 : Int)/10^30)
theorem v2301_pa_checked : Scalar.distance (sourceCoefficient 27 61 1 0) v2301_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2301_pb : Scalar.QComplex := ((-412592804331572221815097 : Int)/10^30,(-431477309613788624054897301 : Int)/10^30)
theorem v2301_pb_checked : Scalar.distance (sourceCoefficient 27 61 1 1) v2301_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2301_pg : Scalar.QComplex := ((-93086385815694959473990 : Int)/10^30,(89012265797165139352 : Int)/10^30)
theorem v2301_pg_checked : Scalar.distance (sourceCoefficient 27 61 1 2) v2301_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2301_mb : Scalar.QComplex := ((-784938135884476810705546 : Int)/10^30,(-431476792906059119575418727 : Int)/10^30)
theorem v2301_mb_checked : Scalar.distance (sourceCoefficient 27 61 3 1) v2301_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2301_mg : Scalar.QComplex := ((-93086274341802842972634 : Int)/10^30,(169341591157589384690 : Int)/10^30)
theorem v2301_mg_checked : Scalar.distance (sourceCoefficient 27 61 3 2) v2301_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2301_upper : Scalar.QComplex := ((999996403057268308769006478782 : Int)/10^30,(-2682139542489437092163777312 : Int)/10^30)
theorem v2301_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 61 5) 1) 14) v2301_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2301 : Material (27 : Basis) (61 : Basis) where
  plus := ![v2301_pa,v2301_pb,v2301_pg]
  minus := ![(Primitive.Addresses.material2301 1).one,v2301_mb,v2301_mg]
  upper := v2301_upper
  lower := (Primitive.Addresses.material2301 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2301_pa_checked.trans (by decide +kernel)
    · exact v2301_pb_checked.trans (by decide +kernel)
    · exact v2301_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 61 Primitive.Addresses.material2301
    · exact v2301_mb_checked.trans (by decide +kernel)
    · exact v2301_mg_checked.trans (by decide +kernel)
  upper_error := v2301_upper_checked
  lower_error := reuse_lower_error 27 61 Primitive.Addresses.material2301

def v2302_pa : Scalar.QComplex := ((999999534632629257412201320088 : Int)/10^30,(-964745834361769009390604559 : Int)/10^30)
theorem v2302_pa_checked : Scalar.distance (sourceCoefficient 27 62 1 0) v2302_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2302_pb : Scalar.QComplex := ((-416266126855937243072579 : Int)/10^30,(-431477305537832611698637182 : Int)/10^30)
theorem v2302_pb_checked : Scalar.distance (sourceCoefficient 27 62 1 1) v2302_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2302_pg : Scalar.QComplex := ((-93086384995440544333299 : Int)/10^30,(89804743952344716742 : Int)/10^30)
theorem v2302_pg_checked : Scalar.distance (sourceCoefficient 27 62 1 2) v2302_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2302_mb : Scalar.QComplex := ((-788611453523729512589917 : Int)/10^30,(-431476785660192726661913651 : Int)/10^30)
theorem v2302_mb_checked : Scalar.distance (sourceCoefficient 27 62 3 1) v2302_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2302_mg : Scalar.QComplex := ((-93086272837675777221338 : Int)/10^30,(170134068309850509487 : Int)/10^30)
theorem v2302_mg_checked : Scalar.distance (sourceCoefficient 27 62 3 2) v2302_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2302_upper : Scalar.QComplex := ((999996380187001569142653053828 : Int)/10^30,(-2690652875012971844221659760 : Int)/10^30)
theorem v2302_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 62 5) 1) 14) v2302_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2302 : Material (27 : Basis) (62 : Basis) where
  plus := ![v2302_pa,v2302_pb,v2302_pg]
  minus := ![(Primitive.Addresses.material2302 1).one,v2302_mb,v2302_mg]
  upper := v2302_upper
  lower := (Primitive.Addresses.material2302 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2302_pa_checked.trans (by decide +kernel)
    · exact v2302_pb_checked.trans (by decide +kernel)
    · exact v2302_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 62 Primitive.Addresses.material2302
    · exact v2302_mb_checked.trans (by decide +kernel)
    · exact v2302_mg_checked.trans (by decide +kernel)
  upper_error := v2302_upper_checked
  lower_error := reuse_lower_error 27 62 Primitive.Addresses.material2302

def v2303_pa : Scalar.QComplex := ((999999510404188418356774980903 : Int)/10^30,(-989540996350948428834541451 : Int)/10^30)
theorem v2303_pa_checked : Scalar.distance (sourceCoefficient 27 63 1 0) v2303_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2303_pb : Scalar.QComplex := ((-426964679882702090802309 : Int)/10^30,(-431477293429040355522146459 : Int)/10^30)
theorem v2303_pb_checked : Scalar.distance (sourceCoefficient 27 63 1 1) v2303_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2303_pg : Scalar.QComplex := ((-93086382561603037829005 : Int)/10^30,(92112836844773333220 : Int)/10^30)
theorem v2303_pg_checked : Scalar.distance (sourceCoefficient 27 63 1 2) v2303_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2303_mb : Scalar.QComplex := ((-799309992117591763105450 : Int)/10^30,(-431476764319035561985515938 : Int)/10^30)
theorem v2303_mb_checked : Scalar.distance (sourceCoefficient 27 63 3 1) v2303_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2303_mg : Scalar.QComplex := ((-93086268412058963425055 : Int)/10^30,(172442158242578504917 : Int)/10^30)
theorem v2303_mg_checked : Scalar.distance (sourceCoefficient 27 63 3 2) v2303_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2303_upper : Scalar.QComplex := ((999996313164396621704419500944 : Int)/10^30,(-2715447958256579223885726421 : Int)/10^30)
theorem v2303_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 63 5) 1) 14) v2303_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2303 : Material (27 : Basis) (63 : Basis) where
  plus := ![v2303_pa,v2303_pb,v2303_pg]
  minus := ![(Primitive.Addresses.material2303 1).one,v2303_mb,v2303_mg]
  upper := v2303_upper
  lower := (Primitive.Addresses.material2303 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2303_pa_checked.trans (by decide +kernel)
    · exact v2303_pb_checked.trans (by decide +kernel)
    · exact v2303_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 63 Primitive.Addresses.material2303
    · exact v2303_mb_checked.trans (by decide +kernel)
    · exact v2303_mg_checked.trans (by decide +kernel)
  upper_error := v2303_upper_checked
  lower_error := reuse_lower_error 27 63 Primitive.Addresses.material2303

def v2304_pa : Scalar.QComplex := ((999999474709655724423539525640 : Int)/10^30,(-1024978249828359592881905905 : Int)/10^30)
theorem v2304_pa_checked : Scalar.distance (sourceCoefficient 27 64 1 0) v2304_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2304_pb : Scalar.QComplex := ((-442255055004403621127440 : Int)/10^30,(-431477275509165638861953713 : Int)/10^30)
theorem v2304_pb_checked : Scalar.distance (sourceCoefficient 27 64 1 1) v2304_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2304_pg : Scalar.QComplex := ((-93086378967258860669372 : Int)/10^30,(95411563915493667364 : Int)/10^30)
theorem v2304_pg_checked : Scalar.distance (sourceCoefficient 27 64 1 2) v2304_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2304_mb : Scalar.QComplex := ((-814600346081943031675618 : Int)/10^30,(-431476733204262440616721241 : Int)/10^30)
theorem v2304_mb_checked : Scalar.distance (sourceCoefficient 27 64 3 1) v2304_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2304_mg : Scalar.QComplex := ((-93086261971063231724500 : Int)/10^30,(175740880983274849720 : Int)/10^30)
theorem v2304_mg_checked : Scalar.distance (sourceCoefficient 27 64 3 2) v2304_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2304_upper : Scalar.QComplex := ((999996216308432431095487277391 : Int)/10^30,(-2750885097348838838521946731 : Int)/10^30)
theorem v2304_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 64 5) 1) 14) v2304_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2304 : Material (27 : Basis) (64 : Basis) where
  plus := ![v2304_pa,v2304_pb,v2304_pg]
  minus := ![(Primitive.Addresses.material2304 1).one,v2304_mb,v2304_mg]
  upper := v2304_upper
  lower := (Primitive.Addresses.material2304 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2304_pa_checked.trans (by decide +kernel)
    · exact v2304_pb_checked.trans (by decide +kernel)
    · exact v2304_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 64 Primitive.Addresses.material2304
    · exact v2304_mb_checked.trans (by decide +kernel)
    · exact v2304_mg_checked.trans (by decide +kernel)
  upper_error := v2304_upper_checked
  lower_error := reuse_lower_error 27 64 Primitive.Addresses.material2304

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
