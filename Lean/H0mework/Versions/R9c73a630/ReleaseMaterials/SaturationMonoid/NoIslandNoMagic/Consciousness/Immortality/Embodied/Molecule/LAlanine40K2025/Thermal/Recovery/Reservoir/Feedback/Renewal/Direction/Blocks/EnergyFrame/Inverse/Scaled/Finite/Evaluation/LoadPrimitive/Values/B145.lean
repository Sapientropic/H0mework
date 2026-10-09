import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B096
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B097

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2321_pa : Scalar.QComplex := ((999999086376467543518570492587 : Int)/10^30,(-1351756720051727281501057893 : Int)/10^30)
theorem v2321_pa_checked : Scalar.distance (sourceCoefficient 27 81 1 0) v2321_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2321_pb : Scalar.QComplex := ((-583252570197093132493422 : Int)/10^30,(-431477076216421915417288368 : Int)/10^30)
theorem v2321_pb_checked : Scalar.distance (sourceCoefficient 27 81 1 1) v2321_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2321_pg : Scalar.QComplex := ((-93086339395398033956143 : Int)/10^30,(125830199784176749281 : Int)/10^30)
theorem v2321_pg_checked : Scalar.distance (sourceCoefficient 27 81 1 2) v2321_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2321_mb : Scalar.QComplex := ((-955597636794151710670389 : Int)/10^30,(-431476412237087604027970085 : Int)/10^30)
theorem v2321_mb_checked : Scalar.distance (sourceCoefficient 27 81 3 1) v2321_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2321_mg : Scalar.QComplex := ((-93086196149304389252647 : Int)/10^30,(206159471376975954388 : Int)/10^30)
theorem v2321_mg_checked : Scalar.distance (sourceCoefficient 27 81 3 2) v2321_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2321_upper : Scalar.QComplex := ((999995263985828132568625793445 : Int)/10^30,(-3077662410646207736417023553 : Int)/10^30)
theorem v2321_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 81 5) 1) 14) v2321_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2321 : Material (27 : Basis) (81 : Basis) where
  plus := ![v2321_pa,v2321_pb,v2321_pg]
  minus := ![(Primitive.Addresses.material2321 1).one,v2321_mb,v2321_mg]
  upper := v2321_upper
  lower := (Primitive.Addresses.material2321 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2321_pa_checked.trans (by decide +kernel)
    · exact v2321_pb_checked.trans (by decide +kernel)
    · exact v2321_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 81 Primitive.Addresses.material2321
    · exact v2321_mb_checked.trans (by decide +kernel)
    · exact v2321_mg_checked.trans (by decide +kernel)
  upper_error := v2321_upper_checked
  lower_error := reuse_lower_error 27 81 Primitive.Addresses.material2321

def v2322_pa : Scalar.QComplex := ((999999072890251442613053862916 : Int)/10^30,(-1361696969807265166381245177 : Int)/10^30)
theorem v2322_pa_checked : Scalar.distance (sourceCoefficient 27 82 1 0) v2322_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2322_pb : Scalar.QComplex := ((-587541562374704169688155 : Int)/10^30,(-431477069191359565559434705 : Int)/10^30)
theorem v2322_pb_checked : Scalar.distance (sourceCoefficient 27 82 1 1) v2322_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2322_pg : Scalar.QComplex := ((-93086338009917020086827 : Int)/10^30,(126755501914820364850 : Int)/10^30)
theorem v2322_pg_checked : Scalar.distance (sourceCoefficient 27 82 1 2) v2322_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2322_mb : Scalar.QComplex := ((-959886621312462532650297 : Int)/10^30,(-431476401510820789680473271 : Int)/10^30)
theorem v2322_mb_checked : Scalar.distance (sourceCoefficient 27 82 3 1) v2322_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2322_mg : Scalar.QComplex := ((-93086193965329826576743 : Int)/10^30,(207084771967479583101 : Int)/10^30)
theorem v2322_mg_checked : Scalar.distance (sourceCoefficient 27 82 3 2) v2322_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2322_upper : Scalar.QComplex := ((999995233343662812152962811780 : Int)/10^30,(-3087602622320925743988329896 : Int)/10^30)
theorem v2322_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 82 5) 1) 14) v2322_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2322 : Material (27 : Basis) (82 : Basis) where
  plus := ![v2322_pa,v2322_pb,v2322_pg]
  minus := ![(Primitive.Addresses.material2322 1).one,v2322_mb,v2322_mg]
  upper := v2322_upper
  lower := (Primitive.Addresses.material2322 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2322_pa_checked.trans (by decide +kernel)
    · exact v2322_pb_checked.trans (by decide +kernel)
    · exact v2322_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 82 Primitive.Addresses.material2322
    · exact v2322_mb_checked.trans (by decide +kernel)
    · exact v2322_mg_checked.trans (by decide +kernel)
  upper_error := v2322_upper_checked
  lower_error := reuse_lower_error 27 82 Primitive.Addresses.material2322

def v2323_pa : Scalar.QComplex := ((999999054321847939712723190460 : Int)/10^30,(-1375265577920645576374979163 : Int)/10^30)
theorem v2323_pa_checked : Scalar.distance (sourceCoefficient 27 83 1 0) v2323_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2323_pb : Scalar.QComplex := ((-593396108768635089888589 : Int)/10^30,(-431477059510275275111541159 : Int)/10^30)
theorem v2323_pb_checked : Scalar.distance (sourceCoefficient 27 83 1 1) v2323_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2323_pg : Scalar.QComplex := ((-93086336101391210720742 : Int)/10^30,(128018554879345645195 : Int)/10^30)
theorem v2323_pg_checked : Scalar.distance (sourceCoefficient 27 83 1 2) v2323_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2323_mb : Scalar.QComplex := ((-965741157172138541596110 : Int)/10^30,(-431476386777530244961683097 : Int)/10^30)
theorem v2323_mb_checked : Scalar.distance (sourceCoefficient 27 83 3 1) v2323_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2323_mg : Scalar.QComplex := ((-93086190966846905250546 : Int)/10^30,(208347822814740703710 : Int)/10^30)
theorem v2323_mg_checked : Scalar.distance (sourceCoefficient 27 83 3 2) v2323_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2323_upper : Scalar.QComplex := ((999995191357100295526377307945 : Int)/10^30,(-3101171178178078316176075036 : Int)/10^30)
theorem v2323_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 83 5) 1) 14) v2323_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2323 : Material (27 : Basis) (83 : Basis) where
  plus := ![v2323_pa,v2323_pb,v2323_pg]
  minus := ![(Primitive.Addresses.material2323 1).one,v2323_mb,v2323_mg]
  upper := v2323_upper
  lower := (Primitive.Addresses.material2323 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2323_pa_checked.trans (by decide +kernel)
    · exact v2323_pb_checked.trans (by decide +kernel)
    · exact v2323_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 83 Primitive.Addresses.material2323
    · exact v2323_mb_checked.trans (by decide +kernel)
    · exact v2323_mg_checked.trans (by decide +kernel)
  upper_error := v2323_upper_checked
  lower_error := reuse_lower_error 27 83 Primitive.Addresses.material2323

def v2324_pa : Scalar.QComplex := ((999999005378936074412944386896 : Int)/10^30,(-1410404601020612562422806223 : Int)/10^30)
theorem v2324_pa_checked : Scalar.distance (sourceCoefficient 27 84 1 0) v2324_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2324_pb : Scalar.QComplex := ((-608557799197359458696286 : Int)/10^30,(-431477033946558937458132860 : Int)/10^30)
theorem v2324_pb_checked : Scalar.distance (sourceCoefficient 27 84 1 1) v2324_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2324_pg : Scalar.QComplex := ((-93086331065888369078598 : Int)/10^30,(131289520210779212036 : Int)/10^30)
theorem v2324_pg_checked : Scalar.distance (sourceCoefficient 27 84 1 2) v2324_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2324_mb : Scalar.QComplex := ((-980902819895136787954963 : Int)/10^30,(-431476348129967443047115969 : Int)/10^30)
theorem v2324_mb_checked : Scalar.distance (sourceCoefficient 27 84 3 1) v2324_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2324_mg : Scalar.QComplex := ((-93086183108650176338872 : Int)/10^30,(211618782582832225449 : Int)/10^30)
theorem v2324_mg_checked : Scalar.distance (sourceCoefficient 27 84 3 2) v2324_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2324_upper : Scalar.QComplex := ((999995081767495241675567041929 : Int)/10^30,(-3136310064471572301205993825 : Int)/10^30)
theorem v2324_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 84 5) 1) 14) v2324_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2324 : Material (27 : Basis) (84 : Basis) where
  plus := ![v2324_pa,v2324_pb,v2324_pg]
  minus := ![(Primitive.Addresses.material2324 1).one,v2324_mb,v2324_mg]
  upper := v2324_upper
  lower := (Primitive.Addresses.material2324 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2324_pa_checked.trans (by decide +kernel)
    · exact v2324_pb_checked.trans (by decide +kernel)
    · exact v2324_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 84 Primitive.Addresses.material2324
    · exact v2324_mb_checked.trans (by decide +kernel)
    · exact v2324_mg_checked.trans (by decide +kernel)
  upper_error := v2324_upper_checked
  lower_error := reuse_lower_error 27 84 Primitive.Addresses.material2324

def v2325_pa : Scalar.QComplex := ((999998890751850040555940086482 : Int)/10^30,(-1489461335344905799873877922 : Int)/10^30)
theorem v2325_pa_checked : Scalar.distance (sourceCoefficient 27 85 1 0) v2325_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2325_pb : Scalar.QComplex := ((-642668982499284919802914 : Int)/10^30,(-431476973835702915621385928 : Int)/10^30)
theorem v2325_pb_checked : Scalar.distance (sourceCoefficient 27 85 1 1) v2325_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2325_pg : Scalar.QComplex := ((-93086319246654154735171 : Int)/10^30,(138648627163196878185 : Int)/10^30)
theorem v2325_pg_checked : Scalar.distance (sourceCoefficient 27 85 1 2) v2325_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2325_mb : Scalar.QComplex := ((-1015013938622948293274443 : Int)/10^30,(-431476258582718924332980947 : Int)/10^30)
theorem v2325_mb_checked : Scalar.distance (sourceCoefficient 27 85 3 1) v2325_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2325_mg : Scalar.QComplex := ((-93086164938842504773499 : Int)/10^30,(218977876595651236981 : Int)/10^30)
theorem v2325_mg_checked : Scalar.distance (sourceCoefficient 27 85 3 2) v2325_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2325_upper : Scalar.QComplex := ((999994830695828458581576570542 : Int)/10^30,(-3215366483214194812564196057 : Int)/10^30)
theorem v2325_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 85 5) 1) 14) v2325_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2325 : Material (27 : Basis) (85 : Basis) where
  plus := ![v2325_pa,v2325_pb,v2325_pg]
  minus := ![(Primitive.Addresses.material2325 1).one,v2325_mb,v2325_mg]
  upper := v2325_upper
  lower := (Primitive.Addresses.material2325 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2325_pa_checked.trans (by decide +kernel)
    · exact v2325_pb_checked.trans (by decide +kernel)
    · exact v2325_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 85 Primitive.Addresses.material2325
    · exact v2325_mb_checked.trans (by decide +kernel)
    · exact v2325_mg_checked.trans (by decide +kernel)
  upper_error := v2325_upper_checked
  lower_error := reuse_lower_error 27 85 Primitive.Addresses.material2325

def v2326_pa : Scalar.QComplex := ((999998868922230759919741521344 : Int)/10^30,(-1504045963108588130570739010 : Int)/10^30)
theorem v2326_pa_checked : Scalar.distance (sourceCoefficient 27 86 1 0) v2326_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2326_pb : Scalar.QComplex := ((-648961917428407769261814 : Int)/10^30,(-431476962353414864254978954 : Int)/10^30)
theorem v2326_pb_checked : Scalar.distance (sourceCoefficient 27 86 1 1) v2326_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2326_pg : Scalar.QComplex := ((-93086316992046133603746 : Int)/10^30,(140006257650498942479 : Int)/10^30)
theorem v2326_pg_checked : Scalar.distance (sourceCoefficient 27 86 1 2) v2326_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2326_mb : Scalar.QComplex := ((-1021306861300226422014223 : Int)/10^30,(-431476241669915727782204334 : Int)/10^30)
theorem v2326_mb_checked : Scalar.distance (sourceCoefficient 27 86 3 1) v2326_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2326_mg : Scalar.QComplex := ((-93086161512661358001323 : Int)/10^30,(220335504631820245613 : Int)/10^30)
theorem v2326_mg_checked : Scalar.distance (sourceCoefficient 27 86 3 2) v2326_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2326_upper : Scalar.QComplex := ((999994783694497277578482349816 : Int)/10^30,(-3229951051579844809194520104 : Int)/10^30)
theorem v2326_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 86 5) 1) 14) v2326_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2326 : Material (27 : Basis) (86 : Basis) where
  plus := ![v2326_pa,v2326_pb,v2326_pg]
  minus := ![(Primitive.Addresses.material2326 1).one,v2326_mb,v2326_mg]
  upper := v2326_upper
  lower := (Primitive.Addresses.material2326 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2326_pa_checked.trans (by decide +kernel)
    · exact v2326_pb_checked.trans (by decide +kernel)
    · exact v2326_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 86 Primitive.Addresses.material2326
    · exact v2326_mb_checked.trans (by decide +kernel)
    · exact v2326_mg_checked.trans (by decide +kernel)
  upper_error := v2326_upper_checked
  lower_error := reuse_lower_error 27 86 Primitive.Addresses.material2326

def v2327_pa : Scalar.QComplex := ((999998867469222342142955776092 : Int)/10^30,(-1505011718455956656521358653 : Int)/10^30)
theorem v2327_pa_checked : Scalar.distance (sourceCoefficient 27 87 1 0) v2327_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2327_pb : Scalar.QComplex := ((-649378618876139205566065 : Int)/10^30,(-431476961588768295965490735 : Int)/10^30)
theorem v2327_pb_checked : Scalar.distance (sourceCoefficient 27 87 1 1) v2327_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2327_pg : Scalar.QComplex := ((-93086316841936494874031 : Int)/10^30,(140096156338227389002 : Int)/10^30)
theorem v2327_pg_checked : Scalar.distance (sourceCoefficient 27 87 1 2) v2327_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2327_mb : Scalar.QComplex := ((-1021723561932945315100290 : Int)/10^30,(-431476240545674862349872152 : Int)/10^30)
theorem v2327_mb_checked : Scalar.distance (sourceCoefficient 27 87 3 1) v2327_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2327_mg : Scalar.QComplex := ((-93086161284973256541231 : Int)/10^30,(220425403156537444585 : Int)/10^30)
theorem v2327_mg_checked : Scalar.distance (sourceCoefficient 27 87 3 2) v2327_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2327_upper : Scalar.QComplex := ((999994780574684906969697615499 : Int)/10^30,(-3230916802981073477643179715 : Int)/10^30)
theorem v2327_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 87 5) 1) 14) v2327_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2327 : Material (27 : Basis) (87 : Basis) where
  plus := ![v2327_pa,v2327_pb,v2327_pg]
  minus := ![(Primitive.Addresses.material2327 1).one,v2327_mb,v2327_mg]
  upper := v2327_upper
  lower := (Primitive.Addresses.material2327 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2327_pa_checked.trans (by decide +kernel)
    · exact v2327_pb_checked.trans (by decide +kernel)
    · exact v2327_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 87 Primitive.Addresses.material2327
    · exact v2327_mb_checked.trans (by decide +kernel)
    · exact v2327_mg_checked.trans (by decide +kernel)
  upper_error := v2327_upper_checked
  lower_error := reuse_lower_error 27 87 Primitive.Addresses.material2327

def v2328_pa : Scalar.QComplex := ((999998849701752295343998274691 : Int)/10^30,(-1516771298588964377509470234 : Int)/10^30)
theorem v2328_pa_checked : Scalar.distance (sourceCoefficient 27 88 1 0) v2328_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2328_pb : Scalar.QComplex := ((-654452609968313397287208 : Int)/10^30,(-431476952234956116907532180 : Int)/10^30)
theorem v2328_pb_checked : Scalar.distance (sourceCoefficient 27 88 1 1) v2328_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2328_pg : Scalar.QComplex := ((-93086315005991343355560 : Int)/10^30,(141190813304044026847 : Int)/10^30)
theorem v2328_pg_checked : Scalar.distance (sourceCoefficient 27 88 1 2) v2328_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2328_mb : Scalar.QComplex := ((-1026797543063922099891205 : Int)/10^30,(-431476226813240377672929824 : Int)/10^30)
theorem v2328_mb_checked : Scalar.distance (sourceCoefficient 27 88 3 1) v2328_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2328_mg : Scalar.QComplex := ((-93086158504389128648871 : Int)/10^30,(221520058130425287902 : Int)/10^30)
theorem v2328_mg_checked : Scalar.distance (sourceCoefficient 27 88 3 2) v2328_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2328_upper : Scalar.QComplex := ((999994742511272833935054641259 : Int)/10^30,(-3242676334934526519351723941 : Int)/10^30)
theorem v2328_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 88 5) 1) 14) v2328_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2328 : Material (27 : Basis) (88 : Basis) where
  plus := ![v2328_pa,v2328_pb,v2328_pg]
  minus := ![(Primitive.Addresses.material2328 1).one,v2328_mb,v2328_mg]
  upper := v2328_upper
  lower := (Primitive.Addresses.material2328 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2328_pa_checked.trans (by decide +kernel)
    · exact v2328_pb_checked.trans (by decide +kernel)
    · exact v2328_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 88 Primitive.Addresses.material2328
    · exact v2328_mb_checked.trans (by decide +kernel)
    · exact v2328_mg_checked.trans (by decide +kernel)
  upper_error := v2328_upper_checked
  lower_error := reuse_lower_error 27 88 Primitive.Addresses.material2328

def v2329_pa : Scalar.QComplex := ((999998825168248348871428115752 : Int)/10^30,(-1532860764411631894291220188 : Int)/10^30)
theorem v2329_pa_checked : Scalar.distance (sourceCoefficient 27 89 1 0) v2329_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2329_pb : Scalar.QComplex := ((-661394848041586011917229 : Int)/10^30,(-431476939308173514132905323 : Int)/10^30)
theorem v2329_pb_checked : Scalar.distance (sourceCoefficient 27 89 1 1) v2329_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2329_pg : Scalar.QComplex := ((-93086312469719096579787 : Int)/10^30,(142688523723601903096 : Int)/10^30)
theorem v2329_pg_checked : Scalar.distance (sourceCoefficient 27 89 1 2) v2329_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2329_mb : Scalar.QComplex := ((-1033739767397051018369754 : Int)/10^30,(-431476207895623797692065853 : Int)/10^30)
theorem v2329_mb_checked : Scalar.distance (sourceCoefficient 27 89 3 1) v2329_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2329_mg : Scalar.QComplex := ((-93086154675661188537994 : Int)/10^30,(223017765803628406696 : Int)/10^30)
theorem v2329_mg_checked : Scalar.distance (sourceCoefficient 27 89 3 2) v2329_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2329_upper : Scalar.QComplex := ((999994690208847042248039078456 : Int)/10^30,(-3258765734451222545171546518 : Int)/10^30)
theorem v2329_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 89 5) 1) 14) v2329_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2329 : Material (27 : Basis) (89 : Basis) where
  plus := ![v2329_pa,v2329_pb,v2329_pg]
  minus := ![(Primitive.Addresses.material2329 1).one,v2329_mb,v2329_mg]
  upper := v2329_upper
  lower := (Primitive.Addresses.material2329 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2329_pa_checked.trans (by decide +kernel)
    · exact v2329_pb_checked.trans (by decide +kernel)
    · exact v2329_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 89 Primitive.Addresses.material2329
    · exact v2329_mb_checked.trans (by decide +kernel)
    · exact v2329_mg_checked.trans (by decide +kernel)
  upper_error := v2329_upper_checked
  lower_error := reuse_lower_error 27 89 Primitive.Addresses.material2329

def v2330_pa : Scalar.QComplex := ((999998784659490464721064124440 : Int)/10^30,(-1559063674779835204367524163 : Int)/10^30)
theorem v2330_pa_checked : Scalar.distance (sourceCoefficient 27 90 1 0) v2330_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2330_pb : Scalar.QComplex := ((-672700806822327551903620 : Int)/10^30,(-431476917937160104202013538 : Int)/10^30)
theorem v2330_pb_checked : Scalar.distance (sourceCoefficient 27 90 1 1) v2330_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2330_pg : Scalar.QComplex := ((-93086308279033180915453 : Int)/10^30,(145127658236720177524 : Int)/10^30)
theorem v2330_pg_checked : Scalar.distance (sourceCoefficient 27 90 1 2) v2330_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2330_mb : Scalar.QComplex := ((-1045045703525845338387303 : Int)/10^30,(-431476176768085118867258246 : Int)/10^30)
theorem v2330_mb_checked : Scalar.distance (sourceCoefficient 27 90 3 1) v2330_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2330_mg : Scalar.QComplex := ((-93086148380113602976958 : Int)/10^30,(225456895792172224204 : Int)/10^30)
theorem v2330_mg_checked : Scalar.distance (sourceCoefficient 27 90 3 2) v2330_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2330_upper : Scalar.QComplex := ((999994604476303305074780710650 : Int)/10^30,(-3284968535878827689644060706 : Int)/10^30)
theorem v2330_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 90 5) 1) 14) v2330_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2330 : Material (27 : Basis) (90 : Basis) where
  plus := ![v2330_pa,v2330_pb,v2330_pg]
  minus := ![(Primitive.Addresses.material2330 1).one,v2330_mb,v2330_mg]
  upper := v2330_upper
  lower := (Primitive.Addresses.material2330 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2330_pa_checked.trans (by decide +kernel)
    · exact v2330_pb_checked.trans (by decide +kernel)
    · exact v2330_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 90 Primitive.Addresses.material2330
    · exact v2330_mb_checked.trans (by decide +kernel)
    · exact v2330_mg_checked.trans (by decide +kernel)
  upper_error := v2330_upper_checked
  lower_error := reuse_lower_error 27 90 Primitive.Addresses.material2330

def v2331_pa : Scalar.QComplex := ((999998761537096411568885696746 : Int)/10^30,(-1573824727657593599521091367 : Int)/10^30)
theorem v2331_pa_checked : Scalar.distance (sourceCoefficient 27 91 1 0) v2331_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2331_pb : Scalar.QComplex := ((-679069864644696513785224 : Int)/10^30,(-431476905724155492294605700 : Int)/10^30)
theorem v2331_pb_checked : Scalar.distance (sourceCoefficient 27 91 1 1) v2331_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2331_pg : Scalar.QComplex := ((-93086305885433317904745 : Int)/10^30,(146501711445728481533 : Int)/10^30)
theorem v2331_pg_checked : Scalar.distance (sourceCoefficient 27 91 1 2) v2331_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2331_mb : Scalar.QComplex := ((-1051414748437450065911488 : Int)/10^30,(-431476159058875005431098471 : Int)/10^30)
theorem v2331_mb_checked : Scalar.distance (sourceCoefficient 27 91 3 1) v2331_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2331_mg : Scalar.QComplex := ((-93086144800768596897958 : Int)/10^30,(226830946423988843123 : Int)/10^30)
theorem v2331_mg_checked : Scalar.distance (sourceCoefficient 27 91 3 2) v2331_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2331_upper : Scalar.QComplex := ((999994555877705535257906566787 : Int)/10^30,(-3299729526864577289913141760 : Int)/10^30)
theorem v2331_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 91 5) 1) 14) v2331_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2331 : Material (27 : Basis) (91 : Basis) where
  plus := ![v2331_pa,v2331_pb,v2331_pg]
  minus := ![(Primitive.Addresses.material2331 1).one,v2331_mb,v2331_mg]
  upper := v2331_upper
  lower := (Primitive.Addresses.material2331 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2331_pa_checked.trans (by decide +kernel)
    · exact v2331_pb_checked.trans (by decide +kernel)
    · exact v2331_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 91 Primitive.Addresses.material2331
    · exact v2331_mb_checked.trans (by decide +kernel)
    · exact v2331_mg_checked.trans (by decide +kernel)
  upper_error := v2331_upper_checked
  lower_error := reuse_lower_error 27 91 Primitive.Addresses.material2331

def v2332_pa : Scalar.QComplex := ((999998710733193060524060636294 : Int)/10^30,(-1605780791910917211546628043 : Int)/10^30)
theorem v2332_pa_checked : Scalar.distance (sourceCoefficient 27 92 1 0) v2332_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2332_pb : Scalar.QComplex := ((-692858177497925652018277 : Int)/10^30,(-431476878854902040006818614 : Int)/10^30)
theorem v2332_pb_checked : Scalar.distance (sourceCoefficient 27 92 1 1) v2332_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2332_pg : Scalar.QComplex := ((-93086300622486455770611 : Int)/10^30,(149476386244577213128 : Int)/10^30)
theorem v2332_pg_checked : Scalar.distance (sourceCoefficient 27 92 1 2) v2332_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2332_mb : Scalar.QComplex := ((-1065203032969704588787942 : Int)/10^30,(-431476120290938568015821802 : Int)/10^30)
theorem v2332_mb_checked : Scalar.distance (sourceCoefficient 27 92 3 1) v2332_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2332_mg : Scalar.QComplex := ((-93086136970813317372592 : Int)/10^30,(229805615573544090059 : Int)/10^30)
theorem v2332_mg_checked : Scalar.distance (sourceCoefficient 27 92 3 2) v2332_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2332_upper : Scalar.QComplex := ((999994449920609980925793017287 : Int)/10^30,(-3331685455840168729817970972 : Int)/10^30)
theorem v2332_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 92 5) 1) 14) v2332_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2332 : Material (27 : Basis) (92 : Basis) where
  plus := ![v2332_pa,v2332_pb,v2332_pg]
  minus := ![(Primitive.Addresses.material2332 1).one,v2332_mb,v2332_mg]
  upper := v2332_upper
  lower := (Primitive.Addresses.material2332 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2332_pa_checked.trans (by decide +kernel)
    · exact v2332_pb_checked.trans (by decide +kernel)
    · exact v2332_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 92 Primitive.Addresses.material2332
    · exact v2332_mb_checked.trans (by decide +kernel)
    · exact v2332_mg_checked.trans (by decide +kernel)
  upper_error := v2332_upper_checked
  lower_error := reuse_lower_error 27 92 Primitive.Addresses.material2332

def v2333_pa : Scalar.QComplex := ((999998649113799201687102059054 : Int)/10^30,(-1643706353550748519032710008 : Int)/10^30)
theorem v2333_pa_checked : Scalar.distance (sourceCoefficient 27 93 1 0) v2333_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2333_pb : Scalar.QComplex := ((-709222191594057016828848 : Int)/10^30,(-431476846204018935513739444 : Int)/10^30)
theorem v2333_pb_checked : Scalar.distance (sourceCoefficient 27 93 1 1) v2333_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2333_pg : Scalar.QComplex := ((-93086294232491052514237 : Int)/10^30,(153006739953133572548 : Int)/10^30)
theorem v2333_pg_checked : Scalar.distance (sourceCoefficient 27 93 1 2) v2333_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2333_mb : Scalar.QComplex := ((-1081567012796524055227412 : Int)/10^30,(-431476073518660463813246545 : Int)/10^30)
theorem v2333_mb_checked : Scalar.distance (sourceCoefficient 27 93 3 1) v2333_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2333_mg : Scalar.QComplex := ((-93086127534284044148035 : Int)/10^30,(233335962453310180347 : Int)/10^30)
theorem v2333_mg_checked : Scalar.distance (sourceCoefficient 27 93 3 2) v2333_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2333_upper : Scalar.QComplex := ((999994322845229086664456865156 : Int)/10^30,(-3369610854644847291586758394 : Int)/10^30)
theorem v2333_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 93 5) 1) 14) v2333_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2333 : Material (27 : Basis) (93 : Basis) where
  plus := ![v2333_pa,v2333_pb,v2333_pg]
  minus := ![(Primitive.Addresses.material2333 1).one,v2333_mb,v2333_mg]
  upper := v2333_upper
  lower := (Primitive.Addresses.material2333 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2333_pa_checked.trans (by decide +kernel)
    · exact v2333_pb_checked.trans (by decide +kernel)
    · exact v2333_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 93 Primitive.Addresses.material2333
    · exact v2333_mb_checked.trans (by decide +kernel)
    · exact v2333_mg_checked.trans (by decide +kernel)
  upper_error := v2333_upper_checked
  lower_error := reuse_lower_error 27 93 Primitive.Addresses.material2333

def v2334_pa : Scalar.QComplex := ((999998574474671617696000583257 : Int)/10^30,(-1688504848865452959187720646 : Int)/10^30)
theorem v2334_pa_checked : Scalar.distance (sourceCoefficient 27 94 1 0) v2334_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2334_pb : Scalar.QComplex := ((-728551718635477665521496 : Int)/10^30,(-431476806570073191239845829 : Int)/10^30)
theorem v2334_pb_checked : Scalar.distance (sourceCoefficient 27 94 1 1) v2334_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2334_pg : Scalar.QComplex := ((-93086286483256702452652 : Int)/10^30,(157176870149467048938 : Int)/10^30)
theorem v2334_pg_checked : Scalar.distance (sourceCoefficient 27 94 1 2) v2334_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2334_mb : Scalar.QComplex := ((-1100896498438368252716270 : Int)/10^30,(-431476017204218209903578172 : Int)/10^30)
theorem v2334_mb_checked : Scalar.distance (sourceCoefficient 27 94 3 1) v2334_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2334_mg : Scalar.QComplex := ((-93086116186418035736763 : Int)/10^30,(237506084409673368733 : Int)/10^30)
theorem v2334_mg_checked : Scalar.distance (sourceCoefficient 27 94 3 2) v2334_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2334_upper : Scalar.QComplex := ((999994170888073843454338929802 : Int)/10^30,(-3414409154417092360204671873 : Int)/10^30)
theorem v2334_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 94 5) 1) 14) v2334_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2334 : Material (27 : Basis) (94 : Basis) where
  plus := ![v2334_pa,v2334_pb,v2334_pg]
  minus := ![(Primitive.Addresses.material2334 1).one,v2334_mb,v2334_mg]
  upper := v2334_upper
  lower := (Primitive.Addresses.material2334 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2334_pa_checked.trans (by decide +kernel)
    · exact v2334_pb_checked.trans (by decide +kernel)
    · exact v2334_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 94 Primitive.Addresses.material2334
    · exact v2334_mb_checked.trans (by decide +kernel)
    · exact v2334_mg_checked.trans (by decide +kernel)
  upper_error := v2334_upper_checked
  lower_error := reuse_lower_error 27 94 Primitive.Addresses.material2334

def v2335_pa : Scalar.QComplex := ((999998498737328245193346415105 : Int)/10^30,(-1732779007756039184060199973 : Int)/10^30)
theorem v2335_pa_checked : Scalar.distance (sourceCoefficient 27 95 1 0) v2335_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2335_pb : Scalar.QComplex := ((-747655005346085159978352 : Int)/10^30,(-431476766265625089577217108 : Int)/10^30)
theorem v2335_pb_checked : Scalar.distance (sourceCoefficient 27 95 1 1) v2335_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2335_pg : Scalar.QComplex := ((-93086278610581178159662 : Int)/10^30,(161298191637499194643 : Int)/10^30)
theorem v2335_pg_checked : Scalar.distance (sourceCoefficient 27 95 1 2) v2335_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2335_mb : Scalar.QComplex := ((-1119999743255025574703668 : Int)/10^30,(-431475960414509064269349611 : Int)/10^30)
theorem v2335_mb_checked : Scalar.distance (sourceCoefficient 27 95 3 1) v2335_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2335_mg : Scalar.QComplex := ((-93086104757230616058306 : Int)/10^30,(241627397569384765426 : Int)/10^30)
theorem v2335_mg_checked : Scalar.distance (sourceCoefficient 27 95 3 2) v2335_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2335_upper : Scalar.QComplex := ((999994018737661547995299736976 : Int)/10^30,(-3458683116650735902768226714 : Int)/10^30)
theorem v2335_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 95 5) 1) 14) v2335_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2335 : Material (27 : Basis) (95 : Basis) where
  plus := ![v2335_pa,v2335_pb,v2335_pg]
  minus := ![(Primitive.Addresses.material2335 1).one,v2335_mb,v2335_mg]
  upper := v2335_upper
  lower := (Primitive.Addresses.material2335 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2335_pa_checked.trans (by decide +kernel)
    · exact v2335_pb_checked.trans (by decide +kernel)
    · exact v2335_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 95 Primitive.Addresses.material2335
    · exact v2335_mb_checked.trans (by decide +kernel)
    · exact v2335_mg_checked.trans (by decide +kernel)
  upper_error := v2335_upper_checked
  lower_error := reuse_lower_error 27 95 Primitive.Addresses.material2335

def v2336_pa : Scalar.QComplex := ((999998461665267392093739433695 : Int)/10^30,(-1754043072088614069474316942 : Int)/10^30)
theorem v2336_pa_checked : Scalar.distance (sourceCoefficient 27 96 1 0) v2336_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2336_pb : Scalar.QComplex := ((-756829962236220363935099 : Int)/10^30,(-431476746507264712844922509 : Int)/10^30)
theorem v2336_pb_checked : Scalar.distance (sourceCoefficient 27 96 1 1) v2336_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2336_pg : Scalar.QComplex := ((-93086274753806076793453 : Int)/10^30,(163277586514033199179 : Int)/10^30)
theorem v2336_pg_checked : Scalar.distance (sourceCoefficient 27 96 1 2) v2336_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2336_mb : Scalar.QComplex := ((-1129174679678329890615925 : Int)/10^30,(-431475932738581473009653019 : Int)/10^30)
theorem v2336_mb_checked : Scalar.distance (sourceCoefficient 27 96 3 1) v2336_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2336_mg : Scalar.QComplex := ((-93086099192328320932771 : Int)/10^30,(243606788380676384836 : Int)/10^30)
theorem v2336_mg_checked : Scalar.distance (sourceCoefficient 27 96 3 2) v2336_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2336_upper : Scalar.QComplex := ((999993944965809932198545864662 : Int)/10^30,(-3479947085329970935912298373 : Int)/10^30)
theorem v2336_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 96 5) 1) 14) v2336_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2336 : Material (27 : Basis) (96 : Basis) where
  plus := ![v2336_pa,v2336_pb,v2336_pg]
  minus := ![(Primitive.Addresses.material2336 1).one,v2336_mb,v2336_mg]
  upper := v2336_upper
  lower := (Primitive.Addresses.material2336 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2336_pa_checked.trans (by decide +kernel)
    · exact v2336_pb_checked.trans (by decide +kernel)
    · exact v2336_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 96 Primitive.Addresses.material2336
    · exact v2336_mb_checked.trans (by decide +kernel)
    · exact v2336_mg_checked.trans (by decide +kernel)
  upper_error := v2336_upper_checked
  lower_error := reuse_lower_error 27 96 Primitive.Addresses.material2336

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
