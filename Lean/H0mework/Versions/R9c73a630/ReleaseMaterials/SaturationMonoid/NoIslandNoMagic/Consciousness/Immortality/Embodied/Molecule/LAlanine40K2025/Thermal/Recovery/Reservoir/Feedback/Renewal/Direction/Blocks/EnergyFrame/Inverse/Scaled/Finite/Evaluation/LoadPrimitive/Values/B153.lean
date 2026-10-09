import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B102

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2449_pa : Scalar.QComplex := ((999999200782354956553997941687 : Int)/10^30,(-1264292154265796215347837201 : Int)/10^30)
theorem v2449_pa_checked : Scalar.distance (sourceCoefficient 29 72 1 0) v2449_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2449_pb : Scalar.QComplex := ((-545513598705711737815387 : Int)/10^30,(-431477139900793096487316055 : Int)/10^30)
theorem v2449_pb_checked : Scalar.distance (sourceCoefficient 29 72 1 1) v2449_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2449_pg : Scalar.QComplex := ((-93086351589809830557664 : Int)/10^30,(117688438042900296568 : Int)/10^30)
theorem v2449_pg_checked : Scalar.distance (sourceCoefficient 29 72 1 2) v2449_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2449_mb : Scalar.QComplex := ((-917858734311458250094911 : Int)/10^30,(-431476508488467769378095835 : Int)/10^30)
theorem v2449_mb_checked : Scalar.distance (sourceCoefficient 29 72 3 1) v2449_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2449_mg : Scalar.QComplex := ((-93086215369685336702319 : Int)/10^30,(198017723190477659393 : Int)/10^30)
theorem v2449_mg_checked : Scalar.distance (sourceCoefficient 29 72 3 2) v2449_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2449_upper : Scalar.QComplex := ((999995529347450974565389509397 : Int)/10^30,(-2990198172582655952647961173 : Int)/10^30)
theorem v2449_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 72 5) 1) 14) v2449_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2449 : Material (29 : Basis) (72 : Basis) where
  plus := ![v2449_pa,v2449_pb,v2449_pg]
  minus := ![(Primitive.Addresses.material2449 1).one,v2449_mb,v2449_mg]
  upper := v2449_upper
  lower := (Primitive.Addresses.material2449 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2449_pa_checked.trans (by decide +kernel)
    · exact v2449_pb_checked.trans (by decide +kernel)
    · exact v2449_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 72 Primitive.Addresses.material2449
    · exact v2449_mb_checked.trans (by decide +kernel)
    · exact v2449_mg_checked.trans (by decide +kernel)
  upper_error := v2449_upper_checked
  lower_error := reuse_lower_error 29 72 Primitive.Addresses.material2449

def v2450_pa : Scalar.QComplex := ((999999188790598081483370440973 : Int)/10^30,(-1273741789287114305016402646 : Int)/10^30)
theorem v2450_pa_checked : Scalar.distance (sourceCoefficient 29 73 1 0) v2450_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2450_pb : Scalar.QComplex := ((-549590902219107210813896 : Int)/10^30,(-431477133755181258644716734 : Int)/10^30)
theorem v2450_pb_checked : Scalar.distance (sourceCoefficient 29 73 1 1) v2450_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2450_pg : Scalar.QComplex := ((-93086350368751540841360 : Int)/10^30,(118568070660434507204 : Int)/10^30)
theorem v2450_pg_checked : Scalar.distance (sourceCoefficient 29 73 1 2) v2450_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2450_mb : Scalar.QComplex := ((-921936031003301055104400 : Int)/10^30,(-431476498824328922700753057 : Int)/10^30)
theorem v2450_mb_checked : Scalar.distance (sourceCoefficient 29 73 3 1) v2450_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2450_mg : Scalar.QComplex := ((-93086213389544169892232 : Int)/10^30,(198897354426766135723 : Int)/10^30)
theorem v2450_mg_checked : Scalar.distance (sourceCoefficient 29 73 3 2) v2450_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2450_upper : Scalar.QComplex := ((999995501046499177205507546000 : Int)/10^30,(-2999647772833168227482060914 : Int)/10^30)
theorem v2450_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 73 5) 1) 14) v2450_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2450 : Material (29 : Basis) (73 : Basis) where
  plus := ![v2450_pa,v2450_pb,v2450_pg]
  minus := ![(Primitive.Addresses.material2450 1).one,v2450_mb,v2450_mg]
  upper := v2450_upper
  lower := (Primitive.Addresses.material2450 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2450_pa_checked.trans (by decide +kernel)
    · exact v2450_pb_checked.trans (by decide +kernel)
    · exact v2450_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 73 Primitive.Addresses.material2450
    · exact v2450_mb_checked.trans (by decide +kernel)
    · exact v2450_mg_checked.trans (by decide +kernel)
  upper_error := v2450_upper_checked
  lower_error := reuse_lower_error 29 73 Primitive.Addresses.material2450

def v2451_pa : Scalar.QComplex := ((999999175190152043607936382629 : Int)/10^30,(-1284374951329049721664913936 : Int)/10^30)
theorem v2451_pa_checked : Scalar.distance (sourceCoefficient 29 74 1 0) v2451_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2451_pb : Scalar.QComplex := ((-554178870797835836591486 : Int)/10^30,(-431477126778431109960387185 : Int)/10^30)
theorem v2451_pb_checked : Scalar.distance (sourceCoefficient 29 74 1 1) v2451_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2451_pg : Scalar.QComplex := ((-93086348983165306798089 : Int)/10^30,(119557873557163388641 : Int)/10^30)
theorem v2451_pg_checked : Scalar.distance (sourceCoefficient 29 74 1 2) v2451_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2451_mb : Scalar.QComplex := ((-926523991853098141346529 : Int)/10^30,(-431476487888371122770708232 : Int)/10^30)
theorem v2451_mb_checked : Scalar.distance (sourceCoefficient 29 74 3 1) v2451_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2451_mg : Scalar.QComplex := ((-93086211149803130956631 : Int)/10^30,(199887155759247646989 : Int)/10^30)
theorem v2451_mg_checked : Scalar.distance (sourceCoefficient 29 74 3 2) v2451_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2451_upper : Scalar.QComplex := ((999995469094200344141442644291 : Int)/10^30,(-3010280895565121803076282751 : Int)/10^30)
theorem v2451_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 74 5) 1) 14) v2451_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2451 : Material (29 : Basis) (74 : Basis) where
  plus := ![v2451_pa,v2451_pb,v2451_pg]
  minus := ![(Primitive.Addresses.material2451 1).one,v2451_mb,v2451_mg]
  upper := v2451_upper
  lower := (Primitive.Addresses.material2451 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2451_pa_checked.trans (by decide +kernel)
    · exact v2451_pb_checked.trans (by decide +kernel)
    · exact v2451_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 74 Primitive.Addresses.material2451
    · exact v2451_mb_checked.trans (by decide +kernel)
    · exact v2451_mg_checked.trans (by decide +kernel)
  upper_error := v2451_upper_checked
  lower_error := reuse_lower_error 29 74 Primitive.Addresses.material2451

def v2452_pa : Scalar.QComplex := ((999999156052227599161264792940 : Int)/10^30,(-1299190067909170451751009873 : Int)/10^30)
theorem v2452_pa_checked : Scalar.distance (sourceCoefficient 29 75 1 0) v2452_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2452_pb : Scalar.QComplex := ((-560571257963503792377704 : Int)/10^30,(-431477116949319407631917404 : Int)/10^30)
theorem v2452_pb_checked : Scalar.distance (sourceCoefficient 29 75 1 1) v2452_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2452_pg : Scalar.QComplex := ((-93086347032164537128568 : Int)/10^30,(120936959586612096382 : Int)/10^30)
theorem v2452_pg_checked : Scalar.distance (sourceCoefficient 29 75 1 2) v2452_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2452_mb : Scalar.QComplex := ((-932916368156507496477064 : Int)/10^30,(-431476472542920858728793077 : Int)/10^30)
theorem v2452_mb_checked : Scalar.distance (sourceCoefficient 29 75 3 1) v2452_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2452_mg : Scalar.QComplex := ((-93086208008713956048698 : Int)/10^30,(201266239591573804209 : Int)/10^30)
theorem v2452_mg_checked : Scalar.distance (sourceCoefficient 29 75 3 2) v2452_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2452_upper : Scalar.QComplex := ((999995424386757202974017273051 : Int)/10^30,(-3025095957049545280744229423 : Int)/10^30)
theorem v2452_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 75 5) 1) 14) v2452_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2452 : Material (29 : Basis) (75 : Basis) where
  plus := ![v2452_pa,v2452_pb,v2452_pg]
  minus := ![(Primitive.Addresses.material2452 1).one,v2452_mb,v2452_mg]
  upper := v2452_upper
  lower := (Primitive.Addresses.material2452 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2452_pa_checked.trans (by decide +kernel)
    · exact v2452_pb_checked.trans (by decide +kernel)
    · exact v2452_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 75 Primitive.Addresses.material2452
    · exact v2452_mb_checked.trans (by decide +kernel)
    · exact v2452_mg_checked.trans (by decide +kernel)
  upper_error := v2452_upper_checked
  lower_error := reuse_lower_error 29 75 Primitive.Addresses.material2452

def v2453_pa : Scalar.QComplex := ((999999139825800062566590057125 : Int)/10^30,(-1311620242286315350186592393 : Int)/10^30)
theorem v2453_pa_checked : Scalar.distance (sourceCoefficient 29 76 1 0) v2453_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2453_pb : Scalar.QComplex := ((-565934596531937722955764 : Int)/10^30,(-431477108605083890382879452 : Int)/10^30)
theorem v2453_pb_checked : Scalar.distance (sourceCoefficient 29 76 1 1) v2453_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2453_pg : Scalar.QComplex := ((-93086345376846875270556 : Int)/10^30,(122094039898870616454 : Int)/10^30)
theorem v2453_pg_checked : Scalar.distance (sourceCoefficient 29 76 1 2) v2453_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2453_mb : Scalar.QComplex := ((-938279697527225920376623 : Int)/10^30,(-431476459570368819663655903 : Int)/10^30)
theorem v2453_mb_checked : Scalar.distance (sourceCoefficient 29 76 3 1) v2453_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2453_mg : Scalar.QComplex := ((-93086205354888714024740 : Int)/10^30,(202423318044533853401 : Int)/10^30)
theorem v2453_mg_checked : Scalar.distance (sourceCoefficient 29 76 3 2) v2453_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2453_upper : Scalar.QComplex := ((999995386707000515395698074549 : Int)/10^30,(-3037526084908063717119515887 : Int)/10^30)
theorem v2453_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 76 5) 1) 14) v2453_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2453 : Material (29 : Basis) (76 : Basis) where
  plus := ![v2453_pa,v2453_pb,v2453_pg]
  minus := ![(Primitive.Addresses.material2453 1).one,v2453_mb,v2453_mg]
  upper := v2453_upper
  lower := (Primitive.Addresses.material2453 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2453_pa_checked.trans (by decide +kernel)
    · exact v2453_pb_checked.trans (by decide +kernel)
    · exact v2453_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 76 Primitive.Addresses.material2453
    · exact v2453_mb_checked.trans (by decide +kernel)
    · exact v2453_mg_checked.trans (by decide +kernel)
  upper_error := v2453_upper_checked
  lower_error := reuse_lower_error 29 76 Primitive.Addresses.material2453

def v2454_pa : Scalar.QComplex := ((999999136047218549917645968027 : Int)/10^30,(-1314497933237536943952637815 : Int)/10^30)
theorem v2454_pa_checked : Scalar.distance (sourceCoefficient 29 77 1 0) v2454_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2454_pb : Scalar.QComplex := ((-567176254958241117304383 : Int)/10^30,(-431477106660651036861850531 : Int)/10^30)
theorem v2454_pb_checked : Scalar.distance (sourceCoefficient 29 77 1 1) v2454_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2454_pg : Scalar.QComplex := ((-93086344991234766782529 : Int)/10^30,(122361913818530237041 : Int)/10^30)
theorem v2454_pg_checked : Scalar.distance (sourceCoefficient 29 77 1 2) v2454_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2454_mb : Scalar.QComplex := ((-939521353813245157435242 : Int)/10^30,(-431476456554441390463604330 : Int)/10^30)
theorem v2454_mb_checked : Scalar.distance (sourceCoefficient 29 77 3 1) v2454_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2454_mg : Scalar.QComplex := ((-93086204738113621044955 : Int)/10^30,(202691191531685888955 : Int)/10^30)
theorem v2454_mg_checked : Scalar.distance (sourceCoefficient 29 77 3 2) v2454_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2454_upper : Scalar.QComplex := ((999995377961791110775372609885 : Int)/10^30,(-3040403765051813775770974460 : Int)/10^30)
theorem v2454_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 77 5) 1) 14) v2454_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2454 : Material (29 : Basis) (77 : Basis) where
  plus := ![v2454_pa,v2454_pb,v2454_pg]
  minus := ![(Primitive.Addresses.material2454 1).one,v2454_mb,v2454_mg]
  upper := v2454_upper
  lower := (Primitive.Addresses.material2454 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2454_pa_checked.trans (by decide +kernel)
    · exact v2454_pb_checked.trans (by decide +kernel)
    · exact v2454_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 77 Primitive.Addresses.material2454
    · exact v2454_mb_checked.trans (by decide +kernel)
    · exact v2454_mg_checked.trans (by decide +kernel)
  upper_error := v2454_upper_checked
  lower_error := reuse_lower_error 29 77 Primitive.Addresses.material2454

def v2455_pa : Scalar.QComplex := ((999999113157306467393586533237 : Int)/10^30,(-1331797507346837526271464973 : Int)/10^30)
theorem v2455_pa_checked : Scalar.distance (sourceCoefficient 29 78 1 0) v2455_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2455_pb : Scalar.QComplex := ((-574640629042374959968454 : Int)/10^30,(-431477094871059282234767138 : Int)/10^30)
theorem v2455_pb_checked : Scalar.distance (sourceCoefficient 29 78 1 1) v2455_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2455_pg : Scalar.QComplex := ((-93086342654128651262556 : Int)/10^30,(123972269058703153194 : Int)/10^30)
theorem v2455_pg_checked : Scalar.distance (sourceCoefficient 29 78 1 2) v2455_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2455_mb : Scalar.QComplex := ((-946985714944164689086464 : Int)/10^30,(-431476438323435373961888375 : Int)/10^30)
theorem v2455_mb_checked : Scalar.distance (sourceCoefficient 29 78 3 1) v2455_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2455_mg : Scalar.QComplex := ((-93086201011344331174836 : Int)/10^30,(204301544155432633980 : Int)/10^30)
theorem v2455_mg_checked : Scalar.distance (sourceCoefficient 29 78 3 2) v2455_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2455_upper : Scalar.QComplex := ((999995325214417612537392920249 : Int)/10^30,(-3057703273889519175178695347 : Int)/10^30)
theorem v2455_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 78 5) 1) 14) v2455_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2455 : Material (29 : Basis) (78 : Basis) where
  plus := ![v2455_pa,v2455_pb,v2455_pg]
  minus := ![(Primitive.Addresses.material2455 1).one,v2455_mb,v2455_mg]
  upper := v2455_upper
  lower := (Primitive.Addresses.material2455 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2455_pa_checked.trans (by decide +kernel)
    · exact v2455_pb_checked.trans (by decide +kernel)
    · exact v2455_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 78 Primitive.Addresses.material2455
    · exact v2455_mb_checked.trans (by decide +kernel)
    · exact v2455_mg_checked.trans (by decide +kernel)
  upper_error := v2455_upper_checked
  lower_error := reuse_lower_error 29 78 Primitive.Addresses.material2455

def v2456_pa : Scalar.QComplex := ((999999105714211897417550365145 : Int)/10^30,(-1337374583450012368677639766 : Int)/10^30)
theorem v2456_pa_checked : Scalar.distance (sourceCoefficient 29 79 1 0) v2456_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2456_pb : Scalar.QComplex := ((-577047010934229874716571 : Int)/10^30,(-431477091033603785330146532 : Int)/10^30)
theorem v2456_pb_checked : Scalar.distance (sourceCoefficient 29 79 1 1) v2456_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2456_pg : Scalar.QComplex := ((-93086341893759134613310 : Int)/10^30,(124491419045958351687 : Int)/10^30)
theorem v2456_pg_checked : Scalar.distance (sourceCoefficient 29 79 1 2) v2456_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2456_mb : Scalar.QComplex := ((-949392092628462387162607 : Int)/10^30,(-431476432409382112663714285 : Int)/10^30)
theorem v2456_mb_checked : Scalar.distance (sourceCoefficient 29 79 3 1) v2456_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2456_mg : Scalar.QComplex := ((-93086199802972040292133 : Int)/10^30,(204820693293219918795 : Int)/10^30)
theorem v2456_mg_checked : Scalar.distance (sourceCoefficient 29 79 3 2) v2456_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2456_upper : Scalar.QComplex := ((999995308145806722488441510043 : Int)/10^30,(-3063280328840188295771474989 : Int)/10^30)
theorem v2456_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 79 5) 1) 14) v2456_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2456 : Material (29 : Basis) (79 : Basis) where
  plus := ![v2456_pa,v2456_pb,v2456_pg]
  minus := ![(Primitive.Addresses.material2456 1).one,v2456_mb,v2456_mg]
  upper := v2456_upper
  lower := (Primitive.Addresses.material2456 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2456_pa_checked.trans (by decide +kernel)
    · exact v2456_pb_checked.trans (by decide +kernel)
    · exact v2456_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 79 Primitive.Addresses.material2456
    · exact v2456_mb_checked.trans (by decide +kernel)
    · exact v2456_mg_checked.trans (by decide +kernel)
  upper_error := v2456_upper_checked
  lower_error := reuse_lower_error 29 79 Primitive.Addresses.material2456

def v2457_pa : Scalar.QComplex := ((999999094025119863899053635414 : Int)/10^30,(-1346086527486891704053743925 : Int)/10^30)
theorem v2457_pa_checked : Scalar.distance (sourceCoefficient 29 80 1 0) v2457_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2457_pb : Scalar.QComplex := ((-580806017237934650715190 : Int)/10^30,(-431477085003310628985859278 : Int)/10^30)
theorem v2457_pb_checked : Scalar.distance (sourceCoefficient 29 80 1 1) v2457_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2457_pg : Scalar.QComplex := ((-93086340699227194557915 : Int)/10^30,(125302382629095536116 : Int)/10^30)
theorem v2457_pg_checked : Scalar.distance (sourceCoefficient 29 80 1 2) v2457_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2457_mb : Scalar.QComplex := ((-953151092328645921613596 : Int)/10^30,(-431476423135238060935176697 : Int)/10^30)
theorem v2457_mb_checked : Scalar.distance (sourceCoefficient 29 80 3 1) v2457_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2457_mg : Scalar.QComplex := ((-93086197908615497212116 : Int)/10^30,(205631655543571033809 : Int)/10^30)
theorem v2457_mg_checked : Scalar.distance (sourceCoefficient 29 80 3 2) v2457_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2457_upper : Scalar.QComplex := ((999995281420707032234916211277 : Int)/10^30,(-3071992239727337941343443690 : Int)/10^30)
theorem v2457_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 80 5) 1) 14) v2457_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2457 : Material (29 : Basis) (80 : Basis) where
  plus := ![v2457_pa,v2457_pb,v2457_pg]
  minus := ![(Primitive.Addresses.material2457 1).one,v2457_mb,v2457_mg]
  upper := v2457_upper
  lower := (Primitive.Addresses.material2457 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2457_pa_checked.trans (by decide +kernel)
    · exact v2457_pb_checked.trans (by decide +kernel)
    · exact v2457_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 80 Primitive.Addresses.material2457
    · exact v2457_mb_checked.trans (by decide +kernel)
    · exact v2457_mg_checked.trans (by decide +kernel)
  upper_error := v2457_upper_checked
  lower_error := reuse_lower_error 29 80 Primitive.Addresses.material2457

def v2458_pa : Scalar.QComplex := ((999999058370328130557362616636 : Int)/10^30,(-1372318642689243047292751575 : Int)/10^30)
theorem v2458_pa_checked : Scalar.distance (sourceCoefficient 29 81 1 0) v2458_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2458_pb : Scalar.QComplex := ((-592124579925567077982692 : Int)/10^30,(-431477066582106962758445497 : Int)/10^30)
theorem v2458_pb_checked : Scalar.distance (sourceCoefficient 29 81 1 1) v2458_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2458_pg : Scalar.QComplex := ((-93086337052654639518277 : Int)/10^30,(127744236004775440400 : Int)/10^30)
theorem v2458_pg_checked : Scalar.distance (sourceCoefficient 29 81 1 2) v2458_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2458_mb : Scalar.QComplex := ((-964469634905191072666812 : Int)/10^30,(-431476394946631423476924701 : Int)/10^30)
theorem v2458_mb_checked : Scalar.distance (sourceCoefficient 29 81 3 1) v2458_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2458_mg : Scalar.QComplex := ((-93086192154834813739842 : Int)/10^30,(208073504863209448647 : Int)/10^30)
theorem v2458_mg_checked : Scalar.distance (sourceCoefficient 29 81 3 2) v2458_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2458_upper : Scalar.QComplex := ((999995200491717322160288470737 : Int)/10^30,(-3098224254323099177082355436 : Int)/10^30)
theorem v2458_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 81 5) 1) 14) v2458_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2458 : Material (29 : Basis) (81 : Basis) where
  plus := ![v2458_pa,v2458_pb,v2458_pg]
  minus := ![(Primitive.Addresses.material2458 1).one,v2458_mb,v2458_mg]
  upper := v2458_upper
  lower := (Primitive.Addresses.material2458 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2458_pa_checked.trans (by decide +kernel)
    · exact v2458_pb_checked.trans (by decide +kernel)
    · exact v2458_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 81 Primitive.Addresses.material2458
    · exact v2458_mb_checked.trans (by decide +kernel)
    · exact v2458_mg_checked.trans (by decide +kernel)
  upper_error := v2458_upper_checked
  lower_error := reuse_lower_error 29 81 Primitive.Addresses.material2458

def v2459_pa : Scalar.QComplex := ((999999044679721196455059890670 : Int)/10^30,(-1382258892165376806600595624 : Int)/10^30)
theorem v2459_pa_checked : Scalar.distance (sourceCoefficient 29 82 1 0) v2459_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2459_pb : Scalar.QComplex := ((-596413572022807054951188 : Int)/10^30,(-431477059498251250666424590 : Int)/10^30)
theorem v2459_pb_checked : Scalar.distance (sourceCoefficient 29 82 1 1) v2459_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2459_pg : Scalar.QComplex := ((-93086335651318615514479 : Int)/10^30,(128669538113745113095 : Int)/10^30)
theorem v2459_pg_checked : Scalar.distance (sourceCoefficient 29 82 1 2) v2459_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2459_mb : Scalar.QComplex := ((-968758619292394840692955 : Int)/10^30,(-431476384161571338143321589 : Int)/10^30)
theorem v2459_mb_checked : Scalar.distance (sourceCoefficient 29 82 3 1) v2459_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2459_mg : Scalar.QComplex := ((-93086189955005265536637 : Int)/10^30,(208998805418356982893 : Int)/10^30)
theorem v2459_mg_checked : Scalar.distance (sourceCoefficient 29 82 3 2) v2459_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2459_upper : Scalar.QComplex := ((999995169645161955190149399148 : Int)/10^30,(-3108164465365653439314833628 : Int)/10^30)
theorem v2459_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 82 5) 1) 14) v2459_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2459 : Material (29 : Basis) (82 : Basis) where
  plus := ![v2459_pa,v2459_pb,v2459_pg]
  minus := ![(Primitive.Addresses.material2459 1).one,v2459_mb,v2459_mg]
  upper := v2459_upper
  lower := (Primitive.Addresses.material2459 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2459_pa_checked.trans (by decide +kernel)
    · exact v2459_pb_checked.trans (by decide +kernel)
    · exact v2459_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 82 Primitive.Addresses.material2459
    · exact v2459_mb_checked.trans (by decide +kernel)
    · exact v2459_mg_checked.trans (by decide +kernel)
  upper_error := v2459_upper_checked
  lower_error := reuse_lower_error 29 82 Primitive.Addresses.material2459

def v2460_pa : Scalar.QComplex := ((999999025832320768378448274210 : Int)/10^30,(-1395827499894086426838868875 : Int)/10^30)
theorem v2460_pa_checked : Scalar.distance (sourceCoefficient 29 83 1 0) v2460_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2460_pb : Scalar.QComplex := ((-602268118306086784564017 : Int)/10^30,(-431477049736913032020379607 : Int)/10^30)
theorem v2460_pb_checked : Scalar.distance (sourceCoefficient 29 83 1 1) v2460_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2460_pg : Scalar.QComplex := ((-93086333721150450658496 : Int)/10^30,(129932591048430702651 : Int)/10^30)
theorem v2460_pg_checked : Scalar.distance (sourceCoefficient 29 83 1 2) v2460_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2460_mb : Scalar.QComplex := ((-974613154972164174719403 : Int)/10^30,(-431476369348026990595579164 : Int)/10^30)
theorem v2460_mb_checked : Scalar.distance (sourceCoefficient 29 83 3 1) v2460_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2460_mg : Scalar.QComplex := ((-93086186934880022529289 : Int)/10^30,(210261856217102045771 : Int)/10^30)
theorem v2460_mg_checked : Scalar.distance (sourceCoefficient 29 83 3 2) v2460_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2460_upper : Scalar.QComplex := ((999995127379603592827315776830 : Int)/10^30,(-3121733020356612412218149831 : Int)/10^30)
theorem v2460_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 83 5) 1) 14) v2460_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2460 : Material (29 : Basis) (83 : Basis) where
  plus := ![v2460_pa,v2460_pb,v2460_pg]
  minus := ![(Primitive.Addresses.material2460 1).one,v2460_mb,v2460_mg]
  upper := v2460_upper
  lower := (Primitive.Addresses.material2460 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2460_pa_checked.trans (by decide +kernel)
    · exact v2460_pb_checked.trans (by decide +kernel)
    · exact v2460_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 83 Primitive.Addresses.material2460
    · exact v2460_mb_checked.trans (by decide +kernel)
    · exact v2460_mg_checked.trans (by decide +kernel)
  upper_error := v2460_upper_checked
  lower_error := reuse_lower_error 29 83 Primitive.Addresses.material2460

def v2461_pa : Scalar.QComplex := ((999998976166882368727166255120 : Int)/10^30,(-1430966521980263837688026495 : Int)/10^30)
theorem v2461_pa_checked : Scalar.distance (sourceCoefficient 29 84 1 0) v2461_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2461_pb : Scalar.QComplex := ((-617429808443192902082712 : Int)/10^30,(-431477023965360739437207125 : Int)/10^30)
theorem v2461_pb_checked : Scalar.distance (sourceCoefficient 29 84 1 1) v2461_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2461_pg : Scalar.QComplex := ((-93086328629599765269754 : Int)/10^30,(133203556301222562923 : Int)/10^30)
theorem v2461_pg_checked : Scalar.distance (sourceCoefficient 29 84 1 2) v2461_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2461_mb : Scalar.QComplex := ((-989774817224191209851598 : Int)/10^30,(-431476330492628562791489311 : Int)/10^30)
theorem v2461_mb_checked : Scalar.distance (sourceCoefficient 29 84 3 1) v2461_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2461_mg : Scalar.QComplex := ((-93086179020635538604441 : Int)/10^30,(213532815858185125372 : Int)/10^30)
theorem v2461_mg_checked : Scalar.distance (sourceCoefficient 29 84 3 2) v2461_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2461_upper : Scalar.QComplex := ((999995017067474830452237804133 : Int)/10^30,(-3156871904389303080774359360 : Int)/10^30)
theorem v2461_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 84 5) 1) 14) v2461_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2461 : Material (29 : Basis) (84 : Basis) where
  plus := ![v2461_pa,v2461_pb,v2461_pg]
  minus := ![(Primitive.Addresses.material2461 1).one,v2461_mb,v2461_mg]
  upper := v2461_upper
  lower := (Primitive.Addresses.material2461 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2461_pa_checked.trans (by decide +kernel)
    · exact v2461_pb_checked.trans (by decide +kernel)
    · exact v2461_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 84 Primitive.Addresses.material2461
    · exact v2461_mb_checked.trans (by decide +kernel)
    · exact v2461_mg_checked.trans (by decide +kernel)
  upper_error := v2461_upper_checked
  lower_error := reuse_lower_error 29 84 Primitive.Addresses.material2461

def v2462_pa : Scalar.QComplex := ((999998859914236396210351459571 : Int)/10^30,(-1510023253930889279218990438 : Int)/10^30)
theorem v2462_pa_checked : Scalar.distance (sourceCoefficient 29 85 1 0) v2462_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2462_pb : Scalar.QComplex := ((-651540991062328895278714 : Int)/10^30,(-431476963386909712288218534 : Int)/10^30)
theorem v2462_pb_checked : Scalar.distance (sourceCoefficient 29 85 1 1) v2462_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2462_pg : Scalar.QComplex := ((-93086316684267581442539 : Int)/10^30,(140562663069510021280 : Int)/10^30)
theorem v2462_pg_checked : Scalar.distance (sourceCoefficient 29 85 1 2) v2462_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2462_mb : Scalar.QComplex := ((-1023885934865700071606978 : Int)/10^30,(-431476240477785802088662365 : Int)/10^30)
theorem v2462_mb_checked : Scalar.distance (sourceCoefficient 29 85 3 1) v2462_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2462_mg : Scalar.QComplex := ((-93086160724730103403394 : Int)/10^30,(220891909578057129249 : Int)/10^30)
theorem v2462_mg_checked : Scalar.distance (sourceCoefficient 29 85 3 2) v2462_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2462_upper : Scalar.QComplex := ((999994764370254626514292085162 : Int)/10^30,(-3235928317952692347030637902 : Int)/10^30)
theorem v2462_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 85 5) 1) 14) v2462_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2462 : Material (29 : Basis) (85 : Basis) where
  plus := ![v2462_pa,v2462_pb,v2462_pg]
  minus := ![(Primitive.Addresses.material2462 1).one,v2462_mb,v2462_mg]
  upper := v2462_upper
  lower := (Primitive.Addresses.material2462 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2462_pa_checked.trans (by decide +kernel)
    · exact v2462_pb_checked.trans (by decide +kernel)
    · exact v2462_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 85 Primitive.Addresses.material2462
    · exact v2462_mb_checked.trans (by decide +kernel)
    · exact v2462_mg_checked.trans (by decide +kernel)
  upper_error := v2462_upper_checked
  lower_error := reuse_lower_error 29 85 Primitive.Addresses.material2462

def v2463_pa : Scalar.QComplex := ((999998837784728854262426749473 : Int)/10^30,(-1524607881242629108212604807 : Int)/10^30)
theorem v2463_pa_checked : Scalar.distance (sourceCoefficient 29 86 1 0) v2463_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2463_pb : Scalar.QComplex := ((-657833925861449737681338 : Int)/10^30,(-431476951818358307251542712 : Int)/10^30)
theorem v2463_pb_checked : Scalar.distance (sourceCoefficient 29 86 1 1) v2463_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2463_pg : Scalar.QComplex := ((-93086314406396621970051 : Int)/10^30,(141920293521753992587 : Int)/10^30)
theorem v2463_pg_checked : Scalar.distance (sourceCoefficient 29 86 1 2) v2463_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2463_mb : Scalar.QComplex := ((-1030178857338534852635954 : Int)/10^30,(-431476223478719396173282922 : Int)/10^30)
theorem v2463_mb_checked : Scalar.distance (sourceCoefficient 29 86 3 1) v2463_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2463_mg : Scalar.QComplex := ((-93086157275286057205565 : Int)/10^30,(222249537559093189883 : Int)/10^30)
theorem v2463_mg_checked : Scalar.distance (sourceCoefficient 29 86 3 2) v2463_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2463_upper : Scalar.QComplex := ((999994717069036410859567629856 : Int)/10^30,(-3250512885348820581699490616 : Int)/10^30)
theorem v2463_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 86 5) 1) 14) v2463_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2463 : Material (29 : Basis) (86 : Basis) where
  plus := ![v2463_pa,v2463_pb,v2463_pg]
  minus := ![(Primitive.Addresses.material2463 1).one,v2463_mb,v2463_mg]
  upper := v2463_upper
  lower := (Primitive.Addresses.material2463 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2463_pa_checked.trans (by decide +kernel)
    · exact v2463_pb_checked.trans (by decide +kernel)
    · exact v2463_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 86 Primitive.Addresses.material2463
    · exact v2463_mb_checked.trans (by decide +kernel)
    · exact v2463_mg_checked.trans (by decide +kernel)
  upper_error := v2463_upper_checked
  lower_error := reuse_lower_error 29 86 Primitive.Addresses.material2463

def v2464_pa : Scalar.QComplex := ((999998836311862631634914037684 : Int)/10^30,(-1525573636559916802257913337 : Int)/10^30)
theorem v2464_pa_checked : Scalar.distance (sourceCoefficient 29 87 1 0) v2464_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2464_pb : Scalar.QComplex := ((-658250627300528373018766 : Int)/10^30,(-431476951047999608607699924 : Int)/10^30)
theorem v2464_pb_checked : Scalar.distance (sourceCoefficient 29 87 1 1) v2464_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2464_pg : Scalar.QComplex := ((-93086314254746573197642 : Int)/10^30,(142010192207149008204 : Int)/10^30)
theorem v2464_pg_checked : Scalar.distance (sourceCoefficient 29 87 1 2) v2464_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2464_mb : Scalar.QComplex := ((-1030595557957671636746025 : Int)/10^30,(-431476222348766409980460886 : Int)/10^30)
theorem v2464_mb_checked : Scalar.distance (sourceCoefficient 29 87 3 1) v2464_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2464_mg : Scalar.QComplex := ((-93086157046057548289990 : Int)/10^30,(222339436080147654329 : Int)/10^30)
theorem v2464_mg_checked : Scalar.distance (sourceCoefficient 29 87 3 2) v2464_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2464_upper : Scalar.QComplex := ((999994713929366316892710549355 : Int)/10^30,(-3251478636685695693358333571 : Int)/10^30)
theorem v2464_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 87 5) 1) 14) v2464_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2464 : Material (29 : Basis) (87 : Basis) where
  plus := ![v2464_pa,v2464_pb,v2464_pg]
  minus := ![(Primitive.Addresses.material2464 1).one,v2464_mb,v2464_mg]
  upper := v2464_upper
  lower := (Primitive.Addresses.material2464 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2464_pa_checked.trans (by decide +kernel)
    · exact v2464_pb_checked.trans (by decide +kernel)
    · exact v2464_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 87 Primitive.Addresses.material2464
    · exact v2464_mb_checked.trans (by decide +kernel)
    · exact v2464_mg_checked.trans (by decide +kernel)
  upper_error := v2464_upper_checked
  lower_error := reuse_lower_error 29 87 Primitive.Addresses.material2464

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
