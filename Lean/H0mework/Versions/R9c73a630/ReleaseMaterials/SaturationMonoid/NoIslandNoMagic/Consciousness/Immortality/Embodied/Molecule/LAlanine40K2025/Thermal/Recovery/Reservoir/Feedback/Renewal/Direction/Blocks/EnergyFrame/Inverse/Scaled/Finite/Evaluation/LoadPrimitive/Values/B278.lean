import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B185
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B186

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4449_pa : Scalar.QComplex := ((999997073959399147763342746242 : Int)/10^30,(-2419105752130500697261862538 : Int)/10^30)
theorem v4449_pa_checked : Scalar.distance (sourceCoefficient 72 94 1 0) v4449_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4449_pb : Scalar.QComplex := ((-1043789718553088656846195 : Int)/10^30,(-431476244253783853452893985 : Int)/10^30)
theorem v4449_pb_checked : Scalar.distance (sourceCoefficient 72 94 1 1) v4449_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4449_pg : Scalar.QComplex := ((-93086155987739540019397 : Int)/10^30,(225185914296785743428 : Int)/10^30)
theorem v4449_pg_checked : Scalar.distance (sourceCoefficient 72 94 1 2) v4449_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4449_mb : Scalar.QComplex := ((-1416133895724832873417843 : Int)/10^30,(-431475182851942111741443938 : Int)/10^30)
theorem v4449_mb_checked : Scalar.distance (sourceCoefficient 72 94 3 1) v4449_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4449_mg : Scalar.QComplex := ((-93085927002207377256438 : Int)/10^30,(305514990622362749050 : Int)/10^30)
theorem v4449_mg_checked : Scalar.distance (sourceCoefficient 72 94 3 2) v4449_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4449_upper : Scalar.QComplex := ((999991409424156775481136253706 : Int)/10^30,(-4145006379784682494842495657 : Int)/10^30)
theorem v4449_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 94 5) 1) 14) v4449_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4449 : Material (72 : Basis) (94 : Basis) where
  plus := ![v4449_pa,v4449_pb,v4449_pg]
  minus := ![(Primitive.Addresses.material4449 1).one,v4449_mb,v4449_mg]
  upper := v4449_upper
  lower := (Primitive.Addresses.material4449 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4449_pa_checked.trans (by decide +kernel)
    · exact v4449_pb_checked.trans (by decide +kernel)
    · exact v4449_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 94 Primitive.Addresses.material4449
    · exact v4449_mb_checked.trans (by decide +kernel)
    · exact v4449_mg_checked.trans (by decide +kernel)
  upper_error := v4449_upper_checked
  lower_error := reuse_lower_error 72 94 Primitive.Addresses.material4449

def v4450_pa : Scalar.QComplex := ((999996965875269448914722539612 : Int)/10^30,(-2463379843870873685123865293 : Int)/10^30)
theorem v4450_pa_checked : Scalar.distance (sourceCoefficient 72 95 1 0) v4450_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4450_pb : Scalar.QComplex := ((-1062892985947825931770198 : Int)/10^30,(-431476194644729044537730844 : Int)/10^30)
theorem v4450_pb_checked : Scalar.distance (sourceCoefficient 72 95 1 1) v4450_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4450_pg : Scalar.QComplex := ((-93086145605858413474526 : Int)/10^30,(229307230575840097459 : Int)/10^30)
theorem v4450_pg_checked : Scalar.distance (sourceCoefficient 72 95 1 2) v4450_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4450_mb : Scalar.QComplex := ((-1435237113196170643624422 : Int)/10^30,(-431475116757646392111044558 : Int)/10^30)
theorem v4450_mb_checked : Scalar.distance (sourceCoefficient 72 95 3 1) v4450_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4450_mg : Scalar.QComplex := ((-93085913063819784731253 : Int)/10^30,(309636296407766869291 : Int)/10^30)
theorem v4450_mg_checked : Scalar.distance (sourceCoefficient 72 95 3 2) v4450_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4450_upper : Scalar.QComplex := ((999991224927122225590870998927 : Int)/10^30,(-4189280219040594091009680512 : Int)/10^30)
theorem v4450_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 95 5) 1) 14) v4450_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4450 : Material (72 : Basis) (95 : Basis) where
  plus := ![v4450_pa,v4450_pb,v4450_pg]
  minus := ![(Primitive.Addresses.material4450 1).one,v4450_mb,v4450_mg]
  upper := v4450_upper
  lower := (Primitive.Addresses.material4450 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4450_pa_checked.trans (by decide +kernel)
    · exact v4450_pb_checked.trans (by decide +kernel)
    · exact v4450_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 95 Primitive.Addresses.material4450
    · exact v4450_mb_checked.trans (by decide +kernel)
    · exact v4450_mg_checked.trans (by decide +kernel)
  upper_error := v4450_upper_checked
  lower_error := reuse_lower_error 72 95 Primitive.Addresses.material4450

def v4451_pa : Scalar.QComplex := ((999996913267642152609012755800 : Int)/10^30,(-2484643875443346708424770631 : Int)/10^30)
theorem v4451_pa_checked : Scalar.distance (sourceCoefficient 72 96 1 0) v4451_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4451_pb : Scalar.QComplex := ((-1072067933414463547399436 : Int)/10^30,(-431476170417537252285004987 : Int)/10^30)
theorem v4451_pb_checked : Scalar.distance (sourceCoefficient 72 96 1 1) v4451_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4451_pg : Scalar.QComplex := ((-93086140543958022987637 : Int)/10^30,(231286622911106781045 : Int)/10^30)
theorem v4451_pg_checked : Scalar.distance (sourceCoefficient 72 96 1 2) v4451_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4451_mb : Scalar.QComplex := ((-1444412036339580637109375 : Int)/10^30,(-431475084612897181335088541 : Int)/10^30)
theorem v4451_mb_checked : Scalar.distance (sourceCoefficient 72 96 3 1) v4451_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4451_mg : Scalar.QComplex := ((-93085906293794842207503 : Int)/10^30,(311615683637823266298 : Int)/10^30)
theorem v4451_mg_checked : Scalar.distance (sourceCoefficient 72 96 3 2) v4451_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4451_upper : Scalar.QComplex := ((999991135619783845953136432787 : Int)/10^30,(-4210544128146797748968548650 : Int)/10^30)
theorem v4451_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 96 5) 1) 14) v4451_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4451 : Material (72 : Basis) (96 : Basis) where
  plus := ![v4451_pa,v4451_pb,v4451_pg]
  minus := ![(Primitive.Addresses.material4451 1).one,v4451_mb,v4451_mg]
  upper := v4451_upper
  lower := (Primitive.Addresses.material4451 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4451_pa_checked.trans (by decide +kernel)
    · exact v4451_pb_checked.trans (by decide +kernel)
    · exact v4451_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 96 Primitive.Addresses.material4451
    · exact v4451_mb_checked.trans (by decide +kernel)
    · exact v4451_mg_checked.trans (by decide +kernel)
  upper_error := v4451_upper_checked
  lower_error := reuse_lower_error 72 96 Primitive.Addresses.material4451

def v4452_pa : Scalar.QComplex := ((999996728809225075233752590945 : Int)/10^30,(-2557805866198693067248974839 : Int)/10^30)
theorem v4452_pa_checked : Scalar.distance (sourceCoefficient 72 97 1 0) v4452_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4452_pb : Scalar.QComplex := ((-1103635671727343640148909 : Int)/10^30,(-431476085073136704182134207 : Int)/10^30)
theorem v4452_pb_checked : Scalar.distance (sourceCoefficient 72 97 1 1) v4452_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4452_pg : Scalar.QComplex := ((-93086122752622244034787 : Int)/10^30,(238097009699090474760 : Int)/10^30)
theorem v4452_pg_checked : Scalar.distance (sourceCoefficient 72 97 1 2) v4452_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4452_mb : Scalar.QComplex := ((-1475979689249975135161522 : Int)/10^30,(-431474972026992004992922098 : Int)/10^30)
theorem v4452_mb_checked : Scalar.distance (sourceCoefficient 72 97 3 1) v4452_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4452_mg : Scalar.QComplex := ((-93085882625408618186777 : Int)/10^30,(318426052536867223576 : Int)/10^30)
theorem v4452_mg_checked : Scalar.distance (sourceCoefficient 72 97 3 2) v4452_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4452_upper : Scalar.QComplex := ((999990824890682657948622933302 : Int)/10^30,(-4283705691577459150178099167 : Int)/10^30)
theorem v4452_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 97 5) 1) 14) v4452_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4452 : Material (72 : Basis) (97 : Basis) where
  plus := ![v4452_pa,v4452_pb,v4452_pg]
  minus := ![(Primitive.Addresses.material4452 1).one,v4452_mb,v4452_mg]
  upper := v4452_upper
  lower := (Primitive.Addresses.material4452 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4452_pa_checked.trans (by decide +kernel)
    · exact v4452_pb_checked.trans (by decide +kernel)
    · exact v4452_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 97 Primitive.Addresses.material4452
    · exact v4452_mb_checked.trans (by decide +kernel)
    · exact v4452_mg_checked.trans (by decide +kernel)
  upper_error := v4452_upper_checked
  lower_error := reuse_lower_error 72 97 Primitive.Addresses.material4452

def v4453_pa : Scalar.QComplex := ((999997992262269383498334282415 : Int)/10^30,(-2003864124690645882798879749 : Int)/10^30)
theorem v4453_pa_checked : Scalar.distance (sourceCoefficient 73 74 1 0) v4453_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4453_pb : Scalar.QComplex := ((-864622324927369658936705 : Int)/10^30,(-431476654698823079385821184 : Int)/10^30)
theorem v4453_pb_checked : Scalar.distance (sourceCoefficient 73 74 1 1) v4453_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4453_pg : Scalar.QComplex := ((-93086243002961476728487 : Int)/10^30,(186532557364323568185 : Int)/10^30)
theorem v4453_pg_checked : Scalar.distance (sourceCoefficient 73 74 1 2) v4453_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4453_mb : Scalar.QComplex := ((-1236966923006905970402131 : Int)/10^30,(-431475747910219809364798401 : Int)/10^30)
theorem v4453_mb_checked : Scalar.distance (sourceCoefficient 73 74 3 1) v4453_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4453_mg : Scalar.QComplex := ((-93086047373503064364827 : Int)/10^30,(266861723172529416708 : Int)/10^30)
theorem v4453_mg_checked : Scalar.distance (sourceCoefficient 73 74 3 2) v4453_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4453_upper : Scalar.QComplex := ((999993044395037841975630975679 : Int)/10^30,(-3729766955705900285292587624 : Int)/10^30)
theorem v4453_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 74 5) 1) 14) v4453_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4453 : Material (73 : Basis) (74 : Basis) where
  plus := ![v4453_pa,v4453_pb,v4453_pg]
  minus := ![(Primitive.Addresses.material4453 1).one,v4453_mb,v4453_mg]
  upper := v4453_upper
  lower := (Primitive.Addresses.material4453 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4453_pa_checked.trans (by decide +kernel)
    · exact v4453_pb_checked.trans (by decide +kernel)
    · exact v4453_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 74 Primitive.Addresses.material4453
    · exact v4453_mb_checked.trans (by decide +kernel)
    · exact v4453_mg_checked.trans (by decide +kernel)
  upper_error := v4453_upper_checked
  lower_error := reuse_lower_error 73 74 Primitive.Addresses.material4453

def v4454_pa : Scalar.QComplex := ((999997962465020194054277323394 : Int)/10^30,(-2018679223666577867456765892 : Int)/10^30)
theorem v4454_pa_checked : Scalar.distance (sourceCoefficient 73 75 1 0) v4454_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4454_pb : Scalar.QComplex := ((-871014707029163250881947 : Int)/10^30,(-431476641803538775404170829 : Int)/10^30)
theorem v4454_pb_checked : Scalar.distance (sourceCoefficient 73 75 1 1) v4454_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4454_pg : Scalar.QComplex := ((-93086240225095312107011 : Int)/10^30,(187911642028179722433 : Int)/10^30)
theorem v4454_pg_checked : Scalar.distance (sourceCoefficient 73 75 1 2) v4454_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4454_mb : Scalar.QComplex := ((-1243359291600473987264492 : Int)/10^30,(-431475729498602455241400838 : Int)/10^30)
theorem v4454_mb_checked : Scalar.distance (sourceCoefficient 73 75 3 1) v4454_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4454_mg : Scalar.QComplex := ((-93086043405549980829585 : Int)/10^30,(268240804925715933699 : Int)/10^30)
theorem v4454_mg_checked : Scalar.distance (sourceCoefficient 73 75 3 2) v4454_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4454_upper : Scalar.QComplex := ((999992989028316214855630748165 : Int)/10^30,(-3744581981189133733425067204 : Int)/10^30)
theorem v4454_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 75 5) 1) 14) v4454_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4454 : Material (73 : Basis) (75 : Basis) where
  plus := ![v4454_pa,v4454_pb,v4454_pg]
  minus := ![(Primitive.Addresses.material4454 1).one,v4454_mb,v4454_mg]
  upper := v4454_upper
  lower := (Primitive.Addresses.material4454 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4454_pa_checked.trans (by decide +kernel)
    · exact v4454_pb_checked.trans (by decide +kernel)
    · exact v4454_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 75 Primitive.Addresses.material4454
    · exact v4454_mb_checked.trans (by decide +kernel)
    · exact v4454_mg_checked.trans (by decide +kernel)
  upper_error := v4454_upper_checked
  lower_error := reuse_lower_error 73 75 Primitive.Addresses.material4454

def v4455_pa : Scalar.QComplex := ((999997937295209461178017011395 : Int)/10^30,(-2031109383151629048219690950 : Int)/10^30)
theorem v4455_pa_checked : Scalar.distance (sourceCoefficient 73 76 1 0) v4455_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4455_pb : Scalar.QComplex := ((-876378041313861496930506 : Int)/10^30,(-431476630886724117372833689 : Int)/10^30)
theorem v4455_pb_checked : Scalar.distance (sourceCoefficient 73 76 1 1) v4455_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4455_pg : Scalar.QComplex := ((-93086237876021314734053 : Int)/10^30,(189068721185228390535 : Int)/10^30)
theorem v4455_pg_checked : Scalar.distance (sourceCoefficient 73 76 1 2) v4455_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4455_mb : Scalar.QComplex := ((-1248722614467438387833400 : Int)/10^30,(-431475713953475929953714719 : Int)/10^30)
theorem v4455_mb_checked : Scalar.distance (sourceCoefficient 73 76 3 1) v4455_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4455_mg : Scalar.QComplex := ((-93086040057969658501944 : Int)/10^30,(269397881624786089135 : Int)/10^30)
theorem v4455_mg_checked : Scalar.distance (sourceCoefficient 73 76 3 2) v4455_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4455_upper : Scalar.QComplex := ((999992942405215353517189760973 : Int)/10^30,(-3757012078720112572755670580 : Int)/10^30)
theorem v4455_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 76 5) 1) 14) v4455_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4455 : Material (73 : Basis) (76 : Basis) where
  plus := ![v4455_pa,v4455_pb,v4455_pg]
  minus := ![(Primitive.Addresses.material4455 1).one,v4455_mb,v4455_mg]
  upper := v4455_upper
  lower := (Primitive.Addresses.material4455 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4455_pa_checked.trans (by decide +kernel)
    · exact v4455_pb_checked.trans (by decide +kernel)
    · exact v4455_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 76 Primitive.Addresses.material4455
    · exact v4455_mb_checked.trans (by decide +kernel)
    · exact v4455_mg_checked.trans (by decide +kernel)
  upper_error := v4455_upper_checked
  lower_error := reuse_lower_error 73 76 Primitive.Addresses.material4455

def v4456_pa : Scalar.QComplex := ((999997931446158778466312866473 : Int)/10^30,(-2033987070639357171895954281 : Int)/10^30)
theorem v4456_pa_checked : Scalar.distance (sourceCoefficient 73 77 1 0) v4456_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4456_pb : Scalar.QComplex := ((-877619698743885197924141 : Int)/10^30,(-431476628346717343063667110 : Int)/10^30)
theorem v4456_pb_checked : Scalar.distance (sourceCoefficient 73 77 1 1) v4456_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4456_pg : Scalar.QComplex := ((-93086237329798722251978 : Int)/10^30,(189336594836217812468 : Int)/10^30)
theorem v4456_pg_checked : Scalar.distance (sourceCoefficient 73 77 1 2) v4456_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4456_mb : Scalar.QComplex := ((-1249964269243224832510986 : Int)/10^30,(-431475710341975661469419864 : Int)/10^30)
theorem v4456_mb_checked : Scalar.distance (sourceCoefficient 73 77 3 1) v4456_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4456_mg : Scalar.QComplex := ((-93086039280584373181015 : Int)/10^30,(269665754704668412014 : Int)/10^30)
theorem v4456_mg_checked : Scalar.distance (sourceCoefficient 73 77 3 2) v4456_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4456_upper : Scalar.QComplex := ((999992931589545840230242357169 : Int)/10^30,(-3759889751826932363751545350 : Int)/10^30)
theorem v4456_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 77 5) 1) 14) v4456_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4456 : Material (73 : Basis) (77 : Basis) where
  plus := ![v4456_pa,v4456_pb,v4456_pg]
  minus := ![(Primitive.Addresses.material4456 1).one,v4456_mb,v4456_mg]
  upper := v4456_upper
  lower := (Primitive.Addresses.material4456 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4456_pa_checked.trans (by decide +kernel)
    · exact v4456_pb_checked.trans (by decide +kernel)
    · exact v4456_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 77 Primitive.Addresses.material4456
    · exact v4456_mb_checked.trans (by decide +kernel)
    · exact v4456_mg_checked.trans (by decide +kernel)
  upper_error := v4456_upper_checked
  lower_error := reuse_lower_error 73 77 Primitive.Addresses.material4456

def v4457_pa : Scalar.QComplex := ((999997896109380327849126210097 : Int)/10^30,(-2051286623801891368222942645 : Int)/10^30)
theorem v4457_pa_checked : Scalar.distance (sourceCoefficient 73 78 1 0) v4457_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4457_pb : Scalar.QComplex := ((-885084066802646636752231 : Int)/10^30,(-431476612976763656225764167 : Int)/10^30)
theorem v4457_pb_checked : Scalar.distance (sourceCoefficient 73 78 1 1) v4457_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4457_pg : Scalar.QComplex := ((-93086234027163991521005 : Int)/10^30,(190946948451507664150 : Int)/10^30)
theorem v4457_pg_checked : Scalar.distance (sourceCoefficient 73 78 1 2) v4457_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4457_mb : Scalar.QComplex := ((-1257428621259083109865223 : Int)/10^30,(-431475688530614245514274156 : Int)/10^30)
theorem v4457_mb_checked : Scalar.distance (sourceCoefficient 73 78 3 1) v4457_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4457_mg : Scalar.QComplex := ((-93086034588288229811228 : Int)/10^30,(271276104870324988453 : Int)/10^30)
theorem v4457_mg_checked : Scalar.distance (sourceCoefficient 73 78 3 2) v4457_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4457_upper : Scalar.QComplex := ((999992866395360664262985508840 : Int)/10^30,(-3777189218235740394482956194 : Int)/10^30)
theorem v4457_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 78 5) 1) 14) v4457_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4457 : Material (73 : Basis) (78 : Basis) where
  plus := ![v4457_pa,v4457_pb,v4457_pg]
  minus := ![(Primitive.Addresses.material4457 1).one,v4457_mb,v4457_mg]
  upper := v4457_upper
  lower := (Primitive.Addresses.material4457 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4457_pa_checked.trans (by decide +kernel)
    · exact v4457_pb_checked.trans (by decide +kernel)
    · exact v4457_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 78 Primitive.Addresses.material4457
    · exact v4457_mb_checked.trans (by decide +kernel)
    · exact v4457_mg_checked.trans (by decide +kernel)
  upper_error := v4457_upper_checked
  lower_error := reuse_lower_error 73 78 Primitive.Addresses.material4457

def v4458_pa : Scalar.QComplex := ((999997884653636645434030682152 : Int)/10^30,(-2056863693106301825863615770 : Int)/10^30)
theorem v4458_pa_checked : Scalar.distance (sourceCoefficient 73 79 1 0) v4458_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4458_pb : Scalar.QComplex := ((-887490446738825600743247 : Int)/10^30,(-431476607985062930761323334 : Int)/10^30)
theorem v4458_pb_checked : Scalar.distance (sourceCoefficient 73 79 1 1) v4458_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4458_pg : Scalar.QComplex := ((-93086232955525162252518 : Int)/10^30,(191466097911368949015 : Int)/10^30)
theorem v4458_pg_checked : Scalar.distance (sourceCoefficient 73 79 1 2) v4458_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4458_mb : Scalar.QComplex := ((-1259834995991643938399985 : Int)/10^30,(-431475681462317873094795174 : Int)/10^30)
theorem v4458_mb_checked : Scalar.distance (sourceCoefficient 73 79 3 1) v4458_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4458_mg : Scalar.QComplex := ((-93086033068647197326271 : Int)/10^30,(271795253212107158272 : Int)/10^30)
theorem v4458_mg_checked : Scalar.distance (sourceCoefficient 73 79 3 2) v4458_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4458_upper : Scalar.QComplex := ((999992845314118372195017859141 : Int)/10^30,(-3782766259462186912885205550 : Int)/10^30)
theorem v4458_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 79 5) 1) 14) v4458_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4458 : Material (73 : Basis) (79 : Basis) where
  plus := ![v4458_pa,v4458_pb,v4458_pg]
  minus := ![(Primitive.Addresses.material4458 1).one,v4458_mb,v4458_mg]
  upper := v4458_upper
  lower := (Primitive.Addresses.material4458 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4458_pa_checked.trans (by decide +kernel)
    · exact v4458_pb_checked.trans (by decide +kernel)
    · exact v4458_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 79 Primitive.Addresses.material4458
    · exact v4458_mb_checked.trans (by decide +kernel)
    · exact v4458_mg_checked.trans (by decide +kernel)
  upper_error := v4458_upper_checked
  lower_error := reuse_lower_error 73 79 Primitive.Addresses.material4458

def v4459_pa : Scalar.QComplex := ((999997866696390157746823285731 : Int)/10^30,(-2065575626478056258592692232 : Int)/10^30)
theorem v4459_pa_checked : Scalar.distance (sourceCoefficient 73 80 1 0) v4459_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4459_pb : Scalar.QComplex := ((-891249449974689355720551 : Int)/10^30,(-431476600151724662950821057 : Int)/10^30)
theorem v4459_pb_checked : Scalar.distance (sourceCoefficient 73 80 1 1) v4459_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4459_pg : Scalar.QComplex := ((-93086231274759795610660 : Int)/10^30,(192277060667190809444 : Int)/10^30)
theorem v4459_pg_checked : Scalar.distance (sourceCoefficient 73 80 1 2) v4459_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4459_mb : Scalar.QComplex := ((-1263593991068040869069043 : Int)/10^30,(-431475670385132028664771505 : Int)/10^30)
theorem v4459_mb_checked : Scalar.distance (sourceCoefficient 73 80 3 1) v4459_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4459_mg : Scalar.QComplex := ((-93086030688058122642581 : Int)/10^30,(272606214215545709330 : Int)/10^30)
theorem v4459_mg_checked : Scalar.distance (sourceCoefficient 73 80 3 2) v4459_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4459_upper : Scalar.QComplex := ((999992812320891970490581628448 : Int)/10^30,(-3791478148865961594895771368 : Int)/10^30)
theorem v4459_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 80 5) 1) 14) v4459_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4459 : Material (73 : Basis) (80 : Basis) where
  plus := ![v4459_pa,v4459_pb,v4459_pg]
  minus := ![(Primitive.Addresses.material4459 1).one,v4459_mb,v4459_mg]
  upper := v4459_upper
  lower := (Primitive.Addresses.material4459 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4459_pa_checked.trans (by decide +kernel)
    · exact v4459_pb_checked.trans (by decide +kernel)
    · exact v4459_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 80 Primitive.Addresses.material4459
    · exact v4459_mb_checked.trans (by decide +kernel)
    · exact v4459_mg_checked.trans (by decide +kernel)
  upper_error := v4459_upper_checked
  lower_error := reuse_lower_error 73 80 Primitive.Addresses.material4459

def v4460_pa : Scalar.QComplex := ((999997812167860482755223764926 : Int)/10^30,(-2091807709237399968107913950 : Int)/10^30)
theorem v4460_pa_checked : Scalar.distance (sourceCoefficient 73 81 1 0) v4460_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4460_pb : Scalar.QComplex := ((-902568003330036373625299 : Int)/10^30,(-431476576301458722088892516 : Int)/10^30)
theorem v4460_pb_checked : Scalar.distance (sourceCoefficient 73 81 1 1) v4460_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4460_pg : Scalar.QComplex := ((-93086226164113192852901 : Int)/10^30,(194718911526200951918 : Int)/10^30)
theorem v4460_pg_checked : Scalar.distance (sourceCoefficient 73 81 1 2) v4460_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4460_mb : Scalar.QComplex := ((-1274912519627267858474277 : Int)/10^30,(-431475636767473191402007747 : Int)/10^30)
theorem v4460_mb_checked : Scalar.distance (sourceCoefficient 73 81 3 1) v4460_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4460_mg : Scalar.QComplex := ((-93086023470206108366523 : Int)/10^30,(275048059755085335696 : Int)/10^30)
theorem v4460_mg_checked : Scalar.distance (sourceCoefficient 73 81 3 2) v4460_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4460_upper : Scalar.QComplex := ((999992712518248422669613620264 : Int)/10^30,(-3817710098444404041803001468 : Int)/10^30)
theorem v4460_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 81 5) 1) 14) v4460_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4460 : Material (73 : Basis) (81 : Basis) where
  plus := ![v4460_pa,v4460_pb,v4460_pg]
  minus := ![(Primitive.Addresses.material4460 1).one,v4460_mb,v4460_mg]
  upper := v4460_upper
  lower := (Primitive.Addresses.material4460 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4460_pa_checked.trans (by decide +kernel)
    · exact v4460_pb_checked.trans (by decide +kernel)
    · exact v4460_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 81 Primitive.Addresses.material4460
    · exact v4460_mb_checked.trans (by decide +kernel)
    · exact v4460_mg_checked.trans (by decide +kernel)
  upper_error := v4460_upper_checked
  lower_error := reuse_lower_error 73 81 Primitive.Addresses.material4460

def v4461_pa : Scalar.QComplex := ((999997791325346010152771943328 : Int)/10^30,(-2101747946290412645622166404 : Int)/10^30)
theorem v4461_pa_checked : Scalar.distance (sourceCoefficient 73 82 1 0) v4461_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4461_pb : Scalar.QComplex := ((-906856991853744798360686 : Int)/10^30,(-431476567160344852371836712 : Int)/10^30)
theorem v4461_pb_checked : Scalar.distance (sourceCoefficient 73 82 1 1) v4461_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4461_pg : Scalar.QComplex := ((-93086224207989228014203 : Int)/10^30,(195644212671483980718 : Int)/10^30)
theorem v4461_pg_checked : Scalar.distance (sourceCoefficient 73 82 1 2) v4461_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4461_mb : Scalar.QComplex := ((-1279201498665620270293906 : Int)/10^30,(-431475623925158798251386855 : Int)/10^30)
theorem v4461_mb_checked : Scalar.distance (sourceCoefficient 73 82 3 1) v4461_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4461_mg : Scalar.QComplex := ((-93086020715589657519494 : Int)/10^30,(275973358867789578653 : Int)/10^30)
theorem v4461_mg_checked : Scalar.distance (sourceCoefficient 73 82 3 2) v4461_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4461_upper : Scalar.QComplex := ((999992674519817610305452409156 : Int)/10^30,(-3827650284720312129553780151 : Int)/10^30)
theorem v4461_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 82 5) 1) 14) v4461_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4461 : Material (73 : Basis) (82 : Basis) where
  plus := ![v4461_pa,v4461_pb,v4461_pg]
  minus := ![(Primitive.Addresses.material4461 1).one,v4461_mb,v4461_mg]
  upper := v4461_upper
  lower := (Primitive.Addresses.material4461 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4461_pa_checked.trans (by decide +kernel)
    · exact v4461_pb_checked.trans (by decide +kernel)
    · exact v4461_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 82 Primitive.Addresses.material4461
    · exact v4461_mb_checked.trans (by decide +kernel)
    · exact v4461_mg_checked.trans (by decide +kernel)
  upper_error := v4461_upper_checked
  lower_error := reuse_lower_error 73 82 Primitive.Addresses.material4461

def v4462_pa : Scalar.QComplex := ((999997762715471539090347939387 : Int)/10^30,(-2115316536946600342907337372 : Int)/10^30)
theorem v4462_pa_checked : Scalar.distance (sourceCoefficient 73 83 1 0) v4462_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4462_pb : Scalar.QComplex := ((-912711533226085054598268 : Int)/10^30,(-431476554590814660709744758 : Int)/10^30)
theorem v4462_pb_checked : Scalar.distance (sourceCoefficient 73 83 1 1) v4462_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4462_pg : Scalar.QComplex := ((-93086221520526196156693 : Int)/10^30,(196907264281819494641 : Int)/10^30)
theorem v4462_pg_checked : Scalar.distance (sourceCoefficient 73 83 1 2) v4462_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4462_mb : Scalar.QComplex := ((-1285056027011108763070911 : Int)/10^30,(-431475606303427761225394745 : Int)/10^30)
theorem v4462_mb_checked : Scalar.distance (sourceCoefficient 73 83 3 1) v4462_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4462_mg : Scalar.QComplex := ((-93086016938170972340577 : Int)/10^30,(277236407688673696086 : Int)/10^30)
theorem v4462_mg_checked : Scalar.distance (sourceCoefficient 73 83 3 2) v4462_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4462_upper : Scalar.QComplex := ((999992622491829210639144595502 : Int)/10^30,(-3841218805789630053553309557 : Int)/10^30)
theorem v4462_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 83 5) 1) 14) v4462_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4462 : Material (73 : Basis) (83 : Basis) where
  plus := ![v4462_pa,v4462_pb,v4462_pg]
  minus := ![(Primitive.Addresses.material4462 1).one,v4462_mb,v4462_mg]
  upper := v4462_upper
  lower := (Primitive.Addresses.material4462 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4462_pa_checked.trans (by decide +kernel)
    · exact v4462_pb_checked.trans (by decide +kernel)
    · exact v4462_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 83 Primitive.Addresses.material4462
    · exact v4462_mb_checked.trans (by decide +kernel)
    · exact v4462_mg_checked.trans (by decide +kernel)
  upper_error := v4462_upper_checked
  lower_error := reuse_lower_error 73 83 Primitive.Addresses.material4462

def v4463_pa : Scalar.QComplex := ((999997687767867506417118432422 : Int)/10^30,(-2150455514203846818863275653 : Int)/10^30)
theorem v4463_pa_checked : Scalar.distance (sourceCoefficient 73 84 1 0) v4463_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4463_pb : Scalar.QComplex := ((-927873210468074272315317 : Int)/10^30,(-431476521546805190837992641 : Int)/10^30)
theorem v4463_pb_checked : Scalar.distance (sourceCoefficient 73 84 1 1) v4463_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4463_pg : Scalar.QComplex := ((-93086214467786764052299 : Int)/10^30,(200178226057140465716 : Int)/10^30)
theorem v4463_pg_checked : Scalar.distance (sourceCoefficient 73 84 1 2) v4463_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4463_mb : Scalar.QComplex := ((-1300217670092220695155208 : Int)/10^30,(-431475560175585991906010096 : Int)/10^30)
theorem v4463_mb_checked : Scalar.distance (sourceCoefficient 73 84 3 1) v4463_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4463_mg : Scalar.QComplex := ((-93086007062741472841037 : Int)/10^30,(280507362159869621557 : Int)/10^30)
theorem v4463_mg_checked : Scalar.distance (sourceCoefficient 73 84 3 2) v4463_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4463_upper : Scalar.QComplex := ((999992486897649840725922504919 : Int)/10^30,(-3876357601358732252196832611 : Int)/10^30)
theorem v4463_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 84 5) 1) 14) v4463_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4463 : Material (73 : Basis) (84 : Basis) where
  plus := ![v4463_pa,v4463_pb,v4463_pg]
  minus := ![(Primitive.Addresses.material4463 1).one,v4463_mb,v4463_mg]
  upper := v4463_upper
  lower := (Primitive.Addresses.material4463 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4463_pa_checked.trans (by decide +kernel)
    · exact v4463_pb_checked.trans (by decide +kernel)
    · exact v4463_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 84 Primitive.Addresses.material4463
    · exact v4463_mb_checked.trans (by decide +kernel)
    · exact v4463_mg_checked.trans (by decide +kernel)
  upper_error := v4463_upper_checked
  lower_error := reuse_lower_error 73 84 Primitive.Addresses.material4463

def v4464_pa : Scalar.QComplex := ((999997514634715706959953139829 : Int)/10^30,(-2229512142049350608267315675 : Int)/10^30)
theorem v4464_pa_checked : Scalar.distance (sourceCoefficient 73 85 1 0) v4464_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4464_pb : Scalar.QComplex := ((-961984363141198222594479 : Int)/10^30,(-431476444606581745055564776 : Int)/10^30)
theorem v4464_pb_checked : Scalar.distance (sourceCoefficient 73 85 1 1) v4464_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4464_pg : Scalar.QComplex := ((-93086198110118661372576 : Int)/10^30,(207537324749782997250 : Int)/10^30)
theorem v4464_pg_checked : Scalar.distance (sourceCoefficient 73 85 1 2) v4464_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4464_mb : Scalar.QComplex := ((-1334328743668255973856440 : Int)/10^30,(-431475453799002746865059996 : Int)/10^30)
theorem v4464_mb_checked : Scalar.distance (sourceCoefficient 73 85 3 1) v4464_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4464_mg : Scalar.QComplex := ((-93085984354508730619655 : Int)/10^30,(287866443996452531806 : Int)/10^30)
theorem v4464_mg_checked : Scalar.distance (sourceCoefficient 73 85 3 2) v4464_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4464_upper : Scalar.QComplex := ((999992177320188202675030651507 : Int)/10^30,(-3955413812646562020556465093 : Int)/10^30)
theorem v4464_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 85 5) 1) 14) v4464_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4464 : Material (73 : Basis) (85 : Basis) where
  plus := ![v4464_pa,v4464_pb,v4464_pg]
  minus := ![(Primitive.Addresses.material4464 1).one,v4464_mb,v4464_mg]
  upper := v4464_upper
  lower := (Primitive.Addresses.material4464 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4464_pa_checked.trans (by decide +kernel)
    · exact v4464_pb_checked.trans (by decide +kernel)
    · exact v4464_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 85 Primitive.Addresses.material4464
    · exact v4464_mb_checked.trans (by decide +kernel)
    · exact v4464_mg_checked.trans (by decide +kernel)
  upper_error := v4464_upper_checked
  lower_error := reuse_lower_error 73 85 Primitive.Addresses.material4464

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
