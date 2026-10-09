import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B061
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B062

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1473_pa : Scalar.QComplex := ((999999745070848642891561519855 : Int)/10^30,(-714043582511141027974061296 : Int)/10^30)
theorem v1473_pa_checked : Scalar.distance (sourceCoefficient 16 58 1 0) v1473_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1473_pb : Scalar.QComplex := ((-308093736510951202188556 : Int)/10^30,(-431477385295412711578343511 : Int)/10^30)
theorem v1473_pb_checked : Scalar.distance (sourceCoefficient 16 58 1 1) v1473_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1473_pg : Scalar.QComplex := ((-93086403393312958567052 : Int)/10^30,(66467765906609574878 : Int)/10^30)
theorem v1473_pg_checked : Scalar.distance (sourceCoefficient 16 58 1 2) v1473_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1473_mb : Scalar.QComplex := ((-680439172283467597743100 : Int)/10^30,(-431476958765644093264825433 : Int)/10^30)
theorem v1473_mb_checked : Scalar.distance (sourceCoefficient 16 58 3 1) v1473_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1473_mg : Scalar.QComplex := ((-93086311374302336081738 : Int)/10^30,(146797114830074130705 : Int)/10^30)
theorem v1473_mg_checked : Scalar.distance (sourceCoefficient 16 58 3 2) v1473_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1473_upper : Scalar.QComplex := ((999997023314250695172766657617 : Int)/10^30,(-2439951359751174292298615330 : Int)/10^30)
theorem v1473_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 58 5) 1) 14) v1473_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1473 : Material (16 : Basis) (58 : Basis) where
  plus := ![v1473_pa,v1473_pb,v1473_pg]
  minus := ![(Primitive.Addresses.material1473 1).one,v1473_mb,v1473_mg]
  upper := v1473_upper
  lower := (Primitive.Addresses.material1473 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1473_pa_checked.trans (by decide +kernel)
    · exact v1473_pb_checked.trans (by decide +kernel)
    · exact v1473_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 58 Primitive.Addresses.material1473
    · exact v1473_mb_checked.trans (by decide +kernel)
    · exact v1473_mg_checked.trans (by decide +kernel)
  upper_error := v1473_upper_checked
  lower_error := reuse_lower_error 16 58 Primitive.Addresses.material1473

def v1474_pa : Scalar.QComplex := ((999999732373730325444486950040 : Int)/10^30,(-731609504944605545535482746 : Int)/10^30)
theorem v1474_pa_checked : Scalar.distance (sourceCoefficient 16 59 1 0) v1474_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1474_pb : Scalar.QComplex := ((-315673035603630634403307 : Int)/10^30,(-431477378284109544126711979 : Int)/10^30)
theorem v1474_pb_checked : Scalar.distance (sourceCoefficient 16 59 1 1) v1474_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1474_pg : Scalar.QComplex := ((-93086402046043288381889 : Int)/10^30,(68102914744109273892 : Int)/10^30)
theorem v1474_pg_checked : Scalar.distance (sourceCoefficient 16 59 1 2) v1474_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1474_mb : Scalar.QComplex := ((-688018462503588730534393 : Int)/10^30,(-431476945213749778418739594 : Int)/10^30)
theorem v1474_mb_checked : Scalar.distance (sourceCoefficient 16 59 3 1) v1474_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1474_mg : Scalar.QComplex := ((-93086308615973365154241 : Int)/10^30,(148432261896100140929 : Int)/10^30)
theorem v1474_mg_checked : Scalar.distance (sourceCoefficient 16 59 3 2) v1474_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1474_upper : Scalar.QComplex := ((999996980299962736467053877391 : Int)/10^30,(-2457517234108186441074465797 : Int)/10^30)
theorem v1474_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 59 5) 1) 14) v1474_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1474 : Material (16 : Basis) (59 : Basis) where
  plus := ![v1474_pa,v1474_pb,v1474_pg]
  minus := ![(Primitive.Addresses.material1474 1).one,v1474_mb,v1474_mg]
  upper := v1474_upper
  lower := (Primitive.Addresses.material1474 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1474_pa_checked.trans (by decide +kernel)
    · exact v1474_pb_checked.trans (by decide +kernel)
    · exact v1474_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 59 Primitive.Addresses.material1474
    · exact v1474_mb_checked.trans (by decide +kernel)
    · exact v1474_mg_checked.trans (by decide +kernel)
  upper_error := v1474_upper_checked
  lower_error := reuse_lower_error 16 59 Primitive.Addresses.material1474

def v1475_pa : Scalar.QComplex := ((999999717343133005935926428923 : Int)/10^30,(-751873429569913507953825919 : Int)/10^30)
theorem v1475_pa_checked : Scalar.distance (sourceCoefficient 16 60 1 0) v1475_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1475_pb : Scalar.QComplex := ((-324416461643759370209254 : Int)/10^30,(-431477369975411033123362479 : Int)/10^30)
theorem v1475_pb_checked : Scalar.distance (sourceCoefficient 16 60 1 1) v1475_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1475_pg : Scalar.QComplex := ((-93086400450216765018077 : Int)/10^30,(69989210935753906418 : Int)/10^30)
theorem v1475_pg_checked : Scalar.distance (sourceCoefficient 16 60 1 2) v1475_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1475_mb : Scalar.QComplex := ((-696761878118107752183739 : Int)/10^30,(-431476929359871477783174816 : Int)/10^30)
theorem v1475_mb_checked : Scalar.distance (sourceCoefficient 16 60 3 1) v1475_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1475_mg : Scalar.QComplex := ((-93086305392358778227029 : Int)/10^30,(150318556008264077005 : Int)/10^30)
theorem v1475_mg_checked : Scalar.distance (sourceCoefficient 16 60 3 2) v1475_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1475_upper : Scalar.QComplex := ((999996930295692228867810421836 : Int)/10^30,(-2477781102611311633560269517 : Int)/10^30)
theorem v1475_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 60 5) 1) 14) v1475_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1475 : Material (16 : Basis) (60 : Basis) where
  plus := ![v1475_pa,v1475_pb,v1475_pg]
  minus := ![(Primitive.Addresses.material1475 1).one,v1475_mb,v1475_mg]
  upper := v1475_upper
  lower := (Primitive.Addresses.material1475 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1475_pa_checked.trans (by decide +kernel)
    · exact v1475_pb_checked.trans (by decide +kernel)
    · exact v1475_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 60 Primitive.Addresses.material1475
    · exact v1475_mb_checked.trans (by decide +kernel)
    · exact v1475_mg_checked.trans (by decide +kernel)
  upper_error := v1475_upper_checked
  lower_error := reuse_lower_error 16 60 Primitive.Addresses.material1475

def v1476_pa : Scalar.QComplex := ((999999712920488361842340291625 : Int)/10^30,(-757732763487015464960479189 : Int)/10^30)
theorem v1476_pa_checked : Scalar.distance (sourceCoefficient 16 61 1 0) v1476_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1476_pb : Scalar.QComplex := ((-326944631938891314036342 : Int)/10^30,(-431477367528913215984569400 : Int)/10^30)
theorem v1476_pb_checked : Scalar.distance (sourceCoefficient 16 61 1 1) v1476_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1476_pg : Scalar.QComplex := ((-93086399980470448857272 : Int)/10^30,(70534635349308205275 : Int)/10^30)
theorem v1476_pg_checked : Scalar.distance (sourceCoefficient 16 61 1 2) v1476_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1476_mb : Scalar.QComplex := ((-699290045360668922023375 : Int)/10^30,(-431476924731677471451703479 : Int)/10^30)
theorem v1476_mb_checked : Scalar.distance (sourceCoefficient 16 61 3 1) v1476_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1476_mg : Scalar.QComplex := ((-93086304451935933080577 : Int)/10^30,(150863979813362025312 : Int)/10^30)
theorem v1476_mg_checked : Scalar.distance (sourceCoefficient 16 61 3 2) v1476_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1476_upper : Scalar.QComplex := ((999996915760375385486606197281 : Int)/10^30,(-2483640420168540570237324990 : Int)/10^30)
theorem v1476_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 61 5) 1) 14) v1476_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1476 : Material (16 : Basis) (61 : Basis) where
  plus := ![v1476_pa,v1476_pb,v1476_pg]
  minus := ![(Primitive.Addresses.material1476 1).one,v1476_mb,v1476_mg]
  upper := v1476_upper
  lower := (Primitive.Addresses.material1476 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1476_pa_checked.trans (by decide +kernel)
    · exact v1476_pb_checked.trans (by decide +kernel)
    · exact v1476_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 61 Primitive.Addresses.material1476
    · exact v1476_mb_checked.trans (by decide +kernel)
    · exact v1476_mg_checked.trans (by decide +kernel)
  upper_error := v1476_upper_checked
  lower_error := reuse_lower_error 16 61 Primitive.Addresses.material1476

def v1477_pa : Scalar.QComplex := ((999999706433395438848334217511 : Int)/10^30,(-766246124258356048750882138 : Int)/10^30)
theorem v1477_pa_checked : Scalar.distance (sourceCoefficient 16 62 1 0) v1477_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1477_pb : Scalar.QComplex := ((-330617954881907153926521 : Int)/10^30,(-431477363939059801913280563 : Int)/10^30)
theorem v1477_pb_checked : Scalar.distance (sourceCoefficient 16 62 1 1) v1477_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1477_pg : Scalar.QComplex := ((-93086399291305007171464 : Int)/10^30,(71327113617386800764 : Int)/10^30)
theorem v1477_pg_checked : Scalar.distance (sourceCoefficient 16 62 1 2) v1477_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1477_mb : Scalar.QComplex := ((-702963363838056935729230 : Int)/10^30,(-431476917971913134548155211 : Int)/10^30)
theorem v1477_mb_checked : Scalar.distance (sourceCoefficient 16 62 3 1) v1477_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1477_mg : Scalar.QComplex := ((-93086303078897694546980 : Int)/10^30,(151656457191646006233 : Int)/10^30)
theorem v1477_mg_checked : Scalar.distance (sourceCoefficient 16 62 3 2) v1477_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1477_upper : Scalar.QComplex := ((999996894580003758977729789526 : Int)/10^30,(-2492153757064096454106958214 : Int)/10^30)
theorem v1477_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 62 5) 1) 14) v1477_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1477 : Material (16 : Basis) (62 : Basis) where
  plus := ![v1477_pa,v1477_pb,v1477_pg]
  minus := ![(Primitive.Addresses.material1477 1).one,v1477_mb,v1477_mg]
  upper := v1477_upper
  lower := (Primitive.Addresses.material1477 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1477_pa_checked.trans (by decide +kernel)
    · exact v1477_pb_checked.trans (by decide +kernel)
    · exact v1477_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 62 Primitive.Addresses.material1477
    · exact v1477_mb_checked.trans (by decide +kernel)
    · exact v1477_mg_checked.trans (by decide +kernel)
  upper_error := v1477_upper_checked
  lower_error := reuse_lower_error 16 62 Primitive.Addresses.material1477

def v1478_pa : Scalar.QComplex := ((999999687126789363129608957057 : Int)/10^30,(-791041290568384203774848770 : Int)/10^30)
theorem v1478_pa_checked : Scalar.distance (sourceCoefficient 16 63 1 0) v1478_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1478_pb : Scalar.QComplex := ((-341316509151571355308870 : Int)/10^30,(-431477353246041533200313928 : Int)/10^30)
theorem v1478_pb_checked : Scalar.distance (sourceCoefficient 16 63 1 1) v1478_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1478_pg : Scalar.QComplex := ((-93086397239264181970802 : Int)/10^30,(73635206844992396437 : Int)/10^30)
theorem v1478_pg_checked : Scalar.distance (sourceCoefficient 16 63 1 2) v1478_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1478_mb : Scalar.QComplex := ((-713661904896567264196808 : Int)/10^30,(-431476898046528357611757892 : Int)/10^30)
theorem v1478_mb_checked : Scalar.distance (sourceCoefficient 16 63 3 1) v1478_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1478_mg : Scalar.QComplex := ((-93086299035077130651339 : Int)/10^30,(153964547789024196537 : Int)/10^30)
theorem v1478_mg_checked : Scalar.distance (sourceCoefficient 16 63 3 2) v1478_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1478_upper : Scalar.QComplex := ((999996832479218786988543374282 : Int)/10^30,(-2516948853123186430111750147 : Int)/10^30)
theorem v1478_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 63 5) 1) 14) v1478_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1478 : Material (16 : Basis) (63 : Basis) where
  plus := ![v1478_pa,v1478_pb,v1478_pg]
  minus := ![(Primitive.Addresses.material1478 1).one,v1478_mb,v1478_mg]
  upper := v1478_upper
  lower := (Primitive.Addresses.material1478 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1478_pa_checked.trans (by decide +kernel)
    · exact v1478_pb_checked.trans (by decide +kernel)
    · exact v1478_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 63 Primitive.Addresses.material1478
    · exact v1478_mb_checked.trans (by decide +kernel)
    · exact v1478_mg_checked.trans (by decide +kernel)
  upper_error := v1478_upper_checked
  lower_error := reuse_lower_error 16 63 Primitive.Addresses.material1478

def v1479_pa : Scalar.QComplex := ((999999658466544514532818642939 : Int)/10^30,(-826478550433000134536485994 : Int)/10^30)
theorem v1479_pa_checked : Scalar.distance (sourceCoefficient 16 64 1 0) v1479_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1479_pb : Scalar.QComplex := ((-356606886110562995592041 : Int)/10^30,(-431477337349591453059721236 : Int)/10^30)
theorem v1479_pb_checked : Scalar.distance (sourceCoefficient 16 64 1 1) v1479_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1479_pg : Scalar.QComplex := ((-93086394190583944825580 : Int)/10^30,(76933934411181127124 : Int)/10^30)
theorem v1479_pg_checked : Scalar.distance (sourceCoefficient 16 64 1 2) v1479_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1479_mb : Scalar.QComplex := ((-728952262444332288271693 : Int)/10^30,(-431476868955177533850479580 : Int)/10^30)
theorem v1479_mb_checked : Scalar.distance (sourceCoefficient 16 64 3 1) v1479_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1479_mg : Scalar.QComplex := ((-93086293139744708222660 : Int)/10^30,(157263271496072157838 : Int)/10^30)
theorem v1479_mg_checked : Scalar.distance (sourceCoefficient 16 64 3 2) v1479_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1479_upper : Scalar.QComplex := ((999996742657520941234631499593 : Int)/10^30,(-2552386010743183973913332304 : Int)/10^30)
theorem v1479_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 64 5) 1) 14) v1479_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1479 : Material (16 : Basis) (64 : Basis) where
  plus := ![v1479_pa,v1479_pb,v1479_pg]
  minus := ![(Primitive.Addresses.material1479 1).one,v1479_mb,v1479_mg]
  upper := v1479_upper
  lower := (Primitive.Addresses.material1479 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1479_pa_checked.trans (by decide +kernel)
    · exact v1479_pb_checked.trans (by decide +kernel)
    · exact v1479_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 64 Primitive.Addresses.material1479
    · exact v1479_mb_checked.trans (by decide +kernel)
    · exact v1479_mg_checked.trans (by decide +kernel)
  upper_error := v1479_upper_checked
  lower_error := reuse_lower_error 16 64 Primitive.Addresses.material1479

def v1480_pa : Scalar.QComplex := ((999999628094106873431121462754 : Int)/10^30,(-862445156481932139561672126 : Int)/10^30)
theorem v1480_pa_checked : Scalar.distance (sourceCoefficient 16 65 1 0) v1480_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1480_pb : Scalar.QComplex := ((-372125663572877546681276 : Int)/10^30,(-431477320476952730503084633 : Int)/10^30)
theorem v1480_pb_checked : Scalar.distance (sourceCoefficient 16 65 1 1) v1480_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1480_pg : Scalar.QComplex := ((-93086390956911880881049 : Int)/10^30,(80281936872497614440 : Int)/10^30)
theorem v1480_pg_checked : Scalar.distance (sourceCoefficient 16 65 1 2) v1480_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1480_mb : Scalar.QComplex := ((-744471019567969444846169 : Int)/10^30,(-431476838690539083561937487 : Int)/10^30)
theorem v1480_mb_checked : Scalar.distance (sourceCoefficient 16 65 3 1) v1480_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1480_mg : Scalar.QComplex := ((-93086287016898512639223 : Int)/10^30,(160611269920260965534 : Int)/10^30)
theorem v1480_mg_checked : Scalar.distance (sourceCoefficient 16 65 3 2) v1480_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1480_upper : Scalar.QComplex := ((999996650210029360867019296208 : Int)/10^30,(-2588352510804009200863787465 : Int)/10^30)
theorem v1480_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 65 5) 1) 14) v1480_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1480 : Material (16 : Basis) (65 : Basis) where
  plus := ![v1480_pa,v1480_pb,v1480_pg]
  minus := ![(Primitive.Addresses.material1480 1).one,v1480_mb,v1480_mg]
  upper := v1480_upper
  lower := (Primitive.Addresses.material1480 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1480_pa_checked.trans (by decide +kernel)
    · exact v1480_pb_checked.trans (by decide +kernel)
    · exact v1480_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 65 Primitive.Addresses.material1480
    · exact v1480_mb_checked.trans (by decide +kernel)
    · exact v1480_mg_checked.trans (by decide +kernel)
  upper_error := v1480_upper_checked
  lower_error := reuse_lower_error 16 65 Primitive.Addresses.material1480

def v1481_pa : Scalar.QComplex := ((999999612771134124291416983990 : Int)/10^30,(-880032716326627596955058377 : Int)/10^30)
theorem v1481_pa_checked : Scalar.distance (sourceCoefficient 16 66 1 0) v1481_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1481_pb : Scalar.QComplex := ((-379714297909714082280354 : Int)/10^30,(-431477311955348655885906723 : Int)/10^30)
theorem v1481_pb_checked : Scalar.distance (sourceCoefficient 16 66 1 1) v1481_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1481_pg : Scalar.QComplex := ((-93086389324511271519677 : Int)/10^30,(81919099771727741468 : Int)/10^30)
theorem v1481_pg_checked : Scalar.distance (sourceCoefficient 16 66 1 2) v1481_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1481_mb : Scalar.QComplex := ((-752059643725450081524283 : Int)/10^30,(-431476823620288528640566177 : Int)/10^30)
theorem v1481_mb_checked : Scalar.distance (sourceCoefficient 16 66 3 1) v1481_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1481_mg : Scalar.QComplex := ((-93086283971700664139409 : Int)/10^30,(162248430801212317853 : Int)/10^30)
theorem v1481_mg_checked : Scalar.distance (sourceCoefficient 16 66 3 2) v1481_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1481_upper : Scalar.QComplex := ((999996604532546672516409232330 : Int)/10^30,(-2605940018008039373703711718 : Int)/10^30)
theorem v1481_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 66 5) 1) 14) v1481_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1481 : Material (16 : Basis) (66 : Basis) where
  plus := ![v1481_pa,v1481_pb,v1481_pg]
  minus := ![(Primitive.Addresses.material1481 1).one,v1481_mb,v1481_mg]
  upper := v1481_upper
  lower := (Primitive.Addresses.material1481 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1481_pa_checked.trans (by decide +kernel)
    · exact v1481_pb_checked.trans (by decide +kernel)
    · exact v1481_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 66 Primitive.Addresses.material1481
    · exact v1481_mb_checked.trans (by decide +kernel)
    · exact v1481_mg_checked.trans (by decide +kernel)
  upper_error := v1481_upper_checked
  lower_error := reuse_lower_error 16 66 Primitive.Addresses.material1481

def v1482_pa : Scalar.QComplex := ((999999586359440986374548953293 : Int)/10^30,(-909549859506744600425508464 : Int)/10^30)
theorem v1482_pa_checked : Scalar.distance (sourceCoefficient 16 67 1 0) v1482_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1482_pb : Scalar.QComplex := ((-392450277430730986768984 : Int)/10^30,(-431477297253618786696507262 : Int)/10^30)
theorem v1482_pb_checked : Scalar.distance (sourceCoefficient 16 67 1 1) v1482_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1482_pg : Scalar.QComplex := ((-93086386509359593352003 : Int)/10^30,(84666744793178190165 : Int)/10^30)
theorem v1482_pg_checked : Scalar.distance (sourceCoefficient 16 67 1 2) v1482_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1482_mb : Scalar.QComplex := ((-764795605817349011542727 : Int)/10^30,(-431476797927987414163836223 : Int)/10^30)
theorem v1482_mb_checked : Scalar.distance (sourceCoefficient 16 67 3 1) v1482_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1482_mg : Scalar.QComplex := ((-93086278785456130007602 : Int)/10^30,(164996072370239842949 : Int)/10^30)
theorem v1482_mg_checked : Scalar.distance (sourceCoefficient 16 67 3 2) v1482_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1482_upper : Scalar.QComplex := ((999996527176981517143661938960 : Int)/10^30,(-2635457071641652631634314802 : Int)/10^30)
theorem v1482_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 67 5) 1) 14) v1482_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1482 : Material (16 : Basis) (67 : Basis) where
  plus := ![v1482_pa,v1482_pb,v1482_pg]
  minus := ![(Primitive.Addresses.material1482 1).one,v1482_mb,v1482_mg]
  upper := v1482_upper
  lower := (Primitive.Addresses.material1482 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1482_pa_checked.trans (by decide +kernel)
    · exact v1482_pb_checked.trans (by decide +kernel)
    · exact v1482_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 67 Primitive.Addresses.material1482
    · exact v1482_mb_checked.trans (by decide +kernel)
    · exact v1482_mg_checked.trans (by decide +kernel)
  upper_error := v1482_upper_checked
  lower_error := reuse_lower_error 16 67 Primitive.Addresses.material1482

def v1483_pa : Scalar.QComplex := ((999999540439551263370419673384 : Int)/10^30,(-958707821120414724678869576 : Int)/10^30)
theorem v1483_pa_checked : Scalar.distance (sourceCoefficient 16 68 1 0) v1483_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1483_pb : Scalar.QComplex := ((-413660825075232592764872 : Int)/10^30,(-431477271656806458403559308 : Int)/10^30)
theorem v1483_pb_checked : Scalar.distance (sourceCoefficient 16 68 1 1) v1483_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1483_pg : Scalar.QComplex := ((-93086381610987876699753 : Int)/10^30,(89242683102661121061 : Int)/10^30)
theorem v1483_pg_checked : Scalar.distance (sourceCoefficient 16 68 1 2) v1483_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1483_mb : Scalar.QComplex := ((-786006123475298157890576 : Int)/10^30,(-431476754027437287133029822 : Int)/10^30)
theorem v1483_mb_checked : Scalar.distance (sourceCoefficient 16 68 3 1) v1483_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1483_mg : Scalar.QComplex := ((-93086269938257568770181 : Int)/10^30,(169572004748817633515 : Int)/10^30)
theorem v1483_mg_checked : Scalar.distance (sourceCoefficient 16 68 3 2) v1483_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1483_upper : Scalar.QComplex := ((999996396414978016667812014500 : Int)/10^30,(-2684614880786749590082599930 : Int)/10^30)
theorem v1483_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 68 5) 1) 14) v1483_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1483 : Material (16 : Basis) (68 : Basis) where
  plus := ![v1483_pa,v1483_pb,v1483_pg]
  minus := ![(Primitive.Addresses.material1483 1).one,v1483_mb,v1483_mg]
  upper := v1483_upper
  lower := (Primitive.Addresses.material1483 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1483_pa_checked.trans (by decide +kernel)
    · exact v1483_pb_checked.trans (by decide +kernel)
    · exact v1483_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 68 Primitive.Addresses.material1483
    · exact v1483_mb_checked.trans (by decide +kernel)
    · exact v1483_mg_checked.trans (by decide +kernel)
  upper_error := v1483_upper_checked
  lower_error := reuse_lower_error 16 68 Primitive.Addresses.material1483

def v1484_pa : Scalar.QComplex := ((999999519463490904126506576080 : Int)/10^30,(-980343198719922987766291695 : Int)/10^30)
theorem v1484_pa_checked : Scalar.distance (sourceCoefficient 16 69 1 0) v1484_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1484_pb : Scalar.QComplex := ((-422996000459871726816643 : Int)/10^30,(-431477259950570806303035468 : Int)/10^30)
theorem v1484_pb_checked : Scalar.distance (sourceCoefficient 16 69 1 1) v1484_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1484_pg : Scalar.QComplex := ((-93086379371950142711770 : Int)/10^30,(91256642762902403855 : Int)/10^30)
theorem v1484_pg_checked : Scalar.distance (sourceCoefficient 16 69 1 2) v1484_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1484_mb : Scalar.QComplex := ((-795341285282070719169093 : Int)/10^30,(-431476734265370077547300001 : Int)/10^30)
theorem v1484_mb_checked : Scalar.distance (sourceCoefficient 16 69 3 1) v1484_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1484_mg : Scalar.QComplex := ((-93086265961264187066004 : Int)/10^30,(171585961726980970382 : Int)/10^30)
theorem v1484_mg_checked : Scalar.distance (sourceCoefficient 16 69 3 2) v1484_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1484_upper : Scalar.QComplex := ((999996338098249908174216858287 : Int)/10^30,(-2706250189960127141959728583 : Int)/10^30)
theorem v1484_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 69 5) 1) 14) v1484_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1484 : Material (16 : Basis) (69 : Basis) where
  plus := ![v1484_pa,v1484_pb,v1484_pg]
  minus := ![(Primitive.Addresses.material1484 1).one,v1484_mb,v1484_mg]
  upper := v1484_upper
  lower := (Primitive.Addresses.material1484 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1484_pa_checked.trans (by decide +kernel)
    · exact v1484_pb_checked.trans (by decide +kernel)
    · exact v1484_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 69 Primitive.Addresses.material1484
    · exact v1484_mb_checked.trans (by decide +kernel)
    · exact v1484_mg_checked.trans (by decide +kernel)
  upper_error := v1484_upper_checked
  lower_error := reuse_lower_error 16 69 Primitive.Addresses.material1484

def v1485_pa : Scalar.QComplex := ((999999505410005289033191937748 : Int)/10^30,(-994575157945678204807614089 : Int)/10^30)
theorem v1485_pa_checked : Scalar.distance (sourceCoefficient 16 70 1 0) v1485_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1485_pb : Scalar.QComplex := ((-429136768407320065141749 : Int)/10^30,(-431477252103261025953411989 : Int)/10^30)
theorem v1485_pb_checked : Scalar.distance (sourceCoefficient 16 70 1 1) v1485_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1485_pg : Scalar.QComplex := ((-93086377871371255839232 : Int)/10^30,(92581444763866427393 : Int)/10^30)
theorem v1485_pg_checked : Scalar.distance (sourceCoefficient 16 70 1 2) v1485_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1485_mb : Scalar.QComplex := ((-801482044171155592970598 : Int)/10^30,(-431476721118857050383426536 : Int)/10^30)
theorem v1485_mb_checked : Scalar.distance (sourceCoefficient 16 70 3 1) v1485_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1485_mg : Scalar.QComplex := ((-93086263317441398962798 : Int)/10^30,(172910761939728666712 : Int)/10^30)
theorem v1485_mg_checked : Scalar.distance (sourceCoefficient 16 70 3 2) v1485_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1485_upper : Scalar.QComplex := ((999996299481714713698720148079 : Int)/10^30,(-2720482103734009646211887882 : Int)/10^30)
theorem v1485_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 70 5) 1) 14) v1485_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1485 : Material (16 : Basis) (70 : Basis) where
  plus := ![v1485_pa,v1485_pb,v1485_pg]
  minus := ![(Primitive.Addresses.material1485 1).one,v1485_mb,v1485_mg]
  upper := v1485_upper
  lower := (Primitive.Addresses.material1485 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1485_pa_checked.trans (by decide +kernel)
    · exact v1485_pb_checked.trans (by decide +kernel)
    · exact v1485_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 70 Primitive.Addresses.material1485
    · exact v1485_mb_checked.trans (by decide +kernel)
    · exact v1485_mg_checked.trans (by decide +kernel)
  upper_error := v1485_upper_checked
  lower_error := reuse_lower_error 16 70 Primitive.Addresses.material1485

def v1486_pa : Scalar.QComplex := ((999999480953903155657199918695 : Int)/10^30,(-1018867962142217400882166043 : Int)/10^30)
theorem v1486_pa_checked : Scalar.distance (sourceCoefficient 16 71 1 0) v1486_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1486_pb : Scalar.QComplex := ((-439618562821732265957015 : Int)/10^30,(-431477238439331318994515556 : Int)/10^30)
theorem v1486_pb_checked : Scalar.distance (sourceCoefficient 16 71 1 1) v1486_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1486_pg : Scalar.QComplex := ((-93086375259185933819552 : Int)/10^30,(94842774691304513926 : Int)/10^30)
theorem v1486_pg_checked : Scalar.distance (sourceCoefficient 16 71 1 2) v1486_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1486_mb : Scalar.QComplex := ((-811963822891360755074056 : Int)/10^30,(-431476698409615933988202267 : Int)/10^30)
theorem v1486_mb_checked : Scalar.distance (sourceCoefficient 16 71 3 1) v1486_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1486_mg : Scalar.QComplex := ((-93086258753831168719239 : Int)/10^30,(175172088770971988933 : Int)/10^30)
theorem v1486_mg_checked : Scalar.distance (sourceCoefficient 16 71 3 2) v1486_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1486_upper : Scalar.QComplex := ((999996233098472787568754026824 : Int)/10^30,(-2744774829540256982826545594 : Int)/10^30)
theorem v1486_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 71 5) 1) 14) v1486_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1486 : Material (16 : Basis) (71 : Basis) where
  plus := ![v1486_pa,v1486_pb,v1486_pg]
  minus := ![(Primitive.Addresses.material1486 1).one,v1486_mb,v1486_mg]
  upper := v1486_upper
  lower := (Primitive.Addresses.material1486 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1486_pa_checked.trans (by decide +kernel)
    · exact v1486_pb_checked.trans (by decide +kernel)
    · exact v1486_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 71 Primitive.Addresses.material1486
    · exact v1486_mb_checked.trans (by decide +kernel)
    · exact v1486_mg_checked.trans (by decide +kernel)
  upper_error := v1486_upper_checked
  lower_error := reuse_lower_error 16 71 Primitive.Addresses.material1486

def v1487_pa : Scalar.QComplex := ((999999453746374104857140192082 : Int)/10^30,(-1045230574274050747366505149 : Int)/10^30)
theorem v1487_pa_checked : Scalar.distance (sourceCoefficient 16 72 1 0) v1487_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1487_pb : Scalar.QComplex := ((-450993432176598091740942 : Int)/10^30,(-431477223227067461271986688 : Int)/10^30)
theorem v1487_pb_checked : Scalar.distance (sourceCoefficient 16 72 1 1) v1487_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1487_pg : Scalar.QComplex := ((-93086372351922503091361 : Int)/10^30,(97296775579204525869 : Int)/10^30)
theorem v1487_pg_checked : Scalar.distance (sourceCoefficient 16 72 1 2) v1487_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1487_mb : Scalar.QComplex := ((-823338674883344288546656 : Int)/10^30,(-431476673381357792335618765 : Int)/10^30)
theorem v1487_mb_checked : Scalar.distance (sourceCoefficient 16 72 3 1) v1487_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1487_mg : Scalar.QComplex := ((-93086253728876578337525 : Int)/10^30,(177626086236297914496 : Int)/10^30)
theorem v1487_mg_checked : Scalar.distance (sourceCoefficient 16 72 3 2) v1487_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1487_upper : Scalar.QComplex := ((999996160391507317133304135556 : Int)/10^30,(-2771137355450349434976037142 : Int)/10^30)
theorem v1487_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 72 5) 1) 14) v1487_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1487 : Material (16 : Basis) (72 : Basis) where
  plus := ![v1487_pa,v1487_pb,v1487_pg]
  minus := ![(Primitive.Addresses.material1487 1).one,v1487_mb,v1487_mg]
  upper := v1487_upper
  lower := (Primitive.Addresses.material1487 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1487_pa_checked.trans (by decide +kernel)
    · exact v1487_pb_checked.trans (by decide +kernel)
    · exact v1487_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 72 Primitive.Addresses.material1487
    · exact v1487_mb_checked.trans (by decide +kernel)
    · exact v1487_mg_checked.trans (by decide +kernel)
  upper_error := v1487_upper_checked
  lower_error := reuse_lower_error 16 72 Primitive.Addresses.material1487

def v1488_pa : Scalar.QComplex := ((999999443824670863396456901010 : Int)/10^30,(-1054680211695569049842009862 : Int)/10^30)
theorem v1488_pa_checked : Scalar.distance (sourceCoefficient 16 73 1 0) v1488_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1488_pb : Scalar.QComplex := ((-455070736380415138809854 : Int)/10^30,(-431477217676909985815518134 : Int)/10^30)
theorem v1488_pb_checked : Scalar.distance (sourceCoefficient 16 73 1 1) v1488_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1488_pg : Scalar.QComplex := ((-93086371291442458730385 : Int)/10^30,(98176408382927119525 : Int)/10^30)
theorem v1488_pg_checked : Scalar.distance (sourceCoefficient 16 73 1 2) v1488_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1488_mb : Scalar.QComplex := ((-827415972779458707021332 : Int)/10^30,(-431476664312672490526811038 : Int)/10^30)
theorem v1488_mb_checked : Scalar.distance (sourceCoefficient 16 73 3 1) v1488_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1488_mg : Scalar.QComplex := ((-93086251909313436419958 : Int)/10^30,(178505717797346498085 : Int)/10^30)
theorem v1488_mg_checked : Scalar.distance (sourceCoefficient 16 73 3 2) v1488_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1488_upper : Scalar.QComplex := ((999996134160601927753821858647 : Int)/10^30,(-2780586961673783125612893759 : Int)/10^30)
theorem v1488_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 73 5) 1) 14) v1488_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1488 : Material (16 : Basis) (73 : Basis) where
  plus := ![v1488_pa,v1488_pb,v1488_pg]
  minus := ![(Primitive.Addresses.material1488 1).one,v1488_mb,v1488_mg]
  upper := v1488_upper
  lower := (Primitive.Addresses.material1488 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1488_pa_checked.trans (by decide +kernel)
    · exact v1488_pb_checked.trans (by decide +kernel)
    · exact v1488_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 73 Primitive.Addresses.material1488
    · exact v1488_mb_checked.trans (by decide +kernel)
    · exact v1488_mg_checked.trans (by decide +kernel)
  upper_error := v1488_upper_checked
  lower_error := reuse_lower_error 16 73 Primitive.Addresses.material1488

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
