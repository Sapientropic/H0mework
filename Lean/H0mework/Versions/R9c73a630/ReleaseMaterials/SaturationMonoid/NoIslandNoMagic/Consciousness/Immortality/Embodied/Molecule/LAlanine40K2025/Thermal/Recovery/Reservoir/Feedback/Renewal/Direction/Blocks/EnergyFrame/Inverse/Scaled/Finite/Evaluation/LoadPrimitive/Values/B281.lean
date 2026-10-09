import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B187
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B188

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4497_pa : Scalar.QComplex := ((999996916202012703556042618303 : Int)/10^30,(-2483462595809097637226548959 : Int)/10^30)
theorem v4497_pa_checked : Scalar.distance (sourceCoefficient 74 95 1 0) v4497_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4497_pb : Scalar.QComplex := ((-1071558245059659674103773 : Int)/10^30,(-431476174595411586954427552 : Int)/10^30)
theorem v4497_pb_checked : Scalar.distance (sourceCoefficient 74 95 1 1) v4497_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4497_pg : Scalar.QComplex := ((-93086141131197798088914 : Int)/10^30,(231176662589663299861 : Int)/10^30)
theorem v4497_pg_checked : Scalar.distance (sourceCoefficient 74 95 1 2) v4497_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4497_mb : Scalar.QComplex := ((-1443902351779874418560423 : Int)/10^30,(-431475089230608055075348944 : Int)/10^30)
theorem v4497_mb_checked : Scalar.distance (sourceCoefficient 74 95 3 1) v4497_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4497_mg : Scalar.QComplex := ((-93085906975925203629263 : Int)/10^30,(311505723864084515837 : Int)/10^30)
theorem v4497_mg_checked : Scalar.distance (sourceCoefficient 74 95 3 2) v4497_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4497_upper : Scalar.QComplex := ((999991140592931510362529728705 : Int)/10^30,(-4209362855336383297048584117 : Int)/10^30)
theorem v4497_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 95 5) 1) 14) v4497_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4497 : Material (74 : Basis) (95 : Basis) where
  plus := ![v4497_pa,v4497_pb,v4497_pg]
  minus := ![(Primitive.Addresses.material4497 1).one,v4497_mb,v4497_mg]
  upper := v4497_upper
  lower := (Primitive.Addresses.material4497 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4497_pa_checked.trans (by decide +kernel)
    · exact v4497_pb_checked.trans (by decide +kernel)
    · exact v4497_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 95 Primitive.Addresses.material4497
    · exact v4497_mb_checked.trans (by decide +kernel)
    · exact v4497_mg_checked.trans (by decide +kernel)
  upper_error := v4497_upper_checked
  lower_error := reuse_lower_error 74 95 Primitive.Addresses.material4497

def v4498_pa : Scalar.QComplex := ((999996863167343840322007129535 : Int)/10^30,(-2504726626320773401611416825 : Int)/10^30)
theorem v4498_pa_checked : Scalar.distance (sourceCoefficient 74 96 1 0) v4498_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4498_pb : Scalar.QComplex := ((-1080733192221157184570261 : Int)/10^30,(-431476150245380573968280109 : Int)/10^30)
theorem v4498_pb_checked : Scalar.distance (sourceCoefficient 74 96 1 1) v4498_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4498_pg : Scalar.QComplex := ((-93086136036170929030103 : Int)/10^30,(233156054842641793284 : Int)/10^30)
theorem v4498_pg_checked : Scalar.distance (sourceCoefficient 74 96 1 2) v4498_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4498_mb : Scalar.QComplex := ((-1453077274512139705480417 : Int)/10^30,(-431475056963019932626795006 : Int)/10^30)
theorem v4498_mb_checked : Scalar.distance (sourceCoefficient 74 96 3 1) v4498_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4498_mg : Scalar.QComplex := ((-93085900172773865879095 : Int)/10^30,(313485110983266094275 : Int)/10^30)
theorem v4498_mg_checked : Scalar.distance (sourceCoefficient 74 96 3 2) v4498_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4498_upper : Scalar.QComplex := ((999991050858554030664553684578 : Int)/10^30,(-4230626762644756272414356141 : Int)/10^30)
theorem v4498_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 96 5) 1) 14) v4498_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4498 : Material (74 : Basis) (96 : Basis) where
  plus := ![v4498_pa,v4498_pb,v4498_pg]
  minus := ![(Primitive.Addresses.material4498 1).one,v4498_mb,v4498_mg]
  upper := v4498_upper
  lower := (Primitive.Addresses.material4498 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4498_pa_checked.trans (by decide +kernel)
    · exact v4498_pb_checked.trans (by decide +kernel)
    · exact v4498_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 96 Primitive.Addresses.material4498
    · exact v4498_mb_checked.trans (by decide +kernel)
    · exact v4498_mg_checked.trans (by decide +kernel)
  upper_error := v4498_upper_checked
  lower_error := reuse_lower_error 74 96 Primitive.Addresses.material4498

def v4499_pa : Scalar.QComplex := ((999996677239628194118808550726 : Int)/10^30,(-2577888613356921971130437722 : Int)/10^30)
theorem v4499_pa_checked : Scalar.distance (sourceCoefficient 74 97 1 0) v4499_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4499_pb : Scalar.QComplex := ((-1112300929464203820035702 : Int)/10^30,(-431476064478333837964540575 : Int)/10^30)
theorem v4499_pb_checked : Scalar.distance (sourceCoefficient 74 97 1 1) v4499_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4499_pg : Scalar.QComplex := ((-93086118130858686934782 : Int)/10^30,(239966441342119788606 : Int)/10^30)
theorem v4499_pg_checked : Scalar.distance (sourceCoefficient 74 97 1 2) v4499_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4499_mb : Scalar.QComplex := ((-1484644925987976519715652 : Int)/10^30,(-431474943954469648972341574 : Int)/10^30)
theorem v4499_mb_checked : Scalar.distance (sourceCoefficient 74 97 3 1) v4499_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4499_mg : Scalar.QComplex := ((-93085876390411470121968 : Int)/10^30,(320295479495447906202 : Int)/10^30)
theorem v4499_mg_checked : Scalar.distance (sourceCoefficient 74 97 3 2) v4499_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4499_upper : Scalar.QComplex := ((999990738660162881177705459204 : Int)/10^30,(-4303788319820349387554851785 : Int)/10^30)
theorem v4499_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 97 5) 1) 14) v4499_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4499 : Material (74 : Basis) (97 : Basis) where
  plus := ![v4499_pa,v4499_pb,v4499_pg]
  minus := ![(Primitive.Addresses.material4499 1).one,v4499_mb,v4499_mg]
  upper := v4499_upper
  lower := (Primitive.Addresses.material4499 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4499_pa_checked.trans (by decide +kernel)
    · exact v4499_pb_checked.trans (by decide +kernel)
    · exact v4499_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 97 Primitive.Addresses.material4499
    · exact v4499_mb_checked.trans (by decide +kernel)
    · exact v4499_mg_checked.trans (by decide +kernel)
  upper_error := v4499_upper_checked
  lower_error := reuse_lower_error 74 97 Primitive.Addresses.material4499

def v4500_pa : Scalar.QComplex := ((999997885283121888724265428364 : Int)/10^30,(-2056557629680013829794949167 : Int)/10^30)
theorem v4500_pa_checked : Scalar.distance (sourceCoefficient 75 76 1 0) v4500_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4500_pb : Scalar.QComplex := ((-887358387826459769662723 : Int)/10^30,(-431476608536745282910352147 : Int)/10^30)
theorem v4500_pb_checked : Scalar.distance (sourceCoefficient 75 76 1 1) v4500_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4500_pg : Scalar.QComplex := ((-93086233044333065149804 : Int)/10^30,(191437607621834929323 : Int)/10^30)
theorem v4500_pg_checked : Scalar.distance (sourceCoefficient 75 76 1 2) v4500_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4500_mb : Scalar.QComplex := ((-1259702937604526698837539 : Int)/10^30,(-431475682127960913486359889 : Int)/10^30)
theorem v4500_mb_checked : Scalar.distance (sourceCoefficient 75 76 3 1) v4500_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4500_mg : Scalar.QComplex := ((-93086033182040903869167 : Int)/10^30,(271766763009818595885 : Int)/10^30)
theorem v4500_mg_checked : Scalar.distance (sourceCoefficient 75 76 3 2) v4500_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4500_upper : Scalar.QComplex := ((999992846471840385856870596175 : Int)/10^30,(-3782460197578178861000680403 : Int)/10^30)
theorem v4500_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 76 5) 1) 14) v4500_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4500 : Material (75 : Basis) (76 : Basis) where
  plus := ![v4500_pa,v4500_pb,v4500_pg]
  minus := ![(Primitive.Addresses.material4500 1).one,v4500_mb,v4500_mg]
  upper := v4500_upper
  lower := (Primitive.Addresses.material4500 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4500_pa_checked.trans (by decide +kernel)
    · exact v4500_pb_checked.trans (by decide +kernel)
    · exact v4500_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 76 Primitive.Addresses.material4500
    · exact v4500_mb_checked.trans (by decide +kernel)
    · exact v4500_mg_checked.trans (by decide +kernel)
  upper_error := v4500_upper_checked
  lower_error := reuse_lower_error 75 76 Primitive.Addresses.material4500

def v4501_pa : Scalar.QComplex := ((999997879360838954338032131649 : Int)/10^30,(-2059435317017961740695773476 : Int)/10^30)
theorem v4501_pa_checked : Scalar.distance (sourceCoefficient 75 77 1 0) v4501_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4501_pb : Scalar.QComplex := ((-888600045213398940991476 : Int)/10^30,(-431476605975673128460302697 : Int)/10^30)
theorem v4501_pb_checked : Scalar.distance (sourceCoefficient 75 77 1 1) v4501_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4501_pg : Scalar.QComplex := ((-93086232492429698620098 : Int)/10^30,(191705481261205596866 : Int)/10^30)
theorem v4501_pg_checked : Scalar.distance (sourceCoefficient 75 77 1 2) v4501_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4501_mb : Scalar.QComplex := ((-1260944592319050155580503 : Int)/10^30,(-431475678495395309884794570 : Int)/10^30)
theorem v4501_mb_checked : Scalar.distance (sourceCoefficient 75 77 3 1) v4501_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4501_mg : Scalar.QComplex := ((-93086032398974856642281 : Int)/10^30,(272034636073179916550 : Int)/10^30)
theorem v4501_mg_checked : Scalar.distance (sourceCoefficient 75 77 3 2) v4501_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4501_upper : Scalar.QComplex := ((999992835582938988473289740865 : Int)/10^30,(-3785337870408826439488886475 : Int)/10^30)
theorem v4501_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 77 5) 1) 14) v4501_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4501 : Material (75 : Basis) (77 : Basis) where
  plus := ![v4501_pa,v4501_pb,v4501_pg]
  minus := ![(Primitive.Addresses.material4501 1).one,v4501_mb,v4501_mg]
  upper := v4501_upper
  lower := (Primitive.Addresses.material4501 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4501_pa_checked.trans (by decide +kernel)
    · exact v4501_pb_checked.trans (by decide +kernel)
    · exact v4501_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 77 Primitive.Addresses.material4501
    · exact v4501_mb_checked.trans (by decide +kernel)
    · exact v4501_mg_checked.trans (by decide +kernel)
  upper_error := v4501_upper_checked
  lower_error := reuse_lower_error 75 77 Primitive.Addresses.material4501

def v4502_pa : Scalar.QComplex := ((999997843583816301980526756742 : Int)/10^30,(-2076734869275633276006807421 : Int)/10^30)
theorem v4502_pa_checked : Scalar.distance (sourceCoefficient 75 78 1 0) v4502_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4502_pb : Scalar.QComplex := ((-896064413011875116257738 : Int)/10^30,(-431476590479082457891768450 : Int)/10^30)
theorem v4502_pb_checked : Scalar.distance (sourceCoefficient 75 78 1 1) v4502_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4502_pg : Scalar.QComplex := ((-93086229155644333727529 : Int)/10^30,(193315834806303419713 : Int)/10^30)
theorem v4502_pg_checked : Scalar.distance (sourceCoefficient 75 78 1 2) v4502_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4502_mb : Scalar.QComplex := ((-1268408943965341252847500 : Int)/10^30,(-431475656557397181966213839 : Int)/10^30)
theorem v4502_mb_checked : Scalar.distance (sourceCoefficient 75 78 3 1) v4502_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4502_mg : Scalar.QComplex := ((-93086027672528152399299 : Int)/10^30,(273644986139174031096 : Int)/10^30)
theorem v4502_mg_checked : Scalar.distance (sourceCoefficient 75 78 3 2) v4502_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4502_upper : Scalar.QComplex := ((999992769948511828168602363683 : Int)/10^30,(-3802637335152951603329192072 : Int)/10^30)
theorem v4502_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 78 5) 1) 14) v4502_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4502 : Material (75 : Basis) (78 : Basis) where
  plus := ![v4502_pa,v4502_pb,v4502_pg]
  minus := ![(Primitive.Addresses.material4502 1).one,v4502_mb,v4502_mg]
  upper := v4502_upper
  lower := (Primitive.Addresses.material4502 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4502_pa_checked.trans (by decide +kernel)
    · exact v4502_pb_checked.trans (by decide +kernel)
    · exact v4502_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 78 Primitive.Addresses.material4502
    · exact v4502_mb_checked.trans (by decide +kernel)
    · exact v4502_mg_checked.trans (by decide +kernel)
  upper_error := v4502_upper_checked
  lower_error := reuse_lower_error 75 78 Primitive.Addresses.material4502

def v4503_pa : Scalar.QComplex := ((999997831986145692289027729047 : Int)/10^30,(-2082311938286708635842024797 : Int)/10^30)
theorem v4503_pa_checked : Scalar.distance (sourceCoefficient 75 79 1 0) v4503_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4503_pb : Scalar.QComplex := ((-898470792863675746909993 : Int)/10^30,(-431476585446556213527390345 : Int)/10^30)
theorem v4503_pb_checked : Scalar.distance (sourceCoefficient 75 79 1 1) v4503_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4503_pg : Scalar.QComplex := ((-93086228072995945328768 : Int)/10^30,(193834984243410107080 : Int)/10^30)
theorem v4503_pg_checked : Scalar.distance (sourceCoefficient 75 79 1 2) v4503_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4503_mb : Scalar.QComplex := ((-1270815318578293195363879 : Int)/10^30,(-431475649448275378662705500 : Int)/10^30)
theorem v4503_mb_checked : Scalar.distance (sourceCoefficient 75 79 3 1) v4503_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4503_mg : Scalar.QComplex := ((-93086026141877584519622 : Int)/10^30,(274164134448700858212 : Int)/10^30)
theorem v4503_mg_checked : Scalar.distance (sourceCoefficient 75 79 3 2) v4503_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4503_upper : Scalar.QComplex := ((999992748725343326477485144440 : Int)/10^30,(-3808214375841110459845348406 : Int)/10^30)
theorem v4503_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 79 5) 1) 14) v4503_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4503 : Material (75 : Basis) (79 : Basis) where
  plus := ![v4503_pa,v4503_pb,v4503_pg]
  minus := ![(Primitive.Addresses.material4503 1).one,v4503_mb,v4503_mg]
  upper := v4503_upper
  lower := (Primitive.Addresses.material4503 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4503_pa_checked.trans (by decide +kernel)
    · exact v4503_pb_checked.trans (by decide +kernel)
    · exact v4503_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 79 Primitive.Addresses.material4503
    · exact v4503_mb_checked.trans (by decide +kernel)
    · exact v4503_mg_checked.trans (by decide +kernel)
  upper_error := v4503_upper_checked
  lower_error := reuse_lower_error 75 79 Primitive.Addresses.material4503

def v4504_pa : Scalar.QComplex := ((999997813807195319193825807035 : Int)/10^30,(-2091023871198660685021163594 : Int)/10^30)
theorem v4504_pa_checked : Scalar.distance (sourceCoefficient 75 80 1 0) v4504_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4504_pb : Scalar.QComplex := ((-902229795967276574346371 : Int)/10^30,(-431476577549444450884477154 : Int)/10^30)
theorem v4504_pb_checked : Scalar.distance (sourceCoefficient 75 80 1 1) v4504_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4504_pg : Scalar.QComplex := ((-93086226375032559378364 : Int)/10^30,(194645946963564165586 : Int)/10^30)
theorem v4504_pg_checked : Scalar.distance (sourceCoefficient 75 80 1 2) v4504_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4504_mb : Scalar.QComplex := ((-1274574313467393593950756 : Int)/10^30,(-431475638307316177283007204 : Int)/10^30)
theorem v4504_mb_checked : Scalar.distance (sourceCoefficient 75 80 3 1) v4504_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4504_mg : Scalar.QComplex := ((-93086023744090527710701 : Int)/10^30,(274975095401630504534 : Int)/10^30)
theorem v4504_mg_checked : Scalar.distance (sourceCoefficient 75 80 3 2) v4504_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4504_upper : Scalar.QComplex := ((999992715510414163144149596351 : Int)/10^30,(-3816926264402442649732787615 : Int)/10^30)
theorem v4504_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 80 5) 1) 14) v4504_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4504 : Material (75 : Basis) (80 : Basis) where
  plus := ![v4504_pa,v4504_pb,v4504_pg]
  minus := ![(Primitive.Addresses.material4504 1).one,v4504_mb,v4504_mg]
  upper := v4504_upper
  lower := (Primitive.Addresses.material4504 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4504_pa_checked.trans (by decide +kernel)
    · exact v4504_pb_checked.trans (by decide +kernel)
    · exact v4504_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 80 Primitive.Addresses.material4504
    · exact v4504_mb_checked.trans (by decide +kernel)
    · exact v4504_mg_checked.trans (by decide +kernel)
  upper_error := v4504_upper_checked
  lower_error := reuse_lower_error 75 80 Primitive.Addresses.material4504

def v4505_pa : Scalar.QComplex := ((999997758611103758610529215016 : Int)/10^30,(-2117255952561851872659209530 : Int)/10^30)
theorem v4505_pa_checked : Scalar.distance (sourceCoefficient 75 81 1 0) v4505_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4505_pb : Scalar.QComplex := ((-913548348921017975574760 : Int)/10^30,(-431476553507153212978191728 : Int)/10^30)
theorem v4505_pb_checked : Scalar.distance (sourceCoefficient 75 81 1 1) v4505_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4505_pg : Scalar.QComplex := ((-93086221212601829448671 : Int)/10^30,(197087797714271929952 : Int)/10^30)
theorem v4505_pg_checked : Scalar.distance (sourceCoefficient 75 81 1 2) v4505_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4505_mb : Scalar.QComplex := ((-1285892841459305933364809 : Int)/10^30,(-431475604497632461043240186 : Int)/10^30)
theorem v4505_mb_checked : Scalar.distance (sourceCoefficient 75 81 3 1) v4505_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4505_mg : Scalar.QComplex := ((-93086016474454499004381 : Int)/10^30,(277416940788180423639 : Int)/10^30)
theorem v4505_mg_checked : Scalar.distance (sourceCoefficient 75 81 3 2) v4505_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4505_upper : Scalar.QComplex := ((999992615040212133619090570806 : Int)/10^30,(-3843158211432583400377936858 : Int)/10^30)
theorem v4505_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 81 5) 1) 14) v4505_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4505 : Material (75 : Basis) (81 : Basis) where
  plus := ![v4505_pa,v4505_pb,v4505_pg]
  minus := ![(Primitive.Addresses.material4505 1).one,v4505_mb,v4505_mg]
  upper := v4505_upper
  lower := (Primitive.Addresses.material4505 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4505_pa_checked.trans (by decide +kernel)
    · exact v4505_pb_checked.trans (by decide +kernel)
    · exact v4505_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 81 Primitive.Addresses.material4505
    · exact v4505_mb_checked.trans (by decide +kernel)
    · exact v4505_mg_checked.trans (by decide +kernel)
  upper_error := v4505_upper_checked
  lower_error := reuse_lower_error 75 81 Primitive.Addresses.material4505

def v4506_pa : Scalar.QComplex := ((999997737515627161357609189868 : Int)/10^30,(-2127196189081239267759113667 : Int)/10^30)
theorem v4506_pa_checked : Scalar.distance (sourceCoefficient 75 82 1 0) v4506_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4506_pb : Scalar.QComplex := ((-917837337291228192057288 : Int)/10^30,(-431476544293274363472345022 : Int)/10^30)
theorem v4506_pb_checked : Scalar.distance (sourceCoefficient 75 82 1 1) v4506_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4506_pg : Scalar.QComplex := ((-93086219236855080396214 : Int)/10^30,(198013098818160565096 : Int)/10^30)
theorem v4506_pg_checked : Scalar.distance (sourceCoefficient 75 82 1 2) v4506_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4506_mb : Scalar.QComplex := ((-1290181820281367293741285 : Int)/10^30,(-431475591582553247659596311 : Int)/10^30)
theorem v4506_mb_checked : Scalar.distance (sourceCoefficient 75 82 3 1) v4506_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4506_mg : Scalar.QComplex := ((-93086013700215306971550 : Int)/10^30,(278342239842556709353 : Int)/10^30)
theorem v4506_mg_checked : Scalar.distance (sourceCoefficient 75 82 3 2) v4506_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4506_upper : Scalar.QComplex := ((999992576788820494350658144196 : Int)/10^30,(-3853098396738277321884517329 : Int)/10^30)
theorem v4506_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 82 5) 1) 14) v4506_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4506 : Material (75 : Basis) (82 : Basis) where
  plus := ![v4506_pa,v4506_pb,v4506_pg]
  minus := ![(Primitive.Addresses.material4506 1).one,v4506_mb,v4506_mg]
  upper := v4506_upper
  lower := (Primitive.Addresses.material4506 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4506_pa_checked.trans (by decide +kernel)
    · exact v4506_pb_checked.trans (by decide +kernel)
    · exact v4506_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 82 Primitive.Addresses.material4506
    · exact v4506_mb_checked.trans (by decide +kernel)
    · exact v4506_mg_checked.trans (by decide +kernel)
  upper_error := v4506_upper_checked
  lower_error := reuse_lower_error 75 82 Primitive.Addresses.material4506

def v4507_pa : Scalar.QComplex := ((999997708560455138327035769381 : Int)/10^30,(-2140764779004960687834230317 : Int)/10^30)
theorem v4507_pa_checked : Scalar.distance (sourceCoefficient 75 83 1 0) v4507_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4507_pb : Scalar.QComplex := ((-923691878452873294154024 : Int)/10^30,(-431476531624418751377968688 : Int)/10^30)
theorem v4507_pb_checked : Scalar.distance (sourceCoefficient 75 83 1 1) v4507_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4507_pg : Scalar.QComplex := ((-93086216522606618268282 : Int)/10^30,(199276150371677186785 : Int)/10^30)
theorem v4507_pg_checked : Scalar.distance (sourceCoefficient 75 83 1 2) v4507_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4507_mb : Scalar.QComplex := ((-1296036348330447346446692 : Int)/10^30,(-431475573861497009005141910 : Int)/10^30)
theorem v4507_mb_checked : Scalar.distance (sourceCoefficient 75 83 3 1) v4507_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4507_mg : Scalar.QComplex := ((-93086009896011250527795 : Int)/10^30,(279605288583507335758 : Int)/10^30)
theorem v4507_mg_checked : Scalar.distance (sourceCoefficient 75 83 3 2) v4507_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4507_upper : Scalar.QComplex := ((999992524415536321166688713766 : Int)/10^30,(-3866666916479177810048660808 : Int)/10^30)
theorem v4507_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 83 5) 1) 14) v4507_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4507 : Material (75 : Basis) (83 : Basis) where
  plus := ![v4507_pa,v4507_pb,v4507_pg]
  minus := ![(Primitive.Addresses.material4507 1).one,v4507_mb,v4507_mg]
  upper := v4507_upper
  lower := (Primitive.Addresses.material4507 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4507_pa_checked.trans (by decide +kernel)
    · exact v4507_pb_checked.trans (by decide +kernel)
    · exact v4507_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 83 Primitive.Addresses.material4507
    · exact v4507_mb_checked.trans (by decide +kernel)
    · exact v4507_mg_checked.trans (by decide +kernel)
  upper_error := v4507_upper_checked
  lower_error := reuse_lower_error 75 83 Primitive.Addresses.material4507

def v4508_pa : Scalar.QComplex := ((999997632718623906287412275511 : Int)/10^30,(-2175903754343539795002682636 : Int)/10^30)
theorem v4508_pa_checked : Scalar.distance (sourceCoefficient 75 84 1 0) v4508_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4508_pb : Scalar.QComplex := ((-938853555142954622921420 : Int)/10^30,(-431476498323183326724986266 : Int)/10^30)
theorem v4508_pb_checked : Scalar.distance (sourceCoefficient 75 84 1 1) v4508_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4508_pg : Scalar.QComplex := ((-93086209400500171686486 : Int)/10^30,(202547111998163245165 : Int)/10^30)
theorem v4508_pg_checked : Scalar.distance (sourceCoefficient 75 84 1 2) v4508_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4508_mb : Scalar.QComplex := ((-1311197990637677181132612 : Int)/10^30,(-431475527476429856953156884 : Int)/10^30)
theorem v4508_mb_checked : Scalar.distance (sourceCoefficient 75 84 3 1) v4508_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4508_mg : Scalar.QComplex := ((-93085999951214890817190 : Int)/10^30,(282876242846007794632 : Int)/10^30)
theorem v4508_mg_checked : Scalar.distance (sourceCoefficient 75 84 3 2) v4508_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4508_upper : Scalar.QComplex := ((999992387927134395179261169981 : Int)/10^30,(-3901805708586260475085788468 : Int)/10^30)
theorem v4508_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 84 5) 1) 14) v4508_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4508 : Material (75 : Basis) (84 : Basis) where
  plus := ![v4508_pa,v4508_pb,v4508_pg]
  minus := ![(Primitive.Addresses.material4508 1).one,v4508_mb,v4508_mg]
  upper := v4508_upper
  lower := (Primitive.Addresses.material4508 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4508_pa_checked.trans (by decide +kernel)
    · exact v4508_pb_checked.trans (by decide +kernel)
    · exact v4508_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 84 Primitive.Addresses.material4508
    · exact v4508_mb_checked.trans (by decide +kernel)
    · exact v4508_mg_checked.trans (by decide +kernel)
  upper_error := v4508_upper_checked
  lower_error := reuse_lower_error 75 84 Primitive.Addresses.material4508

def v4509_pa : Scalar.QComplex := ((999997457573615405915714930756 : Int)/10^30,(-2254960377757500086312626250 : Int)/10^30)
theorem v4509_pa_checked : Scalar.distance (sourceCoefficient 75 85 1 0) v4509_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4509_pb : Scalar.QComplex := ((-972964706541337650335534 : Int)/10^30,(-431476420804245925247662724 : Int)/10^30)
theorem v4509_pb_checked : Scalar.distance (sourceCoefficient 75 85 1 1) v4509_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4509_pg : Scalar.QComplex := ((-93086192886768271299082 : Int)/10^30,(209906210347041974982 : Int)/10^30)
theorem v4509_pg_checked : Scalar.distance (sourceCoefficient 75 85 1 2) v4509_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4509_mb : Scalar.QComplex := ((-1345309062439567932157416 : Int)/10^30,(-431475420521133971742969578 : Int)/10^30)
theorem v4509_mb_checked : Scalar.distance (sourceCoefficient 75 85 3 1) v4509_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4509_mg : Scalar.QComplex := ((-93085977086918705650491 : Int)/10^30,(290235324204151002593 : Int)/10^30)
theorem v4509_mg_checked : Scalar.distance (sourceCoefficient 75 85 3 2) v4509_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4509_upper : Scalar.QComplex := ((999992076337826701080115212009 : Int)/10^30,(-3980861911970271194050501131 : Int)/10^30)
theorem v4509_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 85 5) 1) 14) v4509_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4509 : Material (75 : Basis) (85 : Basis) where
  plus := ![v4509_pa,v4509_pb,v4509_pg]
  minus := ![(Primitive.Addresses.material4509 1).one,v4509_mb,v4509_mg]
  upper := v4509_upper
  lower := (Primitive.Addresses.material4509 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4509_pa_checked.trans (by decide +kernel)
    · exact v4509_pb_checked.trans (by decide +kernel)
    · exact v4509_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 85 Primitive.Addresses.material4509
    · exact v4509_mb_checked.trans (by decide +kernel)
    · exact v4509_mg_checked.trans (by decide +kernel)
  upper_error := v4509_upper_checked
  lower_error := reuse_lower_error 75 85 Primitive.Addresses.material4509

def v4510_pa : Scalar.QComplex := ((999997424579465185163063108836 : Int)/10^30,(-2269544984537372576606492932 : Int)/10^30)
theorem v4510_pa_checked : Scalar.distance (sourceCoefficient 75 86 1 0) v4510_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4510_pb : Scalar.QComplex := ((-979257635434432598440191 : Int)/10^30,(-431476406110461936666634582 : Int)/10^30)
theorem v4510_pb_checked : Scalar.distance (sourceCoefficient 75 86 1 1) v4510_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4510_pg : Scalar.QComplex := ((-93086189766104999763517 : Int)/10^30,(211263839206587457537 : Int)/10^30)
theorem v4510_pg_checked : Scalar.distance (sourceCoefficient 75 86 1 2) v4510_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4510_mb : Scalar.QComplex := ((-1351601976309444053623491 : Int)/10^30,(-431475400396841242584508100 : Int)/10^30)
theorem v4510_mb_checked : Scalar.distance (sourceCoefficient 75 86 3 1) v4510_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4510_mg : Scalar.QComplex := ((-93085972794684035626744 : Int)/10^30,(291592949865197360156 : Int)/10^30)
theorem v4510_mg_checked : Scalar.distance (sourceCoefficient 75 86 3 2) v4510_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4510_upper : Scalar.QComplex := ((999992018172017424370073284671 : Int)/10^30,(-3995446440083175038891686757 : Int)/10^30)
theorem v4510_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 86 5) 1) 14) v4510_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4510 : Material (75 : Basis) (86 : Basis) where
  plus := ![v4510_pa,v4510_pb,v4510_pg]
  minus := ![(Primitive.Addresses.material4510 1).one,v4510_mb,v4510_mg]
  upper := v4510_upper
  lower := (Primitive.Addresses.material4510 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4510_pa_checked.trans (by decide +kernel)
    · exact v4510_pb_checked.trans (by decide +kernel)
    · exact v4510_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 86 Primitive.Addresses.material4510
    · exact v4510_mb_checked.trans (by decide +kernel)
    · exact v4510_mg_checked.trans (by decide +kernel)
  upper_error := v4510_upper_checked
  lower_error := reuse_lower_error 75 86 Primitive.Addresses.material4510

def v4511_pa : Scalar.QComplex := ((999997422387171157983173325329 : Int)/10^30,(-2270510738489500789616040496 : Int)/10^30)
theorem v4511_pa_checked : Scalar.distance (sourceCoefficient 75 87 1 0) v4511_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4511_pb : Scalar.QComplex := ((-979674336480820831846849 : Int)/10^30,(-431476405133158630575500345 : Int)/10^30)
theorem v4511_pb_checked : Scalar.distance (sourceCoefficient 75 87 1 1) v4511_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4511_pg : Scalar.QComplex := ((-93086189558647480800823 : Int)/10^30,(211353737786084290329 : Int)/10^30)
theorem v4511_pg_checked : Scalar.distance (sourceCoefficient 75 87 1 2) v4511_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4511_mb : Scalar.QComplex := ((-1352018676357306706231490 : Int)/10^30,(-431475399059944064873460552 : Int)/10^30)
theorem v4511_mb_checked : Scalar.distance (sourceCoefficient 75 87 3 1) v4511_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4511_mg : Scalar.QComplex := ((-93085972509648168685917 : Int)/10^30,(291682848232194347909 : Int)/10^30)
theorem v4511_mg_checked : Scalar.distance (sourceCoefficient 75 87 3 2) v4511_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4511_upper : Scalar.QComplex := ((999992014312922953495462053835 : Int)/10^30,(-3996412188813225578082649155 : Int)/10^30)
theorem v4511_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 87 5) 1) 14) v4511_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4511 : Material (75 : Basis) (87 : Basis) where
  plus := ![v4511_pa,v4511_pb,v4511_pg]
  minus := ![(Primitive.Addresses.material4511 1).one,v4511_mb,v4511_mg]
  upper := v4511_upper
  lower := (Primitive.Addresses.material4511 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4511_pa_checked.trans (by decide +kernel)
    · exact v4511_pb_checked.trans (by decide +kernel)
    · exact v4511_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 87 Primitive.Addresses.material4511
    · exact v4511_mb_checked.trans (by decide +kernel)
    · exact v4511_mg_checked.trans (by decide +kernel)
  upper_error := v4511_upper_checked
  lower_error := reuse_lower_error 75 87 Primitive.Addresses.material4511

def v4512_pa : Scalar.QComplex := ((999997395617743868626115671937 : Int)/10^30,(-2282270301576001255028202472 : Int)/10^30)
theorem v4512_pa_checked : Scalar.distance (sourceCoefficient 75 88 1 0) v4512_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4512_pb : Scalar.QComplex := ((-984748322669538786297260 : Int)/10^30,(-431476393189918448062583827 : Int)/10^30)
theorem v4512_pb_checked : Scalar.distance (sourceCoefficient 75 88 1 1) v4512_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4512_pg : Scalar.QComplex := ((-93086187024402296113958 : Int)/10^30,(212448393429568874835 : Int)/10^30)
theorem v4512_pg_checked : Scalar.distance (sourceCoefficient 75 88 1 2) v4512_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4512_mb : Scalar.QComplex := ((-1357092650350269336058909 : Int)/10^30,(-431475382738086772365837946 : Int)/10^30)
theorem v4512_mb_checked : Scalar.distance (sourceCoefficient 75 88 3 1) v4512_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4512_mg : Scalar.QComplex := ((-93085969030765408747185 : Int)/10^30,(292777501281149151893 : Int)/10^30)
theorem v4512_mg_checked : Scalar.distance (sourceCoefficient 75 88 3 2) v4512_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4512_upper : Scalar.QComplex := ((999991967247596465985663604825 : Int)/10^30,(-4008171688183635203511812617 : Int)/10^30)
theorem v4512_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 88 5) 1) 14) v4512_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4512 : Material (75 : Basis) (88 : Basis) where
  plus := ![v4512_pa,v4512_pb,v4512_pg]
  minus := ![(Primitive.Addresses.material4512 1).one,v4512_mb,v4512_mg]
  upper := v4512_upper
  lower := (Primitive.Addresses.material4512 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4512_pa_checked.trans (by decide +kernel)
    · exact v4512_pb_checked.trans (by decide +kernel)
    · exact v4512_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 88 Primitive.Addresses.material4512
    · exact v4512_mb_checked.trans (by decide +kernel)
    · exact v4512_mg_checked.trans (by decide +kernel)
  upper_error := v4512_upper_checked
  lower_error := reuse_lower_error 75 88 Primitive.Addresses.material4512

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
