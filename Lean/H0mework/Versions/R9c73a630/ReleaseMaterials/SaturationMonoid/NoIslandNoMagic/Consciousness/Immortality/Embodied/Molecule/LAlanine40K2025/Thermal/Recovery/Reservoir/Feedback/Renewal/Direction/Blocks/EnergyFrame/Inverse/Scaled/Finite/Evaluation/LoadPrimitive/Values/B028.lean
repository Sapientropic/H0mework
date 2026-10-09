import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B018
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B019

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v449_pa : Scalar.QComplex := ((999995237129665869081954611262 : Int)/10^30,(3086376189534907675366407552 : Int)/10^30)
theorem v449_pa_checked : Scalar.distance (sourceCoefficient 4 72 1 0) v449_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v449_pb : Scalar.QComplex := ((1331696262811763742484889 : Int)/10^30,(-431473624190904153591818180 : Int)/10^30)
theorem v449_pb_checked : Scalar.distance (sourceCoefficient 4 72 1 1) v449_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v449_pg : Scalar.QComplex := ((-93085787871123275872108 : Int)/10^30,(-287299127638024230573 : Int)/10^30)
theorem v449_pg_checked : Scalar.distance (sourceCoefficient 4 72 1 2) v449_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v449_mb : Scalar.QComplex := ((959353462134285520571953 : Int)/10^30,(-431474612727451981878382614 : Int)/10^30)
theorem v449_mb_checked : Scalar.distance (sourceCoefficient 4 72 3 1) v449_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v449_mg : Scalar.QComplex := ((-93086001137237900025830 : Int)/10^30,(-206970178158904868166 : Int)/10^30)
theorem v449_mg_checked : Scalar.distance (sourceCoefficient 4 72 3 2) v449_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v449_upper : Scalar.QComplex := ((999999074559537133181264524052 : Int)/10^30,(1360470532313576852872936555 : Int)/10^30)
theorem v449_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 72 5) 1) 14) v449_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material449 : Material (4 : Basis) (72 : Basis) where
  plus := ![v449_pa,v449_pb,v449_pg]
  minus := ![(Primitive.Addresses.material449 1).one,v449_mb,v449_mg]
  upper := v449_upper
  lower := (Primitive.Addresses.material449 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v449_pa_checked.trans (by decide +kernel)
    · exact v449_pb_checked.trans (by decide +kernel)
    · exact v449_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 72 Primitive.Addresses.material449
    · exact v449_mb_checked.trans (by decide +kernel)
    · exact v449_mg_checked.trans (by decide +kernel)
  upper_error := v449_upper_checked
  lower_error := reuse_lower_error 4 72 Primitive.Addresses.material449

def v450_pa : Scalar.QComplex := ((999995266250170221929883391201 : Int)/10^30,(3076926591774442920030982158 : Int)/10^30)
theorem v450_pa_checked : Scalar.distance (sourceCoefficient 4 73 1 0) v450_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v450_pb : Scalar.QComplex := ((1327618970016493862215819 : Int)/10^30,(-431473629871291537311601155 : Int)/10^30)
theorem v450_pb_checked : Scalar.distance (sourceCoefficient 4 73 1 1) v450_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v450_pg : Scalar.QComplex := ((-93085789839224436314182 : Int)/10^30,(-286419497910886394587 : Int)/10^30)
theorem v450_pg_checked : Scalar.distance (sourceCoefficient 4 73 1 2) v450_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v450_mb : Scalar.QComplex := ((955276165955259612468602 : Int)/10^30,(-431474614889317202663097148 : Int)/10^30)
theorem v450_mb_checked : Scalar.distance (sourceCoefficient 4 73 3 1) v450_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v450_mg : Scalar.QComplex := ((-93086002346257490186200 : Int)/10^30,(-206090547060910719182 : Int)/10^30)
theorem v450_mg_checked : Scalar.distance (sourceCoefficient 4 73 3 2) v450_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v450_upper : Scalar.QComplex := ((999999087370849640708802156068 : Int)/10^30,(1351020898367829212524447472 : Int)/10^30)
theorem v450_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 73 5) 1) 14) v450_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material450 : Material (4 : Basis) (73 : Basis) where
  plus := ![v450_pa,v450_pb,v450_pg]
  minus := ![(Primitive.Addresses.material450 1).one,v450_mb,v450_mg]
  upper := v450_upper
  lower := (Primitive.Addresses.material450 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v450_pa_checked.trans (by decide +kernel)
    · exact v450_pb_checked.trans (by decide +kernel)
    · exact v450_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 73 Primitive.Addresses.material450
    · exact v450_mb_checked.trans (by decide +kernel)
    · exact v450_mg_checked.trans (by decide +kernel)
  upper_error := v450_upper_checked
  lower_error := reuse_lower_error 4 73 Primitive.Addresses.material450

def v451_pa : Scalar.QComplex := ((999995298911124133319106408058 : Int)/10^30,(3066293471195596925088353124 : Int)/10^30)
theorem v451_pa_checked : Scalar.distance (sourceCoefficient 4 74 1 0) v451_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v451_pb : Scalar.QComplex := ((1323031013364668432510135 : Int)/10^30,(-431473636201697460010540920 : Int)/10^30)
theorem v451_pb_checked : Scalar.distance (sourceCoefficient 4 74 1 1) v451_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v451_pg : Scalar.QComplex := ((-93085792042226518859708 : Int)/10^30,(-285429698230529419301 : Int)/10^30)
theorem v451_pg_checked : Scalar.distance (sourceCoefficient 4 74 1 2) v451_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v451_mb : Scalar.QComplex := ((950688205548884923824675 : Int)/10^30,(-431474617260520811634239614 : Int)/10^30)
theorem v451_mb_checked : Scalar.distance (sourceCoefficient 4 74 3 1) v451_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v451_mg : Scalar.QComplex := ((-93086003695106207228054 : Int)/10^30,(-205100745848009823267 : Int)/10^30)
theorem v451_mg_checked : Scalar.distance (sourceCoefficient 4 74 3 2) v451_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v451_upper : Scalar.QComplex := ((999999101679953417519255448096 : Int)/10^30,(1340387737255923793223996482 : Int)/10^30)
theorem v451_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 74 5) 1) 14) v451_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material451 : Material (4 : Basis) (74 : Basis) where
  plus := ![v451_pa,v451_pb,v451_pg]
  minus := ![(Primitive.Addresses.material451 1).one,v451_mb,v451_mg]
  upper := v451_upper
  lower := (Primitive.Addresses.material451 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v451_pa_checked.trans (by decide +kernel)
    · exact v451_pb_checked.trans (by decide +kernel)
    · exact v451_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 74 Primitive.Addresses.material451
    · exact v451_mb_checked.trans (by decide +kernel)
    · exact v451_mg_checked.trans (by decide +kernel)
  upper_error := v451_upper_checked
  lower_error := reuse_lower_error 4 74 Primitive.Addresses.material451

def v452_pa : Scalar.QComplex := ((999995344228913772368342847697 : Int)/10^30,(3051478411565589949337436626 : Int)/10^30)
theorem v452_pa_checked : Scalar.distance (sourceCoefficient 4 75 1 0) v452_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v452_pb : Scalar.QComplex := ((1316638642580762789543125 : Int)/10^30,(-431473644913361471284446809 : Int)/10^30)
theorem v452_pb_checked : Scalar.distance (sourceCoefficient 4 75 1 1) v452_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v452_pg : Scalar.QComplex := ((-93085795091182986205377 : Int)/10^30,(-284050616618810927976 : Int)/10^30)
theorem v452_pg_checked : Scalar.distance (sourceCoefficient 4 75 1 2) v452_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v452_mb : Scalar.QComplex := ((944295829627377386535498 : Int)/10^30,(-431474620455853494339615422 : Int)/10^30)
theorem v452_mb_checked : Scalar.distance (sourceCoefficient 4 75 3 1) v452_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v452_mg : Scalar.QComplex := ((-93086005553976219924932 : Int)/10^30,(-203721662118674331710 : Int)/10^30)
theorem v452_mg_checked : Scalar.distance (sourceCoefficient 4 75 3 2) v452_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v452_upper : Scalar.QComplex := ((999999121428226651362976805152 : Int)/10^30,(1325572621476814117977139831 : Int)/10^30)
theorem v452_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 75 5) 1) 14) v452_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material452 : Material (4 : Basis) (75 : Basis) where
  plus := ![v452_pa,v452_pb,v452_pg]
  minus := ![(Primitive.Addresses.material452 1).one,v452_mb,v452_mg]
  upper := v452_upper
  lower := (Primitive.Addresses.material452 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v452_pa_checked.trans (by decide +kernel)
    · exact v452_pb_checked.trans (by decide +kernel)
    · exact v452_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 75 Primitive.Addresses.material452
    · exact v452_mb_checked.trans (by decide +kernel)
    · exact v452_mg_checked.trans (by decide +kernel)
  upper_error := v452_upper_checked
  lower_error := reuse_lower_error 4 75 Primitive.Addresses.material452

def v453_pa : Scalar.QComplex := ((999995382082100464314472895940 : Int)/10^30,(3039048284234004104765910556 : Int)/10^30)
theorem v453_pa_checked : Scalar.distance (sourceCoefficient 4 76 1 0) v453_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v453_pb : Scalar.QComplex := ((1311275317545034818546462 : Int)/10^30,(-431473652125202003633118086 : Int)/10^30)
theorem v453_pb_checked : Scalar.distance (sourceCoefficient 4 76 1 1) v453_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v453_pg : Scalar.QComplex := ((-93085797630927951320028 : Int)/10^30,(-282893539955967140202 : Int)/10^30)
theorem v453_pg_checked : Scalar.distance (sourceCoefficient 4 76 1 2) v453_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v453_mb : Scalar.QComplex := ((938932500365166872226659 : Int)/10^30,(-431474623039383390749879083 : Int)/10^30)
theorem v453_mb_checked : Scalar.distance (sourceCoefficient 4 76 3 1) v453_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v453_mg : Scalar.QComplex := ((-93086007095215192140647 : Int)/10^30,(-202564583694977547502 : Int)/10^30)
theorem v453_mg_checked : Scalar.distance (sourceCoefficient 4 76 3 2) v453_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v453_upper : Scalar.QComplex := ((999999137828084843459693906236 : Int)/10^30,(1313142447327276572449371841 : Int)/10^30)
theorem v453_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 76 5) 1) 14) v453_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material453 : Material (4 : Basis) (76 : Basis) where
  plus := ![v453_pa,v453_pb,v453_pg]
  minus := ![(Primitive.Addresses.material453 1).one,v453_mb,v453_mg]
  upper := v453_upper
  lower := (Primitive.Addresses.material453 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v453_pa_checked.trans (by decide +kernel)
    · exact v453_pb_checked.trans (by decide +kernel)
    · exact v453_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 76 Primitive.Addresses.material453
    · exact v453_mb_checked.trans (by decide +kernel)
    · exact v453_mg_checked.trans (by decide +kernel)
  upper_error := v453_upper_checked
  lower_error := reuse_lower_error 4 76 Primitive.Addresses.material453

def v454_pa : Scalar.QComplex := ((999995390823409210671165648974 : Int)/10^30,(3036170604078402671399395895 : Int)/10^30)
theorem v454_pa_checked : Scalar.distance (sourceCoefficient 4 77 1 0) v454_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v454_pb : Scalar.QComplex := ((1310033662224103191021793 : Int)/10^30,(-431473653782132933981765896 : Int)/10^30)
theorem v454_pb_checked : Scalar.distance (sourceCoefficient 4 77 1 1) v454_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v454_pg : Scalar.QComplex := ((-93085798216508487736547 : Int)/10^30,(-282625666873744583918 : Int)/10^30)
theorem v454_pg_checked : Scalar.distance (sourceCoefficient 4 77 1 2) v454_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v454_mb : Scalar.QComplex := ((937690844076703499644328 : Int)/10^30,(-431474623624821084263151066 : Int)/10^30)
theorem v454_mb_checked : Scalar.distance (sourceCoefficient 4 77 3 1) v454_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v454_mg : Scalar.QComplex := ((-93086007449633105116471 : Int)/10^30,(-202296710207166752775 : Int)/10^30)
theorem v454_mg_checked : Scalar.distance (sourceCoefficient 4 77 3 2) v454_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v454_upper : Scalar.QComplex := ((999999141602765683200179954008 : Int)/10^30,(1310264756370935803917577434 : Int)/10^30)
theorem v454_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 77 5) 1) 14) v454_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material454 : Material (4 : Basis) (77 : Basis) where
  plus := ![v454_pa,v454_pb,v454_pg]
  minus := ![(Primitive.Addresses.material454 1).one,v454_mb,v454_mg]
  upper := v454_upper
  lower := (Primitive.Addresses.material454 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v454_pa_checked.trans (by decide +kernel)
    · exact v454_pb_checked.trans (by decide +kernel)
    · exact v454_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 77 Primitive.Addresses.material454
    · exact v454_mb_checked.trans (by decide +kernel)
    · exact v454_mg_checked.trans (by decide +kernel)
  upper_error := v454_upper_checked
  lower_error := reuse_lower_error 4 77 Primitive.Addresses.material454

def v455_pa : Scalar.QComplex := ((999995443198276355859705110855 : Int)/10^30,(3018871094108910769470318967 : Int)/10^30)
theorem v455_pa_checked : Scalar.distance (sourceCoefficient 4 78 1 0) v455_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v455_pb : Scalar.QComplex := ((1302569306589853986083568 : Int)/10^30,(-431473663642559102515559213 : Int)/10^30)
theorem v455_pb_checked : Scalar.distance (sourceCoefficient 4 78 1 1) v455_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v455_pg : Scalar.QComplex := ((-93085801717840108804125 : Int)/10^30,(-281015316609020189261 : Int)/10^30)
theorem v455_pg_checked : Scalar.distance (sourceCoefficient 4 78 1 2) v455_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v455_mb : Scalar.QComplex := ((930226482712671348906430 : Int)/10^30,(-431474627043840851050674729 : Int)/10^30)
theorem v455_mb_checked : Scalar.distance (sourceCoefficient 4 78 3 1) v455_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v455_mg : Scalar.QComplex := ((-93086009561303671504691 : Int)/10^30,(-200686357520557863459 : Int)/10^30)
theorem v455_mg_checked : Scalar.distance (sourceCoefficient 4 78 3 2) v455_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v455_upper : Scalar.QComplex := ((999999164120170014118425875742 : Int)/10^30,(1292965181772762576591406377 : Int)/10^30)
theorem v455_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 78 5) 1) 14) v455_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material455 : Material (4 : Basis) (78 : Basis) where
  plus := ![v455_pa,v455_pb,v455_pg]
  minus := ![(Primitive.Addresses.material455 1).one,v455_mb,v455_mg]
  upper := v455_upper
  lower := (Primitive.Addresses.material455 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v455_pa_checked.trans (by decide +kernel)
    · exact v455_pb_checked.trans (by decide +kernel)
    · exact v455_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 78 Primitive.Addresses.material455
    · exact v455_mb_checked.trans (by decide +kernel)
    · exact v455_mg_checked.trans (by decide +kernel)
  upper_error := v455_upper_checked
  lower_error := reuse_lower_error 4 78 Primitive.Addresses.material455

def v456_pa : Scalar.QComplex := ((999995460019213341460646722206 : Int)/10^30,(3013294038405733725760809623 : Int)/10^30)
theorem v456_pa_checked : Scalar.distance (sourceCoefficient 4 79 1 0) v456_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v456_pb : Scalar.QComplex := ((1300162930566080127359118 : Int)/10^30,(-431473666784685820727911349 : Int)/10^30)
theorem v456_pb_checked : Scalar.distance (sourceCoefficient 4 79 1 1) v456_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v456_pg : Scalar.QComplex := ((-93085802839679486620720 : Int)/10^30,(-280496168204232095022 : Int)/10^30)
theorem v456_pg_checked : Scalar.distance (sourceCoefficient 4 79 1 2) v456_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v456_mb : Scalar.QComplex := ((927820104873387418967041 : Int)/10^30,(-431474628109372269941694817 : Int)/10^30)
theorem v456_mb_checked : Scalar.distance (sourceCoefficient 4 79 3 1) v456_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v456_mg : Scalar.QComplex := ((-93086010235140939853276 : Int)/10^30,(-200167208340975589291 : Int)/10^30)
theorem v456_mg_checked : Scalar.distance (sourceCoefficient 4 79 3 2) v456_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v456_upper : Scalar.QComplex := ((999999171315589749767230785781 : Int)/10^30,(1287388105344543622116827607 : Int)/10^30)
theorem v456_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 79 5) 1) 14) v456_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material456 : Material (4 : Basis) (79 : Basis) where
  plus := ![v456_pa,v456_pb,v456_pg]
  minus := ![(Primitive.Addresses.material456 1).one,v456_mb,v456_mg]
  upper := v456_upper
  lower := (Primitive.Addresses.material456 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v456_pa_checked.trans (by decide +kernel)
    · exact v456_pb_checked.trans (by decide +kernel)
    · exact v456_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 79 Primitive.Addresses.material456
    · exact v456_mb_checked.trans (by decide +kernel)
    · exact v456_mg_checked.trans (by decide +kernel)
  upper_error := v456_upper_checked
  lower_error := reuse_lower_error 4 79 Primitive.Addresses.material456

def v457_pa : Scalar.QComplex := ((999995486232937119661973943379 : Int)/10^30,(3004582125964870028771280673 : Int)/10^30)
theorem v457_pa_checked : Scalar.distance (sourceCoefficient 4 80 1 0) v457_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v457_pb : Scalar.QComplex := ((1296403933351002693176533 : Int)/10^30,(-431473671657189976432309629 : Int)/10^30)
theorem v457_pb_checked : Scalar.distance (sourceCoefficient 4 80 1 1) v457_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v457_pg : Scalar.QComplex := ((-93085804585343890346780 : Int)/10^30,(-279685207072058649588 : Int)/10^30)
theorem v457_pg_checked : Scalar.distance (sourceCoefficient 4 80 1 2) v457_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v457_mb : Scalar.QComplex := ((924061104853204805685273 : Int)/10^30,(-431474629738029313728180441 : Int)/10^30)
theorem v457_mb_checked : Scalar.distance (sourceCoefficient 4 80 3 1) v457_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v457_mg : Scalar.QComplex := ((-93086011280981760856561 : Int)/10^30,(-199356246004330277510 : Int)/10^30)
theorem v457_mg_checked : Scalar.distance (sourceCoefficient 4 80 3 2) v457_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v457_upper : Scalar.QComplex := ((999999182493303951298379096301 : Int)/10^30,(1278676160636540981939474982 : Int)/10^30)
theorem v457_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 80 5) 1) 14) v457_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material457 : Material (4 : Basis) (80 : Basis) where
  plus := ![v457_pa,v457_pb,v457_pg]
  minus := ![(Primitive.Addresses.material457 1).one,v457_mb,v457_mg]
  upper := v457_upper
  lower := (Primitive.Addresses.material457 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v457_pa_checked.trans (by decide +kernel)
    · exact v457_pb_checked.trans (by decide +kernel)
    · exact v457_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 80 Primitive.Addresses.material457
    · exact v457_mb_checked.trans (by decide +kernel)
    · exact v457_mg_checked.trans (by decide +kernel)
  upper_error := v457_upper_checked
  lower_error := reuse_lower_error 4 80 Primitive.Addresses.material457

def v458_pa : Scalar.QComplex := ((999995564705493363701151726912 : Int)/10^30,(2978350103905724025386049885 : Int)/10^30)
theorem v458_pa_checked : Scalar.distance (sourceCoefficient 4 81 1 0) v458_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v458_pb : Scalar.QComplex := ((1285085397456110769766697 : Int)/10^30,(-431473686064875224765686259 : Int)/10^30)
theorem v458_pb_checked : Scalar.distance (sourceCoefficient 4 81 1 1) v458_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v458_pg : Scalar.QComplex := ((-93085809791855254554286 : Int)/10^30,(-277243360921676257609 : Int)/10^30)
theorem v458_pg_checked : Scalar.distance (sourceCoefficient 4 81 1 2) v458_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v458_mb : Scalar.QComplex := ((912742560739537607332031 : Int)/10^30,(-431474634378322488063376215 : Int)/10^30)
theorem v458_mb_checked : Scalar.distance (sourceCoefficient 4 81 3 1) v458_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v458_mg : Scalar.QComplex := ((-93086014380287935330020 : Int)/10^30,(-196914396270173990457 : Int)/10^30)
theorem v458_mg_checked : Scalar.distance (sourceCoefficient 4 81 3 2) v458_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v458_upper : Scalar.QComplex := ((999999215691652996048678892785 : Int)/10^30,(1252444042210397303362973493 : Int)/10^30)
theorem v458_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 81 5) 1) 14) v458_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material458 : Material (4 : Basis) (81 : Basis) where
  plus := ![v458_pa,v458_pb,v458_pg]
  minus := ![(Primitive.Addresses.material458 1).one,v458_mb,v458_mg]
  upper := v458_upper
  lower := (Primitive.Addresses.material458 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v458_pa_checked.trans (by decide +kernel)
    · exact v458_pb_checked.trans (by decide +kernel)
    · exact v458_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 81 Primitive.Addresses.material458
    · exact v458_mb_checked.trans (by decide +kernel)
    · exact v458_mg_checked.trans (by decide +kernel)
  upper_error := v458_upper_checked
  lower_error := reuse_lower_error 4 81 Primitive.Addresses.material458

def v459_pa : Scalar.QComplex := ((999995594261660348787685998329 : Int)/10^30,(2968409888942581183467248236 : Int)/10^30)
theorem v459_pa_checked : Scalar.distance (sourceCoefficient 4 82 1 0) v459_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v459_pb : Scalar.QComplex := ((1280796415286568315197637 : Int)/10^30,(-431473691421013490652049832 : Int)/10^30)
theorem v459_pb_checked : Scalar.distance (sourceCoefficient 4 82 1 1) v459_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v459_pg : Scalar.QComplex := ((-93085811745256925290390 : Int)/10^30,(-276318061489945573086 : Int)/10^30)
theorem v459_pg_checked : Scalar.distance (sourceCoefficient 4 82 1 2) v459_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v459_mb : Scalar.QComplex := ((908453575544873138704799 : Int)/10^30,(-431474636033260315885698703 : Int)/10^30)
theorem v459_mb_checked : Scalar.distance (sourceCoefficient 4 82 3 1) v459_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v459_mg : Scalar.QComplex := ((-93086015535197143081221 : Int)/10^30,(-195989095497276908740 : Int)/10^30)
theorem v459_mg_checked : Scalar.distance (sourceCoefficient 4 82 3 2) v459_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v459_upper : Scalar.QComplex := ((999999228091866703569076445972 : Int)/10^30,(1242503791040774087636495056 : Int)/10^30)
theorem v459_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 82 5) 1) 14) v459_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material459 : Material (4 : Basis) (82 : Basis) where
  plus := ![v459_pa,v459_pb,v459_pg]
  minus := ![(Primitive.Addresses.material459 1).one,v459_mb,v459_mg]
  upper := v459_upper
  lower := (Primitive.Addresses.material459 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v459_pa_checked.trans (by decide +kernel)
    · exact v459_pb_checked.trans (by decide +kernel)
    · exact v459_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 82 Primitive.Addresses.material459
    · exact v459_mb_checked.trans (by decide +kernel)
    · exact v459_mg_checked.trans (by decide +kernel)
  upper_error := v459_upper_checked
  lower_error := reuse_lower_error 4 82 Primitive.Addresses.material459

def v460_pa : Scalar.QComplex := ((999995634446835235336259946115 : Int)/10^30,(2954841327630790582539215641 : Int)/10^30)
theorem v460_pa_checked : Scalar.distance (sourceCoefficient 4 83 1 0) v460_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v460_pb : Scalar.QComplex := ((1274941882355162940889674 : Int)/10^30,(-431473698640476605387183635 : Int)/10^30)
theorem v460_pb_checked : Scalar.distance (sourceCoefficient 4 83 1 1) v460_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v460_pg : Scalar.QComplex := ((-93085814394362237718703 : Int)/10^30,(-275055012155909472521 : Int)/10^30)
theorem v460_pg_checked : Scalar.distance (sourceCoefficient 4 83 1 2) v460_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v460_mb : Scalar.QComplex := ((902599038563306424664056 : Int)/10^30,(-431474638200522501056960217 : Int)/10^30)
theorem v460_mb_checked : Scalar.distance (sourceCoefficient 4 83 3 1) v460_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v460_mg : Scalar.QComplex := ((-93086017094346779483714 : Int)/10^30,(-194726044347473226092 : Int)/10^30)
theorem v460_mg_checked : Scalar.distance (sourceCoefficient 4 83 3 2) v460_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v460_upper : Scalar.QComplex := ((999999244858875845136267998793 : Int)/10^30,(1228935180581795401850489642 : Int)/10^30)
theorem v460_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 83 5) 1) 14) v460_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material460 : Material (4 : Basis) (83 : Basis) where
  plus := ![v460_pa,v460_pb,v460_pg]
  minus := ![(Primitive.Addresses.material460 1).one,v460_mb,v460_mg]
  upper := v460_upper
  lower := (Primitive.Addresses.material460 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v460_pa_checked.trans (by decide +kernel)
    · exact v460_pb_checked.trans (by decide +kernel)
    · exact v460_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 83 Primitive.Addresses.material460
    · exact v460_mb_checked.trans (by decide +kernel)
    · exact v460_mg_checked.trans (by decide +kernel)
  upper_error := v460_upper_checked
  lower_error := reuse_lower_error 4 83 Primitive.Addresses.material460

def v461_pa : Scalar.QComplex := ((999995737659799627878966642471 : Int)/10^30,(2919702422028700232119298368 : Int)/10^30)
theorem v461_pa_checked : Scalar.distance (sourceCoefficient 4 84 1 0) v461_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v461_pb : Scalar.QComplex := ((1259780225724821795362551 : Int)/10^30,(-431473716844606110602780736 : Int)/10^30)
theorem v461_pb_checked : Scalar.distance (sourceCoefficient 4 84 1 1) v461_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v461_pg : Scalar.QComplex := ((-93085821161891140804559 : Int)/10^30,(-271784055939011451616 : Int)/10^30)
theorem v461_pg_checked : Scalar.distance (sourceCoefficient 4 84 1 2) v461_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v461_mb : Scalar.QComplex := ((887437371868999085108333 : Int)/10^30,(-431474643320818411724600837 : Int)/10^30)
theorem v461_mb_checked : Scalar.distance (sourceCoefficient 4 84 3 1) v461_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v461_mg : Scalar.QComplex := ((-93086021039185265925568 : Int)/10^30,(-191455083508429049645 : Int)/10^30)
theorem v461_mg_checked : Scalar.distance (sourceCoefficient 4 84 3 2) v461_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v461_upper : Scalar.QComplex := ((999999287425123221499490936845 : Int)/10^30,(1193796149178764105394667713 : Int)/10^30)
theorem v461_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 84 5) 1) 14) v461_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material461 : Material (4 : Basis) (84 : Basis) where
  plus := ![v461_pa,v461_pb,v461_pg]
  minus := ![(Primitive.Addresses.material461 1).one,v461_mb,v461_mg]
  upper := v461_upper
  lower := (Primitive.Addresses.material461 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v461_pa_checked.trans (by decide +kernel)
    · exact v461_pb_checked.trans (by decide +kernel)
    · exact v461_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 84 Primitive.Addresses.material461
    · exact v461_mb_checked.trans (by decide +kernel)
    · exact v461_mg_checked.trans (by decide +kernel)
  upper_error := v461_upper_checked
  lower_error := reuse_lower_error 4 84 Primitive.Addresses.material461

def v462_pa : Scalar.QComplex := ((999995965357203890665670924951 : Int)/10^30,(2840645932508339987819387551 : Int)/10^30)
theorem v462_pa_checked : Scalar.distance (sourceCoefficient 4 85 1 0) v462_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v462_pb : Scalar.QComplex := ((1225669112840984479285532 : Int)/10^30,(-431473755203854310634299239 : Int)/10^30)
theorem v462_pb_checked : Scalar.distance (sourceCoefficient 4 85 1 1) v462_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v462_pg : Scalar.QComplex := ((-93085835897442979799744 : Int)/10^30,(-264424967976502380293 : Int)/10^30)
theorem v462_pg_checked : Scalar.distance (sourceCoefficient 4 85 1 2) v462_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v462_mb : Scalar.QComplex := ((853326238583984490335523 : Int)/10^30,(-431474652243698217597179567 : Int)/10^30)
theorem v462_mb_checked : Scalar.distance (sourceCoefficient 4 85 3 1) v462_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v462_mg : Scalar.QComplex := ((-93086029424170147574189 : Int)/10^30,(-184095985569927181265 : Int)/10^30)
theorem v462_mg_checked : Scalar.distance (sourceCoefficient 4 85 3 2) v462_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v462_upper : Scalar.QComplex := ((999999378677859392313078445520 : Int)/10^30,(1114739384418695163647047097 : Int)/10^30)
theorem v462_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 85 5) 1) 14) v462_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material462 : Material (4 : Basis) (85 : Basis) where
  plus := ![v462_pa,v462_pb,v462_pg]
  minus := ![(Primitive.Addresses.material462 1).one,v462_mb,v462_mg]
  upper := v462_upper
  lower := (Primitive.Addresses.material462 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v462_pa_checked.trans (by decide +kernel)
    · exact v462_pb_checked.trans (by decide +kernel)
    · exact v462_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 85 Primitive.Addresses.material462
    · exact v462_mb_checked.trans (by decide +kernel)
    · exact v462_mg_checked.trans (by decide +kernel)
  upper_error := v462_upper_checked
  lower_error := reuse_lower_error 4 85 Primitive.Addresses.material462

def v463_pa : Scalar.QComplex := ((999996006680658337992886034397 : Int)/10^30,(2826061346949964873682340032 : Int)/10^30)
theorem v463_pa_checked : Scalar.distance (sourceCoefficient 4 86 1 0) v463_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v463_pb : Scalar.QComplex := ((1219376190052257300780548 : Int)/10^30,(-431473761887633095019560957 : Int)/10^30)
theorem v463_pb_checked : Scalar.distance (sourceCoefficient 4 86 1 1) v463_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v463_pg : Scalar.QComplex := ((-93085838541743390860576 : Int)/10^30,(-263067340763146310276 : Int)/10^30)
theorem v463_pg_checked : Scalar.distance (sourceCoefficient 4 86 1 2) v463_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v463_mb : Scalar.QComplex := ((847033312370600002150228 : Int)/10^30,(-431474653496965569355839337 : Int)/10^30)
theorem v463_mb_checked : Scalar.distance (sourceCoefficient 4 86 3 1) v463_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v463_mg : Scalar.QComplex := ((-93086030896898434174710 : Int)/10^30,(-182738356580165609534 : Int)/10^30)
theorem v463_mg_checked : Scalar.distance (sourceCoefficient 4 86 3 2) v463_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v463_upper : Scalar.QComplex := ((999999394829580722719981478613 : Int)/10^30,(1100154749261813471358899312 : Int)/10^30)
theorem v463_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 86 5) 1) 14) v463_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material463 : Material (4 : Basis) (86 : Basis) where
  plus := ![v463_pa,v463_pb,v463_pg]
  minus := ![(Primitive.Addresses.material463 1).one,v463_mb,v463_mg]
  upper := v463_upper
  lower := (Primitive.Addresses.material463 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v463_pa_checked.trans (by decide +kernel)
    · exact v463_pb_checked.trans (by decide +kernel)
    · exact v463_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 86 Primitive.Addresses.material463
    · exact v463_mb_checked.trans (by decide +kernel)
    · exact v463_mg_checked.trans (by decide +kernel)
  upper_error := v463_upper_checked
  lower_error := reuse_lower_error 4 86 Primitive.Addresses.material463

def v464_pa : Scalar.QComplex := ((999996009409478943930460538415 : Int)/10^30,(2825095594364805266167835808 : Int)/10^30)
theorem v464_pa_checked : Scalar.distance (sourceCoefficient 4 87 1 0) v464_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v464_pb : Scalar.QComplex := ((1218959489399077794975149 : Int)/10^30,(-431473762325895279761312370 : Int)/10^30)
theorem v464_pb_checked : Scalar.distance (sourceCoefficient 4 87 1 1) v464_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v464_pg : Scalar.QComplex := ((-93085838716026472812514 : Int)/10^30,(-262977442289687662496 : Int)/10^30)
theorem v464_pg_checked : Scalar.distance (sourceCoefficient 4 87 1 2) v464_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v464_mb : Scalar.QComplex := ((846616611494376666848148 : Int)/10^30,(-431474653575633694719373119 : Int)/10^30)
theorem v464_mb_checked : Scalar.distance (sourceCoefficient 4 87 3 1) v464_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v464_mg : Scalar.QComplex := ((-93086030993603117515222 : Int)/10^30,(-182648457989781821680 : Int)/10^30)
theorem v464_mg_checked : Scalar.distance (sourceCoefficient 4 87 3 2) v464_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v464_upper : Scalar.QComplex := ((999999395891595914804465900451 : Int)/10^30,(1099188993405332084995192688 : Int)/10^30)
theorem v464_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 87 5) 1) 14) v464_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material464 : Material (4 : Basis) (87 : Basis) where
  plus := ![v464_pa,v464_pb,v464_pg]
  minus := ![(Primitive.Addresses.material464 1).one,v464_mb,v464_mg]
  upper := v464_upper
  lower := (Primitive.Addresses.material464 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v464_pa_checked.trans (by decide +kernel)
    · exact v464_pb_checked.trans (by decide +kernel)
    · exact v464_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 87 Primitive.Addresses.material464
    · exact v464_mb_checked.trans (by decide +kernel)
    · exact v464_mg_checked.trans (by decide +kernel)
  upper_error := v464_upper_checked
  lower_error := reuse_lower_error 4 87 Primitive.Addresses.material464

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
