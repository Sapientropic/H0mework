import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B144
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B145

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3473_pa : Scalar.QComplex := ((999998178025468364833382295267 : Int)/10^30,(-1908912188572103834222415781 : Int)/10^30)
theorem v3473_pa_checked : Scalar.distance (sourceCoefficient 46 93 1 0) v3473_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3473_pb : Scalar.QComplex := ((-823652596131558616548070 : Int)/10^30,(-431476681006269569735316845 : Int)/10^30)
theorem v3473_pb_checked : Scalar.distance (sourceCoefficient 46 93 1 1) v3473_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3473_pg : Scalar.QComplex := ((-93086254486746038954946 : Int)/10^30,(177693809531869597624 : Int)/10^30)
theorem v3473_pg_checked : Scalar.distance (sourceCoefficient 46 93 1 2) v3473_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3473_mb : Scalar.QComplex := ((-1195997232168138845563946 : Int)/10^30,(-431475809572687246946966214 : Int)/10^30)
theorem v3473_mb_checked : Scalar.distance (sourceCoefficient 46 93 3 1) v3473_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3473_mg : Scalar.QComplex := ((-93086066484724647636375 : Int)/10^30,(258022988541134081645 : Int)/10^30)
theorem v3473_mg_checked : Scalar.distance (sourceCoefficient 46 93 3 2) v3473_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3473_upper : Scalar.QComplex := ((999993394036387919094635563660 : Int)/10^30,(-3634815481617542383369334921 : Int)/10^30)
theorem v3473_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 93 5) 1) 14) v3473_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3473 : Material (46 : Basis) (93 : Basis) where
  plus := ![v3473_pa,v3473_pb,v3473_pg]
  minus := ![(Primitive.Addresses.material3473 1).one,v3473_mb,v3473_mg]
  upper := v3473_upper
  lower := (Primitive.Addresses.material3473 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3473_pa_checked.trans (by decide +kernel)
    · exact v3473_pb_checked.trans (by decide +kernel)
    · exact v3473_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 93 Primitive.Addresses.material3473
    · exact v3473_mb_checked.trans (by decide +kernel)
    · exact v3473_mg_checked.trans (by decide +kernel)
  upper_error := v3473_upper_checked
  lower_error := reuse_lower_error 46 93 Primitive.Addresses.material3473

def v3474_pa : Scalar.QComplex := ((999998091505502408833899618075 : Int)/10^30,(-1953710662516608385264434208 : Int)/10^30)
theorem v3474_pa_checked : Scalar.distance (sourceCoefficient 46 94 1 0) v3474_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3474_pb : Scalar.QComplex := ((-842982117025806028850469 : Int)/10^30,(-431476637954781079110504891 : Int)/10^30)
theorem v3474_pb_checked : Scalar.distance (sourceCoefficient 46 94 1 1) v3474_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3474_pg : Scalar.QComplex := ((-93086245815891057177846 : Int)/10^30,(181863938070473500339 : Int)/10^30)
theorem v3474_pg_checked : Scalar.distance (sourceCoefficient 46 94 1 2) v3474_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3474_mb : Scalar.QComplex := ((-1215326708713626625846750 : Int)/10^30,(-431475749840708823927377988 : Int)/10^30)
theorem v3474_mb_checked : Scalar.distance (sourceCoefficient 46 94 3 1) v3474_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3474_mg : Scalar.QComplex := ((-93086054215239781217030 : Int)/10^30,(262193108044451216688 : Int)/10^30)
theorem v3474_mg_checked : Scalar.distance (sourceCoefficient 46 94 3 2) v3474_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3474_upper : Scalar.QComplex := ((999993230198448882015589440463 : Int)/10^30,(-3679613739514370182427836190 : Int)/10^30)
theorem v3474_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 94 5) 1) 14) v3474_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3474 : Material (46 : Basis) (94 : Basis) where
  plus := ![v3474_pa,v3474_pb,v3474_pg]
  minus := ![(Primitive.Addresses.material3474 1).one,v3474_mb,v3474_mg]
  upper := v3474_upper
  lower := (Primitive.Addresses.material3474 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3474_pa_checked.trans (by decide +kernel)
    · exact v3474_pb_checked.trans (by decide +kernel)
    · exact v3474_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 94 Primitive.Addresses.material3474
    · exact v3474_mb_checked.trans (by decide +kernel)
    · exact v3474_mg_checked.trans (by decide +kernel)
  upper_error := v3474_upper_checked
  lower_error := reuse_lower_error 46 94 Primitive.Addresses.material3474

def v3475_pa : Scalar.QComplex := ((999998004026378000293994228893 : Int)/10^30,(-1997984799764180461448287452 : Int)/10^30)
theorem v3475_pa_checked : Scalar.distance (sourceCoefficient 46 95 1 0) v3475_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3475_pb : Scalar.QComplex := ((-862085397510764873033369 : Int)/10^30,(-431476594272790334427440705 : Int)/10^30)
theorem v3475_pb_checked : Scalar.distance (sourceCoefficient 46 95 1 1) v3475_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3475_pg : Scalar.QComplex := ((-93086237032381864690529 : Int)/10^30,(185985257879613328506 : Int)/10^30)
theorem v3475_pg_checked : Scalar.distance (sourceCoefficient 46 95 1 2) v3475_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3475_mb : Scalar.QComplex := ((-1234429944389970433600798 : Int)/10^30,(-431475689673463665340593663 : Int)/10^30)
theorem v3475_mb_checked : Scalar.distance (sourceCoefficient 46 95 3 1) v3475_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3475_mg : Scalar.QComplex := ((-93086041875220481297703 : Int)/10^30,(266314418739262487744 : Int)/10^30)
theorem v3475_mg_checked : Scalar.distance (sourceCoefficient 46 95 3 2) v3475_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3475_upper : Scalar.QComplex := ((999993066306310392401847444550 : Int)/10^30,(-3723887659839782948884333017 : Int)/10^30)
theorem v3475_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 95 5) 1) 14) v3475_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3475 : Material (46 : Basis) (95 : Basis) where
  plus := ![v3475_pa,v3475_pb,v3475_pg]
  minus := ![(Primitive.Addresses.material3475 1).one,v3475_mb,v3475_mg]
  upper := v3475_upper
  lower := (Primitive.Addresses.material3475 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3475_pa_checked.trans (by decide +kernel)
    · exact v3475_pb_checked.trans (by decide +kernel)
    · exact v3475_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 95 Primitive.Addresses.material3475
    · exact v3475_mb_checked.trans (by decide +kernel)
    · exact v3475_mg_checked.trans (by decide +kernel)
  upper_error := v3475_upper_checked
  lower_error := reuse_lower_error 46 95 Primitive.Addresses.material3475

def v3476_pa : Scalar.QComplex := ((999997961314955666349540451088 : Int)/10^30,(-2019248853517215923393661070 : Int)/10^30)
theorem v3476_pa_checked : Scalar.distance (sourceCoefficient 46 96 1 0) v3476_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3476_pb : Scalar.QComplex := ((-871260351357678166430975 : Int)/10^30,(-431476572892258356320474929 : Int)/10^30)
theorem v3476_pb_checked : Scalar.distance (sourceCoefficient 46 96 1 1) v3476_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3476_pg : Scalar.QComplex := ((-93086232738150106084221 : Int)/10^30,(187964651935471097098 : Int)/10^30)
theorem v3476_pg_checked : Scalar.distance (sourceCoefficient 46 96 1 2) v3476_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3476_mb : Scalar.QComplex := ((-1243604876370192939994988 : Int)/10^30,(-431475660375367702878297175 : Int)/10^30)
theorem v3476_mb_checked : Scalar.distance (sourceCoefficient 46 96 3 1) v3476_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3476_mg : Scalar.QComplex := ((-93086035872862400023805 : Int)/10^30,(268293808352372783904 : Int)/10^30)
theorem v3476_mg_checked : Scalar.distance (sourceCoefficient 46 96 3 2) v3476_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3476_upper : Scalar.QComplex := ((999992986895123954252003148265 : Int)/10^30,(-3745151608206467998479818143 : Int)/10^30)
theorem v3476_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 96 5) 1) 14) v3476_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3476 : Material (46 : Basis) (96 : Basis) where
  plus := ![v3476_pa,v3476_pb,v3476_pg]
  minus := ![(Primitive.Addresses.material3476 1).one,v3476_mb,v3476_mg]
  upper := v3476_upper
  lower := (Primitive.Addresses.material3476 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3476_pa_checked.trans (by decide +kernel)
    · exact v3476_pb_checked.trans (by decide +kernel)
    · exact v3476_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 96 Primitive.Addresses.material3476
    · exact v3476_mb_checked.trans (by decide +kernel)
    · exact v3476_mg_checked.trans (by decide +kernel)
  upper_error := v3476_upper_checked
  lower_error := reuse_lower_error 46 96 Primitive.Addresses.material3476

def v3477_pa : Scalar.QComplex := ((999997810905870271732710005417 : Int)/10^30,(-2092410922195596303905874964 : Int)/10^30)
theorem v3477_pa_checked : Scalar.distance (sourceCoefficient 46 97 1 0) v3477_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3477_pb : Scalar.QComplex := ((-902828112085248442238112 : Int)/10^30,(-431476497342204618192214064 : Int)/10^30)
theorem v3477_pb_checked : Scalar.distance (sourceCoefficient 46 97 1 1) v3477_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3477_pg : Scalar.QComplex := ((-93086217588089831849683 : Int)/10^30,(194775044768102100797 : Int)/10^30)
theorem v3477_pg_checked : Scalar.distance (sourceCoefficient 46 97 1 2) v3477_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3477_mb : Scalar.QComplex := ((-1275172560147349451094190 : Int)/10^30,(-431475557583786346759691723 : Int)/10^30)
theorem v3477_mb_checked : Scalar.distance (sourceCoefficient 46 97 3 1) v3477_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3477_mg : Scalar.QComplex := ((-93086014845745480995420 : Int)/10^30,(275104185575363602407 : Int)/10^30)
theorem v3477_mg_checked : Scalar.distance (sourceCoefficient 46 97 3 2) v3477_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3477_upper : Scalar.QComplex := ((999992710215169248438494355417 : Int)/10^30,(-3818313308326104917371882136 : Int)/10^30)
theorem v3477_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 97 5) 1) 14) v3477_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3477 : Material (46 : Basis) (97 : Basis) where
  plus := ![v3477_pa,v3477_pb,v3477_pg]
  minus := ![(Primitive.Addresses.material3477 1).one,v3477_mb,v3477_mg]
  upper := v3477_upper
  lower := (Primitive.Addresses.material3477 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3477_pa_checked.trans (by decide +kernel)
    · exact v3477_pb_checked.trans (by decide +kernel)
    · exact v3477_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 97 Primitive.Addresses.material3477
    · exact v3477_mb_checked.trans (by decide +kernel)
    · exact v3477_mg_checked.trans (by decide +kernel)
  upper_error := v3477_upper_checked
  lower_error := reuse_lower_error 46 97 Primitive.Addresses.material3477

def v3478_pa : Scalar.QComplex := ((999999418044361384328631849957 : Int)/10^30,(-1078847041317246890713559279 : Int)/10^30)
theorem v3478_pa_checked : Scalar.distance (sourceCoefficient 47 48 1 0) v3478_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3478_pb : Scalar.QComplex := ((-465498246868078121022570 : Int)/10^30,(-431477269845766549368121170 : Int)/10^30)
theorem v3478_pb_checked : Scalar.distance (sourceCoefficient 47 48 1 1) v3478_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3478_pg : Scalar.QComplex := ((-93086375718966497762658 : Int)/10^30,(100426019474840914065 : Int)/10^30)
theorem v3478_pg_checked : Scalar.distance (sourceCoefficient 47 48 1 2) v3478_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3478_mb : Scalar.QComplex := ((-837843524403856590172708 : Int)/10^30,(-431476707483037716015323000 : Int)/10^30)
theorem v3478_mb_checked : Scalar.distance (sourceCoefficient 47 48 3 1) v3478_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3478_mg : Scalar.QComplex := ((-93086254395522773283531 : Int)/10^30,(180755331872381108204 : Int)/10^30)
theorem v3478_mg_checked : Scalar.distance (sourceCoefficient 47 48 3 2) v3478_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3478_upper : Scalar.QComplex := ((999996066670575316069852618993 : Int)/10^30,(-2804753710807331690755354861 : Int)/10^30)
theorem v3478_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 48 5) 1) 14) v3478_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3478 : Material (47 : Basis) (48 : Basis) where
  plus := ![v3478_pa,v3478_pb,v3478_pg]
  minus := ![(Primitive.Addresses.material3478 1).one,v3478_mb,v3478_mg]
  upper := v3478_upper
  lower := (Primitive.Addresses.material3478 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3478_pa_checked.trans (by decide +kernel)
    · exact v3478_pb_checked.trans (by decide +kernel)
    · exact v3478_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 48 Primitive.Addresses.material3478
    · exact v3478_mb_checked.trans (by decide +kernel)
    · exact v3478_mg_checked.trans (by decide +kernel)
  upper_error := v3478_upper_checked
  lower_error := reuse_lower_error 47 48 Primitive.Addresses.material3478

def v3479_pa : Scalar.QComplex := ((999999394025470896919833632771 : Int)/10^30,(-1100885412293682094385159317 : Int)/10^30)
theorem v3479_pa_checked : Scalar.distance (sourceCoefficient 47 49 1 0) v3479_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3479_pb : Scalar.QComplex := ((-475007308408521548810976 : Int)/10^30,(-431477259360281513319810052 : Int)/10^30)
theorem v3479_pb_checked : Scalar.distance (sourceCoefficient 47 49 1 1) v3479_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3479_pg : Scalar.QComplex := ((-93086373469987290000479 : Int)/10^30,(102477492735181032372 : Int)/10^30)
theorem v3479_pg_checked : Scalar.distance (sourceCoefficient 47 49 1 2) v3479_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3479_mb : Scalar.QComplex := ((-847352573355140483478299 : Int)/10^30,(-431476688791664747023191922 : Int)/10^30)
theorem v3479_mb_checked : Scalar.distance (sourceCoefficient 47 49 3 1) v3479_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3479_mg : Scalar.QComplex := ((-93086250376215374171357 : Int)/10^30,(182806802428096208692 : Int)/10^30)
theorem v3479_mg_checked : Scalar.distance (sourceCoefficient 47 49 3 2) v3479_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3479_upper : Scalar.QComplex := ((999996004615491602047082300234 : Int)/10^30,(-2826792007505776129391718305 : Int)/10^30)
theorem v3479_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 49 5) 1) 14) v3479_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3479 : Material (47 : Basis) (49 : Basis) where
  plus := ![v3479_pa,v3479_pb,v3479_pg]
  minus := ![(Primitive.Addresses.material3479 1).one,v3479_mb,v3479_mg]
  upper := v3479_upper
  lower := (Primitive.Addresses.material3479 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3479_pa_checked.trans (by decide +kernel)
    · exact v3479_pb_checked.trans (by decide +kernel)
    · exact v3479_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 49 Primitive.Addresses.material3479
    · exact v3479_mb_checked.trans (by decide +kernel)
    · exact v3479_mg_checked.trans (by decide +kernel)
  upper_error := v3479_upper_checked
  lower_error := reuse_lower_error 47 49 Primitive.Addresses.material3479

def v3480_pa : Scalar.QComplex := ((999999391187065466761257789873 : Int)/10^30,(-1103460691829703659900560985 : Int)/10^30)
theorem v3480_pa_checked : Scalar.distance (sourceCoefficient 47 50 1 0) v3480_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3480_pb : Scalar.QComplex := ((-476118483617409759518768 : Int)/10^30,(-431477258116773552257360703 : Int)/10^30)
theorem v3480_pb_checked : Scalar.distance (sourceCoefficient 47 50 1 1) v3480_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3480_pg : Scalar.QComplex := ((-93086373203742336633265 : Int)/10^30,(102717216310889396419 : Int)/10^30)
theorem v3480_pg_checked : Scalar.distance (sourceCoefficient 47 50 1 2) v3480_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3480_mb : Scalar.QComplex := ((-848463747077196015823873 : Int)/10^30,(-431476686589263089178694775 : Int)/10^30)
theorem v3480_mb_checked : Scalar.distance (sourceCoefficient 47 50 3 1) v3480_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3480_mg : Scalar.QComplex := ((-93086249903099870852044 : Int)/10^30,(183046525684787126066 : Int)/10^30)
theorem v3480_mg_checked : Scalar.distance (sourceCoefficient 47 50 3 2) v3480_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3480_upper : Scalar.QComplex := ((999995997332391547721259805266 : Int)/10^30,(-2829367278307391065263176610 : Int)/10^30)
theorem v3480_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 50 5) 1) 14) v3480_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3480 : Material (47 : Basis) (50 : Basis) where
  plus := ![v3480_pa,v3480_pb,v3480_pg]
  minus := ![(Primitive.Addresses.material3480 1).one,v3480_mb,v3480_mg]
  upper := v3480_upper
  lower := (Primitive.Addresses.material3480 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3480_pa_checked.trans (by decide +kernel)
    · exact v3480_pb_checked.trans (by decide +kernel)
    · exact v3480_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 50 Primitive.Addresses.material3480
    · exact v3480_mb_checked.trans (by decide +kernel)
    · exact v3480_mg_checked.trans (by decide +kernel)
  upper_error := v3480_upper_checked
  lower_error := reuse_lower_error 47 50 Primitive.Addresses.material3480

def v3481_pa : Scalar.QComplex := ((999999378654950188555600486893 : Int)/10^30,(-1114759935391121721057779435 : Int)/10^30)
theorem v3481_pa_checked : Scalar.distance (sourceCoefficient 47 51 1 0) v3481_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3481_pb : Scalar.QComplex := ((-480993853111752562464455 : Int)/10^30,(-431477252615687893468882434 : Int)/10^30)
theorem v3481_pb_checked : Scalar.distance (sourceCoefficient 47 51 1 1) v3481_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3481_pg : Scalar.QComplex := ((-93086372027058673238262 : Int)/10^30,(103769022543046327749 : Int)/10^30)
theorem v3481_pg_checked : Scalar.distance (sourceCoefficient 47 51 1 2) v3481_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3481_mb : Scalar.QComplex := ((-853339110009026776798881 : Int)/10^30,(-431476676880955183568868836 : Int)/10^30)
theorem v3481_mb_checked : Scalar.distance (sourceCoefficient 47 51 3 1) v3481_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3481_mg : Scalar.QComplex := ((-93086247818755238832895 : Int)/10^30,(184098330509883521599 : Int)/10^30)
theorem v3481_mg_checked : Scalar.distance (sourceCoefficient 47 51 3 2) v3481_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3481_upper : Scalar.QComplex := ((999995965298825606990177648825 : Int)/10^30,(-2840666483410619078508887279 : Int)/10^30)
theorem v3481_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 51 5) 1) 14) v3481_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3481 : Material (47 : Basis) (51 : Basis) where
  plus := ![v3481_pa,v3481_pb,v3481_pg]
  minus := ![(Primitive.Addresses.material3481 1).one,v3481_mb,v3481_mg]
  upper := v3481_upper
  lower := (Primitive.Addresses.material3481 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3481_pa_checked.trans (by decide +kernel)
    · exact v3481_pb_checked.trans (by decide +kernel)
    · exact v3481_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 51 Primitive.Addresses.material3481
    · exact v3481_mb_checked.trans (by decide +kernel)
    · exact v3481_mg_checked.trans (by decide +kernel)
  upper_error := v3481_upper_checked
  lower_error := reuse_lower_error 47 51 Primitive.Addresses.material3481

def v3482_pa : Scalar.QComplex := ((999999351397545756097528022953 : Int)/10^30,(-1138948852145108969616590481 : Int)/10^30)
theorem v3482_pa_checked : Scalar.distance (sourceCoefficient 47 52 1 0) v3482_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3482_pb : Scalar.QComplex := ((-491430826642559581912609 : Int)/10^30,(-431477240592282639785596147 : Int)/10^30)
theorem v3482_pb_checked : Scalar.distance (sourceCoefficient 47 52 1 1) v3482_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3482_pg : Scalar.QComplex := ((-93086369461454106482580 : Int)/10^30,(106020682413753494161 : Int)/10^30)
theorem v3482_pg_checked : Scalar.distance (sourceCoefficient 47 52 1 2) v3482_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3482_mb : Scalar.QComplex := ((-863776069278014337615282 : Int)/10^30,(-431476655850916313500635124 : Int)/10^30)
theorem v3482_mb_checked : Scalar.distance (sourceCoefficient 47 52 3 1) v3482_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3482_mg : Scalar.QComplex := ((-93086243310070569944786 : Int)/10^30,(186349987328193621637 : Int)/10^30)
theorem v3482_mg_checked : Scalar.distance (sourceCoefficient 47 52 3 2) v3482_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3482_upper : Scalar.QComplex := ((999995896293585855238335478643 : Int)/10^30,(-2864855317094248973756410696 : Int)/10^30)
theorem v3482_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 52 5) 1) 14) v3482_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3482 : Material (47 : Basis) (52 : Basis) where
  plus := ![v3482_pa,v3482_pb,v3482_pg]
  minus := ![(Primitive.Addresses.material3482 1).one,v3482_mb,v3482_mg]
  upper := v3482_upper
  lower := (Primitive.Addresses.material3482 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3482_pa_checked.trans (by decide +kernel)
    · exact v3482_pb_checked.trans (by decide +kernel)
    · exact v3482_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 52 Primitive.Addresses.material3482
    · exact v3482_mb_checked.trans (by decide +kernel)
    · exact v3482_mg_checked.trans (by decide +kernel)
  upper_error := v3482_upper_checked
  lower_error := reuse_lower_error 47 52 Primitive.Addresses.material3482

def v3483_pa : Scalar.QComplex := ((999999347173516418257535149242 : Int)/10^30,(-1142651539613484817886412428 : Int)/10^30)
theorem v3483_pa_checked : Scalar.distance (sourceCoefficient 47 53 1 0) v3483_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3483_pb : Scalar.QComplex := ((-493028452996023470403856 : Int)/10^30,(-431477238722108315511478641 : Int)/10^30)
theorem v3483_pb_checked : Scalar.distance (sourceCoefficient 47 53 1 1) v3483_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3483_pg : Scalar.QComplex := ((-93086369063119646400611 : Int)/10^30,(106365352365121685729 : Int)/10^30)
theorem v3483_pg_checked : Scalar.distance (sourceCoefficient 47 53 1 2) v3483_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3483_mb : Scalar.QComplex := ((-865373693422732707256804 : Int)/10^30,(-431476652602063096958440360 : Int)/10^30)
theorem v3483_mb_checked : Scalar.distance (sourceCoefficient 47 53 3 1) v3483_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3483_mg : Scalar.QComplex := ((-93086242614301613508548 : Int)/10^30,(186694656807480739383 : Int)/10^30)
theorem v3483_mg_checked : Scalar.distance (sourceCoefficient 47 53 3 2) v3483_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3483_upper : Scalar.QComplex := ((999995885679060143360321626395 : Int)/10^30,(-2868557991757615349940187953 : Int)/10^30)
theorem v3483_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 53 5) 1) 14) v3483_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3483 : Material (47 : Basis) (53 : Basis) where
  plus := ![v3483_pa,v3483_pb,v3483_pg]
  minus := ![(Primitive.Addresses.material3483 1).one,v3483_mb,v3483_mg]
  upper := v3483_upper
  lower := (Primitive.Addresses.material3483 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3483_pa_checked.trans (by decide +kernel)
    · exact v3483_pb_checked.trans (by decide +kernel)
    · exact v3483_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 53 Primitive.Addresses.material3483
    · exact v3483_mb_checked.trans (by decide +kernel)
    · exact v3483_mg_checked.trans (by decide +kernel)
  upper_error := v3483_upper_checked
  lower_error := reuse_lower_error 47 53 Primitive.Addresses.material3483

def v3484_pa : Scalar.QComplex := ((999999345020737327058959282959 : Int)/10^30,(-1144534008384219026935615880 : Int)/10^30)
theorem v3484_pa_checked : Scalar.distance (sourceCoefficient 47 54 1 0) v3484_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3484_pb : Scalar.QComplex := ((-493840695924890568374999 : Int)/10^30,(-431477237768276003169580469 : Int)/10^30)
theorem v3484_pb_checked : Scalar.distance (sourceCoefficient 47 54 1 1) v3484_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3484_pg : Scalar.QComplex := ((-93086368860033081262942 : Int)/10^30,(106540584659179192388 : Int)/10^30)
theorem v3484_pg_checked : Scalar.distance (sourceCoefficient 47 54 1 2) v3484_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3484_mb : Scalar.QComplex := ((-866185935226050314936622 : Int)/10^30,(-431476650947302074223124957 : Int)/10^30)
theorem v3484_mb_checked : Scalar.distance (sourceCoefficient 47 54 3 1) v3484_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3484_mg : Scalar.QComplex := ((-93086242259997546387213 : Int)/10^30,(186869888861036695419 : Int)/10^30)
theorem v3484_mg_checked : Scalar.distance (sourceCoefficient 47 54 3 2) v3484_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3484_upper : Scalar.QComplex := ((999995880277313936418924371216 : Int)/10^30,(-2870440454009132042480977596 : Int)/10^30)
theorem v3484_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 54 5) 1) 14) v3484_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3484 : Material (47 : Basis) (54 : Basis) where
  plus := ![v3484_pa,v3484_pb,v3484_pg]
  minus := ![(Primitive.Addresses.material3484 1).one,v3484_mb,v3484_mg]
  upper := v3484_upper
  lower := (Primitive.Addresses.material3484 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3484_pa_checked.trans (by decide +kernel)
    · exact v3484_pb_checked.trans (by decide +kernel)
    · exact v3484_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 54 Primitive.Addresses.material3484
    · exact v3484_mb_checked.trans (by decide +kernel)
    · exact v3484_mg_checked.trans (by decide +kernel)
  upper_error := v3484_upper_checked
  lower_error := reuse_lower_error 47 54 Primitive.Addresses.material3484

def v3485_pa : Scalar.QComplex := ((999999327341756967782783322802 : Int)/10^30,(-1159877594229374927520317612 : Int)/10^30)
theorem v3485_pa_checked : Scalar.distance (sourceCoefficient 47 55 1 0) v3485_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3485_pb : Scalar.QComplex := ((-500461108041068731633318 : Int)/10^30,(-431477229917770988886205779 : Int)/10^30)
theorem v3485_pb_checked : Scalar.distance (sourceCoefficient 47 55 1 1) v3485_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3485_pg : Scalar.QComplex := ((-93086367190367348590523 : Int)/10^30,(107968864258462033268 : Int)/10^30)
theorem v3485_pg_checked : Scalar.distance (sourceCoefficient 47 55 1 2) v3485_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3485_mb : Scalar.QComplex := ((-872806338102514225854971 : Int)/10^30,(-431476637383682499072834855 : Int)/10^30)
theorem v3485_mb_checked : Scalar.distance (sourceCoefficient 47 55 3 1) v3485_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3485_mg : Scalar.QComplex := ((-93086239357791468551771 : Int)/10^30,(188298166487659437540 : Int)/10^30)
theorem v3485_mg_checked : Scalar.distance (sourceCoefficient 47 55 3 2) v3485_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3485_upper : Scalar.QComplex := ((999995836116722698402673946780 : Int)/10^30,(-2885783986489502935369046043 : Int)/10^30)
theorem v3485_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 55 5) 1) 14) v3485_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3485 : Material (47 : Basis) (55 : Basis) where
  plus := ![v3485_pa,v3485_pb,v3485_pg]
  minus := ![(Primitive.Addresses.material3485 1).one,v3485_mb,v3485_mg]
  upper := v3485_upper
  lower := (Primitive.Addresses.material3485 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3485_pa_checked.trans (by decide +kernel)
    · exact v3485_pb_checked.trans (by decide +kernel)
    · exact v3485_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 55 Primitive.Addresses.material3485
    · exact v3485_mb_checked.trans (by decide +kernel)
    · exact v3485_mg_checked.trans (by decide +kernel)
  upper_error := v3485_upper_checked
  lower_error := reuse_lower_error 47 55 Primitive.Addresses.material3485

def v3486_pa : Scalar.QComplex := ((999999323111474426173933481202 : Int)/10^30,(-1163519055696801245787882680 : Int)/10^30)
theorem v3486_pa_checked : Scalar.distance (sourceCoefficient 47 56 1 0) v3486_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3486_pb : Scalar.QComplex := ((-502032316737569353202267 : Int)/10^30,(-431477228034740536564049664 : Int)/10^30)
theorem v3486_pb_checked : Scalar.distance (sourceCoefficient 47 56 1 1) v3486_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3486_pg : Scalar.QComplex := ((-93086366790355061680961 : Int)/10^30,(108307834898490673360 : Int)/10^30)
theorem v3486_pg_checked : Scalar.distance (sourceCoefficient 47 56 1 2) v3486_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3486_mb : Scalar.QComplex := ((-874377544589011570121243 : Int)/10^30,(-431476634144770407421722952 : Int)/10^30)
theorem v3486_mb_checked : Scalar.distance (sourceCoefficient 47 56 3 1) v3486_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3486_mg : Scalar.QComplex := ((-93086238665262934911250 : Int)/10^30,(188637136656281228907 : Int)/10^30)
theorem v3486_mg_checked : Scalar.distance (sourceCoefficient 47 56 3 2) v3486_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3486_upper : Scalar.QComplex := ((999995825601614315328686660899 : Int)/10^30,(-2889425435232316255434768951 : Int)/10^30)
theorem v3486_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 56 5) 1) 14) v3486_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3486 : Material (47 : Basis) (56 : Basis) where
  plus := ![v3486_pa,v3486_pb,v3486_pg]
  minus := ![(Primitive.Addresses.material3486 1).one,v3486_mb,v3486_mg]
  upper := v3486_upper
  lower := (Primitive.Addresses.material3486 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3486_pa_checked.trans (by decide +kernel)
    · exact v3486_pb_checked.trans (by decide +kernel)
    · exact v3486_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 56 Primitive.Addresses.material3486
    · exact v3486_mb_checked.trans (by decide +kernel)
    · exact v3486_mg_checked.trans (by decide +kernel)
  upper_error := v3486_upper_checked
  lower_error := reuse_lower_error 47 56 Primitive.Addresses.material3486

def v3487_pa : Scalar.QComplex := ((999999309338355219960285943521 : Int)/10^30,(-1175296903997697025262985929 : Int)/10^30)
theorem v3487_pa_checked : Scalar.distance (sourceCoefficient 47 57 1 0) v3487_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3487_pb : Scalar.QComplex := ((-507114193279607501495177 : Int)/10^30,(-431477221892076353874333612 : Int)/10^30)
theorem v3487_pb_checked : Scalar.distance (sourceCoefficient 47 57 1 1) v3487_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3487_pg : Scalar.QComplex := ((-93086365486704404834275 : Int)/10^30,(109404192722201455965 : Int)/10^30)
theorem v3487_pg_checked : Scalar.distance (sourceCoefficient 47 57 1 2) v3487_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3487_mb : Scalar.QComplex := ((-879459413937992294245472 : Int)/10^30,(-431476623616677935370751022 : Int)/10^30)
theorem v3487_mb_checked : Scalar.distance (sourceCoefficient 47 57 3 1) v3487_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3487_mg : Scalar.QComplex := ((-93086236415505339734256 : Int)/10^30,(189733492946776085104 : Int)/10^30)
theorem v3487_mg_checked : Scalar.distance (sourceCoefficient 47 57 3 2) v3487_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3487_upper : Scalar.QComplex := ((999995791501017933263441940815 : Int)/10^30,(-2901203242220336251663409823 : Int)/10^30)
theorem v3487_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 57 5) 1) 14) v3487_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3487 : Material (47 : Basis) (57 : Basis) where
  plus := ![v3487_pa,v3487_pb,v3487_pg]
  minus := ![(Primitive.Addresses.material3487 1).one,v3487_mb,v3487_mg]
  upper := v3487_upper
  lower := (Primitive.Addresses.material3487 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3487_pa_checked.trans (by decide +kernel)
    · exact v3487_pb_checked.trans (by decide +kernel)
    · exact v3487_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 57 Primitive.Addresses.material3487
    · exact v3487_mb_checked.trans (by decide +kernel)
    · exact v3487_mg_checked.trans (by decide +kernel)
  upper_error := v3487_upper_checked
  lower_error := reuse_lower_error 47 57 Primitive.Addresses.material3487

def v3488_pa : Scalar.QComplex := ((999999301807141696725522618012 : Int)/10^30,(-1181687449850120718911417621 : Int)/10^30)
theorem v3488_pa_checked : Scalar.distance (sourceCoefficient 47 58 1 0) v3488_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3488_pb : Scalar.QComplex := ((-509871570016780125635512 : Int)/10^30,(-431477218525728426209816508 : Int)/10^30)
theorem v3488_pb_checked : Scalar.distance (sourceCoefficient 47 58 1 1) v3488_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3488_pg : Scalar.QComplex := ((-93086364773051633545254 : Int)/10^30,(109999065805047661247 : Int)/10^30)
theorem v3488_pg_checked : Scalar.distance (sourceCoefficient 47 58 1 2) v3488_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3488_mb : Scalar.QComplex := ((-882216786743460893902099 : Int)/10^30,(-431476617870839324609622882 : Int)/10^30)
theorem v3488_mb_checked : Scalar.distance (sourceCoefficient 47 58 3 1) v3488_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3488_mg : Scalar.QComplex := ((-93086235188504155763585 : Int)/10^30,(190328365192273654705 : Int)/10^30)
theorem v3488_mg_checked : Scalar.distance (sourceCoefficient 47 58 3 2) v3488_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3488_upper : Scalar.QComplex := ((999995772940313231394254037901 : Int)/10^30,(-2907593765556601269625963326 : Int)/10^30)
theorem v3488_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 58 5) 1) 14) v3488_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3488 : Material (47 : Basis) (58 : Basis) where
  plus := ![v3488_pa,v3488_pb,v3488_pg]
  minus := ![(Primitive.Addresses.material3488 1).one,v3488_mb,v3488_mg]
  upper := v3488_upper
  lower := (Primitive.Addresses.material3488 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3488_pa_checked.trans (by decide +kernel)
    · exact v3488_pb_checked.trans (by decide +kernel)
    · exact v3488_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 58 Primitive.Addresses.material3488
    · exact v3488_mb_checked.trans (by decide +kernel)
    · exact v3488_mg_checked.trans (by decide +kernel)
  upper_error := v3488_upper_checked
  lower_error := reuse_lower_error 47 58 Primitive.Addresses.material3488

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
