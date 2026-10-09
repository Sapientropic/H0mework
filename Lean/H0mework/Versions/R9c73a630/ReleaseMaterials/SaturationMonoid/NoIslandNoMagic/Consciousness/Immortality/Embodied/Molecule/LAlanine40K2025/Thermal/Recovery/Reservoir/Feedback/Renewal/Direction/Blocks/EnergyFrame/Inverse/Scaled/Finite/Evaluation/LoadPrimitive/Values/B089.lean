import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B059
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B060

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1425_pa : Scalar.QComplex := ((999999058817566810124447863745 : Int)/10^30,(-1371992704264632217383833596 : Int)/10^30)
theorem v1425_pa_checked : Scalar.distance (sourceCoefficient 15 91 1 0) v1425_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1425_pb : Scalar.QComplex := ((-591983853598569487384497 : Int)/10^30,(-431477000273889964527971741 : Int)/10^30)
theorem v1425_pb_checked : Scalar.distance (sourceCoefficient 15 91 1 1) v1425_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1425_pg : Scalar.QComplex := ((-93086329920843755706958 : Int)/10^30,(127713885720233886552 : Int)/10^30)
theorem v1425_pg_checked : Scalar.distance (sourceCoefficient 15 91 1 2) v1425_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1425_mb : Scalar.QComplex := ((-964328851409587466880593 : Int)/10^30,(-431476328759879596946507858 : Int)/10^30)
theorem v1425_mb_checked : Scalar.distance (sourceCoefficient 15 91 3 1) v1425_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1425_mg : Scalar.QComplex := ((-93086185049217514060943 : Int)/10^30,(208043148435537104920 : Int)/10^30)
theorem v1425_mg_checked : Scalar.distance (sourceCoefficient 15 91 3 2) v1425_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1425_upper : Scalar.QComplex := ((999995201501495487593288170429 : Int)/10^30,(-3097898317155828730971088542 : Int)/10^30)
theorem v1425_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 91 5) 1) 14) v1425_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1425 : Material (15 : Basis) (91 : Basis) where
  plus := ![v1425_pa,v1425_pb,v1425_pg]
  minus := ![(Primitive.Addresses.material1425 1).one,v1425_mb,v1425_mg]
  upper := v1425_upper
  lower := (Primitive.Addresses.material1425 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1425_pa_checked.trans (by decide +kernel)
    · exact v1425_pb_checked.trans (by decide +kernel)
    · exact v1425_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 91 Primitive.Addresses.material1425
    · exact v1425_mb_checked.trans (by decide +kernel)
    · exact v1425_mg_checked.trans (by decide +kernel)
  upper_error := v1425_upper_checked
  lower_error := reuse_lower_error 15 91 Primitive.Addresses.material1425

def v1426_pa : Scalar.QComplex := ((999999014463428565198122390924 : Int)/10^30,(-1403948778120936333668428667 : Int)/10^30)
theorem v1426_pa_checked : Scalar.distance (sourceCoefficient 15 92 1 0) v1426_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1426_pb : Scalar.QComplex := ((-605772169214111707367757 : Int)/10^30,(-431476975259922015487651421 : Int)/10^30)
theorem v1426_pb_checked : Scalar.distance (sourceCoefficient 15 92 1 1) v1426_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1426_pg : Scalar.QComplex := ((-93086325158218191031710 : Int)/10^30,(130688561264005198710 : Int)/10^30)
theorem v1426_pg_checked : Scalar.distance (sourceCoefficient 15 92 1 2) v1426_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1426_mb : Scalar.QComplex := ((-978117140305181873317201 : Int)/10^30,(-431476291847225588219334771 : Int)/10^30)
theorem v1426_mb_checked : Scalar.distance (sourceCoefficient 15 92 3 1) v1426_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1426_mg : Scalar.QComplex := ((-93086177719582702867340 : Int)/10^30,(211017818761769401122 : Int)/10^30)
theorem v1426_mg_checked : Scalar.distance (sourceCoefficient 15 92 3 2) v1426_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1426_upper : Scalar.QComplex := ((999995101994138859339016510873 : Int)/10^30,(-3129854266866095827664355522 : Int)/10^30)
theorem v1426_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 92 5) 1) 14) v1426_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1426 : Material (15 : Basis) (92 : Basis) where
  plus := ![v1426_pa,v1426_pb,v1426_pg]
  minus := ![(Primitive.Addresses.material1426 1).one,v1426_mb,v1426_mg]
  upper := v1426_upper
  lower := (Primitive.Addresses.material1426 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1426_pa_checked.trans (by decide +kernel)
    · exact v1426_pb_checked.trans (by decide +kernel)
    · exact v1426_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 92 Primitive.Addresses.material1426
    · exact v1426_mb_checked.trans (by decide +kernel)
    · exact v1426_mg_checked.trans (by decide +kernel)
  upper_error := v1426_upper_checked
  lower_error := reuse_lower_error 15 92 Primitive.Addresses.material1426

def v1427_pa : Scalar.QComplex := ((999998960498637069717381807210 : Int)/10^30,(-1441874351425075354325984631 : Int)/10^30)
theorem v1427_pa_checked : Scalar.distance (sourceCoefficient 15 93 1 0) v1427_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1427_pb : Scalar.QComplex := ((-622136186665500276136246 : Int)/10^30,(-431476944810897807489332279 : Int)/10^30)
theorem v1427_pb_checked : Scalar.distance (sourceCoefficient 15 93 1 1) v1427_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1427_pg : Scalar.QComplex := ((-93086319362005740139771 : Int)/10^30,(134218915877385446375 : Int)/10^30)
theorem v1427_pg_checked : Scalar.distance (sourceCoefficient 15 93 1 2) v1427_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1427_mb : Scalar.QComplex := ((-994481125387362354030559 : Int)/10^30,(-431476247276802665222970613 : Int)/10^30)
theorem v1427_mb_checked : Scalar.distance (sourceCoefficient 15 93 3 1) v1427_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1427_mg : Scalar.QComplex := ((-93086168876835380092425 : Int)/10^30,(214548167058766987647 : Int)/10^30)
theorem v1427_mg_checked : Scalar.distance (sourceCoefficient 15 93 3 2) v1427_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1427_upper : Scalar.QComplex := ((999994982573328796265915685967 : Int)/10^30,(-3167779690546213989039404737 : Int)/10^30)
theorem v1427_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 93 5) 1) 14) v1427_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1427 : Material (15 : Basis) (93 : Basis) where
  plus := ![v1427_pa,v1427_pb,v1427_pg]
  minus := ![(Primitive.Addresses.material1427 1).one,v1427_mb,v1427_mg]
  upper := v1427_upper
  lower := (Primitive.Addresses.material1427 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1427_pa_checked.trans (by decide +kernel)
    · exact v1427_pb_checked.trans (by decide +kernel)
    · exact v1427_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 93 Primitive.Addresses.material1427
    · exact v1427_mb_checked.trans (by decide +kernel)
    · exact v1427_mg_checked.trans (by decide +kernel)
  upper_error := v1427_upper_checked
  lower_error := reuse_lower_error 15 93 Primitive.Addresses.material1427

def v1428_pa : Scalar.QComplex := ((999998894901291722168026612391 : Int)/10^30,(-1486672860891900760415764283 : Int)/10^30)
theorem v1428_pa_checked : Scalar.distance (sourceCoefficient 15 94 1 0) v1428_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1428_pb : Scalar.QComplex := ((-641465717777801641031536 : Int)/10^30,(-431476907777835493762717125 : Int)/10^30)
theorem v1428_pb_checked : Scalar.distance (sourceCoefficient 15 94 1 1) v1428_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1428_pg : Scalar.QComplex := ((-93086312314160680240959 : Int)/10^30,(138389047171527498786 : Int)/10^30)
theorem v1428_pg_checked : Scalar.distance (sourceCoefficient 15 94 1 2) v1428_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1428_mb : Scalar.QComplex := ((-1013810617344531013068130 : Int)/10^30,(-431476193563239360446100842 : Int)/10^30)
theorem v1428_mb_checked : Scalar.distance (sourceCoefficient 15 94 3 1) v1428_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1428_mg : Scalar.QComplex := ((-93086158230357453325280 : Int)/10^30,(218718290718205711299 : Int)/10^30)
theorem v1428_mg_checked : Scalar.distance (sourceCoefficient 15 94 3 2) v1428_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1428_upper : Scalar.QComplex := ((999994839657917897548108384701 : Int)/10^30,(-3212578020075854821691848796 : Int)/10^30)
theorem v1428_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 94 5) 1) 14) v1428_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1428 : Material (15 : Basis) (94 : Basis) where
  plus := ![v1428_pa,v1428_pb,v1428_pg]
  minus := ![(Primitive.Addresses.material1428 1).one,v1428_mb,v1428_mg]
  upper := v1428_upper
  lower := (Primitive.Addresses.material1428 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1428_pa_checked.trans (by decide +kernel)
    · exact v1428_pb_checked.trans (by decide +kernel)
    · exact v1428_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 94 Primitive.Addresses.material1428
    · exact v1428_mb_checked.trans (by decide +kernel)
    · exact v1428_mg_checked.trans (by decide +kernel)
  upper_error := v1428_upper_checked
  lower_error := reuse_lower_error 15 94 Primitive.Addresses.material1428

def v1429_pa : Scalar.QComplex := ((999998828099902612801317284265 : Int)/10^30,(-1530947034166943056136402958 : Int)/10^30)
theorem v1429_pa_checked : Scalar.distance (sourceCoefficient 15 95 1 0) v1429_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1429_pb : Scalar.QComplex := ((-660569008626121377170716 : Int)/10^30,(-431476870043829204032738097 : Int)/10^30)
theorem v1429_pb_checked : Scalar.distance (sourceCoefficient 15 95 1 1) v1429_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1429_pg : Scalar.QComplex := ((-93086305134665151982602 : Int)/10^30,(142510369775390915741 : Int)/10^30)
theorem v1429_pg_checked : Scalar.distance (sourceCoefficient 15 95 1 2) v1429_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1429_mb : Scalar.QComplex := ((-1032913868517074551374673 : Int)/10^30,(-431476139343967498992251467 : Int)/10^30)
theorem v1429_mb_checked : Scalar.distance (sourceCoefficient 15 95 3 1) v1429_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1429_mg : Scalar.QComplex := ((-93086147494348808666731 : Int)/10^30,(222839605591931080676 : Int)/10^30)
theorem v1429_mg_checked : Scalar.distance (sourceCoefficient 15 95 3 2) v1429_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1429_upper : Scalar.QComplex := ((999994696443421729904599392557 : Int)/10^30,(-3256852012116579405880406724 : Int)/10^30)
theorem v1429_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 95 5) 1) 14) v1429_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1429 : Material (15 : Basis) (95 : Basis) where
  plus := ![v1429_pa,v1429_pb,v1429_pg]
  minus := ![(Primitive.Addresses.material1429 1).one,v1429_mb,v1429_mg]
  upper := v1429_upper
  lower := (Primitive.Addresses.material1429 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1429_pa_checked.trans (by decide +kernel)
    · exact v1429_pb_checked.trans (by decide +kernel)
    · exact v1429_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 95 Primitive.Addresses.material1429
    · exact v1429_mb_checked.trans (by decide +kernel)
    · exact v1429_mg_checked.trans (by decide +kernel)
  upper_error := v1429_upper_checked
  lower_error := reuse_lower_error 15 95 Primitive.Addresses.material1429

def v1430_pa : Scalar.QComplex := ((999998795319616278156530255377 : Int)/10^30,(-1552211105548745909783997724 : Int)/10^30)
theorem v1430_pa_checked : Scalar.distance (sourceCoefficient 15 96 1 0) v1430_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1430_pb : Scalar.QComplex := ((-669743967543978482087914 : Int)/10^30,(-431476851520004753721921825 : Int)/10^30)
theorem v1430_pb_checked : Scalar.distance (sourceCoefficient 15 96 1 1) v1430_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1430_pg : Scalar.QComplex := ((-93086301610811654814613 : Int)/10^30,(144489765198747749439 : Int)/10^30)
theorem v1430_pg_checked : Scalar.distance (sourceCoefficient 15 96 1 2) v1430_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1430_mb : Scalar.QComplex := ((-1042088808033448916301478 : Int)/10^30,(-431476112902573624647211391 : Int)/10^30)
theorem v1430_mb_checked : Scalar.distance (sourceCoefficient 15 96 3 1) v1430_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1430_mg : Scalar.QComplex := ((-93086142262367521894015 : Int)/10^30,(224818997237341675832 : Int)/10^30)
theorem v1430_mg_checked : Scalar.distance (sourceCoefficient 15 96 3 2) v1430_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1430_upper : Scalar.QComplex := ((999994626963326074140695278450 : Int)/10^30,(-3278115995252245380371072845 : Int)/10^30)
theorem v1430_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 96 5) 1) 14) v1430_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1430 : Material (15 : Basis) (96 : Basis) where
  plus := ![v1430_pa,v1430_pb,v1430_pg]
  minus := ![(Primitive.Addresses.material1430 1).one,v1430_mb,v1430_mg]
  upper := v1430_upper
  lower := (Primitive.Addresses.material1430 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1430_pa_checked.trans (by decide +kernel)
    · exact v1430_pb_checked.trans (by decide +kernel)
    · exact v1430_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 96 Primitive.Addresses.material1430
    · exact v1430_mb_checked.trans (by decide +kernel)
    · exact v1430_mg_checked.trans (by decide +kernel)
  upper_error := v1430_upper_checked
  lower_error := reuse_lower_error 15 96 Primitive.Addresses.material1430

def v1431_pa : Scalar.QComplex := ((999998679080048628579763933728 : Int)/10^30,(-1625373236494720476870394835 : Int)/10^30)
theorem v1431_pa_checked : Scalar.distance (sourceCoefficient 15 97 1 0) v1431_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1431_pb : Scalar.QComplex := ((-701311746182923995751049 : Int)/10^30,(-431476785798868617748269262 : Int)/10^30)
theorem v1431_pb_checked : Scalar.distance (sourceCoefficient 15 97 1 1) v1431_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1431_pg : Scalar.QComplex := ((-93086289111349810965540 : Int)/10^30,(151300162861601669551 : Int)/10^30)
theorem v1431_pg_checked : Scalar.distance (sourceCoefficient 15 97 1 2) v1431_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1431_mb : Scalar.QComplex := ((-1073656518203887208676693 : Int)/10^30,(-431476019939890754217855359 : Int)/10^30)
theorem v1431_mb_checked : Scalar.distance (sourceCoefficient 15 97 3 1) v1431_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1431_mg : Scalar.QComplex := ((-93086123885843878047329 : Int)/10^30,(231629381577900679137 : Int)/10^30)
theorem v1431_mg_checked : Scalar.distance (sourceCoefficient 15 97 3 2) v1431_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1431_upper : Scalar.QComplex := ((999994384452730753665708874205 : Int)/10^30,(-3351277816612871539074142973 : Int)/10^30)
theorem v1431_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 97 5) 1) 14) v1431_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1431 : Material (15 : Basis) (97 : Basis) where
  plus := ![v1431_pa,v1431_pb,v1431_pg]
  minus := ![(Primitive.Addresses.material1431 1).one,v1431_mb,v1431_mg]
  upper := v1431_upper
  lower := (Primitive.Addresses.material1431 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1431_pa_checked.trans (by decide +kernel)
    · exact v1431_pb_checked.trans (by decide +kernel)
    · exact v1431_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 97 Primitive.Addresses.material1431
    · exact v1431_mb_checked.trans (by decide +kernel)
    · exact v1431_mg_checked.trans (by decide +kernel)
  upper_error := v1431_upper_checked
  lower_error := reuse_lower_error 15 97 Primitive.Addresses.material1431

def v1432_pa : Scalar.QComplex := ((999999992457628388561483873725 : Int)/10^30,(-122819962408354704428104609 : Int)/10^30)
theorem v1432_pa_checked : Scalar.distance (sourceCoefficient 16 17 1 0) v1432_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1432_pb : Scalar.QComplex := ((-52994052908954767232290 : Int)/10^30,(-431477517743068938348762479 : Int)/10^30)
theorem v1432_pb_checked : Scalar.distance (sourceCoefficient 16 17 1 1) v1432_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1432_pg : Scalar.QComplex := ((-93086429194536272129739 : Int)/10^30,(11432871820631884688 : Int)/10^30)
theorem v1432_pg_checked : Scalar.distance (sourceCoefficient 16 17 1 2) v1432_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1432_mb : Scalar.QComplex := ((-425339697963104102004628 : Int)/10^30,(-431477311352788688994663341 : Int)/10^30)
theorem v1432_mb_checked : Scalar.distance (sourceCoefficient 16 17 3 1) v1432_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1432_mg : Scalar.QComplex := ((-93086384668150959251839 : Int)/10^30,(91762263501396403282 : Int)/10^30)
theorem v1432_mg_checked : Scalar.distance (sourceCoefficient 16 17 3 2) v1432_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1432_upper : Scalar.QComplex := ((999998291098994896864477044179 : Int)/10^30,(-1848729047173659194519774999 : Int)/10^30)
theorem v1432_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 17 5) 1) 14) v1432_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1432 : Material (16 : Basis) (17 : Basis) where
  plus := ![v1432_pa,v1432_pb,v1432_pg]
  minus := ![(Primitive.Addresses.material1432 1).one,v1432_mb,v1432_mg]
  upper := v1432_upper
  lower := (Primitive.Addresses.material1432 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1432_pa_checked.trans (by decide +kernel)
    · exact v1432_pb_checked.trans (by decide +kernel)
    · exact v1432_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 17 Primitive.Addresses.material1432
    · exact v1432_mb_checked.trans (by decide +kernel)
    · exact v1432_mg_checked.trans (by decide +kernel)
  upper_error := v1432_upper_checked
  lower_error := reuse_lower_error 16 17 Primitive.Addresses.material1432

def v1433_pa : Scalar.QComplex := ((999999989467179791196137089104 : Int)/10^30,(-145140071333410279093919926 : Int)/10^30)
theorem v1433_pa_checked : Scalar.distance (sourceCoefficient 16 18 1 0) v1433_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1433_pb : Scalar.QComplex := ((-62624678168012873512384 : Int)/10^30,(-431477516395450561480995231 : Int)/10^30)
theorem v1433_pb_checked : Scalar.distance (sourceCoefficient 16 18 1 1) v1433_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1433_pg : Scalar.QComplex := ((-93086428909984414435317 : Int)/10^30,(13510571074471978808 : Int)/10^30)
theorem v1433_pg_checked : Scalar.distance (sourceCoefficient 16 18 1 2) v1433_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1433_mb : Scalar.QComplex := ((-434970318473306318261355 : Int)/10^30,(-431477301694374962599874107 : Int)/10^30)
theorem v1433_mb_checked : Scalar.distance (sourceCoefficient 16 18 3 1) v1433_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1433_mg : Scalar.QComplex := ((-93086382590638327545762 : Int)/10^30,(93839961736058672201 : Int)/10^30)
theorem v1433_mg_checked : Scalar.distance (sourceCoefficient 16 18 3 2) v1433_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1433_upper : Scalar.QComplex := ((999998249586067613239419272082 : Int)/10^30,(-1871049117694291441813324147 : Int)/10^30)
theorem v1433_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 18 5) 1) 14) v1433_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1433 : Material (16 : Basis) (18 : Basis) where
  plus := ![v1433_pa,v1433_pb,v1433_pg]
  minus := ![(Primitive.Addresses.material1433 1).one,v1433_mb,v1433_mg]
  upper := v1433_upper
  lower := (Primitive.Addresses.material1433 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1433_pa_checked.trans (by decide +kernel)
    · exact v1433_pb_checked.trans (by decide +kernel)
    · exact v1433_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 18 Primitive.Addresses.material1433
    · exact v1433_mb_checked.trans (by decide +kernel)
    · exact v1433_mg_checked.trans (by decide +kernel)
  upper_error := v1433_upper_checked
  lower_error := reuse_lower_error 16 18 Primitive.Addresses.material1433

def v1434_pa : Scalar.QComplex := ((999999987073010842002186583156 : Int)/10^30,(-160791722886747432670613654 : Int)/10^30)
theorem v1434_pa_checked : Scalar.distance (sourceCoefficient 16 19 1 0) v1434_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1434_pb : Scalar.QComplex := ((-69378013965531792437603 : Int)/10^30,(-431477515279495415644374484 : Int)/10^30)
theorem v1434_pb_checked : Scalar.distance (sourceCoefficient 16 19 1 1) v1434_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1434_pg : Scalar.QComplex := ((-93086428678174698921703 : Int)/10^30,(14967527438023110217 : Int)/10^30)
theorem v1434_pg_checked : Scalar.distance (sourceCoefficient 16 19 1 2) v1434_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1434_mb : Scalar.QComplex := ((-441723650793230646974073 : Int)/10^30,(-431477294750595597978937960 : Int)/10^30)
theorem v1434_mb_checked : Scalar.distance (sourceCoefficient 16 19 3 1) v1434_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1434_mg : Scalar.QComplex := ((-93086381101540975479600 : Int)/10^30,(95296917357077019098 : Int)/10^30)
theorem v1434_mg_checked : Scalar.distance (sourceCoefficient 16 19 3 2) v1434_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1434_upper : Scalar.QComplex := ((999998220178571555556168686669 : Int)/10^30,(-1886700741804213769840091573 : Int)/10^30)
theorem v1434_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 19 5) 1) 14) v1434_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1434 : Material (16 : Basis) (19 : Basis) where
  plus := ![v1434_pa,v1434_pb,v1434_pg]
  minus := ![(Primitive.Addresses.material1434 1).one,v1434_mb,v1434_mg]
  upper := v1434_upper
  lower := (Primitive.Addresses.material1434 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1434_pa_checked.trans (by decide +kernel)
    · exact v1434_pb_checked.trans (by decide +kernel)
    · exact v1434_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 19 Primitive.Addresses.material1434
    · exact v1434_mb_checked.trans (by decide +kernel)
    · exact v1434_mg_checked.trans (by decide +kernel)
  upper_error := v1434_upper_checked
  lower_error := reuse_lower_error 16 19 Primitive.Addresses.material1434

def v1435_pa : Scalar.QComplex := ((999999986617985192701778239157 : Int)/10^30,(-163597155951801690295319200 : Int)/10^30)
theorem v1435_pa_checked : Scalar.distance (sourceCoefficient 16 20 1 0) v1435_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1435_pb : Scalar.QComplex := ((-70588495266331389783694 : Int)/10^30,(-431477515064574764407489499 : Int)/10^30)
theorem v1435_pb_checked : Scalar.distance (sourceCoefficient 16 20 1 1) v1435_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1435_pg : Scalar.QComplex := ((-93086428633812983806849 : Int)/10^30,(15228675185992517905 : Int)/10^30)
theorem v1435_pg_checked : Scalar.distance (sourceCoefficient 16 20 1 2) v1435_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1435_mb : Scalar.QComplex := ((-442934131457845891953452 : Int)/10^30,(-431477293491084182230764000 : Int)/10^30)
theorem v1435_mb_checked : Scalar.distance (sourceCoefficient 16 20 3 1) v1435_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1435_mg : Scalar.QComplex := ((-93086380831820532042996 : Int)/10^30,(95558064969527023008 : Int)/10^30)
theorem v1435_mg_checked : Scalar.distance (sourceCoefficient 16 20 3 2) v1435_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1435_upper : Scalar.QComplex := ((999998214881623620578928174417 : Int)/10^30,(-1889506169905572035295819753 : Int)/10^30)
theorem v1435_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 20 5) 1) 14) v1435_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1435 : Material (16 : Basis) (20 : Basis) where
  plus := ![v1435_pa,v1435_pb,v1435_pg]
  minus := ![(Primitive.Addresses.material1435 1).one,v1435_mb,v1435_mg]
  upper := v1435_upper
  lower := (Primitive.Addresses.material1435 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1435_pa_checked.trans (by decide +kernel)
    · exact v1435_pb_checked.trans (by decide +kernel)
    · exact v1435_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 20 Primitive.Addresses.material1435
    · exact v1435_mb_checked.trans (by decide +kernel)
    · exact v1435_mg_checked.trans (by decide +kernel)
  upper_error := v1435_upper_checked
  lower_error := reuse_lower_error 16 20 Primitive.Addresses.material1435

def v1436_pa : Scalar.QComplex := ((999999976540924941770447117742 : Int)/10^30,(-216605977678666345657395380 : Int)/10^30)
theorem v1436_pa_checked : Scalar.distance (sourceCoefficient 16 21 1 0) v1436_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1436_pb : Scalar.QComplex := ((-93460610125454969299406 : Int)/10^30,(-431477510152576428349567739 : Int)/10^30)
theorem v1436_pb_checked : Scalar.distance (sourceCoefficient 16 21 1 1) v1436_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1436_pg : Scalar.QComplex := ((-93086427634939962091141 : Int)/10^30,(20163077139487735519 : Int)/10^30)
theorem v1436_pg_checked : Scalar.distance (sourceCoefficient 16 21 1 2) v1436_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1436_mb : Scalar.QComplex := ((-465806233561802466303859 : Int)/10^30,(-431477268841482673523998778 : Int)/10^30)
theorem v1436_mb_checked : Scalar.distance (sourceCoefficient 16 21 3 1) v1436_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1436_mg : Scalar.QComplex := ((-93086375574781233601144 : Int)/10^30,(100492464223736449856 : Int)/10^30)
theorem v1436_mg_checked : Scalar.distance (sourceCoefficient 16 21 3 2) v1436_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1436_upper : Scalar.QComplex := ((999998113316161000418529232926 : Int)/10^30,(-1942514895289931772762913751 : Int)/10^30)
theorem v1436_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 21 5) 1) 14) v1436_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1436 : Material (16 : Basis) (21 : Basis) where
  plus := ![v1436_pa,v1436_pb,v1436_pg]
  minus := ![(Primitive.Addresses.material1436 1).one,v1436_mb,v1436_mg]
  upper := v1436_upper
  lower := (Primitive.Addresses.material1436 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1436_pa_checked.trans (by decide +kernel)
    · exact v1436_pb_checked.trans (by decide +kernel)
    · exact v1436_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 21 Primitive.Addresses.material1436
    · exact v1436_mb_checked.trans (by decide +kernel)
    · exact v1436_mg_checked.trans (by decide +kernel)
  upper_error := v1436_upper_checked
  lower_error := reuse_lower_error 16 21 Primitive.Addresses.material1436

def v1437_pa : Scalar.QComplex := ((999999976237983208021552389145 : Int)/10^30,(-218000075732380086711123308 : Int)/10^30)
theorem v1437_pa_checked : Scalar.distance (sourceCoefficient 16 22 1 0) v1437_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1437_pb : Scalar.QComplex := ((-94062132092268676271162 : Int)/10^30,(-431477510001577649991741467 : Int)/10^30)
theorem v1437_pb_checked : Scalar.distance (sourceCoefficient 16 22 1 1) v1437_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1437_pg : Scalar.QComplex := ((-93086427604551934481929 : Int)/10^30,(20292848749648050725 : Int)/10^30)
theorem v1437_pg_checked : Scalar.distance (sourceCoefficient 16 22 1 2) v1437_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1437_mb : Scalar.QComplex := ((-466407755174336909128627 : Int)/10^30,(-431477268171397585573389471 : Int)/10^30)
theorem v1437_mb_checked : Scalar.distance (sourceCoefficient 16 22 3 1) v1437_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1437_mg : Scalar.QComplex := ((-93086375432406162434788 : Int)/10^30,(100622235759353364544 : Int)/10^30)
theorem v1437_mg_checked : Scalar.distance (sourceCoefficient 16 22 3 2) v1437_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1437_upper : Scalar.QComplex := ((999998110607132948743334914511 : Int)/10^30,(-1943908990744450275279895652 : Int)/10^30)
theorem v1437_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 22 5) 1) 14) v1437_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1437 : Material (16 : Basis) (22 : Basis) where
  plus := ![v1437_pa,v1437_pb,v1437_pg]
  minus := ![(Primitive.Addresses.material1437 1).one,v1437_mb,v1437_mg]
  upper := v1437_upper
  lower := (Primitive.Addresses.material1437 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1437_pa_checked.trans (by decide +kernel)
    · exact v1437_pb_checked.trans (by decide +kernel)
    · exact v1437_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 22 Primitive.Addresses.material1437
    · exact v1437_mb_checked.trans (by decide +kernel)
    · exact v1437_mg_checked.trans (by decide +kernel)
  upper_error := v1437_upper_checked
  lower_error := reuse_lower_error 16 22 Primitive.Addresses.material1437

def v1438_pa : Scalar.QComplex := ((999999973937540470364086904036 : Int)/10^30,(-228308822387616088938893013 : Int)/10^30)
theorem v1438_pa_checked : Scalar.distance (sourceCoefficient 16 23 1 0) v1438_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1438_pb : Scalar.QComplex := ((-98510124499771422685804 : Int)/10^30,(-431477508850304808657217821 : Int)/10^30)
theorem v1438_pb_checked : Scalar.distance (sourceCoefficient 16 23 1 1) v1438_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1438_pg : Scalar.QComplex := ((-93086427373294840145569 : Int)/10^30,(21252453167758496714 : Int)/10^30)
theorem v1438_pg_checked : Scalar.distance (sourceCoefficient 16 23 1 2) v1438_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1438_mb : Scalar.QComplex := ((-470855744932152188266842 : Int)/10^30,(-431477263181708055376919780 : Int)/10^30)
theorem v1438_mb_checked : Scalar.distance (sourceCoefficient 16 23 3 1) v1438_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1438_mg : Scalar.QComplex := ((-93086374373053760355326 : Int)/10^30,(101581839620594772603 : Int)/10^30)
theorem v1438_mg_checked : Scalar.distance (sourceCoefficient 16 23 3 2) v1438_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1438_upper : Scalar.QComplex := ((999998090514732112578922739818 : Int)/10^30,(-1954217718075663614318536008 : Int)/10^30)
theorem v1438_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 23 5) 1) 14) v1438_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1438 : Material (16 : Basis) (23 : Basis) where
  plus := ![v1438_pa,v1438_pb,v1438_pg]
  minus := ![(Primitive.Addresses.material1438 1).one,v1438_mb,v1438_mg]
  upper := v1438_upper
  lower := (Primitive.Addresses.material1438 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1438_pa_checked.trans (by decide +kernel)
    · exact v1438_pb_checked.trans (by decide +kernel)
    · exact v1438_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 23 Primitive.Addresses.material1438
    · exact v1438_mb_checked.trans (by decide +kernel)
    · exact v1438_mg_checked.trans (by decide +kernel)
  upper_error := v1438_upper_checked
  lower_error := reuse_lower_error 16 23 Primitive.Addresses.material1438

def v1439_pa : Scalar.QComplex := ((999999961008378386892576243225 : Int)/10^30,(-279254797104487162100364937 : Int)/10^30)
theorem v1439_pa_checked : Scalar.distance (sourceCoefficient 16 24 1 0) v1439_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1439_pb : Scalar.QComplex := ((-120492167047797903831221 : Int)/10^30,(-431477502263028481614716972 : Int)/10^30)
theorem v1439_pb_checked : Scalar.distance (sourceCoefficient 16 24 1 1) v1439_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1439_pg : Scalar.QComplex := ((-93086426060964623125780 : Int)/10^30,(25994832036417176605 : Int)/10^30)
theorem v1439_pg_checked : Scalar.distance (sourceCoefficient 16 24 1 2) v1439_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1439_mb : Scalar.QComplex := ((-492837773610736809482692 : Int)/10^30,(-431477237624921496576152658 : Int)/10^30)
theorem v1439_mb_checked : Scalar.distance (sourceCoefficient 16 24 3 1) v1439_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1439_mg : Scalar.QComplex := ((-93086368968264657139068 : Int)/10^30,(106324215590967190141 : Int)/10^30)
theorem v1439_mg_checked : Scalar.distance (sourceCoefficient 16 24 3 2) v1439_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1439_upper : Scalar.QComplex := ((999997989657458706979026275239 : Int)/10^30,(-2005163594599929049631416079 : Int)/10^30)
theorem v1439_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 24 5) 1) 14) v1439_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1439 : Material (16 : Basis) (24 : Basis) where
  plus := ![v1439_pa,v1439_pb,v1439_pg]
  minus := ![(Primitive.Addresses.material1439 1).one,v1439_mb,v1439_mg]
  upper := v1439_upper
  lower := (Primitive.Addresses.material1439 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1439_pa_checked.trans (by decide +kernel)
    · exact v1439_pb_checked.trans (by decide +kernel)
    · exact v1439_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 24 Primitive.Addresses.material1439
    · exact v1439_mb_checked.trans (by decide +kernel)
    · exact v1439_mg_checked.trans (by decide +kernel)
  upper_error := v1439_upper_checked
  lower_error := reuse_lower_error 16 24 Primitive.Addresses.material1439

def v1440_pa : Scalar.QComplex := ((999999954325751520575921329626 : Int)/10^30,(-302239135243454505190576887 : Int)/10^30)
theorem v1440_pa_checked : Scalar.distance (sourceCoefficient 16 25 1 0) v1440_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1440_pb : Scalar.QComplex := ((-130409392071391503673866 : Int)/10^30,(-431477498802381714011631306 : Int)/10^30)
theorem v1440_pb_checked : Scalar.distance (sourceCoefficient 16 25 1 1) v1440_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1440_pg : Scalar.QComplex := ((-93086425376635845521766 : Int)/10^30,(28134361993754617303 : Int)/10^30)
theorem v1440_pg_checked : Scalar.distance (sourceCoefficient 16 25 1 2) v1440_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1440_mb : Scalar.QComplex := ((-502754991955311994770463 : Int)/10^30,(-431477225606157477403182252 : Int)/10^30)
theorem v1440_mb_checked : Scalar.distance (sourceCoefficient 16 25 3 1) v1440_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1440_mg : Scalar.QComplex := ((-93086366437618142011916 : Int)/10^30,(108463744161114932325 : Int)/10^30)
theorem v1440_mg_checked : Scalar.distance (sourceCoefficient 16 25 3 2) v1440_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1440_upper : Scalar.QComplex := ((999997943305959288660339209309 : Int)/10^30,(-2028147886972816936658367091 : Int)/10^30)
theorem v1440_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 25 5) 1) 14) v1440_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1440 : Material (16 : Basis) (25 : Basis) where
  plus := ![v1440_pa,v1440_pb,v1440_pg]
  minus := ![(Primitive.Addresses.material1440 1).one,v1440_mb,v1440_mg]
  upper := v1440_upper
  lower := (Primitive.Addresses.material1440 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1440_pa_checked.trans (by decide +kernel)
    · exact v1440_pb_checked.trans (by decide +kernel)
    · exact v1440_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 25 Primitive.Addresses.material1440
    · exact v1440_mb_checked.trans (by decide +kernel)
    · exact v1440_mg_checked.trans (by decide +kernel)
  upper_error := v1440_upper_checked
  lower_error := reuse_lower_error 16 25 Primitive.Addresses.material1440

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
