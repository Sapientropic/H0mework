import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B018

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v433_pa : Scalar.QComplex := ((999994097862753127212769287138 : Int)/10^30,(3435729858199199796094894532 : Int)/10^30)
theorem v433_pa_checked : Scalar.distance (sourceCoefficient 4 56 1 0) v433_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v433_pb : Scalar.QComplex := ((1482434717787015182770111 : Int)/10^30,(-431473378128409845933660980 : Int)/10^30)
theorem v433_pb_checked : Scalar.distance (sourceCoefficient 4 56 1 1) v433_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v433_pg : Scalar.QComplex := ((-93085708303389327858498 : Int)/10^30,(-319819235006595089221 : Int)/10^30)
theorem v433_pg_checked : Scalar.distance (sourceCoefficient 4 56 1 2) v433_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v433_mb : Scalar.QComplex := ((1110092073323571430008440 : Int)/10^30,(-431474496745546930182198299 : Int)/10^30)
theorem v433_mb_checked : Scalar.distance (sourceCoefficient 4 56 3 1) v433_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v433_mg : Scalar.QComplex := ((-93085949632921586527175 : Int)/10^30,(-239490342082124310595 : Int)/10^30)
theorem v433_mg_checked : Scalar.distance (sourceCoefficient 4 56 3 2) v433_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v433_upper : Scalar.QComplex := ((999998538247060192870937089268 : Int)/10^30,(1709825646927955368314811780 : Int)/10^30)
theorem v433_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 56 5) 1) 14) v433_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material433 : Material (4 : Basis) (56 : Basis) where
  plus := ![v433_pa,v433_pb,v433_pg]
  minus := ![(Primitive.Addresses.material433 1).one,v433_mb,v433_mg]
  upper := v433_upper
  lower := (Primitive.Addresses.material433 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v433_pa_checked.trans (by decide +kernel)
    · exact v433_pb_checked.trans (by decide +kernel)
    · exact v433_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 56 Primitive.Addresses.material433
    · exact v433_mb_checked.trans (by decide +kernel)
    · exact v433_mg_checked.trans (by decide +kernel)
  upper_error := v433_upper_checked
  lower_error := reuse_lower_error 4 56 Primitive.Addresses.material433

def v434_pa : Scalar.QComplex := ((999994138258927327078065891542 : Int)/10^30,(3423952071121533793296004811 : Int)/10^30)
theorem v434_pa_checked : Scalar.distance (sourceCoefficient 4 57 1 0) v434_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v434_pb : Scalar.QComplex := ((1477352858855915187559403 : Int)/10^30,(-431473387567622001208177758 : Int)/10^30)
theorem v434_pb_checked : Scalar.distance (sourceCoefficient 4 57 1 1) v434_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v434_pg : Scalar.QComplex := ((-93085711201758528032767 : Int)/10^30,(-318722881932089892497 : Int)/10^30)
theorem v434_pg_checked : Scalar.distance (sourceCoefficient 4 57 1 2) v434_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v434_mb : Scalar.QComplex := ((1105010208139064803605049 : Int)/10^30,(-431474501799340191697230544 : Int)/10^30)
theorem v434_mb_checked : Scalar.distance (sourceCoefficient 4 57 3 1) v434_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v434_mg : Scalar.QComplex := ((-93085951585186382117626 : Int)/10^30,(-238393986914679387272 : Int)/10^30)
theorem v434_mg_checked : Scalar.distance (sourceCoefficient 4 57 3 2) v434_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v434_upper : Scalar.QComplex := ((999998558315782203825746872898 : Int)/10^30,(1698047807671787744971336687 : Int)/10^30)
theorem v434_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 57 5) 1) 14) v434_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material434 : Material (4 : Basis) (57 : Basis) where
  plus := ![v434_pa,v434_pb,v434_pg]
  minus := ![(Primitive.Addresses.material434 1).one,v434_mb,v434_mg]
  upper := v434_upper
  lower := (Primitive.Addresses.material434 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v434_pa_checked.trans (by decide +kernel)
    · exact v434_pb_checked.trans (by decide +kernel)
    · exact v434_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 57 Primitive.Addresses.material434
    · exact v434_mb_checked.trans (by decide +kernel)
    · exact v434_mg_checked.trans (by decide +kernel)
  upper_error := v434_upper_checked
  lower_error := reuse_lower_error 4 57 Primitive.Addresses.material434

def v435_pa : Scalar.QComplex := ((999994160119445781766126289792 : Int)/10^30,(3417561558221238567534390829 : Int)/10^30)
theorem v435_pa_checked : Scalar.distance (sourceCoefficient 4 58 1 0) v435_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v435_pb : Scalar.QComplex := ((1474595491597463153921489 : Int)/10^30,(-431473392655848653099506450 : Int)/10^30)
theorem v435_pb_checked : Scalar.distance (sourceCoefficient 4 58 1 1) v435_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v435_pg : Scalar.QComplex := ((-93085712768080873856259 : Int)/10^30,(-318128011405404672216 : Int)/10^30)
theorem v435_pg_checked : Scalar.distance (sourceCoefficient 4 58 1 2) v435_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v435_mb : Scalar.QComplex := ((1102252837516396182837121 : Int)/10^30,(-431474504508081192176402962 : Int)/10^30)
theorem v435_mb_checked : Scalar.distance (sourceCoefficient 4 58 3 1) v435_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v435_mg : Scalar.QComplex := ((-93085952638161672172336 : Int)/10^30,(-237799115257826011096 : Int)/10^30)
theorem v435_mg_checked : Scalar.distance (sourceCoefficient 4 58 3 2) v435_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v435_upper : Scalar.QComplex := ((999998569146822576731538777324 : Int)/10^30,(1691657266560139119772569241 : Int)/10^30)
theorem v435_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 58 5) 1) 14) v435_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material435 : Material (4 : Basis) (58 : Basis) where
  plus := ![v435_pa,v435_pb,v435_pg]
  minus := ![(Primitive.Addresses.material435 1).one,v435_mb,v435_mg]
  upper := v435_upper
  lower := (Primitive.Addresses.material435 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v435_pa_checked.trans (by decide +kernel)
    · exact v435_pb_checked.trans (by decide +kernel)
    · exact v435_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 58 Primitive.Addresses.material435
    · exact v435_mb_checked.trans (by decide +kernel)
    · exact v435_mg_checked.trans (by decide +kernel)
  upper_error := v435_upper_checked
  lower_error := reuse_lower_error 4 58 Primitive.Addresses.material435

def v436_pa : Scalar.QComplex := ((999994219997802710533874285321 : Int)/10^30,(3399995733255195068991537916 : Int)/10^30)
theorem v436_pa_checked : Scalar.distance (sourceCoefficient 4 59 1 0) v436_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v436_pb : Scalar.QComplex := ((1467016220541411128384728 : Int)/10^30,(-431473406520984905599361755 : Int)/10^30)
theorem v436_pb_checked : Scalar.distance (sourceCoefficient 4 59 1 1) v436_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v436_pg : Scalar.QComplex := ((-93085717050634881029931 : Int)/10^30,(-316492870128643726438 : Int)/10^30)
theorem v436_pg_checked : Scalar.distance (sourceCoefficient 4 59 1 2) v436_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v436_mb : Scalar.QComplex := ((1094673557317465037916091 : Int)/10^30,(-431474511832642718376036637 : Int)/10^30)
theorem v436_mb_checked : Scalar.distance (sourceCoefficient 4 59 3 1) v436_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v436_mg : Scalar.QComplex := ((-93085955509660806940043 : Int)/10^30,(-236163970894251663186 : Int)/10^30)
theorem v436_mg_checked : Scalar.distance (sourceCoefficient 4 59 3 2) v436_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v436_upper : Scalar.QComplex := ((999998598708069991522086981030 : Int)/10^30,(1674091364411716544457208084 : Int)/10^30)
theorem v436_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 59 5) 1) 14) v436_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material436 : Material (4 : Basis) (59 : Basis) where
  plus := ![v436_pa,v436_pb,v436_pg]
  minus := ![(Primitive.Addresses.material436 1).one,v436_mb,v436_mg]
  upper := v436_upper
  lower := (Primitive.Addresses.material436 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v436_pa_checked.trans (by decide +kernel)
    · exact v436_pb_checked.trans (by decide +kernel)
    · exact v436_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 59 Primitive.Addresses.material436
    · exact v436_mb_checked.trans (by decide +kernel)
    · exact v436_mg_checked.trans (by decide +kernel)
  upper_error := v436_upper_checked
  lower_error := reuse_lower_error 4 59 Primitive.Addresses.material436

def v437_pa : Scalar.QComplex := ((999994288689766678160277401971 : Int)/10^30,(3379731919484014075022039832 : Int)/10^30)
theorem v437_pa_checked : Scalar.distance (sourceCoefficient 4 60 1 0) v437_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v437_pb : Scalar.QComplex := ((1458272826388612051253199 : Int)/10^30,(-431473422295200838212348344 : Int)/10^30)
theorem v437_pb_checked : Scalar.distance (sourceCoefficient 4 60 1 1) v437_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v437_pg : Scalar.QComplex := ((-93085721949333586675629 : Int)/10^30,(-314606582536170732517 : Int)/10^30)
theorem v437_pg_checked : Scalar.distance (sourceCoefficient 4 60 1 2) v437_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v437_mb : Scalar.QComplex := ((1085930152807793291192394 : Int)/10^30,(-431474520061697411516460447 : Int)/10^30)
theorem v437_mb_checked : Scalar.distance (sourceCoefficient 4 60 3 1) v437_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v437_mg : Scalar.QComplex := ((-93085958780576451511616 : Int)/10^30,(-234277679776773393772 : Int)/10^30)
theorem v437_mg_checked : Scalar.distance (sourceCoefficient 4 60 3 2) v437_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v437_upper : Scalar.QComplex := ((999998632426427400304052579547 : Int)/10^30,(1653827462265007686054143899 : Int)/10^30)
theorem v437_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 60 5) 1) 14) v437_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material437 : Material (4 : Basis) (60 : Basis) where
  plus := ![v437_pa,v437_pb,v437_pg]
  minus := ![(Primitive.Addresses.material437 1).one,v437_mb,v437_mg]
  upper := v437_upper
  lower := (Primitive.Addresses.material437 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v437_pa_checked.trans (by decide +kernel)
    · exact v437_pb_checked.trans (by decide +kernel)
    · exact v437_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 60 Primitive.Addresses.material437
    · exact v437_mb_checked.trans (by decide +kernel)
    · exact v437_mg_checked.trans (by decide +kernel)
  upper_error := v437_upper_checked
  lower_error := reuse_lower_error 4 60 Primitive.Addresses.material437

def v438_pa : Scalar.QComplex := ((999994308475584377059023810047 : Int)/10^30,(3373872617304291220255565661 : Int)/10^30)
theorem v438_pa_checked : Scalar.distance (sourceCoefficient 4 61 1 0) v438_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v438_pb : Scalar.QComplex := ((1455744665222777155442413 : Int)/10^30,(-431473426812301773279797297 : Int)/10^30)
theorem v438_pb_checked : Scalar.distance (sourceCoefficient 4 61 1 1) v438_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v438_pg : Scalar.QComplex := ((-93085723357485728952091 : Int)/10^30,(-314061160584547037055 : Int)/10^30)
theorem v438_pg_checked : Scalar.distance (sourceCoefficient 4 61 1 2) v438_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v438_mb : Scalar.QComplex := ((1083401988685253675805903 : Int)/10^30,(-431474522397107442697347674 : Int)/10^30)
theorem v438_mb_checked : Scalar.distance (sourceCoefficient 4 61 3 1) v438_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v438_mg : Scalar.QComplex := ((-93085959718053490110240 : Int)/10^30,(-233732256813063339948 : Int)/10^30)
theorem v438_mg_checked : Scalar.distance (sourceCoefficient 4 61 3 2) v438_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v438_upper : Scalar.QComplex := ((999998642099591620091384686345 : Int)/10^30,(1647968134663500753062645365 : Int)/10^30)
theorem v438_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 61 5) 1) 14) v438_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material438 : Material (4 : Basis) (61 : Basis) where
  plus := ![v438_pa,v438_pb,v438_pg]
  minus := ![(Primitive.Addresses.material438 1).one,v438_mb,v438_mg]
  upper := v438_upper
  lower := (Primitive.Addresses.material438 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v438_pa_checked.trans (by decide +kernel)
    · exact v438_pb_checked.trans (by decide +kernel)
    · exact v438_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 61 Primitive.Addresses.material438
    · exact v438_mb_checked.trans (by decide +kernel)
    · exact v438_mg_checked.trans (by decide +kernel)
  upper_error := v438_upper_checked
  lower_error := reuse_lower_error 4 61 Primitive.Addresses.material438

def v439_pa : Scalar.QComplex := ((999994337162349032547848918821 : Int)/10^30,(3365359302393229317574408695 : Int)/10^30)
theorem v439_pa_checked : Scalar.distance (sourceCoefficient 4 62 1 0) v439_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v439_pb : Scalar.QComplex := ((1452071355471528089862464 : Int)/10^30,(-431473433340258665375118384 : Int)/10^30)
theorem v439_pb_checked : Scalar.distance (sourceCoefficient 4 62 1 1) v439_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v439_pg : Scalar.QComplex := ((-93085725396826205312607 : Int)/10^30,(-313268685873939983643 : Int)/10^30)
theorem v439_pg_checked : Scalar.distance (sourceCoefficient 4 62 1 2) v439_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v439_mb : Scalar.QComplex := ((1079728674668412919551039 : Int)/10^30,(-431474525755161028537816678 : Int)/10^30)
theorem v439_mb_checked : Scalar.distance (sourceCoefficient 4 62 3 1) v439_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v439_mg : Scalar.QComplex := ((-93085961073523223613233 : Int)/10^30,(-232939780637671856564 : Int)/10^30)
theorem v439_mg_checked : Scalar.distance (sourceCoefficient 4 62 3 2) v439_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v439_upper : Scalar.QComplex := ((999998656093104335416879478365 : Int)/10^30,(1639454782921268013776129279 : Int)/10^30)
theorem v439_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 62 5) 1) 14) v439_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material439 : Material (4 : Basis) (62 : Basis) where
  plus := ![v439_pa,v439_pb,v439_pg]
  minus := ![(Primitive.Addresses.material439 1).one,v439_mb,v439_mg]
  upper := v439_upper
  lower := (Primitive.Addresses.material439 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v439_pa_checked.trans (by decide +kernel)
    · exact v439_pb_checked.trans (by decide +kernel)
    · exact v439_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 62 Primitive.Addresses.material439
    · exact v439_mb_checked.trans (by decide +kernel)
    · exact v439_mg_checked.trans (by decide +kernel)
  upper_error := v439_upper_checked
  lower_error := reuse_lower_error 4 62 Primitive.Addresses.material439

def v440_pa : Scalar.QComplex := ((999994420299619335862260150756 : Int)/10^30,(3340564267945153228851437989 : Int)/10^30)
theorem v440_pa_checked : Scalar.distance (sourceCoefficient 4 63 1 0) v440_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v440_pb : Scalar.QComplex := ((1441372839132119278000193 : Int)/10^30,(-431473452115367300950289513 : Int)/10^30)
theorem v440_pb_checked : Scalar.distance (sourceCoefficient 4 63 1 1) v440_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v440_pg : Scalar.QComplex := ((-93085731291560078448804 : Int)/10^30,(-310960602875123870118 : Int)/10^30)
theorem v440_pg_checked : Scalar.distance (sourceCoefficient 4 63 1 2) v440_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v440_mb : Scalar.QComplex := ((1069030146110477534203265 : Int)/10^30,(-431474535297924915661236594 : Int)/10^30)
theorem v440_mb_checked : Scalar.distance (sourceCoefficient 4 63 3 1) v440_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v440_mg : Scalar.QComplex := ((-93085964976483226091681 : Int)/10^30,(-230631693411370684545 : Int)/10^30)
theorem v440_mg_checked : Scalar.distance (sourceCoefficient 4 63 3 2) v440_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v440_upper : Scalar.QComplex := ((999998696436270746107709630101 : Int)/10^30,(1614659641915096716840336452 : Int)/10^30)
theorem v440_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 63 5) 1) 14) v440_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material440 : Material (4 : Basis) (63 : Basis) where
  plus := ![v440_pa,v440_pb,v440_pg]
  minus := ![(Primitive.Addresses.material440 1).one,v440_mb,v440_mg]
  upper := v440_upper
  lower := (Primitive.Addresses.material440 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v440_pa_checked.trans (by decide +kernel)
    · exact v440_pb_checked.trans (by decide +kernel)
    · exact v440_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 63 Primitive.Addresses.material440
    · exact v440_mb_checked.trans (by decide +kernel)
    · exact v440_mg_checked.trans (by decide +kernel)
  upper_error := v440_upper_checked
  lower_error := reuse_lower_error 4 63 Primitive.Addresses.material440

def v441_pa : Scalar.QComplex := ((999994538052205490241589661549 : Int)/10^30,(3305127192128285835519270150 : Int)/10^30)
theorem v441_pa_checked : Scalar.distance (sourceCoefficient 4 64 1 0) v441_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v441_pb : Scalar.QComplex := ((1426082515114690634720853 : Int)/10^30,(-431473478334775831354615295 : Int)/10^30)
theorem v441_pb_checked : Scalar.distance (sourceCoefficient 4 64 1 1) v441_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v441_pg : Scalar.QComplex := ((-93085739600413453973315 : Int)/10^30,(-307661889585878581344 : Int)/10^30)
theorem v441_pg_checked : Scalar.distance (sourceCoefficient 4 64 1 2) v441_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v441_mb : Scalar.QComplex := ((1053739805160166641526752 : Int)/10^30,(-431474548322462706970393155 : Int)/10^30)
theorem v441_mb_checked : Scalar.distance (sourceCoefficient 4 64 3 1) v441_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v441_mg : Scalar.QComplex := ((-93085970438692507763087 : Int)/10^30,(-227332974180220865788 : Int)/10^30)
theorem v441_mg_checked : Scalar.distance (sourceCoefficient 4 64 3 2) v441_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v441_upper : Scalar.QComplex := ((999998753027503488334292214237 : Int)/10^30,(1579222415647309750101403481 : Int)/10^30)
theorem v441_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 64 5) 1) 14) v441_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material441 : Material (4 : Basis) (64 : Basis) where
  plus := ![v441_pa,v441_pb,v441_pg]
  minus := ![(Primitive.Addresses.material441 1).one,v441_mb,v441_mg]
  upper := v441_upper
  lower := (Primitive.Addresses.material441 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v441_pa_checked.trans (by decide +kernel)
    · exact v441_pb_checked.trans (by decide +kernel)
    · exact v441_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 64 Primitive.Addresses.material441
    · exact v441_mb_checked.trans (by decide +kernel)
    · exact v441_mg_checked.trans (by decide +kernel)
  upper_error := v441_upper_checked
  lower_error := reuse_lower_error 4 64 Primitive.Addresses.material441

def v442_pa : Scalar.QComplex := ((999994656279660213671810298337 : Int)/10^30,(3269160767571027017339470443 : Int)/10^30)
theorem v442_pa_checked : Scalar.distance (sourceCoefficient 4 65 1 0) v442_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v442_pb : Scalar.QComplex := ((1410563789858678416055382 : Int)/10^30,(-431473504207106176243650455 : Int)/10^30)
theorem v442_pb_checked : Scalar.distance (sourceCoefficient 4 65 1 1) v442_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v442_pg : Scalar.QComplex := ((-93085747893929551975769 : Int)/10^30,(-304313901203225385160 : Int)/10^30)
theorem v442_pg_checked : Scalar.distance (sourceCoefficient 4 65 1 2) v442_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v442_mb : Scalar.QComplex := ((1038221063355829235319548 : Int)/10^30,(-431474560802822459909625730 : Int)/10^30)
theorem v442_mb_checked : Scalar.distance (sourceCoefficient 4 65 3 1) v442_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v442_mg : Scalar.QComplex := ((-93085975843042331280005 : Int)/10^30,(-223984979887245888617 : Int)/10^30)
theorem v442_mg_checked : Scalar.distance (sourceCoefficient 4 65 3 2) v442_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v442_upper : Scalar.QComplex := ((999998809179996188577814935158 : Int)/10^30,(1543255840607954055215021172 : Int)/10^30)
theorem v442_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 65 5) 1) 14) v442_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material442 : Material (4 : Basis) (65 : Basis) where
  plus := ![v442_pa,v442_pb,v442_pg]
  minus := ![(Primitive.Addresses.material442 1).one,v442_mb,v442_mg]
  upper := v442_upper
  lower := (Primitive.Addresses.material442 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v442_pa_checked.trans (by decide +kernel)
    · exact v442_pb_checked.trans (by decide +kernel)
    · exact v442_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 65 Primitive.Addresses.material442
    · exact v442_mb_checked.trans (by decide +kernel)
    · exact v442_mg_checked.trans (by decide +kernel)
  upper_error := v442_upper_checked
  lower_error := reuse_lower_error 4 65 Primitive.Addresses.material442

def v443_pa : Scalar.QComplex := ((999994713621582253063012532437 : Int)/10^30,(3251573294529449532077160117 : Int)/10^30)
theorem v443_pa_checked : Scalar.distance (sourceCoefficient 4 66 1 0) v443_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v443_pb : Scalar.QComplex := ((1402975180490864301122043 : Int)/10^30,(-431473516587661476882106876 : Int)/10^30)
theorem v443_pb_checked : Scalar.distance (sourceCoefficient 4 66 1 1) v443_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v443_pg : Scalar.QComplex := ((-93085751898288795632207 : Int)/10^30,(-302676745037482380002 : Int)/10^30)
theorem v443_pg_checked : Scalar.distance (sourceCoefficient 4 66 1 2) v443_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v443_mb : Scalar.QComplex := ((1030632446129739579665287 : Int)/10^30,(-431474566634745044556463479 : Int)/10^30)
theorem v443_mb_checked : Scalar.distance (sourceCoefficient 4 66 3 1) v443_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v443_mg : Scalar.QComplex := ((-93085978434608047670816 : Int)/10^30,(-222347820875509268068 : Int)/10^30)
theorem v443_mg_checked : Scalar.distance (sourceCoefficient 4 66 3 2) v443_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v443_upper : Scalar.QComplex := ((999998836167449877240044767463 : Int)/10^30,(1525668294793896274214714525 : Int)/10^30)
theorem v443_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 66 5) 1) 14) v443_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material443 : Material (4 : Basis) (66 : Basis) where
  plus := ![v443_pa,v443_pb,v443_pg]
  minus := ![(Primitive.Addresses.material443 1).one,v443_mb,v443_mg]
  upper := v443_upper
  lower := (Primitive.Addresses.material443 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v443_pa_checked.trans (by decide +kernel)
    · exact v443_pb_checked.trans (by decide +kernel)
    · exact v443_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 66 Primitive.Addresses.material443
    · exact v443_mb_checked.trans (by decide +kernel)
    · exact v443_mg_checked.trans (by decide +kernel)
  upper_error := v443_upper_checked
  lower_error := reuse_lower_error 4 66 Primitive.Addresses.material443

def v444_pa : Scalar.QComplex := ((999994809163146243392797010762 : Int)/10^30,(3222056294158432621748703035 : Int)/10^30)
theorem v444_pa_checked : Scalar.distance (sourceCoefficient 4 67 1 0) v444_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v444_pb : Scalar.QComplex := ((1390239242049057329438325 : Int)/10^30,(-431473536965957392072361684 : Int)/10^30)
theorem v444_pb_checked : Scalar.distance (sourceCoefficient 4 67 1 1) v444_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v444_pg : Scalar.QComplex := ((-93085758543292811907702 : Int)/10^30,(-299929111094012078123 : Int)/10^30)
theorem v444_pg_checked : Scalar.distance (sourceCoefficient 4 67 1 2) v444_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v444_mb : Scalar.QComplex := ((1017896494844552980575829 : Int)/10^30,(-431474576022492102070584965 : Int)/10^30)
theorem v444_mb_checked : Scalar.distance (sourceCoefficient 4 67 3 1) v444_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v444_mg : Scalar.QComplex := ((-93085982708525245331795 : Int)/10^30,(-219600182220769470243 : Int)/10^30)
theorem v444_mg_checked : Scalar.distance (sourceCoefficient 4 67 3 2) v444_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v444_upper : Scalar.QComplex := ((999998880765206690614313768804 : Int)/10^30,(1496151173488912121756582059 : Int)/10^30)
theorem v444_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 67 5) 1) 14) v444_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material444 : Material (4 : Basis) (67 : Basis) where
  plus := ![v444_pa,v444_pb,v444_pg]
  minus := ![(Primitive.Addresses.material444 1).one,v444_mb,v444_mg]
  upper := v444_upper
  lower := (Primitive.Addresses.material444 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v444_pa_checked.trans (by decide +kernel)
    · exact v444_pb_checked.trans (by decide +kernel)
    · exact v444_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 67 Primitive.Addresses.material444
    · exact v444_mb_checked.trans (by decide +kernel)
    · exact v444_mg_checked.trans (by decide +kernel)
  upper_error := v444_upper_checked
  lower_error := reuse_lower_error 4 67 Primitive.Addresses.material444

def v445_pa : Scalar.QComplex := ((999994966344687548615213989732 : Int)/10^30,(3172898562390068750930995832 : Int)/10^30)
theorem v445_pa_checked : Scalar.distance (sourceCoefficient 4 68 1 0) v445_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v445_pb : Scalar.QComplex := ((1369028760519831634166534 : Int)/10^30,(-431473569791555784490617945 : Int)/10^30)
theorem v445_pb_checked : Scalar.distance (sourceCoefficient 4 68 1 1) v445_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v445_pg : Scalar.QComplex := ((-93085769399901146985853 : Int)/10^30,(-295353190614076786027 : Int)/10^30)
theorem v445_pg_checked : Scalar.distance (sourceCoefficient 4 68 1 2) v445_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v445_mb : Scalar.QComplex := ((996685992885945922941824 : Int)/10^30,(-431474590544387996922824853 : Int)/10^30)
theorem v445_mb_checked : Scalar.distance (sourceCoefficient 4 68 3 1) v445_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v445_mg : Scalar.QComplex := ((-93085989616316255622263 : Int)/10^30,(-215024254075894473039 : Int)/10^30)
theorem v445_mg_checked : Scalar.distance (sourceCoefficient 4 68 3 2) v445_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v445_upper : Scalar.QComplex := ((999998953104728414788653708195 : Int)/10^30,(1446993243654134352333770965 : Int)/10^30)
theorem v445_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 68 5) 1) 14) v445_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material445 : Material (4 : Basis) (68 : Basis) where
  plus := ![v445_pa,v445_pb,v445_pg]
  minus := ![(Primitive.Addresses.material445 1).one,v445_mb,v445_mg]
  upper := v445_upper
  lower := (Primitive.Addresses.material445 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v445_pa_checked.trans (by decide +kernel)
    · exact v445_pb_checked.trans (by decide +kernel)
    · exact v445_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 68 Primitive.Addresses.material445
    · exact v445_mb_checked.trans (by decide +kernel)
    · exact v445_mg_checked.trans (by decide +kernel)
  upper_error := v445_upper_checked
  lower_error := reuse_lower_error 4 68 Primitive.Addresses.material445

def v446_pa : Scalar.QComplex := ((999995034757534466362288184751 : Int)/10^30,(3151263282785894721768821551 : Int)/10^30)
theorem v446_pa_checked : Scalar.distance (sourceCoefficient 4 69 1 0) v446_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v446_pb : Scalar.QComplex := ((1359693613323665529047047 : Int)/10^30,(-431473583798163814425369938 : Int)/10^30)
theorem v446_pb_checked : Scalar.distance (sourceCoefficient 4 69 1 1) v446_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v446_pg : Scalar.QComplex := ((-93085774094937813764622 : Int)/10^30,(-293339238555524016313 : Int)/10^30)
theorem v446_pg_checked : Scalar.distance (sourceCoefficient 4 69 1 2) v446_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v446_mb : Scalar.QComplex := ((987350837078609860632464 : Int)/10^30,(-431474596495179220688195305 : Int)/10^30)
theorem v446_mb_checked : Scalar.distance (sourceCoefficient 4 69 3 1) v446_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v446_mg : Scalar.QComplex := ((-93085992573401252726855 : Int)/10^30,(-213010298715622910052 : Int)/10^30)
theorem v446_mg_checked : Scalar.distance (sourceCoefficient 4 69 3 2) v446_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v446_upper : Scalar.QComplex := ((999998984176943580065835903620 : Int)/10^30,(1425357878198800420078251718 : Int)/10^30)
theorem v446_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 69 5) 1) 14) v446_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material446 : Material (4 : Basis) (69 : Basis) where
  plus := ![v446_pa,v446_pb,v446_pg]
  minus := ![(Primitive.Addresses.material446 1).one,v446_mb,v446_mg]
  upper := v446_upper
  lower := (Primitive.Addresses.material446 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v446_pa_checked.trans (by decide +kernel)
    · exact v446_pb_checked.trans (by decide +kernel)
    · exact v446_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 69 Primitive.Addresses.material446
    · exact v446_mb_checked.trans (by decide +kernel)
    · exact v446_mg_checked.trans (by decide +kernel)
  upper_error := v446_upper_checked
  lower_error := reuse_lower_error 4 69 Primitive.Addresses.material446

def v447_pa : Scalar.QComplex := ((999995079504932953284323475762 : Int)/10^30,(3137031386967896839054553640 : Int)/10^30)
theorem v447_pa_checked : Scalar.distance (sourceCoefficient 4 70 1 0) v447_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v447_pb : Scalar.QComplex := ((1353552863615532579066048 : Int)/10^30,(-431473592865010068220119394 : Int)/10^30)
theorem v447_pb_checked : Scalar.distance (sourceCoefficient 4 70 1 1) v447_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v447_pg : Scalar.QComplex := ((-93085777155659820324098 : Int)/10^30,(-292014441473222868761 : Int)/10^30)
theorem v447_pg_checked : Scalar.distance (sourceCoefficient 4 70 1 2) v447_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v447_mb : Scalar.QComplex := ((981210081832678711686753 : Int)/10^30,(-431474600262831669463100015 : Int)/10^30)
theorem v447_mb_checked : Scalar.distance (sourceCoefficient 4 70 3 1) v447_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v447_mg : Scalar.QComplex := ((-93085994490881904259412 : Int)/10^30,(-211685499485339020600 : Int)/10^30)
theorem v447_mg_checked : Scalar.distance (sourceCoefficient 4 70 3 2) v447_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v447_upper : Scalar.QComplex := ((999999004361314346632908462134 : Int)/10^30,(1411125926347589226204389573 : Int)/10^30)
theorem v447_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 70 5) 1) 14) v447_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material447 : Material (4 : Basis) (70 : Basis) where
  plus := ![v447_pa,v447_pb,v447_pg]
  minus := ![(Primitive.Addresses.material447 1).one,v447_mb,v447_mg]
  upper := v447_upper
  lower := (Primitive.Addresses.material447 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v447_pa_checked.trans (by decide +kernel)
    · exact v447_pb_checked.trans (by decide +kernel)
    · exact v447_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 70 Primitive.Addresses.material447
    · exact v447_mb_checked.trans (by decide +kernel)
    · exact v447_mg_checked.trans (by decide +kernel)
  upper_error := v447_upper_checked
  lower_error := reuse_lower_error 4 70 Primitive.Addresses.material447

def v448_pa : Scalar.QComplex := ((999995155417191792275554158858 : Int)/10^30,(3112738689069942361428330227 : Int)/10^30)
theorem v448_pa_checked : Scalar.distance (sourceCoefficient 4 71 1 0) v448_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v448_pb : Scalar.QComplex := ((1343071099778031377527049 : Int)/10^30,(-431473608072178560309709166 : Int)/10^30)
theorem v448_pb_checked : Scalar.distance (sourceCoefficient 4 71 1 1) v448_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v448_pg : Scalar.QComplex := ((-93085782329246743872548 : Int)/10^30,(-289753119791572282115 : Int)/10^30)
theorem v448_pg_checked : Scalar.distance (sourceCoefficient 4 71 1 2) v448_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v448_mb : Scalar.QComplex := ((970728308774915723892578 : Int)/10^30,(-431474606424704388584087500 : Int)/10^30)
theorem v448_mb_checked : Scalar.distance (sourceCoefficient 4 71 3 1) v448_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v448_mg : Scalar.QComplex := ((-93085997713048136328385 : Int)/10^30,(-209424174181109338222 : Int)/10^30)
theorem v448_mg_checked : Scalar.distance (sourceCoefficient 4 71 3 2) v448_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v448_upper : Scalar.QComplex := ((999999038346467367700484356664 : Int)/10^30,(1386833133613082597057353802 : Int)/10^30)
theorem v448_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 71 5) 1) 14) v448_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material448 : Material (4 : Basis) (71 : Basis) where
  plus := ![v448_pa,v448_pb,v448_pg]
  minus := ![(Primitive.Addresses.material448 1).one,v448_mb,v448_mg]
  upper := v448_upper
  lower := (Primitive.Addresses.material448 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v448_pa_checked.trans (by decide +kernel)
    · exact v448_pb_checked.trans (by decide +kernel)
    · exact v448_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 71 Primitive.Addresses.material448
    · exact v448_mb_checked.trans (by decide +kernel)
    · exact v448_mg_checked.trans (by decide +kernel)
  upper_error := v448_upper_checked
  lower_error := reuse_lower_error 4 71 Primitive.Addresses.material448

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
