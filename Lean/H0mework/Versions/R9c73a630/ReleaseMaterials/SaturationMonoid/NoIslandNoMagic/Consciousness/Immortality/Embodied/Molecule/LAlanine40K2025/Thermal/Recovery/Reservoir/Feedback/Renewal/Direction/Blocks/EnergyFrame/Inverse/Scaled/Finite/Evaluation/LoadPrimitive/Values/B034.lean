import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B022
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B023

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v545_pa : Scalar.QComplex := ((999995457315781337032039164459 : Int)/10^30,(3014191069150399004295628532 : Int)/10^30)
theorem v545_pa_checked : Scalar.distance (sourceCoefficient 5 76 1 0) v545_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v545_pb : Scalar.QComplex := ((1300550089553542537281053 : Int)/10^30,(-431473702804034791734759652 : Int)/10^30)
theorem v545_pb_checked : Scalar.distance (sourceCoefficient 5 76 1 1) v545_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v545_pg : Scalar.QComplex := ((-93085806599241553155576 : Int)/10^30,(-280579681500986396335 : Int)/10^30)
theorem v545_pg_checked : Scalar.distance (sourceCoefficient 5 76 1 2) v545_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v545_mb : Scalar.QComplex := ((928207232633616933094837 : Int)/10^30,(-431474664462808598485311725 : Int)/10^30)
theorem v545_mb_checked : Scalar.distance (sourceCoefficient 5 76 3 1) v545_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v545_mg : Scalar.QComplex := ((-93086014066769820331056 : Int)/10^30,(-200250718362301334446 : Int)/10^30)
theorem v545_mg_checked : Scalar.distance (sourceCoefficient 5 76 3 2) v545_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v545_upper : Scalar.QComplex := ((999999170160355459081831109650 : Int)/10^30,(1288285139419065365314155878 : Int)/10^30)
theorem v545_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 76 5) 1) 14) v545_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material545 : Material (5 : Basis) (76 : Basis) where
  plus := ![v545_pa,v545_pb,v545_pg]
  minus := ![(Primitive.Addresses.material545 1).one,v545_mb,v545_mg]
  upper := v545_upper
  lower := (Primitive.Addresses.material545 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v545_pa_checked.trans (by decide +kernel)
    · exact v545_pb_checked.trans (by decide +kernel)
    · exact v545_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 76 Primitive.Addresses.material545
    · exact v545_mb_checked.trans (by decide +kernel)
    · exact v545_mg_checked.trans (by decide +kernel)
  upper_error := v545_upper_checked
  lower_error := reuse_lower_error 5 76 Primitive.Addresses.material545

def v546_pa : Scalar.QComplex := ((999995465985558638494064335336 : Int)/10^30,(3011313388778401024402889756 : Int)/10^30)
theorem v546_pa_checked : Scalar.distance (sourceCoefficient 5 77 1 0) v546_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v546_pb : Scalar.QComplex := ((1299308434170364241562001 : Int)/10^30,(-431473704440389635323354652 : Int)/10^30)
theorem v546_pb_checked : Scalar.distance (sourceCoefficient 5 77 1 1) v546_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v546_pg : Scalar.QComplex := ((-93085807179273259199547 : Int)/10^30,(-280311808401977547929 : Int)/10^30)
theorem v546_pg_checked : Scalar.distance (sourceCoefficient 5 77 1 2) v546_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v546_mb : Scalar.QComplex := ((926965576300663151656782 : Int)/10^30,(-431474665027670159183877207 : Int)/10^30)
theorem v546_mb_checked : Scalar.distance (sourceCoefficient 5 77 3 1) v546_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v546_mg : Scalar.QComplex := ((-93086014415638890514601 : Int)/10^30,(-199982844862492644549 : Int)/10^30)
theorem v546_mg_checked : Scalar.distance (sourceCoefficient 5 77 3 2) v546_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v546_upper : Scalar.QComplex := ((999999173863504586984526109186 : Int)/10^30,(1285407448369785157159580574 : Int)/10^30)
theorem v546_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 77 5) 1) 14) v546_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material546 : Material (5 : Basis) (77 : Basis) where
  plus := ![v546_pa,v546_pb,v546_pg]
  minus := ![(Primitive.Addresses.material546 1).one,v546_mb,v546_mg]
  upper := v546_upper
  lower := (Primitive.Addresses.material546 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v546_pa_checked.trans (by decide +kernel)
    · exact v546_pb_checked.trans (by decide +kernel)
    · exact v546_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 77 Primitive.Addresses.material546
    · exact v546_mb_checked.trans (by decide +kernel)
    · exact v546_mg_checked.trans (by decide +kernel)
  upper_error := v546_upper_checked
  lower_error := reuse_lower_error 5 77 Primitive.Addresses.material546

def v547_pa : Scalar.QComplex := ((999995517930406157796255091710 : Int)/10^30,(2994013877512354391425025439 : Int)/10^30)
theorem v547_pa_checked : Scalar.distance (sourceCoefficient 5 78 1 0) v547_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v547_pb : Scalar.QComplex := ((1291844078163159864257897 : Int)/10^30,(-431473714177120259153943335 : Int)/10^30)
theorem v547_pb_checked : Scalar.distance (sourceCoefficient 5 78 1 1) v547_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v547_pg : Scalar.QComplex := ((-93085810647247439358705 : Int)/10^30,(-278701458036676934836 : Int)/10^30)
theorem v547_pg_checked : Scalar.distance (sourceCoefficient 5 78 1 2) v547_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v547_mb : Scalar.QComplex := ((919501214670419651459598 : Int)/10^30,(-431474668322994105482184220 : Int)/10^30)
theorem v547_mb_checked : Scalar.distance (sourceCoefficient 5 78 3 1) v547_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v547_mg : Scalar.QComplex := ((-93086016493951941622154 : Int)/10^30,(-198372492104093543386 : Int)/10^30)
theorem v547_mg_checked : Scalar.distance (sourceCoefficient 5 78 3 2) v547_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v547_upper : Scalar.QComplex := ((999999195950887694744299165658 : Int)/10^30,(1268107873217233993054705264 : Int)/10^30)
theorem v547_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 78 5) 1) 14) v547_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material547 : Material (5 : Basis) (78 : Basis) where
  plus := ![v547_pa,v547_pb,v547_pg]
  minus := ![(Primitive.Addresses.material547 1).one,v547_mb,v547_mg]
  upper := v547_upper
  lower := (Primitive.Addresses.material547 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v547_pa_checked.trans (by decide +kernel)
    · exact v547_pb_checked.trans (by decide +kernel)
    · exact v547_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 78 Primitive.Addresses.material547
    · exact v547_mb_checked.trans (by decide +kernel)
    · exact v547_mg_checked.trans (by decide +kernel)
  upper_error := v547_upper_checked
  lower_error := reuse_lower_error 5 78 Primitive.Addresses.material547

def v548_pa : Scalar.QComplex := ((999995534612712430104396270253 : Int)/10^30,(2988436821392776778645454304 : Int)/10^30)
theorem v548_pa_checked : Scalar.distance (sourceCoefficient 5 79 1 0) v548_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v548_pb : Scalar.QComplex := ((1289437702019607996572843 : Int)/10^30,(-431473717279369724421228633 : Int)/10^30)
theorem v548_pb_checked : Scalar.distance (sourceCoefficient 5 79 1 1) v548_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v548_pg : Scalar.QComplex := ((-93085811758332968941564 : Int)/10^30,(-278182309599587856076 : Int)/10^30)
theorem v548_pg_checked : Scalar.distance (sourceCoefficient 5 79 1 2) v548_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v548_mb : Scalar.QComplex := ((917094836745770030445223 : Int)/10^30,(-431474669348648182913234090 : Int)/10^30)
theorem v548_mb_checked : Scalar.distance (sourceCoefficient 5 79 3 1) v548_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v548_mg : Scalar.QComplex := ((-93086017157035337866858 : Int)/10^30,(-197853342901490383415 : Int)/10^30)
theorem v548_mg_checked : Scalar.distance (sourceCoefficient 5 79 3 2) v548_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v548_upper : Scalar.QComplex := ((999999203007676204904859734607 : Int)/10^30,(1262530796611879124353104181 : Int)/10^30)
theorem v548_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 79 5) 1) 14) v548_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material548 : Material (5 : Basis) (79 : Basis) where
  plus := ![v548_pa,v548_pb,v548_pg]
  minus := ![(Primitive.Addresses.material548 1).one,v548_mb,v548_mg]
  upper := v548_upper
  lower := (Primitive.Addresses.material548 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v548_pa_checked.trans (by decide +kernel)
    · exact v548_pb_checked.trans (by decide +kernel)
    · exact v548_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 79 Primitive.Addresses.material548
    · exact v548_mb_checked.trans (by decide +kernel)
    · exact v548_mg_checked.trans (by decide +kernel)
  upper_error := v548_upper_checked
  lower_error := reuse_lower_error 5 79 Primitive.Addresses.material548

def v549_pa : Scalar.QComplex := ((999995560609881327022018943449 : Int)/10^30,(2979724908303001414978904304 : Int)/10^30)
theorem v549_pa_checked : Scalar.distance (sourceCoefficient 5 80 1 0) v549_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v549_pb : Scalar.QComplex := ((1285678704617870522442063 : Int)/10^30,(-431473722089581668615525402 : Int)/10^30)
theorem v549_pb_checked : Scalar.distance (sourceCoefficient 5 80 1 1) v549_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v549_pg : Scalar.QComplex := ((-93085813487198798512894 : Int)/10^30,(-277371348417077098049 : Int)/10^30)
theorem v549_pg_checked : Scalar.distance (sourceCoefficient 5 80 1 2) v549_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v549_mb : Scalar.QComplex := ((913335836592682819713482 : Int)/10^30,(-431474670915012877304647824 : Int)/10^30)
theorem v549_mb_checked : Scalar.distance (sourceCoefficient 5 80 3 1) v549_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v549_mg : Scalar.QComplex := ((-93086018186077547531455 : Int)/10^30,(-197042380529004190700 : Int)/10^30)
theorem v549_mg_checked : Scalar.distance (sourceCoefficient 5 80 3 2) v549_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v549_upper : Scalar.QComplex := ((999999213968834727722692967932 : Int)/10^30,(1253818851628719863366739322 : Int)/10^30)
theorem v549_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 80 5) 1) 14) v549_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material549 : Material (5 : Basis) (80 : Basis) where
  plus := ![v549_pa,v549_pb,v549_pg]
  minus := ![(Primitive.Addresses.material549 1).one,v549_mb,v549_mg]
  upper := v549_upper
  lower := (Primitive.Addresses.material549 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v549_pa_checked.trans (by decide +kernel)
    · exact v549_pb_checked.trans (by decide +kernel)
    · exact v549_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 80 Primitive.Addresses.material549
    · exact v549_mb_checked.trans (by decide +kernel)
    · exact v549_mg_checked.trans (by decide +kernel)
  upper_error := v549_upper_checked
  lower_error := reuse_lower_error 5 80 Primitive.Addresses.material549

def v550_pa : Scalar.QComplex := ((999995638430379545894324384253 : Int)/10^30,(2953492884301341478865951734 : Int)/10^30)
theorem v550_pa_checked : Scalar.distance (sourceCoefficient 5 81 1 0) v550_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v550_pb : Scalar.QComplex := ((1274360168164212683112454 : Int)/10^30,(-431473736309701827439945819 : Int)/10^30)
theorem v550_pb_checked : Scalar.distance (sourceCoefficient 5 81 1 1) v550_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v550_pg : Scalar.QComplex := ((-93085818643128781658610 : Int)/10^30,(-274929502116010206139 : Int)/10^30)
theorem v550_pg_checked : Scalar.distance (sourceCoefficient 5 81 1 2) v550_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v550_mb : Scalar.QComplex := ((902017292082110138122742 : Int)/10^30,(-431474675367740549780122801 : Int)/10^30)
theorem v550_mb_checked : Scalar.distance (sourceCoefficient 5 81 3 1) v550_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v550_mg : Scalar.QComplex := ((-93086021234802229742948 : Int)/10^30,(-194600530687812913577 : Int)/10^30)
theorem v550_mg_checked : Scalar.distance (sourceCoefficient 5 81 3 2) v550_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v550_upper : Scalar.QComplex := ((999999246515123365867128390871 : Int)/10^30,(1227586732385458142404901240 : Int)/10^30)
theorem v550_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 81 5) 1) 14) v550_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material550 : Material (5 : Basis) (81 : Basis) where
  plus := ![v550_pa,v550_pb,v550_pg]
  minus := ![(Primitive.Addresses.material550 1).one,v550_mb,v550_mg]
  upper := v550_upper
  lower := (Primitive.Addresses.material550 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v550_pa_checked.trans (by decide +kernel)
    · exact v550_pb_checked.trans (by decide +kernel)
    · exact v550_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 81 Primitive.Addresses.material550
    · exact v550_mb_checked.trans (by decide +kernel)
    · exact v550_mg_checked.trans (by decide +kernel)
  upper_error := v550_upper_checked
  lower_error := reuse_lower_error 5 81 Primitive.Addresses.material550

def v551_pa : Scalar.QComplex := ((999995667739459328838000504261 : Int)/10^30,(2943552668606582235992565471 : Int)/10^30)
theorem v551_pa_checked : Scalar.distance (sourceCoefficient 5 82 1 0) v551_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v551_pb : Scalar.QComplex := ((1270071185784220103131178 : Int)/10^30,(-431473741594765234135543188 : Int)/10^30)
theorem v551_pb_checked : Scalar.distance (sourceCoefficient 5 82 1 1) v551_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v551_pg : Scalar.QComplex := ((-93085820577363428441342 : Int)/10^30,(-274004202627526646678 : Int)/10^30)
theorem v551_pg_checked : Scalar.distance (sourceCoefficient 5 82 1 2) v551_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v551_mb : Scalar.QComplex := ((897728306738330024832297 : Int)/10^30,(-431474676951603363267117535 : Int)/10^30)
theorem v551_mb_checked : Scalar.distance (sourceCoefficient 5 82 3 1) v551_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v551_mg : Scalar.QComplex := ((-93086022370544371702361 : Int)/10^30,(-193675229874703256476 : Int)/10^30)
theorem v551_mg_checked : Scalar.distance (sourceCoefficient 5 82 3 2) v551_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v551_upper : Scalar.QComplex := ((999999258668248976548494156598 : Int)/10^30,(1217646480910669710703221349 : Int)/10^30)
theorem v551_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 82 5) 1) 14) v551_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material551 : Material (5 : Basis) (82 : Basis) where
  plus := ![v551_pa,v551_pb,v551_pg]
  minus := ![(Primitive.Addresses.material551 1).one,v551_mb,v551_mg]
  upper := v551_upper
  lower := (Primitive.Addresses.material551 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v551_pa_checked.trans (by decide +kernel)
    · exact v551_pb_checked.trans (by decide +kernel)
    · exact v551_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 82 Primitive.Addresses.material551
    · exact v551_mb_checked.trans (by decide +kernel)
    · exact v551_mg_checked.trans (by decide +kernel)
  upper_error := v551_upper_checked
  lower_error := reuse_lower_error 5 82 Primitive.Addresses.material551

def v552_pa : Scalar.QComplex := ((999995707587356011285809029989 : Int)/10^30,(2929984106300087442123812758 : Int)/10^30)
theorem v552_pa_checked : Scalar.distance (sourceCoefficient 5 83 1 0) v552_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v552_pb : Scalar.QComplex := ((1264216652566687163425878 : Int)/10^30,(-431473748717209966836056332 : Int)/10^30)
theorem v552_pb_checked : Scalar.distance (sourceCoefficient 5 83 1 1) v552_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v552_pg : Scalar.QComplex := ((-93085823200305429642827 : Int)/10^30,(-272741153216329451617 : Int)/10^30)
theorem v552_pg_checked : Scalar.distance (sourceCoefficient 5 83 1 2) v552_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v552_mb : Scalar.QComplex := ((891873769554358346082743 : Int)/10^30,(-431474679021846955612933749 : Int)/10^30)
theorem v552_mb_checked : Scalar.distance (sourceCoefficient 5 83 3 1) v552_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v552_mg : Scalar.QComplex := ((-93086023903530640033272 : Int)/10^30,(-192412178670316267299 : Int)/10^30)
theorem v552_mg_checked : Scalar.distance (sourceCoefficient 5 83 3 2) v552_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v552_upper : Scalar.QComplex := ((999999275097978699581987658275 : Int)/10^30,(1204077870039099896109805780 : Int)/10^30)
theorem v552_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 83 5) 1) 14) v552_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material552 : Material (5 : Basis) (83 : Basis) where
  plus := ![v552_pa,v552_pb,v552_pg]
  minus := ![(Primitive.Addresses.material552 1).one,v552_mb,v552_mg]
  upper := v552_upper
  lower := (Primitive.Addresses.material552 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v552_pa_checked.trans (by decide +kernel)
    · exact v552_pb_checked.trans (by decide +kernel)
    · exact v552_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 83 Primitive.Addresses.material552
    · exact v552_mb_checked.trans (by decide +kernel)
    · exact v552_mg_checked.trans (by decide +kernel)
  upper_error := v552_upper_checked
  lower_error := reuse_lower_error 5 83 Primitive.Addresses.material552

def v553_pa : Scalar.QComplex := ((999995809926861037016102757395 : Int)/10^30,(2894845198143254418565238102 : Int)/10^30)
theorem v553_pa_checked : Scalar.distance (sourceCoefficient 5 84 1 0) v553_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v553_pb : Scalar.QComplex := ((1249054995201471983965782 : Int)/10^30,(-431473766670088097459918093 : Int)/10^30)
theorem v553_pb_checked : Scalar.distance (sourceCoefficient 5 84 1 1) v553_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v553_pg : Scalar.QComplex := ((-93085829900078430824464 : Int)/10^30,(-269470196801255189743 : Int)/10^30)
theorem v553_pg_checked : Scalar.distance (sourceCoefficient 5 84 1 2) v553_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v553_mb : Scalar.QComplex := ((876712102341995866552058 : Int)/10^30,(-431474683890890951078014758 : Int)/10^30)
theorem v553_mb_checked : Scalar.distance (sourceCoefficient 5 84 3 1) v553_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v553_mg : Scalar.QComplex := ((-93086027780613078782356 : Int)/10^30,(-189141217691566215405 : Int)/10^30)
theorem v553_mg_checked : Scalar.distance (sourceCoefficient 5 84 3 2) v553_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v553_upper : Scalar.QComplex := ((999999316790763600793831357260 : Int)/10^30,(1168938837588841359007890418 : Int)/10^30)
theorem v553_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 84 5) 1) 14) v553_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material553 : Material (5 : Basis) (84 : Basis) where
  plus := ![v553_pa,v553_pb,v553_pg]
  minus := ![(Primitive.Addresses.material553 1).one,v553_mb,v553_mg]
  upper := v553_upper
  lower := (Primitive.Addresses.material553 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v553_pa_checked.trans (by decide +kernel)
    · exact v553_pb_checked.trans (by decide +kernel)
    · exact v553_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 84 Primitive.Addresses.material553
    · exact v553_mb_checked.trans (by decide +kernel)
    · exact v553_mg_checked.trans (by decide +kernel)
  upper_error := v553_upper_checked
  lower_error := reuse_lower_error 5 84 Primitive.Addresses.material553

def v554_pa : Scalar.QComplex := ((999996035659132065096871449806 : Int)/10^30,(2815788702987368879865695830 : Int)/10^30)
theorem v554_pa_checked : Scalar.distance (sourceCoefficient 5 85 1 0) v554_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v554_pb : Scalar.QComplex := ((1214943880696570831094853 : Int)/10^30,(-431473804464063984033547906 : Int)/10^30)
theorem v554_pb_checked : Scalar.distance (sourceCoefficient 5 85 1 1) v554_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v554_pg : Scalar.QComplex := ((-93085844483191158204908 : Int)/10^30,(-262111108401587734308 : Int)/10^30)
theorem v554_pg_checked : Scalar.distance (sourceCoefficient 5 85 1 2) v554_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v554_mb : Scalar.QComplex := ((842600967923722586175730 : Int)/10^30,(-431474692248497255064340173 : Int)/10^30)
theorem v554_mb_checked : Scalar.distance (sourceCoefficient 5 85 3 1) v554_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v554_mg : Scalar.QComplex := ((-93086036013158528328289 : Int)/10^30,(-181782119447454213408 : Int)/10^30)
theorem v554_mg_checked : Scalar.distance (sourceCoefficient 5 85 3 2) v554_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v554_upper : Scalar.QComplex := ((999999406078359737331188332200 : Int)/10^30,(1089882070584897203921573095 : Int)/10^30)
theorem v554_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 85 5) 1) 14) v554_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material554 : Material (5 : Basis) (85 : Basis) where
  plus := ![v554_pa,v554_pb,v554_pg]
  minus := ![(Primitive.Addresses.material554 1).one,v554_mb,v554_mg]
  upper := v554_upper
  lower := (Primitive.Addresses.material554 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v554_pa_checked.trans (by decide +kernel)
    · exact v554_pb_checked.trans (by decide +kernel)
    · exact v554_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 85 Primitive.Addresses.material554
    · exact v554_mb_checked.trans (by decide +kernel)
    · exact v554_mg_checked.trans (by decide +kernel)
  upper_error := v554_upper_checked
  lower_error := reuse_lower_error 5 85 Primitive.Addresses.material554

def v555_pa : Scalar.QComplex := ((999996076620052659069573959489 : Int)/10^30,(2801204116406308877313161090 : Int)/10^30)
theorem v555_pa_checked : Scalar.distance (sourceCoefficient 5 86 1 0) v555_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v555_pb : Scalar.QComplex := ((1208650957613667454226373 : Int)/10^30,(-431473811043559589927249986 : Int)/10^30)
theorem v555_pb_checked : Scalar.distance (sourceCoefficient 5 86 1 1) v555_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v555_pg : Scalar.QComplex := ((-93085847099369131599691 : Int)/10^30,(-260753481108900060470 : Int)/10^30)
theorem v555_pg_checked : Scalar.distance (sourceCoefficient 5 86 1 2) v555_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v555_mb : Scalar.QComplex := ((836308041506153695460391 : Int)/10^30,(-431474693397481213300023650 : Int)/10^30)
theorem v555_mb_checked : Scalar.distance (sourceCoefficient 5 86 3 1) v555_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v555_mg : Scalar.QComplex := ((-93086037457764319274428 : Int)/10^30,(-180424490402629464511 : Int)/10^30)
theorem v555_mg_checked : Scalar.distance (sourceCoefficient 5 86 3 2) v555_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v555_upper : Scalar.QComplex := ((999999421867545989273826962354 : Int)/10^30,(1075297435031032688462572121 : Int)/10^30)
theorem v555_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 86 5) 1) 14) v555_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material555 : Material (5 : Basis) (86 : Basis) where
  plus := ![v555_pa,v555_pb,v555_pg]
  minus := ![(Primitive.Addresses.material555 1).one,v555_mb,v555_mg]
  upper := v555_upper
  lower := (Primitive.Addresses.material555 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v555_pa_checked.trans (by decide +kernel)
    · exact v555_pb_checked.trans (by decide +kernel)
    · exact v555_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 86 Primitive.Addresses.material555
    · exact v555_mb_checked.trans (by decide +kernel)
    · exact v555_mg_checked.trans (by decide +kernel)
  upper_error := v555_upper_checked
  lower_error := reuse_lower_error 5 86 Primitive.Addresses.material555

def v556_pa : Scalar.QComplex := ((999996079324867234486102406173 : Int)/10^30,(2800238363753616441283589622 : Int)/10^30)
theorem v556_pa_checked : Scalar.distance (sourceCoefficient 5 87 1 0) v556_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v556_pb : Scalar.QComplex := ((1208234256941062071674048 : Int)/10^30,(-431473811474916419150095693 : Int)/10^30)
theorem v556_pb_checked : Scalar.distance (sourceCoefficient 5 87 1 1) v556_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v556_pg : Scalar.QComplex := ((-93085847271790020304433 : Int)/10^30,(-260663582630202763297 : Int)/10^30)
theorem v556_pg_checked : Scalar.distance (sourceCoefficient 5 87 1 2) v556_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v556_mb : Scalar.QComplex := ((835891340616463501451675 : Int)/10^30,(-431474693469243968952174452 : Int)/10^30)
theorem v556_mb_checked : Scalar.distance (sourceCoefficient 5 87 3 1) v556_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v556_mg : Scalar.QComplex := ((-93086037552606805540405 : Int)/10^30,(-180334591808614018117 : Int)/10^30)
theorem v556_mg_checked : Scalar.distance (sourceCoefficient 5 87 3 2) v556_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v556_upper : Scalar.QComplex := ((999999422905555070035892354858 : Int)/10^30,(1074331679148450805035262109 : Int)/10^30)
theorem v556_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 87 5) 1) 14) v556_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material556 : Material (5 : Basis) (87 : Basis) where
  plus := ![v556_pa,v556_pb,v556_pg]
  minus := ![(Primitive.Addresses.material556 1).one,v556_mb,v556_mg]
  upper := v556_upper
  lower := (Primitive.Addresses.material556 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v556_pa_checked.trans (by decide +kernel)
    · exact v556_pb_checked.trans (by decide +kernel)
    · exact v556_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 87 Primitive.Addresses.material556
    · exact v556_mb_checked.trans (by decide +kernel)
    · exact v556_mg_checked.trans (by decide +kernel)
  upper_error := v556_upper_checked
  lower_error := reuse_lower_error 5 87 Primitive.Addresses.material556

def v557_pa : Scalar.QComplex := ((999996112185388500625711122284 : Int)/10^30,(2788478816110370810454207224 : Int)/10^30)
theorem v557_pa_checked : Scalar.distance (sourceCoefficient 5 88 1 0) v557_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v557_pb : Scalar.QComplex := ((1203160275194597599405170 : Int)/10^30,(-431473816684314236297655255 : Int)/10^30)
theorem v557_pb_checked : Scalar.distance (sourceCoefficient 5 88 1 1) v557_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v557_pg : Scalar.QComplex := ((-93085849363157967153020 : Int)/10^30,(-259568928184678730530 : Int)/10^30)
theorem v557_pg_checked : Scalar.distance (sourceCoefficient 5 88 1 2) v557_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v557_mb : Scalar.QComplex := ((830817356263798632182792 : Int)/10^30,(-431474694300022122858669822 : Int)/10^30)
theorem v557_mb_checked : Scalar.distance (sourceCoefficient 5 88 3 1) v557_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v557_mg : Scalar.QComplex := ((-93086038699336488595957 : Int)/10^30,(-179239935965923517184 : Int)/10^30)
theorem v557_mg_checked : Scalar.distance (sourceCoefficient 5 88 3 2) v557_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v557_upper : Scalar.QComplex := ((999999435470114979875856023826 : Int)/10^30,(1062572092305391393163230671 : Int)/10^30)
theorem v557_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 88 5) 1) 14) v557_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material557 : Material (5 : Basis) (88 : Basis) where
  plus := ![v557_pa,v557_pb,v557_pg]
  minus := ![(Primitive.Addresses.material557 1).one,v557_mb,v557_mg]
  upper := v557_upper
  lower := (Primitive.Addresses.material557 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v557_pa_checked.trans (by decide +kernel)
    · exact v557_pb_checked.trans (by decide +kernel)
    · exact v557_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 88 Primitive.Addresses.material557
    · exact v557_mb_checked.trans (by decide +kernel)
    · exact v557_mg_checked.trans (by decide +kernel)
  upper_error := v557_upper_checked
  lower_error := reuse_lower_error 5 88 Primitive.Addresses.material557

def v558_pa : Scalar.QComplex := ((999996156921140012504585264801 : Int)/10^30,(2772389393775677166407579388 : Int)/10^30)
theorem v558_pa_checked : Scalar.distance (sourceCoefficient 5 89 1 0) v558_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v558_pb : Scalar.QComplex := ((1196218049630679745473195 : Int)/10^30,(-431473823682926232217716529 : Int)/10^30)
theorem v558_pb_checked : Scalar.distance (sourceCoefficient 5 89 1 1) v558_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v558_pg : Scalar.QComplex := ((-93085852200238401086878 : Int)/10^30,(-258071221138565554091 : Int)/10^30)
theorem v558_pg_checked : Scalar.distance (sourceCoefficient 5 89 1 2) v558_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v558_mb : Scalar.QComplex := ((823875127245301684383721 : Int)/10^30,(-431474695307803517447207427 : Int)/10^30)
theorem v558_mb_checked : Scalar.distance (sourceCoefficient 5 89 3 1) v558_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v558_mg : Scalar.QComplex := ((-93086040243962139580775 : Int)/10^30,(-177742227029202485481 : Int)/10^30)
theorem v558_mg_checked : Scalar.distance (sourceCoefficient 5 89 3 2) v558_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v558_upper : Scalar.QComplex := ((999999452436916534418924052167 : Int)/10^30,(1046482616724153606502126429 : Int)/10^30)
theorem v558_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 89 5) 1) 14) v558_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material558 : Material (5 : Basis) (89 : Basis) where
  plus := ![v558_pa,v558_pb,v558_pg]
  minus := ![(Primitive.Addresses.material558 1).one,v558_mb,v558_mg]
  upper := v558_upper
  lower := (Primitive.Addresses.material558 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v558_pa_checked.trans (by decide +kernel)
    · exact v558_pb_checked.trans (by decide +kernel)
    · exact v558_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 89 Primitive.Addresses.material558
    · exact v558_mb_checked.trans (by decide +kernel)
    · exact v558_mg_checked.trans (by decide +kernel)
  upper_error := v558_upper_checked
  lower_error := reuse_lower_error 5 89 Primitive.Addresses.material558

def v559_pa : Scalar.QComplex := ((999996229222601850595032496219 : Int)/10^30,(2746186551845417427524332524 : Int)/10^30)
theorem v559_pa_checked : Scalar.distance (sourceCoefficient 5 90 1 0) v559_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v559_pb : Scalar.QComplex := ((1184912110536172624733451 : Int)/10^30,(-431473834761923980449868773 : Int)/10^30)
theorem v559_pb_checked : Scalar.distance (sourceCoefficient 5 90 1 1) v559_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v559_pg : Scalar.QComplex := ((-93085856760463516010275 : Int)/10^30,(-255632091934308249295 : Int)/10^30)
theorem v559_pg_checked : Scalar.distance (sourceCoefficient 5 90 1 2) v559_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v559_mb : Scalar.QComplex := ((812569182799836318282681 : Int)/10^30,(-431474696630280902496919616 : Int)/10^30)
theorem v559_mb_checked : Scalar.distance (sourceCoefficient 5 90 3 1) v559_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v559_mg : Scalar.QComplex := ((-93086042699326907551272 : Int)/10^30,(-175303094797875567878 : Int)/10^30)
theorem v559_mg_checked : Scalar.distance (sourceCoefficient 5 90 3 2) v559_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v559_upper : Scalar.QComplex := ((999999479514542619597782051146 : Int)/10^30,(1020279689034184925546452728 : Int)/10^30)
theorem v559_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 90 5) 1) 14) v559_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material559 : Material (5 : Basis) (90 : Basis) where
  plus := ![v559_pa,v559_pb,v559_pg]
  minus := ![(Primitive.Addresses.material559 1).one,v559_mb,v559_mg]
  upper := v559_upper
  lower := (Primitive.Addresses.material559 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v559_pa_checked.trans (by decide +kernel)
    · exact v559_pb_checked.trans (by decide +kernel)
    · exact v559_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 90 Primitive.Addresses.material559
    · exact v559_mb_checked.trans (by decide +kernel)
    · exact v559_mg_checked.trans (by decide +kernel)
  upper_error := v559_upper_checked
  lower_error := reuse_lower_error 5 90 Primitive.Addresses.material559

def v560_pa : Scalar.QComplex := ((999996269650312289310188663182 : Int)/10^30,(2731425536219610549065395949 : Int)/10^30)
theorem v560_pa_checked : Scalar.distance (sourceCoefficient 5 91 1 0) v560_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v560_pb : Scalar.QComplex := ((1178543063429359285325331 : Int)/10^30,(-431473840829192006544736578 : Int)/10^30)
theorem v560_pb_checked : Scalar.distance (sourceCoefficient 5 91 1 1) v560_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v560_pg : Scalar.QComplex := ((-93085859296570441935741 : Int)/10^30,(-254258041615004275459 : Int)/10^30)
theorem v560_pg_checked : Scalar.distance (sourceCoefficient 5 91 1 2) v560_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v560_mb : Scalar.QComplex := ((806200132828731249661734 : Int)/10^30,(-431474697201345867523974111 : Int)/10^30)
theorem v560_mb_checked : Scalar.distance (sourceCoefficient 5 91 3 1) v560_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v560_mg : Scalar.QComplex := ((-93086044049689348537999 : Int)/10^30,(-173929042801647270063 : Int)/10^30)
theorem v560_mg_checked : Scalar.distance (sourceCoefficient 5 91 3 2) v560_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v560_upper : Scalar.QComplex := ((999999494466018984721568707530 : Int)/10^30,(1005518625618616227047191860 : Int)/10^30)
theorem v560_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 91 5) 1) 14) v560_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material560 : Material (5 : Basis) (91 : Basis) where
  plus := ![v560_pa,v560_pb,v560_pg]
  minus := ![(Primitive.Addresses.material560 1).one,v560_mb,v560_mg]
  upper := v560_upper
  lower := (Primitive.Addresses.material560 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v560_pa_checked.trans (by decide +kernel)
    · exact v560_pb_checked.trans (by decide +kernel)
    · exact v560_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 91 Primitive.Addresses.material560
    · exact v560_mb_checked.trans (by decide +kernel)
    · exact v560_mg_checked.trans (by decide +kernel)
  upper_error := v560_upper_checked
  lower_error := reuse_lower_error 5 91 Primitive.Addresses.material560

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
