import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B058
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B059

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1409_pa : Scalar.QComplex := ((999999420254975073809050053529 : Int)/10^30,(-1076796040923297587707834515 : Int)/10^30)
theorem v1409_pa_checked : Scalar.distance (sourceCoefficient 15 75 1 0) v1409_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1409_pb : Scalar.QComplex := ((-464613213901949737310532 : Int)/10^30,(-431477203562495086336703424 : Int)/10^30)
theorem v1409_pb_checked : Scalar.distance (sourceCoefficient 15 75 1 1) v1409_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1409_pg : Scalar.QComplex := ((-93086368671919773739971 : Int)/10^30,(100235091360645230560 : Int)/10^30)
theorem v1409_pg_checked : Scalar.distance (sourceCoefficient 15 75 1 2) v1409_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1409_mb : Scalar.QComplex := ((-836958434567788442886484 : Int)/10^30,(-431476641963534522638854609 : Int)/10^30)
theorem v1409_mb_checked : Scalar.distance (sourceCoefficient 15 75 3 1) v1409_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1409_mg : Scalar.QComplex := ((-93086247513241036666229 : Int)/10^30,(180564397747992751832 : Int)/10^30)
theorem v1409_mg_checked : Scalar.distance (sourceCoefficient 15 75 3 2) v1409_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1409_upper : Scalar.QComplex := ((999996072421026327755077551578 : Int)/10^30,(-2802702717283425229842480845 : Int)/10^30)
theorem v1409_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 75 5) 1) 14) v1409_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1409 : Material (15 : Basis) (75 : Basis) where
  plus := ![v1409_pa,v1409_pb,v1409_pg]
  minus := ![(Primitive.Addresses.material1409 1).one,v1409_mb,v1409_mg]
  upper := v1409_upper
  lower := (Primitive.Addresses.material1409 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1409_pa_checked.trans (by decide +kernel)
    · exact v1409_pb_checked.trans (by decide +kernel)
    · exact v1409_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 75 Primitive.Addresses.material1409
    · exact v1409_mb_checked.trans (by decide +kernel)
    · exact v1409_mg_checked.trans (by decide +kernel)
  upper_error := v1409_upper_checked
  lower_error := reuse_lower_error 15 75 Primitive.Addresses.material1409

def v1410_pa : Scalar.QComplex := ((999999406792946408002990313162 : Int)/10^30,(-1089226218601712501063394948 : Int)/10^30)
theorem v1410_pa_checked : Scalar.distance (sourceCoefficient 15 76 1 0) v1410_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1410_pb : Scalar.QComplex := ((-469976553419999459675966 : Int)/10^30,(-431477196013443485907011888 : Int)/10^30)
theorem v1410_pb_checked : Scalar.distance (sourceCoefficient 15 76 1 1) v1410_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1410_pg : Scalar.QComplex := ((-93086367231042120205058 : Int)/10^30,(101392171928989938920 : Int)/10^30)
theorem v1410_pg_checked : Scalar.distance (sourceCoefficient 15 76 1 2) v1410_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1410_mb : Scalar.QComplex := ((-842321765574330211449009 : Int)/10^30,(-431476629786165284834090714 : Int)/10^30)
theorem v1410_mb_checked : Scalar.distance (sourceCoefficient 15 76 3 1) v1410_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1410_mg : Scalar.QComplex := ((-93086245073855502128709 : Int)/10^30,(181721476642090963123 : Int)/10^30)
theorem v1410_mg_checked : Scalar.distance (sourceCoefficient 15 76 3 2) v1410_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1410_upper : Scalar.QComplex := ((999996037505658696025427535613 : Int)/10^30,(-2815132853214310430958463449 : Int)/10^30)
theorem v1410_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 76 5) 1) 14) v1410_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1410 : Material (15 : Basis) (76 : Basis) where
  plus := ![v1410_pa,v1410_pb,v1410_pg]
  minus := ![(Primitive.Addresses.material1410 1).one,v1410_mb,v1410_mg]
  upper := v1410_upper
  lower := (Primitive.Addresses.material1410 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1410_pa_checked.trans (by decide +kernel)
    · exact v1410_pb_checked.trans (by decide +kernel)
    · exact v1410_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 76 Primitive.Addresses.material1410
    · exact v1410_mb_checked.trans (by decide +kernel)
    · exact v1410_mg_checked.trans (by decide +kernel)
  upper_error := v1410_upper_checked
  lower_error := reuse_lower_error 15 76 Primitive.Addresses.material1410

def v1411_pa : Scalar.QComplex := ((999999403654346715515233112360 : Int)/10^30,(-1092103910322104534161319629 : Int)/10^30)
theorem v1411_pa_checked : Scalar.distance (sourceCoefficient 15 77 1 0) v1411_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1411_pb : Scalar.QComplex := ((-471218212067556005538774 : Int)/10^30,(-431477194253102463399362550 : Int)/10^30)
theorem v1411_pb_checked : Scalar.distance (sourceCoefficient 15 77 1 1) v1411_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1411_pg : Scalar.QComplex := ((-93086366895074695117501 : Int)/10^30,(101660045908315665251 : Int)/10^30)
theorem v1411_pg_checked : Scalar.distance (sourceCoefficient 15 77 1 2) v1411_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1411_mb : Scalar.QComplex := ((-843563422240465476615418 : Int)/10^30,(-431476626954329427170111741 : Int)/10^30)
theorem v1411_mb_checked : Scalar.distance (sourceCoefficient 15 77 3 1) v1411_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1411_mg : Scalar.QComplex := ((-93086244506725022575247 : Int)/10^30,(181989350231750208065 : Int)/10^30)
theorem v1411_mg_checked : Scalar.distance (sourceCoefficient 15 77 3 2) v1411_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1411_upper : Scalar.QComplex := ((999996029400428830870145685040 : Int)/10^30,(-2818010535231780346253798203 : Int)/10^30)
theorem v1411_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 77 5) 1) 14) v1411_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1411 : Material (15 : Basis) (77 : Basis) where
  plus := ![v1411_pa,v1411_pb,v1411_pg]
  minus := ![(Primitive.Addresses.material1411 1).one,v1411_mb,v1411_mg]
  upper := v1411_upper
  lower := (Primitive.Addresses.material1411 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1411_pa_checked.trans (by decide +kernel)
    · exact v1411_pb_checked.trans (by decide +kernel)
    · exact v1411_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 77 Primitive.Addresses.material1411
    · exact v1411_mb_checked.trans (by decide +kernel)
    · exact v1411_mg_checked.trans (by decide +kernel)
  upper_error := v1411_upper_checked
  lower_error := reuse_lower_error 15 77 Primitive.Addresses.material1411

def v1412_pa : Scalar.QComplex := ((999999384611759841489986877553 : Int)/10^30,(-1109403489094177087921538446 : Int)/10^30)
theorem v1412_pa_checked : Scalar.distance (sourceCoefficient 15 78 1 0) v1412_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1412_pb : Scalar.QComplex := ((-478682587492943930385046 : Int)/10^30,(-431477183570200178022927414 : Int)/10^30)
theorem v1412_pb_checked : Scalar.distance (sourceCoefficient 15 78 1 1) v1412_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1412_pg : Scalar.QComplex := ((-93086364856413372394687 : Int)/10^30,(103270401510189227946 : Int)/10^30)
theorem v1412_pg_checked : Scalar.distance (sourceCoefficient 15 78 1 2) v1412_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1412_mb : Scalar.QComplex := ((-851027785667661759558538 : Int)/10^30,(-431476609830011310406111352 : Int)/10^30)
theorem v1412_mb_checked : Scalar.distance (sourceCoefficient 15 78 3 1) v1412_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1412_mg : Scalar.QComplex := ((-93086241078400102246283 : Int)/10^30,(183599703474741879684 : Int)/10^30)
theorem v1412_mg_checked : Scalar.distance (sourceCoefficient 15 78 3 2) v1412_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1412_upper : Scalar.QComplex := ((999995980500366763470600363434 : Int)/10^30,(-2835310055372385055704269834 : Int)/10^30)
theorem v1412_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 78 5) 1) 14) v1412_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1412 : Material (15 : Basis) (78 : Basis) where
  plus := ![v1412_pa,v1412_pb,v1412_pg]
  minus := ![(Primitive.Addresses.material1412 1).one,v1412_mb,v1412_mg]
  upper := v1412_upper
  lower := (Primitive.Addresses.material1412 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1412_pa_checked.trans (by decide +kernel)
    · exact v1412_pb_checked.trans (by decide +kernel)
    · exact v1412_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 78 Primitive.Addresses.material1412
    · exact v1412_mb_checked.trans (by decide +kernel)
    · exact v1412_mg_checked.trans (by decide +kernel)
  upper_error := v1412_upper_checked
  lower_error := reuse_lower_error 15 78 Primitive.Addresses.material1412

def v1413_pa : Scalar.QComplex := ((999999378408974736543872210620 : Int)/10^30,(-1114980566714734076806035025 : Int)/10^30)
theorem v1413_pa_checked : Scalar.distance (sourceCoefficient 15 79 1 0) v1413_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1413_pb : Scalar.QComplex := ((-481088969821276332462776 : Int)/10^30,(-431477180089521752562600732 : Int)/10^30)
theorem v1413_pb_checked : Scalar.distance (sourceCoefficient 15 79 1 1) v1413_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1413_pg : Scalar.QComplex := ((-93086364192257167796093 : Int)/10^30,(103789551615150826437 : Int)/10^30)
theorem v1413_pg_checked : Scalar.distance (sourceCoefficient 15 79 1 2) v1413_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1413_mb : Scalar.QComplex := ((-853434164096319326457400 : Int)/10^30,(-431476604272734611047408620 : Int)/10^30)
theorem v1413_mb_checked : Scalar.distance (sourceCoefficient 15 79 3 1) v1413_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1413_mg : Scalar.QComplex := ((-93086239966240986014297 : Int)/10^30,(184118852813263275682 : Int)/10^30)
theorem v1413_mg_checked : Scalar.distance (sourceCoefficient 15 79 3 2) v1413_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1413_upper : Scalar.QComplex := ((999995964672060872292390288173 : Int)/10^30,(-2840887113981095679458843278 : Int)/10^30)
theorem v1413_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 79 5) 1) 14) v1413_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1413 : Material (15 : Basis) (79 : Basis) where
  plus := ![v1413_pa,v1413_pb,v1413_pg]
  minus := ![(Primitive.Addresses.material1413 1).one,v1413_mb,v1413_mg]
  upper := v1413_upper
  lower := (Primitive.Addresses.material1413 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1413_pa_checked.trans (by decide +kernel)
    · exact v1413_pb_checked.trans (by decide +kernel)
    · exact v1413_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 79 Primitive.Addresses.material1413
    · exact v1413_mb_checked.trans (by decide +kernel)
    · exact v1413_mg_checked.trans (by decide +kernel)
  upper_error := v1413_upper_checked
  lower_error := reuse_lower_error 15 79 Primitive.Addresses.material1413

def v1414_pa : Scalar.QComplex := ((999999368657368664564550749486 : Int)/10^30,(-1123692513135756705860974172 : Int)/10^30)
theorem v1414_pa_checked : Scalar.distance (sourceCoefficient 15 80 1 0) v1414_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1414_pb : Scalar.QComplex := ((-484847976810783874325798 : Int)/10^30,(-431477174616549640625020318 : Int)/10^30)
theorem v1414_pb_checked : Scalar.distance (sourceCoefficient 15 80 1 1) v1414_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1414_pg : Scalar.QComplex := ((-93086363148019929606682 : Int)/10^30,(104600515383230824787 : Int)/10^30)
theorem v1414_pg_checked : Scalar.distance (sourceCoefficient 15 80 1 2) v1414_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1414_mb : Scalar.QComplex := ((-857193164963248331932015 : Int)/10^30,(-431476595555910804392582679 : Int)/10^30)
theorem v1414_mb_checked : Scalar.distance (sourceCoefficient 15 80 3 1) v1414_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1414_mg : Scalar.QComplex := ((-93086238222178929241358 : Int)/10^30,(184929815378254694442 : Int)/10^30)
theorem v1414_mg_checked : Scalar.distance (sourceCoefficient 15 80 3 2) v1414_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1414_upper : Scalar.QComplex := ((999995939884440143105256534373 : Int)/10^30,(-2849599030596310070071477072 : Int)/10^30)
theorem v1414_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 80 5) 1) 14) v1414_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1414 : Material (15 : Basis) (80 : Basis) where
  plus := ![v1414_pa,v1414_pb,v1414_pg]
  minus := ![(Primitive.Addresses.material1414 1).one,v1414_mb,v1414_mg]
  upper := v1414_upper
  lower := (Primitive.Addresses.material1414 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1414_pa_checked.trans (by decide +kernel)
    · exact v1414_pb_checked.trans (by decide +kernel)
    · exact v1414_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 80 Primitive.Addresses.material1414
    · exact v1414_mb_checked.trans (by decide +kernel)
    · exact v1414_mg_checked.trans (by decide +kernel)
  upper_error := v1414_upper_checked
  lower_error := reuse_lower_error 15 80 Primitive.Addresses.material1414

def v1415_pa : Scalar.QComplex := ((999999338836447629844042913169 : Int)/10^30,(-1149924635618816947976233751 : Int)/10^30)
theorem v1415_pa_checked : Scalar.distance (sourceCoefficient 15 81 1 0) v1415_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1415_pb : Scalar.QComplex := ((-496166541592724264399671 : Int)/10^30,(-431477157873468533685808552 : Int)/10^30)
theorem v1415_pb_checked : Scalar.distance (sourceCoefficient 15 81 1 1) v1415_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1415_pg : Scalar.QComplex := ((-93086359953992514562076 : Int)/10^30,(107042369323690032435 : Int)/10^30)
theorem v1415_pg_checked : Scalar.distance (sourceCoefficient 15 81 1 2) v1415_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1415_mb : Scalar.QComplex := ((-868511711082244854816336 : Int)/10^30,(-431476569045424294087362112 : Int)/10^30)
theorem v1415_mb_checked : Scalar.distance (sourceCoefficient 15 81 3 1) v1415_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1415_mg : Scalar.QComplex := ((-93086232920942729881776 : Int)/10^30,(187371665653198276290 : Int)/10^30)
theorem v1415_mg_checked : Scalar.distance (sourceCoefficient 15 81 3 2) v1415_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1415_upper : Scalar.QComplex := ((999995864789299876943642262968 : Int)/10^30,(-2875831062541500942130603333 : Int)/10^30)
theorem v1415_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 81 5) 1) 14) v1415_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1415 : Material (15 : Basis) (81 : Basis) where
  plus := ![v1415_pa,v1415_pb,v1415_pg]
  minus := ![(Primitive.Addresses.material1415 1).one,v1415_mb,v1415_mg]
  upper := v1415_upper
  lower := (Primitive.Addresses.material1415 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1415_pa_checked.trans (by decide +kernel)
    · exact v1415_pb_checked.trans (by decide +kernel)
    · exact v1415_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 81 Primitive.Addresses.material1415
    · exact v1415_mb_checked.trans (by decide +kernel)
    · exact v1415_mg_checked.trans (by decide +kernel)
  upper_error := v1415_upper_checked
  lower_error := reuse_lower_error 15 81 Primitive.Addresses.material1415

def v1416_pa : Scalar.QComplex := ((999999327356494690857976552640 : Int)/10^30,(-1159864887893843785498607475 : Int)/10^30)
theorem v1416_pa_checked : Scalar.distance (sourceCoefficient 15 82 1 0) v1416_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1416_pb : Scalar.QComplex := ((-500455534495070464214859 : Int)/10^30,(-431477151425511098952757110 : Int)/10^30)
theorem v1416_pb_checked : Scalar.distance (sourceCoefficient 15 82 1 1) v1416_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1416_pg : Scalar.QComplex := ((-93086358724141388214823 : Int)/10^30,(107967671649775497246 : Int)/10^30)
theorem v1416_pg_checked : Scalar.distance (sourceCoefficient 15 82 1 2) v1416_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1416_mb : Scalar.QComplex := ((-872800696823306119476866 : Int)/10^30,(-431476558896261554568328139 : Int)/10^30)
theorem v1416_mb_checked : Scalar.distance (sourceCoefficient 15 82 3 1) v1416_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1416_mg : Scalar.QComplex := ((-93086230892597828122301 : Int)/10^30,(188296966573445265095 : Int)/10^30)
theorem v1416_mg_checked : Scalar.distance (sourceCoefficient 15 82 3 2) v1416_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1416_upper : Scalar.QComplex := ((999995836153390381944756089404 : Int)/10^30,(-2885771280198332360561941830 : Int)/10^30)
theorem v1416_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 82 5) 1) 14) v1416_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1416 : Material (15 : Basis) (82 : Basis) where
  plus := ![v1416_pa,v1416_pb,v1416_pg]
  minus := ![(Primitive.Addresses.material1416 1).one,v1416_mb,v1416_mg]
  upper := v1416_upper
  lower := (Primitive.Addresses.material1416 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1416_pa_checked.trans (by decide +kernel)
    · exact v1416_pb_checked.trans (by decide +kernel)
    · exact v1416_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 82 Primitive.Addresses.material1416
    · exact v1416_mb_checked.trans (by decide +kernel)
    · exact v1416_mg_checked.trans (by decide +kernel)
  upper_error := v1416_upper_checked
  lower_error := reuse_lower_error 15 82 Primitive.Addresses.material1416

def v1417_pa : Scalar.QComplex := ((999999311526674152990481025202 : Int)/10^30,(-1173433499478559558268598645 : Int)/10^30)
theorem v1417_pa_checked : Scalar.distance (sourceCoefficient 15 83 1 0) v1417_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1417_pb : Scalar.QComplex := ((-506310081887536738337736 : Int)/10^30,(-431477142532184723848916585 : Int)/10^30)
theorem v1417_pb_checked : Scalar.distance (sourceCoefficient 15 83 1 1) v1417_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1417_pg : Scalar.QComplex := ((-93086357028052993010597 : Int)/10^30,(109230724883579275924 : Int)/10^30)
theorem v1417_pg_checked : Scalar.distance (sourceCoefficient 15 83 1 2) v1417_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1417_mb : Scalar.QComplex := ((-878655234361316712187239 : Int)/10^30,(-431476544950727770184278715 : Int)/10^30)
theorem v1417_mb_checked : Scalar.distance (sourceCoefficient 15 83 3 1) v1417_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1417_mg : Scalar.QComplex := ((-93086228106552009482589 : Int)/10^30,(189560017873308704368 : Int)/10^30)
theorem v1417_mg_checked : Scalar.distance (sourceCoefficient 15 83 3 2) v1417_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1417_upper : Scalar.QComplex := ((999995796905400760343456799494 : Int)/10^30,(-2899339844253360880720503465 : Int)/10^30)
theorem v1417_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 83 5) 1) 14) v1417_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1417 : Material (15 : Basis) (83 : Basis) where
  plus := ![v1417_pa,v1417_pb,v1417_pg]
  minus := ![(Primitive.Addresses.material1417 1).one,v1417_mb,v1417_mg]
  upper := v1417_upper
  lower := (Primitive.Addresses.material1417 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1417_pa_checked.trans (by decide +kernel)
    · exact v1417_pb_checked.trans (by decide +kernel)
    · exact v1417_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 83 Primitive.Addresses.material1417
    · exact v1417_mb_checked.trans (by decide +kernel)
    · exact v1417_mg_checked.trans (by decide +kernel)
  upper_error := v1417_upper_checked
  lower_error := reuse_lower_error 15 83 Primitive.Addresses.material1417

def v1418_pa : Scalar.QComplex := ((999999269675951073884303372531 : Int)/10^30,(-1208572531741068055877534561 : Int)/10^30)
theorem v1418_pa_checked : Scalar.distance (sourceCoefficient 15 84 1 0) v1418_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1418_pb : Scalar.QComplex := ((-521471774951881302720077 : Int)/10^30,(-431477119008548200599984148 : Int)/10^30)
theorem v1418_pb_checked : Scalar.distance (sourceCoefficient 15 84 1 1) v1418_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1418_pg : Scalar.QComplex := ((-93086352542705564387515 : Int)/10^30,(112501690925769699790 : Int)/10^30)
theorem v1418_pg_checked : Scalar.distance (sourceCoefficient 15 84 1 2) v1418_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1418_mb : Scalar.QComplex := ((-893816901480431170805917 : Int)/10^30,(-431476508343241748637711440 : Int)/10^30)
theorem v1418_mb_checked : Scalar.distance (sourceCoefficient 15 84 3 1) v1418_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1418_mg : Scalar.QComplex := ((-93086220798509875390817 : Int)/10^30,(192830978826916161841 : Int)/10^30)
theorem v1418_mg_checked : Scalar.distance (sourceCoefficient 15 84 3 2) v1418_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1418_upper : Scalar.QComplex := ((999995694407958115988727984731 : Int)/10^30,(-2934478751949857177411681498 : Int)/10^30)
theorem v1418_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 84 5) 1) 14) v1418_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1418 : Material (15 : Basis) (84 : Basis) where
  plus := ![v1418_pa,v1418_pb,v1418_pg]
  minus := ![(Primitive.Addresses.material1418 1).one,v1418_mb,v1418_mg]
  upper := v1418_upper
  lower := (Primitive.Addresses.material1418 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1418_pa_checked.trans (by decide +kernel)
    · exact v1418_pb_checked.trans (by decide +kernel)
    · exact v1418_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 84 Primitive.Addresses.material1418
    · exact v1418_mb_checked.trans (by decide +kernel)
    · exact v1418_mg_checked.trans (by decide +kernel)
  upper_error := v1418_upper_checked
  lower_error := reuse_lower_error 15 84 Primitive.Addresses.material1418

def v1419_pa : Scalar.QComplex := ((999999171005065253205625320807 : Int)/10^30,(-1287629287590565374491887775 : Int)/10^30)
theorem v1419_pa_checked : Scalar.distance (sourceCoefficient 15 85 1 0) v1419_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1419_pb : Scalar.QComplex := ((-555582964445567189594664 : Int)/10^30,(-431477063487519462601308149 : Int)/10^30)
theorem v1419_pb_checked : Scalar.distance (sourceCoefficient 15 85 1 1) v1419_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1419_pg : Scalar.QComplex := ((-93086341961226029483207 : Int)/10^30,(119860799547940924334 : Int)/10^30)
theorem v1419_pg_checked : Scalar.distance (sourceCoefficient 15 85 1 2) v1419_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1419_mb : Scalar.QComplex := ((-927928030360815024223101 : Int)/10^30,(-431476423385813461548803208 : Int)/10^30)
theorem v1419_mb_checked : Scalar.distance (sourceCoefficient 15 85 3 1) v1419_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1419_mg : Scalar.QComplex := ((-93086203866454981469810 : Int)/10^30,(200190075577614651996 : Int)/10^30)
theorem v1419_mg_checked : Scalar.distance (sourceCoefficient 15 85 3 2) v1419_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1419_upper : Scalar.QComplex := ((999995459292430630637700348012 : Int)/10^30,(-3013535219756605743440190266 : Int)/10^30)
theorem v1419_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 85 5) 1) 14) v1419_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1419 : Material (15 : Basis) (85 : Basis) where
  plus := ![v1419_pa,v1419_pb,v1419_pg]
  minus := ![(Primitive.Addresses.material1419 1).one,v1419_mb,v1419_mg]
  upper := v1419_upper
  lower := (Primitive.Addresses.material1419 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1419_pa_checked.trans (by decide +kernel)
    · exact v1419_pb_checked.trans (by decide +kernel)
    · exact v1419_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 85 Primitive.Addresses.material1419
    · exact v1419_mb_checked.trans (by decide +kernel)
    · exact v1419_mg_checked.trans (by decide +kernel)
  upper_error := v1419_upper_checked
  lower_error := reuse_lower_error 15 85 Primitive.Addresses.material1419

def v1420_pa : Scalar.QComplex := ((999999152119094527251222464866 : Int)/10^30,(-1302213919463107140451112108 : Int)/10^30)
theorem v1420_pa_checked : Scalar.distance (sourceCoefficient 15 86 1 0) v1420_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1420_pb : Scalar.QComplex := ((-561875900556610215092629 : Int)/10^30,(-431477052851976760141863202 : Int)/10^30)
theorem v1420_pb_checked : Scalar.distance (sourceCoefficient 15 86 1 1) v1420_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1420_pg : Scalar.QComplex := ((-93086339934962771070409 : Int)/10^30,(121218430353975512451 : Int)/10^30)
theorem v1420_pg_checked : Scalar.distance (sourceCoefficient 15 86 1 2) v1420_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1420_mb : Scalar.QComplex := ((-934220954950715989030916 : Int)/10^30,(-431476407319754278679116836 : Int)/10^30)
theorem v1420_mb_checked : Scalar.distance (sourceCoefficient 15 86 3 1) v1420_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1420_mg : Scalar.QComplex := ((-93086200668618237341257 : Int)/10^30,(201547704129567311733 : Int)/10^30)
theorem v1420_mg_checked : Scalar.distance (sourceCoefficient 15 86 3 2) v1420_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1420_upper : Scalar.QComplex := ((999995415234736528579032440613 : Int)/10^30,(-3028119797311579415339354544 : Int)/10^30)
theorem v1420_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 86 5) 1) 14) v1420_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1420 : Material (15 : Basis) (86 : Basis) where
  plus := ![v1420_pa,v1420_pb,v1420_pg]
  minus := ![(Primitive.Addresses.material1420 1).one,v1420_mb,v1420_mg]
  upper := v1420_upper
  lower := (Primitive.Addresses.material1420 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1420_pa_checked.trans (by decide +kernel)
    · exact v1420_pb_checked.trans (by decide +kernel)
    · exact v1420_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 86 Primitive.Addresses.material1420
    · exact v1420_mb_checked.trans (by decide +kernel)
    · exact v1420_mg_checked.trans (by decide +kernel)
  upper_error := v1420_upper_checked
  lower_error := reuse_lower_error 15 86 Primitive.Addresses.material1420

def v1421_pa : Scalar.QComplex := ((999999150861006705375229022764 : Int)/10^30,(-1303179675084068984401016310 : Int)/10^30)
theorem v1421_pa_checked : Scalar.distance (sourceCoefficient 15 87 1 0) v1421_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1421_pb : Scalar.QComplex := ((-562292602083041219275038 : Int)/10^30,(-431477052143399421802942081 : Int)/10^30)
theorem v1421_pb_checked : Scalar.distance (sourceCoefficient 15 87 1 1) v1421_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1421_pg : Scalar.QComplex := ((-93086339799973516567267 : Int)/10^30,(121308329062927145124 : Int)/10^30)
theorem v1421_pg_checked : Scalar.distance (sourceCoefficient 15 87 1 2) v1421_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1421_mb : Scalar.QComplex := ((-934637655710519640874660 : Int)/10^30,(-431476406251582554406032371 : Int)/10^30)
theorem v1421_mb_checked : Scalar.distance (sourceCoefficient 15 87 3 1) v1421_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1421_mg : Scalar.QComplex := ((-93086200456050496163075 : Int)/10^30,(201637602688555899544 : Int)/10^30)
theorem v1421_mg_checked : Scalar.distance (sourceCoefficient 15 87 3 2) v1421_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1421_upper : Scalar.QComplex := ((999995412309843991362462721995 : Int)/10^30,(-3029085549322816259768629948 : Int)/10^30)
theorem v1421_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 87 5) 1) 14) v1421_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1421 : Material (15 : Basis) (87 : Basis) where
  plus := ![v1421_pa,v1421_pb,v1421_pg]
  minus := ![(Primitive.Addresses.material1421 1).one,v1421_mb,v1421_mg]
  upper := v1421_upper
  lower := (Primitive.Addresses.material1421 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1421_pa_checked.trans (by decide +kernel)
    · exact v1421_pb_checked.trans (by decide +kernel)
    · exact v1421_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 87 Primitive.Addresses.material1421
    · exact v1421_mb_checked.trans (by decide +kernel)
    · exact v1421_mg_checked.trans (by decide +kernel)
  upper_error := v1421_upper_checked
  lower_error := reuse_lower_error 15 87 Primitive.Addresses.material1421

def v1422_pa : Scalar.QComplex := ((999999135466999435444653080776 : Int)/10^30,(-1314939258563604385278510545 : Int)/10^30)
theorem v1422_pa_checked : Scalar.distance (sourceCoefficient 15 88 1 0) v1422_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1422_pb : Scalar.QComplex := ((-567366594137849600521719 : Int)/10^30,(-431477043472317712630297689 : Int)/10^30)
theorem v1422_pb_checked : Scalar.distance (sourceCoefficient 15 88 1 1) v1422_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1422_pg : Scalar.QComplex := ((-93086338148142665222305 : Int)/10^30,(122402986288340692597 : Int)/10^30)
theorem v1422_pg_checked : Scalar.distance (sourceCoefficient 15 88 1 2) v1422_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1422_mb : Scalar.QComplex := ((-939711638393295903230530 : Int)/10^30,(-431476393201877454692697817 : Int)/10^30)
theorem v1422_mb_checked : Scalar.distance (sourceCoefficient 15 88 3 1) v1422_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1422_mg : Scalar.QComplex := ((-93086197859580375869613 : Int)/10^30,(202732258080922904677 : Int)/10^30)
theorem v1422_mg_checked : Scalar.distance (sourceCoefficient 15 88 3 2) v1422_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1422_upper : Scalar.QComplex := ((999995376619885384399020815069 : Int)/10^30,(-3040845088719173431120376101 : Int)/10^30)
theorem v1422_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 88 5) 1) 14) v1422_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1422 : Material (15 : Basis) (88 : Basis) where
  plus := ![v1422_pa,v1422_pb,v1422_pg]
  minus := ![(Primitive.Addresses.material1422 1).one,v1422_mb,v1422_mg]
  upper := v1422_upper
  lower := (Primitive.Addresses.material1422 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1422_pa_checked.trans (by decide +kernel)
    · exact v1422_pb_checked.trans (by decide +kernel)
    · exact v1422_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 88 Primitive.Addresses.material1422
    · exact v1422_mb_checked.trans (by decide +kernel)
    · exact v1422_mg_checked.trans (by decide +kernel)
  upper_error := v1422_upper_checked
  lower_error := reuse_lower_error 15 88 Primitive.Addresses.material1422

def v1423_pa : Scalar.QComplex := ((999999114180868936963725594193 : Int)/10^30,(-1331028729010211706910073817 : Int)/10^30)
theorem v1423_pa_checked : Scalar.distance (sourceCoefficient 15 89 1 0) v1423_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1423_pb : Scalar.QComplex := ((-574308833541206098663206 : Int)/10^30,(-431477031479647418175433824 : Int)/10^30)
theorem v1423_pb_checked : Scalar.distance (sourceCoefficient 15 89 1 1) v1423_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1423_pg : Scalar.QComplex := ((-93086335863775733541865 : Int)/10^30,(123900697066586915765 : Int)/10^30)
theorem v1423_pg_checked : Scalar.distance (sourceCoefficient 15 89 1 2) v1423_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1423_mb : Scalar.QComplex := ((-946653864862605061192861 : Int)/10^30,(-431476375218371687416406693 : Int)/10^30)
theorem v1423_mb_checked : Scalar.distance (sourceCoefficient 15 89 3 1) v1423_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1423_mg : Scalar.QComplex := ((-93086194282757347526320 : Int)/10^30,(204229966330197178367 : Int)/10^30)
theorem v1423_mg_checked : Scalar.distance (sourceCoefficient 15 89 3 2) v1423_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1423_upper : Scalar.QComplex := ((999995327564820223621737794122 : Int)/10^30,(-3056934498464474346790496609 : Int)/10^30)
theorem v1423_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 89 5) 1) 14) v1423_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1423 : Material (15 : Basis) (89 : Basis) where
  plus := ![v1423_pa,v1423_pb,v1423_pg]
  minus := ![(Primitive.Addresses.material1423 1).one,v1423_mb,v1423_mg]
  upper := v1423_upper
  lower := (Primitive.Addresses.material1423 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1423_pa_checked.trans (by decide +kernel)
    · exact v1423_pb_checked.trans (by decide +kernel)
    · exact v1423_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 89 Primitive.Addresses.material1423
    · exact v1423_mb_checked.trans (by decide +kernel)
    · exact v1423_mg_checked.trans (by decide +kernel)
  upper_error := v1423_upper_checked
  lower_error := reuse_lower_error 15 89 Primitive.Addresses.material1423

def v1424_pa : Scalar.QComplex := ((999999078960704006068053658653 : Int)/10^30,(-1357231647020684206269647428 : Int)/10^30)
theorem v1424_pa_checked : Scalar.distance (sourceCoefficient 15 90 1 0) v1424_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1424_pb : Scalar.QComplex := ((-585614794520258919238575 : Int)/10^30,(-431477011629906454103644925 : Int)/10^30)
theorem v1424_pb_checked : Scalar.distance (sourceCoefficient 15 90 1 1) v1424_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1424_pg : Scalar.QComplex := ((-93086332083336650228970 : Int)/10^30,(126339832172531440119 : Int)/10^30)
theorem v1424_pg_checked : Scalar.distance (sourceCoefficient 15 90 1 2) v1424_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1424_mb : Scalar.QComplex := ((-957959804502499448476491 : Int)/10^30,(-431476345612102990967817909 : Int)/10^30)
theorem v1424_mb_checked : Scalar.distance (sourceCoefficient 15 90 3 1) v1424_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1424_mg : Scalar.QComplex := ((-93086188397455929980724 : Int)/10^30,(206669097265591564554 : Int)/10^30)
theorem v1424_mg_checked : Scalar.distance (sourceCoefficient 15 90 3 2) v1424_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1424_upper : Scalar.QComplex := ((999995247120848373101889919522 : Int)/10^30,(-3083137316661968958196741633 : Int)/10^30)
theorem v1424_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 90 5) 1) 14) v1424_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1424 : Material (15 : Basis) (90 : Basis) where
  plus := ![v1424_pa,v1424_pb,v1424_pg]
  minus := ![(Primitive.Addresses.material1424 1).one,v1424_mb,v1424_mg]
  upper := v1424_upper
  lower := (Primitive.Addresses.material1424 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1424_pa_checked.trans (by decide +kernel)
    · exact v1424_pb_checked.trans (by decide +kernel)
    · exact v1424_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 90 Primitive.Addresses.material1424
    · exact v1424_mb_checked.trans (by decide +kernel)
    · exact v1424_mg_checked.trans (by decide +kernel)
  upper_error := v1424_upper_checked
  lower_error := reuse_lower_error 15 90 Primitive.Addresses.material1424

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
