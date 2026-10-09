import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B045
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B046

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1089_pa : Scalar.QComplex := ((999999241083010998040105694803 : Int)/10^30,(-1232003815760699498008784294 : Int)/10^30)
theorem v1089_pa_checked : Scalar.distance (sourceCoefficient 11 89 1 0) v1089_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1089_pb : Scalar.QComplex := ((-531581797778234499597040 : Int)/10^30,(-431477068131930039811052747 : Int)/10^30)
theorem v1089_pb_checked : Scalar.distance (sourceCoefficient 11 89 1 1) v1089_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1089_pg : Scalar.QComplex := ((-93086345723868516931944 : Int)/10^30,(114682820161766253303 : Int)/10^30)
theorem v1089_pg_checked : Scalar.distance (sourceCoefficient 11 89 1 2) v1089_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1089_mb : Scalar.QComplex := ((-903926876638130743623073 : Int)/10^30,(-431476448742148170921227077 : Int)/10^30)
theorem v1089_mb_checked : Scalar.distance (sourceCoefficient 11 89 3 1) v1089_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1089_mg : Scalar.QComplex := ((-93086212097459070649046 : Int)/10^30,(195012101366429355328 : Int)/10^30)
theorem v1089_mg_checked : Scalar.distance (sourceCoefficient 11 89 3 2) v1089_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1089_upper : Scalar.QComplex := ((999995625374790077567583698023 : Int)/10^30,(-2957909951722522864624560780 : Int)/10^30)
theorem v1089_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 89 5) 1) 14) v1089_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1089 : Material (11 : Basis) (89 : Basis) where
  plus := ![v1089_pa,v1089_pb,v1089_pg]
  minus := ![(Primitive.Addresses.material1089 1).one,v1089_mb,v1089_mg]
  upper := v1089_upper
  lower := (Primitive.Addresses.material1089 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1089_pa_checked.trans (by decide +kernel)
    · exact v1089_pb_checked.trans (by decide +kernel)
    · exact v1089_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 89 Primitive.Addresses.material1089
    · exact v1089_mb_checked.trans (by decide +kernel)
    · exact v1089_mg_checked.trans (by decide +kernel)
  upper_error := v1089_upper_checked
  lower_error := reuse_lower_error 11 89 Primitive.Addresses.material1089

def v1090_pa : Scalar.QComplex := ((999999208457590050172591332162 : Int)/10^30,(-1258206737130376387874183311 : Int)/10^30)
theorem v1090_pa_checked : Scalar.distance (sourceCoefficient 11 90 1 0) v1090_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1090_pb : Scalar.QComplex := ((-542887759723567943519404 : Int)/10^30,(-431477049028571415573837418 : Int)/10^30)
theorem v1090_pb_checked : Scalar.distance (sourceCoefficient 11 90 1 1) v1090_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1090_pg : Scalar.QComplex := ((-93086342144708958464862 : Int)/10^30,(117121955528291038394 : Int)/10^30)
theorem v1090_pg_checked : Scalar.distance (sourceCoefficient 11 90 1 2) v1090_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1090_mb : Scalar.QComplex := ((-915232817888399737927790 : Int)/10^30,(-431476419882260702538297100 : Int)/10^30)
theorem v1090_mb_checked : Scalar.distance (sourceCoefficient 11 90 3 1) v1090_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1090_mg : Scalar.QComplex := ((-93086206413436878134669 : Int)/10^30,(197451232736099069874 : Int)/10^30)
theorem v1090_mg_checked : Scalar.distance (sourceCoefficient 11 90 3 2) v1090_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1090_upper : Scalar.QComplex := ((999995547525552547827497343882 : Int)/10^30,(-2984112777757509584767542900 : Int)/10^30)
theorem v1090_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 90 5) 1) 14) v1090_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1090 : Material (11 : Basis) (90 : Basis) where
  plus := ![v1090_pa,v1090_pb,v1090_pg]
  minus := ![(Primitive.Addresses.material1090 1).one,v1090_mb,v1090_mg]
  upper := v1090_upper
  lower := (Primitive.Addresses.material1090 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1090_pa_checked.trans (by decide +kernel)
    · exact v1090_pb_checked.trans (by decide +kernel)
    · exact v1090_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 90 Primitive.Addresses.material1090
    · exact v1090_mb_checked.trans (by decide +kernel)
    · exact v1090_mg_checked.trans (by decide +kernel)
  upper_error := v1090_upper_checked
  lower_error := reuse_lower_error 11 90 Primitive.Addresses.material1090

def v1091_pa : Scalar.QComplex := ((999999189776166564526532154296 : Int)/10^30,(-1272967796296625356549698333 : Int)/10^30)
theorem v1091_pa_checked : Scalar.distance (sourceCoefficient 11 91 1 0) v1091_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1091_pb : Scalar.QComplex := ((-549256819354831515345355 : Int)/10^30,(-431477038093019257205982190 : Int)/10^30)
theorem v1091_pb_checked : Scalar.distance (sourceCoefficient 11 91 1 1) v1091_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1091_pg : Scalar.QComplex := ((-93086340095604144639198 : Int)/10^30,(118496009225110247285 : Int)/10^30)
theorem v1091_pg_checked : Scalar.distance (sourceCoefficient 11 91 1 2) v1091_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1091_mb : Scalar.QComplex := ((-921601865711282334944090 : Int)/10^30,(-431476403450501005993180229 : Int)/10^30)
theorem v1091_mb_checked : Scalar.distance (sourceCoefficient 11 91 3 1) v1091_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1091_mg : Scalar.QComplex := ((-93086203178586372010620 : Int)/10^30,(198825284153010124006 : Int)/10^30)
theorem v1091_mg_checked : Scalar.distance (sourceCoefficient 11 91 3 2) v1091_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1091_upper : Scalar.QComplex := ((999995503367907877848512707420 : Int)/10^30,(-2998873782696452710403377326 : Int)/10^30)
theorem v1091_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 91 5) 1) 14) v1091_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1091 : Material (11 : Basis) (91 : Basis) where
  plus := ![v1091_pa,v1091_pb,v1091_pg]
  minus := ![(Primitive.Addresses.material1091 1).one,v1091_mb,v1091_mg]
  upper := v1091_upper
  lower := (Primitive.Addresses.material1091 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1091_pa_checked.trans (by decide +kernel)
    · exact v1091_pb_checked.trans (by decide +kernel)
    · exact v1091_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 91 Primitive.Addresses.material1091
    · exact v1091_mb_checked.trans (by decide +kernel)
    · exact v1091_mg_checked.trans (by decide +kernel)
  upper_error := v1091_upper_checked
  lower_error := reuse_lower_error 11 91 Primitive.Addresses.material1091

def v1092_pa : Scalar.QComplex := ((999999148586478573067982002128 : Int)/10^30,(-1304923874388417942009408482 : Int)/10^30)
theorem v1092_pa_checked : Scalar.distance (sourceCoefficient 11 92 1 0) v1092_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1092_pb : Scalar.QComplex := ((-563045136188718889567342 : Int)/10^30,(-431477013989310575695377874 : Int)/10^30)
theorem v1092_pb_checked : Scalar.distance (sourceCoefficient 11 92 1 1) v1092_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1092_pg : Scalar.QComplex := ((-93086335578451367724406 : Int)/10^30,(121470685097436941537 : Int)/10^30)
theorem v1092_pg_checked : Scalar.distance (sourceCoefficient 11 92 1 2) v1092_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1092_mb : Scalar.QComplex := ((-935390156610734193296443 : Int)/10^30,(-431476367448104874487601062 : Int)/10^30)
theorem v1092_mb_checked : Scalar.distance (sourceCoefficient 11 92 3 1) v1092_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1092_mg : Scalar.QComplex := ((-93086196094423973648239 : Int)/10^30,(201799955019629640119 : Int)/10^30)
theorem v1092_mg_checked : Scalar.distance (sourceCoefficient 11 92 3 2) v1092_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1092_upper : Scalar.QComplex := ((999995407024989479916228983266 : Int)/10^30,(-3030829742103756028810125574 : Int)/10^30)
theorem v1092_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 92 5) 1) 14) v1092_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1092 : Material (11 : Basis) (92 : Basis) where
  plus := ![v1092_pa,v1092_pb,v1092_pg]
  minus := ![(Primitive.Addresses.material1092 1).one,v1092_mb,v1092_mg]
  upper := v1092_upper
  lower := (Primitive.Addresses.material1092 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1092_pa_checked.trans (by decide +kernel)
    · exact v1092_pb_checked.trans (by decide +kernel)
    · exact v1092_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 92 Primitive.Addresses.material1092
    · exact v1092_mb_checked.trans (by decide +kernel)
    · exact v1092_mg_checked.trans (by decide +kernel)
  upper_error := v1092_upper_checked
  lower_error := reuse_lower_error 11 92 Primitive.Addresses.material1092

def v1093_pa : Scalar.QComplex := ((999999098377267027817667138080 : Int)/10^30,(-1342849452850472011352963762 : Int)/10^30)
theorem v1093_pa_checked : Scalar.distance (sourceCoefficient 11 93 1 0) v1093_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1093_pb : Scalar.QComplex := ((-579409155123790106069227 : Int)/10^30,(-431476984620585044772143722 : Int)/10^30)
theorem v1093_pb_checked : Scalar.distance (sourceCoefficient 11 93 1 1) v1093_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1093_pg : Scalar.QComplex := ((-93086330073566825630303 : Int)/10^30,(125001040110927059030 : Int)/10^30)
theorem v1093_pg_checked : Scalar.distance (sourceCoefficient 11 93 1 2) v1093_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1093_mb : Scalar.QComplex := ((-951754144108845872769875 : Int)/10^30,(-431476323957978945970449923 : Int)/10^30)
theorem v1093_mb_checked : Scalar.distance (sourceCoefficient 11 93 3 1) v1093_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1093_mg : Scalar.QComplex := ((-93086187543004105919668 : Int)/10^30,(205330303968139811864 : Int)/10^30)
theorem v1093_mg_checked : Scalar.distance (sourceCoefficient 11 93 3 2) v1093_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1093_upper : Scalar.QComplex := ((999995291359744871484927786634 : Int)/10^30,(-3068755177423571847308660329 : Int)/10^30)
theorem v1093_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 93 5) 1) 14) v1093_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1093 : Material (11 : Basis) (93 : Basis) where
  plus := ![v1093_pa,v1093_pb,v1093_pg]
  minus := ![(Primitive.Addresses.material1093 1).one,v1093_mb,v1093_mg]
  upper := v1093_upper
  lower := (Primitive.Addresses.material1093 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1093_pa_checked.trans (by decide +kernel)
    · exact v1093_pb_checked.trans (by decide +kernel)
    · exact v1093_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 93 Primitive.Addresses.material1093
    · exact v1093_mb_checked.trans (by decide +kernel)
    · exact v1093_mg_checked.trans (by decide +kernel)
  upper_error := v1093_upper_checked
  lower_error := reuse_lower_error 11 93 Primitive.Addresses.material1093

def v1094_pa : Scalar.QComplex := ((999999037216094152841353297492 : Int)/10^30,(-1387647968593428214043409572 : Int)/10^30)
theorem v1094_pa_checked : Scalar.distance (sourceCoefficient 11 94 1 0) v1094_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1094_pb : Scalar.QComplex := ((-598738688041430675509789 : Int)/10^30,(-431476948863594938808487285 : Int)/10^30)
theorem v1094_pb_checked : Scalar.distance (sourceCoefficient 11 94 1 1) v1094_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1094_pg : Scalar.QComplex := ((-93086323369844606344339 : Int)/10^30,(129171171891921228057 : Int)/10^30)
theorem v1094_pg_checked : Scalar.distance (sourceCoefficient 11 94 1 2) v1094_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1094_mb : Scalar.QComplex := ((-971083638972545907283086 : Int)/10^30,(-431476271520485815890112474 : Int)/10^30)
theorem v1094_mb_checked : Scalar.distance (sourceCoefficient 11 94 3 1) v1094_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1094_mg : Scalar.QComplex := ((-93086177240648471501260 : Int)/10^30,(209500428411392983587 : Int)/10^30)
theorem v1094_mg_checked : Scalar.distance (sourceCoefficient 11 94 3 2) v1094_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1094_upper : Scalar.QComplex := ((999995152880489006149984572096 : Int)/10^30,(-3113553520885765370240291606 : Int)/10^30)
theorem v1094_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 94 5) 1) 14) v1094_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1094 : Material (11 : Basis) (94 : Basis) where
  plus := ![v1094_pa,v1094_pb,v1094_pg]
  minus := ![(Primitive.Addresses.material1094 1).one,v1094_mb,v1094_mg]
  upper := v1094_upper
  lower := (Primitive.Addresses.material1094 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1094_pa_checked.trans (by decide +kernel)
    · exact v1094_pb_checked.trans (by decide +kernel)
    · exact v1094_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 94 Primitive.Addresses.material1094
    · exact v1094_mb_checked.trans (by decide +kernel)
    · exact v1094_mg_checked.trans (by decide +kernel)
  upper_error := v1094_upper_checked
  lower_error := reuse_lower_error 11 94 Primitive.Addresses.material1094

def v1095_pa : Scalar.QComplex := ((999998974798955133474152506192 : Int)/10^30,(-1431922148266402540307764743 : Int)/10^30)
theorem v1095_pa_checked : Scalar.distance (sourceCoefficient 11 95 1 0) v1095_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1095_pb : Scalar.QComplex := ((-617841980730125915335792 : Int)/10^30,(-431476912390725283244753090 : Int)/10^30)
theorem v1095_pb_checked : Scalar.distance (sourceCoefficient 11 95 1 1) v1095_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1095_pg : Scalar.QComplex := ((-93086316530444192230678 : Int)/10^30,(133292494992085125077 : Int)/10^30)
theorem v1095_pg_checked : Scalar.distance (sourceCoefficient 11 95 1 2) v1095_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1095_mb : Scalar.QComplex := ((-990186893073768379820506 : Int)/10^30,(-431476218562348530862529995 : Int)/10^30)
theorem v1095_mb_checked : Scalar.distance (sourceCoefficient 11 95 3 1) v1095_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1095_mg : Scalar.QComplex := ((-93086166844734386069492 : Int)/10^30,(213621744074905414424 : Int)/10^30)
theorem v1095_mg_checked : Scalar.distance (sourceCoefficient 11 95 3 2) v1095_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1095_upper : Scalar.QComplex := ((999995014050225356430216396970 : Int)/10^30,(-3157827526891230375282291009 : Int)/10^30)
theorem v1095_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 95 5) 1) 14) v1095_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1095 : Material (11 : Basis) (95 : Basis) where
  plus := ![v1095_pa,v1095_pb,v1095_pg]
  minus := ![(Primitive.Addresses.material1095 1).one,v1095_mb,v1095_mg]
  upper := v1095_upper
  lower := (Primitive.Addresses.material1095 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1095_pa_checked.trans (by decide +kernel)
    · exact v1095_pb_checked.trans (by decide +kernel)
    · exact v1095_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 95 Primitive.Addresses.material1095
    · exact v1095_mb_checked.trans (by decide +kernel)
    · exact v1095_mg_checked.trans (by decide +kernel)
  upper_error := v1095_upper_checked
  lower_error := reuse_lower_error 11 95 Primitive.Addresses.material1095

def v1096_pa : Scalar.QComplex := ((999998944124343509942209947117 : Int)/10^30,(-1453186222790015860462487860 : Int)/10^30)
theorem v1096_pa_checked : Scalar.distance (sourceCoefficient 11 96 1 0) v1096_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1096_pb : Scalar.QComplex := ((-627016940551729877342826 : Int)/10^30,(-431476894472601565748294702 : Int)/10^30)
theorem v1096_pb_checked : Scalar.distance (sourceCoefficient 11 96 1 1) v1096_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1096_pg : Scalar.QComplex := ((-93086313169932124590224 : Int)/10^30,(135271890659158526316 : Int)/10^30)
theorem v1096_pg_checked : Scalar.distance (sourceCoefficient 11 96 1 2) v1096_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1096_mb : Scalar.QComplex := ((-999361834016581718001345 : Int)/10^30,(-431476192726654383908948665 : Int)/10^30)
theorem v1096_mb_checked : Scalar.distance (sourceCoefficient 11 96 3 1) v1096_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1096_mg : Scalar.QComplex := ((-93086161776094257688410 : Int)/10^30,(215601136104988783433 : Int)/10^30)
theorem v1096_mg_checked : Scalar.distance (sourceCoefficient 11 96 3 2) v1096_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1096_upper : Scalar.QComplex := ((999994946675795853144182104788 : Int)/10^30,(-3179091516802905662985643891 : Int)/10^30)
theorem v1096_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 96 5) 1) 14) v1096_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1096 : Material (11 : Basis) (96 : Basis) where
  plus := ![v1096_pa,v1096_pb,v1096_pg]
  minus := ![(Primitive.Addresses.material1096 1).one,v1096_mb,v1096_mg]
  upper := v1096_upper
  lower := (Primitive.Addresses.material1096 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1096_pa_checked.trans (by decide +kernel)
    · exact v1096_pb_checked.trans (by decide +kernel)
    · exact v1096_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 96 Primitive.Addresses.material1096
    · exact v1096_mb_checked.trans (by decide +kernel)
    · exact v1096_mg_checked.trans (by decide +kernel)
  upper_error := v1096_upper_checked
  lower_error := reuse_lower_error 11 96 Primitive.Addresses.material1096

def v1097_pa : Scalar.QComplex := ((999998835129656040556569516338 : Int)/10^30,(-1526348364887900885510730688 : Int)/10^30)
theorem v1097_pa_checked : Scalar.distance (sourceCoefficient 11 97 1 0) v1097_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1097_pb : Scalar.QComplex := ((-658584722398540407019002 : Int)/10^30,(-431476830835466889536689767 : Int)/10^30)
theorem v1097_pb_checked : Scalar.distance (sourceCoefficient 11 97 1 1) v1097_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1097_pg : Scalar.QComplex := ((-93086301232470227371906 : Int)/10^30,(142082289187088600430 : Int)/10^30)
theorem v1097_pg_checked : Scalar.distance (sourceCoefficient 11 97 1 2) v1097_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1097_mb : Scalar.QComplex := ((-1030929549193283231787994 : Int)/10^30,(-431476101847969429029621276 : Int)/10^30)
theorem v1097_mb_checked : Scalar.distance (sourceCoefficient 11 97 3 1) v1097_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1097_mg : Scalar.QComplex := ((-93086143961569604692455 : Int)/10^30,(222411521795604261036 : Int)/10^30)
theorem v1097_mg_checked : Scalar.distance (sourceCoefficient 11 97 3 2) v1097_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1097_upper : Scalar.QComplex := ((999994711410050675276579576921 : Int)/10^30,(-3252253361819431610804022713 : Int)/10^30)
theorem v1097_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 97 5) 1) 14) v1097_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1097 : Material (11 : Basis) (97 : Basis) where
  plus := ![v1097_pa,v1097_pb,v1097_pg]
  minus := ![(Primitive.Addresses.material1097 1).one,v1097_mb,v1097_mg]
  upper := v1097_upper
  lower := (Primitive.Addresses.material1097 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1097_pa_checked.trans (by decide +kernel)
    · exact v1097_pb_checked.trans (by decide +kernel)
    · exact v1097_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 97 Primitive.Addresses.material1097
    · exact v1097_mb_checked.trans (by decide +kernel)
    · exact v1097_mg_checked.trans (by decide +kernel)
  upper_error := v1097_upper_checked
  lower_error := reuse_lower_error 11 97 Primitive.Addresses.material1097

def v1098_pa : Scalar.QComplex := ((999999999629301523866842469648 : Int)/10^30,(27228605401836093678413848 : Int)/10^30)
theorem v1098_pa_checked : Scalar.distance (sourceCoefficient 12 13 1 0) v1098_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1098_pb : Scalar.QComplex := ((11748531153892814710881 : Int)/10^30,(-431477520649861082025405020 : Int)/10^30)
theorem v1098_pb_checked : Scalar.distance (sourceCoefficient 12 13 1 1) v1098_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1098_pg : Scalar.QComplex := ((-93086429841882878242287 : Int)/10^30,(-2534613667369906114 : Int)/10^30)
theorem v1098_pg_checked : Scalar.distance (sourceCoefficient 12 13 1 2) v1098_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1098_mb : Scalar.QComplex := ((-360597140515310151857695 : Int)/10^30,(-431477370129513898834228626 : Int)/10^30)
theorem v1098_mb_checked : Scalar.distance (sourceCoefficient 12 13 3 1) v1098_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1098_mg : Scalar.QComplex := ((-93086397368808228279084 : Int)/10^30,(77794783772758770951 : Int)/10^30)
theorem v1098_mg_checked : Scalar.distance (sourceCoefficient 12 13 3 2) v1098_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1098_upper : Scalar.QComplex := ((999998557240873091456171677194 : Int)/10^30,(-1698680715220841429194998745 : Int)/10^30)
theorem v1098_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 13 5) 1) 14) v1098_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1098 : Material (12 : Basis) (13 : Basis) where
  plus := ![v1098_pa,v1098_pb,v1098_pg]
  minus := ![(Primitive.Addresses.material1098 1).one,v1098_mb,v1098_mg]
  upper := v1098_upper
  lower := (Primitive.Addresses.material1098 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1098_pa_checked.trans (by decide +kernel)
    · exact v1098_pb_checked.trans (by decide +kernel)
    · exact v1098_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 13 Primitive.Addresses.material1098
    · exact v1098_mb_checked.trans (by decide +kernel)
    · exact v1098_mg_checked.trans (by decide +kernel)
  upper_error := v1098_upper_checked
  lower_error := reuse_lower_error 12 13 Primitive.Addresses.material1098

def v1099_pa : Scalar.QComplex := ((999999999940395659445096863175 : Int)/10^30,(10918272807832454789761913 : Int)/10^30)
theorem v1099_pa_checked : Scalar.distance (sourceCoefficient 12 14 1 0) v1099_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1099_pb : Scalar.QComplex := ((4710989281120388411897 : Int)/10^30,(-431477520644113676037780951 : Int)/10^30)
theorem v1099_pb_checked : Scalar.distance (sourceCoefficient 12 14 1 1) v1099_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1099_pg : Scalar.QComplex := ((-93086429855742230451662 : Int)/10^30,(-1016343035932732028 : Int)/10^30)
theorem v1099_pg_checked : Scalar.distance (sourceCoefficient 12 14 1 2) v1099_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1099_mb : Scalar.QComplex := ((-367634679762724354857235 : Int)/10^30,(-431477364050684817903896651 : Int)/10^30)
theorem v1099_mb_checked : Scalar.distance (sourceCoefficient 12 14 3 1) v1099_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1099_mg : Scalar.QComplex := ((-93086396072468400768548 : Int)/10^30,(79313053850834397312 : Int)/10^30)
theorem v1099_mg_checked : Scalar.distance (sourceCoefficient 12 14 3 2) v1099_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1099_upper : Scalar.QComplex := ((999998529401812368260418315993 : Int)/10^30,(-1714991024059440871338153429 : Int)/10^30)
theorem v1099_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 14 5) 1) 14) v1099_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1099 : Material (12 : Basis) (14 : Basis) where
  plus := ![v1099_pa,v1099_pb,v1099_pg]
  minus := ![(Primitive.Addresses.material1099 1).one,v1099_mb,v1099_mg]
  upper := v1099_upper
  lower := (Primitive.Addresses.material1099 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1099_pa_checked.trans (by decide +kernel)
    · exact v1099_pb_checked.trans (by decide +kernel)
    · exact v1099_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 14 Primitive.Addresses.material1099
    · exact v1099_mb_checked.trans (by decide +kernel)
    · exact v1099_mg_checked.trans (by decide +kernel)
  upper_error := v1099_upper_checked
  lower_error := reuse_lower_error 12 14 Primitive.Addresses.material1099

def v1100_pa : Scalar.QComplex := ((999999999882036630044230082663 : Int)/10^30,(-15359906897426965785030974 : Int)/10^30)
theorem v1100_pa_checked : Scalar.distance (sourceCoefficient 12 15 1 0) v1100_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1100_pb : Scalar.QComplex := ((-6627454541121036408822 : Int)/10^30,(-431477520312928847223507668 : Int)/10^30)
theorem v1100_pb_checked : Scalar.distance (sourceCoefficient 12 15 1 1) v1100_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1100_pg : Scalar.QComplex := ((-93086429817301310006739 : Int)/10^30,(1429798895576281458 : Int)/10^30)
theorem v1100_pg_checked : Scalar.distance (sourceCoefficient 12 15 1 2) v1100_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1100_mb : Scalar.QComplex := ((-378973119077347360919830 : Int)/10^30,(-431477353934933758363515886 : Int)/10^30)
theorem v1100_mb_checked : Scalar.distance (sourceCoefficient 12 15 3 1) v1100_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1100_mg : Scalar.QComplex := ((-93086393923117177887546 : Int)/10^30,(81759194838360192460 : Int)/10^30)
theorem v1100_mg_checked : Scalar.distance (sourceCoefficient 12 15 3 2) v1100_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1100_upper : Scalar.QComplex := ((999998483989699192341271268890 : Int)/10^30,(-1741269164525716082300627750 : Int)/10^30)
theorem v1100_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 15 5) 1) 14) v1100_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1100 : Material (12 : Basis) (15 : Basis) where
  plus := ![v1100_pa,v1100_pb,v1100_pg]
  minus := ![(Primitive.Addresses.material1100 1).one,v1100_mb,v1100_mg]
  upper := v1100_upper
  lower := (Primitive.Addresses.material1100 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1100_pa_checked.trans (by decide +kernel)
    · exact v1100_pb_checked.trans (by decide +kernel)
    · exact v1100_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 15 Primitive.Addresses.material1100
    · exact v1100_mb_checked.trans (by decide +kernel)
    · exact v1100_mg_checked.trans (by decide +kernel)
  upper_error := v1100_upper_checked
  lower_error := reuse_lower_error 12 15 Primitive.Addresses.material1100

def v1101_pa : Scalar.QComplex := ((999999999825297749257009017509 : Int)/10^30,(-18692364790348520495228823 : Int)/10^30)
theorem v1101_pa_checked : Scalar.distance (sourceCoefficient 12 16 1 0) v1101_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1101_pb : Scalar.QComplex := ((-8065335208617678620991 : Int)/10^30,(-431477520242545386790182183 : Int)/10^30)
theorem v1101_pb_checked : Scalar.distance (sourceCoefficient 12 16 1 1) v1101_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1101_pg : Scalar.QComplex := ((-93086429807068279516729 : Int)/10^30,(1740005503288875008 : Int)/10^30)
theorem v1101_pg_checked : Scalar.distance (sourceCoefficient 12 16 1 2) v1101_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1101_mb : Scalar.QComplex := ((-380410999148717559829562 : Int)/10^30,(-431477352623724067828836626 : Int)/10^30)
theorem v1101_mb_checked : Scalar.distance (sourceCoefficient 12 16 3 1) v1101_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1101_mg : Scalar.QComplex := ((-93086393645189819938768 : Int)/10^30,(82069401321738044381 : Int)/10^30)
theorem v1101_mg_checked : Scalar.distance (sourceCoefficient 12 16 3 2) v1101_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1101_upper : Scalar.QComplex := ((999998478181440391095810209890 : Int)/10^30,(-1744601617357406902579010167 : Int)/10^30)
theorem v1101_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 16 5) 1) 14) v1101_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1101 : Material (12 : Basis) (16 : Basis) where
  plus := ![v1101_pa,v1101_pb,v1101_pg]
  minus := ![(Primitive.Addresses.material1101 1).one,v1101_mb,v1101_mg]
  upper := v1101_upper
  lower := (Primitive.Addresses.material1101 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1101_pa_checked.trans (by decide +kernel)
    · exact v1101_pb_checked.trans (by decide +kernel)
    · exact v1101_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 16 Primitive.Addresses.material1101
    · exact v1101_mb_checked.trans (by decide +kernel)
    · exact v1101_mg_checked.trans (by decide +kernel)
  upper_error := v1101_upper_checked
  lower_error := reuse_lower_error 12 16 Primitive.Addresses.material1101

def v1102_pa : Scalar.QComplex := ((999999999677831143467782567908 : Int)/10^30,(-25383808086271100156077891 : Int)/10^30)
theorem v1102_pa_checked : Scalar.distance (sourceCoefficient 12 17 1 0) v1102_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1102_pb : Scalar.QComplex := ((-10952542566828314981928 : Int)/10^30,(-431477520081924135140339483 : Int)/10^30)
theorem v1102_pb_checked : Scalar.distance (sourceCoefficient 12 17 1 1) v1102_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1102_pg : Scalar.QComplex := ((-93086429782878594002716 : Int)/10^30,(2362888069805989572 : Int)/10^30)
theorem v1102_pg_checked : Scalar.distance (sourceCoefficient 12 17 1 2) v1102_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1102_mb : Scalar.QComplex := ((-383298205293280038772670 : Int)/10^30,(-431477349971572960842135482 : Int)/10^30)
theorem v1102_mb_checked : Scalar.distance (sourceCoefficient 12 17 3 1) v1102_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1102_mg : Scalar.QComplex := ((-93086393083480542116809 : Int)/10^30,(82692283635452903156 : Int)/10^30)
theorem v1102_mg_checked : Scalar.distance (sourceCoefficient 12 17 3 2) v1102_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1102_upper : Scalar.QComplex := ((999998466485149919172244403966 : Int)/10^30,(-1751293050432696741582231184 : Int)/10^30)
theorem v1102_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 17 5) 1) 14) v1102_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1102 : Material (12 : Basis) (17 : Basis) where
  plus := ![v1102_pa,v1102_pb,v1102_pg]
  minus := ![(Primitive.Addresses.material1102 1).one,v1102_mb,v1102_mg]
  upper := v1102_upper
  lower := (Primitive.Addresses.material1102 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1102_pa_checked.trans (by decide +kernel)
    · exact v1102_pb_checked.trans (by decide +kernel)
    · exact v1102_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 17 Primitive.Addresses.material1102
    · exact v1102_mb_checked.trans (by decide +kernel)
    · exact v1102_mg_checked.trans (by decide +kernel)
  upper_error := v1102_upper_checked
  lower_error := reuse_lower_error 12 17 Primitive.Addresses.material1102

def v1103_pa : Scalar.QComplex := ((999999998862168141395330585182 : Int)/10^30,(-47703917196753114135986984 : Int)/10^30)
theorem v1103_pa_checked : Scalar.distance (sourceCoefficient 12 18 1 0) v1103_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1103_pb : Scalar.QComplex := ((-20583167879224647817999 : Int)/10^30,(-431477519359886485637655006 : Int)/10^30)
theorem v1103_pb_checked : Scalar.distance (sourceCoefficient 12 18 1 1) v1103_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1103_pg : Scalar.QComplex := ((-93086429667029258531304 : Int)/10^30,(4440587338029988050 : Int)/10^30)
theorem v1103_pg_checked : Scalar.distance (sourceCoefficient 12 18 1 2) v1103_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1103_mb : Scalar.QComplex := ((-392928826396668454331129 : Int)/10^30,(-431477340938739682851646515 : Int)/10^30)
theorem v1103_mb_checked : Scalar.distance (sourceCoefficient 12 18 3 1) v1103_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1103_mg : Scalar.QComplex := ((-93086391174670357405421 : Int)/10^30,(84769982030081749676 : Int)/10^30)
theorem v1103_mg_checked : Scalar.distance (sourceCoefficient 12 18 3 2) v1103_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1103_upper : Scalar.QComplex := ((999998427147004671723193005731 : Int)/10^30,(-1773613124892237794486489951 : Int)/10^30)
theorem v1103_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 18 5) 1) 14) v1103_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1103 : Material (12 : Basis) (18 : Basis) where
  plus := ![v1103_pa,v1103_pb,v1103_pg]
  minus := ![(Primitive.Addresses.material1103 1).one,v1103_mb,v1103_mg]
  upper := v1103_upper
  lower := (Primitive.Addresses.material1103 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1103_pa_checked.trans (by decide +kernel)
    · exact v1103_pb_checked.trans (by decide +kernel)
    · exact v1103_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 18 Primitive.Addresses.material1103
    · exact v1103_mb_checked.trans (by decide +kernel)
    · exact v1103_mg_checked.trans (by decide +kernel)
  upper_error := v1103_upper_checked
  lower_error := reuse_lower_error 12 18 Primitive.Addresses.material1103

def v1104_pa : Scalar.QComplex := ((999999997993035942089960694084 : Int)/10^30,(-63355568909072025490146170 : Int)/10^30)
theorem v1104_pa_checked : Scalar.distance (sourceCoefficient 12 19 1 0) v1104_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1104_pb : Scalar.QComplex := ((-27336503722474936248118 : Int)/10^30,(-431477518682610720906535673 : Int)/10^30)
theorem v1104_pb_checked : Scalar.distance (sourceCoefficient 12 19 1 1) v1104_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1104_pg : Scalar.QComplex := ((-93086429553519731643906 : Int)/10^30,(5897543713913656321 : Int)/10^30)
theorem v1104_pg_checked : Scalar.distance (sourceCoefficient 12 19 1 2) v1104_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1104_mb : Scalar.QComplex := ((-399682159140884684029019 : Int)/10^30,(-431477334433639496531717340 : Int)/10^30)
theorem v1104_mb_checked : Scalar.distance (sourceCoefficient 12 19 3 1) v1104_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1104_mg : Scalar.QComplex := ((-93086389803873139274485 : Int)/10^30,(86226937765520363584 : Int)/10^30)
theorem v1104_mg_checked : Scalar.distance (sourceCoefficient 12 19 3 2) v1104_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1104_upper : Scalar.QComplex := ((999998399264542818177336265403 : Int)/10^30,(-1789264751793216723560543053 : Int)/10^30)
theorem v1104_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 19 5) 1) 14) v1104_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1104 : Material (12 : Basis) (19 : Basis) where
  plus := ![v1104_pa,v1104_pb,v1104_pg]
  minus := ![(Primitive.Addresses.material1104 1).one,v1104_mb,v1104_mg]
  upper := v1104_upper
  lower := (Primitive.Addresses.material1104 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1104_pa_checked.trans (by decide +kernel)
    · exact v1104_pb_checked.trans (by decide +kernel)
    · exact v1104_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 19 Primitive.Addresses.material1104
    · exact v1104_mb_checked.trans (by decide +kernel)
    · exact v1104_mg_checked.trans (by decide +kernel)
  upper_error := v1104_upper_checked
  lower_error := reuse_lower_error 12 19 Primitive.Addresses.material1104

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
