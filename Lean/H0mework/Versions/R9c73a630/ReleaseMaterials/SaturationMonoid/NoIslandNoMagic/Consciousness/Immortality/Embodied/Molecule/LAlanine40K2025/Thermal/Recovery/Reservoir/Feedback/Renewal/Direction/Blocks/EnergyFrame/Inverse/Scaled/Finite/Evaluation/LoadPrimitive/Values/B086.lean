import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B057
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B058

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1377_pa : Scalar.QComplex := ((999999847996252188658961520502 : Int)/10^30,(-551368726459474420801764817 : Int)/10^30)
theorem v1377_pa_checked : Scalar.distance (sourceCoefficient 15 43 1 0) v1377_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1377_pb : Scalar.QComplex := ((-237903203507058024213074 : Int)/10^30,(-431477441371287763885581087 : Int)/10^30)
theorem v1377_pb_checked : Scalar.distance (sourceCoefficient 15 43 1 1) v1377_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1377_pg : Scalar.QComplex := ((-93086414232662309749108 : Int)/10^30,(51324945467726178886 : Int)/10^30)
theorem v1377_pg_checked : Scalar.distance (sourceCoefficient 15 43 1 2) v1377_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1377_mb : Scalar.QComplex := ((-610248713805672329429233 : Int)/10^30,(-431477075412766984065949487 : Int)/10^30)
theorem v1377_mb_checked : Scalar.distance (sourceCoefficient 15 43 3 1) v1377_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1377_mg : Scalar.QComplex := ((-93086335281219682719754 : Int)/10^30,(131654309383425149089 : Int)/10^30)
theorem v1377_mg_checked : Scalar.distance (sourceCoefficient 15 43 3 2) v1377_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1377_upper : Scalar.QComplex := ((999997407001544743158807503717 : Int)/10^30,(-2277276923624505843472665547 : Int)/10^30)
theorem v1377_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 43 5) 1) 14) v1377_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1377 : Material (15 : Basis) (43 : Basis) where
  plus := ![v1377_pa,v1377_pb,v1377_pg]
  minus := ![(Primitive.Addresses.material1377 1).one,v1377_mb,v1377_mg]
  upper := v1377_upper
  lower := (Primitive.Addresses.material1377 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1377_pa_checked.trans (by decide +kernel)
    · exact v1377_pb_checked.trans (by decide +kernel)
    · exact v1377_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 43 Primitive.Addresses.material1377
    · exact v1377_mb_checked.trans (by decide +kernel)
    · exact v1377_mg_checked.trans (by decide +kernel)
  upper_error := v1377_upper_checked
  lower_error := reuse_lower_error 15 43 Primitive.Addresses.material1377

def v1378_pa : Scalar.QComplex := ((999999844750413470698170623032 : Int)/10^30,(-557224504985351071588771644 : Int)/10^30)
theorem v1378_pa_checked : Scalar.distance (sourceCoefficient 15 44 1 0) v1378_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1378_pb : Scalar.QComplex := ((-240429840017937702615728 : Int)/10^30,(-431477439596137525661074391 : Int)/10^30)
theorem v1378_pb_checked : Scalar.distance (sourceCoefficient 15 44 1 1) v1378_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1378_pg : Scalar.QComplex := ((-93086413890106175760047 : Int)/10^30,(51870038953578022774 : Int)/10^30)
theorem v1378_pg_checked : Scalar.distance (sourceCoefficient 15 44 1 2) v1378_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1378_mb : Scalar.QComplex := ((-612775347843895056049458 : Int)/10^30,(-431477071457243893406005479 : Int)/10^30)
theorem v1378_mb_checked : Scalar.distance (sourceCoefficient 15 44 3 1) v1378_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1378_mg : Scalar.QComplex := ((-93086334468272548089116 : Int)/10^30,(132199402370703260715 : Int)/10^30)
theorem v1378_mg_checked : Scalar.distance (sourceCoefficient 15 44 3 2) v1378_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1378_upper : Scalar.QComplex := ((999997393649168355908515018554 : Int)/10^30,(-2283132687826865081020118221 : Int)/10^30)
theorem v1378_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 44 5) 1) 14) v1378_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1378 : Material (15 : Basis) (44 : Basis) where
  plus := ![v1378_pa,v1378_pb,v1378_pg]
  minus := ![(Primitive.Addresses.material1378 1).one,v1378_mb,v1378_mg]
  upper := v1378_upper
  lower := (Primitive.Addresses.material1378 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1378_pa_checked.trans (by decide +kernel)
    · exact v1378_pb_checked.trans (by decide +kernel)
    · exact v1378_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 44 Primitive.Addresses.material1378
    · exact v1378_mb_checked.trans (by decide +kernel)
    · exact v1378_mg_checked.trans (by decide +kernel)
  upper_error := v1378_upper_checked
  lower_error := reuse_lower_error 15 44 Primitive.Addresses.material1378

def v1379_pa : Scalar.QComplex := ((999999843122794531938483527425 : Int)/10^30,(-560137827972424513236053069 : Int)/10^30)
theorem v1379_pa_checked : Scalar.distance (sourceCoefficient 15 45 1 0) v1379_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1379_pb : Scalar.QComplex := ((-241686873250837455066261 : Int)/10^30,(-431477438705629396558557755 : Int)/10^30)
theorem v1379_pb_checked : Scalar.distance (sourceCoefficient 15 45 1 1) v1379_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1379_pg : Scalar.QComplex := ((-93086413718292993226655 : Int)/10^30,(52141229773677554487 : Int)/10^30)
theorem v1379_pg_checked : Scalar.distance (sourceCoefficient 15 45 1 2) v1379_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1379_mb : Scalar.QComplex := ((-614032379840275478216440 : Int)/10^30,(-431477069481973030563051448 : Int)/10^30)
theorem v1379_mb_checked : Scalar.distance (sourceCoefficient 15 45 3 1) v1379_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1379_mg : Scalar.QComplex := ((-93086334062433965764861 : Int)/10^30,(132470592941559017724 : Int)/10^30)
theorem v1379_mg_checked : Scalar.distance (sourceCoefficient 15 45 3 2) v1379_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1379_upper : Scalar.QComplex := ((999997386993420660204114582830 : Int)/10^30,(-2286046003665763524516897150 : Int)/10^30)
theorem v1379_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 45 5) 1) 14) v1379_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1379 : Material (15 : Basis) (45 : Basis) where
  plus := ![v1379_pa,v1379_pb,v1379_pg]
  minus := ![(Primitive.Addresses.material1379 1).one,v1379_mb,v1379_mg]
  upper := v1379_upper
  lower := (Primitive.Addresses.material1379 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1379_pa_checked.trans (by decide +kernel)
    · exact v1379_pb_checked.trans (by decide +kernel)
    · exact v1379_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 45 Primitive.Addresses.material1379
    · exact v1379_mb_checked.trans (by decide +kernel)
    · exact v1379_mg_checked.trans (by decide +kernel)
  upper_error := v1379_upper_checked
  lower_error := reuse_lower_error 15 45 Primitive.Addresses.material1379

def v1380_pa : Scalar.QComplex := ((999999833822668661963949461337 : Int)/10^30,(-576502068566251243807565666 : Int)/10^30)
theorem v1380_pa_checked : Scalar.distance (sourceCoefficient 15 46 1 0) v1380_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1380_pb : Scalar.QComplex := ((-248747674353701384992379 : Int)/10^30,(-431477433612869626155907438 : Int)/10^30)
theorem v1380_pb_checked : Scalar.distance (sourceCoefficient 15 46 1 1) v1380_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1380_pg : Scalar.QComplex := ((-93086412736082370314044 : Int)/10^30,(53664518415589779541 : Int)/10^30)
theorem v1380_pg_checked : Scalar.distance (sourceCoefficient 15 46 1 2) v1380_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1380_mb : Scalar.QComplex := ((-621093173919258150522462 : Int)/10^30,(-431477058296061811332753001 : Int)/10^30)
theorem v1380_mb_checked : Scalar.distance (sourceCoefficient 15 46 3 1) v1380_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1380_mg : Scalar.QComplex := ((-93086331765694216977547 : Int)/10^30,(133993880168677733216 : Int)/10^30)
theorem v1380_mg_checked : Scalar.distance (sourceCoefficient 15 46 3 2) v1380_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1380_upper : Scalar.QComplex := ((999997349450113929039643073767 : Int)/10^30,(-2302410203835802618568610651 : Int)/10^30)
theorem v1380_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 46 5) 1) 14) v1380_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1380 : Material (15 : Basis) (46 : Basis) where
  plus := ![v1380_pa,v1380_pb,v1380_pg]
  minus := ![(Primitive.Addresses.material1380 1).one,v1380_mb,v1380_mg]
  upper := v1380_upper
  lower := (Primitive.Addresses.material1380 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1380_pa_checked.trans (by decide +kernel)
    · exact v1380_pb_checked.trans (by decide +kernel)
    · exact v1380_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 46 Primitive.Addresses.material1380
    · exact v1380_mb_checked.trans (by decide +kernel)
    · exact v1380_mg_checked.trans (by decide +kernel)
  upper_error := v1380_upper_checked
  lower_error := reuse_lower_error 15 46 Primitive.Addresses.material1380

def v1381_pa : Scalar.QComplex := ((999999831544624808411659019641 : Int)/10^30,(-580440110610873661581342372 : Int)/10^30)
theorem v1381_pa_checked : Scalar.distance (sourceCoefficient 15 47 1 0) v1381_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1381_pb : Scalar.QComplex := ((-250446850756749855345914 : Int)/10^30,(-431477432364302747044461526 : Int)/10^30)
theorem v1381_pb_checked : Scalar.distance (sourceCoefficient 15 47 1 1) v1381_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1381_pg : Scalar.QComplex := ((-93086412495372743913534 : Int)/10^30,(54031096667012228667 : Int)/10^30)
theorem v1381_pg_checked : Scalar.distance (sourceCoefficient 15 47 1 2) v1381_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1381_mb : Scalar.QComplex := ((-622792348612168606514715 : Int)/10^30,(-431477055581182689353326611 : Int)/10^30)
theorem v1381_mb_checked : Scalar.distance (sourceCoefficient 15 47 3 1) v1381_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1381_mg : Scalar.QComplex := ((-93086331208644159298220 : Int)/10^30,(134360458075884779459 : Int)/10^30)
theorem v1381_mg_checked : Scalar.distance (sourceCoefficient 15 47 3 2) v1381_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1381_upper : Scalar.QComplex := ((999997340375370155731336020299 : Int)/10^30,(-2306348236083476977084159710 : Int)/10^30)
theorem v1381_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 47 5) 1) 14) v1381_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1381 : Material (15 : Basis) (47 : Basis) where
  plus := ![v1381_pa,v1381_pb,v1381_pg]
  minus := ![(Primitive.Addresses.material1381 1).one,v1381_mb,v1381_mg]
  upper := v1381_upper
  lower := (Primitive.Addresses.material1381 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1381_pa_checked.trans (by decide +kernel)
    · exact v1381_pb_checked.trans (by decide +kernel)
    · exact v1381_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 47 Primitive.Addresses.material1381
    · exact v1381_mb_checked.trans (by decide +kernel)
    · exact v1381_mg_checked.trans (by decide +kernel)
  upper_error := v1381_upper_checked
  lower_error := reuse_lower_error 15 47 Primitive.Addresses.material1381

def v1382_pa : Scalar.QComplex := ((999999815246605026851472020215 : Int)/10^30,(-607870673591414592315407779 : Int)/10^30)
theorem v1382_pa_checked : Scalar.distance (sourceCoefficient 15 48 1 0) v1382_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1382_pb : Scalar.QComplex := ((-262282520471302073773118 : Int)/10^30,(-431477423419856167531501835 : Int)/10^30)
theorem v1382_pb_checked : Scalar.distance (sourceCoefficient 15 48 1 1) v1382_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1382_pg : Scalar.QComplex := ((-93086410771978552170059 : Int)/10^30,(56584509672349978584 : Int)/10^30)
theorem v1382_pg_checked : Scalar.distance (sourceCoefficient 15 48 1 2) v1382_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1382_mb : Scalar.QComplex := ((-634628006201105518186364 : Int)/10^30,(-431477036423089535383916898 : Int)/10^30)
theorem v1382_mb_checked : Scalar.distance (sourceCoefficient 15 48 3 1) v1382_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1382_mg : Scalar.QComplex := ((-93086327281770187099393 : Int)/10^30,(136913868643258602067 : Int)/10^30)
theorem v1382_mg_checked : Scalar.distance (sourceCoefficient 15 48 3 2) v1382_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1382_upper : Scalar.QComplex := ((999997276734711424978113364358 : Int)/10^30,(-2333778730080512970410774344 : Int)/10^30)
theorem v1382_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 48 5) 1) 14) v1382_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1382 : Material (15 : Basis) (48 : Basis) where
  plus := ![v1382_pa,v1382_pb,v1382_pg]
  minus := ![(Primitive.Addresses.material1382 1).one,v1382_mb,v1382_mg]
  upper := v1382_upper
  lower := (Primitive.Addresses.material1382 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1382_pa_checked.trans (by decide +kernel)
    · exact v1382_pb_checked.trans (by decide +kernel)
    · exact v1382_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 48 Primitive.Addresses.material1382
    · exact v1382_mb_checked.trans (by decide +kernel)
    · exact v1382_mg_checked.trans (by decide +kernel)
  upper_error := v1382_upper_checked
  lower_error := reuse_lower_error 15 48 Primitive.Addresses.material1382

def v1383_pa : Scalar.QComplex := ((999999801607272519894648788335 : Int)/10^30,(-629909053435919736049542793 : Int)/10^30)
theorem v1383_pa_checked : Scalar.distance (sourceCoefficient 15 49 1 0) v1383_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1383_pb : Scalar.QComplex := ((-271791584562660687412412 : Int)/10^30,(-431477415920068382676898882 : Int)/10^30)
theorem v1383_pb_checked : Scalar.distance (sourceCoefficient 15 49 1 1) v1383_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1383_pg : Scalar.QComplex := ((-93086409328162669645441 : Int)/10^30,(58635983620604235421 : Int)/10^30)
theorem v1383_pg_checked : Scalar.distance (sourceCoefficient 15 49 1 2) v1383_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1383_mb : Scalar.QComplex := ((-644137060279825904488305 : Int)/10^30,(-431477020717410504549037826 : Int)/10^30)
theorem v1383_mb_checked : Scalar.distance (sourceCoefficient 15 49 3 1) v1383_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1383_mg : Scalar.QComplex := ((-93086324067625219786758 : Int)/10^30,(138965340581707271413 : Int)/10^30)
theorem v1383_mg_checked : Scalar.distance (sourceCoefficient 15 49 3 2) v1383_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1383_upper : Scalar.QComplex := ((999997225059154926790763149595 : Int)/10^30,(-2355817053561189589276915711 : Int)/10^30)
theorem v1383_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 49 5) 1) 14) v1383_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1383 : Material (15 : Basis) (49 : Basis) where
  plus := ![v1383_pa,v1383_pb,v1383_pg]
  minus := ![(Primitive.Addresses.material1383 1).one,v1383_mb,v1383_mg]
  upper := v1383_upper
  lower := (Primitive.Addresses.material1383 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1383_pa_checked.trans (by decide +kernel)
    · exact v1383_pb_checked.trans (by decide +kernel)
    · exact v1383_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 49 Primitive.Addresses.material1383
    · exact v1383_mb_checked.trans (by decide +kernel)
    · exact v1383_mg_checked.trans (by decide +kernel)
  upper_error := v1383_upper_checked
  lower_error := reuse_lower_error 15 49 Primitive.Addresses.material1383

def v1384_pa : Scalar.QComplex := ((999999799981763604004591379000 : Int)/10^30,(-632484334023140786817624837 : Int)/10^30)
theorem v1384_pa_checked : Scalar.distance (sourceCoefficient 15 50 1 0) v1384_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1384_pb : Scalar.QComplex := ((-272902760073928192225696 : Int)/10^30,(-431477415025452136750293033 : Int)/10^30)
theorem v1384_pb_checked : Scalar.distance (sourceCoefficient 15 50 1 1) v1384_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1384_pg : Scalar.QComplex := ((-93086409156004554276057 : Int)/10^30,(58875707277856271646 : Int)/10^30)
theorem v1384_pg_checked : Scalar.distance (sourceCoefficient 15 50 1 2) v1384_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1384_mb : Scalar.QComplex := ((-645248234605338455012435 : Int)/10^30,(-431477018863900170992341339 : Int)/10^30)
theorem v1384_mb_checked : Scalar.distance (sourceCoefficient 15 50 3 1) v1384_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1384_mg : Scalar.QComplex := ((-93086323688596449063929 : Int)/10^30,(139205064001134534280 : Int)/10^30)
theorem v1384_mg_checked : Scalar.distance (sourceCoefficient 15 50 3 2) v1384_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1384_upper : Scalar.QComplex := ((999997218988947765991630444482 : Int)/10^30,(-2358392327507351795278123554 : Int)/10^30)
theorem v1384_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 50 5) 1) 14) v1384_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1384 : Material (15 : Basis) (50 : Basis) where
  plus := ![v1384_pa,v1384_pb,v1384_pg]
  minus := ![(Primitive.Addresses.material1384 1).one,v1384_mb,v1384_mg]
  upper := v1384_upper
  lower := (Primitive.Addresses.material1384 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1384_pa_checked.trans (by decide +kernel)
    · exact v1384_pb_checked.trans (by decide +kernel)
    · exact v1384_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 50 Primitive.Addresses.material1384
    · exact v1384_mb_checked.trans (by decide +kernel)
    · exact v1384_mg_checked.trans (by decide +kernel)
  upper_error := v1384_upper_checked
  lower_error := reuse_lower_error 15 50 Primitive.Addresses.material1384

def v1385_pa : Scalar.QComplex := ((999999792771328151312454286574 : Int)/10^30,(-643783582233698046683963732 : Int)/10^30)
theorem v1385_pa_checked : Scalar.distance (sourceCoefficient 15 51 1 0) v1385_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1385_pb : Scalar.QComplex := ((-277778130905603678725832 : Int)/10^30,(-431477411055156598253963488 : Int)/10^30)
theorem v1385_pb_checked : Scalar.distance (sourceCoefficient 15 51 1 1) v1385_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1385_pg : Scalar.QComplex := ((-93086408392134368047584 : Int)/10^30,(59927513870656342511 : Int)/10^30)
theorem v1385_pg_checked : Scalar.distance (sourceCoefficient 15 51 1 2) v1385_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1385_mb : Scalar.QComplex := ((-650123600195504331176252 : Int)/10^30,(-431477010686380661633667095 : Int)/10^30)
theorem v1385_mb_checked : Scalar.distance (sourceCoefficient 15 51 3 1) v1385_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1385_mg : Scalar.QComplex := ((-93086322017064829283199 : Int)/10^30,(140256869543113373431 : Int)/10^30)
theorem v1385_mg_checked : Scalar.distance (sourceCoefficient 15 51 3 2) v1385_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1385_upper : Scalar.QComplex := ((999997192277045700764606462893 : Int)/10^30,(-2369691546444448682700072503 : Int)/10^30)
theorem v1385_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 51 5) 1) 14) v1385_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1385 : Material (15 : Basis) (51 : Basis) where
  plus := ![v1385_pa,v1385_pb,v1385_pg]
  minus := ![(Primitive.Addresses.material1385 1).one,v1385_mb,v1385_mg]
  upper := v1385_upper
  lower := (Primitive.Addresses.material1385 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1385_pa_checked.trans (by decide +kernel)
    · exact v1385_pb_checked.trans (by decide +kernel)
    · exact v1385_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 51 Primitive.Addresses.material1385
    · exact v1385_mb_checked.trans (by decide +kernel)
    · exact v1385_mg_checked.trans (by decide +kernel)
  upper_error := v1385_upper_checked
  lower_error := reuse_lower_error 15 51 Primitive.Addresses.material1385

def v1386_pa : Scalar.QComplex := ((999999776906338629543217820904 : Int)/10^30,(-667972509142503424240356038 : Int)/10^30)
theorem v1386_pa_checked : Scalar.distance (sourceCoefficient 15 52 1 0) v1386_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1386_pb : Scalar.QComplex := ((-288215107357461151825475 : Int)/10^30,(-431477402308798582396229250 : Int)/10^30)
theorem v1386_pb_checked : Scalar.distance (sourceCoefficient 15 52 1 1) v1386_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1386_pg : Scalar.QComplex := ((-93086406710262487918903 : Int)/10^30,(62179174529093308498 : Int)/10^30)
theorem v1386_pg_checked : Scalar.distance (sourceCoefficient 15 52 1 2) v1386_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1386_mb : Scalar.QComplex := ((-660560565213485431518319 : Int)/10^30,(-431476992933385288461548061 : Int)/10^30)
theorem v1386_mb_checked : Scalar.distance (sourceCoefficient 15 52 3 1) v1386_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1386_mg : Scalar.QComplex := ((-93086318392111838192684 : Int)/10^30,(142508527911774486453 : Int)/10^30)
theorem v1386_mg_checked : Scalar.distance (sourceCoefficient 15 52 3 2) v1386_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1386_upper : Scalar.QComplex := ((999997134664186365742985136620 : Int)/10^30,(-2393880409945156206578027200 : Int)/10^30)
theorem v1386_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 52 5) 1) 14) v1386_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1386 : Material (15 : Basis) (52 : Basis) where
  plus := ![v1386_pa,v1386_pb,v1386_pg]
  minus := ![(Primitive.Addresses.material1386 1).one,v1386_mb,v1386_mg]
  upper := v1386_upper
  lower := (Primitive.Addresses.material1386 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1386_pa_checked.trans (by decide +kernel)
    · exact v1386_pb_checked.trans (by decide +kernel)
    · exact v1386_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 52 Primitive.Addresses.material1386
    · exact v1386_mb_checked.trans (by decide +kernel)
    · exact v1386_mg_checked.trans (by decide +kernel)
  upper_error := v1386_upper_checked
  lower_error := reuse_lower_error 15 52 Primitive.Addresses.material1386

def v1387_pa : Scalar.QComplex := ((999999774426188626685153616415 : Int)/10^30,(-671675198189634894965544801 : Int)/10^30)
theorem v1387_pa_checked : Scalar.distance (sourceCoefficient 15 53 1 0) v1387_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1387_pb : Scalar.QComplex := ((-289812734165056740630355 : Int)/10^30,(-431477400940254070375686718 : Int)/10^30)
theorem v1387_pb_checked : Scalar.distance (sourceCoefficient 15 53 1 1) v1387_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1387_pg : Scalar.QComplex := ((-93086406447204277966787 : Int)/10^30,(62523844602928769655 : Int)/10^30)
theorem v1387_pg_checked : Scalar.distance (sourceCoefficient 15 53 1 2) v1387_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1387_mb : Scalar.QComplex := ((-662158190245219267786254 : Int)/10^30,(-431476990186161305498019515 : Int)/10^30)
theorem v1387_mb_checked : Scalar.distance (sourceCoefficient 15 53 3 1) v1387_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1387_mg : Scalar.QComplex := ((-93086317831618975833030 : Int)/10^30,(142853197630266139433 : Int)/10^30)
theorem v1387_mg_checked : Scalar.distance (sourceCoefficient 15 53 3 2) v1387_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1387_upper : Scalar.QComplex := ((999997125793534666754500187962 : Int)/10^30,(-2397583089197053382527482512 : Int)/10^30)
theorem v1387_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 53 5) 1) 14) v1387_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1387 : Material (15 : Basis) (53 : Basis) where
  plus := ![v1387_pa,v1387_pb,v1387_pg]
  minus := ![(Primitive.Addresses.material1387 1).one,v1387_mb,v1387_mg]
  upper := v1387_upper
  lower := (Primitive.Addresses.material1387 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1387_pa_checked.trans (by decide +kernel)
    · exact v1387_pb_checked.trans (by decide +kernel)
    · exact v1387_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 53 Primitive.Addresses.material1387
    · exact v1387_mb_checked.trans (by decide +kernel)
    · exact v1387_mg_checked.trans (by decide +kernel)
  upper_error := v1387_upper_checked
  lower_error := reuse_lower_error 15 53 Primitive.Addresses.material1387

def v1388_pa : Scalar.QComplex := ((999999773160008368963340996278 : Int)/10^30,(-673557667765493940441391412 : Int)/10^30)
theorem v1388_pa_checked : Scalar.distance (sourceCoefficient 15 54 1 0) v1388_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1388_pb : Scalar.QComplex := ((-290624977325519346903540 : Int)/10^30,(-431477400241453397768649981 : Int)/10^30)
theorem v1388_pb_checked : Scalar.distance (sourceCoefficient 15 54 1 1) v1388_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1388_pg : Scalar.QComplex := ((-93086406312892979066431 : Int)/10^30,(62699076959441439724 : Int)/10^30)
theorem v1388_pg_checked : Scalar.distance (sourceCoefficient 15 54 1 2) v1388_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1388_mb : Scalar.QComplex := ((-662970432500213116427041 : Int)/10^30,(-431476988786431627681137561 : Int)/10^30)
theorem v1388_mb_checked : Scalar.distance (sourceCoefficient 15 54 3 1) v1388_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1388_mg : Scalar.QComplex := ((-93086317546090095444841 : Int)/10^30,(143028429805627192864 : Int)/10^30)
theorem v1388_mg_checked : Scalar.distance (sourceCoefficient 15 54 3 2) v1388_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1388_upper : Scalar.QComplex := ((999997121278384583232623612429 : Int)/10^30,(-2399465553783882867319065734 : Int)/10^30)
theorem v1388_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 54 5) 1) 14) v1388_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1388 : Material (15 : Basis) (54 : Basis) where
  plus := ![v1388_pa,v1388_pb,v1388_pg]
  minus := ![(Primitive.Addresses.material1388 1).one,v1388_mb,v1388_mg]
  upper := v1388_upper
  lower := (Primitive.Addresses.material1388 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1388_pa_checked.trans (by decide +kernel)
    · exact v1388_pb_checked.trans (by decide +kernel)
    · exact v1388_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 54 Primitive.Addresses.material1388
    · exact v1388_mb_checked.trans (by decide +kernel)
    · exact v1388_mg_checked.trans (by decide +kernel)
  upper_error := v1388_upper_checked
  lower_error := reuse_lower_error 15 54 Primitive.Addresses.material1388

def v1389_pa : Scalar.QComplex := ((999999762707498669251864151250 : Int)/10^30,(-688901260235285883958924573 : Int)/10^30)
theorem v1389_pa_checked : Scalar.distance (sourceCoefficient 15 55 1 0) v1389_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1389_pb : Scalar.QComplex := ((-297245391347285167400162 : Int)/10^30,(-431477394469654773747488613 : Int)/10^30)
theorem v1389_pb_checked : Scalar.distance (sourceCoefficient 15 55 1 1) v1389_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1389_pg : Scalar.QComplex := ((-93086405203799203665392 : Int)/10^30,(64127357072610708815 : Int)/10^30)
theorem v1389_pg_checked : Scalar.distance (sourceCoefficient 15 55 1 2) v1389_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1389_mb : Scalar.QComplex := ((-669590839076093968382184 : Int)/10^30,(-431476977301516024359346398 : Int)/10^30)
theorem v1389_mb_checked : Scalar.distance (sourceCoefficient 15 55 3 1) v1389_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1389_mg : Scalar.QComplex := ((-93086315204455322693377 : Int)/10^30,(144456708429884523754 : Int)/10^30)
theorem v1389_mg_checked : Scalar.distance (sourceCoefficient 15 55 3 2) v1389_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1389_upper : Scalar.QComplex := ((999997084344241808281077940936 : Int)/10^30,(-2414809105361112714634311282 : Int)/10^30)
theorem v1389_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 55 5) 1) 14) v1389_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1389 : Material (15 : Basis) (55 : Basis) where
  plus := ![v1389_pa,v1389_pb,v1389_pg]
  minus := ![(Primitive.Addresses.material1389 1).one,v1389_mb,v1389_mg]
  upper := v1389_upper
  lower := (Primitive.Addresses.material1389 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1389_pa_checked.trans (by decide +kernel)
    · exact v1389_pb_checked.trans (by decide +kernel)
    · exact v1389_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 55 Primitive.Addresses.material1389
    · exact v1389_mb_checked.trans (by decide +kernel)
    · exact v1389_mg_checked.trans (by decide +kernel)
  upper_error := v1389_upper_checked
  lower_error := reuse_lower_error 15 55 Primitive.Addresses.material1389

def v1390_pa : Scalar.QComplex := ((999999760192259454325572466662 : Int)/10^30,(-692542723291203478836043930 : Int)/10^30)
theorem v1390_pa_checked : Scalar.distance (sourceCoefficient 15 56 1 0) v1390_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1390_pb : Scalar.QComplex := ((-298816600500717965898232 : Int)/10^30,(-431477393079959406890799850 : Int)/10^30)
theorem v1390_pb_checked : Scalar.distance (sourceCoefficient 15 56 1 1) v1390_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1390_pg : Scalar.QComplex := ((-93086404936826299237619 : Int)/10^30,(64466327835861832797 : Int)/10^30)
theorem v1390_pg_checked : Scalar.distance (sourceCoefficient 15 56 1 2) v1390_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1390_mb : Scalar.QComplex := ((-671162046445249279210101 : Int)/10^30,(-431476974555938440170613772 : Int)/10^30)
theorem v1390_mb_checked : Scalar.distance (sourceCoefficient 15 56 3 1) v1390_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1390_mg : Scalar.QComplex := ((-93086314644966015662549 : Int)/10^30,(144795678836535748340 : Int)/10^30)
theorem v1390_mg_checked : Scalar.distance (sourceCoefficient 15 56 3 2) v1390_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1390_upper : Scalar.QComplex := ((999997075544171455942240234385 : Int)/10^30,(-2418450558652424139777310970 : Int)/10^30)
theorem v1390_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 56 5) 1) 14) v1390_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1390 : Material (15 : Basis) (56 : Basis) where
  plus := ![v1390_pa,v1390_pb,v1390_pg]
  minus := ![(Primitive.Addresses.material1390 1).one,v1390_mb,v1390_mg]
  upper := v1390_upper
  lower := (Primitive.Addresses.material1390 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1390_pa_checked.trans (by decide +kernel)
    · exact v1390_pb_checked.trans (by decide +kernel)
    · exact v1390_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 56 Primitive.Addresses.material1390
    · exact v1390_mb_checked.trans (by decide +kernel)
    · exact v1390_mg_checked.trans (by decide +kernel)
  upper_error := v1390_upper_checked
  lower_error := reuse_lower_error 15 56 Primitive.Addresses.material1390

def v1391_pa : Scalar.QComplex := ((999999751966231806952509817449 : Int)/10^30,(-704320576772640383379707417 : Int)/10^30)
theorem v1391_pa_checked : Scalar.distance (sourceCoefficient 15 57 1 0) v1391_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1391_pb : Scalar.QComplex := ((-303898478532947447042289 : Int)/10^30,(-431477388532925401125336553 : Int)/10^30)
theorem v1391_pb_checked : Scalar.distance (sourceCoefficient 15 57 1 1) v1391_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1391_pg : Scalar.QComplex := ((-93086404063474763023893 : Int)/10^30,(65562686061437677254 : Int)/10^30)
theorem v1391_pg_checked : Scalar.distance (sourceCoefficient 15 57 1 2) v1391_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1391_mb : Scalar.QComplex := ((-676243918661377759489335 : Int)/10^30,(-431476965623474264949851302 : Int)/10^30)
theorem v1391_mb_checked : Scalar.distance (sourceCoefficient 15 57 3 1) v1391_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1391_mg : Scalar.QComplex := ((-93086312825507034107037 : Int)/10^30,(145892035900224277910 : Int)/10^30)
theorem v1391_mg_checked : Scalar.distance (sourceCoefficient 15 57 3 2) v1391_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1391_upper : Scalar.QComplex := ((999997046990649429832303808412 : Int)/10^30,(-2430228380394754347610689989 : Int)/10^30)
theorem v1391_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 57 5) 1) 14) v1391_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1391 : Material (15 : Basis) (57 : Basis) where
  plus := ![v1391_pa,v1391_pb,v1391_pg]
  minus := ![(Primitive.Addresses.material1391 1).one,v1391_mb,v1391_mg]
  upper := v1391_upper
  lower := (Primitive.Addresses.material1391 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1391_pa_checked.trans (by decide +kernel)
    · exact v1391_pb_checked.trans (by decide +kernel)
    · exact v1391_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 57 Primitive.Addresses.material1391
    · exact v1391_mb_checked.trans (by decide +kernel)
    · exact v1391_mg_checked.trans (by decide +kernel)
  upper_error := v1391_upper_checked
  lower_error := reuse_lower_error 15 57 Primitive.Addresses.material1391

def v1392_pa : Scalar.QComplex := ((999999747444816179272264419726 : Int)/10^30,(-710711125463316914607400726 : Int)/10^30)
theorem v1392_pa_checked : Scalar.distance (sourceCoefficient 15 58 1 0) v1392_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1392_pb : Scalar.QComplex := ((-306655856086548253922566 : Int)/10^30,(-431477386032350878231104957 : Int)/10^30)
theorem v1392_pb_checked : Scalar.distance (sourceCoefficient 15 58 1 1) v1392_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1392_pg : Scalar.QComplex := ((-93086403583298106830026 : Int)/10^30,(66157559364452900436 : Int)/10^30)
theorem v1392_pg_checked : Scalar.distance (sourceCoefficient 15 58 1 2) v1392_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1392_mb : Scalar.QComplex := ((-679001293030397693222474 : Int)/10^30,(-431476960743408032051251131 : Int)/10^30)
theorem v1392_mb_checked : Scalar.distance (sourceCoefficient 15 58 3 1) v1392_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1392_mg : Scalar.QComplex := ((-93086311831981688301745 : Int)/10^30,(146486908567370155385 : Int)/10^30)
theorem v1392_mg_checked : Scalar.distance (sourceCoefficient 15 58 3 2) v1392_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1392_upper : Scalar.QComplex := ((999997031439733242210310725838 : Int)/10^30,(-2436618911763906096903245390 : Int)/10^30)
theorem v1392_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 58 5) 1) 14) v1392_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1392 : Material (15 : Basis) (58 : Basis) where
  plus := ![v1392_pa,v1392_pb,v1392_pg]
  minus := ![(Primitive.Addresses.material1392 1).one,v1392_mb,v1392_mg]
  upper := v1392_upper
  lower := (Primitive.Addresses.material1392 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1392_pa_checked.trans (by decide +kernel)
    · exact v1392_pb_checked.trans (by decide +kernel)
    · exact v1392_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 58 Primitive.Addresses.material1392
    · exact v1392_mb_checked.trans (by decide +kernel)
    · exact v1392_mg_checked.trans (by decide +kernel)
  upper_error := v1392_upper_checked
  lower_error := reuse_lower_error 15 58 Primitive.Addresses.material1392

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
