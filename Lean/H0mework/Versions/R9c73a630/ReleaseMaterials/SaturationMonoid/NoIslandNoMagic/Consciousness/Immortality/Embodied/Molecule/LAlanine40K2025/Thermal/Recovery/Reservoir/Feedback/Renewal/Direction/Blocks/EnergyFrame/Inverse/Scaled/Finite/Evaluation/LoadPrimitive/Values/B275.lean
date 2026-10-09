import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B183
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B184

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4401_pa : Scalar.QComplex := ((999996857093030721577726730816 : Int)/10^30,(-2507150585962603684559736141 : Int)/10^30)
theorem v4401_pa_checked : Scalar.distance (sourceCoefficient 70 97 1 0) v4401_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4401_pb : Scalar.QComplex := ((-1081779047105238638820722 : Int)/10^30,(-431476135989251620517518500 : Int)/10^30)
theorem v4401_pb_checked : Scalar.distance (sourceCoefficient 70 97 1 1) v4401_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4401_pg : Scalar.QComplex := ((-93086134215652999575033 : Int)/10^30,(233381689440706234987 : Int)/10^30)
theorem v4401_pg_checked : Scalar.distance (sourceCoefficient 70 97 1 2) v4401_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4401_mb : Scalar.QComplex := ((-1454123116704404373843099 : Int)/10^30,(-431475041804370625977497888 : Int)/10^30)
theorem v4401_mb_checked : Scalar.distance (sourceCoefficient 70 97 3 1) v4401_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4401_mg : Scalar.QComplex := ((-93085898157544118361497 : Int)/10^30,(313710743926291483073 : Int)/10^30)
theorem v4401_mg_checked : Scalar.distance (sourceCoefficient 70 97 3 2) v4401_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4401_upper : Scalar.QComplex := ((999991040600715516997999429574 : Int)/10^30,(-4233050708192670021586653610 : Int)/10^30)
theorem v4401_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 97 5) 1) 14) v4401_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4401 : Material (70 : Basis) (97 : Basis) where
  plus := ![v4401_pa,v4401_pb,v4401_pg]
  minus := ![(Primitive.Addresses.material4401 1).one,v4401_mb,v4401_mg]
  upper := v4401_upper
  lower := (Primitive.Addresses.material4401 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4401_pa_checked.trans (by decide +kernel)
    · exact v4401_pb_checked.trans (by decide +kernel)
    · exact v4401_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 97 Primitive.Addresses.material4401
    · exact v4401_mb_checked.trans (by decide +kernel)
    · exact v4401_mg_checked.trans (by decide +kernel)
  upper_error := v4401_upper_checked
  lower_error := reuse_lower_error 70 97 Primitive.Addresses.material4401

def v4402_pa : Scalar.QComplex := ((999998102706292268858690266727 : Int)/10^30,(-1947969151639437339291879779 : Int)/10^30)
theorem v4402_pa_checked : Scalar.distance (sourceCoefficient 71 72 1 0) v4402_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4402_pb : Scalar.QComplex := ((-840504900437772085982335 : Int)/10^30,(-431476702311088525916661617 : Int)/10^30)
theorem v4402_pb_checked : Scalar.distance (sourceCoefficient 71 72 1 1) v4402_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4402_pg : Scalar.QComplex := ((-93086253279287178764612 : Int)/10^30,(181329493865054573865 : Int)/10^30)
theorem v4402_pg_checked : Scalar.distance (sourceCoefficient 71 72 1 2) v4402_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4402_mb : Scalar.QComplex := ((-1212849548584568459198336 : Int)/10^30,(-431475816334718653718873067 : Int)/10^30)
theorem v4402_mb_checked : Scalar.distance (sourceCoefficient 71 72 3 1) v4402_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4402_mg : Scalar.QComplex := ((-93086062139834402643385 : Int)/10^30,(261658670478605007244 : Int)/10^30)
theorem v4402_mg_checked : Scalar.distance (sourceCoefficient 71 72 3 2) v4402_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4402_upper : Scalar.QComplex := ((999993251308548967978849501815 : Int)/10^30,(-3673872256520052313440969146 : Int)/10^30)
theorem v4402_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 72 5) 1) 14) v4402_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4402 : Material (71 : Basis) (72 : Basis) where
  plus := ![v4402_pa,v4402_pb,v4402_pg]
  minus := ![(Primitive.Addresses.material4402 1).one,v4402_mb,v4402_mg]
  upper := v4402_upper
  lower := (Primitive.Addresses.material4402 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4402_pa_checked.trans (by decide +kernel)
    · exact v4402_pb_checked.trans (by decide +kernel)
    · exact v4402_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 72 Primitive.Addresses.material4402
    · exact v4402_mb_checked.trans (by decide +kernel)
    · exact v4402_mg_checked.trans (by decide +kernel)
  upper_error := v4402_upper_checked
  lower_error := reuse_lower_error 71 72 Primitive.Addresses.material4402

def v4403_pa : Scalar.QComplex := ((999998084254032143222866915960 : Int)/10^30,(-1957418776253804332212020185 : Int)/10^30)
theorem v4403_pa_checked : Scalar.distance (sourceCoefficient 71 73 1 0) v4403_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4403_pb : Scalar.QComplex := ((-844582200957590651855840 : Int)/10^30,(-431476694307102114711517135 : Int)/10^30)
theorem v4403_pb_checked : Scalar.distance (sourceCoefficient 71 73 1 1) v4403_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4403_pg : Scalar.QComplex := ((-93086251557074575601859 : Int)/10^30,(182209125675300522996 : Int)/10^30)
theorem v4403_pg_checked : Scalar.distance (sourceCoefficient 71 73 1 2) v4403_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4403_mb : Scalar.QComplex := ((-1216926840679141913000204 : Int)/10^30,(-431475804812208508958815854 : Int)/10^30)
theorem v4403_mb_checked : Scalar.distance (sourceCoefficient 71 73 3 1) v4403_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4403_mg : Scalar.QComplex := ((-93086059658539805642915 : Int)/10^30,(262538300475131921307 : Int)/10^30)
theorem v4403_mg_checked : Scalar.distance (sourceCoefficient 71 73 3 2) v4403_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4403_upper : Scalar.QComplex := ((999993216547121503667941142590 : Int)/10^30,(-3683321835213386473258877726 : Int)/10^30)
theorem v4403_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 73 5) 1) 14) v4403_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4403 : Material (71 : Basis) (73 : Basis) where
  plus := ![v4403_pa,v4403_pb,v4403_pg]
  minus := ![(Primitive.Addresses.material4403 1).one,v4403_mb,v4403_mg]
  upper := v4403_upper
  lower := (Primitive.Addresses.material4403 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4403_pa_checked.trans (by decide +kernel)
    · exact v4403_pb_checked.trans (by decide +kernel)
    · exact v4403_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 73 Primitive.Addresses.material4403
    · exact v4403_mb_checked.trans (by decide +kernel)
    · exact v4403_mg_checked.trans (by decide +kernel)
  upper_error := v4403_upper_checked
  lower_error := reuse_lower_error 71 73 Primitive.Addresses.material4403

def v4404_pa : Scalar.QComplex := ((999998063383932034588721287640 : Int)/10^30,(-1968051926512364118219847920 : Int)/10^30)
theorem v4404_pa_checked : Scalar.distance (sourceCoefficient 71 74 1 0) v4404_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4404_pb : Scalar.QComplex := ((-849170166146811551262899 : Int)/10^30,(-431476685239223806498637427 : Int)/10^30)
theorem v4404_pb_checked : Scalar.distance (sourceCoefficient 71 74 1 1) v4404_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4404_pg : Scalar.QComplex := ((-93086249607566561495104 : Int)/10^30,(183198927657969106178 : Int)/10^30)
theorem v4404_pg_checked : Scalar.distance (sourceCoefficient 71 74 1 2) v4404_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4404_mb : Scalar.QComplex := ((-1221514796334883114183445 : Int)/10^30,(-431475791785126253115314036 : Int)/10^30)
theorem v4404_mb_checked : Scalar.distance (sourceCoefficient 71 74 3 1) v4404_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4404_mg : Scalar.QComplex := ((-93086056854877985410551 : Int)/10^30,(263528100406914376564 : Int)/10^30)
theorem v4404_mg_checked : Scalar.distance (sourceCoefficient 71 74 3 2) v4404_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4404_upper : Scalar.QComplex := ((999993177325199764178308510906 : Int)/10^30,(-3693954933615218539902293768 : Int)/10^30)
theorem v4404_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 74 5) 1) 14) v4404_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4404 : Material (71 : Basis) (74 : Basis) where
  plus := ![v4404_pa,v4404_pb,v4404_pg]
  minus := ![(Primitive.Addresses.material4404 1).one,v4404_mb,v4404_mg]
  upper := v4404_upper
  lower := (Primitive.Addresses.material4404 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4404_pa_checked.trans (by decide +kernel)
    · exact v4404_pb_checked.trans (by decide +kernel)
    · exact v4404_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 74 Primitive.Addresses.material4404
    · exact v4404_mb_checked.trans (by decide +kernel)
    · exact v4404_mg_checked.trans (by decide +kernel)
  upper_error := v4404_upper_checked
  lower_error := reuse_lower_error 71 74 Primitive.Addresses.material4404

def v4405_pa : Scalar.QComplex := ((999998034117245171001974227968 : Int)/10^30,(-1982867026545902880225639081 : Int)/10^30)
theorem v4405_pa_checked : Scalar.distance (sourceCoefficient 71 75 1 0) v4405_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4405_pb : Scalar.QComplex := ((-855562548552827508266231 : Int)/10^30,(-431476672496556646279751961 : Int)/10^30)
theorem v4405_pb_checked : Scalar.distance (sourceCoefficient 71 75 1 1) v4405_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4405_pg : Scalar.QComplex := ((-93086246870857190804498 : Int)/10^30,(184578012403865959650 : Int)/10^30)
theorem v4405_pg_checked : Scalar.distance (sourceCoefficient 71 75 1 2) v4405_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4405_mb : Scalar.QComplex := ((-1227907165364375104274276 : Int)/10^30,(-431475773526125723398144413 : Int)/10^30)
theorem v4405_mb_checked : Scalar.distance (sourceCoefficient 71 75 3 1) v4405_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4405_mg : Scalar.QComplex := ((-93086052928081609684196 : Int)/10^30,(264907182277658021761 : Int)/10^30)
theorem v4405_mg_checked : Scalar.distance (sourceCoefficient 71 75 3 2) v4405_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4405_upper : Scalar.QComplex := ((999993122489037847372005681985 : Int)/10^30,(-3708769961071759632393122247 : Int)/10^30)
theorem v4405_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 75 5) 1) 14) v4405_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4405 : Material (71 : Basis) (75 : Basis) where
  plus := ![v4405_pa,v4405_pb,v4405_pg]
  minus := ![(Primitive.Addresses.material4405 1).one,v4405_mb,v4405_mg]
  upper := v4405_upper
  lower := (Primitive.Addresses.material4405 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4405_pa_checked.trans (by decide +kernel)
    · exact v4405_pb_checked.trans (by decide +kernel)
    · exact v4405_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 75 Primitive.Addresses.material4405
    · exact v4405_mb_checked.trans (by decide +kernel)
    · exact v4405_mg_checked.trans (by decide +kernel)
  upper_error := v4405_upper_checked
  lower_error := reuse_lower_error 71 75 Primitive.Addresses.material4405

def v4406_pa : Scalar.QComplex := ((999998009392586666908572503572 : Int)/10^30,(-1995297186924371133122345471 : Int)/10^30)
theorem v4406_pa_checked : Scalar.distance (sourceCoefficient 71 76 1 0) v4406_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4406_pb : Scalar.QComplex := ((-860925883094518674989811 : Int)/10^30,(-431476661707790774182873205 : Int)/10^30)
theorem v4406_pb_checked : Scalar.distance (sourceCoefficient 71 76 1 1) v4406_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4406_pg : Scalar.QComplex := ((-93086244556314553186504 : Int)/10^30,(185735091630218799077 : Int)/10^30)
theorem v4406_pg_checked : Scalar.distance (sourceCoefficient 71 76 1 2) v4406_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4406_mb : Scalar.QComplex := ((-1233270488598832664986200 : Int)/10^30,(-431475758109047714593185546 : Int)/10^30)
theorem v4406_mb_checked : Scalar.distance (sourceCoefficient 71 76 3 1) v4406_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4406_mg : Scalar.QComplex := ((-93086049615032574447537 : Int)/10^30,(266064259075831330950 : Int)/10^30)
theorem v4406_mg_checked : Scalar.distance (sourceCoefficient 71 76 3 2) v4406_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4406_upper : Scalar.QComplex := ((999993076311087009857653425130 : Int)/10^30,(-3721200060264446576202206568 : Int)/10^30)
theorem v4406_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 76 5) 1) 14) v4406_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4406 : Material (71 : Basis) (76 : Basis) where
  plus := ![v4406_pa,v4406_pb,v4406_pg]
  minus := ![(Primitive.Addresses.material4406 1).one,v4406_mb,v4406_mg]
  upper := v4406_upper
  lower := (Primitive.Addresses.material4406 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4406_pa_checked.trans (by decide +kernel)
    · exact v4406_pb_checked.trans (by decide +kernel)
    · exact v4406_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 76 Primitive.Addresses.material4406
    · exact v4406_mb_checked.trans (by decide +kernel)
    · exact v4406_mg_checked.trans (by decide +kernel)
  upper_error := v4406_upper_checked
  lower_error := reuse_lower_error 71 76 Primitive.Addresses.material4406

def v4407_pa : Scalar.QComplex := ((999998003646592505765948686465 : Int)/10^30,(-1998174874619721688183859420 : Int)/10^30)
theorem v4407_pa_checked : Scalar.distance (sourceCoefficient 71 77 1 0) v4407_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4407_pb : Scalar.QComplex := ((-862167540584265316924815 : Int)/10^30,(-431476659197428381312766023 : Int)/10^30)
theorem v4407_pb_checked : Scalar.distance (sourceCoefficient 71 77 1 1) v4407_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4407_pg : Scalar.QComplex := ((-93086244018086263756567 : Int)/10^30,(186002965297313913417 : Int)/10^30)
theorem v4407_pg_checked : Scalar.distance (sourceCoefficient 71 77 1 2) v4407_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4407_mb : Scalar.QComplex := ((-1234512143459923794416105 : Int)/10^30,(-431475754527191764971783852 : Int)/10^30)
theorem v4407_mb_checked : Scalar.distance (sourceCoefficient 71 77 3 1) v4407_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4407_mg : Scalar.QComplex := ((-93086048845641575303614 : Int)/10^30,(266332132178718063723 : Int)/10^30)
theorem v4407_mg_checked : Scalar.distance (sourceCoefficient 71 77 3 2) v4407_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4407_upper : Scalar.QComplex := ((999993065598473506311722130309 : Int)/10^30,(-3724077733756754696367737407 : Int)/10^30)
theorem v4407_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 77 5) 1) 14) v4407_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4407 : Material (71 : Basis) (77 : Basis) where
  plus := ![v4407_pa,v4407_pb,v4407_pg]
  minus := ![(Primitive.Addresses.material4407 1).one,v4407_mb,v4407_mg]
  upper := v4407_upper
  lower := (Primitive.Addresses.material4407 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4407_pa_checked.trans (by decide +kernel)
    · exact v4407_pb_checked.trans (by decide +kernel)
    · exact v4407_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 77 Primitive.Addresses.material4407
    · exact v4407_mb_checked.trans (by decide +kernel)
    · exact v4407_mg_checked.trans (by decide +kernel)
  upper_error := v4407_upper_checked
  lower_error := reuse_lower_error 71 77 Primitive.Addresses.material4407

def v4408_pa : Scalar.QComplex := ((999997968929350325697630530938 : Int)/10^30,(-2015474429036652593408833913 : Int)/10^30)
theorem v4408_pa_checked : Scalar.distance (sourceCoefficient 71 78 1 0) v4408_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4408_pb : Scalar.QComplex := ((-869631909003856074883422 : Int)/10^30,(-431476644005685342743445544 : Int)/10^30)
theorem v4408_pb_checked : Scalar.distance (sourceCoefficient 71 78 1 1) v4408_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4408_pg : Scalar.QComplex := ((-93086240763510215996559 : Int)/10^30,(187613319009909857766 : Int)/10^30)
theorem v4408_pg_checked : Scalar.distance (sourceCoefficient 71 78 1 2) v4408_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4408_mb : Scalar.QComplex := ((-1241976495990399019693753 : Int)/10^30,(-431475732894040619549800368 : Int)/10^30)
theorem v4408_mb_checked : Scalar.distance (sourceCoefficient 71 78 3 1) v4408_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4408_mg : Scalar.QComplex := ((-93086044201404013039574 : Int)/10^30,(267942482483153175519 : Int)/10^30)
theorem v4408_mg_checked : Scalar.distance (sourceCoefficient 71 78 3 2) v4408_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4408_upper : Scalar.QComplex := ((999993001023821513191913065417 : Int)/10^30,(-3741377202489220966796511810 : Int)/10^30)
theorem v4408_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 78 5) 1) 14) v4408_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4408 : Material (71 : Basis) (78 : Basis) where
  plus := ![v4408_pa,v4408_pb,v4408_pg]
  minus := ![(Primitive.Addresses.material4408 1).one,v4408_mb,v4408_mg]
  upper := v4408_upper
  lower := (Primitive.Addresses.material4408 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4408_pa_checked.trans (by decide +kernel)
    · exact v4408_pb_checked.trans (by decide +kernel)
    · exact v4408_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 78 Primitive.Addresses.material4408
    · exact v4408_mb_checked.trans (by decide +kernel)
    · exact v4408_mg_checked.trans (by decide +kernel)
  upper_error := v4408_upper_checked
  lower_error := reuse_lower_error 71 78 Primitive.Addresses.material4408

def v4409_pa : Scalar.QComplex := ((999997957673334155646129612576 : Int)/10^30,(-2021051498747742875501100812 : Int)/10^30)
theorem v4409_pa_checked : Scalar.distance (sourceCoefficient 71 79 1 0) v4409_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4409_pb : Scalar.QComplex := ((-872038289057017173071643 : Int)/10^30,(-431476639071436571493060376 : Int)/10^30)
theorem v4409_pb_checked : Scalar.distance (sourceCoefficient 71 79 1 1) v4409_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4409_pg : Scalar.QComplex := ((-93086239707364654277700 : Int)/10^30,(188132468501318120074 : Int)/10^30)
theorem v4409_pg_checked : Scalar.distance (sourceCoefficient 71 79 1 2) v4409_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4409_mb : Scalar.QComplex := ((-1244382870889520387814690 : Int)/10^30,(-431475725883196079002075679 : Int)/10^30)
theorem v4409_mb_checked : Scalar.distance (sourceCoefficient 71 79 3 1) v4409_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4409_mg : Scalar.QComplex := ((-93086042697256215111772 : Int)/10^30,(268461630869852303138 : Int)/10^30)
theorem v4409_mg_checked : Scalar.distance (sourceCoefficient 71 79 3 2) v4409_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4409_upper : Scalar.QComplex := ((999992980142305734124388703446 : Int)/10^30,(-3746954244467058271149709998 : Int)/10^30)
theorem v4409_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 79 5) 1) 14) v4409_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4409 : Material (71 : Basis) (79 : Basis) where
  plus := ![v4409_pa,v4409_pb,v4409_pg]
  minus := ![(Primitive.Addresses.material4409 1).one,v4409_mb,v4409_mg]
  upper := v4409_upper
  lower := (Primitive.Addresses.material4409 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4409_pa_checked.trans (by decide +kernel)
    · exact v4409_pb_checked.trans (by decide +kernel)
    · exact v4409_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 79 Primitive.Addresses.material4409
    · exact v4409_mb_checked.trans (by decide +kernel)
    · exact v4409_mg_checked.trans (by decide +kernel)
  upper_error := v4409_upper_checked
  lower_error := reuse_lower_error 71 79 Primitive.Addresses.material4409

def v4410_pa : Scalar.QComplex := ((999997940028081779106951354786 : Int)/10^30,(-2029763432757000437982986378 : Int)/10^30)
theorem v4410_pa_checked : Scalar.distance (sourceCoefficient 71 80 1 0) v4410_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4410_pb : Scalar.QComplex := ((-875797292476259773477658 : Int)/10^30,(-431476631327843933488357439 : Int)/10^30)
theorem v4410_pb_checked : Scalar.distance (sourceCoefficient 71 80 1 1) v4410_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4410_pg : Scalar.QComplex := ((-93086238050801302572987 : Int)/10^30,(188943431306592389114 : Int)/10^30)
theorem v4410_pg_checked : Scalar.distance (sourceCoefficient 71 80 1 2) v4410_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4410_mb : Scalar.QComplex := ((-1248141866226742532161419 : Int)/10^30,(-431475714895755672713767268 : Int)/10^30)
theorem v4410_mb_checked : Scalar.distance (sourceCoefficient 71 80 3 1) v4410_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4410_mg : Scalar.QComplex := ((-93086040340869103678509 : Int)/10^30,(269272591943628493267 : Int)/10^30)
theorem v4410_mg_checked : Scalar.distance (sourceCoefficient 71 80 3 2) v4410_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4410_upper : Scalar.QComplex := ((999992947461071878616834337980 : Int)/10^30,(-3755666135046808665383892291 : Int)/10^30)
theorem v4410_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 80 5) 1) 14) v4410_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4410 : Material (71 : Basis) (80 : Basis) where
  plus := ![v4410_pa,v4410_pb,v4410_pg]
  minus := ![(Primitive.Addresses.material4410 1).one,v4410_mb,v4410_mg]
  upper := v4410_upper
  lower := (Primitive.Addresses.material4410 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4410_pa_checked.trans (by decide +kernel)
    · exact v4410_pb_checked.trans (by decide +kernel)
    · exact v4410_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 80 Primitive.Addresses.material4410
    · exact v4410_mb_checked.trans (by decide +kernel)
    · exact v4410_mg_checked.trans (by decide +kernel)
  upper_error := v4410_upper_checked
  lower_error := reuse_lower_error 71 80 Primitive.Addresses.material4410

def v4411_pa : Scalar.QComplex := ((999997886438982537910706206100 : Int)/10^30,(-2055995517452312942227365890 : Int)/10^30)
theorem v4411_pa_checked : Scalar.distance (sourceCoefficient 71 81 1 0) v4411_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4411_pb : Scalar.QComplex := ((-887115846388491464845533 : Int)/10^30,(-431476607747806733807341730 : Int)/10^30)
theorem v4411_pb_checked : Scalar.distance (sourceCoefficient 71 81 1 1) v4411_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4411_pg : Scalar.QComplex := ((-93086233013028220738049 : Int)/10^30,(191385282315779550975 : Int)/10^30)
theorem v4411_pg_checked : Scalar.distance (sourceCoefficient 71 81 1 2) v4411_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4411_mb : Scalar.QComplex := ((-1259460395576049220664585 : Int)/10^30,(-431475681548324995447013893 : Int)/10^30)
theorem v4411_mb_checked : Scalar.distance (sourceCoefficient 71 81 3 1) v4411_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4411_mg : Scalar.QComplex := ((-93086033195890453595125 : Int)/10^30,(271714437696231649557 : Int)/10^30)
theorem v4411_mg_checked : Scalar.distance (sourceCoefficient 71 81 3 2) v4411_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4411_upper : Scalar.QComplex := ((999992848597854024113432828968 : Int)/10^30,(-3781898088182588727889740009 : Int)/10^30)
theorem v4411_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 81 5) 1) 14) v4411_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4411 : Material (71 : Basis) (81 : Basis) where
  plus := ![v4411_pa,v4411_pb,v4411_pg]
  minus := ![(Primitive.Addresses.material4411 1).one,v4411_mb,v4411_mg]
  upper := v4411_upper
  lower := (Primitive.Addresses.material4411 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4411_pa_checked.trans (by decide +kernel)
    · exact v4411_pb_checked.trans (by decide +kernel)
    · exact v4411_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 81 Primitive.Addresses.material4411
    · exact v4411_mb_checked.trans (by decide +kernel)
    · exact v4411_mg_checked.trans (by decide +kernel)
  upper_error := v4411_upper_checked
  lower_error := reuse_lower_error 71 81 Primitive.Addresses.material4411

def v4412_pa : Scalar.QComplex := ((999997865952450519901508938832 : Int)/10^30,(-2065935755245369080958839456 : Int)/10^30)
theorem v4412_pa_checked : Scalar.distance (sourceCoefficient 71 82 1 0) v4412_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4412_pb : Scalar.QComplex := ((-891404835125074633329488 : Int)/10^30,(-431476598709091814654346110 : Int)/10^30)
theorem v4412_pb_checked : Scalar.distance (sourceCoefficient 71 82 1 1) v4412_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4412_pg : Scalar.QComplex := ((-93086231084518535694290 : Int)/10^30,(192310583518469249499 : Int)/10^30)
theorem v4412_pg_checked : Scalar.distance (sourceCoefficient 71 82 1 2) v4412_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4412_mb : Scalar.QComplex := ((-1263749374915641979429039 : Int)/10^30,(-431475668808409331031327695 : Int)/10^30)
theorem v4412_mb_checked : Scalar.distance (sourceCoefficient 71 82 3 1) v4412_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4412_mg : Scalar.QComplex := ((-93086030468888222721607 : Int)/10^30,(272639736890172420625 : Int)/10^30)
theorem v4412_mg_checked : Scalar.distance (sourceCoefficient 71 82 3 2) v4412_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4412_upper : Scalar.QComplex := ((999992810955403858900598849552 : Int)/10^30,(-3791838275812932596801883196 : Int)/10^30)
theorem v4412_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 82 5) 1) 14) v4412_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4412 : Material (71 : Basis) (82 : Basis) where
  plus := ![v4412_pa,v4412_pb,v4412_pg]
  minus := ![(Primitive.Addresses.material4412 1).one,v4412_mb,v4412_mg]
  upper := v4412_upper
  lower := (Primitive.Addresses.material4412 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4412_pa_checked.trans (by decide +kernel)
    · exact v4412_pb_checked.trans (by decide +kernel)
    · exact v4412_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 82 Primitive.Addresses.material4412
    · exact v4412_mb_checked.trans (by decide +kernel)
    · exact v4412_mg_checked.trans (by decide +kernel)
  upper_error := v4412_upper_checked
  lower_error := reuse_lower_error 71 82 Primitive.Addresses.material4412

def v4413_pa : Scalar.QComplex := ((999997837828498082933182605164 : Int)/10^30,(-2079504346917440308067406209 : Int)/10^30)
theorem v4413_pa_checked : Scalar.distance (sourceCoefficient 71 83 1 0) v4413_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4413_pb : Scalar.QComplex := ((-897259376789635491947592 : Int)/10^30,(-431476586279337911655448428 : Int)/10^30)
theorem v4413_pb_checked : Scalar.distance (sourceCoefficient 71 83 1 1) v4413_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4413_pg : Scalar.QComplex := ((-93086228434749459908061 : Int)/10^30,(193573635207608905774 : Int)/10^30)
theorem v4413_pg_checked : Scalar.distance (sourceCoefficient 71 83 1 2) v4413_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4413_mb : Scalar.QComplex := ((-1269603903673971607605467 : Int)/10^30,(-431475651326454278450210768 : Int)/10^30)
theorem v4413_mb_checked : Scalar.distance (sourceCoefficient 71 83 3 1) v4413_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4413_mg : Scalar.QComplex := ((-93086026729163411574363 : Int)/10^30,(273902785822388837484 : Int)/10^30)
theorem v4413_mg_checked : Scalar.distance (sourceCoefficient 71 83 3 2) v4413_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4413_upper : Scalar.QComplex := ((999992759413335016281787093545 : Int)/10^30,(-3805406798736789885929457951 : Int)/10^30)
theorem v4413_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 83 5) 1) 14) v4413_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4413 : Material (71 : Basis) (83 : Basis) where
  plus := ![v4413_pa,v4413_pb,v4413_pg]
  minus := ![(Primitive.Addresses.material4413 1).one,v4413_mb,v4413_mg]
  upper := v4413_upper
  lower := (Primitive.Addresses.material4413 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4413_pa_checked.trans (by decide +kernel)
    · exact v4413_pb_checked.trans (by decide +kernel)
    · exact v4413_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 83 Primitive.Addresses.material4413
    · exact v4413_mb_checked.trans (by decide +kernel)
    · exact v4413_mg_checked.trans (by decide +kernel)
  upper_error := v4413_upper_checked
  lower_error := reuse_lower_error 71 83 Primitive.Addresses.material4413

def v4414_pa : Scalar.QComplex := ((999997764139300597036192719577 : Int)/10^30,(-2114643326836197329277443374 : Int)/10^30)
theorem v4414_pa_checked : Scalar.distance (sourceCoefficient 71 84 1 0) v4414_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4414_pb : Scalar.QComplex := ((-912421054797212684452505 : Int)/10^30,(-431476553597311196773748477 : Int)/10^30)
theorem v4414_pb_checked : Scalar.distance (sourceCoefficient 71 84 1 1) v4414_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4414_pg : Scalar.QComplex := ((-93086221479627171595107 : Int)/10^30,(196844597189388638737 : Int)/10^30)
theorem v4414_pg_checked : Scalar.distance (sourceCoefficient 71 84 1 2) v4414_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4414_mb : Scalar.QComplex := ((-1284765547833046043872566 : Int)/10^30,(-431475605560594468670213734 : Int)/10^30)
theorem v4414_mb_checked : Scalar.distance (sourceCoefficient 71 84 3 1) v4414_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4414_mg : Scalar.QComplex := ((-93086016951350841354325 : Int)/10^30,(277173740584282646548 : Int)/10^30)
theorem v4414_mg_checked : Scalar.distance (sourceCoefficient 71 84 3 2) v4414_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4414_upper : Scalar.QComplex := ((999992625077555725370325260085 : Int)/10^30,(-3840545599139294203805414423 : Int)/10^30)
theorem v4414_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 84 5) 1) 14) v4414_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4414 : Material (71 : Basis) (84 : Basis) where
  plus := ![v4414_pa,v4414_pb,v4414_pg]
  minus := ![(Primitive.Addresses.material4414 1).one,v4414_mb,v4414_mg]
  upper := v4414_upper
  lower := (Primitive.Addresses.material4414 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4414_pa_checked.trans (by decide +kernel)
    · exact v4414_pb_checked.trans (by decide +kernel)
    · exact v4414_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 84 Primitive.Addresses.material4414
    · exact v4414_mb_checked.trans (by decide +kernel)
    · exact v4414_mg_checked.trans (by decide +kernel)
  upper_error := v4414_upper_checked
  lower_error := reuse_lower_error 71 84 Primitive.Addresses.material4414

def v4415_pa : Scalar.QComplex := ((999997593837346115026084965787 : Int)/10^30,(-2193699960831296290536604559 : Int)/10^30)
theorem v4415_pa_checked : Scalar.distance (sourceCoefficient 71 85 1 0) v4415_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4415_pb : Scalar.QComplex := ((-946532209239278002083901 : Int)/10^30,(-431476477471486408797431432 : Int)/10^30)
theorem v4415_pb_checked : Scalar.distance (sourceCoefficient 71 85 1 1) v4415_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4415_pg : Scalar.QComplex := ((-93086205341580777009496 : Int)/10^30,(204203696359067718519 : Int)/10^30)
theorem v4415_pg_checked : Scalar.distance (sourceCoefficient 71 85 1 2) v4415_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4415_mb : Scalar.QComplex := ((-1318876623880811393801036 : Int)/10^30,(-431475499998408051680804432 : Int)/10^30)
theorem v4415_mb_checked : Scalar.distance (sourceCoefficient 71 85 3 1) v4415_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4415_mg : Scalar.QComplex := ((-93085994462739313790801 : Int)/10^30,(284532823087425570113 : Int)/10^30)
theorem v4415_mg_checked : Scalar.distance (sourceCoefficient 71 85 3 2) v4415_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4415_upper : Scalar.QComplex := ((999992318331276574387282701247 : Int)/10^30,(-3919601821463099710619881195 : Int)/10^30)
theorem v4415_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 85 5) 1) 14) v4415_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4415 : Material (71 : Basis) (85 : Basis) where
  plus := ![v4415_pa,v4415_pb,v4415_pg]
  minus := ![(Primitive.Addresses.material4415 1).one,v4415_mb,v4415_mg]
  upper := v4415_upper
  lower := (Primitive.Addresses.material4415 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4415_pa_checked.trans (by decide +kernel)
    · exact v4415_pb_checked.trans (by decide +kernel)
    · exact v4415_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 85 Primitive.Addresses.material4415
    · exact v4415_mb_checked.trans (by decide +kernel)
    · exact v4415_mg_checked.trans (by decide +kernel)
  upper_error := v4415_upper_checked
  lower_error := reuse_lower_error 71 85 Primitive.Addresses.material4415

def v4416_pa : Scalar.QComplex := ((999997561736657258072474719775 : Int)/10^30,(-2208284569605042205082771416 : Int)/10^30)
theorem v4416_pa_checked : Scalar.distance (sourceCoefficient 71 86 1 0) v4416_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4416_pb : Scalar.QComplex := ((-952825138705913984588715 : Int)/10^30,(-431476463034708079930569874 : Int)/10^30)
theorem v4416_pb_checked : Scalar.distance (sourceCoefficient 71 86 1 1) v4416_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4416_pg : Scalar.QComplex := ((-93086202290225112344669 : Int)/10^30,(205561325373281999343 : Int)/10^30)
theorem v4416_pg_checked : Scalar.distance (sourceCoefficient 71 86 1 2) v4416_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4416_mb : Scalar.QComplex := ((-1325169538546012645339829 : Int)/10^30,(-431475480131120391601475330 : Int)/10^30)
theorem v4416_mb_checked : Scalar.distance (sourceCoefficient 71 86 3 1) v4416_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4416_mg : Scalar.QComplex := ((-93085990239812091359196 : Int)/10^30,(285890448962950011586 : Int)/10^30)
theorem v4416_mg_checked : Scalar.distance (sourceCoefficient 71 86 3 2) v4416_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4416_upper : Scalar.QComplex := ((999992261058923889525886840105 : Int)/10^30,(-3934186353111907269808500829 : Int)/10^30)
theorem v4416_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 71 86 5) 1) 14) v4416_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4416 : Material (71 : Basis) (86 : Basis) where
  plus := ![v4416_pa,v4416_pb,v4416_pg]
  minus := ![(Primitive.Addresses.material4416 1).one,v4416_mb,v4416_mg]
  upper := v4416_upper
  lower := (Primitive.Addresses.material4416 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4416_pa_checked.trans (by decide +kernel)
    · exact v4416_pb_checked.trans (by decide +kernel)
    · exact v4416_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 71 86 Primitive.Addresses.material4416
    · exact v4416_mb_checked.trans (by decide +kernel)
    · exact v4416_mg_checked.trans (by decide +kernel)
  upper_error := v4416_upper_checked
  lower_error := reuse_lower_error 71 86 Primitive.Addresses.material4416

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
