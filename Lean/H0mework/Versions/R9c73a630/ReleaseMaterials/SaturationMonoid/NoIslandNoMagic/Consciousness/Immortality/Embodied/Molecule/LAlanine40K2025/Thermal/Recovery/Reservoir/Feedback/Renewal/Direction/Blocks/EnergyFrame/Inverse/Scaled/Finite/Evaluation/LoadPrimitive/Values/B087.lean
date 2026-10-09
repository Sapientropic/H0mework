import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B058

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1393_pa : Scalar.QComplex := ((999999734806235558763942450490 : Int)/10^30,(-728277047938996507124236483 : Int)/10^30)
theorem v1393_pa_checked : Scalar.distance (sourceCoefficient 15 59 1 0) v1393_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1393_pb : Scalar.QComplex := ((-314235155191370922872859 : Int)/10^30,(-431477379037886176958543013 : Int)/10^30)
theorem v1393_pb_checked : Scalar.distance (sourceCoefficient 15 59 1 1) v1393_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1393_pg : Scalar.QComplex := ((-93086402240569324226551 : Int)/10^30,(67792708205227308222 : Int)/10^30)
theorem v1393_pg_checked : Scalar.distance (sourceCoefficient 15 59 1 2) v1393_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1393_mb : Scalar.QComplex := ((-686580583277192896164000 : Int)/10^30,(-431476947208352166635437974 : Int)/10^30)
theorem v1393_mb_checked : Scalar.distance (sourceCoefficient 15 59 3 1) v1393_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1393_mg : Scalar.QComplex := ((-93086309078193600439229 : Int)/10^30,(148122055640589454629 : Int)/10^30)
theorem v1393_mg_checked : Scalar.distance (sourceCoefficient 15 59 3 2) v1393_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1393_upper : Scalar.QComplex := ((999996988483982820398937625475 : Int)/10^30,(-2454184786264164012178018990 : Int)/10^30)
theorem v1393_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 59 5) 1) 14) v1393_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1393 : Material (15 : Basis) (59 : Basis) where
  plus := ![v1393_pa,v1393_pb,v1393_pg]
  minus := ![(Primitive.Addresses.material1393 1).one,v1393_mb,v1393_mg]
  upper := v1393_upper
  lower := (Primitive.Addresses.material1393 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1393_pa_checked.trans (by decide +kernel)
    · exact v1393_pb_checked.trans (by decide +kernel)
    · exact v1393_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 59 Primitive.Addresses.material1393
    · exact v1393_mb_checked.trans (by decide +kernel)
    · exact v1393_mg_checked.trans (by decide +kernel)
  upper_error := v1393_upper_checked
  lower_error := reuse_lower_error 15 59 Primitive.Addresses.material1393

def v1394_pa : Scalar.QComplex := ((999999719843166914907710549505 : Int)/10^30,(-748540972614280783988526625 : Int)/10^30)
theorem v1394_pa_checked : Scalar.distance (sourceCoefficient 15 60 1 0) v1394_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1394_pb : Scalar.QComplex := ((-322978581245875428867729 : Int)/10^30,(-431477370748612402114872780 : Int)/10^30)
theorem v1394_pb_checked : Scalar.distance (sourceCoefficient 15 60 1 1) v1394_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1394_pg : Scalar.QComplex := ((-93086400649981136845928 : Int)/10^30,(69679004400748704562 : Int)/10^30)
theorem v1394_pg_checked : Scalar.distance (sourceCoefficient 15 60 1 2) v1394_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1394_mb : Scalar.QComplex := ((-695323998922850355097675 : Int)/10^30,(-431476931373898582521193224 : Int)/10^30)
theorem v1394_mb_checked : Scalar.distance (sourceCoefficient 15 60 3 1) v1394_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1394_mg : Scalar.QComplex := ((-93086305859817344199262 : Int)/10^30,(150008349761150601105 : Int)/10^30)
theorem v1394_mg_checked : Scalar.distance (sourceCoefficient 15 60 3 2) v1394_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1394_upper : Scalar.QComplex := ((999996938547240801621407963502 : Int)/10^30,(-2474448654933813812698238847 : Int)/10^30)
theorem v1394_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 60 5) 1) 14) v1394_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1394 : Material (15 : Basis) (60 : Basis) where
  plus := ![v1394_pa,v1394_pb,v1394_pg]
  minus := ![(Primitive.Addresses.material1394 1).one,v1394_mb,v1394_mg]
  upper := v1394_upper
  lower := (Primitive.Addresses.material1394 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1394_pa_checked.trans (by decide +kernel)
    · exact v1394_pb_checked.trans (by decide +kernel)
    · exact v1394_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 60 Primitive.Addresses.material1394
    · exact v1394_mb_checked.trans (by decide +kernel)
    · exact v1394_mg_checked.trans (by decide +kernel)
  upper_error := v1394_upper_checked
  lower_error := reuse_lower_error 15 60 Primitive.Addresses.material1394

def v1395_pa : Scalar.QComplex := ((999999715440048254400794224916 : Int)/10^30,(-754400306546088483290068512 : Int)/10^30)
theorem v1395_pa_checked : Scalar.distance (sourceCoefficient 15 61 1 0) v1395_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1395_pb : Scalar.QComplex := ((-325506751545237503981694 : Int)/10^30,(-431477368307731266706301170 : Int)/10^30)
theorem v1395_pb_checked : Scalar.distance (sourceCoefficient 15 61 1 1) v1395_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1395_pg : Scalar.QComplex := ((-93086400181749490732177 : Int)/10^30,(70224428815443757599 : Int)/10^30)
theorem v1395_pg_checked : Scalar.distance (sourceCoefficient 15 61 1 2) v1395_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1395_mb : Scalar.QComplex := ((-697852166174488598016344 : Int)/10^30,(-431476926751321252178183271 : Int)/10^30)
theorem v1395_mb_checked : Scalar.distance (sourceCoefficient 15 61 3 1) v1395_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1395_mg : Scalar.QComplex := ((-93086304920909167551463 : Int)/10^30,(150553773568696395198 : Int)/10^30)
theorem v1395_mg_checked : Scalar.distance (sourceCoefficient 15 61 3 2) v1395_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1395_upper : Scalar.QComplex := ((999996924031449887364437576008 : Int)/10^30,(-2480307972539448546054905649 : Int)/10^30)
theorem v1395_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 61 5) 1) 14) v1395_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1395 : Material (15 : Basis) (61 : Basis) where
  plus := ![v1395_pa,v1395_pb,v1395_pg]
  minus := ![(Primitive.Addresses.material1395 1).one,v1395_mb,v1395_mg]
  upper := v1395_upper
  lower := (Primitive.Addresses.material1395 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1395_pa_checked.trans (by decide +kernel)
    · exact v1395_pb_checked.trans (by decide +kernel)
    · exact v1395_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 61 Primitive.Addresses.material1395
    · exact v1395_mb_checked.trans (by decide +kernel)
    · exact v1395_mg_checked.trans (by decide +kernel)
  upper_error := v1395_upper_checked
  lower_error := reuse_lower_error 15 61 Primitive.Addresses.material1395

def v1396_pa : Scalar.QComplex := ((999999708981325747744624049231 : Int)/10^30,(-762913667338999759488049650 : Int)/10^30)
theorem v1396_pa_checked : Scalar.distance (sourceCoefficient 15 62 1 0) v1396_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1396_pb : Scalar.QComplex := ((-329180074494458189497387 : Int)/10^30,(-431477364726038650182991252 : Int)/10^30)
theorem v1396_pb_checked : Scalar.distance (sourceCoefficient 15 62 1 1) v1396_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1396_pg : Scalar.QComplex := ((-93086399494784799632620 : Int)/10^30,(71016907085195635333 : Int)/10^30)
theorem v1396_pg_checked : Scalar.distance (sourceCoefficient 15 62 1 2) v1396_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1396_mb : Scalar.QComplex := ((-701525484665123855772593 : Int)/10^30,(-431476919999717704429473708 : Int)/10^30)
theorem v1396_mb_checked : Scalar.distance (sourceCoefficient 15 62 3 1) v1396_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1396_mg : Scalar.QComplex := ((-93086303550071677340710 : Int)/10^30,(151346250950552806380 : Int)/10^30)
theorem v1396_mg_checked : Scalar.distance (sourceCoefficient 15 62 3 2) v1396_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1396_upper : Scalar.QComplex := ((999996902879448597709936337132 : Int)/10^30,(-2488821309505539855060144170 : Int)/10^30)
theorem v1396_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 62 5) 1) 14) v1396_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1396 : Material (15 : Basis) (62 : Basis) where
  plus := ![v1396_pa,v1396_pb,v1396_pg]
  minus := ![(Primitive.Addresses.material1396 1).one,v1396_mb,v1396_mg]
  upper := v1396_upper
  lower := (Primitive.Addresses.material1396 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1396_pa_checked.trans (by decide +kernel)
    · exact v1396_pb_checked.trans (by decide +kernel)
    · exact v1396_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 62 Primitive.Addresses.material1396
    · exact v1396_mb_checked.trans (by decide +kernel)
    · exact v1396_mg_checked.trans (by decide +kernel)
  upper_error := v1396_upper_checked
  lower_error := reuse_lower_error 15 62 Primitive.Addresses.material1396

def v1397_pa : Scalar.QComplex := ((999999689757348519821119233293 : Int)/10^30,(-787708833713228687745957973 : Int)/10^30)
theorem v1397_pa_checked : Scalar.distance (sourceCoefficient 15 63 1 0) v1397_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1397_pb : Scalar.QComplex := ((-339878628782589850271078 : Int)/10^30,(-431477354056788707213772394 : Int)/10^30)
theorem v1397_pb_checked : Scalar.distance (sourceCoefficient 15 63 1 1) v1397_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1397_pg : Scalar.QComplex := ((-93086397449153661298106 : Int)/10^30,(73325000317781414852 : Int)/10^30)
theorem v1397_pg_checked : Scalar.distance (sourceCoefficient 15 63 1 2) v1397_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1397_mb : Scalar.QComplex := ((-712224025762612631386436 : Int)/10^30,(-431476900098101228450204515 : Int)/10^30)
theorem v1397_mb_checked : Scalar.distance (sourceCoefficient 15 63 3 1) v1397_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1397_mg : Scalar.QComplex := ((-93086299512660793626923 : Int)/10^30,(153654341558442449759 : Int)/10^30)
theorem v1397_mg_checked : Scalar.distance (sourceCoefficient 15 63 3 2) v1397_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1397_upper : Scalar.QComplex := ((999996840861292239645297488582 : Int)/10^30,(-2513616405771440403943401896 : Int)/10^30)
theorem v1397_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 63 5) 1) 14) v1397_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1397 : Material (15 : Basis) (63 : Basis) where
  plus := ![v1397_pa,v1397_pb,v1397_pg]
  minus := ![(Primitive.Addresses.material1397 1).one,v1397_mb,v1397_mg]
  upper := v1397_upper
  lower := (Primitive.Addresses.material1397 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1397_pa_checked.trans (by decide +kernel)
    · exact v1397_pb_checked.trans (by decide +kernel)
    · exact v1397_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 63 Primitive.Addresses.material1397
    · exact v1397_mb_checked.trans (by decide +kernel)
    · exact v1397_mg_checked.trans (by decide +kernel)
  upper_error := v1397_upper_checked
  lower_error := reuse_lower_error 15 63 Primitive.Addresses.material1397

def v1398_pa : Scalar.QComplex := ((999999661215196847739773504063 : Int)/10^30,(-823146093673156907411223679 : Int)/10^30)
theorem v1398_pa_checked : Scalar.distance (sourceCoefficient 15 64 1 0) v1398_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1398_pb : Scalar.QComplex := ((-355169005768998229153064 : Int)/10^30,(-431477338194308325924490435 : Int)/10^30)
theorem v1398_pb_checked : Scalar.distance (sourceCoefficient 15 64 1 1) v1398_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1398_pg : Scalar.QComplex := ((-93086394409634150713032 : Int)/10^30,(76623727891363712570 : Int)/10^30)
theorem v1398_pg_checked : Scalar.distance (sourceCoefficient 15 64 1 2) v1398_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1398_mb : Scalar.QComplex := ((-727514383367108704021869 : Int)/10^30,(-431476871040720067232354954 : Int)/10^30)
theorem v1398_mb_checked : Scalar.distance (sourceCoefficient 15 64 3 1) v1398_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1398_mg : Scalar.QComplex := ((-93086293626489087967120 : Int)/10^30,(156953065280789269776 : Int)/10^30)
theorem v1398_mg_checked : Scalar.distance (sourceCoefficient 15 64 3 2) v1398_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1398_upper : Scalar.QComplex := ((999996751157687230020551993650 : Int)/10^30,(-2549053563690568204028526189 : Int)/10^30)
theorem v1398_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 64 5) 1) 14) v1398_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1398 : Material (15 : Basis) (64 : Basis) where
  plus := ![v1398_pa,v1398_pb,v1398_pg]
  minus := ![(Primitive.Addresses.material1398 1).one,v1398_mb,v1398_mg]
  upper := v1398_upper
  lower := (Primitive.Addresses.material1398 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1398_pa_checked.trans (by decide +kernel)
    · exact v1398_pb_checked.trans (by decide +kernel)
    · exact v1398_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 64 Primitive.Addresses.material1398
    · exact v1398_mb_checked.trans (by decide +kernel)
    · exact v1398_mg_checked.trans (by decide +kernel)
  upper_error := v1398_upper_checked
  lower_error := reuse_lower_error 15 64 Primitive.Addresses.material1398

def v1399_pa : Scalar.QComplex := ((999999630962616407033293342045 : Int)/10^30,(-859112699823104072458808459 : Int)/10^30)
theorem v1399_pa_checked : Scalar.distance (sourceCoefficient 15 65 1 0) v1399_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1399_pb : Scalar.QComplex := ((-370687783260369959065967 : Int)/10^30,(-431477321356146726449975653 : Int)/10^30)
theorem v1399_pb_checked : Scalar.distance (sourceCoefficient 15 65 1 1) v1399_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1399_pg : Scalar.QComplex := ((-93086391185259652200588 : Int)/10^30,(79971730360516150140 : Int)/10^30)
theorem v1399_pg_checked : Scalar.distance (sourceCoefficient 15 65 1 2) v1399_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1399_mb : Scalar.QComplex := ((-743033140549555233028588 : Int)/10^30,(-431476840810558702113489438 : Int)/10^30)
theorem v1399_mb_checked : Scalar.distance (sourceCoefficient 15 65 3 1) v1399_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1399_mg : Scalar.QComplex := ((-93086287512940447591789 : Int)/10^30,(160301063720837405030 : Int)/10^30)
theorem v1399_mg_checked : Scalar.distance (sourceCoefficient 15 65 3 2) v1399_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1399_upper : Scalar.QComplex := ((999996658830052497191934060611 : Int)/10^30,(-2585020064059271095073027968 : Int)/10^30)
theorem v1399_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 65 5) 1) 14) v1399_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1399 : Material (15 : Basis) (65 : Basis) where
  plus := ![v1399_pa,v1399_pb,v1399_pg]
  minus := ![(Primitive.Addresses.material1399 1).one,v1399_mb,v1399_mg]
  upper := v1399_upper
  lower := (Primitive.Addresses.material1399 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1399_pa_checked.trans (by decide +kernel)
    · exact v1399_pb_checked.trans (by decide +kernel)
    · exact v1399_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 65 Primitive.Addresses.material1399
    · exact v1399_mb_checked.trans (by decide +kernel)
    · exact v1399_mg_checked.trans (by decide +kernel)
  upper_error := v1399_upper_checked
  lower_error := reuse_lower_error 15 65 Primitive.Addresses.material1399

def v1400_pa : Scalar.QComplex := ((999999615698253460608771168636 : Int)/10^30,(-876700259718765033990714745 : Int)/10^30)
theorem v1400_pa_checked : Scalar.distance (sourceCoefficient 15 66 1 0) v1400_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1400_pb : Scalar.QComplex := ((-378276417611866806655843 : Int)/10^30,(-431477312851401859017172458 : Int)/10^30)
theorem v1400_pb_checked : Scalar.distance (sourceCoefficient 15 66 1 1) v1400_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1400_pg : Scalar.QComplex := ((-93086389557405523756593 : Int)/10^30,(81608893263699774386 : Int)/10^30)
theorem v1400_pg_checked : Scalar.distance (sourceCoefficient 15 66 1 2) v1400_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1400_mb : Scalar.QComplex := ((-750621764736244912728406 : Int)/10^30,(-431476825757167335447850532 : Int)/10^30)
theorem v1400_mb_checked : Scalar.distance (sourceCoefficient 15 66 3 1) v1400_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1400_mg : Scalar.QComplex := ((-93086284472289074904800 : Int)/10^30,(161938224609665661361 : Int)/10^30)
theorem v1400_mg_checked : Scalar.distance (sourceCoefficient 15 66 3 2) v1400_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1400_upper : Scalar.QComplex := ((999996613211179436302253360214 : Int)/10^30,(-2602607571415421898590977443 : Int)/10^30)
theorem v1400_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 66 5) 1) 14) v1400_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1400 : Material (15 : Basis) (66 : Basis) where
  plus := ![v1400_pa,v1400_pb,v1400_pg]
  minus := ![(Primitive.Addresses.material1400 1).one,v1400_mb,v1400_mg]
  upper := v1400_upper
  lower := (Primitive.Addresses.material1400 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1400_pa_checked.trans (by decide +kernel)
    · exact v1400_pb_checked.trans (by decide +kernel)
    · exact v1400_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 66 Primitive.Addresses.material1400
    · exact v1400_mb_checked.trans (by decide +kernel)
    · exact v1400_mg_checked.trans (by decide +kernel)
  upper_error := v1400_upper_checked
  lower_error := reuse_lower_error 15 66 Primitive.Addresses.material1400

def v1401_pa : Scalar.QComplex := ((999999589384924959619755133934 : Int)/10^30,(-906217402986733994731536296 : Int)/10^30)
theorem v1401_pa_checked : Scalar.distance (sourceCoefficient 15 67 1 0) v1401_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1401_pb : Scalar.QComplex := ((-391012397158154472607092 : Int)/10^30,(-431477298177966741059574551 : Int)/10^30)
theorem v1401_pb_checked : Scalar.distance (sourceCoefficient 15 67 1 1) v1401_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1401_pg : Scalar.QComplex := ((-93086386749884189371816 : Int)/10^30,(84356538291965077048 : Int)/10^30)
theorem v1401_pg_checked : Scalar.distance (sourceCoefficient 15 67 1 2) v1401_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1401_mb : Scalar.QComplex := ((-763357726877831690764765 : Int)/10^30,(-431476800093160939859964126 : Int)/10^30)
theorem v1401_mb_checked : Scalar.distance (sourceCoefficient 15 67 3 1) v1401_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1401_mg : Scalar.QComplex := ((-93086279293674875833852 : Int)/10^30,(164685866192092680912 : Int)/10^30)
theorem v1401_mg_checked : Scalar.distance (sourceCoefficient 15 67 3 2) v1401_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1401_upper : Scalar.QComplex := ((999996535953978619730277699378 : Int)/10^30,(-2632124625306655422714099008 : Int)/10^30)
theorem v1401_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 67 5) 1) 14) v1401_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1401 : Material (15 : Basis) (67 : Basis) where
  plus := ![v1401_pa,v1401_pb,v1401_pg]
  minus := ![(Primitive.Addresses.material1401 1).one,v1401_mb,v1401_mg]
  upper := v1401_upper
  lower := (Primitive.Addresses.material1401 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1401_pa_checked.trans (by decide +kernel)
    · exact v1401_pb_checked.trans (by decide +kernel)
    · exact v1401_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 67 Primitive.Addresses.material1401
    · exact v1401_mb_checked.trans (by decide +kernel)
    · exact v1401_mg_checked.trans (by decide +kernel)
  upper_error := v1401_upper_checked
  lower_error := reuse_lower_error 15 67 Primitive.Addresses.material1401

def v1402_pa : Scalar.QComplex := ((999999543628852074073529151843 : Int)/10^30,(-955375364753157261600272682 : Int)/10^30)
theorem v1402_pa_checked : Scalar.distance (sourceCoefficient 15 68 1 0) v1402_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1402_pb : Scalar.QComplex := ((-412222944846595773576253 : Int)/10^30,(-431477272628276597923658972 : Int)/10^30)
theorem v1402_pb_checked : Scalar.distance (sourceCoefficient 15 68 1 1) v1402_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1402_pg : Scalar.QComplex := ((-93086381864220075995907 : Int)/10^30,(88932476613297378044 : Int)/10^30)
theorem v1402_pg_checked : Scalar.distance (sourceCoefficient 15 68 1 2) v1402_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1402_mb : Scalar.QComplex := ((-784568244620384839211214 : Int)/10^30,(-431476756239732942522469184 : Int)/10^30)
theorem v1402_mb_checked : Scalar.distance (sourceCoefficient 15 68 3 1) v1402_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1402_mg : Scalar.QComplex := ((-93086270459183902915678 : Int)/10^30,(169261798593485926463 : Int)/10^30)
theorem v1402_mg_checked : Scalar.distance (sourceCoefficient 15 68 3 2) v1402_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1402_upper : Scalar.QComplex := ((999996405355791449088328459393 : Int)/10^30,(-2681282434887238296374834514 : Int)/10^30)
theorem v1402_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 68 5) 1) 14) v1402_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1402 : Material (15 : Basis) (68 : Basis) where
  plus := ![v1402_pa,v1402_pb,v1402_pg]
  minus := ![(Primitive.Addresses.material1402 1).one,v1402_mb,v1402_mg]
  upper := v1402_upper
  lower := (Primitive.Addresses.material1402 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1402_pa_checked.trans (by decide +kernel)
    · exact v1402_pb_checked.trans (by decide +kernel)
    · exact v1402_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 68 Primitive.Addresses.material1402
    · exact v1402_mb_checked.trans (by decide +kernel)
    · exact v1402_mg_checked.trans (by decide +kernel)
  upper_error := v1402_upper_checked
  lower_error := reuse_lower_error 15 68 Primitive.Addresses.material1402

def v1403_pa : Scalar.QComplex := ((999999522724890699804258308385 : Int)/10^30,(-977010742422447229188692285 : Int)/10^30)
theorem v1403_pa_checked : Scalar.distance (sourceCoefficient 15 69 1 0) v1403_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1403_pb : Scalar.QComplex := ((-421558120251307730615178 : Int)/10^30,(-431477260942780338380370246 : Int)/10^30)
theorem v1403_pb_checked : Scalar.distance (sourceCoefficient 15 69 1 1) v1403_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1403_pg : Scalar.QComplex := ((-93086379630775206017831 : Int)/10^30,(90946436278951768717 : Int)/10^30)
theorem v1403_pg_checked : Scalar.distance (sourceCoefficient 15 69 1 2) v1403_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1403_mb : Scalar.QComplex := ((-793903406465127377712182 : Int)/10^30,(-431476736498405100449808599 : Int)/10^30)
theorem v1403_mb_checked : Scalar.distance (sourceCoefficient 15 69 3 1) v1403_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1403_mg : Scalar.QComplex := ((-93086266487783378467660 : Int)/10^30,(171275755581888758940 : Int)/10^30)
theorem v1403_mg_checked : Scalar.distance (sourceCoefficient 15 69 3 2) v1403_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1403_upper : Scalar.QComplex := ((999996347111162097749515357069 : Int)/10^30,(-2702917744254833756118718244 : Int)/10^30)
theorem v1403_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 69 5) 1) 14) v1403_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1403 : Material (15 : Basis) (69 : Basis) where
  plus := ![v1403_pa,v1403_pb,v1403_pg]
  minus := ![(Primitive.Addresses.material1403 1).one,v1403_mb,v1403_mg]
  upper := v1403_upper
  lower := (Primitive.Addresses.material1403 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1403_pa_checked.trans (by decide +kernel)
    · exact v1403_pb_checked.trans (by decide +kernel)
    · exact v1403_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 69 Primitive.Addresses.material1403
    · exact v1403_mb_checked.trans (by decide +kernel)
    · exact v1403_mg_checked.trans (by decide +kernel)
  upper_error := v1403_upper_checked
  lower_error := reuse_lower_error 15 69 Primitive.Addresses.material1403

def v1404_pa : Scalar.QComplex := ((999999508718832489649391809170 : Int)/10^30,(-991242701694956070382969555 : Int)/10^30)
theorem v1404_pa_checked : Scalar.distance (sourceCoefficient 15 70 1 0) v1404_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1404_pb : Scalar.QComplex := ((-427698888212204826396676 : Int)/10^30,(-431477253109113129646550747 : Int)/10^30)
theorem v1404_pb_checked : Scalar.distance (sourceCoefficient 15 70 1 1) v1404_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1404_pg : Scalar.QComplex := ((-93086378133875358812271 : Int)/10^30,(92271238283542565385 : Int)/10^30)
theorem v1404_pg_checked : Scalar.distance (sourceCoefficient 15 70 1 2) v1404_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1404_mb : Scalar.QComplex := ((-800044165379433928828314 : Int)/10^30,(-431476723365534628216314230 : Int)/10^30)
theorem v1404_mb_checked : Scalar.distance (sourceCoefficient 15 70 3 1) v1404_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1404_mg : Scalar.QComplex := ((-93086263847639625531816 : Int)/10^30,(172600555801438072585 : Int)/10^30)
theorem v1404_mg_checked : Scalar.distance (sourceCoefficient 15 70 3 2) v1404_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1404_upper : Scalar.QComplex := ((999996308542054156882404512151 : Int)/10^30,(-2717149658157325213232996697 : Int)/10^30)
theorem v1404_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 70 5) 1) 14) v1404_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1404 : Material (15 : Basis) (70 : Basis) where
  plus := ![v1404_pa,v1404_pb,v1404_pg]
  minus := ![(Primitive.Addresses.material1404 1).one,v1404_mb,v1404_mg]
  upper := v1404_upper
  lower := (Primitive.Addresses.material1404 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1404_pa_checked.trans (by decide +kernel)
    · exact v1404_pb_checked.trans (by decide +kernel)
    · exact v1404_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 70 Primitive.Addresses.material1404
    · exact v1404_mb_checked.trans (by decide +kernel)
    · exact v1404_mg_checked.trans (by decide +kernel)
  upper_error := v1404_upper_checked
  lower_error := reuse_lower_error 15 70 Primitive.Addresses.material1404

def v1405_pa : Scalar.QComplex := ((999999484343685103506772158039 : Int)/10^30,(-1015535505972859307910698575 : Int)/10^30)
theorem v1405_pa_checked : Scalar.distance (sourceCoefficient 15 71 1 0) v1405_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1405_pb : Scalar.QComplex := ((-438180682650021528472960 : Int)/10^30,(-431477239468470189788763153 : Int)/10^30)
theorem v1405_pb_checked : Scalar.distance (sourceCoefficient 15 71 1 1) v1405_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1405_pg : Scalar.QComplex := ((-93086375527969860158009 : Int)/10^30,(94532568217292225063 : Int)/10^30)
theorem v1405_pg_checked : Scalar.distance (sourceCoefficient 15 71 1 2) v1405_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1405_mb : Scalar.QComplex := ((-810525944143139014689425 : Int)/10^30,(-431476700679580250054440663 : Int)/10^30)
theorem v1405_mb_checked : Scalar.distance (sourceCoefficient 15 71 3 1) v1405_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1405_mg : Scalar.QComplex := ((-93086259290309210868806 : Int)/10^30,(174861882644412170332 : Int)/10^30)
theorem v1405_mg_checked : Scalar.distance (sourceCoefficient 15 71 3 2) v1405_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1405_upper : Scalar.QComplex := ((999996242239766716986270107331 : Int)/10^30,(-2741442384184657019686150526 : Int)/10^30)
theorem v1405_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 71 5) 1) 14) v1405_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1405 : Material (15 : Basis) (71 : Basis) where
  plus := ![v1405_pa,v1405_pb,v1405_pg]
  minus := ![(Primitive.Addresses.material1405 1).one,v1405_mb,v1405_mg]
  upper := v1405_upper
  lower := (Primitive.Addresses.material1405 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1405_pa_checked.trans (by decide +kernel)
    · exact v1405_pb_checked.trans (by decide +kernel)
    · exact v1405_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 71 Primitive.Addresses.material1405
    · exact v1405_mb_checked.trans (by decide +kernel)
    · exact v1405_mg_checked.trans (by decide +kernel)
  upper_error := v1405_upper_checked
  lower_error := reuse_lower_error 15 71 Primitive.Addresses.material1405

def v1406_pa : Scalar.QComplex := ((999999457224008347747155322355 : Int)/10^30,(-1041898118195214217303505712 : Int)/10^30)
theorem v1406_pa_checked : Scalar.distance (sourceCoefficient 15 72 1 0) v1406_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1406_pb : Scalar.QComplex := ((-449555552030926031609744 : Int)/10^30,(-431477224281477190100385164 : Int)/10^30)
theorem v1406_pb_checked : Scalar.distance (sourceCoefficient 15 72 1 1) v1406_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1406_pg : Scalar.QComplex := ((-93086372627521309500933 : Int)/10^30,(96986569112214177580 : Int)/10^30)
theorem v1406_pg_checked : Scalar.distance (sourceCoefficient 15 72 1 2) v1406_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1406_mb : Scalar.QComplex := ((-821900796182968828145770 : Int)/10^30,(-431476675676592934556306841 : Int)/10^30)
theorem v1406_mb_checked : Scalar.distance (sourceCoefficient 15 72 3 1) v1406_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1406_mg : Scalar.QComplex := ((-93086254272169491961098 : Int)/10^30,(177315880122640968425 : Int)/10^30)
theorem v1406_mg_checked : Scalar.distance (sourceCoefficient 15 72 3 2) v1406_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1406_upper : Scalar.QComplex := ((999996169620653254513583971781 : Int)/10^30,(-2767804910336895991264731350 : Int)/10^30)
theorem v1406_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 72 5) 1) 14) v1406_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1406 : Material (15 : Basis) (72 : Basis) where
  plus := ![v1406_pa,v1406_pb,v1406_pg]
  minus := ![(Primitive.Addresses.material1406 1).one,v1406_mb,v1406_mg]
  upper := v1406_upper
  lower := (Primitive.Addresses.material1406 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1406_pa_checked.trans (by decide +kernel)
    · exact v1406_pb_checked.trans (by decide +kernel)
    · exact v1406_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 72 Primitive.Addresses.material1406
    · exact v1406_mb_checked.trans (by decide +kernel)
    · exact v1406_mg_checked.trans (by decide +kernel)
  upper_error := v1406_upper_checked
  lower_error := reuse_lower_error 15 72 Primitive.Addresses.material1406

def v1407_pa : Scalar.QComplex := ((999999447333795625156669879776 : Int)/10^30,(-1051347755649743707647991480 : Int)/10^30)
theorem v1407_pa_checked : Scalar.distance (sourceCoefficient 15 73 1 0) v1407_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1407_pb : Scalar.QComplex := ((-453632856244238801460023 : Int)/10^30,(-431477218740378014473051781 : Int)/10^30)
theorem v1407_pb_checked : Scalar.distance (sourceCoefficient 15 73 1 1) v1407_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1407_pg : Scalar.QComplex := ((-93086371569484048324530 : Int)/10^30,(97866201918497515787 : Int)/10^30)
theorem v1407_pg_checked : Scalar.distance (sourceCoefficient 15 73 1 2) v1407_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1407_mb : Scalar.QComplex := ((-825978094096395870647984 : Int)/10^30,(-431476666616965921009434185 : Int)/10^30)
theorem v1407_mb_checked : Scalar.distance (sourceCoefficient 15 73 3 1) v1407_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1407_mg : Scalar.QComplex := ((-93086252455049130108736 : Int)/10^30,(178195511688358307482 : Int)/10^30)
theorem v1407_mg_checked : Scalar.distance (sourceCoefficient 15 73 3 2) v1407_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1407_upper : Scalar.QComplex := ((999996143421238280128555312110 : Int)/10^30,(-2777254516647690599376688118 : Int)/10^30)
theorem v1407_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 73 5) 1) 14) v1407_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1407 : Material (15 : Basis) (73 : Basis) where
  plus := ![v1407_pa,v1407_pb,v1407_pg]
  minus := ![(Primitive.Addresses.material1407 1).one,v1407_mb,v1407_mg]
  upper := v1407_upper
  lower := (Primitive.Addresses.material1407 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1407_pa_checked.trans (by decide +kernel)
    · exact v1407_pb_checked.trans (by decide +kernel)
    · exact v1407_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 73 Primitive.Addresses.material1407
    · exact v1407_mb_checked.trans (by decide +kernel)
    · exact v1407_mg_checked.trans (by decide +kernel)
  upper_error := v1407_upper_checked
  lower_error := reuse_lower_error 15 73 Primitive.Addresses.material1407

def v1408_pa : Scalar.QComplex := ((999999436098103303815498114083 : Int)/10^30,(-1061980920453385502449487239 : Int)/10^30)
theorem v1408_pa_checked : Scalar.distance (sourceCoefficient 15 74 1 0) v1408_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1408_pb : Scalar.QComplex := ((-458220825617376848110510 : Int)/10^30,(-431477212443853194670142649 : Int)/10^30)
theorem v1408_pb_checked : Scalar.distance (sourceCoefficient 15 74 1 1) v1408_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1408_pg : Scalar.QComplex := ((-93086370367336540644424 : Int)/10^30,(98856005029457544102 : Int)/10^30)
theorem v1408_pg_checked : Scalar.distance (sourceCoefficient 15 74 1 2) v1408_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1408_mb : Scalar.QComplex := ((-830566056327605904581200 : Int)/10^30,(-431476656361232511142280660 : Int)/10^30)
theorem v1408_mb_checked : Scalar.distance (sourceCoefficient 15 74 3 1) v1408_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1408_mg : Scalar.QComplex := ((-93086250398746564361849 : Int)/10^30,(179185313393370244935 : Int)/10^30)
theorem v1408_mg_checked : Scalar.distance (sourceCoefficient 15 74 3 2) v1408_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1408_upper : Scalar.QComplex := ((999996113833684875121206763500 : Int)/10^30,(-2787887646222696825843436589 : Int)/10^30)
theorem v1408_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 74 5) 1) 14) v1408_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1408 : Material (15 : Basis) (74 : Basis) where
  plus := ![v1408_pa,v1408_pb,v1408_pg]
  minus := ![(Primitive.Addresses.material1408 1).one,v1408_mb,v1408_mg]
  upper := v1408_upper
  lower := (Primitive.Addresses.material1408 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1408_pa_checked.trans (by decide +kernel)
    · exact v1408_pb_checked.trans (by decide +kernel)
    · exact v1408_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 74 Primitive.Addresses.material1408
    · exact v1408_mb_checked.trans (by decide +kernel)
    · exact v1408_mg_checked.trans (by decide +kernel)
  upper_error := v1408_upper_checked
  lower_error := reuse_lower_error 15 74 Primitive.Addresses.material1408

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
