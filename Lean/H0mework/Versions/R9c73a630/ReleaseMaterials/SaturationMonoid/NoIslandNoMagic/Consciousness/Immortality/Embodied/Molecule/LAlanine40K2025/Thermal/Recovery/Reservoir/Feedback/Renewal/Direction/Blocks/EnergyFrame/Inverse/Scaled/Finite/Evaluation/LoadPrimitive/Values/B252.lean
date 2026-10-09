import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B168

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4033_pa : Scalar.QComplex := ((999998435782647989108773955500 : Int)/10^30,(-1768737475502189420414810677 : Int)/10^30)
theorem v4033_pa_checked : Scalar.distance (sourceCoefficient 59 81 1 0) v4033_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4033_pb : Scalar.QComplex := ((-763170438617025501217723 : Int)/10^30,(-431476833290875896588851846 : Int)/10^30)
theorem v4033_pb_checked : Scalar.distance (sourceCoefficient 59 81 1 1) v4033_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4033_pg : Scalar.QComplex := ((-93086282910440752580540 : Int)/10^30,(164645454580172558347 : Int)/10^30)
theorem v4033_pg_checked : Scalar.distance (sourceCoefficient 59 81 1 2) v4033_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4033_mb : Scalar.QComplex := ((-1135515228588633760055993 : Int)/10^30,(-431476014050614791069638793 : Int)/10^30)
theorem v4033_mb_checked : Scalar.distance (sourceCoefficient 59 81 3 1) v4033_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4033_mg : Scalar.QComplex := ((-93086106168551425044483 : Int)/10^30,(244974662976304312337 : Int)/10^30)
theorem v4033_mg_checked : Scalar.distance (sourceCoefficient 59 81 3 2) v4033_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4033_upper : Scalar.QComplex := ((999993893722021852368079849640 : Int)/10^30,(-3494641422186905491549200842 : Int)/10^30)
theorem v4033_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 81 5) 1) 14) v4033_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4033 : Material (59 : Basis) (81 : Basis) where
  plus := ![v4033_pa,v4033_pb,v4033_pg]
  minus := ![(Primitive.Addresses.material4033 1).one,v4033_mb,v4033_mg]
  upper := v4033_upper
  lower := (Primitive.Addresses.material4033 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4033_pa_checked.trans (by decide +kernel)
    · exact v4033_pb_checked.trans (by decide +kernel)
    · exact v4033_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 81 Primitive.Addresses.material4033
    · exact v4033_mb_checked.trans (by decide +kernel)
    · exact v4033_mg_checked.trans (by decide +kernel)
  upper_error := v4033_upper_checked
  lower_error := reuse_lower_error 59 81 Primitive.Addresses.material4033

def v4034_pa : Scalar.QComplex := ((999998418151535253192745697083 : Int)/10^30,(-1778677718770055624596781197 : Int)/10^30)
theorem v4034_pa_checked : Scalar.distance (sourceCoefficient 59 82 1 0) v4034_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4034_pb : Scalar.QComplex := ((-767459428928446963211958 : Int)/10^30,(-431476825073527120698806158 : Int)/10^30)
theorem v4034_pb_checked : Scalar.distance (sourceCoefficient 59 82 1 1) v4034_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4034_pg : Scalar.QComplex := ((-93086281203431721934391 : Int)/10^30,(165570756207554357240 : Int)/10^30)
theorem v4034_pg_checked : Scalar.distance (sourceCoefficient 59 82 1 2) v4034_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4034_mb : Scalar.QComplex := ((-1139804210211866214624532 : Int)/10^30,(-431476002132063605070229887 : Int)/10^30)
theorem v4034_mb_checked : Scalar.distance (sourceCoefficient 59 82 3 1) v4034_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4034_mg : Scalar.QComplex := ((-93086103663049399603603 : Int)/10^30,(245899962786082114368 : Int)/10^30)
theorem v4034_mg_checked : Scalar.distance (sourceCoefficient 59 82 3 2) v4034_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4034_upper : Scalar.QComplex := ((999993858934977267411313234022 : Int)/10^30,(-3504581620220245911104425118 : Int)/10^30)
theorem v4034_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 82 5) 1) 14) v4034_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4034 : Material (59 : Basis) (82 : Basis) where
  plus := ![v4034_pa,v4034_pb,v4034_pg]
  minus := ![(Primitive.Addresses.material4034 1).one,v4034_mb,v4034_mg]
  upper := v4034_upper
  lower := (Primitive.Addresses.material4034 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4034_pa_checked.trans (by decide +kernel)
    · exact v4034_pb_checked.trans (by decide +kernel)
    · exact v4034_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 82 Primitive.Addresses.material4034
    · exact v4034_mb_checked.trans (by decide +kernel)
    · exact v4034_mg_checked.trans (by decide +kernel)
  upper_error := v4034_upper_checked
  lower_error := reuse_lower_error 59 82 Primitive.Addresses.material4034

def v4035_pa : Scalar.QComplex := ((999998393925278139344064585763 : Int)/10^30,(-1792246317961150023978913714 : Int)/10^30)
theorem v4035_pa_checked : Scalar.distance (sourceCoefficient 59 83 1 0) v4035_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4035_pb : Scalar.QComplex := ((-773313972755867441060594 : Int)/10^30,(-431476813764951810653046321 : Int)/10^30)
theorem v4035_pb_checked : Scalar.distance (sourceCoefficient 59 83 1 1) v4035_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4035_pg : Scalar.QComplex := ((-93086278856014762972312 : Int)/10^30,(166833808479959862795 : Int)/10^30)
theorem v4035_pg_checked : Scalar.distance (sourceCoefficient 59 83 1 2) v4035_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4035_mb : Scalar.QComplex := ((-1145658742100581286409241 : Int)/10^30,(-431475985771284861525780442 : Int)/10^30)
theorem v4035_mb_checked : Scalar.distance (sourceCoefficient 59 83 3 1) v4035_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4035_mg : Scalar.QComplex := ((-93086100225676089368839 : Int)/10^30,(247163012562480422716 : Int)/10^30)
theorem v4035_mg_checked : Scalar.distance (sourceCoefficient 59 83 3 2) v4035_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4035_upper : Scalar.QComplex := ((999993811290584965600943478478 : Int)/10^30,(-3518150157390183705350732882 : Int)/10^30)
theorem v4035_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 83 5) 1) 14) v4035_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4035 : Material (59 : Basis) (83 : Basis) where
  plus := ![v4035_pa,v4035_pb,v4035_pg]
  minus := ![(Primitive.Addresses.material4035 1).one,v4035_mb,v4035_mg]
  upper := v4035_upper
  lower := (Primitive.Addresses.material4035 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4035_pa_checked.trans (by decide +kernel)
    · exact v4035_pb_checked.trans (by decide +kernel)
    · exact v4035_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 83 Primitive.Addresses.material4035
    · exact v4035_mb_checked.trans (by decide +kernel)
    · exact v4035_mg_checked.trans (by decide +kernel)
  upper_error := v4035_upper_checked
  lower_error := reuse_lower_error 59 83 Primitive.Addresses.material4035

def v4036_pa : Scalar.QComplex := ((999998330330056614823231514379 : Int)/10^30,(-1827385317597970002118135376 : Int)/10^30)
theorem v4036_pa_checked : Scalar.distance (sourceCoefficient 59 84 1 0) v4036_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4036_pb : Scalar.QComplex := ((-788475656435378486970516 : Int)/10^30,(-431476783986474196064535069 : Int)/10^30)
theorem v4036_pb_checked : Scalar.distance (sourceCoefficient 59 84 1 1) v4036_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4036_pg : Scalar.QComplex := ((-93086272683902623820516 : Int)/10^30,(170104771991309655980 : Int)/10^30)
theorem v4036_pg_checked : Scalar.distance (sourceCoefficient 59 84 1 2) v4036_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4036_mb : Scalar.QComplex := ((-1160820394437219566717147 : Int)/10^30,(-431475942908968176291482247 : Int)/10^30)
theorem v4036_mb_checked : Scalar.distance (sourceCoefficient 59 84 3 1) v4036_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4036_mg : Scalar.QComplex := ((-93086091230872056809423 : Int)/10^30,(250433969529646215732 : Int)/10^30)
theorem v4036_mg_checked : Scalar.distance (sourceCoefficient 59 84 3 2) v4036_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4036_upper : Scalar.QComplex := ((999993687048732570686310736540 : Int)/10^30,(-3553288994932008403406575668 : Int)/10^30)
theorem v4036_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 84 5) 1) 14) v4036_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4036 : Material (59 : Basis) (84 : Basis) where
  plus := ![v4036_pa,v4036_pb,v4036_pg]
  minus := ![(Primitive.Addresses.material4036 1).one,v4036_mb,v4036_mg]
  upper := v4036_upper
  lower := (Primitive.Addresses.material4036 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4036_pa_checked.trans (by decide +kernel)
    · exact v4036_pb_checked.trans (by decide +kernel)
    · exact v4036_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 84 Primitive.Addresses.material4036
    · exact v4036_mb_checked.trans (by decide +kernel)
    · exact v4036_mg_checked.trans (by decide +kernel)
  upper_error := v4036_upper_checked
  lower_error := reuse_lower_error 59 84 Primitive.Addresses.material4036

def v4037_pa : Scalar.QComplex := ((999998182737804335984233679283 : Int)/10^30,(-1906441997251986615771770754 : Int)/10^30)
theorem v4037_pa_checked : Scalar.distance (sourceCoefficient 59 85 1 0) v4037_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4037_pb : Scalar.QComplex := ((-822586824011307930782812 : Int)/10^30,(-431476714393133276459072907 : Int)/10^30)
theorem v4037_pb_checked : Scalar.distance (sourceCoefficient 59 85 1 1) v4037_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4037_pg : Scalar.QComplex := ((-93086258307493797498348 : Int)/10^30,(177463874702843400107 : Int)/10^30)
theorem v4037_pg_checked : Scalar.distance (sourceCoefficient 59 85 1 2) v4037_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4037_mb : Scalar.QComplex := ((-1194931489256083518740940 : Int)/10^30,(-431475843879251861397420760 : Int)/10^30)
theorem v4037_mb_checked : Scalar.distance (sourceCoefficient 59 85 3 1) v4037_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4037_mg : Scalar.QComplex := ((-93086070503894385110108 : Int)/10^30,(257793057094856365047 : Int)/10^30)
theorem v4037_mg_checked : Scalar.distance (sourceCoefficient 59 85 3 2) v4037_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4037_upper : Scalar.QComplex := ((999993403012042996290892107243 : Int)/10^30,(-3632345302109549353604073076 : Int)/10^30)
theorem v4037_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 85 5) 1) 14) v4037_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4037 : Material (59 : Basis) (85 : Basis) where
  plus := ![v4037_pa,v4037_pb,v4037_pg]
  minus := ![(Primitive.Addresses.material4037 1).one,v4037_mb,v4037_mg]
  upper := v4037_upper
  lower := (Primitive.Addresses.material4037 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4037_pa_checked.trans (by decide +kernel)
    · exact v4037_pb_checked.trans (by decide +kernel)
    · exact v4037_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 85 Primitive.Addresses.material4037
    · exact v4037_mb_checked.trans (by decide +kernel)
    · exact v4037_mg_checked.trans (by decide +kernel)
  upper_error := v4037_upper_checked
  lower_error := reuse_lower_error 59 85 Primitive.Addresses.material4037

def v4038_pa : Scalar.QComplex := ((999998154826670580116939877859 : Int)/10^30,(-1921026614645187709349383968 : Int)/10^30)
theorem v4038_pa_checked : Scalar.distance (sourceCoefficient 59 86 1 0) v4038_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4038_pb : Scalar.QComplex := ((-828879755957344621207228 : Int)/10^30,(-431476701161487483792607985 : Int)/10^30)
theorem v4038_pb_checked : Scalar.distance (sourceCoefficient 59 86 1 1) v4038_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4038_pg : Scalar.QComplex := ((-93086255581130401688774 : Int)/10^30,(178821504385686265068 : Int)/10^30)
theorem v4038_pg_checked : Scalar.distance (sourceCoefficient 59 86 1 2) v4038_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4038_mb : Scalar.QComplex := ((-1201224407440659656591511 : Int)/10^30,(-431475825217094149181424916 : Int)/10^30)
theorem v4038_mb_checked : Scalar.distance (sourceCoefficient 59 86 3 1) v4038_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4038_mg : Scalar.QComplex := ((-93086066605958733527927 : Int)/10^30,(259150683919462832610 : Int)/10^30)
theorem v4038_mg_checked : Scalar.distance (sourceCoefficient 59 86 3 2) v4038_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4038_upper : Scalar.QComplex := ((999993349929224296267941193025 : Int)/10^30,(-3646929849608591285163344877 : Int)/10^30)
theorem v4038_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 86 5) 1) 14) v4038_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4038 : Material (59 : Basis) (86 : Basis) where
  plus := ![v4038_pa,v4038_pb,v4038_pg]
  minus := ![(Primitive.Addresses.material4038 1).one,v4038_mb,v4038_mg]
  upper := v4038_upper
  lower := (Primitive.Addresses.material4038 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4038_pa_checked.trans (by decide +kernel)
    · exact v4038_pb_checked.trans (by decide +kernel)
    · exact v4038_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 86 Primitive.Addresses.material4038
    · exact v4038_mb_checked.trans (by decide +kernel)
    · exact v4038_mg_checked.trans (by decide +kernel)
  upper_error := v4038_upper_checked
  lower_error := reuse_lower_error 59 86 Primitive.Addresses.material4038

def v4039_pa : Scalar.QComplex := ((999998152970960412923017026107 : Int)/10^30,(-1921992369302719393080002892 : Int)/10^30)
theorem v4039_pa_checked : Scalar.distance (sourceCoefficient 59 87 1 0) v4039_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4039_pb : Scalar.QComplex := ((-829296457206643343879861 : Int)/10^30,(-431476700281003088462674261 : Int)/10^30)
theorem v4039_pb_checked : Scalar.distance (sourceCoefficient 59 87 1 1) v4039_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4039_pg : Scalar.QComplex := ((-93086255399782374015698 : Int)/10^30,(178911403019902672885 : Int)/10^30)
theorem v4039_pg_checked : Scalar.distance (sourceCoefficient 59 87 1 2) v4039_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4039_mb : Scalar.QComplex := ((-1201641107774983082337685 : Int)/10^30,(-431475823977015671078859075 : Int)/10^30)
theorem v4039_mb_checked : Scalar.distance (sourceCoefficient 59 87 3 1) v4039_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4039_mg : Scalar.QComplex := ((-93086066347032300934433 : Int)/10^30,(259240582363710690068 : Int)/10^30)
theorem v4039_mg_checked : Scalar.distance (sourceCoefficient 59 87 3 2) v4039_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4039_upper : Scalar.QComplex := ((999993346406711966614778600830 : Int)/10^30,(-3647895599624957452146296096 : Int)/10^30)
theorem v4039_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 87 5) 1) 14) v4039_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4039 : Material (59 : Basis) (87 : Basis) where
  plus := ![v4039_pa,v4039_pb,v4039_pg]
  minus := ![(Primitive.Addresses.material4039 1).one,v4039_mb,v4039_mg]
  upper := v4039_upper
  lower := (Primitive.Addresses.material4039 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4039_pa_checked.trans (by decide +kernel)
    · exact v4039_pb_checked.trans (by decide +kernel)
    · exact v4039_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 87 Primitive.Addresses.material4039
    · exact v4039_mb_checked.trans (by decide +kernel)
    · exact v4039_mg_checked.trans (by decide +kernel)
  upper_error := v4039_upper_checked
  lower_error := reuse_lower_error 59 87 Primitive.Addresses.material4039

def v4040_pa : Scalar.QComplex := ((999998130299967441198359928057 : Int)/10^30,(-1933751941004686239319449266 : Int)/10^30)
theorem v4040_pa_checked : Scalar.distance (sourceCoefficient 59 88 1 0) v4040_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4040_pb : Scalar.QComplex := ((-834370445873614624628563 : Int)/10^30,(-431476689516684397526672782 : Int)/10^30)
theorem v4040_pb_checked : Scalar.distance (sourceCoefficient 59 88 1 1) v4040_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4040_pg : Scalar.QComplex := ((-93086253183461034782182 : Int)/10^30,(180006059331706422841 : Int)/10^30)
theorem v4040_pg_checked : Scalar.distance (sourceCoefficient 59 88 1 2) v4040_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4040_mb : Scalar.QComplex := ((-1206715085263554266274357 : Int)/10^30,(-431475808834077292560796611 : Int)/10^30)
theorem v4040_mb_checked : Scalar.distance (sourceCoefficient 59 88 3 1) v4040_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4040_mg : Scalar.QComplex := ((-93086063186072691342132 : Int)/10^30,(260335236355338370524 : Int)/10^30)
theorem v4040_mg_checked : Scalar.distance (sourceCoefficient 59 88 3 2) v4040_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4040_upper : Scalar.QComplex := ((999993303439798823087516204417 : Int)/10^30,(-3659655114684346451854238573 : Int)/10^30)
theorem v4040_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 88 5) 1) 14) v4040_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4040 : Material (59 : Basis) (88 : Basis) where
  plus := ![v4040_pa,v4040_pb,v4040_pg]
  minus := ![(Primitive.Addresses.material4040 1).one,v4040_mb,v4040_mg]
  upper := v4040_upper
  lower := (Primitive.Addresses.material4040 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4040_pa_checked.trans (by decide +kernel)
    · exact v4040_pb_checked.trans (by decide +kernel)
    · exact v4040_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 88 Primitive.Addresses.material4040
    · exact v4040_mb_checked.trans (by decide +kernel)
    · exact v4040_mg_checked.trans (by decide +kernel)
  upper_error := v4040_upper_checked
  lower_error := reuse_lower_error 59 88 Primitive.Addresses.material4040

def v4041_pa : Scalar.QComplex := ((999998099057459993761832579443 : Int)/10^30,(-1949841395198577665449882717 : Int)/10^30)
theorem v4041_pa_checked : Scalar.distance (sourceCoefficient 59 89 1 0) v4041_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4041_pb : Scalar.QComplex := ((-841312680601850489605933 : Int)/10^30,(-431476674660045801375149462 : Int)/10^30)
theorem v4041_pb_checked : Scalar.distance (sourceCoefficient 59 89 1 1) v4041_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4041_pg : Scalar.QComplex := ((-93086250126757822201263 : Int)/10^30,(181503768849196626001 : Int)/10^30)
theorem v4041_pg_checked : Scalar.distance (sourceCoefficient 59 89 1 2) v4041_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4041_mb : Scalar.QComplex := ((-1213657304586268875813463 : Int)/10^30,(-431475787986608324392681375 : Int)/10^30)
theorem v4041_mb_checked : Scalar.distance (sourceCoefficient 59 89 3 1) v4041_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4041_mg : Scalar.QComplex := ((-93086058836914757650117 : Int)/10^30,(261832942677365667960 : Int)/10^30)
theorem v4041_mg_checked : Scalar.distance (sourceCoefficient 59 89 3 2) v4041_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4041_upper : Scalar.QComplex := ((999993244428399592921741363962 : Int)/10^30,(-3675744490993152300098133161 : Int)/10^30)
theorem v4041_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 89 5) 1) 14) v4041_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4041 : Material (59 : Basis) (89 : Basis) where
  plus := ![v4041_pa,v4041_pb,v4041_pg]
  minus := ![(Primitive.Addresses.material4041 1).one,v4041_mb,v4041_mg]
  upper := v4041_upper
  lower := (Primitive.Addresses.material4041 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4041_pa_checked.trans (by decide +kernel)
    · exact v4041_pb_checked.trans (by decide +kernel)
    · exact v4041_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 89 Primitive.Addresses.material4041
    · exact v4041_mb_checked.trans (by decide +kernel)
    · exact v4041_mg_checked.trans (by decide +kernel)
  upper_error := v4041_upper_checked
  lower_error := reuse_lower_error 59 89 Primitive.Addresses.material4041

def v4042_pa : Scalar.QComplex := ((999998047622583209317954919977 : Int)/10^30,(-1976044286397394104695063331 : Int)/10^30)
theorem v4042_pa_checked : Scalar.distance (sourceCoefficient 59 90 1 0) v4042_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4042_pb : Scalar.QComplex := ((-852618633868486088309308 : Int)/10^30,(-431476650146116164257094724 : Int)/10^30)
theorem v4042_pb_checked : Scalar.distance (sourceCoefficient 59 90 1 1) v4042_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4042_pg : Scalar.QComplex := ((-93086245088510774811427 : Int)/10^30,(183942901875306806135 : Int)/10^30)
theorem v4042_pg_checked : Scalar.distance (sourceCoefficient 59 90 1 2) v4042_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4042_mb : Scalar.QComplex := ((-1224963232488764155331350 : Int)/10^30,(-431475753716159347057141779 : Int)/10^30)
theorem v4042_mb_checked : Scalar.distance (sourceCoefficient 59 90 3 1) v4042_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4042_mg : Scalar.QComplex := ((-93086051693807639170337 : Int)/10^30,(264272070447494860914 : Int)/10^30)
theorem v4042_mg_checked : Scalar.distance (sourceCoefficient 59 90 3 2) v4042_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4042_upper : Scalar.QComplex := ((999993147769786313248305092344 : Int)/10^30,(-3701947254393909112146598010 : Int)/10^30)
theorem v4042_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 90 5) 1) 14) v4042_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4042 : Material (59 : Basis) (90 : Basis) where
  plus := ![v4042_pa,v4042_pb,v4042_pg]
  minus := ![(Primitive.Addresses.material4042 1).one,v4042_mb,v4042_mg]
  upper := v4042_upper
  lower := (Primitive.Addresses.material4042 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4042_pa_checked.trans (by decide +kernel)
    · exact v4042_pb_checked.trans (by decide +kernel)
    · exact v4042_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 90 Primitive.Addresses.material4042
    · exact v4042_mb_checked.trans (by decide +kernel)
    · exact v4042_mg_checked.trans (by decide +kernel)
  upper_error := v4042_upper_checked
  lower_error := reuse_lower_error 59 90 Primitive.Addresses.material4042

def v4043_pa : Scalar.QComplex := ((999998018345108828031774062659 : Int)/10^30,(-1990805328350270602140652541 : Int)/10^30)
theorem v4043_pa_checked : Scalar.distance (sourceCoefficient 59 91 1 0) v4043_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4043_pb : Scalar.QComplex := ((-858987688548294655251870 : Int)/10^30,(-431476636162592491244424508 : Int)/10^30)
theorem v4043_pb_checked : Scalar.distance (sourceCoefficient 59 91 1 1) v4043_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4043_pg : Scalar.QComplex := ((-93086242217448888396818 : Int)/10^30,(185316954236849936246 : Int)/10^30)
theorem v4043_pg_checked : Scalar.distance (sourceCoefficient 59 91 1 2) v4043_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4043_mb : Scalar.QComplex := ((-1231332272729931449519889 : Int)/10^30,(-431475734236433543648967961 : Int)/10^30)
theorem v4043_mb_checked : Scalar.distance (sourceCoefficient 59 91 3 1) v4043_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4043_mg : Scalar.QComplex := ((-93086047637001518792646 : Int)/10^30,(265646119819818399379 : Int)/10^30)
theorem v4043_mg_checked : Scalar.distance (sourceCoefficient 59 91 3 2) v4043_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4043_upper : Scalar.QComplex := ((999993093016136237921608649508 : Int)/10^30,(-3716708223831682824202180511 : Int)/10^30)
theorem v4043_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 91 5) 1) 14) v4043_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4043 : Material (59 : Basis) (91 : Basis) where
  plus := ![v4043_pa,v4043_pb,v4043_pg]
  minus := ![(Primitive.Addresses.material4043 1).one,v4043_mb,v4043_mg]
  upper := v4043_upper
  lower := (Primitive.Addresses.material4043 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4043_pa_checked.trans (by decide +kernel)
    · exact v4043_pb_checked.trans (by decide +kernel)
    · exact v4043_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 91 Primitive.Addresses.material4043
    · exact v4043_mb_checked.trans (by decide +kernel)
    · exact v4043_mg_checked.trans (by decide +kernel)
  upper_error := v4043_upper_checked
  lower_error := reuse_lower_error 59 91 Primitive.Addresses.material4043

def v4044_pa : Scalar.QComplex := ((999997954216130150640358924074 : Int)/10^30,(-2022761368641164539464126253 : Int)/10^30)
theorem v4044_pa_checked : Scalar.distance (sourceCoefficient 59 92 1 0) v4044_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4044_pb : Scalar.QComplex := ((-872775994508691187467772 : Int)/10^30,(-431476605460359044599134993 : Int)/10^30)
theorem v4044_pb_checked : Scalar.distance (sourceCoefficient 59 92 1 1) v4044_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4044_pg : Scalar.QComplex := ((-93086235920848999356440 : Int)/10^30,(188291627176884561404 : Int)/10^30)
theorem v4044_pg_checked : Scalar.distance (sourceCoefficient 59 92 1 2) v4044_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4044_mb : Scalar.QComplex := ((-1245120547061666828775846 : Int)/10^30,(-431475691635524487273913937 : Int)/10^30)
theorem v4044_mb_checked : Scalar.distance (sourceCoefficient 59 92 3 1) v4044_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4044_mg : Scalar.QComplex := ((-93086038773395201310153 : Int)/10^30,(268620786218564223782 : Int)/10^30)
theorem v4044_mg_checked : Scalar.distance (sourceCoefficient 59 92 3 2) v4044_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4044_upper : Scalar.QComplex := ((999992973734026560357094209727 : Int)/10^30,(-3748664105847009106745563465 : Int)/10^30)
theorem v4044_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 92 5) 1) 14) v4044_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4044 : Material (59 : Basis) (92 : Basis) where
  plus := ![v4044_pa,v4044_pb,v4044_pg]
  minus := ![(Primitive.Addresses.material4044 1).one,v4044_mb,v4044_mg]
  upper := v4044_upper
  lower := (Primitive.Addresses.material4044 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4044_pa_checked.trans (by decide +kernel)
    · exact v4044_pb_checked.trans (by decide +kernel)
    · exact v4044_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 92 Primitive.Addresses.material4044
    · exact v4044_mb_checked.trans (by decide +kernel)
    · exact v4044_mg_checked.trans (by decide +kernel)
  upper_error := v4044_upper_checked
  lower_error := reuse_lower_error 59 92 Primitive.Addresses.material4044

def v4045_pa : Scalar.QComplex := ((999997876782493400152339759177 : Int)/10^30,(-2060686901289741053515716202 : Int)/10^30)
theorem v4045_pa_checked : Scalar.distance (sourceCoefficient 59 93 1 0) v4045_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4045_pb : Scalar.QComplex := ((-889140000265440118617202 : Int)/10^30,(-431476568260482799752803598 : Int)/10^30)
theorem v4045_pb_checked : Scalar.distance (sourceCoefficient 59 93 1 1) v4045_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4045_pg : Scalar.QComplex := ((-93086228304110814381666 : Int)/10^30,(191821978636530693209 : Int)/10^30)
theorem v4045_pg_checked : Scalar.distance (sourceCoefficient 59 93 1 2) v4045_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4045_mb : Scalar.QComplex := ((-1261484514623530765608100 : Int)/10^30,(-431475640314262133027580273 : Int)/10^30)
theorem v4045_mb_checked : Scalar.distance (sourceCoefficient 59 93 3 1) v4045_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4045_mg : Scalar.QComplex := ((-93086028110125543847839 : Int)/10^30,(272151129790797153649 : Int)/10^30)
theorem v4045_mg_checked : Scalar.distance (sourceCoefficient 59 93 3 2) v4045_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4045_upper : Scalar.QComplex := ((999992830844476364177520497860 : Int)/10^30,(-3786589448366527480066796938 : Int)/10^30)
theorem v4045_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 93 5) 1) 14) v4045_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4045 : Material (59 : Basis) (93 : Basis) where
  plus := ![v4045_pa,v4045_pb,v4045_pg]
  minus := ![(Primitive.Addresses.material4045 1).one,v4045_mb,v4045_mg]
  upper := v4045_upper
  lower := (Primitive.Addresses.material4045 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4045_pa_checked.trans (by decide +kernel)
    · exact v4045_pb_checked.trans (by decide +kernel)
    · exact v4045_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 93 Primitive.Addresses.material4045
    · exact v4045_mb_checked.trans (by decide +kernel)
    · exact v4045_mg_checked.trans (by decide +kernel)
  upper_error := v4045_upper_checked
  lower_error := reuse_lower_error 59 93 Primitive.Addresses.material4045

def v4046_pa : Scalar.QComplex := ((999997783463239554465379844392 : Int)/10^30,(-2105485361586695723072680425 : Int)/10^30)
theorem v4046_pa_checked : Scalar.distance (sourceCoefficient 59 94 1 0) v4046_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4046_pb : Scalar.QComplex := ((-908469517233947153914995 : Int)/10^30,(-431476523253167861785044837 : Int)/10^30)
theorem v4046_pb_checked : Scalar.distance (sourceCoefficient 59 94 1 1) v4046_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4046_pg : Scalar.QComplex := ((-93086219105821324280341 : Int)/10^30,(195992106116466559071 : Int)/10^30)
theorem v4046_pg_checked : Scalar.distance (sourceCoefficient 59 94 1 2) v4046_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4046_mb : Scalar.QComplex := ((-1280813985555489493715131 : Int)/10^30,(-431475578626461378645753842 : Int)/10^30)
theorem v4046_mb_checked : Scalar.distance (sourceCoefficient 59 94 3 1) v4046_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4046_mg : Scalar.QComplex := ((-93086015313207279075076 : Int)/10^30,(276321247780294420112 : Int)/10^30)
theorem v4046_mg_checked : Scalar.distance (sourceCoefficient 59 94 3 2) v4046_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4046_upper : Scalar.QComplex := ((999992660207283118584607754828 : Int)/10^30,(-3831387680880871653041020576 : Int)/10^30)
theorem v4046_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 94 5) 1) 14) v4046_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4046 : Material (59 : Basis) (94 : Basis) where
  plus := ![v4046_pa,v4046_pb,v4046_pg]
  minus := ![(Primitive.Addresses.material4046 1).one,v4046_mb,v4046_mg]
  upper := v4046_upper
  lower := (Primitive.Addresses.material4046 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4046_pa_checked.trans (by decide +kernel)
    · exact v4046_pb_checked.trans (by decide +kernel)
    · exact v4046_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 94 Primitive.Addresses.material4046
    · exact v4046_mb_checked.trans (by decide +kernel)
    · exact v4046_mg_checked.trans (by decide +kernel)
  upper_error := v4046_upper_checked
  lower_error := reuse_lower_error 59 94 Primitive.Addresses.material4046

def v4047_pa : Scalar.QComplex := ((999997689264408475352933439388 : Int)/10^30,(-2149759485047180852270647801 : Int)/10^30)
theorem v4047_pa_checked : Scalar.distance (sourceCoefficient 59 95 1 0) v4047_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4047_pb : Scalar.QComplex := ((-927572793753027582029916 : Int)/10^30,(-431476477638242353892237368 : Int)/10^30)
theorem v4047_pb_checked : Scalar.distance (sourceCoefficient 59 95 1 1) v4047_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4047_pg : Scalar.QComplex := ((-93086209801050901855598 : Int)/10^30,(200113424856114182861 : Int)/10^30)
theorem v4047_pg_checked : Scalar.distance (sourceCoefficient 59 95 1 2) v4047_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4047_mb : Scalar.QComplex := ((-1299917215597920717579035 : Int)/10^30,(-431475516526285598943634593 : Int)/10^30)
theorem v4047_mb_checked : Scalar.distance (sourceCoefficient 59 95 3 1) v4047_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4047_mg : Scalar.QComplex := ((-93086002451927866231306 : Int)/10^30,(280442556955788920311 : Int)/10^30)
theorem v4047_mg_checked : Scalar.distance (sourceCoefficient 59 95 3 2) v4047_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4047_upper : Scalar.QComplex := ((999992489595471761873374106568 : Int)/10^30,(-3875661575821613900377053854 : Int)/10^30)
theorem v4047_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 95 5) 1) 14) v4047_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4047 : Material (59 : Basis) (95 : Basis) where
  plus := ![v4047_pa,v4047_pb,v4047_pg]
  minus := ![(Primitive.Addresses.material4047 1).one,v4047_mb,v4047_mg]
  upper := v4047_upper
  lower := (Primitive.Addresses.material4047 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4047_pa_checked.trans (by decide +kernel)
    · exact v4047_pb_checked.trans (by decide +kernel)
    · exact v4047_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 95 Primitive.Addresses.material4047
    · exact v4047_mb_checked.trans (by decide +kernel)
    · exact v4047_mg_checked.trans (by decide +kernel)
  upper_error := v4047_upper_checked
  lower_error := reuse_lower_error 59 95 Primitive.Addresses.material4047

def v4048_pa : Scalar.QComplex := ((999997643325634636096206333406 : Int)/10^30,(-2171023532072774015415228153 : Int)/10^30)
theorem v4048_pa_checked : Scalar.distance (sourceCoefficient 59 96 1 0) v4048_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4048_pb : Scalar.QComplex := ((-936747745664780956668903 : Int)/10^30,(-431476455329357370522611902 : Int)/10^30)
theorem v4048_pb_checked : Scalar.distance (sourceCoefficient 59 96 1 1) v4048_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4048_pg : Scalar.QComplex := ((-93086205256466963933853 : Int)/10^30,(202092818390110654934 : Int)/10^30)
theorem v4048_pg_checked : Scalar.distance (sourceCoefficient 59 96 1 2) v4048_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4048_mb : Scalar.QComplex := ((-1309092144841857193688651 : Int)/10^30,(-431475486299838646842783624 : Int)/10^30)
theorem v4048_mb_checked : Scalar.distance (sourceCoefficient 59 96 3 1) v4048_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4048_mg : Scalar.QComplex := ((-93085996199218149202325 : Int)/10^30,(282421945830995458959 : Int)/10^30)
theorem v4048_mg_checked : Scalar.distance (sourceCoefficient 59 96 3 2) v4048_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4048_upper : Scalar.QComplex := ((999992406956950236127311238097 : Int)/10^30,(-3896925511890750755779271449 : Int)/10^30)
theorem v4048_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 96 5) 1) 14) v4048_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4048 : Material (59 : Basis) (96 : Basis) where
  plus := ![v4048_pa,v4048_pb,v4048_pg]
  minus := ![(Primitive.Addresses.material4048 1).one,v4048_mb,v4048_mg]
  upper := v4048_upper
  lower := (Primitive.Addresses.material4048 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4048_pa_checked.trans (by decide +kernel)
    · exact v4048_pb_checked.trans (by decide +kernel)
    · exact v4048_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 96 Primitive.Addresses.material4048
    · exact v4048_mb_checked.trans (by decide +kernel)
    · exact v4048_mg_checked.trans (by decide +kernel)
  upper_error := v4048_upper_checked
  lower_error := reuse_lower_error 59 96 Primitive.Addresses.material4048

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
