import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B068

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1633_pa : Scalar.QComplex := ((999999710727767847905064832851 : Int)/10^30,(-760621049291804424540479425 : Int)/10^30)
theorem v1633_pa_checked : Scalar.distance (sourceCoefficient 18 59 1 0) v1633_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1633_pb : Scalar.QComplex := ((-328190865955993585327794 : Int)/10^30,(-431477371451999104786486114 : Int)/10^30)
theorem v1633_pb_checked : Scalar.distance (sourceCoefficient 18 59 1 1) v1633_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1633_pg : Scalar.QComplex := ((-93086400301595051569816 : Int)/10^30,(70803495953681486664 : Int)/10^30)
theorem v1633_pg_checked : Scalar.distance (sourceCoefficient 18 59 1 2) v1633_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1633_mb : Scalar.QComplex := ((-700536282299187745846036 : Int)/10^30,(-431476927579318071046739765 : Int)/10^30)
theorem v1633_mb_checked : Scalar.distance (sourceCoefficient 18 59 3 1) v1633_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1633_mg : Scalar.QComplex := ((-93086304541045823681725 : Int)/10^30,(151132840594742285381 : Int)/10^30)
theorem v1633_mg_checked : Scalar.distance (sourceCoefficient 18 59 3 2) v1633_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1633_upper : Scalar.QComplex := ((999996908582738861524614186207 : Int)/10^30,(-2486528697887130420463446044 : Int)/10^30)
theorem v1633_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 59 5) 1) 14) v1633_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1633 : Material (18 : Basis) (59 : Basis) where
  plus := ![v1633_pa,v1633_pb,v1633_pg]
  minus := ![(Primitive.Addresses.material1633 1).one,v1633_mb,v1633_mg]
  upper := v1633_upper
  lower := (Primitive.Addresses.material1633 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1633_pa_checked.trans (by decide +kernel)
    · exact v1633_pb_checked.trans (by decide +kernel)
    · exact v1633_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 59 Primitive.Addresses.material1633
    · exact v1633_mb_checked.trans (by decide +kernel)
    · exact v1633_mg_checked.trans (by decide +kernel)
  upper_error := v1633_upper_checked
  lower_error := reuse_lower_error 18 59 Primitive.Addresses.material1633

def v1634_pa : Scalar.QComplex := ((999999695109282623233242983377 : Int)/10^30,(-780884973472523654447698961 : Int)/10^30)
theorem v1634_pa_checked : Scalar.distance (sourceCoefficient 18 60 1 0) v1634_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1634_pb : Scalar.QComplex := ((-336934291868235630591441 : Int)/10^30,(-431477362974193657185598573 : Int)/10^30)
theorem v1634_pb_checked : Scalar.distance (sourceCoefficient 18 60 1 1) v1634_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1634_pg : Scalar.QComplex := ((-93086398660164874030387 : Int)/10^30,(72689792110838471749 : Int)/10^30)
theorem v1634_pg_checked : Scalar.distance (sourceCoefficient 18 60 1 2) v1634_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1634_mb : Scalar.QComplex := ((-709279697639888454581161 : Int)/10^30,(-431476911556333007140332145 : Int)/10^30)
theorem v1634_mb_checked : Scalar.distance (sourceCoefficient 18 60 3 1) v1634_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1634_mg : Scalar.QComplex := ((-93086301271827629320508 : Int)/10^30,(153019134633064687217 : Int)/10^30)
theorem v1634_mg_checked : Scalar.distance (sourceCoefficient 18 60 3 2) v1634_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1634_upper : Scalar.QComplex := ((999996857990582091671905518009 : Int)/10^30,(-2506792564931026351063172731 : Int)/10^30)
theorem v1634_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 60 5) 1) 14) v1634_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1634 : Material (18 : Basis) (60 : Basis) where
  plus := ![v1634_pa,v1634_pb,v1634_pg]
  minus := ![(Primitive.Addresses.material1634 1).one,v1634_mb,v1634_mg]
  upper := v1634_upper
  lower := (Primitive.Addresses.material1634 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1634_pa_checked.trans (by decide +kernel)
    · exact v1634_pb_checked.trans (by decide +kernel)
    · exact v1634_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 60 Primitive.Addresses.material1634
    · exact v1634_mb_checked.trans (by decide +kernel)
    · exact v1634_mg_checked.trans (by decide +kernel)
  upper_error := v1634_upper_checked
  lower_error := reuse_lower_error 18 60 Primitive.Addresses.material1634

def v1635_pa : Scalar.QComplex := ((999999690516649607922444321905 : Int)/10^30,(-786744307258852011231480399 : Int)/10^30)
theorem v1635_pa_checked : Scalar.distance (sourceCoefficient 18 61 1 0) v1635_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1635_pb : Scalar.QComplex := ((-339462462125750330226358 : Int)/10^30,(-431477360478798401581093598 : Int)/10^30)
theorem v1635_pb_checked : Scalar.distance (sourceCoefficient 18 61 1 1) v1635_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1635_pg : Scalar.QComplex := ((-93086398177232216018879 : Int)/10^30,(73235216514248397875 : Int)/10^30)
theorem v1635_pg_checked : Scalar.distance (sourceCoefficient 18 61 1 2) v1635_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1635_mb : Scalar.QComplex := ((-711807864802636107098213 : Int)/10^30,(-431476906879241613011887496 : Int)/10^30)
theorem v1635_mb_checked : Scalar.distance (sourceCoefficient 18 61 3 1) v1635_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1635_mg : Scalar.QComplex := ((-93086300318218455987368 : Int)/10^30,(153564558416639047443 : Int)/10^30)
theorem v1635_mg_checked : Scalar.distance (sourceCoefficient 18 61 3 2) v1635_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1635_upper : Scalar.QComplex := ((999996843285277355954569756882 : Int)/10^30,(-2512651882064097374792936173 : Int)/10^30)
theorem v1635_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 61 5) 1) 14) v1635_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1635 : Material (18 : Basis) (61 : Basis) where
  plus := ![v1635_pa,v1635_pb,v1635_pg]
  minus := ![(Primitive.Addresses.material1635 1).one,v1635_mb,v1635_mg]
  upper := v1635_upper
  lower := (Primitive.Addresses.material1635 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1635_pa_checked.trans (by decide +kernel)
    · exact v1635_pb_checked.trans (by decide +kernel)
    · exact v1635_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 61 Primitive.Addresses.material1635
    · exact v1635_mb_checked.trans (by decide +kernel)
    · exact v1635_mg_checked.trans (by decide +kernel)
  upper_error := v1635_upper_checked
  lower_error := reuse_lower_error 18 61 Primitive.Addresses.material1635

def v1636_pa : Scalar.QComplex := ((999999683782570875375939677439 : Int)/10^30,(-795257667838409237716629995 : Int)/10^30)
theorem v1636_pa_checked : Scalar.distance (sourceCoefficient 18 62 1 0) v1636_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1636_pb : Scalar.QComplex := ((-343135785013599367604900 : Int)/10^30,(-431477356817899107564494679 : Int)/10^30)
theorem v1636_pb_checked : Scalar.distance (sourceCoefficient 18 62 1 1) v1636_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1636_pg : Scalar.QComplex := ((-93086397468907585431223 : Int)/10^30,(74027694767449970358 : Int)/10^30)
theorem v1636_pg_checked : Scalar.distance (sourceCoefficient 18 62 1 2) v1636_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1636_mb : Scalar.QComplex := ((-715481183163547944228400 : Int)/10^30,(-431476900048431470223123153 : Int)/10^30)
theorem v1636_mb_checked : Scalar.distance (sourceCoefficient 18 62 3 1) v1636_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1636_mg : Scalar.QComplex := ((-93086298926021048523965 : Int)/10^30,(154357035763512493774 : Int)/10^30)
theorem v1636_mg_checked : Scalar.distance (sourceCoefficient 18 62 3 2) v1636_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1636_upper : Scalar.QComplex := ((999996821857920618750221374582 : Int)/10^30,(-2521165218341595086086099347 : Int)/10^30)
theorem v1636_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 62 5) 1) 14) v1636_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1636 : Material (18 : Basis) (62 : Basis) where
  plus := ![v1636_pa,v1636_pb,v1636_pg]
  minus := ![(Primitive.Addresses.material1636 1).one,v1636_mb,v1636_mg]
  upper := v1636_upper
  lower := (Primitive.Addresses.material1636 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1636_pa_checked.trans (by decide +kernel)
    · exact v1636_pb_checked.trans (by decide +kernel)
    · exact v1636_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 62 Primitive.Addresses.material1636
    · exact v1636_mb_checked.trans (by decide +kernel)
    · exact v1636_mg_checked.trans (by decide +kernel)
  upper_error := v1636_upper_checked
  lower_error := reuse_lower_error 18 62 Primitive.Addresses.material1636

def v1637_pa : Scalar.QComplex := ((999999663756618540632492053049 : Int)/10^30,(-820052833577888102564617380 : Int)/10^30)
theorem v1637_pa_checked : Scalar.distance (sourceCoefficient 18 63 1 0) v1637_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1637_pb : Scalar.QComplex := ((-353834339119144114676321 : Int)/10^30,(-431477345917959688437046003 : Int)/10^30)
theorem v1637_pb_checked : Scalar.distance (sourceCoefficient 18 63 1 1) v1637_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1637_pg : Scalar.QComplex := ((-93086395361065615744541 : Int)/10^30,(76335787950796903421 : Int)/10^30)
theorem v1637_pg_checked : Scalar.distance (sourceCoefficient 18 63 1 2) v1637_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1637_mb : Scalar.QComplex := ((-726179723879375246069189 : Int)/10^30,(-431476879916125761546142262 : Int)/10^30)
theorem v1637_mb_checked : Scalar.distance (sourceCoefficient 18 63 3 1) v1637_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1637_mg : Scalar.QComplex := ((-93086294826399399112852 : Int)/10^30,(156665126268478163446 : Int)/10^30)
theorem v1637_mg_checked : Scalar.distance (sourceCoefficient 18 63 3 2) v1637_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1637_upper : Scalar.QComplex := ((999996759037791443834380081777 : Int)/10^30,(-2545960312588610237187234171 : Int)/10^30)
theorem v1637_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 63 5) 1) 14) v1637_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1637 : Material (18 : Basis) (63 : Basis) where
  plus := ![v1637_pa,v1637_pb,v1637_pg]
  minus := ![(Primitive.Addresses.material1637 1).one,v1637_mb,v1637_mg]
  upper := v1637_upper
  lower := (Primitive.Addresses.material1637 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1637_pa_checked.trans (by decide +kernel)
    · exact v1637_pb_checked.trans (by decide +kernel)
    · exact v1637_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 63 Primitive.Addresses.material1637
    · exact v1637_mb_checked.trans (by decide +kernel)
    · exact v1637_mg_checked.trans (by decide +kernel)
  upper_error := v1637_upper_checked
  lower_error := reuse_lower_error 18 63 Primitive.Addresses.material1637

def v1638_pa : Scalar.QComplex := ((999999634068283781936881752932 : Int)/10^30,(-855490092596112595212678865 : Int)/10^30)
theorem v1638_pa_checked : Scalar.distance (sourceCoefficient 18 64 1 0) v1638_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1638_pb : Scalar.QComplex := ((-369124715834669847996298 : Int)/10^30,(-431477329725777833219407198 : Int)/10^30)
theorem v1638_pb_checked : Scalar.distance (sourceCoefficient 18 64 1 1) v1638_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1638_pg : Scalar.QComplex := ((-93086392232634364729911 : Int)/10^30,(79634515451329338237 : Int)/10^30)
theorem v1638_pg_checked : Scalar.distance (sourceCoefficient 18 64 1 2) v1638_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1638_mb : Scalar.QComplex := ((-741470080928471251207588 : Int)/10^30,(-431476850529043482922385719 : Int)/10^30)
theorem v1638_mb_checked : Scalar.distance (sourceCoefficient 18 64 3 1) v1638_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1638_mg : Scalar.QComplex := ((-93086288851316049168139 : Int)/10^30,(159963849841048320206 : Int)/10^30)
theorem v1638_mg_checked : Scalar.distance (sourceCoefficient 18 64 3 2) v1638_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1638_upper : Scalar.QComplex := ((999996668188006679995639541526 : Int)/10^30,(-2581397467587827686233377991 : Int)/10^30)
theorem v1638_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 64 5) 1) 14) v1638_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1638 : Material (18 : Basis) (64 : Basis) where
  plus := ![v1638_pa,v1638_pb,v1638_pg]
  minus := ![(Primitive.Addresses.material1638 1).one,v1638_mb,v1638_mg]
  upper := v1638_upper
  lower := (Primitive.Addresses.material1638 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1638_pa_checked.trans (by decide +kernel)
    · exact v1638_pb_checked.trans (by decide +kernel)
    · exact v1638_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 64 Primitive.Addresses.material1638
    · exact v1638_mb_checked.trans (by decide +kernel)
    · exact v1638_mg_checked.trans (by decide +kernel)
  upper_error := v1638_upper_checked
  lower_error := reuse_lower_error 18 64 Primitive.Addresses.material1638

def v1639_pa : Scalar.QComplex := ((999999602652399076882652315780 : Int)/10^30,(-891456697748757023724999639 : Int)/10^30)
theorem v1639_pa_checked : Scalar.distance (sourceCoefficient 18 65 1 0) v1639_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1639_pb : Scalar.QComplex := ((-384643493039165786083872 : Int)/10^30,(-431477312552989826191773096 : Int)/10^30)
theorem v1639_pb_checked : Scalar.distance (sourceCoefficient 18 65 1 1) v1639_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1639_pg : Scalar.QComplex := ((-93086388918020001669603 : Int)/10^30,(82982517843118985507 : Int)/10^30)
theorem v1639_pg_checked : Scalar.distance (sourceCoefficient 18 65 1 2) v1639_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1639_mb : Scalar.QComplex := ((-756988837535274576501538 : Int)/10^30,(-431476819964256082407993536 : Int)/10^30)
theorem v1639_mb_checked : Scalar.distance (sourceCoefficient 18 65 3 1) v1639_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1639_mg : Scalar.QComplex := ((-93086282647527644605975 : Int)/10^30,(163311848125860755113 : Int)/10^30)
theorem v1639_mg_checked : Scalar.distance (sourceCoefficient 18 65 3 2) v1639_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1639_upper : Scalar.QComplex := ((999996574697071136678371423559 : Int)/10^30,(-2617363964951471699982149354 : Int)/10^30)
theorem v1639_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 65 5) 1) 14) v1639_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1639 : Material (18 : Basis) (65 : Basis) where
  plus := ![v1639_pa,v1639_pb,v1639_pg]
  minus := ![(Primitive.Addresses.material1639 1).one,v1639_mb,v1639_mg]
  upper := v1639_upper
  lower := (Primitive.Addresses.material1639 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1639_pa_checked.trans (by decide +kernel)
    · exact v1639_pb_checked.trans (by decide +kernel)
    · exact v1639_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 65 Primitive.Addresses.material1639
    · exact v1639_mb_checked.trans (by decide +kernel)
    · exact v1639_mg_checked.trans (by decide +kernel)
  upper_error := v1639_upper_checked
  lower_error := reuse_lower_error 18 65 Primitive.Addresses.material1639

def v1640_pa : Scalar.QComplex := ((999999586819183919828741777445 : Int)/10^30,(-909044257141507791709626945 : Int)/10^30)
theorem v1640_pa_checked : Scalar.distance (sourceCoefficient 18 66 1 0) v1640_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1640_pb : Scalar.QComplex := ((-392232127245999680143582 : Int)/10^30,(-431477303884613674353066592 : Int)/10^30)
theorem v1640_pb_checked : Scalar.distance (sourceCoefficient 18 66 1 1) v1640_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1640_pg : Scalar.QComplex := ((-93086387246038856856632 : Int)/10^30,(84619680707290849004 : Int)/10^30)
theorem v1640_pg_checked : Scalar.distance (sourceCoefficient 18 66 1 2) v1640_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1640_mb : Scalar.QComplex := ((-764577461436094927772999 : Int)/10^30,(-431476804747233617101470343 : Int)/10^30)
theorem v1640_mb_checked : Scalar.distance (sourceCoefficient 18 66 3 1) v1640_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1640_mg : Scalar.QComplex := ((-93086279562749305645906 : Int)/10^30,(164949008937597637501 : Int)/10^30)
theorem v1640_mg_checked : Scalar.distance (sourceCoefficient 18 66 3 2) v1640_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1640_upper : Scalar.QComplex := ((999996528509347580375218422293 : Int)/10^30,(-2634951470822925749301578207 : Int)/10^30)
theorem v1640_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 66 5) 1) 14) v1640_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1640 : Material (18 : Basis) (66 : Basis) where
  plus := ![v1640_pa,v1640_pb,v1640_pg]
  minus := ![(Primitive.Addresses.material1640 1).one,v1640_mb,v1640_mg]
  upper := v1640_upper
  lower := (Primitive.Addresses.material1640 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1640_pa_checked.trans (by decide +kernel)
    · exact v1640_pb_checked.trans (by decide +kernel)
    · exact v1640_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 66 Primitive.Addresses.material1640
    · exact v1640_mb_checked.trans (by decide +kernel)
    · exact v1640_mg_checked.trans (by decide +kernel)
  upper_error := v1640_upper_checked
  lower_error := reuse_lower_error 18 66 Primitive.Addresses.material1640

def v1641_pa : Scalar.QComplex := ((999999559551152646387730589708 : Int)/10^30,(-938561399542958725708331600 : Int)/10^30)
theorem v1641_pa_checked : Scalar.distance (sourceCoefficient 18 67 1 0) v1641_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1641_pb : Scalar.QComplex := ((-404968106543031995542773 : Int)/10^30,(-431477288936556717176906977 : Int)/10^30)
theorem v1641_pb_checked : Scalar.distance (sourceCoefficient 18 67 1 1) v1641_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1641_pg : Scalar.QComplex := ((-93086384364459297874316 : Int)/10^30,(87367325668338596114 : Int)/10^30)
theorem v1641_pg_checked : Scalar.distance (sourceCoefficient 18 67 1 2) v1641_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1641_mb : Scalar.QComplex := ((-777313423091440169329338 : Int)/10^30,(-431476778808605699645425290 : Int)/10^30)
theorem v1641_mb_checked : Scalar.distance (sourceCoefficient 18 67 3 1) v1641_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1641_mg : Scalar.QComplex := ((-93086274310076967558404 : Int)/10^30,(167696650388898214160 : Int)/10^30)
theorem v1641_mg_checked : Scalar.distance (sourceCoefficient 18 67 3 2) v1641_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1641_upper : Scalar.QComplex := ((999996450297446908800384165675 : Int)/10^30,(-2664468522199912161966208691 : Int)/10^30)
theorem v1641_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 67 5) 1) 14) v1641_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1641 : Material (18 : Basis) (67 : Basis) where
  plus := ![v1641_pa,v1641_pb,v1641_pg]
  minus := ![(Primitive.Addresses.material1641 1).one,v1641_mb,v1641_mg]
  upper := v1641_upper
  lower := (Primitive.Addresses.material1641 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1641_pa_checked.trans (by decide +kernel)
    · exact v1641_pb_checked.trans (by decide +kernel)
    · exact v1641_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 67 Primitive.Addresses.material1641
    · exact v1641_mb_checked.trans (by decide +kernel)
    · exact v1641_mg_checked.trans (by decide +kernel)
  upper_error := v1641_upper_checked
  lower_error := reuse_lower_error 18 67 Primitive.Addresses.material1641

def v1642_pa : Scalar.QComplex := ((999999512205114162525438224338 : Int)/10^30,(-987719359803734167121095702 : Int)/10^30)
theorem v1642_pa_checked : Scalar.distance (sourceCoefficient 18 68 1 0) v1642_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1642_pb : Scalar.QComplex := ((-426178653798371199812715 : Int)/10^30,(-431477262929510329983621534 : Int)/10^30)
theorem v1642_pb_checked : Scalar.distance (sourceCoefficient 18 68 1 1) v1642_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1642_pg : Scalar.QComplex := ((-93086379355458338369312 : Int)/10^30,(91943263872874751101 : Int)/10^30)
theorem v1642_pg_checked : Scalar.distance (sourceCoefficient 18 68 1 2) v1642_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1642_mb : Scalar.QComplex := ((-798523940006213542279339 : Int)/10^30,(-431476734497822002292795617 : Int)/10^30)
theorem v1642_mb_checked : Scalar.distance (sourceCoefficient 18 68 3 1) v1642_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1642_mg : Scalar.QComplex := ((-93086265352249295224893 : Int)/10^30,(172272582567061213866 : Int)/10^30)
theorem v1642_mg_checked : Scalar.distance (sourceCoefficient 18 68 3 2) v1642_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1642_upper : Scalar.QComplex := ((999996318109299106520912188379 : Int)/10^30,(-2713626327530713070515345407 : Int)/10^30)
theorem v1642_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 68 5) 1) 14) v1642_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1642 : Material (18 : Basis) (68 : Basis) where
  plus := ![v1642_pa,v1642_pb,v1642_pg]
  minus := ![(Primitive.Addresses.material1642 1).one,v1642_mb,v1642_mg]
  upper := v1642_upper
  lower := (Primitive.Addresses.material1642 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1642_pa_checked.trans (by decide +kernel)
    · exact v1642_pb_checked.trans (by decide +kernel)
    · exact v1642_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 68 Primitive.Addresses.material1642
    · exact v1642_mb_checked.trans (by decide +kernel)
    · exact v1642_mg_checked.trans (by decide +kernel)
  upper_error := v1642_upper_checked
  lower_error := reuse_lower_error 18 68 Primitive.Addresses.material1642

def v1643_pa : Scalar.QComplex := ((999999490601377920768652332806 : Int)/10^30,(-1009354736785589429531182522 : Int)/10^30)
theorem v1643_pa_checked : Scalar.distance (sourceCoefficient 18 69 1 0) v1643_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1643_pb : Scalar.QComplex := ((-435513829005341423757389 : Int)/10^30,(-431477251042722669192641833 : Int)/10^30)
theorem v1643_pb_checked : Scalar.distance (sourceCoefficient 18 69 1 1) v1643_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1643_pg : Scalar.QComplex := ((-93086377067730517271473 : Int)/10^30,(93957223485203441990 : Int)/10^30)
theorem v1643_pg_checked : Scalar.distance (sourceCoefficient 18 69 1 2) v1643_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1643_mb : Scalar.QComplex := ((-807859101479509007865757 : Int)/10^30,(-431476714555203004564641916 : Int)/10^30)
theorem v1643_mb_checked : Scalar.distance (sourceCoefficient 18 69 3 1) v1643_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1643_mg : Scalar.QComplex := ((-93086261326565885886813 : Int)/10^30,(174286539455294624413 : Int)/10^30)
theorem v1643_mg_checked : Scalar.distance (sourceCoefficient 18 69 3 2) v1643_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1643_upper : Scalar.QComplex := ((999996259164897116376985378877 : Int)/10^30,(-2735261635003126910730762853 : Int)/10^30)
theorem v1643_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 69 5) 1) 14) v1643_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1643 : Material (18 : Basis) (69 : Basis) where
  plus := ![v1643_pa,v1643_pb,v1643_pg]
  minus := ![(Primitive.Addresses.material1643 1).one,v1643_mb,v1643_mg]
  upper := v1643_upper
  lower := (Primitive.Addresses.material1643 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1643_pa_checked.trans (by decide +kernel)
    · exact v1643_pb_checked.trans (by decide +kernel)
    · exact v1643_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 69 Primitive.Addresses.material1643
    · exact v1643_mb_checked.trans (by decide +kernel)
    · exact v1643_mg_checked.trans (by decide +kernel)
  upper_error := v1643_upper_checked
  lower_error := reuse_lower_error 18 69 Primitive.Addresses.material1643

def v1644_pa : Scalar.QComplex := ((999999476135001080481639357733 : Int)/10^30,(-1023586695597641904177146852 : Int)/10^30)
theorem v1644_pa_checked : Scalar.distance (sourceCoefficient 18 70 1 0) v1644_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1644_pb : Scalar.QComplex := ((-441654596833787482410876 : Int)/10^30,(-431477243076644043440842255 : Int)/10^30)
theorem v1644_pb_checked : Scalar.distance (sourceCoefficient 18 70 1 1) v1644_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1644_pg : Scalar.QComplex := ((-93086375535122823422255 : Int)/10^30,(95282025454075707523 : Int)/10^30)
theorem v1644_pg_checked : Scalar.distance (sourceCoefficient 18 70 1 2) v1644_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1644_mb : Scalar.QComplex := ((-813999860147099481873779 : Int)/10^30,(-431476701289921278915269193 : Int)/10^30)
theorem v1644_mb_checked : Scalar.distance (sourceCoefficient 18 70 3 1) v1644_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1644_mg : Scalar.QComplex := ((-93086258650714330426458 : Int)/10^30,(175611339608311156789 : Int)/10^30)
theorem v1644_mg_checked : Scalar.distance (sourceCoefficient 18 70 3 2) v1644_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1644_upper : Scalar.QComplex := ((999996220135472025674171202351 : Int)/10^30,(-2749493547650694491264228607 : Int)/10^30)
theorem v1644_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 70 5) 1) 14) v1644_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1644 : Material (18 : Basis) (70 : Basis) where
  plus := ![v1644_pa,v1644_pb,v1644_pg]
  minus := ![(Primitive.Addresses.material1644 1).one,v1644_mb,v1644_mg]
  upper := v1644_upper
  lower := (Primitive.Addresses.material1644 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1644_pa_checked.trans (by decide +kernel)
    · exact v1644_pb_checked.trans (by decide +kernel)
    · exact v1644_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 70 Primitive.Addresses.material1644
    · exact v1644_mb_checked.trans (by decide +kernel)
    · exact v1644_mg_checked.trans (by decide +kernel)
  upper_error := v1644_upper_checked
  lower_error := reuse_lower_error 18 70 Primitive.Addresses.material1644

def v1645_pa : Scalar.QComplex := ((999999450974126995036988647312 : Int)/10^30,(-1047879499074448346869539156 : Int)/10^30)
theorem v1645_pa_checked : Scalar.distance (sourceCoefficient 18 71 1 0) v1645_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1645_pb : Scalar.QComplex := ((-452136391041167364261458 : Int)/10^30,(-431477229209985516802897579 : Int)/10^30)
theorem v1645_pb_checked : Scalar.distance (sourceCoefficient 18 71 1 1) v1645_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1645_pg : Scalar.QComplex := ((-93086372868266916529908 : Int)/10^30,(97543355325682669584 : Int)/10^30)
theorem v1645_pg_checked : Scalar.distance (sourceCoefficient 18 71 1 2) v1645_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1645_mb : Scalar.QComplex := ((-824481638485326561284224 : Int)/10^30,(-431476678377951596985768290 : Int)/10^30)
theorem v1645_mb_checked : Scalar.distance (sourceCoefficient 18 71 3 1) v1645_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1645_mg : Scalar.QComplex := ((-93086254032433583846335 : Int)/10^30,(177872666336545122854 : Int)/10^30)
theorem v1645_mg_checked : Scalar.distance (sourceCoefficient 18 71 3 2) v1645_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1645_upper : Scalar.QComplex := ((999996153047460439344019359209 : Int)/10^30,(-2773786271520837693595660008 : Int)/10^30)
theorem v1645_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 71 5) 1) 14) v1645_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1645 : Material (18 : Basis) (71 : Basis) where
  plus := ![v1645_pa,v1645_pb,v1645_pg]
  minus := ![(Primitive.Addresses.material1645 1).one,v1645_mb,v1645_mg]
  upper := v1645_upper
  lower := (Primitive.Addresses.material1645 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1645_pa_checked.trans (by decide +kernel)
    · exact v1645_pb_checked.trans (by decide +kernel)
    · exact v1645_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 71 Primitive.Addresses.material1645
    · exact v1645_mb_checked.trans (by decide +kernel)
    · exact v1645_mg_checked.trans (by decide +kernel)
  upper_error := v1645_upper_checked
  lower_error := reuse_lower_error 18 71 Primitive.Addresses.material1645

def v1646_pa : Scalar.QComplex := ((999999423001777651913416359000 : Int)/10^30,(-1074242110405854725926410419 : Int)/10^30)
theorem v1646_pa_checked : Scalar.distance (sourceCoefficient 18 72 1 0) v1646_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1646_pb : Scalar.QComplex := ((-463511260165789047753379 : Int)/10^30,(-431477213777719835829536091 : Int)/10^30)
theorem v1646_pb_checked : Scalar.distance (sourceCoefficient 18 72 1 1) v1646_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1646_pg : Scalar.QComplex := ((-93086369901674829960474 : Int)/10^30,(99997356151491943934 : Int)/10^30)
theorem v1646_pg_checked : Scalar.distance (sourceCoefficient 18 72 1 2) v1646_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1646_mb : Scalar.QComplex := ((-835856490057214373244065 : Int)/10^30,(-431476653129691912689410531 : Int)/10^30)
theorem v1646_mb_checked : Scalar.distance (sourceCoefficient 18 72 3 1) v1646_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1646_mg : Scalar.QComplex := ((-93086248948150413295659 : Int)/10^30,(180326663688582376015 : Int)/10^30)
theorem v1646_mg_checked : Scalar.distance (sourceCoefficient 18 72 3 2) v1646_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1646_upper : Scalar.QComplex := ((999996079575677197159371832070 : Int)/10^30,(-2800148795310493929864166135 : Int)/10^30)
theorem v1646_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 72 5) 1) 14) v1646_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1646 : Material (18 : Basis) (72 : Basis) where
  plus := ![v1646_pa,v1646_pb,v1646_pg]
  minus := ![(Primitive.Addresses.material1646 1).one,v1646_mb,v1646_mg]
  upper := v1646_upper
  lower := (Primitive.Addresses.material1646 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1646_pa_checked.trans (by decide +kernel)
    · exact v1646_pb_checked.trans (by decide +kernel)
    · exact v1646_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 72 Primitive.Addresses.material1646
    · exact v1646_mb_checked.trans (by decide +kernel)
    · exact v1646_mg_checked.trans (by decide +kernel)
  upper_error := v1646_upper_checked
  lower_error := reuse_lower_error 18 72 Primitive.Addresses.material1646

def v1647_pa : Scalar.QComplex := ((999999412805925763230004664716 : Int)/10^30,(-1083691747535552275736948288 : Int)/10^30)
theorem v1647_pa_checked : Scalar.distance (sourceCoefficient 18 73 1 0) v1647_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1647_pb : Scalar.QComplex := ((-467588564285663372479779 : Int)/10^30,(-431477208148703048401639379 : Int)/10^30)
theorem v1647_pb_checked : Scalar.distance (sourceCoefficient 18 73 1 1) v1647_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1647_pg : Scalar.QComplex := ((-93086368819928520998646 : Int)/10^30,(100876988932577412055 : Int)/10^30)
theorem v1647_pg_checked : Scalar.distance (sourceCoefficient 18 73 1 2) v1647_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1647_mb : Scalar.QComplex := ((-839933787801334066092164 : Int)/10^30,(-431476643982147400710889284 : Int)/10^30)
theorem v1647_mb_checked : Scalar.distance (sourceCoefficient 18 73 3 1) v1647_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1647_mg : Scalar.QComplex := ((-93086247107321034230461 : Int)/10^30,(181206295208642013946 : Int)/10^30)
theorem v1647_mg_checked : Scalar.distance (sourceCoefficient 18 73 3 2) v1647_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1647_upper : Scalar.QComplex := ((999996053070624072525512755761 : Int)/10^30,(-2809598400768951607933355912 : Int)/10^30)
theorem v1647_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 73 5) 1) 14) v1647_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1647 : Material (18 : Basis) (73 : Basis) where
  plus := ![v1647_pa,v1647_pb,v1647_pg]
  minus := ![(Primitive.Addresses.material1647 1).one,v1647_mb,v1647_mg]
  upper := v1647_upper
  lower := (Primitive.Addresses.material1647 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1647_pa_checked.trans (by decide +kernel)
    · exact v1647_pb_checked.trans (by decide +kernel)
    · exact v1647_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 73 Primitive.Addresses.material1647
    · exact v1647_mb_checked.trans (by decide +kernel)
    · exact v1647_mg_checked.trans (by decide +kernel)
  upper_error := v1647_upper_checked
  lower_error := reuse_lower_error 18 73 Primitive.Addresses.material1647

def v1648_pa : Scalar.QComplex := ((999999401226314255716436333878 : Int)/10^30,(-1094324911970224859295402649 : Int)/10^30)
theorem v1648_pa_checked : Scalar.distance (sourceCoefficient 18 74 1 0) v1648_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1648_pb : Scalar.QComplex := ((-472176533552666815259935 : Int)/10^30,(-431477201753249305872770192 : Int)/10^30)
theorem v1648_pb_checked : Scalar.distance (sourceCoefficient 18 74 1 1) v1648_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1648_pg : Scalar.QComplex := ((-93086367591102507044553 : Int)/10^30,(101866792014915753029 : Int)/10^30)
theorem v1648_pg_checked : Scalar.distance (sourceCoefficient 18 74 1 2) v1648_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1648_mb : Scalar.QComplex := ((-844521749841038330954588 : Int)/10^30,(-431476633627485196542917924 : Int)/10^30)
theorem v1648_mb_checked : Scalar.distance (sourceCoefficient 18 74 3 1) v1648_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1648_mg : Scalar.QComplex := ((-93086245024339996842440 : Int)/10^30,(182196096862009925356 : Int)/10^30)
theorem v1648_mg_checked : Scalar.distance (sourceCoefficient 18 74 3 2) v1648_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1648_upper : Scalar.QComplex := ((999996023139152630380381840386 : Int)/10^30,(-2820231529381415857464652209 : Int)/10^30)
theorem v1648_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 74 5) 1) 14) v1648_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1648 : Material (18 : Basis) (74 : Basis) where
  plus := ![v1648_pa,v1648_pb,v1648_pg]
  minus := ![(Primitive.Addresses.material1648 1).one,v1648_mb,v1648_mg]
  upper := v1648_upper
  lower := (Primitive.Addresses.material1648 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1648_pa_checked.trans (by decide +kernel)
    · exact v1648_pb_checked.trans (by decide +kernel)
    · exact v1648_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 74 Primitive.Addresses.material1648
    · exact v1648_mb_checked.trans (by decide +kernel)
    · exact v1648_mg_checked.trans (by decide +kernel)
  upper_error := v1648_upper_checked
  lower_error := reuse_lower_error 18 74 Primitive.Addresses.material1648

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
