import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B188

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4513_pa : Scalar.QComplex := ((999997358767755746601474922596 : Int)/10^30,(-2298359743904123675406091978 : Int)/10^30)
theorem v4513_pa_checked : Scalar.distance (sourceCoefficient 75 89 1 0) v4513_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4513_pb : Scalar.QComplex := ((-991690553984566337973542 : Int)/10^30,(-431476376720278651717615711 : Int)/10^30)
theorem v4513_pb_checked : Scalar.distance (sourceCoefficient 75 89 1 1) v4513_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4513_pg : Scalar.QComplex := ((-93086183532715458086662 : Int)/10^30,(213946102026607359728 : Int)/10^30)
theorem v4513_pg_checked : Scalar.distance (sourceCoefficient 75 89 1 2) v4513_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4513_mb : Scalar.QComplex := ((-1364034864867829514300709 : Int)/10^30,(-431475360277620150043391726 : Int)/10^30)
theorem v4513_mb_checked : Scalar.distance (sourceCoefficient 75 89 3 1) v4513_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4513_mg : Scalar.QComplex := ((-93085964246624805881455 : Int)/10^30,(294275206307353795964 : Int)/10^30)
theorem v4513_mg_checked : Scalar.distance (sourceCoefficient 75 89 3 2) v4513_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4513_upper : Scalar.QComplex := ((999991902628745392156388984870 : Int)/10^30,(-4024261042948686781006162637 : Int)/10^30)
theorem v4513_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 89 5) 1) 14) v4513_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4513 : Material (75 : Basis) (89 : Basis) where
  plus := ![v4513_pa,v4513_pb,v4513_pg]
  minus := ![(Primitive.Addresses.material4513 1).one,v4513_mb,v4513_mg]
  upper := v4513_upper
  lower := (Primitive.Addresses.material4513 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4513_pa_checked.trans (by decide +kernel)
    · exact v4513_pb_checked.trans (by decide +kernel)
    · exact v4513_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 89 Primitive.Addresses.material4513
    · exact v4513_mb_checked.trans (by decide +kernel)
    · exact v4513_mg_checked.trans (by decide +kernel)
  upper_error := v4513_upper_checked
  lower_error := reuse_lower_error 75 89 Primitive.Addresses.material4513

def v4514_pa : Scalar.QComplex := ((999997298200673251286077602709 : Int)/10^30,(-2324562615585526838916301168 : Int)/10^30)
theorem v4514_pa_checked : Scalar.distance (sourceCoefficient 75 90 1 0) v4514_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4514_pb : Scalar.QComplex := ((-1002996501636985353337783 : Int)/10^30,(-431476349579454763871357743 : Int)/10^30)
theorem v4514_pb_checked : Scalar.distance (sourceCoefficient 75 90 1 1) v4514_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4514_pg : Scalar.QComplex := ((-93086177786064730932816 : Int)/10^30,(216385233538712290178 : Int)/10^30)
theorem v4514_pg_checked : Scalar.distance (sourceCoefficient 75 90 1 2) v4514_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4514_mb : Scalar.QComplex := ((-1375340784889218873455584 : Int)/10^30,(-431475323380282744908489936 : Int)/10^30)
theorem v4514_mb_checked : Scalar.distance (sourceCoefficient 75 90 3 1) v4514_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4514_mg : Scalar.QComplex := ((-93085956395115577927072 : Int)/10^30,(296714331952157832648 : Int)/10^30)
theorem v4514_mg_checked : Scalar.distance (sourceCoefficient 75 90 3 2) v4514_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4514_upper : Scalar.QComplex := ((999991796837973688243803174388 : Int)/10^30,(-4050463771070700796480270333 : Int)/10^30)
theorem v4514_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 90 5) 1) 14) v4514_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4514 : Material (75 : Basis) (90 : Basis) where
  plus := ![v4514_pa,v4514_pb,v4514_pg]
  minus := ![(Primitive.Addresses.material4514 1).one,v4514_mb,v4514_mg]
  upper := v4514_upper
  lower := (Primitive.Addresses.material4514 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4514_pa_checked.trans (by decide +kernel)
    · exact v4514_pb_checked.trans (by decide +kernel)
    · exact v4514_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 90 Primitive.Addresses.material4514
    · exact v4514_mb_checked.trans (by decide +kernel)
    · exact v4514_mg_checked.trans (by decide +kernel)
  upper_error := v4514_upper_checked
  lower_error := reuse_lower_error 75 90 Primitive.Addresses.material4514

def v4515_pa : Scalar.QComplex := ((999997263778695154111082857192 : Int)/10^30,(-2339323646438164131128237229 : Int)/10^30)
theorem v4515_pa_checked : Scalar.distance (sourceCoefficient 75 91 1 0) v4515_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4515_pb : Scalar.QComplex := ((-1009365553123791546934161 : Int)/10^30,(-431476334116105993065512584 : Int)/10^30)
theorem v4515_pb_checked : Scalar.distance (sourceCoefficient 75 91 1 1) v4515_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4515_pg : Scalar.QComplex := ((-93086174515933279701234 : Int)/10^30,(217759285039187399973 : Int)/10^30)
theorem v4515_pg_checked : Scalar.distance (sourceCoefficient 75 91 1 2) v4515_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4515_mb : Scalar.QComplex := ((-1381709820660362572651422 : Int)/10^30,(-431475302420735150130897141 : Int)/10^30)
theorem v4515_mb_checked : Scalar.distance (sourceCoefficient 75 91 3 1) v4515_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4515_mg : Scalar.QComplex := ((-93085951939240784387165 : Int)/10^30,(298088380119034610400 : Int)/10^30)
theorem v4515_mg_checked : Scalar.distance (sourceCoefficient 75 91 3 2) v4515_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4515_upper : Scalar.QComplex := ((999991736939846717168124201283 : Int)/10^30,(-4065224720529305127911877747 : Int)/10^30)
theorem v4515_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 91 5) 1) 14) v4515_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4515 : Material (75 : Basis) (91 : Basis) where
  plus := ![v4515_pa,v4515_pb,v4515_pg]
  minus := ![(Primitive.Addresses.material4515 1).one,v4515_mb,v4515_mg]
  upper := v4515_upper
  lower := (Primitive.Addresses.material4515 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4515_pa_checked.trans (by decide +kernel)
    · exact v4515_pb_checked.trans (by decide +kernel)
    · exact v4515_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 91 Primitive.Addresses.material4515
    · exact v4515_mb_checked.trans (by decide +kernel)
    · exact v4515_mg_checked.trans (by decide +kernel)
  upper_error := v4515_upper_checked
  lower_error := reuse_lower_error 75 91 Primitive.Addresses.material4515

def v4516_pa : Scalar.QComplex := ((999997188512429022538135317461 : Int)/10^30,(-2371279662438102632456280438 : Int)/10^30)
theorem v4516_pa_checked : Scalar.distance (sourceCoefficient 75 92 1 0) v4516_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4516_pb : Scalar.QComplex := ((-1023153852096854135002515 : Int)/10^30,(-431476300210213190796647474 : Int)/10^30)
theorem v4516_pb_checked : Scalar.distance (sourceCoefficient 75 92 1 1) v4516_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4516_pg : Scalar.QComplex := ((-93086167355391464069425 : Int)/10^30,(220733956094923453322 : Int)/10^30)
theorem v4516_pg_checked : Scalar.distance (sourceCoefficient 75 92 1 2) v4516_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4516_mb : Scalar.QComplex := ((-1395498085240152873021625 : Int)/10^30,(-431475256616173960755556048 : Int)/10^30)
theorem v4516_mb_checked : Scalar.distance (sourceCoefficient 75 92 3 1) v4516_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4516_mg : Scalar.QComplex := ((-93085942211694488063107 : Int)/10^30,(301063043887939592456 : Int)/10^30)
theorem v4516_mg_checked : Scalar.distance (sourceCoefficient 75 92 3 2) v4516_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4516_upper : Scalar.QComplex := ((999991606520508097088886942879 : Int)/10^30,(-4097180559031764373892501961 : Int)/10^30)
theorem v4516_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 92 5) 1) 14) v4516_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4516 : Material (75 : Basis) (92 : Basis) where
  plus := ![v4516_pa,v4516_pb,v4516_pg]
  minus := ![(Primitive.Addresses.material4516 1).one,v4516_mb,v4516_mg]
  upper := v4516_upper
  lower := (Primitive.Addresses.material4516 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4516_pa_checked.trans (by decide +kernel)
    · exact v4516_pb_checked.trans (by decide +kernel)
    · exact v4516_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 92 Primitive.Addresses.material4516
    · exact v4516_mb_checked.trans (by decide +kernel)
    · exact v4516_mg_checked.trans (by decide +kernel)
  upper_error := v4516_upper_checked
  lower_error := reuse_lower_error 75 92 Primitive.Addresses.material4516

def v4517_pa : Scalar.QComplex := ((999997097861023345007260924851 : Int)/10^30,(-2409205165796251910830472987 : Int)/10^30)
theorem v4517_pa_checked : Scalar.distance (sourceCoefficient 75 93 1 0) v4517_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4517_pb : Scalar.QComplex := ((-1039517849428162729462495 : Int)/10^30,(-431476259208223629863814473 : Int)/10^30)
theorem v4517_pb_checked : Scalar.distance (sourceCoefficient 75 93 1 1) v4517_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4517_pg : Scalar.QComplex := ((-93086158713324196501993 : Int)/10^30,(224264305282451872937 : Int)/10^30)
theorem v4517_pg_checked : Scalar.distance (sourceCoefficient 75 93 1 2) v4517_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4517_mb : Scalar.QComplex := ((-1411862041095527059385276 : Int)/10^30,(-431475201492806976898816337 : Int)/10^30)
theorem v4517_mb_checked : Scalar.distance (sourceCoefficient 75 93 3 1) v4517_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4517_mg : Scalar.QComplex := ((-93085930523098090520265 : Int)/10^30,(304593384303242836977 : Int)/10^30)
theorem v4517_mg_checked : Scalar.distance (sourceCoefficient 75 93 3 2) v4517_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4517_upper : Scalar.QComplex := ((999991450413259212800808603797 : Int)/10^30,(-4135105849448229074741196547 : Int)/10^30)
theorem v4517_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 93 5) 1) 14) v4517_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4517 : Material (75 : Basis) (93 : Basis) where
  plus := ![v4517_pa,v4517_pb,v4517_pg]
  minus := ![(Primitive.Addresses.material4517 1).one,v4517_mb,v4517_mg]
  upper := v4517_upper
  lower := (Primitive.Addresses.material4517 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4517_pa_checked.trans (by decide +kernel)
    · exact v4517_pb_checked.trans (by decide +kernel)
    · exact v4517_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 93 Primitive.Addresses.material4517
    · exact v4517_mb_checked.trans (by decide +kernel)
    · exact v4517_mg_checked.trans (by decide +kernel)
  upper_error := v4517_upper_checked
  lower_error := reuse_lower_error 75 93 Primitive.Addresses.material4517

def v4518_pa : Scalar.QComplex := ((999996988928654774965961645794 : Int)/10^30,(-2454003590848925803872117326 : Int)/10^30)
theorem v4518_pa_checked : Scalar.distance (sourceCoefficient 75 94 1 0) v4518_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4518_pb : Scalar.QComplex := ((-1058847356258593553721400 : Int)/10^30,(-431476209709770175196721277 : Int)/10^30)
theorem v4518_pb_checked : Scalar.distance (sourceCoefficient 75 94 1 1) v4518_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4518_pg : Scalar.QComplex := ((-93086148303893806445398 : Int)/10^30,(228434430028417566655 : Int)/10^30)
theorem v4518_pg_checked : Scalar.distance (sourceCoefficient 75 94 1 2) v4518_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4518_mb : Scalar.QComplex := ((-1431191498013763084781051 : Int)/10^30,(-431475135313878126776948531 : Int)/10^30)
theorem v4518_mb_checked : Scalar.distance (sourceCoefficient 75 94 3 1) v4518_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4518_mg : Scalar.QComplex := ((-93085916515041736048467 : Int)/10^30,(308763498513610900378 : Int)/10^30)
theorem v4518_mg_checked : Scalar.distance (sourceCoefficient 75 94 3 2) v4518_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4518_upper : Scalar.QComplex := ((999991264163035325185177221719 : Int)/10^30,(-4179904019771525359884043340 : Int)/10^30)
theorem v4518_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 94 5) 1) 14) v4518_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4518 : Material (75 : Basis) (94 : Basis) where
  plus := ![v4518_pa,v4518_pb,v4518_pg]
  minus := ![(Primitive.Addresses.material4518 1).one,v4518_mb,v4518_mg]
  upper := v4518_upper
  lower := (Primitive.Addresses.material4518 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4518_pa_checked.trans (by decide +kernel)
    · exact v4518_pb_checked.trans (by decide +kernel)
    · exact v4518_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 94 Primitive.Addresses.material4518
    · exact v4518_mb_checked.trans (by decide +kernel)
    · exact v4518_mg_checked.trans (by decide +kernel)
  upper_error := v4518_upper_checked
  lower_error := reuse_lower_error 75 94 Primitive.Addresses.material4518

def v4519_pa : Scalar.QComplex := ((999996879299450442802756858662 : Int)/10^30,(-2498277678790425105632516956 : Int)/10^30)
theorem v4519_pa_checked : Scalar.distance (sourceCoefficient 75 95 1 0) v4519_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4519_pb : Scalar.QComplex := ((-1077950622560578457084501 : Int)/10^30,(-431476159656272063000911664 : Int)/10^30)
theorem v4519_pb_checked : Scalar.distance (sourceCoefficient 75 95 1 1) v4519_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4519_pg : Scalar.QComplex := ((-93086137802158113479877 : Int)/10^30,(232555746012785600223 : Int)/10^30)
theorem v4519_pg_checked : Scalar.distance (sourceCoefficient 75 95 1 2) v4519_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4519_mb : Scalar.QComplex := ((-1450294714008814336560494 : Int)/10^30,(-431475068775140212348537470 : Int)/10^30)
theorem v4519_mb_checked : Scalar.distance (sourceCoefficient 75 95 3 1) v4519_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4519_mg : Scalar.QComplex := ((-93085902456799876030986 : Int)/10^30,(312884803900899717108 : Int)/10^30)
theorem v4519_mg_checked : Scalar.distance (sourceCoefficient 75 95 3 2) v4519_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4519_upper : Scalar.QComplex := ((999991078120934999698847575274 : Int)/10^30,(-4224177852561910278900561863 : Int)/10^30)
theorem v4519_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 95 5) 1) 14) v4519_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4519 : Material (75 : Basis) (95 : Basis) where
  plus := ![v4519_pa,v4519_pb,v4519_pg]
  minus := ![(Primitive.Addresses.material4519 1).one,v4519_mb,v4519_mg]
  upper := v4519_upper
  lower := (Primitive.Addresses.material4519 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4519_pa_checked.trans (by decide +kernel)
    · exact v4519_pb_checked.trans (by decide +kernel)
    · exact v4519_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 95 Primitive.Addresses.material4519
    · exact v4519_mb_checked.trans (by decide +kernel)
    · exact v4519_mg_checked.trans (by decide +kernel)
  upper_error := v4519_upper_checked
  lower_error := reuse_lower_error 75 95 Primitive.Addresses.material4519

def v4520_pa : Scalar.QComplex := ((999996825949752231558707428179 : Int)/10^30,(-2519541708514051812230574542 : Int)/10^30)
theorem v4520_pa_checked : Scalar.distance (sourceCoefficient 75 96 1 0) v4520_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4520_pb : Scalar.QComplex := ((-1087125569495392338092903 : Int)/10^30,(-431476135215622331183562154 : Int)/10^30)
theorem v4520_pb_checked : Scalar.distance (sourceCoefficient 75 96 1 1) v4520_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4520_pg : Scalar.QComplex := ((-93086132682693780330714 : Int)/10^30,(234535138204633533357 : Int)/10^30)
theorem v4520_pg_checked : Scalar.distance (sourceCoefficient 75 96 1 2) v4520_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4520_mb : Scalar.QComplex := ((-1459469636436196205391340 : Int)/10^30,(-431475036416933600428034736 : Int)/10^30)
theorem v4520_mb_checked : Scalar.distance (sourceCoefficient 75 96 3 1) v4520_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4520_mg : Scalar.QComplex := ((-93085895629211136042571 : Int)/10^30,(314864190937862327132 : Int)/10^30)
theorem v4520_mg_checked : Scalar.distance (sourceCoefficient 75 96 3 2) v4520_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4520_upper : Scalar.QComplex := ((999990988071530001291247991576 : Int)/10^30,(-4245441758538523294759943075 : Int)/10^30)
theorem v4520_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 96 5) 1) 14) v4520_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4520 : Material (75 : Basis) (96 : Basis) where
  plus := ![v4520_pa,v4520_pb,v4520_pg]
  minus := ![(Primitive.Addresses.material4520 1).one,v4520_mb,v4520_mg]
  upper := v4520_upper
  lower := (Primitive.Addresses.material4520 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4520_pa_checked.trans (by decide +kernel)
    · exact v4520_pb_checked.trans (by decide +kernel)
    · exact v4520_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 96 Primitive.Addresses.material4520
    · exact v4520_mb_checked.trans (by decide +kernel)
    · exact v4520_mg_checked.trans (by decide +kernel)
  upper_error := v4520_upper_checked
  lower_error := reuse_lower_error 75 96 Primitive.Addresses.material4520

def v4521_pa : Scalar.QComplex := ((999996638938132334258861279751 : Int)/10^30,(-2592703692787628210023033628 : Int)/10^30)
theorem v4521_pa_checked : Scalar.distance (sourceCoefficient 75 97 1 0) v4521_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4521_pb : Scalar.QComplex := ((-1118693305943780471817601 : Int)/10^30,(-431476049136788726030416169 : Int)/10^30)
theorem v4521_pb_checked : Scalar.distance (sourceCoefficient 75 97 1 1) v4521_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4521_pg : Scalar.QComplex := ((-93086114693300892080295 : Int)/10^30,(241345524489813214957 : Int)/10^30)
theorem v4521_pg_checked : Scalar.distance (sourceCoefficient 75 97 1 2) v4521_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4521_mb : Scalar.QComplex := ((-1491037286848316788056883 : Int)/10^30,(-431474923096597249471172513 : Int)/10^30)
theorem v4521_mb_checked : Scalar.distance (sourceCoefficient 75 97 3 1) v4521_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4521_mg : Scalar.QComplex := ((-93085871762768310367206 : Int)/10^30,(321674559163188094350 : Int)/10^30)
theorem v4521_mg_checked : Scalar.distance (sourceCoefficient 75 97 3 2) v4521_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4521_upper : Scalar.QComplex := ((999990674789240983004759678011 : Int)/10^30,(-4318603311080827946333338135 : Int)/10^30)
theorem v4521_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 75 97 5) 1) 14) v4521_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4521 : Material (75 : Basis) (97 : Basis) where
  plus := ![v4521_pa,v4521_pb,v4521_pg]
  minus := ![(Primitive.Addresses.material4521 1).one,v4521_mb,v4521_mg]
  upper := v4521_upper
  lower := (Primitive.Addresses.material4521 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4521_pa_checked.trans (by decide +kernel)
    · exact v4521_pb_checked.trans (by decide +kernel)
    · exact v4521_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 75 97 Primitive.Addresses.material4521
    · exact v4521_mb_checked.trans (by decide +kernel)
    · exact v4521_mg_checked.trans (by decide +kernel)
  upper_error := v4521_upper_checked
  lower_error := reuse_lower_error 75 97 Primitive.Addresses.material4521

def v4522_pa : Scalar.QComplex := ((999997853684422448953616365487 : Int)/10^30,(-2071865475466863975270706710 : Int)/10^30)
theorem v4522_pa_checked : Scalar.distance (sourceCoefficient 76 77 1 0) v4522_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4522_pb : Scalar.QComplex := ((-893963379200047203105503 : Int)/10^30,(-431476594913132469439740869 : Int)/10^30)
theorem v4522_pb_checked : Scalar.distance (sourceCoefficient 76 77 1 1) v4522_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4522_pg : Scalar.QComplex := ((-93086230104057265665532 : Int)/10^30,(192862560337878093151 : Int)/10^30)
theorem v4522_pg_checked : Scalar.distance (sourceCoefficient 76 77 1 2) v4522_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4522_mb : Scalar.QComplex := ((-1266307914762209707594254 : Int)/10^30,(-431475662804543095072046402 : Int)/10^30)
theorem v4522_mb_checked : Scalar.distance (sourceCoefficient 76 77 3 1) v4522_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4522_mg : Scalar.QComplex := ((-93086029012096182726652 : Int)/10^30,(273191712657961150125 : Int)/10^30)
theorem v4522_mg_checked : Scalar.distance (sourceCoefficient 76 77 3 2) v4522_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4522_upper : Scalar.QComplex := ((999992788453234897455563778365 : Int)/10^30,(-3797767966029302271421233039 : Int)/10^30)
theorem v4522_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 77 5) 1) 14) v4522_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4522 : Material (76 : Basis) (77 : Basis) where
  plus := ![v4522_pa,v4522_pb,v4522_pg]
  minus := ![(Primitive.Addresses.material4522 1).one,v4522_mb,v4522_mg]
  upper := v4522_upper
  lower := (Primitive.Addresses.material4522 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4522_pa_checked.trans (by decide +kernel)
    · exact v4522_pb_checked.trans (by decide +kernel)
    · exact v4522_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 77 Primitive.Addresses.material4522
    · exact v4522_mb_checked.trans (by decide +kernel)
    · exact v4522_mg_checked.trans (by decide +kernel)
  upper_error := v4522_upper_checked
  lower_error := reuse_lower_error 76 77 Primitive.Addresses.material4522

def v4523_pa : Scalar.QComplex := ((999997817692363164934647506275 : Int)/10^30,(-2089165027278484028840295430 : Int)/10^30)
theorem v4523_pa_checked : Scalar.distance (sourceCoefficient 76 78 1 0) v4523_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4523_pb : Scalar.QComplex := ((-901427746870215920785561 : Int)/10^30,(-431476579354686150754836706 : Int)/10^30)
theorem v4523_pb_checked : Scalar.distance (sourceCoefficient 76 78 1 1) v4523_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4523_pg : Scalar.QComplex := ((-93086226750591073834969 : Int)/10^30,(194472913848374799366 : Int)/10^30)
theorem v4523_pg_checked : Scalar.distance (sourceCoefficient 76 78 1 2) v4523_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4523_mb : Scalar.QComplex := ((-1273772266226814756600324 : Int)/10^30,(-431475640804689452792337633 : Int)/10^30)
theorem v4523_mb_checked : Scalar.distance (sourceCoefficient 76 78 3 1) v4523_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4523_mg : Scalar.QComplex := ((-93086024268968687615917 : Int)/10^30,(274802062674959358551 : Int)/10^30)
theorem v4523_mg_checked : Scalar.distance (sourceCoefficient 76 78 3 2) v4523_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4523_upper : Scalar.QComplex := ((999992722603772195605607810866 : Int)/10^30,(-3815067429956242899584529025 : Int)/10^30)
theorem v4523_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 78 5) 1) 14) v4523_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4523 : Material (76 : Basis) (78 : Basis) where
  plus := ![v4523_pa,v4523_pb,v4523_pg]
  minus := ![(Primitive.Addresses.material4523 1).one,v4523_mb,v4523_mg]
  upper := v4523_upper
  lower := (Primitive.Addresses.material4523 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4523_pa_checked.trans (by decide +kernel)
    · exact v4523_pb_checked.trans (by decide +kernel)
    · exact v4523_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 78 Primitive.Addresses.material4523
    · exact v4523_mb_checked.trans (by decide +kernel)
    · exact v4523_mg_checked.trans (by decide +kernel)
  upper_error := v4523_upper_checked
  lower_error := reuse_lower_error 76 78 Primitive.Addresses.material4523

def v4524_pa : Scalar.QComplex := ((999997806025368556752488356137 : Int)/10^30,(-2094742096144967342732237906 : Int)/10^30)
theorem v4524_pa_checked : Scalar.distance (sourceCoefficient 76 79 1 0) v4524_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4524_pb : Scalar.QComplex := ((-903834126680424406672854 : Int)/10^30,(-431476574302218741839535601 : Int)/10^30)
theorem v4524_pb_checked : Scalar.distance (sourceCoefficient 76 79 1 1) v4524_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4524_pg : Scalar.QComplex := ((-93086225662565082501760 : Int)/10^30,(194992063274265188950 : Int)/10^30)
theorem v4524_pg_checked : Scalar.distance (sourceCoefficient 76 79 1 2) v4524_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4524_mb : Scalar.QComplex := ((-1276178640780966242947663 : Int)/10^30,(-431475633675626528255060906 : Int)/10^30)
theorem v4524_mb_checked : Scalar.distance (sourceCoefficient 76 79 3 1) v4524_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4524_mg : Scalar.QComplex := ((-93086022732940528483278 : Int)/10^30,(275321210968629262927 : Int)/10^30)
theorem v4524_mg_checked : Scalar.distance (sourceCoefficient 76 79 3 2) v4524_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4524_upper : Scalar.QComplex := ((999992701311280048226536862267 : Int)/10^30,(-3820644470380162993139414459 : Int)/10^30)
theorem v4524_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 79 5) 1) 14) v4524_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4524 : Material (76 : Basis) (79 : Basis) where
  plus := ![v4524_pa,v4524_pb,v4524_pg]
  minus := ![(Primitive.Addresses.material4524 1).one,v4524_mb,v4524_mg]
  upper := v4524_upper
  lower := (Primitive.Addresses.material4524 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4524_pa_checked.trans (by decide +kernel)
    · exact v4524_pb_checked.trans (by decide +kernel)
    · exact v4524_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 79 Primitive.Addresses.material4524
    · exact v4524_mb_checked.trans (by decide +kernel)
    · exact v4524_mg_checked.trans (by decide +kernel)
  upper_error := v4524_upper_checked
  lower_error := reuse_lower_error 76 79 Primitive.Addresses.material4524

def v4525_pa : Scalar.QComplex := ((999997787738127247537844952483 : Int)/10^30,(-2103454028830278638058881340 : Int)/10^30)
theorem v4525_pa_checked : Scalar.distance (sourceCoefficient 76 80 1 0) v4525_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4525_pb : Scalar.QComplex := ((-907593129718831640769204 : Int)/10^30,(-431476566373956909618331414 : Int)/10^30)
theorem v4525_pb_checked : Scalar.distance (sourceCoefficient 76 80 1 1) v4525_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4525_pg : Scalar.QComplex := ((-93086223956201349362611 : Int)/10^30,(195803025976838265263 : Int)/10^30)
theorem v4525_pg_checked : Scalar.distance (sourceCoefficient 76 80 1 2) v4525_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4525_mb : Scalar.QComplex := ((-1279937635577991965370056 : Int)/10^30,(-431475622503517325154800987 : Int)/10^30)
theorem v4525_mb_checked : Scalar.distance (sourceCoefficient 76 80 3 1) v4525_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4525_mg : Scalar.QComplex := ((-93086020326753142785041 : Int)/10^30,(276132171896728812317 : Int)/10^30)
theorem v4525_mg_checked : Scalar.distance (sourceCoefficient 76 80 3 2) v4525_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4525_upper : Scalar.QComplex := ((999992667988060501221768896332 : Int)/10^30,(-3829356358527954435063965356 : Int)/10^30)
theorem v4525_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 80 5) 1) 14) v4525_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4525 : Material (76 : Basis) (80 : Basis) where
  plus := ![v4525_pa,v4525_pb,v4525_pg]
  minus := ![(Primitive.Addresses.material4525 1).one,v4525_mb,v4525_mg]
  upper := v4525_upper
  lower := (Primitive.Addresses.material4525 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4525_pa_checked.trans (by decide +kernel)
    · exact v4525_pb_checked.trans (by decide +kernel)
    · exact v4525_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 80 Primitive.Addresses.material4525
    · exact v4525_mb_checked.trans (by decide +kernel)
    · exact v4525_mg_checked.trans (by decide +kernel)
  upper_error := v4525_upper_checked
  lower_error := reuse_lower_error 76 80 Primitive.Addresses.material4525

def v4526_pa : Scalar.QComplex := ((999997732215966067780179546069 : Int)/10^30,(-2129686109505345645225539876 : Int)/10^30)
theorem v4526_pa_checked : Scalar.distance (sourceCoefficient 76 81 1 0) v4526_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4526_pb : Scalar.QComplex := ((-918911682474632966264418 : Int)/10^30,(-431476542237871198351927485 : Int)/10^30)
theorem v4526_pb_checked : Scalar.distance (sourceCoefficient 76 81 1 1) v4526_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4526_pg : Scalar.QComplex := ((-93086218768476738830772 : Int)/10^30,(198244876674166843600 : Int)/10^30)
theorem v4526_pg_checked : Scalar.distance (sourceCoefficient 76 81 1 2) v4526_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4526_mb : Scalar.QComplex := ((-1291256163291023896589552 : Int)/10^30,(-431475588600039341292254985 : Int)/10^30)
theorem v4526_mb_checked : Scalar.distance (sourceCoefficient 76 81 3 1) v4526_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4526_mg : Scalar.QComplex := ((-93086013031823288958477 : Int)/10^30,(278574017208072085502 : Int)/10^30)
theorem v4526_mg_checked : Scalar.distance (sourceCoefficient 76 81 3 2) v4526_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4526_upper : Scalar.QComplex := ((999992567191790525804645344128 : Int)/10^30,(-3855588304307205448227679626 : Int)/10^30)
theorem v4526_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 81 5) 1) 14) v4526_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4526 : Material (76 : Basis) (81 : Basis) where
  plus := ![v4526_pa,v4526_pb,v4526_pg]
  minus := ![(Primitive.Addresses.material4526 1).one,v4526_mb,v4526_mg]
  upper := v4526_upper
  lower := (Primitive.Addresses.material4526 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4526_pa_checked.trans (by decide +kernel)
    · exact v4526_pb_checked.trans (by decide +kernel)
    · exact v4526_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 81 Primitive.Addresses.material4526
    · exact v4526_mb_checked.trans (by decide +kernel)
    · exact v4526_mg_checked.trans (by decide +kernel)
  upper_error := v4526_upper_checked
  lower_error := reuse_lower_error 76 81 Primitive.Addresses.material4526

def v4527_pa : Scalar.QComplex := ((999997710996930493595923719161 : Int)/10^30,(-2139626345761744433755720387 : Int)/10^30)
theorem v4527_pa_checked : Scalar.distance (sourceCoefficient 76 82 1 0) v4527_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4527_pb : Scalar.QComplex := ((-923200670769194068579573 : Int)/10^30,(-431476532988450401709279738 : Int)/10^30)
theorem v4527_pb_checked : Scalar.distance (sourceCoefficient 76 82 1 1) v4527_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4527_pg : Scalar.QComplex := ((-93086216783145269750363 : Int)/10^30,(199170177757654920022 : Int)/10^30)
theorem v4527_pg_checked : Scalar.distance (sourceCoefficient 76 82 1 2) v4527_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4527_mb : Scalar.QComplex := ((-1295545142006765071337095 : Int)/10^30,(-431475575649418259287479752 : Int)/10^30)
theorem v4527_mb_checked : Scalar.distance (sourceCoefficient 76 82 3 1) v4527_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4527_mg : Scalar.QComplex := ((-93086010247999398071286 : Int)/10^30,(279499316233776638387 : Int)/10^30)
theorem v4527_mg_checked : Scalar.distance (sourceCoefficient 76 82 3 2) v4527_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4527_upper : Scalar.QComplex := ((999992528816840547525935797306 : Int)/10^30,(-3865528489136659569854513431 : Int)/10^30)
theorem v4527_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 82 5) 1) 14) v4527_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4527 : Material (76 : Basis) (82 : Basis) where
  plus := ![v4527_pa,v4527_pb,v4527_pg]
  minus := ![(Primitive.Addresses.material4527 1).one,v4527_mb,v4527_mg]
  upper := v4527_upper
  lower := (Primitive.Addresses.material4527 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4527_pa_checked.trans (by decide +kernel)
    · exact v4527_pb_checked.trans (by decide +kernel)
    · exact v4527_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 82 Primitive.Addresses.material4527
    · exact v4527_mb_checked.trans (by decide +kernel)
    · exact v4527_mg_checked.trans (by decide +kernel)
  upper_error := v4527_upper_checked
  lower_error := reuse_lower_error 76 82 Primitive.Addresses.material4527

def v4528_pa : Scalar.QComplex := ((999997681873098390296285065989 : Int)/10^30,(-2153194935324499471794864271 : Int)/10^30)
theorem v4528_pa_checked : Scalar.distance (sourceCoefficient 76 83 1 0) v4528_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4528_pb : Scalar.QComplex := ((-929055211827006584936628 : Int)/10^30,(-431476520271079434399208272 : Int)/10^30)
theorem v4528_pb_checked : Scalar.distance (sourceCoefficient 76 83 1 1) v4528_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4528_pg : Scalar.QComplex := ((-93086214055813503687409 : Int)/10^30,(200433229283170648561 : Int)/10^30)
theorem v4528_pg_checked : Scalar.distance (sourceCoefficient 76 83 1 2) v4528_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4528_mb : Scalar.QComplex := ((-1301399669910146010463779 : Int)/10^30,(-431475557879846773084659276 : Int)/10^30)
theorem v4528_mb_checked : Scalar.distance (sourceCoefficient 76 83 3 1) v4528_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4528_mg : Scalar.QComplex := ((-93086006430712066727532 : Int)/10^30,(280762364935436080020 : Int)/10^30)
theorem v4528_mg_checked : Scalar.distance (sourceCoefficient 76 83 3 2) v4528_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4528_upper : Scalar.QComplex := ((999992476274897168267507269916 : Int)/10^30,(-3879097008225502215778260826 : Int)/10^30)
theorem v4528_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 83 5) 1) 14) v4528_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4528 : Material (76 : Basis) (83 : Basis) where
  plus := ![v4528_pa,v4528_pb,v4528_pg]
  minus := ![(Primitive.Addresses.material4528 1).one,v4528_mb,v4528_mg]
  upper := v4528_upper
  lower := (Primitive.Addresses.material4528 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4528_pa_checked.trans (by decide +kernel)
    · exact v4528_pb_checked.trans (by decide +kernel)
    · exact v4528_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 83 Primitive.Addresses.material4528
    · exact v4528_mb_checked.trans (by decide +kernel)
    · exact v4528_mg_checked.trans (by decide +kernel)
  upper_error := v4528_upper_checked
  lower_error := reuse_lower_error 76 83 Primitive.Addresses.material4528

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
