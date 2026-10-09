import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B141
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B142

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3393_pa : Scalar.QComplex := ((999999188690852691378727415768 : Int)/10^30,(-1273820095772833236285639083 : Int)/10^30)
theorem v3393_pa_checked : Scalar.distance (sourceCoefficient 45 64 1 0) v3393_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3393_pb : Scalar.QComplex := ((-549624730788309076745731 : Int)/10^30,(-431477165964537171629753130 : Int)/10^30)
theorem v3393_pb_checked : Scalar.distance (sourceCoefficient 45 64 1 1) v3393_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3393_pg : Scalar.QComplex := ((-93086353838512493652290 : Int)/10^30,(118575364362995580565 : Int)/10^30)
theorem v3393_pg_checked : Scalar.distance (sourceCoefficient 45 64 1 2) v3393_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3393_mb : Scalar.QComplex := ((-921969887355130496047022 : Int)/10^30,(-431476531004480311031531287 : Int)/10^30)
theorem v3393_mb_checked : Scalar.distance (sourceCoefficient 45 64 3 1) v3393_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3393_mg : Scalar.QComplex := ((-93086216853009693938545 : Int)/10^30,(198904651120858860326 : Int)/10^30)
theorem v3393_mg_checked : Scalar.distance (sourceCoefficient 45 64 3 2) v3393_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3393_upper : Scalar.QComplex := ((999995500811604045217922524902 : Int)/10^30,(-2999726079030107352309413820 : Int)/10^30)
theorem v3393_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 64 5) 1) 14) v3393_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3393 : Material (45 : Basis) (64 : Basis) where
  plus := ![v3393_pa,v3393_pb,v3393_pg]
  minus := ![(Primitive.Addresses.material3393 1).one,v3393_mb,v3393_mg]
  upper := v3393_upper
  lower := (Primitive.Addresses.material3393 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3393_pa_checked.trans (by decide +kernel)
    · exact v3393_pb_checked.trans (by decide +kernel)
    · exact v3393_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 64 Primitive.Addresses.material3393
    · exact v3393_mb_checked.trans (by decide +kernel)
    · exact v3393_mg_checked.trans (by decide +kernel)
  upper_error := v3393_upper_checked
  lower_error := reuse_lower_error 45 64 Primitive.Addresses.material3393

def v3394_pa : Scalar.QComplex := ((999999142229052489380176973128 : Int)/10^30,(-1309786684636181989304186961 : Int)/10^30)
theorem v3394_pa_checked : Scalar.distance (sourceCoefficient 45 65 1 0) v3394_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3394_pb : Scalar.QComplex := ((-565143503307161879288537 : Int)/10^30,(-431477144463766421929004143 : Int)/10^30)
theorem v3394_pb_checked : Scalar.distance (sourceCoefficient 45 65 1 1) v3394_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3394_pg : Scalar.QComplex := ((-93086349356756017384582 : Int)/10^30,(121923365491191596981 : Int)/10^30)
theorem v3394_pg_checked : Scalar.distance (sourceCoefficient 45 65 1 2) v3394_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3394_mb : Scalar.QComplex := ((-937488635541438248655159 : Int)/10^30,(-431476496111715822848790341 : Int)/10^30)
theorem v3394_mb_checked : Scalar.distance (sourceCoefficient 45 65 3 1) v3394_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3394_mg : Scalar.QComplex := ((-93086209482080701173725 : Int)/10^30,(202252647134887057304 : Int)/10^30)
theorem v3394_mg_checked : Scalar.distance (sourceCoefficient 45 65 3 2) v3394_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3394_upper : Scalar.QComplex := ((999995392274803527926631253589 : Int)/10^30,(-3035692534136594758622388891 : Int)/10^30)
theorem v3394_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 65 5) 1) 14) v3394_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3394 : Material (45 : Basis) (65 : Basis) where
  plus := ![v3394_pa,v3394_pb,v3394_pg]
  minus := ![(Primitive.Addresses.material3394 1).one,v3394_mb,v3394_mg]
  upper := v3394_upper
  lower := (Primitive.Addresses.material3394 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3394_pa_checked.trans (by decide +kernel)
    · exact v3394_pb_checked.trans (by decide +kernel)
    · exact v3394_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 65 Primitive.Addresses.material3394
    · exact v3394_mb_checked.trans (by decide +kernel)
    · exact v3394_mg_checked.trans (by decide +kernel)
  upper_error := v3394_upper_checked
  lower_error := reuse_lower_error 45 65 Primitive.Addresses.material3394

def v3395_pa : Scalar.QComplex := ((999999119038430932260121681121 : Int)/10^30,(-1327374235866507084414179109 : Int)/10^30)
theorem v3395_pa_checked : Scalar.distance (sourceCoefficient 45 66 1 0) v3395_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3395_pb : Scalar.QComplex := ((-572732135166060387782825 : Int)/10^30,(-431477133679020026539682527 : Int)/10^30)
theorem v3395_pb_checked : Scalar.distance (sourceCoefficient 45 66 1 1) v3395_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3395_pg : Scalar.QComplex := ((-93086347114045970007261 : Int)/10^30,(123560527722187583406 : Int)/10^30)
theorem v3395_pg_checked : Scalar.distance (sourceCoefficient 45 66 1 2) v3395_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3395_mb : Scalar.QComplex := ((-945077255267991886198075 : Int)/10^30,(-431476478778325928175507268 : Int)/10^30)
theorem v3395_mb_checked : Scalar.distance (sourceCoefficient 45 66 3 1) v3395_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3395_mg : Scalar.QComplex := ((-93086205826574218560025 : Int)/10^30,(203889806820934960143 : Int)/10^30)
theorem v3395_mg_checked : Scalar.distance (sourceCoefficient 45 66 3 2) v3395_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3395_upper : Scalar.QComplex := ((999995338729698617156126639314 : Int)/10^30,(-3053280019147419304221943423 : Int)/10^30)
theorem v3395_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 66 5) 1) 14) v3395_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3395 : Material (45 : Basis) (66 : Basis) where
  plus := ![v3395_pa,v3395_pb,v3395_pg]
  minus := ![(Primitive.Addresses.material3395 1).one,v3395_mb,v3395_mg]
  upper := v3395_upper
  lower := (Primitive.Addresses.material3395 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3395_pa_checked.trans (by decide +kernel)
    · exact v3395_pb_checked.trans (by decide +kernel)
    · exact v3395_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 66 Primitive.Addresses.material3395
    · exact v3395_mb_checked.trans (by decide +kernel)
    · exact v3395_mg_checked.trans (by decide +kernel)
  upper_error := v3395_upper_checked
  lower_error := reuse_lower_error 45 66 Primitive.Addresses.material3395

def v3396_pa : Scalar.QComplex := ((999999079422489042195354357921 : Int)/10^30,(-1356891364278163430753418080 : Int)/10^30)
theorem v3396_pa_checked : Scalar.distance (sourceCoefficient 45 67 1 0) v3396_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3396_pb : Scalar.QComplex := ((-585468110438904920710555 : Int)/10^30,(-431477115179065958772351373 : Int)/10^30)
theorem v3396_pb_checked : Scalar.distance (sourceCoefficient 45 67 1 1) v3396_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3396_pg : Scalar.QComplex := ((-93086343274613999260045 : Int)/10^30,(126308171598018655966 : Int)/10^30)
theorem v3396_pg_checked : Scalar.distance (sourceCoefficient 45 67 1 2) v3396_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3396_mb : Scalar.QComplex := ((-957813209834023608739238 : Int)/10^30,(-431476449287805695354728249 : Int)/10^30)
theorem v3396_mb_checked : Scalar.distance (sourceCoefficient 45 67 3 1) v3396_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3396_mg : Scalar.QComplex := ((-93086199616050761852965 : Int)/10^30,(206637446360435775045 : Int)/10^30)
theorem v3396_mg_checked : Scalar.distance (sourceCoefficient 45 67 3 2) v3396_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3396_upper : Scalar.QComplex := ((999995248169929864836226285358 : Int)/10^30,(-3082797035223258434790853869 : Int)/10^30)
theorem v3396_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 67 5) 1) 14) v3396_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3396 : Material (45 : Basis) (67 : Basis) where
  plus := ![v3396_pa,v3396_pb,v3396_pg]
  minus := ![(Primitive.Addresses.material3396 1).one,v3396_mb,v3396_mg]
  upper := v3396_upper
  lower := (Primitive.Addresses.material3396 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3396_pa_checked.trans (by decide +kernel)
    · exact v3396_pb_checked.trans (by decide +kernel)
    · exact v3396_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 67 Primitive.Addresses.material3396
    · exact v3396_mb_checked.trans (by decide +kernel)
    · exact v3396_mg_checked.trans (by decide +kernel)
  upper_error := v3396_upper_checked
  lower_error := reuse_lower_error 45 67 Primitive.Addresses.material3396

def v3397_pa : Scalar.QComplex := ((999999011512193824207411121640 : Int)/10^30,(-1406049300431333460120984092 : Int)/10^30)
theorem v3397_pa_checked : Scalar.distance (sourceCoefficient 45 68 1 0) v3397_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3397_pb : Scalar.QComplex := ((-606678650759651187905781 : Int)/10^30,(-431477083256676804664190908 : Int)/10^30)
theorem v3397_pb_checked : Scalar.distance (sourceCoefficient 45 68 1 1) v3397_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3397_pg : Scalar.QComplex := ((-93086336670402038617751 : Int)/10^30,(130884107932479082255 : Int)/10^30)
theorem v3397_pg_checked : Scalar.distance (sourceCoefficient 45 68 1 2) v3397_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3397_mb : Scalar.QComplex := ((-979023714709532235981215 : Int)/10^30,(-431476399061687417881062419 : Int)/10^30)
theorem v3397_mb_checked : Scalar.distance (sourceCoefficient 45 68 3 1) v3397_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3397_mg : Scalar.QComplex := ((-93086189063014296143254 : Int)/10^30,(211213375291928494023 : Int)/10^30)
theorem v3397_mg_checked : Scalar.distance (sourceCoefficient 45 68 3 2) v3397_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3397_upper : Scalar.QComplex := ((999995095417597564015777942482 : Int)/10^30,(-3131954780954448288438151378 : Int)/10^30)
theorem v3397_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 68 5) 1) 14) v3397_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3397 : Material (45 : Basis) (68 : Basis) where
  plus := ![v3397_pa,v3397_pb,v3397_pg]
  minus := ![(Primitive.Addresses.material3397 1).one,v3397_mb,v3397_mg]
  upper := v3397_upper
  lower := (Primitive.Addresses.material3397 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3397_pa_checked.trans (by decide +kernel)
    · exact v3397_pb_checked.trans (by decide +kernel)
    · exact v3397_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 68 Primitive.Addresses.material3397
    · exact v3397_mb_checked.trans (by decide +kernel)
    · exact v3397_mg_checked.trans (by decide +kernel)
  upper_error := v3397_upper_checked
  lower_error := reuse_lower_error 45 68 Primitive.Addresses.material3397

def v3398_pa : Scalar.QComplex := ((999998980857727219754360796651 : Int)/10^30,(-1427684666482595207228060289 : Int)/10^30)
theorem v3398_pa_checked : Scalar.distance (sourceCoefficient 45 69 1 0) v3398_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3398_pb : Scalar.QComplex := ((-616013822822417954942149 : Int)/10^30,(-431477068766431462282071223 : Int)/10^30)
theorem v3398_pb_checked : Scalar.distance (sourceCoefficient 45 69 1 1) v3398_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3398_pg : Scalar.QComplex := ((-93086333680590753329434 : Int)/10^30,(132898066696899520421 : Int)/10^30)
theorem v3398_pg_checked : Scalar.distance (sourceCoefficient 45 69 1 2) v3398_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3398_mb : Scalar.QComplex := ((-988358870791958691558071 : Int)/10^30,(-431476376515614421254021131 : Int)/10^30)
theorem v3398_mb_checked : Scalar.distance (sourceCoefficient 45 69 3 1) v3398_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3398_mg : Scalar.QComplex := ((-93086184335248415739090 : Int)/10^30,(213227330726387558631 : Int)/10^30)
theorem v3398_mg_checked : Scalar.distance (sourceCoefficient 45 69 3 2) v3398_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3398_upper : Scalar.QComplex := ((999995027422497556388080178709 : Int)/10^30,(-3153590061875545363016460413 : Int)/10^30)
theorem v3398_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 69 5) 1) 14) v3398_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3398 : Material (45 : Basis) (69 : Basis) where
  plus := ![v3398_pa,v3398_pb,v3398_pg]
  minus := ![(Primitive.Addresses.material3398 1).one,v3398_mb,v3398_mg]
  upper := v3398_upper
  lower := (Primitive.Addresses.material3398 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3398_pa_checked.trans (by decide +kernel)
    · exact v3398_pb_checked.trans (by decide +kernel)
    · exact v3398_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 69 Primitive.Addresses.material3398
    · exact v3398_mb_checked.trans (by decide +kernel)
    · exact v3398_mg_checked.trans (by decide +kernel)
  upper_error := v3398_upper_checked
  lower_error := reuse_lower_error 45 69 Primitive.Addresses.material3398

def v3399_pa : Scalar.QComplex := ((999998960437693026247424458115 : Int)/10^30,(-1441916617997627167402956385 : Int)/10^30)
theorem v3399_pa_checked : Scalar.distance (sourceCoefficient 45 70 1 0) v3399_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3399_pb : Scalar.QComplex := ((-622154588551863895822830 : Int)/10^30,(-431477059087773374543384667 : Int)/10^30)
theorem v3399_pb_checked : Scalar.distance (sourceCoefficient 45 70 1 1) v3399_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3399_pg : Scalar.QComplex := ((-93086331686145814745724 : Int)/10^30,(134222868099727142757 : Int)/10^30)
theorem v3399_pg_checked : Scalar.distance (sourceCoefficient 45 70 1 2) v3399_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3399_mb : Scalar.QComplex := ((-994499625882670885367981 : Int)/10^30,(-431476361537755682631930057 : Int)/10^30)
theorem v3399_mb_checked : Scalar.distance (sourceCoefficient 45 70 3 1) v3399_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3399_mg : Scalar.QComplex := ((-93086181197560275978390 : Int)/10^30,(214552129914814916746 : Int)/10^30)
theorem v3399_mg_checked : Scalar.distance (sourceCoefficient 45 70 3 2) v3399_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3399_upper : Scalar.QComplex := ((999994982439436573734031986423 : Int)/10^30,(-3167821956950630817052122289 : Int)/10^30)
theorem v3399_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 70 5) 1) 14) v3399_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3399 : Material (45 : Basis) (70 : Basis) where
  plus := ![v3399_pa,v3399_pb,v3399_pg]
  minus := ![(Primitive.Addresses.material3399 1).one,v3399_mb,v3399_mg]
  upper := v3399_upper
  lower := (Primitive.Addresses.material3399 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3399_pa_checked.trans (by decide +kernel)
    · exact v3399_pb_checked.trans (by decide +kernel)
    · exact v3399_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 70 Primitive.Addresses.material3399
    · exact v3399_mb_checked.trans (by decide +kernel)
    · exact v3399_mg_checked.trans (by decide +kernel)
  upper_error := v3399_upper_checked
  lower_error := reuse_lower_error 45 70 Primitive.Addresses.material3399

def v3400_pa : Scalar.QComplex := ((999998925114407049559041822718 : Int)/10^30,(-1466209408823256727887454186 : Int)/10^30)
theorem v3400_pa_checked : Scalar.distance (sourceCoefficient 45 71 1 0) v3400_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3400_pb : Scalar.QComplex := ((-632636379120111662352964 : Int)/10^30,(-431477042297880134602890668 : Int)/10^30)
theorem v3400_pb_checked : Scalar.distance (sourceCoefficient 45 71 1 1) v3400_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3400_pg : Scalar.QComplex := ((-93086328230971060752066 : Int)/10^30,(136484196989956722155 : Int)/10^30)
theorem v3400_pg_checked : Scalar.distance (sourceCoefficient 45 71 1 2) v3400_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3400_mb : Scalar.QComplex := ((-1004981398059147304497208 : Int)/10^30,(-431476335702555516260877114 : Int)/10^30)
theorem v3400_mb_checked : Scalar.distance (sourceCoefficient 45 71 3 1) v3400_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3400_mg : Scalar.QComplex := ((-93086175790961822708572 : Int)/10^30,(216813454981388205074 : Int)/10^30)
theorem v3400_mg_checked : Scalar.distance (sourceCoefficient 45 71 3 2) v3400_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3400_upper : Scalar.QComplex := ((999994905189050066662492357437 : Int)/10^30,(-3192114650630214982135908951 : Int)/10^30)
theorem v3400_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 71 5) 1) 14) v3400_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3400 : Material (45 : Basis) (71 : Basis) where
  plus := ![v3400_pa,v3400_pb,v3400_pg]
  minus := ![(Primitive.Addresses.material3400 1).one,v3400_mb,v3400_mg]
  upper := v3400_upper
  lower := (Primitive.Addresses.material3400 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3400_pa_checked.trans (by decide +kernel)
    · exact v3400_pb_checked.trans (by decide +kernel)
    · exact v3400_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 71 Primitive.Addresses.material3400
    · exact v3400_mb_checked.trans (by decide +kernel)
    · exact v3400_mg_checked.trans (by decide +kernel)
  upper_error := v3400_upper_checked
  lower_error := reuse_lower_error 45 71 Primitive.Addresses.material3400

def v3401_pa : Scalar.QComplex := ((999998886113782863022862752125 : Int)/10^30,(-1492572006146252746599275228 : Int)/10^30)
theorem v3401_pa_checked : Scalar.distance (sourceCoefficient 45 72 1 0) v3401_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3401_pb : Scalar.QComplex := ((-644011244215190771969290 : Int)/10^30,(-431477023693312830110028994 : Int)/10^30)
theorem v3401_pb_checked : Scalar.distance (sourceCoefficient 45 72 1 1) v3401_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3401_pg : Scalar.QComplex := ((-93086324408893388129176 : Int)/10^30,(138938196729105269592 : Int)/10^30)
theorem v3401_pg_checked : Scalar.distance (sourceCoefficient 45 72 1 2) v3401_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3401_mb : Scalar.QComplex := ((-1016356242863940617028333 : Int)/10^30,(-431476307281998866951652346 : Int)/10^30)
theorem v3401_mb_checked : Scalar.distance (sourceCoefficient 45 72 3 1) v3401_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3401_mg : Scalar.QComplex := ((-93086169851194322380087 : Int)/10^30,(219267450508519604812 : Int)/10^30)
theorem v3401_mg_checked : Scalar.distance (sourceCoefficient 45 72 3 2) v3401_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3401_upper : Scalar.QComplex := ((999994820689032583630594040900 : Int)/10^30,(-3218477141377679819489388595 : Int)/10^30)
theorem v3401_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 72 5) 1) 14) v3401_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3401 : Material (45 : Basis) (72 : Basis) where
  plus := ![v3401_pa,v3401_pb,v3401_pg]
  minus := ![(Primitive.Addresses.material3401 1).one,v3401_mb,v3401_mg]
  upper := v3401_upper
  lower := (Primitive.Addresses.material3401 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3401_pa_checked.trans (by decide +kernel)
    · exact v3401_pb_checked.trans (by decide +kernel)
    · exact v3401_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 72 Primitive.Addresses.material3401
    · exact v3401_mb_checked.trans (by decide +kernel)
    · exact v3401_mg_checked.trans (by decide +kernel)
  upper_error := v3401_upper_checked
  lower_error := reuse_lower_error 45 72 Primitive.Addresses.material3401

def v3402_pa : Scalar.QComplex := ((999998871964862982081969803416 : Int)/10^30,(-1502021638183873073247382255 : Int)/10^30)
theorem v3402_pa_checked : Scalar.distance (sourceCoefficient 45 73 1 0) v3402_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3402_pb : Scalar.QComplex := ((-648088546870320605170695 : Int)/10^30,(-431477016927189454661627935 : Int)/10^30)
theorem v3402_pb_checked : Scalar.distance (sourceCoefficient 45 73 1 1) v3402_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3402_pg : Scalar.QComplex := ((-93086323020499599747133 : Int)/10^30,(139817829115188008181 : Int)/10^30)
theorem v3402_pg_checked : Scalar.distance (sourceCoefficient 45 73 1 2) v3402_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3402_mb : Scalar.QComplex := ((-1020433538162044591660653 : Int)/10^30,(-431476296997349454357904354 : Int)/10^30)
theorem v3402_mb_checked : Scalar.distance (sourceCoefficient 45 73 3 1) v3402_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3402_mg : Scalar.QComplex := ((-93086167703717918943110 : Int)/10^30,(220147081368953696437 : Int)/10^30)
theorem v3402_mg_checked : Scalar.distance (sourceCoefficient 45 73 3 2) v3402_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3402_upper : Scalar.QComplex := ((999994790230926142833005733027 : Int)/10^30,(-3227926734921431123337476966 : Int)/10^30)
theorem v3402_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 73 5) 1) 14) v3402_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3402 : Material (45 : Basis) (73 : Basis) where
  plus := ![v3402_pa,v3402_pb,v3402_pg]
  minus := ![(Primitive.Addresses.material3402 1).one,v3402_mb,v3402_mg]
  upper := v3402_upper
  lower := (Primitive.Addresses.material3402 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3402_pa_checked.trans (by decide +kernel)
    · exact v3402_pb_checked.trans (by decide +kernel)
    · exact v3402_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 73 Primitive.Addresses.material3402
    · exact v3402_mb_checked.trans (by decide +kernel)
    · exact v3402_mg_checked.trans (by decide +kernel)
  upper_error := v3402_upper_checked
  lower_error := reuse_lower_error 45 73 Primitive.Addresses.material3402

def v3403_pa : Scalar.QComplex := ((999998855937078352371876594619 : Int)/10^30,(-1512654796844041200921650830 : Int)/10^30)
theorem v3403_pa_checked : Scalar.distance (sourceCoefficient 45 74 1 0) v3403_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3403_pb : Scalar.QComplex := ((-652676514476278229016412 : Int)/10^30,(-431477009252211311162742597 : Int)/10^30)
theorem v3403_pb_checked : Scalar.distance (sourceCoefficient 45 74 1 1) v3403_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3403_pg : Scalar.QComplex := ((-93086321446619800362049 : Int)/10^30,(140807631749586359264 : Int)/10^30)
theorem v3403_pg_checked : Scalar.distance (sourceCoefficient 45 74 1 2) v3403_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3403_mb : Scalar.QComplex := ((-1025021497436531725674567 : Int)/10^30,(-431476285363164759053059492 : Int)/10^30)
theorem v3403_mb_checked : Scalar.distance (sourceCoefficient 45 74 3 1) v3403_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3403_mg : Scalar.QComplex := ((-93086165275683611155430 : Int)/10^30,(221136882276615908565 : Int)/10^30)
theorem v3403_mg_checked : Scalar.distance (sourceCoefficient 45 74 3 2) v3403_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3403_upper : Scalar.QComplex := ((999994755851298169793528235547 : Int)/10^30,(-3238559850082256243632853987 : Int)/10^30)
theorem v3403_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 74 5) 1) 14) v3403_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3403 : Material (45 : Basis) (74 : Basis) where
  plus := ![v3403_pa,v3403_pb,v3403_pg]
  minus := ![(Primitive.Addresses.material3403 1).one,v3403_mb,v3403_mg]
  upper := v3403_upper
  lower := (Primitive.Addresses.material3403 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3403_pa_checked.trans (by decide +kernel)
    · exact v3403_pb_checked.trans (by decide +kernel)
    · exact v3403_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 74 Primitive.Addresses.material3403
    · exact v3403_mb_checked.trans (by decide +kernel)
    · exact v3403_mg_checked.trans (by decide +kernel)
  upper_error := v3403_upper_checked
  lower_error := reuse_lower_error 45 74 Primitive.Addresses.material3403

def v3404_pa : Scalar.QComplex := ((999998833417158597085096456104 : Int)/10^30,(-1527469908669334130980888849 : Int)/10^30)
theorem v3404_pa_checked : Scalar.distance (sourceCoefficient 45 75 1 0) v3404_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3404_pb : Scalar.QComplex := ((-659068900274212038554394 : Int)/10^30,(-431476998450263017930304044 : Int)/10^30)
theorem v3404_pb_checked : Scalar.distance (sourceCoefficient 45 75 1 1) v3404_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3404_pg : Scalar.QComplex := ((-93086319233270812529130 : Int)/10^30,(142186717410193455280 : Int)/10^30)
theorem v3404_pg_checked : Scalar.distance (sourceCoefficient 45 75 1 2) v3404_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3404_mb : Scalar.QComplex := ((-1031413871532693280810240 : Int)/10^30,(-431476269044879446631666941 : Int)/10^30)
theorem v3404_mb_checked : Scalar.distance (sourceCoefficient 45 75 3 1) v3404_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3404_mg : Scalar.QComplex := ((-93086161872246634062029 : Int)/10^30,(222515965513705894846 : Int)/10^30)
theorem v3404_mg_checked : Scalar.distance (sourceCoefficient 45 75 3 2) v3404_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3404_upper : Scalar.QComplex := ((999994707761872961272160973314 : Int)/10^30,(-3253374900974841908739296110 : Int)/10^30)
theorem v3404_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 75 5) 1) 14) v3404_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3404 : Material (45 : Basis) (75 : Basis) where
  plus := ![v3404_pa,v3404_pb,v3404_pg]
  minus := ![(Primitive.Addresses.material3404 1).one,v3404_mb,v3404_mg]
  upper := v3404_upper
  lower := (Primitive.Addresses.material3404 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3404_pa_checked.trans (by decide +kernel)
    · exact v3404_pb_checked.trans (by decide +kernel)
    · exact v3404_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 75 Primitive.Addresses.material3404
    · exact v3404_mb_checked.trans (by decide +kernel)
    · exact v3404_mg_checked.trans (by decide +kernel)
  upper_error := v3404_upper_checked
  lower_error := reuse_lower_error 45 75 Primitive.Addresses.material3404

def v3405_pa : Scalar.QComplex := ((999998814353170440314694735540 : Int)/10^30,(-1539900079018429742737588505 : Int)/10^30)
theorem v3405_pa_checked : Scalar.distance (sourceCoefficient 45 76 1 0) v3405_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3405_pb : Scalar.QComplex := ((-664432237683970876271668 : Int)/10^30,(-431476989289798457835220671 : Int)/10^30)
theorem v3405_pb_checked : Scalar.distance (sourceCoefficient 45 76 1 1) v3405_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3405_pg : Scalar.QComplex := ((-93086317357837833100751 : Int)/10^30,(143343797409988043540 : Int)/10^30)
theorem v3405_pg_checked : Scalar.distance (sourceCoefficient 45 76 1 2) v3405_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3405_mb : Scalar.QComplex := ((-1036777199040368140892002 : Int)/10^30,(-431476255256099668524280856 : Int)/10^30)
theorem v3405_mb_checked : Scalar.distance (sourceCoefficient 45 76 3 1) v3405_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3405_mg : Scalar.QComplex := ((-93086158998306426068998 : Int)/10^30,(223673043464252523134 : Int)/10^30)
theorem v3405_mg_checked : Scalar.distance (sourceCoefficient 45 76 3 2) v3405_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3405_upper : Scalar.QComplex := ((999994667244566831778982287661 : Int)/10^30,(-3265805019907944848807235561 : Int)/10^30)
theorem v3405_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 76 5) 1) 14) v3405_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3405 : Material (45 : Basis) (76 : Basis) where
  plus := ![v3405_pa,v3405_pb,v3405_pg]
  minus := ![(Primitive.Addresses.material3405 1).one,v3405_mb,v3405_mg]
  upper := v3405_upper
  lower := (Primitive.Addresses.material3405 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3405_pa_checked.trans (by decide +kernel)
    · exact v3405_pb_checked.trans (by decide +kernel)
    · exact v3405_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 76 Primitive.Addresses.material3405
    · exact v3405_mb_checked.trans (by decide +kernel)
    · exact v3405_mg_checked.trans (by decide +kernel)
  upper_error := v3405_upper_checked
  lower_error := reuse_lower_error 45 76 Primitive.Addresses.material3405

def v3406_pa : Scalar.QComplex := ((999998809917669542198181430714 : Int)/10^30,(-1542777769032095681651260815 : Int)/10^30)
theorem v3406_pa_checked : Scalar.distance (sourceCoefficient 45 77 1 0) v3406_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3406_pb : Scalar.QComplex := ((-665673895840584823676223 : Int)/10^30,(-431476987156401648129654038 : Int)/10^30)
theorem v3406_pb_checked : Scalar.distance (sourceCoefficient 45 77 1 1) v3406_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3406_pg : Scalar.QComplex := ((-93086316921267158992243 : Int)/10^30,(143611671256919575372 : Int)/10^30)
theorem v3406_pg_checked : Scalar.distance (sourceCoefficient 45 77 1 2) v3406_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3406_mb : Scalar.QComplex := ((-1038018854893630647857665 : Int)/10^30,(-431476252051208586229454890 : Int)/10^30)
theorem v3406_mb_checked : Scalar.distance (sourceCoefficient 45 77 3 1) v3406_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3406_mg : Scalar.QComplex := ((-93086158330572849203999 : Int)/10^30,(223940916834701549970 : Int)/10^30)
theorem v3406_mg_checked : Scalar.distance (sourceCoefficient 45 77 3 2) v3406_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3406_upper : Scalar.QComplex := ((999994657842440638231350980095 : Int)/10^30,(-3268682697980357384929428421 : Int)/10^30)
theorem v3406_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 77 5) 1) 14) v3406_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3406 : Material (45 : Basis) (77 : Basis) where
  plus := ![v3406_pa,v3406_pb,v3406_pg]
  minus := ![(Primitive.Addresses.material3406 1).one,v3406_mb,v3406_mg]
  upper := v3406_upper
  lower := (Primitive.Addresses.material3406 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3406_pa_checked.trans (by decide +kernel)
    · exact v3406_pb_checked.trans (by decide +kernel)
    · exact v3406_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 77 Primitive.Addresses.material3406
    · exact v3406_mb_checked.trans (by decide +kernel)
    · exact v3406_mg_checked.trans (by decide +kernel)
  upper_error := v3406_upper_checked
  lower_error := reuse_lower_error 45 77 Primitive.Addresses.material3406

def v3407_pa : Scalar.QComplex := ((999998783078610114709301535697 : Int)/10^30,(-1560077337465329709281065811 : Int)/10^30)
theorem v3407_pa_checked : Scalar.distance (sourceCoefficient 45 78 1 0) v3407_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3407_pb : Scalar.QComplex := ((-673138268291988662504866 : Int)/10^30,(-431476974230831078767225845 : Int)/10^30)
theorem v3407_pb_checked : Scalar.distance (sourceCoefficient 45 78 1 1) v3407_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3407_pg : Scalar.QComplex := ((-93086314277817695389277 : Int)/10^30,(145222026056788526940 : Int)/10^30)
theorem v3407_pg_checked : Scalar.distance (sourceCoefficient 45 78 1 2) v3407_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3407_mb : Scalar.QComplex := ((-1045483213411522229083427 : Int)/10^30,(-431476232684225586941681537 : Int)/10^30)
theorem v3407_mb_checked : Scalar.distance (sourceCoefficient 45 78 3 1) v3407_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3407_mg : Scalar.QComplex := ((-93086154297460705279006 : Int)/10^30,(225551268753783982153 : Int)/10^30)
theorem v3407_mg_checked : Scalar.distance (sourceCoefficient 45 78 3 2) v3407_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3407_upper : Scalar.QComplex := ((999994601145935473195566378849 : Int)/10^30,(-3285982194326134629921754232 : Int)/10^30)
theorem v3407_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 78 5) 1) 14) v3407_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3407 : Material (45 : Basis) (78 : Basis) where
  plus := ![v3407_pa,v3407_pb,v3407_pg]
  minus := ![(Primitive.Addresses.material3407 1).one,v3407_mb,v3407_mg]
  upper := v3407_upper
  lower := (Primitive.Addresses.material3407 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3407_pa_checked.trans (by decide +kernel)
    · exact v3407_pb_checked.trans (by decide +kernel)
    · exact v3407_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 78 Primitive.Addresses.material3407
    · exact v3407_mb_checked.trans (by decide +kernel)
    · exact v3407_mg_checked.trans (by decide +kernel)
  upper_error := v3407_upper_checked
  lower_error := reuse_lower_error 45 78 Primitive.Addresses.material3407

def v3408_pa : Scalar.QComplex := ((999998774362380430677255285334 : Int)/10^30,(-1565654411724078713801526727 : Int)/10^30)
theorem v3408_pa_checked : Scalar.distance (sourceCoefficient 45 79 1 0) v3408_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3408_pb : Scalar.QComplex := ((-675544649653291411977281 : Int)/10^30,(-431476970027156145273263420 : Int)/10^30)
theorem v3408_pb_checked : Scalar.distance (sourceCoefficient 45 79 1 1) v3408_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3408_pg : Scalar.QComplex := ((-93086313418688512670301 : Int)/10^30,(145741175900967882286 : Int)/10^30)
theorem v3408_pg_checked : Scalar.distance (sourceCoefficient 45 79 1 2) v3408_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3408_mb : Scalar.QComplex := ((-1047889590249237079567225 : Int)/10^30,(-431476226403953483257022377 : Int)/10^30)
theorem v3408_mb_checked : Scalar.distance (sourceCoefficient 45 79 3 1) v3408_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3408_mg : Scalar.QComplex := ((-93086152990328908567320 : Int)/10^30,(226070417663270333246 : Int)/10^30)
theorem v3408_mg_checked : Scalar.distance (sourceCoefficient 45 79 3 2) v3408_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3408_upper : Scalar.QComplex := ((999994582804194548587475502579 : Int)/10^30,(-3291559245235064950739097607 : Int)/10^30)
theorem v3408_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 79 5) 1) 14) v3408_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3408 : Material (45 : Basis) (79 : Basis) where
  plus := ![v3408_pa,v3408_pb,v3408_pg]
  minus := ![(Primitive.Addresses.material3408 1).one,v3408_mb,v3408_mg]
  upper := v3408_upper
  lower := (Primitive.Addresses.material3408 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3408_pa_checked.trans (by decide +kernel)
    · exact v3408_pb_checked.trans (by decide +kernel)
    · exact v3408_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 79 Primitive.Addresses.material3408
    · exact v3408_mb_checked.trans (by decide +kernel)
    · exact v3408_mg_checked.trans (by decide +kernel)
  upper_error := v3408_upper_checked
  lower_error := reuse_lower_error 45 79 Primitive.Addresses.material3408

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
