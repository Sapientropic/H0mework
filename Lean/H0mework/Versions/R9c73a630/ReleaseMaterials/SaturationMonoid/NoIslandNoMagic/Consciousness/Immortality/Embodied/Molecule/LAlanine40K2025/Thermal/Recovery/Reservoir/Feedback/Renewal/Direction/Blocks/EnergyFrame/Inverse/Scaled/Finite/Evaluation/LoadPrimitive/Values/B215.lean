import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B143
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B144

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3441_pa : Scalar.QComplex := ((999999254043630096853451001818 : Int)/10^30,(-1221438571257428115003457241 : Int)/10^30)
theorem v3441_pa_checked : Scalar.distance (sourceCoefficient 46 61 1 0) v3441_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3441_pb : Scalar.QComplex := ((-527023284000879759868077 : Int)/10^30,(-431477196861363575427619166 : Int)/10^30)
theorem v3441_pb_checked : Scalar.distance (sourceCoefficient 46 61 1 1) v3441_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3441_pg : Scalar.QComplex := ((-93086360213062528690236 : Int)/10^30,(113699355636955988090 : Int)/10^30)
theorem v3441_pg_checked : Scalar.distance (sourceCoefficient 46 61 1 2) v3441_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3441_mb : Scalar.QComplex := ((-899368475645822400348395 : Int)/10^30,(-431476581405325856704456000 : Int)/10^30)
theorem v3441_mb_checked : Scalar.distance (sourceCoefficient 46 61 3 1) v3441_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3441_mg : Scalar.QComplex := ((-93086227435333278731535 : Int)/10^30,(194028649711329742324 : Int)/10^30)
theorem v3441_mg_checked : Scalar.distance (sourceCoefficient 46 61 3 2) v3441_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3441_upper : Scalar.QComplex := ((999995656570043414213481304991 : Int)/10^30,(-2947344745323794874813297965 : Int)/10^30)
theorem v3441_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 61 5) 1) 14) v3441_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3441 : Material (46 : Basis) (61 : Basis) where
  plus := ![v3441_pa,v3441_pb,v3441_pg]
  minus := ![(Primitive.Addresses.material3441 1).one,v3441_mb,v3441_mg]
  upper := v3441_upper
  lower := (Primitive.Addresses.material3441 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3441_pa_checked.trans (by decide +kernel)
    · exact v3441_pb_checked.trans (by decide +kernel)
    · exact v3441_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 61 Primitive.Addresses.material3441
    · exact v3441_mb_checked.trans (by decide +kernel)
    · exact v3441_mg_checked.trans (by decide +kernel)
  upper_error := v3441_upper_checked
  lower_error := reuse_lower_error 46 61 Primitive.Addresses.material3441

def v3442_pa : Scalar.QComplex := ((999999243608841211137466844320 : Int)/10^30,(-1229951928105379235741155164 : Int)/10^30)
theorem v3442_pa_checked : Scalar.distance (sourceCoefficient 46 62 1 0) v3442_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3442_pb : Scalar.QComplex := ((-530696605815326053485827 : Int)/10^30,(-431477192135948811462918108 : Int)/10^30)
theorem v3442_pb_checked : Scalar.distance (sourceCoefficient 46 62 1 1) v3442_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3442_pg : Scalar.QComplex := ((-93086359217666321099391 : Int)/10^30,(114491833600689321776 : Int)/10^30)
theorem v3442_pg_checked : Scalar.distance (sourceCoefficient 46 62 1 2) v3442_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3442_mb : Scalar.QComplex := ((-903041792014702986826479 : Int)/10^30,(-431476573510001566633573340 : Int)/10^30)
theorem v3442_mb_checked : Scalar.distance (sourceCoefficient 46 62 3 1) v3442_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3442_mg : Scalar.QComplex := ((-93086225756064650952865 : Int)/10^30,(194821126521005215911 : Int)/10^30)
theorem v3442_mg_checked : Scalar.distance (sourceCoefficient 46 62 3 2) v3442_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3442_upper : Scalar.QComplex := ((999995631441988476026320462507 : Int)/10^30,(-2955858071482602039579986580 : Int)/10^30)
theorem v3442_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 62 5) 1) 14) v3442_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3442 : Material (46 : Basis) (62 : Basis) where
  plus := ![v3442_pa,v3442_pb,v3442_pg]
  minus := ![(Primitive.Addresses.material3442 1).one,v3442_mb,v3442_mg]
  upper := v3442_upper
  lower := (Primitive.Addresses.material3442 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3442_pa_checked.trans (by decide +kernel)
    · exact v3442_pb_checked.trans (by decide +kernel)
    · exact v3442_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 62 Primitive.Addresses.material3442
    · exact v3442_mb_checked.trans (by decide +kernel)
    · exact v3442_mg_checked.trans (by decide +kernel)
  upper_error := v3442_upper_checked
  lower_error := reuse_lower_error 46 62 Primitive.Addresses.material3442

def v3443_pa : Scalar.QComplex := ((999999212804569267824892935093 : Int)/10^30,(-1254747082797048804724707665 : Int)/10^30)
theorem v3443_pa_checked : Scalar.distance (sourceCoefficient 46 63 1 0) v3443_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3443_pb : Scalar.QComplex := ((-541395156742949964641072 : Int)/10^30,(-431477178135607719996389361 : Int)/10^30)
theorem v3443_pb_checked : Scalar.distance (sourceCoefficient 46 63 1 1) v3443_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3443_pg : Scalar.QComplex := ((-93086356273728284203541 : Int)/10^30,(116799925927035326488 : Int)/10^30)
theorem v3443_pg_checked : Scalar.distance (sourceCoefficient 46 63 1 2) v3443_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3443_mb : Scalar.QComplex := ((-913740326877103629715388 : Int)/10^30,(-431476550277298082441303500 : Int)/10^30)
theorem v3443_mb_checked : Scalar.distance (sourceCoefficient 46 63 3 1) v3443_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3443_mg : Scalar.QComplex := ((-93086220820347985202564 : Int)/10^30,(197129215447457026700 : Int)/10^30)
theorem v3443_mg_checked : Scalar.distance (sourceCoefficient 46 63 3 2) v3443_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3443_upper : Scalar.QComplex := ((999995557843574813098894719790 : Int)/10^30,(-2980653136079422506357277012 : Int)/10^30)
theorem v3443_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 63 5) 1) 14) v3443_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3443 : Material (46 : Basis) (63 : Basis) where
  plus := ![v3443_pa,v3443_pb,v3443_pg]
  minus := ![(Primitive.Addresses.material3443 1).one,v3443_mb,v3443_mg]
  upper := v3443_upper
  lower := (Primitive.Addresses.material3443 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3443_pa_checked.trans (by decide +kernel)
    · exact v3443_pb_checked.trans (by decide +kernel)
    · exact v3443_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 63 Primitive.Addresses.material3443
    · exact v3443_mb_checked.trans (by decide +kernel)
    · exact v3443_mg_checked.trans (by decide +kernel)
  upper_error := v3443_upper_checked
  lower_error := reuse_lower_error 46 63 Primitive.Addresses.material3443

def v3444_pa : Scalar.QComplex := ((999999167711856685520946309916 : Int)/10^30,(-1290184325561818552632664855 : Int)/10^30)
theorem v3444_pa_checked : Scalar.distance (sourceCoefficient 46 64 1 0) v3444_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3444_pb : Scalar.QComplex := ((-556685528783142247342180 : Int)/10^30,(-431477157512330816958342059 : Int)/10^30)
theorem v3444_pb_checked : Scalar.distance (sourceCoefficient 46 64 1 1) v3444_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3444_pg : Scalar.QComplex := ((-93086351950348269026190 : Int)/10^30,(120098652166754380951 : Int)/10^30)
theorem v3444_pg_checked : Scalar.distance (sourceCoefficient 46 64 1 2) v3444_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3444_mb : Scalar.QComplex := ((-929030675427032467918822 : Int)/10^30,(-431476516459126440498534494 : Int)/10^30)
theorem v3444_mb_checked : Scalar.distance (sourceCoefficient 46 64 3 1) v3444_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3444_mg : Scalar.QComplex := ((-93086213650317404054330 : Int)/10^30,(200427936728027307588 : Int)/10^30)
theorem v3444_mg_checked : Scalar.distance (sourceCoefficient 46 64 3 2) v3444_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3444_upper : Scalar.QComplex := ((999995451589463220651448312867 : Int)/10^30,(-3016090248238650768966593483 : Int)/10^30)
theorem v3444_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 64 5) 1) 14) v3444_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3444 : Material (46 : Basis) (64 : Basis) where
  plus := ![v3444_pa,v3444_pb,v3444_pg]
  minus := ![(Primitive.Addresses.material3444 1).one,v3444_mb,v3444_mg]
  upper := v3444_upper
  lower := (Primitive.Addresses.material3444 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3444_pa_checked.trans (by decide +kernel)
    · exact v3444_pb_checked.trans (by decide +kernel)
    · exact v3444_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 64 Primitive.Addresses.material3444
    · exact v3444_mb_checked.trans (by decide +kernel)
    · exact v3444_mg_checked.trans (by decide +kernel)
  upper_error := v3444_upper_checked
  lower_error := reuse_lower_error 46 64 Primitive.Addresses.material3444

def v3445_pa : Scalar.QComplex := ((999999120661490481214217837375 : Int)/10^30,(-1326150913660039387300819532 : Int)/10^30)
theorem v3445_pa_checked : Scalar.distance (sourceCoefficient 46 65 1 0) v3445_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3445_pb : Scalar.QComplex := ((-572204301081904721253679 : Int)/10^30,(-431477135842258069823009873 : Int)/10^30)
theorem v3445_pb_checked : Scalar.distance (sourceCoefficient 46 65 1 1) v3445_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3445_pg : Scalar.QComplex := ((-93086347422935536396380 : Int)/10^30,(123446653235597875724 : Int)/10^30)
theorem v3445_pg_checked : Scalar.distance (sourceCoefficient 46 65 1 2) v3445_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3445_mb : Scalar.QComplex := ((-944549423247149975138203 : Int)/10^30,(-431476481397060207848122587 : Int)/10^30)
theorem v3445_mb_checked : Scalar.distance (sourceCoefficient 46 65 3 1) v3445_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3445_mg : Scalar.QComplex := ((-93086206233732223145871 : Int)/10^30,(203775932643303712064 : Int)/10^30)
theorem v3445_mg_checked : Scalar.distance (sourceCoefficient 46 65 3 2) v3445_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3445_upper : Scalar.QComplex := ((999995342464098898193276840629 : Int)/10^30,(-3052056701564199870804052307 : Int)/10^30)
theorem v3445_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 65 5) 1) 14) v3445_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3445 : Material (46 : Basis) (65 : Basis) where
  plus := ![v3445_pa,v3445_pb,v3445_pg]
  minus := ![(Primitive.Addresses.material3445 1).one,v3445_mb,v3445_mg]
  upper := v3445_upper
  lower := (Primitive.Addresses.material3445 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3445_pa_checked.trans (by decide +kernel)
    · exact v3445_pb_checked.trans (by decide +kernel)
    · exact v3445_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 65 Primitive.Addresses.material3445
    · exact v3445_mb_checked.trans (by decide +kernel)
    · exact v3445_mg_checked.trans (by decide +kernel)
  upper_error := v3445_upper_checked
  lower_error := reuse_lower_error 46 65 Primitive.Addresses.material3445

def v3446_pa : Scalar.QComplex := ((999999097183061960940554499092 : Int)/10^30,(-1343738464508512638855417049 : Int)/10^30)
theorem v3446_pa_checked : Scalar.distance (sourceCoefficient 46 66 1 0) v3446_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3446_pb : Scalar.QComplex := ((-579792932830962906851456 : Int)/10^30,(-431477124974723519032061427 : Int)/10^30)
theorem v3446_pb_checked : Scalar.distance (sourceCoefficient 46 66 1 1) v3446_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3446_pg : Scalar.QComplex := ((-93086345157899720236989 : Int)/10^30,(125083815436972841606 : Int)/10^30)
theorem v3446_pg_checked : Scalar.distance (sourceCoefficient 46 66 1 2) v3446_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3446_mb : Scalar.QComplex := ((-952138042792420881211682 : Int)/10^30,(-431476463980882283386278180 : Int)/10^30)
theorem v3446_mb_checked : Scalar.distance (sourceCoefficient 46 66 3 1) v3446_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3446_mg : Scalar.QComplex := ((-93086202555900005624612 : Int)/10^30,(205413092280464472445 : Int)/10^30)
theorem v3446_mg_checked : Scalar.distance (sourceCoefficient 46 66 3 2) v3446_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3446_upper : Scalar.QComplex := ((999995288631188111965468264556 : Int)/10^30,(-3069644185696444432812290179 : Int)/10^30)
theorem v3446_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 66 5) 1) 14) v3446_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3446 : Material (46 : Basis) (66 : Basis) where
  plus := ![v3446_pa,v3446_pb,v3446_pg]
  minus := ![(Primitive.Addresses.material3446 1).one,v3446_mb,v3446_mg]
  upper := v3446_upper
  lower := (Primitive.Addresses.material3446 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3446_pa_checked.trans (by decide +kernel)
    · exact v3446_pb_checked.trans (by decide +kernel)
    · exact v3446_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 66 Primitive.Addresses.material3446
    · exact v3446_mb_checked.trans (by decide +kernel)
    · exact v3446_mg_checked.trans (by decide +kernel)
  upper_error := v3446_upper_checked
  lower_error := reuse_lower_error 46 66 Primitive.Addresses.material3446

def v3447_pa : Scalar.QComplex := ((999999057084094607223462622474 : Int)/10^30,(-1373255592267931902950427381 : Int)/10^30)
theorem v3447_pa_checked : Scalar.distance (sourceCoefficient 46 67 1 0) v3447_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3447_pb : Scalar.QComplex := ((-592528907916190350003841 : Int)/10^30,(-431477106335826367154526602 : Int)/10^30)
theorem v3447_pb_checked : Scalar.distance (sourceCoefficient 46 67 1 1) v3447_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3447_pg : Scalar.QComplex := ((-93086341280998486447384 : Int)/10^30,(127831459262208563321 : Int)/10^30)
theorem v3447_pg_checked : Scalar.distance (sourceCoefficient 46 67 1 2) v3447_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3447_mb : Scalar.QComplex := ((-964873997050933960013020 : Int)/10^30,(-431476434351419180095254233 : Int)/10^30)
theorem v3447_mb_checked : Scalar.distance (sourceCoefficient 46 67 3 1) v3447_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3447_mg : Scalar.QComplex := ((-93086196307907343488190 : Int)/10^30,(208160731737035668888 : Int)/10^30)
theorem v3447_mg_checked : Scalar.distance (sourceCoefficient 46 67 3 2) v3447_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3447_upper : Scalar.QComplex := ((999995197588395741104964778232 : Int)/10^30,(-3099161200286389322031338271 : Int)/10^30)
theorem v3447_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 67 5) 1) 14) v3447_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3447 : Material (46 : Basis) (67 : Basis) where
  plus := ![v3447_pa,v3447_pb,v3447_pg]
  minus := ![(Primitive.Addresses.material3447 1).one,v3447_mb,v3447_mg]
  upper := v3447_upper
  lower := (Primitive.Addresses.material3447 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3447_pa_checked.trans (by decide +kernel)
    · exact v3447_pb_checked.trans (by decide +kernel)
    · exact v3447_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 67 Primitive.Addresses.material3447
    · exact v3447_mb_checked.trans (by decide +kernel)
    · exact v3447_mg_checked.trans (by decide +kernel)
  upper_error := v3447_upper_checked
  lower_error := reuse_lower_error 46 67 Primitive.Addresses.material3447

def v3448_pa : Scalar.QComplex := ((999998988369366974137950659078 : Int)/10^30,(-1422413527303219379213457739 : Int)/10^30)
theorem v3448_pa_checked : Scalar.distance (sourceCoefficient 46 68 1 0) v3448_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3448_pb : Scalar.QComplex := ((-613739447915375828240807 : Int)/10^30,(-431477074182040881341920513 : Int)/10^30)
theorem v3448_pb_checked : Scalar.distance (sourceCoefficient 46 68 1 1) v3448_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3448_pg : Scalar.QComplex := ((-93086334614385074990889 : Int)/10^30,(132407395509952577088 : Int)/10^30)
theorem v3448_pg_checked : Scalar.distance (sourceCoefficient 46 68 1 2) v3448_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3448_mb : Scalar.QComplex := ((-986084501405197305471486 : Int)/10^30,(-431476383893904934569050719 : Int)/10^30)
theorem v3448_mb_checked : Scalar.distance (sourceCoefficient 46 68 3 1) v3448_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3448_mg : Scalar.QComplex := ((-93086185692469525031549 : Int)/10^30,(212736660527962366037 : Int)/10^30)
theorem v3448_mg_checked : Scalar.distance (sourceCoefficient 46 68 3 2) v3448_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3448_upper : Scalar.QComplex := ((999995044031634152658407872073 : Int)/10^30,(-3148318943511320916609072046 : Int)/10^30)
theorem v3448_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 68 5) 1) 14) v3448_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3448 : Material (46 : Basis) (68 : Basis) where
  plus := ![v3448_pa,v3448_pb,v3448_pg]
  minus := ![(Primitive.Addresses.material3448 1).one,v3448_mb,v3448_mg]
  upper := v3448_upper
  lower := (Primitive.Addresses.material3448 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3448_pa_checked.trans (by decide +kernel)
    · exact v3448_pb_checked.trans (by decide +kernel)
    · exact v3448_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 68 Primitive.Addresses.material3448
    · exact v3448_mb_checked.trans (by decide +kernel)
    · exact v3448_mg_checked.trans (by decide +kernel)
  upper_error := v3448_upper_checked
  lower_error := reuse_lower_error 46 68 Primitive.Addresses.material3448

def v3449_pa : Scalar.QComplex := ((999998957360853981226553968049 : Int)/10^30,(-1444048892849947127892784979 : Int)/10^30)
theorem v3449_pa_checked : Scalar.distance (sourceCoefficient 46 69 1 0) v3449_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3449_pb : Scalar.QComplex := ((-623074619833012545874860 : Int)/10^30,(-431477059589953502530462986 : Int)/10^30)
theorem v3449_pb_checked : Scalar.distance (sourceCoefficient 46 69 1 1) v3449_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3449_pg : Scalar.QComplex := ((-93086331597109694714321 : Int)/10^30,(134421354235235291754 : Int)/10^30)
theorem v3449_pg_checked : Scalar.distance (sourceCoefficient 46 69 1 2) v3449_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3449_mb : Scalar.QComplex := ((-995419657254608675041111 : Int)/10^30,(-431476361245990064673812380 : Int)/10^30)
theorem v3449_mb_checked : Scalar.distance (sourceCoefficient 46 69 3 1) v3449_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3449_mg : Scalar.QComplex := ((-93086180937239593639365 : Int)/10^30,(214750615899583444680 : Int)/10^30)
theorem v3449_mg_checked : Scalar.distance (sourceCoefficient 46 69 3 2) v3449_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3449_upper : Scalar.QComplex := ((999994975682489154662780460195 : Int)/10^30,(-3169954223316832796562112579 : Int)/10^30)
theorem v3449_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 69 5) 1) 14) v3449_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3449 : Material (46 : Basis) (69 : Basis) where
  plus := ![v3449_pa,v3449_pb,v3449_pg]
  minus := ![(Primitive.Addresses.material3449 1).one,v3449_mb,v3449_mg]
  upper := v3449_upper
  lower := (Primitive.Addresses.material3449 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3449_pa_checked.trans (by decide +kernel)
    · exact v3449_pb_checked.trans (by decide +kernel)
    · exact v3449_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 69 Primitive.Addresses.material3449
    · exact v3449_mb_checked.trans (by decide +kernel)
    · exact v3449_mg_checked.trans (by decide +kernel)
  upper_error := v3449_upper_checked
  lower_error := reuse_lower_error 46 69 Primitive.Addresses.material3449

def v3450_pa : Scalar.QComplex := ((999998936707924674138762199644 : Int)/10^30,(-1458280844028915105471586005 : Int)/10^30)
theorem v3450_pa_checked : Scalar.distance (sourceCoefficient 46 70 1 0) v3450_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3450_pb : Scalar.QComplex := ((-629215385465789119621720 : Int)/10^30,(-431477049844302745525363289 : Int)/10^30)
theorem v3450_pb_checked : Scalar.distance (sourceCoefficient 46 70 1 1) v3450_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3450_pg : Scalar.QComplex := ((-93086329584598610776201 : Int)/10^30,(135746155611993750746 : Int)/10^30)
theorem v3450_pg_checked : Scalar.distance (sourceCoefficient 46 70 1 2) v3450_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3450_mb : Scalar.QComplex := ((-1001560412190839881372526 : Int)/10^30,(-431476346201138765151050660 : Int)/10^30)
theorem v3450_mb_checked : Scalar.distance (sourceCoefficient 46 70 3 1) v3450_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3450_mg : Scalar.QComplex := ((-93086177781485337747620 : Int)/10^30,(216075415046351379387 : Int)/10^30)
theorem v3450_mg_checked : Scalar.distance (sourceCoefficient 46 70 3 2) v3450_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3450_upper : Scalar.QComplex := ((999994930466533985313737209419 : Int)/10^30,(-3184186117653898930568608696 : Int)/10^30)
theorem v3450_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 70 5) 1) 14) v3450_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3450 : Material (46 : Basis) (70 : Basis) where
  plus := ![v3450_pa,v3450_pb,v3450_pg]
  minus := ![(Primitive.Addresses.material3450 1).one,v3450_mb,v3450_mg]
  upper := v3450_upper
  lower := (Primitive.Addresses.material3450 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3450_pa_checked.trans (by decide +kernel)
    · exact v3450_pb_checked.trans (by decide +kernel)
    · exact v3450_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 70 Primitive.Addresses.material3450
    · exact v3450_mb_checked.trans (by decide +kernel)
    · exact v3450_mg_checked.trans (by decide +kernel)
  upper_error := v3450_upper_checked
  lower_error := reuse_lower_error 46 70 Primitive.Addresses.material3450

def v3451_pa : Scalar.QComplex := ((999998900987105564228026670676 : Int)/10^30,(-1482573634273253157856545655 : Int)/10^30)
theorem v3451_pa_checked : Scalar.distance (sourceCoefficient 46 71 1 0) v3451_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3451_pb : Scalar.QComplex := ((-639697175866827411093662 : Int)/10^30,(-431477032940058434567551333 : Int)/10^30)
theorem v3451_pb_checked : Scalar.distance (sourceCoefficient 46 71 1 1) v3451_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3451_pg : Scalar.QComplex := ((-93086326098586407037514 : Int)/10^30,(138007484457131371336 : Int)/10^30)
theorem v3451_pg_checked : Scalar.distance (sourceCoefficient 46 71 1 2) v3451_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3451_mb : Scalar.QComplex := ((-1012042184101427063596401 : Int)/10^30,(-431476320251587714635055742 : Int)/10^30)
theorem v3451_mb_checked : Scalar.distance (sourceCoefficient 46 71 3 1) v3451_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3451_mg : Scalar.QComplex := ((-93086172344049485127294 : Int)/10^30,(218336740041221395433 : Int)/10^30)
theorem v3451_mg_checked : Scalar.distance (sourceCoefficient 46 71 3 2) v3451_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3451_upper : Scalar.QComplex := ((999994852818615940355157725532 : Int)/10^30,(-3208478810066086329300624146 : Int)/10^30)
theorem v3451_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 71 5) 1) 14) v3451_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3451 : Material (46 : Basis) (71 : Basis) where
  plus := ![v3451_pa,v3451_pb,v3451_pg]
  minus := ![(Primitive.Addresses.material3451 1).one,v3451_mb,v3451_mg]
  upper := v3451_upper
  lower := (Primitive.Addresses.material3451 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3451_pa_checked.trans (by decide +kernel)
    · exact v3451_pb_checked.trans (by decide +kernel)
    · exact v3451_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 71 Primitive.Addresses.material3451
    · exact v3451_mb_checked.trans (by decide +kernel)
    · exact v3451_mg_checked.trans (by decide +kernel)
  upper_error := v3451_upper_checked
  lower_error := reuse_lower_error 46 71 Primitive.Addresses.material3451

def v3452_pa : Scalar.QComplex := ((999998861555077427987505561518 : Int)/10^30,(-1508936230954503676398028601 : Int)/10^30)
theorem v3452_pa_checked : Scalar.distance (sourceCoefficient 46 72 1 0) v3452_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3452_pb : Scalar.QComplex := ((-651072040777307354085771 : Int)/10^30,(-431477014211397062297268818 : Int)/10^30)
theorem v3452_pb_checked : Scalar.distance (sourceCoefficient 46 72 1 1) v3452_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3452_pg : Scalar.QComplex := ((-93086322243043856926630 : Int)/10^30,(140461484146498421509 : Int)/10^30)
theorem v3452_pg_checked : Scalar.distance (sourceCoefficient 46 72 1 2) v3452_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3452_mb : Scalar.QComplex := ((-1023417028614533686735441 : Int)/10^30,(-431476291706937203055069704 : Int)/10^30)
theorem v3452_mb_checked : Scalar.distance (sourceCoefficient 46 72 3 1) v3452_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3452_mg : Scalar.QComplex := ((-93086166370817162730508 : Int)/10^30,(220790735489692634373 : Int)/10^30)
theorem v3452_mg_checked : Scalar.distance (sourceCoefficient 46 72 3 2) v3452_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3452_upper : Scalar.QComplex := ((999994767887196257738938784309 : Int)/10^30,(-3234841299427242541759207480 : Int)/10^30)
theorem v3452_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 72 5) 1) 14) v3452_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3452 : Material (46 : Basis) (72 : Basis) where
  plus := ![v3452_pa,v3452_pb,v3452_pg]
  minus := ![(Primitive.Addresses.material3452 1).one,v3452_mb,v3452_mg]
  upper := v3452_upper
  lower := (Primitive.Addresses.material3452 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3452_pa_checked.trans (by decide +kernel)
    · exact v3452_pb_checked.trans (by decide +kernel)
    · exact v3452_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 72 Primitive.Addresses.material3452
    · exact v3452_mb_checked.trans (by decide +kernel)
    · exact v3452_mg_checked.trans (by decide +kernel)
  upper_error := v3452_upper_checked
  lower_error := reuse_lower_error 46 72 Primitive.Addresses.material3452

def v3453_pa : Scalar.QComplex := ((999998847251521471786728468274 : Int)/10^30,(-1518385862759322385397812297 : Int)/10^30)
theorem v3453_pa_checked : Scalar.distance (sourceCoefficient 46 73 1 0) v3453_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3453_pb : Scalar.QComplex := ((-655149343365471412656328 : Int)/10^30,(-431477007400792361202387218 : Int)/10^30)
theorem v3453_pb_checked : Scalar.distance (sourceCoefficient 46 73 1 1) v3453_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3453_pg : Scalar.QComplex := ((-93086320842654635234021 : Int)/10^30,(141341116514522267473 : Int)/10^30)
theorem v3453_pg_checked : Scalar.distance (sourceCoefficient 46 73 1 2) v3453_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3453_mb : Scalar.QComplex := ((-1027494323807286531002956 : Int)/10^30,(-431476281377806539165719087 : Int)/10^30)
theorem v3453_mb_checked : Scalar.distance (sourceCoefficient 46 73 3 1) v3453_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3453_mg : Scalar.QComplex := ((-93086164211345346033425 : Int)/10^30,(221670366321716321405 : Int)/10^30)
theorem v3453_mg_checked : Scalar.distance (sourceCoefficient 46 73 3 2) v3453_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3453_upper : Scalar.QComplex := ((999994737274454373788208065319 : Int)/10^30,(-3244290892471304737266238317 : Int)/10^30)
theorem v3453_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 73 5) 1) 14) v3453_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3453 : Material (46 : Basis) (73 : Basis) where
  plus := ![v3453_pa,v3453_pb,v3453_pg]
  minus := ![(Primitive.Addresses.material3453 1).one,v3453_mb,v3453_mg]
  upper := v3453_upper
  lower := (Primitive.Addresses.material3453 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3453_pa_checked.trans (by decide +kernel)
    · exact v3453_pb_checked.trans (by decide +kernel)
    · exact v3453_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 73 Primitive.Addresses.material3453
    · exact v3453_mb_checked.trans (by decide +kernel)
    · exact v3453_mg_checked.trans (by decide +kernel)
  upper_error := v3453_upper_checked
  lower_error := reuse_lower_error 46 73 Primitive.Addresses.material3453

def v3454_pa : Scalar.QComplex := ((999998831049733249540663285589 : Int)/10^30,(-1529019021155784228283486570 : Int)/10^30)
theorem v3454_pa_checked : Scalar.distance (sourceCoefficient 46 74 1 0) v3454_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3454_pb : Scalar.QComplex := ((-659737310895573482760053 : Int)/10^30,(-431476999675761793372840557 : Int)/10^30)
theorem v3454_pb_checked : Scalar.distance (sourceCoefficient 46 74 1 1) v3454_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3454_pg : Scalar.QComplex := ((-93086319255277025035125 : Int)/10^30,(142330919128464388368 : Int)/10^30)
theorem v3454_pg_checked : Scalar.distance (sourceCoefficient 46 74 1 2) v3454_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3454_mb : Scalar.QComplex := ((-1032082282962725151599517 : Int)/10^30,(-431476269693569503626944460 : Int)/10^30)
theorem v3454_mb_checked : Scalar.distance (sourceCoefficient 46 74 3 1) v3454_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3454_mg : Scalar.QComplex := ((-93086161769813250110590 : Int)/10^30,(222660167197274308148 : Int)/10^30)
theorem v3454_mg_checked : Scalar.distance (sourceCoefficient 46 74 3 2) v3454_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3454_upper : Scalar.QComplex := ((999994702720823522503794076313 : Int)/10^30,(-3254924007068109550298072926 : Int)/10^30)
theorem v3454_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 74 5) 1) 14) v3454_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3454 : Material (46 : Basis) (74 : Basis) where
  plus := ![v3454_pa,v3454_pb,v3454_pg]
  minus := ![(Primitive.Addresses.material3454 1).one,v3454_mb,v3454_mg]
  upper := v3454_upper
  lower := (Primitive.Addresses.material3454 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3454_pa_checked.trans (by decide +kernel)
    · exact v3454_pb_checked.trans (by decide +kernel)
    · exact v3454_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 74 Primitive.Addresses.material3454
    · exact v3454_mb_checked.trans (by decide +kernel)
    · exact v3454_mg_checked.trans (by decide +kernel)
  upper_error := v3454_upper_checked
  lower_error := reuse_lower_error 46 74 Primitive.Addresses.material3454

def v3455_pa : Scalar.QComplex := ((999998808287375403791496961023 : Int)/10^30,(-1543834132610572055846145784 : Int)/10^30)
theorem v3455_pa_checked : Scalar.distance (sourceCoefficient 46 75 1 0) v3455_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3455_pb : Scalar.QComplex := ((-666129696586930880206763 : Int)/10^30,(-431476988804075778145136642 : Int)/10^30)
theorem v3455_pb_checked : Scalar.distance (sourceCoefficient 46 75 1 1) v3455_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3455_pg : Scalar.QComplex := ((-93086317023121623903740 : Int)/10^30,(143710004760330653793 : Int)/10^30)
theorem v3455_pg_checked : Scalar.distance (sourceCoefficient 46 75 1 2) v3455_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3455_mb : Scalar.QComplex := ((-1038474656892129821115676 : Int)/10^30,(-431476253305546587147471228 : Int)/10^30)
theorem v3455_mb_checked : Scalar.distance (sourceCoefficient 46 75 3 1) v3455_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3455_mg : Scalar.QComplex := ((-93086158347569891523252 : Int)/10^30,(224039250389394386872 : Int)/10^30)
theorem v3455_mg_checked : Scalar.distance (sourceCoefficient 46 75 3 2) v3455_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3455_upper : Scalar.QComplex := ((999994654388961224061292541882 : Int)/10^30,(-3269739057171764514405445788 : Int)/10^30)
theorem v3455_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 75 5) 1) 14) v3455_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3455 : Material (46 : Basis) (75 : Basis) where
  plus := ![v3455_pa,v3455_pb,v3455_pg]
  minus := ![(Primitive.Addresses.material3455 1).one,v3455_mb,v3455_mg]
  upper := v3455_upper
  lower := (Primitive.Addresses.material3455 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3455_pa_checked.trans (by decide +kernel)
    · exact v3455_pb_checked.trans (by decide +kernel)
    · exact v3455_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 75 Primitive.Addresses.material3455
    · exact v3455_mb_checked.trans (by decide +kernel)
    · exact v3455_mg_checked.trans (by decide +kernel)
  upper_error := v3455_upper_checked
  lower_error := reuse_lower_error 46 75 Primitive.Addresses.material3455

def v3456_pa : Scalar.QComplex := ((999998789019976918516104023220 : Int)/10^30,(-1556264302646035600289997582 : Int)/10^30)
theorem v3456_pa_checked : Scalar.distance (sourceCoefficient 46 76 1 0) v3456_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3456_pb : Scalar.QComplex := ((-671493033906472929600431 : Int)/10^30,(-431476979585099897103865585 : Int)/10^30)
theorem v3456_pb_checked : Scalar.distance (sourceCoefficient 46 76 1 1) v3456_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3456_pg : Scalar.QComplex := ((-93086315131909693665401 : Int)/10^30,(144867084735796167916 : Int)/10^30)
theorem v3456_pg_checked : Scalar.distance (sourceCoefficient 46 76 1 2) v3456_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3456_mb : Scalar.QComplex := ((-1043837984259095291741176 : Int)/10^30,(-431476239458255587733361458 : Int)/10^30)
theorem v3456_mb_checked : Scalar.distance (sourceCoefficient 46 76 3 1) v3456_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3456_mg : Scalar.QComplex := ((-93086155457850759590380 : Int)/10^30,(225196328301995426190 : Int)/10^30)
theorem v3456_mg_checked : Scalar.distance (sourceCoefficient 46 76 3 2) v3456_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3456_upper : Scalar.QComplex := ((999994613668245610319408394596 : Int)/10^30,(-3282169175440168080519898158 : Int)/10^30)
theorem v3456_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 76 5) 1) 14) v3456_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3456 : Material (46 : Basis) (76 : Basis) where
  plus := ![v3456_pa,v3456_pb,v3456_pg]
  minus := ![(Primitive.Addresses.material3456 1).one,v3456_mb,v3456_mg]
  upper := v3456_upper
  lower := (Primitive.Addresses.material3456 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3456_pa_checked.trans (by decide +kernel)
    · exact v3456_pb_checked.trans (by decide +kernel)
    · exact v3456_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 76 Primitive.Addresses.material3456
    · exact v3456_mb_checked.trans (by decide +kernel)
    · exact v3456_mg_checked.trans (by decide +kernel)
  upper_error := v3456_upper_checked
  lower_error := reuse_lower_error 46 76 Primitive.Addresses.material3456

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
