import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B134
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B135

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3233_pa : Scalar.QComplex := ((999999262936640445508018786016 : Int)/10^30,(-1214135979141787876155813662 : Int)/10^30)
theorem v3233_pa_checked : Scalar.distance (sourceCoefficient 42 63 1 0) v3233_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3233_pb : Scalar.QComplex := ((-523872376901141728430295 : Int)/10^30,(-431477198414222593682742936 : Int)/10^30)
theorem v3233_pb_checked : Scalar.distance (sourceCoefficient 42 63 1 1) v3233_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3233_pg : Scalar.QComplex := ((-93086360794477770501412 : Int)/10^30,(113019583110542625982 : Int)/10^30)
theorem v3233_pg_checked : Scalar.distance (sourceCoefficient 42 63 1 2) v3233_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3233_mb : Scalar.QComplex := ((-896217571059358480291677 : Int)/10^30,(-431476585677275212245352802 : Int)/10^30)
theorem v3233_mb_checked : Scalar.distance (sourceCoefficient 42 63 3 1) v3233_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3233_mg : Scalar.QComplex := ((-93086228603361378531899 : Int)/10^30,(193348877939761926652 : Int)/10^30)
theorem v3233_mg_checked : Scalar.distance (sourceCoefficient 42 63 3 2) v3233_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3233_upper : Scalar.QComplex := ((999995678066652023387159004799 : Int)/10^30,(-2940042179433036863664203630 : Int)/10^30)
theorem v3233_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 63 5) 1) 14) v3233_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3233 : Material (42 : Basis) (63 : Basis) where
  plus := ![v3233_pa,v3233_pb,v3233_pg]
  minus := ![(Primitive.Addresses.material3233 1).one,v3233_mb,v3233_mg]
  upper := v3233_upper
  lower := (Primitive.Addresses.material3233 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3233_pa_checked.trans (by decide +kernel)
    · exact v3233_pb_checked.trans (by decide +kernel)
    · exact v3233_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 63 Primitive.Addresses.material3233
    · exact v3233_mb_checked.trans (by decide +kernel)
    · exact v3233_mg_checked.trans (by decide +kernel)
  upper_error := v3233_upper_checked
  lower_error := reuse_lower_error 42 63 Primitive.Addresses.material3233

def v3234_pa : Scalar.QComplex := ((999999219283074535788253174201 : Int)/10^30,(-1249573223708601154883231272 : Int)/10^30)
theorem v3234_pa_checked : Scalar.distance (sourceCoefficient 42 64 1 0) v3234_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3234_pb : Scalar.QComplex := ((-539162749459694854958347 : Int)/10^30,(-431477178204918644589524409 : Int)/10^30)
theorem v3234_pb_checked : Scalar.distance (sourceCoefficient 42 64 1 1) v3234_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3234_pg : Scalar.QComplex := ((-93086356582735276377902 : Int)/10^30,(116318309490049845504 : Int)/10^30)
theorem v3234_pg_checked : Scalar.distance (sourceCoefficient 42 64 1 2) v3234_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3234_mb : Scalar.QComplex := ((-911507920484887983917287 : Int)/10^30,(-431476552273075922784300203 : Int)/10^30)
theorem v3234_mb_checked : Scalar.distance (sourceCoefficient 42 64 3 1) v3234_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3234_mg : Scalar.QComplex := ((-93086221544968156238864 : Int)/10^30,(196647599456458473252 : Int)/10^30)
theorem v3234_mg_checked : Scalar.distance (sourceCoefficient 42 64 3 2) v3234_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3234_upper : Scalar.QComplex := ((999995573251681849920324758352 : Int)/10^30,(-2975479295878142571674849849 : Int)/10^30)
theorem v3234_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 64 5) 1) 14) v3234_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3234 : Material (42 : Basis) (64 : Basis) where
  plus := ![v3234_pa,v3234_pb,v3234_pg]
  minus := ![(Primitive.Addresses.material3234 1).one,v3234_mb,v3234_mg]
  upper := v3234_upper
  lower := (Primitive.Addresses.material3234 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3234_pa_checked.trans (by decide +kernel)
    · exact v3234_pb_checked.trans (by decide +kernel)
    · exact v3234_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 64 Primitive.Addresses.material3234
    · exact v3234_mb_checked.trans (by decide +kernel)
    · exact v3234_mg_checked.trans (by decide +kernel)
  upper_error := v3234_upper_checked
  lower_error := reuse_lower_error 42 64 Primitive.Addresses.material3234

def v3235_pa : Scalar.QComplex := ((999999173693352320261132206729 : Int)/10^30,(-1285539813687931539925474806 : Int)/10^30)
theorem v3235_pa_checked : Scalar.distance (sourceCoefficient 42 65 1 0) v3235_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3235_pb : Scalar.QComplex := ((-554681522299561644790311 : Int)/10^30,(-431477156955002589654131757 : Int)/10^30)
theorem v3235_pb_checked : Scalar.distance (sourceCoefficient 42 65 1 1) v3235_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3235_pg : Scalar.QComplex := ((-93086352168627655012488 : Int)/10^30,(119666310704814816382 : Int)/10^30)
theorem v3235_pg_checked : Scalar.distance (sourceCoefficient 42 65 1 2) v3235_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3235_mb : Scalar.QComplex := ((-927026669208685907792858 : Int)/10^30,(-431476517631165758941635008 : Int)/10^30)
theorem v3235_mb_checked : Scalar.distance (sourceCoefficient 42 65 3 1) v3235_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3235_mg : Scalar.QComplex := ((-93086214241687918482468 : Int)/10^30,(199995595615433507448 : Int)/10^30)
theorem v3235_mg_checked : Scalar.distance (sourceCoefficient 42 65 3 2) v3235_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3235_upper : Scalar.QComplex := ((999995465586956094159687779332 : Int)/10^30,(-3011445753605737438240733646 : Int)/10^30)
theorem v3235_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 65 5) 1) 14) v3235_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3235 : Material (42 : Basis) (65 : Basis) where
  plus := ![v3235_pa,v3235_pb,v3235_pg]
  minus := ![(Primitive.Addresses.material3235 1).one,v3235_mb,v3235_mg]
  upper := v3235_upper
  lower := (Primitive.Addresses.material3235 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3235_pa_checked.trans (by decide +kernel)
    · exact v3235_pb_checked.trans (by decide +kernel)
    · exact v3235_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 65 Primitive.Addresses.material3235
    · exact v3235_mb_checked.trans (by decide +kernel)
    · exact v3235_mg_checked.trans (by decide +kernel)
  upper_error := v3235_upper_checked
  lower_error := reuse_lower_error 42 65 Primitive.Addresses.material3235

def v3236_pa : Scalar.QComplex := ((999999150929174213954779357171 : Int)/10^30,(-1303127365475387152606879725 : Int)/10^30)
theorem v3236_pa_checked : Scalar.distance (sourceCoefficient 42 66 1 0) v3236_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3236_pb : Scalar.QComplex := ((-562270154318719680379448 : Int)/10^30,(-431477146292923367583424172 : Int)/10^30)
theorem v3236_pb_checked : Scalar.distance (sourceCoefficient 42 66 1 1) v3236_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3236_pg : Scalar.QComplex := ((-93086349958997689402378 : Int)/10^30,(121303472979028544905 : Int)/10^30)
theorem v3236_pg_checked : Scalar.distance (sourceCoefficient 42 66 1 2) v3236_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3236_mb : Scalar.QComplex := ((-934615289201355258608242 : Int)/10^30,(-431476500420442853615617111 : Int)/10^30)
theorem v3236_mb_checked : Scalar.distance (sourceCoefficient 42 66 3 1) v3236_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3236_mg : Scalar.QComplex := ((-93086210619261468023788 : Int)/10^30,(201632755373245756986 : Int)/10^30)
theorem v3236_mg_checked : Scalar.distance (sourceCoefficient 42 66 3 2) v3236_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3236_upper : Scalar.QComplex := ((999995412468293037508728344589 : Int)/10^30,(-3029033239909694381088036278 : Int)/10^30)
theorem v3236_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 66 5) 1) 14) v3236_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3236 : Material (42 : Basis) (66 : Basis) where
  plus := ![v3236_pa,v3236_pb,v3236_pg]
  minus := ![(Primitive.Addresses.material3236 1).one,v3236_mb,v3236_mg]
  upper := v3236_upper
  lower := (Primitive.Addresses.material3236 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3236_pa_checked.trans (by decide +kernel)
    · exact v3236_pb_checked.trans (by decide +kernel)
    · exact v3236_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 66 Primitive.Addresses.material3236
    · exact v3236_mb_checked.trans (by decide +kernel)
    · exact v3236_mg_checked.trans (by decide +kernel)
  upper_error := v3236_upper_checked
  lower_error := reuse_lower_error 42 66 Primitive.Addresses.material3236

def v3237_pa : Scalar.QComplex := ((999999112028930941436520647544 : Int)/10^30,(-1332644494838930204964699759 : Int)/10^30)
theorem v3237_pa_checked : Scalar.distance (sourceCoefficient 42 67 1 0) v3237_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3237_pb : Scalar.QComplex := ((-575006129865376019165496 : Int)/10^30,(-431477127998841206296027415 : Int)/10^30)
theorem v3237_pb_checked : Scalar.distance (sourceCoefficient 42 67 1 1) v3237_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3237_pg : Scalar.QComplex := ((-93086346175083909218726 : Int)/10^30,(124051116928699396170 : Int)/10^30)
theorem v3237_pg_checked : Scalar.distance (sourceCoefficient 42 67 1 2) v3237_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3237_mb : Scalar.QComplex := ((-947351244218856868220786 : Int)/10^30,(-431476471135794214331996465 : Int)/10^30)
theorem v3237_mb_checked : Scalar.distance (sourceCoefficient 42 67 3 1) v3237_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3237_mg : Scalar.QComplex := ((-93086204464256117487929 : Int)/10^30,(204380395034496021109 : Int)/10^30)
theorem v3237_mg_checked : Scalar.distance (sourceCoefficient 42 67 3 2) v3237_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3237_upper : Scalar.QComplex := ((999995322624220193916217533360 : Int)/10^30,(-3058550258172649686165972823 : Int)/10^30)
theorem v3237_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 67 5) 1) 14) v3237_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3237 : Material (42 : Basis) (67 : Basis) where
  plus := ![v3237_pa,v3237_pb,v3237_pg]
  minus := ![(Primitive.Addresses.material3237 1).one,v3237_mb,v3237_mg]
  upper := v3237_upper
  lower := (Primitive.Addresses.material3237 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3237_pa_checked.trans (by decide +kernel)
    · exact v3237_pb_checked.trans (by decide +kernel)
    · exact v3237_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 67 Primitive.Addresses.material3237
    · exact v3237_mb_checked.trans (by decide +kernel)
    · exact v3237_mg_checked.trans (by decide +kernel)
  upper_error := v3237_upper_checked
  lower_error := reuse_lower_error 42 67 Primitive.Addresses.material3237

def v3238_pa : Scalar.QComplex := ((999999045310562880873162995813 : Int)/10^30,(-1381802432624263520902325890 : Int)/10^30)
theorem v3238_pa_checked : Scalar.distance (sourceCoefficient 42 68 1 0) v3238_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3238_pb : Scalar.QComplex := ((-596216670655616789057281 : Int)/10^30,(-431477096419311895093863445 : Int)/10^30)
theorem v3238_pb_checked : Scalar.distance (sourceCoefficient 42 68 1 1) v3238_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3238_pg : Scalar.QComplex := ((-93086339663332150856405 : Int)/10^30,(128627053389770032395 : Int)/10^30)
theorem v3238_pg_checked : Scalar.distance (sourceCoefficient 42 68 1 2) v3238_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3238_mb : Scalar.QComplex := ((-968561749859732425938840 : Int)/10^30,(-431476421252535246949327569 : Int)/10^30)
theorem v3238_mb_checked : Scalar.distance (sourceCoefficient 42 68 3 1) v3238_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3238_mg : Scalar.QComplex := ((-93086194003679710372122 : Int)/10^30,(208956324172387893195 : Int)/10^30)
theorem v3238_mg_checked : Scalar.distance (sourceCoefficient 42 68 3 2) v3238_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3238_upper : Scalar.QComplex := ((999995171063810458319103467230 : Int)/10^30,(-3107708007593158538395626987 : Int)/10^30)
theorem v3238_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 68 5) 1) 14) v3238_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3238 : Material (42 : Basis) (68 : Basis) where
  plus := ![v3238_pa,v3238_pb,v3238_pg]
  minus := ![(Primitive.Addresses.material3238 1).one,v3238_mb,v3238_mg]
  upper := v3238_upper
  lower := (Primitive.Addresses.material3238 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3238_pa_checked.trans (by decide +kernel)
    · exact v3238_pb_checked.trans (by decide +kernel)
    · exact v3238_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 68 Primitive.Addresses.material3238
    · exact v3238_mb_checked.trans (by decide +kernel)
    · exact v3238_mg_checked.trans (by decide +kernel)
  upper_error := v3238_upper_checked
  lower_error := reuse_lower_error 42 68 Primitive.Addresses.material3238

def v3239_pa : Scalar.QComplex := ((999999015180686655642616999918 : Int)/10^30,(-1403437799412440946653769415 : Int)/10^30)
theorem v3239_pa_checked : Scalar.distance (sourceCoefficient 42 69 1 0) v3239_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3239_pb : Scalar.QComplex := ((-605551842930358584541550 : Int)/10^30,(-431477082079965853380287308 : Int)/10^30)
theorem v3239_pb_checked : Scalar.distance (sourceCoefficient 42 69 1 1) v3239_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3239_pg : Scalar.QComplex := ((-93086336714214403082416 : Int)/10^30,(130641012211354511309 : Int)/10^30)
theorem v3239_pg_checked : Scalar.distance (sourceCoefficient 42 69 1 2) v3239_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3239_mb : Scalar.QComplex := ((-977896906284353131260348 : Int)/10^30,(-431476398857361311879221200 : Int)/10^30)
theorem v3239_mb_checked : Scalar.distance (sourceCoefficient 42 69 3 1) v3239_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3239_mg : Scalar.QComplex := ((-93086189316607303000230 : Int)/10^30,(210970279699127667372 : Int)/10^30)
theorem v3239_mg_checked : Scalar.distance (sourceCoefficient 42 69 3 2) v3239_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3239_upper : Scalar.QComplex := ((999995103593298776748554023299 : Int)/10^30,(-3129343290156565598139559942 : Int)/10^30)
theorem v3239_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 69 5) 1) 14) v3239_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3239 : Material (42 : Basis) (69 : Basis) where
  plus := ![v3239_pa,v3239_pb,v3239_pg]
  minus := ![(Primitive.Addresses.material3239 1).one,v3239_mb,v3239_mg]
  upper := v3239_upper
  lower := (Primitive.Addresses.material3239 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3239_pa_checked.trans (by decide +kernel)
    · exact v3239_pb_checked.trans (by decide +kernel)
    · exact v3239_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 69 Primitive.Addresses.material3239
    · exact v3239_mb_checked.trans (by decide +kernel)
    · exact v3239_mg_checked.trans (by decide +kernel)
  upper_error := v3239_upper_checked
  lower_error := reuse_lower_error 42 69 Primitive.Addresses.material3239

def v3240_pa : Scalar.QComplex := ((999998995105733050385526350202 : Int)/10^30,(-1417669751418411691821973670 : Int)/10^30)
theorem v3240_pa_checked : Scalar.distance (sourceCoefficient 42 70 1 0) v3240_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3240_pb : Scalar.QComplex := ((-611692608801023888467287 : Int)/10^30,(-431477072500570774312680731 : Int)/10^30)
theorem v3240_pb_checked : Scalar.distance (sourceCoefficient 42 70 1 1) v3240_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3240_pg : Scalar.QComplex := ((-93086334746538064165620 : Int)/10^30,(131965813652265248847 : Int)/10^30)
theorem v3240_pg_checked : Scalar.distance (sourceCoefficient 42 70 1 2) v3240_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3240_mb : Scalar.QComplex := ((-984037661601944141376079 : Int)/10^30,(-431476383978765423102105409 : Int)/10^30)
theorem v3240_mb_checked : Scalar.distance (sourceCoefficient 42 70 3 1) v3240_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3240_mg : Scalar.QComplex := ((-93086186205687720075257 : Int)/10^30,(212295078948738222409 : Int)/10^30)
theorem v3240_mg_checked : Scalar.distance (sourceCoefficient 42 70 3 2) v3240_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3240_upper : Scalar.QComplex := ((999995058955317021071546055299 : Int)/10^30,(-3143575186318166895825691966 : Int)/10^30)
theorem v3240_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 70 5) 1) 14) v3240_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3240 : Material (42 : Basis) (70 : Basis) where
  plus := ![v3240_pa,v3240_pb,v3240_pg]
  minus := ![(Primitive.Addresses.material3240 1).one,v3240_mb,v3240_mg]
  upper := v3240_upper
  lower := (Primitive.Addresses.material3240 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3240_pa_checked.trans (by decide +kernel)
    · exact v3240_pb_checked.trans (by decide +kernel)
    · exact v3240_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 70 Primitive.Addresses.material3240
    · exact v3240_mb_checked.trans (by decide +kernel)
    · exact v3240_mg_checked.trans (by decide +kernel)
  upper_error := v3240_upper_checked
  lower_error := reuse_lower_error 42 70 Primitive.Addresses.material3240

def v3241_pa : Scalar.QComplex := ((999998960371471744097556346604 : Int)/10^30,(-1441962543093380121443392354 : Int)/10^30)
theorem v3241_pa_checked : Scalar.distance (sourceCoefficient 42 71 1 0) v3241_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3241_pb : Scalar.QComplex := ((-622174399613585401575754 : Int)/10^30,(-431477055880111466200632813 : Int)/10^30)
theorem v3241_pb_checked : Scalar.distance (sourceCoefficient 42 71 1 1) v3241_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3241_pg : Scalar.QComplex := ((-93086331337055145982189 : Int)/10^30,(134227142608379763302 : Int)/10^30)
theorem v3241_pg_checked : Scalar.distance (sourceCoefficient 42 71 1 2) v3241_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3241_mb : Scalar.QComplex := ((-994519434168948068261403 : Int)/10^30,(-431476358312998914639742401 : Int)/10^30)
theorem v3241_mb_checked : Scalar.distance (sourceCoefficient 42 71 3 1) v3241_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3241_mg : Scalar.QComplex := ((-93086180844781028746776 : Int)/10^30,(214556404120626417682 : Int)/10^30)
theorem v3241_mg_checked : Scalar.distance (sourceCoefficient 42 71 3 2) v3241_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3241_upper : Scalar.QComplex := ((999994982293952841235527484924 : Int)/10^30,(-3167867881863691810266356110 : Int)/10^30)
theorem v3241_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 71 5) 1) 14) v3241_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3241 : Material (42 : Basis) (71 : Basis) where
  plus := ![v3241_pa,v3241_pb,v3241_pg]
  minus := ![(Primitive.Addresses.material3241 1).one,v3241_mb,v3241_mg]
  upper := v3241_upper
  lower := (Primitive.Addresses.material3241 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3241_pa_checked.trans (by decide +kernel)
    · exact v3241_pb_checked.trans (by decide +kernel)
    · exact v3241_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 71 Primitive.Addresses.material3241
    · exact v3241_mb_checked.trans (by decide +kernel)
    · exact v3241_mg_checked.trans (by decide +kernel)
  upper_error := v3241_upper_checked
  lower_error := reuse_lower_error 42 71 Primitive.Addresses.material3241

def v3242_pa : Scalar.QComplex := ((999998922010058602323756988143 : Int)/10^30,(-1468325141354270597595367625 : Int)/10^30)
theorem v3242_pa_checked : Scalar.distance (sourceCoefficient 42 72 1 0) v3242_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3242_pb : Scalar.QComplex := ((-633549264978451420251725 : Int)/10^30,(-431477037459414287642845122 : Int)/10^30)
theorem v3242_pb_checked : Scalar.distance (sourceCoefficient 42 72 1 1) v3242_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3242_pg : Scalar.QComplex := ((-93086327564562367730445 : Int)/10^30,(136681142420282681903 : Int)/10^30)
theorem v3242_pg_checked : Scalar.distance (sourceCoefficient 42 72 1 2) v3242_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3242_mb : Scalar.QComplex := ((-1005894279402199826877085 : Int)/10^30,(-431476330076312089988388682 : Int)/10^30)
theorem v3242_mb_checked : Scalar.distance (sourceCoefficient 42 72 3 1) v3242_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3242_mg : Scalar.QComplex := ((-93086174954598341542969 : Int)/10^30,(217010399763301692116 : Int)/10^30)
theorem v3242_mg_checked : Scalar.distance (sourceCoefficient 42 72 3 2) v3242_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3242_upper : Scalar.QComplex := ((999994898433143832215496289671 : Int)/10^30,(-3194230374652269982663238423 : Int)/10^30)
theorem v3242_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 72 5) 1) 14) v3242_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3242 : Material (42 : Basis) (72 : Basis) where
  plus := ![v3242_pa,v3242_pb,v3242_pg]
  minus := ![(Primitive.Addresses.material3242 1).one,v3242_mb,v3242_mg]
  upper := v3242_upper
  lower := (Primitive.Addresses.material3242 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3242_pa_checked.trans (by decide +kernel)
    · exact v3242_pb_checked.trans (by decide +kernel)
    · exact v3242_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 72 Primitive.Addresses.material3242
    · exact v3242_mb_checked.trans (by decide +kernel)
    · exact v3242_mg_checked.trans (by decide +kernel)
  upper_error := v3242_upper_checked
  lower_error := reuse_lower_error 42 72 Primitive.Addresses.material3242

def v3243_pa : Scalar.QComplex := ((999998908090262926964445985886 : Int)/10^30,(-1477774773732180472668857274 : Int)/10^30)
theorem v3243_pa_checked : Scalar.distance (sourceCoefficient 42 73 1 0) v3243_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3243_pb : Scalar.QComplex := ((-637626567731466110929889 : Int)/10^30,(-431477030759198872963577409 : Int)/10^30)
theorem v3243_pb_checked : Scalar.distance (sourceCoefficient 42 73 1 1) v3243_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3243_pg : Scalar.QComplex := ((-93086326193942207655997 : Int)/10^30,(137560774832762369410 : Int)/10^30)
theorem v3243_pg_checked : Scalar.distance (sourceCoefficient 42 73 1 2) v3243_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3243_mb : Scalar.QComplex := ((-1009971574855064224298559 : Int)/10^30,(-431476319857570529153004668 : Int)/10^30)
theorem v3243_mb_checked : Scalar.distance (sourceCoefficient 42 73 3 1) v3243_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3243_mg : Scalar.QComplex := ((-93086172824895537016276 : Int)/10^30,(217890030665470563566 : Int)/10^30)
theorem v3243_mg_checked : Scalar.distance (sourceCoefficient 42 73 3 2) v3243_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3243_upper : Scalar.QComplex := ((999994868204160668437010778807 : Int)/10^30,(-3203679968931757920963651543 : Int)/10^30)
theorem v3243_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 73 5) 1) 14) v3243_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3243 : Material (42 : Basis) (73 : Basis) where
  plus := ![v3243_pa,v3243_pb,v3243_pg]
  minus := ![(Primitive.Addresses.material3243 1).one,v3243_mb,v3243_mg]
  upper := v3243_upper
  lower := (Primitive.Addresses.material3243 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3243_pa_checked.trans (by decide +kernel)
    · exact v3243_pb_checked.trans (by decide +kernel)
    · exact v3243_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 73 Primitive.Addresses.material3243
    · exact v3243_mb_checked.trans (by decide +kernel)
    · exact v3243_mg_checked.trans (by decide +kernel)
  upper_error := v3243_upper_checked
  lower_error := reuse_lower_error 42 73 Primitive.Addresses.material3243

def v3244_pa : Scalar.QComplex := ((999998892320299344828609360342 : Int)/10^30,(-1488407932777846873616423228 : Int)/10^30)
theorem v3244_pa_checked : Scalar.distance (sourceCoefficient 42 74 1 0) v3244_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3244_pb : Scalar.QComplex := ((-642214535448312957419453 : Int)/10^30,(-431477023158383384731337783 : Int)/10^30)
theorem v3244_pb_checked : Scalar.distance (sourceCoefficient 42 74 1 1) v3244_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3244_pg : Scalar.QComplex := ((-93086324640062108673788 : Int)/10^30,(138550577497064601670 : Int)/10^30)
theorem v3244_pg_checked : Scalar.distance (sourceCoefficient 42 74 1 2) v3244_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3244_mb : Scalar.QComplex := ((-1014559534304439571000309 : Int)/10^30,(-431476308297548365808254684 : Int)/10^30)
theorem v3244_mb_checked : Scalar.distance (sourceCoefficient 42 74 3 1) v3244_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3244_mg : Scalar.QComplex := ((-93086170416860896378965 : Int)/10^30,(218879831620295486430 : Int)/10^30)
theorem v3244_mg_checked : Scalar.distance (sourceCoefficient 42 74 3 2) v3244_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3244_upper : Scalar.QComplex := ((999994834082352693642577750886 : Int)/10^30,(-3214313084923056479148370155 : Int)/10^30)
theorem v3244_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 74 5) 1) 14) v3244_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3244 : Material (42 : Basis) (74 : Basis) where
  plus := ![v3244_pa,v3244_pb,v3244_pg]
  minus := ![(Primitive.Addresses.material3244 1).one,v3244_mb,v3244_mg]
  upper := v3244_upper
  lower := (Primitive.Addresses.material3244 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3244_pa_checked.trans (by decide +kernel)
    · exact v3244_pb_checked.trans (by decide +kernel)
    · exact v3244_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 74 Primitive.Addresses.material3244
    · exact v3244_mb_checked.trans (by decide +kernel)
    · exact v3244_mg_checked.trans (by decide +kernel)
  upper_error := v3244_upper_checked
  lower_error := reuse_lower_error 42 74 Primitive.Addresses.material3244

def v3245_pa : Scalar.QComplex := ((999998870159600003098190766856 : Int)/10^30,(-1503223045144822862360467931 : Int)/10^30)
theorem v3245_pa_checked : Scalar.distance (sourceCoefficient 42 75 1 0) v3245_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3245_pb : Scalar.QComplex := ((-648606921402062803973776 : Int)/10^30,(-431477012459765443737538379 : Int)/10^30)
theorem v3245_pb_checked : Scalar.distance (sourceCoefficient 42 75 1 1) v3245_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3245_pg : Scalar.QComplex := ((-93086322454578575239046 : Int)/10^30,(139929663199691148698 : Int)/10^30)
theorem v3245_pg_checked : Scalar.distance (sourceCoefficient 42 75 1 2) v3245_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3245_mb : Scalar.QComplex := ((-1020951908645586545290530 : Int)/10^30,(-431476292082593232688666462 : Int)/10^30)
theorem v3245_mb_checked : Scalar.distance (sourceCoefficient 42 75 3 1) v3245_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3245_mg : Scalar.QComplex := ((-93086167041289327047265 : Int)/10^30,(220258914923451540210 : Int)/10^30)
theorem v3245_mg_checked : Scalar.distance (sourceCoefficient 42 75 3 2) v3245_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3245_upper : Scalar.QComplex := ((999994786352146428765144848674 : Int)/10^30,(-3229128136977306241743261021 : Int)/10^30)
theorem v3245_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 75 5) 1) 14) v3245_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3245 : Material (42 : Basis) (75 : Basis) where
  plus := ![v3245_pa,v3245_pb,v3245_pg]
  minus := ![(Primitive.Addresses.material3245 1).one,v3245_mb,v3245_mg]
  upper := v3245_upper
  lower := (Primitive.Addresses.material3245 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3245_pa_checked.trans (by decide +kernel)
    · exact v3245_pb_checked.trans (by decide +kernel)
    · exact v3245_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 75 Primitive.Addresses.material3245
    · exact v3245_mb_checked.trans (by decide +kernel)
    · exact v3245_mg_checked.trans (by decide +kernel)
  upper_error := v3245_upper_checked
  lower_error := reuse_lower_error 42 75 Primitive.Addresses.material3245

def v3246_pa : Scalar.QComplex := ((999998851397004841991343684590 : Int)/10^30,(-1515653215952507002327406950 : Int)/10^30)
theorem v3246_pa_checked : Scalar.distance (sourceCoefficient 42 76 1 0) v3246_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3246_pb : Scalar.QComplex := ((-653970258943735397970613 : Int)/10^30,(-431477003385997082366383088 : Int)/10^30)
theorem v3246_pb_checked : Scalar.distance (sourceCoefficient 42 76 1 1) v3246_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3246_pg : Scalar.QComplex := ((-93086320602525260363129 : Int)/10^30,(141086743235059377061 : Int)/10^30)
theorem v3246_pg_checked : Scalar.distance (sourceCoefficient 42 76 1 2) v3246_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3246_mb : Scalar.QComplex := ((-1026315236359990027381242 : Int)/10^30,(-431476278380509507188620969 : Int)/10^30)
theorem v3246_mb_checked : Scalar.distance (sourceCoefficient 42 76 3 1) v3246_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3246_mg : Scalar.QComplex := ((-93086164190728744202928 : Int)/10^30,(221415992929747392882 : Int)/10^30)
theorem v3246_mg_checked : Scalar.distance (sourceCoefficient 42 76 3 2) v3246_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3246_upper : Scalar.QComplex := ((999994746136232054563861004151 : Int)/10^30,(-3241558256889173995364010592 : Int)/10^30)
theorem v3246_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 76 5) 1) 14) v3246_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3246 : Material (42 : Basis) (76 : Basis) where
  plus := ![v3246_pa,v3246_pb,v3246_pg]
  minus := ![(Primitive.Addresses.material3246 1).one,v3246_mb,v3246_mg]
  upper := v3246_upper
  lower := (Primitive.Addresses.material3246 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3246_pa_checked.trans (by decide +kernel)
    · exact v3246_pb_checked.trans (by decide +kernel)
    · exact v3246_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 76 Primitive.Addresses.material3246
    · exact v3246_mb_checked.trans (by decide +kernel)
    · exact v3246_mg_checked.trans (by decide +kernel)
  upper_error := v3246_upper_checked
  lower_error := reuse_lower_error 42 76 Primitive.Addresses.material3246

def v3247_pa : Scalar.QComplex := ((999998847031278982312131987557 : Int)/10^30,(-1518530906072874135778905640 : Int)/10^30)
theorem v3247_pa_checked : Scalar.distance (sourceCoefficient 42 77 1 0) v3247_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3247_pb : Scalar.QComplex := ((-655211917131042122218832 : Int)/10^30,(-431477001272671179020234968 : Int)/10^30)
theorem v3247_pb_checked : Scalar.distance (sourceCoefficient 42 77 1 1) v3247_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3247_pg : Scalar.QComplex := ((-93086320171367177175658 : Int)/10^30,(141354617090267936462 : Int)/10^30)
theorem v3247_pg_checked : Scalar.distance (sourceCoefficient 42 77 1 2) v3247_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3247_mb : Scalar.QComplex := ((-1027556892261265587990358 : Int)/10^30,(-431476275195689297293413727 : Int)/10^30)
theorem v3247_mb_checked : Scalar.distance (sourceCoefficient 42 77 3 1) v3247_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3247_mg : Scalar.QComplex := ((-93086163528407749100911 : Int)/10^30,(221683866313144266397 : Int)/10^30)
theorem v3247_mg_checked : Scalar.distance (sourceCoefficient 42 77 3 2) v3247_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3247_upper : Scalar.QComplex := ((999994736803880611375225988260 : Int)/10^30,(-3244435935188712953505876907 : Int)/10^30)
theorem v3247_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 77 5) 1) 14) v3247_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3247 : Material (42 : Basis) (77 : Basis) where
  plus := ![v3247_pa,v3247_pb,v3247_pg]
  minus := ![(Primitive.Addresses.material3247 1).one,v3247_mb,v3247_mg]
  upper := v3247_upper
  lower := (Primitive.Addresses.material3247 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3247_pa_checked.trans (by decide +kernel)
    · exact v3247_pb_checked.trans (by decide +kernel)
    · exact v3247_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 77 Primitive.Addresses.material3247
    · exact v3247_mb_checked.trans (by decide +kernel)
    · exact v3247_mg_checked.trans (by decide +kernel)
  upper_error := v3247_upper_checked
  lower_error := reuse_lower_error 42 77 Primitive.Addresses.material3247

def v3248_pa : Scalar.QComplex := ((999998820611680319114383390257 : Int)/10^30,(-1535830475151786611895951713 : Int)/10^30)
theorem v3248_pa_checked : Scalar.distance (sourceCoefficient 42 78 1 0) v3248_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3248_pb : Scalar.QComplex := ((-662676289768176445097249 : Int)/10^30,(-431476988467759199044014132 : Int)/10^30)
theorem v3248_pb_checked : Scalar.distance (sourceCoefficient 42 78 1 1) v3248_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3248_pg : Scalar.QComplex := ((-93086317560456133813984 : Int)/10^30,(142964971940223471774 : Int)/10^30)
theorem v3248_pg_checked : Scalar.distance (sourceCoefficient 42 78 1 2) v3248_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3248_mb : Scalar.QComplex := ((-1035021251069010512489107 : Int)/10^30,(-431476255949364682188097789 : Int)/10^30)
theorem v3248_mb_checked : Scalar.distance (sourceCoefficient 42 78 3 1) v3248_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3248_mg : Scalar.QComplex := ((-93086159527833970079203 : Int)/10^30,(223294218310392454866 : Int)/10^30)
theorem v3248_mg_checked : Scalar.distance (sourceCoefficient 42 78 3 2) v3248_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3248_upper : Scalar.QComplex := ((999994680526834471510610998027 : Int)/10^30,(-3261735432904118911306452775 : Int)/10^30)
theorem v3248_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 78 5) 1) 14) v3248_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3248 : Material (42 : Basis) (78 : Basis) where
  plus := ![v3248_pa,v3248_pb,v3248_pg]
  minus := ![(Primitive.Addresses.material3248 1).one,v3248_mb,v3248_mg]
  upper := v3248_upper
  lower := (Primitive.Addresses.material3248 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3248_pa_checked.trans (by decide +kernel)
    · exact v3248_pb_checked.trans (by decide +kernel)
    · exact v3248_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 78 Primitive.Addresses.material3248
    · exact v3248_mb_checked.trans (by decide +kernel)
    · exact v3248_mg_checked.trans (by decide +kernel)
  upper_error := v3248_upper_checked
  lower_error := reuse_lower_error 42 78 Primitive.Addresses.material3248

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
