import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B128
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B129

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3089_pa : Scalar.QComplex := ((999998587616922200357372412318 : Int)/10^30,(-1680703471994190532731871051 : Int)/10^30)
theorem v3089_pa_checked : Scalar.distance (sourceCoefficient 39 87 1 0) v3089_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3089_pb : Scalar.QComplex := ((-725185687117108984521260 : Int)/10^30,(-431476863682960779012864558 : Int)/10^30)
theorem v3089_pb_checked : Scalar.distance (sourceCoefficient 39 87 1 1) v3089_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3089_pg : Scalar.QComplex := ((-93086293255671509082990 : Int)/10^30,(156450677238165548712 : Int)/10^30)
theorem v3089_pg_checked : Scalar.distance (sourceCoefficient 39 87 1 2) v3089_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3089_mb : Scalar.QComplex := ((-1097530517459176660522973 : Int)/10^30,(-431476077221818131858617006 : Int)/10^30)
theorem v3089_mb_checked : Scalar.distance (sourceCoefficient 39 87 3 1) v3089_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3089_mg : Scalar.QComplex := ((-93086123585502096626146 : Int)/10^30,(236779897613055637922 : Int)/10^30)
theorem v3089_mg_checked : Scalar.distance (sourceCoefficient 39 87 3 2) v3089_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3089_upper : Scalar.QComplex := ((999994197494773596694977621128 : Int)/10^30,(-3406607811847396619406387272 : Int)/10^30)
theorem v3089_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 87 5) 1) 14) v3089_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3089 : Material (39 : Basis) (87 : Basis) where
  plus := ![v3089_pa,v3089_pb,v3089_pg]
  minus := ![(Primitive.Addresses.material3089 1).one,v3089_mb,v3089_mg]
  upper := v3089_upper
  lower := (Primitive.Addresses.material3089 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3089_pa_checked.trans (by decide +kernel)
    · exact v3089_pb_checked.trans (by decide +kernel)
    · exact v3089_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 87 Primitive.Addresses.material3089
    · exact v3089_mb_checked.trans (by decide +kernel)
    · exact v3089_mg_checked.trans (by decide +kernel)
  upper_error := v3089_upper_checked
  lower_error := reuse_lower_error 39 87 Primitive.Addresses.material3089

def v3090_pa : Scalar.QComplex := ((999998567783388560303460311221 : Int)/10^30,(-1692463048824100914400501413 : Int)/10^30)
theorem v3090_pa_checked : Scalar.distance (sourceCoefficient 39 88 1 0) v3090_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3090_pb : Scalar.QComplex := ((-730259677259141759712053 : Int)/10^30,(-431476853734841988037357237 : Int)/10^30)
theorem v3090_pb_checked : Scalar.distance (sourceCoefficient 39 88 1 1) v3090_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3090_pg : Scalar.QComplex := ((-93086291259457629120318 : Int)/10^30,(157545333947754250341 : Int)/10^30)
theorem v3090_pg_checked : Scalar.distance (sourceCoefficient 39 88 1 2) v3090_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3090_mb : Scalar.QComplex := ((-1102604497127152543055945 : Int)/10^30,(-431476062895078076480888367 : Int)/10^30)
theorem v3090_mb_checked : Scalar.distance (sourceCoefficient 39 88 3 1) v3090_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3090_mg : Scalar.QComplex := ((-93086120644649521078125 : Int)/10^30,(237874552192410946016 : Int)/10^30)
theorem v3090_mg_checked : Scalar.distance (sourceCoefficient 39 88 3 2) v3090_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3090_upper : Scalar.QComplex := ((999994157365306708410758337832 : Int)/10^30,(-3418367336931918911237919510 : Int)/10^30)
theorem v3090_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 88 5) 1) 14) v3090_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3090 : Material (39 : Basis) (88 : Basis) where
  plus := ![v3090_pa,v3090_pb,v3090_pg]
  minus := ![(Primitive.Addresses.material3090 1).one,v3090_mb,v3090_mg]
  upper := v3090_upper
  lower := (Primitive.Addresses.material3090 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3090_pa_checked.trans (by decide +kernel)
    · exact v3090_pb_checked.trans (by decide +kernel)
    · exact v3090_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 88 Primitive.Addresses.material3090
    · exact v3090_mb_checked.trans (by decide +kernel)
    · exact v3090_mg_checked.trans (by decide +kernel)
  upper_error := v3090_upper_checked
  lower_error := reuse_lower_error 39 88 Primitive.Addresses.material3090

def v3091_pa : Scalar.QComplex := ((999998540423094953444520356058 : Int)/10^30,(-1708552510088106485529815543 : Int)/10^30)
theorem v3091_pa_checked : Scalar.distance (sourceCoefficient 39 89 1 0) v3091_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3091_pb : Scalar.QComplex := ((-737201914021107724094631 : Int)/10^30,(-431476839994928663216714344 : Int)/10^30)
theorem v3091_pb_checked : Scalar.distance (sourceCoefficient 39 89 1 1) v3091_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3091_pg : Scalar.QComplex := ((-93086288503905595781329 : Int)/10^30,(159043044013687506887 : Int)/10^30)
theorem v3091_pg_checked : Scalar.distance (sourceCoefficient 39 89 1 2) v3091_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3091_mb : Scalar.QComplex := ((-1109546719447280108468981 : Int)/10^30,(-431476043164332208818318192 : Int)/10^30)
theorem v3091_mb_checked : Scalar.distance (sourceCoefficient 39 89 3 1) v3091_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3091_mg : Scalar.QComplex := ((-93086116596642181214040 : Int)/10^30,(239372259322760996969 : Int)/10^30)
theorem v3091_mg_checked : Scalar.distance (sourceCoefficient 39 89 3 2) v3091_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3091_upper : Scalar.QComplex := ((999994102236103334345473699927 : Int)/10^30,(-3434456727011177271524658881 : Int)/10^30)
theorem v3091_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 89 5) 1) 14) v3091_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3091 : Material (39 : Basis) (89 : Basis) where
  plus := ![v3091_pa,v3091_pb,v3091_pg]
  minus := ![(Primitive.Addresses.material3091 1).one,v3091_mb,v3091_mg]
  upper := v3091_upper
  lower := (Primitive.Addresses.material3091 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3091_pa_checked.trans (by decide +kernel)
    · exact v3091_pb_checked.trans (by decide +kernel)
    · exact v3091_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 89 Primitive.Addresses.material3091
    · exact v3091_mb_checked.trans (by decide +kernel)
    · exact v3091_mg_checked.trans (by decide +kernel)
  upper_error := v3091_upper_checked
  lower_error := reuse_lower_error 39 89 Primitive.Addresses.material3091

def v3092_pa : Scalar.QComplex := ((999998495310696601695717233253 : Int)/10^30,(-1734755412934834685324902198 : Int)/10^30)
theorem v3092_pa_checked : Scalar.distance (sourceCoefficient 39 90 1 0) v3092_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3092_pb : Scalar.QComplex := ((-748507870638284514086021 : Int)/10^30,(-431476817299670462415777271 : Int)/10^30)
theorem v3092_pb_checked : Scalar.distance (sourceCoefficient 39 90 1 1) v3092_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3092_pg : Scalar.QComplex := ((-93086283956105986480867 : Int)/10^30,(161482177943349758283 : Int)/10^30)
theorem v3092_pg_checked : Scalar.distance (sourceCoefficient 39 90 1 2) v3092_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3092_mb : Scalar.QComplex := ((-1120852652269746871336090 : Int)/10^30,(-431476010712551099259257821 : Int)/10^30)
theorem v3092_mb_checked : Scalar.distance (sourceCoefficient 39 90 3 1) v3092_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3092_mg : Scalar.QComplex := ((-93086109943981538482894 : Int)/10^30,(241811388419675974889 : Int)/10^30)
theorem v3092_mg_checked : Scalar.distance (sourceCoefficient 39 90 3 2) v3092_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3092_upper : Scalar.QComplex := ((999994011899938967539168544889 : Int)/10^30,(-3460659512971852699995495733 : Int)/10^30)
theorem v3092_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 90 5) 1) 14) v3092_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3092 : Material (39 : Basis) (90 : Basis) where
  plus := ![v3092_pa,v3092_pb,v3092_pg]
  minus := ![(Primitive.Addresses.material3092 1).one,v3092_mb,v3092_mg]
  upper := v3092_upper
  lower := (Primitive.Addresses.material3092 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3092_pa_checked.trans (by decide +kernel)
    · exact v3092_pb_checked.trans (by decide +kernel)
    · exact v3092_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 90 Primitive.Addresses.material3092
    · exact v3092_mb_checked.trans (by decide +kernel)
    · exact v3092_mg_checked.trans (by decide +kernel)
  upper_error := v3092_upper_checked
  lower_error := reuse_lower_error 39 90 Primitive.Addresses.material3092

def v3093_pa : Scalar.QComplex := ((999998469594904361271868076852 : Int)/10^30,(-1749516461522354326561789749 : Int)/10^30)
theorem v3093_pa_checked : Scalar.distance (sourceCoefficient 39 91 1 0) v3093_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3093_pb : Scalar.QComplex := ((-754876927226559210584730 : Int)/10^30,(-431476804340670577660121398 : Int)/10^30)
theorem v3093_pb_checked : Scalar.distance (sourceCoefficient 39 91 1 1) v3093_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3093_pg : Scalar.QComplex := ((-93086281361330986082259 : Int)/10^30,(162856230819555573598 : Int)/10^30)
theorem v3093_pg_checked : Scalar.distance (sourceCoefficient 39 91 1 2) v3093_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3093_mb : Scalar.QComplex := ((-1127221695303497470898898 : Int)/10^30,(-431475992257347055710753245 : Int)/10^30)
theorem v3093_mb_checked : Scalar.distance (sourceCoefficient 39 91 3 1) v3093_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3093_mg : Scalar.QComplex := ((-93086106163461757116251 : Int)/10^30,(243185438545085146057 : Int)/10^30)
theorem v3093_mg_checked : Scalar.distance (sourceCoefficient 39 91 3 2) v3093_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3093_upper : Scalar.QComplex := ((999993960707954277575463503222 : Int)/10^30,(-3475420495191399936169361742 : Int)/10^30)
theorem v3093_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 91 5) 1) 14) v3093_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3093 : Material (39 : Basis) (91 : Basis) where
  plus := ![v3093_pa,v3093_pb,v3093_pg]
  minus := ![(Primitive.Addresses.material3093 1).one,v3093_mb,v3093_mg]
  upper := v3093_upper
  lower := (Primitive.Addresses.material3093 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3093_pa_checked.trans (by decide +kernel)
    · exact v3093_pb_checked.trans (by decide +kernel)
    · exact v3093_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 91 Primitive.Addresses.material3093
    · exact v3093_mb_checked.trans (by decide +kernel)
    · exact v3093_mg_checked.trans (by decide +kernel)
  upper_error := v3093_upper_checked
  lower_error := reuse_lower_error 39 91 Primitive.Addresses.material3093

def v3094_pa : Scalar.QComplex := ((999998413176577728692417404542 : Int)/10^30,(-1781472516356635151209705675 : Int)/10^30)
theorem v3094_pa_checked : Scalar.distance (sourceCoefficient 39 92 1 0) v3094_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3094_pb : Scalar.QComplex := ((-768665237370385142413778 : Int)/10^30,(-431476775856419000825723202 : Int)/10^30)
theorem v3094_pb_checked : Scalar.distance (sourceCoefficient 39 92 1 1) v3094_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3094_pg : Scalar.QComplex := ((-93086275662861967164856 : Int)/10^30,(165830904887750126730 : Int)/10^30)
theorem v3094_pg_checked : Scalar.distance (sourceCoefficient 39 92 1 2) v3094_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3094_mb : Scalar.QComplex := ((-1141009975732679151537673 : Int)/10^30,(-431475951874415433179416430 : Int)/10^30)
theorem v3094_mb_checked : Scalar.distance (sourceCoefficient 39 92 3 1) v3094_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3094_mg : Scalar.QComplex := ((-93086097897985113494067 : Int)/10^30,(246160106588150480471 : Int)/10^30)
theorem v3094_mg_checked : Scalar.distance (sourceCoefficient 39 92 3 2) v3094_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3094_upper : Scalar.QComplex := ((999993849136460060146047827536 : Int)/10^30,(-3507376405057977369826982125 : Int)/10^30)
theorem v3094_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 92 5) 1) 14) v3094_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3094 : Material (39 : Basis) (92 : Basis) where
  plus := ![v3094_pa,v3094_pb,v3094_pg]
  minus := ![(Primitive.Addresses.material3094 1).one,v3094_mb,v3094_mg]
  upper := v3094_upper
  lower := (Primitive.Addresses.material3094 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3094_pa_checked.trans (by decide +kernel)
    · exact v3094_pb_checked.trans (by decide +kernel)
    · exact v3094_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 92 Primitive.Addresses.material3094
    · exact v3094_mb_checked.trans (by decide +kernel)
    · exact v3094_mg_checked.trans (by decide +kernel)
  upper_error := v3094_upper_checked
  lower_error := reuse_lower_error 39 92 Primitive.Addresses.material3094

def v3095_pa : Scalar.QComplex := ((999998344893967965217676933338 : Int)/10^30,(-1819398066585096535952098942 : Int)/10^30)
theorem v3095_pa_checked : Scalar.distance (sourceCoefficient 39 93 1 0) v3095_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3095_pb : Scalar.QComplex := ((-785029248184017134565343 : Int)/10^30,(-431476741288850856015139726 : Int)/10^30)
theorem v3095_pb_checked : Scalar.distance (sourceCoefficient 39 93 1 1) v3095_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3095_pg : Scalar.QComplex := ((-93086268755987446654466 : Int)/10^30,(169361257711103470402 : Int)/10^30)
theorem v3095_pg_checked : Scalar.distance (sourceCoefficient 39 93 1 2) v3095_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3095_mb : Scalar.QComplex := ((-1157373950622987602038371 : Int)/10^30,(-431475903185455834977894533 : Int)/10^30)
theorem v3095_mb_checked : Scalar.distance (sourceCoefficient 39 93 3 1) v3095_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3095_mg : Scalar.QComplex := ((-93086087944577679363548 : Int)/10^30,(249690452136670485794 : Int)/10^30)
theorem v3095_mg_checked : Scalar.distance (sourceCoefficient 39 93 3 2) v3095_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3095_upper : Scalar.QComplex := ((999993715397892880313558679436 : Int)/10^30,(-3545301780951196835567208284 : Int)/10^30)
theorem v3095_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 93 5) 1) 14) v3095_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3095 : Material (39 : Basis) (93 : Basis) where
  plus := ![v3095_pa,v3095_pb,v3095_pg]
  minus := ![(Primitive.Addresses.material3095 1).one,v3095_mb,v3095_mg]
  upper := v3095_upper
  lower := (Primitive.Addresses.material3095 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3095_pa_checked.trans (by decide +kernel)
    · exact v3095_pb_checked.trans (by decide +kernel)
    · exact v3095_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 93 Primitive.Addresses.material3095
    · exact v3095_mb_checked.trans (by decide +kernel)
    · exact v3095_mg_checked.trans (by decide +kernel)
  upper_error := v3095_upper_checked
  lower_error := reuse_lower_error 39 93 Primitive.Addresses.material3095

def v3096_pa : Scalar.QComplex := ((999998262384105381044801921750 : Int)/10^30,(-1864196548094892585252089004 : Int)/10^30)
theorem v3096_pa_checked : Scalar.distance (sourceCoefficient 39 94 1 0) v3096_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3096_pb : Scalar.QComplex := ((-804358771254433158257415 : Int)/10^30,(-431476699390875232379606231 : Int)/10^30)
theorem v3096_pb_checked : Scalar.distance (sourceCoefficient 39 94 1 1) v3096_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3096_pg : Scalar.QComplex := ((-93086260396204287105693 : Int)/10^30,(173531386836562322707 : Int)/10^30)
theorem v3096_pg_checked : Scalar.distance (sourceCoefficient 39 94 1 2) v3096_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3096_mb : Scalar.QComplex := ((-1176703430340072835344596 : Int)/10^30,(-431475844606987971506525609 : Int)/10^30)
theorem v3096_mb_checked : Scalar.distance (sourceCoefficient 39 94 3 1) v3096_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3096_mg : Scalar.QComplex := ((-93086075986164012916883 : Int)/10^30,(253860572495283324341 : Int)/10^30)
theorem v3096_mg_checked : Scalar.distance (sourceCoefficient 39 94 3 2) v3096_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3096_upper : Scalar.QComplex := ((999993555570038185476399608555 : Int)/10^30,(-3590100053334379491307309533 : Int)/10^30)
theorem v3096_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 94 5) 1) 14) v3096_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3096 : Material (39 : Basis) (94 : Basis) where
  plus := ![v3096_pa,v3096_pb,v3096_pg]
  minus := ![(Primitive.Addresses.material3096 1).one,v3096_mb,v3096_mg]
  upper := v3096_upper
  lower := (Primitive.Addresses.material3096 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3096_pa_checked.trans (by decide +kernel)
    · exact v3096_pb_checked.trans (by decide +kernel)
    · exact v3096_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 94 Primitive.Addresses.material3096
    · exact v3096_mb_checked.trans (by decide +kernel)
    · exact v3096_mg_checked.trans (by decide +kernel)
  upper_error := v3096_upper_checked
  lower_error := reuse_lower_error 39 94 Primitive.Addresses.material3096

def v3097_pa : Scalar.QComplex := ((999998178868148727617355762236 : Int)/10^30,(-1908470692995715239599932853 : Int)/10^30)
theorem v3097_pa_checked : Scalar.distance (sourceCoefficient 39 95 1 0) v3097_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3097_pb : Scalar.QComplex := ((-823462053940862169918326 : Int)/10^30,(-431476656848896237218878866 : Int)/10^30)
theorem v3097_pb_checked : Scalar.distance (sourceCoefficient 39 95 1 1) v3097_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3097_pg : Scalar.QComplex := ((-93086251920126024641320 : Int)/10^30,(177652707239380261012 : Int)/10^30)
theorem v3097_pg_checked : Scalar.distance (sourceCoefficient 39 95 1 2) v3097_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3097_mb : Scalar.QComplex := ((-1195806669201664786483265 : Int)/10^30,(-431475785579752238193998649 : Int)/10^30)
theorem v3097_mb_checked : Scalar.distance (sourceCoefficient 39 95 3 1) v3097_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3097_mg : Scalar.QComplex := ((-93086063953575016232444 : Int)/10^30,(257981884049071530917 : Int)/10^30)
theorem v3097_mg_checked : Scalar.distance (sourceCoefficient 39 95 3 2) v3097_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3097_upper : Scalar.QComplex := ((999993395641048339486091547517 : Int)/10^30,(-3634373988153099446863974893 : Int)/10^30)
theorem v3097_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 95 5) 1) 14) v3097_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3097 : Material (39 : Basis) (95 : Basis) where
  plus := ![v3097_pa,v3097_pb,v3097_pg]
  minus := ![(Primitive.Addresses.material3097 1).one,v3097_mb,v3097_mg]
  upper := v3097_upper
  lower := (Primitive.Addresses.material3097 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3097_pa_checked.trans (by decide +kernel)
    · exact v3097_pb_checked.trans (by decide +kernel)
    · exact v3097_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 95 Primitive.Addresses.material3097
    · exact v3097_mb_checked.trans (by decide +kernel)
    · exact v3097_mg_checked.trans (by decide +kernel)
  upper_error := v3097_upper_checked
  lower_error := reuse_lower_error 39 95 Primitive.Addresses.material3097

def v3098_pa : Scalar.QComplex := ((999998138060162971767474152675 : Int)/10^30,(-1929734750486840442381145196 : Int)/10^30)
theorem v3098_pa_checked : Scalar.distance (sourceCoefficient 39 96 1 0) v3098_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3098_pb : Scalar.QComplex := ((-832637008863043143420611 : Int)/10^30,(-431476636015890930572688444 : Int)/10^30)
theorem v3098_pb_checked : Scalar.distance (sourceCoefficient 39 96 1 1) v3098_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3098_pg : Scalar.QComplex := ((-93086247773547686561264 : Int)/10^30,(179632101585209202188 : Int)/10^30)
theorem v3098_pg_checked : Scalar.distance (sourceCoefficient 39 96 1 2) v3098_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3098_mb : Scalar.QComplex := ((-1204981602729645430395611 : Int)/10^30,(-431475756829181815415694854 : Int)/10^30)
theorem v3098_mb_checked : Scalar.distance (sourceCoefficient 39 96 3 1) v3098_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3098_mg : Scalar.QComplex := ((-93086058098870050274619 : Int)/10^30,(259961274079571143543 : Int)/10^30)
theorem v3098_mg_checked : Scalar.distance (sourceCoefficient 39 96 3 2) v3098_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3098_upper : Scalar.QComplex := ((999993318133289192881853884247 : Int)/10^30,(-3655637943543027525223493230 : Int)/10^30)
theorem v3098_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 96 5) 1) 14) v3098_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3098 : Material (39 : Basis) (96 : Basis) where
  plus := ![v3098_pa,v3098_pb,v3098_pg]
  minus := ![(Primitive.Addresses.material3098 1).one,v3098_mb,v3098_mg]
  upper := v3098_upper
  lower := (Primitive.Addresses.material3098 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3098_pa_checked.trans (by decide +kernel)
    · exact v3098_pb_checked.trans (by decide +kernel)
    · exact v3098_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 96 Primitive.Addresses.material3098
    · exact v3098_mb_checked.trans (by decide +kernel)
    · exact v3098_mg_checked.trans (by decide +kernel)
  upper_error := v3098_upper_checked
  lower_error := reuse_lower_error 39 96 Primitive.Addresses.material3098

def v3099_pa : Scalar.QComplex := ((999997994200127892916083704976 : Int)/10^30,(-2002896832335864694123957516 : Int)/10^30)
theorem v3099_pa_checked : Scalar.distance (sourceCoefficient 39 97 1 0) v3099_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3099_pb : Scalar.QComplex := ((-864204773379170817095943 : Int)/10^30,(-431476562349682300155760802 : Int)/10^30)
theorem v3099_pb_checked : Scalar.distance (sourceCoefficient 39 97 1 1) v3099_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3099_pg : Scalar.QComplex := ((-93086233131510472177685 : Int)/10^30,(186442495439513651219 : Int)/10^30)
theorem v3099_pg_checked : Scalar.distance (sourceCoefficient 39 97 1 2) v3099_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3099_mb : Scalar.QComplex := ((-1236549291921031411430776 : Int)/10^30,(-431475655921441596212388979 : Int)/10^30)
theorem v3099_mb_checked : Scalar.distance (sourceCoefficient 39 97 3 1) v3099_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3099_mg : Scalar.QComplex := ((-93086037579775120278821 : Int)/10^30,(266771652762636047104 : Int)/10^30)
theorem v3099_mg_checked : Scalar.distance (sourceCoefficient 39 97 3 2) v3099_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3099_upper : Scalar.QComplex := ((999993048002352317456154982074 : Int)/10^30,(-3728799668136355419026796554 : Int)/10^30)
theorem v3099_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 97 5) 1) 14) v3099_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3099 : Material (39 : Basis) (97 : Basis) where
  plus := ![v3099_pa,v3099_pb,v3099_pg]
  minus := ![(Primitive.Addresses.material3099 1).one,v3099_mb,v3099_mg]
  upper := v3099_upper
  lower := (Primitive.Addresses.material3099 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3099_pa_checked.trans (by decide +kernel)
    · exact v3099_pb_checked.trans (by decide +kernel)
    · exact v3099_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 97 Primitive.Addresses.material3099
    · exact v3099_mb_checked.trans (by decide +kernel)
    · exact v3099_mg_checked.trans (by decide +kernel)
  upper_error := v3099_upper_checked
  lower_error := reuse_lower_error 39 97 Primitive.Addresses.material3099

def v3100_pa : Scalar.QComplex := ((999999572680382032305113567858 : Int)/10^30,(-924466902237897250728713800 : Int)/10^30)
theorem v3100_pa_checked : Scalar.distance (sourceCoefficient 40 41 1 0) v3100_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3100_pb : Scalar.QComplex := ((-398886687210813820515817 : Int)/10^30,(-431477336606756914549823584 : Int)/10^30)
theorem v3100_pb_checked : Scalar.distance (sourceCoefficient 40 41 1 1) v3100_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3100_pg : Scalar.QComplex := ((-93086390117691036279834 : Int)/10^30,(86055323485738200004 : Int)/10^30)
theorem v3100_pg_checked : Scalar.distance (sourceCoefficient 40 41 1 2) v3100_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3100_mb : Scalar.QComplex := ((-771232047160848130496746 : Int)/10^30,(-431476831726779133969267635 : Int)/10^30)
theorem v3100_mb_checked : Scalar.distance (sourceCoefficient 40 41 3 1) v3100_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3100_mg : Scalar.QComplex := ((-93086281195505356972186 : Int)/10^30,(166384653659596066399 : Int)/10^30)
theorem v3100_mg_checked : Scalar.distance (sourceCoefficient 40 41 3 2) v3100_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3100_upper : Scalar.QComplex := ((999996487752480446001664553560 : Int)/10^30,(-2650374068546807612626392842 : Int)/10^30)
theorem v3100_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 41 5) 1) 14) v3100_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3100 : Material (40 : Basis) (41 : Basis) where
  plus := ![v3100_pa,v3100_pb,v3100_pg]
  minus := ![(Primitive.Addresses.material3100 1).one,v3100_mb,v3100_mg]
  upper := v3100_upper
  lower := (Primitive.Addresses.material3100 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3100_pa_checked.trans (by decide +kernel)
    · exact v3100_pb_checked.trans (by decide +kernel)
    · exact v3100_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 41 Primitive.Addresses.material3100
    · exact v3100_mb_checked.trans (by decide +kernel)
    · exact v3100_mg_checked.trans (by decide +kernel)
  upper_error := v3100_upper_checked
  lower_error := reuse_lower_error 40 41 Primitive.Addresses.material3100

def v3101_pa : Scalar.QComplex := ((999999561810980552401379751879 : Int)/10^30,(-936150547126679019625799597 : Int)/10^30)
theorem v3101_pa_checked : Scalar.distance (sourceCoefficient 40 42 1 0) v3101_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3101_pb : Scalar.QComplex := ((-403927917311526159419691 : Int)/10^30,(-431477331882698798206963403 : Int)/10^30)
theorem v3101_pb_checked : Scalar.distance (sourceCoefficient 40 42 1 1) v3101_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3101_pg : Scalar.QComplex := ((-93086389102212901880295 : Int)/10^30,(87142912273150820298 : Int)/10^30)
theorem v3101_pg_checked : Scalar.distance (sourceCoefficient 40 42 1 2) v3101_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3101_mb : Scalar.QComplex := ((-776273271307830716583553 : Int)/10^30,(-431476822652368248269692603 : Int)/10^30)
theorem v3101_mb_checked : Scalar.distance (sourceCoefficient 40 42 3 1) v3101_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3101_mg : Scalar.QComplex := ((-93086279241487460325119 : Int)/10^30,(167472241165737781326 : Int)/10^30)
theorem v3101_mg_checked : Scalar.distance (sourceCoefficient 40 42 3 2) v3101_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3101_upper : Scalar.QComplex := ((999996456718184008741868346075 : Int)/10^30,(-2662057677274571887107239788 : Int)/10^30)
theorem v3101_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 42 5) 1) 14) v3101_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3101 : Material (40 : Basis) (42 : Basis) where
  plus := ![v3101_pa,v3101_pb,v3101_pg]
  minus := ![(Primitive.Addresses.material3101 1).one,v3101_mb,v3101_mg]
  upper := v3101_upper
  lower := (Primitive.Addresses.material3101 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3101_pa_checked.trans (by decide +kernel)
    · exact v3101_pb_checked.trans (by decide +kernel)
    · exact v3101_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 42 Primitive.Addresses.material3101
    · exact v3101_mb_checked.trans (by decide +kernel)
    · exact v3101_mg_checked.trans (by decide +kernel)
  upper_error := v3101_upper_checked
  lower_error := reuse_lower_error 40 42 Primitive.Addresses.material3101

def v3102_pa : Scalar.QComplex := ((999999547201659467609924962616 : Int)/10^30,(-951628328728418509551709016 : Int)/10^30)
theorem v3102_pa_checked : Scalar.distance (sourceCoefficient 40 43 1 0) v3102_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3102_pb : Scalar.QComplex := ((-410606232075043592140305 : Int)/10^30,(-431477325503625640234640052 : Int)/10^30)
theorem v3102_pb_checked : Scalar.distance (sourceCoefficient 40 43 1 1) v3102_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3102_pg : Scalar.QComplex := ((-93086387734141430307207 : Int)/10^30,(88583683697351542059 : Int)/10^30)
theorem v3102_pg_checked : Scalar.distance (sourceCoefficient 40 43 1 2) v3102_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3102_mb : Scalar.QComplex := ((-782951578079853516243793 : Int)/10^30,(-431476810510212604733765080 : Int)/10^30)
theorem v3102_mb_checked : Scalar.distance (sourceCoefficient 40 43 3 1) v3102_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3102_mg : Scalar.QComplex := ((-93086276630095648998458 : Int)/10^30,(168913010872889391034 : Int)/10^30)
theorem v3102_mg_checked : Scalar.distance (sourceCoefficient 40 43 3 2) v3102_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3102_upper : Scalar.QComplex := ((999996415395637771594100122560 : Int)/10^30,(-2677535410609610984092763196 : Int)/10^30)
theorem v3102_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 43 5) 1) 14) v3102_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3102 : Material (40 : Basis) (43 : Basis) where
  plus := ![v3102_pa,v3102_pb,v3102_pg]
  minus := ![(Primitive.Addresses.material3102 1).one,v3102_mb,v3102_mg]
  upper := v3102_upper
  lower := (Primitive.Addresses.material3102 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3102_pa_checked.trans (by decide +kernel)
    · exact v3102_pb_checked.trans (by decide +kernel)
    · exact v3102_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 43 Primitive.Addresses.material3102
    · exact v3102_mb_checked.trans (by decide +kernel)
    · exact v3102_mg_checked.trans (by decide +kernel)
  upper_error := v3102_upper_checked
  lower_error := reuse_lower_error 40 43 Primitive.Addresses.material3102

def v3103_pa : Scalar.QComplex := ((999999541611988811008871008065 : Int)/10^30,(-957484105486045891565465128 : Int)/10^30)
theorem v3103_pa_checked : Scalar.distance (sourceCoefficient 40 44 1 0) v3103_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3103_pb : Scalar.QComplex := ((-413132868077283402982963 : Int)/10^30,(-431477323054268214780432384 : Int)/10^30)
theorem v3103_pb_checked : Scalar.distance (sourceCoefficient 40 44 1 1) v3103_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3103_pg : Scalar.QComplex := ((-93086387209769507691098 : Int)/10^30,(89128777046036710232 : Int)/10^30)
theorem v3103_pg_checked : Scalar.distance (sourceCoefficient 40 44 1 2) v3103_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3103_mb : Scalar.QComplex := ((-785478211027626127279163 : Int)/10^30,(-431476805880483016815566111 : Int)/10^30)
theorem v3103_mb_checked : Scalar.distance (sourceCoefficient 40 44 3 1) v3103_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3103_mg : Scalar.QComplex := ((-93086275635332911807764 : Int)/10^30,(169458103566102041112 : Int)/10^30)
theorem v3103_mg_checked : Scalar.distance (sourceCoefficient 40 44 3 2) v3103_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3103_upper : Scalar.QComplex := ((999996399699435988403714926945 : Int)/10^30,(-2683391168998482291145936809 : Int)/10^30)
theorem v3103_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 44 5) 1) 14) v3103_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3103 : Material (40 : Basis) (44 : Basis) where
  plus := ![v3103_pa,v3103_pb,v3103_pg]
  minus := ![(Primitive.Addresses.material3103 1).one,v3103_mb,v3103_mg]
  upper := v3103_upper
  lower := (Primitive.Addresses.material3103 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3103_pa_checked.trans (by decide +kernel)
    · exact v3103_pb_checked.trans (by decide +kernel)
    · exact v3103_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 44 Primitive.Addresses.material3103
    · exact v3103_mb_checked.trans (by decide +kernel)
    · exact v3103_mg_checked.trans (by decide +kernel)
  upper_error := v3103_upper_checked
  lower_error := reuse_lower_error 40 44 Primitive.Addresses.material3103

def v3104_pa : Scalar.QComplex := ((999999538818284196619297406728 : Int)/10^30,(-960397427588280462193629150 : Int)/10^30)
theorem v3104_pa_checked : Scalar.distance (sourceCoefficient 40 45 1 0) v3104_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3104_pb : Scalar.QComplex := ((-414389901055657770340731 : Int)/10^30,(-431477321828333585891706959 : Int)/10^30)
theorem v3104_pb_checked : Scalar.distance (sourceCoefficient 40 45 1 1) v3104_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3104_pg : Scalar.QComplex := ((-93086386947500698541049 : Int)/10^30,(89399967797497499314 : Int)/10^30)
theorem v3104_pg_checked : Scalar.distance (sourceCoefficient 40 45 1 2) v3104_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3104_mb : Scalar.QComplex := ((-786735242480023296858066 : Int)/10^30,(-431476803569785998724962848 : Int)/10^30)
theorem v3104_mb_checked : Scalar.distance (sourceCoefficient 40 45 3 1) v3104_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3104_mg : Scalar.QComplex := ((-93086275139038795779760 : Int)/10^30,(169729293990259949248 : Int)/10^30)
theorem v3104_mg_checked : Scalar.distance (sourceCoefficient 40 45 3 2) v3104_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3104_upper : Scalar.QComplex := ((999996391877605880968683214232 : Int)/10^30,(-2686304481939985091816106752 : Int)/10^30)
theorem v3104_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 45 5) 1) 14) v3104_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3104 : Material (40 : Basis) (45 : Basis) where
  plus := ![v3104_pa,v3104_pb,v3104_pg]
  minus := ![(Primitive.Addresses.material3104 1).one,v3104_mb,v3104_mg]
  upper := v3104_upper
  lower := (Primitive.Addresses.material3104 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3104_pa_checked.trans (by decide +kernel)
    · exact v3104_pb_checked.trans (by decide +kernel)
    · exact v3104_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 45 Primitive.Addresses.material3104
    · exact v3104_mb_checked.trans (by decide +kernel)
    · exact v3104_mg_checked.trans (by decide +kernel)
  upper_error := v3104_upper_checked
  lower_error := reuse_lower_error 40 45 Primitive.Addresses.material3104

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
