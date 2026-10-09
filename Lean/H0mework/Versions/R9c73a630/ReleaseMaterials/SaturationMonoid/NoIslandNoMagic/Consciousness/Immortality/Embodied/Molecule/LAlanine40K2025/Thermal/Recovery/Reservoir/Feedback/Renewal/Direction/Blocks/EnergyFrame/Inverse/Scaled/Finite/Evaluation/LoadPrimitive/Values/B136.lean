import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B090
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B091

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2177_pa : Scalar.QComplex := ((999999156498620161940676534836 : Int)/10^30,(-1298846429791274769172184014 : Int)/10^30)
theorem v2177_pa_checked : Scalar.distance (sourceCoefficient 25 78 1 0) v2177_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2177_pb : Scalar.QComplex := ((-560422976329398096476417 : Int)/10^30,(-431477109808820453869075976 : Int)/10^30)
theorem v2177_pb_checked : Scalar.distance (sourceCoefficient 25 78 1 1) v2177_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2177_pg : Scalar.QComplex := ((-93086346282699840847446 : Int)/10^30,(120904970515108448705 : Int)/10^30)
theorem v2177_pg_checked : Scalar.distance (sourceCoefficient 25 78 1 2) v2177_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2177_mb : Scalar.QComplex := ((-932768080415684828796122 : Int)/10^30,(-431476465530384935576376761 : Int)/10^30)
theorem v2177_mb_checked : Scalar.distance (sourceCoefficient 25 78 3 1) v2177_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2177_mg : Scalar.QComplex := ((-93086207286854666800885 : Int)/10^30,(201234249885226871572 : Int)/10^30)
theorem v2177_mg_checked : Scalar.distance (sourceCoefficient 25 78 3 2) v2177_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2177_upper : Scalar.QComplex := ((999995425426237317785559005765 : Int)/10^30,(-3024752320213891275142407896 : Int)/10^30)
theorem v2177_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 78 5) 1) 14) v2177_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2177 : Material (25 : Basis) (78 : Basis) where
  plus := ![v2177_pa,v2177_pb,v2177_pg]
  minus := ![(Primitive.Addresses.material2177 1).one,v2177_mb,v2177_mg]
  upper := v2177_upper
  lower := (Primitive.Addresses.material2177 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2177_pa_checked.trans (by decide +kernel)
    · exact v2177_pb_checked.trans (by decide +kernel)
    · exact v2177_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 78 Primitive.Addresses.material2177
    · exact v2177_mb_checked.trans (by decide +kernel)
    · exact v2177_mg_checked.trans (by decide +kernel)
  upper_error := v2177_upper_checked
  lower_error := reuse_lower_error 25 78 Primitive.Addresses.material2177

def v2178_pa : Scalar.QComplex := ((999999149239296422157891305247 : Int)/10^30,(-1304423506136680084138984512 : Int)/10^30)
theorem v2178_pa_checked : Scalar.distance (sourceCoefficient 25 79 1 0) v2178_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2178_pb : Scalar.QComplex := ((-562829358290931008909172 : Int)/10^30,(-431477106024226941442351240 : Int)/10^30)
theorem v2178_pb_checked : Scalar.distance (sourceCoefficient 25 79 1 1) v2178_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2178_pg : Scalar.QComplex := ((-93086345536585799064464 : Int)/10^30,(121424120521153954723 : Int)/10^30)
theorem v2178_pg_checked : Scalar.distance (sourceCoefficient 25 79 1 2) v2178_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2178_mb : Scalar.QComplex := ((-935174458215278010401623 : Int)/10^30,(-431476459669193578944191987 : Int)/10^30)
theorem v2178_mb_checked : Scalar.distance (sourceCoefficient 25 79 3 1) v2178_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2178_mg : Scalar.QComplex := ((-93086206092737829261293 : Int)/10^30,(201753399054106289682 : Int)/10^30)
theorem v2178_mg_checked : Scalar.distance (sourceCoefficient 25 79 3 2) v2178_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2178_upper : Scalar.QComplex := ((999995408541396566156973536521 : Int)/10^30,(-3030329375723962288876045819 : Int)/10^30)
theorem v2178_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 79 5) 1) 14) v2178_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2178 : Material (25 : Basis) (79 : Basis) where
  plus := ![v2178_pa,v2178_pb,v2178_pg]
  minus := ![(Primitive.Addresses.material2178 1).one,v2178_mb,v2178_mg]
  upper := v2178_upper
  lower := (Primitive.Addresses.material2178 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2178_pa_checked.trans (by decide +kernel)
    · exact v2178_pb_checked.trans (by decide +kernel)
    · exact v2178_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 79 Primitive.Addresses.material2178
    · exact v2178_mb_checked.trans (by decide +kernel)
    · exact v2178_mg_checked.trans (by decide +kernel)
  upper_error := v2178_upper_checked
  lower_error := reuse_lower_error 25 79 Primitive.Addresses.material2178

def v2179_pa : Scalar.QComplex := ((999999137837272586889641708257 : Int)/10^30,(-1313135450553998323578629120 : Int)/10^30)
theorem v2179_pa_checked : Scalar.distance (sourceCoefficient 25 80 1 0) v2179_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2179_pb : Scalar.QComplex := ((-566588364704069667300574 : Int)/10^30,(-431477100076509428940361719 : Int)/10^30)
theorem v2179_pb_checked : Scalar.distance (sourceCoefficient 25 80 1 1) v2179_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2179_pg : Scalar.QComplex := ((-93086344364322319558265 : Int)/10^30,(122235084133802554134 : Int)/10^30)
theorem v2179_pg_checked : Scalar.distance (sourceCoefficient 25 80 1 2) v2179_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2179_mb : Scalar.QComplex := ((-938933458096154448065122 : Int)/10^30,(-431476450477625045874754251 : Int)/10^30)
theorem v2179_mb_checked : Scalar.distance (sourceCoefficient 25 80 3 1) v2179_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2179_mg : Scalar.QComplex := ((-93086204220649712971883 : Int)/10^30,(202564361353185487210 : Int)/10^30)
theorem v2179_mg_checked : Scalar.distance (sourceCoefficient 25 80 3 2) v2179_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2179_upper : Scalar.QComplex := ((999995382103363989996300210223 : Int)/10^30,(-3039041287487003939448911959 : Int)/10^30)
theorem v2179_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 80 5) 1) 14) v2179_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2179 : Material (25 : Basis) (80 : Basis) where
  plus := ![v2179_pa,v2179_pb,v2179_pg]
  minus := ![(Primitive.Addresses.material2179 1).one,v2179_mb,v2179_mg]
  upper := v2179_upper
  lower := (Primitive.Addresses.material2179 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2179_pa_checked.trans (by decide +kernel)
    · exact v2179_pb_checked.trans (by decide +kernel)
    · exact v2179_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 80 Primitive.Addresses.material2179
    · exact v2179_mb_checked.trans (by decide +kernel)
    · exact v2179_mg_checked.trans (by decide +kernel)
  upper_error := v2179_upper_checked
  lower_error := reuse_lower_error 25 80 Primitive.Addresses.material2179

def v2180_pa : Scalar.QComplex := ((999999103046858082983995973533 : Int)/10^30,(-1339367566916973398027409258 : Int)/10^30)
theorem v2180_pa_checked : Scalar.distance (sourceCoefficient 25 81 1 0) v2180_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2180_pb : Scalar.QComplex := ((-577906927725557436870670 : Int)/10^30,(-431477081903945307167179747 : Int)/10^30)
theorem v2180_pb_checked : Scalar.distance (sourceCoefficient 25 81 1 1) v2180_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2180_pg : Scalar.QComplex := ((-93086340784801253738909 : Int)/10^30,(124676937599514387710 : Int)/10^30)
theorem v2180_pg_checked : Scalar.distance (sourceCoefficient 25 81 1 2) v2180_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2180_mb : Scalar.QComplex := ((-950252001221119545665952 : Int)/10^30,(-431476422537657572188744154 : Int)/10^30)
theorem v2180_mb_checked : Scalar.distance (sourceCoefficient 25 81 3 1) v2180_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2180_mg : Scalar.QComplex := ((-93086198533920416060058 : Int)/10^30,(205006210820718213126 : Int)/10^30)
theorem v2180_mg_checked : Scalar.distance (sourceCoefficient 25 81 3 2) v2180_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2180_upper : Scalar.QComplex := ((999995302038748218838102285035 : Int)/10^30,(-3065273304735223860101794471 : Int)/10^30)
theorem v2180_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 81 5) 1) 14) v2180_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2180 : Material (25 : Basis) (81 : Basis) where
  plus := ![v2180_pa,v2180_pb,v2180_pg]
  minus := ![(Primitive.Addresses.material2180 1).one,v2180_mb,v2180_mg]
  upper := v2180_upper
  lower := (Primitive.Addresses.material2180 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2180_pa_checked.trans (by decide +kernel)
    · exact v2180_pb_checked.trans (by decide +kernel)
    · exact v2180_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 81 Primitive.Addresses.material2180
    · exact v2180_mb_checked.trans (by decide +kernel)
    · exact v2180_mg_checked.trans (by decide +kernel)
  upper_error := v2180_upper_checked
  lower_error := reuse_lower_error 25 81 Primitive.Addresses.material2180

def v2181_pa : Scalar.QComplex := ((999999089683793371015336614674 : Int)/10^30,(-1349307816838831359249575591 : Int)/10^30)
theorem v2181_pa_checked : Scalar.distance (sourceCoefficient 25 82 1 0) v2181_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2181_pb : Scalar.QComplex := ((-582195919951010719801958 : Int)/10^30,(-431477074914307658535396325 : Int)/10^30)
theorem v2181_pb_checked : Scalar.distance (sourceCoefficient 25 82 1 1) v2181_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2181_pg : Scalar.QComplex := ((-93086339408873342060549 : Int)/10^30,(125602239743059787817 : Int)/10^30)
theorem v2181_pg_checked : Scalar.distance (sourceCoefficient 25 82 1 2) v2181_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2181_mb : Scalar.QComplex := ((-954540985817842517257342 : Int)/10^30,(-431476411846815404591378990 : Int)/10^30)
theorem v2181_mb_checked : Scalar.distance (sourceCoefficient 25 82 3 1) v2181_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2181_mg : Scalar.QComplex := ((-93086196359498940884393 : Int)/10^30,(205931511432367518509 : Int)/10^30)
theorem v2181_mg_checked : Scalar.distance (sourceCoefficient 25 82 3 2) v2181_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2181_upper : Scalar.QComplex := ((999995271519733816886405804291 : Int)/10^30,(-3075213516788809821399147267 : Int)/10^30)
theorem v2181_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 82 5) 1) 14) v2181_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2181 : Material (25 : Basis) (82 : Basis) where
  plus := ![v2181_pa,v2181_pb,v2181_pg]
  minus := ![(Primitive.Addresses.material2181 1).one,v2181_mb,v2181_mg]
  upper := v2181_upper
  lower := (Primitive.Addresses.material2181 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2181_pa_checked.trans (by decide +kernel)
    · exact v2181_pb_checked.trans (by decide +kernel)
    · exact v2181_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 82 Primitive.Addresses.material2181
    · exact v2181_mb_checked.trans (by decide +kernel)
    · exact v2181_mg_checked.trans (by decide +kernel)
  upper_error := v2181_upper_checked
  lower_error := reuse_lower_error 25 82 Primitive.Addresses.material2181

def v2182_pa : Scalar.QComplex := ((999999071283493585458067733717 : Int)/10^30,(-1362876425181217439676462506 : Int)/10^30)
theorem v2182_pa_checked : Scalar.distance (sourceCoefficient 25 83 1 0) v2182_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2182_pb : Scalar.QComplex := ((-588050466410815500686192 : Int)/10^30,(-431477065281578681018157041 : Int)/10^30)
theorem v2182_pb_checked : Scalar.distance (sourceCoefficient 25 83 1 1) v2182_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2182_pg : Scalar.QComplex := ((-93086337513387677855491 : Int)/10^30,(126865292725349500933 : Int)/10^30)
theorem v2182_pg_checked : Scalar.distance (sourceCoefficient 25 83 1 2) v2182_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2182_mb : Scalar.QComplex := ((-960395521785120819575812 : Int)/10^30,(-431476397161880097952175205 : Int)/10^30)
theorem v2182_mb_checked : Scalar.distance (sourceCoefficient 25 83 3 1) v2182_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2182_mg : Scalar.QComplex := ((-93086193374056144533876 : Int)/10^30,(207194562308646123241 : Int)/10^30)
theorem v2182_mg_checked : Scalar.distance (sourceCoefficient 25 83 3 2) v2182_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2182_upper : Scalar.QComplex := ((999995229701274371989130023756 : Int)/10^30,(-3088782073165099488827015826 : Int)/10^30)
theorem v2182_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 83 5) 1) 14) v2182_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2182 : Material (25 : Basis) (83 : Basis) where
  plus := ![v2182_pa,v2182_pb,v2182_pg]
  minus := ![(Primitive.Addresses.material2182 1).one,v2182_mb,v2182_mg]
  upper := v2182_upper
  lower := (Primitive.Addresses.material2182 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2182_pa_checked.trans (by decide +kernel)
    · exact v2182_pb_checked.trans (by decide +kernel)
    · exact v2182_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 83 Primitive.Addresses.material2182
    · exact v2182_mb_checked.trans (by decide +kernel)
    · exact v2182_mg_checked.trans (by decide +kernel)
  upper_error := v2182_upper_checked
  lower_error := reuse_lower_error 25 83 Primitive.Addresses.material2182

def v2183_pa : Scalar.QComplex := ((999999022775924856199946898129 : Int)/10^30,(-1398015448884849435785852488 : Int)/10^30)
theorem v2183_pa_checked : Scalar.distance (sourceCoefficient 25 84 1 0) v2183_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2183_pb : Scalar.QComplex := ((-603212157013185109488342 : Int)/10^30,(-431477039843089517507329653 : Int)/10^30)
theorem v2183_pb_checked : Scalar.distance (sourceCoefficient 25 84 1 1) v2183_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2183_pg : Scalar.QComplex := ((-93086332511655283197154 : Int)/10^30,(130136258103610582738 : Int)/10^30)
theorem v2183_pg_checked : Scalar.distance (sourceCoefficient 25 84 1 2) v2183_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2183_mb : Scalar.QComplex := ((-975557184789829652535551 : Int)/10^30,(-431476358639544273704367467 : Int)/10^30)
theorem v2183_mb_checked : Scalar.distance (sourceCoefficient 25 84 3 1) v2183_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2183_mg : Scalar.QComplex := ((-93086185549629809621691 : Int)/10^30,(210465522152707517292 : Int)/10^30)
theorem v2183_mg_checked : Scalar.distance (sourceCoefficient 25 84 3 2) v2183_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2183_upper : Scalar.QComplex := ((999995120547010763916472284406 : Int)/10^30,(-3123920960813620343617486838 : Int)/10^30)
theorem v2183_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 84 5) 1) 14) v2183_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2183 : Material (25 : Basis) (84 : Basis) where
  plus := ![v2183_pa,v2183_pb,v2183_pg]
  minus := ![(Primitive.Addresses.material2183 1).one,v2183_mb,v2183_mg]
  upper := v2183_upper
  lower := (Primitive.Addresses.material2183 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2183_pa_checked.trans (by decide +kernel)
    · exact v2183_pb_checked.trans (by decide +kernel)
    · exact v2183_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 84 Primitive.Addresses.material2183
    · exact v2183_mb_checked.trans (by decide +kernel)
    · exact v2183_mg_checked.trans (by decide +kernel)
  upper_error := v2183_upper_checked
  lower_error := reuse_lower_error 25 84 Primitive.Addresses.material2183

def v2184_pa : Scalar.QComplex := ((999998909128285705661548936801 : Int)/10^30,(-1477072184623209216926540980 : Int)/10^30)
theorem v2184_pa_checked : Scalar.distance (sourceCoefficient 25 85 1 0) v2184_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2184_pb : Scalar.QComplex := ((-637323340721869149718495 : Int)/10^30,(-431476980013973010964233394 : Int)/10^30)
theorem v2184_pb_checked : Scalar.distance (sourceCoefficient 25 85 1 1) v2184_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2184_pg : Scalar.QComplex := ((-93086320768398742785234 : Int)/10^30,(137495365165720248117 : Int)/10^30)
theorem v2184_pg_checked : Scalar.distance (sourceCoefficient 25 85 1 2) v2184_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2184_mb : Scalar.QComplex := ((-1009668304167528098145438 : Int)/10^30,(-431476269374034814365051385 : Int)/10^30)
theorem v2184_mb_checked : Scalar.distance (sourceCoefficient 25 85 3 1) v2184_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2184_mg : Scalar.QComplex := ((-93086167455799689038610 : Int)/10^30,(217824616340783797905 : Int)/10^30)
theorem v2184_mg_checked : Scalar.distance (sourceCoefficient 25 85 3 2) v2184_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2184_upper : Scalar.QComplex := ((999994870454786964819438068524 : Int)/10^30,(-3202977382660743758460051877 : Int)/10^30)
theorem v2184_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 85 5) 1) 14) v2184_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2184 : Material (25 : Basis) (85 : Basis) where
  plus := ![v2184_pa,v2184_pb,v2184_pg]
  minus := ![(Primitive.Addresses.material2184 1).one,v2184_mb,v2184_mg]
  upper := v2184_upper
  lower := (Primitive.Addresses.material2184 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2184_pa_checked.trans (by decide +kernel)
    · exact v2184_pb_checked.trans (by decide +kernel)
    · exact v2184_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 85 Primitive.Addresses.material2184
    · exact v2184_mb_checked.trans (by decide +kernel)
    · exact v2184_mg_checked.trans (by decide +kernel)
  upper_error := v2184_upper_checked
  lower_error := reuse_lower_error 25 85 Primitive.Addresses.material2184

def v2185_pa : Scalar.QComplex := ((999998887479357777049161645016 : Int)/10^30,(-1491656812656222981172011112 : Int)/10^30)
theorem v2185_pa_checked : Scalar.distance (sourceCoefficient 25 86 1 0) v2185_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2185_pb : Scalar.QComplex := ((-643616275728465630622621 : Int)/10^30,(-431476968583661125274436956 : Int)/10^30)
theorem v2185_pb_checked : Scalar.distance (sourceCoefficient 25 86 1 1) v2185_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2185_pg : Scalar.QComplex := ((-93086318527807314882086 : Int)/10^30,(138852995673914895842 : Int)/10^30)
theorem v2185_pg_checked : Scalar.distance (sourceCoefficient 25 86 1 2) v2185_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2185_mb : Scalar.QComplex := ((-1015961226967132919542783 : Int)/10^30,(-431476252513207697281528743 : Int)/10^30)
theorem v2185_mb_checked : Scalar.distance (sourceCoefficient 25 86 3 1) v2185_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2185_mg : Scalar.QComplex := ((-93086164043635112246335 : Int)/10^30,(219182244409941070862 : Int)/10^30)
theorem v2185_mg_checked : Scalar.distance (sourceCoefficient 25 86 3 2) v2185_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2185_upper : Scalar.QComplex := ((999994823634146401879991030791 : Int)/10^30,(-3217561951607581668903144020 : Int)/10^30)
theorem v2185_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 86 5) 1) 14) v2185_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2185 : Material (25 : Basis) (86 : Basis) where
  plus := ![v2185_pa,v2185_pb,v2185_pg]
  minus := ![(Primitive.Addresses.material2185 1).one,v2185_mb,v2185_mg]
  upper := v2185_upper
  lower := (Primitive.Addresses.material2185 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2185_pa_checked.trans (by decide +kernel)
    · exact v2185_pb_checked.trans (by decide +kernel)
    · exact v2185_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 86 Primitive.Addresses.material2185
    · exact v2185_mb_checked.trans (by decide +kernel)
    · exact v2185_mg_checked.trans (by decide +kernel)
  upper_error := v2185_upper_checked
  lower_error := reuse_lower_error 25 86 Primitive.Addresses.material2185

def v2186_pa : Scalar.QComplex := ((999998886038314261104370998149 : Int)/10^30,(-1492622568021518949645538990 : Int)/10^30)
theorem v2186_pa_checked : Scalar.distance (sourceCoefficient 25 87 1 0) v2186_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2186_pb : Scalar.QComplex := ((-644032977181353925353440 : Int)/10^30,(-431476967822456280742056520 : Int)/10^30)
theorem v2186_pb_checked : Scalar.distance (sourceCoefficient 25 87 1 1) v2186_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2186_pg : Scalar.QComplex := ((-93086318378625817759380 : Int)/10^30,(138942894363034010300 : Int)/10^30)
theorem v2186_pg_checked : Scalar.distance (sourceCoefficient 25 87 1 2) v2186_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2186_mb : Scalar.QComplex := ((-1016377927607978721728184 : Int)/10^30,(-431476251392408549874656730 : Int)/10^30)
theorem v2186_mb_checked : Scalar.distance (sourceCoefficient 25 87 3 1) v2186_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2186_mg : Scalar.QComplex := ((-93086163816875150847578 : Int)/10^30,(219272142936849881655 : Int)/10^30)
theorem v2186_mg_checked : Scalar.distance (sourceCoefficient 25 87 3 2) v2186_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2186_upper : Scalar.QComplex := ((999994820526298884341746182544 : Int)/10^30,(-3218527703047388088288500524 : Int)/10^30)
theorem v2186_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 87 5) 1) 14) v2186_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2186 : Material (25 : Basis) (87 : Basis) where
  plus := ![v2186_pa,v2186_pb,v2186_pg]
  minus := ![(Primitive.Addresses.material2186 1).one,v2186_mb,v2186_mg]
  upper := v2186_upper
  lower := (Primitive.Addresses.material2186 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2186_pa_checked.trans (by decide +kernel)
    · exact v2186_pb_checked.trans (by decide +kernel)
    · exact v2186_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 87 Primitive.Addresses.material2186
    · exact v2186_mb_checked.trans (by decide +kernel)
    · exact v2186_mg_checked.trans (by decide +kernel)
  upper_error := v2186_upper_checked
  lower_error := reuse_lower_error 25 87 Primitive.Addresses.material2186

def v2187_pa : Scalar.QComplex := ((999998868416535586624340826436 : Int)/10^30,(-1504382148373748279958325968 : Int)/10^30)
theorem v2187_pa_checked : Scalar.distance (sourceCoefficient 25 88 1 0) v2187_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2187_pb : Scalar.QComplex := ((-649106968336587574687927 : Int)/10^30,(-431476958510552465306076768 : Int)/10^30)
theorem v2187_pb_checked : Scalar.distance (sourceCoefficient 25 88 1 1) v2187_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2187_pg : Scalar.QComplex := ((-93086316553982240313706 : Int)/10^30,(140037551345856111247 : Int)/10^30)
theorem v2187_pg_checked : Scalar.distance (sourceCoefficient 25 88 1 2) v2187_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2187_mb : Scalar.QComplex := ((-1021451908838179970975662 : Int)/10^30,(-431476237701882358797822294 : Int)/10^30)
theorem v2187_mb_checked : Scalar.distance (sourceCoefficient 25 88 3 1) v2187_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2187_mg : Scalar.QComplex := ((-93086161047592578144973 : Int)/10^30,(220366797937495931163 : Int)/10^30)
theorem v2187_mg_checked : Scalar.distance (sourceCoefficient 25 88 3 2) v2187_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2187_upper : Scalar.QComplex := ((999994782608577588279235514398 : Int)/10^30,(-3230287235471512504421302114 : Int)/10^30)
theorem v2187_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 88 5) 1) 14) v2187_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2187 : Material (25 : Basis) (88 : Basis) where
  plus := ![v2187_pa,v2187_pb,v2187_pg]
  minus := ![(Primitive.Addresses.material2187 1).one,v2187_mb,v2187_mg]
  upper := v2187_upper
  lower := (Primitive.Addresses.material2187 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2187_pa_checked.trans (by decide +kernel)
    · exact v2187_pb_checked.trans (by decide +kernel)
    · exact v2187_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 88 Primitive.Addresses.material2187
    · exact v2187_mb_checked.trans (by decide +kernel)
    · exact v2187_mg_checked.trans (by decide +kernel)
  upper_error := v2187_upper_checked
  lower_error := reuse_lower_error 25 88 Primitive.Addresses.material2187

def v2188_pa : Scalar.QComplex := ((999998844082366678416062837905 : Int)/10^30,(-1520471614499130611952115871 : Int)/10^30)
theorem v2188_pa_checked : Scalar.distance (sourceCoefficient 25 89 1 0) v2188_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2188_pb : Scalar.QComplex := ((-656049206496936605113879 : Int)/10^30,(-431476945641108915007165373 : Int)/10^30)
theorem v2188_pb_checked : Scalar.distance (sourceCoefficient 25 89 1 1) v2188_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2188_pg : Scalar.QComplex := ((-93086314033172815121556 : Int)/10^30,(141535261788896187208 : Int)/10^30)
theorem v2188_pg_checked : Scalar.distance (sourceCoefficient 25 89 1 2) v2188_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2188_mb : Scalar.QComplex := ((-1028394133307866292659097 : Int)/10^30,(-431476218841604734799698968 : Int)/10^30)
theorem v2188_mb_checked : Scalar.distance (sourceCoefficient 25 89 3 1) v2188_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2188_mg : Scalar.QComplex := ((-93086157234327433596124 : Int)/10^30,(221864505647524959533 : Int)/10^30)
theorem v2188_mg_checked : Scalar.distance (sourceCoefficient 25 89 3 2) v2188_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2188_upper : Scalar.QComplex := ((999994730505486015512079183319 : Int)/10^30,(-3246376635634957087105764522 : Int)/10^30)
theorem v2188_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 89 5) 1) 14) v2188_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2188 : Material (25 : Basis) (89 : Basis) where
  plus := ![v2188_pa,v2188_pb,v2188_pg]
  minus := ![(Primitive.Addresses.material2188 1).one,v2188_mb,v2188_mg]
  upper := v2188_upper
  lower := (Primitive.Addresses.material2188 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2188_pa_checked.trans (by decide +kernel)
    · exact v2188_pb_checked.trans (by decide +kernel)
    · exact v2188_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 89 Primitive.Addresses.material2188
    · exact v2188_mb_checked.trans (by decide +kernel)
    · exact v2188_mg_checked.trans (by decide +kernel)
  upper_error := v2188_upper_checked
  lower_error := reuse_lower_error 25 89 Primitive.Addresses.material2188

def v2189_pa : Scalar.QComplex := ((999998803898240960375726756052 : Int)/10^30,(-1546674525367192620460875354 : Int)/10^30)
theorem v2189_pa_checked : Scalar.distance (sourceCoefficient 25 90 1 0) v2189_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2189_pb : Scalar.QComplex := ((-667355165421463323383481 : Int)/10^30,(-431476924363476482595028390 : Int)/10^30)
theorem v2189_pb_checked : Scalar.distance (sourceCoefficient 25 90 1 1) v2189_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2189_pg : Scalar.QComplex := ((-93086309867669272287723 : Int)/10^30,(143974396340789510508 : Int)/10^30)
theorem v2189_pg_checked : Scalar.distance (sourceCoefficient 25 90 1 2) v2189_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2189_mb : Scalar.QComplex := ((-1039700069661029315297645 : Int)/10^30,(-431476187807446874643507496 : Int)/10^30)
theorem v2189_mb_checked : Scalar.distance (sourceCoefficient 25 90 3 1) v2189_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2189_mg : Scalar.QComplex := ((-93086150963962178027920 : Int)/10^30,(224303635696575065057 : Int)/10^30)
theorem v2189_mg_checked : Scalar.distance (sourceCoefficient 25 90 3 2) v2189_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2189_upper : Scalar.QComplex := ((999994645097573098236604609555 : Int)/10^30,(-3272579438122705853835773001 : Int)/10^30)
theorem v2189_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 90 5) 1) 14) v2189_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2189 : Material (25 : Basis) (90 : Basis) where
  plus := ![v2189_pa,v2189_pb,v2189_pg]
  minus := ![(Primitive.Addresses.material2189 1).one,v2189_mb,v2189_mg]
  upper := v2189_upper
  lower := (Primitive.Addresses.material2189 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2189_pa_checked.trans (by decide +kernel)
    · exact v2189_pb_checked.trans (by decide +kernel)
    · exact v2189_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 90 Primitive.Addresses.material2189
    · exact v2189_mb_checked.trans (by decide +kernel)
    · exact v2189_mg_checked.trans (by decide +kernel)
  upper_error := v2189_upper_checked
  lower_error := reuse_lower_error 25 90 Primitive.Addresses.material2189

def v2190_pa : Scalar.QComplex := ((999998780958724019080338208812 : Int)/10^30,(-1561435578530285308419057256 : Int)/10^30)
theorem v2190_pa_checked : Scalar.distance (sourceCoefficient 25 91 1 0) v2190_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2190_pb : Scalar.QComplex := ((-673724223325909164418969 : Int)/10^30,(-431476912203076773036916505 : Int)/10^30)
theorem v2190_pb_checked : Scalar.distance (sourceCoefficient 25 91 1 1) v2190_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2190_pg : Scalar.QComplex := ((-93086307488255556189875 : Int)/10^30,(145348449571931771883 : Int)/10^30)
theorem v2190_pg_checked : Scalar.distance (sourceCoefficient 25 91 1 2) v2190_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2190_mb : Scalar.QComplex := ((-1046069114700106552905333 : Int)/10^30,(-431476170150841573140784264 : Int)/10^30)
theorem v2190_mb_checked : Scalar.distance (sourceCoefficient 25 91 3 1) v2190_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2190_mg : Scalar.QComplex := ((-93086147398803294479021 : Int)/10^30,(225677686362767638966 : Int)/10^30)
theorem v2190_mg_checked : Scalar.distance (sourceCoefficient 25 91 3 2) v2190_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2190_upper : Scalar.QComplex := ((999994596681851675441440434137 : Int)/10^30,(-3287340429709418626520386760 : Int)/10^30)
theorem v2190_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 91 5) 1) 14) v2190_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2190 : Material (25 : Basis) (91 : Basis) where
  plus := ![v2190_pa,v2190_pb,v2190_pg]
  minus := ![(Primitive.Addresses.material2190 1).one,v2190_mb,v2190_mg]
  upper := v2190_upper
  lower := (Primitive.Addresses.material2190 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2190_pa_checked.trans (by decide +kernel)
    · exact v2190_pb_checked.trans (by decide +kernel)
    · exact v2190_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 91 Primitive.Addresses.material2190
    · exact v2190_mb_checked.trans (by decide +kernel)
    · exact v2190_mg_checked.trans (by decide +kernel)
  upper_error := v2190_upper_checked
  lower_error := reuse_lower_error 25 91 Primitive.Addresses.material2190

def v2191_pa : Scalar.QComplex := ((999998730550729603949501451700 : Int)/10^30,(-1593391643410574338271176898 : Int)/10^30)
theorem v2191_pa_checked : Scalar.distance (sourceCoefficient 25 92 1 0) v2191_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2191_pb : Scalar.QComplex := ((-687512536359485936539550 : Int)/10^30,(-431476885447707177493956034 : Int)/10^30)
theorem v2191_pb_checked : Scalar.distance (sourceCoefficient 25 92 1 1) v2191_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2191_pg : Scalar.QComplex := ((-93086302256020149716207 : Int)/10^30,(148323124419415477038 : Int)/10^30)
theorem v2191_pg_checked : Scalar.distance (sourceCoefficient 25 92 1 2) v2191_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2191_mb : Scalar.QComplex := ((-1059857399510985281749929 : Int)/10^30,(-431476131496788794434284104 : Int)/10^30)
theorem v2191_mb_checked : Scalar.distance (sourceCoefficient 25 92 3 1) v2191_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2191_mg : Scalar.QComplex := ((-93086139599559417209050 : Int)/10^30,(228652355587460444394 : Int)/10^30)
theorem v2191_mg_checked : Scalar.distance (sourceCoefficient 25 92 3 2) v2191_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2191_upper : Scalar.QComplex := ((999994491120663385278028564339 : Int)/10^30,(-3319296359995277457269900222 : Int)/10^30)
theorem v2191_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 92 5) 1) 14) v2191_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2191 : Material (25 : Basis) (92 : Basis) where
  plus := ![v2191_pa,v2191_pb,v2191_pg]
  minus := ![(Primitive.Addresses.material2191 1).one,v2191_mb,v2191_mg]
  upper := v2191_upper
  lower := (Primitive.Addresses.material2191 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2191_pa_checked.trans (by decide +kernel)
    · exact v2191_pb_checked.trans (by decide +kernel)
    · exact v2191_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 92 Primitive.Addresses.material2191
    · exact v2191_mb_checked.trans (by decide +kernel)
    · exact v2191_mg_checked.trans (by decide +kernel)
  upper_error := v2191_upper_checked
  lower_error := reuse_lower_error 25 92 Primitive.Addresses.material2191

def v2192_pa : Scalar.QComplex := ((999998669401201766065178306360 : Int)/10^30,(-1631317205810907819775651670 : Int)/10^30)
theorem v2192_pa_checked : Scalar.distance (sourceCoefficient 25 93 1 0) v2192_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2192_pb : Scalar.QComplex := ((-703876550674377001159741 : Int)/10^30,(-431476852931981805887743341 : Int)/10^30)
theorem v2192_pb_checked : Scalar.distance (sourceCoefficient 25 93 1 1) v2192_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2192_pg : Scalar.QComplex := ((-93086295902473202388029 : Int)/10^30,(151853478186965525588 : Int)/10^30)
theorem v2192_pg_checked : Scalar.distance (sourceCoefficient 25 93 1 2) v2192_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2192_mb : Scalar.QComplex := ((-1076221379673199402747831 : Int)/10^30,(-431476084859668184013405992 : Int)/10^30)
theorem v2192_mb_checked : Scalar.distance (sourceCoefficient 25 93 3 1) v2192_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2192_mg : Scalar.QComplex := ((-93086130199478535432367 : Int)/10^30,(232182702557673577735 : Int)/10^30)
theorem v2192_mg_checked : Scalar.distance (sourceCoefficient 25 93 3 2) v2192_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2192_upper : Scalar.QComplex := ((999994364515146499601323837715 : Int)/10^30,(-3357221760371403186630230399 : Int)/10^30)
theorem v2192_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 93 5) 1) 14) v2192_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2192 : Material (25 : Basis) (93 : Basis) where
  plus := ![v2192_pa,v2192_pb,v2192_pg]
  minus := ![(Primitive.Addresses.material2192 1).one,v2192_mb,v2192_mg]
  upper := v2192_upper
  lower := (Primitive.Addresses.material2192 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2192_pa_checked.trans (by decide +kernel)
    · exact v2192_pb_checked.trans (by decide +kernel)
    · exact v2192_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 93 Primitive.Addresses.material2192
    · exact v2192_mb_checked.trans (by decide +kernel)
    · exact v2192_mg_checked.trans (by decide +kernel)
  upper_error := v2192_upper_checked
  lower_error := reuse_lower_error 25 93 Primitive.Addresses.material2192

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
