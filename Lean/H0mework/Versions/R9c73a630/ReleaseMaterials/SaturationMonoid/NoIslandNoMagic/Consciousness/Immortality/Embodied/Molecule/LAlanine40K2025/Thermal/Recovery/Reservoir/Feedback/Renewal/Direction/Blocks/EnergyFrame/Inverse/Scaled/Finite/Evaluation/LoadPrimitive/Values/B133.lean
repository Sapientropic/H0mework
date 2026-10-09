import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B088
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B089

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2129_pa : Scalar.QComplex := ((999999861389841238336562136101 : Int)/10^30,(-526517139617079097983045143 : Int)/10^30)
theorem v2129_pa_checked : Scalar.distance (sourceCoefficient 25 30 1 0) v2129_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2129_pb : Scalar.QComplex := ((-227180310111174309305512 : Int)/10^30,(-431477461088725802680968099 : Int)/10^30)
theorem v2129_pb_checked : Scalar.distance (sourceCoefficient 25 30 1 1) v2129_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2129_pg : Scalar.QComplex := ((-93086416982950915113141 : Int)/10^30,(49011600800571777960 : Int)/10^30)
theorem v2129_pg_checked : Scalar.distance (sourceCoefficient 25 30 1 2) v2129_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2129_mb : Scalar.QComplex := ((-599525841417672873283609 : Int)/10^30,(-431477104383571740614738285 : Int)/10^30)
theorem v2129_mb_checked : Scalar.distance (sourceCoefficient 25 30 3 1) v2129_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2129_mg : Scalar.QComplex := ((-93086340027819522603768 : Int)/10^30,(129340967951009890848 : Int)/10^30)
theorem v2129_mg_checked : Scalar.distance (sourceCoefficient 25 30 3 2) v2129_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2129_upper : Scalar.QComplex := ((999997463286698216286156040884 : Int)/10^30,(-2252425396911749492780021555 : Int)/10^30)
theorem v2129_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 30 5) 1) 14) v2129_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2129 : Material (25 : Basis) (30 : Basis) where
  plus := ![v2129_pa,v2129_pb,v2129_pg]
  minus := ![(Primitive.Addresses.material2129 1).one,v2129_mb,v2129_mg]
  upper := v2129_upper
  lower := (Primitive.Addresses.material2129 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2129_pa_checked.trans (by decide +kernel)
    · exact v2129_pb_checked.trans (by decide +kernel)
    · exact v2129_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 30 Primitive.Addresses.material2129
    · exact v2129_mb_checked.trans (by decide +kernel)
    · exact v2129_mg_checked.trans (by decide +kernel)
  upper_error := v2129_upper_checked
  lower_error := reuse_lower_error 25 30 Primitive.Addresses.material2129

def v2130_pa : Scalar.QComplex := ((999999855486546712586436135230 : Int)/10^30,(-537612207535030724655605880 : Int)/10^30)
theorem v2130_pa_checked : Scalar.distance (sourceCoefficient 25 31 1 0) v2130_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2130_pb : Scalar.QComplex := ((-231967582473080645263974 : Int)/10^30,(-431477458471828475552899066 : Int)/10^30)
theorem v2130_pb_checked : Scalar.distance (sourceCoefficient 25 31 1 1) v2130_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2130_pg : Scalar.QComplex := ((-93086416425909503172503 : Int)/10^30,(50044401058347567461 : Int)/10^30)
theorem v2130_pg_checked : Scalar.distance (sourceCoefficient 25 31 1 2) v2130_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2130_mb : Scalar.QComplex := ((-604313109738794387117896 : Int)/10^30,(-431477097635474950295307571 : Int)/10^30)
theorem v2130_mb_checked : Scalar.distance (sourceCoefficient 25 31 3 1) v2130_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2130_mg : Scalar.QComplex := ((-93086338579518211211469 : Int)/10^30,(130373767343525292785 : Int)/10^30)
theorem v2130_mg_checked : Scalar.distance (sourceCoefficient 25 31 3 2) v2130_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2130_upper : Scalar.QComplex := ((999997438234331793114152189364 : Int)/10^30,(-2263520438116349965145617843 : Int)/10^30)
theorem v2130_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 31 5) 1) 14) v2130_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2130 : Material (25 : Basis) (31 : Basis) where
  plus := ![v2130_pa,v2130_pb,v2130_pg]
  minus := ![(Primitive.Addresses.material2130 1).one,v2130_mb,v2130_mg]
  upper := v2130_upper
  lower := (Primitive.Addresses.material2130 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2130_pa_checked.trans (by decide +kernel)
    · exact v2130_pb_checked.trans (by decide +kernel)
    · exact v2130_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 31 Primitive.Addresses.material2130
    · exact v2130_mb_checked.trans (by decide +kernel)
    · exact v2130_mg_checked.trans (by decide +kernel)
  upper_error := v2130_upper_checked
  lower_error := reuse_lower_error 25 31 Primitive.Addresses.material2130

def v2131_pa : Scalar.QComplex := ((999999852907456871823219877922 : Int)/10^30,(-542388296905581579427676885 : Int)/10^30)
theorem v2131_pa_checked : Scalar.distance (sourceCoefficient 25 32 1 0) v2131_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2131_pb : Scalar.QComplex := ((-234028357654686024663188 : Int)/10^30,(-431477457323529149003656951 : Int)/10^30)
theorem v2131_pb_checked : Scalar.distance (sourceCoefficient 25 32 1 1) v2131_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2131_pg : Scalar.QComplex := ((-93086416182004027915999 : Int)/10^30,(50488990164555297634 : Int)/10^30)
theorem v2131_pg_checked : Scalar.distance (sourceCoefficient 25 32 1 2) v2131_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2131_mb : Scalar.QComplex := ((-606373883162148382996767 : Int)/10^30,(-431477094708819883453708925 : Int)/10^30)
theorem v2131_mb_checked : Scalar.distance (sourceCoefficient 25 32 3 1) v2131_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2131_mg : Scalar.QComplex := ((-93086337951952451664885 : Int)/10^30,(130818356073712739939 : Int)/10^30)
theorem v2131_mg_checked : Scalar.distance (sourceCoefficient 25 32 3 2) v2131_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2131_upper : Scalar.QComplex := ((999997427412148823474589096729 : Int)/10^30,(-2268296515922201649395830961 : Int)/10^30)
theorem v2131_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 32 5) 1) 14) v2131_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2131 : Material (25 : Basis) (32 : Basis) where
  plus := ![v2131_pa,v2131_pb,v2131_pg]
  minus := ![(Primitive.Addresses.material2131 1).one,v2131_mb,v2131_mg]
  upper := v2131_upper
  lower := (Primitive.Addresses.material2131 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2131_pa_checked.trans (by decide +kernel)
    · exact v2131_pb_checked.trans (by decide +kernel)
    · exact v2131_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 32 Primitive.Addresses.material2131
    · exact v2131_mb_checked.trans (by decide +kernel)
    · exact v2131_mg_checked.trans (by decide +kernel)
  upper_error := v2131_upper_checked
  lower_error := reuse_lower_error 25 32 Primitive.Addresses.material2131

def v2132_pa : Scalar.QComplex := ((999999849275104641093498999798 : Int)/10^30,(-549044413503879411840217444 : Int)/10^30)
theorem v2132_pa_checked : Scalar.distance (sourceCoefficient 25 33 1 0) v2132_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2132_pb : Scalar.QComplex := ((-236900322312460508370903 : Int)/10^30,(-431477455701332509020484749 : Int)/10^30)
theorem v2132_pb_checked : Scalar.distance (sourceCoefficient 25 33 1 1) v2132_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2132_pg : Scalar.QComplex := ((-93086415837957322983756 : Int)/10^30,(51108584292265529373 : Int)/10^30)
theorem v2132_pg_checked : Scalar.distance (sourceCoefficient 25 33 1 2) v2132_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2132_mb : Scalar.QComplex := ((-609245845350676530065075 : Int)/10^30,(-431477090608247696315649037 : Int)/10^30)
theorem v2132_mb_checked : Scalar.distance (sourceCoefficient 25 33 3 1) v2132_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2132_mg : Scalar.QComplex := ((-93086337073224048106635 : Int)/10^30,(131437949673822950013 : Int)/10^30)
theorem v2132_mg_checked : Scalar.distance (sourceCoefficient 25 33 3 2) v2132_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2132_upper : Scalar.QComplex := ((999997412291948592225643648033 : Int)/10^30,(-2274952616337885265204397798 : Int)/10^30)
theorem v2132_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 33 5) 1) 14) v2132_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2132 : Material (25 : Basis) (33 : Basis) where
  plus := ![v2132_pa,v2132_pb,v2132_pg]
  minus := ![(Primitive.Addresses.material2132 1).one,v2132_mb,v2132_mg]
  upper := v2132_upper
  lower := (Primitive.Addresses.material2132 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2132_pa_checked.trans (by decide +kernel)
    · exact v2132_pb_checked.trans (by decide +kernel)
    · exact v2132_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 33 Primitive.Addresses.material2132
    · exact v2132_mb_checked.trans (by decide +kernel)
    · exact v2132_mg_checked.trans (by decide +kernel)
  upper_error := v2132_upper_checked
  lower_error := reuse_lower_error 25 33 Primitive.Addresses.material2132

def v2133_pa : Scalar.QComplex := ((999999840268037340003352873490 : Int)/10^30,(-565211376217511565966026137 : Int)/10^30)
theorem v2133_pa_checked : Scalar.distance (sourceCoefficient 25 34 1 0) v2133_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2133_pb : Scalar.QComplex := ((-243876003211574252348163 : Int)/10^30,(-431477451655060597186634253 : Int)/10^30)
theorem v2133_pb_checked : Scalar.distance (sourceCoefficient 25 34 1 1) v2133_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2133_pg : Scalar.QComplex := ((-93086414982270589923620 : Int)/10^30,(52613509123342622329 : Int)/10^30)
theorem v2133_pg_checked : Scalar.distance (sourceCoefficient 25 34 1 2) v2133_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2133_mb : Scalar.QComplex := ((-616221520160675048345271 : Int)/10^30,(-431477080542278848163639955 : Int)/10^30)
theorem v2133_mb_checked : Scalar.distance (sourceCoefficient 25 34 3 1) v2133_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2133_mg : Scalar.QComplex := ((-93086334918855283736551 : Int)/10^30,(132942873206128637966 : Int)/10^30)
theorem v2133_mg_checked : Scalar.distance (sourceCoefficient 25 34 3 2) v2133_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2133_upper : Scalar.QComplex := ((999997375382183717775597481254 : Int)/10^30,(-2291119539427344515301307874 : Int)/10^30)
theorem v2133_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 34 5) 1) 14) v2133_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2133 : Material (25 : Basis) (34 : Basis) where
  plus := ![v2133_pa,v2133_pb,v2133_pg]
  minus := ![(Primitive.Addresses.material2133 1).one,v2133_mb,v2133_mg]
  upper := v2133_upper
  lower := (Primitive.Addresses.material2133 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2133_pa_checked.trans (by decide +kernel)
    · exact v2133_pb_checked.trans (by decide +kernel)
    · exact v2133_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 34 Primitive.Addresses.material2133
    · exact v2133_mb_checked.trans (by decide +kernel)
    · exact v2133_mg_checked.trans (by decide +kernel)
  upper_error := v2133_upper_checked
  lower_error := reuse_lower_error 25 34 Primitive.Addresses.material2133

def v2134_pa : Scalar.QComplex := ((999999809918559153697918154812 : Int)/10^30,(-616573471341128987990281254 : Int)/10^30)
theorem v2134_pa_checked : Scalar.distance (sourceCoefficient 25 35 1 0) v2134_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2134_pb : Scalar.QComplex := ((-266037592200035313697834 : Int)/10^30,(-431477437802439942045446071 : Int)/10^30)
theorem v2134_pb_checked : Scalar.distance (sourceCoefficient 25 35 1 1) v2134_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2134_pg : Scalar.QComplex := ((-93086412075434629395154 : Int)/10^30,(57394623137694179670 : Int)/10^30)
theorem v2134_pg_checked : Scalar.distance (sourceCoefficient 25 35 1 2) v2134_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2134_mb : Scalar.QComplex := ((-638383088943175968126317 : Int)/10^30,(-431477047565210174860372014 : Int)/10^30)
theorem v2134_mb_checked : Scalar.distance (sourceCoefficient 25 35 3 1) v2134_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2134_mg : Scalar.QComplex := ((-93086327886134344552224 : Int)/10^30,(137723982931784425154 : Int)/10^30)
theorem v2134_mg_checked : Scalar.distance (sourceCoefficient 25 35 3 2) v2134_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2134_upper : Scalar.QComplex := ((999997256386434082960491968557 : Int)/10^30,(-2342481505672708599805370691 : Int)/10^30)
theorem v2134_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 35 5) 1) 14) v2134_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2134 : Material (25 : Basis) (35 : Basis) where
  plus := ![v2134_pa,v2134_pb,v2134_pg]
  minus := ![(Primitive.Addresses.material2134 1).one,v2134_mb,v2134_mg]
  upper := v2134_upper
  lower := (Primitive.Addresses.material2134 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2134_pa_checked.trans (by decide +kernel)
    · exact v2134_pb_checked.trans (by decide +kernel)
    · exact v2134_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 35 Primitive.Addresses.material2134
    · exact v2134_mb_checked.trans (by decide +kernel)
    · exact v2134_mg_checked.trans (by decide +kernel)
  upper_error := v2134_upper_checked
  lower_error := reuse_lower_error 25 35 Primitive.Addresses.material2134

def v2135_pa : Scalar.QComplex := ((999999799833697850275047461622 : Int)/10^30,(-632718392519848745373225892 : Int)/10^30)
theorem v2135_pa_checked : Scalar.distance (sourceCoefficient 25 36 1 0) v2135_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2135_pb : Scalar.QComplex := ((-273003762547643860377200 : Int)/10^30,(-431477433134561443224005681 : Int)/10^30)
theorem v2135_pb_checked : Scalar.distance (sourceCoefficient 25 36 1 1) v2135_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2135_pg : Scalar.QComplex := ((-93086411102531578134405 : Int)/10^30,(58897496187529599005 : Int)/10^30)
theorem v2135_pg_checked : Scalar.distance (sourceCoefficient 25 36 1 2) v2135_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2135_mb : Scalar.QComplex := ((-645349252668792013638804 : Int)/10^30,(-431477036885842148782960375 : Int)/10^30)
theorem v2135_mb_checked : Scalar.distance (sourceCoefficient 25 36 3 1) v2135_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2135_mg : Scalar.QComplex := ((-93086325616319900429287 : Int)/10^30,(139226854582460008032 : Int)/10^30)
theorem v2135_mg_checked : Scalar.distance (sourceCoefficient 25 36 3 2) v2135_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2135_upper : Scalar.QComplex := ((999997218436918501091650616744 : Int)/10^30,(-2358626385399909058912680129 : Int)/10^30)
theorem v2135_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 36 5) 1) 14) v2135_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2135 : Material (25 : Basis) (36 : Basis) where
  plus := ![v2135_pa,v2135_pb,v2135_pg]
  minus := ![(Primitive.Addresses.material2135 1).one,v2135_mb,v2135_mg]
  upper := v2135_upper
  lower := (Primitive.Addresses.material2135 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2135_pa_checked.trans (by decide +kernel)
    · exact v2135_pb_checked.trans (by decide +kernel)
    · exact v2135_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 36 Primitive.Addresses.material2135
    · exact v2135_mb_checked.trans (by decide +kernel)
    · exact v2135_mg_checked.trans (by decide +kernel)
  upper_error := v2135_upper_checked
  lower_error := reuse_lower_error 25 36 Primitive.Addresses.material2135

def v2136_pa : Scalar.QComplex := ((999999795447937290598357975142 : Int)/10^30,(-639612447953647103954256329 : Int)/10^30)
theorem v2136_pa_checked : Scalar.distance (sourceCoefficient 25 37 1 0) v2136_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2136_pb : Scalar.QComplex := ((-275978392391781978245054 : Int)/10^30,(-431477431095638682427698253 : Int)/10^30)
theorem v2136_pb_checked : Scalar.distance (sourceCoefficient 25 37 1 1) v2136_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2136_pg : Scalar.QComplex := ((-93086410678466837006780 : Int)/10^30,(59539239184146877053 : Int)/10^30)
theorem v2136_pg_checked : Scalar.distance (sourceCoefficient 25 37 1 2) v2136_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2136_mb : Scalar.QComplex := ((-648323879645840980339282 : Int)/10^30,(-431477032279948564034476842 : Int)/10^30)
theorem v2136_mb_checked : Scalar.distance (sourceCoefficient 25 37 3 1) v2136_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2136_mg : Scalar.QComplex := ((-93086324638460014151271 : Int)/10^30,(139868596974178266910 : Int)/10^30)
theorem v2136_mg_checked : Scalar.distance (sourceCoefficient 25 37 3 2) v2136_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2136_upper : Scalar.QComplex := ((999997202152650218577571621868 : Int)/10^30,(-2365520422996396828577943361 : Int)/10^30)
theorem v2136_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 37 5) 1) 14) v2136_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2136 : Material (25 : Basis) (37 : Basis) where
  plus := ![v2136_pa,v2136_pb,v2136_pg]
  minus := ![(Primitive.Addresses.material2136 1).one,v2136_mb,v2136_mg]
  upper := v2136_upper
  lower := (Primitive.Addresses.material2136 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2136_pa_checked.trans (by decide +kernel)
    · exact v2136_pb_checked.trans (by decide +kernel)
    · exact v2136_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 37 Primitive.Addresses.material2136
    · exact v2136_mb_checked.trans (by decide +kernel)
    · exact v2136_mg_checked.trans (by decide +kernel)
  upper_error := v2136_upper_checked
  lower_error := reuse_lower_error 25 37 Primitive.Addresses.material2136

def v2137_pa : Scalar.QComplex := ((999999780272848783888296745256 : Int)/10^30,(-662913459021765845578491284 : Int)/10^30)
theorem v2137_pa_checked : Scalar.distance (sourceCoefficient 25 38 1 0) v2137_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2137_pb : Scalar.QComplex := ((-286032254483992853829833 : Int)/10^30,(-431477424001960034362129488 : Int)/10^30)
theorem v2137_pb_checked : Scalar.distance (sourceCoefficient 25 38 1 1) v2137_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2137_pg : Scalar.QComplex := ((-93086409206978676197405 : Int)/10^30,(61708247074291121759 : Int)/10^30)
theorem v2137_pg_checked : Scalar.distance (sourceCoefficient 25 38 1 2) v2137_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2137_mb : Scalar.QComplex := ((-658377731873014328943150 : Int)/10^30,(-431477016510242380831248052 : Int)/10^30)
theorem v2137_mb_checked : Scalar.distance (sourceCoefficient 25 38 3 1) v2137_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2137_mg : Scalar.QComplex := ((-93086321295216280538711 : Int)/10^30,(142037602786873736146 : Int)/10^30)
theorem v2137_mg_checked : Scalar.distance (sourceCoefficient 25 38 3 2) v2137_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2137_upper : Scalar.QComplex := ((999997146762153061017902223620 : Int)/10^30,(-2388821373169570623965983197 : Int)/10^30)
theorem v2137_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 38 5) 1) 14) v2137_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2137 : Material (25 : Basis) (38 : Basis) where
  plus := ![v2137_pa,v2137_pb,v2137_pg]
  minus := ![(Primitive.Addresses.material2137 1).one,v2137_mb,v2137_mg]
  upper := v2137_upper
  lower := (Primitive.Addresses.material2137 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2137_pa_checked.trans (by decide +kernel)
    · exact v2137_pb_checked.trans (by decide +kernel)
    · exact v2137_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 38 Primitive.Addresses.material2137
    · exact v2137_mb_checked.trans (by decide +kernel)
    · exact v2137_mg_checked.trans (by decide +kernel)
  upper_error := v2137_upper_checked
  lower_error := reuse_lower_error 25 38 Primitive.Addresses.material2137

def v2138_pa : Scalar.QComplex := ((999999771220626628556156059340 : Int)/10^30,(-676430849683015276099790854 : Int)/10^30)
theorem v2138_pa_checked : Scalar.distance (sourceCoefficient 25 39 1 0) v2138_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2138_pb : Scalar.QComplex := ((-291864704428830437894104 : Int)/10^30,(-431477419743611634790472147 : Int)/10^30)
theorem v2138_pb_checked : Scalar.distance (sourceCoefficient 25 39 1 1) v2138_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2138_pg : Scalar.QComplex := ((-93086408326313730842072 : Int)/10^30,(62966532683552395594 : Int)/10^30)
theorem v2138_pg_checked : Scalar.distance (sourceCoefficient 25 39 1 2) v2138_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2138_mb : Scalar.QComplex := ((-664210175971401362475808 : Int)/10^30,(-431477007218753948236715639 : Int)/10^30)
theorem v2138_mb_checked : Scalar.distance (sourceCoefficient 25 39 3 1) v2138_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2138_mg : Scalar.QComplex := ((-93086319328707853382818 : Int)/10^30,(143295887167643586994 : Int)/10^30)
theorem v2138_mg_checked : Scalar.distance (sourceCoefficient 25 39 3 2) v2138_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2138_upper : Scalar.QComplex := ((999997114380154394692347706755 : Int)/10^30,(-2402338728074940299880413405 : Int)/10^30)
theorem v2138_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 39 5) 1) 14) v2138_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2138 : Material (25 : Basis) (39 : Basis) where
  plus := ![v2138_pa,v2138_pb,v2138_pg]
  minus := ![(Primitive.Addresses.material2138 1).one,v2138_mb,v2138_mg]
  upper := v2138_upper
  lower := (Primitive.Addresses.material2138 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2138_pa_checked.trans (by decide +kernel)
    · exact v2138_pb_checked.trans (by decide +kernel)
    · exact v2138_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 39 Primitive.Addresses.material2138
    · exact v2138_mb_checked.trans (by decide +kernel)
    · exact v2138_mg_checked.trans (by decide +kernel)
  upper_error := v2138_upper_checked
  lower_error := reuse_lower_error 25 39 Primitive.Addresses.material2138

def v2139_pa : Scalar.QComplex := ((999999755583182571031235965365 : Int)/10^30,(-699166342953060696001794147 : Int)/10^30)
theorem v2139_pa_checked : Scalar.distance (sourceCoefficient 25 40 1 0) v2139_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2139_pb : Scalar.QComplex := ((-301674558189892045035987 : Int)/10^30,(-431477412344217894365538299 : Int)/10^30)
theorem v2139_pb_checked : Scalar.distance (sourceCoefficient 25 40 1 1) v2139_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2139_pg : Scalar.QComplex := ((-93086406800328757233137 : Int)/10^30,(65082898528581704654 : Int)/10^30)
theorem v2139_pg_checked : Scalar.distance (sourceCoefficient 25 40 1 2) v2139_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2139_mb : Scalar.QComplex := ((-674020019694462540245795 : Int)/10^30,(-431476991353900986560364077 : Int)/10^30)
theorem v2139_mb_checked : Scalar.distance (sourceCoefficient 25 40 3 1) v2139_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2139_mg : Scalar.QComplex := ((-93086315976395041286841 : Int)/10^30,(145412250907796864840 : Int)/10^30)
theorem v2139_mg_checked : Scalar.distance (sourceCoefficient 25 40 3 2) v2139_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2139_upper : Scalar.QComplex := ((999997059503334791042772329458 : Int)/10^30,(-2425074160494329367250862960 : Int)/10^30)
theorem v2139_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 40 5) 1) 14) v2139_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2139 : Material (25 : Basis) (40 : Basis) where
  plus := ![v2139_pa,v2139_pb,v2139_pg]
  minus := ![(Primitive.Addresses.material2139 1).one,v2139_mb,v2139_mg]
  upper := v2139_upper
  lower := (Primitive.Addresses.material2139 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2139_pa_checked.trans (by decide +kernel)
    · exact v2139_pb_checked.trans (by decide +kernel)
    · exact v2139_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 40 Primitive.Addresses.material2139
    · exact v2139_mb_checked.trans (by decide +kernel)
    · exact v2139_mg_checked.trans (by decide +kernel)
  upper_error := v2139_upper_checked
  lower_error := reuse_lower_error 25 40 Primitive.Addresses.material2139

def v2140_pa : Scalar.QComplex := ((999999745351568184283714290539 : Int)/10^30,(-713650333696838360285493030 : Int)/10^30)
theorem v2140_pa_checked : Scalar.distance (sourceCoefficient 25 41 1 0) v2140_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2140_pb : Scalar.QComplex := ((-307924074239743366487685 : Int)/10^30,(-431477407475252637352228190 : Int)/10^30)
theorem v2140_pb_checked : Scalar.distance (sourceCoefficient 25 41 1 1) v2140_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2140_pg : Scalar.QComplex := ((-93086405798904240760408 : Int)/10^30,(66431161477618414808 : Int)/10^30)
theorem v2140_pg_checked : Scalar.distance (sourceCoefficient 25 41 1 2) v2140_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2140_mb : Scalar.QComplex := ((-680269529215635692596862 : Int)/10^30,(-431476981091886659217962571 : Int)/10^30)
theorem v2140_mb_checked : Scalar.distance (sourceCoefficient 25 41 3 1) v2140_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2140_mg : Scalar.QComplex := ((-93086313811480696180608 : Int)/10^30,(146760512490629405177 : Int)/10^30)
theorem v2140_mg_checked : Scalar.distance (sourceCoefficient 25 41 3 2) v2140_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2140_upper : Scalar.QComplex := ((999997024273681596698788839715 : Int)/10^30,(-2439558112007066001028168826 : Int)/10^30)
theorem v2140_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 41 5) 1) 14) v2140_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2140 : Material (25 : Basis) (41 : Basis) where
  plus := ![v2140_pa,v2140_pb,v2140_pg]
  minus := ![(Primitive.Addresses.material2140 1).one,v2140_mb,v2140_mg]
  upper := v2140_upper
  lower := (Primitive.Addresses.material2140 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2140_pa_checked.trans (by decide +kernel)
    · exact v2140_pb_checked.trans (by decide +kernel)
    · exact v2140_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 41 Primitive.Addresses.material2140
    · exact v2140_mb_checked.trans (by decide +kernel)
    · exact v2140_mg_checked.trans (by decide +kernel)
  upper_error := v2140_upper_checked
  lower_error := reuse_lower_error 25 41 Primitive.Addresses.material2140

def v2141_pa : Scalar.QComplex := ((999999736945273681935892324819 : Int)/10^30,(-725333980617438863609783033 : Int)/10^30)
theorem v2141_pa_checked : Scalar.distance (sourceCoefficient 25 42 1 0) v2141_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2141_pb : Scalar.QComplex := ((-312965304924911774458140 : Int)/10^30,(-431477403459711376985989677 : Int)/10^30)
theorem v2141_pb_checked : Scalar.distance (sourceCoefficient 25 42 1 1) v2141_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2141_pg : Scalar.QComplex := ((-93086404974494301847646 : Int)/10^30,(67518750422643328318 : Int)/10^30)
theorem v2141_pg_checked : Scalar.distance (sourceCoefficient 25 42 1 2) v2141_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2141_mb : Scalar.QComplex := ((-685310754558492266423747 : Int)/10^30,(-431476972725991861322538226 : Int)/10^30)
theorem v2141_mb_checked : Scalar.distance (sourceCoefficient 25 42 3 1) v2141_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2141_mg : Scalar.QComplex := ((-93086312048530787864586 : Int)/10^30,(147848100319266601947 : Int)/10^30)
theorem v2141_mg_checked : Scalar.distance (sourceCoefficient 25 42 3 2) v2141_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2141_upper : Scalar.QComplex := ((999996995702484961751587817712 : Int)/10^30,(-2451241727017745175722895143 : Int)/10^30)
theorem v2141_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 42 5) 1) 14) v2141_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2141 : Material (25 : Basis) (42 : Basis) where
  plus := ![v2141_pa,v2141_pb,v2141_pg]
  minus := ![(Primitive.Addresses.material2141 1).one,v2141_mb,v2141_mg]
  upper := v2141_upper
  lower := (Primitive.Addresses.material2141 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2141_pa_checked.trans (by decide +kernel)
    · exact v2141_pb_checked.trans (by decide +kernel)
    · exact v2141_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 42 Primitive.Addresses.material2141
    · exact v2141_mb_checked.trans (by decide +kernel)
    · exact v2141_mg_checked.trans (by decide +kernel)
  upper_error := v2141_upper_checked
  lower_error := reuse_lower_error 25 42 Primitive.Addresses.material2141

def v2142_pa : Scalar.QComplex := ((999999725598926804064264599086 : Int)/10^30,(-740811764955121713488535257 : Int)/10^30)
theorem v2142_pa_checked : Scalar.distance (sourceCoefficient 25 43 1 0) v2142_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2142_pb : Scalar.QComplex := ((-319643620475427906271093 : Int)/10^30,(-431477398019238225611638282 : Int)/10^30)
theorem v2142_pb_checked : Scalar.distance (sourceCoefficient 25 43 1 1) v2142_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2142_pg : Scalar.QComplex := ((-93086403859538346239576 : Int)/10^30,(68959522059076716150 : Int)/10^30)
theorem v2142_pg_checked : Scalar.distance (sourceCoefficient 25 43 1 2) v2142_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2142_mb : Scalar.QComplex := ((-691989062927483004859741 : Int)/10^30,(-431476961522435195756471852 : Int)/10^30)
theorem v2142_mb_checked : Scalar.distance (sourceCoefficient 25 43 3 1) v2142_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2142_mg : Scalar.QComplex := ((-93086309690254215109237 : Int)/10^30,(149288870457078089081 : Int)/10^30)
theorem v2142_mg_checked : Scalar.distance (sourceCoefficient 25 43 3 2) v2142_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2142_upper : Scalar.QComplex := ((999996957642903349716824890211 : Int)/10^30,(-2466719468720321024230922933 : Int)/10^30)
theorem v2142_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 43 5) 1) 14) v2142_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2142 : Material (25 : Basis) (43 : Basis) where
  plus := ![v2142_pa,v2142_pb,v2142_pg]
  minus := ![(Primitive.Addresses.material2142 1).one,v2142_mb,v2142_mg]
  upper := v2142_upper
  lower := (Primitive.Addresses.material2142 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2142_pa_checked.trans (by decide +kernel)
    · exact v2142_pb_checked.trans (by decide +kernel)
    · exact v2142_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 43 Primitive.Addresses.material2142
    · exact v2142_mb_checked.trans (by decide +kernel)
    · exact v2142_mg_checked.trans (by decide +kernel)
  upper_error := v2142_upper_checked
  lower_error := reuse_lower_error 25 43 Primitive.Addresses.material2142

def v2143_pa : Scalar.QComplex := ((999999721243751441088168041137 : Int)/10^30,(-746667542761018609203680841 : Int)/10^30)
theorem v2143_pa_checked : Scalar.distance (sourceCoefficient 25 44 1 0) v2143_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2143_pb : Scalar.QComplex := ((-322170256779204201900141 : Int)/10^30,(-431477395924985443010172611 : Int)/10^30)
theorem v2143_pb_checked : Scalar.distance (sourceCoefficient 25 44 1 1) v2143_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2143_pg : Scalar.QComplex := ((-93086403430928723086967 : Int)/10^30,(69504615489078272984 : Int)/10^30)
theorem v2143_pg_checked : Scalar.distance (sourceCoefficient 25 44 1 2) v2143_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2143_mb : Scalar.QComplex := ((-694515696483231301868190 : Int)/10^30,(-431476957247809858256921591 : Int)/10^30)
theorem v2143_mb_checked : Scalar.distance (sourceCoefficient 25 44 3 1) v2143_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2143_mg : Scalar.QComplex := ((-93086308791253671552981 : Int)/10^30,(149833963314245649006 : Int)/10^30)
theorem v2143_mg_checked : Scalar.distance (sourceCoefficient 25 44 3 2) v2143_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2143_upper : Scalar.QComplex := ((999996943181193212297588859509 : Int)/10^30,(-2472575230288087167969660254 : Int)/10^30)
theorem v2143_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 44 5) 1) 14) v2143_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2143 : Material (25 : Basis) (44 : Basis) where
  plus := ![v2143_pa,v2143_pb,v2143_pg]
  minus := ![(Primitive.Addresses.material2143 1).one,v2143_mb,v2143_mg]
  upper := v2143_upper
  lower := (Primitive.Addresses.material2143 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2143_pa_checked.trans (by decide +kernel)
    · exact v2143_pb_checked.trans (by decide +kernel)
    · exact v2143_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 44 Primitive.Addresses.material2143
    · exact v2143_mb_checked.trans (by decide +kernel)
    · exact v2143_mg_checked.trans (by decide +kernel)
  upper_error := v2143_upper_checked
  lower_error := reuse_lower_error 25 44 Primitive.Addresses.material2143

def v2144_pa : Scalar.QComplex := ((999999719064223660028137656236 : Int)/10^30,(-749580865387473252665473192 : Int)/10^30)
theorem v2144_pa_checked : Scalar.distance (sourceCoefficient 25 45 1 0) v2144_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2144_pb : Scalar.QComplex := ((-323427289908371352917164 : Int)/10^30,(-431477394875719810872695466 : Int)/10^30)
theorem v2144_pb_checked : Scalar.distance (sourceCoefficient 25 45 1 1) v2144_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2144_pg : Scalar.QComplex := ((-93086403216302854445378 : Int)/10^30,(69775806281203874528 : Int)/10^30)
theorem v2144_pg_checked : Scalar.distance (sourceCoefficient 25 45 1 2) v2144_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2144_mb : Scalar.QComplex := ((-695772728238878586279389 : Int)/10^30,(-431476955113781641008244102 : Int)/10^30)
theorem v2144_mb_checked : Scalar.distance (sourceCoefficient 25 45 3 1) v2144_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2144_mg : Scalar.QComplex := ((-93086308342602443201890 : Int)/10^30,(150105153820182066362 : Int)/10^30)
theorem v2144_mg_checked : Scalar.distance (sourceCoefficient 25 45 3 2) v2144_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2144_upper : Scalar.QComplex := ((999996935973538118691564560392 : Int)/10^30,(-2475488544813822757348953878 : Int)/10^30)
theorem v2144_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 45 5) 1) 14) v2144_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2144 : Material (25 : Basis) (45 : Basis) where
  plus := ![v2144_pa,v2144_pb,v2144_pg]
  minus := ![(Primitive.Addresses.material2144 1).one,v2144_mb,v2144_mg]
  upper := v2144_upper
  lower := (Primitive.Addresses.material2144 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2144_pa_checked.trans (by decide +kernel)
    · exact v2144_pb_checked.trans (by decide +kernel)
    · exact v2144_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 45 Primitive.Addresses.material2144
    · exact v2144_mb_checked.trans (by decide +kernel)
    · exact v2144_mg_checked.trans (by decide +kernel)
  upper_error := v2144_upper_checked
  lower_error := reuse_lower_error 25 45 Primitive.Addresses.material2144

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
