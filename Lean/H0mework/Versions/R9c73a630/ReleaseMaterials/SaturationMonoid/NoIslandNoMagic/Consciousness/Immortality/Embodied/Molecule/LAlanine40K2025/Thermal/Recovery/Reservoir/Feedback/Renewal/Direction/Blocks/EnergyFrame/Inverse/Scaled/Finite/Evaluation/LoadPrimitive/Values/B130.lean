import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B086
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B087

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2081_pa : Scalar.QComplex := ((999999647186195972075795760887 : Int)/10^30,(-840016359113480655923060382 : Int)/10^30)
theorem v2081_pa_checked : Scalar.distance (sourceCoefficient 24 54 1 0) v2081_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2081_pb : Scalar.QComplex := ((-362448166678929965350840 : Int)/10^30,(-431477357398999396006820844 : Int)/10^30)
theorem v2081_pb_checked : Scalar.distance (sourceCoefficient 24 54 1 1) v2081_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2081_pg : Scalar.QComplex := ((-93086395828277572435738 : Int)/10^30,(78194122894631971977 : Int)/10^30)
theorem v2081_pg_checked : Scalar.distance (sourceCoefficient 24 54 1 2) v2081_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2081_mb : Scalar.QComplex := ((-734793558139459605667646 : Int)/10^30,(-431476883963815962496758429 : Int)/10^30)
theorem v2081_mb_checked : Scalar.distance (sourceCoefficient 24 54 3 1) v2081_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2081_mg : Scalar.QComplex := ((-93086293689951821608938 : Int)/10^30,(158523460923553078489 : Int)/10^30)
theorem v2081_mg_checked : Scalar.distance (sourceCoefficient 24 54 3 2) v2081_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2081_upper : Scalar.QComplex := ((999996708012159557432086671079 : Int)/10^30,(-2565923779791830489386658406 : Int)/10^30)
theorem v2081_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 54 5) 1) 14) v2081_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2081 : Material (24 : Basis) (54 : Basis) where
  plus := ![v2081_pa,v2081_pb,v2081_pg]
  minus := ![(Primitive.Addresses.material2081 1).one,v2081_mb,v2081_mg]
  upper := v2081_upper
  lower := (Primitive.Addresses.material2081 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2081_pa_checked.trans (by decide +kernel)
    · exact v2081_pb_checked.trans (by decide +kernel)
    · exact v2081_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 54 Primitive.Addresses.material2081
    · exact v2081_mb_checked.trans (by decide +kernel)
    · exact v2081_mg_checked.trans (by decide +kernel)
  upper_error := v2081_upper_checked
  lower_error := reuse_lower_error 24 54 Primitive.Addresses.material2081

def v2082_pa : Scalar.QComplex := ((999999634179611371530425080949 : Int)/10^30,(-855359949630786964842854522 : Int)/10^30)
theorem v2082_pa_checked : Scalar.distance (sourceCoefficient 24 55 1 0) v2082_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2082_pb : Scalar.QComplex := ((-369068580139060028433316 : Int)/10^30,(-431477350892516856476036717 : Int)/10^30)
theorem v2082_pb_checked : Scalar.distance (sourceCoefficient 24 55 1 1) v2082_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2082_pg : Scalar.QComplex := ((-93086394521059038182410 : Int)/10^30,(79622402856342979034 : Int)/10^30)
theorem v2082_pg_checked : Scalar.distance (sourceCoefficient 24 55 1 2) v2082_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2082_mb : Scalar.QComplex := ((-741413963519705779181734 : Int)/10^30,(-431476871744217201888106478 : Int)/10^30)
theorem v2082_mb_checked : Scalar.distance (sourceCoefficient 24 55 3 1) v2082_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2082_mg : Scalar.QComplex := ((-93086291150192494477747 : Int)/10^30,(159951739225379460058 : Int)/10^30)
theorem v2082_mg_checked : Scalar.distance (sourceCoefficient 24 55 3 2) v2082_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2082_upper : Scalar.QComplex := ((999996668523949055454266446039 : Int)/10^30,(-2581267325008476035127894219 : Int)/10^30)
theorem v2082_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 55 5) 1) 14) v2082_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2082 : Material (24 : Basis) (55 : Basis) where
  plus := ![v2082_pa,v2082_pb,v2082_pg]
  minus := ![(Primitive.Addresses.material2082 1).one,v2082_mb,v2082_mg]
  upper := v2082_upper
  lower := (Primitive.Addresses.material2082 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2082_pa_checked.trans (by decide +kernel)
    · exact v2082_pb_checked.trans (by decide +kernel)
    · exact v2082_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 55 Primitive.Addresses.material2082
    · exact v2082_mb_checked.trans (by decide +kernel)
    · exact v2082_mg_checked.trans (by decide +kernel)
  upper_error := v2082_upper_checked
  lower_error := reuse_lower_error 24 55 Primitive.Addresses.material2082

def v2083_pa : Scalar.QComplex := ((999999631058218845090174321691 : Int)/10^30,(-859001412217571252113323581 : Int)/10^30)
theorem v2083_pa_checked : Scalar.distance (sourceCoefficient 24 56 1 0) v2083_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2083_pb : Scalar.QComplex := ((-370639789157545846717088 : Int)/10^30,(-431477349328460476267479253 : Int)/10^30)
theorem v2083_pb_checked : Scalar.distance (sourceCoefficient 24 56 1 1) v2083_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2083_pg : Scalar.QComplex := ((-93086394207065594707540 : Int)/10^30,(79961373583202482953 : Int)/10^30)
theorem v2083_pg_checked : Scalar.distance (sourceCoefficient 24 56 1 2) v2083_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2083_mb : Scalar.QComplex := ((-742985170603448458448145 : Int)/10^30,(-431476868824278785723245251 : Int)/10^30)
theorem v2083_mb_checked : Scalar.distance (sourceCoefficient 24 56 3 1) v2083_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2083_mg : Scalar.QComplex := ((-93086290543682697312046 : Int)/10^30,(160290709555062470660 : Int)/10^30)
theorem v2083_mg_checked : Scalar.distance (sourceCoefficient 24 56 3 2) v2083_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2083_upper : Scalar.QComplex := ((999996659117727104077152882966 : Int)/10^30,(-2584908776784489225508967468 : Int)/10^30)
theorem v2083_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 56 5) 1) 14) v2083_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2083 : Material (24 : Basis) (56 : Basis) where
  plus := ![v2083_pa,v2083_pb,v2083_pg]
  minus := ![(Primitive.Addresses.material2083 1).one,v2083_mb,v2083_mg]
  upper := v2083_upper
  lower := (Primitive.Addresses.material2083 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2083_pa_checked.trans (by decide +kernel)
    · exact v2083_pb_checked.trans (by decide +kernel)
    · exact v2083_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 56 Primitive.Addresses.material2083
    · exact v2083_mb_checked.trans (by decide +kernel)
    · exact v2083_mg_checked.trans (by decide +kernel)
  upper_error := v2083_upper_checked
  lower_error := reuse_lower_error 24 56 Primitive.Addresses.material2083

def v2084_pa : Scalar.QComplex := ((999999620871664679641750348376 : Int)/10^30,(-870779264166540576056659384 : Int)/10^30)
theorem v2084_pa_checked : Scalar.distance (sourceCoefficient 24 57 1 0) v2084_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2084_pb : Scalar.QComplex := ((-375721666748958466715307 : Int)/10^30,(-431477344217477740640030221 : Int)/10^30)
theorem v2084_pb_checked : Scalar.distance (sourceCoefficient 24 57 1 1) v2084_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2084_pg : Scalar.QComplex := ((-93086393181632049038276 : Int)/10^30,(81057731689901715961 : Int)/10^30)
theorem v2084_pg_checked : Scalar.distance (sourceCoefficient 24 57 1 2) v2084_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2084_mb : Scalar.QComplex := ((-748067041892097887154838 : Int)/10^30,(-431476859327866471029480419 : Int)/10^30)
theorem v2084_mb_checked : Scalar.distance (sourceCoefficient 24 57 3 1) v2084_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2084_mg : Scalar.QComplex := ((-93086288572141865513241 : Int)/10^30,(161387066368634508403 : Int)/10^30)
theorem v2084_mg_checked : Scalar.distance (sourceCoefficient 24 57 3 2) v2084_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2084_upper : Scalar.QComplex := ((999996628603684124765823926915 : Int)/10^30,(-2596686593610663222550762829 : Int)/10^30)
theorem v2084_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 57 5) 1) 14) v2084_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2084 : Material (24 : Basis) (57 : Basis) where
  plus := ![v2084_pa,v2084_pb,v2084_pg]
  minus := ![(Primitive.Addresses.material2084 1).one,v2084_mb,v2084_mg]
  upper := v2084_upper
  lower := (Primitive.Addresses.material2084 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2084_pa_checked.trans (by decide +kernel)
    · exact v2084_pb_checked.trans (by decide +kernel)
    · exact v2084_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 57 Primitive.Addresses.material2084
    · exact v2084_mb_checked.trans (by decide +kernel)
    · exact v2084_mg_checked.trans (by decide +kernel)
  upper_error := v2084_upper_checked
  lower_error := reuse_lower_error 24 57 Primitive.Addresses.material2084

def v2085_pa : Scalar.QComplex := ((999999615286486441618531253648 : Int)/10^30,(-877169812016051669056688721 : Int)/10^30)
theorem v2085_pa_checked : Scalar.distance (sourceCoefficient 24 58 1 0) v2085_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2085_pb : Scalar.QComplex := ((-378479044060596629468233 : Int)/10^30,(-431477341410910125129621101 : Int)/10^30)
theorem v2085_pb_checked : Scalar.distance (sourceCoefficient 24 58 1 1) v2085_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2085_pg : Scalar.QComplex := ((-93086392618937174507055 : Int)/10^30,(81652604927666033887 : Int)/10^30)
theorem v2085_pg_checked : Scalar.distance (sourceCoefficient 24 58 1 2) v2085_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2085_mb : Scalar.QComplex := ((-750824415755097009343916 : Int)/10^30,(-431476854141807468252779970 : Int)/10^30)
theorem v2085_mb_checked : Scalar.distance (sourceCoefficient 24 58 3 1) v2085_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2085_mg : Scalar.QComplex := ((-93086287496098388404491 : Int)/10^30,(161981938899319998976 : Int)/10^30)
theorem v2085_mg_checked : Scalar.distance (sourceCoefficient 24 58 3 2) v2085_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2085_upper : Scalar.QComplex := ((999996611989008362925543367632 : Int)/10^30,(-2603077122302693024770955740 : Int)/10^30)
theorem v2085_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 58 5) 1) 14) v2085_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2085 : Material (24 : Basis) (58 : Basis) where
  plus := ![v2085_pa,v2085_pb,v2085_pg]
  minus := ![(Primitive.Addresses.material2085 1).one,v2085_mb,v2085_mg]
  upper := v2085_upper
  lower := (Primitive.Addresses.material2085 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2085_pa_checked.trans (by decide +kernel)
    · exact v2085_pb_checked.trans (by decide +kernel)
    · exact v2085_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 58 Primitive.Addresses.material2085
    · exact v2085_mb_checked.trans (by decide +kernel)
    · exact v2085_mg_checked.trans (by decide +kernel)
  upper_error := v2085_upper_checked
  lower_error := reuse_lower_error 24 58 Primitive.Addresses.material2085

def v2086_pa : Scalar.QComplex := ((999999599723904701387228241455 : Int)/10^30,(-894735732144566290771573482 : Int)/10^30)
theorem v2086_pa_checked : Scalar.distance (sourceCoefficient 24 59 1 0) v2086_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2086_pb : Scalar.QComplex := ((-386058342490253372646776 : Int)/10^30,(-431477333575351616254251714 : Int)/10^30)
theorem v2086_pb_checked : Scalar.distance (sourceCoefficient 24 59 1 1) v2086_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2086_pg : Scalar.QComplex := ((-93086391049387708144799 : Int)/10^30,(83287753586366105218 : Int)/10^30)
theorem v2086_pg_checked : Scalar.distance (sourceCoefficient 24 59 1 2) v2086_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2086_mb : Scalar.QComplex := ((-758403704600900463406469 : Int)/10^30,(-431476839765658691049609423 : Int)/10^30)
theorem v2086_mb_checked : Scalar.distance (sourceCoefficient 24 59 3 1) v2086_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2086_mg : Scalar.QComplex := ((-93086284515489858360853 : Int)/10^30,(163617085594728995101 : Int)/10^30)
theorem v2086_mg_checked : Scalar.distance (sourceCoefficient 24 59 3 2) v2086_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2086_upper : Scalar.QComplex := ((999996566109265227341186213564 : Int)/10^30,(-2620642989409228795737877718 : Int)/10^30)
theorem v2086_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 59 5) 1) 14) v2086_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2086 : Material (24 : Basis) (59 : Basis) where
  plus := ![v2086_pa,v2086_pb,v2086_pg]
  minus := ![(Primitive.Addresses.material2086 1).one,v2086_mb,v2086_mg]
  upper := v2086_upper
  lower := (Primitive.Addresses.material2086 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2086_pa_checked.trans (by decide +kernel)
    · exact v2086_pb_checked.trans (by decide +kernel)
    · exact v2086_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 59 Primitive.Addresses.material2086
    · exact v2086_mb_checked.trans (by decide +kernel)
    · exact v2086_mg_checked.trans (by decide +kernel)
  upper_error := v2086_upper_checked
  lower_error := reuse_lower_error 24 59 Primitive.Addresses.material2086

def v2087_pa : Scalar.QComplex := ((999999581387728927559884863625 : Int)/10^30,(-914999654048375440065645046 : Int)/10^30)
theorem v2087_pa_checked : Scalar.distance (sourceCoefficient 24 60 1 0) v2087_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2087_pb : Scalar.QComplex := ((-394801767747538428903943 : Int)/10^30,(-431477324315797941548420720 : Int)/10^30)
theorem v2087_pb_checked : Scalar.distance (sourceCoefficient 24 60 1 1) v2087_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2087_pg : Scalar.QComplex := ((-93086389197140775314553 : Int)/10^30,(85174049566898567880 : Int)/10^30)
theorem v2087_pg_checked : Scalar.distance (sourceCoefficient 24 60 1 2) v2087_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2087_mb : Scalar.QComplex := ((-767147118612030915647110 : Int)/10^30,(-431476822960926256317234305 : Int)/10^30)
theorem v2087_mb_checked : Scalar.distance (sourceCoefficient 24 60 3 1) v2087_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2087_mg : Scalar.QComplex := ((-93086281035455139624539 : Int)/10^30,(165503379274501575298 : Int)/10^30)
theorem v2087_mg_checked : Scalar.distance (sourceCoefficient 24 60 3 2) v2087_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2087_upper : Scalar.QComplex := ((999996512799425885754026096039 : Int)/10^30,(-2640906849485730696032826925 : Int)/10^30)
theorem v2087_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 60 5) 1) 14) v2087_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2087 : Material (24 : Basis) (60 : Basis) where
  plus := ![v2087_pa,v2087_pb,v2087_pg]
  minus := ![(Primitive.Addresses.material2087 1).one,v2087_mb,v2087_mg]
  upper := v2087_upper
  lower := (Primitive.Addresses.material2087 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2087_pa_checked.trans (by decide +kernel)
    · exact v2087_pb_checked.trans (by decide +kernel)
    · exact v2087_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 60 Primitive.Addresses.material2087
    · exact v2087_mb_checked.trans (by decide +kernel)
    · exact v2087_mg_checked.trans (by decide +kernel)
  upper_error := v2087_upper_checked
  lower_error := reuse_lower_error 24 60 Primitive.Addresses.material2087

def v2088_pa : Scalar.QComplex := ((999999576009272993672628584510 : Int)/10^30,(-920858987166068850262184080 : Int)/10^30)
theorem v2088_pa_checked : Scalar.distance (sourceCoefficient 24 61 1 0) v2088_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2088_pb : Scalar.QComplex := ((-397329937812719169248762 : Int)/10^30,(-431477321594359410800576212 : Int)/10^30)
theorem v2088_pb_checked : Scalar.distance (sourceCoefficient 24 61 1 1) v2088_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2088_pg : Scalar.QComplex := ((-93086388653250243405284 : Int)/10^30,(85719473918441128218 : Int)/10^30)
theorem v2088_pg_checked : Scalar.distance (sourceCoefficient 24 61 1 2) v2088_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2088_mb : Scalar.QComplex := ((-769675285387379514651275 : Int)/10^30,(-431476818057791837187236615 : Int)/10^30)
theorem v2088_mb_checked : Scalar.distance (sourceCoefficient 24 61 3 1) v2088_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2088_mg : Scalar.QComplex := ((-93086280020888159850240 : Int)/10^30,(166048802953604689315 : Int)/10^30)
theorem v2088_mg_checked : Scalar.distance (sourceCoefficient 24 61 3 2) v2088_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2088_upper : Scalar.QComplex := ((999996497308300555854420413576 : Int)/10^30,(-2646766164593908700863883496 : Int)/10^30)
theorem v2088_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 61 5) 1) 14) v2088_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2088 : Material (24 : Basis) (61 : Basis) where
  plus := ![v2088_pa,v2088_pb,v2088_pg]
  minus := ![(Primitive.Addresses.material2088 1).one,v2088_mb,v2088_mg]
  upper := v2088_upper
  lower := (Primitive.Addresses.material2088 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2088_pa_checked.trans (by decide +kernel)
    · exact v2088_pb_checked.trans (by decide +kernel)
    · exact v2088_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 61 Primitive.Addresses.material2088
    · exact v2088_mb_checked.trans (by decide +kernel)
    · exact v2088_mg_checked.trans (by decide +kernel)
  upper_error := v2088_upper_checked
  lower_error := reuse_lower_error 24 61 Primitive.Addresses.material2088

def v2089_pa : Scalar.QComplex := ((999999568133427279032125688146 : Int)/10^30,(-929372346765923047102392057 : Int)/10^30)
theorem v2089_pa_checked : Scalar.distance (sourceCoefficient 24 62 1 0) v2089_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2089_pb : Scalar.QComplex := ((-401003260418754993851055 : Int)/10^30,(-431477317605028937469560040 : Int)/10^30)
theorem v2089_pb_checked : Scalar.distance (sourceCoefficient 24 62 1 1) v2089_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2089_pg : Scalar.QComplex := ((-93086387856356437705758 : Int)/10^30,(86511952095645154300 : Int)/10^30)
theorem v2089_pg_checked : Scalar.distance (sourceCoefficient 24 62 1 2) v2089_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2089_mb : Scalar.QComplex := ((-773348603183056928180022 : Int)/10^30,(-431476810898550880566103354 : Int)/10^30)
theorem v2089_mb_checked : Scalar.distance (sourceCoefficient 24 62 3 1) v2089_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2089_mg : Scalar.QComplex := ((-93086278540121675835780 : Int)/10^30,(166841280148049408428 : Int)/10^30)
theorem v2089_mg_checked : Scalar.distance (sourceCoefficient 24 62 3 2) v2089_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2089_upper : Scalar.QComplex := ((999996474739180227962423439757 : Int)/10^30,(-2655279497921118610861933457 : Int)/10^30)
theorem v2089_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 62 5) 1) 14) v2089_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2089 : Material (24 : Basis) (62 : Basis) where
  plus := ![v2089_pa,v2089_pb,v2089_pg]
  minus := ![(Primitive.Addresses.material2089 1).one,v2089_mb,v2089_mg]
  upper := v2089_upper
  lower := (Primitive.Addresses.material2089 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2089_pa_checked.trans (by decide +kernel)
    · exact v2089_pb_checked.trans (by decide +kernel)
    · exact v2089_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 62 Primitive.Addresses.material2089
    · exact v2089_mb_checked.trans (by decide +kernel)
    · exact v2089_mg_checked.trans (by decide +kernel)
  upper_error := v2089_upper_checked
  lower_error := reuse_lower_error 24 62 Primitive.Addresses.material2089

def v2090_pa : Scalar.QComplex := ((999999544782078203400139350620 : Int)/10^30,(-954167509596634398251911770 : Int)/10^30)
theorem v2090_pa_checked : Scalar.distance (sourceCoefficient 24 63 1 0) v2090_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2090_pb : Scalar.QComplex := ((-411701813687587908949360 : Int)/10^30,(-431477305748533593717252703 : Int)/10^30)
theorem v2090_pb_checked : Scalar.distance (sourceCoefficient 24 63 1 1) v2090_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2090_pg : Scalar.QComplex := ((-93086385490556714335646 : Int)/10^30,(88820045053353105801 : Int)/10^30)
theorem v2090_pg_checked : Scalar.distance (sourceCoefficient 24 63 1 2) v2090_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2090_mb : Scalar.QComplex := ((-784047142236708028322076 : Int)/10^30,(-431476789809690325478378195 : Int)/10^30)
theorem v2090_mb_checked : Scalar.distance (sourceCoefficient 24 63 3 1) v2090_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2090_mg : Scalar.QComplex := ((-93086274182542563506976 : Int)/10^30,(169149370204770257111 : Int)/10^30)
theorem v2090_mg_checked : Scalar.distance (sourceCoefficient 24 63 3 2) v2090_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2090_upper : Scalar.QComplex := ((999996408593664285214707761990 : Int)/10^30,(-2680074583520037483394263653 : Int)/10^30)
theorem v2090_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 63 5) 1) 14) v2090_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2090 : Material (24 : Basis) (63 : Basis) where
  plus := ![v2090_pa,v2090_pb,v2090_pg]
  minus := ![(Primitive.Addresses.material2090 1).one,v2090_mb,v2090_mg]
  upper := v2090_upper
  lower := (Primitive.Addresses.material2090 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2090_pa_checked.trans (by decide +kernel)
    · exact v2090_pb_checked.trans (by decide +kernel)
    · exact v2090_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 63 Primitive.Addresses.material2090
    · exact v2090_mb_checked.trans (by decide +kernel)
    · exact v2090_mg_checked.trans (by decide +kernel)
  upper_error := v2090_upper_checked
  lower_error := reuse_lower_error 24 63 Primitive.Addresses.material2090

def v2091_pa : Scalar.QComplex := ((999999510341085340080068156746 : Int)/10^30,(-989604764314515190458822992 : Int)/10^30)
theorem v2091_pa_checked : Scalar.distance (sourceCoefficient 24 64 1 0) v2091_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2091_pb : Scalar.QComplex := ((-426992189166112601061978 : Int)/10^30,(-431477288189241704425105302 : Int)/10^30)
theorem v2091_pb_checked : Scalar.distance (sourceCoefficient 24 64 1 1) v2091_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2091_pg : Scalar.QComplex := ((-93086381993452158557286 : Int)/10^30,(92118772220299179272 : Int)/10^30)
theorem v2091_pg_checked : Scalar.distance (sourceCoefficient 24 64 1 2) v2091_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2091_mb : Scalar.QComplex := ((-799337496869049065789097 : Int)/10^30,(-431476759055499589293844861 : Int)/10^30)
theorem v2091_mb_checked : Scalar.distance (sourceCoefficient 24 64 3 1) v2091_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2091_mg : Scalar.QComplex := ((-93086267838786333942459 : Int)/10^30,(172448093125605719155 : Int)/10^30)
theorem v2091_mg_checked : Scalar.distance (sourceCoefficient 24 64 3 2) v2091_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2091_upper : Scalar.QComplex := ((999996312991235917280569556069 : Int)/10^30,(-2715511726016260906049457479 : Int)/10^30)
theorem v2091_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 64 5) 1) 14) v2091_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2091 : Material (24 : Basis) (64 : Basis) where
  plus := ![v2091_pa,v2091_pb,v2091_pg]
  minus := ![(Primitive.Addresses.material2091 1).one,v2091_mb,v2091_mg]
  upper := v2091_upper
  lower := (Primitive.Addresses.material2091 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2091_pa_checked.trans (by decide +kernel)
    · exact v2091_pb_checked.trans (by decide +kernel)
    · exact v2091_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 64 Primitive.Addresses.material2091
    · exact v2091_mb_checked.trans (by decide +kernel)
    · exact v2091_mg_checked.trans (by decide +kernel)
  upper_error := v2091_upper_checked
  lower_error := reuse_lower_error 24 64 Primitive.Addresses.material2091

def v2092_pa : Scalar.QComplex := ((999999474101549432843468949614 : Int)/10^30,(-1025571364930365415457919997 : Int)/10^30)
theorem v2092_pa_checked : Scalar.distance (sourceCoefficient 24 65 1 0) v2092_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2092_pb : Scalar.QComplex := ((-442510965065592121901561 : Int)/10^30,(-431477269628922386439185229 : Int)/10^30)
theorem v2092_pb_checked : Scalar.distance (sourceCoefficient 24 65 1 1) v2092_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2092_pg : Scalar.QComplex := ((-93086378304657413507319 : Int)/10^30,(95466774260160522211 : Int)/10^30)
theorem v2092_pg_checked : Scalar.distance (sourceCoefficient 24 65 1 2) v2092_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2092_mb : Scalar.QComplex := ((-814856250973459430485739 : Int)/10^30,(-431476727103182520632879417 : Int)/10^30)
theorem v2092_mb_checked : Scalar.distance (sourceCoefficient 24 65 3 1) v2092_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2092_mg : Scalar.QComplex := ((-93086261260817990413369 : Int)/10^30,(175796090735589163571 : Int)/10^30)
theorem v2092_mg_checked : Scalar.distance (sourceCoefficient 24 65 3 2) v2092_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2092_upper : Scalar.QComplex := ((999996214676664186137991953984 : Int)/10^30,(-2751478210517933096559003992 : Int)/10^30)
theorem v2092_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 65 5) 1) 14) v2092_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2092 : Material (24 : Basis) (65 : Basis) where
  plus := ![v2092_pa,v2092_pb,v2092_pg]
  minus := ![(Primitive.Addresses.material2092 1).one,v2092_mb,v2092_mg]
  upper := v2092_upper
  lower := (Primitive.Addresses.material2092 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2092_pa_checked.trans (by decide +kernel)
    · exact v2092_pb_checked.trans (by decide +kernel)
    · exact v2092_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 65 Primitive.Addresses.material2092
    · exact v2092_mb_checked.trans (by decide +kernel)
    · exact v2092_mg_checked.trans (by decide +kernel)
  upper_error := v2092_upper_checked
  lower_error := reuse_lower_error 24 65 Primitive.Addresses.material2092

def v2093_pa : Scalar.QComplex := ((999999455909583665441049787207 : Int)/10^30,(-1043158922041477222446730869 : Int)/10^30)
theorem v2093_pa_checked : Scalar.distance (sourceCoefficient 24 66 1 0) v2093_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2093_pb : Scalar.QComplex := ((-450099598616108766702768 : Int)/10^30,(-431477260282047691042852834 : Int)/10^30)
theorem v2093_pb_checked : Scalar.distance (sourceCoefficient 24 66 1 1) v2093_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2093_pg : Scalar.QComplex := ((-93086376449703212480727 : Int)/10^30,(97103936947341036098 : Int)/10^30)
theorem v2093_pg_checked : Scalar.distance (sourceCoefficient 24 66 1 2) v2093_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2093_mb : Scalar.QComplex := ((-822444873632449092225393 : Int)/10^30,(-431476711207662330776973695 : Int)/10^30)
theorem v2093_mb_checked : Scalar.distance (sourceCoefficient 24 66 3 1) v2093_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2093_mg : Scalar.QComplex := ((-93086257993066816104474 : Int)/10^30,(177433251212437255539 : Int)/10^30)
theorem v2093_mg_checked : Scalar.distance (sourceCoefficient 24 66 3 2) v2093_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2093_upper : Scalar.QComplex := ((999996166130197470470144141512 : Int)/10^30,(-2769065710036762013838120896 : Int)/10^30)
theorem v2093_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 66 5) 1) 14) v2093_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2093 : Material (24 : Basis) (66 : Basis) where
  plus := ![v2093_pa,v2093_pb,v2093_pg]
  minus := ![(Primitive.Addresses.material2093 1).one,v2093_mb,v2093_mg]
  upper := v2093_upper
  lower := (Primitive.Addresses.material2093 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2093_pa_checked.trans (by decide +kernel)
    · exact v2093_pb_checked.trans (by decide +kernel)
    · exact v2093_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 66 Primitive.Addresses.material2093
    · exact v2093_mb_checked.trans (by decide +kernel)
    · exact v2093_mg_checked.trans (by decide +kernel)
  upper_error := v2093_upper_checked
  lower_error := reuse_lower_error 24 66 Primitive.Addresses.material2093

def v2094_pa : Scalar.QComplex := ((999999424682869098290570933392 : Int)/10^30,(-1072676060520424660585653526 : Int)/10^30)
theorem v2094_pa_checked : Scalar.distance (sourceCoefficient 24 67 1 0) v2094_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2094_pb : Scalar.QComplex := ((-462835576784826418625030 : Int)/10^30,(-431477244195268891504959374 : Int)/10^30)
theorem v2094_pb_checked : Scalar.distance (sourceCoefficient 24 67 1 1) v2094_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2094_pg : Scalar.QComplex := ((-93086373261040583215924 : Int)/10^30,(99851581604112252989 : Int)/10^30)
theorem v2094_pg_checked : Scalar.distance (sourceCoefficient 24 67 1 2) v2094_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2094_mb : Scalar.QComplex := ((-835180833176814426597691 : Int)/10^30,(-431476684130313968642116042 : Int)/10^30)
theorem v2094_mb_checked : Scalar.distance (sourceCoefficient 24 67 3 1) v2094_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2094_mg : Scalar.QComplex := ((-93086252433311784652488 : Int)/10^30,(180180892094462556129 : Int)/10^30)
theorem v2094_mg_checked : Scalar.distance (sourceCoefficient 24 67 3 2) v2094_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2094_upper : Scalar.QComplex := ((999996083959626171064775710105 : Int)/10^30,(-2798582750658922536751659619 : Int)/10^30)
theorem v2094_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 67 5) 1) 14) v2094_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2094 : Material (24 : Basis) (67 : Basis) where
  plus := ![v2094_pa,v2094_pb,v2094_pg]
  minus := ![(Primitive.Addresses.material2094 1).one,v2094_mb,v2094_mg]
  upper := v2094_upper
  lower := (Primitive.Addresses.material2094 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2094_pa_checked.trans (by decide +kernel)
    · exact v2094_pb_checked.trans (by decide +kernel)
    · exact v2094_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 67 Primitive.Addresses.material2094
    · exact v2094_mb_checked.trans (by decide +kernel)
    · exact v2094_mg_checked.trans (by decide +kernel)
  upper_error := v2094_upper_checked
  lower_error := reuse_lower_error 24 67 Primitive.Addresses.material2094

def v2095_pa : Scalar.QComplex := ((999999370744024546783088497275 : Int)/10^30,(-1121834013989302777293848406 : Int)/10^30)
theorem v2095_pa_checked : Scalar.distance (sourceCoefficient 24 68 1 0) v2095_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2095_pb : Scalar.QComplex := ((-484046122086465056450385 : Int)/10^30,(-431477216291790869571723224 : Int)/10^30)
theorem v2095_pb_checked : Scalar.distance (sourceCoefficient 24 68 1 1) v2095_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2095_pg : Scalar.QComplex := ((-93086367740622323539542 : Int)/10^30,(104427519281787196288 : Int)/10^30)
theorem v2095_pg_checked : Scalar.distance (sourceCoefficient 24 68 1 2) v2095_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2095_mb : Scalar.QComplex := ((-856391346501352871884720 : Int)/10^30,(-431476637923101028633301917 : Int)/10^30)
theorem v2095_mb_checked : Scalar.distance (sourceCoefficient 24 68 3 1) v2095_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2095_mg : Scalar.QComplex := ((-93086242964067457229129 : Int)/10^30,(184756823304434443654 : Int)/10^30)
theorem v2095_mg_checked : Scalar.distance (sourceCoefficient 24 68 3 2) v2095_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2095_upper : Scalar.QComplex := ((999995945178693842548932344981 : Int)/10^30,(-2847740537819251058268259307 : Int)/10^30)
theorem v2095_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 68 5) 1) 14) v2095_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2095 : Material (24 : Basis) (68 : Basis) where
  plus := ![v2095_pa,v2095_pb,v2095_pg]
  minus := ![(Primitive.Addresses.material2095 1).one,v2095_mb,v2095_mg]
  upper := v2095_upper
  lower := (Primitive.Addresses.material2095 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2095_pa_checked.trans (by decide +kernel)
    · exact v2095_pb_checked.trans (by decide +kernel)
    · exact v2095_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 68 Primitive.Addresses.material2095
    · exact v2095_mb_checked.trans (by decide +kernel)
    · exact v2095_mg_checked.trans (by decide +kernel)
  upper_error := v2095_upper_checked
  lower_error := reuse_lower_error 24 68 Primitive.Addresses.material2095

def v2096_pa : Scalar.QComplex := ((999999346238665789638605030957 : Int)/10^30,(-1143469387879203647475189373 : Int)/10^30)
theorem v2096_pa_checked : Scalar.distance (sourceCoefficient 24 69 1 0) v2096_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2096_pb : Scalar.QComplex := ((-493381296404029459407616 : Int)/10^30,(-431477203570346668747409333 : Int)/10^30)
theorem v2096_pb_checked : Scalar.distance (sourceCoefficient 24 69 1 1) v2096_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2096_pg : Scalar.QComplex := ((-93086365227809776292839 : Int)/10^30,(106441478654266732426 : Int)/10^30)
theorem v2096_pg_checked : Scalar.distance (sourceCoefficient 24 69 1 2) v2096_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2096_mb : Scalar.QComplex := ((-865726506364971845136462 : Int)/10^30,(-431476617145826569169755730 : Int)/10^30)
theorem v2096_mb_checked : Scalar.distance (sourceCoefficient 24 69 3 1) v2096_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2096_mg : Scalar.QComplex := ((-93086238713299612530534 : Int)/10^30,(186770779758580807529 : Int)/10^30)
theorem v2096_mg_checked : Scalar.distance (sourceCoefficient 24 69 3 2) v2096_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2096_upper : Scalar.QComplex := ((999995883332678995075977182207 : Int)/10^30,(-2869375837191777882936957174 : Int)/10^30)
theorem v2096_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 69 5) 1) 14) v2096_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2096 : Material (24 : Basis) (69 : Basis) where
  plus := ![v2096_pa,v2096_pb,v2096_pg]
  minus := ![(Primitive.Addresses.material2096 1).one,v2096_mb,v2096_mg]
  upper := v2096_upper
  lower := (Primitive.Addresses.material2096 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2096_pa_checked.trans (by decide +kernel)
    · exact v2096_pb_checked.trans (by decide +kernel)
    · exact v2096_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 69 Primitive.Addresses.material2096
    · exact v2096_mb_checked.trans (by decide +kernel)
    · exact v2096_mg_checked.trans (by decide +kernel)
  upper_error := v2096_upper_checked
  lower_error := reuse_lower_error 24 69 Primitive.Addresses.material2096

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
