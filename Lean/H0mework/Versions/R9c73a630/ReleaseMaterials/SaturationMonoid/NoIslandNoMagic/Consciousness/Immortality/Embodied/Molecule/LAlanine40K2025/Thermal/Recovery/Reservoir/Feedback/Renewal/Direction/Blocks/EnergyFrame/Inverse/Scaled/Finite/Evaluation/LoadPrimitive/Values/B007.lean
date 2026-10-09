import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B004
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B005

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v113_pa : Scalar.QComplex := ((999969973914530283032473501742 : Int)/10^30,(7749275409586711824223272090 : Int)/10^30)
theorem v113_pa_checked : Scalar.distance (sourceCoefficient 1 18 1 0) v113_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v113_pb : Scalar.QComplex := ((3343603156715957563824514 : Int)/10^30,(-431460050737842408457701093 : Int)/10^30)
theorem v113_pb_checked : Scalar.distance (sourceCoefficient 1 18 1 1) v113_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v113_pg : Scalar.QComplex := ((-93083147879411066855165 : Int)/10^30,(-721348608183806449629 : Int)/10^30)
theorem v113_pg_checked : Scalar.distance (sourceCoefficient 1 18 1 2) v113_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v113_mb : Scalar.QComplex := ((2971271320192260707595413 : Int)/10^30,(-431462775464480770184232964 : Int)/10^30)
theorem v113_mb_checked : Scalar.distance (sourceCoefficient 1 18 3 1) v113_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v113_mg : Scalar.QComplex := ((-93083735711661528671100 : Int)/10^30,(-641021775282175262265 : Int)/10^30)
theorem v113_mg_checked : Scalar.distance (sourceCoefficient 1 18 3 2) v113_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v113_upper : Scalar.QComplex := ((999981859123067035032544202262 : Int)/10^30,(6023406409542198401231700283 : Int)/10^30)
theorem v113_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 18 5) 1) 14) v113_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material113 : Material (1 : Basis) (18 : Basis) where
  plus := ![v113_pa,v113_pb,v113_pg]
  minus := ![(Primitive.Addresses.material113 1).one,v113_mb,v113_mg]
  upper := v113_upper
  lower := (Primitive.Addresses.material113 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v113_pa_checked.trans (by decide +kernel)
    · exact v113_pb_checked.trans (by decide +kernel)
    · exact v113_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 18 Primitive.Addresses.material113
    · exact v113_mb_checked.trans (by decide +kernel)
    · exact v113_mg_checked.trans (by decide +kernel)
  upper_error := v113_upper_checked
  lower_error := reuse_lower_error 1 18 Primitive.Addresses.material113

def v114_pa : Scalar.QComplex := ((999970095081006776776112759020 : Int)/10^30,(7733624226859387336789437751 : Int)/10^30)
theorem v114_pa_checked : Scalar.distance (sourceCoefficient 1 19 1 0) v114_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v114_pb : Scalar.QComplex := ((3336849955776597106338087 : Int)/10^30,(-431460085164239493162097465 : Int)/10^30)
theorem v114_pb_checked : Scalar.distance (sourceCoefficient 1 19 1 1) v114_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v114_pg : Scalar.QComplex := ((-93083157232438697038196 : Int)/10^30,(-719891688187968662983 : Int)/10^30)
theorem v114_pg_checked : Scalar.distance (sourceCoefficient 1 19 1 2) v114_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v114_mb : Scalar.QComplex := ((2964518092058995419630029 : Int)/10^30,(-431462804063156778579178997 : Int)/10^30)
theorem v114_mb_checked : Scalar.distance (sourceCoefficient 1 19 3 1) v114_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v114_mg : Scalar.QComplex := ((-93083743807429337127266 : Int)/10^30,(-639564847757573774483 : Int)/10^30)
theorem v114_mg_checked : Scalar.distance (sourceCoefficient 1 19 3 2) v114_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v114_upper : Scalar.QComplex := ((999981953276841542386247254822 : Int)/10^30,(6007755041003125777755888031 : Int)/10^30)
theorem v114_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 19 5) 1) 14) v114_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material114 : Material (1 : Basis) (19 : Basis) where
  plus := ![v114_pa,v114_pb,v114_pg]
  minus := ![(Primitive.Addresses.material114 1).one,v114_mb,v114_mg]
  upper := v114_upper
  lower := (Primitive.Addresses.material114 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v114_pa_checked.trans (by decide +kernel)
    · exact v114_pb_checked.trans (by decide +kernel)
    · exact v114_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 19 Primitive.Addresses.material114
    · exact v114_mb_checked.trans (by decide +kernel)
    · exact v114_mg_checked.trans (by decide +kernel)
  upper_error := v114_upper_checked
  lower_error := reuse_lower_error 1 19 Primitive.Addresses.material114

def v115_pa : Scalar.QComplex := ((999970116773237071109552253898 : Int)/10^30,(7730818877623250608372217259 : Int)/10^30)
theorem v115_pa_checked : Scalar.distance (sourceCoefficient 1 20 1 0) v115_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v115_pb : Scalar.QComplex := ((3335639498589248973789373 : Int)/10^30,(-431460091320000729133109063 : Int)/10^30)
theorem v115_pb_checked : Scalar.distance (sourceCoefficient 1 20 1 1) v115_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v115_pg : Scalar.QComplex := ((-93083158906082291582059 : Int)/10^30,(-719630546942765606504 : Int)/10^30)
theorem v115_pg_checked : Scalar.distance (sourceCoefficient 1 20 1 2) v115_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v115_mb : Scalar.QComplex := ((2963307630010211117108640 : Int)/10^30,(-431462809174345686765465049 : Int)/10^30)
theorem v115_mb_checked : Scalar.distance (sourceCoefficient 1 20 3 1) v115_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v115_mg : Scalar.QComplex := ((-93083745255719175251973 : Int)/10^30,(-639303705165326494355 : Int)/10^30)
theorem v115_mg_checked : Scalar.distance (sourceCoefficient 1 20 3 2) v115_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v115_upper : Scalar.QComplex := ((999981970127261246413481394451 : Int)/10^30,(6004949658506405612834527495 : Int)/10^30)
theorem v115_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 20 5) 1) 14) v115_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material115 : Material (1 : Basis) (20 : Basis) where
  plus := ![v115_pa,v115_pb,v115_pg]
  minus := ![(Primitive.Addresses.material115 1).one,v115_mb,v115_mg]
  upper := v115_upper
  lower := (Primitive.Addresses.material115 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v115_pa_checked.trans (by decide +kernel)
    · exact v115_pb_checked.trans (by decide +kernel)
    · exact v115_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 20 Primitive.Addresses.material115
    · exact v115_mb_checked.trans (by decide +kernel)
    · exact v115_mg_checked.trans (by decide +kernel)
  upper_error := v115_upper_checked
  lower_error := reuse_lower_error 1 20 Primitive.Addresses.material115

def v116_pa : Scalar.QComplex := ((999970525169918362368055198007 : Int)/10^30,(7677811628170290196062229512 : Int)/10^30)
theorem v116_pa_checked : Scalar.distance (sourceCoefficient 1 21 1 0) v116_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v116_pb : Scalar.QComplex := ((3312767835995884618038501 : Int)/10^30,(-431460206782419549318401578 : Int)/10^30)
theorem v116_pb_checked : Scalar.distance (sourceCoefficient 1 21 1 1) v116_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v116_pg : Scalar.QComplex := ((-93083190369023143960177 : Int)/10^30,(-714696266953503095669 : Int)/10^30)
theorem v116_pg_checked : Scalar.distance (sourceCoefficient 1 21 1 2) v116_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v116_mb : Scalar.QComplex := ((2940435876294144823968024 : Int)/10^30,(-431462904899506798385940651 : Int)/10^30)
theorem v116_mb_checked : Scalar.distance (sourceCoefficient 1 21 3 1) v116_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v116_mg : Scalar.QComplex := ((-93083772460586913526824 : Int)/10^30,(-634369399862221013909 : Int)/10^30)
theorem v116_mg_checked : Scalar.distance (sourceCoefficient 1 21 3 2) v116_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v116_upper : Scalar.QComplex := ((999982287037630503085417348730 : Int)/10^30,(5951941783145894140588781328 : Int)/10^30)
theorem v116_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 21 5) 1) 14) v116_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material116 : Material (1 : Basis) (21 : Basis) where
  plus := ![v116_pa,v116_pb,v116_pg]
  minus := ![(Primitive.Addresses.material116 1).one,v116_mb,v116_mg]
  upper := v116_upper
  lower := (Primitive.Addresses.material116 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v116_pa_checked.trans (by decide +kernel)
    · exact v116_pb_checked.trans (by decide +kernel)
    · exact v116_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 21 Primitive.Addresses.material116
    · exact v116_mb_checked.trans (by decide +kernel)
    · exact v116_mg_checked.trans (by decide +kernel)
  upper_error := v116_upper_checked
  lower_error := reuse_lower_error 1 21 Primitive.Addresses.material116

def v117_pa : Scalar.QComplex := ((999970535872569136598890739201 : Int)/10^30,(7676417571167004986157506768 : Int)/10^30)
theorem v117_pa_checked : Scalar.distance (sourceCoefficient 1 22 1 0) v117_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v117_pb : Scalar.QComplex := ((3312166325837256798281070 : Int)/10^30,(-431460209797191100243307675 : Int)/10^30)
theorem v117_pb_checked : Scalar.distance (sourceCoefficient 1 22 1 1) v117_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v117_pg : Scalar.QComplex := ((-93083191192360106481305 : Int)/10^30,(-714566498527701365467 : Int)/10^30)
theorem v117_pg_checked : Scalar.distance (sourceCoefficient 1 22 1 2) v117_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v117_mb : Scalar.QComplex := ((2939834363757874658462091 : Int)/10^30,(-431462907395201050889686987 : Int)/10^30)
theorem v117_mb_checked : Scalar.distance (sourceCoefficient 1 22 3 1) v117_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v117_mg : Scalar.QComplex := ((-93083773171939262568018 : Int)/10^30,(-634239630774235282408 : Int)/10^30)
theorem v117_mg_checked : Scalar.distance (sourceCoefficient 1 22 3 2) v117_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v117_upper : Scalar.QComplex := ((999982295334249417168299352716 : Int)/10^30,(5950547709747088780209713472 : Int)/10^30)
theorem v117_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 22 5) 1) 14) v117_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material117 : Material (1 : Basis) (22 : Basis) where
  plus := ![v117_pa,v117_pb,v117_pg]
  minus := ![(Primitive.Addresses.material117 1).one,v117_mb,v117_mg]
  upper := v117_upper
  lower := (Primitive.Addresses.material117 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v117_pa_checked.trans (by decide +kernel)
    · exact v117_pb_checked.trans (by decide +kernel)
    · exact v117_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 22 Primitive.Addresses.material117
    · exact v117_mb_checked.trans (by decide +kernel)
    · exact v117_mg_checked.trans (by decide +kernel)
  upper_error := v117_upper_checked
  lower_error := reuse_lower_error 1 22 Primitive.Addresses.material117

def v118_pa : Scalar.QComplex := ((999970614953681501003752430060 : Int)/10^30,(7666109127585574108432866032 : Int)/10^30)
theorem v118_pa_checked : Scalar.distance (sourceCoefficient 1 23 1 0) v118_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v118_pb : Scalar.QComplex := ((3307718420609155762512550 : Int)/10^30,(-431460232055408577986386651 : Int)/10^30)
theorem v118_pb_checked : Scalar.distance (sourceCoefficient 1 23 1 1) v118_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v118_pg : Scalar.QComplex := ((-93083197274026835032549 : Int)/10^30,(-713606917619593203384 : Int)/10^30)
theorem v118_pg_checked : Scalar.distance (sourceCoefficient 1 23 1 2) v118_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v118_mb : Scalar.QComplex := ((2935386440978092808036089 : Int)/10^30,(-431462925815068355244969355 : Int)/10^30)
theorem v118_mb_checked : Scalar.distance (sourceCoefficient 1 23 3 1) v118_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v118_mg : Scalar.QComplex := ((-93083778425528620859226 : Int)/10^30,(-633280044975218468788 : Int)/10^30)
theorem v118_mg_checked : Scalar.distance (sourceCoefficient 1 23 3 2) v118_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v118_upper : Scalar.QComplex := ((999982356623805552692642898037 : Int)/10^30,(5940239145032047943690431308 : Int)/10^30)
theorem v118_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 23 5) 1) 14) v118_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material118 : Material (1 : Basis) (23 : Basis) where
  plus := ![v118_pa,v118_pb,v118_pg]
  minus := ![(Primitive.Addresses.material118 1).one,v118_mb,v118_mg]
  upper := v118_upper
  lower := (Primitive.Addresses.material118 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v118_pa_checked.trans (by decide +kernel)
    · exact v118_pb_checked.trans (by decide +kernel)
    · exact v118_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 23 Primitive.Addresses.material118
    · exact v118_mb_checked.trans (by decide +kernel)
    · exact v118_mg_checked.trans (by decide +kernel)
  upper_error := v118_upper_checked
  lower_error := reuse_lower_error 1 23 Primitive.Addresses.material118

def v119_pa : Scalar.QComplex := ((999971004213387622833746567802 : Int)/10^30,(7615164638345848790028604880 : Int)/10^30)
theorem v119_pa_checked : Scalar.distance (sourceCoefficient 1 24 1 0) v119_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v119_pb : Scalar.QComplex := ((3285736805359698399577031 : Int)/10^30,(-431460341158182287349308000 : Int)/10^30)
theorem v119_pb_checked : Scalar.distance (sourceCoefficient 1 24 1 1) v119_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v119_pg : Scalar.QComplex := ((-93083227160260545702603 : Int)/10^30,(-708864653982173911677 : Int)/10^30)
theorem v119_pg_checked : Scalar.distance (sourceCoefficient 1 24 1 2) v119_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v119_mb : Scalar.QComplex := ((2913404739762615507257757 : Int)/10^30,(-431463015948657495577035255 : Int)/10^30)
theorem v119_mb_checked : Scalar.distance (sourceCoefficient 1 24 3 1) v119_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v119_mg : Scalar.QComplex := ((-93083804219391268051385 : Int)/10^30,(-628537757313086995139 : Int)/10^30)
theorem v119_mg_checked : Scalar.distance (sourceCoefficient 1 24 3 2) v119_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v119_upper : Scalar.QComplex := ((999982657957365138111621381160 : Int)/10^30,(5889294059841215586180501877 : Int)/10^30)
theorem v119_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 24 5) 1) 14) v119_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material119 : Material (1 : Basis) (24 : Basis) where
  plus := ![v119_pa,v119_pb,v119_pg]
  minus := ![(Primitive.Addresses.material119 1).one,v119_mb,v119_mg]
  upper := v119_upper
  lower := (Primitive.Addresses.material119 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v119_pa_checked.trans (by decide +kernel)
    · exact v119_pb_checked.trans (by decide +kernel)
    · exact v119_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 24 Primitive.Addresses.material119
    · exact v119_mb_checked.trans (by decide +kernel)
    · exact v119_mg_checked.trans (by decide +kernel)
  upper_error := v119_upper_checked
  lower_error := reuse_lower_error 1 24 Primitive.Addresses.material119

def v120_pa : Scalar.QComplex := ((999971178978781777651998102758 : Int)/10^30,(7592180963674445687046456266 : Int)/10^30)
theorem v120_pa_checked : Scalar.distance (sourceCoefficient 1 25 1 0) v120_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v120_pb : Scalar.QComplex := ((3275819771183016709926411 : Int)/10^30,(-431460389891247613670893761 : Int)/10^30)
theorem v120_pb_checked : Scalar.distance (sourceCoefficient 1 25 1 1) v120_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v120_pg : Scalar.QComplex := ((-93083240551203432530309 : Int)/10^30,(-706725175491254202673 : Int)/10^30)
theorem v120_pg_checked : Scalar.distance (sourceCoefficient 1 25 1 2) v120_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v120_mb : Scalar.QComplex := ((2903487667224058351607555 : Int)/10^30,(-431463056123750828513905885 : Int)/10^30)
theorem v120_mb_checked : Scalar.distance (sourceCoefficient 1 25 3 1) v120_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v120_mg : Scalar.QComplex := ((-93083815764055589689583 : Int)/10^30,(-626398268063012301649 : Int)/10^30)
theorem v120_mg_checked : Scalar.distance (sourceCoefficient 1 25 3 2) v120_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v120_upper : Scalar.QComplex := ((999982793054761580241482757866 : Int)/10^30,(5866310117772080335664248843 : Int)/10^30)
theorem v120_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 25 5) 1) 14) v120_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material120 : Material (1 : Basis) (25 : Basis) where
  plus := ![v120_pa,v120_pb,v120_pg]
  minus := ![(Primitive.Addresses.material120 1).one,v120_mb,v120_mg]
  upper := v120_upper
  lower := (Primitive.Addresses.material120 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v120_pa_checked.trans (by decide +kernel)
    · exact v120_pb_checked.trans (by decide +kernel)
    · exact v120_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 25 Primitive.Addresses.material120
    · exact v120_mb_checked.trans (by decide +kernel)
    · exact v120_mg_checked.trans (by decide +kernel)
  upper_error := v120_upper_checked
  lower_error := reuse_lower_error 1 25 Primitive.Addresses.material120

def v121_pa : Scalar.QComplex := ((999971234708268043699623566509 : Int)/10^30,(7584837244259376736555371912 : Int)/10^30)
theorem v121_pa_checked : Scalar.distance (sourceCoefficient 1 26 1 0) v121_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v121_pb : Scalar.QComplex := ((3272651091051765558068289 : Int)/10^30,(-431460405398315723839129134 : Int)/10^30)
theorem v121_pb_checked : Scalar.distance (sourceCoefficient 1 26 1 1) v121_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v121_pg : Scalar.QComplex := ((-93083244817768797159990 : Int)/10^30,(-706041571602108417510 : Int)/10^30)
theorem v121_pg_checked : Scalar.distance (sourceCoefficient 1 26 1 2) v121_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v121_mb : Scalar.QComplex := ((2900318974890750261796489 : Int)/10^30,(-431463068896384923477622800 : Int)/10^30)
theorem v121_mb_checked : Scalar.distance (sourceCoefficient 1 26 3 1) v121_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v121_mg : Scalar.QComplex := ((-93083819440699997725423 : Int)/10^30,(-625714660746549735952 : Int)/10^30)
theorem v121_mg_checked : Scalar.distance (sourceCoefficient 1 26 3 2) v121_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v121_upper : Scalar.QComplex := ((999982836109571350377884999895 : Int)/10^30,(5858966313110581244340326882 : Int)/10^30)
theorem v121_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 26 5) 1) 14) v121_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material121 : Material (1 : Basis) (26 : Basis) where
  plus := ![v121_pa,v121_pb,v121_pg]
  minus := ![(Primitive.Addresses.material121 1).one,v121_mb,v121_mg]
  upper := v121_upper
  lower := (Primitive.Addresses.material121 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v121_pa_checked.trans (by decide +kernel)
    · exact v121_pb_checked.trans (by decide +kernel)
    · exact v121_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 26 Primitive.Addresses.material121
    · exact v121_mb_checked.trans (by decide +kernel)
    · exact v121_mg_checked.trans (by decide +kernel)
  upper_error := v121_upper_checked
  lower_error := reuse_lower_error 1 26 Primitive.Addresses.material121

def v122_pa : Scalar.QComplex := ((999971272962816027133909808266 : Int)/10^30,(7579792155810102608613746248 : Int)/10^30)
theorem v122_pa_checked : Scalar.distance (sourceCoefficient 1 27 1 0) v122_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v122_pb : Scalar.QComplex := ((3270474228028744865988426 : Int)/10^30,(-431460416033592394821808523 : Int)/10^30)
theorem v122_pb_checked : Scalar.distance (sourceCoefficient 1 27 1 1) v122_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v122_pg : Scalar.QComplex := ((-93083247745477827603082 : Int)/10^30,(-705571940089860185498 : Int)/10^30)
theorem v122_pg_checked : Scalar.distance (sourceCoefficient 1 27 1 2) v122_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v122_mb : Scalar.QComplex := ((2898142103500510388764242 : Int)/10^30,(-431463077653122887864940836 : Int)/10^30)
theorem v122_mb_checked : Scalar.distance (sourceCoefficient 1 27 3 1) v122_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v122_mg : Scalar.QComplex := ((-93083821963137094396551 : Int)/10^30,(-625245026882685745018 : Int)/10^30)
theorem v122_mg_checked : Scalar.distance (sourceCoefficient 1 27 3 2) v122_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v122_upper : Scalar.QComplex := ((999982865656697381558364649732 : Int)/10^30,(5853921166151494329948736776 : Int)/10^30)
theorem v122_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 27 5) 1) 14) v122_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material122 : Material (1 : Basis) (27 : Basis) where
  plus := ![v122_pa,v122_pb,v122_pg]
  minus := ![(Primitive.Addresses.material122 1).one,v122_mb,v122_mg]
  upper := v122_upper
  lower := (Primitive.Addresses.material122 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v122_pa_checked.trans (by decide +kernel)
    · exact v122_pb_checked.trans (by decide +kernel)
    · exact v122_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 27 Primitive.Addresses.material122
    · exact v122_mb_checked.trans (by decide +kernel)
    · exact v122_mg_checked.trans (by decide +kernel)
  upper_error := v122_upper_checked
  lower_error := reuse_lower_error 1 27 Primitive.Addresses.material122

def v123_pa : Scalar.QComplex := ((999971324456418186992544914734 : Int)/10^30,(7572995766328296479394715449 : Int)/10^30)
theorem v123_pa_checked : Scalar.distance (sourceCoefficient 1 28 1 0) v123_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v123_pb : Scalar.QComplex := ((3267541710819108081691517 : Int)/10^30,(-431460430337539839612898492 : Int)/10^30)
theorem v123_pb_checked : Scalar.distance (sourceCoefficient 1 28 1 1) v123_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v123_pg : Scalar.QComplex := ((-93083251685111781763832 : Int)/10^30,(-704939285444625091820 : Int)/10^30)
theorem v123_pg_checked : Scalar.distance (sourceCoefficient 1 28 1 2) v123_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v123_mb : Scalar.QComplex := ((2895209575039121365295857 : Int)/10^30,(-431463089426434730398372193 : Int)/10^30)
theorem v123_mb_checked : Scalar.distance (sourceCoefficient 1 28 3 1) v123_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v123_mg : Scalar.QComplex := ((-93083825356817116521128 : Int)/10^30,(-624612369073290221592 : Int)/10^30)
theorem v123_mg_checked : Scalar.distance (sourceCoefficient 1 28 3 2) v123_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v123_upper : Scalar.QComplex := ((999982905420271165785525662596 : Int)/10^30,(5847124697918826109070143030 : Int)/10^30)
theorem v123_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 28 5) 1) 14) v123_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material123 : Material (1 : Basis) (28 : Basis) where
  plus := ![v123_pa,v123_pb,v123_pg]
  minus := ![(Primitive.Addresses.material123 1).one,v123_mb,v123_mg]
  upper := v123_upper
  lower := (Primitive.Addresses.material123 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v123_pa_checked.trans (by decide +kernel)
    · exact v123_pb_checked.trans (by decide +kernel)
    · exact v123_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 28 Primitive.Addresses.material123
    · exact v123_mb_checked.trans (by decide +kernel)
    · exact v123_mg_checked.trans (by decide +kernel)
  upper_error := v123_upper_checked
  lower_error := reuse_lower_error 1 28 Primitive.Addresses.material123

def v124_pa : Scalar.QComplex := ((999971428606669851701341288732 : Int)/10^30,(7559230803182276910013657285 : Int)/10^30)
theorem v124_pa_checked : Scalar.distance (sourceCoefficient 1 29 1 0) v124_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v124_pb : Scalar.QComplex := ((3261602382263933819900871 : Int)/10^30,(-431460459226401309424300787 : Int)/10^30)
theorem v124_pb_checked : Scalar.distance (sourceCoefficient 1 29 1 1) v124_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v124_pg : Scalar.QComplex := ((-93083259648819283499332 : Int)/10^30,(-703657948085973268766 : Int)/10^30)
theorem v124_pg_checked : Scalar.distance (sourceCoefficient 1 29 1 2) v124_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v124_mb : Scalar.QComplex := ((2889270223765644222895037 : Int)/10^30,(-431463113189912397879128913 : Int)/10^30)
theorem v124_mb_checked : Scalar.distance (sourceCoefficient 1 29 3 1) v124_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v124_mg : Scalar.QComplex := ((-93083832214785221780207 : Int)/10^30,(-623331025319417955248 : Int)/10^30)
theorem v124_mg_checked : Scalar.distance (sourceCoefficient 1 29 3 2) v124_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v124_upper : Scalar.QComplex := ((999982985813290068600963846879 : Int)/10^30,(5833359575520216263266329865 : Int)/10^30)
theorem v124_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 29 5) 1) 14) v124_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material124 : Material (1 : Basis) (29 : Basis) where
  plus := ![v124_pa,v124_pb,v124_pg]
  minus := ![(Primitive.Addresses.material124 1).one,v124_mb,v124_mg]
  upper := v124_upper
  lower := (Primitive.Addresses.material124 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v124_pa_checked.trans (by decide +kernel)
    · exact v124_pb_checked.trans (by decide +kernel)
    · exact v124_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 29 Primitive.Addresses.material124
    · exact v124_mb_checked.trans (by decide +kernel)
    · exact v124_mg_checked.trans (by decide +kernel)
  upper_error := v124_upper_checked
  lower_error := reuse_lower_error 1 29 Primitive.Addresses.material124

def v125_pa : Scalar.QComplex := ((999971468024262951862397753071 : Int)/10^30,(7554014654503710697767542689 : Int)/10^30)
theorem v125_pa_checked : Scalar.distance (sourceCoefficient 1 30 1 0) v125_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v125_pb : Scalar.QComplex := ((3259351710059636589197167 : Int)/10^30,(-431460470145176846623292987 : Int)/10^30)
theorem v125_pb_checked : Scalar.distance (sourceCoefficient 1 30 1 1) v125_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v125_pg : Scalar.QComplex := ((-93083262661240960947234 : Int)/10^30,(-703172393129692030454 : Int)/10^30)
theorem v125_pg_checked : Scalar.distance (sourceCoefficient 1 30 1 2) v125_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v125_mb : Scalar.QComplex := ((2887019542976963589444706 : Int)/10^30,(-431463122166455123723645524 : Int)/10^30)
theorem v125_mb_checked : Scalar.distance (sourceCoefficient 1 30 3 1) v125_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v125_mg : Scalar.QComplex := ((-93083834808193718878566 : Int)/10^30,(-622845467944346784915 : Int)/10^30)
theorem v125_mg_checked : Scalar.distance (sourceCoefficient 1 30 3 2) v125_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v125_upper : Scalar.QComplex := ((999983016228225046993773520954 : Int)/10^30,(5828143366579301021113121224 : Int)/10^30)
theorem v125_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 30 5) 1) 14) v125_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material125 : Material (1 : Basis) (30 : Basis) where
  plus := ![v125_pa,v125_pb,v125_pg]
  minus := ![(Primitive.Addresses.material125 1).one,v125_mb,v125_mg]
  upper := v125_upper
  lower := (Primitive.Addresses.material125 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v125_pa_checked.trans (by decide +kernel)
    · exact v125_pb_checked.trans (by decide +kernel)
    · exact v125_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 30 Primitive.Addresses.material125
    · exact v125_mb_checked.trans (by decide +kernel)
    · exact v125_mg_checked.trans (by decide +kernel)
  upper_error := v125_upper_checked
  lower_error := reuse_lower_error 1 30 Primitive.Addresses.material125

def v126_pa : Scalar.QComplex := ((999971551775031931501429412588 : Int)/10^30,(7542919901114764144850962138 : Int)/10^30)
theorem v126_pa_checked : Scalar.distance (sourceCoefficient 1 31 1 0) v126_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v126_pb : Scalar.QComplex := ((3254564528172211865167894 : Int)/10^30,(-431460493317364358927897811 : Int)/10^30)
theorem v126_pb_checked : Scalar.distance (sourceCoefficient 1 31 1 1) v126_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v126_pg : Scalar.QComplex := ((-93083269058837562227531 : Int)/10^30,(-702139617270517115010 : Int)/10^30)
theorem v126_pg_checked : Scalar.distance (sourceCoefficient 1 31 1 2) v126_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v126_mb : Scalar.QComplex := ((2882232342875471280589181 : Int)/10^30,(-431463141207511645784795251 : Int)/10^30)
theorem v126_mb_checked : Scalar.distance (sourceCoefficient 1 31 3 1) v126_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v126_mg : Scalar.QComplex := ((-93083840314548886071310 : Int)/10^30,(-621812686948883792181 : Int)/10^30)
theorem v126_mg_checked : Scalar.distance (sourceCoefficient 1 31 3 2) v126_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v126_upper : Scalar.QComplex := ((999983080830331448543751006689 : Int)/10^30,(5817048485168456911302875067 : Int)/10^30)
theorem v126_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 31 5) 1) 14) v126_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material126 : Material (1 : Basis) (31 : Basis) where
  plus := ![v126_pa,v126_pb,v126_pg]
  minus := ![(Primitive.Addresses.material126 1).one,v126_mb,v126_mg]
  upper := v126_upper
  lower := (Primitive.Addresses.material126 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v126_pa_checked.trans (by decide +kernel)
    · exact v126_pb_checked.trans (by decide +kernel)
    · exact v126_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 31 Primitive.Addresses.material126
    · exact v126_mb_checked.trans (by decide +kernel)
    · exact v126_mg_checked.trans (by decide +kernel)
  upper_error := v126_upper_checked
  lower_error := reuse_lower_error 1 31 Primitive.Addresses.material126

def v127_pa : Scalar.QComplex := ((999971587789291552879805789493 : Int)/10^30,(7538143946833126056261125103 : Int)/10^30)
theorem v127_pa_checked : Scalar.distance (sourceCoefficient 1 32 1 0) v127_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v127_pb : Scalar.QComplex := ((3252503791849023395849458 : Int)/10^30,(-431460503270482170047102393 : Int)/10^30)
theorem v127_pb_checked : Scalar.distance (sourceCoefficient 1 32 1 1) v127_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v127_pg : Scalar.QComplex := ((-93083271808692366069529 : Int)/10^30,(-701695038643407937060 : Int)/10^30)
theorem v127_pg_checked : Scalar.distance (sourceCoefficient 1 32 1 2) v127_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v127_mb : Scalar.QComplex := ((2880171598730496725486092 : Int)/10^30,(-431463149382303116110358391 : Int)/10^30)
theorem v127_mb_checked : Scalar.distance (sourceCoefficient 1 32 3 1) v127_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v127_mg : Scalar.QComplex := ((-93083842680751333899542 : Int)/10^30,(-621368106114310708498 : Int)/10^30)
theorem v127_mg_checked : Scalar.distance (sourceCoefficient 1 32 3 2) v127_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v127_upper : Scalar.QComplex := ((999983108601673611993513973249 : Int)/10^30,(5812272475842696783825234412 : Int)/10^30)
theorem v127_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 32 5) 1) 14) v127_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material127 : Material (1 : Basis) (32 : Basis) where
  plus := ![v127_pa,v127_pb,v127_pg]
  minus := ![(Primitive.Addresses.material127 1).one,v127_mb,v127_mg]
  upper := v127_upper
  lower := (Primitive.Addresses.material127 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v127_pa_checked.trans (by decide +kernel)
    · exact v127_pb_checked.trans (by decide +kernel)
    · exact v127_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 32 Primitive.Addresses.material127
    · exact v127_mb_checked.trans (by decide +kernel)
    · exact v127_mg_checked.trans (by decide +kernel)
  upper_error := v127_upper_checked
  lower_error := reuse_lower_error 1 32 Primitive.Addresses.material127

def v128_pa : Scalar.QComplex := ((999971637941912747363319530678 : Int)/10^30,(7531488018191778858129087157 : Int)/10^30)
theorem v128_pa_checked : Scalar.distance (sourceCoefficient 1 33 1 0) v128_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v128_pb : Scalar.QComplex := ((3249631881257192126496542 : Int)/10^30,(-431460517119589038513646909 : Int)/10^30)
theorem v128_pb_checked : Scalar.distance (sourceCoefficient 1 33 1 1) v128_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v128_pg : Scalar.QComplex := ((-93083275636849391690451 : Int)/10^30,(-701075459095868341428 : Int)/10^30)
theorem v128_pg_checked : Scalar.distance (sourceCoefficient 1 33 1 2) v128_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v128_mb : Scalar.QComplex := ((2877299677256853535402411 : Int)/10^30,(-431463160753075333222599823 : Int)/10^30)
theorem v128_mb_checked : Scalar.distance (sourceCoefficient 1 33 3 1) v128_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v128_mg : Scalar.QComplex := ((-93083845974237689422922 : Int)/10^30,(-620748523493941795280 : Int)/10^30)
theorem v128_mg_checked : Scalar.distance (sourceCoefficient 1 33 3 2) v128_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v128_upper : Scalar.QComplex := ((999983147266691096203386488668 : Int)/10^30,(5805616470555699065253996437 : Int)/10^30)
theorem v128_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 33 5) 1) 14) v128_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material128 : Material (1 : Basis) (33 : Basis) where
  plus := ![v128_pa,v128_pb,v128_pg]
  minus := ![(Primitive.Addresses.material128 1).one,v128_mb,v128_mg]
  upper := v128_upper
  lower := (Primitive.Addresses.material128 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v128_pa_checked.trans (by decide +kernel)
    · exact v128_pb_checked.trans (by decide +kernel)
    · exact v128_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 33 Primitive.Addresses.material128
    · exact v128_mb_checked.trans (by decide +kernel)
    · exact v128_mg_checked.trans (by decide +kernel)
  upper_error := v128_upper_checked
  lower_error := reuse_lower_error 1 33 Primitive.Addresses.material128

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
