import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B044
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B045

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1073_pa : Scalar.QComplex := ((999999546540529220310072010590 : Int)/10^30,(-952322810781033542382726173 : Int)/10^30)
theorem v1073_pa_checked : Scalar.distance (sourceCoefficient 11 73 1 0) v1073_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1073_pb : Scalar.QComplex := ((-410905811385953006217270 : Int)/10^30,(-431477247426030918895275897 : Int)/10^30)
theorem v1073_pb_checked : Scalar.distance (sourceCoefficient 11 73 1 1) v1073_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1073_pg : Scalar.QComplex := ((-93086379281188083424735 : Int)/10^30,(88648322560911834281 : Int)/10^30)
theorem v1073_pg_checked : Scalar.distance (sourceCoefficient 11 73 1 2) v1073_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1073_mb : Scalar.QComplex := ((-783251089901768101230647 : Int)/10^30,(-431476732174123502487710001 : Int)/10^30)
theorem v1073_mb_checked : Scalar.distance (sourceCoefficient 11 73 3 1) v1073_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1073_mg : Scalar.QComplex := ((-93086268121365021510650 : Int)/10^30,(168977642417863648738 : Int)/10^30)
theorem v1073_mg_checked : Scalar.distance (sourceCoefficient 11 73 3 2) v1073_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1073_upper : Scalar.QComplex := ((999996413535895489076203478919 : Int)/10^30,(-2678229890486825749574215077 : Int)/10^30)
theorem v1073_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 73 5) 1) 14) v1073_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1073 : Material (11 : Basis) (73 : Basis) where
  plus := ![v1073_pa,v1073_pb,v1073_pg]
  minus := ![(Primitive.Addresses.material1073 1).one,v1073_mb,v1073_mg]
  upper := v1073_upper
  lower := (Primitive.Addresses.material1073 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1073_pa_checked.trans (by decide +kernel)
    · exact v1073_pb_checked.trans (by decide +kernel)
    · exact v1073_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 73 Primitive.Addresses.material1073
    · exact v1073_mb_checked.trans (by decide +kernel)
    · exact v1073_mg_checked.trans (by decide +kernel)
  upper_error := v1073_upper_checked
  lower_error := reuse_lower_error 11 73 Primitive.Addresses.material1073

def v1074_pa : Scalar.QComplex := ((999999536357786039636019051651 : Int)/10^30,(-962955976645155568052957148 : Int)/10^30)
theorem v1074_pa_checked : Scalar.distance (sourceCoefficient 11 74 1 0) v1074_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1074_pb : Scalar.QComplex := ((-415493781064139941417171 : Int)/10^30,(-431477241432388657068094726 : Int)/10^30)
theorem v1074_pb_checked : Scalar.distance (sourceCoefficient 11 74 1 1) v1074_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1074_pg : Scalar.QComplex := ((-93086378160719967794446 : Int)/10^30,(89638125754135456535 : Int)/10^30)
theorem v1074_pg_checked : Scalar.distance (sourceCoefficient 11 74 1 2) v1074_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1074_mb : Scalar.QComplex := ((-787839052699400916338665 : Int)/10^30,(-431476722221272274575813758 : Int)/10^30)
theorem v1074_mb_checked : Scalar.distance (sourceCoefficient 11 74 3 1) v1074_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1074_mg : Scalar.QComplex := ((-93086266146741746410831 : Int)/10^30,(169967444275624786136 : Int)/10^30)
theorem v1074_mg_checked : Scalar.distance (sourceCoefficient 11 74 3 2) v1074_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1074_upper : Scalar.QComplex := ((999996385001287826199244343655 : Int)/10^30,(-2688863022939605321440556546 : Int)/10^30)
theorem v1074_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 74 5) 1) 14) v1074_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1074 : Material (11 : Basis) (74 : Basis) where
  plus := ![v1074_pa,v1074_pb,v1074_pg]
  minus := ![(Primitive.Addresses.material1074 1).one,v1074_mb,v1074_mg]
  upper := v1074_upper
  lower := (Primitive.Addresses.material1074 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1074_pa_checked.trans (by decide +kernel)
    · exact v1074_pb_checked.trans (by decide +kernel)
    · exact v1074_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 74 Primitive.Addresses.material1074
    · exact v1074_mb_checked.trans (by decide +kernel)
    · exact v1074_mg_checked.trans (by decide +kernel)
  upper_error := v1074_upper_checked
  lower_error := reuse_lower_error 11 74 Primitive.Addresses.material1074

def v1075_pa : Scalar.QComplex := ((999999521981725109494877444544 : Int)/10^30,(-977771098611295176288137248 : Int)/10^30)
theorem v1075_pa_checked : Scalar.distance (sourceCoefficient 11 75 1 0) v1075_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1075_pb : Scalar.QComplex := ((-421886169779105145767605 : Int)/10^30,(-431477232973034877537807909 : Int)/10^30)
theorem v1075_pb_checked : Scalar.distance (sourceCoefficient 11 75 1 1) v1075_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1075_pg : Scalar.QComplex := ((-93086376579106574991852 : Int)/10^30,(91017212201388534521 : Int)/10^30)
theorem v1075_pg_checked : Scalar.distance (sourceCoefficient 11 75 1 2) v1075_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1075_mb : Scalar.QComplex := ((-794231431734146338927333 : Int)/10^30,(-431476708245578086334858128 : Int)/10^30)
theorem v1075_mb_checked : Scalar.distance (sourceCoefficient 11 75 3 1) v1075_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1075_mg : Scalar.QComplex := ((-93086263375039450283668 : Int)/10^30,(171346528844519827679 : Int)/10^30)
theorem v1075_mg_checked : Scalar.distance (sourceCoefficient 11 75 3 2) v1075_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1075_upper : Scalar.QComplex := ((999996345055691811321044309193 : Int)/10^30,(-2703678098028584088223024767 : Int)/10^30)
theorem v1075_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 75 5) 1) 14) v1075_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1075 : Material (11 : Basis) (75 : Basis) where
  plus := ![v1075_pa,v1075_pb,v1075_pg]
  minus := ![(Primitive.Addresses.material1075 1).one,v1075_mb,v1075_mg]
  upper := v1075_upper
  lower := (Primitive.Addresses.material1075 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1075_pa_checked.trans (by decide +kernel)
    · exact v1075_pb_checked.trans (by decide +kernel)
    · exact v1075_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 75 Primitive.Addresses.material1075
    · exact v1075_mb_checked.trans (by decide +kernel)
    · exact v1075_mg_checked.trans (by decide +kernel)
  upper_error := v1075_upper_checked
  lower_error := reuse_lower_error 11 75 Primitive.Addresses.material1075

def v1076_pa : Scalar.QComplex := ((999999509750594785207762333063 : Int)/10^30,(-990201277561842555854756700 : Int)/10^30)
theorem v1076_pa_checked : Scalar.distance (sourceCoefficient 11 76 1 0) v1076_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1076_pb : Scalar.QComplex := ((-427249509663085869526595 : Int)/10^30,(-431477225778053214490913365 : Int)/10^30)
theorem v1076_pb_checked : Scalar.distance (sourceCoefficient 11 76 1 1) v1076_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1076_pg : Scalar.QComplex := ((-93086375233712192211752 : Int)/10^30,(92174292868415127990 : Int)/10^30)
theorem v1076_pg_checked : Scalar.distance (sourceCoefficient 11 76 1 2) v1076_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1076_mb : Scalar.QComplex := ((-799594763412165381873923 : Int)/10^30,(-431476696422278338294498458 : Int)/10^30)
theorem v1076_mb_checked : Scalar.distance (sourceCoefficient 11 76 3 1) v1076_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1076_mg : Scalar.QComplex := ((-93086261031137065790152 : Int)/10^30,(172503607919697649590 : Int)/10^30)
theorem v1076_mg_checked : Scalar.distance (sourceCoefficient 11 76 3 2) v1076_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1076_upper : Scalar.QComplex := ((999996311371218492246620981376 : Int)/10^30,(-2716108237356018732094637659 : Int)/10^30)
theorem v1076_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 76 5) 1) 14) v1076_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1076 : Material (11 : Basis) (76 : Basis) where
  plus := ![v1076_pa,v1076_pb,v1076_pg]
  minus := ![(Primitive.Addresses.material1076 1).one,v1076_mb,v1076_mg]
  upper := v1076_upper
  lower := (Primitive.Addresses.material1076 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1076_pa_checked.trans (by decide +kernel)
    · exact v1076_pb_checked.trans (by decide +kernel)
    · exact v1076_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 76 Primitive.Addresses.material1076
    · exact v1076_mb_checked.trans (by decide +kernel)
    · exact v1076_mg_checked.trans (by decide +kernel)
  upper_error := v1076_upper_checked
  lower_error := reuse_lower_error 11 76 Primitive.Addresses.material1076

def v1077_pa : Scalar.QComplex := ((999999506896958514725361127139 : Int)/10^30,(-993078969578925156143391147 : Int)/10^30)
theorem v1077_pa_checked : Scalar.distance (sourceCoefficient 11 77 1 0) v1077_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1077_pb : Scalar.QComplex := ((-428491168395985946090425 : Int)/10^30,(-431477224099682390028079045 : Int)/10^30)
theorem v1077_pb_checked : Scalar.distance (sourceCoefficient 11 77 1 1) v1077_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1077_pg : Scalar.QComplex := ((-93086374919849955371776 : Int)/10^30,(92442166870755740910 : Int)/10^30)
theorem v1077_pg_checked : Scalar.distance (sourceCoefficient 11 77 1 2) v1077_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1077_mb : Scalar.QComplex := ((-800836420234380735076059 : Int)/10^30,(-431476693672412574506460284 : Int)/10^30)
theorem v1077_mb_checked : Scalar.distance (sourceCoefficient 11 77 3 1) v1077_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1077_mg : Scalar.QComplex := ((-93086260486111746392689 : Int)/10^30,(172771481551447554429 : Int)/10^30)
theorem v1077_mg_checked : Scalar.distance (sourceCoefficient 11 77 3 2) v1077_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1077_upper : Scalar.QComplex := ((999996303550951112616148790521 : Int)/10^30,(-2718985920161999787396476431 : Int)/10^30)
theorem v1077_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 77 5) 1) 14) v1077_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1077 : Material (11 : Basis) (77 : Basis) where
  plus := ![v1077_pa,v1077_pb,v1077_pg]
  minus := ![(Primitive.Addresses.material1077 1).one,v1077_mb,v1077_mg]
  upper := v1077_upper
  lower := (Primitive.Addresses.material1077 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1077_pa_checked.trans (by decide +kernel)
    · exact v1077_pb_checked.trans (by decide +kernel)
    · exact v1077_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 77 Primitive.Addresses.material1077
    · exact v1077_mb_checked.trans (by decide +kernel)
    · exact v1077_mg_checked.trans (by decide +kernel)
  upper_error := v1077_upper_checked
  lower_error := reuse_lower_error 11 77 Primitive.Addresses.material1077

def v1078_pa : Scalar.QComplex := ((999999489567462425814477600838 : Int)/10^30,(-1010378550151870370938172203 : Int)/10^30)
theorem v1078_pa_checked : Scalar.distance (sourceCoefficient 11 78 1 0) v1078_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1078_pb : Scalar.QComplex := ((-435955544339397859257617 : Int)/10^30,(-431477213909553491644892132 : Int)/10^30)
theorem v1078_pb_checked : Scalar.distance (sourceCoefficient 11 78 1 1) v1078_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1078_pg : Scalar.QComplex := ((-93086373014076544985654 : Int)/10^30,(94052522612326633374 : Int)/10^30)
theorem v1078_pg_checked : Scalar.distance (sourceCoefficient 11 78 1 2) v1078_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1078_mb : Scalar.QComplex := ((-808300784604842052741784 : Int)/10^30,(-431476677040867214222284297 : Int)/10^30)
theorem v1078_mb_checked : Scalar.distance (sourceCoefficient 11 78 3 1) v1078_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1078_mg : Scalar.QComplex := ((-93086257190674568367670 : Int)/10^30,(174381835048812787098 : Int)/10^30)
theorem v1078_mg_checked : Scalar.distance (sourceCoefficient 11 78 3 2) v1078_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1078_upper : Scalar.QComplex := ((999996256363974170740636475046 : Int)/10^30,(-2736285445060113760418590795 : Int)/10^30)
theorem v1078_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 78 5) 1) 14) v1078_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1078 : Material (11 : Basis) (78 : Basis) where
  plus := ![v1078_pa,v1078_pb,v1078_pg]
  minus := ![(Primitive.Addresses.material1078 1).one,v1078_mb,v1078_mg]
  upper := v1078_upper
  lower := (Primitive.Addresses.material1078 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1078_pa_checked.trans (by decide +kernel)
    · exact v1078_pb_checked.trans (by decide +kernel)
    · exact v1078_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 78 Primitive.Addresses.material1078
    · exact v1078_mb_checked.trans (by decide +kernel)
    · exact v1078_mg_checked.trans (by decide +kernel)
  upper_error := v1078_upper_checked
  lower_error := reuse_lower_error 11 78 Primitive.Addresses.material1078

def v1079_pa : Scalar.QComplex := ((999999483916947431657306212127 : Int)/10^30,(-1015955628359313849476441422 : Int)/10^30)
theorem v1079_pa_checked : Scalar.distance (sourceCoefficient 11 79 1 0) v1079_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1079_pb : Scalar.QComplex := ((-438361926836549126718994 : Int)/10^30,(-431477210587736473147014343 : Int)/10^30)
theorem v1079_pb_checked : Scalar.distance (sourceCoefficient 11 79 1 1) v1079_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1079_pg : Scalar.QComplex := ((-93086372392761048305802 : Int)/10^30,(94571672762814202211 : Int)/10^30)
theorem v1079_pg_checked : Scalar.distance (sourceCoefficient 11 79 1 2) v1079_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1079_mb : Scalar.QComplex := ((-810707163339408661521739 : Int)/10^30,(-431476671642451716991590814 : Int)/10^30)
theorem v1079_mb_checked : Scalar.distance (sourceCoefficient 11 79 3 1) v1079_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1079_mg : Scalar.QComplex := ((-93086256121356104816011 : Int)/10^30,(174900984469829737952 : Int)/10^30)
theorem v1079_mg_checked : Scalar.distance (sourceCoefficient 11 79 3 2) v1079_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1079_upper : Scalar.QComplex := ((999996241087936554897074646281 : Int)/10^30,(-2741862505208878109397088250 : Int)/10^30)
theorem v1079_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 79 5) 1) 14) v1079_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1079 : Material (11 : Basis) (79 : Basis) where
  plus := ![v1079_pa,v1079_pb,v1079_pg]
  minus := ![(Primitive.Addresses.material1079 1).one,v1079_mb,v1079_mg]
  upper := v1079_upper
  lower := (Primitive.Addresses.material1079 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1079_pa_checked.trans (by decide +kernel)
    · exact v1079_pb_checked.trans (by decide +kernel)
    · exact v1079_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 79 Primitive.Addresses.material1079
    · exact v1079_mb_checked.trans (by decide +kernel)
    · exact v1079_mg_checked.trans (by decide +kernel)
  upper_error := v1079_upper_checked
  lower_error := reuse_lower_error 11 79 Primitive.Addresses.material1079

def v1080_pa : Scalar.QComplex := ((999999475028041853408422108815 : Int)/10^30,(-1024667575703274762071531196 : Int)/10^30)
theorem v1080_pa_checked : Scalar.distance (sourceCoefficient 11 80 1 0) v1080_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1080_pb : Scalar.QComplex := ((-442120934091541385572287 : Int)/10^30,(-431477205362921578732255398 : Int)/10^30)
theorem v1080_pb_checked : Scalar.distance (sourceCoefficient 11 80 1 1) v1080_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1080_pg : Scalar.QComplex := ((-93086371415445229758312 : Int)/10^30,(95382636602488387224 : Int)/10^30)
theorem v1080_pg_checked : Scalar.distance (sourceCoefficient 11 80 1 2) v1080_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1080_mb : Scalar.QComplex := ((-814466164685970787270543 : Int)/10^30,(-431476663173784806357959138 : Int)/10^30)
theorem v1080_mb_checked : Scalar.distance (sourceCoefficient 11 80 3 1) v1080_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1080_mg : Scalar.QComplex := ((-93086254444215380984531 : Int)/10^30,(175711947164165487839 : Int)/10^30)
theorem v1080_mg_checked : Scalar.distance (sourceCoefficient 11 80 3 2) v1080_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1080_upper : Scalar.QComplex := ((999996217163013441641583674284 : Int)/10^30,(-2750574424235972197543020455 : Int)/10^30)
theorem v1080_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 80 5) 1) 14) v1080_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1080 : Material (11 : Basis) (80 : Basis) where
  plus := ![v1080_pa,v1080_pb,v1080_pg]
  minus := ![(Primitive.Addresses.material1080 1).one,v1080_mb,v1080_mg]
  upper := v1080_upper
  lower := (Primitive.Addresses.material1080 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1080_pa_checked.trans (by decide +kernel)
    · exact v1080_pb_checked.trans (by decide +kernel)
    · exact v1080_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 80 Primitive.Addresses.material1080
    · exact v1080_mb_checked.trans (by decide +kernel)
    · exact v1080_mg_checked.trans (by decide +kernel)
  upper_error := v1080_upper_checked
  lower_error := reuse_lower_error 11 80 Primitive.Addresses.material1080

def v1081_pa : Scalar.QComplex := ((999999447804756747979390586310 : Int)/10^30,(-1050899701010736109091848080 : Int)/10^30)
theorem v1081_pa_checked : Scalar.distance (sourceCoefficient 11 81 1 0) v1081_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1081_pb : Scalar.QComplex := ((-453439499685925401146713 : Int)/10^30,(-431477189367054721263951041 : Int)/10^30)
theorem v1081_pb_checked : Scalar.distance (sourceCoefficient 11 81 1 1) v1081_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1081_pg : Scalar.QComplex := ((-93086368422921679582859 : Int)/10^30,(97824490762042092377 : Int)/10^30)
theorem v1081_pg_checked : Scalar.distance (sourceCoefficient 11 81 1 2) v1081_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1081_mb : Scalar.QComplex := ((-825784712262222877158390 : Int)/10^30,(-431476637410511566199373821 : Int)/10^30)
theorem v1081_mb_checked : Scalar.distance (sourceCoefficient 11 81 3 1) v1081_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1081_mg : Scalar.QComplex := ((-93086249344482782396321 : Int)/10^30,(178153797832092245599 : Int)/10^30)
theorem v1081_mg_checked : Scalar.distance (sourceCoefficient 11 81 3 2) v1081_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1081_upper : Scalar.QComplex := ((999996144665500361237789388757 : Int)/10^30,(-2776806463488843926159959752 : Int)/10^30)
theorem v1081_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 81 5) 1) 14) v1081_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1081 : Material (11 : Basis) (81 : Basis) where
  plus := ![v1081_pa,v1081_pb,v1081_pg]
  minus := ![(Primitive.Addresses.material1081 1).one,v1081_mb,v1081_mg]
  upper := v1081_upper
  lower := (Primitive.Addresses.material1081 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1081_pa_checked.trans (by decide +kernel)
    · exact v1081_pb_checked.trans (by decide +kernel)
    · exact v1081_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 81 Primitive.Addresses.material1081
    · exact v1081_mb_checked.trans (by decide +kernel)
    · exact v1081_mg_checked.trans (by decide +kernel)
  upper_error := v1081_upper_checked
  lower_error := reuse_lower_error 11 81 Primitive.Addresses.material1081

def v1082_pa : Scalar.QComplex := ((999999437309137291563334051857 : Int)/10^30,(-1060839954373828416436046624 : Int)/10^30)
theorem v1082_pa_checked : Scalar.distance (sourceCoefficient 11 82 1 0) v1082_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1082_pb : Scalar.QComplex := ((-457728492901255422590308 : Int)/10^30,(-431477183202242431402225988 : Int)/10^30)
theorem v1082_pb_checked : Scalar.distance (sourceCoefficient 11 82 1 1) v1082_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1082_pg : Scalar.QComplex := ((-93086367269427289125534 : Int)/10^30,(98749793172530992802 : Int)/10^30)
theorem v1082_pg_checked : Scalar.distance (sourceCoefficient 11 82 1 2) v1082_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1082_mb : Scalar.QComplex := ((-830073698560609354549167 : Int)/10^30,(-431476627544493596032846631 : Int)/10^30)
theorem v1082_mb_checked : Scalar.distance (sourceCoefficient 11 82 3 1) v1082_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1082_mg : Scalar.QComplex := ((-93086247392494515259308 : Int)/10^30,(179079098902635062683 : Int)/10^30)
theorem v1082_mg_checked : Scalar.distance (sourceCoefficient 11 82 3 2) v1082_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1082_upper : Scalar.QComplex := ((999996117013921004857526302405 : Int)/10^30,(-2786746683932609486747275104 : Int)/10^30)
theorem v1082_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 82 5) 1) 14) v1082_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1082 : Material (11 : Basis) (82 : Basis) where
  plus := ![v1082_pa,v1082_pb,v1082_pg]
  minus := ![(Primitive.Addresses.material1082 1).one,v1082_mb,v1082_mg]
  upper := v1082_upper
  lower := (Primitive.Addresses.material1082 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1082_pa_checked.trans (by decide +kernel)
    · exact v1082_pb_checked.trans (by decide +kernel)
    · exact v1082_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 82 Primitive.Addresses.material1082
    · exact v1082_mb_checked.trans (by decide +kernel)
    · exact v1082_mg_checked.trans (by decide +kernel)
  upper_error := v1082_upper_checked
  lower_error := reuse_lower_error 11 82 Primitive.Addresses.material1082

def v1083_pa : Scalar.QComplex := ((999999422822948518067745282553 : Int)/10^30,(-1074408567459565519662604280 : Int)/10^30)
theorem v1083_pa_checked : Scalar.distance (sourceCoefficient 11 83 1 0) v1083_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1083_pb : Scalar.QComplex := ((-463583040725492949606826 : Int)/10^30,(-431477174695413941749436983 : Int)/10^30)
theorem v1083_pb_checked : Scalar.distance (sourceCoefficient 11 83 1 1) v1083_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1083_pg : Scalar.QComplex := ((-93086365677567122893309 : Int)/10^30,(100012846522772026899 : Int)/10^30)
theorem v1083_pg_checked : Scalar.distance (sourceCoefficient 11 83 1 2) v1083_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1083_mb : Scalar.QComplex := ((-835928236863921307310693 : Int)/10^30,(-431476613985457180589877157 : Int)/10^30)
theorem v1083_mb_checked : Scalar.distance (sourceCoefficient 11 83 3 1) v1083_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1083_mg : Scalar.QComplex := ((-93086244710676786302557 : Int)/10^30,(180342150408879981358 : Int)/10^30)
theorem v1083_mg_checked : Scalar.distance (sourceCoefficient 11 83 3 2) v1083_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1083_upper : Scalar.QComplex := ((999996079109558555819810036308 : Int)/10^30,(-2800315251807643633751879480 : Int)/10^30)
theorem v1083_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 83 5) 1) 14) v1083_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1083 : Material (11 : Basis) (83 : Basis) where
  plus := ![v1083_pa,v1083_pb,v1083_pg]
  minus := ![(Primitive.Addresses.material1083 1).one,v1083_mb,v1083_mg]
  upper := v1083_upper
  lower := (Primitive.Addresses.material1083 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1083_pa_checked.trans (by decide +kernel)
    · exact v1083_pb_checked.trans (by decide +kernel)
    · exact v1083_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 83 Primitive.Addresses.material1083
    · exact v1083_mb_checked.trans (by decide +kernel)
    · exact v1083_mg_checked.trans (by decide +kernel)
  upper_error := v1083_upper_checked
  lower_error := reuse_lower_error 11 83 Primitive.Addresses.material1083

def v1084_pa : Scalar.QComplex := ((999999384451868118637860565054 : Int)/10^30,(-1109547603694055848793258635 : Int)/10^30)
theorem v1084_pa_checked : Scalar.distance (sourceCoefficient 11 84 1 0) v1084_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1084_pb : Scalar.QComplex := ((-478744734932384610208138 : Int)/10^30,(-431477152172702349080531619 : Int)/10^30)
theorem v1084_pb_checked : Scalar.distance (sourceCoefficient 11 84 1 1) v1084_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1084_pg : Scalar.QComplex := ((-93086361462142602009592 : Int)/10^30,(103283812873077100526 : Int)/10^30)
theorem v1084_pg_checked : Scalar.distance (sourceCoefficient 11 84 1 2) v1084_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1084_mb : Scalar.QComplex := ((-851089905989335571830980 : Int)/10^30,(-431476578378894730966555145 : Int)/10^30)
theorem v1084_mb_checked : Scalar.distance (sourceCoefficient 11 84 3 1) v1084_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1084_mg : Scalar.QComplex := ((-93086237672557193556449 : Int)/10^30,(183613111903533286369 : Int)/10^30)
theorem v1084_mg_checked : Scalar.distance (sourceCoefficient 11 84 3 2) v1084_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1084_upper : Scalar.QComplex := ((999995980091746553342044491467 : Int)/10^30,(-2835454169481663440567685360 : Int)/10^30)
theorem v1084_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 84 5) 1) 14) v1084_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1084 : Material (11 : Basis) (84 : Basis) where
  plus := ![v1084_pa,v1084_pb,v1084_pg]
  minus := ![(Primitive.Addresses.material1084 1).one,v1084_mb,v1084_mg]
  upper := v1084_upper
  lower := (Primitive.Addresses.material1084 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1084_pa_checked.trans (by decide +kernel)
    · exact v1084_pb_checked.trans (by decide +kernel)
    · exact v1084_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 84 Primitive.Addresses.material1084
    · exact v1084_mb_checked.trans (by decide +kernel)
    · exact v1084_mg_checked.trans (by decide +kernel)
  upper_error := v1084_upper_checked
  lower_error := reuse_lower_error 11 84 Primitive.Addresses.material1084

def v1085_pa : Scalar.QComplex := ((999999293609577590319025297218 : Int)/10^30,(-1188604368926823807709178895 : Int)/10^30)
theorem v1085_pa_checked : Scalar.distance (sourceCoefficient 11 85 1 0) v1085_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1085_pb : Scalar.QComplex := ((-512855927125183668933077 : Int)/10^30,(-431477098903581872013526764 : Int)/10^30)
theorem v1085_pb_checked : Scalar.distance (sourceCoefficient 11 85 1 1) v1085_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1085_pg : Scalar.QComplex := ((-93086351487943004303523 : Int)/10^30,(110642922223127566819 : Int)/10^30)
theorem v1085_pg_checked : Scalar.distance (sourceCoefficient 11 85 1 2) v1085_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1085_mb : Scalar.QComplex := ((-885201039512126999096255 : Int)/10^30,(-431476495673371537107851457 : Int)/10^30)
theorem v1085_mb_checked : Scalar.distance (sourceCoefficient 11 85 3 1) v1085_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1085_mg : Scalar.QComplex := ((-93086221347781382588603 : Int)/10^30,(190972209906165982179 : Int)/10^30)
theorem v1085_mg_checked : Scalar.distance (sourceCoefficient 11 85 3 2) v1085_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1085_upper : Scalar.QComplex := ((999995752804786505903901573300 : Int)/10^30,(-2914510660183113941614358615 : Int)/10^30)
theorem v1085_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 85 5) 1) 14) v1085_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1085 : Material (11 : Basis) (85 : Basis) where
  plus := ![v1085_pa,v1085_pb,v1085_pg]
  minus := ![(Primitive.Addresses.material1085 1).one,v1085_mb,v1085_mg]
  upper := v1085_upper
  lower := (Primitive.Addresses.material1085 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1085_pa_checked.trans (by decide +kernel)
    · exact v1085_pb_checked.trans (by decide +kernel)
    · exact v1085_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 85 Primitive.Addresses.material1085
    · exact v1085_mb_checked.trans (by decide +kernel)
    · exact v1085_mg_checked.trans (by decide +kernel)
  upper_error := v1085_upper_checked
  lower_error := reuse_lower_error 11 85 Primitive.Addresses.material1085

def v1086_pa : Scalar.QComplex := ((999999276167850047075427088350 : Int)/10^30,(-1203189002598040637672219678 : Int)/10^30)
theorem v1086_pa_checked : Scalar.distance (sourceCoefficient 11 86 1 0) v1086_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1086_pb : Scalar.QComplex := ((-519148863753618517483592 : Int)/10^30,(-431477088683478082379250544 : Int)/10^30)
theorem v1086_pb_checked : Scalar.distance (sourceCoefficient 11 86 1 1) v1086_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1086_pg : Scalar.QComplex := ((-93086349573712603714881 : Int)/10^30,(112000553168689008965 : Int)/10^30)
theorem v1086_pg_checked : Scalar.distance (sourceCoefficient 11 86 1 2) v1086_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1086_mb : Scalar.QComplex := ((-891493964977924665402057 : Int)/10^30,(-431476480022750665890599240 : Int)/10^30)
theorem v1086_mb_checked : Scalar.distance (sourceCoefficient 11 86 3 1) v1086_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1086_mg : Scalar.QComplex := ((-93086218261977334163863 : Int)/10^30,(192329838694324754523 : Int)/10^30)
theorem v1086_mg_checked : Scalar.distance (sourceCoefficient 11 86 3 2) v1086_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1086_upper : Scalar.QComplex := ((999995710191330331175484443496 : Int)/10^30,(-2929095242029392711242909704 : Int)/10^30)
theorem v1086_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 86 5) 1) 14) v1086_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1086 : Material (11 : Basis) (86 : Basis) where
  plus := ![v1086_pa,v1086_pb,v1086_pg]
  minus := ![(Primitive.Addresses.material1086 1).one,v1086_mb,v1086_mg]
  upper := v1086_upper
  lower := (Primitive.Addresses.material1086 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1086_pa_checked.trans (by decide +kernel)
    · exact v1086_pb_checked.trans (by decide +kernel)
    · exact v1086_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 86 Primitive.Addresses.material1086
    · exact v1086_mb_checked.trans (by decide +kernel)
    · exact v1086_mg_checked.trans (by decide +kernel)
  upper_error := v1086_upper_checked
  lower_error := reuse_lower_error 11 86 Primitive.Addresses.material1086

def v1087_pa : Scalar.QComplex := ((999999275005396176365638495640 : Int)/10^30,(-1204154758338849545743088759 : Int)/10^30)
theorem v1087_pa_checked : Scalar.distance (sourceCoefficient 11 87 1 0) v1087_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1087_pb : Scalar.QComplex := ((-519565565314523725547987 : Int)/10^30,(-431477088002410006400579820 : Int)/10^30)
theorem v1087_pb_checked : Scalar.distance (sourceCoefficient 11 87 1 1) v1087_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1087_pg : Scalar.QComplex := ((-93086349446141867761838 : Int)/10^30,(112090451886937420215 : Int)/10^30)
theorem v1087_pg_checked : Scalar.distance (sourceCoefficient 11 87 1 2) v1087_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1087_mb : Scalar.QComplex := ((-891910665795941762737178 : Int)/10^30,(-431476478982088163985124269 : Int)/10^30)
theorem v1087_mb_checked : Scalar.distance (sourceCoefficient 11 87 3 1) v1087_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1087_mg : Scalar.QComplex := ((-93086218056828100750824 : Int)/10^30,(192419737269011964840 : Int)/10^30)
theorem v1087_mg_checked : Scalar.distance (sourceCoefficient 11 87 3 2) v1087_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1087_upper : Scalar.QComplex := ((999995707362071395844423033194 : Int)/10^30,(-2930060994325531965163617953 : Int)/10^30)
theorem v1087_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 87 5) 1) 14) v1087_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1087 : Material (11 : Basis) (87 : Basis) where
  plus := ![v1087_pa,v1087_pb,v1087_pg]
  minus := ![(Primitive.Addresses.material1087 1).one,v1087_mb,v1087_mg]
  upper := v1087_upper
  lower := (Primitive.Addresses.material1087 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1087_pa_checked.trans (by decide +kernel)
    · exact v1087_pb_checked.trans (by decide +kernel)
    · exact v1087_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 87 Primitive.Addresses.material1087
    · exact v1087_mb_checked.trans (by decide +kernel)
    · exact v1087_mg_checked.trans (by decide +kernel)
  upper_error := v1087_upper_checked
  lower_error := reuse_lower_error 11 87 Primitive.Addresses.material1087

def v1088_pa : Scalar.QComplex := ((999999260775881670609738401483 : Int)/10^30,(-1215914343285119489807418437 : Int)/10^30)
theorem v1088_pa_checked : Scalar.distance (sourceCoefficient 11 88 1 0) v1088_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1088_pb : Scalar.QComplex := ((-524639557791240694819795 : Int)/10^30,(-431477079666296543596783398 : Int)/10^30)
theorem v1088_pb_checked : Scalar.distance (sourceCoefficient 11 88 1 1) v1088_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1088_pg : Scalar.QComplex := ((-93086347884643069614669 : Int)/10^30,(113185109226128525498 : Int)/10^30)
theorem v1088_pg_checked : Scalar.distance (sourceCoefficient 11 88 1 2) v1088_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1088_mb : Scalar.QComplex := ((-896984649189688966228859 : Int)/10^30,(-431476466267350821828541348 : Int)/10^30)
theorem v1088_mb_checked : Scalar.distance (sourceCoefficient 11 88 3 1) v1088_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1088_mg : Scalar.QComplex := ((-93086215550689901835496 : Int)/10^30,(193514392853108978924 : Int)/10^30)
theorem v1088_mg_checked : Scalar.distance (sourceCoefficient 11 88 3 2) v1088_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1088_upper : Scalar.QComplex := ((999995672836601287229715242902 : Int)/10^30,(-2941820537198430364180546492 : Int)/10^30)
theorem v1088_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 88 5) 1) 14) v1088_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1088 : Material (11 : Basis) (88 : Basis) where
  plus := ![v1088_pa,v1088_pb,v1088_pg]
  minus := ![(Primitive.Addresses.material1088 1).one,v1088_mb,v1088_mg]
  upper := v1088_upper
  lower := (Primitive.Addresses.material1088 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1088_pa_checked.trans (by decide +kernel)
    · exact v1088_pb_checked.trans (by decide +kernel)
    · exact v1088_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 88 Primitive.Addresses.material1088
    · exact v1088_mb_checked.trans (by decide +kernel)
    · exact v1088_mg_checked.trans (by decide +kernel)
  upper_error := v1088_upper_checked
  lower_error := reuse_lower_error 11 88 Primitive.Addresses.material1088

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
