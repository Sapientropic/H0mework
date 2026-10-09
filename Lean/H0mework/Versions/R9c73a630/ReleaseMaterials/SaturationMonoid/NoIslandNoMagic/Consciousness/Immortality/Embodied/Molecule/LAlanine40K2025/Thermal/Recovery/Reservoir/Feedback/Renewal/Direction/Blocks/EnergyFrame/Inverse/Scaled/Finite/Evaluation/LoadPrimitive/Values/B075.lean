import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B050

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1201_pa : Scalar.QComplex := ((999999951839349565434793598012 : Int)/10^30,(-310356727894985647793920299 : Int)/10^30)
theorem v1201_pa_checked : Scalar.distance (sourceCoefficient 13 32 1 0) v1201_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1201_pb : Scalar.QComplex := ((-133911949751529790773213 : Int)/10^30,(-431477494335339555899214792 : Int)/10^30)
theorem v1201_pb_checked : Scalar.distance (sourceCoefficient 13 32 1 1) v1201_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1201_pg : Scalar.QComplex := ((-93086424779053615998624 : Int)/10^30,(28889999597230964258 : Int)/10^30)
theorem v1201_pg_checked : Scalar.distance (sourceCoefficient 13 32 1 2) v1201_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1201_mb : Scalar.QComplex := ((-506257544476431788419819 : Int)/10^30,(-431477218116567453957355941 : Int)/10^30)
theorem v1201_mb_checked : Scalar.distance (sourceCoefficient 13 32 3 1) v1201_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1201_mg : Scalar.QComplex := ((-93086365187954915850171 : Int)/10^30,(109219380967546315187 : Int)/10^30)
theorem v1201_mg_checked : Scalar.distance (sourceCoefficient 13 32 3 2) v1201_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1201_upper : Scalar.QComplex := ((999997926809332542432830197522 : Int)/10^30,(-2036265463242843174272587866 : Int)/10^30)
theorem v1201_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 32 5) 1) 14) v1201_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1201 : Material (13 : Basis) (32 : Basis) where
  plus := ![v1201_pa,v1201_pb,v1201_pg]
  minus := ![(Primitive.Addresses.material1201 1).one,v1201_mb,v1201_mg]
  upper := v1201_upper
  lower := (Primitive.Addresses.material1201 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1201_pa_checked.trans (by decide +kernel)
    · exact v1201_pb_checked.trans (by decide +kernel)
    · exact v1201_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 32 Primitive.Addresses.material1201
    · exact v1201_mb_checked.trans (by decide +kernel)
    · exact v1201_mg_checked.trans (by decide +kernel)
  upper_error := v1201_upper_checked
  lower_error := reuse_lower_error 13 32 Primitive.Addresses.material1201

def v1202_pa : Scalar.QComplex := ((999999949751426740295953867911 : Int)/10^30,(-317012845156925743188274682 : Int)/10^30)
theorem v1202_pa_checked : Scalar.distance (sourceCoefficient 13 33 1 0) v1202_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1202_pb : Scalar.QComplex := ((-136783914600202085014174 : Int)/10^30,(-431477493157400625814008441 : Int)/10^30)
theorem v1202_pb_checked : Scalar.distance (sourceCoefficient 13 33 1 1) v1202_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1202_pg : Scalar.QComplex := ((-93086424554811427072302 : Int)/10^30,(29509593776421270027 : Int)/10^30)
theorem v1202_pg_checked : Scalar.distance (sourceCoefficient 13 33 1 2) v1202_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1202_mb : Scalar.QComplex := ((-509129507239232069958840 : Int)/10^30,(-431477214460252646563600157 : Int)/10^30)
theorem v1202_mb_checked : Scalar.distance (sourceCoefficient 13 33 3 1) v1202_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1202_mg : Scalar.QComplex := ((-93086364429030939264161 : Int)/10^30,(109838974722522481641 : Int)/10^30)
theorem v1202_mg_checked : Scalar.distance (sourceCoefficient 13 33 3 2) v1202_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1202_upper : Scalar.QComplex := ((999997913233558271142246940562 : Int)/10^30,(-2042921566987713109154436041 : Int)/10^30)
theorem v1202_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 33 5) 1) 14) v1202_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1202 : Material (13 : Basis) (33 : Basis) where
  plus := ![v1202_pa,v1202_pb,v1202_pg]
  minus := ![(Primitive.Addresses.material1202 1).one,v1202_mb,v1202_mg]
  upper := v1202_upper
  lower := (Primitive.Addresses.material1202 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1202_pa_checked.trans (by decide +kernel)
    · exact v1202_pb_checked.trans (by decide +kernel)
    · exact v1202_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 33 Primitive.Addresses.material1202
    · exact v1202_mb_checked.trans (by decide +kernel)
    · exact v1202_mg_checked.trans (by decide +kernel)
  upper_error := v1202_upper_checked
  lower_error := reuse_lower_error 13 33 Primitive.Addresses.material1202

def v1203_pa : Scalar.QComplex := ((999999944495605721980764752861 : Int)/10^30,(-333179809525278236546059556 : Int)/10^30)
theorem v1203_pa_checked : Scalar.distance (sourceCoefficient 13 34 1 0) v1203_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1203_pb : Scalar.QComplex := ((-143759595975298910989753 : Int)/10^30,(-431477490190181000948942527 : Int)/10^30)
theorem v1203_pb_checked : Scalar.distance (sourceCoefficient 13 34 1 1) v1203_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1203_pg : Scalar.QComplex := ((-93086423990116463263168 : Int)/10^30,(31014518735858370016 : Int)/10^30)
theorem v1203_pg_checked : Scalar.distance (sourceCoefficient 13 34 1 2) v1203_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1203_mb : Scalar.QComplex := ((-516105183456387017950226 : Int)/10^30,(-431477205473335272847931810 : Int)/10^30)
theorem v1203_mb_checked : Scalar.distance (sourceCoefficient 13 34 3 1) v1203_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1203_mg : Scalar.QComplex := ((-93086362565653725026640 : Int)/10^30,(111343898634300919912 : Int)/10^30)
theorem v1203_mg_checked : Scalar.distance (sourceCoefficient 13 34 3 2) v1203_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1203_upper : Scalar.QComplex := ((999997880075031236529281476407 : Int)/10^30,(-2059088498206201007636915568 : Int)/10^30)
theorem v1203_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 34 5) 1) 14) v1203_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1203 : Material (13 : Basis) (34 : Basis) where
  plus := ![v1203_pa,v1203_pb,v1203_pg]
  minus := ![(Primitive.Addresses.material1203 1).one,v1203_mb,v1203_mg]
  upper := v1203_upper
  lower := (Primitive.Addresses.material1203 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1203_pa_checked.trans (by decide +kernel)
    · exact v1203_pb_checked.trans (by decide +kernel)
    · exact v1203_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 34 Primitive.Addresses.material1203
    · exact v1203_mb_checked.trans (by decide +kernel)
    · exact v1203_mg_checked.trans (by decide +kernel)
  upper_error := v1203_upper_checked
  lower_error := reuse_lower_error 13 34 Primitive.Addresses.material1203

def v1204_pa : Scalar.QComplex := ((999999926063756874937603053708 : Int)/10^30,(-384541910308300136062150498 : Int)/10^30)
theorem v1204_pa_checked : Scalar.distance (sourceCoefficient 13 35 1 0) v1204_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1204_pb : Scalar.QComplex := ((-165921186591697163859173 : Int)/10^30,(-431477479765686415551152649 : Int)/10^30)
theorem v1204_pb_checked : Scalar.distance (sourceCoefficient 13 35 1 1) v1204_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1204_pg : Scalar.QComplex := ((-93086422007755139273149 : Int)/10^30,(35795633189221390933 : Int)/10^30)
theorem v1204_pg_checked : Scalar.distance (sourceCoefficient 13 35 1 2) v1204_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1204_mb : Scalar.QComplex := ((-538266756825142924217463 : Int)/10^30,(-431477175924389988003576595 : Int)/10^30)
theorem v1204_mb_checked : Scalar.distance (sourceCoefficient 13 35 3 1) v1204_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1204_mg : Scalar.QComplex := ((-93086356457406699309481 : Int)/10^30,(116125009596747981753 : Int)/10^30)
theorem v1204_mg_checked : Scalar.distance (sourceCoefficient 13 35 3 2) v1204_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1204_upper : Scalar.QComplex := ((999997772996883423448780247602 : Int)/10^30,(-2110450490679708221293220449 : Int)/10^30)
theorem v1204_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 35 5) 1) 14) v1204_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1204 : Material (13 : Basis) (35 : Basis) where
  plus := ![v1204_pa,v1204_pb,v1204_pg]
  minus := ![(Primitive.Addresses.material1204 1).one,v1204_mb,v1204_mg]
  upper := v1204_upper
  lower := (Primitive.Addresses.material1204 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1204_pa_checked.trans (by decide +kernel)
    · exact v1204_pb_checked.trans (by decide +kernel)
    · exact v1204_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 35 Primitive.Addresses.material1204
    · exact v1204_mb_checked.trans (by decide +kernel)
    · exact v1204_mg_checked.trans (by decide +kernel)
  upper_error := v1204_upper_checked
  lower_error := reuse_lower_error 13 35 Primitive.Addresses.material1204

def v1205_pa : Scalar.QComplex := ((999999919725027550943598234098 : Int)/10^30,(-400686833392415830496043634 : Int)/10^30)
theorem v1205_pa_checked : Scalar.distance (sourceCoefficient 13 36 1 0) v1205_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1205_pb : Scalar.QComplex := ((-172887357487396047272668 : Int)/10^30,(-431477476175389062580159301 : Int)/10^30)
theorem v1205_pb_checked : Scalar.distance (sourceCoefficient 13 36 1 1) v1205_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1205_pg : Scalar.QComplex := ((-93086421325447129883416 : Int)/10^30,(37298506386862230711 : Int)/10^30)
theorem v1205_pg_checked : Scalar.distance (sourceCoefficient 13 36 1 2) v1205_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1205_mb : Scalar.QComplex := ((-545232922028753098800733 : Int)/10^30,(-431477166322602233566627977 : Int)/10^30)
theorem v1205_mb_checked : Scalar.distance (sourceCoefficient 13 36 3 1) v1205_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1205_mg : Scalar.QComplex := ((-93086354478187061306325 : Int)/10^30,(117627881645999363260 : Int)/10^30)
theorem v1205_mg_checked : Scalar.distance (sourceCoefficient 13 36 3 2) v1205_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1205_upper : Scalar.QComplex := ((999997738793490953044741803507 : Int)/10^30,(-2126595378777785729643837079 : Int)/10^30)
theorem v1205_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 36 5) 1) 14) v1205_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1205 : Material (13 : Basis) (36 : Basis) where
  plus := ![v1205_pa,v1205_pb,v1205_pg]
  minus := ![(Primitive.Addresses.material1205 1).one,v1205_mb,v1205_mg]
  upper := v1205_upper
  lower := (Primitive.Addresses.material1205 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1205_pa_checked.trans (by decide +kernel)
    · exact v1205_pb_checked.trans (by decide +kernel)
    · exact v1205_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 36 Primitive.Addresses.material1205
    · exact v1205_mb_checked.trans (by decide +kernel)
    · exact v1205_mg_checked.trans (by decide +kernel)
  upper_error := v1205_upper_checked
  lower_error := reuse_lower_error 13 36 Primitive.Addresses.material1205

def v1206_pa : Scalar.QComplex := ((999999916938905743115577700201 : Int)/10^30,(-407580889658265829553216705 : Int)/10^30)
theorem v1206_pa_checked : Scalar.distance (sourceCoefficient 13 37 1 0) v1206_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1206_pb : Scalar.QComplex := ((-175861987570875214775388 : Int)/10^30,(-431477474596605070948317844 : Int)/10^30)
theorem v1206_pb_checked : Scalar.distance (sourceCoefficient 13 37 1 1) v1206_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1206_pg : Scalar.QComplex := ((-93086421025469605239151 : Int)/10^30,(37940249448023439034 : Int)/10^30)
theorem v1206_pg_checked : Scalar.distance (sourceCoefficient 13 37 1 2) v1206_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1206_mb : Scalar.QComplex := ((-548207549642222059926544 : Int)/10^30,(-431477162176847040111370960 : Int)/10^30)
theorem v1206_mb_checked : Scalar.distance (sourceCoefficient 13 37 3 1) v1206_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1206_mg : Scalar.QComplex := ((-93086353624414289609822 : Int)/10^30,(118269624209343207525 : Int)/10^30)
theorem v1206_mg_checked : Scalar.distance (sourceCoefficient 13 37 3 2) v1206_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1206_upper : Scalar.QComplex := ((999997724108857603859669323504 : Int)/10^30,(-2133489419967155268138899347 : Int)/10^30)
theorem v1206_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 37 5) 1) 14) v1206_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1206 : Material (13 : Basis) (37 : Basis) where
  plus := ![v1206_pa,v1206_pb,v1206_pg]
  minus := ![(Primitive.Addresses.material1206 1).one,v1206_mb,v1206_mg]
  upper := v1206_upper
  lower := (Primitive.Addresses.material1206 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1206_pa_checked.trans (by decide +kernel)
    · exact v1206_pb_checked.trans (by decide +kernel)
    · exact v1206_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 37 Primitive.Addresses.material1206
    · exact v1206_mb_checked.trans (by decide +kernel)
    · exact v1206_mg_checked.trans (by decide +kernel)
  upper_error := v1206_upper_checked
  lower_error := reuse_lower_error 13 37 Primitive.Addresses.material1206

def v1207_pa : Scalar.QComplex := ((999999907170388257632043784769 : Int)/10^30,(-430881903620236871269794495 : Int)/10^30)
theorem v1207_pa_checked : Scalar.distance (sourceCoefficient 13 38 1 0) v1207_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1207_pb : Scalar.QComplex := ((-185915850495507556450006 : Int)/10^30,(-431477469058135641328813266 : Int)/10^30)
theorem v1207_pb_checked : Scalar.distance (sourceCoefficient 13 38 1 1) v1207_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1207_pg : Scalar.QComplex := ((-93086419973380104056370 : Int)/10^30,(40109257562649665276 : Int)/10^30)
theorem v1207_pg_checked : Scalar.distance (sourceCoefficient 13 38 1 2) v1207_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1207_mb : Scalar.QComplex := ((-558261404043892076167607 : Int)/10^30,(-431477147962348777936503392 : Int)/10^30)
theorem v1207_mb_checked : Scalar.distance (sourceCoefficient 13 38 3 1) v1207_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1207_mg : Scalar.QComplex := ((-93086350700568865744727 : Int)/10^30,(120438630608442728954 : Int)/10^30)
theorem v1207_mg_checked : Scalar.distance (sourceCoefficient 13 38 3 2) v1207_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1207_upper : Scalar.QComplex := ((999997674124918420547549838846 : Int)/10^30,(-2156790382365428155911579051 : Int)/10^30)
theorem v1207_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 38 5) 1) 14) v1207_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1207 : Material (13 : Basis) (38 : Basis) where
  plus := ![v1207_pa,v1207_pb,v1207_pg]
  minus := ![(Primitive.Addresses.material1207 1).one,v1207_mb,v1207_mg]
  upper := v1207_upper
  lower := (Primitive.Addresses.material1207 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1207_pa_checked.trans (by decide +kernel)
    · exact v1207_pb_checked.trans (by decide +kernel)
    · exact v1207_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 38 Primitive.Addresses.material1207
    · exact v1207_mb_checked.trans (by decide +kernel)
    · exact v1207_mg_checked.trans (by decide +kernel)
  upper_error := v1207_upper_checked
  lower_error := reuse_lower_error 13 38 Primitive.Addresses.material1207

def v1208_pa : Scalar.QComplex := ((999999901254627974024891707274 : Int)/10^30,(-444399296018008696436930946 : Int)/10^30)
theorem v1208_pa_checked : Scalar.distance (sourceCoefficient 13 39 1 0) v1208_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1208_pb : Scalar.QComplex := ((-191748300939858718349175 : Int)/10^30,(-431477465701995756525658221 : Int)/10^30)
theorem v1208_pb_checked : Scalar.distance (sourceCoefficient 13 39 1 1) v1208_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1208_pg : Scalar.QComplex := ((-93086419336016855649435 : Int)/10^30,(41367543306616496775 : Int)/10^30)
theorem v1208_pg_checked : Scalar.distance (sourceCoefficient 13 39 1 2) v1208_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1208_mb : Scalar.QComplex := ((-564093849420357815825545 : Int)/10^30,(-431477139573068093119289847 : Int)/10^30)
theorem v1208_mb_checked : Scalar.distance (sourceCoefficient 13 39 3 1) v1208_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1208_mg : Scalar.QComplex := ((-93086348977361928700062 : Int)/10^30,(121696915333876493876 : Int)/10^30)
theorem v1208_mg_checked : Scalar.distance (sourceCoefficient 13 39 3 2) v1208_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1208_upper : Scalar.QComplex := ((999997644879373957475343610934 : Int)/10^30,(-2170307744420566293124738753 : Int)/10^30)
theorem v1208_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 39 5) 1) 14) v1208_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1208 : Material (13 : Basis) (39 : Basis) where
  plus := ![v1208_pa,v1208_pb,v1208_pg]
  minus := ![(Primitive.Addresses.material1208 1).one,v1208_mb,v1208_mg]
  upper := v1208_upper
  lower := (Primitive.Addresses.material1208 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1208_pa_checked.trans (by decide +kernel)
    · exact v1208_pb_checked.trans (by decide +kernel)
    · exact v1208_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 39 Primitive.Addresses.material1208
    · exact v1208_mb_checked.trans (by decide +kernel)
    · exact v1208_mg_checked.trans (by decide +kernel)
  upper_error := v1208_upper_checked
  lower_error := reuse_lower_error 13 39 Primitive.Addresses.material1208

def v1209_pa : Scalar.QComplex := ((999999890892536957138214040962 : Int)/10^30,(-467134792304410869246450742 : Int)/10^30)
theorem v1209_pa_checked : Scalar.distance (sourceCoefficient 13 40 1 0) v1209_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1209_pb : Scalar.QComplex := ((-201558155568580400969605 : Int)/10^30,(-431477459820066159146748299 : Int)/10^30)
theorem v1209_pb_checked : Scalar.distance (sourceCoefficient 13 40 1 1) v1209_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1209_pg : Scalar.QComplex := ((-93086418219251696731157 : Int)/10^30,(43483909385630705485 : Int)/10^30)
theorem v1209_pg_checked : Scalar.distance (sourceCoefficient 13 40 1 2) v1209_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1209_mb : Scalar.QComplex := ((-573903695320581957405345 : Int)/10^30,(-431477125225677960716143039 : Int)/10^30)
theorem v1209_mb_checked : Scalar.distance (sourceCoefficient 13 40 3 1) v1209_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1209_mg : Scalar.QComplex := ((-93086346034268577005072 : Int)/10^30,(123813279661152853750 : Int)/10^30)
theorem v1209_mg_checked : Scalar.distance (sourceCoefficient 13 40 3 2) v1209_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1209_upper : Scalar.QComplex := ((999997595277894331487229358072 : Int)/10^30,(-2193043188961088392745840051 : Int)/10^30)
theorem v1209_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 40 5) 1) 14) v1209_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1209 : Material (13 : Basis) (40 : Basis) where
  plus := ![v1209_pa,v1209_pb,v1209_pg]
  minus := ![(Primitive.Addresses.material1209 1).one,v1209_mb,v1209_mg]
  upper := v1209_upper
  lower := (Primitive.Addresses.material1209 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1209_pa_checked.trans (by decide +kernel)
    · exact v1209_pb_checked.trans (by decide +kernel)
    · exact v1209_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 40 Primitive.Addresses.material1209
    · exact v1209_mb_checked.trans (by decide +kernel)
    · exact v1209_mg_checked.trans (by decide +kernel)
  upper_error := v1209_upper_checked
  lower_error := reuse_lower_error 13 40 Primitive.Addresses.material1209

def v1210_pa : Scalar.QComplex := ((999999884021666226496033836538 : Int)/10^30,(-481618785032346955120933037 : Int)/10^30)
theorem v1210_pa_checked : Scalar.distance (sourceCoefficient 13 41 1 0) v1210_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1210_pb : Scalar.QComplex := ((-207807672189178217221498 : Int)/10^30,(-431477455917824445879578924 : Int)/10^30)
theorem v1210_pb_checked : Scalar.distance (sourceCoefficient 13 41 1 1) v1210_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1210_pg : Scalar.QComplex := ((-93086417478526868901921 : Int)/10^30,(44832172488582601031 : Int)/10^30)
theorem v1210_pg_checked : Scalar.distance (sourceCoefficient 13 41 1 2) v1210_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1210_mb : Scalar.QComplex := ((-580153206246740270682378 : Int)/10^30,(-431477115930386324636005936 : Int)/10^30)
theorem v1210_mb_checked : Scalar.distance (sourceCoefficient 13 41 3 1) v1210_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1210_mg : Scalar.QComplex := ((-93086344130053690650051 : Int)/10^30,(125161541622872611990 : Int)/10^30)
theorem v1210_mg_checked : Scalar.distance (sourceCoefficient 13 41 3 2) v1210_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1210_upper : Scalar.QComplex := ((999997563408976363338258031722 : Int)/10^30,(-2207527148258319159097998810 : Int)/10^30)
theorem v1210_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 41 5) 1) 14) v1210_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1210 : Material (13 : Basis) (41 : Basis) where
  plus := ![v1210_pa,v1210_pb,v1210_pg]
  minus := ![(Primitive.Addresses.material1210 1).one,v1210_mb,v1210_mg]
  upper := v1210_upper
  lower := (Primitive.Addresses.material1210 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1210_pa_checked.trans (by decide +kernel)
    · exact v1210_pb_checked.trans (by decide +kernel)
    · exact v1210_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 41 Primitive.Addresses.material1210
    · exact v1210_mb_checked.trans (by decide +kernel)
    · exact v1210_mg_checked.trans (by decide +kernel)
  upper_error := v1210_upper_checked
  lower_error := reuse_lower_error 13 41 Primitive.Addresses.material1210

def v1211_pa : Scalar.QComplex := ((999999878326347105367239773414 : Int)/10^30,(-493302433588957385481541610 : Int)/10^30)
theorem v1211_pa_checked : Scalar.distance (sourceCoefficient 13 42 1 0) v1211_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1211_pb : Scalar.QComplex := ((-212848903344947621730577 : Int)/10^30,(-431477452682099795579757416 : Int)/10^30)
theorem v1211_pb_checked : Scalar.distance (sourceCoefficient 13 42 1 1) v1211_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1211_pg : Scalar.QComplex := ((-93086416864412778094785 : Int)/10^30,(45919761560516116369 : Int)/10^30)
theorem v1211_pg_checked : Scalar.distance (sourceCoefficient 13 42 1 2) v1211_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1211_mb : Scalar.QComplex := ((-585194432733144278672604 : Int)/10^30,(-431477108344307440338170358 : Int)/10^30)
theorem v1211_mb_checked : Scalar.distance (sourceCoefficient 13 42 3 1) v1211_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1211_mg : Scalar.QComplex := ((-93086342577399442620492 : Int)/10^30,(126249129759894208877 : Int)/10^30)
theorem v1211_mg_checked : Scalar.distance (sourceCoefficient 13 42 3 2) v1211_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1211_upper : Scalar.QComplex := ((999997537548748248325991721512 : Int)/10^30,(-2219210769583903394403054966 : Int)/10^30)
theorem v1211_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 42 5) 1) 14) v1211_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1211 : Material (13 : Basis) (42 : Basis) where
  plus := ![v1211_pa,v1211_pb,v1211_pg]
  minus := ![(Primitive.Addresses.material1211 1).one,v1211_mb,v1211_mg]
  upper := v1211_upper
  lower := (Primitive.Addresses.material1211 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1211_pa_checked.trans (by decide +kernel)
    · exact v1211_pb_checked.trans (by decide +kernel)
    · exact v1211_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 42 Primitive.Addresses.material1211
    · exact v1211_mb_checked.trans (by decide +kernel)
    · exact v1211_mg_checked.trans (by decide +kernel)
  upper_error := v1211_upper_checked
  lower_error := reuse_lower_error 13 42 Primitive.Addresses.material1211

def v1212_pa : Scalar.QComplex := ((999999870571335419883483770279 : Int)/10^30,(-508780220142699550551289182 : Int)/10^30)
theorem v1212_pa_checked : Scalar.distance (sourceCoefficient 13 43 1 0) v1212_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1212_pb : Scalar.QComplex := ((-219527219532916927810615 : Int)/10^30,(-431477448274680227814858074 : Int)/10^30)
theorem v1212_pb_checked : Scalar.distance (sourceCoefficient 13 43 1 1) v1212_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1212_pg : Scalar.QComplex := ((-93086416028043963082270 : Int)/10^30,(47360533368853711169 : Int)/10^30)
theorem v1212_pg_checked : Scalar.distance (sourceCoefficient 13 43 1 2) v1212_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1212_mb : Scalar.QComplex := ((-591872742631066669671450 : Int)/10^30,(-431477098173803423635114411 : Int)/10^30)
theorem v1212_mb_checked : Scalar.distance (sourceCoefficient 13 43 3 1) v1212_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1212_mg : Scalar.QComplex := ((-93086340497709758384385 : Int)/10^30,(127689900310017994205 : Int)/10^30)
theorem v1212_mg_checked : Scalar.distance (sourceCoefficient 13 43 3 2) v1212_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1212_upper : Scalar.QComplex := ((999997503080492655089860632155 : Int)/10^30,(-2234688519700853996219894271 : Int)/10^30)
theorem v1212_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 43 5) 1) 14) v1212_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1212 : Material (13 : Basis) (43 : Basis) where
  plus := ![v1212_pa,v1212_pb,v1212_pg]
  minus := ![(Primitive.Addresses.material1212 1).one,v1212_mb,v1212_mg]
  upper := v1212_upper
  lower := (Primitive.Addresses.material1212 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1212_pa_checked.trans (by decide +kernel)
    · exact v1212_pb_checked.trans (by decide +kernel)
    · exact v1212_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 43 Primitive.Addresses.material1212
    · exact v1212_mb_checked.trans (by decide +kernel)
    · exact v1212_mg_checked.trans (by decide +kernel)
  upper_error := v1212_upper_checked
  lower_error := reuse_lower_error 13 43 Primitive.Addresses.material1212

def v1213_pa : Scalar.QComplex := ((999999867574885600585221222219 : Int)/10^30,(-514635998801501092443076676 : Int)/10^30)
theorem v1213_pa_checked : Scalar.distance (sourceCoefficient 13 44 1 0) v1213_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1213_pb : Scalar.QComplex := ((-222053856082032673474397 : Int)/10^30,(-431477446571267123425390638 : Int)/10^30)
theorem v1213_pb_checked : Scalar.distance (sourceCoefficient 13 44 1 1) v1213_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1213_pg : Scalar.QComplex := ((-93086415704833430689188 : Int)/10^30,(47905626865016807881 : Int)/10^30)
theorem v1213_pg_checked : Scalar.distance (sourceCoefficient 13 44 1 2) v1213_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1213_mb : Scalar.QComplex := ((-594399376769431364894835 : Int)/10^30,(-431477094290017407103192229 : Int)/10^30)
theorem v1213_mb_checked : Scalar.distance (sourceCoefficient 13 44 3 1) v1213_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1213_mg : Scalar.QComplex := ((-93086339704108209248328 : Int)/10^30,(128234993324301737699 : Int)/10^30)
theorem v1213_mg_checked : Scalar.distance (sourceCoefficient 13 44 3 2) v1213_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1213_upper : Scalar.QComplex := ((999997489977504565650324021556 : Int)/10^30,(-2240544284466560541603486022 : Int)/10^30)
theorem v1213_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 44 5) 1) 14) v1213_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1213 : Material (13 : Basis) (44 : Basis) where
  plus := ![v1213_pa,v1213_pb,v1213_pg]
  minus := ![(Primitive.Addresses.material1213 1).one,v1213_mb,v1213_mg]
  upper := v1213_upper
  lower := (Primitive.Addresses.material1213 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1213_pa_checked.trans (by decide +kernel)
    · exact v1213_pb_checked.trans (by decide +kernel)
    · exact v1213_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 44 Primitive.Addresses.material1213
    · exact v1213_mb_checked.trans (by decide +kernel)
    · exact v1213_mg_checked.trans (by decide +kernel)
  upper_error := v1213_upper_checked
  lower_error := reuse_lower_error 13 44 Primitive.Addresses.material1213

def v1214_pa : Scalar.QComplex := ((999999866071340755142363971772 : Int)/10^30,(-517549321855250337773907624 : Int)/10^30)
theorem v1214_pa_checked : Scalar.distance (sourceCoefficient 13 45 1 0) v1214_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1214_pb : Scalar.QComplex := ((-223310889334111832370927 : Int)/10^30,(-431477445716449114780567645 : Int)/10^30)
theorem v1214_pb_checked : Scalar.distance (sourceCoefficient 13 45 1 1) v1214_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1214_pg : Scalar.QComplex := ((-93086415542644926679865 : Int)/10^30,(48176817690288516627 : Int)/10^30)
theorem v1214_pg_checked : Scalar.distance (sourceCoefficient 13 45 1 2) v1214_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1214_mb : Scalar.QComplex := ((-595656408815790152898080 : Int)/10^30,(-431477092350436634877904922 : Int)/10^30)
theorem v1214_mb_checked : Scalar.distance (sourceCoefficient 13 45 3 1) v1214_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1214_mg : Scalar.QComplex := ((-93086339307894297401079 : Int)/10^30,(128506183908635333902 : Int)/10^30)
theorem v1214_mg_checked : Scalar.distance (sourceCoefficient 13 45 3 2) v1214_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1214_upper : Scalar.QComplex := ((999997483445830663392577826248 : Int)/10^30,(-2243457600586275318629066161 : Int)/10^30)
theorem v1214_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 45 5) 1) 14) v1214_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1214 : Material (13 : Basis) (45 : Basis) where
  plus := ![v1214_pa,v1214_pb,v1214_pg]
  minus := ![(Primitive.Addresses.material1214 1).one,v1214_mb,v1214_mg]
  upper := v1214_upper
  lower := (Primitive.Addresses.material1214 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1214_pa_checked.trans (by decide +kernel)
    · exact v1214_pb_checked.trans (by decide +kernel)
    · exact v1214_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 45 Primitive.Addresses.material1214
    · exact v1214_mb_checked.trans (by decide +kernel)
    · exact v1214_mg_checked.trans (by decide +kernel)
  upper_error := v1214_upper_checked
  lower_error := reuse_lower_error 13 45 Primitive.Addresses.material1214

def v1215_pa : Scalar.QComplex := ((999999857468143555254579185149 : Int)/10^30,(-533913562830315015817824161 : Int)/10^30)
theorem v1215_pa_checked : Scalar.distance (sourceCoefficient 13 46 1 0) v1215_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1215_pb : Scalar.QComplex := ((-230371690546639495413351 : Int)/10^30,(-431477440824162041764104977 : Int)/10^30)
theorem v1215_pb_checked : Scalar.distance (sourceCoefficient 13 46 1 1) v1215_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1215_pg : Scalar.QComplex := ((-93086414614496471144669 : Int)/10^30,(49700106361774140813 : Int)/10^30)
theorem v1215_pg_checked : Scalar.distance (sourceCoefficient 13 46 1 2) v1215_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1215_mb : Scalar.QComplex := ((-602717203177435426376747 : Int)/10^30,(-431477081364997943753784223 : Int)/10^30)
theorem v1215_mb_checked : Scalar.distance (sourceCoefficient 13 46 3 1) v1215_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1215_mg : Scalar.QComplex := ((-93086337065216670340853 : Int)/10^30,(130029471211980653091 : Int)/10^30)
theorem v1215_mg_checked : Scalar.distance (sourceCoefficient 13 46 3 2) v1215_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1215_upper : Scalar.QComplex := ((999997446599450906339356793926 : Int)/10^30,(-2259821802340387452038708804 : Int)/10^30)
theorem v1215_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 46 5) 1) 14) v1215_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1215 : Material (13 : Basis) (46 : Basis) where
  plus := ![v1215_pa,v1215_pb,v1215_pg]
  minus := ![(Primitive.Addresses.material1215 1).one,v1215_mb,v1215_mg]
  upper := v1215_upper
  lower := (Primitive.Addresses.material1215 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1215_pa_checked.trans (by decide +kernel)
    · exact v1215_pb_checked.trans (by decide +kernel)
    · exact v1215_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 46 Primitive.Addresses.material1215
    · exact v1215_mb_checked.trans (by decide +kernel)
    · exact v1215_mg_checked.trans (by decide +kernel)
  upper_error := v1215_upper_checked
  lower_error := reuse_lower_error 13 46 Primitive.Addresses.material1215

def v1216_pa : Scalar.QComplex := ((999999855357815055785570692064 : Int)/10^30,(-537851604968384558579629670 : Int)/10^30)
theorem v1216_pa_checked : Scalar.distance (sourceCoefficient 13 47 1 0) v1216_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1216_pb : Scalar.QComplex := ((-232070866976568187510499 : Int)/10^30,(-431477439623838764668513323 : Int)/10^30)
theorem v1216_pb_checked : Scalar.distance (sourceCoefficient 13 47 1 1) v1216_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1216_pg : Scalar.QComplex := ((-93086414386796864173747 : Int)/10^30,(50066684620445472538 : Int)/10^30)
theorem v1216_pg_checked : Scalar.distance (sourceCoefficient 13 47 1 2) v1216_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1216_mb : Scalar.QComplex := ((-604416377938858149832385 : Int)/10^30,(-431477078698362382630493496 : Int)/10^30)
theorem v1216_mb_checked : Scalar.distance (sourceCoefficient 13 47 3 1) v1216_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1216_mg : Scalar.QComplex := ((-93086336521176620991429 : Int)/10^30,(130396049137663640052 : Int)/10^30)
theorem v1216_mg_checked : Scalar.distance (sourceCoefficient 13 47 3 2) v1216_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1216_upper : Scalar.QComplex := ((999997437692422076040752739066 : Int)/10^30,(-2263759834970970282493446474 : Int)/10^30)
theorem v1216_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 47 5) 1) 14) v1216_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1216 : Material (13 : Basis) (47 : Basis) where
  plus := ![v1216_pa,v1216_pb,v1216_pg]
  minus := ![(Primitive.Addresses.material1216 1).one,v1216_mb,v1216_mg]
  upper := v1216_upper
  lower := (Primitive.Addresses.material1216 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1216_pa_checked.trans (by decide +kernel)
    · exact v1216_pb_checked.trans (by decide +kernel)
    · exact v1216_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 47 Primitive.Addresses.material1216
    · exact v1216_mb_checked.trans (by decide +kernel)
    · exact v1216_mg_checked.trans (by decide +kernel)
  upper_error := v1216_upper_checked
  lower_error := reuse_lower_error 13 47 Primitive.Addresses.material1216

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
