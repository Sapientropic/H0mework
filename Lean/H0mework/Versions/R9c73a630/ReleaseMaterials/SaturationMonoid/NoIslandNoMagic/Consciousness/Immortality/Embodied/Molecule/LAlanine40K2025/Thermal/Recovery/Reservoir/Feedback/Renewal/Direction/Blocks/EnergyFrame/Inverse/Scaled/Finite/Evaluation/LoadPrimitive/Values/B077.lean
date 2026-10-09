import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B051
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B052

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1233_pa : Scalar.QComplex := ((999999695364873992175130973647 : Int)/10^30,(-780557595064636944084306581 : Int)/10^30)
theorem v1233_pa_checked : Scalar.distance (sourceCoefficient 13 64 1 0) v1233_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1233_pb : Scalar.QComplex := ((-336793024012149514604016 : Int)/10^30,(-431477348427152039770404849 : Int)/10^30)
theorem v1233_pb_checked : Scalar.distance (sourceCoefficient 13 64 1 1) v1233_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1233_pg : Scalar.QComplex := ((-93086397102880471221013 : Int)/10^30,(72659316390436172676 : Int)/10^30)
theorem v1233_pg_checked : Scalar.distance (sourceCoefficient 13 64 1 2) v1233_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1233_mb : Scalar.QComplex := ((-709138417282961076278484 : Int)/10^30,(-431476897131204603587831124 : Int)/10^30)
theorem v1233_mb_checked : Scalar.distance (sourceCoefficient 13 64 3 1) v1233_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1233_mg : Scalar.QComplex := ((-93086299740842980490978 : Int)/10^30,(152988657580143589521 : Int)/10^30)
theorem v1233_mg_checked : Scalar.distance (sourceCoefficient 13 64 3 2) v1233_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1233_upper : Scalar.QComplex := ((999996858811198512415771997977 : Int)/10^30,(-2506465187451858838403654114 : Int)/10^30)
theorem v1233_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 64 5) 1) 14) v1233_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1233 : Material (13 : Basis) (64 : Basis) where
  plus := ![v1233_pa,v1233_pb,v1233_pg]
  minus := ![(Primitive.Addresses.material1233 1).one,v1233_mb,v1233_mg]
  upper := v1233_upper
  lower := (Primitive.Addresses.material1233 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1233_pa_checked.trans (by decide +kernel)
    · exact v1233_pb_checked.trans (by decide +kernel)
    · exact v1233_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 64 Primitive.Addresses.material1233
    · exact v1233_mb_checked.trans (by decide +kernel)
    · exact v1233_mg_checked.trans (by decide +kernel)
  upper_error := v1233_upper_checked
  lower_error := reuse_lower_error 13 64 Primitive.Addresses.material1233

def v1234_pa : Scalar.QComplex := ((999999666644057826963895598220 : Int)/10^30,(-816524202470378722778943316 : Int)/10^30)
theorem v1234_pa_checked : Scalar.distance (sourceCoefficient 13 65 1 0) v1234_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1234_pb : Scalar.QComplex := ((-352311801864752652977015 : Int)/10^30,(-431477332029604980801566026 : Int)/10^30)
theorem v1234_pb_checked : Scalar.distance (sourceCoefficient 13 65 1 1) v1234_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1234_pg : Scalar.QComplex := ((-93086393997328025132338 : Int)/10^30,(76007318957003137928 : Int)/10^30)
theorem v1234_pg_checked : Scalar.distance (sourceCoefficient 13 65 1 2) v1234_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1234_mb : Scalar.QComplex := ((-724657175206869383156493 : Int)/10^30,(-431476867341657303187274815 : Int)/10^30)
theorem v1234_mb_checked : Scalar.distance (sourceCoefficient 13 65 3 1) v1234_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1234_mg : Scalar.QComplex := ((-93086293746116264232187 : Int)/10^30,(156336656220144295880 : Int)/10^30)
theorem v1234_mg_checked : Scalar.distance (sourceCoefficient 13 65 3 2) v1234_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1234_upper : Scalar.QComplex := ((999996768015323606311865815420 : Int)/10^30,(-2542431691720040651671866790 : Int)/10^30)
theorem v1234_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 65 5) 1) 14) v1234_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1234 : Material (13 : Basis) (65 : Basis) where
  plus := ![v1234_pa,v1234_pb,v1234_pg]
  minus := ![(Primitive.Addresses.material1234 1).one,v1234_mb,v1234_mg]
  upper := v1234_upper
  lower := (Primitive.Addresses.material1234 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1234_pa_checked.trans (by decide +kernel)
    · exact v1234_pb_checked.trans (by decide +kernel)
    · exact v1234_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 65 Primitive.Addresses.material1234
    · exact v1234_mb_checked.trans (by decide +kernel)
    · exact v1234_mg_checked.trans (by decide +kernel)
  upper_error := v1234_upper_checked
  lower_error := reuse_lower_error 13 65 Primitive.Addresses.material1234

def v1235_pa : Scalar.QComplex := ((999999652128722905156232100604 : Int)/10^30,(-834111763000176198930560938 : Int)/10^30)
theorem v1235_pa_checked : Scalar.distance (sourceCoefficient 13 66 1 0) v1235_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1235_pb : Scalar.QComplex := ((-359900436398659922548243 : Int)/10^30,(-431477323740319269075955697 : Int)/10^30)
theorem v1235_pb_checked : Scalar.distance (sourceCoefficient 13 66 1 1) v1235_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1235_pg : Scalar.QComplex := ((-93086392427577515119057 : Int)/10^30,(77644481909378013861 : Int)/10^30)
theorem v1235_pg_checked : Scalar.distance (sourceCoefficient 13 66 1 2) v1235_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1235_mb : Scalar.QComplex := ((-732245799761900964373088 : Int)/10^30,(-431476852503724854591559427 : Int)/10^30)
theorem v1235_mb_checked : Scalar.distance (sourceCoefficient 13 66 3 1) v1235_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1235_mg : Scalar.QComplex := ((-93086290763568445891443 : Int)/10^30,(157973817208304591397 : Int)/10^30)
theorem v1235_mg_checked : Scalar.distance (sourceCoefficient 13 66 3 2) v1235_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1235_upper : Scalar.QComplex := ((999996723145476359987692318123 : Int)/10^30,(-2560019201003081444534791177 : Int)/10^30)
theorem v1235_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 66 5) 1) 14) v1235_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1235 : Material (13 : Basis) (66 : Basis) where
  plus := ![v1235_pa,v1235_pb,v1235_pg]
  minus := ![(Primitive.Addresses.material1235 1).one,v1235_mb,v1235_mg]
  upper := v1235_upper
  lower := (Primitive.Addresses.material1235 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1235_pa_checked.trans (by decide +kernel)
    · exact v1235_pb_checked.trans (by decide +kernel)
    · exact v1235_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 66 Primitive.Addresses.material1235
    · exact v1235_mb_checked.trans (by decide +kernel)
    · exact v1235_mg_checked.trans (by decide +kernel)
  upper_error := v1235_upper_checked
  lower_error := reuse_lower_error 13 66 Primitive.Addresses.material1235

def v1236_pa : Scalar.QComplex := ((999999627072485646874658702878 : Int)/10^30,(-863628907362021851511899402 : Int)/10^30)
theorem v1236_pa_checked : Scalar.distance (sourceCoefficient 13 67 1 0) v1236_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1236_pb : Scalar.QComplex := ((-372636416259603035090927 : Int)/10^30,(-431477309428488534249528649 : Int)/10^30)
theorem v1236_pb_checked : Scalar.distance (sourceCoefficient 13 67 1 1) v1236_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1236_pg : Scalar.QComplex := ((-93086389717571290095673 : Int)/10^30,(80392127022497543177 : Int)/10^30)
theorem v1236_pg_checked : Scalar.distance (sourceCoefficient 13 67 1 2) v1236_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1236_mb : Scalar.QComplex := ((-744981762530191368425630 : Int)/10^30,(-431476827201322435959527050 : Int)/10^30)
theorem v1236_mb_checked : Scalar.distance (sourceCoefficient 13 67 3 1) v1236_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1236_mg : Scalar.QComplex := ((-93086285682469246647181 : Int)/10^30,(160721458959736953468 : Int)/10^30)
theorem v1236_mg_checked : Scalar.distance (sourceCoefficient 13 67 3 2) v1236_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1236_upper : Scalar.QComplex := ((999996647145363025901487193594 : Int)/10^30,(-2589536258157815473783951061 : Int)/10^30)
theorem v1236_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 67 5) 1) 14) v1236_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1236 : Material (13 : Basis) (67 : Basis) where
  plus := ![v1236_pa,v1236_pb,v1236_pg]
  minus := ![(Primitive.Addresses.material1236 1).one,v1236_mb,v1236_mg]
  upper := v1236_upper
  lower := (Primitive.Addresses.material1236 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1236_pa_checked.trans (by decide +kernel)
    · exact v1236_pb_checked.trans (by decide +kernel)
    · exact v1236_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 67 Primitive.Addresses.material1236
    · exact v1236_mb_checked.trans (by decide +kernel)
    · exact v1236_mg_checked.trans (by decide +kernel)
  upper_error := v1236_upper_checked
  lower_error := reuse_lower_error 13 67 Primitive.Addresses.material1236

def v1237_pa : Scalar.QComplex := ((999999583409977261682415241535 : Int)/10^30,(-912786871032547292961616209 : Int)/10^30)
theorem v1237_pa_checked : Scalar.distance (sourceCoefficient 13 68 1 0) v1237_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1237_pb : Scalar.QComplex := ((-393846964495762484427660 : Int)/10^30,(-431477284481015691708301824 : Int)/10^30)
theorem v1237_pb_checked : Scalar.distance (sourceCoefficient 13 68 1 1) v1237_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1237_pg : Scalar.QComplex := ((-93086384994309207277852 : Int)/10^30,(84968065491534899110 : Int)/10^30)
theorem v1237_pg_checked : Scalar.distance (sourceCoefficient 13 68 1 2) v1237_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1237_mb : Scalar.QComplex := ((-766192281340148868851997 : Int)/10^30,(-431476783950111042327603429 : Int)/10^30)
theorem v1237_mb_checked : Scalar.distance (sourceCoefficient 13 68 3 1) v1237_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1237_mg : Scalar.QComplex := ((-93086277010380116354586 : Int)/10^30,(165297391648980837015 : Int)/10^30)
theorem v1237_mg_checked : Scalar.distance (sourceCoefficient 13 68 3 2) v1237_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1237_upper : Scalar.QComplex := ((999996518640733951187510031911 : Int)/10^30,(-2638694073255800087012277087 : Int)/10^30)
theorem v1237_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 68 5) 1) 14) v1237_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1237 : Material (13 : Basis) (68 : Basis) where
  plus := ![v1237_pa,v1237_pb,v1237_pg]
  minus := ![(Primitive.Addresses.material1237 1).one,v1237_mb,v1237_mg]
  upper := v1237_upper
  lower := (Primitive.Addresses.material1237 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1237_pa_checked.trans (by decide +kernel)
    · exact v1237_pb_checked.trans (by decide +kernel)
    · exact v1237_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 68 Primitive.Addresses.material1237
    · exact v1237_mb_checked.trans (by decide +kernel)
    · exact v1237_mg_checked.trans (by decide +kernel)
  upper_error := v1237_upper_checked
  lower_error := reuse_lower_error 13 68 Primitive.Addresses.material1237

def v1238_pa : Scalar.QComplex := ((999999563427434454145827574783 : Int)/10^30,(-934422249572484953873116626 : Int)/10^30)
theorem v1238_pa_checked : Scalar.distance (sourceCoefficient 13 69 1 0) v1238_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1238_pb : Scalar.QComplex := ((-403182140150917692858849 : Int)/10^30,(-431477273060567009400473843 : Int)/10^30)
theorem v1238_pb_checked : Scalar.distance (sourceCoefficient 13 69 1 1) v1238_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1238_pg : Scalar.QComplex := ((-93086382832340637963372 : Int)/10^30,(86982025224727191175 : Int)/10^30)
theorem v1238_pg_checked : Scalar.distance (sourceCoefficient 13 69 1 2) v1238_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1238_mb : Scalar.QComplex := ((-775527443664058687348220 : Int)/10^30,(-431476764473830462679830904 : Int)/10^30)
theorem v1238_mb_checked : Scalar.distance (sourceCoefficient 13 69 3 1) v1238_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1238_mg : Scalar.QComplex := ((-93086273110455807674105 : Int)/10^30,(167311348766602374037 : Int)/10^30)
theorem v1238_mg_checked : Scalar.distance (sourceCoefficient 13 69 3 2) v1238_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1238_upper : Scalar.QComplex := ((999996461317520291577728252182 : Int)/10^30,(-2660329385084326799092985742 : Int)/10^30)
theorem v1238_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 69 5) 1) 14) v1238_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1238 : Material (13 : Basis) (69 : Basis) where
  plus := ![v1238_pa,v1238_pb,v1238_pg]
  minus := ![(Primitive.Addresses.material1238 1).one,v1238_mb,v1238_mg]
  upper := v1238_upper
  lower := (Primitive.Addresses.material1238 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1238_pa_checked.trans (by decide +kernel)
    · exact v1238_pb_checked.trans (by decide +kernel)
    · exact v1238_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 69 Primitive.Addresses.material1238
    · exact v1238_mb_checked.trans (by decide +kernel)
    · exact v1238_mg_checked.trans (by decide +kernel)
  upper_error := v1238_upper_checked
  lower_error := reuse_lower_error 13 69 Primitive.Addresses.material1238

def v1239_pa : Scalar.QComplex := ((999999550027494229086030587332 : Int)/10^30,(-948654209428584145925844994 : Int)/10^30)
theorem v1239_pa_checked : Scalar.distance (sourceCoefficient 13 70 1 0) v1239_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1239_pb : Scalar.QComplex := ((-409322908279685519369839 : Int)/10^30,(-431477265401250642681060251 : Int)/10^30)
theorem v1239_pb_checked : Scalar.distance (sourceCoefficient 13 70 1 1) v1239_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1239_pg : Scalar.QComplex := ((-93086381382458587904284 : Int)/10^30,(88306827274588270871 : Int)/10^30)
theorem v1239_pg_checked : Scalar.distance (sourceCoefficient 13 70 1 2) v1239_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1239_mb : Scalar.QComplex := ((-781668202896692830875903 : Int)/10^30,(-431476751515310622677075731 : Int)/10^30)
theorem v1239_mb_checked : Scalar.distance (sourceCoefficient 13 70 3 1) v1239_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1239_mg : Scalar.QComplex := ((-93086270517329795311642 : Int)/10^30,(168636149071996195188 : Int)/10^30)
theorem v1239_mg_checked : Scalar.distance (sourceCoefficient 13 70 3 2) v1239_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1239_upper : Scalar.QComplex := ((999996423354528425840145061327 : Int)/10^30,(-2674561300616512393556454881 : Int)/10^30)
theorem v1239_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 70 5) 1) 14) v1239_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1239 : Material (13 : Basis) (70 : Basis) where
  plus := ![v1239_pa,v1239_pb,v1239_pg]
  minus := ![(Primitive.Addresses.material1239 1).one,v1239_mb,v1239_mg]
  upper := v1239_upper
  lower := (Primitive.Addresses.material1239 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1239_pa_checked.trans (by decide +kernel)
    · exact v1239_pb_checked.trans (by decide +kernel)
    · exact v1239_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 70 Primitive.Addresses.material1239
    · exact v1239_mb_checked.trans (by decide +kernel)
    · exact v1239_mg_checked.trans (by decide +kernel)
  upper_error := v1239_upper_checked
  lower_error := reuse_lower_error 13 70 Primitive.Addresses.material1239

def v1240_pa : Scalar.QComplex := ((999999526686941258605728855992 : Int)/10^30,(-972947014722557729454824439 : Int)/10^30)
theorem v1240_pa_checked : Scalar.distance (sourceCoefficient 13 71 1 0) v1240_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1240_pb : Scalar.QComplex := ((-419804703009776537853599 : Int)/10^30,(-431477252058210498516491862 : Int)/10^30)
theorem v1240_pb_checked : Scalar.distance (sourceCoefficient 13 71 1 1) v1240_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1240_pg : Scalar.QComplex := ((-93086378856808668953589 : Int)/10^30,(90568157287156560733 : Int)/10^30)
theorem v1240_pg_checked : Scalar.distance (sourceCoefficient 13 71 1 2) v1240_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1240_mb : Scalar.QComplex := ((-792149982209489933468296 : Int)/10^30,(-431476729126958677177727899 : Int)/10^30)
theorem v1240_mb_checked : Scalar.distance (sourceCoefficient 13 71 3 1) v1240_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1240_mg : Scalar.QComplex := ((-93086266040254862452452 : Int)/10^30,(170897476063045844479 : Int)/10^30)
theorem v1240_mg_checked : Scalar.distance (sourceCoefficient 13 71 3 2) v1240_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1240_upper : Scalar.QComplex := ((999996358086832107054238428079 : Int)/10^30,(-2698854029445529136454382518 : Int)/10^30)
theorem v1240_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 71 5) 1) 14) v1240_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1240 : Material (13 : Basis) (71 : Basis) where
  plus := ![v1240_pa,v1240_pb,v1240_pg]
  minus := ![(Primitive.Addresses.material1240 1).one,v1240_mb,v1240_mg]
  upper := v1240_upper
  lower := (Primitive.Addresses.material1240 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1240_pa_checked.trans (by decide +kernel)
    · exact v1240_pb_checked.trans (by decide +kernel)
    · exact v1240_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 71 Primitive.Addresses.material1240
    · exact v1240_mb_checked.trans (by decide +kernel)
    · exact v1240_mg_checked.trans (by decide +kernel)
  upper_error := v1240_upper_checked
  lower_error := reuse_lower_error 13 71 Primitive.Addresses.material1240

def v1241_pa : Scalar.QComplex := ((999999500690008962078377047450 : Int)/10^30,(-999309628075991318083224636 : Int)/10^30)
theorem v1241_pa_checked : Scalar.distance (sourceCoefficient 13 72 1 0) v1241_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1241_pb : Scalar.QComplex := ((-431179572716037693236979 : Int)/10^30,(-431477237194176798905044074 : Int)/10^30)
theorem v1241_pb_checked : Scalar.distance (sourceCoefficient 13 72 1 1) v1241_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1241_pg : Scalar.QComplex := ((-93086376043453674782425 : Int)/10^30,(93022158269818572024 : Int)/10^30)
theorem v1241_pg_checked : Scalar.distance (sourceCoefficient 13 72 1 2) v1241_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1241_mb : Scalar.QComplex := ((-803524834853375608445558 : Int)/10^30,(-431476704446930260735879521 : Int)/10^30)
theorem v1241_mb_checked : Scalar.distance (sourceCoefficient 13 72 3 1) v1241_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1241_mg : Scalar.QComplex := ((-93086261109208591886024 : Int)/10^30,(173351473704172485375 : Int)/10^30)
theorem v1241_mg_checked : Scalar.distance (sourceCoefficient 13 72 3 2) v1241_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1241_upper : Scalar.QComplex := ((999996286590459479478642417534 : Int)/10^30,(-2725216558666600184712921729 : Int)/10^30)
theorem v1241_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 72 5) 1) 14) v1241_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1241 : Material (13 : Basis) (72 : Basis) where
  plus := ![v1241_pa,v1241_pb,v1241_pg]
  minus := ![(Primitive.Addresses.material1241 1).one,v1241_mb,v1241_mg]
  upper := v1241_upper
  lower := (Primitive.Addresses.material1241 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1241_pa_checked.trans (by decide +kernel)
    · exact v1241_pb_checked.trans (by decide +kernel)
    · exact v1241_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 72 Primitive.Addresses.material1241
    · exact v1241_mb_checked.trans (by decide +kernel)
    · exact v1241_mg_checked.trans (by decide +kernel)
  upper_error := v1241_upper_checked
  lower_error := reuse_lower_error 13 72 Primitive.Addresses.material1241

def v1242_pa : Scalar.QComplex := ((999999491202242249328882251235 : Int)/10^30,(-1008759265943160466286952725 : Int)/10^30)
theorem v1242_pa_checked : Scalar.distance (sourceCoefficient 13 73 1 0) v1242_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1242_pb : Scalar.QComplex := ((-435256877048046942541212 : Int)/10^30,(-431477231768841883031504007 : Int)/10^30)
theorem v1242_pb_checked : Scalar.distance (sourceCoefficient 13 73 1 1) v1242_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1242_pg : Scalar.QComplex := ((-93086375016634963767631 : Int)/10^30,(93901791108111202268 : Int)/10^30)
theorem v1242_pg_checked : Scalar.distance (sourceCoefficient 13 73 1 2) v1242_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1242_mb : Scalar.QComplex := ((-807602132985398428544414 : Int)/10^30,(-431476695503067361408759711 : Int)/10^30)
theorem v1242_mb_checked : Scalar.distance (sourceCoefficient 13 73 3 1) v1242_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1242_mg : Scalar.QComplex := ((-93086259323306740948601 : Int)/10^30,(174231105328839307308 : Int)/10^30)
theorem v1242_mg_checked : Scalar.distance (sourceCoefficient 13 73 3 2) v1242_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1242_upper : Scalar.QComplex := ((999996260793489203359932287536 : Int)/10^30,(-2734666166084619139474557052 : Int)/10^30)
theorem v1242_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 73 5) 1) 14) v1242_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1242 : Material (13 : Basis) (73 : Basis) where
  plus := ![v1242_pa,v1242_pb,v1242_pg]
  minus := ![(Primitive.Addresses.material1242 1).one,v1242_mb,v1242_mg]
  upper := v1242_upper
  lower := (Primitive.Addresses.material1242 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1242_pa_checked.trans (by decide +kernel)
    · exact v1242_pb_checked.trans (by decide +kernel)
    · exact v1242_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 73 Primitive.Addresses.material1242
    · exact v1242_mb_checked.trans (by decide +kernel)
    · exact v1242_mg_checked.trans (by decide +kernel)
  upper_error := v1242_upper_checked
  lower_error := reuse_lower_error 13 73 Primitive.Addresses.material1242

def v1243_pa : Scalar.QComplex := ((999999480419400608102547293482 : Int)/10^30,(-1019392431215670563441281334 : Int)/10^30)
theorem v1243_pa_checked : Scalar.distance (sourceCoefficient 13 74 1 0) v1243_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1243_pb : Scalar.QComplex := ((-439844846556055730888811 : Int)/10^30,(-431477225602580309425922345 : Int)/10^30)
theorem v1243_pb_checked : Scalar.distance (sourceCoefficient 13 74 1 1) v1243_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1243_pg : Scalar.QComplex := ((-93086373849615998328644 : Int)/10^30,(94891594255442292145 : Int)/10^30)
theorem v1243_pg_checked : Scalar.distance (sourceCoefficient 13 74 1 2) v1243_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1243_mb : Scalar.QComplex := ((-812190095463890468585672 : Int)/10^30,(-431476685377597032848598039 : Int)/10^30)
theorem v1243_mb_checked : Scalar.distance (sourceCoefficient 13 74 3 1) v1243_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1243_mg : Scalar.QComplex := ((-93086257302132672976283 : Int)/10^30,(175220907100536642604 : Int)/10^30)
theorem v1243_mg_checked : Scalar.distance (sourceCoefficient 13 74 3 2) v1243_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1243_upper : Scalar.QComplex := ((999996231658784994775373632621 : Int)/10^30,(-2745299296910072161555304731 : Int)/10^30)
theorem v1243_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 74 5) 1) 14) v1243_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1243 : Material (13 : Basis) (74 : Basis) where
  plus := ![v1243_pa,v1243_pb,v1243_pg]
  minus := ![(Primitive.Addresses.material1243 1).one,v1243_mb,v1243_mg]
  upper := v1243_upper
  lower := (Primitive.Addresses.material1243 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1243_pa_checked.trans (by decide +kernel)
    · exact v1243_pb_checked.trans (by decide +kernel)
    · exact v1243_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 74 Primitive.Addresses.material1243
    · exact v1243_mb_checked.trans (by decide +kernel)
    · exact v1243_mg_checked.trans (by decide +kernel)
  upper_error := v1243_upper_checked
  lower_error := reuse_lower_error 13 74 Primitive.Addresses.material1243

def v1244_pa : Scalar.QComplex := ((999999465207226332680057916207 : Int)/10^30,(-1034207552346882215216102148 : Int)/10^30)
theorem v1244_pa_checked : Scalar.distance (sourceCoefficient 13 75 1 0) v1244_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1244_pb : Scalar.QComplex := ((-446237235030852532328152 : Int)/10^30,(-431477216902717147948544772 : Int)/10^30)
theorem v1244_pb_checked : Scalar.distance (sourceCoefficient 13 75 1 1) v1244_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1244_pg : Scalar.QComplex := ((-93086372203143604450593 : Int)/10^30,(96270680637928322058 : Int)/10^30)
theorem v1244_pg_checked : Scalar.distance (sourceCoefficient 13 75 1 2) v1244_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1244_mb : Scalar.QComplex := ((-818582474050918813209034 : Int)/10^30,(-431476671161393759467701301 : Int)/10^30)
theorem v1244_mb_checked : Scalar.distance (sourceCoefficient 13 75 3 1) v1244_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1244_mg : Scalar.QComplex := ((-93086254465571455814679 : Int)/10^30,(176599991548694263403 : Int)/10^30)
theorem v1244_mg_checked : Scalar.distance (sourceCoefficient 13 75 3 2) v1244_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1244_upper : Scalar.QComplex := ((999996190877078320918345629720 : Int)/10^30,(-2760114369721068433059084696 : Int)/10^30)
theorem v1244_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 75 5) 1) 14) v1244_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1244 : Material (13 : Basis) (75 : Basis) where
  plus := ![v1244_pa,v1244_pb,v1244_pg]
  minus := ![(Primitive.Addresses.material1244 1).one,v1244_mb,v1244_mg]
  upper := v1244_upper
  lower := (Primitive.Addresses.material1244 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1244_pa_checked.trans (by decide +kernel)
    · exact v1244_pb_checked.trans (by decide +kernel)
    · exact v1244_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 75 Primitive.Addresses.material1244
    · exact v1244_mb_checked.trans (by decide +kernel)
    · exact v1244_mg_checked.trans (by decide +kernel)
  upper_error := v1244_upper_checked
  lower_error := reuse_lower_error 13 75 Primitive.Addresses.material1244

def v1245_pa : Scalar.QComplex := ((999999452274580453911083748038 : Int)/10^30,(-1046637730587352089447329700 : Int)/10^30)
theorem v1245_pa_checked : Scalar.distance (sourceCoefficient 13 76 1 0) v1245_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1245_pb : Scalar.QComplex := ((-451600574710578291813717 : Int)/10^30,(-431477209505943379907707980 : Int)/10^30)
theorem v1245_pb_checked : Scalar.distance (sourceCoefficient 13 76 1 1) v1245_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1245_pg : Scalar.QComplex := ((-93086370803331243196388 : Int)/10^30,(97427761249872769230 : Int)/10^30)
theorem v1245_pg_checked : Scalar.distance (sourceCoefficient 13 76 1 2) v1245_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1245_mb : Scalar.QComplex := ((-823945805350545469704918 : Int)/10^30,(-431476659136302157832657294 : Int)/10^30)
theorem v1245_mb_checked : Scalar.distance (sourceCoefficient 13 76 3 1) v1245_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1245_mg : Scalar.QComplex := ((-93086252067251160642769 : Int)/10^30,(177757070521829694998 : Int)/10^30)
theorem v1245_mg_checked : Scalar.distance (sourceCoefficient 13 76 3 2) v1245_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1245_upper : Scalar.QComplex := ((999996156491091717716432321027 : Int)/10^30,(-2772544507127674423130616021 : Int)/10^30)
theorem v1245_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 76 5) 1) 14) v1245_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1245 : Material (13 : Basis) (76 : Basis) where
  plus := ![v1245_pa,v1245_pb,v1245_pg]
  minus := ![(Primitive.Addresses.material1245 1).one,v1245_mb,v1245_mg]
  upper := v1245_upper
  lower := (Primitive.Addresses.material1245 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1245_pa_checked.trans (by decide +kernel)
    · exact v1245_pb_checked.trans (by decide +kernel)
    · exact v1245_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 76 Primitive.Addresses.material1245
    · exact v1245_mb_checked.trans (by decide +kernel)
    · exact v1245_mg_checked.trans (by decide +kernel)
  upper_error := v1245_upper_checked
  lower_error := reuse_lower_error 13 76 Primitive.Addresses.material1245

def v1246_pa : Scalar.QComplex := ((999999449258537373471468608110 : Int)/10^30,(-1049515422438802662293469984 : Int)/10^30)
theorem v1246_pa_checked : Scalar.distance (sourceCoefficient 13 77 1 0) v1246_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1246_pb : Scalar.QComplex := ((-452842233395834042878651 : Int)/10^30,(-431477207780855969070280312 : Int)/10^30)
theorem v1246_pb_checked : Scalar.distance (sourceCoefficient 13 77 1 1) v1246_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1246_pg : Scalar.QComplex := ((-93086370476870782092767 : Int)/10^30,(97695635239364971252 : Int)/10^30)
theorem v1246_pg_checked : Scalar.distance (sourceCoefficient 13 77 1 2) v1246_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1246_mb : Scalar.QComplex := ((-825187462084802205143989 : Int)/10^30,(-431476656339719866179653017 : Int)/10^30)
theorem v1246_mb_checked : Scalar.distance (sourceCoefficient 13 77 3 1) v1246_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1246_mg : Scalar.QComplex := ((-93086251509627632760156 : Int)/10^30,(178024944129859493587 : Int)/10^30)
theorem v1246_mg_checked : Scalar.distance (sourceCoefficient 13 77 3 2) v1246_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1246_upper : Scalar.QComplex := ((999996148508418055880465329002 : Int)/10^30,(-2775422189487724277123965826 : Int)/10^30)
theorem v1246_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 77 5) 1) 14) v1246_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1246 : Material (13 : Basis) (77 : Basis) where
  plus := ![v1246_pa,v1246_pb,v1246_pg]
  minus := ![(Primitive.Addresses.material1246 1).one,v1246_mb,v1246_mg]
  upper := v1246_upper
  lower := (Primitive.Addresses.material1246 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1246_pa_checked.trans (by decide +kernel)
    · exact v1246_pb_checked.trans (by decide +kernel)
    · exact v1246_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 77 Primitive.Addresses.material1246
    · exact v1246_mb_checked.trans (by decide +kernel)
    · exact v1246_mg_checked.trans (by decide +kernel)
  upper_error := v1246_upper_checked
  lower_error := reuse_lower_error 13 77 Primitive.Addresses.material1246

def v1247_pa : Scalar.QComplex := ((999999430952713839868181377142 : Int)/10^30,(-1066815002006181834249612928 : Int)/10^30)
theorem v1247_pa_checked : Scalar.distance (sourceCoefficient 13 78 1 0) v1247_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1247_pb : Scalar.QComplex := ((-460306609049993228219790 : Int)/10^30,(-431477197309884873771313328 : Int)/10^30)
theorem v1247_pb_checked : Scalar.distance (sourceCoefficient 13 78 1 1) v1247_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1247_pg : Scalar.QComplex := ((-93086368495361680016939 : Int)/10^30,(99305990902932074915 : Int)/10^30)
theorem v1247_pg_checked : Scalar.distance (sourceCoefficient 13 78 1 2) v1247_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1247_mb : Scalar.QComplex := ((-832651825923656735410361 : Int)/10^30,(-431476639427332663162158647 : Int)/10^30)
theorem v1247_mb_checked : Scalar.distance (sourceCoefficient 13 78 3 1) v1247_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1247_mg : Scalar.QComplex := ((-93086248138454858559047 : Int)/10^30,(179635297483864475580 : Int)/10^30)
theorem v1247_mg_checked : Scalar.distance (sourceCoefficient 13 78 3 2) v1247_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1247_upper : Scalar.QComplex := ((999996100345116858953356400874 : Int)/10^30,(-2792721711695221107174750086 : Int)/10^30)
theorem v1247_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 78 5) 1) 14) v1247_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1247 : Material (13 : Basis) (78 : Basis) where
  plus := ![v1247_pa,v1247_pb,v1247_pg]
  minus := ![(Primitive.Addresses.material1247 1).one,v1247_mb,v1247_mg]
  upper := v1247_upper
  lower := (Primitive.Addresses.material1247 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1247_pa_checked.trans (by decide +kernel)
    · exact v1247_pb_checked.trans (by decide +kernel)
    · exact v1247_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 78 Primitive.Addresses.material1247
    · exact v1247_mb_checked.trans (by decide +kernel)
    · exact v1247_mg_checked.trans (by decide +kernel)
  upper_error := v1247_upper_checked
  lower_error := reuse_lower_error 13 78 Primitive.Addresses.material1247

def v1248_pa : Scalar.QComplex := ((999999424987448179334682112954 : Int)/10^30,(-1072392079885848413039260904 : Int)/10^30)
theorem v1248_pa_checked : Scalar.distance (sourceCoefficient 13 79 1 0) v1248_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1248_pb : Scalar.QComplex := ((-462712991452858931033363 : Int)/10^30,(-431477193897529308097853625 : Int)/10^30)
theorem v1248_pb_checked : Scalar.distance (sourceCoefficient 13 79 1 1) v1248_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1248_pg : Scalar.QComplex := ((-93086367849630338507067 : Int)/10^30,(99825141027993327692 : Int)/10^30)
theorem v1248_pg_checked : Scalar.distance (sourceCoefficient 13 79 1 2) v1248_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1248_mb : Scalar.QComplex := ((-835058204485807126141603 : Int)/10^30,(-431476633938378733831718008 : Int)/10^30)
theorem v1248_mb_checked : Scalar.distance (sourceCoefficient 13 79 3 1) v1248_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1248_mg : Scalar.QComplex := ((-93086247044720581210268 : Int)/10^30,(180154446858385345401 : Int)/10^30)
theorem v1248_mg_checked : Scalar.distance (sourceCoefficient 13 79 3 2) v1248_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1248_upper : Scalar.QComplex := ((999996084754329611230804331731 : Int)/10^30,(-2798298770972977948381675566 : Int)/10^30)
theorem v1248_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 79 5) 1) 14) v1248_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1248 : Material (13 : Basis) (79 : Basis) where
  plus := ![v1248_pa,v1248_pb,v1248_pg]
  minus := ![(Primitive.Addresses.material1248 1).one,v1248_mb,v1248_mg]
  upper := v1248_upper
  lower := (Primitive.Addresses.material1248 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1248_pa_checked.trans (by decide +kernel)
    · exact v1248_pb_checked.trans (by decide +kernel)
    · exact v1248_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 79 Primitive.Addresses.material1248
    · exact v1248_mb_checked.trans (by decide +kernel)
    · exact v1248_mg_checked.trans (by decide +kernel)
  upper_error := v1248_upper_checked
  lower_error := reuse_lower_error 13 79 Primitive.Addresses.material1248

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
