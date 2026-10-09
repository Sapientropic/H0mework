import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B120
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B121

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2897_pa : Scalar.QComplex := ((999999053711065358884958679996 : Int)/10^30,(-1375709625545842525862086938 : Int)/10^30)
theorem v2897_pa_checked : Scalar.distance (sourceCoefficient 36 72 1 0) v2897_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2897_pb : Scalar.QComplex := ((-593587743395282136268845 : Int)/10^30,(-431477086928319106398032252 : Int)/10^30)
theorem v2897_pb_checked : Scalar.distance (sourceCoefficient 36 72 1 1) v2897_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2897_pg : Scalar.QComplex := ((-93086339030530986210732 : Int)/10^30,(128059893792785596440 : Int)/10^30)
theorem v2897_pg_checked : Scalar.distance (sourceCoefficient 36 72 1 2) v2897_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2897_mb : Scalar.QComplex := ((-965932815387968221886917 : Int)/10^30,(-431476414030191815364178266 : Int)/10^30)
theorem v2897_mb_checked : Scalar.distance (sourceCoefficient 36 72 3 1) v2897_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2897_mg : Scalar.QComplex := ((-93086193860311969624798 : Int)/10^30,(208389164240503990889 : Int)/10^30)
theorem v2897_mg_checked : Scalar.distance (sourceCoefficient 36 72 3 2) v2897_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2897_upper : Scalar.QComplex := ((999995189979932706983463545995 : Int)/10^30,(-3101615224087763164684701420 : Int)/10^30)
theorem v2897_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 72 5) 1) 14) v2897_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2897 : Material (36 : Basis) (72 : Basis) where
  plus := ![v2897_pa,v2897_pb,v2897_pg]
  minus := ![(Primitive.Addresses.material2897 1).one,v2897_mb,v2897_mg]
  upper := v2897_upper
  lower := (Primitive.Addresses.material2897 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2897_pa_checked.trans (by decide +kernel)
    · exact v2897_pb_checked.trans (by decide +kernel)
    · exact v2897_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 72 Primitive.Addresses.material2897
    · exact v2897_mb_checked.trans (by decide +kernel)
    · exact v2897_mg_checked.trans (by decide +kernel)
  upper_error := v2897_upper_checked
  lower_error := reuse_lower_error 36 72 Primitive.Addresses.material2897

def v2898_pa : Scalar.QComplex := ((999999040666453204036312389054 : Int)/10^30,(-1385159259172414934587935049 : Int)/10^30)
theorem v2898_pa_checked : Scalar.distance (sourceCoefficient 36 73 1 0) v2898_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2898_pb : Scalar.QComplex := ((-597665046507476689957946 : Int)/10^30,(-431477080479851692893759784 : Int)/10^30)
theorem v2898_pb_checked : Scalar.distance (sourceCoefficient 36 73 1 1) v2898_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2898_pg : Scalar.QComplex := ((-93086337727800582684770 : Int)/10^30,(128939526302126563252 : Int)/10^30)
theorem v2898_pg_checked : Scalar.distance (sourceCoefficient 36 73 1 2) v2898_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2898_mb : Scalar.QComplex := ((-970010111417259535285195 : Int)/10^30,(-431476404063197852010458289 : Int)/10^30)
theorem v2898_mb_checked : Scalar.distance (sourceCoefficient 36 73 3 1) v2898_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2898_mg : Scalar.QComplex := ((-93086191798498812781211 : Int)/10^30,(209268795298119907838 : Int)/10^30)
theorem v2898_mg_checked : Scalar.distance (sourceCoefficient 36 73 3 2) v2898_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2898_upper : Scalar.QComplex := ((999995160626129605154339920082 : Int)/10^30,(-3111064821126399137273941636 : Int)/10^30)
theorem v2898_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 73 5) 1) 14) v2898_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2898 : Material (36 : Basis) (73 : Basis) where
  plus := ![v2898_pa,v2898_pb,v2898_pg]
  minus := ![(Primitive.Addresses.material2898 1).one,v2898_mb,v2898_mg]
  upper := v2898_upper
  lower := (Primitive.Addresses.material2898 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2898_pa_checked.trans (by decide +kernel)
    · exact v2898_pb_checked.trans (by decide +kernel)
    · exact v2898_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 73 Primitive.Addresses.material2898
    · exact v2898_mb_checked.trans (by decide +kernel)
    · exact v2898_mg_checked.trans (by decide +kernel)
  upper_error := v2898_upper_checked
  lower_error := reuse_lower_error 36 73 Primitive.Addresses.material2898

def v2899_pa : Scalar.QComplex := ((999999025881286193862117488111 : Int)/10^30,(-1395792419633022357853449120 : Int)/10^30)
theorem v2899_pa_checked : Scalar.distance (sourceCoefficient 36 74 1 0) v2899_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2899_pb : Scalar.QComplex := ((-602253014631333683940787 : Int)/10^30,(-431477073162314582813309979 : Int)/10^30)
theorem v2899_pb_checked : Scalar.distance (sourceCoefficient 36 74 1 1) v2899_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2899_pg : Scalar.QComplex := ((-93086336250313146393422 : Int)/10^30,(129929329076188633560 : Int)/10^30)
theorem v2899_pg_checked : Scalar.distance (sourceCoefficient 36 74 1 2) v2899_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2899_mb : Scalar.QComplex := ((-974598071518101359892200 : Int)/10^30,(-431476392786453610108585249 : Int)/10^30)
theorem v2899_mb_checked : Scalar.distance (sourceCoefficient 36 74 3 1) v2899_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2899_mg : Scalar.QComplex := ((-93086189466856711672484 : Int)/10^30,(210258596428628055186 : Int)/10^30)
theorem v2899_mg_checked : Scalar.distance (sourceCoefficient 36 74 3 2) v2899_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2899_upper : Scalar.QComplex := ((999995127489114293522894937533 : Int)/10^30,(-3121697940232306153546837676 : Int)/10^30)
theorem v2899_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 74 5) 1) 14) v2899_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2899 : Material (36 : Basis) (74 : Basis) where
  plus := ![v2899_pa,v2899_pb,v2899_pg]
  minus := ![(Primitive.Addresses.material2899 1).one,v2899_mb,v2899_mg]
  upper := v2899_upper
  lower := (Primitive.Addresses.material2899 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2899_pa_checked.trans (by decide +kernel)
    · exact v2899_pb_checked.trans (by decide +kernel)
    · exact v2899_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 74 Primitive.Addresses.material2899
    · exact v2899_mb_checked.trans (by decide +kernel)
    · exact v2899_mg_checked.trans (by decide +kernel)
  upper_error := v2899_upper_checked
  lower_error := reuse_lower_error 36 74 Primitive.Addresses.material2899

def v2900_pa : Scalar.QComplex := ((999999005092697606627318600376 : Int)/10^30,(-1410607533988885587201611341 : Int)/10^30)
theorem v2900_pa_checked : Scalar.distance (sourceCoefficient 36 75 1 0) v2900_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2900_pb : Scalar.QComplex := ((-608645401157190265119051 : Int)/10^30,(-431477062858386590664826162 : Int)/10^30)
theorem v2900_pb_checked : Scalar.distance (sourceCoefficient 36 75 1 1) v2900_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2900_pg : Scalar.QComplex := ((-93086334171267020373756 : Int)/10^30,(131308414933097187958 : Int)/10^30)
theorem v2900_pg_checked : Scalar.distance (sourceCoefficient 36 75 1 2) v2900_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2900_mb : Scalar.QComplex := ((-980990446771954505462972 : Int)/10^30,(-431476376966187785170861187 : Int)/10^30)
theorem v2900_mb_checked : Scalar.distance (sourceCoefficient 36 75 3 1) v2900_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2900_mg : Scalar.QComplex := ((-93086186197722376985925 : Int)/10^30,(211637679977916747727 : Int)/10^30)
theorem v2900_mg_checked : Scalar.distance (sourceCoefficient 36 75 3 2) v2900_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2900_upper : Scalar.QComplex := ((999995081131013306904345529624 : Int)/10^30,(-3136512996643578879876084358 : Int)/10^30)
theorem v2900_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 75 5) 1) 14) v2900_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2900 : Material (36 : Basis) (75 : Basis) where
  plus := ![v2900_pa,v2900_pb,v2900_pg]
  minus := ![(Primitive.Addresses.material2900 1).one,v2900_mb,v2900_mg]
  upper := v2900_upper
  lower := (Primitive.Addresses.material2900 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2900_pa_checked.trans (by decide +kernel)
    · exact v2900_pb_checked.trans (by decide +kernel)
    · exact v2900_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 75 Primitive.Addresses.material2900
    · exact v2900_mb_checked.trans (by decide +kernel)
    · exact v2900_mg_checked.trans (by decide +kernel)
  upper_error := v2900_upper_checked
  lower_error := reuse_lower_error 36 75 Primitive.Addresses.material2900

def v2901_pa : Scalar.QComplex := ((999998987481330369664898278827 : Int)/10^30,(-1423037706480968076761325563 : Int)/10^30)
theorem v2901_pa_checked : Scalar.distance (sourceCoefficient 36 76 1 0) v2901_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2901_pb : Scalar.QComplex := ((-614008739183382855211945 : Int)/10^30,(-431477054115770862763789700 : Int)/10^30)
theorem v2901_pb_checked : Scalar.distance (sourceCoefficient 36 76 1 1) v2901_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2901_pg : Scalar.QComplex := ((-93086332408516784765191 : Int)/10^30,(132465495099127604218 : Int)/10^30)
theorem v2901_pg_checked : Scalar.distance (sourceCoefficient 36 76 1 2) v2901_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2901_mb : Scalar.QComplex := ((-986353775256647611364558 : Int)/10^30,(-431476363595256151718739998 : Int)/10^30)
theorem v2901_mb_checked : Scalar.distance (sourceCoefficient 36 76 3 1) v2901_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2901_mg : Scalar.QComplex := ((-93086183436464727401739 : Int)/10^30,(212794758191939274991 : Int)/10^30)
theorem v2901_mg_checked : Scalar.distance (sourceCoefficient 36 76 3 2) v2901_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2901_upper : Scalar.QComplex := ((999995042066322235109984191725 : Int)/10^30,(-3148943120226757432867962375 : Int)/10^30)
theorem v2901_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 76 5) 1) 14) v2901_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2901 : Material (36 : Basis) (76 : Basis) where
  plus := ![v2901_pa,v2901_pb,v2901_pg]
  minus := ![(Primitive.Addresses.material2901 1).one,v2901_mb,v2901_mg]
  upper := v2901_upper
  lower := (Primitive.Addresses.material2901 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2901_pa_checked.trans (by decide +kernel)
    · exact v2901_pb_checked.trans (by decide +kernel)
    · exact v2901_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 76 Primitive.Addresses.material2901
    · exact v2901_mb_checked.trans (by decide +kernel)
    · exact v2901_mg_checked.trans (by decide +kernel)
  upper_error := v2901_upper_checked
  lower_error := reuse_lower_error 36 76 Primitive.Addresses.material2901

def v2902_pa : Scalar.QComplex := ((999998983382123552727031718551 : Int)/10^30,(-1425915396993327660028096297 : Int)/10^30)
theorem v2902_pa_checked : Scalar.distance (sourceCoefficient 36 77 1 0) v2902_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2902_pb : Scalar.QComplex := ((-615250397483446861683193 : Int)/10^30,(-431477052079109606740837117 : Int)/10^30)
theorem v2902_pb_checked : Scalar.distance (sourceCoefficient 36 77 1 1) v2902_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2902_pg : Scalar.QComplex := ((-93086331998033122939449 : Int)/10^30,(132733368984743811024 : Int)/10^30)
theorem v2902_pg_checked : Scalar.distance (sourceCoefficient 36 77 1 2) v2902_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2902_mb : Scalar.QComplex := ((-987595431336838550004392 : Int)/10^30,(-431476360487100463296520189 : Int)/10^30)
theorem v2902_mb_checked : Scalar.distance (sourceCoefficient 36 77 3 1) v2902_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2902_mg : Scalar.QComplex := ((-93086182794818119722988 : Int)/10^30,(213062631623584879082 : Int)/10^30)
theorem v2902_mg_checked : Scalar.distance (sourceCoefficient 36 77 3 2) v2902_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2902_upper : Scalar.QComplex := ((999995033000488761170480571449 : Int)/10^30,(-3151820799378275946351269056 : Int)/10^30)
theorem v2902_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 77 5) 1) 14) v2902_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2902 : Material (36 : Basis) (77 : Basis) where
  plus := ![v2902_pa,v2902_pb,v2902_pg]
  minus := ![(Primitive.Addresses.material2902 1).one,v2902_mb,v2902_mg]
  upper := v2902_upper
  lower := (Primitive.Addresses.material2902 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2902_pa_checked.trans (by decide +kernel)
    · exact v2902_pb_checked.trans (by decide +kernel)
    · exact v2902_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 77 Primitive.Addresses.material2902
    · exact v2902_mb_checked.trans (by decide +kernel)
    · exact v2902_mg_checked.trans (by decide +kernel)
  upper_error := v2902_upper_checked
  lower_error := reuse_lower_error 36 77 Primitive.Addresses.material2902

def v2903_pa : Scalar.QComplex := ((999998958564735134569610865821 : Int)/10^30,(-1443214968444912531125184121 : Int)/10^30)
theorem v2903_pa_checked : Scalar.distance (sourceCoefficient 36 78 1 0) v2903_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2903_pb : Scalar.QComplex := ((-622714770803084356909458 : Int)/10^30,(-431477039735076076423140637 : Int)/10^30)
theorem v2903_pb_checked : Scalar.distance (sourceCoefficient 36 78 1 1) v2903_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2903_pg : Scalar.QComplex := ((-93086329511408769755613 : Int)/10^30,(134343724018752344231 : Int)/10^30)
theorem v2903_pg_checked : Scalar.distance (sourceCoefficient 36 78 1 2) v2903_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2903_mb : Scalar.QComplex := ((-995059791224803737584343 : Int)/10^30,(-431476341701653537274119679 : Int)/10^30)
theorem v2903_mb_checked : Scalar.distance (sourceCoefficient 36 78 3 1) v2903_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2903_mg : Scalar.QComplex := ((-93086178918530825772055 : Int)/10^30,(214672983912139812873 : Int)/10^30)
theorem v2903_mg_checked : Scalar.distance (sourceCoefficient 36 78 3 2) v2903_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2903_upper : Scalar.QComplex := ((999994978325646385024935597252 : Int)/10^30,(-3169120302231620296876666314 : Int)/10^30)
theorem v2903_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 78 5) 1) 14) v2903_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2903 : Material (36 : Basis) (78 : Basis) where
  plus := ![v2903_pa,v2903_pb,v2903_pg]
  minus := ![(Primitive.Addresses.material2903 1).one,v2903_mb,v2903_mg]
  upper := v2903_upper
  lower := (Primitive.Addresses.material2903 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2903_pa_checked.trans (by decide +kernel)
    · exact v2903_pb_checked.trans (by decide +kernel)
    · exact v2903_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 78 Primitive.Addresses.material2903
    · exact v2903_mb_checked.trans (by decide +kernel)
    · exact v2903_mg_checked.trans (by decide +kernel)
  upper_error := v2903_upper_checked
  lower_error := reuse_lower_error 36 78 Primitive.Addresses.material2903

def v2904_pa : Scalar.QComplex := ((999998950500256353853570551494 : Int)/10^30,(-1448792043684179315340786025 : Int)/10^30)
theorem v2904_pa_checked : Scalar.distance (sourceCoefficient 36 79 1 0) v2904_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2904_pb : Scalar.QComplex := ((-625121152446434681366946 : Int)/10^30,(-431477035718878377472364569 : Int)/10^30)
theorem v2904_pb_checked : Scalar.distance (sourceCoefficient 36 79 1 1) v2904_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2904_pg : Scalar.QComplex := ((-93086328702837223181100 : Int)/10^30,(134862873938992447464 : Int)/10^30)
theorem v2904_pg_checked : Scalar.distance (sourceCoefficient 36 79 1 2) v2904_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2904_mb : Scalar.QComplex := ((-997466168506350467783581 : Int)/10^30,(-431476335608858354931950061 : Int)/10^30)
theorem v2904_mb_checked : Scalar.distance (sourceCoefficient 36 79 3 1) v2904_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2904_mg : Scalar.QComplex := ((-93086177661956580742914 : Int)/10^30,(215192132941315846493 : Int)/10^30)
theorem v2904_mg_checked : Scalar.distance (sourceCoefficient 36 79 3 2) v2904_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2904_upper : Scalar.QComplex := ((999994960635653700741704331289 : Int)/10^30,(-3174697355245929869766444882 : Int)/10^30)
theorem v2904_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 79 5) 1) 14) v2904_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2904 : Material (36 : Basis) (79 : Basis) where
  plus := ![v2904_pa,v2904_pb,v2904_pg]
  minus := ![(Primitive.Addresses.material2904 1).one,v2904_mb,v2904_mg]
  upper := v2904_upper
  lower := (Primitive.Addresses.material2904 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2904_pa_checked.trans (by decide +kernel)
    · exact v2904_pb_checked.trans (by decide +kernel)
    · exact v2904_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 79 Primitive.Addresses.material2904
    · exact v2904_mb_checked.trans (by decide +kernel)
    · exact v2904_mg_checked.trans (by decide +kernel)
  upper_error := v2904_upper_checked
  lower_error := reuse_lower_error 36 79 Primitive.Addresses.material2904

def v2905_pa : Scalar.QComplex := ((999998937840500774228715690802 : Int)/10^30,(-1457503986364613952055505171 : Int)/10^30)
theorem v2905_pa_checked : Scalar.distance (sourceCoefficient 36 80 1 0) v2905_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2905_pb : Scalar.QComplex := ((-628880158359955883377468 : Int)/10^30,(-431477029409372237441595490 : Int)/10^30)
theorem v2905_pb_checked : Scalar.distance (sourceCoefficient 36 80 1 1) v2905_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2905_pg : Scalar.QComplex := ((-93086327433008948814534 : Int)/10^30,(135673837416907473380 : Int)/10^30)
theorem v2905_pg_checked : Scalar.distance (sourceCoefficient 36 80 1 2) v2905_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2905_mb : Scalar.QComplex := ((-1001225167575402343894185 : Int)/10^30,(-431476326055501760191536274 : Int)/10^30)
theorem v2905_mb_checked : Scalar.distance (sourceCoefficient 36 80 3 1) v2905_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2905_mg : Scalar.QComplex := ((-93086175692303822189975 : Int)/10^30,(216003095021467496884 : Int)/10^30)
theorem v2905_mg_checked : Scalar.distance (sourceCoefficient 36 80 3 2) v2905_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2905_upper : Scalar.QComplex := ((999994932939894251171644864984 : Int)/10^30,(-3183409263101359614271526038 : Int)/10^30)
theorem v2905_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 80 5) 1) 14) v2905_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2905 : Material (36 : Basis) (80 : Basis) where
  plus := ![v2905_pa,v2905_pb,v2905_pg]
  minus := ![(Primitive.Addresses.material2905 1).one,v2905_mb,v2905_mg]
  upper := v2905_upper
  lower := (Primitive.Addresses.material2905 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2905_pa_checked.trans (by decide +kernel)
    · exact v2905_pb_checked.trans (by decide +kernel)
    · exact v2905_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 80 Primitive.Addresses.material2905
    · exact v2905_mb_checked.trans (by decide +kernel)
    · exact v2905_mg_checked.trans (by decide +kernel)
  upper_error := v2905_upper_checked
  lower_error := reuse_lower_error 36 80 Primitive.Addresses.material2905

def v2906_pa : Scalar.QComplex := ((999998899262990778279618408871 : Int)/10^30,(-1483736097431574013130672289 : Int)/10^30)
theorem v2906_pa_checked : Scalar.distance (sourceCoefficient 36 81 1 0) v2906_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2906_pb : Scalar.QComplex := ((-640198719858036132280489 : Int)/10^30,(-431477010147443803363120595 : Int)/10^30)
theorem v2906_pb_checked : Scalar.distance (sourceCoefficient 36 81 1 1) v2906_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2906_pg : Scalar.QComplex := ((-93086323559715227682818 : Int)/10^30,(138115690471796713098 : Int)/10^30)
theorem v2906_pg_checked : Scalar.distance (sourceCoefficient 36 81 1 2) v2906_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2906_mb : Scalar.QComplex := ((-1012543708236888149690032 : Int)/10^30,(-431476297026171694452431742 : Int)/10^30)
theorem v2906_mb_checked : Scalar.distance (sourceCoefficient 36 81 3 1) v2906_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2906_mg : Scalar.QComplex := ((-93086169711802333872171 : Int)/10^30,(218444943824665211406 : Int)/10^30)
theorem v2906_mg_checked : Scalar.distance (sourceCoefficient 36 81 3 2) v2906_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2906_upper : Scalar.QComplex := ((999994849088197768845329658776 : Int)/10^30,(-3209641268517389152695321236 : Int)/10^30)
theorem v2906_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 81 5) 1) 14) v2906_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2906 : Material (36 : Basis) (81 : Basis) where
  plus := ![v2906_pa,v2906_pb,v2906_pg]
  minus := ![(Primitive.Addresses.material2906 1).one,v2906_mb,v2906_mg]
  upper := v2906_upper
  lower := (Primitive.Addresses.material2906 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2906_pa_checked.trans (by decide +kernel)
    · exact v2906_pb_checked.trans (by decide +kernel)
    · exact v2906_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 81 Primitive.Addresses.material2906
    · exact v2906_mb_checked.trans (by decide +kernel)
    · exact v2906_mg_checked.trans (by decide +kernel)
  upper_error := v2906_upper_checked
  lower_error := reuse_lower_error 36 81 Primitive.Addresses.material2906

def v2907_pa : Scalar.QComplex := ((999998884464865505477223450869 : Int)/10^30,(-1493676345320635136081784490 : Int)/10^30)
theorem v2907_pa_checked : Scalar.distance (sourceCoefficient 36 82 1 0) v2907_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2907_pb : Scalar.QComplex := ((-644487711498752027770529 : Int)/10^30,(-431477002745008600542366030 : Int)/10^30)
theorem v2907_pb_checked : Scalar.distance (sourceCoefficient 36 82 1 1) v2907_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2907_pg : Scalar.QComplex := ((-93086322072466766610270 : Int)/10^30,(139040992457653952130 : Int)/10^30)
theorem v2907_pg_checked : Scalar.distance (sourceCoefficient 36 82 1 2) v2907_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2907_mb : Scalar.QComplex := ((-1016832691892648254011229 : Int)/10^30,(-431476285922532630971520407 : Int)/10^30)
theorem v2907_mb_checked : Scalar.distance (sourceCoefficient 36 82 3 1) v2907_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2907_mg : Scalar.QComplex := ((-93086167426060486829829 : Int)/10^30,(219370244182561793992 : Int)/10^30)
theorem v2907_mg_checked : Scalar.distance (sourceCoefficient 36 82 3 2) v2907_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2907_upper : Scalar.QComplex := ((999994817134128451836957852816 : Int)/10^30,(-3219581476061396963011802282 : Int)/10^30)
theorem v2907_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 82 5) 1) 14) v2907_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2907 : Material (36 : Basis) (82 : Basis) where
  plus := ![v2907_pa,v2907_pb,v2907_pg]
  minus := ![(Primitive.Addresses.material2907 1).one,v2907_mb,v2907_mg]
  upper := v2907_upper
  lower := (Primitive.Addresses.material2907 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2907_pa_checked.trans (by decide +kernel)
    · exact v2907_pb_checked.trans (by decide +kernel)
    · exact v2907_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 82 Primitive.Addresses.material2907
    · exact v2907_mb_checked.trans (by decide +kernel)
    · exact v2907_mg_checked.trans (by decide +kernel)
  upper_error := v2907_upper_checked
  lower_error := reuse_lower_error 36 82 Primitive.Addresses.material2907

def v2908_pa : Scalar.QComplex := ((999998864105683917741204427051 : Int)/10^30,(-1507244950865193737227278336 : Int)/10^30)
theorem v2908_pa_checked : Scalar.distance (sourceCoefficient 36 83 1 0) v2908_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2908_pb : Scalar.QComplex := ((-650342257153757087940781 : Int)/10^30,(-431476992548804019658854679 : Int)/10^30)
theorem v2908_pb_checked : Scalar.distance (sourceCoefficient 36 83 1 1) v2908_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2908_pg : Scalar.QComplex := ((-93086320025026680323447 : Int)/10^30,(140304045222910530692 : Int)/10^30)
theorem v2908_pg_checked : Scalar.distance (sourceCoefficient 36 83 1 2) v2908_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2908_mb : Scalar.QComplex := ((-1022687226568873067573441 : Int)/10^30,(-431476270674122625279675938 : Int)/10^30)
theorem v2908_mb_checked : Scalar.distance (sourceCoefficient 36 83 3 1) v2908_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2908_mg : Scalar.QComplex := ((-93086164288663512266942 : Int)/10^30,(220633294710677522499 : Int)/10^30)
theorem v2908_mg_checked : Scalar.distance (sourceCoefficient 36 83 3 2) v2908_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2908_upper : Scalar.QComplex := ((999994773356794951081682167563 : Int)/10^30,(-3233150026259011036002041574 : Int)/10^30)
theorem v2908_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 83 5) 1) 14) v2908_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2908 : Material (36 : Basis) (83 : Basis) where
  plus := ![v2908_pa,v2908_pb,v2908_pg]
  minus := ![(Primitive.Addresses.material2908 1).one,v2908_mb,v2908_mg]
  upper := v2908_upper
  lower := (Primitive.Addresses.material2908 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2908_pa_checked.trans (by decide +kernel)
    · exact v2908_pb_checked.trans (by decide +kernel)
    · exact v2908_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 83 Primitive.Addresses.material2908
    · exact v2908_mb_checked.trans (by decide +kernel)
    · exact v2908_mg_checked.trans (by decide +kernel)
  upper_error := v2908_upper_checked
  lower_error := reuse_lower_error 36 83 Primitive.Addresses.material2908

def v2909_pa : Scalar.QComplex := ((999998810525141437494755933124 : Int)/10^30,(-1542383967199663073521183730 : Int)/10^30)
theorem v2909_pa_checked : Scalar.distance (sourceCoefficient 36 84 1 0) v2909_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2909_pb : Scalar.QComplex := ((-665503945636374828193053 : Int)/10^30,(-431476965651065538119302289 : Int)/10^30)
theorem v2909_pb_checked : Scalar.distance (sourceCoefficient 36 84 1 1) v2909_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2909_pg : Scalar.QComplex := ((-93086314629773455625087 : Int)/10^30,(143575010029530766466 : Int)/10^30)
theorem v2909_pg_checked : Scalar.distance (sourceCoefficient 36 84 1 2) v2909_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2909_mb : Scalar.QComplex := ((-1037848886194564381954573 : Int)/10^30,(-431476230692539855598747767 : Int)/10^30)
theorem v2909_mb_checked : Scalar.distance (sourceCoefficient 36 84 3 1) v2909_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2909_mg : Scalar.QComplex := ((-93086156070716987140830 : Int)/10^30,(223904253643507530562 : Int)/10^30)
theorem v2909_mg_checked : Scalar.distance (sourceCoefficient 36 84 3 2) v2909_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2909_upper : Scalar.QComplex := ((999994659129577866125411136827 : Int)/10^30,(-3268288897782887728856988597 : Int)/10^30)
theorem v2909_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 84 5) 1) 14) v2909_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2909 : Material (36 : Basis) (84 : Basis) where
  plus := ![v2909_pa,v2909_pb,v2909_pg]
  minus := ![(Primitive.Addresses.material2909 1).one,v2909_mb,v2909_mg]
  upper := v2909_upper
  lower := (Primitive.Addresses.material2909 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2909_pa_checked.trans (by decide +kernel)
    · exact v2909_pb_checked.trans (by decide +kernel)
    · exact v2909_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 84 Primitive.Addresses.material2909
    · exact v2909_mb_checked.trans (by decide +kernel)
    · exact v2909_mg_checked.trans (by decide +kernel)
  upper_error := v2909_upper_checked
  lower_error := reuse_lower_error 36 84 Primitive.Addresses.material2909

def v2910_pa : Scalar.QComplex := ((999998685464187364803476531741 : Int)/10^30,(-1621440685707001231118166877 : Int)/10^30)
theorem v2910_pa_checked : Scalar.distance (sourceCoefficient 36 85 1 0) v2910_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2910_pb : Scalar.QComplex := ((-699615124388526951207670 : Int)/10^30,(-431476902538890085866599095 : Int)/10^30)
theorem v2910_pb_checked : Scalar.distance (sourceCoefficient 36 85 1 1) v2910_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2910_pg : Scalar.QComplex := ((-93086302001163007246318 : Int)/10^30,(150934115754995255749 : Int)/10^30)
theorem v2910_pg_checked : Scalar.distance (sourceCoefficient 36 85 1 2) v2910_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2910_mb : Scalar.QComplex := ((-1071959997782600749230856 : Int)/10^30,(-431476138143976950246524090 : Int)/10^30)
theorem v2910_mb_checked : Scalar.distance (sourceCoefficient 36 85 3 1) v2910_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2910_mg : Scalar.QComplex := ((-93086137091534441713208 : Int)/10^30,(231263345730918585057 : Int)/10^30)
theorem v2910_mg_checked : Scalar.distance (sourceCoefficient 36 85 3 2) v2910_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2910_upper : Scalar.QComplex := ((999994397624085882847506043348 : Int)/10^30,(-3347345282700669035944160726 : Int)/10^30)
theorem v2910_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 85 5) 1) 14) v2910_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2910 : Material (36 : Basis) (85 : Basis) where
  plus := ![v2910_pa,v2910_pb,v2910_pg]
  minus := ![(Primitive.Addresses.material2910 1).one,v2910_mb,v2910_mg]
  upper := v2910_upper
  lower := (Primitive.Addresses.material2910 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2910_pa_checked.trans (by decide +kernel)
    · exact v2910_pb_checked.trans (by decide +kernel)
    · exact v2910_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 85 Primitive.Addresses.material2910
    · exact v2910_mb_checked.trans (by decide +kernel)
    · exact v2910_mg_checked.trans (by decide +kernel)
  upper_error := v2910_upper_checked
  lower_error := reuse_lower_error 36 85 Primitive.Addresses.material2910

def v2911_pa : Scalar.QComplex := ((999998661709696252409270142818 : Int)/10^30,(-1636025310462599278088707707 : Int)/10^30)
theorem v2911_pa_checked : Scalar.distance (sourceCoefficient 36 86 1 0) v2911_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2911_pb : Scalar.QComplex := ((-705908058452369379077061 : Int)/10^30,(-431476890502909467167721378 : Int)/10^30)
theorem v2911_pb_checked : Scalar.distance (sourceCoefficient 36 86 1 1) v2911_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2911_pg : Scalar.QComplex := ((-93086299597238788075008 : Int)/10^30,(152291746008954142972 : Int)/10^30)
theorem v2911_pg_checked : Scalar.distance (sourceCoefficient 36 86 1 2) v2911_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2911_mb : Scalar.QComplex := ((-1078252919116787030344164 : Int)/10^30,(-431476120677482139226357600 : Int)/10^30)
theorem v2911_mb_checked : Scalar.distance (sourceCoefficient 36 86 3 1) v2911_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2911_mg : Scalar.QComplex := ((-93086133516037353863044 : Int)/10^30,(232620973404891349547 : Int)/10^30)
theorem v2911_mg_checked : Scalar.distance (sourceCoefficient 36 86 3 2) v2911_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2911_upper : Scalar.QComplex := ((999994348697890928637468510696 : Int)/10^30,(-3361929844736085070430526222 : Int)/10^30)
theorem v2911_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 86 5) 1) 14) v2911_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2911 : Material (36 : Basis) (86 : Basis) where
  plus := ![v2911_pa,v2911_pb,v2911_pg]
  minus := ![(Primitive.Addresses.material2911 1).one,v2911_mb,v2911_mg]
  upper := v2911_upper
  lower := (Primitive.Addresses.material2911 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2911_pa_checked.trans (by decide +kernel)
    · exact v2911_pb_checked.trans (by decide +kernel)
    · exact v2911_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 86 Primitive.Addresses.material2911
    · exact v2911_mb_checked.trans (by decide +kernel)
    · exact v2911_mg_checked.trans (by decide +kernel)
  upper_error := v2911_upper_checked
  lower_error := reuse_lower_error 36 86 Primitive.Addresses.material2911

def v2912_pa : Scalar.QComplex := ((999998660129227930020136955858 : Int)/10^30,(-1636991065609789416691932424 : Int)/10^30)
theorem v2912_pa_checked : Scalar.distance (sourceCoefficient 36 87 1 0) v2912_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2912_pb : Scalar.QComplex := ((-706324759842519171114665 : Int)/10^30,(-431476889701598846471534009 : Int)/10^30)
theorem v2912_pb_checked : Scalar.distance (sourceCoefficient 36 87 1 1) v2912_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2912_pg : Scalar.QComplex := ((-93086299437241826964188 : Int)/10^30,(152381644681154347452 : Int)/10^30)
theorem v2912_pg_checked : Scalar.distance (sourceCoefficient 36 87 1 2) v2912_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2912_mb : Scalar.QComplex := ((-1078669619660284874664503 : Int)/10^30,(-431476119516577284729394231 : Int)/10^30)
theorem v2912_mb_checked : Scalar.distance (sourceCoefficient 36 87 3 1) v2912_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2912_mg : Scalar.QComplex := ((-93086133278461947103523 : Int)/10^30,(232710871905547998352 : Int)/10^30)
theorem v2912_mg_checked : Scalar.distance (sourceCoefficient 36 87 3 2) v2912_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2912_upper : Scalar.QComplex := ((999994345450619188742628282769 : Int)/10^30,(-3362895595717151417385293240 : Int)/10^30)
theorem v2912_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 87 5) 1) 14) v2912_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2912 : Material (36 : Basis) (87 : Basis) where
  plus := ![v2912_pa,v2912_pb,v2912_pg]
  minus := ![(Primitive.Addresses.material2912 1).one,v2912_mb,v2912_mg]
  upper := v2912_upper
  lower := (Primitive.Addresses.material2912 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2912_pa_checked.trans (by decide +kernel)
    · exact v2912_pb_checked.trans (by decide +kernel)
    · exact v2912_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 87 Primitive.Addresses.material2912
    · exact v2912_mb_checked.trans (by decide +kernel)
    · exact v2912_mg_checked.trans (by decide +kernel)
  upper_error := v2912_upper_checked
  lower_error := reuse_lower_error 36 87 Primitive.Addresses.material2912

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
