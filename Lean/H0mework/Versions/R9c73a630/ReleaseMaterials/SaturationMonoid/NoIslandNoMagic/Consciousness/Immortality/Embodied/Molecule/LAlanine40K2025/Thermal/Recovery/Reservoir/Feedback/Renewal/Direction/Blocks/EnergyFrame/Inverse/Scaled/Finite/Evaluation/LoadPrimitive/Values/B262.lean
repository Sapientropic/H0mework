import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B174
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B175

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4193_pa : Scalar.QComplex := ((999998735341294748966385022966 : Int)/10^30,(-1590382284590854735145000237 : Int)/10^30)
theorem v4193_pa_checked : Scalar.distance (sourceCoefficient 64 66 1 0) v4193_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4193_pb : Scalar.QComplex := ((-686214205270600301099725 : Int)/10^30,(-431476975122599972861689490 : Int)/10^30)
theorem v4193_pb_checked : Scalar.distance (sourceCoefficient 64 66 1 1) v4193_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4193_pg : Scalar.QComplex := ((-93086312152164117855884 : Int)/10^30,(148043009008576307864 : Int)/10^30)
theorem v4193_pg_checked : Scalar.distance (sourceCoefficient 64 66 1 2) v4193_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4193_mb : Scalar.QComplex := ((-1058559146290921322522702 : Int)/10^30,(-431476222292049454787826228 : Int)/10^30)
theorem v4193_mb_checked : Scalar.distance (sourceCoefficient 64 66 3 1) v4193_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4193_mg : Scalar.QComplex := ((-93086149737426684186476 : Int)/10^30,(228372248820847583308 : Int)/10^30)
theorem v4193_mg_checked : Scalar.distance (sourceCoefficient 64 66 3 2) v4193_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4193_upper : Scalar.QComplex := ((999994501105101711247390843183 : Int)/10^30,(-3316287013925725155620866197 : Int)/10^30)
theorem v4193_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 66 5) 1) 14) v4193_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4193 : Material (64 : Basis) (66 : Basis) where
  plus := ![v4193_pa,v4193_pb,v4193_pg]
  minus := ![(Primitive.Addresses.material4193 1).one,v4193_mb,v4193_mg]
  upper := v4193_upper
  lower := (Primitive.Addresses.material4193 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4193_pa_checked.trans (by decide +kernel)
    · exact v4193_pb_checked.trans (by decide +kernel)
    · exact v4193_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 66 Primitive.Addresses.material4193
    · exact v4193_mb_checked.trans (by decide +kernel)
    · exact v4193_mg_checked.trans (by decide +kernel)
  upper_error := v4193_upper_checked
  lower_error := reuse_lower_error 64 66 Primitive.Addresses.material4193

def v4194_pa : Scalar.QComplex := ((999998687962103687348749890497 : Int)/10^30,(-1619899401562288725229130478 : Int)/10^30)
theorem v4194_pa_checked : Scalar.distance (sourceCoefficient 64 67 1 0) v4194_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4194_pb : Scalar.QComplex := ((-698950177252645681019251 : Int)/10^30,(-431476954389534257537431690 : Int)/10^30)
theorem v4194_pb_checked : Scalar.distance (sourceCoefficient 64 67 1 1) v4194_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4194_pg : Scalar.QComplex := ((-93086307710521190985528 : Int)/10^30,(150790651996966169687 : Int)/10^30)
theorem v4194_pg_checked : Scalar.distance (sourceCoefficient 64 67 1 2) v4194_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4194_mb : Scalar.QComplex := ((-1071295095639080341144017 : Int)/10^30,(-431476190568421245711102146 : Int)/10^30)
theorem v4194_mb_checked : Scalar.distance (sourceCoefficient 64 67 3 1) v4194_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4194_mg : Scalar.QComplex := ((-93086142924693261408733 : Int)/10^30,(231119886953226585347 : Int)/10^30)
theorem v4194_mg_checked : Scalar.distance (sourceCoefficient 64 67 3 2) v4194_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4194_upper : Scalar.QComplex := ((999994402782115094608266431691 : Int)/10^30,(-3345804005162695175165092255 : Int)/10^30)
theorem v4194_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 67 5) 1) 14) v4194_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4194 : Material (64 : Basis) (67 : Basis) where
  plus := ![v4194_pa,v4194_pb,v4194_pg]
  minus := ![(Primitive.Addresses.material4194 1).one,v4194_mb,v4194_mg]
  upper := v4194_upper
  lower := (Primitive.Addresses.material4194 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4194_pa_checked.trans (by decide +kernel)
    · exact v4194_pb_checked.trans (by decide +kernel)
    · exact v4194_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 67 Primitive.Addresses.material4194
    · exact v4194_mb_checked.trans (by decide +kernel)
    · exact v4194_mg_checked.trans (by decide +kernel)
  upper_error := v4194_upper_checked
  lower_error := reuse_lower_error 64 67 Primitive.Addresses.material4194

def v4195_pa : Scalar.QComplex := ((999998607122864304471469156104 : Int)/10^30,(-1669057318154275347146643342 : Int)/10^30)
theorem v4195_pa_checked : Scalar.distance (sourceCoefficient 64 68 1 0) v4195_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4195_pb : Scalar.QComplex := ((-720160711946584734692394 : Int)/10^30,(-431476918748112631716836234 : Int)/10^30)
theorem v4195_pb_checked : Scalar.distance (sourceCoefficient 64 68 1 1) v4195_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4195_pg : Scalar.QComplex := ((-93086300103384855893942 : Int)/10^30,(155366586814025995874 : Int)/10^30)
theorem v4195_pg_checked : Scalar.distance (sourceCoefficient 64 68 1 2) v4195_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4195_mb : Scalar.QComplex := ((-1092505591678426325898234 : Int)/10^30,(-431476136623276736971962006 : Int)/10^30)
theorem v4195_mb_checked : Scalar.distance (sourceCoefficient 64 68 3 1) v4195_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4195_mg : Scalar.QComplex := ((-93086131368734104132687 : Int)/10^30,(235695813501840704109 : Int)/10^30)
theorem v4195_mg_checked : Scalar.distance (sourceCoefficient 64 68 3 2) v4195_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4195_upper : Scalar.QComplex := ((999994237100891645870058288365 : Int)/10^30,(-3394961709018546031500617900 : Int)/10^30)
theorem v4195_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 68 5) 1) 14) v4195_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4195 : Material (64 : Basis) (68 : Basis) where
  plus := ![v4195_pa,v4195_pb,v4195_pg]
  minus := ![(Primitive.Addresses.material4195 1).one,v4195_mb,v4195_mg]
  upper := v4195_upper
  lower := (Primitive.Addresses.material4195 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4195_pa_checked.trans (by decide +kernel)
    · exact v4195_pb_checked.trans (by decide +kernel)
    · exact v4195_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 68 Primitive.Addresses.material4195
    · exact v4195_mb_checked.trans (by decide +kernel)
    · exact v4195_mg_checked.trans (by decide +kernel)
  upper_error := v4195_upper_checked
  lower_error := reuse_lower_error 64 68 Primitive.Addresses.material4195

def v4196_pa : Scalar.QComplex := ((999998570778117345487931877176 : Int)/10^30,(-1690692675394861429378899026 : Int)/10^30)
theorem v4196_pa_checked : Scalar.distance (sourceCoefficient 64 69 1 0) v4196_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4196_pb : Scalar.QComplex := ((-729495881474945874702875 : Int)/10^30,(-431476902621048605332728784 : Int)/10^30)
theorem v4196_pb_checked : Scalar.distance (sourceCoefficient 64 69 1 1) v4196_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4196_pg : Scalar.QComplex := ((-93086296672167003599485 : Int)/10^30,(157380544894984485525 : Int)/10^30)
theorem v4196_pg_checked : Scalar.distance (sourceCoefficient 64 69 1 2) v4196_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4196_mb : Scalar.QComplex := ((-1101840743813947293407459 : Int)/10^30,(-431476112440387852883246046 : Int)/10^30)
theorem v4196_mb_checked : Scalar.distance (sourceCoefficient 64 69 3 1) v4196_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4196_mg : Scalar.QComplex := ((-93086126199562410875101 : Int)/10^30,(237709767871924087572 : Int)/10^30)
theorem v4196_mg_checked : Scalar.distance (sourceCoefficient 64 69 3 2) v4196_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4196_upper : Scalar.QComplex := ((999994163415534965142933680312 : Int)/10^30,(-3416596971308072889952201817 : Int)/10^30)
theorem v4196_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 69 5) 1) 14) v4196_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4196 : Material (64 : Basis) (69 : Basis) where
  plus := ![v4196_pa,v4196_pb,v4196_pg]
  minus := ![(Primitive.Addresses.material4196 1).one,v4196_mb,v4196_mg]
  upper := v4196_upper
  lower := (Primitive.Addresses.material4196 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4196_pa_checked.trans (by decide +kernel)
    · exact v4196_pb_checked.trans (by decide +kernel)
    · exact v4196_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 69 Primitive.Addresses.material4196
    · exact v4196_mb_checked.trans (by decide +kernel)
    · exact v4196_mg_checked.trans (by decide +kernel)
  upper_error := v4196_upper_checked
  lower_error := reuse_lower_error 64 69 Primitive.Addresses.material4196

def v4197_pa : Scalar.QComplex := ((999998546614962109806390158283 : Int)/10^30,(-1704924621047018270962522816 : Int)/10^30)
theorem v4197_pa_checked : Scalar.distance (sourceCoefficient 64 70 1 0) v4197_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4197_pb : Scalar.QComplex := ((-735636645517925959685518 : Int)/10^30,(-431476891865675475387462436 : Int)/10^30)
theorem v4197_pb_checked : Scalar.distance (sourceCoefficient 64 70 1 1) v4197_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4197_pg : Scalar.QComplex := ((-93086294387360588046831 : Int)/10^30,(158705345843017015808 : Int)/10^30)
theorem v4197_pg_checked : Scalar.distance (sourceCoefficient 64 70 1 2) v4197_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4197_mb : Scalar.QComplex := ((-1107981496289037671288706 : Int)/10^30,(-431476096385815928308871739 : Int)/10^30)
theorem v4197_mb_checked : Scalar.distance (sourceCoefficient 64 70 3 1) v4197_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4197_mg : Scalar.QComplex := ((-93086122771513294727986 : Int)/10^30,(239034566354987645748 : Int)/10^30)
theorem v4197_mg_checked : Scalar.distance (sourceCoefficient 64 70 3 2) v4197_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4197_upper : Scalar.QComplex := ((999994114689368634043953354602 : Int)/10^30,(-3430828854060004611955355075 : Int)/10^30)
theorem v4197_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 70 5) 1) 14) v4197_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4197 : Material (64 : Basis) (70 : Basis) where
  plus := ![v4197_pa,v4197_pb,v4197_pg]
  minus := ![(Primitive.Addresses.material4197 1).one,v4197_mb,v4197_mg]
  upper := v4197_upper
  lower := (Primitive.Addresses.material4197 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4197_pa_checked.trans (by decide +kernel)
    · exact v4197_pb_checked.trans (by decide +kernel)
    · exact v4197_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 70 Primitive.Addresses.material4197
    · exact v4197_mb_checked.trans (by decide +kernel)
    · exact v4197_mg_checked.trans (by decide +kernel)
  upper_error := v4197_upper_checked
  lower_error := reuse_lower_error 64 70 Primitive.Addresses.material4197

def v4198_pa : Scalar.QComplex := ((999998504902471097801392515330 : Int)/10^30,(-1729217401742122269436378889 : Int)/10^30)
theorem v4198_pa_checked : Scalar.distance (sourceCoefficient 64 71 1 0) v4198_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4198_pb : Scalar.QComplex := ((-746118433172111069706161 : Int)/10^30,(-431476873237916699246803152 : Int)/10^30)
theorem v4198_pb_checked : Scalar.distance (sourceCoefficient 64 71 1 1) v4198_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4198_pg : Scalar.QComplex := ((-93086290436562265242527 : Int)/10^30,(160966673947401219155 : Int)/10^30)
theorem v4198_pg_checked : Scalar.distance (sourceCoefficient 64 71 1 2) v4198_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4198_mb : Scalar.QComplex := ((-1118463263965457335597427 : Int)/10^30,(-431476068712753424763815302 : Int)/10^30)
theorem v4198_mb_checked : Scalar.distance (sourceCoefficient 64 71 3 1) v4198_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4198_mg : Scalar.QComplex := ((-93086116869292135339994 : Int)/10^30,(241295890208015032804 : Int)/10^30)
theorem v4198_mg_checked : Scalar.distance (sourceCoefficient 64 71 3 2) v4198_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4198_upper : Scalar.QComplex := ((999994031049804091994256007423 : Int)/10^30,(-3455121526581890036452860510 : Int)/10^30)
theorem v4198_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 71 5) 1) 14) v4198_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4198 : Material (64 : Basis) (71 : Basis) where
  plus := ![v4198_pa,v4198_pb,v4198_pg]
  minus := ![(Primitive.Addresses.material4198 1).one,v4198_mb,v4198_mg]
  upper := v4198_upper
  lower := (Primitive.Addresses.material4198 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4198_pa_checked.trans (by decide +kernel)
    · exact v4198_pb_checked.trans (by decide +kernel)
    · exact v4198_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 71 Primitive.Addresses.material4198
    · exact v4198_mb_checked.trans (by decide +kernel)
    · exact v4198_mg_checked.trans (by decide +kernel)
  upper_error := v4198_upper_checked
  lower_error := reuse_lower_error 64 71 Primitive.Addresses.material4198

def v4199_pa : Scalar.QComplex := ((999998458968265660427847225850 : Int)/10^30,(-1755579987895834401567514079 : Int)/10^30)
theorem v4199_pa_checked : Scalar.distance (sourceCoefficient 64 72 1 0) v4199_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4199_pb : Scalar.QComplex := ((-757493295054326955045611 : Int)/10^30,(-431476852638893131107955116 : Int)/10^30)
theorem v4199_pb_checked : Scalar.distance (sourceCoefficient 64 72 1 1) v4199_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4199_pg : Scalar.QComplex := ((-93086286076632659273722 : Int)/10^30,(163420672820125805291 : Int)/10^30)
theorem v4199_pg_checked : Scalar.distance (sourceCoefficient 64 72 1 2) v4199_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4199_mb : Scalar.QComplex := ((-1129838103836262691596583 : Int)/10^30,(-431476038297744026992082844 : Int)/10^30)
theorem v4199_mb_checked : Scalar.distance (sourceCoefficient 64 72 3 1) v4199_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4199_mg : Scalar.QComplex := ((-93086110391673649617306 : Int)/10^30,(243749884404580799325 : Int)/10^30)
theorem v4199_mg_checked : Scalar.distance (sourceCoefficient 64 72 3 2) v4199_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4199_upper : Scalar.QComplex := ((999993939616234962050507646038 : Int)/10^30,(-3481483994193355393194195813 : Int)/10^30)
theorem v4199_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 72 5) 1) 14) v4199_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4199 : Material (64 : Basis) (72 : Basis) where
  plus := ![v4199_pa,v4199_pb,v4199_pg]
  minus := ![(Primitive.Addresses.material4199 1).one,v4199_mb,v4199_mg]
  upper := v4199_upper
  lower := (Primitive.Addresses.material4199 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4199_pa_checked.trans (by decide +kernel)
    · exact v4199_pb_checked.trans (by decide +kernel)
    · exact v4199_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 72 Primitive.Addresses.material4199
    · exact v4199_mb_checked.trans (by decide +kernel)
    · exact v4199_mg_checked.trans (by decide +kernel)
  upper_error := v4199_upper_checked
  lower_error := reuse_lower_error 64 72 Primitive.Addresses.material4199

def v4200_pa : Scalar.QComplex := ((999998442334014362164056686069 : Int)/10^30,(-1765029615885339492661460153 : Int)/10^30)
theorem v4200_pa_checked : Scalar.distance (sourceCoefficient 64 73 1 0) v4200_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4200_pb : Scalar.QComplex := ((-761570596545009659485331 : Int)/10^30,(-431476845157860010309762135 : Int)/10^30)
theorem v4200_pb_checked : Scalar.distance (sourceCoefficient 64 73 1 1) v4200_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4200_pg : Scalar.QComplex := ((-93086284495446681911247 : Int)/10^30,(164300304892188050603 : Int)/10^30)
theorem v4200_pg_checked : Scalar.distance (sourceCoefficient 64 73 1 2) v4200_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4200_mb : Scalar.QComplex := ((-1133915397352985059146903 : Int)/10^30,(-431476027298186140107541483 : Int)/10^30)
theorem v4200_mb_checked : Scalar.distance (sourceCoefficient 64 73 3 1) v4200_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4200_mg : Scalar.QComplex := ((-93086108051405399970784 : Int)/10^30,(244629514784623538545 : Int)/10^30)
theorem v4200_mg_checked : Scalar.distance (sourceCoefficient 64 73 3 2) v4200_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4200_upper : Scalar.QComplex := ((999993906672807792218874734125 : Int)/10^30,(-3490933579399540931885844367 : Int)/10^30)
theorem v4200_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 73 5) 1) 14) v4200_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4200 : Material (64 : Basis) (73 : Basis) where
  plus := ![v4200_pa,v4200_pb,v4200_pg]
  minus := ![(Primitive.Addresses.material4200 1).one,v4200_mb,v4200_mg]
  upper := v4200_upper
  lower := (Primitive.Addresses.material4200 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4200_pa_checked.trans (by decide +kernel)
    · exact v4200_pb_checked.trans (by decide +kernel)
    · exact v4200_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 73 Primitive.Addresses.material4200
    · exact v4200_mb_checked.trans (by decide +kernel)
    · exact v4200_mg_checked.trans (by decide +kernel)
  upper_error := v4200_upper_checked
  lower_error := reuse_lower_error 64 73 Primitive.Addresses.material4200

def v4201_pa : Scalar.QComplex := ((999998423509621023946682637432 : Int)/10^30,(-1775662769962301042856100211 : Int)/10^30)
theorem v4201_pa_checked : Scalar.distance (sourceCoefficient 64 74 1 0) v4201_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4201_pb : Scalar.QComplex := ((-766158562832600234645325 : Int)/10^30,(-431476836678432687815800506 : Int)/10^30)
theorem v4201_pb_checked : Scalar.distance (sourceCoefficient 64 74 1 1) v4201_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4201_pg : Scalar.QComplex := ((-93086282704628284058811 : Int)/10^30,(165290107171057790003 : Int)/10^30)
theorem v4201_pg_checked : Scalar.distance (sourceCoefficient 64 74 1 2) v4201_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4201_mb : Scalar.QComplex := ((-1138503354614902224936711 : Int)/10^30,(-431476014859553703032200781 : Int)/10^30)
theorem v4201_mb_checked : Scalar.distance (sourceCoefficient 64 74 3 1) v4201_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4201_mg : Scalar.QComplex := ((-93086105406432881297085 : Int)/10^30,(245619315149549031443 : Int)/10^30)
theorem v4201_mg_checked : Scalar.distance (sourceCoefficient 64 74 3 2) v4201_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4201_upper : Scalar.QComplex := ((999993869496583186091042459803 : Int)/10^30,(-3501566685150473376326032489 : Int)/10^30)
theorem v4201_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 74 5) 1) 14) v4201_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4201 : Material (64 : Basis) (74 : Basis) where
  plus := ![v4201_pa,v4201_pb,v4201_pg]
  minus := ![(Primitive.Addresses.material4201 1).one,v4201_mb,v4201_mg]
  upper := v4201_upper
  lower := (Primitive.Addresses.material4201 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4201_pa_checked.trans (by decide +kernel)
    · exact v4201_pb_checked.trans (by decide +kernel)
    · exact v4201_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 74 Primitive.Addresses.material4201
    · exact v4201_mb_checked.trans (by decide +kernel)
    · exact v4201_mg_checked.trans (by decide +kernel)
  upper_error := v4201_upper_checked
  lower_error := reuse_lower_error 64 74 Primitive.Addresses.material4201

def v4202_pa : Scalar.QComplex := ((999998397093204281927201762792 : Int)/10^30,(-1790477875352261882088536531 : Int)/10^30)
theorem v4202_pa_checked : Scalar.distance (sourceCoefficient 64 75 1 0) v4202_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4202_pb : Scalar.QComplex := ((-772550946779399991091933 : Int)/10^30,(-431476824755650511232645095 : Int)/10^30)
theorem v4202_pb_checked : Scalar.distance (sourceCoefficient 64 75 1 1) v4202_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4202_pg : Scalar.QComplex := ((-93086280189020137773421 : Int)/10^30,(166669192332463149416 : Int)/10^30)
theorem v4202_pg_checked : Scalar.distance (sourceCoefficient 64 75 1 2) v4202_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4202_mb : Scalar.QComplex := ((-1144895725892701255395332 : Int)/10^30,(-431475997420436522043086618 : Int)/10^30)
theorem v4202_mb_checked : Scalar.distance (sourceCoefficient 64 75 3 1) v4202_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4202_mg : Scalar.QComplex := ((-93086101700737289084727 : Int)/10^30,(246998397626601426501 : Int)/10^30)
theorem v4202_mg_checked : Scalar.distance (sourceCoefficient 64 75 3 2) v4202_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4202_upper : Scalar.QComplex := ((999993817510677901010901511282 : Int)/10^30,(-3516381722882736223621577523 : Int)/10^30)
theorem v4202_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 75 5) 1) 14) v4202_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4202 : Material (64 : Basis) (75 : Basis) where
  plus := ![v4202_pa,v4202_pb,v4202_pg]
  minus := ![(Primitive.Addresses.material4202 1).one,v4202_mb,v4202_mg]
  upper := v4202_upper
  lower := (Primitive.Addresses.material4202 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4202_pa_checked.trans (by decide +kernel)
    · exact v4202_pb_checked.trans (by decide +kernel)
    · exact v4202_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 75 Primitive.Addresses.material4202
    · exact v4202_mb_checked.trans (by decide +kernel)
    · exact v4202_mg_checked.trans (by decide +kernel)
  upper_error := v4202_upper_checked
  lower_error := reuse_lower_error 64 75 Primitive.Addresses.material4202

def v4203_pa : Scalar.QComplex := ((999998374759978484954195539322 : Int)/10^30,(-1802908040257451421268420438 : Int)/10^30)
theorem v4203_pa_checked : Scalar.distance (sourceCoefficient 64 76 1 0) v4203_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4203_pb : Scalar.QComplex := ((-777914282623210131823510 : Int)/10^30,(-431476814654784270216470923 : Int)/10^30)
theorem v4203_pb_checked : Scalar.distance (sourceCoefficient 64 76 1 1) v4203_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4203_pg : Scalar.QComplex := ((-93086278059985777244914 : Int)/10^30,(167826271909962924406 : Int)/10^30)
theorem v4203_pg_checked : Scalar.distance (sourceCoefficient 64 76 1 2) v4203_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4203_mb : Scalar.QComplex := ((-1150259051022903705050213 : Int)/10^30,(-431475982691256764512331809 : Int)/10^30)
theorem v4203_mb_checked : Scalar.distance (sourceCoefficient 64 76 3 1) v4203_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4203_mg : Scalar.QComplex := ((-93086098573196158840356 : Int)/10^30,(248155474936006828650 : Int)/10^30)
theorem v4203_mg_checked : Scalar.distance (sourceCoefficient 64 76 3 2) v4203_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4203_upper : Scalar.QComplex := ((999993773724148396148565741094 : Int)/10^30,(-3528811830729533615103555362 : Int)/10^30)
theorem v4203_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 76 5) 1) 14) v4203_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4203 : Material (64 : Basis) (76 : Basis) where
  plus := ![v4203_pa,v4203_pb,v4203_pg]
  minus := ![(Primitive.Addresses.material4203 1).one,v4203_mb,v4203_mg]
  upper := v4203_upper
  lower := (Primitive.Addresses.material4203 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4203_pa_checked.trans (by decide +kernel)
    · exact v4203_pb_checked.trans (by decide +kernel)
    · exact v4203_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 76 Primitive.Addresses.material4203
    · exact v4203_mb_checked.trans (by decide +kernel)
    · exact v4203_mg_checked.trans (by decide +kernel)
  upper_error := v4203_upper_checked
  lower_error := reuse_lower_error 64 76 Primitive.Addresses.material4203

def v4204_pa : Scalar.QComplex := ((999998369567621306044469711694 : Int)/10^30,(-1805785729005013918776675527 : Int)/10^30)
theorem v4204_pa_checked : Scalar.distance (sourceCoefficient 64 77 1 0) v4204_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4204_pb : Scalar.QComplex := ((-779155940415627304578063 : Int)/10^30,(-431476812303676484260245620 : Int)/10^30)
theorem v4204_pb_checked : Scalar.distance (sourceCoefficient 64 77 1 1) v4204_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4204_pg : Scalar.QComplex := ((-93086277564704229483904 : Int)/10^30,(168094145658680249553 : Int)/10^30)
theorem v4204_pg_checked : Scalar.distance (sourceCoefficient 64 77 1 2) v4204_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4204_mb : Scalar.QComplex := ((-1151500706324094805807038 : Int)/10^30,(-431475979268655101316007223 : Int)/10^30)
theorem v4204_mb_checked : Scalar.distance (sourceCoefficient 64 77 3 1) v4204_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4204_mg : Scalar.QComplex := ((-93086097846751814938034 : Int)/10^30,(248423348157576845650 : Int)/10^30)
theorem v4204_mg_checked : Scalar.distance (sourceCoefficient 64 77 3 2) v4204_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4204_upper : Scalar.QComplex := ((999993763565169234235925426910 : Int)/10^30,(-3531689506229579316349034828 : Int)/10^30)
theorem v4204_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 77 5) 1) 14) v4204_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4204 : Material (64 : Basis) (77 : Basis) where
  plus := ![v4204_pa,v4204_pb,v4204_pg]
  minus := ![(Primitive.Addresses.material4204 1).one,v4204_mb,v4204_mg]
  upper := v4204_upper
  lower := (Primitive.Addresses.material4204 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4204_pa_checked.trans (by decide +kernel)
    · exact v4204_pb_checked.trans (by decide +kernel)
    · exact v4204_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 77 Primitive.Addresses.material4204
    · exact v4204_mb_checked.trans (by decide +kernel)
    · exact v4204_mg_checked.trans (by decide +kernel)
  upper_error := v4204_upper_checked
  lower_error := reuse_lower_error 64 77 Primitive.Addresses.material4204

def v4205_pa : Scalar.QComplex := ((999998338178632266903458689435 : Int)/10^30,(-1823085289781017027533992755 : Int)/10^30)
theorem v4205_pa_checked : Scalar.distance (sourceCoefficient 64 78 1 0) v4205_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4205_pb : Scalar.QComplex := ((-786620310664415851532122 : Int)/10^30,(-431476798069311045974484787 : Int)/10^30)
theorem v4205_pb_checked : Scalar.distance (sourceCoefficient 64 78 1 1) v4205_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4205_pg : Scalar.QComplex := ((-93086274568307516574298 : Int)/10^30,(169704499864562299950 : Int)/10^30)
theorem v4205_pg_checked : Scalar.distance (sourceCoefficient 64 78 1 2) v4205_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4205_mb : Scalar.QComplex := ((-1158965061509940889344439 : Int)/10^30,(-431475958592879621186840588 : Int)/10^30)
theorem v4205_mb_checked : Scalar.distance (sourceCoefficient 64 78 3 1) v4205_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4205_mg : Scalar.QComplex := ((-93086093460693065708737 : Int)/10^30,(250033699178095017831 : Int)/10^30)
theorem v4205_mg_checked : Scalar.distance (sourceCoefficient 64 78 3 2) v4205_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4205_upper : Scalar.QComplex := ((999993702318754449819601388784 : Int)/10^30,(-3548988987065371303693281667 : Int)/10^30)
theorem v4205_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 78 5) 1) 14) v4205_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4205 : Material (64 : Basis) (78 : Basis) where
  plus := ![v4205_pa,v4205_pb,v4205_pg]
  minus := ![(Primitive.Addresses.material4205 1).one,v4205_mb,v4205_mg]
  upper := v4205_upper
  lower := (Primitive.Addresses.material4205 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4205_pa_checked.trans (by decide +kernel)
    · exact v4205_pb_checked.trans (by decide +kernel)
    · exact v4205_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 78 Primitive.Addresses.material4205
    · exact v4205_mb_checked.trans (by decide +kernel)
    · exact v4205_mg_checked.trans (by decide +kernel)
  upper_error := v4205_upper_checked
  lower_error := reuse_lower_error 64 78 Primitive.Addresses.material4205

def v4206_pa : Scalar.QComplex := ((999998327995585917702621504077 : Int)/10^30,(-1828662361554432509861751842 : Int)/10^30)
theorem v4206_pa_checked : Scalar.distance (sourceCoefficient 64 79 1 0) v4206_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4206_pb : Scalar.QComplex := ((-789026691310808253615976 : Int)/10^30,(-431476793443703843838347700 : Int)/10^30)
theorem v4206_pb_checked : Scalar.distance (sourceCoefficient 64 79 1 1) v4206_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4206_pg : Scalar.QComplex := ((-93086273595394396277793 : Int)/10^30,(170223649515949303592 : Int)/10^30)
theorem v4206_pg_checked : Scalar.distance (sourceCoefficient 64 79 1 2) v4206_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4206_mb : Scalar.QComplex := ((-1161371437268637113919225 : Int)/10^30,(-431475951890676022900105068 : Int)/10^30)
theorem v4206_mb_checked : Scalar.distance (sourceCoefficient 64 79 3 1) v4206_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4206_mg : Scalar.QComplex := ((-93086092039777540157598 : Int)/10^30,(250552847796598675515 : Int)/10^30)
theorem v4206_mg_checked : Scalar.distance (sourceCoefficient 64 79 3 2) v4206_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4206_upper : Scalar.QComplex := ((999993682510203334154029565948 : Int)/10^30,(-3554566032957379308417313083 : Int)/10^30)
theorem v4206_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 79 5) 1) 14) v4206_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4206 : Material (64 : Basis) (79 : Basis) where
  plus := ![v4206_pa,v4206_pb,v4206_pg]
  minus := ![(Primitive.Addresses.material4206 1).one,v4206_mb,v4206_mg]
  upper := v4206_upper
  lower := (Primitive.Addresses.material4206 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4206_pa_checked.trans (by decide +kernel)
    · exact v4206_pb_checked.trans (by decide +kernel)
    · exact v4206_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 79 Primitive.Addresses.material4206
    · exact v4206_mb_checked.trans (by decide +kernel)
    · exact v4206_mg_checked.trans (by decide +kernel)
  upper_error := v4206_upper_checked
  lower_error := reuse_lower_error 64 79 Primitive.Addresses.material4206

def v4207_pa : Scalar.QComplex := ((999998312026418432304748002883 : Int)/10^30,(-1837374298797220694791153999 : Int)/10^30)
theorem v4207_pa_checked : Scalar.distance (sourceCoefficient 64 80 1 0) v4207_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4207_pb : Scalar.QComplex := ((-792785695660181362336900 : Int)/10^30,(-431476786182239836641750929 : Int)/10^30)
theorem v4207_pb_checked : Scalar.distance (sourceCoefficient 64 80 1 1) v4207_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4207_pg : Scalar.QComplex := ((-93086272068848343090092 : Int)/10^30,(171034612572055089843 : Int)/10^30)
theorem v4207_pg_checked : Scalar.distance (sourceCoefficient 64 80 1 2) v4207_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4207_mb : Scalar.QComplex := ((-1165130433952044714370699 : Int)/10^30,(-431475941385363265240642053 : Int)/10^30)
theorem v4207_mb_checked : Scalar.distance (sourceCoefficient 64 80 3 1) v4207_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4207_mg : Scalar.QComplex := ((-93086089813407462373663 : Int)/10^30,(251363809233405362316 : Int)/10^30)
theorem v4207_mg_checked : Scalar.distance (sourceCoefficient 64 80 3 2) v4207_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4207_upper : Scalar.QComplex := ((999993651505046292675710626138 : Int)/10^30,(-3563277929663425978011329368 : Int)/10^30)
theorem v4207_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 80 5) 1) 14) v4207_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4207 : Material (64 : Basis) (80 : Basis) where
  plus := ![v4207_pa,v4207_pb,v4207_pg]
  minus := ![(Primitive.Addresses.material4207 1).one,v4207_mb,v4207_mg]
  upper := v4207_upper
  lower := (Primitive.Addresses.material4207 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4207_pa_checked.trans (by decide +kernel)
    · exact v4207_pb_checked.trans (by decide +kernel)
    · exact v4207_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 80 Primitive.Addresses.material4207
    · exact v4207_mb_checked.trans (by decide +kernel)
    · exact v4207_mg_checked.trans (by decide +kernel)
  upper_error := v4207_upper_checked
  lower_error := reuse_lower_error 64 80 Primitive.Addresses.material4207

def v4208_pa : Scalar.QComplex := ((999998263484097650188688743367 : Int)/10^30,(-1863606393317039334076092804 : Int)/10^30)
theorem v4208_pa_checked : Scalar.distance (sourceCoefficient 64 81 1 0) v4208_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4208_pb : Scalar.QComplex := ((-804104252398448723574015 : Int)/10^30,(-431476764053916926339092034 : Int)/10^30)
theorem v4208_pb_checked : Scalar.distance (sourceCoefficient 64 81 1 1) v4208_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4208_pg : Scalar.QComplex := ((-93086267422564084191489 : Int)/10^30,(173476464343349083632 : Int)/10^30)
theorem v4208_pg_checked : Scalar.distance (sourceCoefficient 64 81 1 2) v4208_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4208_mb : Scalar.QComplex := ((-1176448967380150069429922 : Int)/10^30,(-431475909489643898071165759 : Int)/10^30)
theorem v4208_mb_checked : Scalar.distance (sourceCoefficient 64 81 3 1) v4208_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4208_mg : Scalar.QComplex := ((-93086083059916831793562 : Int)/10^30,(253805656085952288959 : Int)/10^30)
theorem v4208_mg_checked : Scalar.distance (sourceCoefficient 64 81 3 2) v4208_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4208_upper : Scalar.QComplex := ((999993557688582424462499602966 : Int)/10^30,(-3589509901333979323316959988 : Int)/10^30)
theorem v4208_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 81 5) 1) 14) v4208_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4208 : Material (64 : Basis) (81 : Basis) where
  plus := ![v4208_pa,v4208_pb,v4208_pg]
  minus := ![(Primitive.Addresses.material4208 1).one,v4208_mb,v4208_mg]
  upper := v4208_upper
  lower := (Primitive.Addresses.material4208 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4208_pa_checked.trans (by decide +kernel)
    · exact v4208_pb_checked.trans (by decide +kernel)
    · exact v4208_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 81 Primitive.Addresses.material4208
    · exact v4208_mb_checked.trans (by decide +kernel)
    · exact v4208_mg_checked.trans (by decide +kernel)
  upper_error := v4208_upper_checked
  lower_error := reuse_lower_error 64 81 Primitive.Addresses.material4208

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
