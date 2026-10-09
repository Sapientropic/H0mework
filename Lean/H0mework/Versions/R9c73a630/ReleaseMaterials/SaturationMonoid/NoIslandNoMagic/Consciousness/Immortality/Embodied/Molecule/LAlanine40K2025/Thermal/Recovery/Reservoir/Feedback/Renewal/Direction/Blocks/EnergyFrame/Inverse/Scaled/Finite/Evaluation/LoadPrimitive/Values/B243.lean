import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B162

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3889_pa : Scalar.QComplex := ((999997773137677880610912103780 : Int)/10^30,(-2110383776786339992270747411 : Int)/10^30)
theorem v3889_pa_checked : Scalar.distance (sourceCoefficient 55 95 1 0) v3889_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3889_pb : Scalar.QComplex := ((-910583052760816215107325 : Int)/10^30,(-431476509170452240392808437 : Int)/10^30)
theorem v3889_pb_checked : Scalar.distance (sourceCoefficient 55 95 1 1) v3889_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3889_pg : Scalar.QComplex := ((-93086217106142598247311 : Int)/10^30,(196448079886041775450 : Int)/10^30)
theorem v3889_pg_checked : Scalar.distance (sourceCoefficient 55 95 1 2) v3889_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3889_mb : Scalar.QComplex := ((-1282927508142643365613900 : Int)/10^30,(-431475562719865031310662706 : Int)/10^30)
theorem v3889_mb_checked : Scalar.distance (sourceCoefficient 55 95 3 1) v3889_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3889_mg : Scalar.QComplex := ((-93086012920044470766653 : Int)/10^30,(276777219654457084667 : Int)/10^30)
theorem v3889_mg_checked : Scalar.distance (sourceCoefficient 55 95 3 2) v3889_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3889_upper : Scalar.QComplex := ((999992641427516569610918672362 : Int)/10^30,(-3836286070963919169203451179 : Int)/10^30)
theorem v3889_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 95 5) 1) 14) v3889_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3889 : Material (55 : Basis) (95 : Basis) where
  plus := ![v3889_pa,v3889_pb,v3889_pg]
  minus := ![(Primitive.Addresses.material3889 1).one,v3889_mb,v3889_mg]
  upper := v3889_upper
  lower := (Primitive.Addresses.material3889 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3889_pa_checked.trans (by decide +kernel)
    · exact v3889_pb_checked.trans (by decide +kernel)
    · exact v3889_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 95 Primitive.Addresses.material3889
    · exact v3889_mb_checked.trans (by decide +kernel)
    · exact v3889_mg_checked.trans (by decide +kernel)
  upper_error := v3889_upper_checked
  lower_error := reuse_lower_error 55 95 Primitive.Addresses.material3889

def v3890_pa : Scalar.QComplex := ((999997728036192888407145458239 : Int)/10^30,(-2131647825604324557860586359 : Int)/10^30)
theorem v3890_pa_checked : Scalar.distance (sourceCoefficient 55 96 1 0) v3890_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3890_pb : Scalar.QComplex := ((-919758005188153950093412 : Int)/10^30,(-431476487102414782871361714 : Int)/10^30)
theorem v3890_pb_checked : Scalar.distance (sourceCoefficient 55 96 1 1) v3890_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3890_pg : Scalar.QComplex := ((-93086212626508848884508 : Int)/10^30,(198427473559077672173 : Int)/10^30)
theorem v3890_pg_checked : Scalar.distance (sourceCoefficient 55 96 1 2) v3890_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3890_mb : Scalar.QComplex := ((-1292102438110004577532084 : Int)/10^30,(-431475532734265070453367410 : Int)/10^30)
theorem v3890_mb_checked : Scalar.distance (sourceCoefficient 55 96 3 1) v3890_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3890_mg : Scalar.QComplex := ((-93086006732284798127927 : Int)/10^30,(278756608724752083674 : Int)/10^30)
theorem v3890_mg_checked : Scalar.distance (sourceCoefficient 55 96 3 2) v3890_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3890_upper : Scalar.QComplex := ((999992559626279550369477293290 : Int)/10^30,(-3857550010270529349257040917 : Int)/10^30)
theorem v3890_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 96 5) 1) 14) v3890_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3890 : Material (55 : Basis) (96 : Basis) where
  plus := ![v3890_pa,v3890_pb,v3890_pg]
  minus := ![(Primitive.Addresses.material3890 1).one,v3890_mb,v3890_mg]
  upper := v3890_upper
  lower := (Primitive.Addresses.material3890 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3890_pa_checked.trans (by decide +kernel)
    · exact v3890_pb_checked.trans (by decide +kernel)
    · exact v3890_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 96 Primitive.Addresses.material3890
    · exact v3890_mb_checked.trans (by decide +kernel)
    · exact v3890_mg_checked.trans (by decide +kernel)
  upper_error := v3890_upper_checked
  lower_error := reuse_lower_error 55 96 Primitive.Addresses.material3890

def v3891_pa : Scalar.QComplex := ((999997569403749430642796051944 : Int)/10^30,(-2204809876914692417053101827 : Int)/10^30)
theorem v3891_pa_checked : Scalar.distance (sourceCoefficient 55 97 1 0) v3891_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3891_pb : Scalar.QComplex := ((-951325760919786722457455 : Int)/10^30,(-431476409186898508414774415 : Int)/10^30)
theorem v3891_pb_checked : Scalar.distance (sourceCoefficient 55 97 1 1) v3891_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3891_pg : Scalar.QComplex := ((-93086196838546073537571 : Int)/10^30,(205237865044436850665 : Int)/10^30)
theorem v3891_pg_checked : Scalar.distance (sourceCoefficient 55 97 1 2) v3891_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3891_mb : Scalar.QComplex := ((-1323670114849937813030521 : Int)/10^30,(-431475427577226370045301576 : Int)/10^30)
theorem v3891_mb_checked : Scalar.distance (sourceCoefficient 55 97 3 1) v3891_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3891_mg : Scalar.QComplex := ((-93085985067266778142304 : Int)/10^30,(285566984049990450223 : Int)/10^30)
theorem v3891_mg_checked : Scalar.distance (sourceCoefficient 55 97 3 2) v3891_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3891_upper : Scalar.QComplex := ((999992274723009004748299113195 : Int)/10^30,(-3930711678829409614667171257 : Int)/10^30)
theorem v3891_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 97 5) 1) 14) v3891_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3891 : Material (55 : Basis) (97 : Basis) where
  plus := ![v3891_pa,v3891_pb,v3891_pg]
  minus := ![(Primitive.Addresses.material3891 1).one,v3891_mb,v3891_mg]
  upper := v3891_upper
  lower := (Primitive.Addresses.material3891 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3891_pa_checked.trans (by decide +kernel)
    · exact v3891_pb_checked.trans (by decide +kernel)
    · exact v3891_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 97 Primitive.Addresses.material3891
    · exact v3891_mb_checked.trans (by decide +kernel)
    · exact v3891_mg_checked.trans (by decide +kernel)
  upper_error := v3891_upper_checked
  lower_error := reuse_lower_error 55 97 Primitive.Addresses.material3891

def v3892_pa : Scalar.QComplex := ((999999171300979034843278241186 : Int)/10^30,(-1287399454399544980212774254 : Int)/10^30)
theorem v3892_pa_checked : Scalar.distance (sourceCoefficient 56 57 1 0) v3892_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3892_pb : Scalar.QComplex := ((-555483925109065870221577 : Int)/10^30,(-431477163425677851602597485 : Int)/10^30)
theorem v3892_pb_checked : Scalar.distance (sourceCoefficient 56 57 1 1) v3892_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3892_pg : Scalar.QComplex := ((-93086352755266667622570 : Int)/10^30,(119839419059983136533 : Int)/10^30)
theorem v3892_pg_checked : Scalar.distance (sourceCoefficient 56 57 1 2) v3892_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3892_mb : Scalar.QComplex := ((-927829077303320218291750 : Int)/10^30,(-431476523409401125840831445 : Int)/10^30)
theorem v3892_mb_checked : Scalar.distance (sourceCoefficient 56 57 3 1) v3892_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3892_mg : Scalar.QComplex := ((-93086214678941998660671 : Int)/10^30,(200168704412388722169 : Int)/10^30)
theorem v3892_mg_checked : Scalar.distance (sourceCoefficient 56 57 3 2) v3892_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3892_upper : Scalar.QComplex := ((999995459985015208943520787559 : Int)/10^30,(-3013305387418615231100844558 : Int)/10^30)
theorem v3892_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 57 5) 1) 14) v3892_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3892 : Material (56 : Basis) (57 : Basis) where
  plus := ![v3892_pa,v3892_pb,v3892_pg]
  minus := ![(Primitive.Addresses.material3892 1).one,v3892_mb,v3892_mg]
  upper := v3892_upper
  lower := (Primitive.Addresses.material3892 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3892_pa_checked.trans (by decide +kernel)
    · exact v3892_pb_checked.trans (by decide +kernel)
    · exact v3892_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 57 Primitive.Addresses.material3892
    · exact v3892_mb_checked.trans (by decide +kernel)
    · exact v3892_mg_checked.trans (by decide +kernel)
  upper_error := v3892_upper_checked
  lower_error := reuse_lower_error 56 57 Primitive.Addresses.material3892

def v3893_pa : Scalar.QComplex := ((999999163053368528432255034413 : Int)/10^30,(-1293789999367544793949150236 : Int)/10^30)
theorem v3893_pa_checked : Scalar.distance (sourceCoefficient 56 58 1 0) v3893_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3893_pb : Scalar.QComplex := ((-558241301591832480613881 : Int)/10^30,(-431477159853257129107030518 : Int)/10^30)
theorem v3893_pb_checked : Scalar.distance (sourceCoefficient 56 58 1 1) v3893_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3893_pg : Scalar.QComplex := ((-93086351986041531760992 : Int)/10^30,(120434292074222790635 : Int)/10^30)
theorem v3893_pg_checked : Scalar.distance (sourceCoefficient 56 58 1 2) v3893_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3893_mb : Scalar.QComplex := ((-930586449676551358162283 : Int)/10^30,(-431476517457490016519904793 : Int)/10^30)
theorem v3893_mb_checked : Scalar.distance (sourceCoefficient 56 58 3 1) v3893_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3893_mg : Scalar.QComplex := ((-93086213396368530013936 : Int)/10^30,(200763576541323318395 : Int)/10^30)
theorem v3893_mg_checked : Scalar.distance (sourceCoefficient 56 58 3 2) v3893_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3893_upper : Scalar.QComplex := ((999995440707916117322607963866 : Int)/10^30,(-3019695908634021484461226909 : Int)/10^30)
theorem v3893_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 58 5) 1) 14) v3893_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3893 : Material (56 : Basis) (58 : Basis) where
  plus := ![v3893_pa,v3893_pb,v3893_pg]
  minus := ![(Primitive.Addresses.material3893 1).one,v3893_mb,v3893_mg]
  upper := v3893_upper
  lower := (Primitive.Addresses.material3893 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3893_pa_checked.trans (by decide +kernel)
    · exact v3893_pb_checked.trans (by decide +kernel)
    · exact v3893_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 58 Primitive.Addresses.material3893
    · exact v3893_mb_checked.trans (by decide +kernel)
    · exact v3893_mg_checked.trans (by decide +kernel)
  upper_error := v3893_upper_checked
  lower_error := reuse_lower_error 56 58 Primitive.Addresses.material3893

def v3894_pa : Scalar.QComplex := ((999999140172467051190793740696 : Int)/10^30,(-1311355911487888933778936444 : Int)/10^30)
theorem v3894_pa_checked : Scalar.distance (sourceCoefficient 56 59 1 0) v3894_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3894_pb : Scalar.QComplex := ((-565820597717925554562357 : Int)/10^30,(-431477149912571675987194747 : Int)/10^30)
theorem v3894_pb_checked : Scalar.distance (sourceCoefficient 56 59 1 1) v3894_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3894_pg : Scalar.QComplex := ((-93086349848795187160805 : Int)/10^30,(122069440111712864585 : Int)/10^30)
theorem v3894_pg_checked : Scalar.distance (sourceCoefficient 56 59 1 2) v3894_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3894_mb : Scalar.QComplex := ((-938165734402162259231830 : Int)/10^30,(-431476500976217066778936148 : Int)/10^30)
theorem v3894_mb_checked : Scalar.distance (sourceCoefficient 56 59 3 1) v3894_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3894_mg : Scalar.QComplex := ((-93086209848063869188109 : Int)/10^30,(202398722125625710643 : Int)/10^30)
theorem v3894_mg_checked : Scalar.distance (sourceCoefficient 56 59 3 2) v3894_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3894_upper : Scalar.QComplex := ((999995387509877965881426762690 : Int)/10^30,(-3037261755101642747473083655 : Int)/10^30)
theorem v3894_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 59 5) 1) 14) v3894_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3894 : Material (56 : Basis) (59 : Basis) where
  plus := ![v3894_pa,v3894_pb,v3894_pg]
  minus := ![(Primitive.Addresses.material3894 1).one,v3894_mb,v3894_mg]
  upper := v3894_upper
  lower := (Primitive.Addresses.material3894 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3894_pa_checked.trans (by decide +kernel)
    · exact v3894_pb_checked.trans (by decide +kernel)
    · exact v3894_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 59 Primitive.Addresses.material3894
    · exact v3894_mb_checked.trans (by decide +kernel)
    · exact v3894_mg_checked.trans (by decide +kernel)
  upper_error := v3894_upper_checked
  lower_error := reuse_lower_error 56 59 Primitive.Addresses.material3894

def v3895_pa : Scalar.QComplex := ((999999113393929138142038094395 : Int)/10^30,(-1331619823993842108312315703 : Int)/10^30)
theorem v3895_pa_checked : Scalar.distance (sourceCoefficient 56 60 1 0) v3895_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3895_pb : Scalar.QComplex := ((-574564020271901581391253 : Int)/10^30,(-431477138224558377414621716 : Int)/10^30)
theorem v3895_pb_checked : Scalar.distance (sourceCoefficient 56 60 1 1) v3895_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3895_pg : Scalar.QComplex := ((-93086347341657131647319 : Int)/10^30,(123955735363234613058 : Int)/10^30)
theorem v3895_pg_checked : Scalar.distance (sourceCoefficient 56 60 1 2) v3895_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3895_mb : Scalar.QComplex := ((-946909143614333406974015 : Int)/10^30,(-431476481743028245240262924 : Int)/10^30)
theorem v3895_mb_checked : Scalar.distance (sourceCoefficient 56 60 3 1) v3895_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3895_mg : Scalar.QComplex := ((-93086205713138900717863 : Int)/10^30,(204285014511246304420 : Int)/10^30)
theorem v3895_mg_checked : Scalar.distance (sourceCoefficient 56 60 3 2) v3895_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3895_upper : Scalar.QComplex := ((999995325757705278826396829133 : Int)/10^30,(-3057525591209551502824211684 : Int)/10^30)
theorem v3895_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 60 5) 1) 14) v3895_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3895 : Material (56 : Basis) (60 : Basis) where
  plus := ![v3895_pa,v3895_pb,v3895_pg]
  minus := ![(Primitive.Addresses.material3895 1).one,v3895_mb,v3895_mg]
  upper := v3895_upper
  lower := (Primitive.Addresses.material3895 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3895_pa_checked.trans (by decide +kernel)
    · exact v3895_pb_checked.trans (by decide +kernel)
    · exact v3895_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 60 Primitive.Addresses.material3895
    · exact v3895_mb_checked.trans (by decide +kernel)
    · exact v3895_mg_checked.trans (by decide +kernel)
  upper_error := v3895_upper_checked
  lower_error := reuse_lower_error 56 60 Primitive.Addresses.material3895

def v3896_pa : Scalar.QComplex := ((999999105574355824602327362312 : Int)/10^30,(-1337479154362251130296518117 : Int)/10^30)
theorem v3896_pa_checked : Scalar.distance (sourceCoefficient 56 61 1 0) v3896_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3896_pb : Scalar.QComplex := ((-577092189546246057991940 : Int)/10^30,(-431477134800928340092375826 : Int)/10^30)
theorem v3896_pb_checked : Scalar.distance (sourceCoefficient 56 61 1 1) v3896_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3896_pg : Scalar.QComplex := ((-93086346608404182638592 : Int)/10^30,(124501159501509617481 : Int)/10^30)
theorem v3896_pg_checked : Scalar.distance (sourceCoefficient 56 61 1 2) v3896_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3896_mb : Scalar.QComplex := ((-949437308992886392056285 : Int)/10^30,(-431476476137703263449931155 : Int)/10^30)
theorem v3896_mb_checked : Scalar.distance (sourceCoefficient 56 61 3 1) v3896_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3896_mg : Scalar.QComplex := ((-93086204509209758392685 : Int)/10^30,(204830437813670704542 : Int)/10^30)
theorem v3896_mg_checked : Scalar.distance (sourceCoefficient 56 61 3 2) v3896_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3896_upper : Scalar.QComplex := ((999995307825470950047360818366 : Int)/10^30,(-3063384899355302073337697168 : Int)/10^30)
theorem v3896_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 61 5) 1) 14) v3896_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3896 : Material (56 : Basis) (61 : Basis) where
  plus := ![v3896_pa,v3896_pb,v3896_pg]
  minus := ![(Primitive.Addresses.material3896 1).one,v3896_mb,v3896_mg]
  upper := v3896_upper
  lower := (Primitive.Addresses.material3896 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3896_pa_checked.trans (by decide +kernel)
    · exact v3896_pb_checked.trans (by decide +kernel)
    · exact v3896_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 61 Primitive.Addresses.material3896
    · exact v3896_mb_checked.trans (by decide +kernel)
    · exact v3896_mg_checked.trans (by decide +kernel)
  upper_error := v3896_upper_checked
  lower_error := reuse_lower_error 56 61 Primitive.Addresses.material3896

def v3897_pa : Scalar.QComplex := ((999999094151671309387604285542 : Int)/10^30,(-1345992509942024231564930008 : Int)/10^30)
theorem v3897_pa_checked : Scalar.distance (sourceCoefficient 56 62 1 0) v3897_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3897_pb : Scalar.QComplex := ((-580765510995898815783501 : Int)/10^30,(-431477129791343740212116153 : Int)/10^30)
theorem v3897_pb_checked : Scalar.distance (sourceCoefficient 56 62 1 1) v3897_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3897_pg : Scalar.QComplex := ((-93086345536374910787291 : Int)/10^30,(125293637366867814403 : Int)/10^30)
theorem v3897_pg_checked : Scalar.distance (sourceCoefficient 56 62 1 2) v3897_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3897_mb : Scalar.QComplex := ((-953110624751747808676663 : Int)/10^30,(-431476467958209558073298722 : Int)/10^30)
theorem v3897_mb_checked : Scalar.distance (sourceCoefficient 56 62 3 1) v3897_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3897_mg : Scalar.QComplex := ((-93086202753308179780863 : Int)/10^30,(205622914458840194962 : Int)/10^30)
theorem v3897_mg_checked : Scalar.distance (sourceCoefficient 56 62 3 2) v3897_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3897_upper : Scalar.QComplex := ((999995281709524042476168215297 : Int)/10^30,(-3071898222540914872113891517 : Int)/10^30)
theorem v3897_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 62 5) 1) 14) v3897_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3897 : Material (56 : Basis) (62 : Basis) where
  plus := ![v3897_pa,v3897_pb,v3897_pg]
  minus := ![(Primitive.Addresses.material3897 1).one,v3897_mb,v3897_mg]
  upper := v3897_upper
  lower := (Primitive.Addresses.material3897 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3897_pa_checked.trans (by decide +kernel)
    · exact v3897_pb_checked.trans (by decide +kernel)
    · exact v3897_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 62 Primitive.Addresses.material3897
    · exact v3897_mb_checked.trans (by decide +kernel)
    · exact v3897_mg_checked.trans (by decide +kernel)
  upper_error := v3897_upper_checked
  lower_error := reuse_lower_error 56 62 Primitive.Addresses.material3897

def v3898_pa : Scalar.QComplex := ((999999060470153014670013919066 : Int)/10^30,(-1370787660892206381215986216 : Int)/10^30)
theorem v3898_pa_checked : Scalar.distance (sourceCoefficient 56 63 1 0) v3898_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3898_pb : Scalar.QComplex := ((-591464060847277591486463 : Int)/10^30,(-431477114963357906944443359 : Int)/10^30)
theorem v3898_pb_checked : Scalar.distance (sourceCoefficient 56 63 1 1) v3898_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3898_pg : Scalar.QComplex := ((-93086342369243048655777 : Int)/10^30,(127601729402979064348 : Int)/10^30)
theorem v3898_pg_checked : Scalar.distance (sourceCoefficient 56 63 1 2) v3898_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3898_mb : Scalar.QComplex := ((-963809157823683580409583 : Int)/10^30,(-431476443897862569000927054 : Int)/10^30)
theorem v3898_mb_checked : Scalar.distance (sourceCoefficient 56 63 3 1) v3898_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3898_mg : Scalar.QComplex := ((-93086197594398022359682 : Int)/10^30,(207931002902451140150 : Int)/10^30)
theorem v3898_mg_checked : Scalar.distance (sourceCoefficient 56 63 3 2) v3898_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3898_upper : Scalar.QComplex := ((999995205233874770932042015158 : Int)/10^30,(-3096693278430387311289641810 : Int)/10^30)
theorem v3898_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 63 5) 1) 14) v3898_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3898 : Material (56 : Basis) (63 : Basis) where
  plus := ![v3898_pa,v3898_pb,v3898_pg]
  minus := ![(Primitive.Addresses.material3898 1).one,v3898_mb,v3898_mg]
  upper := v3898_upper
  lower := (Primitive.Addresses.material3898 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3898_pa_checked.trans (by decide +kernel)
    · exact v3898_pb_checked.trans (by decide +kernel)
    · exact v3898_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 63 Primitive.Addresses.material3898
    · exact v3898_mb_checked.trans (by decide +kernel)
    · exact v3898_mg_checked.trans (by decide +kernel)
  upper_error := v3898_upper_checked
  lower_error := reuse_lower_error 56 63 Primitive.Addresses.material3898

def v3899_pa : Scalar.QComplex := ((999999011265279062996580435063 : Int)/10^30,(-1406224898185798178322869322 : Int)/10^30)
theorem v3899_pa_checked : Scalar.distance (sourceCoefficient 56 64 1 0) v3899_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3899_pb : Scalar.QComplex := ((-606754431313676355926194 : Int)/10^30,(-431477093157210885773647159 : Int)/10^30)
theorem v3899_pb_checked : Scalar.distance (sourceCoefficient 56 64 1 1) v3899_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3899_pg : Scalar.QComplex := ((-93086337726874350063173 : Int)/10^30,(130900455218287767533 : Int)/10^30)
theorem v3899_pg_checked : Scalar.distance (sourceCoefficient 56 64 1 2) v3899_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3899_mb : Scalar.QComplex := ((-979099503779055848890810 : Int)/10^30,(-431476408896822607474939196 : Int)/10^30)
theorem v3899_mb_checked : Scalar.distance (sourceCoefficient 56 64 3 1) v3899_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3899_mg : Scalar.QComplex := ((-93086190105379242817278 : Int)/10^30,(211229723483338360717 : Int)/10^30)
theorem v3899_mg_checked : Scalar.distance (sourceCoefficient 56 64 3 2) v3899_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3899_upper : Scalar.QComplex := ((999995094867617376453221714678 : Int)/10^30,(-3132130378021228300608321933 : Int)/10^30)
theorem v3899_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 64 5) 1) 14) v3899_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3899 : Material (56 : Basis) (64 : Basis) where
  plus := ![v3899_pa,v3899_pb,v3899_pg]
  minus := ![(Primitive.Addresses.material3899 1).one,v3899_mb,v3899_mg]
  upper := v3899_upper
  lower := (Primitive.Addresses.material3899 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3899_pa_checked.trans (by decide +kernel)
    · exact v3899_pb_checked.trans (by decide +kernel)
    · exact v3899_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 64 Primitive.Addresses.material3899
    · exact v3899_mb_checked.trans (by decide +kernel)
    · exact v3899_mg_checked.trans (by decide +kernel)
  upper_error := v3899_upper_checked
  lower_error := reuse_lower_error 56 64 Primitive.Addresses.material3899

def v3900_pa : Scalar.QComplex := ((999998960041325911169279563059 : Int)/10^30,(-1442191480582109675178568236 : Int)/10^30)
theorem v3900_pa_checked : Scalar.distance (sourceCoefficient 56 65 1 0) v3900_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3900_pb : Scalar.QComplex := ((-622273201972275043135655 : Int)/10^30,(-431477070286598851496340555 : Int)/10^30)
theorem v3900_pb_checked : Scalar.distance (sourceCoefficient 56 65 1 1) v3900_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3900_pg : Scalar.QComplex := ((-93086332875708027812940 : Int)/10^30,(134248455844822610528 : Int)/10^30)
theorem v3900_pg_checked : Scalar.distance (sourceCoefficient 56 65 1 2) v3900_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3900_mb : Scalar.QComplex := ((-994618248922998845594876 : Int)/10^30,(-431476372634218950085674519 : Int)/10^30)
theorem v3900_mb_checked : Scalar.distance (sourceCoefficient 56 65 3 1) v3900_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3900_mg : Scalar.QComplex := ((-93086182365040974529098 : Int)/10^30,(214577718676921511584 : Int)/10^30)
theorem v3900_mg_checked : Scalar.distance (sourceCoefficient 56 65 3 2) v3900_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3900_upper : Scalar.QComplex := ((999994981568682163520216102737 : Int)/10^30,(-3168096818441644110387206429 : Int)/10^30)
theorem v3900_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 65 5) 1) 14) v3900_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3900 : Material (56 : Basis) (65 : Basis) where
  plus := ![v3900_pa,v3900_pb,v3900_pg]
  minus := ![(Primitive.Addresses.material3900 1).one,v3900_mb,v3900_mg]
  upper := v3900_upper
  lower := (Primitive.Addresses.material3900 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3900_pa_checked.trans (by decide +kernel)
    · exact v3900_pb_checked.trans (by decide +kernel)
    · exact v3900_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 65 Primitive.Addresses.material3900
    · exact v3900_mb_checked.trans (by decide +kernel)
    · exact v3900_mg_checked.trans (by decide +kernel)
  upper_error := v3900_upper_checked
  lower_error := reuse_lower_error 56 65 Primitive.Addresses.material3900

def v3901_pa : Scalar.QComplex := ((999998934522026226092724425262 : Int)/10^30,(-1459779028587718119160780011 : Int)/10^30)
theorem v3901_pa_checked : Scalar.distance (sourceCoefficient 56 66 1 0) v3901_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3901_pb : Scalar.QComplex := ((-629861832903578398518658 : Int)/10^30,(-431477058832004287032965963 : Int)/10^30)
theorem v3901_pb_checked : Scalar.distance (sourceCoefficient 56 66 1 1) v3901_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3901_pg : Scalar.QComplex := ((-93086330452357703437430 : Int)/10^30,(135885617825670797597 : Int)/10^30)
theorem v3901_pg_checked : Scalar.distance (sourceCoefficient 56 66 1 2) v3901_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3901_mb : Scalar.QComplex := ((-1002206867143908874343283 : Int)/10^30,(-431476354630981936226265190 : Int)/10^30)
theorem v3901_mb_checked : Scalar.distance (sourceCoefficient 56 66 3 1) v3901_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3901_mg : Scalar.QComplex := ((-93086178528894498044126 : Int)/10^30,(216214877956937284895 : Int)/10^30)
theorem v3901_mg_checked : Scalar.distance (sourceCoefficient 56 66 3 2) v3901_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3901_upper : Scalar.QComplex := ((999994925694908158654133322615 : Int)/10^30,(-3185684296208669614872238557 : Int)/10^30)
theorem v3901_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 66 5) 1) 14) v3901_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3901 : Material (56 : Basis) (66 : Basis) where
  plus := ![v3901_pa,v3901_pb,v3901_pg]
  minus := ![(Primitive.Addresses.material3901 1).one,v3901_mb,v3901_mg]
  upper := v3901_upper
  lower := (Primitive.Addresses.material3901 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3901_pa_checked.trans (by decide +kernel)
    · exact v3901_pb_checked.trans (by decide +kernel)
    · exact v3901_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 66 Primitive.Addresses.material3901
    · exact v3901_mb_checked.trans (by decide +kernel)
    · exact v3901_mg_checked.trans (by decide +kernel)
  upper_error := v3901_upper_checked
  lower_error := reuse_lower_error 56 66 Primitive.Addresses.material3901

def v3902_pa : Scalar.QComplex := ((999998890997871627790568982654 : Int)/10^30,(-1489296151495295487639680344 : Int)/10^30)
theorem v3902_pa_checked : Scalar.distance (sourceCoefficient 56 67 1 0) v3902_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3902_pb : Scalar.QComplex := ((-642597806593165384054142 : Int)/10^30,(-431477039207846280387359121 : Int)/10^30)
theorem v3902_pb_checked : Scalar.distance (sourceCoefficient 56 67 1 1) v3902_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3902_pg : Scalar.QComplex := ((-93086326309757760611615 : Int)/10^30,(138633261274539320648 : Int)/10^30)
theorem v3902_pg_checked : Scalar.distance (sourceCoefficient 56 67 1 2) v3902_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3902_mb : Scalar.QComplex := ((-1014942819156546272025238 : Int)/10^30,(-431476324016259549399671711 : Int)/10^30)
theorem v3902_mb_checked : Scalar.distance (sourceCoefficient 56 67 3 1) v3902_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3902_mg : Scalar.QComplex := ((-93086172015203550591209 : Int)/10^30,(218962516807855403541 : Int)/10^30)
theorem v3902_mg_checked : Scalar.distance (sourceCoefficient 56 67 3 2) v3902_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3902_upper : Scalar.QComplex := ((999994831226942018461572497348 : Int)/10^30,(-3215201300035217381129457901 : Int)/10^30)
theorem v3902_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 67 5) 1) 14) v3902_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3902 : Material (56 : Basis) (67 : Basis) where
  plus := ![v3902_pa,v3902_pb,v3902_pg]
  minus := ![(Primitive.Addresses.material3902 1).one,v3902_mb,v3902_mg]
  upper := v3902_upper
  lower := (Primitive.Addresses.material3902 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3902_pa_checked.trans (by decide +kernel)
    · exact v3902_pb_checked.trans (by decide +kernel)
    · exact v3902_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 67 Primitive.Addresses.material3902
    · exact v3902_mb_checked.trans (by decide +kernel)
    · exact v3902_mg_checked.trans (by decide +kernel)
  upper_error := v3902_upper_checked
  lower_error := reuse_lower_error 56 67 Primitive.Addresses.material3902

def v3903_pa : Scalar.QComplex := ((999998816578824352189001737512 : Int)/10^30,(-1538454078225912801287659741 : Int)/10^30)
theorem v3903_pa_checked : Scalar.distance (sourceCoefficient 56 68 1 0) v3903_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3903_pb : Scalar.QComplex := ((-663808344203498568649191 : Int)/10^30,(-431477005413203687145754381 : Int)/10^30)
theorem v3903_pb_checked : Scalar.distance (sourceCoefficient 56 68 1 1) v3903_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3903_pg : Scalar.QComplex := ((-93086319200648726367841 : Int)/10^30,(143209196878073257487 : Int)/10^30)
theorem v3903_pg_checked : Scalar.distance (sourceCoefficient 56 68 1 2) v3903_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3903_mb : Scalar.QComplex := ((-1036153319705972431070215 : Int)/10^30,(-431476271917890868882501017 : Int)/10^30)
theorem v3903_mb_checked : Scalar.distance (sourceCoefficient 56 68 3 1) v3903_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3903_mg : Scalar.QComplex := ((-93086160957270830032913 : Int)/10^30,(223538444572718470428 : Int)/10^30)
theorem v3903_mg_checked : Scalar.distance (sourceCoefficient 56 68 3 2) v3903_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3903_upper : Scalar.QComplex := ((999994671965883616520298263208 : Int)/10^30,(-3264359025110352970775646109 : Int)/10^30)
theorem v3903_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 68 5) 1) 14) v3903_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3903 : Material (56 : Basis) (68 : Basis) where
  plus := ![v3903_pa,v3903_pb,v3903_pg]
  minus := ![(Primitive.Addresses.material3903 1).one,v3903_mb,v3903_mg]
  upper := v3903_upper
  lower := (Primitive.Addresses.material3903 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3903_pa_checked.trans (by decide +kernel)
    · exact v3903_pb_checked.trans (by decide +kernel)
    · exact v3903_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 68 Primitive.Addresses.material3903
    · exact v3903_mb_checked.trans (by decide +kernel)
    · exact v3903_mg_checked.trans (by decide +kernel)
  upper_error := v3903_upper_checked
  lower_error := reuse_lower_error 56 68 Primitive.Addresses.material3903

def v3904_pa : Scalar.QComplex := ((999998783059729083615279468488 : Int)/10^30,(-1560089440028726834731462555 : Int)/10^30)
theorem v3904_pa_checked : Scalar.distance (sourceCoefficient 56 69 1 0) v3904_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3904_pb : Scalar.QComplex := ((-673143515044192232426512 : Int)/10^30,(-431476990098943109796782906 : Int)/10^30)
theorem v3904_pb_checked : Scalar.distance (sourceCoefficient 56 69 1 1) v3904_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3904_pg : Scalar.QComplex := ((-93086315988622396674427 : Int)/10^30,(145223155312933006267 : Int)/10^30)
theorem v3904_pg_checked : Scalar.distance (sourceCoefficient 56 69 1 2) v3904_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3904_mb : Scalar.QComplex := ((-1045488473855238202913811 : Int)/10^30,(-431476248547803998701187255 : Int)/10^30)
theorem v3904_mb_checked : Scalar.distance (sourceCoefficient 56 69 3 1) v3904_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3904_mg : Scalar.QComplex := ((-93086156007290272360501 : Int)/10^30,(225552399485855393233 : Int)/10^30)
theorem v3904_mg_checked : Scalar.distance (sourceCoefficient 56 69 3 2) v3904_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3904_upper : Scalar.QComplex := ((999994601106166543735158459143 : Int)/10^30,(-3285994296838919462064574428 : Int)/10^30)
theorem v3904_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 69 5) 1) 14) v3904_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3904 : Material (56 : Basis) (69 : Basis) where
  plus := ![v3904_pa,v3904_pb,v3904_pg]
  minus := ![(Primitive.Addresses.material3904 1).one,v3904_mb,v3904_mg]
  upper := v3904_upper
  lower := (Primitive.Addresses.material3904 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3904_pa_checked.trans (by decide +kernel)
    · exact v3904_pb_checked.trans (by decide +kernel)
    · exact v3904_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 69 Primitive.Addresses.material3904
    · exact v3904_mb_checked.trans (by decide +kernel)
    · exact v3904_mg_checked.trans (by decide +kernel)
  upper_error := v3904_upper_checked
  lower_error := reuse_lower_error 56 69 Primitive.Addresses.material3904

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
