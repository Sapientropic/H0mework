import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B139
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B140

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3345_pa : Scalar.QComplex := ((999999015604226488839453845279 : Int)/10^30,(-1403135979863420858773323505 : Int)/10^30)
theorem v3345_pa_checked : Scalar.distance (sourceCoefficient 44 68 1 0) v3345_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3345_pb : Scalar.QComplex := ((-605421618222627108677467 : Int)/10^30,(-431477084856077675197635794 : Int)/10^30)
theorem v3345_pb_checked : Scalar.distance (sourceCoefficient 44 68 1 1) v3345_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3345_pg : Scalar.QComplex := ((-93086337033384783282751 : Int)/10^30,(130612917300038754757 : Int)/10^30)
theorem v3345_pg_checked : Scalar.distance (sourceCoefficient 44 68 1 2) v3345_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3345_mb : Scalar.QComplex := ((-977766684020769736441152 : Int)/10^30,(-431476401745850157692414152 : Int)/10^30)
theorem v3345_mb_checked : Scalar.distance (sourceCoefficient 44 68 3 1) v3345_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3345_mg : Scalar.QComplex := ((-93086189660022207476510 : Int)/10^30,(210942185073702593517 : Int)/10^30)
theorem v3345_mg_checked : Scalar.distance (sourceCoefficient 44 68 3 2) v3345_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3345_upper : Scalar.QComplex := ((999995104537751139885633891119 : Int)/10^30,(-3129041471788061603174002887 : Int)/10^30)
theorem v3345_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 68 5) 1) 14) v3345_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3345 : Material (44 : Basis) (68 : Basis) where
  plus := ![v3345_pa,v3345_pb,v3345_pg]
  minus := ![(Primitive.Addresses.material3345 1).one,v3345_mb,v3345_mg]
  upper := v3345_upper
  lower := (Primitive.Addresses.material3345 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3345_pa_checked.trans (by decide +kernel)
    · exact v3345_pb_checked.trans (by decide +kernel)
    · exact v3345_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 68 Primitive.Addresses.material3345
    · exact v3345_mb_checked.trans (by decide +kernel)
    · exact v3345_mg_checked.trans (by decide +kernel)
  upper_error := v3345_upper_checked
  lower_error := reuse_lower_error 44 68 Primitive.Addresses.material3345

def v3346_pa : Scalar.QComplex := ((999998985012790703604051841602 : Int)/10^30,(-1424771346003897167451494953 : Int)/10^30)
theorem v3346_pa_checked : Scalar.distance (sourceCoefficient 44 69 1 0) v3346_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3346_pb : Scalar.QComplex := ((-614756790311056593704153 : Int)/10^30,(-431477070383963253483615695 : Int)/10^30)
theorem v3346_pb_checked : Scalar.distance (sourceCoefficient 44 69 1 1) v3346_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3346_pg : Scalar.QComplex := ((-93086334048462926221381 : Int)/10^30,(132626876071379747043 : Int)/10^30)
theorem v3346_pg_checked : Scalar.distance (sourceCoefficient 44 69 1 2) v3346_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3346_mb : Scalar.QComplex := ((-987101840144505068403139 : Int)/10^30,(-431476379217908052836732240 : Int)/10^30)
theorem v3346_mb_checked : Scalar.distance (sourceCoefficient 44 69 3 1) v3346_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3346_mg : Scalar.QComplex := ((-93086184937145747506609 : Int)/10^30,(212956140519301566016 : Int)/10^30)
theorem v3346_mg_checked : Scalar.distance (sourceCoefficient 44 69 3 2) v3346_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3346_upper : Scalar.QComplex := ((999995036605681703622343554199 : Int)/10^30,(-3150676752907158582307206604 : Int)/10^30)
theorem v3346_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 69 5) 1) 14) v3346_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3346 : Material (44 : Basis) (69 : Basis) where
  plus := ![v3346_pa,v3346_pb,v3346_pg]
  minus := ![(Primitive.Addresses.material3346 1).one,v3346_mb,v3346_mg]
  upper := v3346_upper
  lower := (Primitive.Addresses.material3346 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3346_pa_checked.trans (by decide +kernel)
    · exact v3346_pb_checked.trans (by decide +kernel)
    · exact v3346_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 69 Primitive.Addresses.material3346
    · exact v3346_mb_checked.trans (by decide +kernel)
    · exact v3346_mg_checked.trans (by decide +kernel)
  upper_error := v3346_upper_checked
  lower_error := reuse_lower_error 44 69 Primitive.Addresses.material3346

def v3347_pa : Scalar.QComplex := ((999998964634218788154085780359 : Int)/10^30,(-1439003297578358895410091977 : Int)/10^30)
theorem v3347_pa_checked : Scalar.distance (sourceCoefficient 44 70 1 0) v3347_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3347_pb : Scalar.QComplex := ((-620897556057597606753909 : Int)/10^30,(-431477060717231859422390165 : Int)/10^30)
theorem v3347_pb_checked : Scalar.distance (sourceCoefficient 44 70 1 1) v3347_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3347_pg : Scalar.QComplex := ((-93086332057234300467174 : Int)/10^30,(133951677478817456753 : Int)/10^30)
theorem v3347_pg_checked : Scalar.distance (sourceCoefficient 44 70 1 2) v3347_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3347_mb : Scalar.QComplex := ((-993242595262604527502153 : Int)/10^30,(-431476364251975988698971711 : Int)/10^30)
theorem v3347_mb_checked : Scalar.distance (sourceCoefficient 44 70 3 1) v3347_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3347_mg : Scalar.QComplex := ((-93086181802673915399534 : Int)/10^30,(214280939715114542903 : Int)/10^30)
theorem v3347_mg_checked : Scalar.distance (sourceCoefficient 44 70 3 2) v3347_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3347_upper : Scalar.QComplex := ((999994991664082834701685206414 : Int)/10^30,(-3164908648113233846110759441 : Int)/10^30)
theorem v3347_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 70 5) 1) 14) v3347_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3347 : Material (44 : Basis) (70 : Basis) where
  plus := ![v3347_pa,v3347_pb,v3347_pg]
  minus := ![(Primitive.Addresses.material3347 1).one,v3347_mb,v3347_mg]
  upper := v3347_upper
  lower := (Primitive.Addresses.material3347 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3347_pa_checked.trans (by decide +kernel)
    · exact v3347_pb_checked.trans (by decide +kernel)
    · exact v3347_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 70 Primitive.Addresses.material3347
    · exact v3347_mb_checked.trans (by decide +kernel)
    · exact v3347_mg_checked.trans (by decide +kernel)
  upper_error := v3347_upper_checked
  lower_error := reuse_lower_error 44 70 Primitive.Addresses.material3347

def v3348_pa : Scalar.QComplex := ((999998929381705568592965555999 : Int)/10^30,(-1463296088506793521003453866 : Int)/10^30)
theorem v3348_pa_checked : Scalar.distance (sourceCoefficient 44 71 1 0) v3348_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3348_pb : Scalar.QComplex := ((-631379346655417422275114 : Int)/10^30,(-431477043947696521485951330 : Int)/10^30)
theorem v3348_pb_checked : Scalar.distance (sourceCoefficient 44 71 1 1) v3348_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3348_pg : Scalar.QComplex := ((-93086328607549532484068 : Int)/10^30,(136213006377021833124 : Int)/10^30)
theorem v3348_pg_checked : Scalar.distance (sourceCoefficient 44 71 1 2) v3348_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3348_mb : Scalar.QComplex := ((-1003724367486220937155056 : Int)/10^30,(-431476338437133691232450211 : Int)/10^30)
theorem v3348_mb_checked : Scalar.distance (sourceCoefficient 44 71 3 1) v3348_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3348_mg : Scalar.QComplex := ((-93086176401565439214205 : Int)/10^30,(216542264794400235901 : Int)/10^30)
theorem v3348_mg_checked : Scalar.distance (sourceCoefficient 44 71 3 2) v3348_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3348_upper : Scalar.QComplex := ((999994914484468801917483824208 : Int)/10^30,(-3189201342017770281534624216 : Int)/10^30)
theorem v3348_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 71 5) 1) 14) v3348_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3348 : Material (44 : Basis) (71 : Basis) where
  plus := ![v3348_pa,v3348_pb,v3348_pg]
  minus := ![(Primitive.Addresses.material3348 1).one,v3348_mb,v3348_mg]
  upper := v3348_upper
  lower := (Primitive.Addresses.material3348 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3348_pa_checked.trans (by decide +kernel)
    · exact v3348_pb_checked.trans (by decide +kernel)
    · exact v3348_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 71 Primitive.Addresses.material3348
    · exact v3348_mb_checked.trans (by decide +kernel)
    · exact v3348_mg_checked.trans (by decide +kernel)
  upper_error := v3348_upper_checked
  lower_error := reuse_lower_error 44 71 Primitive.Addresses.material3348

def v3349_pa : Scalar.QComplex := ((999998890457884154988278129674 : Int)/10^30,(-1489658685943299096740884004 : Int)/10^30)
theorem v3349_pa_checked : Scalar.distance (sourceCoefficient 44 72 1 0) v3349_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3349_pb : Scalar.QComplex := ((-642754211783147745817324 : Int)/10^30,(-431477025365221663081400546 : Int)/10^30)
theorem v3349_pb_checked : Scalar.distance (sourceCoefficient 44 72 1 1) v3349_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3349_pg : Scalar.QComplex := ((-93086324791429606393801 : Int)/10^30,(138667006124975546624 : Int)/10^30)
theorem v3349_pg_checked : Scalar.distance (sourceCoefficient 44 72 1 2) v3349_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3349_mb : Scalar.QComplex := ((-1015099212342730237421902 : Int)/10^30,(-431476310038669451608981917 : Int)/10^30)
theorem v3349_mb_checked : Scalar.distance (sourceCoefficient 44 72 3 1) v3349_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3349_mg : Scalar.QComplex := ((-93086170467755675601540 : Int)/10^30,(218996260335478065355 : Int)/10^30)
theorem v3349_mg_checked : Scalar.distance (sourceCoefficient 44 72 3 2) v3349_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3349_upper : Scalar.QComplex := ((999994830061253781521170838316 : Int)/10^30,(-3215563833011299125441182838 : Int)/10^30)
theorem v3349_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 72 5) 1) 14) v3349_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3349 : Material (44 : Basis) (72 : Basis) where
  plus := ![v3349_pa,v3349_pb,v3349_pg]
  minus := ![(Primitive.Addresses.material3349 1).one,v3349_mb,v3349_mg]
  upper := v3349_upper
  lower := (Primitive.Addresses.material3349 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3349_pa_checked.trans (by decide +kernel)
    · exact v3349_pb_checked.trans (by decide +kernel)
    · exact v3349_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 72 Primitive.Addresses.material3349
    · exact v3349_mb_checked.trans (by decide +kernel)
    · exact v3349_mg_checked.trans (by decide +kernel)
  upper_error := v3349_upper_checked
  lower_error := reuse_lower_error 44 72 Primitive.Addresses.material3349

def v3350_pa : Scalar.QComplex := ((999998876336494108638355327164 : Int)/10^30,(-1499108318022099701697158537 : Int)/10^30)
theorem v3350_pa_checked : Scalar.distance (sourceCoefficient 44 73 1 0) v3350_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3350_pb : Scalar.QComplex := ((-646831514450123154928859 : Int)/10^30,(-431477018607017290583888029 : Int)/10^30)
theorem v3350_pb_checked : Scalar.distance (sourceCoefficient 44 73 1 1) v3350_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3350_pg : Scalar.QComplex := ((-93086323405171362994697 : Int)/10^30,(139546638514252722740 : Int)/10^30)
theorem v3350_pg_checked : Scalar.distance (sourceCoefficient 44 73 1 2) v3350_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3350_mb : Scalar.QComplex := ((-1019176507659513526441666 : Int)/10^30,(-431476299761939028795317247 : Int)/10^30)
theorem v3350_mb_checked : Scalar.distance (sourceCoefficient 44 73 3 1) v3350_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3350_mg : Scalar.QComplex := ((-93086168322414813595687 : Int)/10^30,(219875891200949472457 : Int)/10^30)
theorem v3350_mg_checked : Scalar.distance (sourceCoefficient 44 73 3 2) v3350_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3350_upper : Scalar.QComplex := ((999994799630677063238673420699 : Int)/10^30,(-3225013426643744643281181229 : Int)/10^30)
theorem v3350_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 73 5) 1) 14) v3350_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3350 : Material (44 : Basis) (73 : Basis) where
  plus := ![v3350_pa,v3350_pb,v3350_pg]
  minus := ![(Primitive.Addresses.material3350 1).one,v3350_mb,v3350_mg]
  upper := v3350_upper
  lower := (Primitive.Addresses.material3350 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3350_pa_checked.trans (by decide +kernel)
    · exact v3350_pb_checked.trans (by decide +kernel)
    · exact v3350_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 73 Primitive.Addresses.material3350
    · exact v3350_mb_checked.trans (by decide +kernel)
    · exact v3350_mg_checked.trans (by decide +kernel)
  upper_error := v3350_upper_checked
  lower_error := reuse_lower_error 44 73 Primitive.Addresses.material3350

def v3351_pa : Scalar.QComplex := ((999998860339687309380586180611 : Int)/10^30,(-1509741476728916825832451515 : Int)/10^30)
theorem v3351_pa_checked : Scalar.distance (sourceCoefficient 44 74 1 0) v3351_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3351_pb : Scalar.QComplex := ((-651419482069499440591962 : Int)/10^30,(-431477010940949971801749510 : Int)/10^30)
theorem v3351_pb_checked : Scalar.distance (sourceCoefficient 44 74 1 1) v3351_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3351_pg : Scalar.QComplex := ((-93086321833694576608000 : Int)/10^30,(140536441152269730883 : Int)/10^30)
theorem v3351_pg_checked : Scalar.distance (sourceCoefficient 44 74 1 2) v3351_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3351_mb : Scalar.QComplex := ((-1023764466955108957678491 : Int)/10^30,(-431476288136665143309611122 : Int)/10^30)
theorem v3351_mb_checked : Scalar.distance (sourceCoefficient 44 74 3 1) v3351_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3351_mg : Scalar.QComplex := ((-93086165896783514788902 : Int)/10^30,(220865692114304032287 : Int)/10^30)
theorem v3351_mg_checked : Scalar.distance (sourceCoefficient 44 74 3 2) v3351_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3351_upper : Scalar.QComplex := ((999994765282026794001744510483 : Int)/10^30,(-3235646541904683615633267653 : Int)/10^30)
theorem v3351_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 74 5) 1) 14) v3351_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3351 : Material (44 : Basis) (74 : Basis) where
  plus := ![v3351_pa,v3351_pb,v3351_pg]
  minus := ![(Primitive.Addresses.material3351 1).one,v3351_mb,v3351_mg]
  upper := v3351_upper
  lower := (Primitive.Addresses.material3351 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3351_pa_checked.trans (by decide +kernel)
    · exact v3351_pb_checked.trans (by decide +kernel)
    · exact v3351_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 74 Primitive.Addresses.material3351
    · exact v3351_mb_checked.trans (by decide +kernel)
    · exact v3351_mg_checked.trans (by decide +kernel)
  upper_error := v3351_upper_checked
  lower_error := reuse_lower_error 44 74 Primitive.Addresses.material3351

def v3352_pa : Scalar.QComplex := ((999998837862928766761857722369 : Int)/10^30,(-1524556588619754694734473671 : Int)/10^30)
theorem v3352_pa_checked : Scalar.distance (sourceCoefficient 44 75 1 0) v3352_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3352_pb : Scalar.QComplex := ((-657811867886287361338475 : Int)/10^30,(-431477000151417073532014653 : Int)/10^30)
theorem v3352_pb_checked : Scalar.distance (sourceCoefficient 44 75 1 1) v3352_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3352_pg : Scalar.QComplex := ((-93086319623693691385015 : Int)/10^30,(141915526817961280445 : Int)/10^30)
theorem v3352_pg_checked : Scalar.distance (sourceCoefficient 44 75 1 2) v3352_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3352_mb : Scalar.QComplex := ((-1030156841080838543686628 : Int)/10^30,(-431476271830795204957854496 : Int)/10^30)
theorem v3352_mb_checked : Scalar.distance (sourceCoefficient 44 75 3 1) v3352_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3352_mg : Scalar.QComplex := ((-93086162496694634671129 : Int)/10^30,(222244775359367731980 : Int)/10^30)
theorem v3352_mg_checked : Scalar.distance (sourceCoefficient 44 75 3 2) v3352_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3352_upper : Scalar.QComplex := ((999994717235762620740254479411 : Int)/10^30,(-3250461592937306459471437545 : Int)/10^30)
theorem v3352_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 75 5) 1) 14) v3352_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3352 : Material (44 : Basis) (75 : Basis) where
  plus := ![v3352_pa,v3352_pb,v3352_pg]
  minus := ![(Primitive.Addresses.material3352 1).one,v3352_mb,v3352_mg]
  upper := v3352_upper
  lower := (Primitive.Addresses.material3352 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3352_pa_checked.trans (by decide +kernel)
    · exact v3352_pb_checked.trans (by decide +kernel)
    · exact v3352_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 75 Primitive.Addresses.material3352
    · exact v3352_mb_checked.trans (by decide +kernel)
    · exact v3352_mg_checked.trans (by decide +kernel)
  upper_error := v3352_upper_checked
  lower_error := reuse_lower_error 44 75 Primitive.Addresses.material3352

def v3353_pa : Scalar.QComplex := ((999998818835153716735080876853 : Int)/10^30,(-1536986759024337119834894139 : Int)/10^30)
theorem v3353_pa_checked : Scalar.distance (sourceCoefficient 44 76 1 0) v3353_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3353_pb : Scalar.QComplex := ((-663175205312007073631047 : Int)/10^30,(-431476991001369274102874259 : Int)/10^30)
theorem v3353_pb_checked : Scalar.distance (sourceCoefficient 44 76 1 1) v3353_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3353_pg : Scalar.QComplex := ((-93086317751069835927088 : Int)/10^30,(143072606822060093099 : Int)/10^30)
theorem v3353_pg_checked : Scalar.distance (sourceCoefficient 44 76 1 2) v3353_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3353_mb : Scalar.QComplex := ((-1035520168613463467701950 : Int)/10^30,(-431476258052432169864259418 : Int)/10^30)
theorem v3353_mb_checked : Scalar.distance (sourceCoefficient 44 76 3 1) v3353_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3353_mg : Scalar.QComplex := ((-93086159625563545888233 : Int)/10^30,(223401853316642730527 : Int)/10^30)
theorem v3353_mg_checked : Scalar.distance (sourceCoefficient 44 76 3 2) v3353_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3353_upper : Scalar.QComplex := ((999994676754669448290325957638 : Int)/10^30,(-3262891711988396667254122812 : Int)/10^30)
theorem v3353_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 76 5) 1) 14) v3353_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3353 : Material (44 : Basis) (76 : Basis) where
  plus := ![v3353_pa,v3353_pb,v3353_pg]
  minus := ![(Primitive.Addresses.material3353 1).one,v3353_mb,v3353_mg]
  upper := v3353_upper
  lower := (Primitive.Addresses.material3353 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3353_pa_checked.trans (by decide +kernel)
    · exact v3353_pb_checked.trans (by decide +kernel)
    · exact v3353_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 76 Primitive.Addresses.material3353
    · exact v3353_mb_checked.trans (by decide +kernel)
    · exact v3353_mg_checked.trans (by decide +kernel)
  upper_error := v3353_upper_checked
  lower_error := reuse_lower_error 44 76 Primitive.Addresses.material3353

def v3354_pa : Scalar.QComplex := ((999998814408036460412237109335 : Int)/10^30,(-1539864449050912895360810683 : Int)/10^30)
theorem v3354_pa_checked : Scalar.distance (sourceCoefficient 44 77 1 0) v3354_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3354_pb : Scalar.QComplex := ((-664416863472334557106111 : Int)/10^30,(-431476988870384032966152570 : Int)/10^30)
theorem v3354_pb_checked : Scalar.distance (sourceCoefficient 44 77 1 1) v3354_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3354_pg : Scalar.QComplex := ((-93086317315149497877223 : Int)/10^30,(143340480669993067080 : Int)/10^30)
theorem v3354_pg_checked : Scalar.distance (sourceCoefficient 44 77 1 2) v3354_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3354_mb : Scalar.QComplex := ((-1036761824472520584417300 : Int)/10^30,(-431476254849952652035726825 : Int)/10^30)
theorem v3354_mb_checked : Scalar.distance (sourceCoefficient 44 77 3 1) v3354_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3354_mg : Scalar.QComplex := ((-93086158958480303975528 : Int)/10^30,(223669726688654409869 : Int)/10^30)
theorem v3354_mg_checked : Scalar.distance (sourceCoefficient 44 77 3 2) v3354_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3354_upper : Scalar.QComplex := ((999994667360926861768707725948 : Int)/10^30,(-3265769390088188425938706020 : Int)/10^30)
theorem v3354_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 77 5) 1) 14) v3354_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3354 : Material (44 : Basis) (77 : Basis) where
  plus := ![v3354_pa,v3354_pb,v3354_pg]
  minus := ![(Primitive.Addresses.material3354 1).one,v3354_mb,v3354_mg]
  upper := v3354_upper
  lower := (Primitive.Addresses.material3354 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3354_pa_checked.trans (by decide +kernel)
    · exact v3354_pb_checked.trans (by decide +kernel)
    · exact v3354_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 77 Primitive.Addresses.material3354
    · exact v3354_mb_checked.trans (by decide +kernel)
    · exact v3354_mg_checked.trans (by decide +kernel)
  upper_error := v3354_upper_checked
  lower_error := reuse_lower_error 44 77 Primitive.Addresses.material3354

def v3355_pa : Scalar.QComplex := ((999998787619376271285614961189 : Int)/10^30,(-1557164017562264369333597280 : Int)/10^30)
theorem v3355_pa_checked : Scalar.distance (sourceCoefficient 44 78 1 0) v3355_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3355_pb : Scalar.QComplex := ((-671881235946209009864908 : Int)/10^30,(-431476975959310888706968460 : Int)/10^30)
theorem v3355_pb_checked : Scalar.distance (sourceCoefficient 44 78 1 1) v3355_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3355_pg : Scalar.QComplex := ((-93086314675609605176788 : Int)/10^30,(144950835475921747032 : Int)/10^30)
theorem v3355_pg_checked : Scalar.distance (sourceCoefficient 44 78 1 2) v3355_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3355_mb : Scalar.QComplex := ((-1044226183025393396130691 : Int)/10^30,(-431476235497467053062015843 : Int)/10^30)
theorem v3355_mb_checked : Scalar.distance (sourceCoefficient 44 78 3 1) v3355_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3355_mg : Scalar.QComplex := ((-93086154929277724268082 : Int)/10^30,(225280078617170351787 : Int)/10^30)
theorem v3355_mg_checked : Scalar.distance (sourceCoefficient 44 78 3 2) v3355_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3355_upper : Scalar.QComplex := ((999994610714820725207810012793 : Int)/10^30,(-3283068886599067514157322007 : Int)/10^30)
theorem v3355_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 78 5) 1) 14) v3355_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3355 : Material (44 : Basis) (78 : Basis) where
  plus := ![v3355_pa,v3355_pb,v3355_pg]
  minus := ![(Primitive.Addresses.material3355 1).one,v3355_mb,v3355_mg]
  upper := v3355_upper
  lower := (Primitive.Addresses.material3355 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3355_pa_checked.trans (by decide +kernel)
    · exact v3355_pb_checked.trans (by decide +kernel)
    · exact v3355_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 78 Primitive.Addresses.material3355
    · exact v3355_mb_checked.trans (by decide +kernel)
    · exact v3355_mg_checked.trans (by decide +kernel)
  upper_error := v3355_upper_checked
  lower_error := reuse_lower_error 44 78 Primitive.Addresses.material3355

def v3356_pa : Scalar.QComplex := ((999998778919394408464842732431 : Int)/10^30,(-1562741091846382902536903107 : Int)/10^30)
theorem v3356_pa_checked : Scalar.distance (sourceCoefficient 44 79 1 0) v3356_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3356_pb : Scalar.QComplex := ((-674287617314809346631805 : Int)/10^30,(-431476971760309668119411452 : Int)/10^30)
theorem v3356_pb_checked : Scalar.distance (sourceCoefficient 44 79 1 1) v3356_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3356_pg : Scalar.QComplex := ((-93086313817740798825662 : Int)/10^30,(145469985322069068051 : Int)/10^30)
theorem v3356_pg_checked : Scalar.distance (sourceCoefficient 44 79 1 2) v3356_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3356_mb : Scalar.QComplex := ((-1046632559874439034933759 : Int)/10^30,(-431476229221868654246036020 : Int)/10^30)
theorem v3356_mb_checked : Scalar.distance (sourceCoefficient 44 79 3 1) v3356_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3356_mg : Scalar.QComplex := ((-93086153623406301756684 : Int)/10^30,(225799227529712315861 : Int)/10^30)
theorem v3356_mg_checked : Scalar.distance (sourceCoefficient 44 79 3 2) v3356_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3356_upper : Scalar.QComplex := ((999994592389327553826267066162 : Int)/10^30,(-3288645937561409591292410293 : Int)/10^30)
theorem v3356_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 79 5) 1) 14) v3356_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3356 : Material (44 : Basis) (79 : Basis) where
  plus := ![v3356_pa,v3356_pb,v3356_pg]
  minus := ![(Primitive.Addresses.material3356 1).one,v3356_mb,v3356_mg]
  upper := v3356_upper
  lower := (Primitive.Addresses.material3356 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3356_pa_checked.trans (by decide +kernel)
    · exact v3356_pb_checked.trans (by decide +kernel)
    · exact v3356_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 79 Primitive.Addresses.material3356
    · exact v3356_mb_checked.trans (by decide +kernel)
    · exact v3356_mg_checked.trans (by decide +kernel)
  upper_error := v3356_upper_checked
  lower_error := reuse_lower_error 44 79 Primitive.Addresses.material3356

def v3357_pa : Scalar.QComplex := ((999998765266920211149222783766 : Int)/10^30,(-1571453033027689068252019879 : Int)/10^30)
theorem v3357_pa_checked : Scalar.distance (sourceCoefficient 44 80 1 0) v3357_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3357_pb : Scalar.QComplex := ((-678046622797103743635945 : Int)/10^30,(-431476965165246362028057694 : Int)/10^30)
theorem v3357_pb_checked : Scalar.distance (sourceCoefficient 44 80 1 1) v3357_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3357_pg : Scalar.QComplex := ((-93086312470905332938534 : Int)/10^30,(146280948683693665613 : Int)/10^30)
theorem v3357_pg_checked : Scalar.distance (sourceCoefficient 44 80 1 2) v3357_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3357_mb : Scalar.QComplex := ((-1050391558265841293310480 : Int)/10^30,(-431476219382955371900332072 : Int)/10^30)
theorem v3357_mb_checked : Scalar.distance (sourceCoefficient 44 80 3 1) v3357_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3357_mg : Scalar.QComplex := ((-93086151576746480709882 : Int)/10^30,(226610189427119843191 : Int)/10^30)
theorem v3357_mg_checked : Scalar.distance (sourceCoefficient 44 80 3 2) v3357_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3357_upper : Scalar.QComplex := ((999994563700853552462951714632 : Int)/10^30,(-3297357842204370822168882804 : Int)/10^30)
theorem v3357_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 80 5) 1) 14) v3357_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3357 : Material (44 : Basis) (80 : Basis) where
  plus := ![v3357_pa,v3357_pb,v3357_pg]
  minus := ![(Primitive.Addresses.material3357 1).one,v3357_mb,v3357_mg]
  upper := v3357_upper
  lower := (Primitive.Addresses.material3357 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3357_pa_checked.trans (by decide +kernel)
    · exact v3357_pb_checked.trans (by decide +kernel)
    · exact v3357_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 80 Primitive.Addresses.material3357
    · exact v3357_mb_checked.trans (by decide +kernel)
    · exact v3357_mg_checked.trans (by decide +kernel)
  upper_error := v3357_upper_checked
  lower_error := reuse_lower_error 44 80 Primitive.Addresses.material3357

def v3358_pa : Scalar.QComplex := ((999998723700282994463978027122 : Int)/10^30,(-1597685139528469300062488782 : Int)/10^30)
theorem v3358_pa_checked : Scalar.distance (sourceCoefficient 44 81 1 0) v3358_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3358_pb : Scalar.QComplex := ((-689365182981714751834040 : Int)/10^30,(-431476945043490499451726680 : Int)/10^30)
theorem v3358_pb_checked : Scalar.distance (sourceCoefficient 44 81 1 1) v3358_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3358_pg : Scalar.QComplex := ((-93086308365738966365454 : Int)/10^30,(148722801384375098691 : Int)/10^30)
theorem v3358_pg_checked : Scalar.distance (sourceCoefficient 44 81 1 2) v3358_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3358_mb : Scalar.QComplex := ((-1061710096871866001862210 : Int)/10^30,(-431476189493799331281217376 : Int)/10^30)
theorem v3358_mb_checked : Scalar.distance (sourceCoefficient 44 81 3 1) v3358_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3358_mg : Scalar.QComplex := ((-93086145364372738952881 : Int)/10^30,(229052037676014233101 : Int)/10^30)
theorem v3358_mg_checked : Scalar.distance (sourceCoefficient 44 81 3 2) v3358_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3358_upper : Scalar.QComplex := ((999994476860042182166501484118 : Int)/10^30,(-3323589837895264920629053422 : Int)/10^30)
theorem v3358_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 81 5) 1) 14) v3358_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3358 : Material (44 : Basis) (81 : Basis) where
  plus := ![v3358_pa,v3358_pb,v3358_pg]
  minus := ![(Primitive.Addresses.material3358 1).one,v3358_mb,v3358_mg]
  upper := v3358_upper
  lower := (Primitive.Addresses.material3358 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3358_pa_checked.trans (by decide +kernel)
    · exact v3358_pb_checked.trans (by decide +kernel)
    · exact v3358_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 81 Primitive.Addresses.material3358
    · exact v3358_mb_checked.trans (by decide +kernel)
    · exact v3358_mg_checked.trans (by decide +kernel)
  upper_error := v3358_upper_checked
  lower_error := reuse_lower_error 44 81 Primitive.Addresses.material3358

def v3359_pa : Scalar.QComplex := ((999998707769474750032059515012 : Int)/10^30,(-1607625385666762072719252429 : Int)/10^30)
theorem v3359_pa_checked : Scalar.distance (sourceCoefficient 44 82 1 0) v3359_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3359_pb : Scalar.QComplex := ((-693654174118819213620316 : Int)/10^30,(-431476937315237152199474061 : Int)/10^30)
theorem v3359_pb_checked : Scalar.distance (sourceCoefficient 44 82 1 1) v3359_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3359_pg : Scalar.QComplex := ((-93086306790625995917419 : Int)/10^30,(149648103234421695213 : Int)/10^30)
theorem v3359_pg_checked : Scalar.distance (sourceCoefficient 44 82 1 2) v3359_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3359_mb : Scalar.QComplex := ((-1065999079742848475657302 : Int)/10^30,(-431476178064342679279779253 : Int)/10^30)
theorem v3359_mb_checked : Scalar.distance (sourceCoefficient 44 82 3 1) v3359_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3359_mg : Scalar.QComplex := ((-93086142990766532449492 : Int)/10^30,(229977337822277109425 : Int)/10^30)
theorem v3359_mg_checked : Scalar.distance (sourceCoefficient 44 82 3 2) v3359_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3359_upper : Scalar.QComplex := ((999994443773294602194182221831 : Int)/10^30,(-3333530041733598935378925200 : Int)/10^30)
theorem v3359_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 82 5) 1) 14) v3359_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3359 : Material (44 : Basis) (82 : Basis) where
  plus := ![v3359_pa,v3359_pb,v3359_pg]
  minus := ![(Primitive.Addresses.material3359 1).one,v3359_mb,v3359_mg]
  upper := v3359_upper
  lower := (Primitive.Addresses.material3359 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3359_pa_checked.trans (by decide +kernel)
    · exact v3359_pb_checked.trans (by decide +kernel)
    · exact v3359_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 82 Primitive.Addresses.material3359
    · exact v3359_mb_checked.trans (by decide +kernel)
    · exact v3359_mg_checked.trans (by decide +kernel)
  upper_error := v3359_upper_checked
  lower_error := reuse_lower_error 44 82 Primitive.Addresses.material3359

def v3360_pa : Scalar.QComplex := ((999998685864161857492289697441 : Int)/10^30,(-1621193988803318481541450104 : Int)/10^30)
theorem v3360_pa_checked : Scalar.distance (sourceCoefficient 44 83 1 0) v3360_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3360_pb : Scalar.QComplex := ((-699508719081158431190489 : Int)/10^30,(-431476926674285325516652299 : Int)/10^30)
theorem v3360_pb_checked : Scalar.distance (sourceCoefficient 44 83 1 1) v3360_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3360_pg : Scalar.QComplex := ((-93086304623249376811888 : Int)/10^30,(150911155812884672814 : Int)/10^30)
theorem v3360_pg_checked : Scalar.distance (sourceCoefficient 44 83 1 2) v3360_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3360_mb : Scalar.QComplex := ((-1071853613342610862078159 : Int)/10^30,(-431476162371186191127775589 : Int)/10^30)
theorem v3360_mb_checked : Scalar.distance (sourceCoefficient 44 83 3 1) v3360_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3360_mg : Scalar.QComplex := ((-93086139733433230920215 : Int)/10^30,(231240388060099480441 : Int)/10^30)
theorem v3360_mg_checked : Scalar.distance (sourceCoefficient 44 83 3 2) v3360_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3360_upper : Scalar.QComplex := ((999994398449836255409444604322 : Int)/10^30,(-3347098586854732034327286164 : Int)/10^30)
theorem v3360_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 83 5) 1) 14) v3360_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3360 : Material (44 : Basis) (83 : Basis) where
  plus := ![v3360_pa,v3360_pb,v3360_pg]
  minus := ![(Primitive.Addresses.material3360 1).one,v3360_mb,v3360_mg]
  upper := v3360_upper
  lower := (Primitive.Addresses.material3360 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3360_pa_checked.trans (by decide +kernel)
    · exact v3360_pb_checked.trans (by decide +kernel)
    · exact v3360_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 83 Primitive.Addresses.material3360
    · exact v3360_mb_checked.trans (by decide +kernel)
    · exact v3360_mg_checked.trans (by decide +kernel)
  upper_error := v3360_upper_checked
  lower_error := reuse_lower_error 44 83 Primitive.Addresses.material3360

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
