import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B100
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B101

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2417_pa : Scalar.QComplex := ((999999732001990691722467974258 : Int)/10^30,(-732117440574681345196212347 : Int)/10^30)
theorem v2417_pa_checked : Scalar.distance (sourceCoefficient 29 40 1 0) v2417_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2417_pb : Scalar.QComplex := ((-315892216674903974636072 : Int)/10^30,(-431477403090488781899422012 : Int)/10^30)
theorem v2417_pb_checked : Scalar.distance (sourceCoefficient 29 40 1 1) v2417_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2417_pg : Scalar.QComplex := ((-93086404704590203230313 : Int)/10^30,(68150198628741122579 : Int)/10^30)
theorem v2417_pg_checked : Scalar.distance (sourceCoefficient 29 40 1 2) v2417_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2417_mb : Scalar.QComplex := ((-688237664900038985213081 : Int)/10^30,(-431476969830976386682860273 : Int)/10^30)
theorem v2417_mb_checked : Scalar.distance (sourceCoefficient 29 40 3 1) v2417_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2417_mg : Scalar.QComplex := ((-93086311233715427253971 : Int)/10^30,(148479548057332289393 : Int)/10^30)
theorem v2417_mg_checked : Scalar.distance (sourceCoefficient 29 40 3 2) v2417_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2417_upper : Scalar.QComplex := ((999996979051572838457128215610 : Int)/10^30,(-2458025168340162902199659634 : Int)/10^30)
theorem v2417_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 40 5) 1) 14) v2417_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2417 : Material (29 : Basis) (40 : Basis) where
  plus := ![v2417_pa,v2417_pb,v2417_pg]
  minus := ![(Primitive.Addresses.material2417 1).one,v2417_mb,v2417_mg]
  upper := v2417_upper
  lower := (Primitive.Addresses.material2417 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2417_pa_checked.trans (by decide +kernel)
    · exact v2417_pb_checked.trans (by decide +kernel)
    · exact v2417_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 40 Primitive.Addresses.material2417
    · exact v2417_mb_checked.trans (by decide +kernel)
    · exact v2417_mg_checked.trans (by decide +kernel)
  upper_error := v2417_upper_checked
  lower_error := reuse_lower_error 29 40 Primitive.Addresses.material2417

def v2418_pa : Scalar.QComplex := ((999999721293112795431795674739 : Int)/10^30,(-746601430973452818355174710 : Int)/10^30)
theorem v2418_pa_checked : Scalar.distance (sourceCoefficient 29 41 1 0) v2418_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2418_pb : Scalar.QComplex := ((-322141732625513686389997 : Int)/10^30,(-431477398084237875656259938 : Int)/10^30)
theorem v2418_pb_checked : Scalar.distance (sourceCoefficient 29 41 1 1) v2418_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2418_pg : Scalar.QComplex := ((-93086403666143390018171 : Int)/10^30,(69498461551015003962 : Int)/10^30)
theorem v2418_pg_checked : Scalar.distance (sourceCoefficient 29 41 1 2) v2418_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2418_mb : Scalar.QComplex := ((-694487174203499232649312 : Int)/10^30,(-431476959431676546869367766 : Int)/10^30)
theorem v2418_mb_checked : Scalar.distance (sourceCoefficient 29 41 3 1) v2418_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2418_mg : Scalar.QComplex := ((-93086309031778822288534 : Int)/10^30,(149827809581453436259 : Int)/10^30)
theorem v2418_mg_checked : Scalar.distance (sourceCoefficient 29 41 3 2) v2418_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2418_upper : Scalar.QComplex := ((999996943344657440847315419762 : Int)/10^30,(-2472509118684180338234313502 : Int)/10^30)
theorem v2418_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 41 5) 1) 14) v2418_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2418 : Material (29 : Basis) (41 : Basis) where
  plus := ![v2418_pa,v2418_pb,v2418_pg]
  minus := ![(Primitive.Addresses.material2418 1).one,v2418_mb,v2418_mg]
  upper := v2418_upper
  lower := (Primitive.Addresses.material2418 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2418_pa_checked.trans (by decide +kernel)
    · exact v2418_pb_checked.trans (by decide +kernel)
    · exact v2418_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 41 Primitive.Addresses.material2418
    · exact v2418_mb_checked.trans (by decide +kernel)
    · exact v2418_mg_checked.trans (by decide +kernel)
  upper_error := v2418_upper_checked
  lower_error := reuse_lower_error 29 41 Primitive.Addresses.material2418

def v2419_pa : Scalar.QComplex := ((999999712501829208857837168971 : Int)/10^30,(-758285077610713711854003240 : Int)/10^30)
theorem v2419_pa_checked : Scalar.distance (sourceCoefficient 29 42 1 0) v2419_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2419_pb : Scalar.QComplex := ((-327182963229178980276422 : Int)/10^30,(-431477393957953859372579504 : Int)/10^30)
theorem v2419_pb_checked : Scalar.distance (sourceCoefficient 29 42 1 1) v2419_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2419_pg : Scalar.QComplex := ((-93086402811869068373433 : Int)/10^30,(70586050474060690274 : Int)/10^30)
theorem v2419_pg_checked : Scalar.distance (sourceCoefficient 29 42 1 2) v2419_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2419_mb : Scalar.QComplex := ((-699528399369286712051324 : Int)/10^30,(-431476950955039104624607413 : Int)/10^30)
theorem v2419_mb_checked : Scalar.distance (sourceCoefficient 29 42 3 1) v2419_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2419_mg : Scalar.QComplex := ((-93086307238964561327493 : Int)/10^30,(150915397362339796760 : Int)/10^30)
theorem v2419_mg_checked : Scalar.distance (sourceCoefficient 29 42 3 2) v2419_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2419_upper : Scalar.QComplex := ((999996914388472784088457008031 : Int)/10^30,(-2484192732747064091667226653 : Int)/10^30)
theorem v2419_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 42 5) 1) 14) v2419_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2419 : Material (29 : Basis) (42 : Basis) where
  plus := ![v2419_pa,v2419_pb,v2419_pg]
  minus := ![(Primitive.Addresses.material2419 1).one,v2419_mb,v2419_mg]
  upper := v2419_upper
  lower := (Primitive.Addresses.material2419 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2419_pa_checked.trans (by decide +kernel)
    · exact v2419_pb_checked.trans (by decide +kernel)
    · exact v2419_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 42 Primitive.Addresses.material2419
    · exact v2419_mb_checked.trans (by decide +kernel)
    · exact v2419_mg_checked.trans (by decide +kernel)
  upper_error := v2419_upper_checked
  lower_error := reuse_lower_error 29 42 Primitive.Addresses.material2419

def v2420_pa : Scalar.QComplex := ((999999700645472223938690035187 : Int)/10^30,(-773762861566119183756270587 : Int)/10^30)
theorem v2420_pa_checked : Scalar.distance (sourceCoefficient 29 43 1 0) v2420_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2420_pb : Scalar.QComplex := ((-333861278669732383089443 : Int)/10^30,(-431477388370775445225129029 : Int)/10^30)
theorem v2420_pb_checked : Scalar.distance (sourceCoefficient 29 43 1 1) v2420_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2420_pg : Scalar.QComplex := ((-93086401657350596183484 : Int)/10^30,(72026822080840047928 : Int)/10^30)
theorem v2420_pg_checked : Scalar.distance (sourceCoefficient 29 43 1 2) v2420_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2420_mb : Scalar.QComplex := ((-706206707501714728018111 : Int)/10^30,(-431476939604777325803398641 : Int)/10^30)
theorem v2420_mb_checked : Scalar.distance (sourceCoefficient 29 43 3 1) v2420_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2420_mg : Scalar.QComplex := ((-93086304841125512311292 : Int)/10^30,(152356167436356594777 : Int)/10^30)
theorem v2420_mg_checked : Scalar.distance (sourceCoefficient 29 43 3 2) v2420_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2420_upper : Scalar.QComplex := ((999996875818882484382393578724 : Int)/10^30,(-2499670473187131954547487588 : Int)/10^30)
theorem v2420_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 43 5) 1) 14) v2420_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2420 : Material (29 : Basis) (43 : Basis) where
  plus := ![v2420_pa,v2420_pb,v2420_pg]
  minus := ![(Primitive.Addresses.material2420 1).one,v2420_mb,v2420_mg]
  upper := v2420_upper
  lower := (Primitive.Addresses.material2420 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2420_pa_checked.trans (by decide +kernel)
    · exact v2420_pb_checked.trans (by decide +kernel)
    · exact v2420_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 43 Primitive.Addresses.material2420
    · exact v2420_mb_checked.trans (by decide +kernel)
    · exact v2420_mg_checked.trans (by decide +kernel)
  upper_error := v2420_upper_checked
  lower_error := reuse_lower_error 29 43 Primitive.Addresses.material2420

def v2421_pa : Scalar.QComplex := ((999999696097342507810376342756 : Int)/10^30,(-779618639225329204480831165 : Int)/10^30)
theorem v2421_pa_checked : Scalar.distance (sourceCoefficient 29 44 1 0) v2421_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2421_pb : Scalar.QComplex := ((-336387914931313953098505 : Int)/10^30,(-431477386221019019309170418 : Int)/10^30)
theorem v2421_pb_checked : Scalar.distance (sourceCoefficient 29 44 1 1) v2421_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2421_pg : Scalar.QComplex := ((-93086401213773113201494 : Int)/10^30,(72571915499462806888 : Int)/10^30)
theorem v2421_pg_checked : Scalar.distance (sourceCoefficient 29 44 1 2) v2421_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2421_mb : Scalar.QComplex := ((-708733340967371170728488 : Int)/10^30,(-431476935274648402068046318 : Int)/10^30)
theorem v2421_mb_checked : Scalar.distance (sourceCoefficient 29 44 3 1) v2421_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2421_mg : Scalar.QComplex := ((-93086303927157124318262 : Int)/10^30,(152901260269228772158 : Int)/10^30)
theorem v2421_mg_checked : Scalar.distance (sourceCoefficient 29 44 3 2) v2421_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2421_upper : Scalar.QComplex := ((999996861164218534362022327648 : Int)/10^30,(-2505526234275189732909961274 : Int)/10^30)
theorem v2421_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 44 5) 1) 14) v2421_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2421 : Material (29 : Basis) (44 : Basis) where
  plus := ![v2421_pa,v2421_pb,v2421_pg]
  minus := ![(Primitive.Addresses.material2421 1).one,v2421_mb,v2421_mg]
  upper := v2421_upper
  lower := (Primitive.Addresses.material2421 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2421_pa_checked.trans (by decide +kernel)
    · exact v2421_pb_checked.trans (by decide +kernel)
    · exact v2421_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 44 Primitive.Addresses.material2421
    · exact v2421_mb_checked.trans (by decide +kernel)
    · exact v2421_mg_checked.trans (by decide +kernel)
  upper_error := v2421_upper_checked
  lower_error := reuse_lower_error 29 44 Primitive.Addresses.material2421

def v2422_pa : Scalar.QComplex := ((999999693821817525096864360527 : Int)/10^30,(-782531961778384389872851785 : Int)/10^30)
theorem v2422_pa_checked : Scalar.distance (sourceCoefficient 29 45 1 0) v2422_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2422_pb : Scalar.QComplex := ((-337644948039367626897781 : Int)/10^30,(-431477385144139631111804751 : Int)/10^30)
theorem v2422_pb_checked : Scalar.distance (sourceCoefficient 29 45 1 1) v2422_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2422_pg : Scalar.QComplex := ((-93086400991700547272662 : Int)/10^30,(72843106285894663865 : Int)/10^30)
theorem v2422_pg_checked : Scalar.distance (sourceCoefficient 29 45 1 2) v2422_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2422_mb : Scalar.QComplex := ((-709990372678075557981175 : Int)/10^30,(-431476933113006457261323622 : Int)/10^30)
theorem v2422_mb_checked : Scalar.distance (sourceCoefficient 29 45 3 1) v2422_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2422_mg : Scalar.QComplex := ((-93086303471059206366120 : Int)/10^30,(153172450763045282696 : Int)/10^30)
theorem v2422_mg_checked : Scalar.distance (sourceCoefficient 29 45 3 2) v2422_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2422_upper : Scalar.QComplex := ((999996853860566508759877552222 : Int)/10^30,(-2508439548561843512283549225 : Int)/10^30)
theorem v2422_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 45 5) 1) 14) v2422_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2422 : Material (29 : Basis) (45 : Basis) where
  plus := ![v2422_pa,v2422_pb,v2422_pg]
  minus := ![(Primitive.Addresses.material2422 1).one,v2422_mb,v2422_mg]
  upper := v2422_upper
  lower := (Primitive.Addresses.material2422 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2422_pa_checked.trans (by decide +kernel)
    · exact v2422_pb_checked.trans (by decide +kernel)
    · exact v2422_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 45 Primitive.Addresses.material2422
    · exact v2422_mb_checked.trans (by decide +kernel)
    · exact v2422_mg_checked.trans (by decide +kernel)
  upper_error := v2422_upper_checked
  lower_error := reuse_lower_error 29 45 Primitive.Addresses.material2422

def v2423_pa : Scalar.QComplex := ((999999680882379975252010805886 : Int)/10^30,(-798896199899236326395491308 : Int)/10^30)
theorem v2423_pa_checked : Scalar.distance (sourceCoefficient 29 46 1 0) v2423_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2423_pb : Scalar.QComplex := ((-344705748430876214077194 : Int)/10^30,(-431477379004525759106388068 : Int)/10^30)
theorem v2423_pb_checked : Scalar.distance (sourceCoefficient 29 46 1 1) v2423_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2423_pg : Scalar.QComplex := ((-93086399727181150351499 : Int)/10^30,(74366394735973228093 : Int)/10^30)
theorem v2423_pg_checked : Scalar.distance (sourceCoefficient 29 46 1 2) v2423_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2423_mb : Scalar.QComplex := ((-717051165142315211285908 : Int)/10^30,(-431476920880242140087506966 : Int)/10^30)
theorem v2423_mb_checked : Scalar.distance (sourceCoefficient 29 46 3 1) v2423_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2423_mg : Scalar.QComplex := ((-93086300892010954230523 : Int)/10^30,(154695737554710651535 : Int)/10^30)
theorem v2423_mg_checked : Scalar.distance (sourceCoefficient 29 46 3 2) v2423_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2423_upper : Scalar.QComplex := ((999996812677957786182478148579 : Int)/10^30,(-2524803739977789691812240367 : Int)/10^30)
theorem v2423_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 46 5) 1) 14) v2423_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2423 : Material (29 : Basis) (46 : Basis) where
  plus := ![v2423_pa,v2423_pb,v2423_pg]
  minus := ![(Primitive.Addresses.material2423 1).one,v2423_mb,v2423_mg]
  upper := v2423_upper
  lower := (Primitive.Addresses.material2423 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2423_pa_checked.trans (by decide +kernel)
    · exact v2423_pb_checked.trans (by decide +kernel)
    · exact v2423_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 46 Primitive.Addresses.material2423
    · exact v2423_mb_checked.trans (by decide +kernel)
    · exact v2423_mg_checked.trans (by decide +kernel)
  upper_error := v2423_upper_checked
  lower_error := reuse_lower_error 29 46 Primitive.Addresses.material2423

def v2424_pa : Scalar.QComplex := ((999999677728538536687195258817 : Int)/10^30,(-802834241339848892087401265 : Int)/10^30)
theorem v2424_pa_checked : Scalar.distance (sourceCoefficient 29 47 1 0) v2424_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2424_pb : Scalar.QComplex := ((-346404924660180238639881 : Int)/10^30,(-431477377504034237634499079 : Int)/10^30)
theorem v2424_pb_checked : Scalar.distance (sourceCoefficient 29 47 1 1) v2424_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2424_pg : Scalar.QComplex := ((-93086399418534132447489 : Int)/10^30,(74732972940541410313 : Int)/10^30)
theorem v2424_pg_checked : Scalar.distance (sourceCoefficient 29 47 1 2) v2424_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2424_mb : Scalar.QComplex := ((-718750339444081666087948 : Int)/10^30,(-431476917913438619484326933 : Int)/10^30)
theorem v2424_mb_checked : Scalar.distance (sourceCoefficient 29 47 3 1) v2424_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2424_mg : Scalar.QComplex := ((-93086300267023570777013 : Int)/10^30,(155062315356436539237 : Int)/10^30)
theorem v2424_mg_checked : Scalar.distance (sourceCoefficient 29 47 3 2) v2424_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2424_upper : Scalar.QComplex := ((999996802727418774725479802302 : Int)/10^30,(-2528741770109907917852296472 : Int)/10^30)
theorem v2424_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 47 5) 1) 14) v2424_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2424 : Material (29 : Basis) (47 : Basis) where
  plus := ![v2424_pa,v2424_pb,v2424_pg]
  minus := ![(Primitive.Addresses.material2424 1).one,v2424_mb,v2424_mg]
  upper := v2424_upper
  lower := (Primitive.Addresses.material2424 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2424_pa_checked.trans (by decide +kernel)
    · exact v2424_pb_checked.trans (by decide +kernel)
    · exact v2424_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 47 Primitive.Addresses.material2424
    · exact v2424_mb_checked.trans (by decide +kernel)
    · exact v2424_mg_checked.trans (by decide +kernel)
  upper_error := v2424_upper_checked
  lower_error := reuse_lower_error 29 47 Primitive.Addresses.material2424

def v2425_pa : Scalar.QComplex := ((999999655330121527322212453221 : Int)/10^30,(-830264800017458555826272692 : Int)/10^30)
theorem v2425_pa_checked : Scalar.distance (sourceCoefficient 29 48 1 0) v2425_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2425_pb : Scalar.QComplex := ((-358240593136987071254256 : Int)/10^30,(-431477366804798178909642726 : Int)/10^30)
theorem v2425_pb_checked : Scalar.distance (sourceCoefficient 29 48 1 1) v2425_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2425_pg : Scalar.QComplex := ((-93086397221919779335829 : Int)/10^30,(77286385612092071781 : Int)/10^30)
theorem v2425_pg_checked : Scalar.distance (sourceCoefficient 29 48 1 2) v2425_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2425_mb : Scalar.QComplex := ((-730585994280969365040384 : Int)/10^30,(-431476897000557707809863484 : Int)/10^30)
theorem v2425_mb_checked : Scalar.distance (sourceCoefficient 29 48 3 1) v2425_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2425_mg : Scalar.QComplex := ((-93086295866929901454718 : Int)/10^30,(157615725181655711465 : Int)/10^30)
theorem v2425_mg_checked : Scalar.distance (sourceCoefficient 29 48 3 2) v2425_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2425_upper : Scalar.QComplex := ((999996732986379328461537116922 : Int)/10^30,(-2556172249275286861416701588 : Int)/10^30)
theorem v2425_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 48 5) 1) 14) v2425_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2425 : Material (29 : Basis) (48 : Basis) where
  plus := ![v2425_pa,v2425_pb,v2425_pg]
  minus := ![(Primitive.Addresses.material2425 1).one,v2425_mb,v2425_mg]
  upper := v2425_upper
  lower := (Primitive.Addresses.material2425 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2425_pa_checked.trans (by decide +kernel)
    · exact v2425_pb_checked.trans (by decide +kernel)
    · exact v2425_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 48 Primitive.Addresses.material2425
    · exact v2425_mb_checked.trans (by decide +kernel)
    · exact v2425_mg_checked.trans (by decide +kernel)
  upper_error := v2425_upper_checked
  lower_error := reuse_lower_error 29 48 Primitive.Addresses.material2425

def v2426_pa : Scalar.QComplex := ((999999636789581887492136955732 : Int)/10^30,(-852303176283655475047352733 : Int)/10^30)
theorem v2426_pa_checked : Scalar.distance (sourceCoefficient 29 49 1 0) v2426_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2426_pb : Scalar.QComplex := ((-367749656199039332848641 : Int)/10^30,(-431477357895169956680549009 : Int)/10^30)
theorem v2426_pb_checked : Scalar.distance (sourceCoefficient 29 49 1 1) v2426_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2426_pg : Scalar.QComplex := ((-93086395397907338939102 : Int)/10^30,(79337859282769716685 : Int)/10^30)
theorem v2426_pg_checked : Scalar.distance (sourceCoefficient 29 49 1 2) v2426_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2426_mb : Scalar.QComplex := ((-740095046113754981957212 : Int)/10^30,(-431476879885039652793544950 : Int)/10^30)
theorem v2426_mb_checked : Scalar.distance (sourceCoefficient 29 49 3 1) v2426_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2426_mg : Scalar.QComplex := ((-93086292272588757370643 : Int)/10^30,(159667196514435366206 : Int)/10^30)
theorem v2426_mg_checked : Scalar.distance (sourceCoefficient 29 49 3 2) v2426_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2426_upper : Scalar.QComplex := ((999996676409629173008596741377 : Int)/10^30,(-2578210560718621707938121140 : Int)/10^30)
theorem v2426_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 49 5) 1) 14) v2426_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2426 : Material (29 : Basis) (49 : Basis) where
  plus := ![v2426_pa,v2426_pb,v2426_pg]
  minus := ![(Primitive.Addresses.material2426 1).one,v2426_mb,v2426_mg]
  upper := v2426_upper
  lower := (Primitive.Addresses.material2426 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2426_pa_checked.trans (by decide +kernel)
    · exact v2426_pb_checked.trans (by decide +kernel)
    · exact v2426_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 49 Primitive.Addresses.material2426
    · exact v2426_mb_checked.trans (by decide +kernel)
    · exact v2426_mg_checked.trans (by decide +kernel)
  upper_error := v2426_upper_checked
  lower_error := reuse_lower_error 29 49 Primitive.Addresses.material2426

def v2427_pa : Scalar.QComplex := ((999999634591345590777309173197 : Int)/10^30,(-854878456445687175146350249 : Int)/10^30)
theorem v2427_pa_checked : Scalar.distance (sourceCoefficient 29 50 1 0) v2427_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2427_pb : Scalar.QComplex := ((-368860831588000409155236 : Int)/10^30,(-431477356835807720962542332 : Int)/10^30)
theorem v2427_pb_checked : Scalar.distance (sourceCoefficient 29 50 1 1) v2427_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2427_pg : Scalar.QComplex := ((-93086395181321601403192 : Int)/10^30,(79577582907038954359 : Int)/10^30)
theorem v2427_pg_checked : Scalar.distance (sourceCoefficient 29 50 1 2) v2427_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2427_mb : Scalar.QComplex := ((-741206220174792780208889 : Int)/10^30,(-431476877866783496332848223 : Int)/10^30)
theorem v2427_mb_checked : Scalar.distance (sourceCoefficient 29 50 3 1) v2427_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2427_mg : Scalar.QComplex := ((-93086291849132409486393 : Int)/10^30,(159906919862540805820 : Int)/10^30)
theorem v2427_mg_checked : Scalar.distance (sourceCoefficient 29 50 3 2) v2427_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2427_upper : Scalar.QComplex := ((999996669766696218233096495699 : Int)/10^30,(-2580785833251119694658401677 : Int)/10^30)
theorem v2427_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 50 5) 1) 14) v2427_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2427 : Material (29 : Basis) (50 : Basis) where
  plus := ![v2427_pa,v2427_pb,v2427_pg]
  minus := ![(Primitive.Addresses.material2427 1).one,v2427_mb,v2427_mg]
  upper := v2427_upper
  lower := (Primitive.Addresses.material2427 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2427_pa_checked.trans (by decide +kernel)
    · exact v2427_pb_checked.trans (by decide +kernel)
    · exact v2427_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 50 Primitive.Addresses.material2427
    · exact v2427_mb_checked.trans (by decide +kernel)
    · exact v2427_mg_checked.trans (by decide +kernel)
  upper_error := v2427_upper_checked
  lower_error := reuse_lower_error 29 50 Primitive.Addresses.material2427

def v2428_pa : Scalar.QComplex := ((999999624868023247219209464224 : Int)/10^30,(-866177702773259800461103218 : Int)/10^30)
theorem v2428_pa_checked : Scalar.distance (sourceCoefficient 29 51 1 0) v2428_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2428_pb : Scalar.QComplex := ((-373736201878032213633284 : Int)/10^30,(-431477352142676062364607541 : Int)/10^30)
theorem v2428_pb_checked : Scalar.distance (sourceCoefficient 29 51 1 1) v2428_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2428_pg : Scalar.QComplex := ((-93086394222521692877719 : Int)/10^30,(80629389353772095854 : Int)/10^30)
theorem v2428_pg_checked : Scalar.distance (sourceCoefficient 29 51 1 2) v2428_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2428_mb : Scalar.QComplex := ((-746081584599540159711969 : Int)/10^30,(-431476868966428603431594350 : Int)/10^30)
theorem v2428_mb_checked : Scalar.distance (sourceCoefficient 29 51 3 1) v2428_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2428_mg : Scalar.QComplex := ((-93086289982671266039087 : Int)/10^30,(160958725090237198954 : Int)/10^30)
theorem v2428_mg_checked : Scalar.distance (sourceCoefficient 29 51 3 2) v2428_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2428_upper : Scalar.QComplex := ((999996640541914254650605617024 : Int)/10^30,(-2592085045968219945696491875 : Int)/10^30)
theorem v2428_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 51 5) 1) 14) v2428_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2428 : Material (29 : Basis) (51 : Basis) where
  plus := ![v2428_pa,v2428_pb,v2428_pg]
  minus := ![(Primitive.Addresses.material2428 1).one,v2428_mb,v2428_mg]
  upper := v2428_upper
  lower := (Primitive.Addresses.material2428 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2428_pa_checked.trans (by decide +kernel)
    · exact v2428_pb_checked.trans (by decide +kernel)
    · exact v2428_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 51 Primitive.Addresses.material2428
    · exact v2428_mb_checked.trans (by decide +kernel)
    · exact v2428_mg_checked.trans (by decide +kernel)
  upper_error := v2428_upper_checked
  lower_error := reuse_lower_error 29 51 Primitive.Addresses.material2428

def v2429_pa : Scalar.QComplex := ((999999603623557491223441115964 : Int)/10^30,(-890366625555601641372131417 : Int)/10^30)
theorem v2429_pa_checked : Scalar.distance (sourceCoefficient 29 52 1 0) v2429_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2429_pb : Scalar.QComplex := ((-384173177142905545001115 : Int)/10^30,(-431477341848902706181341225 : Int)/10^30)
theorem v2429_pb_checked : Scalar.distance (sourceCoefficient 29 52 1 1) v2429_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2429_pg : Scalar.QComplex := ((-93086392123352953388455 : Int)/10^30,(82881049692110933397 : Int)/10^30)
theorem v2429_pg_checked : Scalar.distance (sourceCoefficient 29 52 1 2) v2429_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2429_mb : Scalar.QComplex := ((-756518547095187814589535 : Int)/10^30,(-431476849666019490421249348 : Int)/10^30)
theorem v2429_mb_checked : Scalar.distance (sourceCoefficient 29 52 3 1) v2429_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2429_mg : Scalar.QComplex := ((-93086285940421847196950 : Int)/10^30,(163210382778691907444 : Int)/10^30)
theorem v2429_mg_checked : Scalar.distance (sourceCoefficient 29 52 3 2) v2429_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2429_upper : Scalar.QComplex := ((999996577549593819402100022427 : Int)/10^30,(-2616273896057982120808546063 : Int)/10^30)
theorem v2429_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 52 5) 1) 14) v2429_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2429 : Material (29 : Basis) (52 : Basis) where
  plus := ![v2429_pa,v2429_pb,v2429_pg]
  minus := ![(Primitive.Addresses.material2429 1).one,v2429_mb,v2429_mg]
  upper := v2429_upper
  lower := (Primitive.Addresses.material2429 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2429_pa_checked.trans (by decide +kernel)
    · exact v2429_pb_checked.trans (by decide +kernel)
    · exact v2429_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 52 Primitive.Addresses.material2429
    · exact v2429_mb_checked.trans (by decide +kernel)
    · exact v2429_mg_checked.trans (by decide +kernel)
  upper_error := v2429_upper_checked
  lower_error := reuse_lower_error 29 52 Primitive.Addresses.material2429

def v2430_pa : Scalar.QComplex := ((999999600319951045837724388809 : Int)/10^30,(-894069313959596210467411104 : Int)/10^30)
theorem v2430_pa_checked : Scalar.distance (sourceCoefficient 29 53 1 0) v2430_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2430_pb : Scalar.QComplex := ((-385770803765501728022092 : Int)/10^30,(-431477340243489570857939416 : Int)/10^30)
theorem v2430_pb_checked : Scalar.distance (sourceCoefficient 29 53 1 1) v2430_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2430_pg : Scalar.QComplex := ((-93086391796417560589535 : Int)/10^30,(83225719716056963430 : Int)/10^30)
theorem v2430_pg_checked : Scalar.distance (sourceCoefficient 29 53 1 2) v2430_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2430_mb : Scalar.QComplex := ((-758116171737515360213706 : Int)/10^30,(-431476846681927131998030539 : Int)/10^30)
theorem v2430_mb_checked : Scalar.distance (sourceCoefficient 29 53 3 1) v2430_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2430_mg : Scalar.QComplex := ((-93086285316051868827218 : Int)/10^30,(163555052392171016001 : Int)/10^30)
theorem v2430_mg_checked : Scalar.distance (sourceCoefficient 29 53 3 2) v2430_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2430_upper : Scalar.QComplex := ((999996567855488014323550996666 : Int)/10^30,(-2619976573245532236587146146 : Int)/10^30)
theorem v2430_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 53 5) 1) 14) v2430_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2430 : Material (29 : Basis) (53 : Basis) where
  plus := ![v2430_pa,v2430_pb,v2430_pg]
  minus := ![(Primitive.Addresses.material2430 1).one,v2430_mb,v2430_mg]
  upper := v2430_upper
  lower := (Primitive.Addresses.material2430 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2430_pa_checked.trans (by decide +kernel)
    · exact v2430_pb_checked.trans (by decide +kernel)
    · exact v2430_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 53 Primitive.Addresses.material2430
    · exact v2430_mb_checked.trans (by decide +kernel)
    · exact v2430_mg_checked.trans (by decide +kernel)
  upper_error := v2430_upper_checked
  lower_error := reuse_lower_error 29 53 Primitive.Addresses.material2430

def v2431_pa : Scalar.QComplex := ((999999598635120536936169478419 : Int)/10^30,(-895951783207311438321243614 : Int)/10^30)
theorem v2431_pa_checked : Scalar.distance (sourceCoefficient 29 54 1 0) v2431_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2431_pb : Scalar.QComplex := ((-386583046831573216163671 : Int)/10^30,(-431477339424263453144174092 : Int)/10^30)
theorem v2431_pb_checked : Scalar.distance (sourceCoefficient 29 54 1 1) v2431_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2431_pg : Scalar.QComplex := ((-93086391629630714400551 : Int)/10^30,(83400952047114853431 : Int)/10^30)
theorem v2431_pg_checked : Scalar.distance (sourceCoefficient 29 54 1 2) v2431_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2431_mb : Scalar.QComplex := ((-758928413794196390502616 : Int)/10^30,(-431476845161772135369600656 : Int)/10^30)
theorem v2431_mb_checked : Scalar.distance (sourceCoefficient 29 54 3 1) v2431_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2431_mg : Scalar.QComplex := ((-93086284998047475208860 : Int)/10^30,(163730284514052364175 : Int)/10^30)
theorem v2431_mg_checked : Scalar.distance (sourceCoefficient 29 54 3 2) v2431_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2431_upper : Scalar.QComplex := ((999996562921688869498763391031 : Int)/10^30,(-2621859036781666038606256191 : Int)/10^30)
theorem v2431_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 54 5) 1) 14) v2431_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2431 : Material (29 : Basis) (54 : Basis) where
  plus := ![v2431_pa,v2431_pb,v2431_pg]
  minus := ![(Primitive.Addresses.material2431 1).one,v2431_mb,v2431_mg]
  upper := v2431_upper
  lower := (Primitive.Addresses.material2431 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2431_pa_checked.trans (by decide +kernel)
    · exact v2431_pb_checked.trans (by decide +kernel)
    · exact v2431_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 54 Primitive.Addresses.material2431
    · exact v2431_mb_checked.trans (by decide +kernel)
    · exact v2431_mg_checked.trans (by decide +kernel)
  upper_error := v2431_upper_checked
  lower_error := reuse_lower_error 29 54 Primitive.Addresses.material2431

def v2432_pa : Scalar.QComplex := ((999999584770285391064698903438 : Int)/10^30,(-911295372973085334086592360 : Int)/10^30)
theorem v2432_pa_checked : Scalar.distance (sourceCoefficient 29 55 1 0) v2432_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2432_pb : Scalar.QComplex := ((-393203460075523721947669 : Int)/10^30,(-431477332670903706871025885 : Int)/10^30)
theorem v2432_pb_checked : Scalar.distance (sourceCoefficient 29 55 1 1) v2432_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2432_pg : Scalar.QComplex := ((-93086390255835948073810 : Int)/10^30,(84829231950527969945 : Int)/10^30)
theorem v2432_pg_checked : Scalar.distance (sourceCoefficient 29 55 1 2) v2432_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2432_mb : Scalar.QComplex := ((-765548818745219176729733 : Int)/10^30,(-431476832695296446495473123 : Int)/10^30)
theorem v2432_mb_checked : Scalar.distance (sourceCoefficient 29 55 3 1) v2432_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2432_mg : Scalar.QComplex := ((-93086282391711991102084 : Int)/10^30,(165158562700128587112 : Int)/10^30)
theorem v2432_mg_checked : Scalar.distance (sourceCoefficient 29 55 3 2) v2432_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2432_upper : Scalar.QComplex := ((999996522575230397534979959730 : Int)/10^30,(-2637202579765517709160710355 : Int)/10^30)
theorem v2432_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 55 5) 1) 14) v2432_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2432 : Material (29 : Basis) (55 : Basis) where
  plus := ![v2432_pa,v2432_pb,v2432_pg]
  minus := ![(Primitive.Addresses.material2432 1).one,v2432_mb,v2432_mg]
  upper := v2432_upper
  lower := (Primitive.Addresses.material2432 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2432_pa_checked.trans (by decide +kernel)
    · exact v2432_pb_checked.trans (by decide +kernel)
    · exact v2432_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 55 Primitive.Addresses.material2432
    · exact v2432_mb_checked.trans (by decide +kernel)
    · exact v2432_mg_checked.trans (by decide +kernel)
  upper_error := v2432_upper_checked
  lower_error := reuse_lower_error 29 55 Primitive.Addresses.material2432

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
