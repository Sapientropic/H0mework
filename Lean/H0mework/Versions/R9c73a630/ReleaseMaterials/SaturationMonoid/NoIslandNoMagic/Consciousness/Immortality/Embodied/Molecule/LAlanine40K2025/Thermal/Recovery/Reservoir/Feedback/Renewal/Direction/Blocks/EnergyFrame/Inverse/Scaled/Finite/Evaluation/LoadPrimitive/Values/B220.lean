import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B146
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B147

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3521_pa : Scalar.QComplex := ((999998301731870551226380057213 : Int)/10^30,(-1842968630981793932511250155 : Int)/10^30)
theorem v3521_pa_checked : Scalar.distance (sourceCoefficient 47 91 1 0) v3521_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3521_pb : Scalar.QComplex := ((-795199453138467571724100 : Int)/10^30,(-431476743178726000940381800 : Int)/10^30)
theorem v3521_pb_checked : Scalar.distance (sourceCoefficient 47 91 1 1) v3521_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3521_pg : Scalar.QComplex := ((-93086266950944375345183 : Int)/10^30,(171555361312790318310 : Int)/10^30)
theorem v3521_pg_checked : Scalar.distance (sourceCoefficient 47 91 1 2) v3521_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3521_mb : Scalar.QComplex := ((-1167544153421483066580803 : Int)/10^30,(-431475896298901449553090606 : Int)/10^30)
theorem v3521_mb_checked : Scalar.distance (sourceCoefficient 47 91 3 1) v3521_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3521_mg : Scalar.QComplex := ((-93086084246122690656440 : Int)/10^30,(251884553363721412888 : Int)/10^30)
theorem v3521_mg_checked : Scalar.distance (sourceCoefficient 47 91 3 2) v3521_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3521_upper : Scalar.QComplex := ((999993631555203907395024542294 : Int)/10^30,(-3568872235748442854577880565 : Int)/10^30)
theorem v3521_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 91 5) 1) 14) v3521_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3521 : Material (47 : Basis) (91 : Basis) where
  plus := ![v3521_pa,v3521_pb,v3521_pg]
  minus := ![(Primitive.Addresses.material3521 1).one,v3521_mb,v3521_mg]
  upper := v3521_upper
  lower := (Primitive.Addresses.material3521 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3521_pa_checked.trans (by decide +kernel)
    · exact v3521_pb_checked.trans (by decide +kernel)
    · exact v3521_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 91 Primitive.Addresses.material3521
    · exact v3521_mb_checked.trans (by decide +kernel)
    · exact v3521_mg_checked.trans (by decide +kernel)
  upper_error := v3521_upper_checked
  lower_error := reuse_lower_error 47 91 Primitive.Addresses.material3521

def v3522_pa : Scalar.QComplex := ((999998242327176698896567586411 : Int)/10^30,(-1874924680404109751595969144 : Int)/10^30)
theorem v3522_pa_checked : Scalar.distance (sourceCoefficient 47 92 1 0) v3522_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3522_pb : Scalar.QComplex := ((-808987761725532797289918 : Int)/10^30,(-431476713835440942344872229 : Int)/10^30)
theorem v3522_pb_checked : Scalar.distance (sourceCoefficient 47 92 1 1) v3522_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3522_pg : Scalar.QComplex := ((-93086261020816814352818 : Int)/10^30,(174530034961167805843 : Int)/10^30)
theorem v3522_pg_checked : Scalar.distance (sourceCoefficient 47 92 1 2) v3522_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3522_mb : Scalar.QComplex := ((-1181332431552597415281466 : Int)/10^30,(-431475855056938008532443051 : Int)/10^30)
theorem v3522_mb_checked : Scalar.distance (sourceCoefficient 47 92 3 1) v3522_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3522_mg : Scalar.QComplex := ((-93086075748987953499577 : Int)/10^30,(254859220787058949723 : Int)/10^30)
theorem v3522_mg_checked : Scalar.distance (sourceCoefficient 47 92 3 2) v3522_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3522_upper : Scalar.QComplex := ((999993516997356258619047522075 : Int)/10^30,(-3600828135048864442987177387 : Int)/10^30)
theorem v3522_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 92 5) 1) 14) v3522_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3522 : Material (47 : Basis) (92 : Basis) where
  plus := ![v3522_pa,v3522_pb,v3522_pg]
  minus := ![(Primitive.Addresses.material3522 1).one,v3522_mb,v3522_mg]
  upper := v3522_upper
  lower := (Primitive.Addresses.material3522 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3522_pa_checked.trans (by decide +kernel)
    · exact v3522_pb_checked.trans (by decide +kernel)
    · exact v3522_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 92 Primitive.Addresses.material3522
    · exact v3522_mb_checked.trans (by decide +kernel)
    · exact v3522_mg_checked.trans (by decide +kernel)
  upper_error := v3522_upper_checked
  lower_error := reuse_lower_error 47 92 Primitive.Addresses.material3522

def v3523_pa : Scalar.QComplex := ((999998170500336572953565819936 : Int)/10^30,(-1912850224085794540669845575 : Int)/10^30)
theorem v3523_pa_checked : Scalar.distance (sourceCoefficient 47 93 1 0) v3523_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3523_pb : Scalar.QComplex := ((-825351770655973659380315 : Int)/10^30,(-431476678248369064121570049 : Int)/10^30)
theorem v3523_pb_checked : Scalar.distance (sourceCoefficient 47 93 1 1) v3523_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3523_pg : Scalar.QComplex := ((-93086253839009181091099 : Int)/10^30,(178060387276674456744 : Int)/10^30)
theorem v3523_pg_checked : Scalar.distance (sourceCoefficient 47 93 1 2) v3523_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3523_mb : Scalar.QComplex := ((-1197696403679929631727587 : Int)/10^30,(-431475805348476681635165485 : Int)/10^30)
theorem v3523_mb_checked : Scalar.distance (sourceCoefficient 47 93 3 1) v3523_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3523_mg : Scalar.QComplex := ((-93086065520647947236715 : Int)/10^30,(258389565590477557593 : Int)/10^30)
theorem v3523_mg_checked : Scalar.distance (sourceCoefficient 47 93 3 2) v3523_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3523_upper : Scalar.QComplex := ((999993379714575294175572621439 : Int)/10^30,(-3638753498278296988160196637 : Int)/10^30)
theorem v3523_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 93 5) 1) 14) v3523_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3523 : Material (47 : Basis) (93 : Basis) where
  plus := ![v3523_pa,v3523_pb,v3523_pg]
  minus := ![(Primitive.Addresses.material3523 1).one,v3523_mb,v3523_mg]
  upper := v3523_upper
  lower := (Primitive.Addresses.material3523 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3523_pa_checked.trans (by decide +kernel)
    · exact v3523_pb_checked.trans (by decide +kernel)
    · exact v3523_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 93 Primitive.Addresses.material3523
    · exact v3523_mb_checked.trans (by decide +kernel)
    · exact v3523_mg_checked.trans (by decide +kernel)
  upper_error := v3523_upper_checked
  lower_error := reuse_lower_error 47 93 Primitive.Addresses.material3523

def v3524_pa : Scalar.QComplex := ((999998083803952314179602748828 : Int)/10^30,(-1957648697689232399664919271 : Int)/10^30)
theorem v3524_pa_checked : Scalar.distance (sourceCoefficient 47 94 1 0) v3524_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3524_pb : Scalar.QComplex := ((-844681291452112672805871 : Int)/10^30,(-431476635146133556500869942 : Int)/10^30)
theorem v3524_pb_checked : Scalar.distance (sourceCoefficient 47 94 1 1) v3524_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3524_pg : Scalar.QComplex := ((-93086245154469074988777 : Int)/10^30,(182230515788821126790 : Int)/10^30)
theorem v3524_pg_checked : Scalar.distance (sourceCoefficient 47 94 1 2) v3524_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3524_mb : Scalar.QComplex := ((-1217025880083516659557138 : Int)/10^30,(-431475745565751345178252378 : Int)/10^30)
theorem v3524_mb_checked : Scalar.distance (sourceCoefficient 47 94 3 1) v3524_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3524_mg : Scalar.QComplex := ((-93086053237477984419144 : Int)/10^30,(262559685055527823879 : Int)/10^30)
theorem v3524_mg_checked : Scalar.distance (sourceCoefficient 47 94 3 2) v3524_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3524_upper : Scalar.QComplex := ((999993215700218805726553681744 : Int)/10^30,(-3683551755529576617105180379 : Int)/10^30)
theorem v3524_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 94 5) 1) 14) v3524_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3524 : Material (47 : Basis) (94 : Basis) where
  plus := ![v3524_pa,v3524_pb,v3524_pg]
  minus := ![(Primitive.Addresses.material3524 1).one,v3524_mb,v3524_mg]
  upper := v3524_upper
  lower := (Primitive.Addresses.material3524 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3524_pa_checked.trans (by decide +kernel)
    · exact v3524_pb_checked.trans (by decide +kernel)
    · exact v3524_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 94 Primitive.Addresses.material3524
    · exact v3524_mb_checked.trans (by decide +kernel)
    · exact v3524_mg_checked.trans (by decide +kernel)
  upper_error := v3524_upper_checked
  lower_error := reuse_lower_error 47 94 Primitive.Addresses.material3524

def v3525_pa : Scalar.QComplex := ((999997996150474463176189785589 : Int)/10^30,(-2001922834591964642610320841 : Int)/10^30)
theorem v3525_pa_checked : Scalar.distance (sourceCoefficient 47 95 1 0) v3525_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3525_pb : Scalar.QComplex := ((-863784571837877768601016 : Int)/10^30,(-431476591413989755716051428 : Int)/10^30)
theorem v3525_pb_checked : Scalar.distance (sourceCoefficient 47 95 1 1) v3525_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3525_pg : Scalar.QComplex := ((-93086236357434933629716 : Int)/10^30,(186351835571211032227 : Int)/10^30)
theorem v3525_pg_checked : Scalar.distance (sourceCoefficient 47 95 1 2) v3525_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3525_mb : Scalar.QComplex := ((-1236129115617386927251779 : Int)/10^30,(-431475685348353234763725957 : Int)/10^30)
theorem v3525_mb_checked : Scalar.distance (sourceCoefficient 47 95 3 1) v3525_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3525_mg : Scalar.QComplex := ((-93086040883933763748009 : Int)/10^30,(266680995711917760431 : Int)/10^30)
theorem v3525_mg_checked : Scalar.distance (sourceCoefficient 47 95 3 2) v3525_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3525_upper : Scalar.QComplex := ((999993051633727728490544211376 : Int)/10^30,(-3727825675209231839450378278 : Int)/10^30)
theorem v3525_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 95 5) 1) 14) v3525_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3525 : Material (47 : Basis) (95 : Basis) where
  plus := ![v3525_pa,v3525_pb,v3525_pg]
  minus := ![(Primitive.Addresses.material3525 1).one,v3525_mb,v3525_mg]
  upper := v3525_upper
  lower := (Primitive.Addresses.material3525 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3525_pa_checked.trans (by decide +kernel)
    · exact v3525_pb_checked.trans (by decide +kernel)
    · exact v3525_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 95 Primitive.Addresses.material3525
    · exact v3525_mb_checked.trans (by decide +kernel)
    · exact v3525_mg_checked.trans (by decide +kernel)
  upper_error := v3525_upper_checked
  lower_error := reuse_lower_error 47 95 Primitive.Addresses.material3525

def v3526_pa : Scalar.QComplex := ((999997953355313377833821553575 : Int)/10^30,(-2023186888176635816087012891 : Int)/10^30)
theorem v3526_pa_checked : Scalar.distance (sourceCoefficient 47 96 1 0) v3526_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3526_pb : Scalar.QComplex := ((-872959525636360796249475 : Int)/10^30,(-431476570009370187416398947 : Int)/10^30)
theorem v3526_pb_checked : Scalar.distance (sourceCoefficient 47 96 1 1) v3526_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3526_pg : Scalar.QComplex := ((-93086232056707390879256 : Int)/10^30,(188331229614008442775 : Int)/10^30)
theorem v3526_pg_checked : Scalar.distance (sourceCoefficient 47 96 1 2) v3526_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3526_mb : Scalar.QComplex := ((-1245304047528392680458125 : Int)/10^30,(-431475656026169732870791575 : Int)/10^30)
theorem v3526_mb_checked : Scalar.distance (sourceCoefficient 47 96 3 1) v3526_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3526_mg : Scalar.QComplex := ((-93086034875079912019137 : Int)/10^30,(268660385306362134253 : Int)/10^30)
theorem v3526_mg_checked : Scalar.distance (sourceCoefficient 47 96 3 2) v3526_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3526_upper : Scalar.QComplex := ((999992972138802954243307031357 : Int)/10^30,(-3749089623263027363143396201 : Int)/10^30)
theorem v3526_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 96 5) 1) 14) v3526_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3526 : Material (47 : Basis) (96 : Basis) where
  plus := ![v3526_pa,v3526_pb,v3526_pg]
  minus := ![(Primitive.Addresses.material3526 1).one,v3526_mb,v3526_mg]
  upper := v3526_upper
  lower := (Primitive.Addresses.material3526 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3526_pa_checked.trans (by decide +kernel)
    · exact v3526_pb_checked.trans (by decide +kernel)
    · exact v3526_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 96 Primitive.Addresses.material3526
    · exact v3526_mb_checked.trans (by decide +kernel)
    · exact v3526_mg_checked.trans (by decide +kernel)
  upper_error := v3526_upper_checked
  lower_error := reuse_lower_error 47 96 Primitive.Addresses.material3526

def v3527_pa : Scalar.QComplex := ((999997802658112633650969125724 : Int)/10^30,(-2096348956262131490042569040 : Int)/10^30)
theorem v3527_pa_checked : Scalar.distance (sourceCoefficient 47 97 1 0) v3527_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3527_pb : Scalar.QComplex := ((-904527286193386808255509 : Int)/10^30,(-431476494376439593737159402 : Int)/10^30)
theorem v3527_pb_checked : Scalar.distance (sourceCoefficient 47 97 1 1) v3527_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3527_pg : Scalar.QComplex := ((-93086216884297426953312 : Int)/10^30,(195141622400648182093 : Int)/10^30)
theorem v3527_pg_checked : Scalar.distance (sourceCoefficient 47 97 1 2) v3527_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3527_mb : Scalar.QComplex := ((-1276871731063485997552166 : Int)/10^30,(-431475553151711699232067055 : Int)/10^30)
theorem v3527_mb_checked : Scalar.distance (sourceCoefficient 47 97 3 1) v3527_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3527_mg : Scalar.QComplex := ((-93086013825613351309546 : Int)/10^30,(275470762464074929888 : Int)/10^30)
theorem v3527_mg_checked : Scalar.distance (sourceCoefficient 47 97 3 2) v3527_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3527_upper : Scalar.QComplex := ((999992695170734351242962464885 : Int)/10^30,(-3822251322292519502780310538 : Int)/10^30)
theorem v3527_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 97 5) 1) 14) v3527_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3527 : Material (47 : Basis) (97 : Basis) where
  plus := ![v3527_pa,v3527_pb,v3527_pg]
  minus := ![(Primitive.Addresses.material3527 1).one,v3527_mb,v3527_mg]
  upper := v3527_upper
  lower := (Primitive.Addresses.material3527 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3527_pa_checked.trans (by decide +kernel)
    · exact v3527_pb_checked.trans (by decide +kernel)
    · exact v3527_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 97 Primitive.Addresses.material3527
    · exact v3527_mb_checked.trans (by decide +kernel)
    · exact v3527_mg_checked.trans (by decide +kernel)
  upper_error := v3527_upper_checked
  lower_error := reuse_lower_error 47 97 Primitive.Addresses.material3527

def v3528_pa : Scalar.QComplex := ((999999363451341135687148403701 : Int)/10^30,(-1128315963077023297520842001 : Int)/10^30)
theorem v3528_pa_checked : Scalar.distance (sourceCoefficient 48 49 1 0) v3528_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3528_pb : Scalar.QComplex := ((-486842974614528809405367 : Int)/10^30,(-431477246309287960236358713 : Int)/10^30)
theorem v3528_pb_checked : Scalar.distance (sourceCoefficient 48 49 1 1) v3528_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3528_pg : Scalar.QComplex := ((-93086370639166344775920 : Int)/10^30,(105030904794357305197 : Int)/10^30)
theorem v3528_pg_checked : Scalar.distance (sourceCoefficient 48 49 1 2) v3528_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3528_mb : Scalar.QComplex := ((-859188223891768657527386 : Int)/10^30,(-431476665527029176254686900 : Int)/10^30)
theorem v3528_mb_checked : Scalar.distance (sourceCoefficient 48 49 3 1) v3528_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3528_mg : Scalar.QComplex := ((-93086245341915877331780 : Int)/10^30,(185360211093649494904 : Int)/10^30)
theorem v3528_mg_checked : Scalar.distance (sourceCoefficient 48 49 3 2) v3528_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3528_upper : Scalar.QComplex := ((999995926698765205470394975715 : Int)/10^30,(-2854222464666359855081873539 : Int)/10^30)
theorem v3528_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 49 5) 1) 14) v3528_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3528 : Material (48 : Basis) (49 : Basis) where
  plus := ![v3528_pa,v3528_pb,v3528_pg]
  minus := ![(Primitive.Addresses.material3528 1).one,v3528_mb,v3528_mg]
  upper := v3528_upper
  lower := (Primitive.Addresses.material3528 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3528_pa_checked.trans (by decide +kernel)
    · exact v3528_pb_checked.trans (by decide +kernel)
    · exact v3528_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 49 Primitive.Addresses.material3528
    · exact v3528_mb_checked.trans (by decide +kernel)
    · exact v3528_mg_checked.trans (by decide +kernel)
  upper_error := v3528_upper_checked
  lower_error := reuse_lower_error 48 49 Primitive.Addresses.material3528

def v3529_pa : Scalar.QComplex := ((999999360542294326628804875375 : Int)/10^30,(-1130891242534216923802138580 : Int)/10^30)
theorem v3529_pa_checked : Scalar.distance (sourceCoefficient 48 50 1 0) v3529_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3529_pb : Scalar.QComplex := ((-487954149800742031052906 : Int)/10^30,(-431477245045459887937768001 : Int)/10^30)
theorem v3529_pb_checked : Scalar.distance (sourceCoefficient 48 50 1 1) v3529_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3529_pg : Scalar.QComplex := ((-93086370367441596608596 : Int)/10^30,(105270628363950826383 : Int)/10^30)
theorem v3529_pg_checked : Scalar.distance (sourceCoefficient 48 50 1 2) v3529_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3529_mb : Scalar.QComplex := ((-860299397573613868442687 : Int)/10^30,(-431476663304307434307648794 : Int)/10^30)
theorem v3529_mb_checked : Scalar.distance (sourceCoefficient 48 50 3 1) v3529_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3529_mg : Scalar.QComplex := ((-93086244863320586529569 : Int)/10^30,(185599934339496755581 : Int)/10^30)
theorem v3529_mg_checked : Scalar.distance (sourceCoefficient 48 50 3 2) v3529_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3529_upper : Scalar.QComplex := ((999995919345024013506712450526 : Int)/10^30,(-2856797735267226357679016492 : Int)/10^30)
theorem v3529_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 50 5) 1) 14) v3529_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3529 : Material (48 : Basis) (50 : Basis) where
  plus := ![v3529_pa,v3529_pb,v3529_pg]
  minus := ![(Primitive.Addresses.material3529 1).one,v3529_mb,v3529_mg]
  upper := v3529_upper
  lower := (Primitive.Addresses.material3529 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3529_pa_checked.trans (by decide +kernel)
    · exact v3529_pb_checked.trans (by decide +kernel)
    · exact v3529_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 50 Primitive.Addresses.material3529
    · exact v3529_mb_checked.trans (by decide +kernel)
    · exact v3529_mg_checked.trans (by decide +kernel)
  upper_error := v3529_upper_checked
  lower_error := reuse_lower_error 48 50 Primitive.Addresses.material3529

def v3530_pa : Scalar.QComplex := ((999999347700234386314721586372 : Int)/10^30,(-1142190485747620967793112190 : Int)/10^30)
theorem v3530_pa_checked : Scalar.distance (sourceCoefficient 48 51 1 0) v3530_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3530_pb : Scalar.QComplex := ((-492829519194978017706307 : Int)/10^30,(-431477239455218126751183300 : Int)/10^30)
theorem v3530_pb_checked : Scalar.distance (sourceCoefficient 48 51 1 1) v3530_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3530_pg : Scalar.QComplex := ((-93086369166714898180328 : Int)/10^30,(106322434569111605722 : Int)/10^30)
theorem v3530_pg_checked : Scalar.distance (sourceCoefficient 48 51 1 2) v3530_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3530_mb : Scalar.QComplex := ((-865174760328400149471979 : Int)/10^30,(-431476653506843545884281798 : Int)/10^30)
theorem v3530_mb_checked : Scalar.distance (sourceCoefficient 48 51 3 1) v3530_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3530_mg : Scalar.QComplex := ((-93086242754932951725939 : Int)/10^30,(186651739116848952800 : Int)/10^30)
theorem v3530_mg_checked : Scalar.distance (sourceCoefficient 48 51 3 2) v3530_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3530_upper : Scalar.QComplex := ((999995887001514472933991904908 : Int)/10^30,(-2868096939487504503245438066 : Int)/10^30)
theorem v3530_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 51 5) 1) 14) v3530_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3530 : Material (48 : Basis) (51 : Basis) where
  plus := ![v3530_pa,v3530_pb,v3530_pg]
  minus := ![(Primitive.Addresses.material3530 1).one,v3530_mb,v3530_mg]
  upper := v3530_upper
  lower := (Primitive.Addresses.material3530 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3530_pa_checked.trans (by decide +kernel)
    · exact v3530_pb_checked.trans (by decide +kernel)
    · exact v3530_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 51 Primitive.Addresses.material3530
    · exact v3530_mb_checked.trans (by decide +kernel)
    · exact v3530_mg_checked.trans (by decide +kernel)
  upper_error := v3530_upper_checked
  lower_error := reuse_lower_error 48 51 Primitive.Addresses.material3530

def v3531_pa : Scalar.QComplex := ((999999319779314242605094359015 : Int)/10^30,(-1166379401744821828976479882 : Int)/10^30)
theorem v3531_pa_checked : Scalar.distance (sourceCoefficient 48 52 1 0) v3531_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3531_pb : Scalar.QComplex := ((-503266492508094162356195 : Int)/10^30,(-431477227240951464836639995 : Int)/10^30)
theorem v3531_pb_checked : Scalar.distance (sourceCoefficient 48 52 1 1) v3531_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3531_pg : Scalar.QComplex := ((-93086366549640074184563 : Int)/10^30,(108574094381113319688 : Int)/10^30)
theorem v3531_pg_checked : Scalar.distance (sourceCoefficient 48 52 1 2) v3531_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3531_mb : Scalar.QComplex := ((-875611719214992117321526 : Int)/10^30,(-431476632285943526508636668 : Int)/10^30)
theorem v3531_mb_checked : Scalar.distance (sourceCoefficient 48 52 3 1) v3531_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3531_mg : Scalar.QComplex := ((-93086238194778095422638 : Int)/10^30,(188903395832037108387 : Int)/10^30)
theorem v3531_mg_checked : Scalar.distance (sourceCoefficient 48 52 3 2) v3531_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3531_upper : Scalar.QComplex := ((999995817332761304303954335184 : Int)/10^30,(-2892285771269181214316877785 : Int)/10^30)
theorem v3531_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 52 5) 1) 14) v3531_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3531 : Material (48 : Basis) (52 : Basis) where
  plus := ![v3531_pa,v3531_pb,v3531_pg]
  minus := ![(Primitive.Addresses.material3531 1).one,v3531_mb,v3531_mg]
  upper := v3531_upper
  lower := (Primitive.Addresses.material3531 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3531_pa_checked.trans (by decide +kernel)
    · exact v3531_pb_checked.trans (by decide +kernel)
    · exact v3531_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 52 Primitive.Addresses.material3531
    · exact v3531_mb_checked.trans (by decide +kernel)
    · exact v3531_mg_checked.trans (by decide +kernel)
  upper_error := v3531_upper_checked
  lower_error := reuse_lower_error 48 52 Primitive.Addresses.material3531

def v3532_pa : Scalar.QComplex := ((999999315453718086637673990826 : Int)/10^30,(-1170082089095937136253614790 : Int)/10^30)
theorem v3532_pa_checked : Scalar.distance (sourceCoefficient 48 53 1 0) v3532_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3532_pb : Scalar.QComplex := ((-504864118827827859383785 : Int)/10^30,(-431477225341561274826379540 : Int)/10^30)
theorem v3532_pb_checked : Scalar.distance (sourceCoefficient 48 53 1 1) v3532_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3532_pg : Scalar.QComplex := ((-93086366143426870363989 : Int)/10^30,(108918764323385373658 : Int)/10^30)
theorem v3532_pg_checked : Scalar.distance (sourceCoefficient 48 53 1 2) v3532_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3532_mb : Scalar.QComplex := ((-877209343300768331762138 : Int)/10^30,(-431476629007874484216337080 : Int)/10^30)
theorem v3532_mb_checked : Scalar.distance (sourceCoefficient 48 53 3 1) v3532_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3532_mg : Scalar.QComplex := ((-93086237491130406030967 : Int)/10^30,(189248065295429090920 : Int)/10^30)
theorem v3532_mg_checked : Scalar.distance (sourceCoefficient 48 53 3 2) v3532_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3532_upper : Scalar.QComplex := ((999995806616669127951413672903 : Int)/10^30,(-2895988445639992110135593722 : Int)/10^30)
theorem v3532_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 53 5) 1) 14) v3532_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3532 : Material (48 : Basis) (53 : Basis) where
  plus := ![v3532_pa,v3532_pb,v3532_pg]
  minus := ![(Primitive.Addresses.material3532 1).one,v3532_mb,v3532_mg]
  upper := v3532_upper
  lower := (Primitive.Addresses.material3532 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3532_pa_checked.trans (by decide +kernel)
    · exact v3532_pb_checked.trans (by decide +kernel)
    · exact v3532_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 53 Primitive.Addresses.material3532
    · exact v3532_mb_checked.trans (by decide +kernel)
    · exact v3532_mg_checked.trans (by decide +kernel)
  upper_error := v3532_upper_checked
  lower_error := reuse_lower_error 48 53 Primitive.Addresses.material3532

def v3533_pa : Scalar.QComplex := ((999999313249301808964845947157 : Int)/10^30,(-1171964557806911173756735735 : Int)/10^30)
theorem v3533_pa_checked : Scalar.distance (sourceCoefficient 48 54 1 0) v3533_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3533_pb : Scalar.QComplex := ((-505676361739504843690096 : Int)/10^30,(-431477224372875439111657235 : Int)/10^30)
theorem v3533_pb_checked : Scalar.distance (sourceCoefficient 48 54 1 1) v3533_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3533_pg : Scalar.QComplex := ((-93086365936334704114623 : Int)/10^30,(109093996612807162806 : Int)/10^30)
theorem v3533_pg_checked : Scalar.distance (sourceCoefficient 48 54 1 2) v3533_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3533_mb : Scalar.QComplex := ((-878021585074077910484902 : Int)/10^30,(-431476627338259958473137014 : Int)/10^30)
theorem v3533_mb_checked : Scalar.distance (sourceCoefficient 48 54 3 1) v3533_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3533_mg : Scalar.QComplex := ((-93086237132820743289820 : Int)/10^30,(189423297340892677817 : Int)/10^30)
theorem v3533_mg_checked : Scalar.distance (sourceCoefficient 48 54 3 2) v3533_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3533_upper : Scalar.QComplex := ((999995801163285914583922451844 : Int)/10^30,(-2897870907742627620770460919 : Int)/10^30)
theorem v3533_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 54 5) 1) 14) v3533_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3533 : Material (48 : Basis) (54 : Basis) where
  plus := ![v3533_pa,v3533_pb,v3533_pg]
  minus := ![(Primitive.Addresses.material3533 1).one,v3533_mb,v3533_mg]
  upper := v3533_upper
  lower := (Primitive.Addresses.material3533 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3533_pa_checked.trans (by decide +kernel)
    · exact v3533_pb_checked.trans (by decide +kernel)
    · exact v3533_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 54 Primitive.Addresses.material3533
    · exact v3533_mb_checked.trans (by decide +kernel)
    · exact v3533_mg_checked.trans (by decide +kernel)
  upper_error := v3533_upper_checked
  lower_error := reuse_lower_error 48 54 Primitive.Addresses.material3533

def v3534_pa : Scalar.QComplex := ((999999295149438184216276253051 : Int)/10^30,(-1187308143161350071041293462 : Int)/10^30)
theorem v3534_pa_checked : Scalar.distance (sourceCoefficient 48 55 1 0) v3534_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3534_pb : Scalar.QComplex := ((-512296773714527437201277 : Int)/10^30,(-431477216401302646994597357 : Int)/10^30)
theorem v3534_pb_checked : Scalar.distance (sourceCoefficient 48 55 1 1) v3534_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3534_pg : Scalar.QComplex := ((-93086364234020204322307 : Int)/10^30,(110522276174024092121 : Int)/10^30)
theorem v3534_pg_checked : Scalar.distance (sourceCoefficient 48 55 1 2) v3534_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3534_mb : Scalar.QComplex := ((-884641987704910264634612 : Int)/10^30,(-431476613653572772379127764 : Int)/10^30)
theorem v3534_mb_checked : Scalar.distance (sourceCoefficient 48 55 3 1) v3534_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3534_mg : Scalar.QComplex := ((-93086234197965943340276 : Int)/10^30,(190851574901275106969 : Int)/10^30)
theorem v3534_mg_checked : Scalar.distance (sourceCoefficient 48 55 3 2) v3534_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3534_upper : Scalar.QComplex := ((999995756581812884884491990488 : Int)/10^30,(-2913214439005875907249946955 : Int)/10^30)
theorem v3534_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 55 5) 1) 14) v3534_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3534 : Material (48 : Basis) (55 : Basis) where
  plus := ![v3534_pa,v3534_pb,v3534_pg]
  minus := ![(Primitive.Addresses.material3534 1).one,v3534_mb,v3534_mg]
  upper := v3534_upper
  lower := (Primitive.Addresses.material3534 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3534_pa_checked.trans (by decide +kernel)
    · exact v3534_pb_checked.trans (by decide +kernel)
    · exact v3534_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 55 Primitive.Addresses.material3534
    · exact v3534_mb_checked.trans (by decide +kernel)
    · exact v3534_mg_checked.trans (by decide +kernel)
  upper_error := v3534_upper_checked
  lower_error := reuse_lower_error 48 55 Primitive.Addresses.material3534

def v3535_pa : Scalar.QComplex := ((999999290819268288453729006181 : Int)/10^30,(-1190949604511367353711287382 : Int)/10^30)
theorem v3535_pa_checked : Scalar.distance (sourceCoefficient 48 56 1 0) v3535_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3535_pb : Scalar.QComplex := ((-513867982377255152596343 : Int)/10^30,(-431477214489539429578025847 : Int)/10^30)
theorem v3535_pb_checked : Scalar.distance (sourceCoefficient 48 56 1 1) v3535_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3535_pg : Scalar.QComplex := ((-93086363826259453096899 : Int)/10^30,(110861246804945075589 : Int)/10^30)
theorem v3535_pg_checked : Scalar.distance (sourceCoefficient 48 56 1 2) v3535_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3535_mb : Scalar.QComplex := ((-886213194132839633101418 : Int)/10^30,(-431476610385927955476619015 : Int)/10^30)
theorem v3535_mb_checked : Scalar.distance (sourceCoefficient 48 56 3 1) v3535_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3535_mg : Scalar.QComplex := ((-93086233497688956128514 : Int)/10^30,(191190545054102669377 : Int)/10^30)
theorem v3535_mg_checked : Scalar.distance (sourceCoefficient 48 56 3 2) v3535_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3535_upper : Scalar.QComplex := ((999995745966817499064631895312 : Int)/10^30,(-2916855887458883855025766312 : Int)/10^30)
theorem v3535_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 56 5) 1) 14) v3535_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3535 : Material (48 : Basis) (56 : Basis) where
  plus := ![v3535_pa,v3535_pb,v3535_pg]
  minus := ![(Primitive.Addresses.material3535 1).one,v3535_mb,v3535_mg]
  upper := v3535_upper
  lower := (Primitive.Addresses.material3535 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3535_pa_checked.trans (by decide +kernel)
    · exact v3535_pb_checked.trans (by decide +kernel)
    · exact v3535_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 56 Primitive.Addresses.material3535
    · exact v3535_mb_checked.trans (by decide +kernel)
    · exact v3535_mg_checked.trans (by decide +kernel)
  upper_error := v3535_upper_checked
  lower_error := reuse_lower_error 48 56 Primitive.Addresses.material3535

def v3536_pa : Scalar.QComplex := ((999999276723076020833451195559 : Int)/10^30,(-1202727452430027613878265049 : Int)/10^30)
theorem v3536_pa_checked : Scalar.distance (sourceCoefficient 48 57 1 0) v3536_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3536_pb : Scalar.QComplex := ((-518949858809342612152209 : Int)/10^30,(-431477208253942738474884573 : Int)/10^30)
theorem v3536_pb_checked : Scalar.distance (sourceCoefficient 48 57 1 1) v3536_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3536_pg : Scalar.QComplex := ((-93086362497547364713703 : Int)/10^30,(111957604599005075005 : Int)/10^30)
theorem v3536_pg_checked : Scalar.distance (sourceCoefficient 48 57 1 2) v3536_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3536_mb : Scalar.QComplex := ((-891295063291673140192288 : Int)/10^30,(-431476599764903104497734355 : Int)/10^30)
theorem v3536_mb_checked : Scalar.distance (sourceCoefficient 48 57 3 1) v3536_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3536_mg : Scalar.QComplex := ((-93086231222869964333817 : Int)/10^30,(192286901293319866734 : Int)/10^30)
theorem v3536_mg_checked : Scalar.distance (sourceCoefficient 48 57 3 2) v3536_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3536_upper : Scalar.QComplex := ((999995711543149196475961230158 : Int)/10^30,(-2928633693507074106212525005 : Int)/10^30)
theorem v3536_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 57 5) 1) 14) v3536_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3536 : Material (48 : Basis) (57 : Basis) where
  plus := ![v3536_pa,v3536_pb,v3536_pg]
  minus := ![(Primitive.Addresses.material3536 1).one,v3536_mb,v3536_mg]
  upper := v3536_upper
  lower := (Primitive.Addresses.material3536 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3536_pa_checked.trans (by decide +kernel)
    · exact v3536_pb_checked.trans (by decide +kernel)
    · exact v3536_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 57 Primitive.Addresses.material3536
    · exact v3536_mb_checked.trans (by decide +kernel)
    · exact v3536_mg_checked.trans (by decide +kernel)
  upper_error := v3536_upper_checked
  lower_error := reuse_lower_error 48 57 Primitive.Addresses.material3536

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
