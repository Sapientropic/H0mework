import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B188
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B189

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4529_pa : Scalar.QComplex := ((999997605594483201073368231175 : Int)/10^30,(-2188333909717635935715815122 : Int)/10^30)
theorem v4529_pa_checked : Scalar.distance (sourceCoefficient 76 84 1 0) v4529_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4529_pb : Scalar.QComplex := ((-944216888245129750407799 : Int)/10^30,(-431476486844202371301707389 : Int)/10^30)
theorem v4529_pb_checked : Scalar.distance (sourceCoefficient 76 84 1 1) v4529_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4529_pg : Scalar.QComplex := ((-93086206899824841141863 : Int)/10^30,(203704190836316806760 : Int)/10^30)
theorem v4529_pg_checked : Scalar.distance (sourceCoefficient 76 84 1 2) v4529_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4529_mb : Scalar.QComplex := ((-1316561311836994707827643 : Int)/10^30,(-431475511369138264057926270 : Int)/10^30)
theorem v4529_mb_checked : Scalar.distance (sourceCoefficient 76 84 3 1) v4529_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4529_mg : Scalar.QComplex := ((-93085996452033566958104 : Int)/10^30,(284033319095357839644 : Int)/10^30)
theorem v4529_mg_checked : Scalar.distance (sourceCoefficient 76 84 3 2) v4529_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4529_upper : Scalar.QComplex := ((999992339349713567383414720474 : Int)/10^30,(-3914235798633294160326344591 : Int)/10^30)
theorem v4529_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 84 5) 1) 14) v4529_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4529 : Material (76 : Basis) (84 : Basis) where
  plus := ![v4529_pa,v4529_pb,v4529_pg]
  minus := ![(Primitive.Addresses.material4529 1).one,v4529_mb,v4529_mg]
  upper := v4529_upper
  lower := (Primitive.Addresses.material4529 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4529_pa_checked.trans (by decide +kernel)
    · exact v4529_pb_checked.trans (by decide +kernel)
    · exact v4529_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 84 Primitive.Addresses.material4529
    · exact v4529_mb_checked.trans (by decide +kernel)
    · exact v4529_mg_checked.trans (by decide +kernel)
  upper_error := v4529_upper_checked
  lower_error := reuse_lower_error 76 84 Primitive.Addresses.material4529

def v4530_pa : Scalar.QComplex := ((999997429466786262256119083196 : Int)/10^30,(-2267390530948403875542443815 : Int)/10^30)
theorem v4530_pa_checked : Scalar.distance (sourceCoefficient 76 85 1 0) v4530_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4530_pb : Scalar.QComplex := ((-978328039015513834345235 : Int)/10^30,(-431476409042592991473085810 : Int)/10^30)
theorem v4530_pb_checked : Scalar.distance (sourceCoefficient 76 85 1 1) v4530_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4530_pg : Scalar.QComplex := ((-93086190309863808898919 : Int)/10^30,(211063289015840885484 : Int)/10^30)
theorem v4530_pg_checked : Scalar.distance (sourceCoefficient 76 85 1 2) v4530_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4530_mb : Scalar.QComplex := ((-1350672382766953562964612 : Int)/10^30,(-431475404131171047682941414 : Int)/10^30)
theorem v4530_mb_checked : Scalar.distance (sourceCoefficient 76 85 3 1) v4530_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4530_mg : Scalar.QComplex := ((-93085973511508424464891 : Int)/10^30,(291392400218364152011 : Int)/10^30)
theorem v4530_mg_checked : Scalar.distance (sourceCoefficient 76 85 3 2) v4530_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4530_upper : Scalar.QComplex := ((999992026777722666429652328319 : Int)/10^30,(-3993291998138084683458015247 : Int)/10^30)
theorem v4530_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 85 5) 1) 14) v4530_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4530 : Material (76 : Basis) (85 : Basis) where
  plus := ![v4530_pa,v4530_pb,v4530_pg]
  minus := ![(Primitive.Addresses.material4530 1).one,v4530_mb,v4530_mg]
  upper := v4530_upper
  lower := (Primitive.Addresses.material4530 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4530_pa_checked.trans (by decide +kernel)
    · exact v4530_pb_checked.trans (by decide +kernel)
    · exact v4530_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 85 Primitive.Addresses.material4530
    · exact v4530_mb_checked.trans (by decide +kernel)
    · exact v4530_mg_checked.trans (by decide +kernel)
  upper_error := v4530_upper_checked
  lower_error := reuse_lower_error 76 85 Primitive.Addresses.material4530

def v4531_pa : Scalar.QComplex := ((999997396291346684093929163670 : Int)/10^30,(-2281975137317026245593797622 : Int)/10^30)
theorem v4531_pa_checked : Scalar.distance (sourceCoefficient 76 86 1 0) v4531_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4531_pb : Scalar.QComplex := ((-984620967790311995453306 : Int)/10^30,(-431476394296660815104101213 : Int)/10^30)
theorem v4531_pb_checked : Scalar.distance (sourceCoefficient 76 86 1 1) v4531_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4531_pg : Scalar.QComplex := ((-93086187175137554860355 : Int)/10^30,(212420917843484863572 : Int)/10^30)
theorem v4531_pg_checked : Scalar.distance (sourceCoefficient 76 86 1 2) v4531_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4531_mb : Scalar.QComplex := ((-1356965296473531404087585 : Int)/10^30,(-431475383954730252238476373 : Int)/10^30)
theorem v4531_mb_checked : Scalar.distance (sourceCoefficient 76 86 3 1) v4531_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4531_mg : Scalar.QComplex := ((-93085969205210804703998 : Int)/10^30,(292750025835373296459 : Int)/10^30)
theorem v4531_mg_checked : Scalar.distance (sourceCoefficient 76 86 3 2) v4531_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4531_upper : Scalar.QComplex := ((999991968430625012099673640123 : Int)/10^30,(-4007876525526850036118602148 : Int)/10^30)
theorem v4531_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 86 5) 1) 14) v4531_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4531 : Material (76 : Basis) (86 : Basis) where
  plus := ![v4531_pa,v4531_pb,v4531_pg]
  minus := ![(Primitive.Addresses.material4531 1).one,v4531_mb,v4531_mg]
  upper := v4531_upper
  lower := (Primitive.Addresses.material4531 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4531_pa_checked.trans (by decide +kernel)
    · exact v4531_pb_checked.trans (by decide +kernel)
    · exact v4531_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 86 Primitive.Addresses.material4531
    · exact v4531_mb_checked.trans (by decide +kernel)
    · exact v4531_mg_checked.trans (by decide +kernel)
  upper_error := v4531_upper_checked
  lower_error := reuse_lower_error 76 86 Primitive.Addresses.material4531

def v4532_pa : Scalar.QComplex := ((999997394087048156824931344368 : Int)/10^30,(-2282940891241829229262055026 : Int)/10^30)
theorem v4532_pa_checked : Scalar.distance (sourceCoefficient 76 87 1 0) v4532_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4532_pb : Scalar.QComplex := ((-985037668828840080802048 : Int)/10^30,(-431476393315904394424865732 : Int)/10^30)
theorem v4532_pb_checked : Scalar.distance (sourceCoefficient 76 87 1 1) v4532_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4532_pg : Scalar.QComplex := ((-93086186966748822520942 : Int)/10^30,(212510816420862023000 : Int)/10^30)
theorem v4532_pg_checked : Scalar.distance (sourceCoefficient 76 87 1 2) v4532_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4532_mb : Scalar.QComplex := ((-1357381996510554029197338 : Int)/10^30,(-431475382614379968008033723 : Int)/10^30)
theorem v4532_mb_checked : Scalar.distance (sourceCoefficient 76 87 3 1) v4532_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4532_mg : Scalar.QComplex := ((-93085968919243726562369 : Int)/10^30,(292839924199447016433 : Int)/10^30)
theorem v4532_mg_checked : Scalar.distance (sourceCoefficient 76 87 3 2) v4532_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4532_upper : Scalar.QComplex := ((999991964559526106176114026205 : Int)/10^30,(-4008842274208856708551934146 : Int)/10^30)
theorem v4532_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 87 5) 1) 14) v4532_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4532 : Material (76 : Basis) (87 : Basis) where
  plus := ![v4532_pa,v4532_pb,v4532_pg]
  minus := ![(Primitive.Addresses.material4532 1).one,v4532_mb,v4532_mg]
  upper := v4532_upper
  lower := (Primitive.Addresses.material4532 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4532_pa_checked.trans (by decide +kernel)
    · exact v4532_pb_checked.trans (by decide +kernel)
    · exact v4532_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 87 Primitive.Addresses.material4532
    · exact v4532_mb_checked.trans (by decide +kernel)
    · exact v4532_mg_checked.trans (by decide +kernel)
  upper_error := v4532_upper_checked
  lower_error := reuse_lower_error 76 87 Primitive.Addresses.material4532

def v4533_pa : Scalar.QComplex := ((999997367171447325228574000691 : Int)/10^30,(-2294700453994672279885061878 : Int)/10^30)
theorem v4533_pa_checked : Scalar.distance (sourceCoefficient 76 88 1 0) v4533_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4533_pb : Scalar.QComplex := ((-990111654921580920207585 : Int)/10^30,(-431476381330617147293639520 : Int)/10^30)
theorem v4533_pb_checked : Scalar.distance (sourceCoefficient 76 88 1 1) v4533_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4533_pg : Scalar.QComplex := ((-93086184421164660215518 : Int)/10^30,(213605472038464126309 : Int)/10^30)
theorem v4533_pg_checked : Scalar.distance (sourceCoefficient 76 88 1 2) v4533_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4533_mb : Scalar.QComplex := ((-1362455970371254856680439 : Int)/10^30,(-431475366250475709362072862 : Int)/10^30)
theorem v4533_mb_checked : Scalar.distance (sourceCoefficient 76 88 3 1) v4533_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4533_mg : Scalar.QComplex := ((-93085965429022015562513 : Int)/10^30,(293934577212734321860 : Int)/10^30)
theorem v4533_mg_checked : Scalar.distance (sourceCoefficient 76 88 3 2) v4533_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4533_upper : Scalar.QComplex := ((999991917348026869997765063758 : Int)/10^30,(-4020601772993327142990600969 : Int)/10^30)
theorem v4533_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 88 5) 1) 14) v4533_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4533 : Material (76 : Basis) (88 : Basis) where
  plus := ![v4533_pa,v4533_pb,v4533_pg]
  minus := ![(Primitive.Addresses.material4533 1).one,v4533_mb,v4533_mg]
  upper := v4533_upper
  lower := (Primitive.Addresses.material4533 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4533_pa_checked.trans (by decide +kernel)
    · exact v4533_pb_checked.trans (by decide +kernel)
    · exact v4533_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 88 Primitive.Addresses.material4533
    · exact v4533_mb_checked.trans (by decide +kernel)
    · exact v4533_mg_checked.trans (by decide +kernel)
  upper_error := v4533_upper_checked
  lower_error := reuse_lower_error 76 88 Primitive.Addresses.material4533

def v4534_pa : Scalar.QComplex := ((999997330121464461881198288917 : Int)/10^30,(-2310789895863499546008407972 : Int)/10^30)
theorem v4534_pa_checked : Scalar.distance (sourceCoefficient 76 89 1 0) v4534_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4534_pb : Scalar.QComplex := ((-997053886104491450421480 : Int)/10^30,(-431476364803448528171104374 : Int)/10^30)
theorem v4534_pb_checked : Scalar.distance (sourceCoefficient 76 89 1 1) v4534_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4534_pg : Scalar.QComplex := ((-93086180913963825194901 : Int)/10^30,(215103180599874156198 : Int)/10^30)
theorem v4534_pg_checked : Scalar.distance (sourceCoefficient 76 89 1 2) v4534_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4534_mb : Scalar.QComplex := ((-1369398184707053279598013 : Int)/10^30,(-431475343732480399693708720 : Int)/10^30)
theorem v4534_mb_checked : Scalar.distance (sourceCoefficient 76 89 3 1) v4534_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4534_mg : Scalar.QComplex := ((-93085960629367452225783 : Int)/10^30,(295432282189922643513 : Int)/10^30)
theorem v4534_mg_checked : Scalar.distance (sourceCoefficient 76 89 3 2) v4534_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4534_upper : Scalar.QComplex := ((999991852529182145416198961404 : Int)/10^30,(-4036691126953911470154751178 : Int)/10^30)
theorem v4534_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 89 5) 1) 14) v4534_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4534 : Material (76 : Basis) (89 : Basis) where
  plus := ![v4534_pa,v4534_pb,v4534_pg]
  minus := ![(Primitive.Addresses.material4534 1).one,v4534_mb,v4534_mg]
  upper := v4534_upper
  lower := (Primitive.Addresses.material4534 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4534_pa_checked.trans (by decide +kernel)
    · exact v4534_pb_checked.trans (by decide +kernel)
    · exact v4534_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 89 Primitive.Addresses.material4534
    · exact v4534_mb_checked.trans (by decide +kernel)
    · exact v4534_mg_checked.trans (by decide +kernel)
  upper_error := v4534_upper_checked
  lower_error := reuse_lower_error 76 89 Primitive.Addresses.material4534

def v4535_pa : Scalar.QComplex := ((999997269228675429553846532532 : Int)/10^30,(-2336992766790018374854018478 : Int)/10^30)
theorem v4535_pa_checked : Scalar.distance (sourceCoefficient 76 90 1 0) v4535_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4535_pb : Scalar.QComplex := ((-1008359833539766721040021 : Int)/10^30,(-431476337568934608769980095 : Int)/10^30)
theorem v4535_pb_checked : Scalar.distance (sourceCoefficient 76 90 1 1) v4535_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4535_pg : Scalar.QComplex := ((-93086175142047382556411 : Int)/10^30,(217542312053421180509 : Int)/10^30)
theorem v4535_pg_checked : Scalar.distance (sourceCoefficient 76 90 1 2) v4535_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4535_mb : Scalar.QComplex := ((-1380704104430448697270259 : Int)/10^30,(-431475306741453185274293139 : Int)/10^30)
theorem v4535_mb_checked : Scalar.distance (sourceCoefficient 76 90 3 1) v4535_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4535_mg : Scalar.QComplex := ((-93085952752592568727172 : Int)/10^30,(297871407754365621323 : Int)/10^30)
theorem v4535_mg_checked : Scalar.distance (sourceCoefficient 76 90 3 2) v4535_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4535_upper : Scalar.QComplex := ((999991746412705692455164475475 : Int)/10^30,(-4062893853758902340259390832 : Int)/10^30)
theorem v4535_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 90 5) 1) 14) v4535_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4535 : Material (76 : Basis) (90 : Basis) where
  plus := ![v4535_pa,v4535_pb,v4535_pg]
  minus := ![(Primitive.Addresses.material4535 1).one,v4535_mb,v4535_mg]
  upper := v4535_upper
  lower := (Primitive.Addresses.material4535 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4535_pa_checked.trans (by decide +kernel)
    · exact v4535_pb_checked.trans (by decide +kernel)
    · exact v4535_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 90 Primitive.Addresses.material4535
    · exact v4535_mb_checked.trans (by decide +kernel)
    · exact v4535_mg_checked.trans (by decide +kernel)
  upper_error := v4535_upper_checked
  lower_error := reuse_lower_error 76 90 Primitive.Addresses.material4535

def v4536_pa : Scalar.QComplex := ((999997234623214991222356307004 : Int)/10^30,(-2351753797213643752619641096 : Int)/10^30)
theorem v4536_pa_checked : Scalar.distance (sourceCoefficient 76 91 1 0) v4536_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4536_pb : Scalar.QComplex := ((-1014728884903166918164533 : Int)/10^30,(-431476322052806834903965848 : Int)/10^30)
theorem v4536_pb_checked : Scalar.distance (sourceCoefficient 76 91 1 1) v4536_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4536_pg : Scalar.QComplex := ((-93086171857682834661911 : Int)/10^30,(218916363520616967567 : Int)/10^30)
theorem v4536_pg_checked : Scalar.distance (sourceCoefficient 76 91 1 2) v4536_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4536_mb : Scalar.QComplex := ((-1387073140032640543381055 : Int)/10^30,(-431475285729126713582383170 : Int)/10^30)
theorem v4536_mb_checked : Scalar.distance (sourceCoefficient 76 91 3 1) v4536_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4536_mg : Scalar.QComplex := ((-93085948282484712542537 : Int)/10^30,(299245455875680567345 : Int)/10^30)
theorem v4536_mg_checked : Scalar.distance (sourceCoefficient 76 91 3 2) v4536_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4536_upper : Scalar.QComplex := ((999991686331097393934028502609 : Int)/10^30,(-4077654802471821520759387975 : Int)/10^30)
theorem v4536_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 91 5) 1) 14) v4536_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4536 : Material (76 : Basis) (91 : Basis) where
  plus := ![v4536_pa,v4536_pb,v4536_pg]
  minus := ![(Primitive.Addresses.material4536 1).one,v4536_mb,v4536_mg]
  upper := v4536_upper
  lower := (Primitive.Addresses.material4536 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4536_pa_checked.trans (by decide +kernel)
    · exact v4536_pb_checked.trans (by decide +kernel)
    · exact v4536_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 91 Primitive.Addresses.material4536
    · exact v4536_mb_checked.trans (by decide +kernel)
    · exact v4536_mg_checked.trans (by decide +kernel)
  upper_error := v4536_upper_checked
  lower_error := reuse_lower_error 76 91 Primitive.Addresses.material4536

def v4537_pa : Scalar.QComplex := ((999997158959729675746386314034 : Int)/10^30,(-2383709812275539890085404878 : Int)/10^30)
theorem v4537_pa_checked : Scalar.distance (sourceCoefficient 76 92 1 0) v4537_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4537_pb : Scalar.QComplex := ((-1028517183606400047918034 : Int)/10^30,(-431476288032653268565007280 : Int)/10^30)
theorem v4537_pb_checked : Scalar.distance (sourceCoefficient 76 92 1 1) v4537_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4537_pg : Scalar.QComplex := ((-93086164666327922791241 : Int)/10^30,(221891034503587175747 : Int)/10^30)
theorem v4537_pg_checked : Scalar.distance (sourceCoefficient 76 92 1 2) v4537_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4537_mb : Scalar.QComplex := ((-1400861404243999592627534 : Int)/10^30,(-431475239810305035532122914 : Int)/10^30)
theorem v4537_mb_checked : Scalar.distance (sourceCoefficient 76 92 3 1) v4537_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4537_mg : Scalar.QComplex := ((-93085938524125394246388 : Int)/10^30,(302220119545229417043 : Int)/10^30)
theorem v4537_mg_checked : Scalar.distance (sourceCoefficient 76 92 3 2) v4537_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4537_upper : Scalar.QComplex := ((999991555514541800539104059243 : Int)/10^30,(-4109610639350675524007897035 : Int)/10^30)
theorem v4537_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 92 5) 1) 14) v4537_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4537 : Material (76 : Basis) (92 : Basis) where
  plus := ![v4537_pa,v4537_pb,v4537_pg]
  minus := ![(Primitive.Addresses.material4537 1).one,v4537_mb,v4537_mg]
  upper := v4537_upper
  lower := (Primitive.Addresses.material4537 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4537_pa_checked.trans (by decide +kernel)
    · exact v4537_pb_checked.trans (by decide +kernel)
    · exact v4537_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 92 Primitive.Addresses.material4537
    · exact v4537_mb_checked.trans (by decide +kernel)
    · exact v4537_mg_checked.trans (by decide +kernel)
  upper_error := v4537_upper_checked
  lower_error := reuse_lower_error 76 92 Primitive.Addresses.material4537

def v4538_pa : Scalar.QComplex := ((999997067836902983474722621590 : Int)/10^30,(-2421635314503945503034944597 : Int)/10^30)
theorem v4538_pa_checked : Scalar.distance (sourceCoefficient 76 93 1 0) v4538_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4538_pb : Scalar.QComplex := ((-1044881180612735984072094 : Int)/10^30,(-431476246895058662850207201 : Int)/10^30)
theorem v4538_pb_checked : Scalar.distance (sourceCoefficient 76 93 1 1) v4538_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4538_pg : Scalar.QComplex := ((-93086155987691572799764 : Int)/10^30,(225421383603479092264 : Int)/10^30)
theorem v4538_pg_checked : Scalar.distance (sourceCoefficient 76 93 1 2) v4538_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4538_mb : Scalar.QComplex := ((-1417225359657380195465098 : Int)/10^30,(-431475184551333337822139647 : Int)/10^30)
theorem v4538_mb_checked : Scalar.distance (sourceCoefficient 76 93 3 1) v4538_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4538_mg : Scalar.QComplex := ((-93085926798960003522198 : Int)/10^30,(305750459841338719975 : Int)/10^30)
theorem v4538_mg_checked : Scalar.distance (sourceCoefficient 76 93 3 2) v4538_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4538_upper : Scalar.QComplex := ((999991398935874553471537852547 : Int)/10^30,(-4147535927823768337590197064 : Int)/10^30)
theorem v4538_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 93 5) 1) 14) v4538_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4538 : Material (76 : Basis) (93 : Basis) where
  plus := ![v4538_pa,v4538_pb,v4538_pg]
  minus := ![(Primitive.Addresses.material4538 1).one,v4538_mb,v4538_mg]
  upper := v4538_upper
  lower := (Primitive.Addresses.material4538 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4538_pa_checked.trans (by decide +kernel)
    · exact v4538_pb_checked.trans (by decide +kernel)
    · exact v4538_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 93 Primitive.Addresses.material4538
    · exact v4538_mb_checked.trans (by decide +kernel)
    · exact v4538_mg_checked.trans (by decide +kernel)
  upper_error := v4538_upper_checked
  lower_error := reuse_lower_error 76 93 Primitive.Addresses.material4538

def v4539_pa : Scalar.QComplex := ((999996958347681712171813812158 : Int)/10^30,(-2466433738199109014664390007 : Int)/10^30)
theorem v4539_pa_checked : Scalar.distance (sourceCoefficient 76 94 1 0) v4539_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4539_pb : Scalar.QComplex := ((-1064210687052676673703165 : Int)/10^30,(-431476197236425596106510132 : Int)/10^30)
theorem v4539_pb_checked : Scalar.distance (sourceCoefficient 76 94 1 1) v4539_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4539_pg : Scalar.QComplex := ((-93086145535064991531411 : Int)/10^30,(229591508244139957839 : Int)/10^30)
theorem v4539_pg_checked : Scalar.distance (sourceCoefficient 76 94 1 2) v4539_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4539_mb : Scalar.QComplex := ((-1436554816046898440630178 : Int)/10^30,(-431475118212225272241257275 : Int)/10^30)
theorem v4539_mb_checked : Scalar.distance (sourceCoefficient 76 94 3 1) v4539_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4539_mg : Scalar.QComplex := ((-93085912747707564795880 : Int)/10^30,(309920573909125626912 : Int)/10^30)
theorem v4539_mg_checked : Scalar.distance (sourceCoefficient 76 94 3 2) v4539_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4539_upper : Scalar.QComplex := ((999991212128801136900748893660 : Int)/10^30,(-4192334095828479018077994720 : Int)/10^30)
theorem v4539_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 94 5) 1) 14) v4539_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4539 : Material (76 : Basis) (94 : Basis) where
  plus := ![v4539_pa,v4539_pb,v4539_pg]
  minus := ![(Primitive.Addresses.material4539 1).one,v4539_mb,v4539_mg]
  upper := v4539_upper
  lower := (Primitive.Addresses.material4539 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4539_pa_checked.trans (by decide +kernel)
    · exact v4539_pb_checked.trans (by decide +kernel)
    · exact v4539_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 94 Primitive.Addresses.material4539
    · exact v4539_mb_checked.trans (by decide +kernel)
    · exact v4539_mg_checked.trans (by decide +kernel)
  upper_error := v4539_upper_checked
  lower_error := reuse_lower_error 76 94 Primitive.Addresses.material4539

def v4540_pa : Scalar.QComplex := ((999996848168142286078289073661 : Int)/10^30,(-2510707824774476645129144844 : Int)/10^30)
theorem v4540_pa_checked : Scalar.distance (sourceCoefficient 76 95 1 0) v4540_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4540_pb : Scalar.QComplex := ((-1083313952961691515377891 : Int)/10^30,(-431476147024622673066892937 : Int)/10^30)
theorem v4540_pb_checked : Scalar.distance (sourceCoefficient 76 95 1 1) v4540_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4540_pg : Scalar.QComplex := ((-93086134990638691439742 : Int)/10^30,(233712824122534392585 : Int)/10^30)
theorem v4540_pg_checked : Scalar.distance (sourceCoefficient 76 95 1 2) v4540_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4540_mb : Scalar.QComplex := ((-1455658031512369855067764 : Int)/10^30,(-431475051515182945028619118 : Int)/10^30)
theorem v4540_mb_checked : Scalar.distance (sourceCoefficient 76 95 3 1) v4540_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4540_mg : Scalar.QComplex := ((-93085898646775204998360 : Int)/10^30,(314041879153600813043 : Int)/10^30)
theorem v4540_mg_checked : Scalar.distance (sourceCoefficient 76 95 3 2) v4540_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4540_upper : Scalar.QComplex := ((999991025536368894962904962918 : Int)/10^30,(-4236607926302905854377504282 : Int)/10^30)
theorem v4540_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 95 5) 1) 14) v4540_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4540 : Material (76 : Basis) (95 : Basis) where
  plus := ![v4540_pa,v4540_pb,v4540_pg]
  minus := ![(Primitive.Addresses.material4540 1).one,v4540_mb,v4540_mg]
  upper := v4540_upper
  lower := (Primitive.Addresses.material4540 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4540_pa_checked.trans (by decide +kernel)
    · exact v4540_pb_checked.trans (by decide +kernel)
    · exact v4540_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 95 Primitive.Addresses.material4540
    · exact v4540_mb_checked.trans (by decide +kernel)
    · exact v4540_mg_checked.trans (by decide +kernel)
  upper_error := v4540_upper_checked
  lower_error := reuse_lower_error 76 95 Primitive.Addresses.material4540

def v4541_pa : Scalar.QComplex := ((999996794554128256327294321035 : Int)/10^30,(-2531971853833313987694962957 : Int)/10^30)
theorem v4541_pa_checked : Scalar.distance (sourceCoefficient 76 96 1 0) v4541_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4541_pb : Scalar.QComplex := ((-1092488899705277623741891 : Int)/10^30,(-431476122507942053900148916 : Int)/10^30)
theorem v4541_pb_checked : Scalar.distance (sourceCoefficient 76 96 1 1) v4541_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4541_pg : Scalar.QComplex := ((-93086129850670845303636 : Int)/10^30,(235692216262813269293 : Int)/10^30)
theorem v4541_pg_checked : Scalar.distance (sourceCoefficient 76 96 1 2) v4541_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4541_mb : Scalar.QComplex := ((-1464832953682912790978570 : Int)/10^30,(-431475019080945639089451231 : Int)/10^30)
theorem v4541_mb_checked : Scalar.distance (sourceCoefficient 76 96 3 1) v4541_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4541_mg : Scalar.QComplex := ((-93085891798683004159170 : Int)/10^30,(316021266121300777578 : Int)/10^30)
theorem v4541_mg_checked : Scalar.distance (sourceCoefficient 76 96 3 2) v4541_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4541_upper : Scalar.QComplex := ((999990935222649619081856105726 : Int)/10^30,(-4257871831158545372131069322 : Int)/10^30)
theorem v4541_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 96 5) 1) 14) v4541_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4541 : Material (76 : Basis) (96 : Basis) where
  plus := ![v4541_pa,v4541_pb,v4541_pg]
  minus := ![(Primitive.Addresses.material4541 1).one,v4541_mb,v4541_mg]
  upper := v4541_upper
  lower := (Primitive.Addresses.material4541 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4541_pa_checked.trans (by decide +kernel)
    · exact v4541_pb_checked.trans (by decide +kernel)
    · exact v4541_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 96 Primitive.Addresses.material4541
    · exact v4541_mb_checked.trans (by decide +kernel)
    · exact v4541_mg_checked.trans (by decide +kernel)
  upper_error := v4541_upper_checked
  lower_error := reuse_lower_error 76 96 Primitive.Addresses.material4541

def v4542_pa : Scalar.QComplex := ((999996606633091376332881542087 : Int)/10^30,(-2605133835776649248265867825 : Int)/10^30)
theorem v4542_pa_checked : Scalar.distance (sourceCoefficient 76 97 1 0) v4542_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4542_pb : Scalar.QComplex := ((-1124056635483367999334342 : Int)/10^30,(-431476036167513133575108856 : Int)/10^30)
theorem v4542_pb_checked : Scalar.distance (sourceCoefficient 76 97 1 1) v4542_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4542_pg : Scalar.QComplex := ((-93086111790732641342801 : Int)/10^30,(242502602367231430234 : Int)/10^30)
theorem v4542_pg_checked : Scalar.distance (sourceCoefficient 76 97 1 2) v4542_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4542_mb : Scalar.QComplex := ((-1496400603198990889916644 : Int)/10^30,(-431474905499014648801362446 : Int)/10^30)
theorem v4542_mb_checked : Scalar.distance (sourceCoefficient 76 97 3 1) v4542_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4542_mg : Scalar.QComplex := ((-93085867861695045029684 : Int)/10^30,(322831634104987661227 : Int)/10^30)
theorem v4542_mg_checked : Scalar.distance (sourceCoefficient 76 97 3 2) v4542_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4542_upper : Scalar.QComplex := ((999990621030948994355374281963 : Int)/10^30,(-4331033379801041146636735118 : Int)/10^30)
theorem v4542_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 76 97 5) 1) 14) v4542_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4542 : Material (76 : Basis) (97 : Basis) where
  plus := ![v4542_pa,v4542_pb,v4542_pg]
  minus := ![(Primitive.Addresses.material4542 1).one,v4542_mb,v4542_mg]
  upper := v4542_upper
  lower := (Primitive.Addresses.material4542 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4542_pa_checked.trans (by decide +kernel)
    · exact v4542_pb_checked.trans (by decide +kernel)
    · exact v4542_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 76 97 Primitive.Addresses.material4542
    · exact v4542_mb_checked.trans (by decide +kernel)
    · exact v4542_mg_checked.trans (by decide +kernel)
  upper_error := v4542_upper_checked
  lower_error := reuse_lower_error 76 97 Primitive.Addresses.material4542

def v4543_pa : Scalar.QComplex := ((999997811676246136925523091715 : Int)/10^30,(-2092042714421791444421936194 : Int)/10^30)
theorem v4543_pa_checked : Scalar.distance (sourceCoefficient 77 78 1 0) v4543_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4543_pb : Scalar.QComplex := ((-902669404201166426857860 : Int)/10^30,(-431476576766622461738048512 : Int)/10^30)
theorem v4543_pb_checked : Scalar.distance (sourceCoefficient 77 78 1 1) v4543_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4543_pg : Scalar.QComplex := ((-93086226191408806661511 : Int)/10^30,(194740787472646809566 : Int)/10^30)
theorem v4543_pg_checked : Scalar.distance (sourceCoefficient 77 78 1 2) v4543_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4543_mb : Scalar.QComplex := ((-1275013920862057090256467 : Int)/10^30,(-431475637145132372989911945 : Int)/10^30)
theorem v4543_mb_checked : Scalar.distance (sourceCoefficient 77 78 3 1) v4543_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4543_mg : Scalar.QComplex := ((-93086023478623755485006 : Int)/10^30,(275069935716940664070 : Int)/10^30)
theorem v4543_mg_checked : Scalar.distance (sourceCoefficient 77 78 3 2) v4543_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4543_upper : Scalar.QComplex := ((999992711621037180285833035190 : Int)/10^30,(-3817945102430301139617072162 : Int)/10^30)
theorem v4543_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 78 5) 1) 14) v4543_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4543 : Material (77 : Basis) (78 : Basis) where
  plus := ![v4543_pa,v4543_pb,v4543_pg]
  minus := ![(Primitive.Addresses.material4543 1).one,v4543_mb,v4543_mg]
  upper := v4543_upper
  lower := (Primitive.Addresses.material4543 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4543_pa_checked.trans (by decide +kernel)
    · exact v4543_pb_checked.trans (by decide +kernel)
    · exact v4543_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 78 Primitive.Addresses.material4543
    · exact v4543_mb_checked.trans (by decide +kernel)
    · exact v4543_mg_checked.trans (by decide +kernel)
  upper_error := v4543_upper_checked
  lower_error := reuse_lower_error 77 78 Primitive.Addresses.material4543

def v4544_pa : Scalar.QComplex := ((999997799993202434344947971387 : Int)/10^30,(-2097619783254677632372243268 : Int)/10^30)
theorem v4544_pa_checked : Scalar.distance (sourceCoefficient 77 79 1 0) v4544_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4544_pb : Scalar.QComplex := ((-905075784001710643062882 : Int)/10^30,(-431476571709538503874722740 : Int)/10^30)
theorem v4544_pb_checked : Scalar.distance (sourceCoefficient 77 79 1 1) v4544_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4544_pg : Scalar.QComplex := ((-93086225102137854578585 : Int)/10^30,(195259936895931002062 : Int)/10^30)
theorem v4544_pg_checked : Scalar.distance (sourceCoefficient 77 79 1 2) v4544_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4544_mb : Scalar.QComplex := ((-1277420295402560436699486 : Int)/10^30,(-431475630011452909563392184 : Int)/10^30)
theorem v4544_mb_checked : Scalar.distance (sourceCoefficient 77 79 3 1) v4544_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4544_mg : Scalar.QComplex := ((-93086021941350638315238 : Int)/10^30,(275589084006930027271 : Int)/10^30)
theorem v4544_mg_checked : Scalar.distance (sourceCoefficient 77 79 3 2) v4544_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4544_upper : Scalar.QComplex := ((999992690312496020397178431587 : Int)/10^30,(-3823522142792924876300099194 : Int)/10^30)
theorem v4544_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 79 5) 1) 14) v4544_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4544 : Material (77 : Basis) (79 : Basis) where
  plus := ![v4544_pa,v4544_pb,v4544_pg]
  minus := ![(Primitive.Addresses.material4544 1).one,v4544_mb,v4544_mg]
  upper := v4544_upper
  lower := (Primitive.Addresses.material4544 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4544_pa_checked.trans (by decide +kernel)
    · exact v4544_pb_checked.trans (by decide +kernel)
    · exact v4544_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 79 Primitive.Addresses.material4544
    · exact v4544_mb_checked.trans (by decide +kernel)
    · exact v4544_mg_checked.trans (by decide +kernel)
  upper_error := v4544_upper_checked
  lower_error := reuse_lower_error 77 79 Primitive.Addresses.material4544

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
