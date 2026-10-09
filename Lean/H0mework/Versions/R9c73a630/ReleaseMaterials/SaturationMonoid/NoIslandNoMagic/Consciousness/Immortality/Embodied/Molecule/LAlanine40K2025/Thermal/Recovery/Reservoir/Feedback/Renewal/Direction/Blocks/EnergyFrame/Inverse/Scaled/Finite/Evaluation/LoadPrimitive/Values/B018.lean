import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B012

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v289_pa : Scalar.QComplex := ((999966971360177941990436955097 : Int)/10^30,(8127495847619211419485132057 : Int)/10^30)
theorem v289_pa_checked : Scalar.distance (sourceCoefficient 3 5 1 0) v289_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v289_pb : Scalar.QComplex := ((3506831759740604503391899 : Int)/10^30,(-431463269819414094538540522 : Int)/10^30)
theorem v289_pb_checked : Scalar.distance (sourceCoefficient 3 5 1 1) v289_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v289_pg : Scalar.QComplex := ((-93083355371733768491767 : Int)/10^30,(-756559572399850346094 : Int)/10^30)
theorem v289_pg_checked : Scalar.distance (sourceCoefficient 3 5 1 2) v289_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v289_mb : Scalar.QComplex := ((3134497084517024512315427 : Int)/10^30,(-431466135403786711968834818 : Int)/10^30)
theorem v289_mb_checked : Scalar.distance (sourceCoefficient 3 5 3 1) v289_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v289_mg : Scalar.QComplex := ((-93083973589383246919942 : Int)/10^30,(-676232547331038576331 : Int)/10^30)
theorem v289_mg_checked : Scalar.distance (sourceCoefficient 3 5 3 2) v289_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v289_upper : Scalar.QComplex := ((999979509347350799979278793760 : Int)/10^30,(6401631466396206978281249966 : Int)/10^30)
theorem v289_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 5 5) 1) 14) v289_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material289 : Material (3 : Basis) (5 : Basis) where
  plus := ![v289_pa,v289_pb,v289_pg]
  minus := ![(Primitive.Addresses.material289 1).one,v289_mb,v289_mg]
  upper := v289_upper
  lower := (Primitive.Addresses.material289 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v289_pa_checked.trans (by decide +kernel)
    · exact v289_pb_checked.trans (by decide +kernel)
    · exact v289_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 5 Primitive.Addresses.material289
    · exact v289_mb_checked.trans (by decide +kernel)
    · exact v289_mg_checked.trans (by decide +kernel)
  upper_error := v289_upper_checked
  lower_error := reuse_lower_error 3 5 Primitive.Addresses.material289

def v290_pa : Scalar.QComplex := ((999990784980489274604696585698 : Int)/10^30,(4293012241406517065409818924 : Int)/10^30)
theorem v290_pa_checked : Scalar.distance (sourceCoefficient 3 6 1 0) v290_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v290_pb : Scalar.QComplex := ((1852333668338106555736445 : Int)/10^30,(-431472470816980259316123248 : Int)/10^30)
theorem v290_pb_checked : Scalar.distance (sourceCoefficient 3 6 1 1) v290_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v290_pg : Scalar.QComplex := ((-93085456240106195768597 : Int)/10^30,(-399620685648101696795 : Int)/10^30)
theorem v290_pg_checked : Scalar.distance (sourceCoefficient 3 6 1 2) v290_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v290_mb : Scalar.QComplex := ((1479991669113278239026136 : Int)/10^30,(-431473908640589872369656623 : Int)/10^30)
theorem v290_mb_checked : Scalar.distance (sourceCoefficient 3 6 3 1) v290_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v290_mg : Scalar.QComplex := ((-93085766434790088820906 : Int)/10^30,(-319291980529164572016 : Int)/10^30)
theorem v290_mg_checked : Scalar.distance (sourceCoefficient 3 6 3 2) v290_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v290_upper : Scalar.QComplex := ((999996704961351854783341240192 : Int)/10^30,(2567112471048111391427304265 : Int)/10^30)
theorem v290_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 6 5) 1) 14) v290_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material290 : Material (3 : Basis) (6 : Basis) where
  plus := ![v290_pa,v290_pb,v290_pg]
  minus := ![(Primitive.Addresses.material290 1).one,v290_mb,v290_mg]
  upper := v290_upper
  lower := (Primitive.Addresses.material290 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v290_pa_checked.trans (by decide +kernel)
    · exact v290_pb_checked.trans (by decide +kernel)
    · exact v290_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 6 Primitive.Addresses.material290
    · exact v290_mb_checked.trans (by decide +kernel)
    · exact v290_mg_checked.trans (by decide +kernel)
  upper_error := v290_upper_checked
  lower_error := reuse_lower_error 3 6 Primitive.Addresses.material290

def v291_pa : Scalar.QComplex := ((999991038467371324837178733931 : Int)/10^30,(4233554646899372531230293504 : Int)/10^30)
theorem v291_pa_checked : Scalar.distance (sourceCoefficient 3 7 1 0) v291_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v291_pb : Scalar.QComplex := ((1826678975725074696376047 : Int)/10^30,(-431472546886731992957854798 : Int)/10^30)
theorem v291_pb_checked : Scalar.distance (sourceCoefficient 3 7 1 1) v291_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v291_pg : Scalar.QComplex := ((-93085476243796207946324 : Int)/10^30,(-394085982125151903264 : Int)/10^30)
theorem v291_pg_checked : Scalar.distance (sourceCoefficient 3 7 1 2) v291_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v291_mb : Scalar.QComplex := ((1454336920407891225175623 : Int)/10^30,(-431473962571469001182940031 : Int)/10^30)
theorem v291_mb_checked : Scalar.distance (sourceCoefficient 3 7 3 1) v291_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v291_mg : Scalar.QComplex := ((-93085781662272786198151 : Int)/10^30,(-313757261804754300772 : Int)/10^30)
theorem v291_mg_checked : Scalar.distance (sourceCoefficient 3 7 3 2) v291_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v291_upper : Scalar.QComplex := ((999996855829442197588660951088 : Int)/10^30,(2507654527600707227565105355 : Int)/10^30)
theorem v291_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 7 5) 1) 14) v291_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material291 : Material (3 : Basis) (7 : Basis) where
  plus := ![v291_pa,v291_pb,v291_pg]
  minus := ![(Primitive.Addresses.material291 1).one,v291_mb,v291_mg]
  upper := v291_upper
  lower := (Primitive.Addresses.material291 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v291_pa_checked.trans (by decide +kernel)
    · exact v291_pb_checked.trans (by decide +kernel)
    · exact v291_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 7 Primitive.Addresses.material291
    · exact v291_mb_checked.trans (by decide +kernel)
    · exact v291_mg_checked.trans (by decide +kernel)
  upper_error := v291_upper_checked
  lower_error := reuse_lower_error 3 7 Primitive.Addresses.material291

def v292_pa : Scalar.QComplex := ((999991200013491658639813103920 : Int)/10^30,(4195222947224637474407096873 : Int)/10^30)
theorem v292_pa_checked : Scalar.distance (sourceCoefficient 3 8 1 0) v292_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v292_pb : Scalar.QComplex := ((1810139660217242068189954 : Int)/10^30,(-431472594849851022437889433 : Int)/10^30)
theorem v292_pb_checked : Scalar.distance (sourceCoefficient 3 8 1 1) v292_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v292_pg : Scalar.QComplex := ((-93085488936422982339638 : Int)/10^30,(-390517815791217038395 : Int)/10^30)
theorem v292_pg_checked : Scalar.distance (sourceCoefficient 3 8 1 2) v292_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v292_mb : Scalar.QComplex := ((1437797569668390100865971 : Int)/10^30,(-431473996261885791660548267 : Int)/10^30)
theorem v292_mb_checked : Scalar.distance (sourceCoefficient 3 8 3 1) v292_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v292_mg : Scalar.QComplex := ((-93085791275727992606706 : Int)/10^30,(-310189085846245583671 : Int)/10^30)
theorem v292_mg_checked : Scalar.distance (sourceCoefficient 3 8 3 2) v292_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v292_upper : Scalar.QComplex := ((999996951218285713459231845881 : Int)/10^30,(2469322606202587731926528905 : Int)/10^30)
theorem v292_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 8 5) 1) 14) v292_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material292 : Material (3 : Basis) (8 : Basis) where
  plus := ![v292_pa,v292_pb,v292_pg]
  minus := ![(Primitive.Addresses.material292 1).one,v292_mb,v292_mg]
  upper := v292_upper
  lower := (Primitive.Addresses.material292 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v292_pa_checked.trans (by decide +kernel)
    · exact v292_pb_checked.trans (by decide +kernel)
    · exact v292_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 8 Primitive.Addresses.material292
    · exact v292_mb_checked.trans (by decide +kernel)
    · exact v292_mg_checked.trans (by decide +kernel)
  upper_error := v292_upper_checked
  lower_error := reuse_lower_error 3 8 Primitive.Addresses.material292

def v293_pa : Scalar.QComplex := ((999991288556285887203924044254 : Int)/10^30,(4174064151276787456049780233 : Int)/10^30)
theorem v293_pa_checked : Scalar.distance (sourceCoefficient 3 9 1 0) v293_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v293_pb : Scalar.QComplex := ((1801010088817218823187071 : Int)/10^30,(-431472620963025379622657652 : Int)/10^30)
theorem v293_pb_checked : Scalar.distance (sourceCoefficient 3 9 1 1) v293_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v293_pg : Scalar.QComplex := ((-93085495874300677485485 : Int)/10^30,(-388548216148656955643 : Int)/10^30)
theorem v293_pg_checked : Scalar.distance (sourceCoefficient 3 9 1 2) v293_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v293_mb : Scalar.QComplex := ((1428667979133230153580839 : Int)/10^30,(-431474014496641488129126349 : Int)/10^30)
theorem v293_mb_checked : Scalar.distance (sourceCoefficient 3 9 3 1) v293_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v293_mg : Scalar.QComplex := ((-93085796513927320409183 : Int)/10^30,(-308219480949981482496 : Int)/10^30)
theorem v293_mg_checked : Scalar.distance (sourceCoefficient 3 9 3 2) v293_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v293_upper : Scalar.QComplex := ((999997003242785772917166986645 : Int)/10^30,(2448163688951448492167861781 : Int)/10^30)
theorem v293_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 9 5) 1) 14) v293_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material293 : Material (3 : Basis) (9 : Basis) where
  plus := ![v293_pa,v293_pb,v293_pg]
  minus := ![(Primitive.Addresses.material293 1).one,v293_mb,v293_mg]
  upper := v293_upper
  lower := (Primitive.Addresses.material293 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v293_pa_checked.trans (by decide +kernel)
    · exact v293_pb_checked.trans (by decide +kernel)
    · exact v293_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 9 Primitive.Addresses.material293
    · exact v293_mb_checked.trans (by decide +kernel)
    · exact v293_mg_checked.trans (by decide +kernel)
  upper_error := v293_upper_checked
  lower_error := reuse_lower_error 3 9 Primitive.Addresses.material293

def v294_pa : Scalar.QComplex := ((999991462468518279696334639798 : Int)/10^30,(4132189501220485648582551611 : Int)/10^30)
theorem v294_pa_checked : Scalar.distance (sourceCoefficient 3 10 1 0) v294_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v294_pb : Scalar.QComplex := ((1782942066744333782170580 : Int)/10^30,(-431472671883441614952247949 : Int)/10^30)
theorem v294_pb_checked : Scalar.distance (sourceCoefficient 3 10 1 1) v294_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v294_pg : Scalar.QComplex := ((-93085509461487722329490 : Int)/10^30,(-384650248876128980479 : Int)/10^30)
theorem v294_pg_checked : Scalar.distance (sourceCoefficient 3 10 1 2) v294_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v294_mb : Scalar.QComplex := ((1410599919845869639024919 : Int)/10^30,(-431474049825149468066996503 : Int)/10^30)
theorem v294_mb_checked : Scalar.distance (sourceCoefficient 3 10 3 1) v294_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v294_mg : Scalar.QComplex := ((-93085806737339107859781 : Int)/10^30,(-304321503403714393286 : Int)/10^30)
theorem v294_mg_checked : Scalar.distance (sourceCoefficient 3 10 3 2) v294_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v294_upper : Scalar.QComplex := ((999997104882911984969884401452 : Int)/10^30,(2406288801105783086665803941 : Int)/10^30)
theorem v294_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 10 5) 1) 14) v294_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material294 : Material (3 : Basis) (10 : Basis) where
  plus := ![v294_pa,v294_pb,v294_pg]
  minus := ![(Primitive.Addresses.material294 1).one,v294_mb,v294_mg]
  upper := v294_upper
  lower := (Primitive.Addresses.material294 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v294_pa_checked.trans (by decide +kernel)
    · exact v294_pb_checked.trans (by decide +kernel)
    · exact v294_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 10 Primitive.Addresses.material294
    · exact v294_mb_checked.trans (by decide +kernel)
    · exact v294_mg_checked.trans (by decide +kernel)
  upper_error := v294_upper_checked
  lower_error := reuse_lower_error 3 10 Primitive.Addresses.material294

def v295_pa : Scalar.QComplex := ((999991499671344851191186692492 : Int)/10^30,(4123176573312180148967985393 : Int)/10^30)
theorem v295_pa_checked : Scalar.distance (sourceCoefficient 3 11 1 0) v295_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v295_pb : Scalar.QComplex := ((1779053179916568747232039 : Int)/10^30,(-431472682711409861914965614 : Int)/10^30)
theorem v295_pb_checked : Scalar.distance (sourceCoefficient 3 11 1 1) v295_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v295_pg : Scalar.QComplex := ((-93085512361032854824886 : Int)/10^30,(-383811266403678014350 : Int)/10^30)
theorem v295_pg_checked : Scalar.distance (sourceCoefficient 3 11 1 2) v295_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v295_mb : Scalar.QComplex := ((1406711025122065977429138 : Int)/10^30,(-431474057297179499881935563 : Int)/10^30)
theorem v295_mb_checked : Scalar.distance (sourceCoefficient 3 11 3 1) v295_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v295_mg : Scalar.QComplex := ((-93085808912879073364689 : Int)/10^30,(-303482518741478086366 : Int)/10^30)
theorem v295_mg_checked : Scalar.distance (sourceCoefficient 3 11 3 2) v295_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v295_upper : Scalar.QComplex := ((999997126530187223922154929610 : Int)/10^30,(2397275822412471325250529424 : Int)/10^30)
theorem v295_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 11 5) 1) 14) v295_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material295 : Material (3 : Basis) (11 : Basis) where
  plus := ![v295_pa,v295_pb,v295_pg]
  minus := ![(Primitive.Addresses.material295 1).one,v295_mb,v295_mg]
  upper := v295_upper
  lower := (Primitive.Addresses.material295 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v295_pa_checked.trans (by decide +kernel)
    · exact v295_pb_checked.trans (by decide +kernel)
    · exact v295_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 11 Primitive.Addresses.material295
    · exact v295_mb_checked.trans (by decide +kernel)
    · exact v295_mg_checked.trans (by decide +kernel)
  upper_error := v295_upper_checked
  lower_error := reuse_lower_error 3 11 Primitive.Addresses.material295

def v296_pa : Scalar.QComplex := ((999991519950615450818576738420 : Int)/10^30,(4118255317226070000666913007 : Int)/10^30)
theorem v296_pa_checked : Scalar.distance (sourceCoefficient 3 12 1 0) v296_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v296_pb : Scalar.QComplex := ((1776929762533357391951355 : Int)/10^30,(-431472688603991961489756425 : Int)/10^30)
theorem v296_pb_checked : Scalar.distance (sourceCoefficient 3 12 1 1) v296_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v296_pg : Scalar.QComplex := ((-93085513940524349498654 : Int)/10^30,(-383353163596044883911 : Int)/10^30)
theorem v296_pg_checked : Scalar.distance (sourceCoefficient 3 12 1 2) v296_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v296_mb : Scalar.QComplex := ((1404587603444466998999477 : Int)/10^30,(-431474061357345838836502288 : Int)/10^30)
theorem v296_mb_checked : Scalar.distance (sourceCoefficient 3 12 3 1) v296_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v296_mg : Scalar.QComplex := ((-93085810097047889118748 : Int)/10^30,(-303024414741387545295 : Int)/10^30)
theorem v296_mg_checked : Scalar.distance (sourceCoefficient 3 12 3 2) v296_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v296_upper : Scalar.QComplex := ((999997138315786068196674848307 : Int)/10^30,(2392354538655812691962756794 : Int)/10^30)
theorem v296_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 12 5) 1) 14) v296_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material296 : Material (3 : Basis) (12 : Basis) where
  plus := ![v296_pa,v296_pb,v296_pg]
  minus := ![(Primitive.Addresses.material296 1).one,v296_mb,v296_mg]
  upper := v296_upper
  lower := (Primitive.Addresses.material296 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v296_pa_checked.trans (by decide +kernel)
    · exact v296_pb_checked.trans (by decide +kernel)
    · exact v296_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 12 Primitive.Addresses.material296
    · exact v296_mb_checked.trans (by decide +kernel)
    · exact v296_mg_checked.trans (by decide +kernel)
  upper_error := v296_upper_checked
  lower_error := reuse_lower_error 3 12 Primitive.Addresses.material296

def v297_pa : Scalar.QComplex := ((999991730776401698933611624112 : Int)/10^30,(4066740564204116288628086428 : Int)/10^30)
theorem v297_pa_checked : Scalar.distance (sourceCoefficient 3 13 1 0) v297_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v297_pb : Scalar.QComplex := ((1754702242562563588690650 : Int)/10^30,(-431472749450092725973078524 : Int)/10^30)
theorem v297_pb_checked : Scalar.distance (sourceCoefficient 3 13 1 1) v297_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v297_pg : Scalar.QComplex := ((-93085530316463961430416 : Int)/10^30,(-378557832457777503521 : Int)/10^30)
theorem v297_pg_checked : Scalar.distance (sourceCoefficient 3 13 1 2) v297_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v297_mb : Scalar.QComplex := ((1382360039242550175612521 : Int)/10^30,(-431474103022075303077917784 : Int)/10^30)
theorem v297_mb_checked : Scalar.distance (sourceCoefficient 3 13 3 1) v297_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v297_mg : Scalar.QComplex := ((-93085822334826604912173 : Int)/10^30,(-298229071256942764985 : Int)/10^30)
theorem v297_mg_checked : Scalar.distance (sourceCoefficient 3 13 3 2) v297_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v297_upper : Scalar.QComplex := ((999997260231467982064018459995 : Int)/10^30,(2340839498492851159828047179 : Int)/10^30)
theorem v297_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 13 5) 1) 14) v297_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material297 : Material (3 : Basis) (13 : Basis) where
  plus := ![v297_pa,v297_pb,v297_pg]
  minus := ![(Primitive.Addresses.material297 1).one,v297_mb,v297_mg]
  upper := v297_upper
  lower := (Primitive.Addresses.material297 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v297_pa_checked.trans (by decide +kernel)
    · exact v297_pb_checked.trans (by decide +kernel)
    · exact v297_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 13 Primitive.Addresses.material297
    · exact v297_mb_checked.trans (by decide +kernel)
    · exact v297_mg_checked.trans (by decide +kernel)
  upper_error := v297_upper_checked
  lower_error := reuse_lower_error 3 13 Primitive.Addresses.material297

def v298_pa : Scalar.QComplex := ((999991796973280509694607927342 : Int)/10^30,(4050430365940544115042361546 : Int)/10^30)
theorem v298_pa_checked : Scalar.distance (sourceCoefficient 3 14 1 0) v298_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v298_pb : Scalar.QComplex := ((1747664739330132617860630 : Int)/10^30,(-431472768396491124124486163 : Int)/10^30)
theorem v298_pb_checked : Scalar.distance (sourceCoefficient 3 14 1 1) v298_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v298_pg : Scalar.QComplex := ((-93085535441215297803854 : Int)/10^30,(-377039572246618611490 : Int)/10^30)
theorem v298_pg_checked : Scalar.distance (sourceCoefficient 3 14 1 2) v298_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v298_mb : Scalar.QComplex := ((1375322522280614784505786 : Int)/10^30,(-431474115895418314410958477 : Int)/10^30)
theorem v298_mb_checked : Scalar.distance (sourceCoefficient 3 14 3 1) v298_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v298_mg : Scalar.QComplex := ((-93085826149385850777882 : Int)/10^30,(-296710807188671944429 : Int)/10^30)
theorem v298_mg_checked : Scalar.distance (sourceCoefficient 3 14 3 2) v298_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v298_upper : Scalar.QComplex := ((999997298278325647052568826077 : Int)/10^30,(2324529210271595875919398699 : Int)/10^30)
theorem v298_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 14 5) 1) 14) v298_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material298 : Material (3 : Basis) (14 : Basis) where
  plus := ![v298_pa,v298_pb,v298_pg]
  minus := ![(Primitive.Addresses.material298 1).one,v298_mb,v298_mg]
  upper := v298_upper
  lower := (Primitive.Addresses.material298 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v298_pa_checked.trans (by decide +kernel)
    · exact v298_pb_checked.trans (by decide +kernel)
    · exact v298_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 14 Primitive.Addresses.material298
    · exact v298_mb_checked.trans (by decide +kernel)
    · exact v298_mg_checked.trans (by decide +kernel)
  upper_error := v298_upper_checked
  lower_error := reuse_lower_error 3 14 Primitive.Addresses.material298

def v299_pa : Scalar.QComplex := ((999991903065949008552457027885 : Int)/10^30,(4024152400399600793077730947 : Int)/10^30)
theorem v299_pa_checked : Scalar.distance (sourceCoefficient 3 15 1 0) v299_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v299_pb : Scalar.QComplex := ((1736326357112563267321411 : Int)/10^30,(-431472798599809951571356114 : Int)/10^30)
theorem v299_pb_checked : Scalar.distance (sourceCoefficient 3 15 1 1) v299_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v299_pg : Scalar.QComplex := ((-93085543637121672165194 : Int)/10^30,(-374593446928260674889 : Int)/10^30)
theorem v299_pg_checked : Scalar.distance (sourceCoefficient 3 15 1 2) v299_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v299_mb : Scalar.QComplex := ((1363984118220739482130439 : Int)/10^30,(-431474136314212703797942635 : Int)/10^30)
theorem v299_mb_checked : Scalar.distance (sourceCoefficient 3 15 3 1) v299_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v299_mg : Scalar.QComplex := ((-93085832234393193080466 : Int)/10^30,(-294264675708420186149 : Int)/10^30)
theorem v299_mg_checked : Scalar.distance (sourceCoefficient 3 15 3 2) v299_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v299_upper : Scalar.QComplex := ((999997359017451528086761152408 : Int)/10^30,(2298251100762274223193575730 : Int)/10^30)
theorem v299_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 15 5) 1) 14) v299_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material299 : Material (3 : Basis) (15 : Basis) where
  plus := ![v299_pa,v299_pb,v299_pg]
  minus := ![(Primitive.Addresses.material299 1).one,v299_mb,v299_mg]
  upper := v299_upper
  lower := (Primitive.Addresses.material299 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v299_pa_checked.trans (by decide +kernel)
    · exact v299_pb_checked.trans (by decide +kernel)
    · exact v299_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 15 Primitive.Addresses.material299
    · exact v299_mb_checked.trans (by decide +kernel)
    · exact v299_mg_checked.trans (by decide +kernel)
  upper_error := v299_upper_checked
  lower_error := reuse_lower_error 3 15 Primitive.Addresses.material299

def v300_pa : Scalar.QComplex := ((999991916470714846662150393756 : Int)/10^30,(4020819969466547972215564840 : Int)/10^30)
theorem v300_pa_checked : Scalar.distance (sourceCoefficient 3 16 1 0) v300_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v300_pb : Scalar.QComplex := ((1734888484200111375682754 : Int)/10^30,(-431472802401648664258293341 : Int)/10^30)
theorem v300_pb_checked : Scalar.distance (sourceCoefficient 3 16 1 1) v300_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v300_pg : Scalar.QComplex := ((-93085544671124454859141 : Int)/10^30,(-374283242411878596457 : Int)/10^30)
theorem v300_pg_checked : Scalar.distance (sourceCoefficient 3 16 1 2) v300_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v300_mb : Scalar.QComplex := ((1362546242562857809246553 : Int)/10^30,(-431474138875230436832587235 : Int)/10^30)
theorem v300_mb_checked : Scalar.distance (sourceCoefficient 3 16 3 1) v300_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v300_mg : Scalar.QComplex := ((-93085833000703064222973 : Int)/10^30,(-293954470415243594505 : Int)/10^30)
theorem v300_mg_checked : Scalar.distance (sourceCoefficient 3 16 3 2) v300_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v300_upper : Scalar.QComplex := ((999997366670723926695889587541 : Int)/10^30,(2294918651657076056558065841 : Int)/10^30)
theorem v300_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 16 5) 1) 14) v300_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material300 : Material (3 : Basis) (16 : Basis) where
  plus := ![v300_pa,v300_pb,v300_pg]
  minus := ![(Primitive.Addresses.material300 1).one,v300_mb,v300_mg]
  upper := v300_upper
  lower := (Primitive.Addresses.material300 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v300_pa_checked.trans (by decide +kernel)
    · exact v300_pb_checked.trans (by decide +kernel)
    · exact v300_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 16 Primitive.Addresses.material300
    · exact v300_mb_checked.trans (by decide +kernel)
    · exact v300_mg_checked.trans (by decide +kernel)
  upper_error := v300_upper_checked
  lower_error := reuse_lower_error 3 16 Primitive.Addresses.material300

def v301_pa : Scalar.QComplex := ((999991943353416156113259231007 : Int)/10^30,(4014128580169498820356536045 : Int)/10^30)
theorem v301_pa_checked : Scalar.distance (sourceCoefficient 3 17 1 0) v301_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v301_pb : Scalar.QComplex := ((1732001292374753757664315 : Int)/10^30,(-431472810016296040296220577 : Int)/10^30)
theorem v301_pb_checked : Scalar.distance (sourceCoefficient 3 17 1 1) v301_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v301_pg : Scalar.QComplex := ((-93085546743718890208420 : Int)/10^30,(-373660364034161236725 : Int)/10^30)
theorem v301_pg_checked : Scalar.distance (sourceCoefficient 3 17 1 2) v301_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v301_mb : Scalar.QComplex := ((1359659045241435924459842 : Int)/10^30,(-431474143998358466598379707 : Int)/10^30)
theorem v301_mb_checked : Scalar.distance (sourceCoefficient 3 17 3 1) v301_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v301_mg : Scalar.QComplex := ((-93085834535780741281282 : Int)/10^30,(-293331590480896670227 : Int)/10^30)
theorem v301_mg_checked : Scalar.distance (sourceCoefficient 3 17 3 2) v301_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v301_upper : Scalar.QComplex := ((999997382004654308909532741429 : Int)/10^30,(2288227225928961556351094966 : Int)/10^30)
theorem v301_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 17 5) 1) 14) v301_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material301 : Material (3 : Basis) (17 : Basis) where
  plus := ![v301_pa,v301_pb,v301_pg]
  minus := ![(Primitive.Addresses.material301 1).one,v301_mb,v301_mg]
  upper := v301_upper
  lower := (Primitive.Addresses.material301 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v301_pa_checked.trans (by decide +kernel)
    · exact v301_pb_checked.trans (by decide +kernel)
    · exact v301_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 17 Primitive.Addresses.material301
    · exact v301_mb_checked.trans (by decide +kernel)
    · exact v301_mg_checked.trans (by decide +kernel)
  upper_error := v301_upper_checked
  lower_error := reuse_lower_error 3 17 Primitive.Addresses.material301

def v302_pa : Scalar.QComplex := ((999992032700112474421633080226 : Int)/10^30,(3991808649870840060022562592 : Int)/10^30)
theorem v302_pa_checked : Scalar.distance (sourceCoefficient 3 18 1 0) v302_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v302_pb : Scalar.QComplex := ((1722370718497833087694029 : Int)/10^30,(-431472835229597072008704672 : Int)/10^30)
theorem v302_pb_checked : Scalar.distance (sourceCoefficient 3 18 1 1) v302_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v302_pg : Scalar.QComplex := ((-93085553621943850343203 : Int)/10^30,(-371582678636725075929 : Int)/10^30)
theorem v302_pg_checked : Scalar.distance (sourceCoefficient 3 18 1 2) v302_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v302_mb : Scalar.QComplex := ((1350028453192474822393046 : Int)/10^30,(-431474160900898599410093987 : Int)/10^30)
theorem v302_mb_checked : Scalar.distance (sourceCoefficient 3 18 3 1) v302_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v302_mg : Scalar.QComplex := ((-93085839621054217827770 : Int)/10^30,(-291253899921479380966 : Int)/10^30)
theorem v302_mg_checked : Scalar.distance (sourceCoefficient 3 18 3 2) v302_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v302_upper : Scalar.QComplex := ((999997432829042708583568090067 : Int)/10^30,(2265907174668924716252510521 : Int)/10^30)
theorem v302_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 18 5) 1) 14) v302_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material302 : Material (3 : Basis) (18 : Basis) where
  plus := ![v302_pa,v302_pb,v302_pg]
  minus := ![(Primitive.Addresses.material302 1).one,v302_mb,v302_mg]
  upper := v302_upper
  lower := (Primitive.Addresses.material302 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v302_pa_checked.trans (by decide +kernel)
    · exact v302_pb_checked.trans (by decide +kernel)
    · exact v302_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 18 Primitive.Addresses.material302
    · exact v302_mb_checked.trans (by decide +kernel)
    · exact v302_mg_checked.trans (by decide +kernel)
  upper_error := v302_upper_checked
  lower_error := reuse_lower_error 3 18 Primitive.Addresses.material302

def v303_pa : Scalar.QComplex := ((999992095056025133688419494864 : Int)/10^30,(3976157122347327132321500640 : Int)/10^30)
theorem v303_pa_checked : Scalar.distance (sourceCoefficient 3 19 1 0) v303_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v303_pb : Scalar.QComplex := ((1715617418377669252061363 : Int)/10^30,(-431472852739100696733549938 : Int)/10^30)
theorem v303_pb_checked : Scalar.distance (sourceCoefficient 3 19 1 1) v303_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v303_pg : Scalar.QComplex := ((-93085558412927309853645 : Int)/10^30,(-370125731894413361734 : Int)/10^30)
theorem v303_pg_checked : Scalar.distance (sourceCoefficient 3 19 1 2) v303_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v303_mb : Scalar.QComplex := ((1343275140476960233191599 : Int)/10^30,(-431474172582601858191686513 : Int)/10^30)
theorem v303_mb_checked : Scalar.distance (sourceCoefficient 3 19 3 1) v303_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v303_mg : Scalar.QComplex := ((-93085843154756473266505 : Int)/10^30,(-289796949587252577017 : Int)/10^30)
theorem v303_mg_checked : Scalar.distance (sourceCoefficient 3 19 3 2) v303_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v303_upper : Scalar.QComplex := ((999997468171745885945293609174 : Int)/10^30,(2250255562835875111562237995 : Int)/10^30)
theorem v303_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 19 5) 1) 14) v303_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material303 : Material (3 : Basis) (19 : Basis) where
  plus := ![v303_pa,v303_pb,v303_pg]
  minus := ![(Primitive.Addresses.material303 1).one,v303_mb,v303_mg]
  upper := v303_upper
  lower := (Primitive.Addresses.material303 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v303_pa_checked.trans (by decide +kernel)
    · exact v303_pb_checked.trans (by decide +kernel)
    · exact v303_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 19 Primitive.Addresses.material303
    · exact v303_mb_checked.trans (by decide +kernel)
    · exact v303_mg_checked.trans (by decide +kernel)
  upper_error := v303_upper_checked
  lower_error := reuse_lower_error 3 19 Primitive.Addresses.material303

def v304_pa : Scalar.QComplex := ((999992106206932746950030165951 : Int)/10^30,(3973351711406518732943366821 : Int)/10^30)
theorem v304_pa_checked : Scalar.distance (sourceCoefficient 3 20 1 0) v304_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v304_pb : Scalar.QComplex := ((1714406943440940353013539 : Int)/10^30,(-431472855862644264607385780 : Int)/10^30)
theorem v304_pb_checked : Scalar.distance (sourceCoefficient 3 20 1 1) v304_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v304_pg : Scalar.QComplex := ((-93085559268861019806230 : Int)/10^30,(-369864585862665570808 : Int)/10^30)
theorem v304_pg_checked : Scalar.distance (sourceCoefficient 3 20 1 2) v304_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v304_mb : Scalar.QComplex := ((1342064663295469054630407 : Int)/10^30,(-431474174661558910397814780 : Int)/10^30)
theorem v304_mb_checked : Scalar.distance (sourceCoefficient 3 20 3 1) v304_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v304_mg : Scalar.QComplex := ((-93085843785332600698168 : Int)/10^30,(-289535802914109146808 : Int)/10^30)
theorem v304_mg_checked : Scalar.distance (sourceCoefficient 3 20 3 2) v304_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v304_upper : Scalar.QComplex := ((999997474480752112297061643412 : Int)/10^30,(2247450136827941823746643825 : Int)/10^30)
theorem v304_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 20 5) 1) 14) v304_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material304 : Material (3 : Basis) (20 : Basis) where
  plus := ![v304_pa,v304_pb,v304_pg]
  minus := ![(Primitive.Addresses.material304 1).one,v304_mb,v304_mg]
  upper := v304_upper
  lower := (Primitive.Addresses.material304 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v304_pa_checked.trans (by decide +kernel)
    · exact v304_pb_checked.trans (by decide +kernel)
    · exact v304_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 20 Primitive.Addresses.material304
    · exact v304_mb_checked.trans (by decide +kernel)
    · exact v304_mg_checked.trans (by decide +kernel)
  upper_error := v304_upper_checked
  lower_error := reuse_lower_error 3 20 Primitive.Addresses.material304

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
