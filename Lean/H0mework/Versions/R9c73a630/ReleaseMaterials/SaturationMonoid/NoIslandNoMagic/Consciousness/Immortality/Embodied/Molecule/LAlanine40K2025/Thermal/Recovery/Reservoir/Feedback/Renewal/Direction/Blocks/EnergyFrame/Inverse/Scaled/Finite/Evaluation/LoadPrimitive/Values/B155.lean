import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B103
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B104

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2481_pa : Scalar.QComplex := ((999999770307215598309813783499 : Int)/10^30,(-677779843344876379801642418 : Int)/10^30)
theorem v2481_pa_checked : Scalar.distance (sourceCoefficient 30 37 1 0) v2481_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2481_pb : Scalar.QComplex := ((-292446765967231986383049 : Int)/10^30,(-431477420973573643423577121 : Int)/10^30)
theorem v2481_pb_checked : Scalar.distance (sourceCoefficient 30 37 1 1) v2481_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2481_pg : Scalar.QComplex := ((-93086408416475889212495 : Int)/10^30,(63092105805857666661 : Int)/10^30)
theorem v2481_pg_checked : Scalar.distance (sourceCoefficient 30 37 1 2) v2481_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2481_mb : Scalar.QComplex := ((-664792238354476616709285 : Int)/10^30,(-431477007946422606336756560 : Int)/10^30)
theorem v2481_mb_checked : Scalar.distance (sourceCoefficient 30 37 3 1) v2481_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2481_mg : Scalar.QComplex := ((-93086319310506029235783 : Int)/10^30,(143421460320998127573 : Int)/10^30)
theorem v2481_mg_checked : Scalar.distance (sourceCoefficient 30 37 3 2) v2481_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2481_upper : Scalar.QComplex := ((999997111138504044241199099123 : Int)/10^30,(-2403687718151169233963336079 : Int)/10^30)
theorem v2481_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 37 5) 1) 14) v2481_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2481 : Material (30 : Basis) (37 : Basis) where
  plus := ![v2481_pa,v2481_pb,v2481_pg]
  minus := ![(Primitive.Addresses.material2481 1).one,v2481_mb,v2481_mg]
  upper := v2481_upper
  lower := (Primitive.Addresses.material2481 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2481_pa_checked.trans (by decide +kernel)
    · exact v2481_pb_checked.trans (by decide +kernel)
    · exact v2481_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 37 Primitive.Addresses.material2481
    · exact v2481_mb_checked.trans (by decide +kernel)
    · exact v2481_mg_checked.trans (by decide +kernel)
  upper_error := v2481_upper_checked
  lower_error := reuse_lower_error 30 37 Primitive.Addresses.material2481

def v2482_pa : Scalar.QComplex := ((999999754242788007429041923749 : Int)/10^30,(-701080853816829510621244547 : Int)/10^30)
theorem v2482_pa_checked : Scalar.distance (sourceCoefficient 30 38 1 0) v2482_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2482_pb : Scalar.QComplex := ((-302500627887954823485213 : Int)/10^30,(-431477413624075115234395654 : Int)/10^30)
theorem v2482_pb_checked : Scalar.distance (sourceCoefficient 30 38 1 1) v2482_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2482_pg : Scalar.QComplex := ((-93086406875999894937837 : Int)/10^30,(65261113649756137839 : Int)/10^30)
theorem v2482_pg_checked : Scalar.distance (sourceCoefficient 30 38 1 2) v2482_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2482_mb : Scalar.QComplex := ((-674846090189400955836390 : Int)/10^30,(-431476991920896786249801660 : Int)/10^30)
theorem v2482_mb_checked : Scalar.distance (sourceCoefficient 30 38 3 1) v2482_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2482_mg : Scalar.QComplex := ((-93086315898274527753282 : Int)/10^30,(145590466027914447317 : Int)/10^30)
theorem v2482_mg_checked : Scalar.distance (sourceCoefficient 30 38 3 2) v2482_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2482_upper : Scalar.QComplex := ((999997054858670156004676362966 : Int)/10^30,(-2426988666193259727398220045 : Int)/10^30)
theorem v2482_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 38 5) 1) 14) v2482_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2482 : Material (30 : Basis) (38 : Basis) where
  plus := ![v2482_pa,v2482_pb,v2482_pg]
  minus := ![(Primitive.Addresses.material2482 1).one,v2482_mb,v2482_mg]
  upper := v2482_upper
  lower := (Primitive.Addresses.material2482 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2482_pa_checked.trans (by decide +kernel)
    · exact v2482_pb_checked.trans (by decide +kernel)
    · exact v2482_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 38 Primitive.Addresses.material2482
    · exact v2482_mb_checked.trans (by decide +kernel)
    · exact v2482_mg_checked.trans (by decide +kernel)
  upper_error := v2482_upper_checked
  lower_error := reuse_lower_error 30 38 Primitive.Addresses.material2482

def v2483_pa : Scalar.QComplex := ((999999744674642152833987193417 : Int)/10^30,(-714598244122733389906512693 : Int)/10^30)
theorem v2483_pa_checked : Scalar.distance (sourceCoefficient 30 39 1 0) v2483_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2483_pb : Scalar.QComplex := ((-308333077730576663423120 : Int)/10^30,(-431477409217320397787400949 : Int)/10^30)
theorem v2483_pb_checked : Scalar.distance (sourceCoefficient 30 39 1 1) v2483_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2483_pg : Scalar.QComplex := ((-93086405955313703617852 : Int)/10^30,(66519399231452537781 : Int)/10^30)
theorem v2483_pg_checked : Scalar.distance (sourceCoefficient 30 39 1 2) v2483_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2483_mb : Scalar.QComplex := ((-680678534057504314948297 : Int)/10^30,(-431476982481002179245970087 : Int)/10^30)
theorem v2483_mb_checked : Scalar.distance (sourceCoefficient 30 39 3 1) v2483_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2483_mg : Scalar.QComplex := ((-93086313891744893321720 : Int)/10^30,(146848750346582901758 : Int)/10^30)
theorem v2483_mg_checked : Scalar.distance (sourceCoefficient 30 39 3 2) v2483_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2483_upper : Scalar.QComplex := ((999997021960749172118137935637 : Int)/10^30,(-2440506019852846880626668465 : Int)/10^30)
theorem v2483_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 39 5) 1) 14) v2483_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2483 : Material (30 : Basis) (39 : Basis) where
  plus := ![v2483_pa,v2483_pb,v2483_pg]
  minus := ![(Primitive.Addresses.material2483 1).one,v2483_mb,v2483_mg]
  upper := v2483_upper
  lower := (Primitive.Addresses.material2483 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2483_pa_checked.trans (by decide +kernel)
    · exact v2483_pb_checked.trans (by decide +kernel)
    · exact v2483_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 39 Primitive.Addresses.material2483
    · exact v2483_mb_checked.trans (by decide +kernel)
    · exact v2483_mg_checked.trans (by decide +kernel)
  upper_error := v2483_upper_checked
  lower_error := reuse_lower_error 30 39 Primitive.Addresses.material2483

def v2484_pa : Scalar.QComplex := ((999999728169443357553551464458 : Int)/10^30,(-737333736779378197284442503 : Int)/10^30)
theorem v2484_pa_checked : Scalar.distance (sourceCoefficient 30 40 1 0) v2484_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2484_pb : Scalar.QComplex := ((-318142931315192555121407 : Int)/10^30,(-431477401568315551005410340 : Int)/10^30)
theorem v2484_pb_checked : Scalar.distance (sourceCoefficient 30 40 1 1) v2484_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2484_pg : Scalar.QComplex := ((-93086404362015238046203 : Int)/10^30,(68635765028899119367 : Int)/10^30)
theorem v2484_pg_checked : Scalar.distance (sourceCoefficient 30 40 1 2) v2484_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2484_mb : Scalar.QComplex := ((-690488377388716700254257 : Int)/10^30,(-431476966366538356418890060 : Int)/10^30)
theorem v2484_mb_checked : Scalar.distance (sourceCoefficient 30 40 3 1) v2484_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2484_mg : Scalar.QComplex := ((-93086310472118655388670 : Int)/10^30,(148965113981064957970 : Int)/10^30)
theorem v2484_mg_checked : Scalar.distance (sourceCoefficient 30 40 3 2) v2484_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2484_upper : Scalar.QComplex := ((999996966216177181805605125928 : Int)/10^30,(-2463241450161170293790047731 : Int)/10^30)
theorem v2484_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 40 5) 1) 14) v2484_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2484 : Material (30 : Basis) (40 : Basis) where
  plus := ![v2484_pa,v2484_pb,v2484_pg]
  minus := ![(Primitive.Addresses.material2484 1).one,v2484_mb,v2484_mg]
  upper := v2484_upper
  lower := (Primitive.Addresses.material2484 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2484_pa_checked.trans (by decide +kernel)
    · exact v2484_pb_checked.trans (by decide +kernel)
    · exact v2484_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 40 Primitive.Addresses.material2484
    · exact v2484_mb_checked.trans (by decide +kernel)
    · exact v2484_mg_checked.trans (by decide +kernel)
  upper_error := v2484_upper_checked
  lower_error := reuse_lower_error 30 40 Primitive.Addresses.material2484

def v2485_pa : Scalar.QComplex := ((999999717385012656870327766769 : Int)/10^30,(-751817727122091923282231658 : Int)/10^30)
theorem v2485_pa_checked : Scalar.distance (sourceCoefficient 30 41 1 0) v2485_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2485_pb : Scalar.QComplex := ((-324392447249677161843828 : Int)/10^30,(-431477396540331753806913763 : Int)/10^30)
theorem v2485_pb_checked : Scalar.distance (sourceCoefficient 30 41 1 1) v2485_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2485_pg : Scalar.QComplex := ((-93086403317707640824744 : Int)/10^30,(69984027946824487801 : Int)/10^30)
theorem v2485_pg_checked : Scalar.distance (sourceCoefficient 30 41 1 2) v2485_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2485_mb : Scalar.QComplex := ((-696737886657297342581718 : Int)/10^30,(-431476955945505647657450990 : Int)/10^30)
theorem v2485_mb_checked : Scalar.distance (sourceCoefficient 30 41 3 1) v2485_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2485_mg : Scalar.QComplex := ((-93086308264321272348724 : Int)/10^30,(150313375495780000868 : Int)/10^30)
theorem v2485_mg_checked : Scalar.distance (sourceCoefficient 30 41 3 2) v2485_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2485_upper : Scalar.QComplex := ((999996930433709189080854099861 : Int)/10^30,(-2477725400318732779870287294 : Int)/10^30)
theorem v2485_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 41 5) 1) 14) v2485_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2485 : Material (30 : Basis) (41 : Basis) where
  plus := ![v2485_pa,v2485_pb,v2485_pg]
  minus := ![(Primitive.Addresses.material2485 1).one,v2485_mb,v2485_mg]
  upper := v2485_upper
  lower := (Primitive.Addresses.material2485 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2485_pa_checked.trans (by decide +kernel)
    · exact v2485_pb_checked.trans (by decide +kernel)
    · exact v2485_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 41 Primitive.Addresses.material2485
    · exact v2485_mb_checked.trans (by decide +kernel)
    · exact v2485_mg_checked.trans (by decide +kernel)
  upper_error := v2485_upper_checked
  lower_error := reuse_lower_error 30 41 Primitive.Addresses.material2485

def v2486_pa : Scalar.QComplex := ((999999708532783692355397042708 : Int)/10^30,(-763501373713335910581556822 : Int)/10^30)
theorem v2486_pa_checked : Scalar.distance (sourceCoefficient 30 42 1 0) v2486_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2486_pb : Scalar.QComplex := ((-329433677840105615455669 : Int)/10^30,(-431477392396516697305499465 : Int)/10^30)
theorem v2486_pb_checked : Scalar.distance (sourceCoefficient 30 42 1 1) v2486_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2486_pg : Scalar.QComplex := ((-93086402458705662817755 : Int)/10^30,(71071616866300549529 : Int)/10^30)
theorem v2486_pg_checked : Scalar.distance (sourceCoefficient 30 42 1 2) v2486_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2486_mb : Scalar.QComplex := ((-701779111794719488498664 : Int)/10^30,(-431476947451337183145361246 : Int)/10^30)
theorem v2486_mb_checked : Scalar.distance (sourceCoefficient 30 42 3 1) v2486_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2486_mg : Scalar.QComplex := ((-93086306466779359866181 : Int)/10^30,(151400963269016983598 : Int)/10^30)
theorem v2486_mg_checked : Scalar.distance (sourceCoefficient 30 42 3 2) v2486_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2486_upper : Scalar.QComplex := ((999996901416579324573010245142 : Int)/10^30,(-2489409014230413502235852529 : Int)/10^30)
theorem v2486_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 42 5) 1) 14) v2486_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2486 : Material (30 : Basis) (42 : Basis) where
  plus := ![v2486_pa,v2486_pb,v2486_pg]
  minus := ![(Primitive.Addresses.material2486 1).one,v2486_mb,v2486_mg]
  upper := v2486_upper
  lower := (Primitive.Addresses.material2486 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2486_pa_checked.trans (by decide +kernel)
    · exact v2486_pb_checked.trans (by decide +kernel)
    · exact v2486_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 42 Primitive.Addresses.material2486
    · exact v2486_mb_checked.trans (by decide +kernel)
    · exact v2486_mg_checked.trans (by decide +kernel)
  upper_error := v2486_upper_checked
  lower_error := reuse_lower_error 30 42 Primitive.Addresses.material2486

def v2487_pa : Scalar.QComplex := ((999999696595689980102408128133 : Int)/10^30,(-778979157606684522449640949 : Int)/10^30)
theorem v2487_pa_checked : Scalar.distance (sourceCoefficient 30 43 1 0) v2487_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2487_pb : Scalar.QComplex := ((-336111993262808258371865 : Int)/10^30,(-431477386786114228094686651 : Int)/10^30)
theorem v2487_pb_checked : Scalar.distance (sourceCoefficient 30 43 1 1) v2487_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2487_pg : Scalar.QComplex := ((-93086401297924279223914 : Int)/10^30,(72512388468266030907 : Int)/10^30)
theorem v2487_pg_checked : Scalar.distance (sourceCoefficient 30 43 1 2) v2487_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2487_mb : Scalar.QComplex := ((-708457419889255437668208 : Int)/10^30,(-431476936077851373312569049 : Int)/10^30)
theorem v2487_mb_checked : Scalar.distance (sourceCoefficient 30 43 3 1) v2487_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2487_mg : Scalar.QComplex := ((-93086304062677405932213 : Int)/10^30,(152841733332815296661 : Int)/10^30)
theorem v2487_mg_checked : Scalar.distance (sourceCoefficient 30 43 3 2) v2487_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2487_upper : Scalar.QComplex := ((999996862766252524885487061230 : Int)/10^30,(-2504886754469080330508811460 : Int)/10^30)
theorem v2487_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 43 5) 1) 14) v2487_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2487 : Material (30 : Basis) (43 : Basis) where
  plus := ![v2487_pa,v2487_pb,v2487_pg]
  minus := ![(Primitive.Addresses.material2487 1).one,v2487_mb,v2487_mg]
  upper := v2487_upper
  lower := (Primitive.Addresses.material2487 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2487_pa_checked.trans (by decide +kernel)
    · exact v2487_pb_checked.trans (by decide +kernel)
    · exact v2487_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 43 Primitive.Addresses.material2487
    · exact v2487_mb_checked.trans (by decide +kernel)
    · exact v2487_mg_checked.trans (by decide +kernel)
  upper_error := v2487_upper_checked
  lower_error := reuse_lower_error 30 43 Primitive.Addresses.material2487

def v2488_pa : Scalar.QComplex := ((999999692017014785012232063769 : Int)/10^30,(-784834935242090477839445501 : Int)/10^30)
theorem v2488_pa_checked : Scalar.distance (sourceCoefficient 30 44 1 0) v2488_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2488_pb : Scalar.QComplex := ((-338638629517542549056261 : Int)/10^30,(-431477384627571343915558938 : Int)/10^30)
theorem v2488_pb_checked : Scalar.distance (sourceCoefficient 30 44 1 1) v2488_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2488_pg : Scalar.QComplex := ((-93086400851977321595221 : Int)/10^30,(73057481885042260323 : Int)/10^30)
theorem v2488_pg_checked : Scalar.distance (sourceCoefficient 30 44 1 2) v2488_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2488_mb : Scalar.QComplex := ((-710984053340482285849751 : Int)/10^30,(-431476931738936000494541262 : Int)/10^30)
theorem v2488_mb_checked : Scalar.distance (sourceCoefficient 30 44 3 1) v2488_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2488_mg : Scalar.QComplex := ((-93086303146339545768216 : Int)/10^30,(153386826161796195284 : Int)/10^30)
theorem v2488_mg_checked : Scalar.distance (sourceCoefficient 30 44 3 2) v2488_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2488_upper : Scalar.QComplex := ((999996848081043182480813507755 : Int)/10^30,(-2510742515480615353365918814 : Int)/10^30)
theorem v2488_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 44 5) 1) 14) v2488_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2488 : Material (30 : Basis) (44 : Basis) where
  plus := ![v2488_pa,v2488_pb,v2488_pg]
  minus := ![(Primitive.Addresses.material2488 1).one,v2488_mb,v2488_mg]
  upper := v2488_upper
  lower := (Primitive.Addresses.material2488 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2488_pa_checked.trans (by decide +kernel)
    · exact v2488_pb_checked.trans (by decide +kernel)
    · exact v2488_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 44 Primitive.Addresses.material2488
    · exact v2488_mb_checked.trans (by decide +kernel)
    · exact v2488_mg_checked.trans (by decide +kernel)
  upper_error := v2488_upper_checked
  lower_error := reuse_lower_error 30 44 Primitive.Addresses.material2488

def v2489_pa : Scalar.QComplex := ((999999689726293044851400296396 : Int)/10^30,(-787748257783236212291815771 : Int)/10^30)
theorem v2489_pa_checked : Scalar.distance (sourceCoefficient 30 45 1 0) v2489_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2489_pb : Scalar.QComplex := ((-339895662622170449315406 : Int)/10^30,(-431477383546320582946886416 : Int)/10^30)
theorem v2489_pb_checked : Scalar.distance (sourceCoefficient 30 45 1 1) v2489_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2489_pg : Scalar.QComplex := ((-93086400628725912423359 : Int)/10^30,(73328672670550277079 : Int)/10^30)
theorem v2489_pg_checked : Scalar.distance (sourceCoefficient 30 45 1 2) v2489_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2489_mb : Scalar.QComplex := ((-712241085043988603015562 : Int)/10^30,(-431476929572922687500461851 : Int)/10^30)
theorem v2489_mb_checked : Scalar.distance (sourceCoefficient 30 45 3 1) v2489_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2489_mg : Scalar.QComplex := ((-93086302689062785809214 : Int)/10^30,(153658016653671577318 : Int)/10^30)
theorem v2489_mg_checked : Scalar.distance (sourceCoefficient 30 45 3 2) v2489_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2489_upper : Scalar.QComplex := ((999996840762194442619765933326 : Int)/10^30,(-2513655829729131474822576942 : Int)/10^30)
theorem v2489_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 45 5) 1) 14) v2489_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2489 : Material (30 : Basis) (45 : Basis) where
  plus := ![v2489_pa,v2489_pb,v2489_pg]
  minus := ![(Primitive.Addresses.material2489 1).one,v2489_mb,v2489_mg]
  upper := v2489_upper
  lower := (Primitive.Addresses.material2489 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2489_pa_checked.trans (by decide +kernel)
    · exact v2489_pb_checked.trans (by decide +kernel)
    · exact v2489_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 45 Primitive.Addresses.material2489
    · exact v2489_mb_checked.trans (by decide +kernel)
    · exact v2489_mg_checked.trans (by decide +kernel)
  upper_error := v2489_upper_checked
  lower_error := reuse_lower_error 30 45 Primitive.Addresses.material2489

def v2490_pa : Scalar.QComplex := ((999999676701494758940529482845 : Int)/10^30,(-804112495836369558112287148 : Int)/10^30)
theorem v2490_pa_checked : Scalar.distance (sourceCoefficient 30 46 1 0) v2490_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2490_pb : Scalar.QComplex := ((-346956462994199670294417 : Int)/10^30,(-431477377382152552035817694 : Int)/10^30)
theorem v2490_pb_checked : Scalar.distance (sourceCoefficient 30 46 1 1) v2490_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2490_pg : Scalar.QComplex := ((-93086399357584910383239 : Int)/10^30,(74851961115375773122 : Int)/10^30)
theorem v2490_pg_checked : Scalar.distance (sourceCoefficient 30 46 1 2) v2490_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2490_mb : Scalar.QComplex := ((-719301877467559764115638 : Int)/10^30,(-431476917315604237373444410 : Int)/10^30)
theorem v2490_mb_checked : Scalar.distance (sourceCoefficient 30 46 3 1) v2490_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2490_mg : Scalar.QComplex := ((-93086300103392935553347 : Int)/10^30,(155181303434369732937 : Int)/10^30)
theorem v2490_mg_checked : Scalar.distance (sourceCoefficient 30 46 3 2) v2490_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2490_upper : Scalar.QComplex := ((999996799494225227987282634060 : Int)/10^30,(-2530020020930034277923524368 : Int)/10^30)
theorem v2490_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 46 5) 1) 14) v2490_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2490 : Material (30 : Basis) (46 : Basis) where
  plus := ![v2490_pa,v2490_pb,v2490_pg]
  minus := ![(Primitive.Addresses.material2490 1).one,v2490_mb,v2490_mg]
  upper := v2490_upper
  lower := (Primitive.Addresses.material2490 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2490_pa_checked.trans (by decide +kernel)
    · exact v2490_pb_checked.trans (by decide +kernel)
    · exact v2490_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 46 Primitive.Addresses.material2490
    · exact v2490_mb_checked.trans (by decide +kernel)
    · exact v2490_mg_checked.trans (by decide +kernel)
  upper_error := v2490_upper_checked
  lower_error := reuse_lower_error 30 46 Primitive.Addresses.material2490

def v2491_pa : Scalar.QComplex := ((999999673527111324253576890959 : Int)/10^30,(-808050537260477171654869072 : Int)/10^30)
theorem v2491_pa_checked : Scalar.distance (sourceCoefficient 30 47 1 0) v2491_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2491_pb : Scalar.QComplex := ((-348655639218756017689751 : Int)/10^30,(-431477375875752090926991434 : Int)/10^30)
theorem v2491_pb_checked : Scalar.distance (sourceCoefficient 30 47 1 1) v2491_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2491_pg : Scalar.QComplex := ((-93086399047344408250938 : Int)/10^30,(75218539318663632789 : Int)/10^30)
theorem v2491_pg_checked : Scalar.distance (sourceCoefficient 30 47 1 2) v2491_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2491_mb : Scalar.QComplex := ((-721001051759479394740187 : Int)/10^30,(-431476914342891783430526953 : Int)/10^30)
theorem v2491_mb_checked : Scalar.distance (sourceCoefficient 30 47 3 1) v2491_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2491_mg : Scalar.QComplex := ((-93086299476812069569734 : Int)/10^30,(155547881233440193441 : Int)/10^30)
theorem v2491_mg_checked : Scalar.distance (sourceCoefficient 30 47 3 2) v2491_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2491_upper : Scalar.QComplex := ((999996789523144279489087526696 : Int)/10^30,(-2533958051010193954644962224 : Int)/10^30)
theorem v2491_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 47 5) 1) 14) v2491_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2491 : Material (30 : Basis) (47 : Basis) where
  plus := ![v2491_pa,v2491_pb,v2491_pg]
  minus := ![(Primitive.Addresses.material2491 1).one,v2491_mb,v2491_mg]
  upper := v2491_upper
  lower := (Primitive.Addresses.material2491 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2491_pa_checked.trans (by decide +kernel)
    · exact v2491_pb_checked.trans (by decide +kernel)
    · exact v2491_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 47 Primitive.Addresses.material2491
    · exact v2491_mb_checked.trans (by decide +kernel)
    · exact v2491_mg_checked.trans (by decide +kernel)
  upper_error := v2491_upper_checked
  lower_error := reuse_lower_error 30 47 Primitive.Addresses.material2491

def v2492_pa : Scalar.QComplex := ((999999650985608357450621924334 : Int)/10^30,(-835481095820876836751555228 : Int)/10^30)
theorem v2492_pa_checked : Scalar.distance (sourceCoefficient 30 48 1 0) v2492_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2492_pb : Scalar.QComplex := ((-360491307661847197640665 : Int)/10^30,(-431477365135357116598500950 : Int)/10^30)
theorem v2492_pb_checked : Scalar.distance (sourceCoefficient 30 48 1 1) v2492_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2492_pg : Scalar.QComplex := ((-93086396839630587735878 : Int)/10^30,(77771951981122077364 : Int)/10^30)
theorem v2492_pg_checked : Scalar.distance (sourceCoefficient 30 48 1 2) v2492_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2492_mb : Scalar.QComplex := ((-732836706527133163145851 : Int)/10^30,(-431476893388852000572864459 : Int)/10^30)
theorem v2492_mb_checked : Scalar.distance (sourceCoefficient 30 48 3 1) v2492_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2492_mg : Scalar.QComplex := ((-93086295065618944823052 : Int)/10^30,(158101291039988811695 : Int)/10^30)
theorem v2492_mg_checked : Scalar.distance (sourceCoefficient 30 48 3 2) v2492_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2492_upper : Scalar.QComplex := ((999996719639019291190722675281 : Int)/10^30,(-2561388529811409692256426090 : Int)/10^30)
theorem v2492_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 48 5) 1) 14) v2492_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2492 : Material (30 : Basis) (48 : Basis) where
  plus := ![v2492_pa,v2492_pb,v2492_pg]
  minus := ![(Primitive.Addresses.material2492 1).one,v2492_mb,v2492_mg]
  upper := v2492_upper
  lower := (Primitive.Addresses.material2492 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2492_pa_checked.trans (by decide +kernel)
    · exact v2492_pb_checked.trans (by decide +kernel)
    · exact v2492_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 48 Primitive.Addresses.material2492
    · exact v2492_mb_checked.trans (by decide +kernel)
    · exact v2492_mg_checked.trans (by decide +kernel)
  upper_error := v2492_upper_checked
  lower_error := reuse_lower_error 30 48 Primitive.Addresses.material2492

def v2493_pa : Scalar.QComplex := ((999999632330109988369523033312 : Int)/10^30,(-857519471990060953839672735 : Int)/10^30)
theorem v2493_pa_checked : Scalar.distance (sourceCoefficient 30 49 1 0) v2493_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2493_pb : Scalar.QComplex := ((-370000370695993564054397 : Int)/10^30,(-431477356192660823165860722 : Int)/10^30)
theorem v2493_pb_checked : Scalar.distance (sourceCoefficient 30 49 1 1) v2493_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2493_pg : Scalar.QComplex := ((-93086395006700565978433 : Int)/10^30,(79823425644274242805 : Int)/10^30)
theorem v2493_pg_checked : Scalar.distance (sourceCoefficient 30 49 1 2) v2493_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2493_mb : Scalar.QComplex := ((-742345758303476639154646 : Int)/10^30,(-431476876240265910747284315 : Int)/10^30)
theorem v2493_mb_checked : Scalar.distance (sourceCoefficient 30 49 3 1) v2493_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2493_mg : Scalar.QComplex := ((-93086291462360229192832 : Int)/10^30,(160152762357547518693 : Int)/10^30)
theorem v2493_mg_checked : Scalar.distance (sourceCoefficient 30 49 3 2) v2493_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2493_upper : Scalar.QComplex := ((999996662947310745139577673493 : Int)/10^30,(-2583426840959323543421240559 : Int)/10^30)
theorem v2493_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 49 5) 1) 14) v2493_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2493 : Material (30 : Basis) (49 : Basis) where
  plus := ![v2493_pa,v2493_pb,v2493_pg]
  minus := ![(Primitive.Addresses.material2493 1).one,v2493_mb,v2493_mg]
  upper := v2493_upper
  lower := (Primitive.Addresses.material2493 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2493_pa_checked.trans (by decide +kernel)
    · exact v2493_pb_checked.trans (by decide +kernel)
    · exact v2493_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 49 Primitive.Addresses.material2493
    · exact v2493_mb_checked.trans (by decide +kernel)
    · exact v2493_mg_checked.trans (by decide +kernel)
  upper_error := v2493_upper_checked
  lower_error := reuse_lower_error 30 49 Primitive.Addresses.material2493

def v2494_pa : Scalar.QComplex := ((999999630118440263923582299201 : Int)/10^30,(-860094752140590962813574181 : Int)/10^30)
theorem v2494_pa_checked : Scalar.distance (sourceCoefficient 30 50 1 0) v2494_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2494_pb : Scalar.QComplex := ((-371111546081646159628008 : Int)/10^30,(-431477355129434439441883929 : Int)/10^30)
theorem v2494_pb_checked : Scalar.distance (sourceCoefficient 30 50 1 1) v2494_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2494_pg : Scalar.QComplex := ((-93086394789072770258036 : Int)/10^30,(80063149267651271014 : Int)/10^30)
theorem v2494_pg_checked : Scalar.distance (sourceCoefficient 30 50 1 2) v2494_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2494_mb : Scalar.QComplex := ((-743456932357871372210850 : Int)/10^30,(-431476874218145610574486239 : Int)/10^30)
theorem v2494_mb_checked : Scalar.distance (sourceCoefficient 30 50 3 1) v2494_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2494_mg : Scalar.QComplex := ((-93086291037861824282036 : Int)/10^30,(160392485703861499893 : Int)/10^30)
theorem v2494_mg_checked : Scalar.distance (sourceCoefficient 30 50 3 2) v2494_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2494_upper : Scalar.QComplex := ((999996656290944402491352537109 : Int)/10^30,(-2586002113457134978553985950 : Int)/10^30)
theorem v2494_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 50 5) 1) 14) v2494_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2494 : Material (30 : Basis) (50 : Basis) where
  plus := ![v2494_pa,v2494_pb,v2494_pg]
  minus := ![(Primitive.Addresses.material2494 1).one,v2494_mb,v2494_mg]
  upper := v2494_upper
  lower := (Primitive.Addresses.material2494 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2494_pa_checked.trans (by decide +kernel)
    · exact v2494_pb_checked.trans (by decide +kernel)
    · exact v2494_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 50 Primitive.Addresses.material2494
    · exact v2494_mb_checked.trans (by decide +kernel)
    · exact v2494_mg_checked.trans (by decide +kernel)
  upper_error := v2494_upper_checked
  lower_error := reuse_lower_error 30 50 Primitive.Addresses.material2494

def v2495_pa : Scalar.QComplex := ((999999620336177688854905873368 : Int)/10^30,(-871393998417290120106139001 : Int)/10^30)
theorem v2495_pa_checked : Scalar.distance (sourceCoefficient 30 51 1 0) v2495_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2495_pb : Scalar.QComplex := ((-375986916357044125753896 : Int)/10^30,(-431477350419348524452602122 : Int)/10^30)
theorem v2495_pb_checked : Scalar.distance (sourceCoefficient 30 51 1 1) v2495_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2495_pg : Scalar.QComplex := ((-93086393825700748653516 : Int)/10^30,(81114955710438054605 : Int)/10^30)
theorem v2495_pg_checked : Scalar.distance (sourceCoefficient 30 51 1 2) v2495_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2495_mb : Scalar.QComplex := ((-748332296753354159136246 : Int)/10^30,(-431476865300836480223073265 : Int)/10^30)
theorem v2495_mb_checked : Scalar.distance (sourceCoefficient 30 51 3 1) v2495_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2495_mg : Scalar.QComplex := ((-93086289166828572863620 : Int)/10^30,(161444290923666008926 : Int)/10^30)
theorem v2495_mg_checked : Scalar.distance (sourceCoefficient 30 51 3 2) v2495_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2495_upper : Scalar.QComplex := ((999996627007222382985826771959 : Int)/10^30,(-2597301326021636344768721230 : Int)/10^30)
theorem v2495_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 51 5) 1) 14) v2495_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2495 : Material (30 : Basis) (51 : Basis) where
  plus := ![v2495_pa,v2495_pb,v2495_pg]
  minus := ![(Primitive.Addresses.material2495 1).one,v2495_mb,v2495_mg]
  upper := v2495_upper
  lower := (Primitive.Addresses.material2495 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2495_pa_checked.trans (by decide +kernel)
    · exact v2495_pb_checked.trans (by decide +kernel)
    · exact v2495_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 51 Primitive.Addresses.material2495
    · exact v2495_mb_checked.trans (by decide +kernel)
    · exact v2495_mg_checked.trans (by decide +kernel)
  upper_error := v2495_upper_checked
  lower_error := reuse_lower_error 30 51 Primitive.Addresses.material2495

def v2496_pa : Scalar.QComplex := ((999999598965535312986917325981 : Int)/10^30,(-895582921088485417611634195 : Int)/10^30)
theorem v2496_pa_checked : Scalar.distance (sourceCoefficient 30 52 1 0) v2496_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2496_pb : Scalar.QComplex := ((-386423891589945967639749 : Int)/10^30,(-431477340089280252102567901 : Int)/10^30)
theorem v2496_pb_checked : Scalar.distance (sourceCoefficient 30 52 1 1) v2496_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2496_pg : Scalar.QComplex := ((-93086391716744233330713 : Int)/10^30,(83366616040155029773 : Int)/10^30)
theorem v2496_pg_checked : Scalar.distance (sourceCoefficient 30 52 1 2) v2496_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2496_mb : Scalar.QComplex := ((-758769259185709458446703 : Int)/10^30,(-431476845964132492150171888 : Int)/10^30)
theorem v2496_mb_checked : Scalar.distance (sourceCoefficient 30 52 3 1) v2496_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2496_mg : Scalar.QComplex := ((-93086285114791389272660 : Int)/10^30,(163695948595052448531 : Int)/10^30)
theorem v2496_mg_checked : Scalar.distance (sourceCoefficient 30 52 3 2) v2496_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2496_upper : Scalar.QComplex := ((999996563888725707619205313263 : Int)/10^30,(-2621490175782482742769049019 : Int)/10^30)
theorem v2496_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 52 5) 1) 14) v2496_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2496 : Material (30 : Basis) (52 : Basis) where
  plus := ![v2496_pa,v2496_pb,v2496_pg]
  minus := ![(Primitive.Addresses.material2496 1).one,v2496_mb,v2496_mg]
  upper := v2496_upper
  lower := (Primitive.Addresses.material2496 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2496_pa_checked.trans (by decide +kernel)
    · exact v2496_pb_checked.trans (by decide +kernel)
    · exact v2496_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 52 Primitive.Addresses.material2496
    · exact v2496_mb_checked.trans (by decide +kernel)
    · exact v2496_mg_checked.trans (by decide +kernel)
  upper_error := v2496_upper_checked
  lower_error := reuse_lower_error 30 52 Primitive.Addresses.material2496

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
