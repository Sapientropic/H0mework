import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B098
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B099

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2369_pa : Scalar.QComplex := ((999999541912955205941423405402 : Int)/10^30,(-957169723583219354346012518 : Int)/10^30)
theorem v2369_pa_checked : Scalar.distance (sourceCoefficient 28 60 1 0) v2369_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2369_pb : Scalar.QComplex := ((-412997206754799767394673 : Int)/10^30,(-431477310021938396312699712 : Int)/10^30)
theorem v2369_pb_checked : Scalar.distance (sourceCoefficient 28 60 1 1) v2369_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2369_pg : Scalar.QComplex := ((-93086385817988053917439 : Int)/10^30,(89099510998096221534 : Int)/10^30)
theorem v2369_pg_checked : Scalar.distance (sourceCoefficient 28 60 1 2) v2369_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2369_mb : Scalar.QComplex := ((-785342538509341723088857 : Int)/10^30,(-431476792965227662224056945 : Int)/10^30)
theorem v2369_mb_checked : Scalar.distance (sourceCoefficient 28 60 3 1) v2369_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2369_mg : Scalar.QComplex := ((-93086274268807257536719 : Int)/10^30,(169428836328013928491 : Int)/10^30)
theorem v2369_mg_checked : Scalar.distance (sourceCoefficient 28 60 3 2) v2369_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2369_upper : Scalar.QComplex := ((999996400542996578857344832272 : Int)/10^30,(-2683076788083331362489641992 : Int)/10^30)
theorem v2369_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 60 5) 1) 14) v2369_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2369 : Material (28 : Basis) (60 : Basis) where
  plus := ![v2369_pa,v2369_pb,v2369_pg]
  minus := ![(Primitive.Addresses.material2369 1).one,v2369_mb,v2369_mg]
  upper := v2369_upper
  lower := (Primitive.Addresses.material2369 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2369_pa_checked.trans (by decide +kernel)
    · exact v2369_pb_checked.trans (by decide +kernel)
    · exact v2369_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 60 Primitive.Addresses.material2369
    · exact v2369_mb_checked.trans (by decide +kernel)
    · exact v2369_mg_checked.trans (by decide +kernel)
  upper_error := v2369_upper_checked
  lower_error := reuse_lower_error 28 60 Primitive.Addresses.material2369

def v2370_pa : Scalar.QComplex := ((999999536287410683634170289225 : Int)/10^30,(-963029056468892930637148419 : Int)/10^30)
theorem v2370_pa_checked : Scalar.distance (sourceCoefficient 28 61 1 0) v2370_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2370_pb : Scalar.QComplex := ((-415525376753239614361194 : Int)/10^30,(-431477307229424419742302629 : Int)/10^30)
theorem v2370_pb_checked : Scalar.distance (sourceCoefficient 28 61 1 1) v2370_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2370_pg : Scalar.QComplex := ((-93086385254930360120844 : Int)/10^30,(89644935331640533771 : Int)/10^30)
theorem v2370_pg_checked : Scalar.distance (sourceCoefficient 28 61 1 2) v2370_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2370_mb : Scalar.QComplex := ((-787870705156614544939795 : Int)/10^30,(-431476787991017881330528555 : Int)/10^30)
theorem v2370_mb_checked : Scalar.distance (sourceCoefficient 28 61 3 1) v2370_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2370_mg : Scalar.QComplex := ((-93086273235073138543583 : Int)/10^30,(169974259972578403656 : Int)/10^30)
theorem v2370_mg_checked : Scalar.distance (sourceCoefficient 28 61 3 2) v2370_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2370_upper : Scalar.QComplex := ((999996384804783428992354345655 : Int)/10^30,(-2688936102533037391070308136 : Int)/10^30)
theorem v2370_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 61 5) 1) 14) v2370_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2370 : Material (28 : Basis) (61 : Basis) where
  plus := ![v2370_pa,v2370_pb,v2370_pg]
  minus := ![(Primitive.Addresses.material2370 1).one,v2370_mb,v2370_mg]
  upper := v2370_upper
  lower := (Primitive.Addresses.material2370 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2370_pa_checked.trans (by decide +kernel)
    · exact v2370_pb_checked.trans (by decide +kernel)
    · exact v2370_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 61 Primitive.Addresses.material2370
    · exact v2370_mb_checked.trans (by decide +kernel)
    · exact v2370_mg_checked.trans (by decide +kernel)
  upper_error := v2370_upper_checked
  lower_error := reuse_lower_error 28 61 Primitive.Addresses.material2370

def v2371_pa : Scalar.QComplex := ((999999528052555852483638834738 : Int)/10^30,(-971542415729052297436715985 : Int)/10^30)
theorem v2371_pa_checked : Scalar.distance (sourceCoefficient 28 62 1 0) v2371_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2371_pb : Scalar.QComplex := ((-419198699261561652877391 : Int)/10^30,(-431477303136824373515710103 : Int)/10^30)
theorem v2371_pb_checked : Scalar.distance (sourceCoefficient 28 62 1 1) v2371_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2371_pg : Scalar.QComplex := ((-93086384430187490664649 : Int)/10^30,(90437413482493744387 : Int)/10^30)
theorem v2371_pg_checked : Scalar.distance (sourceCoefficient 28 62 1 2) v2371_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2371_mb : Scalar.QComplex := ((-791544022765461218445779 : Int)/10^30,(-431476780728507474588397108 : Int)/10^30)
theorem v2371_mb_checked : Scalar.distance (sourceCoefficient 28 62 3 1) v2371_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2371_mg : Scalar.QComplex := ((-93086271726457623881499 : Int)/10^30,(170766737116639829368 : Int)/10^30)
theorem v2371_mg_checked : Scalar.distance (sourceCoefficient 28 62 3 2) v2371_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2371_upper : Scalar.QComplex := ((999996361876655105574695458033 : Int)/10^30,(-2697449434900935810919588696 : Int)/10^30)
theorem v2371_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 62 5) 1) 14) v2371_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2371 : Material (28 : Basis) (62 : Basis) where
  plus := ![v2371_pa,v2371_pb,v2371_pg]
  minus := ![(Primitive.Addresses.material2371 1).one,v2371_mb,v2371_mg]
  upper := v2371_upper
  lower := (Primitive.Addresses.material2371 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2371_pa_checked.trans (by decide +kernel)
    · exact v2371_pb_checked.trans (by decide +kernel)
    · exact v2371_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 62 Primitive.Addresses.material2371
    · exact v2371_mb_checked.trans (by decide +kernel)
    · exact v2371_mg_checked.trans (by decide +kernel)
  upper_error := v2371_upper_checked
  lower_error := reuse_lower_error 28 62 Primitive.Addresses.material2371

def v2372_pa : Scalar.QComplex := ((999999503655592599036051885740 : Int)/10^30,(-996337577552988381722276564 : Int)/10^30)
theorem v2372_pa_checked : Scalar.distance (sourceCoefficient 28 63 1 0) v2372_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2372_pb : Scalar.QComplex := ((-429897252240793978833715 : Int)/10^30,(-431477290979556362938833987 : Int)/10^30)
theorem v2372_pb_checked : Scalar.distance (sourceCoefficient 28 63 1 1) v2372_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2372_pg : Scalar.QComplex := ((-93086381983277359407106 : Int)/10^30,(92745506362104100925 : Int)/10^30)
theorem v2372_pg_checked : Scalar.distance (sourceCoefficient 28 63 1 2) v2372_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2372_mb : Scalar.QComplex := ((-802242561269958572105834 : Int)/10^30,(-431476759338874614579778323 : Int)/10^30)
theorem v2372_mb_checked : Scalar.distance (sourceCoefficient 28 63 3 1) v2372_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2372_mg : Scalar.QComplex := ((-93086267287768201261084 : Int)/10^30,(173074827025268483237 : Int)/10^30)
theorem v2372_mg_checked : Scalar.distance (sourceCoefficient 28 63 3 2) v2372_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2372_upper : Scalar.QComplex := ((999996294685528279933647224162 : Int)/10^30,(-2722244517688445702528955230 : Int)/10^30)
theorem v2372_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 63 5) 1) 14) v2372_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2372 : Material (28 : Basis) (63 : Basis) where
  plus := ![v2372_pa,v2372_pb,v2372_pg]
  minus := ![(Primitive.Addresses.material2372 1).one,v2372_mb,v2372_mg]
  upper := v2372_upper
  lower := (Primitive.Addresses.material2372 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2372_pa_checked.trans (by decide +kernel)
    · exact v2372_pb_checked.trans (by decide +kernel)
    · exact v2372_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 63 Primitive.Addresses.material2372
    · exact v2372_mb_checked.trans (by decide +kernel)
    · exact v2372_mg_checked.trans (by decide +kernel)
  upper_error := v2372_upper_checked
  lower_error := reuse_lower_error 28 63 Primitive.Addresses.material2372

def v2373_pa : Scalar.QComplex := ((999999467720207616360549453672 : Int)/10^30,(-1031774830786980149778900582 : Int)/10^30)
theorem v2373_pa_checked : Scalar.distance (sourceCoefficient 28 64 1 0) v2373_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2373_pb : Scalar.QComplex := ((-445187627292475512917328 : Int)/10^30,(-431477272990400082728540372 : Int)/10^30)
theorem v2373_pb_checked : Scalar.distance (sourceCoefficient 28 64 1 1) v2373_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2373_pg : Scalar.QComplex := ((-93086378370249782786204 : Int)/10^30,(96044233413941899903 : Int)/10^30)
theorem v2373_pg_checked : Scalar.distance (sourceCoefficient 28 64 1 2) v2373_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2373_mb : Scalar.QComplex := ((-817532915104503001488183 : Int)/10^30,(-431476728154820015881678363 : Int)/10^30)
theorem v2373_mb_checked : Scalar.distance (sourceCoefficient 28 64 3 1) v2373_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2373_mg : Scalar.QComplex := ((-93086260828089093350720 : Int)/10^30,(176373549730959367640 : Int)/10^30)
theorem v2373_mg_checked : Scalar.distance (sourceCoefficient 28 64 3 2) v2373_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2373_upper : Scalar.QComplex := ((999996197588712579423434253052 : Int)/10^30,(-2757681656121597083298830843 : Int)/10^30)
theorem v2373_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 64 5) 1) 14) v2373_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2373 : Material (28 : Basis) (64 : Basis) where
  plus := ![v2373_pa,v2373_pb,v2373_pg]
  minus := ![(Primitive.Addresses.material2373 1).one,v2373_mb,v2373_mg]
  upper := v2373_upper
  lower := (Primitive.Addresses.material2373 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2373_pa_checked.trans (by decide +kernel)
    · exact v2373_pb_checked.trans (by decide +kernel)
    · exact v2373_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 64 Primitive.Addresses.material2373
    · exact v2373_mb_checked.trans (by decide +kernel)
    · exact v2373_mg_checked.trans (by decide +kernel)
  upper_error := v2373_upper_checked
  lower_error := reuse_lower_error 28 64 Primitive.Addresses.material2373

def v2374_pa : Scalar.QComplex := ((999999429963957028267189102617 : Int)/10^30,(-1067741429842625959966161717 : Int)/10^30)
theorem v2374_pa_checked : Scalar.distance (sourceCoefficient 28 65 1 0) v2374_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2374_pb : Scalar.QComplex := ((-460706402743159627734178 : Int)/10^30,(-431477253993795253337415086 : Int)/10^30)
theorem v2374_pb_checked : Scalar.distance (sourceCoefficient 28 65 1 1) v2374_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2374_pg : Scalar.QComplex := ((-93086374563800410890017 : Int)/10^30,(99392235332775029331 : Int)/10^30)
theorem v2374_pg_checked : Scalar.distance (sourceCoefficient 28 65 1 2) v2374_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2374_mb : Scalar.QComplex := ((-833051668383623380496448 : Int)/10^30,(-431476695766217985554765239 : Int)/10^30)
theorem v2374_mb_checked : Scalar.distance (sourceCoefficient 28 65 3 1) v2374_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2374_mg : Scalar.QComplex := ((-93086254132466271225503 : Int)/10^30,(179721547118383999609 : Int)/10^30)
theorem v2374_mg_checked : Scalar.distance (sourceCoefficient 28 65 3 2) v2374_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2374_upper : Scalar.QComplex := ((999996097757431119163726147682 : Int)/10^30,(-2793648136445355238859985105 : Int)/10^30)
theorem v2374_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 65 5) 1) 14) v2374_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2374 : Material (28 : Basis) (65 : Basis) where
  plus := ![v2374_pa,v2374_pb,v2374_pg]
  minus := ![(Primitive.Addresses.material2374 1).one,v2374_mb,v2374_mg]
  upper := v2374_upper
  lower := (Primitive.Addresses.material2374 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2374_pa_checked.trans (by decide +kernel)
    · exact v2374_pb_checked.trans (by decide +kernel)
    · exact v2374_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 65 Primitive.Addresses.material2374
    · exact v2374_mb_checked.trans (by decide +kernel)
    · exact v2374_mg_checked.trans (by decide +kernel)
  upper_error := v2374_upper_checked
  lower_error := reuse_lower_error 28 65 Primitive.Addresses.material2374

def v2375_pa : Scalar.QComplex := ((999999411030322445936133207586 : Int)/10^30,(-1085328986170942849681545278 : Int)/10^30)
theorem v2375_pa_checked : Scalar.distance (sourceCoefficient 28 66 1 0) v2375_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2375_pb : Scalar.QComplex := ((-468295036068504007701268 : Int)/10^30,(-431477244433578285109523068 : Int)/10^30)
theorem v2375_pb_checked : Scalar.distance (sourceCoefficient 28 66 1 1) v2375_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2375_pg : Scalar.QComplex := ((-93086372651313459235124 : Int)/10^30,(101029397959232557618 : Int)/10^30)
theorem v2375_pg_checked : Scalar.distance (sourceCoefficient 28 66 1 2) v2375_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2375_mb : Scalar.QComplex := ((-840640290633336088369554 : Int)/10^30,(-431476679657355796617901461 : Int)/10^30)
theorem v2375_mb_checked : Scalar.distance (sourceCoefficient 28 66 3 1) v2375_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2375_mg : Scalar.QComplex := ((-93086250807182420111581 : Int)/10^30,(181358707484860955974 : Int)/10^30)
theorem v2375_mg_checked : Scalar.distance (sourceCoefficient 28 66 3 2) v2375_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2375_upper : Scalar.QComplex := ((999996048469298044228831513540 : Int)/10^30,(-2811235633901337313849222570 : Int)/10^30)
theorem v2375_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 66 5) 1) 14) v2375_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2375 : Material (28 : Basis) (66 : Basis) where
  plus := ![v2375_pa,v2375_pb,v2375_pg]
  minus := ![(Primitive.Addresses.material2375 1).one,v2375_mb,v2375_mg]
  upper := v2375_upper
  lower := (Primitive.Addresses.material2375 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2375_pa_checked.trans (by decide +kernel)
    · exact v2375_pb_checked.trans (by decide +kernel)
    · exact v2375_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 66 Primitive.Addresses.material2375
    · exact v2375_mb_checked.trans (by decide +kernel)
    · exact v2375_mg_checked.trans (by decide +kernel)
  upper_error := v2375_upper_checked
  lower_error := reuse_lower_error 28 66 Primitive.Addresses.material2375

def v2376_pa : Scalar.QComplex := ((999999378558867579346200691273 : Int)/10^30,(-1114846123306811581950825465 : Int)/10^30)
theorem v2376_pa_checked : Scalar.distance (sourceCoefficient 28 67 1 0) v2376_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2376_pb : Scalar.QComplex := ((-481031013850882828666929 : Int)/10^30,(-431477227988747861326254201 : Int)/10^30)
theorem v2376_pb_checked : Scalar.distance (sourceCoefficient 28 67 1 1) v2376_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2376_pg : Scalar.QComplex := ((-93086369366093806558998 : Int)/10^30,(103777042511818441951 : Int)/10^30)
theorem v2376_pg_checked : Scalar.distance (sourceCoefficient 28 67 1 2) v2376_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2376_mb : Scalar.QComplex := ((-853376249482380309959625 : Int)/10^30,(-431476652221956276949662936 : Int)/10^30)
theorem v2376_mb_checked : Scalar.distance (sourceCoefficient 28 67 3 1) v2376_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2376_mg : Scalar.QComplex := ((-93086245150870491108114 : Int)/10^30,(184106348179376600361 : Int)/10^30)
theorem v2376_mg_checked : Scalar.distance (sourceCoefficient 28 67 3 2) v2376_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2376_upper : Scalar.QComplex := ((999995965053990617310471150506 : Int)/10^30,(-2840752671032112296376452307 : Int)/10^30)
theorem v2376_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 67 5) 1) 14) v2376_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2376 : Material (28 : Basis) (67 : Basis) where
  plus := ![v2376_pa,v2376_pb,v2376_pg]
  minus := ![(Primitive.Addresses.material2376 1).one,v2376_mb,v2376_mg]
  upper := v2376_upper
  lower := (Primitive.Addresses.material2376 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2376_pa_checked.trans (by decide +kernel)
    · exact v2376_pb_checked.trans (by decide +kernel)
    · exact v2376_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 67 Primitive.Addresses.material2376
    · exact v2376_mb_checked.trans (by decide +kernel)
    · exact v2376_mg_checked.trans (by decide +kernel)
  upper_error := v2376_upper_checked
  lower_error := reuse_lower_error 28 67 Primitive.Addresses.material2376

def v2377_pa : Scalar.QComplex := ((999999322547027852050532999938 : Int)/10^30,(-1164004074457374681706026464 : Int)/10^30)
theorem v2377_pa_checked : Scalar.distance (sourceCoefficient 28 68 1 0) v2377_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2377_pb : Scalar.QComplex := ((-502241558485654286503025 : Int)/10^30,(-431477199488969320736813351 : Int)/10^30)
theorem v2377_pb_checked : Scalar.distance (sourceCoefficient 28 68 1 1) v2377_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2377_pg : Scalar.QComplex := ((-93086363684869117438282 : Int)/10^30,(108352980009656999446 : Int)/10^30)
theorem v2377_pg_checked : Scalar.distance (sourceCoefficient 28 68 1 2) v2377_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2377_mb : Scalar.QComplex := ((-874586761625471332340623 : Int)/10^30,(-431476605418443615790921235 : Int)/10^30)
theorem v2377_mb_checked : Scalar.distance (sourceCoefficient 28 68 3 1) v2377_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2377_mg : Scalar.QComplex := ((-93086235520819949306705 : Int)/10^30,(188682279070743462886 : Int)/10^30)
theorem v2377_mg_checked : Scalar.distance (sourceCoefficient 28 68 3 2) v2377_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2377_upper : Scalar.QComplex := ((999995824200070201690649113021 : Int)/10^30,(-2889910452296327641040838004 : Int)/10^30)
theorem v2377_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 68 5) 1) 14) v2377_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2377 : Material (28 : Basis) (68 : Basis) where
  plus := ![v2377_pa,v2377_pb,v2377_pg]
  minus := ![(Primitive.Addresses.material2377 1).one,v2377_mb,v2377_mg]
  upper := v2377_upper
  lower := (Primitive.Addresses.material2377 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2377_pa_checked.trans (by decide +kernel)
    · exact v2377_pb_checked.trans (by decide +kernel)
    · exact v2377_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 68 Primitive.Addresses.material2377
    · exact v2377_mb_checked.trans (by decide +kernel)
    · exact v2377_mg_checked.trans (by decide +kernel)
  upper_error := v2377_upper_checked
  lower_error := reuse_lower_error 28 68 Primitive.Addresses.material2377

def v2378_pa : Scalar.QComplex := ((999999297129303495816183783062 : Int)/10^30,(-1185639447294645147324700970 : Int)/10^30)
theorem v2378_pa_checked : Scalar.distance (sourceCoefficient 28 69 1 0) v2378_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2378_pb : Scalar.QComplex := ((-511576732500427799906664 : Int)/10^30,(-431477186505081635337500454 : Int)/10^30)
theorem v2378_pb_checked : Scalar.distance (sourceCoefficient 28 69 1 1) v2378_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2378_pg : Scalar.QComplex := ((-93086361101282525154483 : Int)/10^30,(110366939300481865860 : Int)/10^30)
theorem v2378_pg_checked : Scalar.distance (sourceCoefficient 28 69 1 2) v2378_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2378_mb : Scalar.QComplex := ((-883921920959822621609201 : Int)/10^30,(-431476584378726030766980098 : Int)/10^30)
theorem v2378_mb_checked : Scalar.distance (sourceCoefficient 28 69 3 1) v2378_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2378_mg : Scalar.QComplex := ((-93086231199278156387728 : Int)/10^30,(190696235382160374119 : Int)/10^30)
theorem v2378_mg_checked : Scalar.distance (sourceCoefficient 28 69 3 2) v2378_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2378_upper : Scalar.QComplex := ((999995761441692930733798443030 : Int)/10^30,(-2911545749041565374047690298 : Int)/10^30)
theorem v2378_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 69 5) 1) 14) v2378_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2378 : Material (28 : Basis) (69 : Basis) where
  plus := ![v2378_pa,v2378_pb,v2378_pg]
  minus := ![(Primitive.Addresses.material2378 1).one,v2378_mb,v2378_mg]
  upper := v2378_upper
  lower := (Primitive.Addresses.material2378 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2378_pa_checked.trans (by decide +kernel)
    · exact v2378_pb_checked.trans (by decide +kernel)
    · exact v2378_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 69 Primitive.Addresses.material2378
    · exact v2378_mb_checked.trans (by decide +kernel)
    · exact v2378_mg_checked.trans (by decide +kernel)
  upper_error := v2378_upper_checked
  lower_error := reuse_lower_error 28 69 Primitive.Addresses.material2378

def v2379_pa : Scalar.QComplex := ((999999280154048639924310831953 : Int)/10^30,(-1199871403335356471418118526 : Int)/10^30)
theorem v2379_pa_checked : Scalar.distance (sourceCoefficient 28 70 1 0) v2379_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2379_pb : Scalar.QComplex := ((-517717499531692969118928 : Int)/10^30,(-431477177817320077523005978 : Int)/10^30)
theorem v2379_pb_checked : Scalar.distance (sourceCoefficient 28 70 1 1) v2379_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2379_pg : Scalar.QComplex := ((-93086359374056090165170 : Int)/10^30,(111691741054375594074 : Int)/10^30)
theorem v2379_pg_checked : Scalar.distance (sourceCoefficient 28 70 1 2) v2379_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2379_mb : Scalar.QComplex := ((-890062678207452636025450 : Int)/10^30,(-431476570391762329701654516 : Int)/10^30)
theorem v2379_mb_checked : Scalar.distance (sourceCoefficient 28 70 3 1) v2379_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2379_mg : Scalar.QComplex := ((-93086228328808117769525 : Int)/10^30,(192021035152251240923 : Int)/10^30)
theorem v2379_mg_checked : Scalar.distance (sourceCoefficient 28 70 3 2) v2379_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2379_upper : Scalar.QComplex := ((999995719903398344188626768155 : Int)/10^30,(-2925777654587700080317353751 : Int)/10^30)
theorem v2379_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 70 5) 1) 14) v2379_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2379 : Material (28 : Basis) (70 : Basis) where
  plus := ![v2379_pa,v2379_pb,v2379_pg]
  minus := ![(Primitive.Addresses.material2379 1).one,v2379_mb,v2379_mg]
  upper := v2379_upper
  lower := (Primitive.Addresses.material2379 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2379_pa_checked.trans (by decide +kernel)
    · exact v2379_pb_checked.trans (by decide +kernel)
    · exact v2379_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 70 Primitive.Addresses.material2379
    · exact v2379_mb_checked.trans (by decide +kernel)
    · exact v2379_mg_checked.trans (by decide +kernel)
  upper_error := v2379_upper_checked
  lower_error := reuse_lower_error 28 70 Primitive.Addresses.material2379

def v2380_pa : Scalar.QComplex := ((999999250710722554599242355516 : Int)/10^30,(-1224164201999217186975956956 : Int)/10^30)
theorem v2380_pa_checked : Scalar.distance (sourceCoefficient 28 71 1 0) v2380_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2380_pb : Scalar.QComplex := ((-528199292354621014891584 : Int)/10^30,(-431477162718807117403490426 : Int)/10^30)
theorem v2380_pb_checked : Scalar.distance (sourceCoefficient 28 71 1 1) v2380_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2380_pg : Scalar.QComplex := ((-93086356375001722226647 : Int)/10^30,(113953070552632623893 : Int)/10^30)
theorem v2380_pg_checked : Scalar.distance (sourceCoefficient 28 71 1 2) v2380_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2380_mb : Scalar.QComplex := ((-900544454098193499422209 : Int)/10^30,(-431476546247939867685867991 : Int)/10^30)
theorem v2380_mb_checked : Scalar.distance (sourceCoefficient 28 71 3 1) v2380_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2380_mg : Scalar.QComplex := ((-93086223378329356020072 : Int)/10^30,(194282361220463103540 : Int)/10^30)
theorem v2380_mg_checked : Scalar.distance (sourceCoefficient 28 71 3 2) v2380_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2380_upper : Scalar.QComplex := ((999995648532949442894956840105 : Int)/10^30,(-2950070366253781073048548262 : Int)/10^30)
theorem v2380_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 71 5) 1) 14) v2380_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2380 : Material (28 : Basis) (71 : Basis) where
  plus := ![v2380_pa,v2380_pb,v2380_pg]
  minus := ![(Primitive.Addresses.material2380 1).one,v2380_mb,v2380_mg]
  upper := v2380_upper
  lower := (Primitive.Addresses.material2380 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2380_pa_checked.trans (by decide +kernel)
    · exact v2380_pb_checked.trans (by decide +kernel)
    · exact v2380_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 71 Primitive.Addresses.material2380
    · exact v2380_mb_checked.trans (by decide +kernel)
    · exact v2380_mg_checked.trans (by decide +kernel)
  upper_error := v2380_upper_checked
  lower_error := reuse_lower_error 28 71 Primitive.Addresses.material2380

def v2381_pa : Scalar.QComplex := ((999999218091045558493850682079 : Int)/10^30,(-1250526807989896417648969265 : Int)/10^30)
theorem v2381_pa_checked : Scalar.distance (sourceCoefficient 28 72 1 0) v2381_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2381_pb : Scalar.QComplex := ((-539574159942973665584622 : Int)/10^30,(-431477145949729920381494548 : Int)/10^30)
theorem v2381_pb_checked : Scalar.distance (sourceCoefficient 28 72 1 1) v2381_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2381_pg : Scalar.QComplex := ((-93086353047907033257552 : Int)/10^30,(116407070964150894924 : Int)/10^30)
theorem v2381_pg_checked : Scalar.distance (sourceCoefficient 28 72 1 2) v2381_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2381_mb : Scalar.QComplex := ((-911919302980204720012034 : Int)/10^30,(-431476519662870490827882887 : Int)/10^30)
theorem v2381_mb_checked : Scalar.distance (sourceCoefficient 28 72 3 1) v2381_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2381_mg : Scalar.QComplex := ((-93086217933544074815806 : Int)/10^30,(196736357847111998206 : Int)/10^30)
theorem v2381_mg_checked : Scalar.distance (sourceCoefficient 28 72 3 2) v2381_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2381_upper : Scalar.QComplex := ((999995570413854686987666718213 : Int)/10^30,(-2976432876681852188543599116 : Int)/10^30)
theorem v2381_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 72 5) 1) 14) v2381_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2381 : Material (28 : Basis) (72 : Basis) where
  plus := ![v2381_pa,v2381_pb,v2381_pg]
  minus := ![(Primitive.Addresses.material2381 1).one,v2381_mb,v2381_mg]
  upper := v2381_upper
  lower := (Primitive.Addresses.material2381 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2381_pa_checked.trans (by decide +kernel)
    · exact v2381_pb_checked.trans (by decide +kernel)
    · exact v2381_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 72 Primitive.Addresses.material2381
    · exact v2381_mb_checked.trans (by decide +kernel)
    · exact v2381_mg_checked.trans (by decide +kernel)
  upper_error := v2381_upper_checked
  lower_error := reuse_lower_error 28 72 Primitive.Addresses.material2381

def v2382_pa : Scalar.QComplex := ((999999206229366285637081419067 : Int)/10^30,(-1259976443175390041331829621 : Int)/10^30)
theorem v2382_pa_checked : Scalar.distance (sourceCoefficient 28 73 1 0) v2382_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2382_pb : Scalar.QComplex := ((-543651463503594504114245 : Int)/10^30,(-431477139841535121251980937 : Int)/10^30)
theorem v2382_pb_checked : Scalar.distance (sourceCoefficient 28 73 1 1) v2382_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2382_pg : Scalar.QComplex := ((-93086351836939126219388 : Int)/10^30,(117286703594420533769 : Int)/10^30)
theorem v2382_pg_checked : Scalar.distance (sourceCoefficient 28 73 1 2) v2382_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2382_mb : Scalar.QComplex := ((-915996599751562092177001 : Int)/10^30,(-431476510036148628178188761 : Int)/10^30)
theorem v2382_mb_checked : Scalar.distance (sourceCoefficient 28 73 3 1) v2382_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2382_mg : Scalar.QComplex := ((-93086215963493275936647 : Int)/10^30,(197615989104843443801 : Int)/10^30)
theorem v2382_mg_checked : Scalar.distance (sourceCoefficient 28 73 3 2) v2382_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2382_upper : Scalar.QComplex := ((999995542242980014754256662921 : Int)/10^30,(-2985882477321041893745048564 : Int)/10^30)
theorem v2382_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 73 5) 1) 14) v2382_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2382 : Material (28 : Basis) (73 : Basis) where
  plus := ![v2382_pa,v2382_pb,v2382_pg]
  minus := ![(Primitive.Addresses.material2382 1).one,v2382_mb,v2382_mg]
  upper := v2382_upper
  lower := (Primitive.Addresses.material2382 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2382_pa_checked.trans (by decide +kernel)
    · exact v2382_pb_checked.trans (by decide +kernel)
    · exact v2382_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 73 Primitive.Addresses.material2382
    · exact v2382_mb_checked.trans (by decide +kernel)
    · exact v2382_mg_checked.trans (by decide +kernel)
  upper_error := v2382_upper_checked
  lower_error := reuse_lower_error 28 73 Primitive.Addresses.material2382

def v2383_pa : Scalar.QComplex := ((999999192775289522272424715252 : Int)/10^30,(-1270609605403533042533371614 : Int)/10^30)
theorem v2383_pa_checked : Scalar.distance (sourceCoefficient 28 74 1 0) v2383_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2383_pb : Scalar.QComplex := ((-548239432135886051341385 : Int)/10^30,(-431477132906888337863225728 : Int)/10^30)
theorem v2383_pb_checked : Scalar.distance (sourceCoefficient 28 74 1 1) v2383_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2383_pg : Scalar.QComplex := ((-93086350462707052813349 : Int)/10^30,(118276506505593914122 : Int)/10^30)
theorem v2383_pg_checked : Scalar.distance (sourceCoefficient 28 74 1 2) v2383_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2383_mb : Scalar.QComplex := ((-920584560691255387909658 : Int)/10^30,(-431476499142294131644322330 : Int)/10^30)
theorem v2383_mb_checked : Scalar.distance (sourceCoefficient 28 74 3 1) v2383_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2383_mg : Scalar.QComplex := ((-93086213735106380945654 : Int)/10^30,(198605790461567577861 : Int)/10^30)
theorem v2383_mg_checked : Scalar.distance (sourceCoefficient 28 74 3 2) v2383_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2383_upper : Scalar.QComplex := ((999995510437049916823730156297 : Int)/10^30,(-2996515600491822865846721571 : Int)/10^30)
theorem v2383_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 74 5) 1) 14) v2383_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2383 : Material (28 : Basis) (74 : Basis) where
  plus := ![v2383_pa,v2383_pb,v2383_pg]
  minus := ![(Primitive.Addresses.material2383 1).one,v2383_mb,v2383_mg]
  upper := v2383_upper
  lower := (Primitive.Addresses.material2383 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2383_pa_checked.trans (by decide +kernel)
    · exact v2383_pb_checked.trans (by decide +kernel)
    · exact v2383_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 74 Primitive.Addresses.material2383
    · exact v2383_mb_checked.trans (by decide +kernel)
    · exact v2383_mg_checked.trans (by decide +kernel)
  upper_error := v2383_upper_checked
  lower_error := reuse_lower_error 28 74 Primitive.Addresses.material2383

def v2384_pa : Scalar.QComplex := ((999999173841300450696273931537 : Int)/10^30,(-1285424722245690516243182211 : Int)/10^30)
theorem v2384_pa_checked : Scalar.distance (sourceCoefficient 28 75 1 0) v2384_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2384_pb : Scalar.QComplex := ((-554631819376929312182525 : Int)/10^30,(-431477123136438984673405349 : Int)/10^30)
theorem v2384_pb_checked : Scalar.distance (sourceCoefficient 28 75 1 1) v2384_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2384_pg : Scalar.QComplex := ((-93086348527525962433177 : Int)/10^30,(119655592555369341979 : Int)/10^30)
theorem v2384_pg_checked : Scalar.distance (sourceCoefficient 28 75 1 2) v2384_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2384_mb : Scalar.QComplex := ((-926976937120662985281970 : Int)/10^30,(-431476483855506129852889507 : Int)/10^30)
theorem v2384_mb_checked : Scalar.distance (sourceCoefficient 28 75 3 1) v2384_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2384_mg : Scalar.QComplex := ((-93086210609836861895636 : Int)/10^30,(199984874327872118363 : Int)/10^30)
theorem v2384_mg_checked : Scalar.distance (sourceCoefficient 28 75 3 2) v2384_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2384_upper : Scalar.QComplex := ((999995465933541392537395925256 : Int)/10^30,(-3011330662590256649567447254 : Int)/10^30)
theorem v2384_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 75 5) 1) 14) v2384_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2384 : Material (28 : Basis) (75 : Basis) where
  plus := ![v2384_pa,v2384_pb,v2384_pg]
  minus := ![(Primitive.Addresses.material2384 1).one,v2384_mb,v2384_mg]
  upper := v2384_upper
  lower := (Primitive.Addresses.material2384 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2384_pa_checked.trans (by decide +kernel)
    · exact v2384_pb_checked.trans (by decide +kernel)
    · exact v2384_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 75 Primitive.Addresses.material2384
    · exact v2384_mb_checked.trans (by decide +kernel)
    · exact v2384_mg_checked.trans (by decide +kernel)
  upper_error := v2384_upper_checked
  lower_error := reuse_lower_error 28 75 Primitive.Addresses.material2384

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
