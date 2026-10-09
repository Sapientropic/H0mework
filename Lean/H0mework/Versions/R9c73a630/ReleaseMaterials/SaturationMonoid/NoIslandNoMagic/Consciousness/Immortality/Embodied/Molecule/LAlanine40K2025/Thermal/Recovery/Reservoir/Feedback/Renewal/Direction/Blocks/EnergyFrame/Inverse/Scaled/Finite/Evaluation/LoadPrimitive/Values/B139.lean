import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B092
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B093

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2225_pa : Scalar.QComplex := ((999999607778122080482881014689 : Int)/10^30,(-885688208118993034648075692 : Int)/10^30)
theorem v2225_pa_checked : Scalar.distance (sourceCoefficient 26 55 1 0) v2225_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2225_pb : Scalar.QComplex := ((-382154543092748939665550 : Int)/10^30,(-431477341236131252790667286 : Int)/10^30)
theorem v2225_pb_checked : Scalar.distance (sourceCoefficient 26 55 1 1) v2225_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2225_pg : Scalar.QComplex := ((-93086392250620467388559 : Int)/10^30,(82445552289663106111 : Int)/10^30)
theorem v2225_pg_checked : Scalar.distance (sourceCoefficient 26 55 1 2) v2225_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2225_mb : Scalar.QComplex := ((-754499913267866756186528 : Int)/10^30,(-431476850795238534575880844 : Int)/10^30)
theorem v2225_mb_checked : Scalar.distance (sourceCoefficient 26 55 3 1) v2225_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2225_mg : Scalar.QComplex := ((-93086286443503958047119 : Int)/10^30,(162774885648225798970 : Int)/10^30)
theorem v2225_mg_checked : Scalar.distance (sourceCoefficient 26 55 3 2) v2225_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2225_upper : Scalar.QComplex := ((999996589778676293797628031926 : Int)/10^30,(-2611595492759728302302464285 : Int)/10^30)
theorem v2225_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 55 5) 1) 14) v2225_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2225 : Material (26 : Basis) (55 : Basis) where
  plus := ![v2225_pa,v2225_pb,v2225_pg]
  minus := ![(Primitive.Addresses.material2225 1).one,v2225_mb,v2225_mg]
  upper := v2225_upper
  lower := (Primitive.Addresses.material2225 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2225_pa_checked.trans (by decide +kernel)
    · exact v2225_pb_checked.trans (by decide +kernel)
    · exact v2225_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 55 Primitive.Addresses.material2225
    · exact v2225_mb_checked.trans (by decide +kernel)
    · exact v2225_mg_checked.trans (by decide +kernel)
  upper_error := v2225_upper_checked
  lower_error := reuse_lower_error 26 55 Primitive.Addresses.material2225

def v2226_pa : Scalar.QComplex := ((999999604546290295037621423659 : Int)/10^30,(-889329670609436170821003032 : Int)/10^30)
theorem v2226_pa_checked : Scalar.distance (sourceCoefficient 26 56 1 0) v2226_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2226_pb : Scalar.QComplex := ((-383725752083522064533308 : Int)/10^30,(-431477339640306834822444437 : Int)/10^30)
theorem v2226_pb_checked : Scalar.distance (sourceCoefficient 26 56 1 1) v2226_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2226_pg : Scalar.QComplex := ((-93086391928060027050102 : Int)/10^30,(82784523009049231933 : Int)/10^30)
theorem v2226_pg_checked : Scalar.distance (sourceCoefficient 26 56 1 2) v2226_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2226_mb : Scalar.QComplex := ((-756071120296482366548344 : Int)/10^30,(-431476847843532116394852847 : Int)/10^30)
theorem v2226_mb_checked : Scalar.distance (sourceCoefficient 26 56 3 1) v2226_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2226_mg : Scalar.QComplex := ((-93086285828427173656905 : Int)/10^30,(163113855963042501808 : Int)/10^30)
theorem v2226_mg_checked : Scalar.distance (sourceCoefficient 26 56 3 2) v2226_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2226_upper : Scalar.QComplex := ((999996580262015414177895611771 : Int)/10^30,(-2615236944248792343003491131 : Int)/10^30)
theorem v2226_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 56 5) 1) 14) v2226_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2226 : Material (26 : Basis) (56 : Basis) where
  plus := ![v2226_pa,v2226_pb,v2226_pg]
  minus := ![(Primitive.Addresses.material2226 1).one,v2226_mb,v2226_mg]
  upper := v2226_upper
  lower := (Primitive.Addresses.material2226 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2226_pa_checked.trans (by decide +kernel)
    · exact v2226_pb_checked.trans (by decide +kernel)
    · exact v2226_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 56 Primitive.Addresses.material2226
    · exact v2226_mb_checked.trans (by decide +kernel)
    · exact v2226_mg_checked.trans (by decide +kernel)
  upper_error := v2226_upper_checked
  lower_error := reuse_lower_error 26 56 Primitive.Addresses.material2226

def v2227_pa : Scalar.QComplex := ((999999594002534260624930514135 : Int)/10^30,(-901107522244048272475266828 : Int)/10^30)
theorem v2227_pa_checked : Scalar.distance (sourceCoefficient 26 57 1 0) v2227_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2227_pb : Scalar.QComplex := ((-388807629584509303272075 : Int)/10^30,(-431477334426574383593468291 : Int)/10^30)
theorem v2227_pb_checked : Scalar.distance (sourceCoefficient 26 57 1 1) v2227_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2227_pg : Scalar.QComplex := ((-93086390874917609395369 : Int)/10^30,(83880881091363138920 : Int)/10^30)
theorem v2227_pg_checked : Scalar.distance (sourceCoefficient 26 57 1 2) v2227_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2227_mb : Scalar.QComplex := ((-761152991406038070776372 : Int)/10^30,(-431476838244370202391007332 : Int)/10^30)
theorem v2227_mb_checked : Scalar.distance (sourceCoefficient 26 57 3 1) v2227_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2227_mg : Scalar.QComplex := ((-93086283829177501233349 : Int)/10^30,(164210212728317714047 : Int)/10^30)
theorem v2227_mg_checked : Scalar.distance (sourceCoefficient 26 57 3 2) v2227_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2227_upper : Scalar.QComplex := ((999996549390771640464571069242 : Int)/10^30,(-2627014760144111565222463044 : Int)/10^30)
theorem v2227_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 57 5) 1) 14) v2227_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2227 : Material (26 : Basis) (57 : Basis) where
  plus := ![v2227_pa,v2227_pb,v2227_pg]
  minus := ![(Primitive.Addresses.material2227 1).one,v2227_mb,v2227_mg]
  upper := v2227_upper
  lower := (Primitive.Addresses.material2227 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2227_pa_checked.trans (by decide +kernel)
    · exact v2227_pb_checked.trans (by decide +kernel)
    · exact v2227_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 57 Primitive.Addresses.material2227
    · exact v2227_mb_checked.trans (by decide +kernel)
    · exact v2227_mg_checked.trans (by decide +kernel)
  upper_error := v2227_upper_checked
  lower_error := reuse_lower_error 26 57 Primitive.Addresses.material2227

def v2228_pa : Scalar.QComplex := ((999999588223541764693991211534 : Int)/10^30,(-907498069921231546397676780 : Int)/10^30)
theorem v2228_pa_checked : Scalar.distance (sourceCoefficient 26 58 1 0) v2228_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2228_pb : Scalar.QComplex := ((-391565006846577080408923 : Int)/10^30,(-431477331564255772371877463 : Int)/10^30)
theorem v2228_pb_checked : Scalar.distance (sourceCoefficient 26 58 1 1) v2228_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2228_pg : Scalar.QComplex := ((-93086390297188170586847 : Int)/10^30,(84475754315759639119 : Int)/10^30)
theorem v2228_pg_checked : Scalar.distance (sourceCoefficient 26 58 1 2) v2228_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2228_mb : Scalar.QComplex := ((-763910365171356227439580 : Int)/10^30,(-431476833002560267438779044 : Int)/10^30)
theorem v2228_mb_checked : Scalar.distance (sourceCoefficient 26 58 3 1) v2228_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2228_mg : Scalar.QComplex := ((-93086282738099476981178 : Int)/10^30,(164805085232661240030 : Int)/10^30)
theorem v2228_mg_checked : Scalar.distance (sourceCoefficient 26 58 3 2) v2228_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2228_upper : Scalar.QComplex := ((999996532582282206802322703951 : Int)/10^30,(-2633405288329307978570483896 : Int)/10^30)
theorem v2228_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 58 5) 1) 14) v2228_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2228 : Material (26 : Basis) (58 : Basis) where
  plus := ![v2228_pa,v2228_pb,v2228_pg]
  minus := ![(Primitive.Addresses.material2228 1).one,v2228_mb,v2228_mg]
  upper := v2228_upper
  lower := (Primitive.Addresses.material2228 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2228_pa_checked.trans (by decide +kernel)
    · exact v2228_pb_checked.trans (by decide +kernel)
    · exact v2228_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 58 Primitive.Addresses.material2228
    · exact v2228_mb_checked.trans (by decide +kernel)
    · exact v2228_mg_checked.trans (by decide +kernel)
  upper_error := v2228_upper_checked
  lower_error := reuse_lower_error 26 58 Primitive.Addresses.material2228

def v2229_pa : Scalar.QComplex := ((999999572128216063580459367972 : Int)/10^30,(-925063989569681386119459531 : Int)/10^30)
theorem v2229_pa_checked : Scalar.distance (sourceCoefficient 26 59 1 0) v2229_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2229_pb : Scalar.QComplex := ((-399144305138142385610208 : Int)/10^30,(-431477323575452571548602936 : Int)/10^30)
theorem v2229_pb_checked : Scalar.distance (sourceCoefficient 26 59 1 1) v2229_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2229_pg : Scalar.QComplex := ((-93086388686312676899156 : Int)/10^30,(86110902937220113654 : Int)/10^30)
theorem v2229_pg_checked : Scalar.distance (sourceCoefficient 26 59 1 2) v2229_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2229_mb : Scalar.QComplex := ((-771489653746825027676300 : Int)/10^30,(-431476818473166974514397364 : Int)/10^30)
theorem v2229_mb_checked : Scalar.distance (sourceCoefficient 26 59 3 1) v2229_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2229_mg : Scalar.QComplex := ((-93086279716164967135767 : Int)/10^30,(166440231855168152898 : Int)/10^30)
theorem v2229_mg_checked : Scalar.distance (sourceCoefficient 26 59 3 2) v2229_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2229_upper : Scalar.QComplex := ((999996486169796732343548534182 : Int)/10^30,(-2650971154036311936216274095 : Int)/10^30)
theorem v2229_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 59 5) 1) 14) v2229_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2229 : Material (26 : Basis) (59 : Basis) where
  plus := ![v2229_pa,v2229_pb,v2229_pg]
  minus := ![(Primitive.Addresses.material2229 1).one,v2229_mb,v2229_mg]
  upper := v2229_upper
  lower := (Primitive.Addresses.material2229 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2229_pa_checked.trans (by decide +kernel)
    · exact v2229_pb_checked.trans (by decide +kernel)
    · exact v2229_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 59 Primitive.Addresses.material2229
    · exact v2229_mb_checked.trans (by decide +kernel)
    · exact v2229_mg_checked.trans (by decide +kernel)
  upper_error := v2229_upper_checked
  lower_error := reuse_lower_error 26 59 Primitive.Addresses.material2229

def v2230_pa : Scalar.QComplex := ((999999553177470603908833655111 : Int)/10^30,(-945327910908066628406452957 : Int)/10^30)
theorem v2230_pa_checked : Scalar.distance (sourceCoefficient 26 60 1 0) v2230_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2230_pb : Scalar.QComplex := ((-407887730232782308992387 : Int)/10^30,(-431477314139116898459002236 : Int)/10^30)
theorem v2230_pb_checked : Scalar.distance (sourceCoefficient 26 60 1 1) v2230_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2230_pg : Scalar.QComplex := ((-93086386786392329689379 : Int)/10^30,(87997198873891499468 : Int)/10^30)
theorem v2230_pg_checked : Scalar.distance (sourceCoefficient 26 60 1 2) v2230_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2230_mb : Scalar.QComplex := ((-780233067442755504962622 : Int)/10^30,(-431476801491652747577694281 : Int)/10^30)
theorem v2230_mb_checked : Scalar.distance (sourceCoefficient 26 60 3 1) v2230_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2230_mg : Scalar.QComplex := ((-93086276188456889621048 : Int)/10^30,(168326525449939663100 : Int)/10^30)
theorem v2230_mg_checked : Scalar.distance (sourceCoefficient 26 60 3 2) v2230_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2230_upper : Scalar.QComplex := ((999996432245389596111829358212 : Int)/10^30,(-2671235012486699247195782691 : Int)/10^30)
theorem v2230_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 60 5) 1) 14) v2230_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2230 : Material (26 : Basis) (60 : Basis) where
  plus := ![v2230_pa,v2230_pb,v2230_pg]
  minus := ![(Primitive.Addresses.material2230 1).one,v2230_mb,v2230_mg]
  upper := v2230_upper
  lower := (Primitive.Addresses.material2230 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2230_pa_checked.trans (by decide +kernel)
    · exact v2230_pb_checked.trans (by decide +kernel)
    · exact v2230_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 60 Primitive.Addresses.material2230
    · exact v2230_mb_checked.trans (by decide +kernel)
    · exact v2230_mg_checked.trans (by decide +kernel)
  upper_error := v2230_upper_checked
  lower_error := reuse_lower_error 26 60 Primitive.Addresses.material2230

def v2231_pa : Scalar.QComplex := ((999999547621311235820732917526 : Int)/10^30,(-951187243859946056082287374 : Int)/10^30)
theorem v2231_pa_checked : Scalar.distance (sourceCoefficient 26 61 1 0) v2231_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2231_pb : Scalar.QComplex := ((-410415900250266379893995 : Int)/10^30,(-431477311366561677604030439 : Int)/10^30)
theorem v2231_pb_checked : Scalar.distance (sourceCoefficient 26 61 1 1) v2231_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2231_pg : Scalar.QComplex := ((-93086386228716982738877 : Int)/10^30,(88542623212571533595 : Int)/10^30)
theorem v2231_pg_checked : Scalar.distance (sourceCoefficient 26 61 1 2) v2231_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2231_mb : Scalar.QComplex := ((-782761234126296050931035 : Int)/10^30,(-431476796537401698533726728 : Int)/10^30)
theorem v2231_mb_checked : Scalar.distance (sourceCoefficient 26 61 3 1) v2231_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2231_mg : Scalar.QComplex := ((-93086275160105111038014 : Int)/10^30,(168871949104284581160 : Int)/10^30)
theorem v2231_mg_checked : Scalar.distance (sourceCoefficient 26 61 3 2) v2231_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2231_upper : Scalar.QComplex := ((999996416576561382859661251448 : Int)/10^30,(-2677094327122363510165545543 : Int)/10^30)
theorem v2231_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 61 5) 1) 14) v2231_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2231 : Material (26 : Basis) (61 : Basis) where
  plus := ![v2231_pa,v2231_pb,v2231_pg]
  minus := ![(Primitive.Addresses.material2231 1).one,v2231_mb,v2231_mg]
  upper := v2231_upper
  lower := (Primitive.Addresses.material2231 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2231_pa_checked.trans (by decide +kernel)
    · exact v2231_pb_checked.trans (by decide +kernel)
    · exact v2231_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 61 Primitive.Addresses.material2231
    · exact v2231_mb_checked.trans (by decide +kernel)
    · exact v2231_mg_checked.trans (by decide +kernel)
  upper_error := v2231_upper_checked
  lower_error := reuse_lower_error 26 61 Primitive.Addresses.material2231

def v2232_pa : Scalar.QComplex := ((999999539487270056452751645125 : Int)/10^30,(-959700603217024166861012120 : Int)/10^30)
theorem v2232_pa_checked : Scalar.distance (sourceCoefficient 26 62 1 0) v2232_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2232_pb : Scalar.QComplex := ((-414089222786467257275134 : Int)/10^30,(-431477307302960846988765341 : Int)/10^30)
theorem v2232_pb_checked : Scalar.distance (sourceCoefficient 26 62 1 1) v2232_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2232_pg : Scalar.QComplex := ((-93086385411794432292045 : Int)/10^30,(89335101370942927339 : Int)/10^30)
theorem v2232_pg_checked : Scalar.distance (sourceCoefficient 26 62 1 2) v2232_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2232_mb : Scalar.QComplex := ((-786434551788046569917784 : Int)/10^30,(-431476789303890472547007084 : Int)/10^30)
theorem v2232_mb_checked : Scalar.distance (sourceCoefficient 26 62 3 1) v2232_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2232_mg : Scalar.QComplex := ((-93086273659309905985577 : Int)/10^30,(169664426262612770292 : Int)/10^30)
theorem v2232_mg_checked : Scalar.distance (sourceCoefficient 26 62 3 2) v2232_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2232_upper : Scalar.QComplex := ((999996393749246393801500910972 : Int)/10^30,(-2685607659761175746878533525 : Int)/10^30)
theorem v2232_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 62 5) 1) 14) v2232_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2232 : Material (26 : Basis) (62 : Basis) where
  plus := ![v2232_pa,v2232_pb,v2232_pg]
  minus := ![(Primitive.Addresses.material2232 1).one,v2232_mb,v2232_mg]
  upper := v2232_upper
  lower := (Primitive.Addresses.material2232 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2232_pa_checked.trans (by decide +kernel)
    · exact v2232_pb_checked.trans (by decide +kernel)
    · exact v2232_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 62 Primitive.Addresses.material2232
    · exact v2232_mb_checked.trans (by decide +kernel)
    · exact v2232_mg_checked.trans (by decide +kernel)
  upper_error := v2232_upper_checked
  lower_error := reuse_lower_error 26 62 Primitive.Addresses.material2232

def v2233_pa : Scalar.QComplex := ((999999515383926599124278758600 : Int)/10^30,(-984495765328126154454391720 : Int)/10^30)
theorem v2233_pa_checked : Scalar.distance (sourceCoefficient 26 63 1 0) v2233_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2233_pb : Scalar.QComplex := ((-424787775848303335662953 : Int)/10^30,(-431477295230153061906353605 : Int)/10^30)
theorem v2233_pb_checked : Scalar.distance (sourceCoefficient 26 63 1 1) v2233_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2233_pg : Scalar.QComplex := ((-93086382987660982866986 : Int)/10^30,(91643194272829324182 : Int)/10^30)
theorem v2233_pg_checked : Scalar.distance (sourceCoefficient 26 63 1 2) v2233_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2233_mb : Scalar.QComplex := ((-797133090448033015906557 : Int)/10^30,(-431476767998717735301132690 : Int)/10^30)
theorem v2233_mb_checked : Scalar.distance (sourceCoefficient 26 63 3 1) v2233_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2233_mg : Scalar.QComplex := ((-93086269243397137493626 : Int)/10^30,(171972516213172706770 : Int)/10^30)
theorem v2233_mg_checked : Scalar.distance (sourceCoefficient 26 63 3 2) v2233_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2233_upper : Scalar.QComplex := ((999996326851738431345073802216 : Int)/10^30,(-2710402743342612245217602594 : Int)/10^30)
theorem v2233_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 63 5) 1) 14) v2233_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2233 : Material (26 : Basis) (63 : Basis) where
  plus := ![v2233_pa,v2233_pb,v2233_pg]
  minus := ![(Primitive.Addresses.material2233 1).one,v2233_mb,v2233_mg]
  upper := v2233_upper
  lower := (Primitive.Addresses.material2233 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2233_pa_checked.trans (by decide +kernel)
    · exact v2233_pb_checked.trans (by decide +kernel)
    · exact v2233_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 63 Primitive.Addresses.material2233
    · exact v2233_mb_checked.trans (by decide +kernel)
    · exact v2233_mg_checked.trans (by decide +kernel)
  upper_error := v2233_upper_checked
  lower_error := reuse_lower_error 26 63 Primitive.Addresses.material2233

def v2234_pa : Scalar.QComplex := ((999999479868183123341338396615 : Int)/10^30,(-1019933018985173553241230489 : Int)/10^30)
theorem v2234_pa_checked : Scalar.distance (sourceCoefficient 26 64 1 0) v2234_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2234_pb : Scalar.QComplex := ((-440078151021677529223273 : Int)/10^30,(-431477277361707362743968423 : Int)/10^30)
theorem v2234_pb_checked : Scalar.distance (sourceCoefficient 26 64 1 1) v2234_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2234_pg : Scalar.QComplex := ((-93086379407185847178131 : Int)/10^30,(94941921357484404587 : Int)/10^30)
theorem v2234_pg_checked : Scalar.distance (sourceCoefficient 26 64 1 2) v2234_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2234_mb : Scalar.QComplex := ((-812423444508437854295465 : Int)/10^30,(-431476736935373567689590799 : Int)/10^30)
theorem v2234_mb_checked : Scalar.distance (sourceCoefficient 26 64 3 1) v2234_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2234_mg : Scalar.QComplex := ((-93086262816270430074713 : Int)/10^30,(175271238979772150797 : Int)/10^30)
theorem v2234_mg_checked : Scalar.distance (sourceCoefficient 26 64 3 2) v2234_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2234_upper : Scalar.QComplex := ((999996230174562882565053605537 : Int)/10^30,(-2745839882923081797942466671 : Int)/10^30)
theorem v2234_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 64 5) 1) 14) v2234_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2234 : Material (26 : Basis) (64 : Basis) where
  plus := ![v2234_pa,v2234_pb,v2234_pg]
  minus := ![(Primitive.Addresses.material2234 1).one,v2234_mb,v2234_mg]
  upper := v2234_upper
  lower := (Primitive.Addresses.material2234 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2234_pa_checked.trans (by decide +kernel)
    · exact v2234_pb_checked.trans (by decide +kernel)
    · exact v2234_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 64 Primitive.Addresses.material2234
    · exact v2234_mb_checked.trans (by decide +kernel)
    · exact v2234_mg_checked.trans (by decide +kernel)
  upper_error := v2234_upper_checked
  lower_error := reuse_lower_error 26 64 Primitive.Addresses.material2234

def v2235_pa : Scalar.QComplex := ((999999442537842459164566332269 : Int)/10^30,(-1055899618485400238593808967 : Int)/10^30)
theorem v2235_pa_checked : Scalar.distance (sourceCoefficient 26 65 1 0) v2235_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2235_pb : Scalar.QComplex := ((-455596926600246075599321 : Int)/10^30,(-431477258487616234590601375 : Int)/10^30)
theorem v2235_pb_checked : Scalar.distance (sourceCoefficient 26 65 1 1) v2235_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2235_pg : Scalar.QComplex := ((-93086375633775169935798 : Int)/10^30,(98289923310804572140 : Int)/10^30)
theorem v2235_pg_checked : Scalar.distance (sourceCoefficient 26 65 1 2) v2235_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2235_mb : Scalar.QComplex := ((-827942198021166423601622 : Int)/10^30,(-431476704669285082624481055 : Int)/10^30)
theorem v2235_mb_checked : Scalar.distance (sourceCoefficient 26 65 3 1) v2235_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2235_mg : Scalar.QComplex := ((-93086256153686260540772 : Int)/10^30,(178619236430194713528 : Int)/10^30)
theorem v2235_mg_checked : Scalar.distance (sourceCoefficient 26 65 3 2) v2235_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2235_upper : Scalar.QComplex := ((999996130769189944572874533861 : Int)/10^30,(-2781806364426502056951507943 : Int)/10^30)
theorem v2235_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 65 5) 1) 14) v2235_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2235 : Material (26 : Basis) (65 : Basis) where
  plus := ![v2235_pa,v2235_pb,v2235_pg]
  minus := ![(Primitive.Addresses.material2235 1).one,v2235_mb,v2235_mg]
  upper := v2235_upper
  lower := (Primitive.Addresses.material2235 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2235_pa_checked.trans (by decide +kernel)
    · exact v2235_pb_checked.trans (by decide +kernel)
    · exact v2235_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 65 Primitive.Addresses.material2235
    · exact v2235_mb_checked.trans (by decide +kernel)
    · exact v2235_mg_checked.trans (by decide +kernel)
  upper_error := v2235_upper_checked
  lower_error := reuse_lower_error 26 65 Primitive.Addresses.material2235

def v2236_pa : Scalar.QComplex := ((999999423812476519839497593486 : Int)/10^30,(-1073487175036692644050997338 : Int)/10^30)
theorem v2236_pa_checked : Scalar.distance (sourceCoefficient 26 66 1 0) v2236_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2236_pb : Scalar.QComplex := ((-463185559989729735037901 : Int)/10^30,(-431477248987308089331400920 : Int)/10^30)
theorem v2236_pb_checked : Scalar.distance (sourceCoefficient 26 66 1 1) v2236_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2236_pg : Scalar.QComplex := ((-93086373737444038335563 : Int)/10^30,(99927085954558762357 : Int)/10^30)
theorem v2236_pg_checked : Scalar.distance (sourceCoefficient 26 66 1 2) v2236_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2236_mb : Scalar.QComplex := ((-835530820386717003092989 : Int)/10^30,(-431476688620331639000206622 : Int)/10^30)
theorem v2236_mb_checked : Scalar.distance (sourceCoefficient 26 66 3 1) v2236_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2236_mg : Scalar.QComplex := ((-93086252844558208539718 : Int)/10^30,(180256396827910070459 : Int)/10^30)
theorem v2236_mg_checked : Scalar.distance (sourceCoefficient 26 66 3 2) v2236_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2236_upper : Scalar.QComplex := ((999996081689324817616776262345 : Int)/10^30,(-2799393862464912099431344094 : Int)/10^30)
theorem v2236_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 66 5) 1) 14) v2236_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2236 : Material (26 : Basis) (66 : Basis) where
  plus := ![v2236_pa,v2236_pb,v2236_pg]
  minus := ![(Primitive.Addresses.material2236 1).one,v2236_mb,v2236_mg]
  upper := v2236_upper
  lower := (Primitive.Addresses.material2236 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2236_pa_checked.trans (by decide +kernel)
    · exact v2236_pb_checked.trans (by decide +kernel)
    · exact v2236_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 66 Primitive.Addresses.material2236
    · exact v2236_mb_checked.trans (by decide +kernel)
    · exact v2236_mg_checked.trans (by decide +kernel)
  upper_error := v2236_upper_checked
  lower_error := reuse_lower_error 26 66 Primitive.Addresses.material2236

def v2237_pa : Scalar.QComplex := ((999999391690558222333270032064 : Int)/10^30,(-1103004312555012861895014929 : Int)/10^30)
theorem v2237_pa_checked : Scalar.distance (sourceCoefficient 26 67 1 0) v2237_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2237_pb : Scalar.QComplex := ((-475921537882121364226671 : Int)/10^30,(-431477232643022443100847145 : Int)/10^30)
theorem v2237_pb_checked : Scalar.distance (sourceCoefficient 26 67 1 1) v2237_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2237_pg : Scalar.QComplex := ((-93086370479338644541910 : Int)/10^30,(102674730536812182242 : Int)/10^30)
theorem v2237_pg_checked : Scalar.distance (sourceCoefficient 26 67 1 2) v2237_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2237_mb : Scalar.QComplex := ((-848266779432539606602686 : Int)/10^30,(-431476661285476764511168679 : Int)/10^30)
theorem v2237_mb_checked : Scalar.distance (sourceCoefficient 26 67 3 1) v2237_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2237_mg : Scalar.QComplex := ((-93086247215360502721099 : Int)/10^30,(183004037575491623586 : Int)/10^30)
theorem v2237_mg_checked : Scalar.distance (sourceCoefficient 26 67 3 2) v2237_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2237_upper : Scalar.QComplex := ((999995998623552779111892279443 : Int)/10^30,(-2828910900581406406445379517 : Int)/10^30)
theorem v2237_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 67 5) 1) 14) v2237_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2237 : Material (26 : Basis) (67 : Basis) where
  plus := ![v2237_pa,v2237_pb,v2237_pg]
  minus := ![(Primitive.Addresses.material2237 1).one,v2237_mb,v2237_mg]
  upper := v2237_upper
  lower := (Primitive.Addresses.material2237 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2237_pa_checked.trans (by decide +kernel)
    · exact v2237_pb_checked.trans (by decide +kernel)
    · exact v2237_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 67 Primitive.Addresses.material2237
    · exact v2237_mb_checked.trans (by decide +kernel)
    · exact v2237_mg_checked.trans (by decide +kernel)
  upper_error := v2237_upper_checked
  lower_error := reuse_lower_error 26 67 Primitive.Addresses.material2237

def v2238_pa : Scalar.QComplex := ((999999336260838011346464027405 : Int)/10^30,(-1152162264365411298703845688 : Int)/10^30)
theorem v2238_pa_checked : Scalar.distance (sourceCoefficient 26 68 1 0) v2238_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2238_pb : Scalar.QComplex := ((-497132082706695557280251 : Int)/10^30,(-431477204310691552275893079 : Int)/10^30)
theorem v2238_pb_checked : Scalar.distance (sourceCoefficient 26 68 1 1) v2238_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2238_pg : Scalar.QComplex := ((-93086364843270143977848 : Int)/10^30,(107250668085835501734 : Int)/10^30)
theorem v2238_pg_checked : Scalar.distance (sourceCoefficient 26 68 1 2) v2238_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2238_mb : Scalar.QComplex := ((-869477291909933073713498 : Int)/10^30,(-431476614649411526977288924 : Int)/10^30)
theorem v2238_mb_checked : Scalar.distance (sourceCoefficient 26 68 3 1) v2238_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2238_mg : Scalar.QComplex := ((-93086237630466088492488 : Int)/10^30,(187579968557010986015 : Int)/10^30)
theorem v2238_mg_checked : Scalar.distance (sourceCoefficient 26 68 3 2) v2238_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2238_upper : Scalar.QComplex := ((999995858351749873986360988057 : Int)/10^30,(-2878068683510141581095270808 : Int)/10^30)
theorem v2238_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 68 5) 1) 14) v2238_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2238 : Material (26 : Basis) (68 : Basis) where
  plus := ![v2238_pa,v2238_pb,v2238_pg]
  minus := ![(Primitive.Addresses.material2238 1).one,v2238_mb,v2238_mg]
  upper := v2238_upper
  lower := (Primitive.Addresses.material2238 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2238_pa_checked.trans (by decide +kernel)
    · exact v2238_pb_checked.trans (by decide +kernel)
    · exact v2238_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 68 Primitive.Addresses.material2238
    · exact v2238_mb_checked.trans (by decide +kernel)
    · exact v2238_mg_checked.trans (by decide +kernel)
  upper_error := v2238_upper_checked
  lower_error := reuse_lower_error 26 68 Primitive.Addresses.material2238

def v2239_pa : Scalar.QComplex := ((999999311099315805101212550271 : Int)/10^30,(-1173797637502156881343093445 : Int)/10^30)
theorem v2239_pa_checked : Scalar.distance (sourceCoefficient 26 69 1 0) v2239_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2239_pb : Scalar.QComplex := ((-506467256807613587192760 : Int)/10^30,(-431477191400500842301402834 : Int)/10^30)
theorem v2239_pb_checked : Scalar.distance (sourceCoefficient 26 69 1 1) v2239_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2239_pg : Scalar.QComplex := ((-93086362279557670733605 : Int)/10^30,(109264627399891258776 : Int)/10^30)
theorem v2239_pg_checked : Scalar.distance (sourceCoefficient 26 69 1 2) v2239_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2239_mb : Scalar.QComplex := ((-878812451394026018018468 : Int)/10^30,(-431476593683390815598580429 : Int)/10^30)
theorem v2239_mb_checked : Scalar.distance (sourceCoefficient 26 69 3 1) v2239_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2239_mg : Scalar.QComplex := ((-93086233328798387165811 : Int)/10^30,(189593924908809248860 : Int)/10^30)
theorem v2239_mg_checked : Scalar.distance (sourceCoefficient 26 69 3 2) v2239_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2239_upper : Scalar.QComplex := ((999995795849573854568717460566 : Int)/10^30,(-2899703980997035653493384327 : Int)/10^30)
theorem v2239_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 69 5) 1) 14) v2239_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2239 : Material (26 : Basis) (69 : Basis) where
  plus := ![v2239_pa,v2239_pb,v2239_pg]
  minus := ![(Primitive.Addresses.material2239 1).one,v2239_mb,v2239_mg]
  upper := v2239_upper
  lower := (Primitive.Addresses.material2239 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2239_pa_checked.trans (by decide +kernel)
    · exact v2239_pb_checked.trans (by decide +kernel)
    · exact v2239_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 69 Primitive.Addresses.material2239
    · exact v2239_mb_checked.trans (by decide +kernel)
    · exact v2239_mg_checked.trans (by decide +kernel)
  upper_error := v2239_upper_checked
  lower_error := reuse_lower_error 26 69 Primitive.Addresses.material2239

def v2240_pa : Scalar.QComplex := ((999999294292593184081967584323 : Int)/10^30,(-1188029593742888220475429310 : Int)/10^30)
theorem v2240_pa_checked : Scalar.distance (sourceCoefficient 26 70 1 0) v2240_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2240_pb : Scalar.QComplex := ((-512608023896414846942881 : Int)/10^30,(-431477182761217862604693258 : Int)/10^30)
theorem v2240_pb_checked : Scalar.distance (sourceCoefficient 26 70 1 1) v2240_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2240_pg : Scalar.QComplex := ((-93086360565404622104356 : Int)/10^30,(110589429169300944150 : Int)/10^30)
theorem v2240_pg_checked : Scalar.distance (sourceCoefficient 26 70 1 2) v2240_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2240_mb : Scalar.QComplex := ((-884953208741026931070799 : Int)/10^30,(-431476579744905624949194728 : Int)/10^30)
theorem v2240_mb_checked : Scalar.distance (sourceCoefficient 26 70 3 1) v2240_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2240_mg : Scalar.QComplex := ((-93086230471401716650281 : Int)/10^30,(190918724705697810671 : Int)/10^30)
theorem v2240_mg_checked : Scalar.distance (sourceCoefficient 26 70 3 2) v2240_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2240_upper : Scalar.QComplex := ((999995754479810906670806831903 : Int)/10^30,(-2913935887034061425160890037 : Int)/10^30)
theorem v2240_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 70 5) 1) 14) v2240_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2240 : Material (26 : Basis) (70 : Basis) where
  plus := ![v2240_pa,v2240_pb,v2240_pg]
  minus := ![(Primitive.Addresses.material2240 1).one,v2240_mb,v2240_mg]
  upper := v2240_upper
  lower := (Primitive.Addresses.material2240 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2240_pa_checked.trans (by decide +kernel)
    · exact v2240_pb_checked.trans (by decide +kernel)
    · exact v2240_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 70 Primitive.Addresses.material2240
    · exact v2240_mb_checked.trans (by decide +kernel)
    · exact v2240_mg_checked.trans (by decide +kernel)
  upper_error := v2240_upper_checked
  lower_error := reuse_lower_error 26 70 Primitive.Addresses.material2240

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
