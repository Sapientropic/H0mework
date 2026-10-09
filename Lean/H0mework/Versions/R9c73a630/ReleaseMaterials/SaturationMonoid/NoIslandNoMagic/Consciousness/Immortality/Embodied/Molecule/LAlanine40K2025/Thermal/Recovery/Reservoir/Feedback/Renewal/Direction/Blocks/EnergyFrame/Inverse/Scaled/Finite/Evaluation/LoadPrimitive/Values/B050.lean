import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B033
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B034

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v801_pa : Scalar.QComplex := ((999999824861676801624275069451 : Int)/10^30,(-591841715092235786483787664 : Int)/10^30)
theorem v801_pa_checked : Scalar.distance (sourceCoefficient 8 62 1 0) v801_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v801_pb : Scalar.QComplex := ((-255366367118196640794646 : Int)/10^30,(-431477396543367419501176347 : Int)/10^30)
theorem v801_pb_checked : Scalar.distance (sourceCoefficient 8 62 1 1) v801_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v801_pg : Scalar.QComplex := ((-93086408320344564419562 : Int)/10^30,(55092429200884565648 : Int)/10^30)
theorem v801_pg_checked : Scalar.distance (sourceCoefficient 8 62 1 2) v801_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v801_mb : Scalar.QComplex := ((-627711832230000744960343 : Int)/10^30,(-431477015514939646444759281 : Int)/10^30)
theorem v801_mb_checked : Scalar.distance (sourceCoefficient 8 62 3 1) v801_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v801_mg : Scalar.QComplex := ((-93086326117735358269104 : Int)/10^30,(135421786611713226171 : Int)/10^30)
theorem v801_mg_checked : Scalar.distance (sourceCoefficient 8 62 3 2) v801_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v801_upper : Scalar.QComplex := ((999997314014297113057632082160 : Int)/10^30,(-2317749812049326566134870824 : Int)/10^30)
theorem v801_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 62 5) 1) 14) v801_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material801 : Material (8 : Basis) (62 : Basis) where
  plus := ![v801_pa,v801_pb,v801_pg]
  minus := ![(Primitive.Addresses.material801 1).one,v801_mb,v801_mg]
  upper := v801_upper
  lower := (Primitive.Addresses.material801 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v801_pa_checked.trans (by decide +kernel)
    · exact v801_pb_checked.trans (by decide +kernel)
    · exact v801_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 62 Primitive.Addresses.material801
    · exact v801_mb_checked.trans (by decide +kernel)
    · exact v801_mg_checked.trans (by decide +kernel)
  upper_error := v801_upper_checked
  lower_error := reuse_lower_error 8 62 Primitive.Addresses.material801

def v802_pa : Scalar.QComplex := ((999999809879458330552570666172 : Int)/10^30,(-616636884392325735277975948 : Int)/10^30)
theorem v802_pa_checked : Scalar.distance (sourceCoefficient 8 63 1 0) v802_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v802_pb : Scalar.QComplex := ((-266064922247957089012758 : Int)/10^30,(-431477387094266435162130181 : Int)/10^30)
theorem v802_pb_checked : Scalar.distance (sourceCoefficient 8 63 1 1) v802_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v802_pg : Scalar.QComplex := ((-93086406603755230651825 : Int)/10^30,(57400522660435301354 : Int)/10^30)
theorem v802_pg_checked : Scalar.distance (sourceCoefficient 8 63 1 2) v802_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v802_mb : Scalar.QComplex := ((-638410375222051592470456 : Int)/10^30,(-431476996833470948490703909 : Int)/10^30)
theorem v802_mb_checked : Scalar.distance (sourceCoefficient 8 63 3 1) v802_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v802_mg : Scalar.QComplex := ((-93086322409365960744256 : Int)/10^30,(137729877730515999077 : Int)/10^30)
theorem v802_mg_checked : Scalar.distance (sourceCoefficient 8 63 3 2) v802_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v802_upper : Scalar.QComplex := ((999997256237888144472707893511 : Int)/10^30,(-2342544918561974582805865787 : Int)/10^30)
theorem v802_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 63 5) 1) 14) v802_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material802 : Material (8 : Basis) (63 : Basis) where
  plus := ![v802_pa,v802_pb,v802_pg]
  minus := ![(Primitive.Addresses.material802 1).one,v802_mb,v802_mg]
  upper := v802_upper
  lower := (Primitive.Addresses.material802 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v802_pa_checked.trans (by decide +kernel)
    · exact v802_pb_checked.trans (by decide +kernel)
    · exact v802_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 63 Primitive.Addresses.material802
    · exact v802_mb_checked.trans (by decide +kernel)
    · exact v802_mg_checked.trans (by decide +kernel)
  upper_error := v802_upper_checked
  lower_error := reuse_lower_error 8 63 Primitive.Addresses.material802

def v803_pa : Scalar.QComplex := ((999999787399629688386844545426 : Int)/10^30,(-652074148716469862075236684 : Int)/10^30)
theorem v803_pa_checked : Scalar.distance (sourceCoefficient 8 64 1 0) v803_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v803_pb : Scalar.QComplex := ((-281355300489739424230728 : Int)/10^30,(-431477372975623344406074695 : Int)/10^30)
theorem v803_pb_checked : Scalar.distance (sourceCoefficient 8 64 1 1) v803_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v803_pg : Scalar.QComplex := ((-93086404034502375584668 : Int)/10^30,(60699250572558651586 : Int)/10^30)
theorem v803_pg_checked : Scalar.distance (sourceCoefficient 8 64 1 2) v803_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v803_mb : Scalar.QComplex := ((-653700735586774196222908 : Int)/10^30,(-431476969519925345164575881 : Int)/10^30)
theorem v803_mb_checked : Scalar.distance (sourceCoefficient 8 64 3 1) v803_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v803_mg : Scalar.QComplex := ((-93086316993460443354921 : Int)/10^30,(141028602197222689242 : Int)/10^30)
theorem v803_mg_checked : Scalar.distance (sourceCoefficient 8 64 3 2) v803_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v803_upper : Scalar.QComplex := ((999997172596589603404822299805 : Int)/10^30,(-2377982091308331370021260883 : Int)/10^30)
theorem v803_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 64 5) 1) 14) v803_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material803 : Material (8 : Basis) (64 : Basis) where
  plus := ![v803_pa,v803_pb,v803_pg]
  minus := ![(Primitive.Addresses.material803 1).one,v803_mb,v803_mg]
  upper := v803_upper
  lower := (Primitive.Addresses.material803 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v803_pa_checked.trans (by decide +kernel)
    · exact v803_pb_checked.trans (by decide +kernel)
    · exact v803_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 64 Primitive.Addresses.material803
    · exact v803_mb_checked.trans (by decide +kernel)
    · exact v803_mg_checked.trans (by decide +kernel)
  upper_error := v803_upper_checked
  lower_error := reuse_lower_error 8 64 Primitive.Addresses.material803

def v804_pa : Scalar.QComplex := ((999999763299928609209477401849 : Int)/10^30,(-688040759515493565058722136 : Int)/10^30)
theorem v804_pa_checked : Scalar.distance (sourceCoefficient 8 65 1 0) v804_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v804_pb : Scalar.QComplex := ((-296874079318425736557153 : Int)/10^30,(-431477357907347704586780779 : Int)/10^30)
theorem v804_pb_checked : Scalar.distance (sourceCoefficient 8 65 1 1) v804_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v804_pg : Scalar.QComplex := ((-93086401287419168704725 : Int)/10^30,(64047253402349355565 : Int)/10^30)
theorem v804_pg_checked : Scalar.distance (sourceCoefficient 8 65 1 2) v804_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v804_mb : Scalar.QComplex := ((-669219495633866680177719 : Int)/10^30,(-431476941059648126649246457 : Int)/10^30)
theorem v804_mb_checked : Scalar.distance (sourceCoefficient 8 65 3 1) v804_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v804_mg : Scalar.QComplex := ((-93086311357202605680149 : Int)/10^30,(144376601409789844899 : Int)/10^30)
theorem v804_mg_checked : Scalar.distance (sourceCoefficient 8 65 3 2) v804_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v804_upper : Scalar.QComplex := ((999997086421817044229932820622 : Int)/10^30,(-2413948606945415467892150924 : Int)/10^30)
theorem v804_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 65 5) 1) 14) v804_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material804 : Material (8 : Basis) (65 : Basis) where
  plus := ![v804_pa,v804_pb,v804_pg]
  minus := ![(Primitive.Addresses.material804 1).one,v804_mb,v804_mg]
  upper := v804_upper
  lower := (Primitive.Addresses.material804 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v804_pa_checked.trans (by decide +kernel)
    · exact v804_pb_checked.trans (by decide +kernel)
    · exact v804_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 65 Primitive.Addresses.material804
    · exact v804_mb_checked.trans (by decide +kernel)
    · exact v804_mg_checked.trans (by decide +kernel)
  upper_error := v804_upper_checked
  lower_error := reuse_lower_error 8 65 Primitive.Addresses.material804

def v805_pa : Scalar.QComplex := ((999999751044304772012329648624 : Int)/10^30,(-705628321765104007685290541 : Int)/10^30)
theorem v805_pa_checked : Scalar.distance (sourceCoefficient 8 66 1 0) v805_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v805_pb : Scalar.QComplex := ((-304462714347040056341847 : Int)/10^30,(-431477350268071631380483988 : Int)/10^30)
theorem v805_pb_checked : Scalar.distance (sourceCoefficient 8 66 1 1) v805_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v805_pg : Scalar.QComplex := ((-93086399892959015247732 : Int)/10^30,(65684416488133599718 : Int)/10^30)
theorem v805_pg_checked : Scalar.distance (sourceCoefficient 8 66 1 2) v805_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v805_mb : Scalar.QComplex := ((-676808121244534170100536 : Int)/10^30,(-431476926871724647634645721 : Int)/10^30)
theorem v805_mb_checked : Scalar.distance (sourceCoefficient 8 66 3 1) v805_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v805_mg : Scalar.QComplex := ((-93086308549944963500808 : Int)/10^30,(146013762682627141886 : Int)/10^30)
theorem v805_mg_checked : Scalar.distance (sourceCoefficient 8 66 3 2) v805_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v805_upper : Scalar.QComplex := ((999997043811674548700898928589 : Int)/10^30,(-2431536121848322998420157600 : Int)/10^30)
theorem v805_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 66 5) 1) 14) v805_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material805 : Material (8 : Basis) (66 : Basis) where
  plus := ![v805_pa,v805_pb,v805_pg]
  minus := ![(Primitive.Addresses.material805 1).one,v805_mb,v805_mg]
  upper := v805_upper
  lower := (Primitive.Addresses.material805 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v805_pa_checked.trans (by decide +kernel)
    · exact v805_pb_checked.trans (by decide +kernel)
    · exact v805_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 66 Primitive.Addresses.material805
    · exact v805_mb_checked.trans (by decide +kernel)
    · exact v805_mg_checked.trans (by decide +kernel)
  upper_error := v805_upper_checked
  lower_error := reuse_lower_error 8 66 Primitive.Addresses.material805

def v806_pa : Scalar.QComplex := ((999999729780533119658649338989 : Int)/10^30,(-735145469102627619687875012 : Int)/10^30)
theorem v806_pa_checked : Scalar.distance (sourceCoefficient 8 67 1 0) v806_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v806_pb : Scalar.QComplex := ((-317198695063941862231281 : Int)/10^30,(-431477337047149908860466803 : Int)/10^30)
theorem v806_pb_checked : Scalar.distance (sourceCoefficient 8 67 1 1) v806_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v806_pg : Scalar.QComplex := ((-93086397477142012540539 : Int)/10^30,(68432061832082482775 : Int)/10^30)
theorem v806_pg_checked : Scalar.distance (sourceCoefficient 8 67 1 2) v806_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v806_mb : Scalar.QComplex := ((-689544085810188293689697 : Int)/10^30,(-431476902660230096459939511 : Int)/10^30)
theorem v806_mb_checked : Scalar.distance (sourceCoefficient 8 67 3 1) v806_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v806_mg : Scalar.QComplex := ((-93086303763034677837306 : Int)/10^30,(148761404918760820817 : Int)/10^30)
theorem v806_mg_checked : Scalar.distance (sourceCoefficient 8 67 3 2) v806_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v806_upper : Scalar.QComplex := ((999996971604016036360354601558 : Int)/10^30,(-2461053188524182141207133800 : Int)/10^30)
theorem v806_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 67 5) 1) 14) v806_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material806 : Material (8 : Basis) (67 : Basis) where
  plus := ![v806_pa,v806_pb,v806_pg]
  minus := ![(Primitive.Addresses.material806 1).one,v806_mb,v806_mg]
  upper := v806_upper
  lower := (Primitive.Addresses.material806 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v806_pa_checked.trans (by decide +kernel)
    · exact v806_pb_checked.trans (by decide +kernel)
    · exact v806_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 67 Primitive.Addresses.material806
    · exact v806_mb_checked.trans (by decide +kernel)
    · exact v806_mg_checked.trans (by decide +kernel)
  upper_error := v806_upper_checked
  lower_error := reuse_lower_error 8 67 Primitive.Addresses.material806

def v807_pa : Scalar.QComplex := ((999999692434011290064001266137 : Int)/10^30,(-784303437977314100685309750 : Int)/10^30)
theorem v807_pa_checked : Scalar.distance (sourceCoefficient 8 68 1 0) v807_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v807_pb : Scalar.QComplex := ((-338409244797086842962842 : Int)/10^30,(-431477313916481046031248311 : Int)/10^30)
theorem v807_pb_checked : Scalar.distance (sourceCoefficient 8 68 1 1) v807_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v807_pg : Scalar.QComplex := ((-93086393243823770495730 : Int)/10^30,(73008000704817127434 : Int)/10^30)
theorem v807_pg_checked : Scalar.distance (sourceCoefficient 8 68 1 2) v807_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v807_mb : Scalar.QComplex := ((-710754607684950776792497 : Int)/10^30,(-431476861225820714229778664 : Int)/10^30)
theorem v807_mb_checked : Scalar.distance (sourceCoefficient 8 68 3 1) v807_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v807_mg : Scalar.QComplex := ((-93086295580888857516663 : Int)/10^30,(153337338434501311111 : Int)/10^30)
theorem v807_mg_checked : Scalar.distance (sourceCoefficient 8 68 3 2) v807_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v807_upper : Scalar.QComplex := ((999996849415355128414089706324 : Int)/10^30,(-2510211019727139856133647259 : Int)/10^30)
theorem v807_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 68 5) 1) 14) v807_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material807 : Material (8 : Basis) (68 : Basis) where
  plus := ![v807_pa,v807_pb,v807_pg]
  minus := ![(Primitive.Addresses.material807 1).one,v807_mb,v807_mg]
  upper := v807_upper
  lower := (Primitive.Addresses.material807 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v807_pa_checked.trans (by decide +kernel)
    · exact v807_pb_checked.trans (by decide +kernel)
    · exact v807_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 68 Primitive.Addresses.material807
    · exact v807_mb_checked.trans (by decide +kernel)
    · exact v807_mg_checked.trans (by decide +kernel)
  upper_error := v807_upper_checked
  lower_error := reuse_lower_error 8 68 Primitive.Addresses.material807

def v808_pa : Scalar.QComplex := ((999999675231257352752239524239 : Int)/10^30,(-805938818906099919024038807 : Int)/10^30)
theorem v808_pa_checked : Scalar.distance (sourceCoefficient 8 69 1 0) v808_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v808_pb : Scalar.QComplex := ((-347744421139398170782068 : Int)/10^30,(-431477303295643224828298321 : Int)/10^30)
theorem v808_pb_checked : Scalar.distance (sourceCoefficient 8 69 1 1) v808_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v808_pg : Scalar.QComplex := ((-93086391297489040513995 : Int)/10^30,(75021960623317197863 : Int)/10^30)
theorem v808_pg_checked : Scalar.distance (sourceCoefficient 8 69 1 2) v808_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v808_mb : Scalar.QComplex := ((-720089771386044618814325 : Int)/10^30,(-431476842549150104970433851 : Int)/10^30)
theorem v808_mb_checked : Scalar.distance (sourceCoefficient 8 69 3 1) v808_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v808_mg : Scalar.QComplex := ((-93086291896598147966326 : Int)/10^30,(155351295923512849055 : Int)/10^30)
theorem v808_mg_checked : Scalar.distance (sourceCoefficient 8 69 3 2) v808_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v808_upper : Scalar.QComplex := ((999996794871922075924943482800 : Int)/10^30,(-2531846338742174577264536408 : Int)/10^30)
theorem v808_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 69 5) 1) 14) v808_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material808 : Material (8 : Basis) (69 : Basis) where
  plus := ![v808_pa,v808_pb,v808_pg]
  minus := ![(Primitive.Addresses.material808 1).one,v808_mb,v808_mg]
  upper := v808_upper
  lower := (Primitive.Addresses.material808 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v808_pa_checked.trans (by decide +kernel)
    · exact v808_pb_checked.trans (by decide +kernel)
    · exact v808_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 69 Primitive.Addresses.material808
    · exact v808_mb_checked.trans (by decide +kernel)
    · exact v808_mg_checked.trans (by decide +kernel)
  upper_error := v808_upper_checked
  lower_error := reuse_lower_error 8 69 Primitive.Addresses.material808

def v809_pa : Scalar.QComplex := ((999999663659888954250551196556 : Int)/10^30,(-820170780366399421840881184 : Int)/10^30)
theorem v809_pa_checked : Scalar.distance (sourceCoefficient 8 70 1 0) v809_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v809_pb : Scalar.QComplex := ((-353885189729616865570496 : Int)/10^30,(-431477296162318563231071323 : Int)/10^30)
theorem v809_pb_checked : Scalar.distance (sourceCoefficient 8 70 1 1) v809_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v809_pg : Scalar.QComplex := ((-93086389989453001443434 : Int)/10^30,(76346762797619336775 : Int)/10^30)
theorem v809_pg_checked : Scalar.distance (sourceCoefficient 8 70 1 2) v809_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v809_mb : Scalar.QComplex := ((-726230531534036610533654 : Int)/10^30,(-431476830116621376027798098 : Int)/10^30)
theorem v809_mb_checked : Scalar.distance (sourceCoefficient 8 70 3 1) v809_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v809_mg : Scalar.QComplex := ((-93086289445317986389608 : Int)/10^30,(156676096475754402062 : Int)/10^30)
theorem v809_mg_checked : Scalar.distance (sourceCoefficient 8 70 3 2) v809_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v809_upper : Scalar.QComplex := ((999996758737496544598327965473 : Int)/10^30,(-2546078259034507179123225575 : Int)/10^30)
theorem v809_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 70 5) 1) 14) v809_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material809 : Material (8 : Basis) (70 : Basis) where
  plus := ![v809_pa,v809_pb,v809_pg]
  minus := ![(Primitive.Addresses.material809 1).one,v809_mb,v809_mg]
  upper := v809_upper
  lower := (Primitive.Addresses.material809 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v809_pa_checked.trans (by decide +kernel)
    · exact v809_pb_checked.trans (by decide +kernel)
    · exact v809_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 70 Primitive.Addresses.material809
    · exact v809_mb_checked.trans (by decide +kernel)
    · exact v809_mg_checked.trans (by decide +kernel)
  upper_error := v809_upper_checked
  lower_error := reuse_lower_error 8 70 Primitive.Addresses.material809

def v810_pa : Scalar.QComplex := ((999999643440560316380616216056 : Int)/10^30,(-844463588458735584855578300 : Int)/10^30)
theorem v810_pa_checked : Scalar.distance (sourceCoefficient 8 71 1 0) v810_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v810_pb : Scalar.QComplex := ((-364366985264661497670466 : Int)/10^30,(-431477283717103748462982573 : Int)/10^30)
theorem v810_pb_checked : Scalar.distance (sourceCoefficient 8 71 1 1) v810_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v810_pg : Scalar.QComplex := ((-93086387705922759464526 : Int)/10^30,(78608093027262265213 : Int)/10^30)
theorem v810_pg_checked : Scalar.distance (sourceCoefficient 8 71 1 2) v810_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v810_mb : Scalar.QComplex := ((-736712312426569849738640 : Int)/10^30,(-431476808626093730984812340 : Int)/10^30)
theorem v810_mb_checked : Scalar.distance (sourceCoefficient 8 71 3 1) v810_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v810_mg : Scalar.QComplex := ((-93086285210362453024347 : Int)/10^30,(158937423892816985664 : Int)/10^30)
theorem v810_mg_checked : Scalar.distance (sourceCoefficient 8 71 3 2) v810_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v810_upper : Scalar.QComplex := ((999996696591015080005842703197 : Int)/10^30,(-2570370996048832376500453601 : Int)/10^30)
theorem v810_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 71 5) 1) 14) v810_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material810 : Material (8 : Basis) (71 : Basis) where
  plus := ![v810_pa,v810_pb,v810_pg]
  minus := ![(Primitive.Addresses.material810 1).one,v810_mb,v810_mg]
  upper := v810_upper
  lower := (Primitive.Addresses.material810 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v810_pa_checked.trans (by decide +kernel)
    · exact v810_pb_checked.trans (by decide +kernel)
    · exact v810_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 71 Primitive.Addresses.material810
    · exact v810_mb_checked.trans (by decide +kernel)
    · exact v810_mg_checked.trans (by decide +kernel)
  upper_error := v810_upper_checked
  lower_error := reuse_lower_error 8 71 Primitive.Addresses.material810

def v811_pa : Scalar.QComplex := ((999999620830788514826312746120 : Int)/10^30,(-870826204934748410111942820 : Int)/10^30)
theorem v811_pa_checked : Scalar.distance (sourceCoefficient 8 72 1 0) v811_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v811_pb : Scalar.QComplex := ((-375741855869137718478312 : Int)/10^30,(-431477269827392349152352405 : Int)/10^30)
theorem v811_pb_checked : Scalar.distance (sourceCoefficient 8 72 1 1) v811_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v811_pg : Scalar.QComplex := ((-93086385155316646813895 : Int)/10^30,(81062094252149055414 : Int)/10^30)
theorem v811_pg_checked : Scalar.distance (sourceCoefficient 8 72 1 2) v811_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v811_mb : Scalar.QComplex := ((-748087166809466519006018 : Int)/10^30,(-431476784920386476939913095 : Int)/10^30)
theorem v811_mb_checked : Scalar.distance (sourceCoefficient 8 72 3 1) v811_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v811_mg : Scalar.QComplex := ((-93086280542064757115961 : Int)/10^30,(161391422002908766260 : Int)/10^30)
theorem v811_mg_checked : Scalar.distance (sourceCoefficient 8 72 3 2) v811_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v811_upper : Scalar.QComplex := ((999996628481792513337137346088 : Int)/10^30,(-2596733534238409744195711459 : Int)/10^30)
theorem v811_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 72 5) 1) 14) v811_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material811 : Material (8 : Basis) (72 : Basis) where
  plus := ![v811_pa,v811_pb,v811_pg]
  minus := ![(Primitive.Addresses.material811 1).one,v811_mb,v811_mg]
  upper := v811_upper
  lower := (Primitive.Addresses.material811 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v811_pa_checked.trans (by decide +kernel)
    · exact v811_pb_checked.trans (by decide +kernel)
    · exact v811_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 72 Primitive.Addresses.material811
    · exact v811_mb_checked.trans (by decide +kernel)
    · exact v811_mg_checked.trans (by decide +kernel)
  upper_error := v811_upper_checked
  lower_error := reuse_lower_error 8 72 Primitive.Addresses.material811

def v812_pa : Scalar.QComplex := ((999999612557144229287805654954 : Int)/10^30,(-880275843942941501937854416 : Int)/10^30)
theorem v812_pa_checked : Scalar.distance (sourceCoefficient 8 73 1 0) v812_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v812_pb : Scalar.QComplex := ((-379819160529364385091508 : Int)/10^30,(-431477264751301749721389233 : Int)/10^30)
theorem v812_pb_checked : Scalar.distance (sourceCoefficient 8 73 1 1) v812_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v812_pg : Scalar.QComplex := ((-93086384222679864746257 : Int)/10^30,(81941727178953217606 : Int)/10^30)
theorem v812_pg_checked : Scalar.distance (sourceCoefficient 8 73 1 2) v812_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v812_mb : Scalar.QComplex := ((-752164465571088749913326 : Int)/10^30,(-431476776325767480778901140 : Int)/10^30)
theorem v812_mb_checked : Scalar.distance (sourceCoefficient 8 73 3 1) v812_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v812_mg : Scalar.QComplex := ((-93086278850344723675992 : Int)/10^30,(162271053797361850069 : Int)/10^30)
theorem v812_mg_checked : Scalar.distance (sourceCoefficient 8 73 3 2) v812_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v812_upper : Scalar.QComplex := ((999996603898940886832866620919 : Int)/10^30,(-2606183144892916108198368809 : Int)/10^30)
theorem v812_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 73 5) 1) 14) v812_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material812 : Material (8 : Basis) (73 : Basis) where
  plus := ![v812_pa,v812_pb,v812_pg]
  minus := ![(Primitive.Addresses.material812 1).one,v812_mb,v812_mg]
  upper := v812_upper
  lower := (Primitive.Addresses.material812 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v812_pa_checked.trans (by decide +kernel)
    · exact v812_pb_checked.trans (by decide +kernel)
    · exact v812_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 73 Primitive.Addresses.material812
    · exact v812_mb_checked.trans (by decide +kernel)
    · exact v812_mg_checked.trans (by decide +kernel)
  upper_error := v812_upper_checked
  lower_error := reuse_lower_error 8 73 Primitive.Addresses.material812

def v813_pa : Scalar.QComplex := ((999999603140488744546528457377 : Int)/10^30,(-890909010513102437309828135 : Int)/10^30)
theorem v813_pa_checked : Scalar.distance (sourceCoefficient 8 74 1 0) v813_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v813_pb : Scalar.QComplex := ((-384407130410644574246761 : Int)/10^30,(-431477258978025873979657527 : Int)/10^30)
theorem v813_pb_checked : Scalar.distance (sourceCoefficient 8 74 1 1) v813_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v813_pg : Scalar.QComplex := ((-93086383161638718736552 : Int)/10^30,(82931530426945703872 : Int)/10^30)
theorem v813_pg_checked : Scalar.distance (sourceCoefficient 8 74 1 2) v813_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v813_mb : Scalar.QComplex := ((-756752428761981009613940 : Int)/10^30,(-431476766593282381639646398 : Int)/10^30)
theorem v813_mb_checked : Scalar.distance (sourceCoefficient 8 74 3 1) v813_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v813_mg : Scalar.QComplex := ((-93086276935148348806318 : Int)/10^30,(163260855761174629378 : Int)/10^30)
theorem v813_mg_checked : Scalar.distance (sourceCoefficient 8 74 3 2) v813_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v813_upper : Scalar.QComplex := ((999996576130418560331944341772 : Int)/10^30,(-2616816279373931402451525992 : Int)/10^30)
theorem v813_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 74 5) 1) 14) v813_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material813 : Material (8 : Basis) (74 : Basis) where
  plus := ![v813_pa,v813_pb,v813_pg]
  minus := ![(Primitive.Addresses.material813 1).one,v813_mb,v813_mg]
  upper := v813_upper
  lower := (Primitive.Addresses.material813 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v813_pa_checked.trans (by decide +kernel)
    · exact v813_pb_checked.trans (by decide +kernel)
    · exact v813_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 74 Primitive.Addresses.material813
    · exact v813_mb_checked.trans (by decide +kernel)
    · exact v813_mg_checked.trans (by decide +kernel)
  upper_error := v813_upper_checked
  lower_error := reuse_lower_error 8 74 Primitive.Addresses.material813

def v814_pa : Scalar.QComplex := ((999999589831812900111695858108 : Int)/10^30,(-905724133476543121020996761 : Int)/10^30)
theorem v814_pa_checked : Scalar.distance (sourceCoefficient 8 75 1 0) v814_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v814_pb : Scalar.QComplex := ((-390799519412485072928205 : Int)/10^30,(-431477250825707169540059780 : Int)/10^30)
theorem v814_pb_checked : Scalar.distance (sourceCoefficient 8 75 1 1) v814_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v814_pg : Scalar.QComplex := ((-93086381662824542385321 : Int)/10^30,(84310616951561440120 : Int)/10^30)
theorem v814_pg_checked : Scalar.distance (sourceCoefficient 8 75 1 2) v814_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v814_mb : Scalar.QComplex := ((-763144808348559061173650 : Int)/10^30,(-431476752924622906605730561 : Int)/10^30)
theorem v814_mb_checked : Scalar.distance (sourceCoefficient 8 75 3 1) v814_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v814_mg : Scalar.QComplex := ((-93086274246245171540096 : Int)/10^30,(164639940478884295037 : Int)/10^30)
theorem v814_mg_checked : Scalar.distance (sourceCoefficient 8 75 3 2) v814_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v814_upper : Scalar.QComplex := ((999996537252204320164170190767 : Int)/10^30,(-2631631357302419584857709445 : Int)/10^30)
theorem v814_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 75 5) 1) 14) v814_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material814 : Material (8 : Basis) (75 : Basis) where
  plus := ![v814_pa,v814_pb,v814_pg]
  minus := ![(Primitive.Addresses.material814 1).one,v814_mb,v814_mg]
  upper := v814_upper
  lower := (Primitive.Addresses.material814 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v814_pa_checked.trans (by decide +kernel)
    · exact v814_pb_checked.trans (by decide +kernel)
    · exact v814_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 75 Primitive.Addresses.material814
    · exact v814_mb_checked.trans (by decide +kernel)
    · exact v814_mg_checked.trans (by decide +kernel)
  upper_error := v814_upper_checked
  lower_error := reuse_lower_error 8 75 Primitive.Addresses.material814

def v815_pa : Scalar.QComplex := ((999999578496239673586561441179 : Int)/10^30,(-918154313276045612136038472 : Int)/10^30)
theorem v815_pa_checked : Scalar.distance (sourceCoefficient 8 76 1 0) v815_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v815_pb : Scalar.QComplex := ((-396162859540669129820410 : Int)/10^30,(-431477243888333977527905848 : Int)/10^30)
theorem v815_pb_checked : Scalar.distance (sourceCoefficient 8 76 1 1) v815_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v815_pg : Scalar.QComplex := ((-93086380386900331937215 : Int)/10^30,(85467697684443195759 : Int)/10^30)
theorem v815_pg_checked : Scalar.distance (sourceCoefficient 8 76 1 2) v815_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v815_mb : Scalar.QComplex := ((-768508140493085854573535 : Int)/10^30,(-431476741358931322944226465 : Int)/10^30)
theorem v815_mb_checked : Scalar.distance (sourceCoefficient 8 76 3 1) v815_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v815_mg : Scalar.QComplex := ((-93086271971812876681615 : Int)/10^30,(165797019679866884498 : Int)/10^30)
theorem v815_mg_checked : Scalar.distance (sourceCoefficient 8 76 3 2) v815_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v815_upper : Scalar.QComplex := ((999996504463285299805124041120 : Int)/10^30,(-2644061499024458382290746613 : Int)/10^30)
theorem v815_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 76 5) 1) 14) v815_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material815 : Material (8 : Basis) (76 : Basis) where
  plus := ![v815_pa,v815_pb,v815_pg]
  minus := ![(Primitive.Addresses.material815 1).one,v815_mb,v815_mg]
  upper := v815_upper
  lower := (Primitive.Addresses.material815 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v815_pa_checked.trans (by decide +kernel)
    · exact v815_pb_checked.trans (by decide +kernel)
    · exact v815_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 76 Primitive.Addresses.material815
    · exact v815_mb_checked.trans (by decide +kernel)
    · exact v815_mg_checked.trans (by decide +kernel)
  upper_error := v815_upper_checked
  lower_error := reuse_lower_error 8 76 Primitive.Addresses.material815

def v816_pa : Scalar.QComplex := ((999999575849932478738135666226 : Int)/10^30,(-921032005491255417956522517 : Int)/10^30)
theorem v816_pa_checked : Scalar.distance (sourceCoefficient 8 77 1 0) v816_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v816_pb : Scalar.QComplex := ((-397404518330560822589720 : Int)/10^30,(-431477242269601702318604604 : Int)/10^30)
theorem v816_pb_checked : Scalar.distance (sourceCoefficient 8 77 1 1) v816_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v816_pg : Scalar.QComplex := ((-93086380089121030104972 : Int)/10^30,(85735571702152936044 : Int)/10^30)
theorem v816_pg_checked : Scalar.distance (sourceCoefficient 8 77 1 2) v816_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v816_mb : Scalar.QComplex := ((-769749797423758184745818 : Int)/10^30,(-431476738668704037022365884 : Int)/10^30)
theorem v816_mb_checked : Scalar.distance (sourceCoefficient 8 77 3 1) v816_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v816_mg : Scalar.QComplex := ((-93086271442870473040609 : Int)/10^30,(166064893340864759543 : Int)/10^30)
theorem v816_mg_checked : Scalar.distance (sourceCoefficient 8 77 3 2) v816_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v816_upper : Scalar.QComplex := ((999996496850346345066740920179 : Int)/10^30,(-2646939182386397523834661947 : Int)/10^30)
theorem v816_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 77 5) 1) 14) v816_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material816 : Material (8 : Basis) (77 : Basis) where
  plus := ![v816_pa,v816_pb,v816_pg]
  minus := ![(Primitive.Addresses.material816 1).one,v816_mb,v816_mg]
  upper := v816_upper
  lower := (Primitive.Addresses.material816 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v816_pa_checked.trans (by decide +kernel)
    · exact v816_pb_checked.trans (by decide +kernel)
    · exact v816_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 77 Primitive.Addresses.material816
    · exact v816_mb_checked.trans (by decide +kernel)
    · exact v816_mg_checked.trans (by decide +kernel)
  upper_error := v816_upper_checked
  lower_error := reuse_lower_error 8 77 Primitive.Addresses.material816

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
