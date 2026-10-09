import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B006

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v145_pa : Scalar.QComplex := ((999973655925519917084334773004 : Int)/10^30,(7258612467262983669592393384 : Int)/10^30)
theorem v145_pa_checked : Scalar.distance (sourceCoefficient 1 50 1 0) v145_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v145_pb : Scalar.QComplex := ((3131891157467860677315868 : Int)/10^30,(-431461062953655770266286145 : Int)/10^30)
theorem v145_pb_checked : Scalar.distance (sourceCoefficient 1 50 1 1) v145_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v145_pg : Scalar.QComplex := ((-93083428438999683201563 : Int)/10^30,(-675674334177888733819 : Int)/10^30)
theorem v145_pg_checked : Scalar.distance (sourceCoefficient 1 50 1 2) v145_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v145_mb : Scalar.QComplex := ((2759558526277558434177006 : Int)/10^30,(-431463604981997041161904078 : Int)/10^30)
theorem v145_mb_checked : Scalar.distance (sourceCoefficient 1 50 3 1) v145_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v145_mg : Scalar.QComplex := ((-93083976856304305691808 : Int)/10^30,(-595347276172588135198 : Int)/10^30)
theorem v145_mg_checked : Scalar.distance (sourceCoefficient 1 50 3 2) v145_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v145_upper : Scalar.QComplex := ((999984694288846889894247333544 : Int)/10^30,(5532737843186346839099193921 : Int)/10^30)
theorem v145_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 50 5) 1) 14) v145_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material145 : Material (1 : Basis) (50 : Basis) where
  plus := ![v145_pa,v145_pb,v145_pg]
  minus := ![(Primitive.Addresses.material145 1).one,v145_mb,v145_mg]
  upper := v145_upper
  lower := (Primitive.Addresses.material145 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v145_pa_checked.trans (by decide +kernel)
    · exact v145_pb_checked.trans (by decide +kernel)
    · exact v145_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 50 Primitive.Addresses.material145
    · exact v145_mb_checked.trans (by decide +kernel)
    · exact v145_mg_checked.trans (by decide +kernel)
  upper_error := v145_upper_checked
  lower_error := reuse_lower_error 1 50 Primitive.Addresses.material145

def v146_pa : Scalar.QComplex := ((999973737878565697534162441085 : Int)/10^30,(7247313513956927034501581145 : Int)/10^30)
theorem v146_pa_checked : Scalar.distance (sourceCoefficient 1 51 1 0) v146_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v146_pb : Scalar.QComplex := ((3127015871465626968087025 : Int)/10^30,(-431461084631320650088381467 : Int)/10^30)
theorem v146_pb_checked : Scalar.distance (sourceCoefficient 1 51 1 1) v146_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v146_pg : Scalar.QComplex := ((-93083434591710819148654 : Int)/10^30,(-674622550461374047878 : Int)/10^30)
theorem v146_pg_checked : Scalar.distance (sourceCoefficient 1 51 1 2) v146_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v146_mb : Scalar.QComplex := ((2754683223383768049653993 : Int)/10^30,(-431463622452501604201498818 : Int)/10^30)
theorem v146_mb_checked : Scalar.distance (sourceCoefficient 1 51 3 1) v146_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v146_mg : Scalar.QComplex := ((-93083982101371173931289 : Int)/10^30,(-594295487538187993306 : Int)/10^30)
theorem v146_mg_checked : Scalar.distance (sourceCoefficient 1 51 3 2) v146_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v146_upper : Scalar.QComplex := ((999984756740802237692320655935 : Int)/10^30,(5521438765265231590268834916 : Int)/10^30)
theorem v146_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 51 5) 1) 14) v146_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material146 : Material (1 : Basis) (51 : Basis) where
  plus := ![v146_pa,v146_pb,v146_pg]
  minus := ![(Primitive.Addresses.material146 1).one,v146_mb,v146_mg]
  upper := v146_upper
  lower := (Primitive.Addresses.material146 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v146_pa_checked.trans (by decide +kernel)
    · exact v146_pb_checked.trans (by decide +kernel)
    · exact v146_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 51 Primitive.Addresses.material146
    · exact v146_mb_checked.trans (by decide +kernel)
    · exact v146_mg_checked.trans (by decide +kernel)
  upper_error := v146_upper_checked
  lower_error := reuse_lower_error 1 51 Primitive.Addresses.material146

def v147_pa : Scalar.QComplex := ((999973912890795729665818761936 : Int)/10^30,(7223125214979595854997751209 : Int)/10^30)
theorem v147_pa_checked : Scalar.distance (sourceCoefficient 1 52 1 0) v147_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v147_pb : Scalar.QComplex := ((3116579075638598105832278 : Int)/10^30,(-431461130790976018447036477 : Int)/10^30)
theorem v147_pb_checked : Scalar.distance (sourceCoefficient 1 52 1 1) v147_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v147_pg : Scalar.QComplex := ((-93083447716548824399903 : Int)/10^30,(-672370938512737457653 : Int)/10^30)
theorem v147_pg_checked : Scalar.distance (sourceCoefficient 1 52 1 2) v147_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v147_mb : Scalar.QComplex := ((2744246391609131629744813 : Int)/10^30,(-431463659605655042319708177 : Int)/10^30)
theorem v147_mb_checked : Scalar.distance (sourceCoefficient 1 52 3 1) v147_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v147_mg : Scalar.QComplex := ((-93083993283164589369831 : Int)/10^30,(-592043865101785357537 : Int)/10^30)
theorem v147_mg_checked : Scalar.distance (sourceCoefficient 1 52 3 2) v147_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v147_upper : Scalar.QComplex := ((999984890005961920134047339658 : Int)/10^30,(5497250200258298330332534768 : Int)/10^30)
theorem v147_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 52 5) 1) 14) v147_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material147 : Material (1 : Basis) (52 : Basis) where
  plus := ![v147_pa,v147_pb,v147_pg]
  minus := ![(Primitive.Addresses.material147 1).one,v147_mb,v147_mg]
  upper := v147_upper
  lower := (Primitive.Addresses.material147 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v147_pa_checked.trans (by decide +kernel)
    · exact v147_pb_checked.trans (by decide +kernel)
    · exact v147_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 52 Primitive.Addresses.material147
    · exact v147_mb_checked.trans (by decide +kernel)
    · exact v147_mg_checked.trans (by decide +kernel)
  upper_error := v147_upper_checked
  lower_error := reuse_lower_error 1 52 Primitive.Addresses.material147

def v148_pa : Scalar.QComplex := ((999973939628933571602918219033 : Int)/10^30,(7219422621644799804122450784 : Int)/10^30)
theorem v148_pa_checked : Scalar.distance (sourceCoefficient 1 53 1 0) v148_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v148_pb : Scalar.QComplex := ((3114981476362707000334574 : Int)/10^30,(-431461137827099633384352751 : Int)/10^30)
theorem v148_pb_checked : Scalar.distance (sourceCoefficient 1 53 1 1) v148_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v148_pg : Scalar.QComplex := ((-93083449720008898926564 : Int)/10^30,(-672026275863483943743 : Int)/10^30)
theorem v148_pg_checked : Scalar.distance (sourceCoefficient 1 53 1 2) v148_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v148_mb : Scalar.QComplex := ((2742648786856241964108244 : Int)/10^30,(-431463665263119815492969616 : Int)/10^30)
theorem v148_mb_checked : Scalar.distance (sourceCoefficient 1 53 3 1) v148_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v148_mg : Scalar.QComplex := ((-93083994989195574640441 : Int)/10^30,(-591699200851969687981 : Int)/10^30)
theorem v148_mg_checked : Scalar.distance (sourceCoefficient 1 53 3 2) v148_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v148_upper : Scalar.QComplex := ((999984910353719739541181839972 : Int)/10^30,(5493547566290479864203509860 : Int)/10^30)
theorem v148_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 53 5) 1) 14) v148_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material148 : Material (1 : Basis) (53 : Basis) where
  plus := ![v148_pa,v148_pb,v148_pg]
  minus := ![(Primitive.Addresses.material148 1).one,v148_mb,v148_mg]
  upper := v148_upper
  lower := (Primitive.Addresses.material148 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v148_pa_checked.trans (by decide +kernel)
    · exact v148_pb_checked.trans (by decide +kernel)
    · exact v148_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 53 Primitive.Addresses.material148
    · exact v148_mb_checked.trans (by decide +kernel)
    · exact v148_mg_checked.trans (by decide +kernel)
  upper_error := v148_upper_checked
  lower_error := reuse_lower_error 1 53 Primitive.Addresses.material148

def v149_pa : Scalar.QComplex := ((999973953217508285857295661421 : Int)/10^30,(7217540200688189775638457595 : Int)/10^30)
theorem v149_pa_checked : Scalar.distance (sourceCoefficient 1 54 1 0) v149_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v149_pb : Scalar.QComplex := ((3114169247187597317262541 : Int)/10^30,(-431461141401283264157342070 : Int)/10^30)
theorem v149_pb_checked : Scalar.distance (sourceCoefficient 1 54 1 1) v149_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v149_pg : Scalar.QComplex := ((-93083450738009257828585 : Int)/10^30,(-671851047278455857724 : Int)/10^30)
theorem v149_pg_checked : Scalar.distance (sourceCoefficient 1 54 1 2) v149_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v149_mb : Scalar.QComplex := ((2741836554899202825534606 : Int)/10^30,(-431463668136384918758468350 : Int)/10^30)
theorem v149_mb_checked : Scalar.distance (sourceCoefficient 1 54 3 1) v149_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v149_mg : Scalar.QComplex := ((-93083995855981177617670 : Int)/10^30,(-591523971453698751811 : Int)/10^30)
theorem v149_mg_checked : Scalar.distance (sourceCoefficient 1 54 3 2) v149_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v149_upper : Scalar.QComplex := ((999984920693386415996026175982 : Int)/10^30,(5491665124684867514956767230 : Int)/10^30)
theorem v149_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 54 5) 1) 14) v149_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material149 : Material (1 : Basis) (54 : Basis) where
  plus := ![v149_pa,v149_pb,v149_pg]
  minus := ![(Primitive.Addresses.material149 1).one,v149_mb,v149_mg]
  upper := v149_upper
  lower := (Primitive.Addresses.material149 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v149_pa_checked.trans (by decide +kernel)
    · exact v149_pb_checked.trans (by decide +kernel)
    · exact v149_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 54 Primitive.Addresses.material149
    · exact v149_mb_checked.trans (by decide +kernel)
    · exact v149_mg_checked.trans (by decide +kernel)
  upper_error := v149_upper_checked
  lower_error := reuse_lower_error 1 54 Primitive.Addresses.material149

def v150_pa : Scalar.QComplex := ((999974063842819549233647060724 : Int)/10^30,(7202197003460280498163174900 : Int)/10^30)
theorem v150_pa_checked : Scalar.distance (sourceCoefficient 1 55 1 0) v150_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v150_pb : Scalar.QComplex := ((3107548946857368324931188 : Int)/10^30,(-431461170457633971152352184 : Int)/10^30)
theorem v150_pb_checked : Scalar.distance (sourceCoefficient 1 55 1 1) v150_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v150_pg : Scalar.QComplex := ((-93083459021152796966131 : Int)/10^30,(-670422797824926233657 : Int)/10^30)
theorem v150_pg_checked : Scalar.distance (sourceCoefficient 1 55 1 2) v150_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v150_mb : Scalar.QComplex := ((2735216231959692198139295 : Int)/10^30,(-431463691479703789016933642 : Int)/10^30)
theorem v150_mb_checked : Scalar.distance (sourceCoefficient 1 55 3 1) v150_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v150_mg : Scalar.QComplex := ((-93084002906606680133748 : Int)/10^30,(-590095715383991858178 : Int)/10^30)
theorem v150_mg_checked : Scalar.distance (sourceCoefficient 1 55 3 2) v150_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v150_upper : Scalar.QComplex := ((999985004837566424574202262687 : Int)/10^30,(5476321759379596779153059316 : Int)/10^30)
theorem v150_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 55 5) 1) 14) v150_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material150 : Material (1 : Basis) (55 : Basis) where
  plus := ![v150_pa,v150_pb,v150_pg]
  minus := ![(Primitive.Addresses.material150 1).one,v150_mb,v150_mg]
  upper := v150_upper
  lower := (Primitive.Addresses.material150 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v150_pa_checked.trans (by decide +kernel)
    · exact v150_pb_checked.trans (by decide +kernel)
    · exact v150_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 55 Primitive.Addresses.material150
    · exact v150_mb_checked.trans (by decide +kernel)
    · exact v150_mg_checked.trans (by decide +kernel)
  upper_error := v150_upper_checked
  lower_error := reuse_lower_error 1 55 Primitive.Addresses.material150

def v151_pa : Scalar.QComplex := ((999974090062730157235212824822 : Int)/10^30,(7198555633933532529478679542 : Int)/10^30)
theorem v151_pa_checked : Scalar.distance (sourceCoefficient 1 56 1 0) v151_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v151_pb : Scalar.QComplex := ((3105977764607650267612405 : Int)/10^30,(-431461177333631466384580219 : Int)/10^30)
theorem v151_pb_checked : Scalar.distance (sourceCoefficient 1 56 1 1) v151_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v151_pg : Scalar.QComplex := ((-93083460983220214449269 : Int)/10^30,(-670083834316904718701 : Int)/10^30)
theorem v151_pg_checked : Scalar.distance (sourceCoefficient 1 56 1 2) v151_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v151_mb : Scalar.QComplex := ((2733645044361320944012458 : Int)/10^30,(-431463696999839205916027739 : Int)/10^30)
theorem v151_mb_checked : Scalar.distance (sourceCoefficient 1 56 3 1) v151_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v151_mg : Scalar.QComplex := ((-93084004576163125976635 : Int)/10^30,(-589756750309006135605 : Int)/10^30)
theorem v151_mg_checked : Scalar.distance (sourceCoefficient 1 56 3 2) v151_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v151_upper : Scalar.QComplex := ((999985024772764520394903386043 : Int)/10^30,(5472680350023053917546230093 : Int)/10^30)
theorem v151_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 56 5) 1) 14) v151_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material151 : Material (1 : Basis) (56 : Basis) where
  plus := ![v151_pa,v151_pb,v151_pg]
  minus := ![(Primitive.Addresses.material151 1).one,v151_mb,v151_mg]
  upper := v151_upper
  lower := (Primitive.Addresses.material151 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v151_pa_checked.trans (by decide +kernel)
    · exact v151_pb_checked.trans (by decide +kernel)
    · exact v151_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 56 Primitive.Addresses.material151
    · exact v151_mb_checked.trans (by decide +kernel)
    · exact v151_mg_checked.trans (by decide +kernel)
  upper_error := v151_upper_checked
  lower_error := reuse_lower_error 1 56 Primitive.Addresses.material151

def v152_pa : Scalar.QComplex := ((999974174776927216141949700485 : Int)/10^30,(7186778082243875509220458432 : Int)/10^30)
theorem v152_pa_checked : Scalar.distance (sourceCoefficient 1 57 1 0) v152_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v152_pb : Scalar.QComplex := ((3100895973385983578274846 : Int)/10^30,(-431461199520940288896131851 : Int)/10^30)
theorem v152_pb_checked : Scalar.distance (sourceCoefficient 1 57 1 1) v152_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v152_pg : Scalar.QComplex := ((-93083467319418960933624 : Int)/10^30,(-668987499501871799125 : Int)/10^30)
theorem v152_pg_checked : Scalar.distance (sourceCoefficient 1 57 1 2) v152_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v152_mb : Scalar.QComplex := ((2728563235885189141300493 : Int)/10^30,(-431463714801782818160512124 : Int)/10^30)
theorem v152_mb_checked : Scalar.distance (sourceCoefficient 1 57 3 1) v152_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v152_mg : Scalar.QComplex := ((-93084009966271944918314 : Int)/10^30,(-588660410434334626224 : Int)/10^30)
theorem v152_mg_checked : Scalar.distance (sourceCoefficient 1 57 3 2) v152_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v152_upper : Scalar.QComplex := ((999985089159849642251336062935 : Int)/10^30,(5460902669665657738876488779 : Int)/10^30)
theorem v152_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 57 5) 1) 14) v152_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material152 : Material (1 : Basis) (57 : Basis) where
  plus := ![v152_pa,v152_pb,v152_pg]
  minus := ![(Primitive.Addresses.material152 1).one,v152_mb,v152_mg]
  upper := v152_upper
  lower := (Primitive.Addresses.material152 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v152_pa_checked.trans (by decide +kernel)
    · exact v152_pb_checked.trans (by decide +kernel)
    · exact v152_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 57 Primitive.Addresses.material152
    · exact v152_mb_checked.trans (by decide +kernel)
    · exact v152_mg_checked.trans (by decide +kernel)
  upper_error := v152_upper_checked
  lower_error := reuse_lower_error 1 57 Primitive.Addresses.material152

def v153_pa : Scalar.QComplex := ((999974220683974935564964349258 : Int)/10^30,(7180387696844380695304282203 : Int)/10^30)
theorem v153_pa_checked : Scalar.distance (sourceCoefficient 1 58 1 0) v153_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v153_pb : Scalar.QComplex := ((3098138642803175592264486 : Int)/10^30,(-431461211526160437450988868 : Int)/10^30)
theorem v153_pb_checked : Scalar.distance (sourceCoefficient 1 58 1 1) v153_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v153_pg : Scalar.QComplex := ((-93083470751074254042019 : Int)/10^30,(-668392638865653482706 : Int)/10^30)
theorem v153_pg_checked : Scalar.distance (sourceCoefficient 1 58 1 2) v153_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v153_mb : Scalar.QComplex := ((2725805895969097054343614 : Int)/10^30,(-431463724427546389219415251 : Int)/10^30)
theorem v153_mb_checked : Scalar.distance (sourceCoefficient 1 58 3 1) v153_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v153_mg : Scalar.QComplex := ((-93084012884588022736709 : Int)/10^30,(-588065547058246149208 : Int)/10^30)
theorem v153_mg_checked : Scalar.distance (sourceCoefficient 1 58 3 2) v153_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v153_upper : Scalar.QComplex := ((999985124037603520226174733829 : Int)/10^30,(5454512214552491601219788905 : Int)/10^30)
theorem v153_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 58 5) 1) 14) v153_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material153 : Material (1 : Basis) (58 : Basis) where
  plus := ![v153_pa,v153_pb,v153_pg]
  minus := ![(Primitive.Addresses.material153 1).one,v153_mb,v153_mg]
  upper := v153_upper
  lower := (Primitive.Addresses.material153 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v153_pa_checked.trans (by decide +kernel)
    · exact v153_pb_checked.trans (by decide +kernel)
    · exact v153_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 58 Primitive.Addresses.material153
    · exact v153_mb_checked.trans (by decide +kernel)
    · exact v153_mg_checked.trans (by decide +kernel)
  upper_error := v153_upper_checked
  lower_error := reuse_lower_error 1 58 Primitive.Addresses.material153

def v154_pa : Scalar.QComplex := ((999974346659864286985949605339 : Int)/10^30,(7162822221552473342984702201 : Int)/10^30)
theorem v154_pa_checked : Scalar.distance (sourceCoefficient 1 59 1 0) v154_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v154_pb : Scalar.QComplex := ((3090559472330993550218701 : Int)/10^30,(-431461244404277300775849632 : Int)/10^30)
theorem v154_pb_checked : Scalar.distance (sourceCoefficient 1 59 1 1) v154_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v154_pg : Scalar.QComplex := ((-93083480160933845841456 : Int)/10^30,(-666757524713745276349 : Int)/10^30)
theorem v154_pg_checked : Scalar.distance (sourceCoefficient 1 59 1 2) v154_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v154_mb : Scalar.QComplex := ((2718226699946652486658760 : Int)/10^30,(-431463750765168246192103250 : Int)/10^30)
theorem v154_mb_checked : Scalar.distance (sourceCoefficient 1 59 3 1) v154_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v154_mg : Scalar.QComplex := ((-93084020883414240526239 : Int)/10^30,(-586430425394880646635 : Int)/10^30)
theorem v154_mg_checked : Scalar.distance (sourceCoefficient 1 59 3 2) v154_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v154_upper : Scalar.QComplex := ((999985219696888418996576781439 : Int)/10^30,(5436946547999339733378724424 : Int)/10^30)
theorem v154_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 59 5) 1) 14) v154_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material154 : Material (1 : Basis) (59 : Basis) where
  plus := ![v154_pa,v154_pb,v154_pg]
  minus := ![(Primitive.Addresses.material154 1).one,v154_mb,v154_mg]
  upper := v154_upper
  lower := (Primitive.Addresses.material154 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v154_pa_checked.trans (by decide +kernel)
    · exact v154_pb_checked.trans (by decide +kernel)
    · exact v154_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 59 Primitive.Addresses.material154
    · exact v154_mb_checked.trans (by decide +kernel)
    · exact v154_mg_checked.trans (by decide +kernel)
  upper_error := v154_upper_checked
  lower_error := reuse_lower_error 1 59 Primitive.Addresses.material154

def v155_pa : Scalar.QComplex := ((999974491601485643465561389984 : Int)/10^30,(7142558809720666321716203077 : Int)/10^30)
theorem v155_pa_checked : Scalar.distance (sourceCoefficient 1 60 1 0) v155_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v155_pb : Scalar.QComplex := ((3081816193796172650096424 : Int)/10^30,(-431461282111735943391649179 : Int)/10^30)
theorem v155_pb_checked : Scalar.distance (sourceCoefficient 1 60 1 1) v155_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v155_pg : Scalar.QComplex := ((-93083490974456811080892 : Int)/10^30,(-664871268300433180143 : Int)/10^30)
theorem v155_pg_checked : Scalar.distance (sourceCoefficient 1 60 1 2) v155_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v155_mb : Scalar.QComplex := ((2709483392127515244936051 : Int)/10^30,(-431463780927557255694606696 : Int)/10^30)
theorem v155_mb_checked : Scalar.distance (sourceCoefficient 1 60 3 1) v155_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v155_mg : Scalar.QComplex := ((-93084030069178848543754 : Int)/10^30,(-584544160352324723276 : Int)/10^30)
theorem v155_mg_checked : Scalar.distance (sourceCoefficient 1 60 3 2) v155_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v155_upper : Scalar.QComplex := ((999985329665483362619806010443 : Int)/10^30,(5416682916191414867916822503 : Int)/10^30)
theorem v155_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 60 5) 1) 14) v155_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material155 : Material (1 : Basis) (60 : Basis) where
  plus := ![v155_pa,v155_pb,v155_pg]
  minus := ![(Primitive.Addresses.material155 1).one,v155_mb,v155_mg]
  upper := v155_upper
  lower := (Primitive.Addresses.material155 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v155_pa_checked.trans (by decide +kernel)
    · exact v155_pb_checked.trans (by decide +kernel)
    · exact v155_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 60 Primitive.Addresses.material155
    · exact v155_mb_checked.trans (by decide +kernel)
    · exact v155_mg_checked.trans (by decide +kernel)
  upper_error := v155_upper_checked
  lower_error := reuse_lower_error 1 60 Primitive.Addresses.material155

def v156_pa : Scalar.QComplex := ((999974533434969184835494853418 : Int)/10^30,(7136699623474134999424488005 : Int)/10^30)
theorem v156_pa_checked : Scalar.distance (sourceCoefficient 1 61 1 0) v156_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v156_pb : Scalar.QComplex := ((3079288065978553495401179 : Int)/10^30,(-431461292970856164562055189 : Int)/10^30)
theorem v156_pb_checked : Scalar.distance (sourceCoefficient 1 61 1 1) v156_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v156_pg : Scalar.QComplex := ((-93083494092886374924999 : Int)/10^30,(-664325855341955779152 : Int)/10^30)
theorem v156_pg_checked : Scalar.distance (sourceCoefficient 1 61 1 2) v156_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v156_mb : Scalar.QComplex := ((2706955255880301943638855 : Int)/10^30,(-431463789605012989563062864 : Int)/10^30)
theorem v156_mb_checked : Scalar.distance (sourceCoefficient 1 61 3 1) v156_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v156_mg : Scalar.QComplex := ((-93084032716940432575792 : Int)/10^30,(-583998744905865228586 : Int)/10^30)
theorem v156_mg_checked : Scalar.distance (sourceCoefficient 1 61 3 2) v156_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v156_upper : Scalar.QComplex := ((999985361386480677641161645078 : Int)/10^30,(5410823666470655703045421308 : Int)/10^30)
theorem v156_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 61 5) 1) 14) v156_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material156 : Material (1 : Basis) (61 : Basis) where
  plus := ![v156_pa,v156_pb,v156_pg]
  minus := ![(Primitive.Addresses.material156 1).one,v156_mb,v156_mg]
  upper := v156_upper
  lower := (Primitive.Addresses.material156 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v156_pa_checked.trans (by decide +kernel)
    · exact v156_pb_checked.trans (by decide +kernel)
    · exact v156_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 61 Primitive.Addresses.material156
    · exact v156_mb_checked.trans (by decide +kernel)
    · exact v156_mg_checked.trans (by decide +kernel)
  upper_error := v156_upper_checked
  lower_error := reuse_lower_error 1 61 Primitive.Addresses.material156

def v157_pa : Scalar.QComplex := ((999974594156047680332217153346 : Int)/10^30,(7128186476778817123305630058 : Int)/10^30)
theorem v157_pa_checked : Scalar.distance (sourceCoefficient 1 62 1 0) v157_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v157_pb : Scalar.QComplex := ((3075614804614610868446564 : Int)/10^30,(-431461308713495268305947792 : Int)/10^30)
theorem v157_pb_checked : Scalar.distance (sourceCoefficient 1 62 1 1) v157_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v157_pg : Scalar.QComplex := ((-93083498617186653968375 : Int)/10^30,(-663533393680146621504 : Int)/10^30)
theorem v157_pg_checked : Scalar.distance (sourceCoefficient 1 62 1 2) v157_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v157_mb : Scalar.QComplex := ((2703281982298893874431785 : Int)/10^30,(-431463802177787112070957357 : Int)/10^30)
theorem v157_mb_checked : Scalar.distance (sourceCoefficient 1 62 3 1) v157_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v157_mg : Scalar.QComplex := ((-93084036557380304022430 : Int)/10^30,(-583206279634858391022 : Int)/10^30)
theorem v157_mg_checked : Scalar.distance (sourceCoefficient 1 62 3 2) v157_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v157_upper : Scalar.QComplex := ((999985407414549846740880533755 : Int)/10^30,(5402310427655596895126977304 : Int)/10^30)
theorem v157_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 62 5) 1) 14) v157_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material157 : Material (1 : Basis) (62 : Basis) where
  plus := ![v157_pa,v157_pb,v157_pg]
  minus := ![(Primitive.Addresses.material157 1).one,v157_mb,v157_mg]
  upper := v157_upper
  lower := (Primitive.Addresses.material157 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v157_pa_checked.trans (by decide +kernel)
    · exact v157_pb_checked.trans (by decide +kernel)
    · exact v157_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 62 Primitive.Addresses.material157
    · exact v157_mb_checked.trans (by decide +kernel)
    · exact v157_mg_checked.trans (by decide +kernel)
  upper_error := v157_upper_checked
  lower_error := reuse_lower_error 1 62 Primitive.Addresses.material157

def v158_pa : Scalar.QComplex := ((999974770593277913500272667769 : Int)/10^30,(7103391930705319809849496632 : Int)/10^30)
theorem v158_pa_checked : Scalar.distance (sourceCoefficient 1 63 1 0) v158_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v158_pb : Scalar.QComplex := ((3064916428756284680055518 : Int)/10^30,(-431461354326371252685108878 : Int)/10^30)
theorem v158_pb_checked : Scalar.distance (sourceCoefficient 1 63 1 1) v158_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v158_pg : Scalar.QComplex := ((-93083511749367474951089 : Int)/10^30,(-661225348565424659493 : Int)/10^30)
theorem v158_pg_checked : Scalar.distance (sourceCoefficient 1 63 1 2) v158_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v158_mb : Scalar.QComplex := ((2692583571062204311181319 : Int)/10^30,(-431463838558429583918307675 : Int)/10^30)
theorem v158_mb_checked : Scalar.distance (sourceCoefficient 1 63 3 1) v158_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v158_mg : Scalar.QComplex := ((-93084047697817251782144 : Int)/10^30,(-580898224047046511055 : Int)/10^30)
theorem v158_mg_checked : Scalar.distance (sourceCoefficient 1 63 3 2) v158_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v158_upper : Scalar.QComplex := ((999985541058380118172793042816 : Int)/10^30,(5377515613996010264210920678 : Int)/10^30)
theorem v158_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 63 5) 1) 14) v158_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material158 : Material (1 : Basis) (63 : Basis) where
  plus := ![v158_pa,v158_pb,v158_pg]
  minus := ![(Primitive.Addresses.material158 1).one,v158_mb,v158_mg]
  upper := v158_upper
  lower := (Primitive.Addresses.material158 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v158_pa_checked.trans (by decide +kernel)
    · exact v158_pb_checked.trans (by decide +kernel)
    · exact v158_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 63 Primitive.Addresses.material158
    · exact v158_mb_checked.trans (by decide +kernel)
    · exact v158_mg_checked.trans (by decide +kernel)
  upper_error := v158_upper_checked
  lower_error := reuse_lower_error 1 63 Primitive.Addresses.material158

def v159_pa : Scalar.QComplex := ((999975021690221705780455181881 : Int)/10^30,(7067955548857750043413073839 : Int)/10^30)
theorem v159_pa_checked : Scalar.distance (sourceCoefficient 1 64 1 0) v159_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v159_pb : Scalar.QComplex := ((3049626304359307723075601 : Int)/10^30,(-431461418902331125826892739 : Int)/10^30)
theorem v159_pb_checked : Scalar.distance (sourceCoefficient 1 64 1 1) v159_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v159_pg : Scalar.QComplex := ((-93083530401984037366711 : Int)/10^30,(-657926689108624112043 : Int)/10^30)
theorem v159_pg_checked : Scalar.distance (sourceCoefficient 1 64 1 2) v159_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v159_mb : Scalar.QComplex := ((2677293396632294483148644 : Int)/10^30,(-431463889939676699527110296 : Int)/10^30)
theorem v159_mb_checked : Scalar.distance (sourceCoefficient 1 64 3 1) v159_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v159_mg : Scalar.QComplex := ((-93084063503832323864182 : Int)/10^30,(-577599549722119624857 : Int)/10^30)
theorem v159_mg_checked : Scalar.distance (sourceCoefficient 1 64 3 2) v159_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v159_upper : Scalar.QComplex := ((999985730994969625594556671792 : Int)/10^30,(5342078851556222961230474699 : Int)/10^30)
theorem v159_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 64 5) 1) 14) v159_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material159 : Material (1 : Basis) (64 : Basis) where
  plus := ![v159_pa,v159_pb,v159_pg]
  minus := ![(Primitive.Addresses.material159 1).one,v159_mb,v159_mg]
  upper := v159_upper
  lower := (Primitive.Addresses.material159 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v159_pa_checked.trans (by decide +kernel)
    · exact v159_pb_checked.trans (by decide +kernel)
    · exact v159_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 64 Primitive.Addresses.material159
    · exact v159_mb_checked.trans (by decide +kernel)
    · exact v159_mg_checked.trans (by decide +kernel)
  upper_error := v159_upper_checked
  lower_error := reuse_lower_error 1 64 Primitive.Addresses.material159

def v160_pa : Scalar.QComplex := ((999975275253902421932042981663 : Int)/10^30,(7031989823804251368900873040 : Int)/10^30)
theorem v160_pa_checked : Scalar.distance (sourceCoefficient 1 65 1 0) v160_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v160_pb : Scalar.QComplex := ((3034107780315726384492057 : Int)/10^30,(-431461483704172576855723959 : Int)/10^30)
theorem v160_pb_checked : Scalar.distance (sourceCoefficient 1 65 1 1) v160_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v160_pg : Scalar.QComplex := ((-93083549193775853592169 : Int)/10^30,(-654578754987732169706 : Int)/10^30)
theorem v160_pg_checked : Scalar.distance (sourceCoefficient 1 65 1 2) v160_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v160_mb : Scalar.QComplex := ((2661774822445898271934764 : Int)/10^30,(-431463941349706700635565596 : Int)/10^30)
theorem v160_mb_checked : Scalar.distance (sourceCoefficient 1 65 3 1) v160_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v160_mg : Scalar.QComplex := ((-93084079406500782072363 : Int)/10^30,(-574251600631346577359 : Int)/10^30)
theorem v160_mg_checked : Scalar.distance (sourceCoefficient 1 65 3 2) v160_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v160_upper : Scalar.QComplex := ((999985922484694031180062816070 : Int)/10^30,(5306112742441537124408022175 : Int)/10^30)
theorem v160_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 65 5) 1) 14) v160_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material160 : Material (1 : Basis) (65 : Basis) where
  plus := ![v160_pa,v160_pb,v160_pg]
  minus := ![(Primitive.Addresses.material160 1).one,v160_mb,v160_mg]
  upper := v160_upper
  lower := (Primitive.Addresses.material160 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v160_pa_checked.trans (by decide +kernel)
    · exact v160_pb_checked.trans (by decide +kernel)
    · exact v160_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 65 Primitive.Addresses.material160
    · exact v160_mb_checked.trans (by decide +kernel)
    · exact v160_mg_checked.trans (by decide +kernel)
  upper_error := v160_upper_checked
  lower_error := reuse_lower_error 1 65 Primitive.Addresses.material160

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
