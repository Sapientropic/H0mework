import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B010
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B011

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v257_pa : Scalar.QComplex := ((999987335901964193826262378334 : Int)/10^30,(5032696662052391864329381391 : Int)/10^30)
theorem v257_pa_checked : Scalar.distance (sourceCoefficient 2 67 1 0) v257_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v257_pb : Scalar.QComplex := ((2171479059779617890123272 : Int)/10^30,(-431468794121674541389922258 : Int)/10^30)
theorem v257_pb_checked : Scalar.distance (sourceCoefficient 2 67 1 1) v257_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v257_pg : Scalar.QComplex := ((-93084899105805494675967 : Int)/10^30,(-468473993817855924265 : Int)/10^30)
theorem v257_pg_checked : Scalar.distance (sourceCoefficient 2 67 1 2) v257_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v257_mb : Scalar.QComplex := ((1799140114544831299875488 : Int)/10^30,(-431470507354752195312410400 : Int)/10^30)
theorem v257_mb_checked : Scalar.distance (sourceCoefficient 2 67 3 1) v257_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v257_mg : Scalar.QComplex := ((-93085268718000746904592 : Int)/10^30,(-388145743843494523864 : Int)/10^30)
theorem v257_mg_checked : Scalar.distance (sourceCoefficient 2 67 3 2) v257_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v257_upper : Scalar.QComplex := ((999994532516170159634619416771 : Int)/10^30,(3306801742817567403868348184 : Int)/10^30)
theorem v257_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 67 5) 1) 14) v257_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material257 : Material (2 : Basis) (67 : Basis) where
  plus := ![v257_pa,v257_pb,v257_pg]
  minus := ![(Primitive.Addresses.material257 1).one,v257_mb,v257_mg]
  upper := v257_upper
  lower := (Primitive.Addresses.material257 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v257_pa_checked.trans (by decide +kernel)
    · exact v257_pb_checked.trans (by decide +kernel)
    · exact v257_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 67 Primitive.Addresses.material257
    · exact v257_mb_checked.trans (by decide +kernel)
    · exact v257_mg_checked.trans (by decide +kernel)
  upper_error := v257_upper_checked
  lower_error := reuse_lower_error 2 67 Primitive.Addresses.material257

def v258_pa : Scalar.QComplex := ((999987582090943036652958558255 : Int)/10^30,(4983539295466761649698458696 : Int)/10^30)
theorem v258_pa_checked : Scalar.distance (sourceCoefficient 2 68 1 0) v258_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v258_pb : Scalar.QComplex := ((2150268683295447474128415 : Int)/10^30,(-431468852550323306225769022 : Int)/10^30)
theorem v258_pb_checked : Scalar.distance (sourceCoefficient 2 68 1 1) v258_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v258_pg : Scalar.QComplex := ((-93084916866886673150604 : Int)/10^30,(-463898101665824673464 : Int)/10^30)
theorem v258_pg_checked : Scalar.distance (sourceCoefficient 2 68 1 2) v258_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v258_mb : Scalar.QComplex := ((1777929695536961055630159 : Int)/10^30,(-431470547479779578548122283 : Int)/10^30)
theorem v258_mb_checked : Scalar.distance (sourceCoefficient 2 68 3 1) v258_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v258_mg : Scalar.QComplex := ((-93085282530286475446102 : Int)/10^30,(-383569838068263922245 : Int)/10^30)
theorem v258_mg_checked : Scalar.distance (sourceCoefficient 2 68 3 2) v258_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v258_upper : Scalar.QComplex := ((999994693863627127559746142474 : Int)/10^30,(3257644024546216895600313823 : Int)/10^30)
theorem v258_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 68 5) 1) 14) v258_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material258 : Material (2 : Basis) (68 : Basis) where
  plus := ![v258_pa,v258_pb,v258_pg]
  minus := ![(Primitive.Addresses.material258 1).one,v258_mb,v258_mg]
  upper := v258_upper
  lower := (Primitive.Addresses.material258 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v258_pa_checked.trans (by decide +kernel)
    · exact v258_pb_checked.trans (by decide +kernel)
    · exact v258_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 68 Primitive.Addresses.material258
    · exact v258_mb_checked.trans (by decide +kernel)
    · exact v258_mg_checked.trans (by decide +kernel)
  upper_error := v258_upper_checked
  lower_error := reuse_lower_error 2 68 Primitive.Addresses.material258

def v259_pa : Scalar.QComplex := ((999987689677706048867050169805 : Int)/10^30,(4961904175200009336570493484 : Int)/10^30)
theorem v259_pa_checked : Scalar.distance (sourceCoefficient 2 69 1 0) v259_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v259_pb : Scalar.QComplex := ((2140933581932794331047947 : Int)/10^30,(-431468877825334664208974107 : Int)/10^30)
theorem v259_pb_checked : Scalar.distance (sourceCoefficient 2 69 1 1) v259_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v259_pg : Scalar.QComplex := ((-93084924600716957431230 : Int)/10^30,(-461884161967371822959 : Int)/10^30)
theorem v259_pg_checked : Scalar.distance (sourceCoefficient 2 69 1 2) v259_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v259_mb : Scalar.QComplex := ((1768594575838996327388668 : Int)/10^30,(-431470564699009486877816767 : Int)/10^30)
theorem v259_mb_checked : Scalar.distance (sourceCoefficient 2 69 3 1) v259_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v259_mg : Scalar.QComplex := ((-93085288526174624780361 : Int)/10^30,(-381555892445745646516 : Int)/10^30)
theorem v259_mg_checked : Scalar.distance (sourceCoefficient 2 69 3 2) v259_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v259_upper : Scalar.QComplex := ((999994764109975044292518374515 : Int)/10^30,(3236008750817442015863468201 : Int)/10^30)
theorem v259_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 69 5) 1) 14) v259_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material259 : Material (2 : Basis) (69 : Basis) where
  plus := ![v259_pa,v259_pb,v259_pg]
  minus := ![(Primitive.Addresses.material259 1).one,v259_mb,v259_mg]
  upper := v259_upper
  lower := (Primitive.Addresses.material259 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v259_pa_checked.trans (by decide +kernel)
    · exact v259_pb_checked.trans (by decide +kernel)
    · exact v259_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 69 Primitive.Addresses.material259
    · exact v259_mb_checked.trans (by decide +kernel)
    · exact v259_mg_checked.trans (by decide +kernel)
  upper_error := v259_upper_checked
  lower_error := reuse_lower_error 2 69 Primitive.Addresses.material259

def v260_pa : Scalar.QComplex := ((999987760194085195683356923626 : Int)/10^30,(4947672383733567418774665952 : Int)/10^30)
theorem v260_pa_checked : Scalar.distance (sourceCoefficient 2 70 1 0) v260_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v260_pb : Scalar.QComplex := ((2134792862241453653486994 : Int)/10^30,(-431468894304645390145110430 : Int)/10^30)
theorem v260_pb_checked : Scalar.distance (sourceCoefficient 2 70 1 1) v260_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v260_pg : Scalar.QComplex := ((-93084929660386753023066 : Int)/10^30,(-460559372979814695512 : Int)/10^30)
theorem v260_pg_checked : Scalar.distance (sourceCoefficient 2 70 1 2) v260_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v260_mb : Scalar.QComplex := ((1762453844213223279788305 : Int)/10^30,(-431470575879149550934643963 : Int)/10^30)
theorem v260_mb_checked : Scalar.distance (sourceCoefficient 2 70 3 1) v260_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v260_mg : Scalar.QComplex := ((-93085292442609306445175 : Int)/10^30,(-380231099585200850458 : Int)/10^30)
theorem v260_mg_checked : Scalar.distance (sourceCoefficient 2 70 3 2) v260_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v260_upper : Scalar.QComplex := ((999994810063468192203102831278 : Int)/10^30,(3221776858842708492209933249 : Int)/10^30)
theorem v260_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 70 5) 1) 14) v260_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material260 : Material (2 : Basis) (70 : Basis) where
  plus := ![v260_pa,v260_pb,v260_pg]
  minus := ![(Primitive.Addresses.material260 1).one,v260_mb,v260_mg]
  upper := v260_upper
  lower := (Primitive.Addresses.material260 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v260_pa_checked.trans (by decide +kernel)
    · exact v260_pb_checked.trans (by decide +kernel)
    · exact v260_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 70 Primitive.Addresses.material260
    · exact v260_mb_checked.trans (by decide +kernel)
    · exact v260_mg_checked.trans (by decide +kernel)
  upper_error := v260_upper_checked
  lower_error := reuse_lower_error 2 70 Primitive.Addresses.material260

def v261_pa : Scalar.QComplex := ((999987880091915685233005956902 : Int)/10^30,(4923379863108021624394960789 : Int)/10^30)
theorem v261_pa_checked : Scalar.distance (sourceCoefficient 2 71 1 0) v261_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v261_pb : Scalar.QComplex := ((2124311149396473772540764 : Int)/10^30,(-431468922164292612977972490 : Int)/10^30)
theorem v261_pb_checked : Scalar.distance (sourceCoefficient 2 71 1 1) v261_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v261_pg : Scalar.QComplex := ((-93084938246016285386935 : Int)/10^30,(-458298065049513925099 : Int)/10^30)
theorem v261_pg_checked : Scalar.distance (sourceCoefficient 2 71 1 2) v261_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v261_mb : Scalar.QComplex := ((1751972111229443327597630 : Int)/10^30,(-431470594693540293952107203 : Int)/10^30)
theorem v261_mb_checked : Scalar.distance (sourceCoefficient 2 71 3 1) v261_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v261_mg : Scalar.QComplex := ((-93085299076828743665719 : Int)/10^30,(-377969785087876765343 : Int)/10^30)
theorem v261_mg_checked : Scalar.distance (sourceCoefficient 2 71 3 2) v261_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v261_upper : Scalar.QComplex := ((999994888034433308582391764453 : Int)/10^30,(3197484167465240190906045931 : Int)/10^30)
theorem v261_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 71 5) 1) 14) v261_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material261 : Material (2 : Basis) (71 : Basis) where
  plus := ![v261_pa,v261_pb,v261_pg]
  minus := ![(Primitive.Addresses.material261 1).one,v261_mb,v261_mg]
  upper := v261_upper
  lower := (Primitive.Addresses.material261 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v261_pa_checked.trans (by decide +kernel)
    · exact v261_pb_checked.trans (by decide +kernel)
    · exact v261_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 71 Primitive.Addresses.material261
    · exact v261_mb_checked.trans (by decide +kernel)
    · exact v261_mg_checked.trans (by decide +kernel)
  upper_error := v261_upper_checked
  lower_error := reuse_lower_error 2 71 Primitive.Addresses.material261

def v262_pa : Scalar.QComplex := ((999988009537648688083640083082 : Int)/10^30,(4897017554740480455177431294 : Int)/10^30)
theorem v262_pa_checked : Scalar.distance (sourceCoefficient 2 72 1 0) v262_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v262_pb : Scalar.QComplex := ((2112936367419655763306646 : Int)/10^30,(-431468952013521243379205797 : Int)/10^30)
theorem v262_pb_checked : Scalar.distance (sourceCoefficient 2 72 1 1) v262_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v262_pg : Scalar.QComplex := ((-93084947490650432239003 : Int)/10^30,(-455844087725182938773 : Int)/10^30)
theorem v262_pg_checked : Scalar.distance (sourceCoefficient 2 72 1 2) v262_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v262_mb : Scalar.QComplex := ((1740597307729436552866752 : Int)/10^30,(-431470614726833265290125099 : Int)/10^30)
theorem v262_mb_checked : Scalar.distance (sourceCoefficient 2 72 3 1) v262_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v262_mg : Scalar.QComplex := ((-93085306203787540456232 : Int)/10^30,(-375515800699570783302 : Int)/10^30)
theorem v262_mg_checked : Scalar.distance (sourceCoefficient 2 72 3 2) v262_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v262_upper : Scalar.QComplex := ((999994971981020844776608270831 : Int)/10^30,(3171121674949668663111301704 : Int)/10^30)
theorem v262_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 72 5) 1) 14) v262_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material262 : Material (2 : Basis) (72 : Basis) where
  plus := ![v262_pa,v262_pb,v262_pg]
  minus := ![(Primitive.Addresses.material262 1).one,v262_mb,v262_mg]
  upper := v262_upper
  lower := (Primitive.Addresses.material262 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v262_pa_checked.trans (by decide +kernel)
    · exact v262_pb_checked.trans (by decide +kernel)
    · exact v262_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 72 Primitive.Addresses.material262
    · exact v262_mb_checked.trans (by decide +kernel)
    · exact v262_mg_checked.trans (by decide +kernel)
  upper_error := v262_upper_checked
  lower_error := reuse_lower_error 2 72 Primitive.Addresses.material262

def v263_pa : Scalar.QComplex := ((999988055768067196073999632000 : Int)/10^30,(4887568025197336052697417357 : Int)/10^30)
theorem v263_pa_checked : Scalar.distance (sourceCoefficient 2 73 1 0) v263_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v263_pb : Scalar.QComplex := ((2108859094247140514190707 : Int)/10^30,(-431468962615586479041754459 : Int)/10^30)
theorem v263_pb_checked : Scalar.distance (sourceCoefficient 2 73 1 1) v263_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v263_pg : Scalar.QComplex := ((-93084950785999418231591 : Int)/10^30,(-454964463289789107870 : Int)/10^30)
theorem v263_pg_checked : Scalar.distance (sourceCoefficient 2 73 1 2) v263_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v263_mb : Scalar.QComplex := ((1736520026925971647383464 : Int)/10^30,(-431470621810391439005479876 : Int)/10^30)
theorem v263_mb_checked : Scalar.distance (sourceCoefficient 2 73 3 1) v263_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v263_mg : Scalar.QComplex := ((-93085308740059028508837 : Int)/10^30,(-374636173747963572616 : Int)/10^30)
theorem v263_mg_checked : Scalar.distance (sourceCoefficient 2 73 3 2) v263_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v263_upper : Scalar.QComplex := ((999995001902339761145616358556 : Int)/10^30,(3161672079690980141444131449 : Int)/10^30)
theorem v263_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 73 5) 1) 14) v263_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material263 : Material (2 : Basis) (73 : Basis) where
  plus := ![v263_pa,v263_pb,v263_pg]
  minus := ![(Primitive.Addresses.material263 1).one,v263_mb,v263_mg]
  upper := v263_upper
  lower := (Primitive.Addresses.material263 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v263_pa_checked.trans (by decide +kernel)
    · exact v263_pb_checked.trans (by decide +kernel)
    · exact v263_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 73 Primitive.Addresses.material263
    · exact v263_mb_checked.trans (by decide +kernel)
    · exact v263_mg_checked.trans (by decide +kernel)
  upper_error := v263_upper_checked
  lower_error := reuse_lower_error 2 73 Primitive.Addresses.material263

def v264_pa : Scalar.QComplex := ((999988107681881024995374861475 : Int)/10^30,(4876934981186417903369013222 : Int)/10^30)
theorem v264_pa_checked : Scalar.distance (sourceCoefficient 2 74 1 0) v264_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v264_pb : Scalar.QComplex := ((2104271159620126883165317 : Int)/10^30,(-431468974484089919138122663 : Int)/10^30)
theorem v264_pb_checked : Scalar.distance (sourceCoefficient 2 74 1 1) v264_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v264_pg : Scalar.QComplex := ((-93084954482481599243290 : Int)/10^30,(-453974669548948197735 : Int)/10^30)
theorem v264_pg_checked : Scalar.distance (sourceCoefficient 2 74 1 2) v264_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v264_mb : Scalar.QComplex := ((1731932083765271825714864 : Int)/10^30,(-431470629719709509707863055 : Int)/10^30)
theorem v264_mb_checked : Scalar.distance (sourceCoefficient 2 74 3 1) v264_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v264_mg : Scalar.QComplex := ((-93085311582392413460827 : Int)/10^30,(-373646377185770469169 : Int)/10^30)
theorem v264_mg_checked : Scalar.distance (sourceCoefficient 2 74 3 2) v264_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v264_upper : Scalar.QComplex := ((999995035464406929912247870337 : Int)/10^30,(3151038961918198916971167906 : Int)/10^30)
theorem v264_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 74 5) 1) 14) v264_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material264 : Material (2 : Basis) (74 : Basis) where
  plus := ![v264_pa,v264_pb,v264_pg]
  minus := ![(Primitive.Addresses.material264 1).one,v264_mb,v264_mg]
  upper := v264_upper
  lower := (Primitive.Addresses.material264 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v264_pa_checked.trans (by decide +kernel)
    · exact v264_pb_checked.trans (by decide +kernel)
    · exact v264_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 74 Primitive.Addresses.material264
    · exact v264_mb_checked.trans (by decide +kernel)
    · exact v264_mg_checked.trans (by decide +kernel)
  upper_error := v264_upper_checked
  lower_error := reuse_lower_error 2 74 Primitive.Addresses.material264

def v265_pa : Scalar.QComplex := ((999988179824558889204611234902 : Int)/10^30,(4862120027896692323566510682 : Int)/10^30)
theorem v265_pa_checked : Scalar.distance (sourceCoefficient 2 75 1 0) v265_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v265_pb : Scalar.QComplex := ((2097878819425068471081216 : Int)/10^30,(-431468990911950134868626624 : Int)/10^30)
theorem v265_pb_checked : Scalar.distance (sourceCoefficient 2 75 1 1) v265_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v265_pg : Scalar.QComplex := ((-93084959612294443937346 : Int)/10^30,(-452595596186242335533 : Int)/10^30)
theorem v265_pg_checked : Scalar.distance (sourceCoefficient 2 75 1 2) v265_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v265_mb : Scalar.QComplex := ((1725539731773870329813079 : Int)/10^30,(-431470640631261920574832143 : Int)/10^30)
theorem v265_mb_checked : Scalar.distance (sourceCoefficient 2 75 3 1) v265_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v265_mg : Scalar.QComplex := ((-93085315522125147234538 : Int)/10^30,(-372267299909759199891 : Int)/10^30)
theorem v265_mg_checked : Scalar.distance (sourceCoefficient 2 75 3 2) v265_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v265_upper : Scalar.QComplex := ((999995082037711970074604944923 : Int)/10^30,(3136223906181888714539088492 : Int)/10^30)
theorem v265_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 75 5) 1) 14) v265_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material265 : Material (2 : Basis) (75 : Basis) where
  plus := ![v265_pa,v265_pb,v265_pg]
  minus := ![(Primitive.Addresses.material265 1).one,v265_mb,v265_mg]
  upper := v265_upper
  lower := (Primitive.Addresses.material265 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v265_pa_checked.trans (by decide +kernel)
    · exact v265_pb_checked.trans (by decide +kernel)
    · exact v265_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 75 Primitive.Addresses.material265
    · exact v265_mb_checked.trans (by decide +kernel)
    · exact v265_mg_checked.trans (by decide +kernel)
  upper_error := v265_upper_checked
  lower_error := reuse_lower_error 2 75 Primitive.Addresses.material265

def v266_pa : Scalar.QComplex := ((999988240184356336281208518218 : Int)/10^30,(4849689989480097131401234485 : Int)/10^30)
theorem v266_pa_checked : Scalar.distance (sourceCoefficient 2 76 1 0) v266_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v266_pb : Scalar.QComplex := ((2092515519965791720115848 : Int)/10^30,(-431469004597831497777767703 : Int)/10^30)
theorem v266_pb_checked : Scalar.distance (sourceCoefficient 2 76 1 1) v266_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v266_pg : Scalar.QComplex := ((-93084963897918969475306 : Int)/10^30,(-451438526420699022975 : Int)/10^30)
theorem v266_pg_checked : Scalar.distance (sourceCoefficient 2 76 1 2) v266_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v266_mb : Scalar.QComplex := ((1720176422501295855455210 : Int)/10^30,(-431470649688852308289768390 : Int)/10^30)
theorem v266_mb_checked : Scalar.distance (sourceCoefficient 2 76 3 1) v266_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v266_mg : Scalar.QComplex := ((-93085318809248981862480 : Int)/10^30,(-371110226876744893570 : Int)/10^30)
theorem v266_mg_checked : Scalar.distance (sourceCoefficient 2 76 3 2) v266_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v266_upper : Scalar.QComplex := ((999995120944300855556442842943 : Int)/10^30,(3123793782102841013406661516 : Int)/10^30)
theorem v266_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 76 5) 1) 14) v266_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material266 : Material (2 : Basis) (76 : Basis) where
  plus := ![v266_pa,v266_pb,v266_pg]
  minus := ![(Primitive.Addresses.material266 1).one,v266_mb,v266_mg]
  upper := v266_upper
  lower := (Primitive.Addresses.material266 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v266_pa_checked.trans (by decide +kernel)
    · exact v266_pb_checked.trans (by decide +kernel)
    · exact v266_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 76 Primitive.Addresses.material266
    · exact v266_mb_checked.trans (by decide +kernel)
    · exact v266_mg_checked.trans (by decide +kernel)
  upper_error := v266_upper_checked
  lower_error := reuse_lower_error 2 76 Primitive.Addresses.material266

def v267_pa : Scalar.QComplex := ((999988254136136855047145279592 : Int)/10^30,(4846812329869190857957970544 : Int)/10^30)
theorem v267_pa_checked : Scalar.distance (sourceCoefficient 2 77 1 0) v267_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v267_pb : Scalar.QComplex := ((2091273870554554113316254 : Int)/10^30,(-431469007753557917936792805 : Int)/10^30)
theorem v267_pb_checked : Scalar.distance (sourceCoefficient 2 77 1 1) v267_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v267_pg : Scalar.QComplex := ((-93084964887685467801787 : Int)/10^30,(-451170654932166505285 : Int)/10^30)
theorem v267_pg_checked : Scalar.distance (sourceCoefficient 2 77 1 2) v267_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v267_mb : Scalar.QComplex := ((1718934770829131298685451 : Int)/10^30,(-431470651773090033343135619 : Int)/10^30)
theorem v267_mb_checked : Scalar.distance (sourceCoefficient 2 77 3 1) v267_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v267_mg : Scalar.QComplex := ((-93085319567854081534086 : Int)/10^30,(-370842354633829262766 : Int)/10^30)
theorem v267_mg_checked : Scalar.distance (sourceCoefficient 2 77 3 2) v267_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v267_upper : Scalar.QComplex := ((999995129929481165600578746925 : Int)/10^30,(3120916102698363217016410313 : Int)/10^30)
theorem v267_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 77 5) 1) 14) v267_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material267 : Material (2 : Basis) (77 : Basis) where
  plus := ![v267_pa,v267_pb,v267_pg]
  minus := ![(Primitive.Addresses.material267 1).one,v267_mb,v267_mg]
  upper := v267_upper
  lower := (Primitive.Addresses.material267 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v267_pa_checked.trans (by decide +kernel)
    · exact v267_pb_checked.trans (by decide +kernel)
    · exact v267_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 77 Primitive.Addresses.material267
    · exact v267_mb_checked.trans (by decide +kernel)
    · exact v267_mg_checked.trans (by decide +kernel)
  upper_error := v267_upper_checked
  lower_error := reuse_lower_error 2 77 Primitive.Addresses.material267

def v268_pa : Scalar.QComplex := ((999988337834363206917449856091 : Int)/10^30,(4829512943090516773036320139 : Int)/10^30)
theorem v268_pa_checked : Scalar.distance (sourceCoefficient 2 78 1 0) v268_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v268_pb : Scalar.QComplex := ((2083809550356217911586721 : Int)/10^30,(-431469026624167997825055040 : Int)/10^30)
theorem v268_pb_checked : Scalar.distance (sourceCoefficient 2 78 1 1) v268_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v268_pg : Scalar.QComplex := ((-93084970818828156258342 : Int)/10^30,(-449560314223581844076 : Int)/10^30)
theorem v268_pg_checked : Scalar.distance (sourceCoefficient 2 78 1 2) v268_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v268_mb : Scalar.QComplex := ((1711470437125616044866653 : Int)/10^30,(-431470664202320936178819749 : Int)/10^30)
theorem v268_mb_checked : Scalar.distance (sourceCoefficient 2 78 3 1) v268_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v268_mg : Scalar.QComplex := ((-93085324109343057099772 : Int)/10^30,(-369232009406539032181 : Int)/10^30)
theorem v268_mg_checked : Scalar.distance (sourceCoefficient 2 78 3 2) v268_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v268_upper : Scalar.QComplex := ((999995183770410666912320136890 : Int)/10^30,(3103616597229547970662422491 : Int)/10^30)
theorem v268_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 78 5) 1) 14) v268_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material268 : Material (2 : Basis) (78 : Basis) where
  plus := ![v268_pa,v268_pb,v268_pg]
  minus := ![(Primitive.Addresses.material268 1).one,v268_mb,v268_mg]
  upper := v268_upper
  lower := (Primitive.Addresses.material268 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v268_pa_checked.trans (by decide +kernel)
    · exact v268_pb_checked.trans (by decide +kernel)
    · exact v268_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 78 Primitive.Addresses.material268
    · exact v268_mb_checked.trans (by decide +kernel)
    · exact v268_mg_checked.trans (by decide +kernel)
  upper_error := v268_upper_checked
  lower_error := reuse_lower_error 2 78 Primitive.Addresses.material268

def v269_pa : Scalar.QComplex := ((999988364753396683309059686183 : Int)/10^30,(4823935926986371352879026806 : Int)/10^30)
theorem v269_pa_checked : Scalar.distance (sourceCoefficient 2 79 1 0) v269_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v269_pb : Scalar.QComplex := ((2081403185723129207466635 : Int)/10^30,(-431469032671018461700599227 : Int)/10^30)
theorem v269_pb_checked : Scalar.distance (sourceCoefficient 2 79 1 1) v269_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v269_pg : Scalar.QComplex := ((-93084972723995600771566 : Int)/10^30,(-449041168890563894596 : Int)/10^30)
theorem v269_pg_checked : Scalar.distance (sourceCoefficient 2 79 1 2) v269_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v269_mb : Scalar.QComplex := ((1709064068170367259652725 : Int)/10^30,(-431470668172584848819899952 : Int)/10^30)
theorem v269_mb_checked : Scalar.distance (sourceCoefficient 2 79 3 1) v269_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v269_mg : Scalar.QComplex := ((-93085325566510751275435 : Int)/10^30,(-368712862622748917239 : Int)/10^30)
theorem v269_mg_checked : Scalar.distance (sourceCoefficient 2 79 3 2) v269_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v269_upper : Scalar.QComplex := ((999995201063980197759462137681 : Int)/10^30,(3098039542971903210686917429 : Int)/10^30)
theorem v269_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 79 5) 1) 14) v269_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material269 : Material (2 : Basis) (79 : Basis) where
  plus := ![v269_pa,v269_pb,v269_pg]
  minus := ![(Primitive.Addresses.material269 1).one,v269_mb,v269_mg]
  upper := v269_upper
  lower := (Primitive.Addresses.material269 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v269_pa_checked.trans (by decide +kernel)
    · exact v269_pb_checked.trans (by decide +kernel)
    · exact v269_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 79 Primitive.Addresses.material269
    · exact v269_mb_checked.trans (by decide +kernel)
    · exact v269_mg_checked.trans (by decide +kernel)
  upper_error := v269_upper_checked
  lower_error := reuse_lower_error 2 79 Primitive.Addresses.material269

def v270_pa : Scalar.QComplex := ((999988406741345733472141713287 : Int)/10^30,(4815224076290409871960501918 : Int)/10^30)
theorem v270_pa_checked : Scalar.distance (sourceCoefficient 2 80 1 0) v270_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v270_pb : Scalar.QComplex := ((2077644206269009704873347 : Int)/10^30,(-431469042080988303461002456 : Int)/10^30)
theorem v270_pb_checked : Scalar.distance (sourceCoefficient 2 80 1 1) v270_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v270_pg : Scalar.QComplex := ((-93084975693295897975599 : Int)/10^30,(-448230212548056722081 : Int)/10^30)
theorem v270_pg_checked : Scalar.distance (sourceCoefficient 2 80 1 2) v270_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v270_mb : Scalar.QComplex := ((1705305081995507437545873 : Int)/10^30,(-431470674338721216063314291 : Int)/10^30)
theorem v270_mb_checked : Scalar.distance (sourceCoefficient 2 80 3 1) v270_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v270_mg : Scalar.QComplex := ((-93085327835991143407401 : Int)/10^30,(-367901904019825429408 : Int)/10^30)
theorem v270_mg_checked : Scalar.distance (sourceCoefficient 2 80 3 2) v270_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v270_upper : Scalar.QComplex := ((999995228016002743496564497300 : Int)/10^30,(3089327632783829031933901464 : Int)/10^30)
theorem v270_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 80 5) 1) 14) v270_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material270 : Material (2 : Basis) (80 : Basis) where
  plus := ![v270_pa,v270_pb,v270_pg]
  minus := ![(Primitive.Addresses.material270 1).one,v270_mb,v270_mg]
  upper := v270_upper
  lower := (Primitive.Addresses.material270 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v270_pa_checked.trans (by decide +kernel)
    · exact v270_pb_checked.trans (by decide +kernel)
    · exact v270_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 80 Primitive.Addresses.material270
    · exact v270_mb_checked.trans (by decide +kernel)
    · exact v270_mg_checked.trans (by decide +kernel)
  upper_error := v270_upper_checked
  lower_error := reuse_lower_error 2 80 Primitive.Addresses.material270

def v271_pa : Scalar.QComplex := ((999988532710916514125985062645 : Int)/10^30,(4788992239318500273359578835 : Int)/10^30)
theorem v271_pa_checked : Scalar.distance (sourceCoefficient 2 81 1 0) v271_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v271_pb : Scalar.QComplex := ((2066325723614570514207195 : Int)/10^30,(-431469070151218962124548064 : Int)/10^30)
theorem v271_pb_checked : Scalar.distance (sourceCoefficient 2 81 1 1) v271_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v271_pg : Scalar.QComplex := ((-93084984584238673574216 : Int)/10^30,(-445788380755233421839 : Int)/10^30)
theorem v271_pg_checked : Scalar.distance (sourceCoefficient 2 81 1 2) v271_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v271_mb : Scalar.QComplex := ((1693986579332111797170471 : Int)/10^30,(-431470692641600657651460984 : Int)/10^30)
theorem v271_mb_checked : Scalar.distance (sourceCoefficient 2 81 3 1) v271_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v271_mg : Scalar.QComplex := ((-93085334619739747316626 : Int)/10^30,(-365460065463724520717 : Int)/10^30)
theorem v271_mg_checked : Scalar.distance (sourceCoefficient 2 81 3 2) v271_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v271_upper : Scalar.QComplex := ((999995308711615027416820565429 : Int)/10^30,(3063095617469107897747561264 : Int)/10^30)
theorem v271_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 81 5) 1) 14) v271_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material271 : Material (2 : Basis) (81 : Basis) where
  plus := ![v271_pa,v271_pb,v271_pg]
  minus := ![(Primitive.Addresses.material271 1).one,v271_mb,v271_mg]
  upper := v271_upper
  lower := (Primitive.Addresses.material271 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v271_pa_checked.trans (by decide +kernel)
    · exact v271_pb_checked.trans (by decide +kernel)
    · exact v271_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 81 Primitive.Addresses.material271
    · exact v271_mb_checked.trans (by decide +kernel)
    · exact v271_mg_checked.trans (by decide +kernel)
  upper_error := v271_upper_checked
  lower_error := reuse_lower_error 2 81 Primitive.Addresses.material271

def v272_pa : Scalar.QComplex := ((999988580265335455073021195936 : Int)/10^30,(4779052094165750496268260707 : Int)/10^30)
theorem v272_pa_checked : Scalar.distance (sourceCoefficient 2 82 1 0) v272_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v272_pb : Scalar.QComplex := ((2062036761526028350918504 : Int)/10^30,(-431469080684565346343694174 : Int)/10^30)
theorem v272_pb_checked : Scalar.distance (sourceCoefficient 2 82 1 1) v272_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v272_pg : Scalar.QComplex := ((-93084987933798074008654 : Int)/10^30,(-444863086738823909713 : Int)/10^30)
theorem v272_pg_checked : Scalar.distance (sourceCoefficient 2 82 1 2) v272_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v272_mb : Scalar.QComplex := ((1689697609750742709426129 : Int)/10^30,(-431470699473762005094210150 : Int)/10^30)
theorem v272_mb_checked : Scalar.distance (sourceCoefficient 2 82 3 1) v272_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v272_mg : Scalar.QComplex := ((-93085337170810838091106 : Int)/10^30,(-364534768901325354907 : Int)/10^30)
theorem v272_mg_checked : Scalar.distance (sourceCoefficient 2 82 3 2) v272_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v272_upper : Scalar.QComplex := ((999995339110174370920935422329 : Int)/10^30,(3053155405046423685316165483 : Int)/10^30)
theorem v272_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 82 5) 1) 14) v272_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material272 : Material (2 : Basis) (82 : Basis) where
  plus := ![v272_pa,v272_pb,v272_pg]
  minus := ![(Primitive.Addresses.material272 1).one,v272_mb,v272_mg]
  upper := v272_upper
  lower := (Primitive.Addresses.material272 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v272_pa_checked.trans (by decide +kernel)
    · exact v272_pb_checked.trans (by decide +kernel)
    · exact v272_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 82 Primitive.Addresses.material272
    · exact v272_mb_checked.trans (by decide +kernel)
    · exact v272_mg_checked.trans (by decide +kernel)
  upper_error := v272_upper_checked
  lower_error := reuse_lower_error 2 82 Primitive.Addresses.material272

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
