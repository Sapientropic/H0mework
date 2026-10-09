import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B008
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B009

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v209_pa : Scalar.QComplex := ((999983287313209920434854361484 : Int)/10^30,(5781443960314705583618523513 : Int)/10^30)
theorem v209_pa_checked : Scalar.distance (sourceCoefficient 2 19 1 0) v209_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v209_pb : Scalar.QComplex := ((2494548205580061245705577 : Int)/10^30,(-431467732300121322394785805 : Int)/10^30)
theorem v209_pb_checked : Scalar.distance (sourceCoefficient 2 19 1 1) v209_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v209_pg : Scalar.QComplex := ((-93084596133529987149456 : Int)/10^30,(-538172370420796457288 : Int)/10^30)
theorem v209_pg_checked : Scalar.distance (sourceCoefficient 2 19 1 2) v209_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v209_mb : Scalar.QComplex := ((2122210056356044445081061 : Int)/10^30,(-431469724327716672604677289 : Int)/10^30)
theorem v209_mb_checked : Scalar.distance (sourceCoefficient 2 19 3 1) v209_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v209_mg : Scalar.QComplex := ((-93085025892397959787062 : Int)/10^30,(-457844355945972472687 : Int)/10^30)
theorem v209_mg_checked : Scalar.distance (sourceCoefficient 2 19 3 2) v209_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v209_upper : Scalar.QComplex := ((999991776203356760074601693064 : Int)/10^30,(4055554913405639170688811417 : Int)/10^30)
theorem v209_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 19 5) 1) 14) v209_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material209 : Material (2 : Basis) (19 : Basis) where
  plus := ![v209_pa,v209_pb,v209_pg]
  minus := ![(Primitive.Addresses.material209 1).one,v209_mb,v209_mg]
  upper := v209_upper
  lower := (Primitive.Addresses.material209 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v209_pa_checked.trans (by decide +kernel)
    · exact v209_pb_checked.trans (by decide +kernel)
    · exact v209_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 19 Primitive.Addresses.material209
    · exact v209_mb_checked.trans (by decide +kernel)
    · exact v209_mg_checked.trans (by decide +kernel)
  upper_error := v209_upper_checked
  lower_error := reuse_lower_error 2 19 Primitive.Addresses.material209

def v210_pa : Scalar.QComplex := ((999983303528729022110343970763 : Int)/10^30,(5778638574076326217216250190 : Int)/10^30)
theorem v210_pa_checked : Scalar.distance (sourceCoefficient 2 20 1 0) v210_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v210_pb : Scalar.QComplex := ((2493337737749008556770390 : Int)/10^30,(-431467736880505080233180631 : Int)/10^30)
theorem v210_pb_checked : Scalar.distance (sourceCoefficient 2 20 1 1) v210_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v210_pg : Scalar.QComplex := ((-93084597382335249338601 : Int)/10^30,(-537911226305263035538 : Int)/10^30)
theorem v210_pg_checked : Scalar.distance (sourceCoefficient 2 20 1 2) v210_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v210_mb : Scalar.QComplex := ((2120999585023039360571556 : Int)/10^30,(-431469727863519504205722481 : Int)/10^30)
theorem v210_mb_checked : Scalar.distance (sourceCoefficient 2 20 3 1) v210_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v210_mg : Scalar.QComplex := ((-93085026915847146777947 : Int)/10^30,(-457583210850012242857 : Int)/10^30)
theorem v210_mg_checked : Scalar.distance (sourceCoefficient 2 20 3 2) v210_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v210_upper : Scalar.QComplex := ((999991787577009565847891790172 : Int)/10^30,(4052749503359038153445569476 : Int)/10^30)
theorem v210_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 20 5) 1) 14) v210_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material210 : Material (2 : Basis) (20 : Basis) where
  plus := ![v210_pa,v210_pb,v210_pg]
  minus := ![(Primitive.Addresses.material210 1).one,v210_mb,v210_mg]
  upper := v210_upper
  lower := (Primitive.Addresses.material210 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v210_pa_checked.trans (by decide +kernel)
    · exact v210_pb_checked.trans (by decide +kernel)
    · exact v210_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 20 Primitive.Addresses.material210
    · exact v210_mb_checked.trans (by decide +kernel)
    · exact v210_mg_checked.trans (by decide +kernel)
  upper_error := v210_upper_checked
  lower_error := reuse_lower_error 2 20 Primitive.Addresses.material210

def v211_pa : Scalar.QComplex := ((999983608442612263474431565883 : Int)/10^30,(5725630628351732547431324111 : Int)/10^30)
theorem v211_pa_checked : Scalar.distance (sourceCoefficient 2 21 1 0) v211_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v211_pb : Scalar.QComplex := ((2470465874872938759055092 : Int)/10^30,(-431467822576069791519125358 : Int)/10^30)
theorem v211_pb_checked : Scalar.distance (sourceCoefficient 2 21 1 1) v211_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v211_pg : Scalar.QComplex := ((-93084620817929620159074 : Int)/10^30,(-532976892304961689788 : Int)/10^30)
theorem v211_pg_checked : Scalar.distance (sourceCoefficient 2 21 1 2) v211_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v211_mb : Scalar.QComplex := ((2098127656711796646509436 : Int)/10^30,(-431469793821664755532649264 : Int)/10^30)
theorem v211_mb_checked : Scalar.distance (sourceCoefficient 2 21 3 1) v211_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v211_mg : Scalar.QComplex := ((-93085046093324783349169 : Int)/10^30,(-452648858463126513594 : Int)/10^30)
theorem v211_mg_checked : Scalar.distance (sourceCoefficient 2 21 3 2) v211_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v211_upper : Scalar.QComplex := ((999992001003533196423431093175 : Int)/10^30,(3999741110329851986545626785 : Int)/10^30)
theorem v211_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 21 5) 1) 14) v211_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material211 : Material (2 : Basis) (21 : Basis) where
  plus := ![v211_pa,v211_pb,v211_pg]
  minus := ![(Primitive.Addresses.material211 1).one,v211_mb,v211_mg]
  upper := v211_upper
  lower := (Primitive.Addresses.material211 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v211_pa_checked.trans (by decide +kernel)
    · exact v211_pb_checked.trans (by decide +kernel)
    · exact v211_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 21 Primitive.Addresses.material211
    · exact v211_mb_checked.trans (by decide +kernel)
    · exact v211_mg_checked.trans (by decide +kernel)
  upper_error := v211_upper_checked
  lower_error := reuse_lower_error 2 21 Primitive.Addresses.material211

def v212_pa : Scalar.QComplex := ((999983616423731228392009449175 : Int)/10^30,(5724236553110978949255592041 : Int)/10^30)
theorem v212_pa_checked : Scalar.distance (sourceCoefficient 2 22 1 0) v212_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v212_pb : Scalar.QComplex := ((2469864359468298903887249 : Int)/10^30,(-431467824807992030660995399 : Int)/10^30)
theorem v212_pb_checked : Scalar.distance (sourceCoefficient 2 22 1 1) v212_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v212_pg : Scalar.QComplex := ((-93084621430152477666277 : Int)/10^30,(-532847122464446874250 : Int)/10^30)
theorem v212_pg_checked : Scalar.distance (sourceCoefficient 2 22 1 2) v212_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v212_mb : Scalar.QComplex := ((2097526139605080096767731 : Int)/10^30,(-431469795534505460671821352 : Int)/10^30)
theorem v212_mb_checked : Scalar.distance (sourceCoefficient 2 22 3 1) v212_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v212_mg : Scalar.QComplex := ((-93085046593561885150191 : Int)/10^30,(-452519088142610187920 : Int)/10^30)
theorem v212_mg_checked : Scalar.distance (sourceCoefficient 2 22 3 2) v212_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v212_upper : Scalar.QComplex := ((999992006578592878379043880038 : Int)/10^30,(3998347023390722407899973537 : Int)/10^30)
theorem v212_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 22 5) 1) 14) v212_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material212 : Material (2 : Basis) (22 : Basis) where
  plus := ![v212_pa,v212_pb,v212_pg]
  minus := ![(Primitive.Addresses.material212 1).one,v212_mb,v212_mg]
  upper := v212_upper
  lower := (Primitive.Addresses.material212 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v212_pa_checked.trans (by decide +kernel)
    · exact v212_pb_checked.trans (by decide +kernel)
    · exact v212_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 22 Primitive.Addresses.material212
    · exact v212_mb_checked.trans (by decide +kernel)
    · exact v212_mg_checked.trans (by decide +kernel)
  upper_error := v212_upper_checked
  lower_error := reuse_lower_error 2 22 Primitive.Addresses.material212

def v213_pa : Scalar.QComplex := ((999983675380302856647119310096 : Int)/10^30,(5713927974789186069990761132 : Int)/10^30)
theorem v213_pa_checked : Scalar.distance (sourceCoefficient 2 23 1 0) v213_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v213_pb : Scalar.QComplex := ((2465416415482101635779355 : Int)/10^30,(-431467841277380334391593730 : Int)/10^30)
theorem v213_pb_checked : Scalar.distance (sourceCoefficient 2 23 1 1) v213_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v213_pg : Scalar.QComplex := ((-93084625950722484570625 : Int)/10^30,(-531887531104287570230 : Int)/10^30)
theorem v213_pg_checked : Scalar.distance (sourceCoefficient 2 23 1 2) v213_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v213_mb : Scalar.QComplex := ((2093078183062715303398039 : Int)/10^30,(-431469808165512299968838468 : Int)/10^30)
theorem v213_mb_checked : Scalar.distance (sourceCoefficient 2 23 3 1) v213_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v213_mg : Scalar.QComplex := ((-93085050286046083412765 : Int)/10^30,(-451559493238702285736 : Int)/10^30)
theorem v213_mg_checked : Scalar.distance (sourceCoefficient 2 23 3 2) v213_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v213_upper : Scalar.QComplex := ((999992047743405701251802971322 : Int)/10^30,(3988038358668651876302337233 : Int)/10^30)
theorem v213_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 23 5) 1) 14) v213_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material213 : Material (2 : Basis) (23 : Basis) where
  plus := ![v213_pa,v213_pb,v213_pg]
  minus := ![(Primitive.Addresses.material213 1).one,v213_mb,v213_mg]
  upper := v213_upper
  lower := (Primitive.Addresses.material213 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v213_pa_checked.trans (by decide +kernel)
    · exact v213_pb_checked.trans (by decide +kernel)
    · exact v213_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 23 Primitive.Addresses.material213
    · exact v213_mb_checked.trans (by decide +kernel)
    · exact v213_mg_checked.trans (by decide +kernel)
  upper_error := v213_upper_checked
  lower_error := reuse_lower_error 2 23 Primitive.Addresses.material213

def v214_pa : Scalar.QComplex := ((999983965184217205772540843179 : Int)/10^30,(5662982822706710874688283198 : Int)/10^30)
theorem v214_pa_checked : Scalar.distance (sourceCoefficient 2 24 1 0) v214_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v214_pb : Scalar.QComplex := ((2443434609565782597085738 : Int)/10^30,(-431467921771671910190499939 : Int)/10^30)
theorem v214_pb_checked : Scalar.distance (sourceCoefficient 2 24 1 1) v214_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v214_pg : Scalar.QComplex := ((-93084648121992236499145 : Int)/10^30,(-527145216048970655314 : Int)/10^30)
theorem v214_pg_checked : Scalar.distance (sourceCoefficient 2 24 1 2) v214_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v214_mb : Scalar.QComplex := ((2071096315868278923909126 : Int)/10^30,(-431469869690465422067950273 : Int)/10^30)
theorem v214_mb_checked : Scalar.distance (sourceCoefficient 2 24 3 1) v214_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v214_mg : Scalar.QComplex := ((-93085068364903273167191 : Int)/10^30,(-446817160816358761426 : Int)/10^30)
theorem v214_mg_checked : Scalar.distance (sourceCoefficient 2 24 3 2) v214_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v214_upper : Scalar.QComplex := ((999992249620177635231493325028 : Int)/10^30,(3937092782287730909045988902 : Int)/10^30)
theorem v214_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 24 5) 1) 14) v214_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material214 : Material (2 : Basis) (24 : Basis) where
  plus := ![v214_pa,v214_pb,v214_pg]
  minus := ![(Primitive.Addresses.material214 1).one,v214_mb,v214_mg]
  upper := v214_upper
  lower := (Primitive.Addresses.material214 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v214_pa_checked.trans (by decide +kernel)
    · exact v214_pb_checked.trans (by decide +kernel)
    · exact v214_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 24 Primitive.Addresses.material214
    · exact v214_mb_checked.trans (by decide +kernel)
    · exact v214_mg_checked.trans (by decide +kernel)
  upper_error := v214_upper_checked
  lower_error := reuse_lower_error 2 24 Primitive.Addresses.material214

def v215_pa : Scalar.QComplex := ((999984095079999084151504278706 : Int)/10^30,(5639998850651608196517972730 : Int)/10^30)
theorem v215_pa_checked : Scalar.distance (sourceCoefficient 2 25 1 0) v215_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v215_pb : Scalar.QComplex := ((2433517489846619355033154 : Int)/10^30,(-431467957597983279252086047 : Int)/10^30)
theorem v215_pb_checked : Scalar.distance (sourceCoefficient 2 25 1 1) v215_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v215_pg : Scalar.QComplex := ((-93084658032319017158165 : Int)/10^30,(-525005714489466224376 : Int)/10^30)
theorem v215_pg_checked : Scalar.distance (sourceCoefficient 2 25 1 2) v215_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v215_mb : Scalar.QComplex := ((2061179168925219433728290 : Int)/10^30,(-431469896958735784210297962 : Int)/10^30)
theorem v215_mb_checked : Scalar.distance (sourceCoefficient 2 25 3 1) v215_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v215_mg : Scalar.QComplex := ((-93085076428932877479507 : Int)/10^30,(-444677651501322873984 : Int)/10^30)
theorem v215_mg_checked : Scalar.distance (sourceCoefficient 2 25 3 2) v215_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v215_upper : Scalar.QComplex := ((999992339847515371651769156993 : Int)/10^30,(3914108620276219251134749702 : Int)/10^30)
theorem v215_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 25 5) 1) 14) v215_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material215 : Material (2 : Basis) (25 : Basis) where
  plus := ![v215_pa,v215_pb,v215_pg]
  minus := ![(Primitive.Addresses.material215 1).one,v215_mb,v215_mg]
  upper := v215_upper
  lower := (Primitive.Addresses.material215 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v215_pa_checked.trans (by decide +kernel)
    · exact v215_pb_checked.trans (by decide +kernel)
    · exact v215_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 25 Primitive.Addresses.material215
    · exact v215_mb_checked.trans (by decide +kernel)
    · exact v215_mg_checked.trans (by decide +kernel)
  upper_error := v215_upper_checked
  lower_error := reuse_lower_error 2 25 Primitive.Addresses.material215

def v216_pa : Scalar.QComplex := ((999984136472794518359749144363 : Int)/10^30,(5632655036434228629138460275 : Int)/10^30)
theorem v216_pa_checked : Scalar.distance (sourceCoefficient 2 26 1 0) v216_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v216_pb : Scalar.QComplex := ((2430348782445464904732403 : Int)/10^30,(-431467968981099169736522432 : Int)/10^30)
theorem v216_pb_checked : Scalar.distance (sourceCoefficient 2 26 1 1) v216_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v216_pg : Scalar.QComplex := ((-93084661186761636746388 : Int)/10^30,(-524322103246335978176 : Int)/10^30)
theorem v216_pg_checked : Scalar.distance (sourceCoefficient 2 26 1 2) v216_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v216_mb : Scalar.QComplex := ((2058010452880803228979875 : Int)/10^30,(-431469905607395662327745500 : Int)/10^30)
theorem v216_mb_checked : Scalar.distance (sourceCoefficient 2 26 3 1) v216_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v216_mg : Scalar.QComplex := ((-93085078993448608410635 : Int)/10^30,(-443994037790590426296 : Int)/10^30)
theorem v216_mg_checked : Scalar.distance (sourceCoefficient 2 26 3 2) v216_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v216_upper : Scalar.QComplex := ((999992368565492042577952505695 : Int)/10^30,(3906764745556378501150150645 : Int)/10^30)
theorem v216_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 26 5) 1) 14) v216_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material216 : Material (2 : Basis) (26 : Basis) where
  plus := ![v216_pa,v216_pb,v216_pg]
  minus := ![(Primitive.Addresses.material216 1).one,v216_mb,v216_mg]
  upper := v216_upper
  lower := (Primitive.Addresses.material216 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v216_pa_checked.trans (by decide +kernel)
    · exact v216_pb_checked.trans (by decide +kernel)
    · exact v216_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 26 Primitive.Addresses.material216
    · exact v216_mb_checked.trans (by decide +kernel)
    · exact v216_mg_checked.trans (by decide +kernel)
  upper_error := v216_upper_checked
  lower_error := reuse_lower_error 2 26 Primitive.Addresses.material216

def v217_pa : Scalar.QComplex := ((999984164878127302921207628032 : Int)/10^30,(5627609882917385951315547439 : Int)/10^30)
theorem v217_pa_checked : Scalar.distance (sourceCoefficient 2 27 1 0) v217_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v217_pb : Scalar.QComplex := ((2428171900705745486415412 : Int)/10^30,(-431467976783246982734293612 : Int)/10^30)
theorem v217_pb_checked : Scalar.distance (sourceCoefficient 2 27 1 1) v217_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v217_pg : Scalar.QComplex := ((-93084663350449435647820 : Int)/10^30,(-523852466686680332203 : Int)/10^30)
theorem v217_pg_checked : Scalar.distance (sourceCoefficient 2 27 1 2) v217_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v217_mb : Scalar.QComplex := ((2055833565218734203846755 : Int)/10^30,(-431469911530989671965477616 : Int)/10^30)
theorem v217_mb_checked : Scalar.distance (sourceCoefficient 2 27 3 1) v217_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v217_mg : Scalar.QComplex := ((-93085080751860402334852 : Int)/10^30,(-443524399538636813363 : Int)/10^30)
theorem v217_mg_checked : Scalar.distance (sourceCoefficient 2 27 3 2) v217_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v217_upper : Scalar.QComplex := ((999992388263305243414239641492 : Int)/10^30,(3901719550528671866808660812 : Int)/10^30)
theorem v217_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 27 5) 1) 14) v217_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material217 : Material (2 : Basis) (27 : Basis) where
  plus := ![v217_pa,v217_pb,v217_pg]
  minus := ![(Primitive.Addresses.material217 1).one,v217_mb,v217_mg]
  upper := v217_upper
  lower := (Primitive.Addresses.material217 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v217_pa_checked.trans (by decide +kernel)
    · exact v217_pb_checked.trans (by decide +kernel)
    · exact v217_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 27 Primitive.Addresses.material217
    · exact v217_mb_checked.trans (by decide +kernel)
    · exact v217_mg_checked.trans (by decide +kernel)
  upper_error := v217_upper_checked
  lower_error := reuse_lower_error 2 27 Primitive.Addresses.material217

def v218_pa : Scalar.QComplex := ((999984203103557285460915053669 : Int)/10^30,(5620813405859676491688696886 : Int)/10^30)
theorem v218_pa_checked : Scalar.distance (sourceCoefficient 2 28 1 0) v218_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v218_pb : Scalar.QComplex := ((2425239358304883321564474 : Int)/10^30,(-431467987270601895792499421 : Int)/10^30)
theorem v218_pb_checked : Scalar.distance (sourceCoefficient 2 28 1 1) v218_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v218_pg : Scalar.QComplex := ((-93084666260847558194470 : Int)/10^30,(-523219805248026161421 : Int)/10^30)
theorem v218_pg_checked : Scalar.distance (sourceCoefficient 2 28 1 2) v218_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v218_mb : Scalar.QComplex := ((2052901014859676641607661 : Int)/10^30,(-431469919487688664964918529 : Int)/10^30)
theorem v218_mb_checked : Scalar.distance (sourceCoefficient 2 28 3 1) v218_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v218_mg : Scalar.QComplex := ((-93085083116299113662170 : Int)/10^30,(-442891735824008909955 : Int)/10^30)
theorem v218_mg_checked : Scalar.distance (sourceCoefficient 2 28 3 2) v218_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v218_upper : Scalar.QComplex := ((999992414758575463642017705894 : Int)/10^30,(3894923017619892248418038236 : Int)/10^30)
theorem v218_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 28 5) 1) 14) v218_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material218 : Material (2 : Basis) (28 : Basis) where
  plus := ![v218_pa,v218_pb,v218_pg]
  minus := ![(Primitive.Addresses.material218 1).one,v218_mb,v218_mg]
  upper := v218_upper
  lower := (Primitive.Addresses.material218 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v218_pa_checked.trans (by decide +kernel)
    · exact v218_pb_checked.trans (by decide +kernel)
    · exact v218_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 28 Primitive.Addresses.material218
    · exact v218_mb_checked.trans (by decide +kernel)
    · exact v218_mg_checked.trans (by decide +kernel)
  upper_error := v218_upper_checked
  lower_error := reuse_lower_error 2 28 Primitive.Addresses.material218

def v219_pa : Scalar.QComplex := ((999984280381320301330767586874 : Int)/10^30,(5607048265619434039070972694 : Int)/10^30)
theorem v219_pa_checked : Scalar.distance (sourceCoefficient 2 29 1 0) v219_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v219_pb : Scalar.QComplex := ((2419299978808522656717223 : Int)/10^30,(-431468008429586438111104402 : Int)/10^30)
theorem v219_pb_checked : Scalar.distance (sourceCoefficient 2 29 1 1) v219_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v219_pg : Scalar.QComplex := ((-93084672140008101295198 : Int)/10^30,(-521938454151859614512 : Int)/10^30)
theorem v219_pg_checked : Scalar.distance (sourceCoefficient 2 29 1 2) v219_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v219_mb : Scalar.QComplex := ((2046961619315567711575124 : Int)/10^30,(-431469935521248323189770896 : Int)/10^30)
theorem v219_mb_checked : Scalar.distance (sourceCoefficient 2 29 3 1) v219_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v219_mg : Scalar.QComplex := ((-93085087889709181602086 : Int)/10^30,(-441610380131497175653 : Int)/10^30)
theorem v219_mg_checked : Scalar.distance (sourceCoefficient 2 29 3 2) v219_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v219_upper : Scalar.QComplex := ((999992468278840092470856168580 : Int)/10^30,(3881157764506800835188852829 : Int)/10^30)
theorem v219_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 29 5) 1) 14) v219_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material219 : Material (2 : Basis) (29 : Basis) where
  plus := ![v219_pa,v219_pb,v219_pg]
  minus := ![(Primitive.Addresses.material219 1).one,v219_mb,v219_mg]
  upper := v219_upper
  lower := (Primitive.Addresses.material219 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v219_pa_checked.trans (by decide +kernel)
    · exact v219_pb_checked.trans (by decide +kernel)
    · exact v219_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 29 Primitive.Addresses.material219
    · exact v219_mb_checked.trans (by decide +kernel)
    · exact v219_mg_checked.trans (by decide +kernel)
  upper_error := v219_upper_checked
  lower_error := reuse_lower_error 2 29 Primitive.Addresses.material219

def v220_pa : Scalar.QComplex := ((999984309615748116568001199544 : Int)/10^30,(5601832049928745609750098785 : Int)/10^30)
theorem v220_pa_checked : Scalar.distance (sourceCoefficient 2 30 1 0) v220_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v220_pb : Scalar.QComplex := ((2417049287328176175757631 : Int)/10^30,(-431468016419172410942219113 : Int)/10^30)
theorem v220_pb_checked : Scalar.distance (sourceCoefficient 2 30 1 1) v220_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v220_pg : Scalar.QComplex := ((-93084674362503459343719 : Int)/10^30,(-521452893997328579799 : Int)/10^30)
theorem v220_pg_checked : Scalar.distance (sourceCoefficient 2 30 1 2) v220_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v220_mb : Scalar.QComplex := ((2044710921778603673471814 : Int)/10^30,(-431469941568585940975213469 : Int)/10^30)
theorem v220_mb_checked : Scalar.distance (sourceCoefficient 2 30 3 1) v220_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v220_mg : Scalar.QComplex := ((-93085089693187167571280 : Int)/10^30,(-441124818239848981147 : Int)/10^30)
theorem v220_mg_checked : Scalar.distance (sourceCoefficient 2 30 3 2) v220_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v220_upper : Scalar.QComplex := ((999992488510509295724681829955 : Int)/10^30,(3875941506129082654885404409 : Int)/10^30)
theorem v220_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 30 5) 1) 14) v220_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material220 : Material (2 : Basis) (30 : Basis) where
  plus := ![v220_pa,v220_pb,v220_pg]
  minus := ![(Primitive.Addresses.material220 1).one,v220_mb,v220_mg]
  upper := v220_upper
  lower := (Primitive.Addresses.material220 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v220_pa_checked.trans (by decide +kernel)
    · exact v220_pb_checked.trans (by decide +kernel)
    · exact v220_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 30 Primitive.Addresses.material220
    · exact v220_mb_checked.trans (by decide +kernel)
    · exact v220_mg_checked.trans (by decide +kernel)
  upper_error := v220_upper_checked
  lower_error := reuse_lower_error 2 30 Primitive.Addresses.material220

def v221_pa : Scalar.QComplex := ((999984371706914654294744709904 : Int)/10^30,(5590737154181606581943405393 : Int)/10^30)
theorem v221_pa_checked : Scalar.distance (sourceCoefficient 2 31 1 0) v221_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v221_pb : Scalar.QComplex := ((2412262064491391752169843 : Int)/10^30,(-431468033360970950207522265 : Int)/10^30)
theorem v221_pb_checked : Scalar.distance (sourceCoefficient 2 31 1 1) v221_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v221_pg : Scalar.QComplex := ((-93084679079926024532376 : Int)/10^30,(-520420107095174941718 : Int)/10^30)
theorem v221_pg_checked : Scalar.distance (sourceCoefficient 2 31 1 2) v221_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v221_mb : Scalar.QComplex := ((2039923686104311989806036 : Int)/10^30,(-431469954379220472402489007 : Int)/10^30)
theorem v221_mb_checked : Scalar.distance (sourceCoefficient 2 31 3 1) v221_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v221_mg : Scalar.QComplex := ((-93085093519359394684684 : Int)/10^30,(-440092027651325898497 : Int)/10^30)
theorem v221_mg_checked : Scalar.distance (sourceCoefficient 2 31 3 2) v221_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v221_upper : Scalar.QComplex := ((999992531452799817470315441036 : Int)/10^30,(3864846519742766966946546335 : Int)/10^30)
theorem v221_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 31 5) 1) 14) v221_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material221 : Material (2 : Basis) (31 : Basis) where
  plus := ![v221_pa,v221_pb,v221_pg]
  minus := ![(Primitive.Addresses.material221 1).one,v221_mb,v221_mg]
  upper := v221_upper
  lower := (Primitive.Addresses.material221 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v221_pa_checked.trans (by decide +kernel)
    · exact v221_pb_checked.trans (by decide +kernel)
    · exact v221_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 31 Primitive.Addresses.material221
    · exact v221_mb_checked.trans (by decide +kernel)
    · exact v221_mg_checked.trans (by decide +kernel)
  upper_error := v221_upper_checked
  lower_error := reuse_lower_error 2 31 Primitive.Addresses.material221

def v222_pa : Scalar.QComplex := ((999984398397373503070017385778 : Int)/10^30,(5585961138693084825829659977 : Int)/10^30)
theorem v222_pa_checked : Scalar.distance (sourceCoefficient 2 32 1 0) v222_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v222_pb : Scalar.QComplex := ((2410201310562032377179729 : Int)/10^30,(-431468040632095635327708855 : Int)/10^30)
theorem v222_pb_checked : Scalar.distance (sourceCoefficient 2 32 1 1) v222_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v222_pg : Scalar.QComplex := ((-93084681106516959097724 : Int)/10^30,(-519975523720138738283 : Int)/10^30)
theorem v222_pg_checked : Scalar.distance (sourceCoefficient 2 32 1 2) v222_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v222_mb : Scalar.QComplex := ((2037862926667612359864124 : Int)/10^30,(-431469959872004622025109013 : Int)/10^30)
theorem v222_mb_checked : Scalar.distance (sourceCoefficient 2 32 3 1) v222_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v222_mg : Scalar.QComplex := ((-93085095162294145293277 : Int)/10^30,(-439647442692971701791 : Int)/10^30)
theorem v222_mg_checked : Scalar.distance (sourceCoefficient 2 32 3 2) v222_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v222_upper : Scalar.QComplex := ((999992549900249457494409888150 : Int)/10^30,(3860070465302248617322627544 : Int)/10^30)
theorem v222_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 32 5) 1) 14) v222_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material222 : Material (2 : Basis) (32 : Basis) where
  plus := ![v222_pa,v222_pb,v222_pg]
  minus := ![(Primitive.Addresses.material222 1).one,v222_mb,v222_mg]
  upper := v222_upper
  lower := (Primitive.Addresses.material222 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v222_pa_checked.trans (by decide +kernel)
    · exact v222_pb_checked.trans (by decide +kernel)
    · exact v222_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 32 Primitive.Addresses.material222
    · exact v222_mb_checked.trans (by decide +kernel)
    · exact v222_mg_checked.trans (by decide +kernel)
  upper_error := v222_upper_checked
  lower_error := reuse_lower_error 2 32 Primitive.Addresses.material222

def v223_pa : Scalar.QComplex := ((999984435556036086831199802304 : Int)/10^30,(5579305124826068500088577954 : Int)/10^30)
theorem v223_pa_checked : Scalar.distance (sourceCoefficient 2 33 1 0) v223_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v223_pb : Scalar.QComplex := ((2407329375455022522559242 : Int)/10^30,(-431468050743487784422824030 : Int)/10^30)
theorem v223_pb_checked : Scalar.distance (sourceCoefficient 2 33 1 1) v223_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v223_pg : Scalar.QComplex := ((-93084683926709425514881 : Int)/10^30,(-519355937561492164898 : Int)/10^30)
theorem v223_pg_checked : Scalar.distance (sourceCoefficient 2 33 1 2) v223_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v223_mb : Scalar.QComplex := ((2034990983904279175029931 : Int)/10^30,(-431469967505042355992936698 : Int)/10^30)
theorem v223_mb_checked : Scalar.distance (sourceCoefficient 2 33 3 1) v223_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v223_mg : Scalar.QComplex := ((-93085097447810611836595 : Int)/10^30,(-439027854331326289991 : Int)/10^30)
theorem v223_mg_checked : Scalar.distance (sourceCoefficient 2 33 3 2) v223_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v223_upper : Scalar.QComplex := ((999992575571180592183622203234 : Int)/10^30,(3853414397216102464155081337 : Int)/10^30)
theorem v223_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 33 5) 1) 14) v223_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material223 : Material (2 : Basis) (33 : Basis) where
  plus := ![v223_pa,v223_pb,v223_pg]
  minus := ![(Primitive.Addresses.material223 1).one,v223_mb,v223_mg]
  upper := v223_upper
  lower := (Primitive.Addresses.material223 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v223_pa_checked.trans (by decide +kernel)
    · exact v223_pb_checked.trans (by decide +kernel)
    · exact v223_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 33 Primitive.Addresses.material223
    · exact v223_mb_checked.trans (by decide +kernel)
    · exact v223_mg_checked.trans (by decide +kernel)
  upper_error := v223_upper_checked
  lower_error := reuse_lower_error 2 33 Primitive.Addresses.material223

def v224_pa : Scalar.QComplex := ((999984525625784655438137145718 : Int)/10^30,(5563138410504610769232083121 : Int)/10^30)
theorem v224_pa_checked : Scalar.distance (sourceCoefficient 2 34 1 0) v224_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v224_pb : Scalar.QComplex := ((2400353766006186388599511 : Int)/10^30,(-431468075196791402486573085 : Int)/10^30)
theorem v224_pb_checked : Scalar.distance (sourceCoefficient 2 34 1 1) v224_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v224_pg : Scalar.QComplex := ((-93084690756605947255350 : Int)/10^30,(-517851031998674993685 : Int)/10^30)
theorem v224_pg_checked : Scalar.distance (sourceCoefficient 2 34 1 2) v224_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v224_mb : Scalar.QComplex := ((2028015355950681553495230 : Int)/10^30,(-431469985938700084415638839 : Int)/10^30)
theorem v224_mb_checked : Scalar.distance (sourceCoefficient 2 34 3 1) v224_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v224_mg : Scalar.QComplex := ((-93085102979038868213724 : Int)/10^30,(-437522943434961146256 : Int)/10^30)
theorem v224_mg_checked : Scalar.distance (sourceCoefficient 2 34 3 2) v224_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v224_upper : Scalar.QComplex := ((999992637738512726510894460863 : Int)/10^30,(3837247551520851673788611458 : Int)/10^30)
theorem v224_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 34 5) 1) 14) v224_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material224 : Material (2 : Basis) (34 : Basis) where
  plus := ![v224_pa,v224_pb,v224_pg]
  minus := ![(Primitive.Addresses.material224 1).one,v224_mb,v224_mg]
  upper := v224_upper
  lower := (Primitive.Addresses.material224 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v224_pa_checked.trans (by decide +kernel)
    · exact v224_pb_checked.trans (by decide +kernel)
    · exact v224_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 34 Primitive.Addresses.material224
    · exact v224_mb_checked.trans (by decide +kernel)
    · exact v224_mg_checked.trans (by decide +kernel)
  upper_error := v224_upper_checked
  lower_error := reuse_lower_error 2 34 Primitive.Addresses.material224

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
