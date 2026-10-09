import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B112
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B113

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2705_pa : Scalar.QComplex := ((999999365117980259098086649706 : Int)/10^30,(-1126837892692034401313294356 : Int)/10^30)
theorem v2705_pa_checked : Scalar.distance (sourceCoefficient 33 66 1 0) v2705_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2705_pb : Scalar.QComplex := ((-486205198840510584520211 : Int)/10^30,(-431477227834449545725159921 : Int)/10^30)
theorem v2705_pb_checked : Scalar.distance (sourceCoefficient 33 66 1 1) v2705_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2705_pg : Scalar.QComplex := ((-93086368723867635017878 : Int)/10^30,(104893314166035860431 : Int)/10^30)
theorem v2705_pg_checked : Scalar.distance (sourceCoefficient 33 66 1 2) v2705_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2705_mb : Scalar.QComplex := ((-858550432412270025212936 : Int)/10^30,(-431476647602569409393336115 : Int)/10^30)
theorem v2705_mb_checked : Scalar.distance (sourceCoefficient 33 66 3 1) v2705_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2705_mg : Scalar.QComplex := ((-93086243545352396116526 : Int)/10^30,(185222618863742804594 : Int)/10^30)
theorem v2705_mg_checked : Scalar.distance (sourceCoefficient 33 66 3 2) v2705_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2705_upper : Scalar.QComplex := ((999995930916417241611094421782 : Int)/10^30,(-2852744399359251101658364964 : Int)/10^30)
theorem v2705_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 66 5) 1) 14) v2705_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2705 : Material (33 : Basis) (66 : Basis) where
  plus := ![v2705_pa,v2705_pb,v2705_pg]
  minus := ![(Primitive.Addresses.material2705 1).one,v2705_mb,v2705_mg]
  upper := v2705_upper
  lower := (Primitive.Addresses.material2705 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2705_pa_checked.trans (by decide +kernel)
    · exact v2705_pb_checked.trans (by decide +kernel)
    · exact v2705_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 66 Primitive.Addresses.material2705
    · exact v2705_mb_checked.trans (by decide +kernel)
    · exact v2705_mg_checked.trans (by decide +kernel)
  upper_error := v2705_upper_checked
  lower_error := reuse_lower_error 33 66 Primitive.Addresses.material2705

def v2706_pa : Scalar.QComplex := ((999999331421300585120173597530 : Int)/10^30,(-1156355028454618837574696382 : Int)/10^30)
theorem v2706_pa_checked : Scalar.distance (sourceCoefficient 33 67 1 0) v2706_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2706_pb : Scalar.QComplex := ((-498941176227861884226044 : Int)/10^30,(-431477211037181159859231593 : Int)/10^30)
theorem v2706_pb_checked : Scalar.distance (sourceCoefficient 33 67 1 1) v2706_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2706_pg : Scalar.QComplex := ((-93086365343604814859293 : Int)/10^30,(107640958612093303158 : Int)/10^30)
theorem v2706_pg_checked : Scalar.distance (sourceCoefficient 33 67 1 2) v2706_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2706_mb : Scalar.QComplex := ((-871286390562148784569214 : Int)/10^30,(-431476619814732399762158090 : Int)/10^30)
theorem v2706_mb_checked : Scalar.distance (sourceCoefficient 33 67 3 1) v2706_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2706_mg : Scalar.QComplex := ((-93086237793997426948762 : Int)/10^30,(187970259369712074089 : Int)/10^30)
theorem v2706_mg_checked : Scalar.distance (sourceCoefficient 33 67 3 2) v2706_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2706_upper : Scalar.QComplex := ((999995846275889202297290642681 : Int)/10^30,(-2882261433002116967497961897 : Int)/10^30)
theorem v2706_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 67 5) 1) 14) v2706_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2706 : Material (33 : Basis) (67 : Basis) where
  plus := ![v2706_pa,v2706_pb,v2706_pg]
  minus := ![(Primitive.Addresses.material2706 1).one,v2706_mb,v2706_mg]
  upper := v2706_upper
  lower := (Primitive.Addresses.material2706 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2706_pa_checked.trans (by decide +kernel)
    · exact v2706_pb_checked.trans (by decide +kernel)
    · exact v2706_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 67 Primitive.Addresses.material2706
    · exact v2706_mb_checked.trans (by decide +kernel)
    · exact v2706_mg_checked.trans (by decide +kernel)
  upper_error := v2706_upper_checked
  lower_error := reuse_lower_error 33 67 Primitive.Addresses.material2706

def v2707_pa : Scalar.QComplex := ((999999273368966859249243818766 : Int)/10^30,(-1205512977237840932056211277 : Int)/10^30)
theorem v2707_pa_checked : Scalar.distance (sourceCoefficient 33 68 1 0) v2707_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2707_pb : Scalar.QComplex := ((-520151720181663751297932 : Int)/10^30,(-431477181950451115418247765 : Int)/10^30)
theorem v2707_pb_checked : Scalar.distance (sourceCoefficient 33 68 1 1) v2707_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2707_pg : Scalar.QComplex := ((-93086359504094877873265 : Int)/10^30,(112216895926292429192 : Int)/10^30)
theorem v2707_pg_checked : Scalar.distance (sourceCoefficient 33 68 1 2) v2707_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2707_mb : Scalar.QComplex := ((-892496901517757757232632 : Int)/10^30,(-431476572424269040946830402 : Int)/10^30)
theorem v2707_mb_checked : Scalar.distance (sourceCoefficient 33 68 3 1) v2707_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2707_mg : Scalar.QComplex := ((-93086228005661854691431 : Int)/10^30,(192546189940846533525 : Int)/10^30)
theorem v2707_mg_checked : Scalar.distance (sourceCoefficient 33 68 3 2) v2707_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2707_upper : Scalar.QComplex := ((999995703381481912994135737038 : Int)/10^30,(-2931419208377287303393632908 : Int)/10^30)
theorem v2707_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 68 5) 1) 14) v2707_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2707 : Material (33 : Basis) (68 : Basis) where
  plus := ![v2707_pa,v2707_pb,v2707_pg]
  minus := ![(Primitive.Addresses.material2707 1).one,v2707_mb,v2707_mg]
  upper := v2707_upper
  lower := (Primitive.Addresses.material2707 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2707_pa_checked.trans (by decide +kernel)
    · exact v2707_pb_checked.trans (by decide +kernel)
    · exact v2707_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 68 Primitive.Addresses.material2707
    · exact v2707_mb_checked.trans (by decide +kernel)
    · exact v2707_mg_checked.trans (by decide +kernel)
  upper_error := v2707_upper_checked
  lower_error := reuse_lower_error 33 68 Primitive.Addresses.material2707

def v2708_pa : Scalar.QComplex := ((999999247053181307100897007228 : Int)/10^30,(-1227148349001410027251753048 : Int)/10^30)
theorem v2708_pa_checked : Scalar.distance (sourceCoefficient 33 69 1 0) v2708_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2708_pb : Scalar.QComplex := ((-529486893887585275038983 : Int)/10^30,(-431477168708234629447086301 : Int)/10^30)
theorem v2708_pb_checked : Scalar.distance (sourceCoefficient 33 69 1 1) v2708_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2708_pg : Scalar.QComplex := ((-93086356850843861814634 : Int)/10^30,(114230855133828108168 : Int)/10^30)
theorem v2708_pg_checked : Scalar.distance (sourceCoefficient 33 69 1 2) v2708_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2708_mb : Scalar.QComplex := ((-901832060320331051642105 : Int)/10^30,(-431476551126223018064016263 : Int)/10^30)
theorem v2708_mb_checked : Scalar.distance (sourceCoefficient 33 69 3 1) v2708_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2708_mg : Scalar.QComplex := ((-93086223614455735811689 : Int)/10^30,(194560146108857028184 : Int)/10^30)
theorem v2708_mg_checked : Scalar.distance (sourceCoefficient 33 69 3 2) v2708_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2708_upper : Scalar.QComplex := ((999995639725046636791105030577 : Int)/10^30,(-2953054502498853112457131119 : Int)/10^30)
theorem v2708_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 69 5) 1) 14) v2708_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2708 : Material (33 : Basis) (69 : Basis) where
  plus := ![v2708_pa,v2708_pb,v2708_pg]
  minus := ![(Primitive.Addresses.material2708 1).one,v2708_mb,v2708_mg]
  upper := v2708_upper
  lower := (Primitive.Addresses.material2708 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2708_pa_checked.trans (by decide +kernel)
    · exact v2708_pb_checked.trans (by decide +kernel)
    · exact v2708_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 69 Primitive.Addresses.material2708
    · exact v2708_mb_checked.trans (by decide +kernel)
    · exact v2708_mg_checked.trans (by decide +kernel)
  upper_error := v2708_upper_checked
  lower_error := reuse_lower_error 33 69 Primitive.Addresses.material2708

def v2709_pa : Scalar.QComplex := ((999999229487173171684217478573 : Int)/10^30,(-1241380304325235884351089906 : Int)/10^30)
theorem v2709_pa_checked : Scalar.distance (sourceCoefficient 33 70 1 0) v2709_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2709_pb : Scalar.QComplex := ((-535627660712637144691259 : Int)/10^30,(-431477159850541906050658726 : Int)/10^30)
theorem v2709_pb_checked : Scalar.distance (sourceCoefficient 33 70 1 1) v2709_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2709_pg : Scalar.QComplex := ((-93086355077791499881666 : Int)/10^30,(115555656832111580500 : Int)/10^30)
theorem v2709_pg_checked : Scalar.distance (sourceCoefficient 33 70 1 2) v2709_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2709_mb : Scalar.QComplex := ((-907972817215104900799383 : Int)/10^30,(-431476536969328392642686784 : Int)/10^30)
theorem v2709_mb_checked : Scalar.distance (sourceCoefficient 33 70 3 1) v2709_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2709_mg : Scalar.QComplex := ((-93086220698159835302064 : Int)/10^30,(195884945783791948782 : Int)/10^30)
theorem v2709_mg_checked : Scalar.distance (sourceCoefficient 33 70 3 2) v2709_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2709_upper : Scalar.QComplex := ((999995597596000887858022565673 : Int)/10^30,(-2967286406308516851708464670 : Int)/10^30)
theorem v2709_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 70 5) 1) 14) v2709_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2709 : Material (33 : Basis) (70 : Basis) where
  plus := ![v2709_pa,v2709_pb,v2709_pg]
  minus := ![(Primitive.Addresses.material2709 1).one,v2709_mb,v2709_mg]
  upper := v2709_upper
  lower := (Primitive.Addresses.material2709 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2709_pa_checked.trans (by decide +kernel)
    · exact v2709_pb_checked.trans (by decide +kernel)
    · exact v2709_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 70 Primitive.Addresses.material2709
    · exact v2709_mb_checked.trans (by decide +kernel)
    · exact v2709_mg_checked.trans (by decide +kernel)
  upper_error := v2709_upper_checked
  lower_error := reuse_lower_error 33 70 Primitive.Addresses.material2709

def v2710_pa : Scalar.QComplex := ((999999199035478986238387256307 : Int)/10^30,(-1265673101746007440481383093 : Int)/10^30)
theorem v2710_pa_checked : Scalar.distance (sourceCoefficient 33 71 1 0) v2710_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2710_pb : Scalar.QComplex := ((-546109453177988522548994 : Int)/10^30,(-431477144461970181815416825 : Int)/10^30)
theorem v2710_pb_checked : Scalar.distance (sourceCoefficient 33 71 1 1) v2710_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2710_pg : Scalar.QComplex := ((-93086352000515978680016 : Int)/10^30,(117816986233939669688 : Int)/10^30)
theorem v2710_pg_checked : Scalar.distance (sourceCoefficient 33 71 1 2) v2710_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2710_mb : Scalar.QComplex := ((-918454592497961579753272 : Int)/10^30,(-431476512535447583085867885 : Int)/10^30)
theorem v2710_mb_checked : Scalar.distance (sourceCoefficient 33 71 3 1) v2710_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2710_mg : Scalar.QComplex := ((-93086215669460032628627 : Int)/10^30,(198146271688073574358 : Int)/10^30)
theorem v2710_mg_checked : Scalar.distance (sourceCoefficient 33 71 3 2) v2710_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2710_upper : Scalar.QComplex := ((999995525217187533748541788211 : Int)/10^30,(-2991579114991158674078411225 : Int)/10^30)
theorem v2710_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 71 5) 1) 14) v2710_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2710 : Material (33 : Basis) (71 : Basis) where
  plus := ![v2710_pa,v2710_pb,v2710_pg]
  minus := ![(Primitive.Addresses.material2710 1).one,v2710_mb,v2710_mg]
  upper := v2710_upper
  lower := (Primitive.Addresses.material2710 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2710_pa_checked.trans (by decide +kernel)
    · exact v2710_pb_checked.trans (by decide +kernel)
    · exact v2710_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 71 Primitive.Addresses.material2710
    · exact v2710_mb_checked.trans (by decide +kernel)
    · exact v2710_mg_checked.trans (by decide +kernel)
  upper_error := v2710_upper_checked
  lower_error := reuse_lower_error 33 71 Primitive.Addresses.material2710

def v2711_pa : Scalar.QComplex := ((999999165321518401366164314164 : Int)/10^30,(-1292035706359967447927933717 : Int)/10^30)
theorem v2711_pa_checked : Scalar.distance (sourceCoefficient 33 72 1 0) v2711_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2711_pb : Scalar.QComplex := ((-557484320370325596183276 : Int)/10^30,(-431477127378120488298637146 : Int)/10^30)
theorem v2711_pb_checked : Scalar.distance (sourceCoefficient 33 72 1 1) v2711_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2711_pg : Scalar.QComplex := ((-93086348588535498377598 : Int)/10^30,(120270986538663045952 : Int)/10^30)
theorem v2711_pg_checked : Scalar.distance (sourceCoefficient 33 72 1 2) v2711_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2711_mb : Scalar.QComplex := ((-929829440712322883091012 : Int)/10^30,(-431476485635606168680892362 : Int)/10^30)
theorem v2711_mb_checked : Scalar.distance (sourceCoefficient 33 72 3 1) v2711_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2711_mg : Scalar.QComplex := ((-93086210139789083857082 : Int)/10^30,(200600268134674999214 : Int)/10^30)
theorem v2711_mg_checked : Scalar.distance (sourceCoefficient 33 72 3 2) v2711_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2711_upper : Scalar.QComplex := ((999995446003813194973766582345 : Int)/10^30,(-3017941622153878415228709505 : Int)/10^30)
theorem v2711_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 72 5) 1) 14) v2711_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2711 : Material (33 : Basis) (72 : Basis) where
  plus := ![v2711_pa,v2711_pb,v2711_pg]
  minus := ![(Primitive.Addresses.material2711 1).one,v2711_mb,v2711_mg]
  upper := v2711_upper
  lower := (Primitive.Addresses.material2711 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2711_pa_checked.trans (by decide +kernel)
    · exact v2711_pb_checked.trans (by decide +kernel)
    · exact v2711_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 72 Primitive.Addresses.material2711
    · exact v2711_mb_checked.trans (by decide +kernel)
    · exact v2711_mg_checked.trans (by decide +kernel)
  upper_error := v2711_upper_checked
  lower_error := reuse_lower_error 33 72 Primitive.Addresses.material2711

def v2712_pa : Scalar.QComplex := ((999999153067594875299662955453 : Int)/10^30,(-1301485341044954614197815456 : Int)/10^30)
theorem v2712_pa_checked : Scalar.distance (sourceCoefficient 33 73 1 0) v2712_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2712_pb : Scalar.QComplex := ((-561561623786974919158984 : Int)/10^30,(-431477121157095976855403283 : Int)/10^30)
theorem v2712_pb_checked : Scalar.distance (sourceCoefficient 33 73 1 1) v2712_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2712_pg : Scalar.QComplex := ((-93086347347140411290720 : Int)/10^30,(121150619130107386604 : Int)/10^30)
theorem v2712_pg_checked : Scalar.distance (sourceCoefficient 33 73 1 2) v2712_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2712_mb : Scalar.QComplex := ((-933906737242341833244102 : Int)/10^30,(-431476475896054759970070138 : Int)/10^30)
theorem v2712_mb_checked : Scalar.distance (sourceCoefficient 33 73 3 1) v2712_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2712_mg : Scalar.QComplex := ((-93086208139311149763123 : Int)/10^30,(201479899327323875080 : Int)/10^30)
theorem v2712_mg_checked : Scalar.distance (sourceCoefficient 33 73 3 2) v2712_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2712_upper : Scalar.QComplex := ((999995417440695717561103244262 : Int)/10^30,(-3027391221615584411543440728 : Int)/10^30)
theorem v2712_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 73 5) 1) 14) v2712_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2712 : Material (33 : Basis) (73 : Basis) where
  plus := ![v2712_pa,v2712_pb,v2712_pg]
  minus := ![(Primitive.Addresses.material2712 1).one,v2712_mb,v2712_mg]
  upper := v2712_upper
  lower := (Primitive.Addresses.material2712 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2712_pa_checked.trans (by decide +kernel)
    · exact v2712_pb_checked.trans (by decide +kernel)
    · exact v2712_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 73 Primitive.Addresses.material2712
    · exact v2712_mb_checked.trans (by decide +kernel)
    · exact v2712_mg_checked.trans (by decide +kernel)
  upper_error := v2712_upper_checked
  lower_error := reuse_lower_error 33 73 Primitive.Addresses.material2712

def v2713_pa : Scalar.QComplex := ((999999139172146916677715593267 : Int)/10^30,(-1312118502705472835514470127 : Int)/10^30)
theorem v2713_pa_checked : Scalar.distance (sourceCoefficient 33 74 1 0) v2713_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2713_pb : Scalar.QComplex := ((-566149592255988253890370 : Int)/10^30,(-431477114095488034684502641 : Int)/10^30)
theorem v2713_pb_checked : Scalar.distance (sourceCoefficient 33 74 1 1) v2713_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2713_pg : Scalar.QComplex := ((-93086345938670281609852 : Int)/10^30,(122140421997248964778 : Int)/10^30)
theorem v2713_pg_checked : Scalar.distance (sourceCoefficient 33 74 1 2) v2713_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2713_mb : Scalar.QComplex := ((-938494697909195215366279 : Int)/10^30,(-431476464875239292829243705 : Int)/10^30)
theorem v2713_mb_checked : Scalar.distance (sourceCoefficient 33 74 3 1) v2713_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2713_mg : Scalar.QComplex := ((-93086205876686249243156 : Int)/10^30,(202469700610470322816 : Int)/10^30)
theorem v2713_mg_checked : Scalar.distance (sourceCoefficient 33 74 3 2) v2713_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2713_upper : Scalar.QComplex := ((999995385193396061412709875885 : Int)/10^30,(-3038024343456974807038626020 : Int)/10^30)
theorem v2713_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 74 5) 1) 14) v2713_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2713 : Material (33 : Basis) (74 : Basis) where
  plus := ![v2713_pa,v2713_pb,v2713_pg]
  minus := ![(Primitive.Addresses.material2713 1).one,v2713_mb,v2713_mg]
  upper := v2713_upper
  lower := (Primitive.Addresses.material2713 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2713_pa_checked.trans (by decide +kernel)
    · exact v2713_pb_checked.trans (by decide +kernel)
    · exact v2713_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 74 Primitive.Addresses.material2713
    · exact v2713_mb_checked.trans (by decide +kernel)
    · exact v2713_mg_checked.trans (by decide +kernel)
  upper_error := v2713_upper_checked
  lower_error := reuse_lower_error 33 74 Primitive.Addresses.material2713

def v2714_pa : Scalar.QComplex := ((999999119623198185268122303991 : Int)/10^30,(-1326933618748937486522939613 : Int)/10^30)
theorem v2714_pa_checked : Scalar.distance (sourceCoefficient 33 75 1 0) v2714_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2714_pb : Scalar.QComplex := ((-572541979267286195632252 : Int)/10^30,(-431477104148144512342438378 : Int)/10^30)
theorem v2714_pb_checked : Scalar.distance (sourceCoefficient 33 75 1 1) v2714_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2714_pg : Scalar.QComplex := ((-93086343955785526733494 : Int)/10^30,(123519507985068175116 : Int)/10^30)
theorem v2714_pg_checked : Scalar.distance (sourceCoefficient 33 75 1 2) v2714_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2714_mb : Scalar.QComplex := ((-944887073956205878223258 : Int)/10^30,(-431476449411557386011213675 : Int)/10^30)
theorem v2714_mb_checked : Scalar.distance (sourceCoefficient 33 75 3 1) v2714_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2714_mg : Scalar.QComplex := ((-93086202703713136924631 : Int)/10^30,(203848784373652554902 : Int)/10^30)
theorem v2714_mg_checked : Scalar.distance (sourceCoefficient 33 75 3 2) v2714_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2714_upper : Scalar.QComplex := ((999995340074930171674463360732 : Int)/10^30,(-3052839403695352373449169838 : Int)/10^30)
theorem v2714_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 75 5) 1) 14) v2714_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2714 : Material (33 : Basis) (75 : Basis) where
  plus := ![v2714_pa,v2714_pb,v2714_pg]
  minus := ![(Primitive.Addresses.material2714 1).one,v2714_mb,v2714_mg]
  upper := v2714_upper
  lower := (Primitive.Addresses.material2714 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2714_pa_checked.trans (by decide +kernel)
    · exact v2714_pb_checked.trans (by decide +kernel)
    · exact v2714_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 75 Primitive.Addresses.material2714
    · exact v2714_mb_checked.trans (by decide +kernel)
    · exact v2714_mg_checked.trans (by decide +kernel)
  upper_error := v2714_upper_checked
  lower_error := reuse_lower_error 33 75 Primitive.Addresses.material2714

def v2715_pa : Scalar.QComplex := ((999999103051913182882000211976 : Int)/10^30,(-1339363792671119490080032889 : Int)/10^30)
theorem v2715_pa_checked : Scalar.distance (sourceCoefficient 33 76 1 0) v2715_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2715_pb : Scalar.QComplex := ((-577905317704849292783691 : Int)/10^30,(-431477095704710171476554965 : Int)/10^30)
theorem v2715_pb_checked : Scalar.distance (sourceCoefficient 33 76 1 1) v2715_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2715_pg : Scalar.QComplex := ((-93086342273716573836498 : Int)/10^30,(124676588262034303344 : Int)/10^30)
theorem v2715_pg_checked : Scalar.distance (sourceCoefficient 33 76 1 2) v2715_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2715_mb : Scalar.QComplex := ((-950250403110449400393215 : Int)/10^30,(-431476436339806673201121725 : Int)/10^30)
theorem v2715_mb_checked : Scalar.distance (sourceCoefficient 33 76 3 1) v2715_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2715_mg : Scalar.QComplex := ((-93086200023136644278162 : Int)/10^30,(205005862768235066058 : Int)/10^30)
theorem v2715_mg_checked : Scalar.distance (sourceCoefficient 33 76 3 2) v2715_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2715_upper : Scalar.QComplex := ((999995302050317317154064947663 : Int)/10^30,(-3065269530503715891828626982 : Int)/10^30)
theorem v2715_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 76 5) 1) 14) v2715_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2715 : Material (33 : Basis) (76 : Basis) where
  plus := ![v2715_pa,v2715_pb,v2715_pg]
  minus := ![(Primitive.Addresses.material2715 1).one,v2715_mb,v2715_mg]
  upper := v2715_upper
  lower := (Primitive.Addresses.material2715 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2715_pa_checked.trans (by decide +kernel)
    · exact v2715_pb_checked.trans (by decide +kernel)
    · exact v2715_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 76 Primitive.Addresses.material2715
    · exact v2715_mb_checked.trans (by decide +kernel)
    · exact v2715_mg_checked.trans (by decide +kernel)
  upper_error := v2715_upper_checked
  lower_error := reuse_lower_error 33 76 Primitive.Addresses.material2715

def v2716_pa : Scalar.QComplex := ((999999099193494237663438704872 : Int)/10^30,(-1342241483516402237276514427 : Int)/10^30)
theorem v2716_pa_checked : Scalar.distance (sourceCoefficient 33 77 1 0) v2716_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2716_pb : Scalar.QComplex := ((-579146976100679201748795 : Int)/10^30,(-431477093737311947713811233 : Int)/10^30)
theorem v2716_pb_checked : Scalar.distance (sourceCoefficient 33 77 1 1) v2716_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2716_pg : Scalar.QComplex := ((-93086341881911314250172 : Int)/10^30,(124944462173476033365 : Int)/10^30)
theorem v2716_pg_checked : Scalar.distance (sourceCoefficient 33 77 1 2) v2716_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2716_mb : Scalar.QComplex := ((-951492059346177083218271 : Int)/10^30,(-431476433300913908607657663 : Int)/10^30)
theorem v2716_mb_checked : Scalar.distance (sourceCoefficient 33 77 3 1) v2716_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2716_mg : Scalar.QComplex := ((-93086199400168409597741 : Int)/10^30,(205273736241824803637 : Int)/10^30)
theorem v2716_mg_checked : Scalar.distance (sourceCoefficient 33 77 3 2) v2716_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2716_upper : Scalar.QComplex := ((999995293225270781713437995796 : Int)/10^30,(-3068147210403735095874134626 : Int)/10^30)
theorem v2716_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 77 5) 1) 14) v2716_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2716 : Material (33 : Basis) (77 : Basis) where
  plus := ![v2716_pa,v2716_pb,v2716_pg]
  minus := ![(Primitive.Addresses.material2716 1).one,v2716_mb,v2716_mg]
  upper := v2716_upper
  lower := (Primitive.Addresses.material2716 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2716_pa_checked.trans (by decide +kernel)
    · exact v2716_pb_checked.trans (by decide +kernel)
    · exact v2716_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 77 Primitive.Addresses.material2716
    · exact v2716_mb_checked.trans (by decide +kernel)
    · exact v2716_mg_checked.trans (by decide +kernel)
  upper_error := v2716_upper_checked
  lower_error := reuse_lower_error 33 77 Primitive.Addresses.material2716

def v2717_pa : Scalar.QComplex := ((999999075823630136436749358414 : Int)/10^30,(-1359541056983997040145752544 : Int)/10^30)
theorem v2717_pa_checked : Scalar.distance (sourceCoefficient 33 78 1 0) v2717_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2717_pb : Scalar.QComplex := ((-586611350000225310129375 : Int)/10^30,(-431477081809661196995555144 : Int)/10^30)
theorem v2717_pb_checked : Scalar.distance (sourceCoefficient 33 78 1 1) v2717_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2717_pg : Scalar.QComplex := ((-93086339507574350074541 : Int)/10^30,(126554817363870534540 : Int)/10^30)
theorem v2717_pg_checked : Scalar.distance (sourceCoefficient 33 78 1 2) v2717_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2717_mb : Scalar.QComplex := ((-958956420173370253636132 : Int)/10^30,(-431476414931849106711344029 : Int)/10^30)
theorem v2717_mb_checked : Scalar.distance (sourceCoefficient 33 78 3 1) v2717_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2717_mg : Scalar.QComplex := ((-93086195636168327891240 : Int)/10^30,(206884088783664606644 : Int)/10^30)
theorem v2717_mg_checked : Scalar.distance (sourceCoefficient 33 78 3 2) v2717_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2717_upper : Scalar.QComplex := ((999995239997947087130941363955 : Int)/10^30,(-3085446717771382028203919480 : Int)/10^30)
theorem v2717_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 78 5) 1) 14) v2717_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2717 : Material (33 : Basis) (78 : Basis) where
  plus := ![v2717_pa,v2717_pb,v2717_pg]
  minus := ![(Primitive.Addresses.material2717 1).one,v2717_mb,v2717_mg]
  upper := v2717_upper
  lower := (Primitive.Addresses.material2717 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2717_pa_checked.trans (by decide +kernel)
    · exact v2717_pb_checked.trans (by decide +kernel)
    · exact v2717_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 78 Primitive.Addresses.material2717
    · exact v2717_mb_checked.trans (by decide +kernel)
    · exact v2717_mg_checked.trans (by decide +kernel)
  upper_error := v2717_upper_checked
  lower_error := reuse_lower_error 33 78 Primitive.Addresses.material2717

def v2718_pa : Scalar.QComplex := ((999999068225807541548632619016 : Int)/10^30,(-1365118132878527477646523372 : Int)/10^30)
theorem v2718_pa_checked : Scalar.distance (sourceCoefficient 33 79 1 0) v2718_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2718_pb : Scalar.QComplex := ((-589017731832063315042881 : Int)/10^30,(-431477077927697926569851297 : Int)/10^30)
theorem v2718_pb_checked : Scalar.distance (sourceCoefficient 33 79 1 1) v2718_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2718_pg : Scalar.QComplex := ((-93086338735202267652460 : Int)/10^30,(127073967334940764638 : Int)/10^30)
theorem v2718_pg_checked : Scalar.distance (sourceCoefficient 33 79 1 2) v2718_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2718_mb : Scalar.QComplex := ((-961362797759242860231714 : Int)/10^30,(-431476408973288140256255011 : Int)/10^30)
theorem v2718_mb_checked : Scalar.distance (sourceCoefficient 33 79 3 1) v2718_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2718_mg : Scalar.QComplex := ((-93086194415793489671705 : Int)/10^30,(207403237894909255404 : Int)/10^30)
theorem v2718_mg_checked : Scalar.distance (sourceCoefficient 33 79 3 2) v2718_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2718_upper : Scalar.QComplex := ((999995222774608762720441652585 : Int)/10^30,(-3091023772246360520461146534 : Int)/10^30)
theorem v2718_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 79 5) 1) 14) v2718_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2718 : Material (33 : Basis) (79 : Basis) where
  plus := ![v2718_pa,v2718_pb,v2718_pg]
  minus := ![(Primitive.Addresses.material2718 1).one,v2718_mb,v2718_mg]
  upper := v2718_upper
  lower := (Primitive.Addresses.material2718 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2718_pa_checked.trans (by decide +kernel)
    · exact v2718_pb_checked.trans (by decide +kernel)
    · exact v2718_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 79 Primitive.Addresses.material2718
    · exact v2718_mb_checked.trans (by decide +kernel)
    · exact v2718_mg_checked.trans (by decide +kernel)
  upper_error := v2718_upper_checked
  lower_error := reuse_lower_error 33 79 Primitive.Addresses.material2718

def v2719_pa : Scalar.QComplex := ((999999056295015041889829551523 : Int)/10^30,(-1373830076587756796847324479 : Int)/10^30)
theorem v2719_pa_checked : Scalar.distance (sourceCoefficient 33 80 1 0) v2719_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2719_pb : Scalar.QComplex := ((-592776738041519019443507 : Int)/10^30,(-431477071827879229515113935 : Int)/10^30)
theorem v2719_pb_checked : Scalar.distance (sourceCoefficient 33 80 1 1) v2719_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2719_pg : Scalar.QComplex := ((-93086337521921133700830 : Int)/10^30,(127884930892661474778 : Int)/10^30)
theorem v2719_pg_checked : Scalar.distance (sourceCoefficient 33 80 1 2) v2719_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2719_mb : Scalar.QComplex := ((-965121797305179947858942 : Int)/10^30,(-431476399629618655037507564 : Int)/10^30)
theorem v2719_mb_checked : Scalar.distance (sourceCoefficient 33 80 3 1) v2719_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2719_mg : Scalar.QComplex := ((-93086192502687781609908 : Int)/10^30,(208214200103664195693 : Int)/10^30)
theorem v2719_mg_checked : Scalar.distance (sourceCoefficient 33 80 3 2) v2719_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2719_upper : Scalar.QComplex := ((999995195807809531805265942151 : Int)/10^30,(-3099735682388707560190858807 : Int)/10^30)
theorem v2719_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 80 5) 1) 14) v2719_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2719 : Material (33 : Basis) (80 : Basis) where
  plus := ![v2719_pa,v2719_pb,v2719_pg]
  minus := ![(Primitive.Addresses.material2719 1).one,v2719_mb,v2719_mg]
  upper := v2719_upper
  lower := (Primitive.Addresses.material2719 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2719_pa_checked.trans (by decide +kernel)
    · exact v2719_pb_checked.trans (by decide +kernel)
    · exact v2719_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 80 Primitive.Addresses.material2719
    · exact v2719_mb_checked.trans (by decide +kernel)
    · exact v2719_mg_checked.trans (by decide +kernel)
  upper_error := v2719_upper_checked
  lower_error := reuse_lower_error 33 80 Primitive.Addresses.material2719

def v2720_pa : Scalar.QComplex := ((999999019912450673200841819053 : Int)/10^30,(-1400062190790821252849318870 : Int)/10^30)
theorem v2720_pa_checked : Scalar.distance (sourceCoefficient 33 81 1 0) v2720_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2720_pb : Scalar.QComplex := ((-604095300441704913904365 : Int)/10^30,(-431477053197330555989157698 : Int)/10^30)
theorem v2720_pb_checked : Scalar.distance (sourceCoefficient 33 81 1 1) v2720_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2720_pg : Scalar.QComplex := ((-93086333818893783815430 : Int)/10^30,(130326784190824674708 : Int)/10^30)
theorem v2720_pg_checked : Scalar.distance (sourceCoefficient 33 81 1 2) v2720_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2720_mb : Scalar.QComplex := ((-976440339413623360385479 : Int)/10^30,(-431476371231667336282838570 : Int)/10^30)
theorem v2720_mb_checked : Scalar.distance (sourceCoefficient 33 81 3 1) v2720_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2720_mg : Scalar.QComplex := ((-93086186692452391205996 : Int)/10^30,(210656049297067989717 : Int)/10^30)
theorem v2720_mg_checked : Scalar.distance (sourceCoefficient 33 81 3 2) v2720_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2720_upper : Scalar.QComplex := ((999995114151049994993704431441 : Int)/10^30,(-3125967694729113851421492417 : Int)/10^30)
theorem v2720_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 81 5) 1) 14) v2720_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2720 : Material (33 : Basis) (81 : Basis) where
  plus := ![v2720_pa,v2720_pb,v2720_pg]
  minus := ![(Primitive.Addresses.material2720 1).one,v2720_mb,v2720_mg]
  upper := v2720_upper
  lower := (Primitive.Addresses.material2720 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2720_pa_checked.trans (by decide +kernel)
    · exact v2720_pb_checked.trans (by decide +kernel)
    · exact v2720_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 81 Primitive.Addresses.material2720
    · exact v2720_mb_checked.trans (by decide +kernel)
    · exact v2720_mg_checked.trans (by decide +kernel)
  upper_error := v2720_upper_checked
  lower_error := reuse_lower_error 33 81 Primitive.Addresses.material2720

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
