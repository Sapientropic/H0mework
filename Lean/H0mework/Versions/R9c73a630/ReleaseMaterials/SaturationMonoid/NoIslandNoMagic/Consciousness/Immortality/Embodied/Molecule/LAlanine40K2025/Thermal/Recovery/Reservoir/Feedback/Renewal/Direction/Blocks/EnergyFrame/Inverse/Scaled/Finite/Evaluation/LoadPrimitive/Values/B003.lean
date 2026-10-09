import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B002

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v49_pa : Scalar.QComplex := ((999973599383519684893705672714 : Int)/10^30,(7266397729830075293926585251 : Int)/10^30)
theorem v49_pa_checked : Scalar.distance (sourceCoefficient 0 50 1 0) v49_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v49_pb : Scalar.QComplex := ((3135250215129824969538648 : Int)/10^30,(-431461029131506319315725752 : Int)/10^30)
theorem v49_pb_checked : Scalar.distance (sourceCoefficient 0 50 1 1) v49_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v49_pg : Scalar.QComplex := ((-93083422158976350740844 : Int)/10^30,(-676399024812042002859 : Int)/10^30)
theorem v49_pg_checked : Scalar.distance (sourceCoefficient 0 50 1 2) v49_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v49_mb : Scalar.QComplex := ((2762917611875783725437818 : Int)/10^30,(-431463574058575659677435145 : Int)/10^30)
theorem v49_mb_checked : Scalar.distance (sourceCoefficient 0 50 3 1) v49_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v49_mg : Scalar.QComplex := ((-93083971201658689990507 : Int)/10^30,(-596071971956283255307 : Int)/10^30)
theorem v49_mg_checked : Scalar.distance (sourceCoefficient 0 50 3 2) v49_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v49_upper : Scalar.QComplex := ((999984651183587787668237050652 : Int)/10^30,(5540523191744567341502178646 : Int)/10^30)
theorem v49_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 50 5) 1) 14) v49_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material49 : Material (0 : Basis) (50 : Basis) where
  plus := ![v49_pa,v49_pb,v49_pg]
  minus := ![(Primitive.Addresses.material49 1).one,v49_mb,v49_mg]
  upper := v49_upper
  lower := (Primitive.Addresses.material49 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v49_pa_checked.trans (by decide +kernel)
    · exact v49_pb_checked.trans (by decide +kernel)
    · exact v49_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 50 Primitive.Addresses.material49
    · exact v49_mb_checked.trans (by decide +kernel)
    · exact v49_mg_checked.trans (by decide +kernel)
  upper_error := v49_upper_checked
  lower_error := reuse_lower_error 0 50 Primitive.Addresses.material49

def v50_pa : Scalar.QComplex := ((999973681424533100992372263347 : Int)/10^30,(7255098777162403899696042906 : Int)/10^30)
theorem v50_pa_checked : Scalar.distance (sourceCoefficient 0 51 1 0) v50_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v50_pb : Scalar.QComplex := ((3130374929311222543579296 : Int)/10^30,(-431461050834475057664672792 : Int)/10^30)
theorem v50_pb_checked : Scalar.distance (sourceCoefficient 0 51 1 1) v50_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v50_pg : Scalar.QComplex := ((-93083428318511285255168 : Int)/10^30,(-675347241145047941858 : Int)/10^30)
theorem v50_pg_checked : Scalar.distance (sourceCoefficient 0 51 1 2) v50_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v50_mb : Scalar.QComplex := ((2758042309143788465544787 : Int)/10^30,(-431463591554384230287625645 : Int)/10^30)
theorem v50_mb_checked : Scalar.distance (sourceCoefficient 0 51 3 1) v50_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v50_mg : Scalar.QComplex := ((-93083976453549396990479 : Int)/10^30,(-595020183365515089086 : Int)/10^30)
theorem v50_mg_checked : Scalar.distance (sourceCoefficient 0 51 3 2) v50_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v50_upper : Scalar.QComplex := ((999984713723511741892701269189 : Int)/10^30,(5529224114310012223963934191 : Int)/10^30)
theorem v50_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 51 5) 1) 14) v50_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material50 : Material (0 : Basis) (51 : Basis) where
  plus := ![v50_pa,v50_pb,v50_pg]
  minus := ![(Primitive.Addresses.material50 1).one,v50_mb,v50_mg]
  upper := v50_upper
  lower := (Primitive.Addresses.material50 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v50_pa_checked.trans (by decide +kernel)
    · exact v50_pb_checked.trans (by decide +kernel)
    · exact v50_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 51 Primitive.Addresses.material50
    · exact v50_mb_checked.trans (by decide +kernel)
    · exact v50_mg_checked.trans (by decide +kernel)
  upper_error := v50_upper_checked
  lower_error := reuse_lower_error 0 51 Primitive.Addresses.material50

def v51_pa : Scalar.QComplex := ((999973856625080352773875625918 : Int)/10^30,(7230910479548357885972415489 : Int)/10^30)
theorem v51_pa_checked : Scalar.distance (sourceCoefficient 0 52 1 0) v51_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v51_pb : Scalar.QComplex := ((3119938133876342153658776 : Int)/10^30,(-431461097048299804413725338 : Int)/10^30)
theorem v51_pb_checked : Scalar.distance (sourceCoefficient 0 52 1 1) v51_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v51_pg : Scalar.QComplex := ((-93083441457957376094684 : Int)/10^30,(-673095629302163690268 : Int)/10^30)
theorem v51_pg_checked : Scalar.distance (sourceCoefficient 0 52 1 2) v51_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v51_mb : Scalar.QComplex := ((2747605477714554638102358 : Int)/10^30,(-431463628761707365032967217 : Int)/10^30)
theorem v51_mb_checked : Scalar.distance (sourceCoefficient 0 52 3 1) v51_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v51_mg : Scalar.QComplex := ((-93083987649950983837534 : Int)/10^30,(-592768561022258632636 : Int)/10^30)
theorem v51_mg_checked : Scalar.distance (sourceCoefficient 0 52 3 2) v51_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v51_upper : Scalar.QComplex := ((999984847176990716414417493236 : Int)/10^30,(5505035550341343662243802576 : Int)/10^30)
theorem v51_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 52 5) 1) 14) v51_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material51 : Material (0 : Basis) (52 : Basis) where
  plus := ![v51_pa,v51_pb,v51_pg]
  minus := ![(Primitive.Addresses.material51 1).one,v51_mb,v51_mg]
  upper := v51_upper
  lower := (Primitive.Addresses.material51 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v51_pa_checked.trans (by decide +kernel)
    · exact v51_pb_checked.trans (by decide +kernel)
    · exact v51_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 52 Primitive.Addresses.material51
    · exact v51_mb_checked.trans (by decide +kernel)
    · exact v51_mg_checked.trans (by decide +kernel)
  upper_error := v51_upper_checked
  lower_error := reuse_lower_error 0 52 Primitive.Addresses.material51

def v52_pa : Scalar.QComplex := ((999973883392044615411089753817 : Int)/10^30,(7227207886421842962240535942 : Int)/10^30)
theorem v52_pa_checked : Scalar.distance (sourceCoefficient 0 53 1 0) v52_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v52_pb : Scalar.QComplex := ((3118340534660363035726367 : Int)/10^30,(-431461104092715328379119772 : Int)/10^30)
theorem v52_pb_checked : Scalar.distance (sourceCoefficient 0 53 1 1) v52_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v52_pg : Scalar.QComplex := ((-93083443463653564852540 : Int)/10^30,(-672750966669066895825 : Int)/10^30)
theorem v52_pg_checked : Scalar.distance (sourceCoefficient 0 53 1 2) v52_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v52_mb : Scalar.QComplex := ((2746007873014421393685601 : Int)/10^30,(-431463634427464095848197058 : Int)/10^30)
theorem v52_mb_checked : Scalar.distance (sourceCoefficient 0 53 3 1) v52_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v52_mg : Scalar.QComplex := ((-93083989358218096449253 : Int)/10^30,(-592423896786670010660 : Int)/10^30)
theorem v52_mg_checked : Scalar.distance (sourceCoefficient 0 53 3 2) v52_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v52_upper : Scalar.QComplex := ((999984867553575273062429554064 : Int)/10^30,(5501332916532054226031985941 : Int)/10^30)
theorem v52_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 53 5) 1) 14) v52_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material52 : Material (0 : Basis) (53 : Basis) where
  plus := ![v52_pa,v52_pb,v52_pg]
  minus := ![(Primitive.Addresses.material52 1).one,v52_mb,v52_mg]
  upper := v52_upper
  lower := (Primitive.Addresses.material52 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v52_pa_checked.trans (by decide +kernel)
    · exact v52_pb_checked.trans (by decide +kernel)
    · exact v52_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 53 Primitive.Addresses.material52
    · exact v52_mb_checked.trans (by decide +kernel)
    · exact v52_mg_checked.trans (by decide +kernel)
  upper_error := v52_upper_checked
  lower_error := reuse_lower_error 0 53 Primitive.Addresses.material52

def v53_pa : Scalar.QComplex := ((999973896995274857163069598718 : Int)/10^30,(7225325465571083395909326288 : Int)/10^30)
theorem v53_pa_checked : Scalar.distance (sourceCoefficient 0 54 1 0) v53_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v53_pb : Scalar.QComplex := ((3117528305515701197974267 : Int)/10^30,(-431461107671114616082216995 : Int)/10^30)
theorem v53_pb_checked : Scalar.distance (sourceCoefficient 0 54 1 1) v53_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v53_pg : Scalar.QComplex := ((-93083444482790777818100 : Int)/10^30,(-672575738092249809242 : Int)/10^30)
theorem v53_pg_checked : Scalar.distance (sourceCoefficient 0 54 1 2) v53_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v53_mb : Scalar.QComplex := ((2745195641084192167030229 : Int)/10^30,(-431463637304944880749241147 : Int)/10^30)
theorem v53_mb_checked : Scalar.distance (sourceCoefficient 0 54 3 1) v53_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v53_mg : Scalar.QComplex := ((-93083990226140560152441 : Int)/10^30,(-592248667395629017015 : Int)/10^30)
theorem v53_mg_checked : Scalar.distance (sourceCoefficient 0 54 3 2) v53_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v53_upper : Scalar.QComplex := ((999984877907897637875484640892 : Int)/10^30,(5499450475006998070364404584 : Int)/10^30)
theorem v53_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 54 5) 1) 14) v53_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material53 : Material (0 : Basis) (54 : Basis) where
  plus := ![v53_pa,v53_pb,v53_pg]
  minus := ![(Primitive.Addresses.material53 1).one,v53_mb,v53_mg]
  upper := v53_upper
  lower := (Primitive.Addresses.material53 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v53_pa_checked.trans (by decide +kernel)
    · exact v53_pb_checked.trans (by decide +kernel)
    · exact v53_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 54 Primitive.Addresses.material53
    · exact v53_mb_checked.trans (by decide +kernel)
    · exact v53_mg_checked.trans (by decide +kernel)
  upper_error := v53_upper_checked
  lower_error := reuse_lower_error 0 54 Primitive.Addresses.material53

def v54_pa : Scalar.QComplex := ((999974007740040086504210593936 : Int)/10^30,(7209982269204908929398672179 : Int)/10^30)
theorem v54_pa_checked : Scalar.distance (sourceCoefficient 0 55 1 0) v54_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v54_pb : Scalar.QComplex := ((3110908005433349893798508 : Int)/10^30,(-431461136761826210611899677 : Int)/10^30)
theorem v54_pb_checked : Scalar.distance (sourceCoefficient 0 55 1 1) v54_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v54_pg : Scalar.QComplex := ((-93083452775200563117520 : Int)/10^30,(-671147488705566411838 : Int)/10^30)
theorem v54_pg_checked : Scalar.distance (sourceCoefficient 0 55 1 2) v54_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v54_mb : Scalar.QComplex := ((2738575318362907237108825 : Int)/10^30,(-431463660682624839655531090 : Int)/10^30)
theorem v54_mb_checked : Scalar.distance (sourceCoefficient 0 55 3 1) v54_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v54_mg : Scalar.QComplex := ((-93083997286032363065428 : Int)/10^30,(-590820411384771972053 : Int)/10^30)
theorem v54_mg_checked : Scalar.distance (sourceCoefficient 0 55 3 2) v54_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v54_upper : Scalar.QComplex := ((999984962171532921781907821072 : Int)/10^30,(5484107110357294153596464018 : Int)/10^30)
theorem v54_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 55 5) 1) 14) v54_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material54 : Material (0 : Basis) (55 : Basis) where
  plus := ![v54_pa,v54_pb,v54_pg]
  minus := ![(Primitive.Addresses.material54 1).one,v54_mb,v54_mg]
  upper := v54_upper
  lower := (Primitive.Addresses.material54 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v54_pa_checked.trans (by decide +kernel)
    · exact v54_pb_checked.trans (by decide +kernel)
    · exact v54_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 55 Primitive.Addresses.material54
    · exact v54_mb_checked.trans (by decide +kernel)
    · exact v54_mg_checked.trans (by decide +kernel)
  upper_error := v54_upper_checked
  lower_error := reuse_lower_error 0 55 Primitive.Addresses.material54

def v55_pa : Scalar.QComplex := ((999974033988300459230056016141 : Int)/10^30,(7206340899882405590874135952 : Int)/10^30)
theorem v55_pa_checked : Scalar.distance (sourceCoefficient 0 56 1 0) v55_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v55_pb : Scalar.QComplex := ((3109336823242382725133259 : Int)/10^30,(-431461143645978504672214970 : Int)/10^30)
theorem v55_pb_checked : Scalar.distance (sourceCoefficient 0 56 1 1) v55_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v55_pg : Scalar.QComplex := ((-93083454739467119774563 : Int)/10^30,(-670808525213388498112 : Int)/10^30)
theorem v55_pg_checked : Scalar.distance (sourceCoefficient 0 56 1 2) v55_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v55_mb : Scalar.QComplex := ((2737004130816249625649745 : Int)/10^30,(-431463666210915103045679014 : Int)/10^30)
theorem v55_mb_checked : Scalar.distance (sourceCoefficient 0 56 3 1) v55_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v55_mg : Scalar.QComplex := ((-93083998957787960935696 : Int)/10^30,(-590481446323732086749 : Int)/10^30)
theorem v55_mg_checked : Scalar.distance (sourceCoefficient 0 56 3 2) v55_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v55_upper : Scalar.QComplex := ((999984982135081092610946971000 : Int)/10^30,(5480465701156066495907668308 : Int)/10^30)
theorem v55_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 56 5) 1) 14) v55_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material55 : Material (0 : Basis) (56 : Basis) where
  plus := ![v55_pa,v55_pb,v55_pg]
  minus := ![(Primitive.Addresses.material55 1).one,v55_mb,v55_mg]
  upper := v55_upper
  lower := (Primitive.Addresses.material55 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v55_pa_checked.trans (by decide +kernel)
    · exact v55_pb_checked.trans (by decide +kernel)
    · exact v55_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 56 Primitive.Addresses.material55
    · exact v55_mb_checked.trans (by decide +kernel)
    · exact v55_mg_checked.trans (by decide +kernel)
  upper_error := v55_upper_checked
  lower_error := reuse_lower_error 0 56 Primitive.Addresses.material55

def v56_pa : Scalar.QComplex := ((999974118794191266048730560930 : Int)/10^30,(7194563348852645170852595059 : Int)/10^30)
theorem v56_pa_checked : Scalar.distance (sourceCoefficient 0 57 1 0) v56_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v56_pb : Scalar.QComplex := ((3104255032210535034444999 : Int)/10^30,(-431461165859662997864258048 : Int)/10^30)
theorem v56_pb_checked : Scalar.distance (sourceCoefficient 0 57 1 1) v56_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v56_pg : Scalar.QComplex := ((-93083461082778705233578 : Int)/10^30,(-669712190449544872946 : Int)/10^30)
theorem v56_pg_checked : Scalar.distance (sourceCoefficient 0 57 1 2) v56_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v56_mb : Scalar.QComplex := ((2731922322507175735027638 : Int)/10^30,(-431463684039234539955033927 : Int)/10^30)
theorem v56_mb_checked : Scalar.distance (sourceCoefficient 0 57 3 1) v56_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v56_mg : Scalar.QComplex := ((-93084004355009660377656 : Int)/10^30,(-589385106494111793033 : Int)/10^30)
theorem v56_mg_checked : Scalar.distance (sourceCoefficient 0 57 3 2) v56_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v56_upper : Scalar.QComplex := ((999985046613860964733917563025 : Int)/10^30,(5468688021300310844131964501 : Int)/10^30)
theorem v56_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 57 5) 1) 14) v56_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material56 : Material (0 : Basis) (57 : Basis) where
  plus := ![v56_pa,v56_pb,v56_pg]
  minus := ![(Primitive.Addresses.material56 1).one,v56_mb,v56_mg]
  upper := v56_upper
  lower := (Primitive.Addresses.material56 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v56_pa_checked.trans (by decide +kernel)
    · exact v56_pb_checked.trans (by decide +kernel)
    · exact v56_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 57 Primitive.Addresses.material56
    · exact v56_mb_checked.trans (by decide +kernel)
    · exact v56_mg_checked.trans (by decide +kernel)
  upper_error := v56_upper_checked
  lower_error := reuse_lower_error 0 57 Primitive.Addresses.material56

def v57_pa : Scalar.QComplex := ((999974164750991124400306388039 : Int)/10^30,(7188172963810751874635317382 : Int)/10^30)
theorem v57_pa_checked : Scalar.distance (sourceCoefficient 0 58 1 0) v57_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v57_pb : Scalar.QComplex := ((3101497701730590983381095 : Int)/10^30,(-431461177879194329478762192 : Int)/10^30)
theorem v57_pb_checked : Scalar.distance (sourceCoefficient 0 58 1 1) v57_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v57_pg : Scalar.QComplex := ((-93083464518293355796847 : Int)/10^30,(-669117329841066310293 : Int)/10^30)
theorem v57_pg_checked : Scalar.distance (sourceCoefficient 0 58 1 2) v57_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v57_mb : Scalar.QComplex := ((2729164982681597638287554 : Int)/10^30,(-431463693679309377511819715 : Int)/10^30)
theorem v57_mb_checked : Scalar.distance (sourceCoefficient 0 58 3 1) v57_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v57_mg : Scalar.QComplex := ((-93084007277185118152068 : Int)/10^30,(-588790243142432607790 : Int)/10^30)
theorem v57_mg_checked : Scalar.distance (sourceCoefficient 0 58 3 2) v57_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v57_upper : Scalar.QComplex := ((999985081541367524725128966972 : Int)/10^30,(5462297566458878013256799035 : Int)/10^30)
theorem v57_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 58 5) 1) 14) v57_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material57 : Material (0 : Basis) (58 : Basis) where
  plus := ![v57_pa,v57_pb,v57_pg]
  minus := ![(Primitive.Addresses.material57 1).one,v57_mb,v57_mg]
  upper := v57_upper
  lower := (Primitive.Addresses.material57 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v57_pa_checked.trans (by decide +kernel)
    · exact v57_pb_checked.trans (by decide +kernel)
    · exact v57_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 58 Primitive.Addresses.material57
    · exact v57_mb_checked.trans (by decide +kernel)
    · exact v57_mg_checked.trans (by decide +kernel)
  upper_error := v57_upper_checked
  lower_error := reuse_lower_error 0 58 Primitive.Addresses.material57

def v58_pa : Scalar.QComplex := ((999974290863635915826368893596 : Int)/10^30,(7170607489500158116084509663 : Int)/10^30)
theorem v58_pa_checked : Scalar.distance (sourceCoefficient 0 59 1 0) v58_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v58_pb : Scalar.QComplex := ((3093918531540683402210342 : Int)/10^30,(-431461210796648840161301147 : Int)/10^30)
theorem v58_pb_checked : Scalar.distance (sourceCoefficient 0 59 1 1) v58_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v58_pg : Scalar.QComplex := ((-93083473938761297946562 : Int)/10^30,(-667482215765280256048 : Int)/10^30)
theorem v58_pg_checked : Scalar.distance (sourceCoefficient 0 59 1 2) v58_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v58_mb : Scalar.QComplex := ((2721585786907480808406241 : Int)/10^30,(-431463720056269110785128538 : Int)/10^30)
theorem v58_mb_checked : Scalar.distance (sourceCoefficient 0 59 3 1) v58_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v58_mg : Scalar.QComplex := ((-93084015286619748031890 : Int)/10^30,(-587155121546034700415 : Int)/10^30)
theorem v58_mg_checked : Scalar.distance (sourceCoefficient 0 59 3 2) v58_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v58_upper : Scalar.QComplex := ((999985177337409353477683570036 : Int)/10^30,(5444731900651010794541022900 : Int)/10^30)
theorem v58_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 59 5) 1) 14) v58_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material58 : Material (0 : Basis) (59 : Basis) where
  plus := ![v58_pa,v58_pb,v58_pg]
  minus := ![(Primitive.Addresses.material58 1).one,v58_mb,v58_mg]
  upper := v58_upper
  lower := (Primitive.Addresses.material58 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v58_pa_checked.trans (by decide +kernel)
    · exact v58_pb_checked.trans (by decide +kernel)
    · exact v58_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 59 Primitive.Addresses.material58
    · exact v58_mb_checked.trans (by decide +kernel)
    · exact v58_mg_checked.trans (by decide +kernel)
  upper_error := v58_upper_checked
  lower_error := reuse_lower_error 0 59 Primitive.Addresses.material58

def v59_pa : Scalar.QComplex := ((999974435963017410031579591018 : Int)/10^30,(7150344078797403551785046820 : Int)/10^30)
theorem v59_pa_checked : Scalar.distance (sourceCoefficient 0 60 1 0) v59_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v59_pb : Scalar.QComplex := ((3085175253330633977128372 : Int)/10^30,(-431461248549487121530903843 : Int)/10^30)
theorem v59_pb_checked : Scalar.distance (sourceCoefficient 0 60 1 1) v59_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v59_pg : Scalar.QComplex := ((-93083484764521983161848 : Int)/10^30,(-665595959439550663292 : Int)/10^30)
theorem v59_pg_checked : Scalar.distance (sourceCoefficient 0 60 1 2) v59_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v59_mb : Scalar.QComplex := ((2712842479373954336375103 : Int)/10^30,(-431463750264038022407677469 : Int)/10^30)
theorem v59_mb_checked : Scalar.distance (sourceCoefficient 0 60 3 1) v59_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v59_mg : Scalar.QComplex := ((-93084024484622147048349 : Int)/10^30,(-585268856580500646722 : Int)/10^30)
theorem v59_mg_checked : Scalar.distance (sourceCoefficient 0 60 3 2) v59_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v59_upper : Scalar.QComplex := ((999985287463766148503432266878 : Int)/10^30,(5424468269699857018630662833 : Int)/10^30)
theorem v59_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 60 5) 1) 14) v59_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material59 : Material (0 : Basis) (60 : Basis) where
  plus := ![v59_pa,v59_pb,v59_pg]
  minus := ![(Primitive.Addresses.material59 1).one,v59_mb,v59_mg]
  upper := v59_upper
  lower := (Primitive.Addresses.material59 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v59_pa_checked.trans (by decide +kernel)
    · exact v59_pb_checked.trans (by decide +kernel)
    · exact v59_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 60 Primitive.Addresses.material59
    · exact v59_mb_checked.trans (by decide +kernel)
    · exact v59_mg_checked.trans (by decide +kernel)
  upper_error := v59_upper_checked
  lower_error := reuse_lower_error 0 60 Primitive.Addresses.material59

def v60_pa : Scalar.QComplex := ((999974477842117456505988718513 : Int)/10^30,(7144484892876743045171551342 : Int)/10^30)
theorem v60_pa_checked : Scalar.distance (sourceCoefficient 0 61 1 0) v60_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v60_pb : Scalar.QComplex := ((3082647125606751426492784 : Int)/10^30,(-431461259421728911347052085 : Int)/10^30)
theorem v60_pb_checked : Scalar.distance (sourceCoefficient 0 61 1 1) v60_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v60_pg : Scalar.QComplex := ((-93083487886490096200514 : Int)/10^30,(-665050546506351610777 : Int)/10^30)
theorem v60_pg_checked : Scalar.distance (sourceCoefficient 0 61 1 2) v60_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v60_mb : Scalar.QComplex := ((2710314343209154281467380 : Int)/10^30,(-431463758954615400926583741 : Int)/10^30)
theorem v60_mb_checked : Scalar.distance (sourceCoefficient 0 61 3 1) v60_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v60_mg : Scalar.QComplex := ((-93084027135922300771458 : Int)/10^30,(-584723441156265882511 : Int)/10^30)
theorem v60_mg_checked : Scalar.distance (sourceCoefficient 0 61 3 2) v60_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v60_upper : Scalar.QComplex := ((999985319230380463112302794699 : Int)/10^30,(5418609020226238234577872233 : Int)/10^30)
theorem v60_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 61 5) 1) 14) v60_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material60 : Material (0 : Basis) (61 : Basis) where
  plus := ![v60_pa,v60_pb,v60_pg]
  minus := ![(Primitive.Addresses.material60 1).one,v60_mb,v60_mg]
  upper := v60_upper
  lower := (Primitive.Addresses.material60 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v60_pa_checked.trans (by decide +kernel)
    · exact v60_pb_checked.trans (by decide +kernel)
    · exact v60_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 61 Primitive.Addresses.material60
    · exact v60_mb_checked.trans (by decide +kernel)
    · exact v60_mg_checked.trans (by decide +kernel)
  upper_error := v60_upper_checked
  lower_error := reuse_lower_error 0 61 Primitive.Addresses.material60

def v61_pa : Scalar.QComplex := ((999974538629474780384874516004 : Int)/10^30,(7135971746654425181657657963 : Int)/10^30)
theorem v61_pa_checked : Scalar.distance (sourceCoefficient 0 62 1 0) v61_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v61_pb : Scalar.QComplex := ((3078973864378867053988643 : Int)/10^30,(-431461275183433092165750124 : Int)/10^30)
theorem v61_pb_checked : Scalar.distance (sourceCoefficient 0 62 1 1) v61_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v61_pg : Scalar.QComplex := ((-93083492415931735646741 : Int)/10^30,(-664258084881233861151 : Int)/10^30)
theorem v61_pg_checked : Scalar.distance (sourceCoefficient 0 62 1 2) v61_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v61_mb : Scalar.QComplex := ((2706641069747352113193717 : Int)/10^30,(-431463771546454710822629912 : Int)/10^30)
theorem v61_mb_checked : Scalar.distance (sourceCoefficient 0 62 3 1) v61_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v61_mg : Scalar.QComplex := ((-93084030981503562369617 : Int)/10^30,(-583930975917513676838 : Int)/10^30)
theorem v61_mg_checked : Scalar.distance (sourceCoefficient 0 62 3 2) v61_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v61_upper : Scalar.QComplex := ((999985365324729178234767494023 : Int)/10^30,(5410095781769787489767163972 : Int)/10^30)
theorem v61_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 62 5) 1) 14) v61_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material61 : Material (0 : Basis) (62 : Basis) where
  plus := ![v61_pa,v61_pb,v61_pg]
  minus := ![(Primitive.Addresses.material61 1).one,v61_mb,v61_mg]
  upper := v61_upper
  lower := (Primitive.Addresses.material61 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v61_pa_checked.trans (by decide +kernel)
    · exact v61_pb_checked.trans (by decide +kernel)
    · exact v61_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 62 Primitive.Addresses.material61
    · exact v61_mb_checked.trans (by decide +kernel)
    · exact v61_mg_checked.trans (by decide +kernel)
  upper_error := v61_upper_checked
  lower_error := reuse_lower_error 0 62 Primitive.Addresses.material61

def v62_pa : Scalar.QComplex := ((999974715259742150458998276031 : Int)/10^30,(7111177201955325700669606188 : Int)/10^30)
theorem v62_pa_checked : Scalar.distance (sourceCoefficient 0 63 1 0) v62_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v62_pb : Scalar.QComplex := ((3068275488915885812102678 : Int)/10^30,(-431461320851836126107941100 : Int)/10^30)
theorem v62_pb_checked : Scalar.distance (sourceCoefficient 0 63 1 1) v62_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v62_pg : Scalar.QComplex := ((-93083505563086772366638 : Int)/10^30,(-661950039873126253155 : Int)/10^30)
theorem v62_pg_checked : Scalar.distance (sourceCoefficient 0 63 1 2) v62_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v62_mb : Scalar.QComplex := ((2695942658858090006315924 : Int)/10^30,(-431463807982624552722635015 : Int)/10^30)
theorem v62_mb_checked : Scalar.distance (sourceCoefficient 0 63 3 1) v62_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v62_mg : Scalar.QComplex := ((-93084042136914812294315 : Int)/10^30,(-581622920423394037422 : Int)/10^30)
theorem v62_mg_checked : Scalar.distance (sourceCoefficient 0 63 3 2) v62_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v62_upper : Scalar.QComplex := ((999985499161598671152583004613 : Int)/10^30,(5385300969151432058207454233 : Int)/10^30)
theorem v62_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 63 5) 1) 14) v62_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material62 : Material (0 : Basis) (63 : Basis) where
  plus := ![v62_pa,v62_pb,v62_pg]
  minus := ![(Primitive.Addresses.material62 1).one,v62_mb,v62_mg]
  upper := v62_upper
  lower := (Primitive.Addresses.material62 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v62_pa_checked.trans (by decide +kernel)
    · exact v62_pb_checked.trans (by decide +kernel)
    · exact v62_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 63 Primitive.Addresses.material62
    · exact v62_mb_checked.trans (by decide +kernel)
    · exact v62_mg_checked.trans (by decide +kernel)
  upper_error := v62_upper_checked
  lower_error := reuse_lower_error 0 63 Primitive.Addresses.material62

def v63_pa : Scalar.QComplex := ((999974966632574748071205731397 : Int)/10^30,(7075740822063737088655504618 : Int)/10^30)
theorem v63_pa_checked : Scalar.distance (sourceCoefficient 0 64 1 0) v63_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v63_pb : Scalar.QComplex := ((3052985365081545965465870 : Int)/10^30,(-431461385507155291568735099 : Int)/10^30)
theorem v63_pb_checked : Scalar.distance (sourceCoefficient 0 64 1 1) v63_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v63_pg : Scalar.QComplex := ((-93083524237104493277857 : Int)/10^30,(-658651380568054452548 : Int)/10^30)
theorem v63_pg_checked : Scalar.distance (sourceCoefficient 0 64 1 2) v63_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v63_mb : Scalar.QComplex := ((2680652484922333584069386 : Int)/10^30,(-431463859443231416631842337 : Int)/10^30)
theorem v63_mb_checked : Scalar.distance (sourceCoefficient 0 64 3 1) v63_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v63_mg : Scalar.QComplex := ((-93084057964331165838395 : Int)/10^30,(-578324246231727605661 : Int)/10^30)
theorem v63_mg_checked : Scalar.distance (sourceCoefficient 0 64 3 2) v63_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v63_upper : Scalar.QComplex := ((999985689374079948848431517139 : Int)/10^30,(5349864208191463946878998906 : Int)/10^30)
theorem v63_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 64 5) 1) 14) v63_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material63 : Material (0 : Basis) (64 : Basis) where
  plus := ![v63_pa,v63_pb,v63_pg]
  minus := ![(Primitive.Addresses.material63 1).one,v63_mb,v63_mg]
  upper := v63_upper
  lower := (Primitive.Addresses.material63 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v63_pa_checked.trans (by decide +kernel)
    · exact v63_pb_checked.trans (by decide +kernel)
    · exact v63_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 64 Primitive.Addresses.material63
    · exact v63_mb_checked.trans (by decide +kernel)
    · exact v63_mg_checked.trans (by decide +kernel)
  upper_error := v63_upper_checked
  lower_error := reuse_lower_error 0 64 Primitive.Addresses.material63

def v64_pa : Scalar.QComplex := ((999975220476265454011562085980 : Int)/10^30,(7039775098985440312349540876 : Int)/10^30)
theorem v64_pa_checked : Scalar.distance (sourceCoefficient 0 65 1 0) v64_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v64_pb : Scalar.QComplex := ((3037466841606130540712978 : Int)/10^30,(-431461450389541486843978271 : Int)/10^30)
theorem v64_pb_checked : Scalar.distance (sourceCoefficient 0 65 1 1) v64_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v64_pg : Scalar.QComplex := ((-93083543050617154405258 : Int)/10^30,(-655303446600382236814 : Int)/10^30)
theorem v64_pg_checked : Scalar.distance (sourceCoefficient 0 65 1 2) v64_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v64_mb : Scalar.QComplex := ((2665133911234596588447986 : Int)/10^30,(-431463910933806622297814622 : Int)/10^30)
theorem v64_mb_checked : Scalar.distance (sourceCoefficient 0 65 3 1) v64_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v64_mg : Scalar.QComplex := ((-93084073888720593082579 : Int)/10^30,(-574976297275430116835 : Int)/10^30)
theorem v64_mg_checked : Scalar.distance (sourceCoefficient 0 65 3 2) v64_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v64_upper : Scalar.QComplex := ((999985881143817336200006097312 : Int)/10^30,(5313898100568705226364006745 : Int)/10^30)
theorem v64_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 65 5) 1) 14) v64_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material64 : Material (0 : Basis) (65 : Basis) where
  plus := ![v64_pa,v64_pb,v64_pg]
  minus := ![(Primitive.Addresses.material64 1).one,v64_mb,v64_mg]
  upper := v64_upper
  lower := (Primitive.Addresses.material64 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v64_pa_checked.trans (by decide +kernel)
    · exact v64_pb_checked.trans (by decide +kernel)
    · exact v64_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 65 Primitive.Addresses.material64
    · exact v64_mb_checked.trans (by decide +kernel)
    · exact v64_mg_checked.trans (by decide +kernel)
  upper_error := v64_upper_checked
  lower_error := reuse_lower_error 0 65 Primitive.Addresses.material64

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
