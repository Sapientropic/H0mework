import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B128

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3073_pa : Scalar.QComplex := ((999999029692214638727174654986 : Int)/10^30,(-1393059449278941332142073214 : Int)/10^30)
theorem v3073_pa_checked : Scalar.distance (sourceCoefficient 39 71 1 0) v3073_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3073_pb : Scalar.QComplex := ((-601073809795129931169035 : Int)/10^30,(-431477082244876914856928824 : Int)/10^30)
theorem v3073_pb_checked : Scalar.distance (sourceCoefficient 39 71 1 1) v3073_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3073_pg : Scalar.QComplex := ((-93086337407416424982862 : Int)/10^30,(129674927748761201244 : Int)/10^30)
theorem v3073_pg_checked : Scalar.distance (sourceCoefficient 39 71 1 2) v3073_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3073_mb : Scalar.QComplex := ((-973418874958811689093810 : Int)/10^30,(-431476402886613224528684425 : Int)/10^30)
theorem v3073_mb_checked : Scalar.distance (sourceCoefficient 39 71 3 1) v3073_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3073_mg : Scalar.QComplex := ((-93086190843496447178912 : Int)/10^30,(210004196194453879212 : Int)/10^30)
theorem v3073_mg_checked : Scalar.distance (sourceCoefficient 39 71 3 2) v3073_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3073_upper : Scalar.QComplex := ((999995136016895960467772082310 : Int)/10^30,(-3118964980525980204098946316 : Int)/10^30)
theorem v3073_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 71 5) 1) 14) v3073_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3073 : Material (39 : Basis) (71 : Basis) where
  plus := ![v3073_pa,v3073_pb,v3073_pg]
  minus := ![(Primitive.Addresses.material3073 1).one,v3073_mb,v3073_mg]
  upper := v3073_upper
  lower := (Primitive.Addresses.material3073 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3073_pa_checked.trans (by decide +kernel)
    · exact v3073_pb_checked.trans (by decide +kernel)
    · exact v3073_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 71 Primitive.Addresses.material3073
    · exact v3073_mb_checked.trans (by decide +kernel)
    · exact v3073_mg_checked.trans (by decide +kernel)
  upper_error := v3073_upper_checked
  lower_error := reuse_lower_error 39 71 Primitive.Addresses.material3073

def v3074_pa : Scalar.QComplex := ((999998992620015453617190505439 : Int)/10^30,(-1419422049384302172119832288 : Int)/10^30)
theorem v3074_pa_checked : Scalar.distance (sourceCoefficient 39 72 1 0) v3074_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3074_pb : Scalar.QComplex := ((-612448675690560932442718 : Int)/10^30,(-431477064195024285439145450 : Int)/10^30)
theorem v3074_pb_checked : Scalar.distance (sourceCoefficient 39 72 1 1) v3074_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3074_pg : Scalar.QComplex := ((-93086333734930582227936 : Int)/10^30,(132128927703743418475 : Int)/10^30)
theorem v3074_pg_checked : Scalar.distance (sourceCoefficient 39 72 1 2) v3074_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3074_mb : Scalar.QComplex := ((-984793721042650376442960 : Int)/10^30,(-431476375020770353081276724 : Int)/10^30)
theorem v3074_mb_checked : Scalar.distance (sourceCoefficient 39 72 3 1) v3074_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3074_mg : Scalar.QComplex := ((-93086185053320534763779 : Int)/10^30,(212458192066509880189 : Int)/10^30)
theorem v3074_mg_checked : Scalar.distance (sourceCoefficient 39 72 3 2) v3074_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3074_upper : Scalar.QComplex := ((999995053445295804590290435768 : Int)/10^30,(-3145327477384092325824883369 : Int)/10^30)
theorem v3074_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 72 5) 1) 14) v3074_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3074 : Material (39 : Basis) (72 : Basis) where
  plus := ![v3074_pa,v3074_pb,v3074_pg]
  minus := ![(Primitive.Addresses.material3074 1).one,v3074_mb,v3074_mg]
  upper := v3074_upper
  lower := (Primitive.Addresses.material3074 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3074_pa_checked.trans (by decide +kernel)
    · exact v3074_pb_checked.trans (by decide +kernel)
    · exact v3074_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 72 Primitive.Addresses.material3074
    · exact v3074_mb_checked.trans (by decide +kernel)
    · exact v3074_mg_checked.trans (by decide +kernel)
  upper_error := v3074_upper_checked
  lower_error := reuse_lower_error 39 72 Primitive.Addresses.material3074

def v3075_pa : Scalar.QComplex := ((999998979162336517727782534924 : Int)/10^30,(-1428871682431634324599550302 : Int)/10^30)
theorem v3075_pa_checked : Scalar.distance (sourceCoefficient 39 73 1 0) v3075_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3075_pb : Scalar.QComplex := ((-616525978636136059581200 : Int)/10^30,(-431477057627737522897760609 : Int)/10^30)
theorem v3075_pb_checked : Scalar.distance (sourceCoefficient 39 73 1 1) v3075_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3075_pg : Scalar.QComplex := ((-93086332400157752742154 : Int)/10^30,(133008560168151546638 : Int)/10^30)
theorem v3075_pg_checked : Scalar.distance (sourceCoefficient 39 73 1 2) v3075_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3075_mb : Scalar.QComplex := ((-988871016802786578536444 : Int)/10^30,(-431476364934957228717379186 : Int)/10^30)
theorem v3075_mb_checked : Scalar.distance (sourceCoefficient 39 73 3 1) v3075_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3075_mg : Scalar.QComplex := ((-93086182959465002666247 : Int)/10^30,(213337823051541804754 : Int)/10^30)
theorem v3075_mg_checked : Scalar.distance (sourceCoefficient 39 73 3 2) v3075_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3075_upper : Scalar.QComplex := ((999995023678427536650987273154 : Int)/10^30,(-3154777073130573113927610193 : Int)/10^30)
theorem v3075_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 73 5) 1) 14) v3075_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3075 : Material (39 : Basis) (73 : Basis) where
  plus := ![v3075_pa,v3075_pb,v3075_pg]
  minus := ![(Primitive.Addresses.material3075 1).one,v3075_mb,v3075_mg]
  upper := v3075_upper
  lower := (Primitive.Addresses.material3075 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3075_pa_checked.trans (by decide +kernel)
    · exact v3075_pb_checked.trans (by decide +kernel)
    · exact v3075_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 73 Primitive.Addresses.material3075
    · exact v3075_mb_checked.trans (by decide +kernel)
    · exact v3075_mg_checked.trans (by decide +kernel)
  upper_error := v3075_upper_checked
  lower_error := reuse_lower_error 39 73 Primitive.Addresses.material3075

def v3076_pa : Scalar.QComplex := ((999998963912367851070508324914 : Int)/10^30,(-1439504842235786816241617137 : Int)/10^30)
theorem v3076_pa_checked : Scalar.distance (sourceCoefficient 39 74 1 0) v3076_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3076_pb : Scalar.QComplex := ((-621113946571162696980387 : Int)/10^30,(-431477050176499440663418779 : Int)/10^30)
theorem v3076_pb_checked : Scalar.distance (sourceCoefficient 39 74 1 1) v3076_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3076_pg : Scalar.QComplex := ((-93086330886614711553679 : Int)/10^30,(133998362891291079736 : Int)/10^30)
theorem v3076_pg_checked : Scalar.distance (sourceCoefficient 39 74 1 2) v3076_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3076_mb : Scalar.QComplex := ((-993458976599420199569409 : Int)/10^30,(-431476353524512227396689618 : Int)/10^30)
theorem v3076_mb_checked : Scalar.distance (sourceCoefficient 39 74 3 1) v3076_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3076_mg : Scalar.QComplex := ((-93086180591767354029400 : Int)/10^30,(214327624100013070710 : Int)/10^30)
theorem v3076_mg_checked : Scalar.distance (sourceCoefficient 39 74 3 2) v3076_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3076_upper : Scalar.QComplex := ((999994990076612393785589730989 : Int)/10^30,(-3165410190777820683676661854 : Int)/10^30)
theorem v3076_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 74 5) 1) 14) v3076_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3076 : Material (39 : Basis) (74 : Basis) where
  plus := ![v3076_pa,v3076_pb,v3076_pg]
  minus := ![(Primitive.Addresses.material3076 1).one,v3076_mb,v3076_mg]
  upper := v3076_upper
  lower := (Primitive.Addresses.material3076 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3076_pa_checked.trans (by decide +kernel)
    · exact v3076_pb_checked.trans (by decide +kernel)
    · exact v3076_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 74 Primitive.Addresses.material3076
    · exact v3076_mb_checked.trans (by decide +kernel)
    · exact v3076_mg_checked.trans (by decide +kernel)
  upper_error := v3076_upper_checked
  lower_error := reuse_lower_error 39 74 Primitive.Addresses.material3076

def v3077_pa : Scalar.QComplex := ((999998942476174093464466111816 : Int)/10^30,(-1454319955668775352921782281 : Int)/10^30)
theorem v3077_pa_checked : Scalar.distance (sourceCoefficient 39 75 1 0) v3077_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3077_pb : Scalar.QComplex := ((-627506332831552833109416 : Int)/10^30,(-431477039686286740810038763 : Int)/10^30)
theorem v3077_pb_checked : Scalar.distance (sourceCoefficient 39 75 1 1) v3077_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3077_pg : Scalar.QComplex := ((-93086328757332542255707 : Int)/10^30,(135377448676610377095 : Int)/10^30)
theorem v3077_pg_checked : Scalar.distance (sourceCoefficient 39 75 1 2) v3077_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3077_mb : Scalar.QComplex := ((-999851351427051686138695 : Int)/10^30,(-431476337517961993201965580 : Int)/10^30)
theorem v3077_mb_checked : Scalar.distance (sourceCoefficient 39 75 3 1) v3077_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3077_mg : Scalar.QComplex := ((-93086177272397056548014 : Int)/10^30,(215706707534361090066 : Int)/10^30)
theorem v3077_mg_checked : Scalar.distance (sourceCoefficient 39 75 3 2) v3077_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3077_upper : Scalar.QComplex := ((999994943070908794125622225381 : Int)/10^30,(-3180225245148512318072715792 : Int)/10^30)
theorem v3077_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 75 5) 1) 14) v3077_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3077 : Material (39 : Basis) (75 : Basis) where
  plus := ![v3077_pa,v3077_pb,v3077_pg]
  minus := ![(Primitive.Addresses.material3077 1).one,v3077_mb,v3077_mg]
  upper := v3077_upper
  lower := (Primitive.Addresses.material3077 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3077_pa_checked.trans (by decide +kernel)
    · exact v3077_pb_checked.trans (by decide +kernel)
    · exact v3077_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 75 Primitive.Addresses.material3077
    · exact v3077_mb_checked.trans (by decide +kernel)
    · exact v3077_mg_checked.trans (by decide +kernel)
  upper_error := v3077_upper_checked
  lower_error := reuse_lower_error 39 75 Primitive.Addresses.material3077

def v3078_pa : Scalar.QComplex := ((999998924321453374461831118105 : Int)/10^30,(-1466750127379145880990929379 : Int)/10^30)
theorem v3078_pa_checked : Scalar.distance (sourceCoefficient 39 76 1 0) v3078_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3078_pb : Scalar.QComplex := ((-632869670632884673663077 : Int)/10^30,(-431477030787374477543459053 : Int)/10^30)
theorem v3078_pb_checked : Scalar.distance (sourceCoefficient 39 76 1 1) v3078_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3078_pg : Scalar.QComplex := ((-93086326952433277793209 : Int)/10^30,(136534528782001815029 : Int)/10^30)
theorem v3078_pg_checked : Scalar.distance (sourceCoefficient 39 76 1 2) v3078_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3078_mb : Scalar.QComplex := ((-1005214679552007255541160 : Int)/10^30,(-431476323990734076625343864 : Int)/10^30)
theorem v3078_mb_checked : Scalar.distance (sourceCoefficient 39 76 3 1) v3078_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3078_mg : Scalar.QComplex := ((-93086174468990446132613 : Int)/10^30,(216863785651371948004 : Int)/10^30)
theorem v3078_mg_checked : Scalar.distance (sourceCoefficient 39 76 3 2) v3078_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3078_upper : Scalar.QComplex := ((999994903462866398716160108173 : Int)/10^30,(-3192655367012201256483594158 : Int)/10^30)
theorem v3078_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 76 5) 1) 14) v3078_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3078 : Material (39 : Basis) (76 : Basis) where
  plus := ![v3078_pa,v3078_pb,v3078_pg]
  minus := ![(Primitive.Addresses.material3078 1).one,v3078_mb,v3078_mg]
  upper := v3078_upper
  lower := (Primitive.Addresses.material3078 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3078_pa_checked.trans (by decide +kernel)
    · exact v3078_pb_checked.trans (by decide +kernel)
    · exact v3078_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 76 Primitive.Addresses.material3078
    · exact v3078_mb_checked.trans (by decide +kernel)
    · exact v3078_mg_checked.trans (by decide +kernel)
  upper_error := v3078_upper_checked
  lower_error := reuse_lower_error 39 76 Primitive.Addresses.material3078

def v3079_pa : Scalar.QComplex := ((999998920096455611271283814913 : Int)/10^30,(-1469627817709569707174273038 : Int)/10^30)
theorem v3079_pa_checked : Scalar.distance (sourceCoefficient 39 77 1 0) v3079_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3079_pb : Scalar.QComplex := ((-634111328880614556208523 : Int)/10^30,(-431477028714529246059197110 : Int)/10^30)
theorem v3079_pb_checked : Scalar.distance (sourceCoefficient 39 77 1 1) v3079_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3079_pg : Scalar.QComplex := ((-93086326532191757786021 : Int)/10^30,(136802402653504897094 : Int)/10^30)
theorem v3079_pg_checked : Scalar.distance (sourceCoefficient 39 77 1 2) v3079_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3079_mb : Scalar.QComplex := ((-1006456335548638948584226 : Int)/10^30,(-431476320846394471376754355 : Int)/10^30)
theorem v3079_mb_checked : Scalar.distance (sourceCoefficient 39 77 3 1) v3079_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3079_mg : Scalar.QComplex := ((-93086173817585996084702 : Int)/10^30,(217131659060483840476 : Int)/10^30)
theorem v3079_mg_checked : Scalar.distance (sourceCoefficient 39 77 3 2) v3079_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3079_upper : Scalar.QComplex := ((999994894271242479879425388857 : Int)/10^30,(-3195533045764680522288786305 : Int)/10^30)
theorem v3079_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 77 5) 1) 14) v3079_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3079 : Material (39 : Basis) (77 : Basis) where
  plus := ![v3079_pa,v3079_pb,v3079_pg]
  minus := ![(Primitive.Addresses.material3079 1).one,v3079_mb,v3079_mg]
  upper := v3079_upper
  lower := (Primitive.Addresses.material3079 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3079_pa_checked.trans (by decide +kernel)
    · exact v3079_pb_checked.trans (by decide +kernel)
    · exact v3079_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 77 Primitive.Addresses.material3079
    · exact v3079_mb_checked.trans (by decide +kernel)
    · exact v3079_mg_checked.trans (by decide +kernel)
  upper_error := v3079_upper_checked
  lower_error := reuse_lower_error 39 77 Primitive.Addresses.material3079

def v3080_pa : Scalar.QComplex := ((999998894522860278980990266893 : Int)/10^30,(-1486927388059797482759545977 : Int)/10^30)
theorem v3080_pa_checked : Scalar.distance (sourceCoefficient 39 78 1 0) v3080_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3080_pb : Scalar.QComplex := ((-641575701883444846663838 : Int)/10^30,(-431477016152971536101326413 : Int)/10^30)
theorem v3080_pb_checked : Scalar.distance (sourceCoefficient 39 78 1 1) v3080_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3080_pg : Scalar.QComplex := ((-93086323986906904477856 : Int)/10^30,(138412757602078932373 : Int)/10^30)
theorem v3080_pg_checked : Scalar.distance (sourceCoefficient 39 78 1 2) v3080_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3080_mb : Scalar.QComplex := ((-1013920694932083479250930 : Int)/10^30,(-431476301843423720098722305 : Int)/10^30)
theorem v3080_mb_checked : Scalar.distance (sourceCoefficient 39 78 3 1) v3080_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3080_mg : Scalar.QComplex := ((-93086169882638297577550 : Int)/10^30,(218742011212982938514 : Int)/10^30)
theorem v3080_mg_checked : Scalar.distance (sourceCoefficient 39 78 3 2) v3080_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3080_upper : Scalar.QComplex := ((999994838840196216724808534337 : Int)/10^30,(-3212832546211524886406406060 : Int)/10^30)
theorem v3080_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 78 5) 1) 14) v3080_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3080 : Material (39 : Basis) (78 : Basis) where
  plus := ![v3080_pa,v3080_pb,v3080_pg]
  minus := ![(Primitive.Addresses.material3080 1).one,v3080_mb,v3080_mg]
  upper := v3080_upper
  lower := (Primitive.Addresses.material3080 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3080_pa_checked.trans (by decide +kernel)
    · exact v3080_pb_checked.trans (by decide +kernel)
    · exact v3080_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 78 Primitive.Addresses.material3080
    · exact v3080_mb_checked.trans (by decide +kernel)
    · exact v3080_mg_checked.trans (by decide +kernel)
  upper_error := v3080_upper_checked
  lower_error := reuse_lower_error 39 78 Primitive.Addresses.material3080

def v3081_pa : Scalar.QComplex := ((999998886214593791308078367357 : Int)/10^30,(-1492504462941217727132840209 : Int)/10^30)
theorem v3081_pa_checked : Scalar.distance (sourceCoefficient 39 79 1 0) v3081_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3081_pb : Scalar.QComplex := ((-643982083423860017463581 : Int)/10^30,(-431477012066647896890832691 : Int)/10^30)
theorem v3081_pb_checked : Scalar.distance (sourceCoefficient 39 79 1 1) v3081_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3081_pg : Scalar.QComplex := ((-93086323159424252312513 : Int)/10^30,(138931907494560155616 : Int)/10^30)
theorem v3081_pg_checked : Scalar.distance (sourceCoefficient 39 79 1 2) v3081_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3081_mb : Scalar.QComplex := ((-1016327072050179566030855 : Int)/10^30,(-431476295680502712436329085 : Int)/10^30)
theorem v3081_mb_checked : Scalar.distance (sourceCoefficient 39 79 3 1) v3081_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3081_mg : Scalar.QComplex := ((-93086168607152977953710 : Int)/10^30,(219261160198080670080 : Int)/10^30)
theorem v3081_mg_checked : Scalar.distance (sourceCoefficient 39 79 3 2) v3081_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3081_upper : Scalar.QComplex := ((999994820906416806188522063024 : Int)/10^30,(-3218409598447232986464714567 : Int)/10^30)
theorem v3081_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 79 5) 1) 14) v3081_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3081 : Material (39 : Basis) (79 : Basis) where
  plus := ![v3081_pa,v3081_pb,v3081_pg]
  minus := ![(Primitive.Addresses.material3081 1).one,v3081_mb,v3081_mg]
  upper := v3081_upper
  lower := (Primitive.Addresses.material3081 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3081_pa_checked.trans (by decide +kernel)
    · exact v3081_pb_checked.trans (by decide +kernel)
    · exact v3081_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 79 Primitive.Addresses.material3081
    · exact v3081_mb_checked.trans (by decide +kernel)
    · exact v3081_mg_checked.trans (by decide +kernel)
  upper_error := v3081_upper_checked
  lower_error := reuse_lower_error 39 79 Primitive.Addresses.material3081

def v3082_pa : Scalar.QComplex := ((999998873174017721058026508332 : Int)/10^30,(-1501216405059939920213332630 : Int)/10^30)
theorem v3082_pa_checked : Scalar.distance (sourceCoefficient 39 80 1 0) v3082_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3082_pb : Scalar.QComplex := ((-647741089175803698929555 : Int)/10^30,(-431477005647598108069168562 : Int)/10^30)
theorem v3082_pb_checked : Scalar.distance (sourceCoefficient 39 80 1 1) v3082_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3082_pg : Scalar.QComplex := ((-93086321860054962136562 : Int)/10^30,(139742870928902011006 : Int)/10^30)
theorem v3082_pg_checked : Scalar.distance (sourceCoefficient 39 80 1 2) v3082_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3082_mb : Scalar.QComplex := ((-1020086070863122746515859 : Int)/10^30,(-431476286017602649127250134 : Int)/10^30)
theorem v3082_mb_checked : Scalar.distance (sourceCoefficient 39 80 3 1) v3082_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3082_mg : Scalar.QComplex := ((-93086166607959252192541 : Int)/10^30,(220072122209166600003 : Int)/10^30)
theorem v3082_mg_checked : Scalar.distance (sourceCoefficient 39 80 3 2) v3082_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3082_upper : Scalar.QComplex := ((999994792829838402645371625226 : Int)/10^30,(-3227121505083689504886217580 : Int)/10^30)
theorem v3082_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 80 5) 1) 14) v3082_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3082 : Material (39 : Basis) (80 : Basis) where
  plus := ![v3082_pa,v3082_pb,v3082_pg]
  minus := ![(Primitive.Addresses.material3082 1).one,v3082_mb,v3082_mg]
  upper := v3082_upper
  lower := (Primitive.Addresses.material3082 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3082_pa_checked.trans (by decide +kernel)
    · exact v3082_pb_checked.trans (by decide +kernel)
    · exact v3082_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 80 Primitive.Addresses.material3082
    · exact v3082_mb_checked.trans (by decide +kernel)
    · exact v3082_mg_checked.trans (by decide +kernel)
  upper_error := v3082_upper_checked
  lower_error := reuse_lower_error 39 80 Primitive.Addresses.material3082

def v3083_pa : Scalar.QComplex := ((999998833449837485269703190132 : Int)/10^30,(-1527448514415519974214794555 : Int)/10^30)
theorem v3083_pa_checked : Scalar.distance (sourceCoefficient 39 81 1 0) v3083_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3083_pb : Scalar.QComplex := ((-659059650181602637808163 : Int)/10^30,(-431476986055828069264868349 : Int)/10^30)
theorem v3083_pb_checked : Scalar.distance (sourceCoefficient 39 81 1 1) v3083_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3083_pg : Scalar.QComplex := ((-93086317897811711055860 : Int)/10^30,(142184723851036041855 : Int)/10^30)
theorem v3083_pg_checked : Scalar.distance (sourceCoefficient 39 81 1 2) v3083_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3083_mb : Scalar.QComplex := ((-1031404610747688976222150 : Int)/10^30,(-431476256658431526294023253 : Int)/10^30)
theorem v3083_mb_checked : Scalar.distance (sourceCoefficient 39 81 3 1) v3083_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3083_mg : Scalar.QComplex := ((-93086160538508381607492 : Int)/10^30,(222513970802849716879 : Int)/10^30)
theorem v3083_mg_checked : Scalar.distance (sourceCoefficient 39 81 3 2) v3083_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3083_upper : Scalar.QComplex := ((999994707831476341997092302692 : Int)/10^30,(-3253353506809292776284849802 : Int)/10^30)
theorem v3083_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 81 5) 1) 14) v3083_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3083 : Material (39 : Basis) (81 : Basis) where
  plus := ![v3083_pa,v3083_pb,v3083_pg]
  minus := ![(Primitive.Addresses.material3083 1).one,v3083_mb,v3083_mg]
  upper := v3083_upper
  lower := (Primitive.Addresses.material3083 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3083_pa_checked.trans (by decide +kernel)
    · exact v3083_pb_checked.trans (by decide +kernel)
    · exact v3083_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 81 Primitive.Addresses.material3083
    · exact v3083_mb_checked.trans (by decide +kernel)
    · exact v3083_mg_checked.trans (by decide +kernel)
  upper_error := v3083_upper_checked
  lower_error := reuse_lower_error 39 81 Primitive.Addresses.material3083

def v3084_pa : Scalar.QComplex := ((999998818217199473579827579669 : Int)/10^30,(-1537388761648221729569369294 : Int)/10^30)
theorem v3084_pa_checked : Scalar.distance (sourceCoefficient 39 82 1 0) v3084_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3084_pb : Scalar.QComplex := ((-663348641633515668242429 : Int)/10^30,(-431476978528404553556219389 : Int)/10^30)
theorem v3084_pb_checked : Scalar.distance (sourceCoefficient 39 82 1 1) v3084_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3084_pg : Scalar.QComplex := ((-93086316376857217960261 : Int)/10^30,(143110025785978157156 : Int)/10^30)
theorem v3084_pg_checked : Scalar.distance (sourceCoefficient 39 82 1 2) v3084_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3084_mb : Scalar.QComplex := ((-1035693594106787001029900 : Int)/10^30,(-431476245429804359392447837 : Int)/10^30)
theorem v3084_mb_checked : Scalar.distance (sourceCoefficient 39 82 3 1) v3084_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3084_mg : Scalar.QComplex := ((-93086158219060559029853 : Int)/10^30,(223439271080744407120 : Int)/10^30)
theorem v3084_mg_checked : Scalar.distance (sourceCoefficient 39 82 3 2) v3084_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3084_upper : Scalar.QComplex := ((999994675442896066073646980328 : Int)/10^30,(-3263293712947012627942928410 : Int)/10^30)
theorem v3084_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 82 5) 1) 14) v3084_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3084 : Material (39 : Basis) (82 : Basis) where
  plus := ![v3084_pa,v3084_pb,v3084_pg]
  minus := ![(Primitive.Addresses.material3084 1).one,v3084_mb,v3084_mg]
  upper := v3084_upper
  lower := (Primitive.Addresses.material3084 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3084_pa_checked.trans (by decide +kernel)
    · exact v3084_pb_checked.trans (by decide +kernel)
    · exact v3084_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 82 Primitive.Addresses.material3084
    · exact v3084_mb_checked.trans (by decide +kernel)
    · exact v3084_mg_checked.trans (by decide +kernel)
  upper_error := v3084_upper_checked
  lower_error := reuse_lower_error 39 82 Primitive.Addresses.material3084

def v3085_pa : Scalar.QComplex := ((999998797264900689740139256853 : Int)/10^30,(-1550957366289866979019725320 : Int)/10^30)
theorem v3085_pa_checked : Scalar.distance (sourceCoefficient 39 83 1 0) v3085_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3085_pb : Scalar.QComplex := ((-669203187028796199695441 : Int)/10^30,(-431476968161588823838920379 : Int)/10^30)
theorem v3085_pb_checked : Scalar.distance (sourceCoefficient 39 83 1 1) v3085_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3085_pg : Scalar.QComplex := ((-93086314283407831147855 : Int)/10^30,(144373078481193920817 : Int)/10^30)
theorem v3085_pg_checked : Scalar.distance (sourceCoefficient 39 83 1 2) v3085_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3085_mb : Scalar.QComplex := ((-1041548128376057645179524 : Int)/10^30,(-431476230010783492523714459 : Int)/10^30)
theorem v3085_mb_checked : Scalar.distance (sourceCoefficient 39 83 3 1) v3085_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3085_mg : Scalar.QComplex := ((-93086155035654361514818 : Int)/10^30,(224702321499115392633 : Int)/10^30)
theorem v3085_mg_checked : Scalar.distance (sourceCoefficient 39 83 3 2) v3085_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3085_upper : Scalar.QComplex := ((999994631072447810939626518817 : Int)/10^30,(-3276862261218048220718182334 : Int)/10^30)
theorem v3085_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 83 5) 1) 14) v3085_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3085 : Material (39 : Basis) (83 : Basis) where
  plus := ![v3085_pa,v3085_pb,v3085_pg]
  minus := ![(Primitive.Addresses.material3085 1).one,v3085_mb,v3085_mg]
  upper := v3085_upper
  lower := (Primitive.Addresses.material3085 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3085_pa_checked.trans (by decide +kernel)
    · exact v3085_pb_checked.trans (by decide +kernel)
    · exact v3085_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 83 Primitive.Addresses.material3085
    · exact v3085_mb_checked.trans (by decide +kernel)
    · exact v3085_mg_checked.trans (by decide +kernel)
  upper_error := v3085_upper_checked
  lower_error := reuse_lower_error 39 83 Primitive.Addresses.material3085

def v3086_pa : Scalar.QComplex := ((999998742148345185708360617143 : Int)/10^30,(-1586096380248627186089413546 : Int)/10^30)
theorem v3086_pa_checked : Scalar.distance (sourceCoefficient 39 84 1 0) v3086_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3086_pb : Scalar.QComplex := ((-684364874828037256411781 : Int)/10^30,(-431476940822013640514399574 : Int)/10^30)
theorem v3086_pb_checked : Scalar.distance (sourceCoefficient 39 84 1 1) v3086_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3086_pg : Scalar.QComplex := ((-93086308769002969742569 : Int)/10^30,(147644043103525594773 : Int)/10^30)
theorem v3086_pg_checked : Scalar.distance (sourceCoefficient 39 84 1 2) v3086_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3086_mb : Scalar.QComplex := ((-1056709786937087356423008 : Int)/10^30,(-431476189587364775297114631 : Int)/10^30)
theorem v3086_mb_checked : Scalar.distance (sourceCoefficient 39 84 3 1) v3086_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3086_mg : Scalar.QComplex := ((-93086146698556403080108 : Int)/10^30,(227973280144834411410 : Int)/10^30)
theorem v3086_mg_checked : Scalar.distance (sourceCoefficient 39 84 3 2) v3086_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3086_upper : Scalar.QComplex := ((999994515309224090167425898430 : Int)/10^30,(-3312001127715200189648116428 : Int)/10^30)
theorem v3086_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 84 5) 1) 14) v3086_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3086 : Material (39 : Basis) (84 : Basis) where
  plus := ![v3086_pa,v3086_pb,v3086_pg]
  minus := ![(Primitive.Addresses.material3086 1).one,v3086_mb,v3086_mg]
  upper := v3086_upper
  lower := (Primitive.Addresses.material3086 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3086_pa_checked.trans (by decide +kernel)
    · exact v3086_pb_checked.trans (by decide +kernel)
    · exact v3086_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 84 Primitive.Addresses.material3086
    · exact v3086_mb_checked.trans (by decide +kernel)
    · exact v3086_mg_checked.trans (by decide +kernel)
  upper_error := v3086_upper_checked
  lower_error := reuse_lower_error 39 84 Primitive.Addresses.material3086

def v3087_pa : Scalar.QComplex := ((999998613631627071769769844252 : Int)/10^30,(-1665153093213712588526949100 : Int)/10^30)
theorem v3087_pa_checked : Scalar.distance (sourceCoefficient 39 85 1 0) v3087_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3087_pb : Scalar.QComplex := ((-718476051985951167514495 : Int)/10^30,(-431476876715781920984224960 : Int)/10^30)
theorem v3087_pb_checked : Scalar.distance (sourceCoefficient 39 85 1 1) v3087_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3087_pg : Scalar.QComplex := ((-93086295872321917096351 : Int)/10^30,(155003148399066331359 : Int)/10^30)
theorem v3087_pg_checked : Scalar.distance (sourceCoefficient 39 85 1 2) v3087_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3087_mb : Scalar.QComplex := ((-1090820896073060317366991 : Int)/10^30,(-431476096044747348555773512 : Int)/10^30)
theorem v3087_mb_checked : Scalar.distance (sourceCoefficient 39 85 3 1) v3087_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3087_mg : Scalar.QComplex := ((-93086127451303724204811 : Int)/10^30,(235332371570989015257 : Int)/10^30)
theorem v3087_mg_checked : Scalar.distance (sourceCoefficient 39 85 3 2) v3087_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3087_upper : Scalar.QComplex := ((999994250347982778022272473952 : Int)/10^30,(-3391057501126401765382281076 : Int)/10^30)
theorem v3087_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 85 5) 1) 14) v3087_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3087 : Material (39 : Basis) (85 : Basis) where
  plus := ![v3087_pa,v3087_pb,v3087_pg]
  minus := ![(Primitive.Addresses.material3087 1).one,v3087_mb,v3087_mg]
  upper := v3087_upper
  lower := (Primitive.Addresses.material3087 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3087_pa_checked.trans (by decide +kernel)
    · exact v3087_pb_checked.trans (by decide +kernel)
    · exact v3087_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 85 Primitive.Addresses.material3087
    · exact v3087_mb_checked.trans (by decide +kernel)
    · exact v3087_mg_checked.trans (by decide +kernel)
  upper_error := v3087_upper_checked
  lower_error := reuse_lower_error 39 85 Primitive.Addresses.material3087

def v3088_pa : Scalar.QComplex := ((999998589239606060772119120366 : Int)/10^30,(-1679737716917009235432600180 : Int)/10^30)
theorem v3088_pa_checked : Scalar.distance (sourceCoefficient 39 86 1 0) v3088_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3088_pb : Scalar.QComplex := ((-724768985747097351808600 : Int)/10^30,(-431476864496414769244956311 : Int)/10^30)
theorem v3088_pb_checked : Scalar.distance (sourceCoefficient 39 86 1 1) v3088_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3088_pg : Scalar.QComplex := ((-93086293418943214821396 : Int)/10^30,(156360778571396071582 : Int)/10^30)
theorem v3088_pg_checked : Scalar.distance (sourceCoefficient 39 86 1 2) v3088_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3088_mb : Scalar.QComplex := ((-1097113816946296149021645 : Int)/10^30,(-431476078394866333991628793 : Int)/10^30)
theorem v3088_mb_checked : Scalar.distance (sourceCoefficient 39 86 3 1) v3088_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3088_mg : Scalar.QComplex := ((-93086123826352242107444 : Int)/10^30,(236689999120655671570 : Int)/10^30)
theorem v3088_mg_checked : Scalar.distance (sourceCoefficient 39 86 3 2) v3088_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3088_upper : Scalar.QComplex := ((999994200784260690911437528284 : Int)/10^30,(-3405642061009199198354144521 : Int)/10^30)
theorem v3088_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 86 5) 1) 14) v3088_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3088 : Material (39 : Basis) (86 : Basis) where
  plus := ![v3088_pa,v3088_pb,v3088_pg]
  minus := ![(Primitive.Addresses.material3088 1).one,v3088_mb,v3088_mg]
  upper := v3088_upper
  lower := (Primitive.Addresses.material3088 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3088_pa_checked.trans (by decide +kernel)
    · exact v3088_pb_checked.trans (by decide +kernel)
    · exact v3088_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 86 Primitive.Addresses.material3088
    · exact v3088_mb_checked.trans (by decide +kernel)
    · exact v3088_mg_checked.trans (by decide +kernel)
  upper_error := v3088_upper_checked
  lower_error := reuse_lower_error 39 86 Primitive.Addresses.material3088

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
