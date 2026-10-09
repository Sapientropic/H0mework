import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B085
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B086

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2049_pa : Scalar.QComplex := ((999998644584389956129388886643 : Int)/10^30,(-1646459651171648139162120515 : Int)/10^30)
theorem v2049_pa_checked : Scalar.distance (sourceCoefficient 23 95 1 0) v2049_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2049_pb : Scalar.QComplex := ((-710410126773804645316323 : Int)/10^30,(-431476813517592293990899055 : Int)/10^30)
theorem v2049_pb_checked : Scalar.distance (sourceCoefficient 23 95 1 1) v2049_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2049_pg : Scalar.QComplex := ((-93086290495812901892778 : Int)/10^30,(153263029113700919275 : Int)/10^30)
theorem v2049_pg_checked : Scalar.distance (sourceCoefficient 23 95 1 2) v2049_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2049_mb : Scalar.QComplex := ((-1082754919327035075348327 : Int)/10^30,(-431476039807111435433070335 : Int)/10^30)
theorem v2049_mb_checked : Scalar.distance (sourceCoefficient 23 95 3 1) v2049_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2049_mg : Scalar.QComplex := ((-93086123576441282128308 : Int)/10^30,(233592248293864409352 : Int)/10^30)
theorem v2049_mg_checked : Scalar.distance (sourceCoefficient 23 95 3 2) v2049_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2049_upper : Scalar.QComplex := ((999994313563884670666024355130 : Int)/10^30,(-3372364140347684077408438694 : Int)/10^30)
theorem v2049_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 95 5) 1) 14) v2049_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2049 : Material (23 : Basis) (95 : Basis) where
  plus := ![v2049_pa,v2049_pb,v2049_pg]
  minus := ![(Primitive.Addresses.material2049 1).one,v2049_mb,v2049_mg]
  upper := v2049_upper
  lower := (Primitive.Addresses.material2049 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2049_pa_checked.trans (by decide +kernel)
    · exact v2049_pb_checked.trans (by decide +kernel)
    · exact v2049_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 95 Primitive.Addresses.material2049
    · exact v2049_mb_checked.trans (by decide +kernel)
    · exact v2049_mg_checked.trans (by decide +kernel)
  upper_error := v2049_upper_checked
  lower_error := reuse_lower_error 23 95 Primitive.Addresses.material2049

def v2050_pa : Scalar.QComplex := ((999998609347832211001314847366 : Int)/10^30,(-1667723718625044198619844791 : Int)/10^30)
theorem v2050_pa_checked : Scalar.distance (sourceCoefficient 23 96 1 0) v2050_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2050_pb : Scalar.QComplex := ((-719585084561649153918713 : Int)/10^30,(-431476794287217382203755108 : Int)/10^30)
theorem v2050_pb_checked : Scalar.distance (sourceCoefficient 23 96 1 1) v2050_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2050_pg : Scalar.QComplex := ((-93086286781421479400282 : Int)/10^30,(155242424232323317974 : Int)/10^30)
theorem v2050_pg_checked : Scalar.distance (sourceCoefficient 23 96 1 2) v2050_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2050_mb : Scalar.QComplex := ((-1091929857103676038313090 : Int)/10^30,(-431476012659168337842707085 : Int)/10^30)
theorem v2050_mb_checked : Scalar.distance (sourceCoefficient 23 96 3 1) v2050_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2050_mg : Scalar.QComplex := ((-93086118153922403949154 : Int)/10^30,(235571639470115034930 : Int)/10^30)
theorem v2050_mg_checked : Scalar.distance (sourceCoefficient 23 96 3 2) v2050_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2050_upper : Scalar.QComplex := ((999994241627528042820309728466 : Int)/10^30,(-3393628115315647485317235034 : Int)/10^30)
theorem v2050_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 96 5) 1) 14) v2050_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2050 : Material (23 : Basis) (96 : Basis) where
  plus := ![v2050_pa,v2050_pb,v2050_pg]
  minus := ![(Primitive.Addresses.material2050 1).one,v2050_mb,v2050_mg]
  upper := v2050_upper
  lower := (Primitive.Addresses.material2050 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2050_pa_checked.trans (by decide +kernel)
    · exact v2050_pb_checked.trans (by decide +kernel)
    · exact v2050_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 96 Primitive.Addresses.material2050
    · exact v2050_mb_checked.trans (by decide +kernel)
    · exact v2050_mg_checked.trans (by decide +kernel)
  upper_error := v2050_upper_checked
  lower_error := reuse_lower_error 23 96 Primitive.Addresses.material2050

def v2051_pa : Scalar.QComplex := ((999998484657105474534718249086 : Int)/10^30,(-1740885835655756771453199272 : Int)/10^30)
theorem v2051_pa_checked : Scalar.distance (sourceCoefficient 23 97 1 0) v2051_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2051_pb : Scalar.QComplex := ((-751152859197847001918550 : Int)/10^30,(-431476726135091638037403348 : Int)/10^30)
theorem v2051_pb_checked : Scalar.distance (sourceCoefficient 23 97 1 1) v2051_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2051_pg : Scalar.QComplex := ((-93086273626386192267393 : Int)/10^30,(162052820815742319561 : Int)/10^30)
theorem v2051_pg_checked : Scalar.distance (sourceCoefficient 23 97 1 2) v2051_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2051_mb : Scalar.QComplex := ((-1123497561173533611268176 : Int)/10^30,(-431475917265500218580143103 : Int)/10^30)
theorem v2051_mb_checked : Scalar.distance (sourceCoefficient 23 97 3 1) v2051_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2051_mg : Scalar.QComplex := ((-93086099121826492422325 : Int)/10^30,(242382022165509166011 : Int)/10^30)
theorem v2051_mg_checked : Scalar.distance (sourceCoefficient 23 97 3 2) v2051_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2051_upper : Scalar.QComplex := ((999993990665810238944029461087 : Int)/10^30,(-3466789908175098474106916856 : Int)/10^30)
theorem v2051_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 97 5) 1) 14) v2051_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2051 : Material (23 : Basis) (97 : Basis) where
  plus := ![v2051_pa,v2051_pb,v2051_pg]
  minus := ![(Primitive.Addresses.material2051 1).one,v2051_mb,v2051_mg]
  upper := v2051_upper
  lower := (Primitive.Addresses.material2051 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2051_pa_checked.trans (by decide +kernel)
    · exact v2051_pb_checked.trans (by decide +kernel)
    · exact v2051_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 97 Primitive.Addresses.material2051
    · exact v2051_mb_checked.trans (by decide +kernel)
    · exact v2051_mg_checked.trans (by decide +kernel)
  upper_error := v2051_upper_checked
  lower_error := reuse_lower_error 23 97 Primitive.Addresses.material2051

def v2052_pa : Scalar.QComplex := ((999999891717514348745275576028 : Int)/10^30,(-465365404362435121952468294 : Int)/10^30)
theorem v2052_pa_checked : Scalar.distance (sourceCoefficient 24 25 1 0) v2052_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2052_pb : Scalar.QComplex := ((-200794711016090524057469 : Int)/10^30,(-431477474241204055240543749 : Int)/10^30)
theorem v2052_pb_checked : Scalar.distance (sourceCoefficient 24 25 1 1) v2052_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2052_pg : Scalar.QComplex := ((-93086419813248067402094 : Int)/10^30,(43319204087754674412 : Int)/10^30)
theorem v2052_pg_checked : Scalar.distance (sourceCoefficient 24 25 1 2) v2052_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2052_mb : Scalar.QComplex := ((-573140263497149878913721 : Int)/10^30,(-431477140305628751693744803 : Int)/10^30)
theorem v2052_mb_checked : Scalar.distance (sourceCoefficient 24 25 3 1) v2052_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2052_mg : Scalar.QComplex := ((-93086347770397608174081 : Int)/10^30,(123648575800151209437 : Int)/10^30)
theorem v2052_mg_checked : Scalar.distance (sourceCoefficient 24 25 3 2) v2052_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2052_upper : Scalar.QComplex := ((999997599156673564617313373199 : Int)/10^30,(-2191273805078244274666070034 : Int)/10^30)
theorem v2052_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 25 5) 1) 14) v2052_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2052 : Material (24 : Basis) (25 : Basis) where
  plus := ![v2052_pa,v2052_pb,v2052_pg]
  minus := ![(Primitive.Addresses.material2052 1).one,v2052_mb,v2052_mg]
  upper := v2052_upper
  lower := (Primitive.Addresses.material2052 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2052_pa_checked.trans (by decide +kernel)
    · exact v2052_pb_checked.trans (by decide +kernel)
    · exact v2052_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 25 Primitive.Addresses.material2052
    · exact v2052_mb_checked.trans (by decide +kernel)
    · exact v2052_mg_checked.trans (by decide +kernel)
  upper_error := v2052_upper_checked
  lower_error := reuse_lower_error 24 25 Primitive.Addresses.material2052

def v2053_pa : Scalar.QComplex := ((999999888272936332463466728610 : Int)/10^30,(-472709334424587294687039479 : Int)/10^30)
theorem v2053_pa_checked : Scalar.distance (sourceCoefficient 24 26 1 0) v2053_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2053_pb : Scalar.QComplex := ((-203963451740121680510443 : Int)/10^30,(-431477472726790432337610977 : Int)/10^30)
theorem v2053_pb_checked : Scalar.distance (sourceCoefficient 24 26 1 1) v2053_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2053_pg : Scalar.QComplex := ((-93086419489567465863461 : Int)/10^30,(44002824317187721797 : Int)/10^30)
theorem v2053_pg_checked : Scalar.distance (sourceCoefficient 24 26 1 2) v2053_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2053_mb : Scalar.QComplex := ((-576309001734443295297018 : Int)/10^30,(-431477136056735162621716482 : Int)/10^30)
theorem v2053_mb_checked : Scalar.distance (sourceCoefficient 24 26 3 1) v2053_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2053_mg : Scalar.QComplex := ((-93086346856783658267997 : Int)/10^30,(124332195495719421322 : Int)/10^30)
theorem v2053_mg_checked : Scalar.distance (sourceCoefficient 24 26 3 2) v2053_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2053_upper : Scalar.QComplex := ((999997583037143627486068477298 : Int)/10^30,(-2198617718257446132024148143 : Int)/10^30)
theorem v2053_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 26 5) 1) 14) v2053_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2053 : Material (24 : Basis) (26 : Basis) where
  plus := ![v2053_pa,v2053_pb,v2053_pg]
  minus := ![(Primitive.Addresses.material2053 1).one,v2053_mb,v2053_mg]
  upper := v2053_upper
  lower := (Primitive.Addresses.material2053 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2053_pa_checked.trans (by decide +kernel)
    · exact v2053_pb_checked.trans (by decide +kernel)
    · exact v2053_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 26 Primitive.Addresses.material2053
    · exact v2053_mb_checked.trans (by decide +kernel)
    · exact v2053_mg_checked.trans (by decide +kernel)
  upper_error := v2053_upper_checked
  lower_error := reuse_lower_error 24 26 Primitive.Addresses.material2053

def v2054_pa : Scalar.QComplex := ((999999885875280182935228539148 : Int)/10^30,(-477754567335235288798175725 : Int)/10^30)
theorem v2054_pa_checked : Scalar.distance (sourceCoefficient 24 27 1 0) v2054_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2054_pb : Scalar.QComplex := ((-206140356317556668757029 : Int)/10^30,(-431477471668417951934110346 : Int)/10^30)
theorem v2054_pb_checked : Scalar.distance (sourceCoefficient 24 27 1 1) v2054_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2054_pg : Scalar.QComplex := ((-93086419263806851498641 : Int)/10^30,(44472467035574193763 : Int)/10^30)
theorem v2054_pg_checked : Scalar.distance (sourceCoefficient 24 27 1 2) v2054_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2054_mb : Scalar.QComplex := ((-578485904587989436649292 : Int)/10^30,(-431477133119792470114863479 : Int)/10^30)
theorem v2054_mb_checked : Scalar.distance (sourceCoefficient 24 27 3 1) v2054_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2054_mg : Scalar.QComplex := ((-93086346225742613919486 : Int)/10^30,(124801837844415203184 : Int)/10^30)
theorem v2054_mg_checked : Scalar.distance (sourceCoefficient 24 27 3 2) v2054_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2054_upper : Scalar.QComplex := ((999997571931876745160876851100 : Int)/10^30,(-2203662939515675359995525716 : Int)/10^30)
theorem v2054_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 27 5) 1) 14) v2054_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2054 : Material (24 : Basis) (27 : Basis) where
  plus := ![v2054_pa,v2054_pb,v2054_pg]
  minus := ![(Primitive.Addresses.material2054 1).one,v2054_mb,v2054_mg]
  upper := v2054_upper
  lower := (Primitive.Addresses.material2054 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2054_pa_checked.trans (by decide +kernel)
    · exact v2054_pb_checked.trans (by decide +kernel)
    · exact v2054_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 27 Primitive.Addresses.material2054
    · exact v2054_mb_checked.trans (by decide +kernel)
    · exact v2054_mg_checked.trans (by decide +kernel)
  upper_error := v2054_upper_checked
  lower_error := reuse_lower_error 24 27 Primitive.Addresses.material2054

def v2055_pa : Scalar.QComplex := ((999999882605084092556612188471 : Int)/10^30,(-484551151101016882835914859 : Int)/10^30)
theorem v2055_pa_checked : Scalar.distance (sourceCoefficient 24 28 1 0) v2055_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2055_pb : Scalar.QComplex := ((-209072929413113138050246 : Int)/10^30,(-431477470219501474302516774 : Int)/10^30)
theorem v2055_pb_checked : Scalar.distance (sourceCoefficient 24 28 1 1) v2055_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2055_pg : Scalar.QComplex := ((-93086418955307682227512 : Int)/10^30,(45105136751779590829 : Int)/10^30)
theorem v2055_pg_checked : Scalar.distance (sourceCoefficient 24 28 1 2) v2055_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2055_mb : Scalar.QComplex := ((-581418475341265253835031 : Int)/10^30,(-431477129140198028705111296 : Int)/10^30)
theorem v2055_mb_checked : Scalar.distance (sourceCoefficient 24 28 3 1) v2055_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2055_mg : Scalar.QComplex := ((-93086345371278088817695 : Int)/10^30,(125434507058827861677 : Int)/10^30)
theorem v2055_mg_checked : Scalar.distance (sourceCoefficient 24 28 3 2) v2055_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2055_upper : Scalar.QComplex := ((999997556931398526878924794347 : Int)/10^30,(-2210459507514682035592412411 : Int)/10^30)
theorem v2055_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 28 5) 1) 14) v2055_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2055 : Material (24 : Basis) (28 : Basis) where
  plus := ![v2055_pa,v2055_pb,v2055_pg]
  minus := ![(Primitive.Addresses.material2055 1).one,v2055_mb,v2055_mg]
  upper := v2055_upper
  lower := (Primitive.Addresses.material2055 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2055_pa_checked.trans (by decide +kernel)
    · exact v2055_pb_checked.trans (by decide +kernel)
    · exact v2055_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 28 Primitive.Addresses.material2055
    · exact v2055_mb_checked.trans (by decide +kernel)
    · exact v2055_mg_checked.trans (by decide +kernel)
  upper_error := v2055_upper_checked
  lower_error := reuse_lower_error 24 28 Primitive.Addresses.material2055

def v2056_pa : Scalar.QComplex := ((999999875840321918787679478173 : Int)/10^30,(-498316506596760227983754564 : Int)/10^30)
theorem v2056_pa_checked : Scalar.distance (sourceCoefficient 24 29 1 0) v2056_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2056_pb : Scalar.QComplex := ((-215012370827954633287800 : Int)/10^30,(-431477467203543316127815014 : Int)/10^30)
theorem v2056_pb_checked : Scalar.distance (sourceCoefficient 24 29 1 1) v2056_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2056_pg : Scalar.QComplex := ((-93086418315124349870430 : Int)/10^30,(46386504545730916910 : Int)/10^30)
theorem v2056_pg_checked : Scalar.distance (sourceCoefficient 24 29 1 2) v2056_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2056_mb : Scalar.QComplex := ((-587357911941945207653031 : Int)/10^30,(-431477120998770555012422007 : Int)/10^30)
theorem v2056_mb_checked : Scalar.distance (sourceCoefficient 24 29 3 1) v2056_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2056_mg : Scalar.QComplex := ((-93086343625332299313251 : Int)/10^30,(126715873823218013632 : Int)/10^30)
theorem v2056_mg_checked : Scalar.distance (sourceCoefficient 24 29 3 2) v2056_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2056_upper : Scalar.QComplex := ((999997526408891626071205469454 : Int)/10^30,(-2224224830833179544579888095 : Int)/10^30)
theorem v2056_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 29 5) 1) 14) v2056_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2056 : Material (24 : Basis) (29 : Basis) where
  plus := ![v2056_pa,v2056_pb,v2056_pg]
  minus := ![(Primitive.Addresses.material2056 1).one,v2056_mb,v2056_mg]
  upper := v2056_upper
  lower := (Primitive.Addresses.material2056 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2056_pa_checked.trans (by decide +kernel)
    · exact v2056_pb_checked.trans (by decide +kernel)
    · exact v2056_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 29 Primitive.Addresses.material2056
    · exact v2056_mb_checked.trans (by decide +kernel)
    · exact v2056_mg_checked.trans (by decide +kernel)
  upper_error := v2056_upper_checked
  lower_error := reuse_lower_error 24 29 Primitive.Addresses.material2056

def v2057_pa : Scalar.QComplex := ((999999873227349836397952950060 : Int)/10^30,(-503532803554941457596448178 : Int)/10^30)
theorem v2057_pa_checked : Scalar.distance (sourceCoefficient 24 30 1 0) v2057_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2057_pb : Scalar.QComplex := ((-217263085684984259788175 : Int)/10^30,(-431477466032182953651676353 : Int)/10^30)
theorem v2057_pb_checked : Scalar.distance (sourceCoefficient 24 30 1 1) v2057_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2057_pg : Scalar.QComplex := ((-93086418067154306398101 : Int)/10^30,(46872071004338222535 : Int)/10^30)
theorem v2057_pg_checked : Scalar.distance (sourceCoefficient 24 30 1 2) v2057_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2057_mb : Scalar.QComplex := ((-589608624950099593426206 : Int)/10^30,(-431477117885145075504899896 : Int)/10^30)
theorem v2057_mb_checked : Scalar.distance (sourceCoefficient 24 30 3 1) v2057_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2057_mg : Scalar.QComplex := ((-93086342958340363494874 : Int)/10^30,(127201439887039755874 : Int)/10^30)
theorem v2057_mg_checked : Scalar.distance (sourceCoefficient 24 30 3 2) v2057_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2057_upper : Scalar.QComplex := ((999997514793068104339116170532 : Int)/10^30,(-2229441115512546437036574778 : Int)/10^30)
theorem v2057_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 30 5) 1) 14) v2057_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2057 : Material (24 : Basis) (30 : Basis) where
  plus := ![v2057_pa,v2057_pb,v2057_pg]
  minus := ![(Primitive.Addresses.material2057 1).one,v2057_mb,v2057_mg]
  upper := v2057_upper
  lower := (Primitive.Addresses.material2057 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2057_pa_checked.trans (by decide +kernel)
    · exact v2057_pb_checked.trans (by decide +kernel)
    · exact v2057_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 30 Primitive.Addresses.material2057
    · exact v2057_mb_checked.trans (by decide +kernel)
    · exact v2057_mg_checked.trans (by decide +kernel)
  upper_error := v2057_upper_checked
  lower_error := reuse_lower_error 24 30 Primitive.Addresses.material2057

def v2058_pa : Scalar.QComplex := ((999999867579068115669892186181 : Int)/10^30,(-514627871605645757132378100 : Int)/10^30)
theorem v2058_pa_checked : Scalar.distance (sourceCoefficient 24 31 1 0) v2058_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2058_pb : Scalar.QComplex := ((-222050358085077124960040 : Int)/10^30,(-431477463488640488001858031 : Int)/10^30)
theorem v2058_pb_checked : Scalar.distance (sourceCoefficient 24 31 1 1) v2058_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2058_pg : Scalar.QComplex := ((-93086417529894754106102 : Int)/10^30,(47904871272411905675 : Int)/10^30)
theorem v2058_pg_checked : Scalar.distance (sourceCoefficient 24 31 1 2) v2058_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2058_mb : Scalar.QComplex := ((-594395893372709563930718 : Int)/10^30,(-431477111210403086397097628 : Int)/10^30)
theorem v2058_mb_checked : Scalar.distance (sourceCoefficient 24 31 3 1) v2058_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2058_mg : Scalar.QComplex := ((-93086341529820895498906 : Int)/10^30,(128234239306923901550 : Int)/10^30)
theorem v2058_mg_checked : Scalar.distance (sourceCoefficient 24 31 3 2) v2058_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2058_upper : Scalar.QComplex := ((999997489995713877258490250233 : Int)/10^30,(-2240536157290028351433158670 : Int)/10^30)
theorem v2058_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 31 5) 1) 14) v2058_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2058 : Material (24 : Basis) (31 : Basis) where
  plus := ![v2058_pa,v2058_pb,v2058_pg]
  minus := ![(Primitive.Addresses.material2058 1).one,v2058_mb,v2058_mg]
  upper := v2058_upper
  lower := (Primitive.Addresses.material2058 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2058_pa_checked.trans (by decide +kernel)
    · exact v2058_pb_checked.trans (by decide +kernel)
    · exact v2058_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 31 Primitive.Addresses.material2058
    · exact v2058_mb_checked.trans (by decide +kernel)
    · exact v2058_mg_checked.trans (by decide +kernel)
  upper_error := v2058_upper_checked
  lower_error := reuse_lower_error 24 31 Primitive.Addresses.material2058

def v2059_pa : Scalar.QComplex := ((999999865109753533295195901950 : Int)/10^30,(-519403961034213731522314138 : Int)/10^30)
theorem v2059_pa_checked : Scalar.distance (sourceCoefficient 24 32 1 0) v2059_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2059_pb : Scalar.QComplex := ((-224111133283371226214517 : Int)/10^30,(-431477462371918198815044687 : Int)/10^30)
theorem v2059_pb_checked : Scalar.distance (sourceCoefficient 24 32 1 1) v2059_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2059_pg : Scalar.QComplex := ((-93086417294504767920925 : Int)/10^30,(48349460383120141292 : Int)/10^30)
theorem v2059_pg_checked : Scalar.distance (sourceCoefficient 24 32 1 2) v2059_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2059_mb : Scalar.QComplex := ((-596456666840001836517685 : Int)/10^30,(-431477108315325030758738272 : Int)/10^30)
theorem v2059_mb_checked : Scalar.distance (sourceCoefficient 24 32 3 1) v2059_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2059_mg : Scalar.QComplex := ((-93086340910770617969208 : Int)/10^30,(128678828048960336018 : Int)/10^30)
theorem v2059_mg_checked : Scalar.distance (sourceCoefficient 24 32 3 2) v2059_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2059_upper : Scalar.QComplex := ((999997479283305902377809680201 : Int)/10^30,(-2245312235343359206136490145 : Int)/10^30)
theorem v2059_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 32 5) 1) 14) v2059_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2059 : Material (24 : Basis) (32 : Basis) where
  plus := ![v2059_pa,v2059_pb,v2059_pg]
  minus := ![(Primitive.Addresses.material2059 1).one,v2059_mb,v2059_mg]
  upper := v2059_upper
  lower := (Primitive.Addresses.material2059 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2059_pa_checked.trans (by decide +kernel)
    · exact v2059_pb_checked.trans (by decide +kernel)
    · exact v2059_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 32 Primitive.Addresses.material2059
    · exact v2059_mb_checked.trans (by decide +kernel)
    · exact v2059_mg_checked.trans (by decide +kernel)
  upper_error := v2059_upper_checked
  lower_error := reuse_lower_error 24 32 Primitive.Addresses.material2059

def v2060_pa : Scalar.QComplex := ((999999861630387744568754862359 : Int)/10^30,(-526060077714240633248769859 : Int)/10^30)
theorem v2060_pa_checked : Scalar.distance (sourceCoefficient 24 33 1 0) v2060_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2060_pb : Scalar.QComplex := ((-226983097964655213912609 : Int)/10^30,(-431477460793728365699224290 : Int)/10^30)
theorem v2060_pb_checked : Scalar.distance (sourceCoefficient 24 33 1 1) v2060_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2060_pg : Scalar.QComplex := ((-93086416962325531068512 : Int)/10^30,(48969054517170262427 : Int)/10^30)
theorem v2060_pg_checked : Scalar.distance (sourceCoefficient 24 33 1 2) v2060_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2060_mb : Scalar.QComplex := ((-599328629090015371156225 : Int)/10^30,(-431477104258759613814641667 : Int)/10^30)
theorem v2060_mb_checked : Scalar.distance (sourceCoefficient 24 33 3 1) v2060_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2060_mg : Scalar.QComplex := ((-93086340043909672600948 : Int)/10^30,(129298421665651523589 : Int)/10^30)
theorem v2060_mg_checked : Scalar.distance (sourceCoefficient 24 33 3 2) v2060_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2060_upper : Scalar.QComplex := ((999997464316091744219850523460 : Int)/10^30,(-2251968336104812489609181840 : Int)/10^30)
theorem v2060_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 33 5) 1) 14) v2060_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2060 : Material (24 : Basis) (33 : Basis) where
  plus := ![v2060_pa,v2060_pb,v2060_pg]
  minus := ![(Primitive.Addresses.material2060 1).one,v2060_mb,v2060_mg]
  upper := v2060_upper
  lower := (Primitive.Addresses.material2060 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2060_pa_checked.trans (by decide +kernel)
    · exact v2060_pb_checked.trans (by decide +kernel)
    · exact v2060_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 33 Primitive.Addresses.material2060
    · exact v2060_mb_checked.trans (by decide +kernel)
    · exact v2060_mg_checked.trans (by decide +kernel)
  upper_error := v2060_upper_checked
  lower_error := reuse_lower_error 24 33 Primitive.Addresses.material2060

def v2061_pa : Scalar.QComplex := ((999999852994907399229224172921 : Int)/10^30,(-542227040630623936326820850 : Int)/10^30)
theorem v2061_pa_checked : Scalar.distance (sourceCoefficient 24 34 1 0) v2061_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2061_pb : Scalar.QComplex := ((-233958778922090666243312 : Int)/10^30,(-431477456854344065468116659 : Int)/10^30)
theorem v2061_pb_checked : Scalar.distance (sourceCoefficient 24 34 1 1) v2061_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2061_pg : Scalar.QComplex := ((-93086416135463550568489 : Int)/10^30,(50473979363975172545 : Int)/10^30)
theorem v2061_pg_checked : Scalar.distance (sourceCoefficient 24 34 1 2) v2061_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2061_mb : Scalar.QComplex := ((-606304304050574770847873 : Int)/10^30,(-431477094299678287137225048 : Int)/10^30)
theorem v2061_mb_checked : Scalar.distance (sourceCoefficient 24 34 3 1) v2061_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2061_mg : Scalar.QComplex := ((-93086337918365636485808 : Int)/10^30,(130803345238559486088 : Int)/10^30)
theorem v2061_mg_checked : Scalar.distance (sourceCoefficient 24 34 3 2) v2061_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2061_upper : Scalar.QComplex := ((999997427777912922155209222035 : Int)/10^30,(-2268135260038347962204580113 : Int)/10^30)
theorem v2061_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 34 5) 1) 14) v2061_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2061 : Material (24 : Basis) (34 : Basis) where
  plus := ![v2061_pa,v2061_pb,v2061_pg]
  minus := ![(Primitive.Addresses.material2061 1).one,v2061_mb,v2061_mg]
  upper := v2061_upper
  lower := (Primitive.Addresses.material2061 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2061_pa_checked.trans (by decide +kernel)
    · exact v2061_pb_checked.trans (by decide +kernel)
    · exact v2061_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 34 Primitive.Addresses.material2061
    · exact v2061_mb_checked.trans (by decide +kernel)
    · exact v2061_mg_checked.trans (by decide +kernel)
  upper_error := v2061_upper_checked
  lower_error := reuse_lower_error 24 34 Primitive.Addresses.material2061

def v2062_pa : Scalar.QComplex := ((999999823825953032606452878247 : Int)/10^30,(-593589136438237276955542367 : Int)/10^30)
theorem v2062_pa_checked : Scalar.distance (sourceCoefficient 24 35 1 0) v2062_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2062_pb : Scalar.QComplex := ((-256120368107304301665587 : Int)/10^30,(-431477443341303068568294649 : Int)/10^30)
theorem v2062_pb_checked : Scalar.distance (sourceCoefficient 24 35 1 1) v2062_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2062_pg : Scalar.QComplex := ((-93086413320203213062460 : Int)/10^30,(55255093431385678250 : Int)/10^30)
theorem v2062_pg_checked : Scalar.distance (sourceCoefficient 24 35 1 2) v2062_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2062_mb : Scalar.QComplex := ((-628465873322870142403783 : Int)/10^30,(-431477061662188975845686942 : Int)/10^30)
theorem v2062_mb_checked : Scalar.distance (sourceCoefficient 24 35 3 1) v2062_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2062_mg : Scalar.QComplex := ((-93086330977220240438645 : Int)/10^30,(135584455096299840140 : Int)/10^30)
theorem v2062_mg_checked : Scalar.distance (sourceCoefficient 24 35 3 2) v2062_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2062_upper : Scalar.QComplex := ((999997309962684168256307898903 : Int)/10^30,(-2319497229005183963069482095 : Int)/10^30)
theorem v2062_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 35 5) 1) 14) v2062_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2062 : Material (24 : Basis) (35 : Basis) where
  plus := ![v2062_pa,v2062_pb,v2062_pg]
  minus := ![(Primitive.Addresses.material2062 1).one,v2062_mb,v2062_mg]
  upper := v2062_upper
  lower := (Primitive.Addresses.material2062 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2062_pa_checked.trans (by decide +kernel)
    · exact v2062_pb_checked.trans (by decide +kernel)
    · exact v2062_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 35 Primitive.Addresses.material2062
    · exact v2062_mb_checked.trans (by decide +kernel)
    · exact v2062_mg_checked.trans (by decide +kernel)
  upper_error := v2062_upper_checked
  lower_error := reuse_lower_error 24 35 Primitive.Addresses.material2062

def v2063_pa : Scalar.QComplex := ((999999814112172075105978280119 : Int)/10^30,(-609734057844486388179227898 : Int)/10^30)
theorem v2063_pa_checked : Scalar.distance (sourceCoefficient 24 36 1 0) v2063_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2063_pb : Scalar.QComplex := ((-263086538520362048828869 : Int)/10^30,(-431477438780166454017705193 : Int)/10^30)
theorem v2063_pb_checked : Scalar.distance (sourceCoefficient 24 36 1 1) v2063_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2063_pg : Scalar.QComplex := ((-93086412376085615585054 : Int)/10^30,(56757966498871010255 : Int)/10^30)
theorem v2063_pg_checked : Scalar.distance (sourceCoefficient 24 36 1 2) v2063_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2063_mb : Scalar.QComplex := ((-635432037206048802680196 : Int)/10^30,(-431477051089562737814532083 : Int)/10^30)
theorem v2063_mb_checked : Scalar.distance (sourceCoefficient 24 36 3 1) v2063_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2063_mg : Scalar.QComplex := ((-93086328736191224149831 : Int)/10^30,(137087326789465879283 : Int)/10^30)
theorem v2063_mg_checked : Scalar.distance (sourceCoefficient 24 36 3 2) v2063_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2063_upper : Scalar.QComplex := ((999997272384247986934254122837 : Int)/10^30,(-2335642109600364450055330814 : Int)/10^30)
theorem v2063_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 36 5) 1) 14) v2063_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2063 : Material (24 : Basis) (36 : Basis) where
  plus := ![v2063_pa,v2063_pb,v2063_pg]
  minus := ![(Primitive.Addresses.material2063 1).one,v2063_mb,v2063_mg]
  upper := v2063_upper
  lower := (Primitive.Addresses.material2063 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2063_pa_checked.trans (by decide +kernel)
    · exact v2063_pb_checked.trans (by decide +kernel)
    · exact v2063_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 36 Primitive.Addresses.material2063
    · exact v2063_mb_checked.trans (by decide +kernel)
    · exact v2063_mg_checked.trans (by decide +kernel)
  upper_error := v2063_upper_checked
  lower_error := reuse_lower_error 24 36 Primitive.Addresses.material2063

def v2064_pa : Scalar.QComplex := ((999999809884866824513900983466 : Int)/10^30,(-616628113377267559448689355 : Int)/10^30)
theorem v2064_pa_checked : Scalar.distance (sourceCoefficient 24 37 1 0) v2064_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2064_pb : Scalar.QComplex := ((-266061168392972738874675 : Int)/10^30,(-431477436786823628791457277 : Int)/10^30)
theorem v2064_pb_checked : Scalar.distance (sourceCoefficient 24 37 1 1) v2064_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2064_pg : Scalar.QComplex := ((-93086411964312573615138 : Int)/10^30,(57399709503166585499 : Int)/10^30)
theorem v2064_pg_checked : Scalar.distance (sourceCoefficient 24 37 1 2) v2064_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2064_mb : Scalar.QComplex := ((-638406664250903762509855 : Int)/10^30,(-431477046529249047094067509 : Int)/10^30)
theorem v2064_mb_checked : Scalar.distance (sourceCoefficient 24 37 3 1) v2064_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2064_mg : Scalar.QComplex := ((-93086327770623025826739 : Int)/10^30,(137729069199469615273 : Int)/10^30)
theorem v2064_mg_checked : Scalar.distance (sourceCoefficient 24 37 3 2) v2064_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2064_upper : Scalar.QComplex := ((999997256258434606668862854778 : Int)/10^30,(-2342536147569314373512444360 : Int)/10^30)
theorem v2064_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 37 5) 1) 14) v2064_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2064 : Material (24 : Basis) (37 : Basis) where
  plus := ![v2064_pa,v2064_pb,v2064_pg]
  minus := ![(Primitive.Addresses.material2064 1).one,v2064_mb,v2064_mg]
  upper := v2064_upper
  lower := (Primitive.Addresses.material2064 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2064_pa_checked.trans (by decide +kernel)
    · exact v2064_pb_checked.trans (by decide +kernel)
    · exact v2064_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 37 Primitive.Addresses.material2064
    · exact v2064_mb_checked.trans (by decide +kernel)
    · exact v2064_mg_checked.trans (by decide +kernel)
  upper_error := v2064_upper_checked
  lower_error := reuse_lower_error 24 37 Primitive.Addresses.material2064

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
