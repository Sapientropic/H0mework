import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B024
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B025

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v593_pa : Scalar.QComplex := ((999999995883199146756965082554 : Int)/10^30,(-90739195993451587170695675 : Int)/10^30)
theorem v593_pa_checked : Scalar.distance (sourceCoefficient 6 33 1 0) v593_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v593_pb : Scalar.QComplex := ((-39151921587180480047746 : Int)/10^30,(-431477499853815198529374110 : Int)/10^30)
theorem v593_pb_checked : Scalar.distance (sourceCoefficient 6 33 1 1) v593_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v593_pg : Scalar.QComplex := ((-93086427424270554449504 : Int)/10^30,(8446587617154011751 : Int)/10^30)
theorem v593_pg_checked : Scalar.distance (sourceCoefficient 6 33 1 2) v593_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v593_mb : Scalar.QComplex := ((-411497556357767647185196 : Int)/10^30,(-431477305408677514401176450 : Int)/10^30)
theorem v593_mb_checked : Scalar.distance (sourceCoefficient 6 33 3 1) v593_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v593_mg : Scalar.QComplex := ((-93086385474914671076088 : Int)/10^30,(88775978882189034681 : Int)/10^30)
theorem v593_mg_checked : Scalar.distance (sourceCoefficient 6 33 3 2) v593_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v593_upper : Scalar.QComplex := ((999998349893053040802692891251 : Int)/10^30,(-1816648334451513544010559787 : Int)/10^30)
theorem v593_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 33 5) 1) 14) v593_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material593 : Material (6 : Basis) (33 : Basis) where
  plus := ![v593_pa,v593_pb,v593_pg]
  minus := ![(Primitive.Addresses.material593 1).one,v593_mb,v593_mg]
  upper := v593_upper
  lower := (Primitive.Addresses.material593 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v593_pa_checked.trans (by decide +kernel)
    · exact v593_pb_checked.trans (by decide +kernel)
    · exact v593_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 33 Primitive.Addresses.material593
    · exact v593_mb_checked.trans (by decide +kernel)
    · exact v593_mg_checked.trans (by decide +kernel)
  upper_error := v593_upper_checked
  lower_error := reuse_lower_error 6 33 Primitive.Addresses.material593

def v594_pa : Scalar.QComplex := ((999999994285536339127516982438 : Int)/10^30,(-106906161137185498995101706 : Int)/10^30)
theorem v594_pa_checked : Scalar.distance (sourceCoefficient 6 34 1 0) v594_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v594_pb : Scalar.QComplex := ((-46127603185317069271484 : Int)/10^30,(-431477497938870906101863299 : Int)/10^30)
theorem v594_pb_checked : Scalar.distance (sourceCoefficient 6 34 1 1) v594_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v594_pg : Scalar.QComplex := ((-93086427143346327332981 : Int)/10^30,(9951512636739017839 : Int)/10^30)
theorem v594_pg_checked : Scalar.distance (sourceCoefficient 6 34 1 2) v594_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v594_mb : Scalar.QComplex := ((-418473233706028494548781 : Int)/10^30,(-431477297474034888839595236 : Int)/10^30)
theorem v594_mb_checked : Scalar.distance (sourceCoefficient 6 34 3 1) v594_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v594_mg : Scalar.QComplex := ((-93086383895308035965429 : Int)/10^30,(90280903098996721862 : Int)/10^30)
theorem v594_mg_checked : Scalar.distance (sourceCoefficient 6 34 3 2) v594_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v594_upper : Scalar.QComplex := ((999998320392677430240544854463 : Int)/10^30,(-1832815272759030912243227125 : Int)/10^30)
theorem v594_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 34 5) 1) 14) v594_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material594 : Material (6 : Basis) (34 : Basis) where
  plus := ![v594_pa,v594_pb,v594_pg]
  minus := ![(Primitive.Addresses.material594 1).one,v594_mb,v594_mg]
  upper := v594_upper
  lower := (Primitive.Addresses.material594 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v594_pa_checked.trans (by decide +kernel)
    · exact v594_pb_checked.trans (by decide +kernel)
    · exact v594_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 34 Primitive.Addresses.material594
    · exact v594_mb_checked.trans (by decide +kernel)
    · exact v594_mg_checked.trans (by decide +kernel)
  upper_error := v594_upper_checked
  lower_error := reuse_lower_error 6 34 Primitive.Addresses.material594

def v595_pa : Scalar.QComplex := ((999999987475578103968721415490 : Int)/10^30,(-158268264775985376124043183 : Int)/10^30)
theorem v595_pa_checked : Scalar.distance (sourceCoefficient 6 35 1 0) v595_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v595_pb : Scalar.QComplex := ((-68289194623184636292371 : Int)/10^30,(-431477490857432598485778114 : Int)/10^30)
theorem v595_pb_checked : Scalar.distance (sourceCoefficient 6 35 1 1) v595_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v595_pg : Scalar.QComplex := ((-93086426062518579792903 : Int)/10^30,(14732627311630516520 : Int)/10^30)
theorem v595_pg_checked : Scalar.distance (sourceCoefficient 6 35 1 2) v595_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v595_mb : Scalar.QComplex := ((-440634810781160411157038 : Int)/10^30,(-431477271268143928113286768 : Int)/10^30)
theorem v595_mb_checked : Scalar.distance (sourceCoefficient 6 35 3 1) v595_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v595_mg : Scalar.QComplex := ((-93086378688594059846959 : Int)/10^30,(95062015060955051893 : Int)/10^30)
theorem v595_mg_checked : Scalar.distance (sourceCoefficient 6 35 3 2) v595_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v595_upper : Scalar.QComplex := ((999998224936397990789831322236 : Int)/10^30,(-1884177288146640716598625414 : Int)/10^30)
theorem v595_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 35 5) 1) 14) v595_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material595 : Material (6 : Basis) (35 : Basis) where
  plus := ![v595_pa,v595_pb,v595_pg]
  minus := ![(Primitive.Addresses.material595 1).one,v595_mb,v595_mg]
  upper := v595_upper
  lower := (Primitive.Addresses.material595 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v595_pa_checked.trans (by decide +kernel)
    · exact v595_pb_checked.trans (by decide +kernel)
    · exact v595_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 35 Primitive.Addresses.material595
    · exact v595_mb_checked.trans (by decide +kernel)
    · exact v595_mg_checked.trans (by decide +kernel)
  upper_error := v595_upper_checked
  lower_error := reuse_lower_error 6 35 Primitive.Addresses.material595

def v596_pa : Scalar.QComplex := ((999999984790019656494541960514 : Int)/10^30,(-174413188881080360886607844 : Int)/10^30)
theorem v596_pa_checked : Scalar.distance (sourceCoefficient 6 36 1 0) v596_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v596_pb : Scalar.QComplex := ((-75255365812569920168368 : Int)/10^30,(-431477488317975956578565816 : Int)/10^30)
theorem v596_pb_checked : Scalar.distance (sourceCoefficient 6 36 1 1) v596_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v596_pg : Scalar.QComplex := ((-93086425663594428461983 : Int)/10^30,(16235500588470786142 : Int)/10^30)
theorem v596_pg_checked : Scalar.distance (sourceCoefficient 6 36 1 2) v596_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v596_mb : Scalar.QComplex := ((-447600977185285082389260 : Int)/10^30,(-431477262717196240025960224 : Int)/10^30)
theorem v596_mb_checked : Scalar.distance (sourceCoefficient 6 36 3 1) v596_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v596_mg : Scalar.QComplex := ((-93086376992758106040313 : Int)/10^30,(96564887433953340124 : Int)/10^30)
theorem v596_mg_checked : Scalar.distance (sourceCoefficient 6 36 3 2) v596_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v596_upper : Scalar.QComplex := ((999998194386169193819096672906 : Int)/10^30,(-1900322183570737514449350832 : Int)/10^30)
theorem v596_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 36 5) 1) 14) v596_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material596 : Material (6 : Basis) (36 : Basis) where
  plus := ![v596_pa,v596_pb,v596_pg]
  minus := ![(Primitive.Addresses.material596 1).one,v596_mb,v596_mg]
  upper := v596_upper
  lower := (Primitive.Addresses.material596 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v596_pa_checked.trans (by decide +kernel)
    · exact v596_pb_checked.trans (by decide +kernel)
    · exact v596_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 36 Primitive.Addresses.material596
    · exact v596_mb_checked.trans (by decide +kernel)
    · exact v596_mg_checked.trans (by decide +kernel)
  upper_error := v596_upper_checked
  lower_error := reuse_lower_error 6 36 Primitive.Addresses.material596

def v597_pa : Scalar.QComplex := ((999999983563841211239375296640 : Int)/10^30,(-181307245600869282185392414 : Int)/10^30)
theorem v597_pa_checked : Scalar.distance (sourceCoefficient 6 37 1 0) v597_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v597_pb : Scalar.QComplex := ((-78229996026625377723163 : Int)/10^30,(-431477487187912281054613179 : Int)/10^30)
theorem v597_pb_checked : Scalar.distance (sourceCoefficient 6 37 1 1) v597_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v597_pg : Scalar.QComplex := ((-93086425484624867333237 : Int)/10^30,(16877243684844955338 : Int)/10^30)
theorem v597_pg_checked : Scalar.distance (sourceCoefficient 6 37 1 2) v597_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v597_mb : Scalar.QComplex := ((-450575605316555708135911 : Int)/10^30,(-431477259020161082918053430 : Int)/10^30)
theorem v597_mb_checked : Scalar.distance (sourceCoefficient 6 37 3 1) v597_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v597_mg : Scalar.QComplex := ((-93086376259993222415336 : Int)/10^30,(97206630136934554667 : Int)/10^30)
theorem v597_mg_checked : Scalar.distance (sourceCoefficient 6 37 3 2) v597_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v597_upper : Scalar.QComplex := ((999998181261476100397084558521 : Int)/10^30,(-1907216227906366025941686299 : Int)/10^30)
theorem v597_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 37 5) 1) 14) v597_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material597 : Material (6 : Basis) (37 : Basis) where
  plus := ![v597_pa,v597_pb,v597_pg]
  minus := ![(Primitive.Addresses.material597 1).one,v597_mb,v597_mg]
  upper := v597_upper
  lower := (Primitive.Addresses.material597 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v597_pa_checked.trans (by decide +kernel)
    · exact v597_pb_checked.trans (by decide +kernel)
    · exact v597_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 37 Primitive.Addresses.material597
    · exact v597_mb_checked.trans (by decide +kernel)
    · exact v597_mg_checked.trans (by decide +kernel)
  upper_error := v597_upper_checked
  lower_error := reuse_lower_error 6 37 Primitive.Addresses.material597

def v598_pa : Scalar.QComplex := ((999999979067729510044664313519 : Int)/10^30,(-204608261176695217787626179 : Int)/10^30)
theorem v598_pa_checked : Scalar.distance (sourceCoefficient 6 38 1 0) v598_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v598_pb : Scalar.QComplex := ((-88283859415485777562424 : Int)/10^30,(-431477483166059187228035719 : Int)/10^30)
theorem v598_pb_checked : Scalar.distance (sourceCoefficient 6 38 1 1) v598_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v598_pg : Scalar.QComplex := ((-93086424841526552312387 : Int)/10^30,(19046251924661171671 : Int)/10^30)
theorem v598_pg_checked : Scalar.distance (sourceCoefficient 6 38 1 2) v598_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v598_mb : Scalar.QComplex := ((-460629461491225201613460 : Int)/10^30,(-431477246322278191222632234 : Int)/10^30)
theorem v598_mb_checked : Scalar.distance (sourceCoefficient 6 38 3 1) v598_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v598_mg : Scalar.QComplex := ((-93086373745138724392739 : Int)/10^30,(99375637014164992953 : Int)/10^30)
theorem v598_mg_checked : Scalar.distance (sourceCoefficient 6 38 3 2) v598_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v598_upper : Scalar.QComplex := ((999998136549932063377573523334 : Int)/10^30,(-1930517201018185478718836158 : Int)/10^30)
theorem v598_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 38 5) 1) 14) v598_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material598 : Material (6 : Basis) (38 : Basis) where
  plus := ![v598_pa,v598_pb,v598_pg]
  minus := ![(Primitive.Addresses.material598 1).one,v598_mb,v598_mg]
  upper := v598_upper
  lower := (Primitive.Addresses.material598 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v598_pa_checked.trans (by decide +kernel)
    · exact v598_pb_checked.trans (by decide +kernel)
    · exact v598_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 38 Primitive.Addresses.material598
    · exact v598_mb_checked.trans (by decide +kernel)
    · exact v598_mg_checked.trans (by decide +kernel)
  upper_error := v598_upper_checked
  lower_error := reuse_lower_error 6 38 Primitive.Addresses.material598

def v599_pa : Scalar.QComplex := ((999999976210599126890212962345 : Int)/10^30,(-218125654567004062374751780 : Int)/10^30)
theorem v599_pa_checked : Scalar.distance (sourceCoefficient 6 39 1 0) v599_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v599_pb : Scalar.QComplex := ((-94116310145341871807923 : Int)/10^30,(-431477480689739303604105909 : Int)/10^30)
theorem v599_pb_checked : Scalar.distance (sourceCoefficient 6 39 1 1) v599_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v599_pg : Scalar.QComplex := ((-93086424441427414592256 : Int)/10^30,(20304537745621108285 : Int)/10^30)
theorem v599_pg_checked : Scalar.distance (sourceCoefficient 6 39 1 2) v599_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v599_mb : Scalar.QComplex := ((-466461907912440802706984 : Int)/10^30,(-431477238812816933609549774 : Int)/10^30)
theorem v599_mb_checked : Scalar.distance (sourceCoefficient 6 39 3 1) v599_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v599_mg : Scalar.QComplex := ((-93086372259195743249022 : Int)/10^30,(100633922021340075865 : Int)/10^30)
theorem v599_mg_checked : Scalar.distance (sourceCoefficient 6 39 3 2) v599_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v599_upper : Scalar.QComplex := ((999998110363011232259269940561 : Int)/10^30,(-1944034569344776888529007875 : Int)/10^30)
theorem v599_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 39 5) 1) 14) v599_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material599 : Material (6 : Basis) (39 : Basis) where
  plus := ![v599_pa,v599_pb,v599_pg]
  minus := ![(Primitive.Addresses.material599 1).one,v599_mb,v599_mg]
  upper := v599_upper
  lower := (Primitive.Addresses.material599 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v599_pa_checked.trans (by decide +kernel)
    · exact v599_pb_checked.trans (by decide +kernel)
    · exact v599_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 39 Primitive.Addresses.material599
    · exact v599_mb_checked.trans (by decide +kernel)
    · exact v599_mg_checked.trans (by decide +kernel)
  upper_error := v599_upper_checked
  lower_error := reuse_lower_error 6 39 Primitive.Addresses.material599

def v600_pa : Scalar.QComplex := ((999999970992952159529916369525 : Int)/10^30,(-240861152616048366450796973 : Int)/10^30)
theorem v600_pa_checked : Scalar.distance (sourceCoefficient 6 40 1 0) v600_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v600_pb : Scalar.QComplex := ((-103926165281090508178761 : Int)/10^30,(-431477476287617629455947745 : Int)/10^30)
theorem v600_pb_checked : Scalar.distance (sourceCoefficient 6 40 1 1) v600_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v600_pg : Scalar.QComplex := ((-93086423723727190200478 : Int)/10^30,(22420903961367033873 : Int)/10^30)
theorem v600_pg_checked : Scalar.distance (sourceCoefficient 6 40 1 2) v600_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v600_mb : Scalar.QComplex := ((-476271755596699298921255 : Int)/10^30,(-431477225945233735895608902 : Int)/10^30)
theorem v600_mb_checked : Scalar.distance (sourceCoefficient 6 40 3 1) v600_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v600_mg : Scalar.QComplex := ((-93086369715167059497107 : Int)/10^30,(102750286829723166984 : Int)/10^30)
theorem v600_mg_checked : Scalar.distance (sourceCoefficient 6 40 3 2) v600_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v600_upper : Scalar.QComplex := ((999998065905964951592020919096 : Int)/10^30,(-1966770024526782223332258059 : Int)/10^30)
theorem v600_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 40 5) 1) 14) v600_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material600 : Material (6 : Basis) (40 : Basis) where
  plus := ![v600_pa,v600_pb,v600_pg]
  minus := ![(Primitive.Addresses.material600 1).one,v600_mb,v600_mg]
  upper := v600_upper
  lower := (Primitive.Addresses.material600 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v600_pa_checked.trans (by decide +kernel)
    · exact v600_pb_checked.trans (by decide +kernel)
    · exact v600_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 40 Primitive.Addresses.material600
    · exact v600_mb_checked.trans (by decide +kernel)
    · exact v600_mg_checked.trans (by decide +kernel)
  upper_error := v600_upper_checked
  lower_error := reuse_lower_error 6 40 Primitive.Addresses.material600

def v601_pa : Scalar.QComplex := ((999999967399427540925778292803 : Int)/10^30,(-255345146527892945488719359 : Int)/10^30)
theorem v601_pa_checked : Scalar.distance (sourceCoefficient 6 41 1 0) v601_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v601_pb : Scalar.QComplex := ((-110175682242241579633932 : Int)/10^30,(-431477473328109997284193501 : Int)/10^30)
theorem v601_pb_checked : Scalar.distance (sourceCoefficient 6 41 1 1) v601_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v601_pg : Scalar.QComplex := ((-93086423237232731564531 : Int)/10^30,(23769167156157106791 : Int)/10^30)
theorem v601_pg_checked : Scalar.distance (sourceCoefficient 6 41 1 2) v601_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v601_mb : Scalar.QComplex := ((-482521267676947793416513 : Int)/10^30,(-431477217592675536005782171 : Int)/10^30)
theorem v601_mb_checked : Scalar.distance (sourceCoefficient 6 41 3 1) v601_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v601_mg : Scalar.QComplex := ((-93086368065182368421578 : Int)/10^30,(104098549102670426904 : Int)/10^30)
theorem v601_mg_checked : Scalar.distance (sourceCoefficient 6 41 3 2) v601_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v601_upper : Scalar.QComplex := ((999998037314386170940386097177 : Int)/10^30,(-1981253990664321790416129420 : Int)/10^30)
theorem v601_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 41 5) 1) 14) v601_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material601 : Material (6 : Basis) (41 : Basis) where
  plus := ![v601_pa,v601_pb,v601_pg]
  minus := ![(Primitive.Addresses.material601 1).one,v601_mb,v601_mg]
  upper := v601_upper
  lower := (Primitive.Addresses.material601 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v601_pa_checked.trans (by decide +kernel)
    · exact v601_pb_checked.trans (by decide +kernel)
    · exact v601_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 41 Primitive.Addresses.material601
    · exact v601_mb_checked.trans (by decide +kernel)
    · exact v601_mg_checked.trans (by decide +kernel)
  upper_error := v601_upper_checked
  lower_error := reuse_lower_error 6 41 Primitive.Addresses.material601

def v602_pa : Scalar.QComplex := ((999999964347810398067979333527 : Int)/10^30,(-267028796074103996475617771 : Int)/10^30)
theorem v602_pa_checked : Scalar.distance (sourceCoefficient 6 42 1 0) v602_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v602_pb : Scalar.QComplex := ((-115216913682671254885502 : Int)/10^30,(-431477470852850633914713876 : Int)/10^30)
theorem v602_pb_checked : Scalar.distance (sourceCoefficient 6 42 1 1) v602_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v602_pg : Scalar.QComplex := ((-93086422828195952214714 : Int)/10^30,(24856756304855944591 : Int)/10^30)
theorem v602_pg_checked : Scalar.distance (sourceCoefficient 6 42 1 2) v602_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v602_mb : Scalar.QComplex := ((-487562495104259258692987 : Int)/10^30,(-431477210767061409833314144 : Int)/10^30)
theorem v602_mb_checked : Scalar.distance (sourceCoefficient 6 42 3 1) v602_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v602_mg : Scalar.QComplex := ((-93086366717605289244667 : Int)/10^30,(105186137493429801118 : Int)/10^30)
theorem v602_mg_checked : Scalar.distance (sourceCoefficient 6 42 3 2) v602_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v602_upper : Scalar.QComplex := ((999998014097854388754673971593 : Int)/10^30,(-1992937617542294952179352860 : Int)/10^30)
theorem v602_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 42 5) 1) 14) v602_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material602 : Material (6 : Basis) (42 : Basis) where
  plus := ![v602_pa,v602_pb,v602_pg]
  minus := ![(Primitive.Addresses.material602 1).one,v602_mb,v602_mg]
  upper := v602_upper
  lower := (Primitive.Addresses.material602 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v602_pa_checked.trans (by decide +kernel)
    · exact v602_pb_checked.trans (by decide +kernel)
    · exact v602_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 42 Primitive.Addresses.material602
    · exact v602_mb_checked.trans (by decide +kernel)
    · exact v602_mg_checked.trans (by decide +kernel)
  upper_error := v602_upper_checked
  lower_error := reuse_lower_error 6 42 Primitive.Addresses.material602

def v603_pa : Scalar.QComplex := ((999999960095014205971680949042 : Int)/10^30,(-282506583986371451930708397 : Int)/10^30)
theorem v603_pa_checked : Scalar.distance (sourceCoefficient 6 43 1 0) v603_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v603_pb : Scalar.QComplex := ((-121895230261422628287641 : Int)/10^30,(-431477467452849197142100143 : Int)/10^30)
theorem v603_pb_checked : Scalar.distance (sourceCoefficient 6 43 1 1) v603_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v603_pg : Scalar.QComplex := ((-93086422263501078799396 : Int)/10^30,(26297528218577094852 : Int)/10^30)
theorem v603_pg_checked : Scalar.distance (sourceCoefficient 6 43 1 2) v603_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v603_mb : Scalar.QComplex := ((-494240806262320046125935 : Int)/10^30,(-431477201603974811787408426 : Int)/10^30)
theorem v603_mb_checked : Scalar.distance (sourceCoefficient 6 43 3 1) v603_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v603_mg : Scalar.QComplex := ((-93086364909589354507871 : Int)/10^30,(106626908383379478526 : Int)/10^30)
theorem v603_mg_checked : Scalar.distance (sourceCoefficient 6 43 3 2) v603_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v603_upper : Scalar.QComplex := ((999997983131806728076015477843 : Int)/10^30,(-2008415375062275044096771300 : Int)/10^30)
theorem v603_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 43 5) 1) 14) v603_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material603 : Material (6 : Basis) (43 : Basis) where
  plus := ![v603_pa,v603_pb,v603_pg]
  minus := ![(Primitive.Addresses.material603 1).one,v603_mb,v603_mg]
  upper := v603_upper
  lower := (Primitive.Addresses.material603 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v603_pa_checked.trans (by decide +kernel)
    · exact v603_pb_checked.trans (by decide +kernel)
    · exact v603_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 43 Primitive.Addresses.material603
    · exact v603_mb_checked.trans (by decide +kernel)
    · exact v603_mg_checked.trans (by decide +kernel)
  upper_error := v603_upper_checked
  lower_error := reuse_lower_error 6 43 Primitive.Addresses.material603

def v604_pa : Scalar.QComplex := ((999999958423572888260062300622 : Int)/10^30,(-288362363173283388912487657 : Int)/10^30)
theorem v604_pa_checked : Scalar.distance (sourceCoefficient 6 44 1 0) v604_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v604_pb : Scalar.QComplex := ((-124421866962450210385422 : Int)/10^30,(-431477466130576998857607185 : Int)/10^30)
theorem v604_pb_checked : Scalar.distance (sourceCoefficient 6 44 1 1) v604_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v604_pg : Scalar.QComplex := ((-93086422043074136588475 : Int)/10^30,(26842621755706783398 : Int)/10^30)
theorem v604_pg_checked : Scalar.distance (sourceCoefficient 6 44 1 2) v604_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v604_mb : Scalar.QComplex := ((-496767440881503957239013 : Int)/10^30,(-431477198101329428351209392 : Int)/10^30)
theorem v604_mb_checked : Scalar.distance (sourceCoefficient 6 44 3 1) v604_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v604_mg : Scalar.QComplex := ((-93086364218771321930622 : Int)/10^30,(107172001527327407727 : Int)/10^30)
theorem v604_mg_checked : Scalar.distance (sourceCoefficient 6 44 3 2) v604_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v604_upper : Scalar.QComplex := ((999997971353824255307973961205 : Int)/10^30,(-2014271142642935667918221775 : Int)/10^30)
theorem v604_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 44 5) 1) 14) v604_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material604 : Material (6 : Basis) (44 : Basis) where
  plus := ![v604_pa,v604_pb,v604_pg]
  minus := ![(Primitive.Addresses.material604 1).one,v604_mb,v604_mg]
  upper := v604_upper
  lower := (Primitive.Addresses.material604 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v604_pa_checked.trans (by decide +kernel)
    · exact v604_pb_checked.trans (by decide +kernel)
    · exact v604_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 44 Primitive.Addresses.material604
    · exact v604_mb_checked.trans (by decide +kernel)
    · exact v604_mg_checked.trans (by decide +kernel)
  upper_error := v604_upper_checked
  lower_error := reuse_lower_error 6 44 Primitive.Addresses.material604

def v605_pa : Scalar.QComplex := ((999999957579236329352919954590 : Int)/10^30,(-291275686492664488046574565 : Int)/10^30)
theorem v605_pa_checked : Scalar.distance (sourceCoefficient 6 45 1 0) v605_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v605_pb : Scalar.QComplex := ((-125678900290938815262012 : Int)/10^30,(-431477465465381353547449565 : Int)/10^30)
theorem v605_pb_checked : Scalar.distance (sourceCoefficient 6 45 1 1) v605_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v605_pg : Scalar.QComplex := ((-93086421932021753038271 : Int)/10^30,(27113812601584092470 : Int)/10^30)
theorem v605_pg_checked : Scalar.distance (sourceCoefficient 6 45 1 2) v605_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v605_mb : Scalar.QComplex := ((-498024473167907722055190 : Int)/10^30,(-431477196351370882917604891 : Int)/10^30)
theorem v605_mb_checked : Scalar.distance (sourceCoefficient 6 45 3 1) v605_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v605_mg : Scalar.QComplex := ((-93086363873693493720473 : Int)/10^30,(107443192176394765455 : Int)/10^30)
theorem v605_mg_checked : Scalar.distance (sourceCoefficient 6 45 3 2) v605_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v605_upper : Scalar.QComplex := ((999997965481357199316154189403 : Int)/10^30,(-2017184460166015602771659034 : Int)/10^30)
theorem v605_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 45 5) 1) 14) v605_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material605 : Material (6 : Basis) (45 : Basis) where
  plus := ![v605_pa,v605_pb,v605_pg]
  minus := ![(Primitive.Addresses.material605 1).one,v605_mb,v605_mg]
  upper := v605_upper
  lower := (Primitive.Addresses.material605 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v605_pa_checked.trans (by decide +kernel)
    · exact v605_pb_checked.trans (by decide +kernel)
    · exact v605_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 45 Primitive.Addresses.material605
    · exact v605_mb_checked.trans (by decide +kernel)
    · exact v605_mg_checked.trans (by decide +kernel)
  upper_error := v605_upper_checked
  lower_error := reuse_lower_error 6 45 Primitive.Addresses.material605

def v606_pa : Scalar.QComplex := ((999999952678835924180693229815 : Int)/10^30,(-307639928995483361084994729 : Int)/10^30)
theorem v606_pa_checked : Scalar.distance (sourceCoefficient 6 46 1 0) v606_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v606_pb : Scalar.QComplex := ((-132739701942927521181900 : Int)/10^30,(-431477461638209954402436979 : Int)/10^30)
theorem v606_pb_checked : Scalar.distance (sourceCoefficient 6 46 1 1) v606_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v606_pg : Scalar.QComplex := ((-93086421291106735953139 : Int)/10^30,(28637101391580700434 : Int)/10^30)
theorem v606_pg_checked : Scalar.distance (sourceCoefficient 6 46 1 2) v606_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v606_mb : Scalar.QComplex := ((-505085268888160730301770 : Int)/10^30,(-431477186431047089838603288 : Int)/10^30)
theorem v606_mb_checked : Scalar.distance (sourceCoefficient 6 46 3 1) v606_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v606_mg : Scalar.QComplex := ((-93086361918249095890532 : Int)/10^30,(108966479846120545162 : Int)/10^30)
theorem v606_mg_checked : Scalar.distance (sourceCoefficient 6 46 3 2) v606_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v606_upper : Scalar.QComplex := ((999997932337766085332482773357 : Int)/10^30,(-2033548669838571008343255862 : Int)/10^30)
theorem v606_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 46 5) 1) 14) v606_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material606 : Material (6 : Basis) (46 : Basis) where
  plus := ![v606_pa,v606_pb,v606_pg]
  minus := ![(Primitive.Addresses.material606 1).one,v606_mb,v606_mg]
  upper := v606_upper
  lower := (Primitive.Addresses.material606 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v606_pa_checked.trans (by decide +kernel)
    · exact v606_pb_checked.trans (by decide +kernel)
    · exact v606_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 46 Primitive.Addresses.material606
    · exact v606_mb_checked.trans (by decide +kernel)
    · exact v606_mg_checked.trans (by decide +kernel)
  upper_error := v606_upper_checked
  lower_error := reuse_lower_error 6 46 Primitive.Addresses.material606

def v607_pa : Scalar.QComplex := ((999999951459582656692480867517 : Int)/10^30,(-311577971510251222385262026 : Int)/10^30)
theorem v607_pa_checked : Scalar.distance (sourceCoefficient 6 47 1 0) v607_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v607_pb : Scalar.QComplex := ((-134438878481214112899909 : Int)/10^30,(-431477460694205953682982106 : Int)/10^30)
theorem v607_pb_checked : Scalar.distance (sourceCoefficient 6 47 1 1) v607_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v607_pg : Scalar.QComplex := ((-93086421132529637398539 : Int)/10^30,(29003679679473282822 : Int)/10^30)
theorem v607_pg_checked : Scalar.distance (sourceCoefficient 6 47 1 2) v607_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v607_mb : Scalar.QComplex := ((-506784443979133304352608 : Int)/10^30,(-431477184020730616144081263 : Int)/10^30)
theorem v607_mb_checked : Scalar.distance (sourceCoefficient 6 47 3 1) v607_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v607_mg : Scalar.QComplex := ((-93086361443331504003339 : Int)/10^30,(109333057860674383507 : Int)/10^30)
theorem v607_mg_checked : Scalar.distance (sourceCoefficient 6 47 3 2) v607_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v607_upper : Scalar.QComplex := ((999997924321810509715665870640 : Int)/10^30,(-2037486704383766608973838337 : Int)/10^30)
theorem v607_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 47 5) 1) 14) v607_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material607 : Material (6 : Basis) (47 : Basis) where
  plus := ![v607_pa,v607_pb,v607_pg]
  minus := ![(Primitive.Addresses.material607 1).one,v607_mb,v607_mg]
  upper := v607_upper
  lower := (Primitive.Addresses.material607 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v607_pa_checked.trans (by decide +kernel)
    · exact v607_pb_checked.trans (by decide +kernel)
    · exact v607_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 47 Primitive.Addresses.material607
    · exact v607_mb_checked.trans (by decide +kernel)
    · exact v607_mg_checked.trans (by decide +kernel)
  upper_error := v607_upper_checked
  lower_error := reuse_lower_error 6 47 Primitive.Addresses.material607

def v608_pa : Scalar.QComplex := ((999999942536603970777999522772 : Int)/10^30,(-339008537881278320089323695 : Int)/10^30)
theorem v608_pa_checked : Scalar.distance (sourceCoefficient 6 48 1 0) v608_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v608_pb : Scalar.QComplex := ((-146274549171045333070826 : Int)/10^30,(-431477453871202244547340083 : Int)/10^30)
theorem v608_pb_checked : Scalar.distance (sourceCoefficient 6 48 1 1) v608_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v608_pg : Scalar.QComplex := ((-93086419981232303547854 : Int)/10^30,(31557092947817904099 : Int)/10^30)
theorem v608_pg_checked : Scalar.distance (sourceCoefficient 6 48 1 2) v608_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v608_mb : Scalar.QComplex := ((-518620104374058505522613 : Int)/10^30,(-431477166984078701020000279 : Int)/10^30)
theorem v608_mb_checked : Scalar.distance (sourceCoefficient 6 48 3 1) v608_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v608_mg : Scalar.QComplex := ((-93086358088553949716412 : Int)/10^30,(111886469184748801622 : Int)/10^30)
theorem v608_mg_checked : Scalar.distance (sourceCoefficient 6 48 3 2) v608_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v608_upper : Scalar.QComplex := ((999997868056176038679228400934 : Int)/10^30,(-2064917214499935592122267194 : Int)/10^30)
theorem v608_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 48 5) 1) 14) v608_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material608 : Material (6 : Basis) (48 : Basis) where
  plus := ![v608_pa,v608_pb,v608_pg]
  minus := ![(Primitive.Addresses.material608 1).one,v608_mb,v608_mg]
  upper := v608_upper
  lower := (Primitive.Addresses.material608 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v608_pa_checked.trans (by decide +kernel)
    · exact v608_pb_checked.trans (by decide +kernel)
    · exact v608_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 48 Primitive.Addresses.material608
    · exact v608_mb_checked.trans (by decide +kernel)
    · exact v608_mg_checked.trans (by decide +kernel)
  upper_error := v608_upper_checked
  lower_error := reuse_lower_error 6 48 Primitive.Addresses.material608

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
