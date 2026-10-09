import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B137
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B138

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3297_pa : Scalar.QComplex := ((999998885097796696729135849097 : Int)/10^30,(-1493252545150892685333116127 : Int)/10^30)
theorem v3297_pa_checked : Scalar.distance (sourceCoefficient 43 73 1 0) v3297_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3297_pb : Scalar.QComplex := ((-644304879565818677642182 : Int)/10^30,(-431477021968699959026665610 : Int)/10^30)
theorem v3297_pb_checked : Scalar.distance (sourceCoefficient 43 73 1 1) v3297_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3297_pg : Scalar.QComplex := ((-93086324175573195549666 : Int)/10^30,(139001545467045050279 : Int)/10^30)
theorem v3297_pg_checked : Scalar.distance (sourceCoefficient 43 73 1 2) v3297_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3297_mb : Scalar.QComplex := ((-1016649876616971427799369 : Int)/10^30,(-431476305303992555273859920 : Int)/10^30)
theorem v3297_mb_checked : Scalar.distance (sourceCoefficient 43 73 3 1) v3297_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3297_mg : Scalar.QComplex := ((-93086169563207108955561 : Int)/10^30,(219330799021526937339 : Int)/10^30)
theorem v3297_mg_checked : Scalar.distance (sourceCoefficient 43 73 3 2) v3297_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3297_upper : Scalar.QComplex := ((999994818498499346536611477773 : Int)/10^30,(-3219157677615236899061170360 : Int)/10^30)
theorem v3297_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 73 5) 1) 14) v3297_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3297 : Material (43 : Basis) (73 : Basis) where
  plus := ![v3297_pa,v3297_pb,v3297_pg]
  minus := ![(Primitive.Addresses.material3297 1).one,v3297_mb,v3297_mg]
  upper := v3297_upper
  lower := (Primitive.Addresses.material3297 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3297_pa_checked.trans (by decide +kernel)
    · exact v3297_pb_checked.trans (by decide +kernel)
    · exact v3297_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 73 Primitive.Addresses.material3297
    · exact v3297_mb_checked.trans (by decide +kernel)
    · exact v3297_mg_checked.trans (by decide +kernel)
  upper_error := v3297_upper_checked
  lower_error := reuse_lower_error 43 73 Primitive.Addresses.material3297

def v3298_pa : Scalar.QComplex := ((999998869163255329728348252587 : Int)/10^30,(-1503885703951201275278325220 : Int)/10^30)
theorem v3298_pa_checked : Scalar.distance (sourceCoefficient 43 74 1 0) v3298_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3298_pb : Scalar.QComplex := ((-648892847212087939727895 : Int)/10^30,(-431477014320543395917519501 : Int)/10^30)
theorem v3298_pb_checked : Scalar.distance (sourceCoefficient 43 74 1 1) v3298_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3298_pg : Scalar.QComplex := ((-93086322608926464749157 : Int)/10^30,(139991348112314380624 : Int)/10^30)
theorem v3298_pg_checked : Scalar.distance (sourceCoefficient 43 74 1 2) v3298_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3298_mb : Scalar.QComplex := ((-1021237835954916000920622 : Int)/10^30,(-431476293696629395584725869 : Int)/10^30)
theorem v3298_mb_checked : Scalar.distance (sourceCoefficient 43 74 3 1) v3298_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3298_mg : Scalar.QComplex := ((-93086167142405857678088 : Int)/10^30,(220320599946301937102 : Int)/10^30)
theorem v3298_mg_checked : Scalar.distance (sourceCoefficient 43 74 3 2) v3298_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3298_upper : Scalar.QComplex := ((999994784212114255461828473904 : Int)/10^30,(-3229790793077131685378277690 : Int)/10^30)
theorem v3298_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 74 5) 1) 14) v3298_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3298 : Material (43 : Basis) (74 : Basis) where
  plus := ![v3298_pa,v3298_pb,v3298_pg]
  minus := ![(Primitive.Addresses.material3298 1).one,v3298_mb,v3298_mg]
  upper := v3298_upper
  lower := (Primitive.Addresses.material3298 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3298_pa_checked.trans (by decide +kernel)
    · exact v3298_pb_checked.trans (by decide +kernel)
    · exact v3298_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 74 Primitive.Addresses.material3298
    · exact v3298_mb_checked.trans (by decide +kernel)
    · exact v3298_mg_checked.trans (by decide +kernel)
  upper_error := v3298_upper_checked
  lower_error := reuse_lower_error 43 74 Primitive.Addresses.material3298

def v3299_pa : Scalar.QComplex := ((999998846773250814890802142227 : Int)/10^30,(-1518700815973404078180228509 : Int)/10^30)
theorem v3299_pa_checked : Scalar.distance (sourceCoefficient 43 75 1 0) v3299_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3299_pb : Scalar.QComplex := ((-655285233066663203283004 : Int)/10^30,(-431477003555965438726660934 : Int)/10^30)
theorem v3299_pb_checked : Scalar.distance (sourceCoefficient 43 75 1 1) v3299_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3299_pg : Scalar.QComplex := ((-93086320405655265019301 : Int)/10^30,(141370433788196173950 : Int)/10^30)
theorem v3299_pg_checked : Scalar.distance (sourceCoefficient 43 75 1 2) v3299_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3299_mb : Scalar.QComplex := ((-1027630210139967905889647 : Int)/10^30,(-431476277415714356411205507 : Int)/10^30)
theorem v3299_mb_checked : Scalar.distance (sourceCoefficient 43 75 3 1) v3299_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3299_mg : Scalar.QComplex := ((-93086163749046651753952 : Int)/10^30,(221699683207363292253 : Int)/10^30)
theorem v3299_mg_checked : Scalar.distance (sourceCoefficient 43 75 3 2) v3299_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3299_upper : Scalar.QComplex := ((999994736252603754047628504538 : Int)/10^30,(-3244605844390848849250090282 : Int)/10^30)
theorem v3299_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 75 5) 1) 14) v3299_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3299 : Material (43 : Basis) (75 : Basis) where
  plus := ![v3299_pa,v3299_pb,v3299_pg]
  minus := ![(Primitive.Addresses.material3299 1).one,v3299_mb,v3299_mg]
  upper := v3299_upper
  lower := (Primitive.Addresses.material3299 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3299_pa_checked.trans (by decide +kernel)
    · exact v3299_pb_checked.trans (by decide +kernel)
    · exact v3299_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 75 Primitive.Addresses.material3299
    · exact v3299_mb_checked.trans (by decide +kernel)
    · exact v3299_mg_checked.trans (by decide +kernel)
  upper_error := v3299_upper_checked
  lower_error := reuse_lower_error 43 75 Primitive.Addresses.material3299

def v3300_pa : Scalar.QComplex := ((999998827818264101300004702402 : Int)/10^30,(-1531130986489195840709809112 : Int)/10^30)
theorem v3300_pa_checked : Scalar.distance (sourceCoefficient 43 76 1 0) v3300_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3300_pb : Scalar.QComplex := ((-660648570524372467300124 : Int)/10^30,(-431476994426855325891034709 : Int)/10^30)
theorem v3300_pb_checked : Scalar.distance (sourceCoefficient 43 76 1 1) v3300_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3300_pg : Scalar.QComplex := ((-93086318538677748110634 : Int)/10^30,(142527513800921719947 : Int)/10^30)
theorem v3300_pg_checked : Scalar.distance (sourceCoefficient 43 76 1 2) v3300_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3300_mb : Scalar.QComplex := ((-1032993537722650650250148 : Int)/10^30,(-431476263658288972509524597 : Int)/10^30)
theorem v3300_mb_checked : Scalar.distance (sourceCoefficient 43 76 3 1) v3300_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3300_mg : Scalar.QComplex := ((-93086160883561891973443 : Int)/10^30,(222856761178137556798 : Int)/10^30)
theorem v3300_mg_checked : Scalar.distance (sourceCoefficient 43 76 3 2) v3300_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3300_upper : Scalar.QComplex := ((999994695844298617686775015241 : Int)/10^30,(-3257035963678774294210892331 : Int)/10^30)
theorem v3300_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 76 5) 1) 14) v3300_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3300 : Material (43 : Basis) (76 : Basis) where
  plus := ![v3300_pa,v3300_pb,v3300_pg]
  minus := ![(Primitive.Addresses.material3300 1).one,v3300_mb,v3300_mg]
  upper := v3300_upper
  lower := (Primitive.Addresses.material3300 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3300_pa_checked.trans (by decide +kernel)
    · exact v3300_pb_checked.trans (by decide +kernel)
    · exact v3300_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 76 Primitive.Addresses.material3300
    · exact v3300_mb_checked.trans (by decide +kernel)
    · exact v3300_mg_checked.trans (by decide +kernel)
  upper_error := v3300_upper_checked
  lower_error := reuse_lower_error 43 76 Primitive.Addresses.material3300

def v3301_pa : Scalar.QComplex := ((999998823407997963103452680390 : Int)/10^30,(-1534008676541646500164080627 : Int)/10^30)
theorem v3301_pa_checked : Scalar.distance (sourceCoefficient 43 77 1 0) v3301_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3301_pb : Scalar.QComplex := ((-661890228692142904363927 : Int)/10^30,(-431476992300717337034926846 : Int)/10^30)
theorem v3301_pb_checked : Scalar.distance (sourceCoefficient 43 77 1 1) v3301_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3301_pg : Scalar.QComplex := ((-93086318104064585392517 : Int)/10^30,(142795387650861861033 : Int)/10^30)
theorem v3301_pg_checked : Scalar.distance (sourceCoefficient 43 77 1 2) v3301_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3301_mb : Scalar.QComplex := ((-1034235193593333678188917 : Int)/10^30,(-431476260460656698733818547 : Int)/10^30)
theorem v3301_mb_checked : Scalar.distance (sourceCoefficient 43 77 3 1) v3301_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3301_mg : Scalar.QComplex := ((-93086160217785823173671 : Int)/10^30,(223124634553284435936 : Int)/10^30)
theorem v3301_mg_checked : Scalar.distance (sourceCoefficient 43 77 3 2) v3301_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3301_upper : Scalar.QComplex := ((999994686467407079535985242124 : Int)/10^30,(-3259913641833524399450715229 : Int)/10^30)
theorem v3301_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 77 5) 1) 14) v3301_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3301 : Material (43 : Basis) (77 : Basis) where
  plus := ![v3301_pa,v3301_pb,v3301_pg]
  minus := ![(Primitive.Addresses.material3301 1).one,v3301_mb,v3301_mg]
  upper := v3301_upper
  lower := (Primitive.Addresses.material3301 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3301_pa_checked.trans (by decide +kernel)
    · exact v3301_pb_checked.trans (by decide +kernel)
    · exact v3301_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 77 Primitive.Addresses.material3301
    · exact v3301_mb_checked.trans (by decide +kernel)
    · exact v3301_mg_checked.trans (by decide +kernel)
  upper_error := v3301_upper_checked
  lower_error := reuse_lower_error 43 77 Primitive.Addresses.material3301

def v3302_pa : Scalar.QComplex := ((999998796720640231793718497556 : Int)/10^30,(-1551308245209569856884426827 : Int)/10^30)
theorem v3302_pa_checked : Scalar.distance (sourceCoefficient 43 78 1 0) v3302_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3302_pb : Scalar.QComplex := ((-669354601211055520715671 : Int)/10^30,(-431476979418784013971402516 : Int)/10^30)
theorem v3302_pb_checked : Scalar.distance (sourceCoefficient 43 78 1 1) v3302_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3302_pg : Scalar.QComplex := ((-93086315472382929328033 : Int)/10^30,(144405742468936138749 : Int)/10^30)
theorem v3302_pg_checked : Scalar.distance (sourceCoefficient 43 78 1 2) v3302_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3302_mb : Scalar.QComplex := ((-1041699552216390990008515 : Int)/10^30,(-431476241137310871239773420 : Int)/10^30)
theorem v3302_mb_checked : Scalar.distance (sourceCoefficient 43 78 3 1) v3302_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3302_mg : Scalar.QComplex := ((-93086156196441466695091 : Int)/10^30,(224734986500727275390 : Int)/10^30)
theorem v3302_mg_checked : Scalar.distance (sourceCoefficient 43 78 3 2) v3302_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3302_upper : Scalar.QComplex := ((999994629922602979684998866598 : Int)/10^30,(-3277213138675813989326228192 : Int)/10^30)
theorem v3302_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 78 5) 1) 14) v3302_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3302 : Material (43 : Basis) (78 : Basis) where
  plus := ![v3302_pa,v3302_pb,v3302_pg]
  minus := ![(Primitive.Addresses.material3302 1).one,v3302_mb,v3302_mg]
  upper := v3302_upper
  lower := (Primitive.Addresses.material3302 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3302_pa_checked.trans (by decide +kernel)
    · exact v3302_pb_checked.trans (by decide +kernel)
    · exact v3302_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 78 Primitive.Addresses.material3302
    · exact v3302_mb_checked.trans (by decide +kernel)
    · exact v3302_mg_checked.trans (by decide +kernel)
  upper_error := v3302_upper_checked
  lower_error := reuse_lower_error 43 78 Primitive.Addresses.material3302

def v3303_pa : Scalar.QComplex := ((999998788053316485969146008197 : Int)/10^30,(-1556885319544537945517301644 : Int)/10^30)
theorem v3303_pa_checked : Scalar.distance (sourceCoefficient 43 79 1 0) v3303_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3303_pb : Scalar.QComplex := ((-671760982594282817017019 : Int)/10^30,(-431476975229176955274531184 : Int)/10^30)
theorem v3303_pb_checked : Scalar.distance (sourceCoefficient 43 79 1 1) v3303_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3303_pg : Scalar.QComplex := ((-93086314617047479193302 : Int)/10^30,(144924892319027962673 : Int)/10^30)
theorem v3303_pg_checked : Scalar.distance (sourceCoefficient 43 79 1 2) v3303_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3303_mb : Scalar.QComplex := ((-1044105929088170321514064 : Int)/10^30,(-431476234871106618194196163 : Int)/10^30)
theorem v3303_mb_checked : Scalar.distance (sourceCoefficient 43 79 3 1) v3303_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3303_mg : Scalar.QComplex := ((-93086154893103396052876 : Int)/10^30,(225254135419399913217 : Int)/10^30)
theorem v3303_mg_checked : Scalar.distance (sourceCoefficient 43 79 3 2) v3303_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3303_upper : Scalar.QComplex := ((999994611629767788897507049631 : Int)/10^30,(-3282790189745370493370656228 : Int)/10^30)
theorem v3303_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 79 5) 1) 14) v3303_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3303 : Material (43 : Basis) (79 : Basis) where
  plus := ![v3303_pa,v3303_pb,v3303_pg]
  minus := ![(Primitive.Addresses.material3303 1).one,v3303_mb,v3303_mg]
  upper := v3303_upper
  lower := (Primitive.Addresses.material3303 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3303_pa_checked.trans (by decide +kernel)
    · exact v3303_pb_checked.trans (by decide +kernel)
    · exact v3303_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 79 Primitive.Addresses.material3303
    · exact v3303_mb_checked.trans (by decide +kernel)
    · exact v3303_mg_checked.trans (by decide +kernel)
  upper_error := v3303_upper_checked
  lower_error := reuse_lower_error 43 79 Primitive.Addresses.material3303

def v3304_pa : Scalar.QComplex := ((999998774451857494812650610151 : Int)/10^30,(-1565597260805640621846656380 : Int)/10^30)
theorem v3304_pa_checked : Scalar.distance (sourceCoefficient 43 80 1 0) v3304_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3304_pb : Scalar.QComplex := ((-675519988099530813535403 : Int)/10^30,(-431476968648788258414830898 : Int)/10^30)
theorem v3304_pb_checked : Scalar.distance (sourceCoefficient 43 80 1 1) v3304_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3304_pg : Scalar.QComplex := ((-93086313274169366071084 : Int)/10^30,(145735855686842537022 : Int)/10^30)
theorem v3304_pg_checked : Scalar.distance (sourceCoefficient 43 80 1 2) v3304_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3304_mb : Scalar.QComplex := ((-1047864927515189697705406 : Int)/10^30,(-431476225046867919808195419 : Int)/10^30)
theorem v3304_mb_checked : Scalar.distance (sourceCoefficient 43 80 3 1) v3304_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3304_mg : Scalar.QComplex := ((-93086152850400920955809 : Int)/10^30,(226065097326412432232 : Int)/10^30)
theorem v3304_mg_checked : Scalar.distance (sourceCoefficient 43 80 3 2) v3304_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3304_upper : Scalar.QComplex := ((999994582992308779990621104499 : Int)/10^30,(-3291502094556175733781136366 : Int)/10^30)
theorem v3304_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 80 5) 1) 14) v3304_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3304 : Material (43 : Basis) (80 : Basis) where
  plus := ![v3304_pa,v3304_pb,v3304_pg]
  minus := ![(Primitive.Addresses.material3304 1).one,v3304_mb,v3304_mg]
  upper := v3304_upper
  lower := (Primitive.Addresses.material3304 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3304_pa_checked.trans (by decide +kernel)
    · exact v3304_pb_checked.trans (by decide +kernel)
    · exact v3304_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 80 Primitive.Addresses.material3304
    · exact v3304_mb_checked.trans (by decide +kernel)
    · exact v3304_mg_checked.trans (by decide +kernel)
  upper_error := v3304_upper_checked
  lower_error := reuse_lower_error 43 80 Primitive.Addresses.material3304

def v3305_pa : Scalar.QComplex := ((999998733038829708373035078353 : Int)/10^30,(-1591829367549376161186407851 : Int)/10^30)
theorem v3305_pa_checked : Scalar.distance (sourceCoefficient 43 81 1 0) v3305_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3305_pb : Scalar.QComplex := ((-686838548354028321465497 : Int)/10^30,(-431476948571218404841175563 : Int)/10^30)
theorem v3305_pb_checked : Scalar.distance (sourceCoefficient 43 81 1 1) v3305_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3305_pg : Scalar.QComplex := ((-93086309180918793798032 : Int)/10^30,(148177708406370504873 : Int)/10^30)
theorem v3305_pg_checked : Scalar.distance (sourceCoefficient 43 81 1 2) v3305_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3305_mb : Scalar.QComplex := ((-1059183466229231415672536 : Int)/10^30,(-431476195201897811430384151 : Int)/10^30)
theorem v3305_mb_checked : Scalar.distance (sourceCoefficient 43 81 3 1) v3305_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3305_mg : Scalar.QComplex := ((-93086146649942952798330 : Int)/10^30,(228506945604436143711 : Int)/10^30)
theorem v3305_mg_checked : Scalar.distance (sourceCoefficient 43 81 3 2) v3305_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3305_upper : Scalar.QComplex := ((999994496305106191837777916966 : Int)/10^30,(-3317734090755140719182499572 : Int)/10^30)
theorem v3305_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 81 5) 1) 14) v3305_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3305 : Material (43 : Basis) (81 : Basis) where
  plus := ![v3305_pa,v3305_pb,v3305_pg]
  minus := ![(Primitive.Addresses.material3305 1).one,v3305_mb,v3305_mg]
  upper := v3305_upper
  lower := (Primitive.Addresses.material3305 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3305_pa_checked.trans (by decide +kernel)
    · exact v3305_pb_checked.trans (by decide +kernel)
    · exact v3305_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 81 Primitive.Addresses.material3305
    · exact v3305_mb_checked.trans (by decide +kernel)
    · exact v3305_mg_checked.trans (by decide +kernel)
  upper_error := v3305_upper_checked
  lower_error := reuse_lower_error 43 81 Primitive.Addresses.material3305

def v3306_pa : Scalar.QComplex := ((999998717166229353034579585850 : Int)/10^30,(-1601769613780785806712514414 : Int)/10^30)
theorem v3306_pa_checked : Scalar.distance (sourceCoefficient 43 82 1 0) v3306_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3306_pb : Scalar.QComplex := ((-691127539517918007098648 : Int)/10^30,(-431476940859708654006844128 : Int)/10^30)
theorem v3306_pb_checked : Scalar.distance (sourceCoefficient 43 82 1 1) v3306_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3306_pg : Scalar.QComplex := ((-93086307610321127072425 : Int)/10^30,(149103010263640365617 : Int)/10^30)
theorem v3306_pg_checked : Scalar.distance (sourceCoefficient 43 82 1 2) v3306_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3306_mb : Scalar.QComplex := ((-1063472449141448072946218 : Int)/10^30,(-431476183789184726498019228 : Int)/10^30)
theorem v3306_mb_checked : Scalar.distance (sourceCoefficient 43 82 3 1) v3306_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3306_mg : Scalar.QComplex := ((-93086144280852042102763 : Int)/10^30,(229432245761818785318 : Int)/10^30)
theorem v3306_mg_checked : Scalar.distance (sourceCoefficient 43 82 3 2) v3306_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3306_upper : Scalar.QComplex := ((999994463276566253553833372772 : Int)/10^30,(-3327674294787053004111938632 : Int)/10^30)
theorem v3306_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 82 5) 1) 14) v3306_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3306 : Material (43 : Basis) (82 : Basis) where
  plus := ![v3306_pa,v3306_pb,v3306_pg]
  minus := ![(Primitive.Addresses.material3306 1).one,v3306_mb,v3306_mg]
  upper := v3306_upper
  lower := (Primitive.Addresses.material3306 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3306_pa_checked.trans (by decide +kernel)
    · exact v3306_pb_checked.trans (by decide +kernel)
    · exact v3306_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 82 Primitive.Addresses.material3306
    · exact v3306_mb_checked.trans (by decide +kernel)
    · exact v3306_mg_checked.trans (by decide +kernel)
  upper_error := v3306_upper_checked
  lower_error := reuse_lower_error 43 82 Primitive.Addresses.material3306

def v3307_pa : Scalar.QComplex := ((999998695340371207949254473759 : Int)/10^30,(-1615338217045382261341859573 : Int)/10^30)
theorem v3307_pa_checked : Scalar.distance (sourceCoefficient 43 83 1 0) v3307_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3307_pb : Scalar.QComplex := ((-696982084517088157428202 : Int)/10^30,(-431476930241612117967378906 : Int)/10^30)
theorem v3307_pb_checked : Scalar.distance (sourceCoefficient 43 83 1 1) v3307_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3307_pg : Scalar.QComplex := ((-93086305449107973473477 : Int)/10^30,(150366062852035668611 : Int)/10^30)
theorem v3307_pg_checked : Scalar.distance (sourceCoefficient 43 83 1 2) v3307_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3307_mb : Scalar.QComplex := ((-1069326982797764464873754 : Int)/10^30,(-431476168118883488695866692 : Int)/10^30)
theorem v3307_mb_checked : Scalar.distance (sourceCoefficient 43 83 3 1) v3307_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3307_mg : Scalar.QComplex := ((-93086141029682195213980 : Int)/10^30,(230695296014892271169 : Int)/10^30)
theorem v3307_mg_checked : Scalar.distance (sourceCoefficient 43 83 3 2) v3307_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3307_upper : Scalar.QComplex := ((999994418032562314899524176704 : Int)/10^30,(-3341242840173357644194828402 : Int)/10^30)
theorem v3307_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 83 5) 1) 14) v3307_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3307 : Material (43 : Basis) (83 : Basis) where
  plus := ![v3307_pa,v3307_pb,v3307_pg]
  minus := ![(Primitive.Addresses.material3307 1).one,v3307_mb,v3307_mg]
  upper := v3307_upper
  lower := (Primitive.Addresses.material3307 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3307_pa_checked.trans (by decide +kernel)
    · exact v3307_pb_checked.trans (by decide +kernel)
    · exact v3307_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 83 Primitive.Addresses.material3307
    · exact v3307_mb_checked.trans (by decide +kernel)
    · exact v3307_mg_checked.trans (by decide +kernel)
  upper_error := v3307_upper_checked
  lower_error := reuse_lower_error 43 83 Primitive.Addresses.material3307

def v3308_pa : Scalar.QComplex := ((999998637961533370895683847333 : Int)/10^30,(-1650477227382863363735777990 : Int)/10^30)
theorem v3308_pa_checked : Scalar.distance (sourceCoefficient 43 84 1 0) v3308_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3308_pb : Scalar.QComplex := ((-712143771274662247025251 : Int)/10^30,(-431476902251287652844711182 : Int)/10^30)
theorem v3308_pb_checked : Scalar.distance (sourceCoefficient 43 84 1 1) v3308_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3308_pg : Scalar.QComplex := ((-93086299759213295434243 : Int)/10^30,(153637027193457397424 : Int)/10^30)
theorem v3308_pg_checked : Scalar.distance (sourceCoefficient 43 84 1 2) v3308_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3308_mb : Scalar.QComplex := ((-1084488639755560275326027 : Int)/10^30,(-431476127044716630886495955 : Int)/10^30)
theorem v3308_mb_checked : Scalar.distance (sourceCoefficient 43 84 3 1) v3308_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3308_mg : Scalar.QComplex := ((-93086132517094727900832 : Int)/10^30,(233966254228261641411 : Int)/10^30)
theorem v3308_mg_checked : Scalar.distance (sourceCoefficient 43 84 3 2) v3308_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3308_upper : Scalar.QComplex := ((999994300007065880508535051318 : Int)/10^30,(-3376381699144741827773283061 : Int)/10^30)
theorem v3308_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 84 5) 1) 14) v3308_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3308 : Material (43 : Basis) (84 : Basis) where
  plus := ![v3308_pa,v3308_pb,v3308_pg]
  minus := ![(Primitive.Addresses.material3308 1).one,v3308_mb,v3308_mg]
  upper := v3308_upper
  lower := (Primitive.Addresses.material3308 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3308_pa_checked.trans (by decide +kernel)
    · exact v3308_pb_checked.trans (by decide +kernel)
    · exact v3308_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 84 Primitive.Addresses.material3308
    · exact v3308_mb_checked.trans (by decide +kernel)
    · exact v3308_mg_checked.trans (by decide +kernel)
  upper_error := v3308_upper_checked
  lower_error := reuse_lower_error 43 84 Primitive.Addresses.material3308

def v3309_pa : Scalar.QComplex := ((999998504355070708949532869524 : Int)/10^30,(-1729533931910081497094766035 : Int)/10^30)
theorem v3309_pa_checked : Scalar.distance (sourceCoefficient 43 85 1 0) v3309_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3309_pb : Scalar.QComplex := ((-746254946005409601204027 : Int)/10^30,(-431476836680982446916883926 : Int)/10^30)
theorem v3309_pb_checked : Scalar.distance (sourceCoefficient 43 85 1 1) v3309_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3309_pg : Scalar.QComplex := ((-93086286467710464755686 : Int)/10^30,(160996131834455705303 : Int)/10^30)
theorem v3309_pg_checked : Scalar.distance (sourceCoefficient 43 85 1 2) v3309_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3309_mb : Scalar.QComplex := ((-1118599745200938103751975 : Int)/10^30,(-431476032038028357424395746 : Int)/10^30)
theorem v3309_mb_checked : Scalar.distance (sourceCoefficient 43 85 3 1) v3309_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3309_mg : Scalar.QComplex := ((-93086112875020982844025 : Int)/10^30,(241325344659160647939 : Int)/10^30)
theorem v3309_mg_checked : Scalar.distance (sourceCoefficient 43 85 3 2) v3309_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3309_upper : Scalar.QComplex := ((999994029956102163925871376059 : Int)/10^30,(-3455438055333651349798462850 : Int)/10^30)
theorem v3309_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 85 5) 1) 14) v3309_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3309 : Material (43 : Basis) (85 : Basis) where
  plus := ![v3309_pa,v3309_pb,v3309_pg]
  minus := ![(Primitive.Addresses.material3309 1).one,v3309_mb,v3309_mg]
  upper := v3309_upper
  lower := (Primitive.Addresses.material3309 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3309_pa_checked.trans (by decide +kernel)
    · exact v3309_pb_checked.trans (by decide +kernel)
    · exact v3309_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 85 Primitive.Addresses.material3309
    · exact v3309_mb_checked.trans (by decide +kernel)
    · exact v3309_mg_checked.trans (by decide +kernel)
  upper_error := v3309_upper_checked
  lower_error := reuse_lower_error 43 85 Primitive.Addresses.material3309

def v3310_pa : Scalar.QComplex := ((999998479024078090322579830753 : Int)/10^30,(-1744118554012771177522025433 : Int)/10^30)
theorem v3310_pa_checked : Scalar.distance (sourceCoefficient 43 86 1 0) v3310_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3310_pb : Scalar.QComplex := ((-752547879306138532070289 : Int)/10^30,(-431476824191518552084155854 : Int)/10^30)
theorem v3310_pb_checked : Scalar.distance (sourceCoefficient 43 86 1 1) v3310_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3310_pg : Scalar.QComplex := ((-93086283941493836216760 : Int)/10^30,(162353761882623126606 : Int)/10^30)
theorem v3310_pg_checked : Scalar.distance (sourceCoefficient 43 86 1 2) v3310_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3310_mb : Scalar.QComplex := ((-1124892665380675528829250 : Int)/10^30,(-431476014118051097655506373 : Int)/10^30)
theorem v3310_mb_checked : Scalar.distance (sourceCoefficient 43 86 3 1) v3310_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3310_mg : Scalar.QComplex := ((-93086109177231708750064 : Int)/10^30,(242682972021809181696 : Int)/10^30)
theorem v3310_mg_checked : Scalar.distance (sourceCoefficient 43 86 3 2) v3310_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3310_upper : Scalar.QComplex := ((999993979453412630176062538206 : Int)/10^30,(-3470022611995264388278647195 : Int)/10^30)
theorem v3310_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 86 5) 1) 14) v3310_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3310 : Material (43 : Basis) (86 : Basis) where
  plus := ![v3310_pa,v3310_pb,v3310_pg]
  minus := ![(Primitive.Addresses.material3310 1).one,v3310_mb,v3310_mg]
  upper := v3310_upper
  lower := (Primitive.Addresses.material3310 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3310_pa_checked.trans (by decide +kernel)
    · exact v3310_pb_checked.trans (by decide +kernel)
    · exact v3310_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 86 Primitive.Addresses.material3310
    · exact v3310_mb_checked.trans (by decide +kernel)
    · exact v3310_mg_checked.trans (by decide +kernel)
  upper_error := v3310_upper_checked
  lower_error := reuse_lower_error 43 86 Primitive.Addresses.material3310

def v3311_pa : Scalar.QComplex := ((999998477339218021894653782784 : Int)/10^30,(-1745084308983481095313343081 : Int)/10^30)
theorem v3311_pa_checked : Scalar.distance (sourceCoefficient 43 87 1 0) v3311_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3311_pb : Scalar.QComplex := ((-752964580645523495594871 : Int)/10^30,(-431476823360179472329143245 : Int)/10^30)
theorem v3311_pb_checked : Scalar.distance (sourceCoefficient 43 87 1 1) v3311_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3311_pg : Scalar.QComplex := ((-93086283773398996302037 : Int)/10^30,(162443660541133403542 : Int)/10^30)
theorem v3311_pg_checked : Scalar.distance (sourceCoefficient 43 87 1 2) v3311_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3311_mb : Scalar.QComplex := ((-1125309365847495355802457 : Int)/10^30,(-431476012927117839088446084 : Int)/10^30)
theorem v3311_mb_checked : Scalar.distance (sourceCoefficient 43 87 3 1) v3311_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3311_mg : Scalar.QComplex := ((-93086108931558438015642 : Int)/10^30,(242772870501787803360 : Int)/10^30)
theorem v3311_mg_checked : Scalar.distance (sourceCoefficient 43 87 3 2) v3311_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3311_upper : Scalar.QComplex := ((999993976101749604310523418937 : Int)/10^30,(-3470988362619680093950331104 : Int)/10^30)
theorem v3311_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 87 5) 1) 14) v3311_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3311 : Material (43 : Basis) (87 : Basis) where
  plus := ![v3311_pa,v3311_pb,v3311_pg]
  minus := ![(Primitive.Addresses.material3311 1).one,v3311_mb,v3311_mg]
  upper := v3311_upper
  lower := (Primitive.Addresses.material3311 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3311_pa_checked.trans (by decide +kernel)
    · exact v3311_pb_checked.trans (by decide +kernel)
    · exact v3311_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 87 Primitive.Addresses.material3311
    · exact v3311_mb_checked.trans (by decide +kernel)
    · exact v3311_mg_checked.trans (by decide +kernel)
  upper_error := v3311_upper_checked
  lower_error := reuse_lower_error 43 87 Primitive.Addresses.material3311

def v3312_pa : Scalar.QComplex := ((999998456748591913729950512397 : Int)/10^30,(-1756843884512118947746448175 : Int)/10^30)
theorem v3312_pa_checked : Scalar.distance (sourceCoefficient 43 88 1 0) v3312_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3312_pb : Scalar.QComplex := ((-758038570413243066423790 : Int)/10^30,(-431476813194281775427926970 : Int)/10^30)
theorem v3312_pb_checked : Scalar.distance (sourceCoefficient 43 88 1 1) v3312_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3312_pg : Scalar.QComplex := ((-93086281718455922776979 : Int)/10^30,(163538317149779763954 : Int)/10^30)
theorem v3312_pg_checked : Scalar.distance (sourceCoefficient 43 88 1 2) v3312_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3312_mb : Scalar.QComplex := ((-1130383344953224785931401 : Int)/10^30,(-431475998382599281889485077 : Int)/10^30)
theorem v3312_mb_checked : Scalar.distance (sourceCoefficient 43 88 3 1) v3312_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3312_mg : Scalar.QComplex := ((-93086105931976777881492 : Int)/10^30,(243867524929520158843 : Int)/10^30)
theorem v3312_mg_checked : Scalar.distance (sourceCoefficient 43 88 3 2) v3312_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3312_upper : Scalar.QComplex := ((999993935215193621394144827599 : Int)/10^30,(-3482747885096258877571872303 : Int)/10^30)
theorem v3312_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 88 5) 1) 14) v3312_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3312 : Material (43 : Basis) (88 : Basis) where
  plus := ![v3312_pa,v3312_pb,v3312_pg]
  minus := ![(Primitive.Addresses.material3312 1).one,v3312_mb,v3312_mg]
  upper := v3312_upper
  lower := (Primitive.Addresses.material3312 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3312_pa_checked.trans (by decide +kernel)
    · exact v3312_pb_checked.trans (by decide +kernel)
    · exact v3312_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 88 Primitive.Addresses.material3312
    · exact v3312_mb_checked.trans (by decide +kernel)
    · exact v3312_mg_checked.trans (by decide +kernel)
  upper_error := v3312_upper_checked
  lower_error := reuse_lower_error 43 88 Primitive.Addresses.material3312

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
