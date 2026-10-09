import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B122
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B123

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2945_pa : Scalar.QComplex := ((999999406770706215210359696592 : Int)/10^30,(-1089246636739624859240563159 : Int)/10^30)
theorem v2945_pa_checked : Scalar.distance (sourceCoefficient 37 60 1 0) v2945_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2945_pb : Scalar.QComplex := ((-469985431605253497585137 : Int)/10^30,(-431477258633458392042971839 : Int)/10^30)
theorem v2945_pb_checked : Scalar.distance (sourceCoefficient 37 60 1 1) v2945_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2945_pg : Scalar.QComplex := ((-93086373984789558923883 : Int)/10^30,(101394079939157374746 : Int)/10^30)
theorem v2945_pg_checked : Scalar.distance (sourceCoefficient 37 60 1 2) v2945_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2945_mb : Scalar.QComplex := ((-842330697794531058453438 : Int)/10^30,(-431476692398495400661010726 : Int)/10^30)
theorem v2945_mb_checked : Scalar.distance (sourceCoefficient 37 60 3 1) v2945_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2945_mg : Scalar.QComplex := ((-93086251825953899277791 : Int)/10^30,(181723390479727821684 : Int)/10^30)
theorem v2945_mg_checked : Scalar.distance (sourceCoefficient 37 60 3 2) v2945_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2945_upper : Scalar.QComplex := ((999996037448178682639223240465 : Int)/10^30,(-2815153271283427816052586543 : Int)/10^30)
theorem v2945_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 60 5) 1) 14) v2945_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2945 : Material (37 : Basis) (60 : Basis) where
  plus := ![v2945_pa,v2945_pb,v2945_pg]
  minus := ![(Primitive.Addresses.material2945 1).one,v2945_mb,v2945_mg]
  upper := v2945_upper
  lower := (Primitive.Addresses.material2945 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2945_pa_checked.trans (by decide +kernel)
    · exact v2945_pb_checked.trans (by decide +kernel)
    · exact v2945_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 60 Primitive.Addresses.material2945
    · exact v2945_mb_checked.trans (by decide +kernel)
    · exact v2945_mg_checked.trans (by decide +kernel)
  upper_error := v2945_upper_checked
  lower_error := reuse_lower_error 37 60 Primitive.Addresses.material2945

def v2946_pa : Scalar.QComplex := ((999999400371278737851494748480 : Int)/10^30,(-1095105968831187426846705160 : Int)/10^30)
theorem v2946_pa_checked : Scalar.distance (sourceCoefficient 37 61 1 0) v2946_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2946_pb : Scalar.QComplex := ((-472513601375265982776647 : Int)/10^30,(-431477255618335687230085788 : Int)/10^30)
theorem v2946_pb_checked : Scalar.distance (sourceCoefficient 37 61 1 1) v2946_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2946_pg : Scalar.QComplex := ((-93086373361700197785927 : Int)/10^30,(101939504211100888571 : Int)/10^30)
theorem v2946_pg_checked : Scalar.distance (sourceCoefficient 37 61 1 2) v2946_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2946_mb : Scalar.QComplex := ((-844858864021275297034984 : Int)/10^30,(-431476687201677171534921840 : Int)/10^30)
theorem v2946_mb_checked : Scalar.distance (sourceCoefficient 37 61 3 1) v2946_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2946_mg : Scalar.QComplex := ((-93086250732188188454541 : Int)/10^30,(182268814010886896184 : Int)/10^30)
theorem v2946_mg_checked : Scalar.distance (sourceCoefficient 37 61 3 2) v2946_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2946_upper : Scalar.QComplex := ((999996020936085100893935595888 : Int)/10^30,(-2821012583603372244377503593 : Int)/10^30)
theorem v2946_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 61 5) 1) 14) v2946_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2946 : Material (37 : Basis) (61 : Basis) where
  plus := ![v2946_pa,v2946_pb,v2946_pg]
  minus := ![(Primitive.Addresses.material2946 1).one,v2946_mb,v2946_mg]
  upper := v2946_upper
  lower := (Primitive.Addresses.material2946 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2946_pa_checked.trans (by decide +kernel)
    · exact v2946_pb_checked.trans (by decide +kernel)
    · exact v2946_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 61 Primitive.Addresses.material2946
    · exact v2946_mb_checked.trans (by decide +kernel)
    · exact v2946_mg_checked.trans (by decide +kernel)
  upper_error := v2946_upper_checked
  lower_error := reuse_lower_error 37 61 Primitive.Addresses.material2946

def v2947_pa : Scalar.QComplex := ((999999391012005180697127089317 : Int)/10^30,(-1103619326929457099287065618 : Int)/10^30)
theorem v2947_pa_checked : Scalar.distance (sourceCoefficient 37 62 1 0) v2947_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2947_pb : Scalar.QComplex := ((-476186923549368504736526 : Int)/10^30,(-431477251202294711286240137 : Int)/10^30)
theorem v2947_pb_checked : Scalar.distance (sourceCoefficient 37 62 1 1) v2947_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2947_pg : Scalar.QComplex := ((-93086372449733891698086 : Int)/10^30,(102731982271823963686 : Int)/10^30)
theorem v2947_pg_checked : Scalar.distance (sourceCoefficient 37 62 1 2) v2947_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2947_mb : Scalar.QComplex := ((-848532181016787623322574 : Int)/10^30,(-431476679615726243923767482 : Int)/10^30)
theorem v2947_mb_checked : Scalar.distance (sourceCoefficient 37 62 3 1) v2947_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2947_mg : Scalar.QComplex := ((-93086249136349347416332 : Int)/10^30,(183061290989548322539 : Int)/10^30)
theorem v2947_mg_checked : Scalar.distance (sourceCoefficient 37 62 3 2) v2947_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2947_upper : Scalar.QComplex := ((999995996883541731478256038692 : Int)/10^30,(-2829525912868737985753162605 : Int)/10^30)
theorem v2947_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 62 5) 1) 14) v2947_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2947 : Material (37 : Basis) (62 : Basis) where
  plus := ![v2947_pa,v2947_pb,v2947_pg]
  minus := ![(Primitive.Addresses.material2947 1).one,v2947_mb,v2947_mg]
  upper := v2947_upper
  lower := (Primitive.Addresses.material2947 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2947_pa_checked.trans (by decide +kernel)
    · exact v2947_pb_checked.trans (by decide +kernel)
    · exact v2947_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 62 Primitive.Addresses.material2947
    · exact v2947_mb_checked.trans (by decide +kernel)
    · exact v2947_mg_checked.trans (by decide +kernel)
  upper_error := v2947_upper_checked
  lower_error := reuse_lower_error 37 62 Primitive.Addresses.material2947

def v2948_pa : Scalar.QComplex := ((999999363340171997944569942599 : Int)/10^30,(-1128414485314848423542201180 : Int)/10^30)
theorem v2948_pa_checked : Scalar.distance (sourceCoefficient 37 63 1 0) v2948_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2948_pb : Scalar.QComplex := ((-486885475539497672740138 : Int)/10^30,(-431477238103004881981384577 : Int)/10^30)
theorem v2948_pb_checked : Scalar.distance (sourceCoefficient 37 63 1 1) v2948_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2948_pg : Scalar.QComplex := ((-93086369748785471206905 : Int)/10^30,(105040074884699443052 : Int)/10^30)
theorem v2948_pg_checked : Scalar.distance (sourceCoefficient 37 63 1 2) v2948_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2948_mb : Scalar.QComplex := ((-859230717719259784843729 : Int)/10^30,(-431476657284072769496422649 : Int)/10^30)
theorem v2948_mb_checked : Scalar.distance (sourceCoefficient 37 63 3 1) v2948_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2948_mg : Scalar.QComplex := ((-93086244443621960332529 : Int)/10^30,(185369380412218596406 : Int)/10^30)
theorem v2948_mg_checked : Scalar.distance (sourceCoefficient 37 63 3 2) v2948_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2948_upper : Scalar.QComplex := ((999995926417555788682617530375 : Int)/10^30,(-2854320986565579834539442308 : Int)/10^30)
theorem v2948_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 63 5) 1) 14) v2948_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2948 : Material (37 : Basis) (63 : Basis) where
  plus := ![v2948_pa,v2948_pb,v2948_pg]
  minus := ![(Primitive.Addresses.material2948 1).one,v2948_mb,v2948_mg]
  upper := v2948_upper
  lower := (Primitive.Addresses.material2948 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2948_pa_checked.trans (by decide +kernel)
    · exact v2948_pb_checked.trans (by decide +kernel)
    · exact v2948_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 63 Primitive.Addresses.material2948
    · exact v2948_mb_checked.trans (by decide +kernel)
    · exact v2948_mg_checked.trans (by decide +kernel)
  upper_error := v2948_upper_checked
  lower_error := reuse_lower_error 37 63 Primitive.Addresses.material2948

def v2949_pa : Scalar.QComplex := ((999999322724341870913336819767 : Int)/10^30,(-1163851733493513439193992661 : Int)/10^30)
theorem v2949_pa_checked : Scalar.distance (sourceCoefficient 37 64 1 0) v2949_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2949_pb : Scalar.QComplex := ((-502175849137006005081210 : Int)/10^30,(-431477218767510722188113992 : Int)/10^30)
theorem v2949_pb_checked : Scalar.distance (sourceCoefficient 37 64 1 1) v2949_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2949_pg : Scalar.QComplex := ((-93086365772686291364518 : Int)/10^30,(108338801544385313675 : Int)/10^30)
theorem v2949_pg_checked : Scalar.distance (sourceCoefficient 37 64 1 2) v2949_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2949_mb : Scalar.QComplex := ((-874521068937802600665721 : Int)/10^30,(-431476624753682047404448543 : Int)/10^30)
theorem v2949_mb_checked : Scalar.distance (sourceCoefficient 37 64 3 1) v2949_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2949_mg : Scalar.QComplex := ((-93086237620871722798283 : Int)/10^30,(188668102412443257027 : Int)/10^30)
theorem v2949_mg_checked : Scalar.distance (sourceCoefficient 37 64 3 2) v2949_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2949_upper : Scalar.QComplex := ((999995824640310639825271668373 : Int)/10^30,(-2889758111865388279728502219 : Int)/10^30)
theorem v2949_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 64 5) 1) 14) v2949_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2949 : Material (37 : Basis) (64 : Basis) where
  plus := ![v2949_pa,v2949_pb,v2949_pg]
  minus := ![(Primitive.Addresses.material2949 1).one,v2949_mb,v2949_mg]
  upper := v2949_upper
  lower := (Primitive.Addresses.material2949 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2949_pa_checked.trans (by decide +kernel)
    · exact v2949_pb_checked.trans (by decide +kernel)
    · exact v2949_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 64 Primitive.Addresses.material2949
    · exact v2949_mb_checked.trans (by decide +kernel)
    · exact v2949_mg_checked.trans (by decide +kernel)
  upper_error := v2949_upper_checked
  lower_error := reuse_lower_error 37 64 Primitive.Addresses.material2949

def v2950_pa : Scalar.QComplex := ((999999280217731755783655844190 : Int)/10^30,(-1199818327248721021770467788 : Int)/10^30)
theorem v2950_pa_checked : Scalar.distance (sourceCoefficient 37 65 1 0) v2950_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2950_pb : Scalar.QComplex := ((-517694623063010196828039 : Int)/10^30,(-431477198404457028303210118 : Int)/10^30)
theorem v2950_pb_checked : Scalar.distance (sourceCoefficient 37 65 1 1) v2950_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2950_pg : Scalar.QComplex := ((-93086361597741916766679 : Int)/10^30,(111686803052052722274 : Int)/10^30)
theorem v2950_pg_checked : Scalar.distance (sourceCoefficient 37 65 1 2) v2950_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2950_mb : Scalar.QComplex := ((-890039819513059796826140 : Int)/10^30,(-431476590998632977105223455 : Int)/10^30)
theorem v2950_mb_checked : Scalar.distance (sourceCoefficient 37 65 3 1) v2950_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2950_mg : Scalar.QComplex := ((-93086230556754389996443 : Int)/10^30,(192016099070707730330 : Int)/10^30)
theorem v2950_mg_checked : Scalar.distance (sourceCoefficient 37 65 3 2) v2950_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2950_upper : Scalar.QComplex := ((999995720058685875707270886936 : Int)/10^30,(-2925724578690026507644189825 : Int)/10^30)
theorem v2950_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 65 5) 1) 14) v2950_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2950 : Material (37 : Basis) (65 : Basis) where
  plus := ![v2950_pa,v2950_pb,v2950_pg]
  minus := ![(Primitive.Addresses.material2950 1).one,v2950_mb,v2950_mg]
  upper := v2950_upper
  lower := (Primitive.Addresses.material2950 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2950_pa_checked.trans (by decide +kernel)
    · exact v2950_pb_checked.trans (by decide +kernel)
    · exact v2950_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 65 Primitive.Addresses.material2950
    · exact v2950_mb_checked.trans (by decide +kernel)
    · exact v2950_mg_checked.trans (by decide +kernel)
  upper_error := v2950_upper_checked
  lower_error := reuse_lower_error 37 65 Primitive.Addresses.material2950

def v2951_pa : Scalar.QComplex := ((999999258961185977859446904781 : Int)/10^30,(-1217405880922939035746240854 : Int)/10^30)
theorem v2951_pa_checked : Scalar.distance (sourceCoefficient 37 66 1 0) v2951_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2951_pb : Scalar.QComplex := ((-525283255624898597158266 : Int)/10^30,(-431477188176050770506230308 : Int)/10^30)
theorem v2951_pb_checked : Scalar.distance (sourceCoefficient 37 66 1 1) v2951_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2951_pg : Scalar.QComplex := ((-93086359505062042632031 : Int)/10^30,(113323965472626429469 : Int)/10^30)
theorem v2951_pg_checked : Scalar.distance (sourceCoefficient 37 66 1 2) v2951_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2951_mb : Scalar.QComplex := ((-897628440422699546562269 : Int)/10^30,(-431476574221582406224807797 : Int)/10^30)
theorem v2951_mb_checked : Scalar.distance (sourceCoefficient 37 66 3 1) v2951_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2951_mg : Scalar.QComplex := ((-93086227051277861165292 : Int)/10^30,(193653259075802565751 : Int)/10^30)
theorem v2951_mg_checked : Scalar.distance (sourceCoefficient 37 66 3 2) v2951_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2951_upper : Scalar.QComplex := ((999995668447649645616462284845 : Int)/10^30,(-2943312069482779669126047166 : Int)/10^30)
theorem v2951_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 66 5) 1) 14) v2951_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2951 : Material (37 : Basis) (66 : Basis) where
  plus := ![v2951_pa,v2951_pb,v2951_pg]
  minus := ![(Primitive.Addresses.material2951 1).one,v2951_mb,v2951_mg]
  upper := v2951_upper
  lower := (Primitive.Addresses.material2951 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2951_pa_checked.trans (by decide +kernel)
    · exact v2951_pb_checked.trans (by decide +kernel)
    · exact v2951_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 66 Primitive.Addresses.material2951
    · exact v2951_mb_checked.trans (by decide +kernel)
    · exact v2951_mg_checked.trans (by decide +kernel)
  upper_error := v2951_upper_checked
  lower_error := reuse_lower_error 37 66 Primitive.Addresses.material2951

def v2952_pa : Scalar.QComplex := ((999999222591197004076412855048 : Int)/10^30,(-1246923013512622678442936118 : Int)/10^30)
theorem v2952_pa_checked : Scalar.distance (sourceCoefficient 37 67 1 0) v2952_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2952_pb : Scalar.QComplex := ((-538019232099559678300755 : Int)/10^30,(-431477170609800494644572875 : Int)/10^30)
theorem v2952_pb_checked : Scalar.distance (sourceCoefficient 37 67 1 1) v2952_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2952_pg : Scalar.QComplex := ((-93086355917425209949639 : Int)/10^30,(116071609672555536441 : Int)/10^30)
theorem v2952_pg_checked : Scalar.distance (sourceCoefficient 37 67 1 2) v2952_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2952_mb : Scalar.QComplex := ((-910364396996291689783833 : Int)/10^30,(-431476545664764580535555100 : Int)/10^30)
theorem v2952_mb_checked : Scalar.distance (sourceCoefficient 37 67 3 1) v2952_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2952_mg : Scalar.QComplex := ((-93086221092549169086211 : Int)/10^30,(196400899156689158106 : Int)/10^30)
theorem v2952_mg_checked : Scalar.distance (sourceCoefficient 37 67 3 2) v2952_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2952_upper : Scalar.QComplex := ((999995581133821764216636979427 : Int)/10^30,(-2972829095338860136325525782 : Int)/10^30)
theorem v2952_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 67 5) 1) 14) v2952_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2952 : Material (37 : Basis) (67 : Basis) where
  plus := ![v2952_pa,v2952_pb,v2952_pg]
  minus := ![(Primitive.Addresses.material2952 1).one,v2952_mb,v2952_mg]
  upper := v2952_upper
  lower := (Primitive.Addresses.material2952 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2952_pa_checked.trans (by decide +kernel)
    · exact v2952_pb_checked.trans (by decide +kernel)
    · exact v2952_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 67 Primitive.Addresses.material2952
    · exact v2952_mb_checked.trans (by decide +kernel)
    · exact v2952_mg_checked.trans (by decide +kernel)
  upper_error := v2952_upper_checked
  lower_error := reuse_lower_error 37 67 Primitive.Addresses.material2952

def v2953_pa : Scalar.QComplex := ((999999160086723935674368722022 : Int)/10^30,(-1296080956836547287694297909 : Int)/10^30)
theorem v2953_pa_checked : Scalar.distance (sourceCoefficient 37 68 1 0) v2953_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2953_pb : Scalar.QComplex := ((-559229774482985501737761 : Int)/10^30,(-431477140242405129242187126 : Int)/10^30)
theorem v2953_pb_checked : Scalar.distance (sourceCoefficient 37 68 1 1) v2953_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2953_pg : Scalar.QComplex := ((-93086349732553814927451 : Int)/10^30,(120647546563265909239 : Int)/10^30)
theorem v2953_pg_checked : Scalar.distance (sourceCoefficient 37 68 1 2) v2953_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2953_mb : Scalar.QComplex := ((-931574905276368710570360 : Int)/10^30,(-431476496993637732772852327 : Int)/10^30)
theorem v2953_mb_checked : Scalar.distance (sourceCoefficient 37 68 3 1) v2953_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2953_mg : Scalar.QComplex := ((-93086210958852632838297 : Int)/10^30,(200976829006303638208 : Int)/10^30)
theorem v2953_mg_checked : Scalar.distance (sourceCoefficient 37 68 3 2) v2953_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2953_upper : Scalar.QComplex := ((999995433787291185573129302921 : Int)/10^30,(-3021986857570752507690750836 : Int)/10^30)
theorem v2953_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 68 5) 1) 14) v2953_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2953 : Material (37 : Basis) (68 : Basis) where
  plus := ![v2953_pa,v2953_pb,v2953_pg]
  minus := ![(Primitive.Addresses.material2953 1).one,v2953_mb,v2953_mg]
  upper := v2953_upper
  lower := (Primitive.Addresses.material2953 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2953_pa_checked.trans (by decide +kernel)
    · exact v2953_pb_checked.trans (by decide +kernel)
    · exact v2953_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 68 Primitive.Addresses.material2953
    · exact v2953_mb_checked.trans (by decide +kernel)
    · exact v2953_mg_checked.trans (by decide +kernel)
  upper_error := v2953_upper_checked
  lower_error := reuse_lower_error 37 68 Primitive.Addresses.material2953

def v2954_pa : Scalar.QComplex := ((999999131811465052178422843357 : Int)/10^30,(-1317716326128014147201242925 : Int)/10^30)
theorem v2954_pa_checked : Scalar.distance (sourceCoefficient 37 69 1 0) v2954_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2954_pb : Scalar.QComplex := ((-568564947477802689430142 : Int)/10^30,(-431477126436542867583691035 : Int)/10^30)
theorem v2954_pb_checked : Scalar.distance (sourceCoefficient 37 69 1 1) v2954_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2954_pg : Scalar.QComplex := ((-93086346927302487765247 : Int)/10^30,(122661505579035615744 : Int)/10^30)
theorem v2954_pg_checked : Scalar.distance (sourceCoefficient 37 69 1 2) v2954_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2954_mb : Scalar.QComplex := ((-940910062881437014953014 : Int)/10^30,(-431476475131946757724800792 : Int)/10^30)
theorem v2954_mb_checked : Scalar.distance (sourceCoefficient 37 69 3 1) v2954_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2954_mg : Scalar.QComplex := ((-93086206415646424937042 : Int)/10^30,(202990784851378809157 : Int)/10^30)
theorem v2954_mg_checked : Scalar.distance (sourceCoefficient 37 69 3 2) v2954_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2954_upper : Scalar.QComplex := ((999995368171389763052042100683 : Int)/10^30,(-3043622145838346555097601899 : Int)/10^30)
theorem v2954_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 69 5) 1) 14) v2954_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2954 : Material (37 : Basis) (69 : Basis) where
  plus := ![v2954_pa,v2954_pb,v2954_pg]
  minus := ![(Primitive.Addresses.material2954 1).one,v2954_mb,v2954_mg]
  upper := v2954_upper
  lower := (Primitive.Addresses.material2954 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2954_pa_checked.trans (by decide +kernel)
    · exact v2954_pb_checked.trans (by decide +kernel)
    · exact v2954_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 69 Primitive.Addresses.material2954
    · exact v2954_mb_checked.trans (by decide +kernel)
    · exact v2954_mg_checked.trans (by decide +kernel)
  upper_error := v2954_upper_checked
  lower_error := reuse_lower_error 37 69 Primitive.Addresses.material2954

def v2955_pa : Scalar.QComplex := ((999999112956496542423373470399 : Int)/10^30,(-1331948279802551577576443327 : Int)/10^30)
theorem v2955_pa_checked : Scalar.distance (sourceCoefficient 37 70 1 0) v2955_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2955_pb : Scalar.QComplex := ((-574705713828433990096949 : Int)/10^30,(-431477117208078540962580534 : Int)/10^30)
theorem v2955_pb_checked : Scalar.distance (sourceCoefficient 37 70 1 1) v2955_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2955_pg : Scalar.QComplex := ((-93086345054262861639875 : Int)/10^30,(123986307149380447803 : Int)/10^30)
theorem v2955_pg_checked : Scalar.distance (sourceCoefficient 37 70 1 2) v2955_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2955_mb : Scalar.QComplex := ((-947050818981831277123497 : Int)/10^30,(-431476460604281076537585293 : Int)/10^30)
theorem v2955_mb_checked : Scalar.distance (sourceCoefficient 37 70 3 1) v2955_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2955_mg : Scalar.QComplex := ((-93086203399363407870125 : Int)/10^30,(204315584312090631381 : Int)/10^30)
theorem v2955_mg_checked : Scalar.distance (sourceCoefficient 37 70 3 2) v2955_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2955_upper : Scalar.QComplex := ((999995324753388406057857695372 : Int)/10^30,(-3057854045774095651509870262 : Int)/10^30)
theorem v2955_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 70 5) 1) 14) v2955_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2955 : Material (37 : Basis) (70 : Basis) where
  plus := ![v2955_pa,v2955_pb,v2955_pg]
  minus := ![(Primitive.Addresses.material2955 1).one,v2955_mb,v2955_mg]
  upper := v2955_upper
  lower := (Primitive.Addresses.material2955 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2955_pa_checked.trans (by decide +kernel)
    · exact v2955_pb_checked.trans (by decide +kernel)
    · exact v2955_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 70 Primitive.Addresses.material2955
    · exact v2955_mb_checked.trans (by decide +kernel)
    · exact v2955_mg_checked.trans (by decide +kernel)
  upper_error := v2955_upper_checked
  lower_error := reuse_lower_error 37 70 Primitive.Addresses.material2955

def v2956_pa : Scalar.QComplex := ((999999080304651181863173983304 : Int)/10^30,(-1356241074365740854337690688 : Int)/10^30)
theorem v2956_pa_checked : Scalar.distance (sourceCoefficient 37 71 1 0) v2956_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2956_pb : Scalar.QComplex := ((-585187505471797057207076 : Int)/10^30,(-431477101186629660127946437 : Int)/10^30)
theorem v2956_pb_checked : Scalar.distance (sourceCoefficient 37 71 1 1) v2956_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2956_pg : Scalar.QComplex := ((-93086341806317162448896 : Int)/10^30,(126247636329540098125 : Int)/10^30)
theorem v2956_pg_checked : Scalar.distance (sourceCoefficient 37 71 1 2) v2956_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2956_mb : Scalar.QComplex := ((-957532592896555468977342 : Int)/10^30,(-431476435537524055369354711 : Int)/10^30)
theorem v2956_mb_checked : Scalar.distance (sourceCoefficient 37 71 3 1) v2956_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2956_mg : Scalar.QComplex := ((-93086198199993682045545 : Int)/10^30,(206576909847423223723 : Int)/10^30)
theorem v2956_mg_checked : Scalar.distance (sourceCoefficient 37 71 3 2) v2956_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2956_upper : Scalar.QComplex := ((999995250174432085628511425574 : Int)/10^30,(-3082146747801898118451946339 : Int)/10^30)
theorem v2956_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 71 5) 1) 14) v2956_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2956 : Material (37 : Basis) (71 : Basis) where
  plus := ![v2956_pa,v2956_pb,v2956_pg]
  minus := ![(Primitive.Addresses.material2956 1).one,v2956_mb,v2956_mg]
  upper := v2956_upper
  lower := (Primitive.Addresses.material2956 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2956_pa_checked.trans (by decide +kernel)
    · exact v2956_pb_checked.trans (by decide +kernel)
    · exact v2956_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 71 Primitive.Addresses.material2956
    · exact v2956_mb_checked.trans (by decide +kernel)
    · exact v2956_mg_checked.trans (by decide +kernel)
  upper_error := v2956_upper_checked
  lower_error := reuse_lower_error 37 71 Primitive.Addresses.material2956

def v2957_pa : Scalar.QComplex := ((999999044203081033163585019342 : Int)/10^30,(-1382603675818172603871696686 : Int)/10^30)
theorem v2957_pa_checked : Scalar.distance (sourceCoefficient 37 72 1 0) v2957_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2957_pb : Scalar.QComplex := ((-596562371754715255025217 : Int)/10^30,(-431477083415980093840327841 : Int)/10^30)
theorem v2957_pb_checked : Scalar.distance (sourceCoefficient 37 72 1 1) v2957_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2957_pg : Scalar.QComplex := ((-93086338209124978023868 : Int)/10^30,(128701636389017331480 : Int)/10^30)
theorem v2957_pg_checked : Scalar.distance (sourceCoefficient 37 72 1 2) v2957_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2957_mb : Scalar.QComplex := ((-968907439608820877233926 : Int)/10^30,(-431476407950883808708052331 : Int)/10^30)
theorem v2957_mb_checked : Scalar.distance (sourceCoefficient 37 72 3 1) v2957_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2957_mg : Scalar.QComplex := ((-93086192485111309750548 : Int)/10^30,(209030905888949237955 : Int)/10^30)
theorem v2957_mg_checked : Scalar.distance (sourceCoefficient 37 72 3 2) v2957_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2957_upper : Scalar.QComplex := ((999995168573457195601308751501 : Int)/10^30,(-3108509247682296805496253717 : Int)/10^30)
theorem v2957_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 72 5) 1) 14) v2957_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2957 : Material (37 : Basis) (72 : Basis) where
  plus := ![v2957_pa,v2957_pb,v2957_pg]
  minus := ![(Primitive.Addresses.material2957 1).one,v2957_mb,v2957_mg]
  upper := v2957_upper
  lower := (Primitive.Addresses.material2957 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2957_pa_checked.trans (by decide +kernel)
    · exact v2957_pb_checked.trans (by decide +kernel)
    · exact v2957_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 72 Primitive.Addresses.material2957
    · exact v2957_mb_checked.trans (by decide +kernel)
    · exact v2957_mg_checked.trans (by decide +kernel)
  upper_error := v2957_upper_checked
  lower_error := reuse_lower_error 37 72 Primitive.Addresses.material2957

def v2958_pa : Scalar.QComplex := ((999999031093322567392075604830 : Int)/10^30,(-1392053309354590153906550034 : Int)/10^30)
theorem v2958_pa_checked : Scalar.distance (sourceCoefficient 37 73 1 0) v2958_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2958_pb : Scalar.QComplex := ((-600639674840976613185807 : Int)/10^30,(-431477076948773235300542996 : Int)/10^30)
theorem v2958_pb_checked : Scalar.distance (sourceCoefficient 37 73 1 1) v2958_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2958_pg : Scalar.QComplex := ((-93086336901341043356193 : Int)/10^30,(129581268891364803504 : Int)/10^30)
theorem v2958_pg_checked : Scalar.distance (sourceCoefficient 37 73 1 2) v2958_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2958_mb : Scalar.QComplex := ((-972984735596007707687433 : Int)/10^30,(-431476397965150429675551552 : Int)/10^30)
theorem v2958_mb_checked : Scalar.distance (sourceCoefficient 37 73 3 1) v2958_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2958_mg : Scalar.QComplex := ((-93086190418244629681979 : Int)/10^30,(209910536935210692946 : Int)/10^30)
theorem v2958_mg_checked : Scalar.distance (sourceCoefficient 37 73 3 2) v2958_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2958_upper : Scalar.QComplex := ((999995139154508035476206814140 : Int)/10^30,(-3117958844518341431043869430 : Int)/10^30)
theorem v2958_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 73 5) 1) 14) v2958_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2958 : Material (37 : Basis) (73 : Basis) where
  plus := ![v2958_pa,v2958_pb,v2958_pg]
  minus := ![(Primitive.Addresses.material2958 1).one,v2958_mb,v2958_mg]
  upper := v2958_upper
  lower := (Primitive.Addresses.material2958 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2958_pa_checked.trans (by decide +kernel)
    · exact v2958_pb_checked.trans (by decide +kernel)
    · exact v2958_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 73 Primitive.Addresses.material2958
    · exact v2958_mb_checked.trans (by decide +kernel)
    · exact v2958_mg_checked.trans (by decide +kernel)
  upper_error := v2958_upper_checked
  lower_error := reuse_lower_error 37 73 Primitive.Addresses.material2958

def v2959_pa : Scalar.QComplex := ((999999016234849945084142301056 : Int)/10^30,(-1402686469713015109051566501 : Int)/10^30)
theorem v2959_pa_checked : Scalar.distance (sourceCoefficient 37 74 1 0) v2959_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2959_pb : Scalar.QComplex := ((-605227642935440649755038 : Int)/10^30,(-431477069610149643602857759 : Int)/10^30)
theorem v2959_pb_checked : Scalar.distance (sourceCoefficient 37 74 1 1) v2959_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2959_pg : Scalar.QComplex := ((-93086335418167142424525 : Int)/10^30,(130571071657500373031 : Int)/10^30)
theorem v2959_pg_checked : Scalar.distance (sourceCoefficient 37 74 1 2) v2959_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2959_mb : Scalar.QComplex := ((-977572695649259901889373 : Int)/10^30,(-431476386667319739372702324 : Int)/10^30)
theorem v2959_mb_checked : Scalar.distance (sourceCoefficient 37 74 3 1) v2959_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2959_mg : Scalar.QComplex := ((-93086188080916072890476 : Int)/10^30,(210900338052885179589 : Int)/10^30)
theorem v2959_mg_checked : Scalar.distance (sourceCoefficient 37 74 3 2) v2959_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2959_upper : Scalar.QComplex := ((999995105944187397248791674751 : Int)/10^30,(-3128591963395547295075402454 : Int)/10^30)
theorem v2959_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 74 5) 1) 14) v2959_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2959 : Material (37 : Basis) (74 : Basis) where
  plus := ![v2959_pa,v2959_pb,v2959_pg]
  minus := ![(Primitive.Addresses.material2959 1).one,v2959_mb,v2959_mg]
  upper := v2959_upper
  lower := (Primitive.Addresses.material2959 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2959_pa_checked.trans (by decide +kernel)
    · exact v2959_pb_checked.trans (by decide +kernel)
    · exact v2959_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 74 Primitive.Addresses.material2959
    · exact v2959_mb_checked.trans (by decide +kernel)
    · exact v2959_mg_checked.trans (by decide +kernel)
  upper_error := v2959_upper_checked
  lower_error := reuse_lower_error 37 74 Primitive.Addresses.material2959

def v2960_pa : Scalar.QComplex := ((999998995344125118048988171107 : Int)/10^30,(-1417501583925208560766513686 : Int)/10^30)
theorem v2960_pa_checked : Scalar.distance (sourceCoefficient 37 75 1 0) v2960_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2960_pb : Scalar.QComplex := ((-611620029419970379794946 : Int)/10^30,(-431477059276841991740260771 : Int)/10^30)
theorem v2960_pb_checked : Scalar.distance (sourceCoefficient 37 75 1 1) v2960_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2960_pg : Scalar.QComplex := ((-93086333331198101655666 : Int)/10^30,(131950157503264172125 : Int)/10^30)
theorem v2960_pg_checked : Scalar.distance (sourceCoefficient 37 75 1 2) v2960_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2960_mb : Scalar.QComplex := ((-983965070836432888587138 : Int)/10^30,(-431476370817674301323466360 : Int)/10^30)
theorem v2960_mb_checked : Scalar.distance (sourceCoefficient 37 75 3 1) v2960_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2960_mg : Scalar.QComplex := ((-93086184803858836022209 : Int)/10^30,(212279421584192002381 : Int)/10^30)
theorem v2960_mg_checked : Scalar.distance (sourceCoefficient 37 75 3 2) v2960_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2960_upper : Scalar.QComplex := ((999995059483950570910821016248 : Int)/10^30,(-3143407019486872573582572898 : Int)/10^30)
theorem v2960_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 75 5) 1) 14) v2960_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2960 : Material (37 : Basis) (75 : Basis) where
  plus := ![v2960_pa,v2960_pb,v2960_pg]
  minus := ![(Primitive.Addresses.material2960 1).one,v2960_mb,v2960_mg]
  upper := v2960_upper
  lower := (Primitive.Addresses.material2960 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2960_pa_checked.trans (by decide +kernel)
    · exact v2960_pb_checked.trans (by decide +kernel)
    · exact v2960_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 75 Primitive.Addresses.material2960
    · exact v2960_mb_checked.trans (by decide +kernel)
    · exact v2960_mg_checked.trans (by decide +kernel)
  upper_error := v2960_upper_checked
  lower_error := reuse_lower_error 37 75 Primitive.Addresses.material2960

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
