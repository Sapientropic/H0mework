import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B048
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B049

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1169_pa : Scalar.QComplex := ((999999378979344282310533686007 : Int)/10^30,(-1114468898520153457135075274 : Int)/10^30)
theorem v1169_pa_checked : Scalar.distance (sourceCoefficient 12 84 1 0) v1169_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1169_pb : Scalar.QComplex := ((-480868163459208803643284 : Int)/10^30,(-431477150657740730289034604 : Int)/10^30)
theorem v1169_pb_checked : Scalar.distance (sourceCoefficient 12 84 1 1) v1169_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1169_pg : Scalar.QComplex := ((-93086361044015773757509 : Int)/10^30,(103741918685847949080 : Int)/10^30)
theorem v1169_pg_checked : Scalar.distance (sourceCoefficient 12 84 1 2) v1169_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1169_mb : Scalar.QComplex := ((-853213332418166633573040 : Int)/10^30,(-431476575031510493285912226 : Int)/10^30)
theorem v1169_mb_checked : Scalar.distance (sourceCoefficient 12 84 3 1) v1169_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1169_mg : Scalar.QComplex := ((-93086236859105836890751 : Int)/10^30,(184071217184905783310 : Int)/10^30)
theorem v1169_mg_checked : Scalar.distance (sourceCoefficient 12 84 3 2) v1169_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1169_upper : Scalar.QComplex := ((999995966125522454230749747912 : Int)/10^30,(-2840375447532990823319715357 : Int)/10^30)
theorem v1169_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 84 5) 1) 14) v1169_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1169 : Material (12 : Basis) (84 : Basis) where
  plus := ![v1169_pa,v1169_pb,v1169_pg]
  minus := ![(Primitive.Addresses.material1169 1).one,v1169_mb,v1169_mg]
  upper := v1169_upper
  lower := (Primitive.Addresses.material1169 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1169_pa_checked.trans (by decide +kernel)
    · exact v1169_pb_checked.trans (by decide +kernel)
    · exact v1169_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 84 Primitive.Addresses.material1169
    · exact v1169_mb_checked.trans (by decide +kernel)
    · exact v1169_mg_checked.trans (by decide +kernel)
  upper_error := v1169_upper_checked
  lower_error := reuse_lower_error 12 84 Primitive.Addresses.material1169

def v1170_pa : Scalar.QComplex := ((999999287747991864835187458591 : Int)/10^30,(-1193525663304902100548704532 : Int)/10^30)
theorem v1170_pa_checked : Scalar.distance (sourceCoefficient 12 85 1 0) v1170_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1170_pb : Scalar.QComplex := ((-514979355523134373776044 : Int)/10^30,(-431477097276705964698039294 : Int)/10^30)
theorem v1170_pb_checked : Scalar.distance (sourceCoefficient 12 85 1 1) v1170_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1170_pg : Scalar.QComplex := ((-93086351039635860275133 : Int)/10^30,(111101028001144653074 : Int)/10^30)
theorem v1170_pg_checked : Scalar.distance (sourceCoefficient 12 85 1 2) v1170_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1170_mb : Scalar.QComplex := ((-887324465715507629667867 : Int)/10^30,(-431476492214073163786038846 : Int)/10^30)
theorem v1170_mb_checked : Scalar.distance (sourceCoefficient 12 85 3 1) v1170_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1170_mg : Scalar.QComplex := ((-93086220504149751375040 : Int)/10^30,(191430315126740476519 : Int)/10^30)
theorem v1170_mg_checked : Scalar.distance (sourceCoefficient 12 85 3 2) v1170_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1170_upper : Scalar.QComplex := ((999995738449501870338771911014 : Int)/10^30,(-2919431937114937150870973687 : Int)/10^30)
theorem v1170_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 85 5) 1) 14) v1170_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1170 : Material (12 : Basis) (85 : Basis) where
  plus := ![v1170_pa,v1170_pb,v1170_pg]
  minus := ![(Primitive.Addresses.material1170 1).one,v1170_mb,v1170_mg]
  upper := v1170_upper
  lower := (Primitive.Addresses.material1170 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1170_pa_checked.trans (by decide +kernel)
    · exact v1170_pb_checked.trans (by decide +kernel)
    · exact v1170_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 85 Primitive.Addresses.material1170
    · exact v1170_mb_checked.trans (by decide +kernel)
    · exact v1170_mg_checked.trans (by decide +kernel)
  upper_error := v1170_upper_checked
  lower_error := reuse_lower_error 12 85 Primitive.Addresses.material1170

def v1171_pa : Scalar.QComplex := ((999999270234488995198983288777 : Int)/10^30,(-1208110296890106380043550121 : Int)/10^30)
theorem v1171_pa_checked : Scalar.distance (sourceCoefficient 12 86 1 0) v1171_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1171_pb : Scalar.QComplex := ((-521272292126827571846085 : Int)/10^30,(-431477087035955885318054806 : Int)/10^30)
theorem v1171_pb_checked : Scalar.distance (sourceCoefficient 12 86 1 1) v1171_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1171_pg : Scalar.QComplex := ((-93086349119837702831868 : Int)/10^30,(112458658940033928175 : Int)/10^30)
theorem v1171_pg_checked : Scalar.distance (sourceCoefficient 12 86 1 2) v1171_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1171_mb : Scalar.QComplex := ((-893617391138746836529469 : Int)/10^30,(-431476476542806031861565657 : Int)/10^30)
theorem v1171_mb_checked : Scalar.distance (sourceCoefficient 12 86 3 1) v1171_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1171_mg : Scalar.QComplex := ((-93086217412777953926586 : Int)/10^30,(192787943903422360898 : Int)/10^30)
theorem v1171_mg_checked : Scalar.distance (sourceCoefficient 12 86 3 2) v1171_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1171_upper : Scalar.QComplex := ((999995695764270624568525270424 : Int)/10^30,(-2934016518751325796190027891 : Int)/10^30)
theorem v1171_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 86 5) 1) 14) v1171_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1171 : Material (12 : Basis) (86 : Basis) where
  plus := ![v1171_pa,v1171_pb,v1171_pg]
  minus := ![(Primitive.Addresses.material1171 1).one,v1171_mb,v1171_mg]
  upper := v1171_upper
  lower := (Primitive.Addresses.material1171 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1171_pa_checked.trans (by decide +kernel)
    · exact v1171_pb_checked.trans (by decide +kernel)
    · exact v1171_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 86 Primitive.Addresses.material1171
    · exact v1171_mb_checked.trans (by decide +kernel)
    · exact v1171_mg_checked.trans (by decide +kernel)
  upper_error := v1171_upper_checked
  lower_error := reuse_lower_error 12 86 Primitive.Addresses.material1171

def v1172_pa : Scalar.QComplex := ((999999269067282352834218816203 : Int)/10^30,(-1209076052625182811455339498 : Int)/10^30)
theorem v1172_pa_checked : Scalar.distance (sourceCoefficient 12 87 1 0) v1172_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1172_pb : Scalar.QComplex := ((-521688993686083823649660 : Int)/10^30,(-431477086353520666820922693 : Int)/10^30)
theorem v1172_pb_checked : Scalar.distance (sourceCoefficient 12 87 1 1) v1172_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1172_pg : Scalar.QComplex := ((-93086348991898284794622 : Int)/10^30,(112548557657837659648 : Int)/10^30)
theorem v1172_pg_checked : Scalar.distance (sourceCoefficient 12 87 1 2) v1172_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1172_mb : Scalar.QComplex := ((-894034091953935195798133 : Int)/10^30,(-431476475500776389369653925 : Int)/10^30)
theorem v1172_mb_checked : Scalar.distance (sourceCoefficient 12 87 3 1) v1172_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1172_mg : Scalar.QComplex := ((-93086217207260038950361 : Int)/10^30,(192877842477346735569 : Int)/10^30)
theorem v1172_mg_checked : Scalar.distance (sourceCoefficient 12 87 3 2) v1172_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1172_upper : Scalar.QComplex := ((999995692930258934554917727920 : Int)/10^30,(-2934982271033529729281095106 : Int)/10^30)
theorem v1172_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 87 5) 1) 14) v1172_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1172 : Material (12 : Basis) (87 : Basis) where
  plus := ![v1172_pa,v1172_pb,v1172_pg]
  minus := ![(Primitive.Addresses.material1172 1).one,v1172_mb,v1172_mg]
  upper := v1172_upper
  lower := (Primitive.Addresses.material1172 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1172_pa_checked.trans (by decide +kernel)
    · exact v1172_pb_checked.trans (by decide +kernel)
    · exact v1172_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 87 Primitive.Addresses.material1172
    · exact v1172_mb_checked.trans (by decide +kernel)
    · exact v1172_mg_checked.trans (by decide +kernel)
  upper_error := v1172_upper_checked
  lower_error := reuse_lower_error 12 87 Primitive.Addresses.material1172

def v1173_pa : Scalar.QComplex := ((999999254779895426916234740617 : Int)/10^30,(-1220835637501282672398585787 : Int)/10^30)
theorem v1173_pa_checked : Scalar.distance (sourceCoefficient 12 88 1 0) v1173_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1173_pb : Scalar.QComplex := ((-526762986142616254095535 : Int)/10^30,(-431477078000760107993326789 : Int)/10^30)
theorem v1173_pb_checked : Scalar.distance (sourceCoefficient 12 88 1 1) v1173_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1173_pg : Scalar.QComplex := ((-93086347425910206284116 : Int)/10^30,(113643214991585530046 : Int)/10^30)
theorem v1173_pg_checked : Scalar.distance (sourceCoefficient 12 88 1 2) v1173_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1173_mb : Scalar.QComplex := ((-899108075313132173868341 : Int)/10^30,(-431476462769391974806094111 : Int)/10^30)
theorem v1173_mb_checked : Scalar.distance (sourceCoefficient 12 88 3 1) v1173_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1173_mg : Scalar.QComplex := ((-93086214696632566040527 : Int)/10^30,(193972498052126470032 : Int)/10^30)
theorem v1173_mg_checked : Scalar.distance (sourceCoefficient 12 88 3 2) v1173_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1173_upper : Scalar.QComplex := ((999995658346916613079495302380 : Int)/10^30,(-2946741813736375602632224579 : Int)/10^30)
theorem v1173_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 88 5) 1) 14) v1173_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1173 : Material (12 : Basis) (88 : Basis) where
  plus := ![v1173_pa,v1173_pb,v1173_pg]
  minus := ![(Primitive.Addresses.material1173 1).one,v1173_mb,v1173_mg]
  upper := v1173_upper
  lower := (Primitive.Addresses.material1173 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1173_pa_checked.trans (by decide +kernel)
    · exact v1173_pb_checked.trans (by decide +kernel)
    · exact v1173_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 88 Primitive.Addresses.material1173
    · exact v1173_mb_checked.trans (by decide +kernel)
    · exact v1173_mg_checked.trans (by decide +kernel)
  upper_error := v1173_upper_checked
  lower_error := reuse_lower_error 12 88 Primitive.Addresses.material1173

def v1174_pa : Scalar.QComplex := ((999999235007843667980412072578 : Int)/10^30,(-1236925109879753361271519389 : Int)/10^30)
theorem v1174_pa_checked : Scalar.distance (sourceCoefficient 12 89 1 0) v1174_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1174_pb : Scalar.QComplex := ((-533705226101676404927369 : Int)/10^30,(-431477066443617035687909755 : Int)/10^30)
theorem v1174_pb_checked : Scalar.distance (sourceCoefficient 12 89 1 1) v1174_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1174_pg : Scalar.QComplex := ((-93086345258993417033408 : Int)/10^30,(115140925919690292094 : Int)/10^30)
theorem v1174_pg_checked : Scalar.distance (sourceCoefficient 12 89 1 2) v1174_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1174_mb : Scalar.QComplex := ((-906050302713985154904197 : Int)/10^30,(-431476445221412787965336127 : Int)/10^30)
theorem v1174_mb_checked : Scalar.distance (sourceCoefficient 12 89 3 1) v1174_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1174_mg : Scalar.QComplex := ((-93086211237259507073739 : Int)/10^30,(195470206552613409961 : Int)/10^30)
theorem v1174_mg_checked : Scalar.distance (sourceCoefficient 12 89 3 2) v1174_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1174_upper : Scalar.QComplex := ((999995610805924602583976147041 : Int)/10^30,(-2962831228026699556564729272 : Int)/10^30)
theorem v1174_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 89 5) 1) 14) v1174_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1174 : Material (12 : Basis) (89 : Basis) where
  plus := ![v1174_pa,v1174_pb,v1174_pg]
  minus := ![(Primitive.Addresses.material1174 1).one,v1174_mb,v1174_mg]
  upper := v1174_upper
  lower := (Primitive.Addresses.material1174 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1174_pa_checked.trans (by decide +kernel)
    · exact v1174_pb_checked.trans (by decide +kernel)
    · exact v1174_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 89 Primitive.Addresses.material1174
    · exact v1174_mb_checked.trans (by decide +kernel)
    · exact v1174_mg_checked.trans (by decide +kernel)
  upper_error := v1174_upper_checked
  lower_error := reuse_lower_error 12 89 Primitive.Addresses.material1174

def v1175_pa : Scalar.QComplex := ((999999202253470339414280733237 : Int)/10^30,(-1263128031088553530017382950 : Int)/10^30)
theorem v1175_pa_checked : Scalar.distance (sourceCoefficient 12 90 1 0) v1175_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1175_pb : Scalar.QComplex := ((-545011188000733398128492 : Int)/10^30,(-431477047303165049220726329 : Int)/10^30)
theorem v1175_pb_checked : Scalar.distance (sourceCoefficient 12 90 1 1) v1175_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1175_pg : Scalar.QComplex := ((-93086341669830762347913 : Int)/10^30,(117580061273735545501 : Int)/10^30)
theorem v1175_pg_checked : Scalar.distance (sourceCoefficient 12 90 1 2) v1175_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1175_mb : Scalar.QComplex := ((-917356243885967814737066 : Int)/10^30,(-431476416324432011098484819 : Int)/10^30)
theorem v1175_mb_checked : Scalar.distance (sourceCoefficient 12 90 3 1) v1175_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1175_mg : Scalar.QComplex := ((-93086205543234232834832 : Int)/10^30,(197909337901171375956 : Int)/10^30)
theorem v1175_mg_checked : Scalar.distance (sourceCoefficient 12 90 3 2) v1175_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1175_upper : Scalar.QComplex := ((999995532827735161863322086263 : Int)/10^30,(-2989034053678249684577934790 : Int)/10^30)
theorem v1175_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 90 5) 1) 14) v1175_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1175 : Material (12 : Basis) (90 : Basis) where
  plus := ![v1175_pa,v1175_pb,v1175_pg]
  minus := ![(Primitive.Addresses.material1175 1).one,v1175_mb,v1175_mg]
  upper := v1175_upper
  lower := (Primitive.Addresses.material1175 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1175_pa_checked.trans (by decide +kernel)
    · exact v1175_pb_checked.trans (by decide +kernel)
    · exact v1175_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 90 Primitive.Addresses.material1175
    · exact v1175_mb_checked.trans (by decide +kernel)
    · exact v1175_mg_checked.trans (by decide +kernel)
  upper_error := v1175_upper_checked
  lower_error := reuse_lower_error 12 90 Primitive.Addresses.material1175

def v1176_pa : Scalar.QComplex := ((999999183499403284977918949159 : Int)/10^30,(-1277889090162686898785593333 : Int)/10^30)
theorem v1176_pa_checked : Scalar.distance (sourceCoefficient 12 91 1 0) v1176_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1176_pb : Scalar.QComplex := ((-551380247605499767831410 : Int)/10^30,(-431477036346716850148378972 : Int)/10^30)
theorem v1176_pb_checked : Scalar.distance (sourceCoefficient 12 91 1 1) v1176_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1176_pg : Scalar.QComplex := ((-93086339615090840415463 : Int)/10^30,(118954114963409161568 : Int)/10^30)
theorem v1176_pg_checked : Scalar.distance (sourceCoefficient 12 91 1 2) v1176_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1176_mb : Scalar.QComplex := ((-923725291664320877491213 : Int)/10^30,(-431476399871776304495318812 : Int)/10^30)
theorem v1176_mb_checked : Scalar.distance (sourceCoefficient 12 91 3 1) v1176_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1176_mg : Scalar.QComplex := ((-93086202302748626868531 : Int)/10^30,(199283389306073995425 : Int)/10^30)
theorem v1176_mg_checked : Scalar.distance (sourceCoefficient 12 91 3 2) v1176_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1176_upper : Scalar.QComplex := ((999995488597447190271266021785 : Int)/10^30,(-3003795058399701137942848732 : Int)/10^30)
theorem v1176_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 91 5) 1) 14) v1176_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1176 : Material (12 : Basis) (91 : Basis) where
  plus := ![v1176_pa,v1176_pb,v1176_pg]
  minus := ![(Primitive.Addresses.material1176 1).one,v1176_mb,v1176_mg]
  upper := v1176_upper
  lower := (Primitive.Addresses.material1176 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1176_pa_checked.trans (by decide +kernel)
    · exact v1176_pb_checked.trans (by decide +kernel)
    · exact v1176_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 91 Primitive.Addresses.material1176
    · exact v1176_mb_checked.trans (by decide +kernel)
    · exact v1176_mg_checked.trans (by decide +kernel)
  upper_error := v1176_upper_checked
  lower_error := reuse_lower_error 12 91 Primitive.Addresses.material1176

def v1177_pa : Scalar.QComplex := ((999999142152449915008871579403 : Int)/10^30,(-1309845168051385785627905400 : Int)/10^30)
theorem v1177_pa_checked : Scalar.distance (sourceCoefficient 12 92 1 0) v1177_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1177_pb : Scalar.QComplex := ((-565168564380966909723521 : Int)/10^30,(-431477012197770527033248011 : Int)/10^30)
theorem v1177_pb_checked : Scalar.distance (sourceCoefficient 12 92 1 1) v1177_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1177_pg : Scalar.QComplex := ((-93086335085738671032370 : Int)/10^30,(121928790819981468169 : Int)/10^30)
theorem v1177_pg_checked : Scalar.distance (sourceCoefficient 12 92 1 2) v1177_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1177_mb : Scalar.QComplex := ((-937513582466314477989251 : Int)/10^30,(-431476363824142598643283784 : Int)/10^30)
theorem v1177_mb_checked : Scalar.distance (sourceCoefficient 12 92 3 1) v1177_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1177_mg : Scalar.QComplex := ((-93086195206386854175568 : Int)/10^30,(202258060146411603492 : Int)/10^30)
theorem v1177_mg_checked : Scalar.distance (sourceCoefficient 12 92 3 2) v1177_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1177_upper : Scalar.QComplex := ((999995392097263998578091979578 : Int)/10^30,(-3035751017332485283910978485 : Int)/10^30)
theorem v1177_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 92 5) 1) 14) v1177_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1177 : Material (12 : Basis) (92 : Basis) where
  plus := ![v1177_pa,v1177_pb,v1177_pg]
  minus := ![(Primitive.Addresses.material1177 1).one,v1177_mb,v1177_mg]
  upper := v1177_upper
  lower := (Primitive.Addresses.material1177 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1177_pa_checked.trans (by decide +kernel)
    · exact v1177_pb_checked.trans (by decide +kernel)
    · exact v1177_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 92 Primitive.Addresses.material1177
    · exact v1177_mb_checked.trans (by decide +kernel)
    · exact v1177_mg_checked.trans (by decide +kernel)
  upper_error := v1177_upper_checked
  lower_error := reuse_lower_error 12 92 Primitive.Addresses.material1177

def v1178_pa : Scalar.QComplex := ((999999091756595301907137562013 : Int)/10^30,(-1347770746265886106130688381 : Int)/10^30)
theorem v1178_pa_checked : Scalar.distance (sourceCoefficient 12 93 1 0) v1178_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1178_pb : Scalar.QComplex := ((-581532583244828888917844 : Int)/10^30,(-431476982775356814965462105 : Int)/10^30)
theorem v1178_pb_checked : Scalar.distance (sourceCoefficient 12 93 1 1) v1178_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1178_pg : Scalar.QComplex := ((-93086329566375849965022 : Int)/10^30,(125459145814268342392 : Int)/10^30)
theorem v1178_pg_checked : Scalar.distance (sourceCoefficient 12 93 1 2) v1178_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1178_mb : Scalar.QComplex := ((-953877569846886464367743 : Int)/10^30,(-431476320280328570422509053 : Int)/10^30)
theorem v1178_mb_checked : Scalar.distance (sourceCoefficient 12 93 3 1) v1178_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1178_mg : Scalar.QComplex := ((-93086186640488729436211 : Int)/10^30,(205788409063224436441 : Int)/10^30)
theorem v1178_mg_checked : Scalar.distance (sourceCoefficient 12 93 3 2) v1178_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1178_upper : Scalar.QComplex := ((999995276245377027533609157931 : Int)/10^30,(-3073676452082618719286269638 : Int)/10^30)
theorem v1178_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 93 5) 1) 14) v1178_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1178 : Material (12 : Basis) (93 : Basis) where
  plus := ![v1178_pa,v1178_pb,v1178_pg]
  minus := ![(Primitive.Addresses.material1178 1).one,v1178_mb,v1178_mg]
  upper := v1178_upper
  lower := (Primitive.Addresses.material1178 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1178_pa_checked.trans (by decide +kernel)
    · exact v1178_pb_checked.trans (by decide +kernel)
    · exact v1178_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 93 Primitive.Addresses.material1178
    · exact v1178_mb_checked.trans (by decide +kernel)
    · exact v1178_mg_checked.trans (by decide +kernel)
  upper_error := v1178_upper_checked
  lower_error := reuse_lower_error 12 93 Primitive.Addresses.material1178

def v1179_pa : Scalar.QComplex := ((999999030374955587618925936480 : Int)/10^30,(-1392569261707307467601349491 : Int)/10^30)
theorem v1179_pa_checked : Scalar.distance (sourceCoefficient 12 94 1 0) v1179_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1179_pb : Scalar.QComplex := ((-600862116075732473315679 : Int)/10^30,(-431476946954949065895861540 : Int)/10^30)
theorem v1179_pb_checked : Scalar.distance (sourceCoefficient 12 94 1 1) v1179_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1179_pg : Scalar.QComplex := ((-93086322845551573699517 : Int)/10^30,(129629277571871846175 : Int)/10^30)
theorem v1179_pg_checked : Scalar.distance (sourceCoefficient 12 94 1 2) v1179_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1179_mb : Scalar.QComplex := ((-973207064569122976358559 : Int)/10^30,(-431476267779417895699625938 : Int)/10^30)
theorem v1179_mb_checked : Scalar.distance (sourceCoefficient 12 94 3 1) v1179_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1179_mg : Scalar.QComplex := ((-93086176321031064591230 : Int)/10^30,(209958533468328646705 : Int)/10^30)
theorem v1179_mg_checked : Scalar.distance (sourceCoefficient 12 94 3 2) v1179_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1179_upper : Scalar.QComplex := ((999995137545655171668008377588 : Int)/10^30,(-3118474794862772086041932163 : Int)/10^30)
theorem v1179_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 94 5) 1) 14) v1179_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1179 : Material (12 : Basis) (94 : Basis) where
  plus := ![v1179_pa,v1179_pb,v1179_pg]
  minus := ![(Primitive.Addresses.material1179 1).one,v1179_mb,v1179_mg]
  upper := v1179_upper
  lower := (Primitive.Addresses.material1179 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1179_pa_checked.trans (by decide +kernel)
    · exact v1179_pb_checked.trans (by decide +kernel)
    · exact v1179_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 94 Primitive.Addresses.material1179
    · exact v1179_mb_checked.trans (by decide +kernel)
    · exact v1179_mg_checked.trans (by decide +kernel)
  upper_error := v1179_upper_checked
  lower_error := reuse_lower_error 12 94 Primitive.Addresses.material1179

def v1180_pa : Scalar.QComplex := ((999998967739930142938788824498 : Int)/10^30,(-1436843441072572318629126618 : Int)/10^30)
theorem v1180_pa_checked : Scalar.distance (sourceCoefficient 12 95 1 0) v1180_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1180_pb : Scalar.QComplex := ((-619965408675914585793501 : Int)/10^30,(-431476910419404028311488265 : Int)/10^30)
theorem v1180_pb_checked : Scalar.distance (sourceCoefficient 12 95 1 1) v1180_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1180_pg : Scalar.QComplex := ((-93086315989249270653016 : Int)/10^30,(133750600648166099336 : Int)/10^30)
theorem v1180_pg_checked : Scalar.distance (sourceCoefficient 12 95 1 2) v1180_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1180_mb : Scalar.QComplex := ((-992310318527746322615888 : Int)/10^30,(-431476214758605328371155929 : Int)/10^30)
theorem v1180_mb_checked : Scalar.distance (sourceCoefficient 12 95 3 1) v1180_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1180_mg : Scalar.QComplex := ((-93086165908215117118395 : Int)/10^30,(214079849093385873654 : Int)/10^30)
theorem v1180_mg_checked : Scalar.distance (sourceCoefficient 12 95 3 2) v1180_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1180_upper : Scalar.QComplex := ((999994998497505952230178720751 : Int)/10^30,(-3162748800184475870556439652 : Int)/10^30)
theorem v1180_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 95 5) 1) 14) v1180_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1180 : Material (12 : Basis) (95 : Basis) where
  plus := ![v1180_pa,v1180_pb,v1180_pg]
  minus := ![(Primitive.Addresses.material1180 1).one,v1180_mb,v1180_mg]
  upper := v1180_upper
  lower := (Primitive.Addresses.material1180 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1180_pa_checked.trans (by decide +kernel)
    · exact v1180_pb_checked.trans (by decide +kernel)
    · exact v1180_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 95 Primitive.Addresses.material1180
    · exact v1180_mb_checked.trans (by decide +kernel)
    · exact v1180_mg_checked.trans (by decide +kernel)
  upper_error := v1180_upper_checked
  lower_error := reuse_lower_error 12 95 Primitive.Addresses.material1180

def v1181_pa : Scalar.QComplex := ((999998936960671675142613641486 : Int)/10^30,(-1458107515444969238827045744 : Int)/10^30)
theorem v1181_pa_checked : Scalar.distance (sourceCoefficient 12 96 1 0) v1181_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1181_pb : Scalar.QComplex := ((-629140368454020906643777 : Int)/10^30,(-431476892471178477407228982 : Int)/10^30)
theorem v1181_pb_checked : Scalar.distance (sourceCoefficient 12 96 1 1) v1181_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1181_pg : Scalar.QComplex := ((-93086312620619536545360 : Int)/10^30,(135729996303509339883 : Int)/10^30)
theorem v1181_pg_checked : Scalar.distance (sourceCoefficient 12 96 1 2) v1181_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1181_mb : Scalar.QComplex := ((-1001485259401085509341446 : Int)/10^30,(-431476188892809396754567260 : Int)/10^30)
theorem v1181_mb_checked : Scalar.distance (sourceCoefficient 12 96 3 1) v1181_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1181_mg : Scalar.QComplex := ((-93086160831457335415289 : Int)/10^30,(216059241104733905783 : Int)/10^30)
theorem v1181_mg_checked : Scalar.distance (sourceCoefficient 12 96 3 2) v1181_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1181_upper : Scalar.QComplex := ((999994931018430021524881735167 : Int)/10^30,(-3184012789764324023809540239 : Int)/10^30)
theorem v1181_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 96 5) 1) 14) v1181_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1181 : Material (12 : Basis) (96 : Basis) where
  plus := ![v1181_pa,v1181_pb,v1181_pg]
  minus := ![(Primitive.Addresses.material1181 1).one,v1181_mb,v1181_mg]
  upper := v1181_upper
  lower := (Primitive.Addresses.material1181 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1181_pa_checked.trans (by decide +kernel)
    · exact v1181_pb_checked.trans (by decide +kernel)
    · exact v1181_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 96 Primitive.Addresses.material1181
    · exact v1181_mb_checked.trans (by decide +kernel)
    · exact v1181_mg_checked.trans (by decide +kernel)
  upper_error := v1181_upper_checked
  lower_error := reuse_lower_error 12 96 Primitive.Addresses.material1181

def v1182_pa : Scalar.QComplex := ((999998827605931513091532603027 : Int)/10^30,(-1531269657005572977440672240 : Int)/10^30)
theorem v1182_pa_checked : Scalar.distance (sourceCoefficient 12 97 1 0) v1182_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1182_pb : Scalar.QComplex := ((-660708150146281610648110 : Int)/10^30,(-431476828730474065389997497 : Int)/10^30)
theorem v1182_pb_checked : Scalar.distance (sourceCoefficient 12 97 1 1) v1182_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1182_pg : Scalar.QComplex := ((-93086300655227627061029 : Int)/10^30,(142540394789761422899 : Int)/10^30)
theorem v1182_pg_checked : Scalar.distance (sourceCoefficient 12 97 1 2) v1182_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1182_mb : Scalar.QComplex := ((-1033052974333861237609702 : Int)/10^30,(-431476097910554878002898222 : Int)/10^30)
theorem v1182_mb_checked : Scalar.distance (sourceCoefficient 12 97 3 1) v1182_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1182_mg : Scalar.QComplex := ((-93086142989002716519170 : Int)/10^30,(222869626729569065142 : Int)/10^30)
theorem v1182_mg_checked : Scalar.distance (sourceCoefficient 12 97 3 2) v1182_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1182_upper : Scalar.QComplex := ((999994695392633614546788173059 : Int)/10^30,(-3257174633622151201595238482 : Int)/10^30)
theorem v1182_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 97 5) 1) 14) v1182_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1182 : Material (12 : Basis) (97 : Basis) where
  plus := ![v1182_pa,v1182_pb,v1182_pg]
  minus := ![(Primitive.Addresses.material1182 1).one,v1182_mb,v1182_mg]
  upper := v1182_upper
  lower := (Primitive.Addresses.material1182 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1182_pa_checked.trans (by decide +kernel)
    · exact v1182_pb_checked.trans (by decide +kernel)
    · exact v1182_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 97 Primitive.Addresses.material1182
    · exact v1182_mb_checked.trans (by decide +kernel)
    · exact v1182_mg_checked.trans (by decide +kernel)
  upper_error := v1182_upper_checked
  lower_error := reuse_lower_error 12 97 Primitive.Addresses.material1182

def v1183_pa : Scalar.QComplex := ((999999999175945383431862290574 : Int)/10^30,(-40596911612303828151476071 : Int)/10^30)
theorem v1183_pa_checked : Scalar.distance (sourceCoefficient 13 14 1 0) v1183_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1183_pb : Scalar.QComplex := ((-17516654781982815054796 : Int)/10^30,(-431477520625960856339277181 : Int)/10^30)
theorem v1183_pb_checked : Scalar.distance (sourceCoefficient 13 14 1 1) v1183_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1183_pg : Scalar.QComplex := ((-93086429818204123125692 : Int)/10^30,(3779021566748676461 : Int)/10^30)
theorem v1183_pg_checked : Scalar.distance (sourceCoefficient 13 14 1 2) v1183_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1183_mb : Scalar.QComplex := ((-389862315533794754285580 : Int)/10^30,(-431477344851076274432627241 : Int)/10^30)
theorem v1183_mb_checked : Scalar.distance (sourceCoefficient 13 14 3 1) v1183_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1183_mg : Scalar.QComplex := ((-93086391896746630510004 : Int)/10^30,(84108416635588709266 : Int)/10^30)
theorem v1183_mg_checked : Scalar.distance (sourceCoefficient 13 14 3 2) v1183_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1183_upper : Scalar.QComplex := ((999998439726828342674680028847 : Int)/10^30,(-1766506130434389533124418957 : Int)/10^30)
theorem v1183_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 14 5) 1) 14) v1183_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1183 : Material (13 : Basis) (14 : Basis) where
  plus := ![v1183_pa,v1183_pb,v1183_pg]
  minus := ![(Primitive.Addresses.material1183 1).one,v1183_mb,v1183_mg]
  upper := v1183_upper
  lower := (Primitive.Addresses.material1183 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1183_pa_checked.trans (by decide +kernel)
    · exact v1183_pb_checked.trans (by decide +kernel)
    · exact v1183_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 14 Primitive.Addresses.material1183
    · exact v1183_mb_checked.trans (by decide +kernel)
    · exact v1183_mg_checked.trans (by decide +kernel)
  upper_error := v1183_upper_checked
  lower_error := reuse_lower_error 13 14 Primitive.Addresses.material1183

def v1184_pa : Scalar.QComplex := ((999999997763861080666529074673 : Int)/10^30,(-66875091279688168991583878 : Int)/10^30)
theorem v1184_pa_checked : Scalar.distance (sourceCoefficient 13 15 1 0) v1184_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1184_pb : Scalar.QComplex := ((-28855098593329409604964 : Int)/10^30,(-431477519905374680026250294 : Int)/10^30)
theorem v1184_pb_checked : Scalar.distance (sourceCoefficient 13 15 1 1) v1184_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1184_pg : Scalar.QComplex := ((-93086429674751992134558 : Int)/10^30,(6225163495319643321 : Int)/10^30)
theorem v1184_pg_checked : Scalar.distance (sourceCoefficient 13 15 1 2) v1184_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1184_mb : Scalar.QComplex := ((-401200754501487109228494 : Int)/10^30,(-431477334345924021787158905 : Int)/10^30)
theorem v1184_mb_checked : Scalar.distance (sourceCoefficient 13 15 3 1) v1184_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1184_mg : Scalar.QComplex := ((-93086389642384238718665 : Int)/10^30,(86554557529556513709 : Int)/10^30)
theorem v1184_mg_checked : Scalar.distance (sourceCoefficient 13 15 3 2) v1184_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1184_upper : Scalar.QComplex := ((999998392960991974974793103263 : Int)/10^30,(-1792784268526382707933089658 : Int)/10^30)
theorem v1184_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 15 5) 1) 14) v1184_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1184 : Material (13 : Basis) (15 : Basis) where
  plus := ![v1184_pa,v1184_pb,v1184_pg]
  minus := ![(Primitive.Addresses.material1184 1).one,v1184_mb,v1184_mg]
  upper := v1184_upper
  lower := (Primitive.Addresses.material1184 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1184_pa_checked.trans (by decide +kernel)
    · exact v1184_pb_checked.trans (by decide +kernel)
    · exact v1184_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 15 Primitive.Addresses.material1184
    · exact v1184_mb_checked.trans (by decide +kernel)
    · exact v1184_mg_checked.trans (by decide +kernel)
  upper_error := v1184_upper_checked
  lower_error := reuse_lower_error 13 15 Primitive.Addresses.material1184

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
