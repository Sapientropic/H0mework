import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B195
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B196

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4689_pa : Scalar.QComplex := ((999996815269436089047329565363 : Int)/10^30,(-2523777126711695323406336956 : Int)/10^30)
theorem v4689_pa_checked : Scalar.distance (sourceCoefficient 86 89 1 0) v4689_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4689_pb : Scalar.QComplex := ((-1088953098041020387273771 : Int)/10^30,(-431476146801295176916551458 : Int)/10^30)
theorem v4689_pb_checked : Scalar.distance (sourceCoefficient 86 89 1 1) v4689_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4689_pg : Scalar.QComplex := ((-93086133435336928553082 : Int)/10^30,(234929402564984816273 : Int)/10^30)
theorem v4689_pg_checked : Scalar.distance (sourceCoefficient 86 89 1 2) v4689_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4689_mb : Scalar.QComplex := ((-1461297174299265721386971 : Int)/10^30,(-431475046425527306238773410 : Int)/10^30)
theorem v4689_mb_checked : Scalar.distance (sourceCoefficient 86 89 3 1) v4689_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4689_mg : Scalar.QComplex := ((-93085896041621618045960 : Int)/10^30,(315258455800908109045 : Int)/10^30)
theorem v4689_mg_checked : Scalar.distance (sourceCoefficient 86 89 3 2) v4689_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4689_upper : Scalar.QComplex := ((999990970081282190860883899085 : Int)/10^30,(-4249677151994752176453663682 : Int)/10^30)
theorem v4689_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 86 89 5) 1) 14) v4689_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4689 : Material (86 : Basis) (89 : Basis) where
  plus := ![v4689_pa,v4689_pb,v4689_pg]
  minus := ![(Primitive.Addresses.material4689 1).one,v4689_mb,v4689_mg]
  upper := v4689_upper
  lower := (Primitive.Addresses.material4689 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4689_pa_checked.trans (by decide +kernel)
    · exact v4689_pb_checked.trans (by decide +kernel)
    · exact v4689_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 86 89 Primitive.Addresses.material4689
    · exact v4689_mb_checked.trans (by decide +kernel)
    · exact v4689_mg_checked.trans (by decide +kernel)
  upper_error := v4689_upper_checked
  lower_error := reuse_lower_error 86 89 Primitive.Addresses.material4689

def v4690_pa : Scalar.QComplex := ((999996748795755245291412287738 : Int)/10^30,(-2549979984074458586100006988 : Int)/10^30)
theorem v4690_pa_checked : Scalar.distance (sourceCoefficient 86 90 1 0) v4690_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4690_pb : Scalar.QComplex := ((-1100259041574658607257031 : Int)/10^30,(-431476117961428362451118491 : Int)/10^30)
theorem v4690_pb_checked : Scalar.distance (sourceCoefficient 86 90 1 1) v4690_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4690_pg : Scalar.QComplex := ((-93086127230499408215759 : Int)/10^30,(237368532966363858133 : Int)/10^30)
theorem v4690_pg_checked : Scalar.distance (sourceCoefficient 86 90 1 2) v4690_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4690_mb : Scalar.QComplex := ((-1472603088735678295151627 : Int)/10^30,(-431475007829151161438351713 : Int)/10^30)
theorem v4690_mb_checked : Scalar.distance (sourceCoefficient 86 90 3 1) v4690_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4690_mg : Scalar.QComplex := ((-93085887731926726018401 : Int)/10^30,(317697579939592104163 : Int)/10^30)
theorem v4690_mg_checked : Scalar.distance (sourceCoefficient 86 90 3 2) v4690_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4690_upper : Scalar.QComplex := ((999990858383945648365672296161 : Int)/10^30,(-4275879855603894710051440718 : Int)/10^30)
theorem v4690_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 86 90 5) 1) 14) v4690_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4690 : Material (86 : Basis) (90 : Basis) where
  plus := ![v4690_pa,v4690_pb,v4690_pg]
  minus := ![(Primitive.Addresses.material4690 1).one,v4690_mb,v4690_mg]
  upper := v4690_upper
  lower := (Primitive.Addresses.material4690 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4690_pa_checked.trans (by decide +kernel)
    · exact v4690_pb_checked.trans (by decide +kernel)
    · exact v4690_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 86 90 Primitive.Addresses.material4690
    · exact v4690_mb_checked.trans (by decide +kernel)
    · exact v4690_mg_checked.trans (by decide +kernel)
  upper_error := v4690_upper_checked
  lower_error := reuse_lower_error 86 90 Primitive.Addresses.material4690

def v4691_pa : Scalar.QComplex := ((999996711046375429927181732473 : Int)/10^30,(-2564741006792732875907223196 : Int)/10^30)
theorem v4691_pa_checked : Scalar.distance (sourceCoefficient 86 91 1 0) v4691_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4691_pb : Scalar.QComplex := ((-1106628090721601634604377 : Int)/10^30,(-431476101540946904435121372 : Int)/10^30)
theorem v4691_pb_checked : Scalar.distance (sourceCoefficient 86 91 1 1) v4691_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4691_pg : Scalar.QComplex := ((-93086123702254668702331 : Int)/10^30,(238742583835839960136 : Int)/10^30)
theorem v4691_pg_checked : Scalar.distance (sourceCoefficient 86 91 1 2) v4691_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4691_mb : Scalar.QComplex := ((-1478972121340997297930067 : Int)/10^30,(-431474985912473255031378478 : Int)/10^30)
theorem v4691_mb_checked : Scalar.distance (sourceCoefficient 86 91 3 1) v4691_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4691_mg : Scalar.QComplex := ((-93085883017939284827746 : Int)/10^30,(319071627252729966276 : Int)/10^30)
theorem v4691_mg_checked : Scalar.distance (sourceCoefficient 86 91 3 2) v4691_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4691_upper : Scalar.QComplex := ((999990795158435954047351197121 : Int)/10^30,(-4290640791185354648187746867 : Int)/10^30)
theorem v4691_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 86 91 5) 1) 14) v4691_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4691 : Material (86 : Basis) (91 : Basis) where
  plus := ![v4691_pa,v4691_pb,v4691_pg]
  minus := ![(Primitive.Addresses.material4691 1).one,v4691_mb,v4691_mg]
  upper := v4691_upper
  lower := (Primitive.Addresses.material4691 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4691_pa_checked.trans (by decide +kernel)
    · exact v4691_pb_checked.trans (by decide +kernel)
    · exact v4691_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 86 91 Primitive.Addresses.material4691
    · exact v4691_mb_checked.trans (by decide +kernel)
    · exact v4691_mg_checked.trans (by decide +kernel)
  upper_error := v4691_upper_checked
  lower_error := reuse_lower_error 86 91 Primitive.Addresses.material4691

def v4692_pa : Scalar.QComplex := ((999996628576648826910261707201 : Int)/10^30,(-2596697005014402261075242066 : Int)/10^30)
theorem v4692_pa_checked : Scalar.distance (sourceCoefficient 86 92 1 0) v4692_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4692_pb : Scalar.QComplex := ((-1120416384580715285804129 : Int)/10^30,(-431476065562966612851981677 : Int)/10^30)
theorem v4692_pb_checked : Scalar.distance (sourceCoefficient 86 92 1 1) v4692_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4692_pg : Scalar.QComplex := ((-93086115982925839723786 : Int)/10^30,(241717253512479683092 : Int)/10^30)
theorem v4692_pg_checked : Scalar.distance (sourceCoefficient 86 92 1 2) v4692_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4692_mb : Scalar.QComplex := ((-1492760379018722385666550 : Int)/10^30,(-431474938035829760982242956 : Int)/10^30)
theorem v4692_mb_checked : Scalar.distance (sourceCoefficient 86 92 3 1) v4692_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4692_mg : Scalar.QComplex := ((-93085872731607373316914 : Int)/10^30,(322046289160331105755 : Int)/10^30)
theorem v4692_mg_checked : Scalar.distance (sourceCoefficient 86 92 3 2) v4692_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4692_upper : Scalar.QComplex := ((999990657535678274911998277977 : Int)/10^30,(-4322596599477051975768680122 : Int)/10^30)
theorem v4692_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 86 92 5) 1) 14) v4692_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4692 : Material (86 : Basis) (92 : Basis) where
  plus := ![v4692_pa,v4692_pb,v4692_pg]
  minus := ![(Primitive.Addresses.material4692 1).one,v4692_mb,v4692_mg]
  upper := v4692_upper
  lower := (Primitive.Addresses.material4692 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4692_pa_checked.trans (by decide +kernel)
    · exact v4692_pb_checked.trans (by decide +kernel)
    · exact v4692_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 86 92 Primitive.Addresses.material4692
    · exact v4692_mb_checked.trans (by decide +kernel)
    · exact v4692_mg_checked.trans (by decide +kernel)
  upper_error := v4692_upper_checked
  lower_error := reuse_lower_error 86 92 Primitive.Addresses.material4692

def v4693_pa : Scalar.QComplex := ((999996529376152949127858553223 : Int)/10^30,(-2634622486974529822590359144 : Int)/10^30)
theorem v4693_pa_checked : Scalar.distance (sourceCoefficient 86 93 1 0) v4693_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4693_pb : Scalar.QComplex := ((-1136780375756847044396446 : Int)/10^30,(-431476022101816917371094767 : Int)/10^30)
theorem v4693_pb_checked : Scalar.distance (sourceCoefficient 86 93 1 1) v4693_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4693_pg : Scalar.QComplex := ((-93086106677688336901681 : Int)/10^30,(245247601040120235787 : Int)/10^30)
theorem v4693_pg_checked : Scalar.distance (sourceCoefficient 86 93 1 2) v4693_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4693_mb : Scalar.QComplex := ((-1509124326596777588362195 : Int)/10^30,(-431474880453308869875547078 : Int)/10^30)
theorem v4693_mb_checked : Scalar.distance (sourceCoefficient 86 93 3 1) v4693_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4693_mg : Scalar.QComplex := ((-93085860379842419856458 : Int)/10^30,(325576627343461056461 : Int)/10^30)
theorem v4693_mg_checked : Scalar.distance (sourceCoefficient 86 93 3 2) v4693_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4693_upper : Scalar.QComplex := ((999990492879388854282267705313 : Int)/10^30,(-4360521853740572711368486384 : Int)/10^30)
theorem v4693_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 86 93 5) 1) 14) v4693_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4693 : Material (86 : Basis) (93 : Basis) where
  plus := ![v4693_pa,v4693_pb,v4693_pg]
  minus := ![(Primitive.Addresses.material4693 1).one,v4693_mb,v4693_mg]
  upper := v4693_upper
  lower := (Primitive.Addresses.material4693 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4693_pa_checked.trans (by decide +kernel)
    · exact v4693_pb_checked.trans (by decide +kernel)
    · exact v4693_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 86 93 Primitive.Addresses.material4693
    · exact v4693_mb_checked.trans (by decide +kernel)
    · exact v4693_mg_checked.trans (by decide +kernel)
  upper_error := v4693_upper_checked
  lower_error := reuse_lower_error 86 93 Primitive.Addresses.material4693

def v4694_pa : Scalar.QComplex := ((999996410345414129327489694815 : Int)/10^30,(-2679420886333705348699302520 : Int)/10^30)
theorem v4694_pa_checked : Scalar.distance (sourceCoefficient 86 94 1 0) v4694_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4694_pb : Scalar.QComplex := ((-1156109875196499985457914 : Int)/10^30,(-431475969698550329598070497 : Int)/10^30)
theorem v4694_pb_checked : Scalar.distance (sourceCoefficient 86 94 1 1) v4694_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4694_pg : Scalar.QComplex := ((-93086095484906922479994 : Int)/10^30,(249417723792989244740 : Int)/10^30)
theorem v4694_pg_checked : Scalar.distance (sourceCoefficient 86 94 1 2) v4694_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4694_mb : Scalar.QComplex := ((-1528453773617515576541451 : Int)/10^30,(-431474811369574346150879092 : Int)/10^30)
theorem v4694_mb_checked : Scalar.distance (sourceCoefficient 86 94 3 1) v4694_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4694_mg : Scalar.QComplex := ((-93085845588437052649627 : Int)/10^30,(329746738884736524012 : Int)/10^30)
theorem v4694_mg_checked : Scalar.distance (sourceCoefficient 86 94 3 2) v4694_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4694_upper : Scalar.QComplex := ((999990296530854101891101223769 : Int)/10^30,(-4405319980941537962934870256 : Int)/10^30)
theorem v4694_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 86 94 5) 1) 14) v4694_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4694 : Material (86 : Basis) (94 : Basis) where
  plus := ![v4694_pa,v4694_pb,v4694_pg]
  minus := ![(Primitive.Addresses.material4694 1).one,v4694_mb,v4694_mg]
  upper := v4694_upper
  lower := (Primitive.Addresses.material4694 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4694_pa_checked.trans (by decide +kernel)
    · exact v4694_pb_checked.trans (by decide +kernel)
    · exact v4694_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 86 94 Primitive.Addresses.material4694
    · exact v4694_mb_checked.trans (by decide +kernel)
    · exact v4694_mg_checked.trans (by decide +kernel)
  upper_error := v4694_upper_checked
  lower_error := reuse_lower_error 86 94 Primitive.Addresses.material4694

def v4695_pa : Scalar.QComplex := ((999996290736034607217828183415 : Int)/10^30,(-2723694948437948581541120890 : Int)/10^30)
theorem v4695_pa_checked : Scalar.distance (sourceCoefficient 86 95 1 0) v4695_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4695_pb : Scalar.QComplex := ((-1175213134066354881189382 : Int)/10^30,(-431475916774238099009795180 : Int)/10^30)
theorem v4695_pb_checked : Scalar.distance (sourceCoefficient 86 95 1 1) v4695_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4695_pg : Scalar.QComplex := ((-93086084208988836453063 : Int)/10^30,(253539037773109020729 : Int)/10^30)
theorem v4695_pg_checked : Scalar.distance (sourceCoefficient 86 95 1 2) v4695_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4695_mb : Scalar.QComplex := ((-1547556979703056300506404 : Int)/10^30,(-431474741960029795858767168 : Int)/10^30)
theorem v4695_mb_checked : Scalar.distance (sourceCoefficient 86 95 3 1) v4695_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4695_mg : Scalar.QComplex := ((-93085830756014817410203 : Int)/10^30,(333868041599693292106 : Int)/10^30)
theorem v4695_mg_checked : Scalar.distance (sourceCoefficient 86 95 3 2) v4695_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4695_upper : Scalar.QComplex := ((999990100508638043516943939868 : Int)/10^30,(-4449593770669828311163759426 : Int)/10^30)
theorem v4695_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 86 95 5) 1) 14) v4695_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4695 : Material (86 : Basis) (95 : Basis) where
  plus := ![v4695_pa,v4695_pb,v4695_pg]
  minus := ![(Primitive.Addresses.material4695 1).one,v4695_mb,v4695_mg]
  upper := v4695_upper
  lower := (Primitive.Addresses.material4695 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4695_pa_checked.trans (by decide +kernel)
    · exact v4695_pb_checked.trans (by decide +kernel)
    · exact v4695_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 86 95 Primitive.Addresses.material4695
    · exact v4695_mb_checked.trans (by decide +kernel)
    · exact v4695_mg_checked.trans (by decide +kernel)
  upper_error := v4695_upper_checked
  lower_error := reuse_lower_error 86 95 Primitive.Addresses.material4695

def v4696_pa : Scalar.QComplex := ((999996232593041921277319420784 : Int)/10^30,(-2744958965595343390830887028 : Int)/10^30)
theorem v4696_pa_checked : Scalar.distance (sourceCoefficient 86 96 1 0) v4696_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4696_pb : Scalar.QComplex := ((-1184388077386471105659742 : Int)/10^30,(-431475890954789181850314698 : Int)/10^30)
theorem v4696_pb_checked : Scalar.distance (sourceCoefficient 86 96 1 1) v4696_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4696_pg : Scalar.QComplex := ((-93086078717698947983369 : Int)/10^30,(255518428990168908087 : Int)/10^30)
theorem v4696_pg_checked : Scalar.distance (sourceCoefficient 86 96 1 2) v4696_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4696_mb : Scalar.QComplex := ((-1556731897325900260576178 : Int)/10^30,(-431474708223027631307362054 : Int)/10^30)
theorem v4696_mb_checked : Scalar.distance (sourceCoefficient 86 96 3 1) v4696_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4696_mg : Scalar.QComplex := ((-93085823556601501747085 : Int)/10^30,(335847427340999511471 : Int)/10^30)
theorem v4696_mg_checked : Scalar.distance (sourceCoefficient 86 96 3 2) v4696_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4696_upper : Scalar.QComplex := ((999990005665967397638200264174 : Int)/10^30,(-4470857655807436726592965508 : Int)/10^30)
theorem v4696_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 86 96 5) 1) 14) v4696_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4696 : Material (86 : Basis) (96 : Basis) where
  plus := ![v4696_pa,v4696_pb,v4696_pg]
  minus := ![(Primitive.Addresses.material4696 1).one,v4696_mb,v4696_mg]
  upper := v4696_upper
  lower := (Primitive.Addresses.material4696 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4696_pa_checked.trans (by decide +kernel)
    · exact v4696_pb_checked.trans (by decide +kernel)
    · exact v4696_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 86 96 Primitive.Addresses.material4696
    · exact v4696_mb_checked.trans (by decide +kernel)
    · exact v4696_mg_checked.trans (by decide +kernel)
  upper_error := v4696_upper_checked
  lower_error := reuse_lower_error 86 96 Primitive.Addresses.material4696

def v4697_pa : Scalar.QComplex := ((999996029089395927880989897943 : Int)/10^30,(-2818120905854326983191152180 : Int)/10^30)
theorem v4697_pa_checked : Scalar.distance (sourceCoefficient 86 97 1 0) v4697_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4697_pb : Scalar.QComplex := ((-1215955801173987929937820 : Int)/10^30,(-431475800131996659842816131 : Int)/10^30)
theorem v4697_pb_checked : Scalar.distance (sourceCoefficient 86 97 1 1) v4697_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4697_pg : Scalar.QComplex := ((-93086059448986213912745 : Int)/10^30,(262328811861047535504 : Int)/10^30)
theorem v4697_pg_checked : Scalar.distance (sourceCoefficient 86 97 1 2) v4697_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4697_mb : Scalar.QComplex := ((-1588299530983331362748997 : Int)/10^30,(-431474590158745055650577204 : Int)/10^30)
theorem v4697_mb_checked : Scalar.distance (sourceCoefficient 86 97 3 1) v4697_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4697_mg : Scalar.QComplex := ((-93085798410842252988797 : Int)/10^30,(342657791048030087290 : Int)/10^30)
theorem v4697_mg_checked : Scalar.distance (sourceCoefficient 86 97 3 2) v4697_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4697_upper : Scalar.QComplex := ((999989675891752811385018747546 : Int)/10^30,(-4544019135871473230357497890 : Int)/10^30)
theorem v4697_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 86 97 5) 1) 14) v4697_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4697 : Material (86 : Basis) (97 : Basis) where
  plus := ![v4697_pa,v4697_pb,v4697_pg]
  minus := ![(Primitive.Addresses.material4697 1).one,v4697_mb,v4697_mg]
  upper := v4697_upper
  lower := (Primitive.Addresses.material4697 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4697_pa_checked.trans (by decide +kernel)
    · exact v4697_pb_checked.trans (by decide +kernel)
    · exact v4697_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 86 97 Primitive.Addresses.material4697
    · exact v4697_mb_checked.trans (by decide +kernel)
    · exact v4697_mg_checked.trans (by decide +kernel)
  upper_error := v4697_upper_checked
  lower_error := reuse_lower_error 86 97 Primitive.Addresses.material4697

def v4698_pa : Scalar.QComplex := ((999996853323991892705207071124 : Int)/10^30,(-2508653446501666476802415606 : Int)/10^30)
theorem v4698_pa_checked : Scalar.distance (sourceCoefficient 87 88 1 0) v4698_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4698_pb : Scalar.QComplex := ((-1082427570121334709552410 : Int)/10^30,(-431476163270744638444464661 : Int)/10^30)
theorem v4698_pb_checked : Scalar.distance (sourceCoefficient 87 88 1 1) v4698_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4698_pg : Scalar.QComplex := ((-93086136983067688204800 : Int)/10^30,(233521593180893631356 : Int)/10^30)
theorem v4698_pg_checked : Scalar.distance (sourceCoefficient 87 88 1 2) v4698_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4698_mb : Scalar.QComplex := ((-1454771663021725448353582 : Int)/10^30,(-431475068526207331259237083 : Int)/10^30)
theorem v4698_mb_checked : Scalar.distance (sourceCoefficient 87 88 3 1) v4698_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4698_mg : Scalar.QComplex := ((-93085900804227149805128 : Int)/10^30,(313850650002540559610 : Int)/10^30)
theorem v4698_mg_checked : Scalar.distance (sourceCoefficient 87 88 3 2) v4698_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4698_upper : Scalar.QComplex := ((999991034237881349686779868406 : Int)/10^30,(-4234553559988379485192987093 : Int)/10^30)
theorem v4698_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 87 88 5) 1) 14) v4698_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4698 : Material (87 : Basis) (88 : Basis) where
  plus := ![v4698_pa,v4698_pb,v4698_pg]
  minus := ![(Primitive.Addresses.material4698 1).one,v4698_mb,v4698_mg]
  upper := v4698_upper
  lower := (Primitive.Addresses.material4698 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4698_pa_checked.trans (by decide +kernel)
    · exact v4698_pb_checked.trans (by decide +kernel)
    · exact v4698_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 87 88 Primitive.Addresses.material4698
    · exact v4698_mb_checked.trans (by decide +kernel)
    · exact v4698_mg_checked.trans (by decide +kernel)
  upper_error := v4698_upper_checked
  lower_error := reuse_lower_error 87 88 Primitive.Addresses.material4698

def v4699_pa : Scalar.QComplex := ((999996812831615733486088778201 : Int)/10^30,(-2524742880075259892289913972 : Int)/10^30)
theorem v4699_pa_checked : Scalar.distance (sourceCoefficient 87 89 1 0) v4699_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4699_pb : Scalar.QComplex := ((-1089369798918107300567568 : Int)/10^30,(-431476145753365810363748110 : Int)/10^30)
theorem v4699_pb_checked : Scalar.distance (sourceCoefficient 87 89 1 1) v4699_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4699_pg : Scalar.QComplex := ((-93086133208833435157237 : Int)/10^30,(235019301098825575467 : Int)/10^30)
theorem v4699_pg_checked : Scalar.distance (sourceCoefficient 87 89 1 2) v4699_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4699_mb : Scalar.QComplex := ((-1461713874116880007621992 : Int)/10^30,(-431475045018004240462781040 : Int)/10^30)
theorem v4699_mb_checked : Scalar.distance (sourceCoefficient 87 89 3 1) v4699_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4699_mg : Scalar.QComplex := ((-93085895737539823162804 : Int)/10^30,(315348354105813222063 : Int)/10^30)
theorem v4699_mg_checked : Scalar.distance (sourceCoefficient 87 89 3 2) v4699_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4699_upper : Scalar.QComplex := ((999990965976662773095001924798 : Int)/10^30,(-4250642899712483779303370099 : Int)/10^30)
theorem v4699_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 87 89 5) 1) 14) v4699_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4699 : Material (87 : Basis) (89 : Basis) where
  plus := ![v4699_pa,v4699_pb,v4699_pg]
  minus := ![(Primitive.Addresses.material4699 1).one,v4699_mb,v4699_mg]
  upper := v4699_upper
  lower := (Primitive.Addresses.material4699 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4699_pa_checked.trans (by decide +kernel)
    · exact v4699_pb_checked.trans (by decide +kernel)
    · exact v4699_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 87 89 Primitive.Addresses.material4699
    · exact v4699_mb_checked.trans (by decide +kernel)
    · exact v4699_mg_checked.trans (by decide +kernel)
  upper_error := v4699_upper_checked
  lower_error := reuse_lower_error 87 89 Primitive.Addresses.material4699

def v4700_pa : Scalar.QComplex := ((999996746332629311505791936210 : Int)/10^30,(-2550945737373813550078008527 : Int)/10^30)
theorem v4700_pa_checked : Scalar.distance (sourceCoefficient 87 90 1 0) v4700_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4700_pb : Scalar.QComplex := ((-1100675742433275519902669 : Int)/10^30,(-431476116906219803838283829 : Int)/10^30)
theorem v4700_pb_checked : Scalar.distance (sourceCoefficient 87 90 1 1) v4700_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4700_pg : Scalar.QComplex := ((-93086127002032909876853 : Int)/10^30,(237458431495223748260 : Int)/10^30)
theorem v4700_pg_checked : Scalar.distance (sourceCoefficient 87 90 1 2) v4700_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4700_mb : Scalar.QComplex := ((-1473019788528540972710548 : Int)/10^30,(-431475006414348922251482610 : Int)/10^30)
theorem v4700_mb_checked : Scalar.distance (sourceCoefficient 87 90 3 1) v4700_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4700_mg : Scalar.QComplex := ((-93085887425881931221366 : Int)/10^30,(317787478237822365112 : Int)/10^30)
theorem v4700_mg_checked : Scalar.distance (sourceCoefficient 87 90 3 2) v4700_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4700_upper : Scalar.QComplex := ((999990854254020800885049937858 : Int)/10^30,(-4276845603213741671317079906 : Int)/10^30)
theorem v4700_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 87 90 5) 1) 14) v4700_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4700 : Material (87 : Basis) (90 : Basis) where
  plus := ![v4700_pa,v4700_pb,v4700_pg]
  minus := ![(Primitive.Addresses.material4700 1).one,v4700_mb,v4700_mg]
  upper := v4700_upper
  lower := (Primitive.Addresses.material4700 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4700_pa_checked.trans (by decide +kernel)
    · exact v4700_pb_checked.trans (by decide +kernel)
    · exact v4700_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 87 90 Primitive.Addresses.material4700
    · exact v4700_mb_checked.trans (by decide +kernel)
    · exact v4700_mg_checked.trans (by decide +kernel)
  upper_error := v4700_upper_checked
  lower_error := reuse_lower_error 87 90 Primitive.Addresses.material4700

def v4701_pa : Scalar.QComplex := ((999996708568993943401871633558 : Int)/10^30,(-2565706760055624249510899794 : Int)/10^30)
theorem v4701_pa_checked : Scalar.distance (sourceCoefficient 87 91 1 0) v4701_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4701_pb : Scalar.QComplex := ((-1107044791569729734264815 : Int)/10^30,(-431476100481637712144903468 : Int)/10^30)
theorem v4701_pb_checked : Scalar.distance (sourceCoefficient 87 91 1 1) v4701_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4701_pg : Scalar.QComplex := ((-93086123472682338272078 : Int)/10^30,(238832482361871295724 : Int)/10^30)
theorem v4701_pg_checked : Scalar.distance (sourceCoefficient 87 91 1 2) v4701_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4701_mb : Scalar.QComplex := ((-1479388821119832504231356 : Int)/10^30,(-431474984493570392745352667 : Int)/10^30)
theorem v4701_mb_checked : Scalar.distance (sourceCoefficient 87 91 3 1) v4701_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4701_mg : Scalar.QComplex := ((-93085882710788660792032 : Int)/10^30,(319161525547177390450 : Int)/10^30)
theorem v4701_mg_checked : Scalar.distance (sourceCoefficient 87 91 3 2) v4701_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4701_upper : Scalar.QComplex := ((999990791014255637991859357349 : Int)/10^30,(-4291606538734134282612233361 : Int)/10^30)
theorem v4701_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 87 91 5) 1) 14) v4701_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4701 : Material (87 : Basis) (91 : Basis) where
  plus := ![v4701_pa,v4701_pb,v4701_pg]
  minus := ![(Primitive.Addresses.material4701 1).one,v4701_mb,v4701_mg]
  upper := v4701_upper
  lower := (Primitive.Addresses.material4701 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4701_pa_checked.trans (by decide +kernel)
    · exact v4701_pb_checked.trans (by decide +kernel)
    · exact v4701_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 87 91 Primitive.Addresses.material4701
    · exact v4701_mb_checked.trans (by decide +kernel)
    · exact v4701_mg_checked.trans (by decide +kernel)
  upper_error := v4701_upper_checked
  lower_error := reuse_lower_error 87 91 Primitive.Addresses.material4701

def v4702_pa : Scalar.QComplex := ((999996626068405629330925148495 : Int)/10^30,(-2597662758197633062624619133 : Int)/10^30)
theorem v4702_pa_checked : Scalar.distance (sourceCoefficient 87 92 1 0) v4702_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4702_pb : Scalar.QComplex := ((-1120833085405928888189318 : Int)/10^30,(-431476064494779997570432740 : Int)/10^30)
theorem v4702_pb_checked : Scalar.distance (sourceCoefficient 87 92 1 1) v4702_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4702_pg : Scalar.QComplex := ((-93086115750959503877299 : Int)/10^30,(241807152032331586807 : Int)/10^30)
theorem v4702_pg_checked : Scalar.distance (sourceCoefficient 87 92 1 2) v4702_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4702_mb : Scalar.QComplex := ((-1493177078766982287007475 : Int)/10^30,(-431474936608049498784535527 : Int)/10^30)
theorem v4702_mb_checked : Scalar.distance (sourceCoefficient 87 92 3 1) v4702_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4702_mg : Scalar.QComplex := ((-93085872422062750088936 : Int)/10^30,(322136187446533181505 : Int)/10^30)
theorem v4702_mg_checked : Scalar.distance (sourceCoefficient 87 92 3 2) v4702_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4702_upper : Scalar.QComplex := ((999990653360636431254293937220 : Int)/10^30,(-4323562346892906643257238255 : Int)/10^30)
theorem v4702_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 87 92 5) 1) 14) v4702_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4702 : Material (87 : Basis) (92 : Basis) where
  plus := ![v4702_pa,v4702_pb,v4702_pg]
  minus := ![(Primitive.Addresses.material4702 1).one,v4702_mb,v4702_mg]
  upper := v4702_upper
  lower := (Primitive.Addresses.material4702 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4702_pa_checked.trans (by decide +kernel)
    · exact v4702_pb_checked.trans (by decide +kernel)
    · exact v4702_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 87 92 Primitive.Addresses.material4702
    · exact v4702_mb_checked.trans (by decide +kernel)
    · exact v4702_mg_checked.trans (by decide +kernel)
  upper_error := v4702_upper_checked
  lower_error := reuse_lower_error 87 92 Primitive.Addresses.material4702

def v4703_pa : Scalar.QComplex := ((999996526831282973135925826951 : Int)/10^30,(-2635588240061939420079755773 : Int)/10^30)
theorem v4703_pa_checked : Scalar.distance (sourceCoefficient 87 93 1 0) v4703_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4703_pb : Scalar.QComplex := ((-1137197076554497516601481 : Int)/10^30,(-431476021023094547802475641 : Int)/10^30)
theorem v4703_pb_checked : Scalar.distance (sourceCoefficient 87 93 1 1) v4703_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4703_pg : Scalar.QComplex := ((-93086106442880787691895 : Int)/10^30,(245337499552539094684 : Int)/10^30)
theorem v4703_pg_checked : Scalar.distance (sourceCoefficient 87 93 1 2) v4703_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4703_mb : Scalar.QComplex := ((-1509541026308382488348995 : Int)/10^30,(-431474879014992881099452237 : Int)/10^30)
theorem v4703_mb_checked : Scalar.distance (sourceCoefficient 87 93 3 1) v4703_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4703_mg : Scalar.QComplex := ((-93085860067456590737477 : Int)/10^30,(325666525619778250991 : Int)/10^30)
theorem v4703_mg_checked : Scalar.distance (sourceCoefficient 87 93 3 2) v4703_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4703_upper : Scalar.QComplex := ((999990488667720452141956534725 : Int)/10^30,(-4361487600997391820726732243 : Int)/10^30)
theorem v4703_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 87 93 5) 1) 14) v4703_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4703 : Material (87 : Basis) (93 : Basis) where
  plus := ![v4703_pa,v4703_pb,v4703_pg]
  minus := ![(Primitive.Addresses.material4703 1).one,v4703_mb,v4703_mg]
  upper := v4703_upper
  lower := (Primitive.Addresses.material4703 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4703_pa_checked.trans (by decide +kernel)
    · exact v4703_pb_checked.trans (by decide +kernel)
    · exact v4703_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 87 93 Primitive.Addresses.material4703
    · exact v4703_mb_checked.trans (by decide +kernel)
    · exact v4703_mg_checked.trans (by decide +kernel)
  upper_error := v4703_upper_checked
  lower_error := reuse_lower_error 87 93 Primitive.Addresses.material4703

def v4704_pa : Scalar.QComplex := ((999996407757279810689633710741 : Int)/10^30,(-2680386639306139352157251548 : Int)/10^30)
theorem v4704_pa_checked : Scalar.distance (sourceCoefficient 87 94 1 0) v4704_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4704_pb : Scalar.QComplex := ((-1156526575961077535096312 : Int)/10^30,(-431475968607382899264323963 : Int)/10^30)
theorem v4704_pb_checked : Scalar.distance (sourceCoefficient 87 94 1 1) v4704_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4704_pg : Scalar.QComplex := ((-93086095246743270611958 : Int)/10^30,(249507622296489214013 : Int)/10^30)
theorem v4704_pg_checked : Scalar.distance (sourceCoefficient 87 94 1 2) v4704_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4704_mb : Scalar.QComplex := ((-1528870473285308039340600 : Int)/10^30,(-431474809918813329783964361 : Int)/10^30)
theorem v4704_mb_checked : Scalar.distance (sourceCoefficient 87 94 3 1) v4704_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4704_mg : Scalar.QComplex := ((-93085845272695129818626 : Int)/10^30,(329836637149238666798 : Int)/10^30)
theorem v4704_mg_checked : Scalar.distance (sourceCoefficient 87 94 3 2) v4704_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4704_upper : Scalar.QComplex := ((999990292275921619979467773658 : Int)/10^30,(-4406285728008711319007951419 : Int)/10^30)
theorem v4704_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 87 94 5) 1) 14) v4704_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4704 : Material (87 : Basis) (94 : Basis) where
  plus := ![v4704_pa,v4704_pb,v4704_pg]
  minus := ![(Primitive.Addresses.material4704 1).one,v4704_mb,v4704_mg]
  upper := v4704_upper
  lower := (Primitive.Addresses.material4704 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4704_pa_checked.trans (by decide +kernel)
    · exact v4704_pb_checked.trans (by decide +kernel)
    · exact v4704_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 87 94 Primitive.Addresses.material4704
    · exact v4704_mb_checked.trans (by decide +kernel)
    · exact v4704_mg_checked.trans (by decide +kernel)
  upper_error := v4704_upper_checked
  lower_error := reuse_lower_error 87 94 Primitive.Addresses.material4704

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
