import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B072
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B073

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1745_pa : Scalar.QComplex := ((999998890143132411324170584696 : Int)/10^30,(-1489869961907778421629319994 : Int)/10^30)
theorem v1745_pa_checked : Scalar.distance (sourceCoefficient 19 93 1 0) v1745_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1745_pb : Scalar.QComplex := ((-642845221024468674599788 : Int)/10^30,(-431476923486075898849098554 : Int)/10^30)
theorem v1745_pb_checked : Scalar.distance (sourceCoefficient 19 93 1 1) v1745_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1745_pg : Scalar.QComplex := ((-93086313787138980267967 : Int)/10^30,(138686656698518641602 : Int)/10^30)
theorem v1745_pg_checked : Scalar.distance (sourceCoefficient 19 93 1 2) v1745_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1745_mb : Scalar.QComplex := ((-1015190133633049938193647 : Int)/10^30,(-431476208081024745282864011 : Int)/10^30)
theorem v1745_mb_checked : Scalar.distance (sourceCoefficient 19 93 3 1) v1745_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1745_mg : Scalar.QComplex := ((-93086159446511586937314 : Int)/10^30,(219015901405497158233 : Int)/10^30)
theorem v1745_mg_checked : Scalar.distance (sourceCoefficient 19 93 3 2) v1745_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1745_upper : Scalar.QComplex := ((999994829381859358757272080732 : Int)/10^30,(-3215775108117874763946720434 : Int)/10^30)
theorem v1745_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 93 5) 1) 14) v1745_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1745 : Material (19 : Basis) (93 : Basis) where
  plus := ![v1745_pa,v1745_pb,v1745_pg]
  minus := ![(Primitive.Addresses.material1745 1).one,v1745_mb,v1745_mg]
  upper := v1745_upper
  lower := (Primitive.Addresses.material1745 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1745_pa_checked.trans (by decide +kernel)
    · exact v1745_pb_checked.trans (by decide +kernel)
    · exact v1745_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 93 Primitive.Addresses.material1745
    · exact v1745_mb_checked.trans (by decide +kernel)
    · exact v1745_mg_checked.trans (by decide +kernel)
  upper_error := v1745_upper_checked
  lower_error := reuse_lower_error 19 93 Primitive.Addresses.material1745

def v1746_pa : Scalar.QComplex := ((999998822395653019287879266169 : Int)/10^30,(-1534668468174617254717630448 : Int)/10^30)
theorem v1746_pa_checked : Scalar.distance (sourceCoefficient 19 94 1 0) v1746_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1746_pb : Scalar.QComplex := ((-662174751216288692423344 : Int)/10^30,(-431476885834524026965055279 : Int)/10^30)
theorem v1746_pb_checked : Scalar.distance (sourceCoefficient 19 94 1 1) v1746_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1746_pg : Scalar.QComplex := ((-93086306572503686532316 : Int)/10^30,(142856787744431282384 : Int)/10^30)
theorem v1746_pg_checked : Scalar.distance (sourceCoefficient 19 94 1 2) v1746_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1746_mb : Scalar.QComplex := ((-1034519624136008959942542 : Int)/10^30,(-431476153748972906974440571 : Int)/10^30)
theorem v1746_mb_checked : Scalar.distance (sourceCoefficient 19 94 3 1) v1746_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1746_mg : Scalar.QComplex := ((-93086148633243702647759 : Int)/10^30,(223186024672774102834 : Int)/10^30)
theorem v1746_mg_checked : Scalar.distance (sourceCoefficient 19 94 3 2) v1746_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1746_upper : Scalar.QComplex := ((999994684316323140811139918270 : Int)/10^30,(-3260573430736597487454148608 : Int)/10^30)
theorem v1746_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 94 5) 1) 14) v1746_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1746 : Material (19 : Basis) (94 : Basis) where
  plus := ![v1746_pa,v1746_pb,v1746_pg]
  minus := ![(Primitive.Addresses.material1746 1).one,v1746_mb,v1746_mg]
  upper := v1746_upper
  lower := (Primitive.Addresses.material1746 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1746_pa_checked.trans (by decide +kernel)
    · exact v1746_pb_checked.trans (by decide +kernel)
    · exact v1746_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 94 Primitive.Addresses.material1746
    · exact v1746_mb_checked.trans (by decide +kernel)
    · exact v1746_mg_checked.trans (by decide +kernel)
  upper_error := v1746_upper_checked
  lower_error := reuse_lower_error 19 94 Primitive.Addresses.material1746

def v1747_pa : Scalar.QComplex := ((999998753469295729474581699074 : Int)/10^30,(-1578942638192488026088983370 : Int)/10^30)
theorem v1747_pa_checked : Scalar.distance (sourceCoefficient 19 95 1 0) v1747_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1747_pb : Scalar.QComplex := ((-681278041127677748433712 : Int)/10^30,(-431476847489267188203755778 : Int)/10^30)
theorem v1747_pb_checked : Scalar.distance (sourceCoefficient 19 95 1 1) v1747_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1747_pg : Scalar.QComplex := ((-93086299228170092452710 : Int)/10^30,(146978110095629337540 : Int)/10^30)
theorem v1747_pg_checked : Scalar.distance (sourceCoefficient 19 95 1 2) v1747_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1747_mb : Scalar.QComplex := ((-1053622873844140472871134 : Int)/10^30,(-431476098918451532614764817 : Int)/10^30)
theorem v1747_mb_checked : Scalar.distance (sourceCoefficient 19 95 3 1) v1747_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1747_mg : Scalar.QComplex := ((-93086137732397271583536 : Int)/10^30,(227307339151586377719 : Int)/10^30)
theorem v1747_mg_checked : Scalar.distance (sourceCoefficient 19 95 3 2) v1747_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1747_upper : Scalar.QComplex := ((999994538976867579194093899693 : Int)/10^30,(-3304847415852653094624430464 : Int)/10^30)
theorem v1747_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 95 5) 1) 14) v1747_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1747 : Material (19 : Basis) (95 : Basis) where
  plus := ![v1747_pa,v1747_pb,v1747_pg]
  minus := ![(Primitive.Addresses.material1747 1).one,v1747_mb,v1747_mg]
  upper := v1747_upper
  lower := (Primitive.Addresses.material1747 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1747_pa_checked.trans (by decide +kernel)
    · exact v1747_pb_checked.trans (by decide +kernel)
    · exact v1747_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 95 Primitive.Addresses.material1747
    · exact v1747_mb_checked.trans (by decide +kernel)
    · exact v1747_mg_checked.trans (by decide +kernel)
  upper_error := v1747_upper_checked
  lower_error := reuse_lower_error 19 95 Primitive.Addresses.material1747

def v1748_pa : Scalar.QComplex := ((999998719668426249056772240393 : Int)/10^30,(-1600206707976487552616759866 : Int)/10^30)
theorem v1748_pa_checked : Scalar.distance (sourceCoefficient 19 96 1 0) v1748_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1748_pb : Scalar.QComplex := ((-690452999585924134910928 : Int)/10^30,(-431476828671870340788849202 : Int)/10^30)
theorem v1748_pb_checked : Scalar.distance (sourceCoefficient 19 96 1 1) v1748_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1748_pg : Scalar.QComplex := ((-93086295625147903542607 : Int)/10^30,(148957505395041346561 : Int)/10^30)
theorem v1748_pg_checked : Scalar.distance (sourceCoefficient 19 96 1 2) v1748_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1748_mb : Scalar.QComplex := ((-1062797812647564533801145 : Int)/10^30,(-431476072183485767099404717 : Int)/10^30)
theorem v1748_mb_checked : Scalar.distance (sourceCoefficient 19 96 3 1) v1748_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1748_mg : Scalar.QComplex := ((-93086132421247429505628 : Int)/10^30,(229286730604733179000 : Int)/10^30)
theorem v1748_mg_checked : Scalar.distance (sourceCoefficient 19 96 3 2) v1748_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1748_upper : Scalar.QComplex := ((999994468476193055359467890136 : Int)/10^30,(-3326111395629084198711144043 : Int)/10^30)
theorem v1748_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 96 5) 1) 14) v1748_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1748 : Material (19 : Basis) (96 : Basis) where
  plus := ![v1748_pa,v1748_pb,v1748_pg]
  minus := ![(Primitive.Addresses.material1748 1).one,v1748_mb,v1748_mg]
  upper := v1748_upper
  lower := (Primitive.Addresses.material1748 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1748_pa_checked.trans (by decide +kernel)
    · exact v1748_pb_checked.trans (by decide +kernel)
    · exact v1748_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 96 Primitive.Addresses.material1748
    · exact v1748_mb_checked.trans (by decide +kernel)
    · exact v1748_mg_checked.trans (by decide +kernel)
  upper_error := v1748_upper_checked
  lower_error := reuse_lower_error 19 96 Primitive.Addresses.material1748

def v1749_pa : Scalar.QComplex := ((999998599917393822720506556136 : Int)/10^30,(-1673368833259199574101735594 : Int)/10^30)
theorem v1749_pa_checked : Scalar.distance (sourceCoefficient 19 97 1 0) v1749_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1749_pb : Scalar.QComplex := ((-722020776595823014591302 : Int)/10^30,(-431476761940655680443353507 : Int)/10^30)
theorem v1749_pb_checked : Scalar.distance (sourceCoefficient 19 97 1 1) v1749_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1749_pg : Scalar.QComplex := ((-93086282853294661340395 : Int)/10^30,(155767902618584579519 : Int)/10^30)
theorem v1749_pg_checked : Scalar.distance (sourceCoefficient 19 97 1 2) v1749_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1749_mb : Scalar.QComplex := ((-1094365520317304524477197 : Int)/10^30,(-431475978210726154190478634 : Int)/10^30)
theorem v1749_mb_checked : Scalar.distance (sourceCoefficient 19 97 3 1) v1749_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1749_mg : Scalar.QComplex := ((-93086113772332867834906 : Int)/10^30,(236097114270920150001 : Int)/10^30)
theorem v1749_mg_checked : Scalar.distance (sourceCoefficient 19 97 3 2) v1749_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1749_upper : Scalar.QComplex := ((999994222454147962316668021590 : Int)/10^30,(-3399273205265986599486317253 : Int)/10^30)
theorem v1749_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 97 5) 1) 14) v1749_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1749 : Material (19 : Basis) (97 : Basis) where
  plus := ![v1749_pa,v1749_pb,v1749_pg]
  minus := ![(Primitive.Addresses.material1749 1).one,v1749_mb,v1749_mg]
  upper := v1749_upper
  lower := (Primitive.Addresses.material1749 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1749_pa_checked.trans (by decide +kernel)
    · exact v1749_pb_checked.trans (by decide +kernel)
    · exact v1749_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 97 Primitive.Addresses.material1749
    · exact v1749_mb_checked.trans (by decide +kernel)
    · exact v1749_mg_checked.trans (by decide +kernel)
  upper_error := v1749_upper_checked
  lower_error := reuse_lower_error 19 97 Primitive.Addresses.material1749

def v1750_pa : Scalar.QComplex := ((999999965132298627314483378584 : Int)/10^30,(-264074613565208941361952432 : Int)/10^30)
theorem v1750_pa_checked : Scalar.distance (sourceCoefficient 20 21 1 0) v1750_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1750_pb : Scalar.QComplex := ((-113942259566959950710992 : Int)/10^30,(-431477505753952676066311403 : Int)/10^30)
theorem v1750_pb_checked : Scalar.distance (sourceCoefficient 20 21 1 1) v1750_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1750_pg : Scalar.QComplex := ((-93086426629468974560378 : Int)/10^30,(24581762997452765912 : Int)/10^30)
theorem v1750_pg_checked : Scalar.distance (sourceCoefficient 20 21 1 2) v1750_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1750_mb : Scalar.QComplex := ((-486287871581239111460766 : Int)/10^30,(-431477246768119550278141991 : Int)/10^30)
theorem v1750_mb_checked : Scalar.distance (sourceCoefficient 20 21 3 1) v1750_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1750_mg : Scalar.QComplex := ((-93086370756183735252797 : Int)/10^30,(104911147568746613903 : Int)/10^30)
theorem v1750_mg_checked : Scalar.distance (sourceCoefficient 20 21 3 2) v1750_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1750_upper : Scalar.QComplex := ((999998019980992458607282789933 : Int)/10^30,(-1989983440787263236873609714 : Int)/10^30)
theorem v1750_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 21 5) 1) 14) v1750_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1750 : Material (20 : Basis) (21 : Basis) where
  plus := ![v1750_pa,v1750_pb,v1750_pg]
  minus := ![(Primitive.Addresses.material1750 1).one,v1750_mb,v1750_mg]
  upper := v1750_upper
  lower := (Primitive.Addresses.material1750 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1750_pa_checked.trans (by decide +kernel)
    · exact v1750_pb_checked.trans (by decide +kernel)
    · exact v1750_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 21 Primitive.Addresses.material1750
    · exact v1750_mb_checked.trans (by decide +kernel)
    · exact v1750_mg_checked.trans (by decide +kernel)
  upper_error := v1750_upper_checked
  lower_error := reuse_lower_error 20 21 Primitive.Addresses.material1750

def v1751_pa : Scalar.QComplex := ((999999964763180959112381974470 : Int)/10^30,(-265468711602971810427829182 : Int)/10^30)
theorem v1751_pa_checked : Scalar.distance (sourceCoefficient 20 22 1 0) v1751_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1751_pb : Scalar.QComplex := ((-114543781529185362578592 : Int)/10^30,(-431477505583918279073208162 : Int)/10^30)
theorem v1751_pb_checked : Scalar.distance (sourceCoefficient 20 22 1 1) v1751_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1751_pg : Scalar.QComplex := ((-93086426593947545720135 : Int)/10^30,(24711534606375739681 : Int)/10^30)
theorem v1751_pg_checked : Scalar.distance (sourceCoefficient 20 22 1 2) v1751_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1751_mb : Scalar.QComplex := ((-486889393172758379340005 : Int)/10^30,(-431477246078998854739578529 : Int)/10^30)
theorem v1751_mb_checked : Scalar.distance (sourceCoefficient 20 22 3 1) v1751_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1751_mg : Scalar.QComplex := ((-93086370608675265834579 : Int)/10^30,(105040919098696293551 : Int)/10^30)
theorem v1751_mg_checked : Scalar.distance (sourceCoefficient 20 22 3 2) v1751_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1751_upper : Scalar.QComplex := ((999998017205788598569920591955 : Int)/10^30,(-1991377536111617231727333163 : Int)/10^30)
theorem v1751_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 22 5) 1) 14) v1751_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1751 : Material (20 : Basis) (22 : Basis) where
  plus := ![v1751_pa,v1751_pb,v1751_pg]
  minus := ![(Primitive.Addresses.material1751 1).one,v1751_mb,v1751_mg]
  upper := v1751_upper
  lower := (Primitive.Addresses.material1751 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1751_pa_checked.trans (by decide +kernel)
    · exact v1751_pb_checked.trans (by decide +kernel)
    · exact v1751_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 22 Primitive.Addresses.material1751
    · exact v1751_mb_checked.trans (by decide +kernel)
    · exact v1751_mg_checked.trans (by decide +kernel)
  upper_error := v1751_upper_checked
  lower_error := reuse_lower_error 20 22 Primitive.Addresses.material1751

def v1752_pa : Scalar.QComplex := ((999999961973396068627445827584 : Int)/10^30,(-275777458137394728202324501 : Int)/10^30)
theorem v1752_pa_checked : Scalar.distance (sourceCoefficient 20 23 1 0) v1752_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1752_pb : Scalar.QComplex := ((-118991773901936022443710 : Int)/10^30,(-431477504291885346030548428 : Int)/10^30)
theorem v1752_pb_checked : Scalar.distance (sourceCoefficient 20 23 1 1) v1752_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1752_pg : Scalar.QComplex := ((-93086426324731189752906 : Int)/10^30,(25671139015114470083 : Int)/10^30)
theorem v1752_pg_checked : Scalar.distance (sourceCoefficient 20 23 1 2) v1752_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1752_mb : Scalar.QComplex := ((-491337382774351965323557 : Int)/10^30,(-431477240948549315235873463 : Int)/10^30)
theorem v1752_mb_checked : Scalar.distance (sourceCoefficient 20 23 3 1) v1752_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1752_mg : Scalar.QComplex := ((-93086369511363624345585 : Int)/10^30,(106000522917808856346 : Int)/10^30)
theorem v1752_mg_checked : Scalar.distance (sourceCoefficient 20 23 3 2) v1752_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1752_upper : Scalar.QComplex := ((999997996624046546908115913775 : Int)/10^30,(-2001686262477457503242709556 : Int)/10^30)
theorem v1752_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 23 5) 1) 14) v1752_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1752 : Material (20 : Basis) (23 : Basis) where
  plus := ![v1752_pa,v1752_pb,v1752_pg]
  minus := ![(Primitive.Addresses.material1752 1).one,v1752_mb,v1752_mg]
  upper := v1752_upper
  lower := (Primitive.Addresses.material1752 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1752_pa_checked.trans (by decide +kernel)
    · exact v1752_pb_checked.trans (by decide +kernel)
    · exact v1752_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 23 Primitive.Addresses.material1752
    · exact v1752_mb_checked.trans (by decide +kernel)
    · exact v1752_mg_checked.trans (by decide +kernel)
  upper_error := v1752_upper_checked
  lower_error := reuse_lower_error 20 23 Primitive.Addresses.material1752

def v1753_pa : Scalar.QComplex := ((999999946625898006837654028275 : Int)/10^30,(-326723432183138539529991832 : Int)/10^30)
theorem v1753_pa_checked : Scalar.distance (sourceCoefficient 20 24 1 0) v1753_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1753_pb : Scalar.QComplex := ((-140973816256911620237935 : Int)/10^30,(-431477497008970615654915979 : Int)/10^30)
theorem v1753_pb_checked : Scalar.distance (sourceCoefficient 20 24 1 1) v1753_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1753_pg : Scalar.QComplex := ((-93086424824805754239270 : Int)/10^30,(30413517831712449372 : Int)/10^30)
theorem v1753_pg_checked : Scalar.distance (sourceCoefficient 20 24 1 2) v1753_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1753_mb : Scalar.QComplex := ((-513319410659581163384037 : Int)/10^30,(-431477214696124778714162191 : Int)/10^30)
theorem v1753_mb_checked : Scalar.distance (sourceCoefficient 20 24 3 1) v1753_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1753_mg : Scalar.QComplex := ((-93086363918979417411793 : Int)/10^30,(110742898674234368082 : Int)/10^30)
theorem v1753_mg_checked : Scalar.distance (sourceCoefficient 20 24 3 2) v1753_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1753_upper : Scalar.QComplex := ((999997893348441923122070051949 : Int)/10^30,(-2052632134156768167435826688 : Int)/10^30)
theorem v1753_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 24 5) 1) 14) v1753_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1753 : Material (20 : Basis) (24 : Basis) where
  plus := ![v1753_pa,v1753_pb,v1753_pg]
  minus := ![(Primitive.Addresses.material1753 1).one,v1753_mb,v1753_mg]
  upper := v1753_upper
  lower := (Primitive.Addresses.material1753 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1753_pa_checked.trans (by decide +kernel)
    · exact v1753_pb_checked.trans (by decide +kernel)
    · exact v1753_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 24 Primitive.Addresses.material1753
    · exact v1753_mb_checked.trans (by decide +kernel)
    · exact v1753_mg_checked.trans (by decide +kernel)
  upper_error := v1753_upper_checked
  lower_error := reuse_lower_error 20 24 Primitive.Addresses.material1753

def v1754_pa : Scalar.QComplex := ((999999938852235938634386898496 : Int)/10^30,(-349707769978995714762258258 : Int)/10^30)
theorem v1754_pa_checked : Scalar.distance (sourceCoefficient 20 25 1 0) v1754_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1754_pb : Scalar.QComplex := ((-150891041181809004480375 : Int)/10^30,(-431477493234485741231539442 : Int)/10^30)
theorem v1754_pb_checked : Scalar.distance (sourceCoefficient 20 25 1 1) v1754_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1754_pg : Scalar.QComplex := ((-93086424055843166941602 : Int)/10^30,(32553047762434139634 : Int)/10^30)
theorem v1754_pg_checked : Scalar.distance (sourceCoefficient 20 25 1 2) v1754_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1754_mb : Scalar.QComplex := ((-523236628634632018378428 : Int)/10^30,(-431477202363522854747560143 : Int)/10^30)
theorem v1754_mb_checked : Scalar.distance (sourceCoefficient 20 25 3 1) v1754_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1754_mg : Scalar.QComplex := ((-93086361303699147072217 : Int)/10^30,(112882427144731203740 : Int)/10^30)
theorem v1754_mg_checked : Scalar.distance (sourceCoefficient 20 25 3 2) v1754_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1754_upper : Scalar.QComplex := ((999997845905909520062564993780 : Int)/10^30,(-2075616424303518617111171878 : Int)/10^30)
theorem v1754_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 25 5) 1) 14) v1754_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1754 : Material (20 : Basis) (25 : Basis) where
  plus := ![v1754_pa,v1754_pb,v1754_pg]
  minus := ![(Primitive.Addresses.material1754 1).one,v1754_mb,v1754_mg]
  upper := v1754_upper
  lower := (Primitive.Addresses.material1754 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1754_pa_checked.trans (by decide +kernel)
    · exact v1754_pb_checked.trans (by decide +kernel)
    · exact v1754_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 25 Primitive.Addresses.material1754
    · exact v1754_mb_checked.trans (by decide +kernel)
    · exact v1754_mg_checked.trans (by decide +kernel)
  upper_error := v1754_upper_checked
  lower_error := reuse_lower_error 20 25 Primitive.Addresses.material1754

def v1755_pa : Scalar.QComplex := ((999999936257039592572044340898 : Int)/10^30,(-357051700390420924564773760 : Int)/10^30)
theorem v1755_pa_checked : Scalar.distance (sourceCoefficient 20 26 1 0) v1755_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1755_pb : Scalar.QComplex := ((-154059782006309136355787 : Int)/10^30,(-431477491964398181577097744 : Int)/10^30)
theorem v1755_pb_checked : Scalar.distance (sourceCoefficient 20 26 1 1) v1755_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1755_pg : Scalar.QComplex := ((-93086423798050821413322 : Int)/10^30,(33236668018961003723 : Int)/10^30)
theorem v1755_pg_checked : Scalar.distance (sourceCoefficient 20 26 1 2) v1755_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1755_mb : Scalar.QComplex := ((-526405367183236761321019 : Int)/10^30,(-431477198358955151250062459 : Int)/10^30)
theorem v1755_mb_checked : Scalar.distance (sourceCoefficient 20 26 3 1) v1755_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1755_mg : Scalar.QComplex := ((-93086360455973405262534 : Int)/10^30,(113566046924251819680 : Int)/10^30)
theorem v1755_mg_checked : Scalar.distance (sourceCoefficient 20 26 3 2) v1755_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1755_upper : Scalar.QComplex := ((999997830635759385282987798761 : Int)/10^30,(-2082960339297948698831633587 : Int)/10^30)
theorem v1755_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 26 5) 1) 14) v1755_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1755 : Material (20 : Basis) (26 : Basis) where
  plus := ![v1755_pa,v1755_pb,v1755_pg]
  minus := ![(Primitive.Addresses.material1755 1).one,v1755_mb,v1755_mg]
  upper := v1755_upper
  lower := (Primitive.Addresses.material1755 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1755_pa_checked.trans (by decide +kernel)
    · exact v1755_pb_checked.trans (by decide +kernel)
    · exact v1755_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 26 Primitive.Addresses.material1755
    · exact v1755_mb_checked.trans (by decide +kernel)
    · exact v1755_mg_checked.trans (by decide +kernel)
  upper_error := v1755_upper_checked
  lower_error := reuse_lower_error 20 26 Primitive.Addresses.material1755

def v1756_pa : Scalar.QComplex := ((999999934442903209920737841694 : Int)/10^30,(-362096933544631919702241165 : Int)/10^30)
theorem v1756_pa_checked : Scalar.distance (sourceCoefficient 20 27 1 0) v1756_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1756_pb : Scalar.QComplex := ((-156236686653805430699088 : Int)/10^30,(-431477491073876141619815494 : Int)/10^30)
theorem v1756_pb_checked : Scalar.distance (sourceCoefficient 20 27 1 1) v1756_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1756_pg : Scalar.QComplex := ((-93086423617555016889121 : Int)/10^30,(33706310756241150851 : Int)/10^30)
theorem v1756_pg_checked : Scalar.distance (sourceCoefficient 20 27 1 2) v1756_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1756_mb : Scalar.QComplex := ((-528582270251691553084860 : Int)/10^30,(-431477195589862776231285999 : Int)/10^30)
theorem v1756_mb_checked : Scalar.distance (sourceCoefficient 20 27 3 1) v1756_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1756_mg : Scalar.QComplex := ((-93086359870197137596093 : Int)/10^30,(114035689330902761910 : Int)/10^30)
theorem v1756_mg_checked : Scalar.distance (sourceCoefficient 20 27 3 2) v1756_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1756_upper : Scalar.QComplex := ((999997820114010980382936237878 : Int)/10^30,(-2088005561806842746200713475 : Int)/10^30)
theorem v1756_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 27 5) 1) 14) v1756_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1756 : Material (20 : Basis) (27 : Basis) where
  plus := ![v1756_pa,v1756_pb,v1756_pg]
  minus := ![(Primitive.Addresses.material1756 1).one,v1756_mb,v1756_mg]
  upper := v1756_upper
  lower := (Primitive.Addresses.material1756 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1756_pa_checked.trans (by decide +kernel)
    · exact v1756_pb_checked.trans (by decide +kernel)
    · exact v1756_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 27 Primitive.Addresses.material1756
    · exact v1756_mb_checked.trans (by decide +kernel)
    · exact v1756_mg_checked.trans (by decide +kernel)
  upper_error := v1756_upper_checked
  lower_error := reuse_lower_error 20 27 Primitive.Addresses.material1756

def v1757_pa : Scalar.QComplex := ((999999931958784005617332699351 : Int)/10^30,(-368893517643178789169915472 : Int)/10^30)
theorem v1757_pa_checked : Scalar.distance (sourceCoefficient 20 28 1 0) v1757_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1757_pb : Scalar.QComplex := ((-159169259845082390048181 : Int)/10^30,(-431477489851075999761796809 : Int)/10^30)
theorem v1757_pb_checked : Scalar.distance (sourceCoefficient 20 28 1 1) v1757_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1757_pg : Scalar.QComplex := ((-93086423370033423332977 : Int)/10^30,(34338980498259824121 : Int)/10^30)
theorem v1757_pg_checked : Scalar.distance (sourceCoefficient 20 28 1 2) v1757_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1757_mb : Scalar.QComplex := ((-531514841295816038556238 : Int)/10^30,(-431477191836384503799191039 : Int)/10^30)
theorem v1757_mb_checked : Scalar.distance (sourceCoefficient 20 28 3 1) v1757_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1757_mg : Scalar.QComplex := ((-93086359076710143228856 : Int)/10^30,(114668358623749588511 : Int)/10^30)
theorem v1757_mg_checked : Scalar.distance (sourceCoefficient 20 28 3 2) v1757_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1757_upper : Scalar.QComplex := ((999997805899607903084335495838 : Int)/10^30,(-2094802131495311594640518161 : Int)/10^30)
theorem v1757_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 28 5) 1) 14) v1757_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1757 : Material (20 : Basis) (28 : Basis) where
  plus := ![v1757_pa,v1757_pb,v1757_pg]
  minus := ![(Primitive.Addresses.material1757 1).one,v1757_mb,v1757_mg]
  upper := v1757_upper
  lower := (Primitive.Addresses.material1757 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1757_pa_checked.trans (by decide +kernel)
    · exact v1757_pb_checked.trans (by decide +kernel)
    · exact v1757_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 28 Primitive.Addresses.material1757
    · exact v1757_mb_checked.trans (by decide +kernel)
    · exact v1757_mg_checked.trans (by decide +kernel)
  upper_error := v1757_upper_checked
  lower_error := reuse_lower_error 20 28 Primitive.Addresses.material1757

def v1758_pa : Scalar.QComplex := ((999999926786090459726354419878 : Int)/10^30,(-382658873829251137345524628 : Int)/10^30)
theorem v1758_pa_checked : Scalar.distance (sourceCoefficient 20 29 1 0) v1758_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1758_pb : Scalar.QComplex := ((-165108701458498181749077 : Int)/10^30,(-431477487293079054716623733 : Int)/10^30)
theorem v1758_pb_checked : Scalar.distance (sourceCoefficient 20 29 1 1) v1758_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1758_pg : Scalar.QComplex := ((-93086422853350078073008 : Int)/10^30,(35620348345761368752 : Int)/10^30)
theorem v1758_pg_checked : Scalar.distance (sourceCoefficient 20 29 1 2) v1758_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1758_mb : Scalar.QComplex := ((-537454278490270116022704 : Int)/10^30,(-431477184152917901355466531 : Int)/10^30)
theorem v1758_mb_checked : Scalar.distance (sourceCoefficient 20 29 3 1) v1758_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1758_mg : Scalar.QComplex := ((-93086357454264248625407 : Int)/10^30,(115949725548264865708 : Int)/10^30)
theorem v1758_mg_checked : Scalar.distance (sourceCoefficient 20 29 3 2) v1758_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1758_upper : Scalar.QComplex := ((999997776969166067510133827868 : Int)/10^30,(-2108567458251903098871468981 : Int)/10^30)
theorem v1758_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 29 5) 1) 14) v1758_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1758 : Material (20 : Basis) (29 : Basis) where
  plus := ![v1758_pa,v1758_pb,v1758_pg]
  minus := ![(Primitive.Addresses.material1758 1).one,v1758_mb,v1758_mg]
  upper := v1758_upper
  lower := (Primitive.Addresses.material1758 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1758_pa_checked.trans (by decide +kernel)
    · exact v1758_pb_checked.trans (by decide +kernel)
    · exact v1758_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 29 Primitive.Addresses.material1758
    · exact v1758_mb_checked.trans (by decide +kernel)
    · exact v1758_mg_checked.trans (by decide +kernel)
  upper_error := v1758_upper_checked
  lower_error := reuse_lower_error 20 29 Primitive.Addresses.material1758

def v1759_pa : Scalar.QComplex := ((999999924776423010329330425681 : Int)/10^30,(-387875171054754166031330587 : Int)/10^30)
theorem v1759_pa_checked : Scalar.distance (sourceCoefficient 20 30 1 0) v1759_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1759_pb : Scalar.QComplex := ((-167359416392423372446358 : Int)/10^30,(-431477486295260282543723295 : Int)/10^30)
theorem v1759_pb_checked : Scalar.distance (sourceCoefficient 20 30 1 1) v1759_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1759_pg : Scalar.QComplex := ((-93086422652179596551803 : Int)/10^30,(36105914825105367605 : Int)/10^30)
theorem v1759_pg_checked : Scalar.distance (sourceCoefficient 20 30 1 2) v1759_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1759_mb : Scalar.QComplex := ((-539704991725078613769664 : Int)/10^30,(-431477181212833881176308677 : Int)/10^30)
theorem v1759_mb_checked : Scalar.distance (sourceCoefficient 20 30 3 1) v1759_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1759_mg : Scalar.QComplex := ((-93086356834071839437706 : Int)/10^30,(116435291673209207646 : Int)/10^30)
theorem v1759_mg_checked : Scalar.distance (sourceCoefficient 20 30 3 2) v1759_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1759_upper : Scalar.QComplex := ((999997765956645818846191404688 : Int)/10^30,(-2113783744239840457433487579 : Int)/10^30)
theorem v1759_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 30 5) 1) 14) v1759_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1759 : Material (20 : Basis) (30 : Basis) where
  plus := ![v1759_pa,v1759_pb,v1759_pg]
  minus := ![(Primitive.Addresses.material1759 1).one,v1759_mb,v1759_mg]
  upper := v1759_upper
  lower := (Primitive.Addresses.material1759 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1759_pa_checked.trans (by decide +kernel)
    · exact v1759_pb_checked.trans (by decide +kernel)
    · exact v1759_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 30 Primitive.Addresses.material1759
    · exact v1759_mb_checked.trans (by decide +kernel)
    · exact v1759_mg_checked.trans (by decide +kernel)
  upper_error := v1759_upper_checked
  lower_error := reuse_lower_error 20 30 Primitive.Addresses.material1759

def v1760_pa : Scalar.QComplex := ((999999920411370755864266672142 : Int)/10^30,(-398970239684517774553421328 : Int)/10^30)
theorem v1760_pa_checked : Scalar.distance (sourceCoefficient 20 31 1 0) v1760_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1760_pb : Scalar.QComplex := ((-172146688959083619753460 : Int)/10^30,(-431477484120840926641379726 : Int)/10^30)
theorem v1760_pb_checked : Scalar.distance (sourceCoefficient 20 31 1 1) v1760_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1760_pg : Scalar.QComplex := ((-93086422214462752226214 : Int)/10^30,(37138715138097853817 : Int)/10^30)
theorem v1760_pg_checked : Scalar.distance (sourceCoefficient 20 31 1 2) v1760_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1760_mb : Scalar.QComplex := ((-544492260632792523413109 : Int)/10^30,(-431477174907214720634428776 : Int)/10^30)
theorem v1760_mb_checked : Scalar.distance (sourceCoefficient 20 31 3 1) v1760_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1760_mg : Scalar.QComplex := ((-93086355505095003580944 : Int)/10^30,(117468091223913013407 : Int)/10^30)
theorem v1760_mg_checked : Scalar.distance (sourceCoefficient 20 31 3 2) v1760_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1760_upper : Scalar.QComplex := ((999997742442518147405175757962 : Int)/10^30,(-2124878788811118463477539770 : Int)/10^30)
theorem v1760_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 31 5) 1) 14) v1760_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1760 : Material (20 : Basis) (31 : Basis) where
  plus := ![v1760_pa,v1760_pb,v1760_pg]
  minus := ![(Primitive.Addresses.material1760 1).one,v1760_mb,v1760_mg]
  upper := v1760_upper
  lower := (Primitive.Addresses.material1760 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1760_pa_checked.trans (by decide +kernel)
    · exact v1760_pb_checked.trans (by decide +kernel)
    · exact v1760_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 31 Primitive.Addresses.material1760
    · exact v1760_mb_checked.trans (by decide +kernel)
    · exact v1760_mg_checked.trans (by decide +kernel)
  upper_error := v1760_upper_checked
  lower_error := reuse_lower_error 20 31 Primitive.Addresses.material1760

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
