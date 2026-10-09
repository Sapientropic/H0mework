import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B021
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B022

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v513_pa : Scalar.QComplex := ((999993712248116048175308635241 : Int)/10^30,(3546190100950581476456272481 : Int)/10^30)
theorem v513_pa_checked : Scalar.distance (sourceCoefficient 5 44 1 0) v513_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v513_pb : Scalar.QComplex := ((1530096031527857157536780 : Int)/10^30,(-431473318436454308231128272 : Int)/10^30)
theorem v513_pb_checked : Scalar.distance (sourceCoefficient 5 44 1 1) v513_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v513_pg : Scalar.QComplex := ((-93085683916717961148009 : Int)/10^30,(-330101606442677790641 : Int)/10^30)
theorem v513_pg_checked : Scalar.distance (sourceCoefficient 5 44 1 2) v513_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v513_mb : Scalar.QComplex := ((1157753420829397272573885 : Int)/10^30,(-431474478183180790983519825 : Int)/10^30)
theorem v513_mb_checked : Scalar.distance (sourceCoefficient 5 44 3 1) v513_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v513_mg : Scalar.QComplex := ((-93085934119482748609963 : Int)/10^30,(-249772730734209253336 : Int)/10^30)
theorem v513_mg_checked : Scalar.distance (sourceCoefficient 5 44 3 2) v513_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v513_upper : Scalar.QComplex := ((999998343277355555479082621969 : Int)/10^30,(1820286390697661953903543133 : Int)/10^30)
theorem v513_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 44 5) 1) 14) v513_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material513 : Material (5 : Basis) (44 : Basis) where
  plus := ![v513_pa,v513_pb,v513_pg]
  minus := ![(Primitive.Addresses.material513 1).one,v513_mb,v513_mg]
  upper := v513_upper
  lower := (Primitive.Addresses.material513 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v513_pa_checked.trans (by decide +kernel)
    · exact v513_pb_checked.trans (by decide +kernel)
    · exact v513_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 44 Primitive.Addresses.material513
    · exact v513_mb_checked.trans (by decide +kernel)
    · exact v513_mg_checked.trans (by decide +kernel)
  upper_error := v513_upper_checked
  lower_error := reuse_lower_error 5 44 Primitive.Addresses.material513

def v514_pa : Scalar.QComplex := ((999993722575071098052390334200 : Int)/10^30,(3543276795812056964074995512 : Int)/10^30)
theorem v514_pa_checked : Scalar.distance (sourceCoefficient 5 45 1 0) v514_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v514_pb : Scalar.QComplex := ((1528839003429116125072924 : Int)/10^30,(-431473320984696823949652933 : Int)/10^30)
theorem v514_pb_checked : Scalar.distance (sourceCoefficient 5 45 1 1) v514_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v514_pg : Scalar.QComplex := ((-93085684672244863240177 : Int)/10^30,(-329830417007125313624 : Int)/10^30)
theorem v514_pg_checked : Scalar.distance (sourceCoefficient 5 45 1 2) v514_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v514_mb : Scalar.QComplex := ((1156496390999686727810878 : Int)/10^30,(-431474479646663723105324781 : Int)/10^30)
theorem v514_mb_checked : Scalar.distance (sourceCoefficient 5 45 3 1) v514_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v514_mg : Scalar.QComplex := ((-93085934640985100421924 : Int)/10^30,(-249501540747647308308 : Int)/10^30)
theorem v514_mg_checked : Scalar.distance (sourceCoefficient 5 45 3 2) v514_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v514_upper : Scalar.QComplex := ((999998348576194848454022015361 : Int)/10^30,(1817373072074775662449231586 : Int)/10^30)
theorem v514_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 45 5) 1) 14) v514_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material514 : Material (5 : Basis) (45 : Basis) where
  plus := ![v514_pa,v514_pb,v514_pg]
  minus := ![(Primitive.Addresses.material514 1).one,v514_mb,v514_mg]
  upper := v514_upper
  lower := (Primitive.Addresses.material514 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v514_pa_checked.trans (by decide +kernel)
    · exact v514_pb_checked.trans (by decide +kernel)
    · exact v514_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 45 Primitive.Addresses.material514
    · exact v514_mb_checked.trans (by decide +kernel)
    · exact v514_mg_checked.trans (by decide +kernel)
  upper_error := v514_upper_checked
  lower_error := reuse_lower_error 5 45 Primitive.Addresses.material514

def v515_pa : Scalar.QComplex := ((999993780424221049363641011506 : Int)/10^30,(3526912654826938382676223177 : Int)/10^30)
theorem v515_pa_checked : Scalar.distance (sourceCoefficient 5 46 1 0) v515_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v515_pb : Scalar.QComplex := ((1521778230978828636797190 : Int)/10^30,(-431473335207524094398292307 : Int)/10^30)
theorem v515_pb_checked : Scalar.distance (sourceCoefficient 5 46 1 1) v515_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v515_pg : Scalar.QComplex := ((-93085688898937125640638 : Int)/10^30,(-328307136092056499406 : Int)/10^30)
theorem v515_pg_checked : Scalar.distance (sourceCoefficient 5 46 1 2) v515_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v515_mb : Scalar.QComplex := ((1149435608904788153983446 : Int)/10^30,(-431474487776357078533499783 : Int)/10^30)
theorem v515_mb_checked : Scalar.distance (sourceCoefficient 5 46 3 1) v515_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v515_mg : Scalar.QComplex := ((-93085937553152965352938 : Int)/10^30,(-247978256752320536848 : Int)/10^30)
theorem v515_mg_checked : Scalar.distance (sourceCoefficient 5 46 3 2) v515_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v515_upper : Scalar.QComplex := ((999998378182235843210741535387 : Int)/10^30,(1801008855619738029277553372 : Int)/10^30)
theorem v515_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 46 5) 1) 14) v515_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material515 : Material (5 : Basis) (46 : Basis) where
  plus := ![v515_pa,v515_pb,v515_pg]
  minus := ![(Primitive.Addresses.material515 1).one,v515_mb,v515_mg]
  upper := v515_upper
  lower := (Primitive.Addresses.material515 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v515_pa_checked.trans (by decide +kernel)
    · exact v515_pb_checked.trans (by decide +kernel)
    · exact v515_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 46 Primitive.Addresses.material515
    · exact v515_mb_checked.trans (by decide +kernel)
    · exact v515_mg_checked.trans (by decide +kernel)
  upper_error := v515_upper_checked
  lower_error := reuse_lower_error 5 46 Primitive.Addresses.material515

def v516_pa : Scalar.QComplex := ((999993794305599653667975162616 : Int)/10^30,(3522974636589039305179145616 : Int)/10^30)
theorem v516_pa_checked : Scalar.distance (sourceCoefficient 5 47 1 0) v516_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v516_pb : Scalar.QComplex := ((1520079061423815503598657 : Int)/10^30,(-431473338607238609293855261 : Int)/10^30)
theorem v516_pb_checked : Scalar.distance (sourceCoefficient 5 47 1 1) v516_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v516_pg : Scalar.QComplex := ((-93085689911746036534718 : Int)/10^30,(-327940559687368393637 : Int)/10^30)
theorem v516_pg_checked : Scalar.distance (sourceCoefficient 5 47 1 2) v516_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v516_mb : Scalar.QComplex := ((1147736437048652993104137 : Int)/10^30,(-431474489709763529339554219 : Int)/10^30)
theorem v516_mb_checked : Scalar.distance (sourceCoefficient 5 47 3 1) v516_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v516_mg : Scalar.QComplex := ((-93085938249622571874526 : Int)/10^30,(-247611679610117105032 : Int)/10^30)
theorem v516_mg_checked : Scalar.distance (sourceCoefficient 5 47 3 2) v516_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v516_upper : Scalar.QComplex := ((999998385266931548442283448832 : Int)/10^30,(1797070819289054362814125217 : Int)/10^30)
theorem v516_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 47 5) 1) 14) v516_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material516 : Material (5 : Basis) (47 : Basis) where
  plus := ![v516_pa,v516_pb,v516_pg]
  minus := ![(Primitive.Addresses.material516 1).one,v516_mb,v516_mg]
  upper := v516_upper
  lower := (Primitive.Addresses.material516 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v516_pa_checked.trans (by decide +kernel)
    · exact v516_pb_checked.trans (by decide +kernel)
    · exact v516_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 47 Primitive.Addresses.material516
    · exact v516_mb_checked.trans (by decide +kernel)
    · exact v516_mg_checked.trans (by decide +kernel)
  upper_error := v516_upper_checked
  lower_error := reuse_lower_error 5 47 Primitive.Addresses.material516

def v517_pa : Scalar.QComplex := ((999993890566578659012595427445 : Int)/10^30,(3495544237669614303818892578 : Int)/10^30)
theorem v517_pa_checked : Scalar.distance (sourceCoefficient 5 48 1 0) v517_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v517_pb : Scalar.QComplex := ((1508243438901658693267232 : Int)/10^30,(-431473362040551631065192157 : Int)/10^30)
theorem v517_pb_checked : Scalar.distance (sourceCoefficient 5 48 1 1) v517_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v517_pg : Scalar.QComplex := ((-93085696919777192119050 : Int)/10^30,(-325387159408573895323 : Int)/10^30)
theorem v517_pg_checked : Scalar.distance (sourceCoefficient 5 48 1 2) v517_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v517_mb : Scalar.QComplex := ((1135900798711545621894332 : Int)/10^30,(-431474502929458645846575419 : Int)/10^30)
theorem v517_mb_checked : Scalar.distance (sourceCoefficient 5 48 3 1) v517_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v517_mg : Scalar.QComplex := ((-93085943054181678328447 : Int)/10^30,(-245058274234454969408 : Int)/10^30)
theorem v517_mg_checked : Scalar.distance (sourceCoefficient 5 48 3 2) v517_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v517_upper : Scalar.QComplex := ((999998434185387115789869688104 : Int)/10^30,(1769640295086269315507285129 : Int)/10^30)
theorem v517_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 48 5) 1) 14) v517_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material517 : Material (5 : Basis) (48 : Basis) where
  plus := ![v517_pa,v517_pb,v517_pg]
  minus := ![(Primitive.Addresses.material517 1).one,v517_mb,v517_mg]
  upper := v517_upper
  lower := (Primitive.Addresses.material517 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v517_pa_checked.trans (by decide +kernel)
    · exact v517_pb_checked.trans (by decide +kernel)
    · exact v517_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 48 Primitive.Addresses.material517
    · exact v517_mb_checked.trans (by decide +kernel)
    · exact v517_mg_checked.trans (by decide +kernel)
  upper_error := v517_upper_checked
  lower_error := reuse_lower_error 5 48 Primitive.Addresses.material517

def v518_pa : Scalar.QComplex := ((999993967359881378288644626454 : Int)/10^30,(3473505987398988478469009219 : Int)/10^30)
theorem v518_pa_checked : Scalar.distance (sourceCoefficient 5 49 1 0) v518_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v518_pb : Scalar.QComplex := ((1498734412082395630170995 : Int)/10^30,(-431473380553842481510003672 : Int)/10^30)
theorem v518_pb_checked : Scalar.distance (sourceCoefficient 5 49 1 1) v518_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v518_pg : Scalar.QComplex := ((-93085702491000586573559 : Int)/10^30,(-323335695511619999741 : Int)/10^30)
theorem v518_pg_checked : Scalar.distance (sourceCoefficient 5 49 1 2) v518_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v518_mb : Scalar.QComplex := ((1126391759456791631337895 : Int)/10^30,(-431474513236880728592865719 : Int)/10^30)
theorem v518_mb_checked : Scalar.distance (sourceCoefficient 5 49 3 1) v518_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v518_mg : Scalar.QComplex := ((-93085946855082049794731 : Int)/10^30,(-243006806293639968367 : Int)/10^30)
theorem v518_mg_checked : Scalar.distance (sourceCoefficient 5 49 3 2) v518_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v518_upper : Scalar.QComplex := ((999998472942554787809039009836 : Int)/10^30,(1747601945100754614056743167 : Int)/10^30)
theorem v518_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 49 5) 1) 14) v518_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material518 : Material (5 : Basis) (49 : Basis) where
  plus := ![v518_pa,v518_pb,v518_pg]
  minus := ![(Primitive.Addresses.material518 1).one,v518_mb,v518_mg]
  upper := v518_upper
  lower := (Primitive.Addresses.material518 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v518_pa_checked.trans (by decide +kernel)
    · exact v518_pb_checked.trans (by decide +kernel)
    · exact v518_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 49 Primitive.Addresses.material518
    · exact v518_mb_checked.trans (by decide +kernel)
    · exact v518_mg_checked.trans (by decide +kernel)
  upper_error := v518_upper_checked
  lower_error := reuse_lower_error 5 49 Primitive.Addresses.material518

def v519_pa : Scalar.QComplex := ((999993976301819682794069739891 : Int)/10^30,(3470930721822987394628689973 : Int)/10^30)
theorem v519_pa_checked : Scalar.distance (sourceCoefficient 5 50 1 0) v519_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v519_pb : Scalar.QComplex := ((1497623240889125090082708 : Int)/10^30,(-431473382698967730397490898 : Int)/10^30)
theorem v519_pb_checked : Scalar.distance (sourceCoefficient 5 50 1 1) v519_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v519_pg : Scalar.QComplex := ((-93085703138580355012841 : Int)/10^30,(-323095973018817776114 : Int)/10^30)
theorem v519_pg_checked : Scalar.distance (sourceCoefficient 5 50 1 2) v519_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v519_mb : Scalar.QComplex := ((1125280586826114432601366 : Int)/10^30,(-431474514423114484252485932 : Int)/10^30)
theorem v519_mb_checked : Scalar.distance (sourceCoefficient 5 50 3 1) v519_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v519_mg : Scalar.QComplex := ((-93085947295791862522433 : Int)/10^30,(-242767083331265210416 : Int)/10^30)
theorem v519_mg_checked : Scalar.distance (sourceCoefficient 5 50 3 2) v519_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v519_upper : Scalar.QComplex := ((999998477439805016437949278052 : Int)/10^30,(1745026667927334786455001186 : Int)/10^30)
theorem v519_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 50 5) 1) 14) v519_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material519 : Material (5 : Basis) (50 : Basis) where
  plus := ![v519_pa,v519_pb,v519_pg]
  minus := ![(Primitive.Addresses.material519 1).one,v519_mb,v519_mg]
  upper := v519_upper
  lower := (Primitive.Addresses.material519 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v519_pa_checked.trans (by decide +kernel)
    · exact v519_pb_checked.trans (by decide +kernel)
    · exact v519_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 50 Primitive.Addresses.material519
    · exact v519_mb_checked.trans (by decide +kernel)
    · exact v519_mg_checked.trans (by decide +kernel)
  upper_error := v519_upper_checked
  lower_error := reuse_lower_error 5 50 Primitive.Addresses.material519

def v520_pa : Scalar.QComplex := ((999994015456899268434882729031 : Int)/10^30,(3459631539153700934298015668 : Int)/10^30)
theorem v520_pa_checked : Scalar.distance (sourceCoefficient 5 51 1 0) v520_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v520_pb : Scalar.QComplex := ((1492747888910481328728731 : Int)/10^30,(-431473392065779683139155318 : Int)/10^30)
theorem v520_pb_checked : Scalar.distance (sourceCoefficient 5 51 1 1) v520_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v520_pg : Scalar.QComplex := ((-93085705971375314583162 : Int)/10^30,(-322044171510182771593 : Int)/10^30)
theorem v520_pg_checked : Scalar.distance (sourceCoefficient 5 51 1 2) v520_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v520_mb : Scalar.QComplex := ((1120405228579650177823059 : Int)/10^30,(-431474519582713769434420514 : Int)/10^30)
theorem v520_mb_checked : Scalar.distance (sourceCoefficient 5 51 3 1) v520_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v520_mg : Scalar.QComplex := ((-93085949220928436743158 : Int)/10^30,(-241715279769689511503 : Int)/10^30)
theorem v520_mg_checked : Scalar.distance (sourceCoefficient 5 51 3 2) v520_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v520_upper : Scalar.QComplex := ((999998497093462051843244129689 : Int)/10^30,(1733727434508738373049089337 : Int)/10^30)
theorem v520_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 51 5) 1) 14) v520_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material520 : Material (5 : Basis) (51 : Basis) where
  plus := ![v520_pa,v520_pb,v520_pg]
  minus := ![(Primitive.Addresses.material520 1).one,v520_mb,v520_mg]
  upper := v520_upper
  lower := (Primitive.Addresses.material520 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v520_pa_checked.trans (by decide +kernel)
    · exact v520_pb_checked.trans (by decide +kernel)
    · exact v520_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 51 Primitive.Addresses.material520
    · exact v520_mb_checked.trans (by decide +kernel)
    · exact v520_mg_checked.trans (by decide +kernel)
  upper_error := v520_upper_checked
  lower_error := reuse_lower_error 5 51 Primitive.Addresses.material520

def v521_pa : Scalar.QComplex := ((999994098849141226340736163475 : Int)/10^30,(3435442750791498857308909862 : Int)/10^30)
theorem v521_pa_checked : Scalar.distance (sourceCoefficient 5 52 1 0) v521_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v521_pb : Scalar.QComplex := ((1482310952311733587413419 : Int)/10^30,(-431473411870907664222050040 : Int)/10^30)
theorem v521_pb_checked : Scalar.distance (sourceCoefficient 5 52 1 1) v521_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v521_pg : Scalar.QComplex := ((-93085711989084096229803 : Int)/10^30,(-319792521599077735996 : Int)/10^30)
theorem v521_pg_checked : Scalar.distance (sourceCoefficient 5 52 1 2) v521_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v521_mb : Scalar.QComplex := ((1109968278776117465965466 : Int)/10^30,(-431474530381228153618607505 : Int)/10^30)
theorem v521_mb_checked : Scalar.distance (sourceCoefficient 5 52 3 1) v521_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v521_mg : Scalar.QComplex := ((-93085953295562514985610 : Int)/10^30,(-239463625503964992277 : Int)/10^30)
theorem v521_mg_checked : Scalar.distance (sourceCoefficient 5 52 3 2) v521_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v521_upper : Scalar.QComplex := ((999998538737925483378444287623 : Int)/10^30,(1709538538245450812628612287 : Int)/10^30)
theorem v521_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 52 5) 1) 14) v521_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material521 : Material (5 : Basis) (52 : Basis) where
  plus := ![v521_pa,v521_pb,v521_pg]
  minus := ![(Primitive.Addresses.material521 1).one,v521_mb,v521_mg]
  upper := v521_upper
  lower := (Primitive.Addresses.material521 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v521_pa_checked.trans (by decide +kernel)
    · exact v521_pb_checked.trans (by decide +kernel)
    · exact v521_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 52 Primitive.Addresses.material521
    · exact v521_mb_checked.trans (by decide +kernel)
    · exact v521_mg_checked.trans (by decide +kernel)
  upper_error := v521_upper_checked
  lower_error := reuse_lower_error 5 52 Primitive.Addresses.material521

def v522_pa : Scalar.QComplex := ((999994111562665409596887005733 : Int)/10^30,(3431740082740323564998567639 : Int)/10^30)
theorem v522_pa_checked : Scalar.distance (sourceCoefficient 5 53 1 0) v522_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v522_pb : Scalar.QComplex := ((1480713331543651871173782 : Int)/10^30,(-431473414872845445028584829 : Int)/10^30)
theorem v522_pb_checked : Scalar.distance (sourceCoefficient 5 53 1 1) v522_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v522_pg : Scalar.QComplex := ((-93085712904629376331693 : Int)/10^30,(-319447853153939787352 : Int)/10^30)
theorem v522_pg_checked : Scalar.distance (sourceCoefficient 5 53 1 2) v522_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v522_mb : Scalar.QComplex := ((1108370656012365873981426 : Int)/10^30,(-431474532004490047980320168 : Int)/10^30)
theorem v522_mb_checked : Scalar.distance (sourceCoefficient 5 53 3 1) v522_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v522_mg : Scalar.QComplex := ((-93085953913674109324618 : Int)/10^30,(-239118956397088515784 : Int)/10^30)
theorem v522_mg_checked : Scalar.distance (sourceCoefficient 5 53 3 2) v522_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v522_upper : Scalar.QComplex := ((999998545060961578426874190568 : Int)/10^30,(1705835853766575258205510743 : Int)/10^30)
theorem v522_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 53 5) 1) 14) v522_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material522 : Material (5 : Basis) (53 : Basis) where
  plus := ![v522_pa,v522_pb,v522_pg]
  minus := ![(Primitive.Addresses.material522 1).one,v522_mb,v522_mg]
  upper := v522_upper
  lower := (Primitive.Addresses.material522 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v522_pa_checked.trans (by decide +kernel)
    · exact v522_pb_checked.trans (by decide +kernel)
    · exact v522_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 53 Primitive.Addresses.material522
    · exact v522_mb_checked.trans (by decide +kernel)
    · exact v522_mg_checked.trans (by decide +kernel)
  upper_error := v522_upper_checked
  lower_error := reuse_lower_error 5 53 Primitive.Addresses.material522

def v523_pa : Scalar.QComplex := ((999994118021041332715618523404 : Int)/10^30,(3429857623817364602981649857 : Int)/10^30)
theorem v523_pa_checked : Scalar.distance (sourceCoefficient 5 54 1 0) v523_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v523_pb : Scalar.QComplex := ((1479901091447509703121336 : Int)/10^30,(-431473416396024495396654420 : Int)/10^30)
theorem v523_pb_checked : Scalar.distance (sourceCoefficient 5 54 1 1) v523_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v523_pg : Scalar.QComplex := ((-93085713369527245297029 : Int)/10^30,(-319272621623793475034 : Int)/10^30)
theorem v523_pg_checked : Scalar.distance (sourceCoefficient 5 54 1 2) v523_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v523_mb : Scalar.QComplex := ((1107558414904222895899106 : Int)/10^30,(-431474532826741910164470505 : Int)/10^30)
theorem v523_mb_checked : Scalar.distance (sourceCoefficient 5 54 3 1) v523_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v523_mg : Scalar.QComplex := ((-93085954227354886806111 : Int)/10^30,(-238943724531002987923 : Int)/10^30)
theorem v523_mg_checked : Scalar.distance (sourceCoefficient 5 54 3 2) v523_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v523_upper : Scalar.QComplex := ((999998548270374556865621004358 : Int)/10^30,(1703953386500746788761420625 : Int)/10^30)
theorem v523_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 54 5) 1) 14) v523_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material523 : Material (5 : Basis) (54 : Basis) where
  plus := ![v523_pa,v523_pb,v523_pg]
  minus := ![(Primitive.Addresses.material523 1).one,v523_mb,v523_mg]
  upper := v523_upper
  lower := (Primitive.Addresses.material523 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v523_pa_checked.trans (by decide +kernel)
    · exact v523_pb_checked.trans (by decide +kernel)
    · exact v523_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 54 Primitive.Addresses.material523
    · exact v523_mb_checked.trans (by decide +kernel)
    · exact v523_mg_checked.trans (by decide +kernel)
  upper_error := v523_upper_checked
  lower_error := reuse_lower_error 5 54 Primitive.Addresses.material523

def v524_pa : Scalar.QComplex := ((999994170529678874498492454723 : Int)/10^30,(3414514117634715261689753148 : Int)/10^30)
theorem v524_pa_checked : Scalar.distance (sourceCoefficient 5 55 1 0) v524_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v524_pb : Scalar.QComplex := ((1473280702246351418420437 : Int)/10^30,(-431473428735090573399464376 : Int)/10^30)
theorem v524_pb_checked : Scalar.distance (sourceCoefficient 5 55 1 1) v524_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v524_pg : Scalar.QComplex := ((-93085717144454721220016 : Int)/10^30,(-317844348204087092395 : Int)/10^30)
theorem v524_pg_checked : Scalar.distance (sourceCoefficient 5 55 1 2) v524_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v524_mb : Scalar.QComplex := ((1100938017520079783113057 : Int)/10^30,(-431474539452705684430439422 : Int)/10^30)
theorem v524_mb_checked : Scalar.distance (sourceCoefficient 5 55 3 1) v524_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v524_mg : Scalar.QComplex := ((-93085956769745322991359 : Int)/10^30,(-237515448385515679461 : Int)/10^30)
theorem v524_mg_checked : Scalar.distance (sourceCoefficient 5 55 3 2) v524_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v524_upper : Scalar.QComplex := ((999998574297434173955768807362 : Int)/10^30,(1688609812545302680949344161 : Int)/10^30)
theorem v524_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 55 5) 1) 14) v524_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material524 : Material (5 : Basis) (55 : Basis) where
  plus := ![v524_pa,v524_pb,v524_pg]
  minus := ![(Primitive.Addresses.material524 1).one,v524_mb,v524_mg]
  upper := v524_upper
  lower := (Primitive.Addresses.material524 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v524_pa_checked.trans (by decide +kernel)
    · exact v524_pb_checked.trans (by decide +kernel)
    · exact v524_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 55 Primitive.Addresses.material524
    · exact v524_mb_checked.trans (by decide +kernel)
    · exact v524_mg_checked.trans (by decide +kernel)
  upper_error := v524_upper_checked
  lower_error := reuse_lower_error 5 55 Primitive.Addresses.material524

def v525_pa : Scalar.QComplex := ((999994182956878762717923213268 : Int)/10^30,(3410872674915305281013678631 : Int)/10^30)
theorem v525_pa_checked : Scalar.distance (sourceCoefficient 5 56 1 0) v525_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v525_pb : Scalar.QComplex := ((1471709498942741125543433 : Int)/10^30,(-431473431643609318294834652 : Int)/10^30)
theorem v525_pb_checked : Scalar.distance (sourceCoefficient 5 56 1 1) v525_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v525_pg : Scalar.QComplex := ((-93085718036596494738846 : Int)/10^30,(-317505379018378739871 : Int)/10^30)
theorem v525_pg_checked : Scalar.distance (sourceCoefficient 5 56 1 2) v525_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v525_mb : Scalar.QComplex := ((1099366812291579605685314 : Int)/10^30,(-431474541005345659705570065 : Int)/10^30)
theorem v525_mb_checked : Scalar.distance (sourceCoefficient 5 56 3 1) v525_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v525_mg : Scalar.QComplex := ((-93085957369371623664126 : Int)/10^30,(-237176478556142876460 : Int)/10^30)
theorem v525_mg_checked : Scalar.distance (sourceCoefficient 5 56 3 2) v525_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v525_upper : Scalar.QComplex := ((999998580439815768722100157808 : Int)/10^30,(1684968353801174256625000308 : Int)/10^30)
theorem v525_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 56 5) 1) 14) v525_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material525 : Material (5 : Basis) (56 : Basis) where
  plus := ![v525_pa,v525_pb,v525_pg]
  minus := ![(Primitive.Addresses.material525 1).one,v525_mb,v525_mg]
  upper := v525_upper
  lower := (Primitive.Addresses.material525 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v525_pa_checked.trans (by decide +kernel)
    · exact v525_pb_checked.trans (by decide +kernel)
    · exact v525_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 56 Primitive.Addresses.material525
    · exact v525_mb_checked.trans (by decide +kernel)
    · exact v525_mg_checked.trans (by decide +kernel)
  upper_error := v525_upper_checked
  lower_error := reuse_lower_error 5 56 Primitive.Addresses.material525

def v526_pa : Scalar.QComplex := ((999994223060288622601104047446 : Int)/10^30,(3399094886837136958055993974 : Int)/10^30)
theorem v526_pa_checked : Scalar.distance (sourceCoefficient 5 57 1 0) v526_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v526_pb : Scalar.QComplex := ((1466627639723845595264234 : Int)/10^30,(-431473440998607506067826449 : Int)/10^30)
theorem v526_pb_checked : Scalar.distance (sourceCoefficient 5 57 1 1) v526_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v526_pg : Scalar.QComplex := ((-93085720912255402414226 : Int)/10^30,(-316409025866262655366 : Int)/10^30)
theorem v526_pg_checked : Scalar.distance (sourceCoefficient 5 57 1 2) v526_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v526_mb : Scalar.QComplex := ((1094284946891950412470379 : Int)/10^30,(-431474545974924736721201266 : Int)/10^30)
theorem v526_mb_checked : Scalar.distance (sourceCoefficient 5 57 3 1) v526_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v526_mg : Scalar.QComplex := ((-93085959298926068237067 : Int)/10^30,(-236080123330685053848 : Int)/10^30)
theorem v526_mg_checked : Scalar.distance (sourceCoefficient 5 57 3 2) v526_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v526_upper : Scalar.QComplex := ((999998600215772148956648326786 : Int)/10^30,(1673190514049790494689087979 : Int)/10^30)
theorem v526_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 57 5) 1) 14) v526_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material526 : Material (5 : Basis) (57 : Basis) where
  plus := ![v526_pa,v526_pb,v526_pg]
  minus := ![(Primitive.Addresses.material526 1).one,v526_mb,v526_mg]
  upper := v526_upper
  lower := (Primitive.Addresses.material526 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v526_pa_checked.trans (by decide +kernel)
    · exact v526_pb_checked.trans (by decide +kernel)
    · exact v526_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 57 Primitive.Addresses.material526
    · exact v526_mb_checked.trans (by decide +kernel)
    · exact v526_mg_checked.trans (by decide +kernel)
  upper_error := v526_upper_checked
  lower_error := reuse_lower_error 5 57 Primitive.Addresses.material526

def v527_pa : Scalar.QComplex := ((999994244761955989317072405744 : Int)/10^30,(3392704373395421941191431152 : Int)/10^30)
theorem v527_pa_checked : Scalar.distance (sourceCoefficient 5 58 1 0) v527_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v527_pb : Scalar.QComplex := ((1463870272309653595806976 : Int)/10^30,(-431473446041140477347534759 : Int)/10^30)
theorem v527_pb_checked : Scalar.distance (sourceCoefficient 5 58 1 1) v527_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v527_pg : Scalar.QComplex := ((-93085722466255364120462 : Int)/10^30,(-315814155297578461583 : Int)/10^30)
theorem v527_pg_checked : Scalar.distance (sourceCoefficient 5 58 1 2) v527_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v527_mb : Scalar.QComplex := ((1091527576152973472273062 : Int)/10^30,(-431474548637971939206022663 : Int)/10^30)
theorem v527_mb_checked : Scalar.distance (sourceCoefficient 5 58 3 1) v527_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v527_mg : Scalar.QComplex := ((-93085960339578942519486 : Int)/10^30,(-235485251642466382321 : Int)/10^30)
theorem v527_mg_checked : Scalar.distance (sourceCoefficient 5 58 3 2) v527_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v527_upper : Scalar.QComplex := ((999998610887960736038941542184 : Int)/10^30,(1666799972670885451750252384 : Int)/10^30)
theorem v527_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 58 5) 1) 14) v527_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material527 : Material (5 : Basis) (58 : Basis) where
  plus := ![v527_pa,v527_pb,v527_pg]
  minus := ![(Primitive.Addresses.material527 1).one,v527_mb,v527_mg]
  upper := v527_upper
  lower := (Primitive.Addresses.material527 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v527_pa_checked.trans (by decide +kernel)
    · exact v527_pb_checked.trans (by decide +kernel)
    · exact v527_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 58 Primitive.Addresses.material527
    · exact v527_mb_checked.trans (by decide +kernel)
    · exact v527_mg_checked.trans (by decide +kernel)
  upper_error := v527_upper_checked
  lower_error := reuse_lower_error 5 58 Primitive.Addresses.material527

def v528_pa : Scalar.QComplex := ((999994304203673410411027090721 : Int)/10^30,(3375138546946389274158586988 : Int)/10^30)
theorem v528_pa_checked : Scalar.distance (sourceCoefficient 5 59 1 0) v528_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v528_pb : Scalar.QComplex := ((1456291000827018198927306 : Int)/10^30,(-431473459780676922914216301 : Int)/10^30)
theorem v528_pb_checked : Scalar.distance (sourceCoefficient 5 59 1 1) v528_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v528_pg : Scalar.QComplex := ((-93085726714938405935928 : Int)/10^30,(-314179013905779197307 : Int)/10^30)
theorem v528_pg_checked : Scalar.distance (sourceCoefficient 5 59 1 2) v528_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v528_mb : Scalar.QComplex := ((1083948295635846091423624 : Int)/10^30,(-431474555836933337116794023 : Int)/10^30)
theorem v528_mb_checked : Scalar.distance (sourceCoefficient 5 59 3 1) v528_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v528_mg : Scalar.QComplex := ((-93085963177207025267807 : Int)/10^30,(-233850107193082876360 : Int)/10^30)
theorem v528_mg_checked : Scalar.distance (sourceCoefficient 5 59 3 2) v528_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v528_upper : Scalar.QComplex := ((999998640012566733974182748571 : Int)/10^30,(1649234069793076095301322430 : Int)/10^30)
theorem v528_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 59 5) 1) 14) v528_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material528 : Material (5 : Basis) (59 : Basis) where
  plus := ![v528_pa,v528_pb,v528_pg]
  minus := ![(Primitive.Addresses.material528 1).one,v528_mb,v528_mg]
  upper := v528_upper
  lower := (Primitive.Addresses.material528 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v528_pa_checked.trans (by decide +kernel)
    · exact v528_pb_checked.trans (by decide +kernel)
    · exact v528_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 59 Primitive.Addresses.material528
    · exact v528_mb_checked.trans (by decide +kernel)
    · exact v528_mg_checked.trans (by decide +kernel)
  upper_error := v528_upper_checked
  lower_error := reuse_lower_error 5 59 Primitive.Addresses.material528

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
