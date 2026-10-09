import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B062

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1489_pa : Scalar.QComplex := ((999999432553543968135954229621 : Int)/10^30,(-1065313376461709330966556533 : Int)/10^30)
theorem v1489_pa_checked : Scalar.distance (sourceCoefficient 16 74 1 0) v1489_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1489_pb : Scalar.QComplex := ((-459658705742765813055008 : Int)/10^30,(-431477211370192352245529724 : Int)/10^30)
theorem v1489_pb_checked : Scalar.distance (sourceCoefficient 16 74 1 1) v1489_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1489_pg : Scalar.QComplex := ((-93086370086546219548542 : Int)/10^30,(99166211490978079644 : Int)/10^30)
theorem v1489_pg_checked : Scalar.distance (sourceCoefficient 16 74 1 2) v1489_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1489_mb : Scalar.QComplex := ((-832003934991085433352147 : Int)/10^30,(-431476654046746279996845175 : Int)/10^30)
theorem v1489_mb_checked : Scalar.distance (sourceCoefficient 16 74 3 1) v1489_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1489_mg : Scalar.QComplex := ((-93086249850262142705206 : Int)/10^30,(179495519497077336938 : Int)/10^30)
theorem v1489_mg_checked : Scalar.distance (sourceCoefficient 16 74 3 2) v1489_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1489_upper : Scalar.QComplex := ((999996104537614066326988315405 : Int)/10^30,(-2791220091150131034271462273 : Int)/10^30)
theorem v1489_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 74 5) 1) 14) v1489_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1489 : Material (16 : Basis) (74 : Basis) where
  plus := ![v1489_pa,v1489_pb,v1489_pg]
  minus := ![(Primitive.Addresses.material1489 1).one,v1489_mb,v1489_mg]
  upper := v1489_upper
  lower := (Primitive.Addresses.material1489 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1489_pa_checked.trans (by decide +kernel)
    · exact v1489_pb_checked.trans (by decide +kernel)
    · exact v1489_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 74 Primitive.Addresses.material1489
    · exact v1489_mb_checked.trans (by decide +kernel)
    · exact v1489_mg_checked.trans (by decide +kernel)
  upper_error := v1489_upper_checked
  lower_error := reuse_lower_error 16 74 Primitive.Addresses.material1489

def v1490_pa : Scalar.QComplex := ((999999416661044973065847606894 : Int)/10^30,(-1080128496878742595500654633 : Int)/10^30)
theorem v1490_pa_checked : Scalar.distance (sourceCoefficient 16 75 1 0) v1490_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1490_pb : Scalar.QComplex := ((-466051094012128022093212 : Int)/10^30,(-431477202474632661757942033 : Int)/10^30)
theorem v1490_pb_checked : Scalar.distance (sourceCoefficient 16 75 1 1) v1490_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1490_pg : Scalar.QComplex := ((-93086368387299662639926 : Int)/10^30,(100545297818063849132 : Int)/10^30)
theorem v1490_pg_checked : Scalar.distance (sourceCoefficient 16 75 1 2) v1490_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1490_mb : Scalar.QComplex := ((-838396313203801971375730 : Int)/10^30,(-431476639634846727753300656 : Int)/10^30)
theorem v1490_mb_checked : Scalar.distance (sourceCoefficient 16 75 3 1) v1490_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1490_mg : Scalar.QComplex := ((-93086246960926829971199 : Int)/10^30,(180874603844292992106 : Int)/10^30)
theorem v1490_mg_checked : Scalar.distance (sourceCoefficient 16 75 3 2) v1490_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1490_upper : Scalar.QComplex := ((999996063075584918693203047084 : Int)/10^30,(-2806035162072771234683994037 : Int)/10^30)
theorem v1490_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 75 5) 1) 14) v1490_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1490 : Material (16 : Basis) (75 : Basis) where
  plus := ![v1490_pa,v1490_pb,v1490_pg]
  minus := ![(Primitive.Addresses.material1490 1).one,v1490_mb,v1490_mg]
  upper := v1490_upper
  lower := (Primitive.Addresses.material1490 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1490_pa_checked.trans (by decide +kernel)
    · exact v1490_pb_checked.trans (by decide +kernel)
    · exact v1490_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 75 Primitive.Addresses.material1490
    · exact v1490_mb_checked.trans (by decide +kernel)
    · exact v1490_mg_checked.trans (by decide +kernel)
  upper_error := v1490_upper_checked
  lower_error := reuse_lower_error 16 75 Primitive.Addresses.material1490

def v1491_pa : Scalar.QComplex := ((999999403157593263613739984166 : Int)/10^30,(-1092558674512226844893165051 : Int)/10^30)
theorem v1491_pa_checked : Scalar.distance (sourceCoefficient 16 76 1 0) v1491_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1491_pb : Scalar.QComplex := ((-471414433517253364757213 : Int)/10^30,(-431477194913665654404552958 : Int)/10^30)
theorem v1491_pb_checked : Scalar.distance (sourceCoefficient 16 76 1 1) v1491_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1491_pg : Scalar.QComplex := ((-93086366943208739915385 : Int)/10^30,(101702378382923195108 : Int)/10^30)
theorem v1491_pg_checked : Scalar.distance (sourceCoefficient 16 76 1 2) v1491_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1491_mb : Scalar.QComplex := ((-843759644187136905524016 : Int)/10^30,(-431476627445562098614647369 : Int)/10^30)
theorem v1491_mb_checked : Scalar.distance (sourceCoefficient 16 76 3 1) v1491_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1491_mg : Scalar.QComplex := ((-93086244518328030448208 : Int)/10^30,(182031682732132935719 : Int)/10^30)
theorem v1491_mg_checked : Scalar.distance (sourceCoefficient 16 76 3 2) v1491_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1491_upper : Scalar.QComplex := ((999996028118794382558512689260 : Int)/10^30,(-2818465297887233423291958735 : Int)/10^30)
theorem v1491_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 76 5) 1) 14) v1491_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1491 : Material (16 : Basis) (76 : Basis) where
  plus := ![v1491_pa,v1491_pb,v1491_pg]
  minus := ![(Primitive.Addresses.material1491 1).one,v1491_mb,v1491_mg]
  upper := v1491_upper
  lower := (Primitive.Addresses.material1491 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1491_pa_checked.trans (by decide +kernel)
    · exact v1491_pb_checked.trans (by decide +kernel)
    · exact v1491_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 76 Primitive.Addresses.material1491
    · exact v1491_mb_checked.trans (by decide +kernel)
    · exact v1491_mg_checked.trans (by decide +kernel)
  upper_error := v1491_upper_checked
  lower_error := reuse_lower_error 16 76 Primitive.Addresses.material1491

def v1492_pa : Scalar.QComplex := ((999999400009403784655018176181 : Int)/10^30,(-1095436366222143647891796573 : Int)/10^30)
theorem v1492_pa_checked : Scalar.distance (sourceCoefficient 16 77 1 0) v1492_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1492_pb : Scalar.QComplex := ((-472656092161796693384400 : Int)/10^30,(-431477193150566113983088140 : Int)/10^30)
theorem v1492_pb_checked : Scalar.distance (sourceCoefficient 16 77 1 1) v1492_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1492_pg : Scalar.QComplex := ((-93086366606497415716069 : Int)/10^30,(101970252361436336675 : Int)/10^30)
theorem v1492_pg_checked : Scalar.distance (sourceCoefficient 16 77 1 2) v1492_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1492_mb : Scalar.QComplex := ((-845001300847878477856175 : Int)/10^30,(-431476624610967726664245970 : Int)/10^30)
theorem v1492_mb_checked : Scalar.distance (sourceCoefficient 16 77 3 1) v1492_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1492_mg : Scalar.QComplex := ((-93086243950453652761199 : Int)/10^30,(182299556320337644771 : Int)/10^30)
theorem v1492_mg_checked : Scalar.distance (sourceCoefficient 16 77 3 2) v1492_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1492_upper : Scalar.QComplex := ((999996020003974763294423530484 : Int)/10^30,(-2821342979877677022619372890 : Int)/10^30)
theorem v1492_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 77 5) 1) 14) v1492_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1492 : Material (16 : Basis) (77 : Basis) where
  plus := ![v1492_pa,v1492_pb,v1492_pg]
  minus := ![(Primitive.Addresses.material1492 1).one,v1492_mb,v1492_mg]
  upper := v1492_upper
  lower := (Primitive.Addresses.material1492 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1492_pa_checked.trans (by decide +kernel)
    · exact v1492_pb_checked.trans (by decide +kernel)
    · exact v1492_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 77 Primitive.Addresses.material1492
    · exact v1492_mb_checked.trans (by decide +kernel)
    · exact v1492_mg_checked.trans (by decide +kernel)
  upper_error := v1492_upper_checked
  lower_error := reuse_lower_error 16 77 Primitive.Addresses.material1492

def v1493_pa : Scalar.QComplex := ((999999380909166792904021121244 : Int)/10^30,(-1112735944930661524417803911 : Int)/10^30)
theorem v1493_pa_checked : Scalar.distance (sourceCoefficient 16 78 1 0) v1493_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1493_pb : Scalar.QComplex := ((-480120467568903010413994 : Int)/10^30,(-431477182451080677079219249 : Int)/10^30)
theorem v1493_pb_checked : Scalar.distance (sourceCoefficient 16 78 1 1) v1493_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1493_pg : Scalar.QComplex := ((-93086364563364056890294 : Int)/10^30,(103580607958379834657 : Int)/10^30)
theorem v1493_pg_checked : Scalar.distance (sourceCoefficient 16 78 1 2) v1493_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1493_mb : Scalar.QComplex := ((-852465664242482646898938 : Int)/10^30,(-431476607470066480323681200 : Int)/10^30)
theorem v1493_mb_checked : Scalar.distance (sourceCoefficient 16 78 3 1) v1493_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1493_mg : Scalar.QComplex := ((-93086240517656702248841 : Int)/10^30,(183909909554540087769 : Int)/10^30)
theorem v1493_mg_checked : Scalar.distance (sourceCoefficient 16 78 3 2) v1493_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1493_upper : Scalar.QComplex := ((999995971046262773721812953683 : Int)/10^30,(-2838642499855228276276038945 : Int)/10^30)
theorem v1493_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 78 5) 1) 14) v1493_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1493 : Material (16 : Basis) (78 : Basis) where
  plus := ![v1493_pa,v1493_pb,v1493_pg]
  minus := ![(Primitive.Addresses.material1493 1).one,v1493_mb,v1493_mg]
  upper := v1493_upper
  lower := (Primitive.Addresses.material1493 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1493_pa_checked.trans (by decide +kernel)
    · exact v1493_pb_checked.trans (by decide +kernel)
    · exact v1493_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 78 Primitive.Addresses.material1493
    · exact v1493_mb_checked.trans (by decide +kernel)
    · exact v1493_mg_checked.trans (by decide +kernel)
  upper_error := v1493_upper_checked
  lower_error := reuse_lower_error 16 78 Primitive.Addresses.material1493

def v1494_pa : Scalar.QComplex := ((999999374687796311653618920772 : Int)/10^30,(-1118313022530517025626218178 : Int)/10^30)
theorem v1494_pa_checked : Scalar.distance (sourceCoefficient 16 79 1 0) v1494_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1494_pb : Scalar.QComplex := ((-482526849891280595403094 : Int)/10^30,(-431477178965056137458060354 : Int)/10^30)
theorem v1494_pb_checked : Scalar.distance (sourceCoefficient 16 79 1 1) v1494_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1494_pg : Scalar.QComplex := ((-93086363897766147105566 : Int)/10^30,(104099758061735576928 : Int)/10^30)
theorem v1494_pg_checked : Scalar.distance (sourceCoefficient 16 79 1 2) v1494_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1494_mb : Scalar.QComplex := ((-854872042660571943185668 : Int)/10^30,(-431476601907443673933487840 : Int)/10^30)
theorem v1494_mb_checked : Scalar.distance (sourceCoefficient 16 79 3 1) v1494_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1494_mg : Scalar.QComplex := ((-93086239404055882753316 : Int)/10^30,(184429058890211501502 : Int)/10^30)
theorem v1494_mg_checked : Scalar.distance (sourceCoefficient 16 79 3 2) v1494_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1494_upper : Scalar.QComplex := ((999995955199371569648939863084 : Int)/10^30,(-2844219558411160769737931529 : Int)/10^30)
theorem v1494_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 79 5) 1) 14) v1494_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1494 : Material (16 : Basis) (79 : Basis) where
  plus := ![v1494_pa,v1494_pb,v1494_pg]
  minus := ![(Primitive.Addresses.material1494 1).one,v1494_mb,v1494_mg]
  upper := v1494_upper
  lower := (Primitive.Addresses.material1494 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1494_pa_checked.trans (by decide +kernel)
    · exact v1494_pb_checked.trans (by decide +kernel)
    · exact v1494_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 79 Primitive.Addresses.material1494
    · exact v1494_mb_checked.trans (by decide +kernel)
    · exact v1494_mg_checked.trans (by decide +kernel)
  upper_error := v1494_upper_checked
  lower_error := reuse_lower_error 16 79 Primitive.Addresses.material1494

def v1495_pa : Scalar.QComplex := ((999999364907158045110830286016 : Int)/10^30,(-1127024968918994463770204718 : Int)/10^30)
theorem v1495_pa_checked : Scalar.distance (sourceCoefficient 16 80 1 0) v1495_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1495_pb : Scalar.QComplex := ((-486285856871426459412659 : Int)/10^30,(-431477173483732866861555350 : Int)/10^30)
theorem v1495_pb_checked : Scalar.distance (sourceCoefficient 16 80 1 1) v1495_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1495_pg : Scalar.QComplex := ((-93086362851276822934917 : Int)/10^30,(104910721827290979073 : Int)/10^30)
theorem v1495_pg_checked : Scalar.distance (sourceCoefficient 16 80 1 2) v1495_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1495_mb : Scalar.QComplex := ((-858631043510932600492176 : Int)/10^30,(-431476593182268719807961697 : Int)/10^30)
theorem v1495_mb_checked : Scalar.distance (sourceCoefficient 16 80 3 1) v1495_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1495_mg : Scalar.QComplex := ((-93086237657741743016306 : Int)/10^30,(185240021450734876226 : Int)/10^30)
theorem v1495_mg_checked : Scalar.distance (sourceCoefficient 16 80 3 2) v1495_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1495_upper : Scalar.QComplex := ((999995930382718745308429412457 : Int)/10^30,(-2852931474943723083875424046 : Int)/10^30)
theorem v1495_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 80 5) 1) 14) v1495_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1495 : Material (16 : Basis) (80 : Basis) where
  plus := ![v1495_pa,v1495_pb,v1495_pg]
  minus := ![(Primitive.Addresses.material1495 1).one,v1495_mb,v1495_mg]
  upper := v1495_upper
  lower := (Primitive.Addresses.material1495 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1495_pa_checked.trans (by decide +kernel)
    · exact v1495_pb_checked.trans (by decide +kernel)
    · exact v1495_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 80 Primitive.Addresses.material1495
    · exact v1495_mb_checked.trans (by decide +kernel)
    · exact v1495_mg_checked.trans (by decide +kernel)
  upper_error := v1495_upper_checked
  lower_error := reuse_lower_error 16 80 Primitive.Addresses.material1495

def v1496_pa : Scalar.QComplex := ((999999334998819566926598805556 : Int)/10^30,(-1153257091302532084719831245 : Int)/10^30)
theorem v1496_pa_checked : Scalar.distance (sourceCoefficient 16 81 1 0) v1496_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1496_pb : Scalar.QComplex := ((-497604421624739003433657 : Int)/10^30,(-431477156715505988191956451 : Int)/10^30)
theorem v1496_pb_checked : Scalar.distance (sourceCoefficient 16 81 1 1) v1496_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1496_pg : Scalar.QComplex := ((-93086359650468260220276 : Int)/10^30,(107352575760030015964 : Int)/10^30)
theorem v1496_pg_checked : Scalar.distance (sourceCoefficient 16 81 1 2) v1496_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1496_mb : Scalar.QComplex := ((-869949589579601619503272 : Int)/10^30,(-431476566646636471839815825 : Int)/10^30)
theorem v1496_mb_checked : Scalar.distance (sourceCoefficient 16 81 3 1) v1496_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1496_mg : Scalar.QComplex := ((-93086232349724405173781 : Int)/10^30,(187681871712106465164 : Int)/10^30)
theorem v1496_mg_checked : Scalar.distance (sourceCoefficient 16 81 3 2) v1496_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1496_upper : Scalar.QComplex := ((999995855200161337648120272092 : Int)/10^30,(-2879163506638516906026305487 : Int)/10^30)
theorem v1496_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 81 5) 1) 14) v1496_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1496 : Material (16 : Basis) (81 : Basis) where
  plus := ![v1496_pa,v1496_pb,v1496_pg]
  minus := ![(Primitive.Addresses.material1496 1).one,v1496_mb,v1496_mg]
  upper := v1496_upper
  lower := (Primitive.Addresses.material1496 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1496_pa_checked.trans (by decide +kernel)
    · exact v1496_pb_checked.trans (by decide +kernel)
    · exact v1496_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 81 Primitive.Addresses.material1496
    · exact v1496_mb_checked.trans (by decide +kernel)
    · exact v1496_mg_checked.trans (by decide +kernel)
  upper_error := v1496_upper_checked
  lower_error := reuse_lower_error 16 81 Primitive.Addresses.material1496

def v1497_pa : Scalar.QComplex := ((999999323485741155847976463646 : Int)/10^30,(-1163197343539247267834240805 : Int)/10^30)
theorem v1497_pa_checked : Scalar.distance (sourceCoefficient 16 82 1 0) v1497_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1497_pb : Scalar.QComplex := ((-501893414516064792738286 : Int)/10^30,(-431477150258019956835820050 : Int)/10^30)
theorem v1497_pb_checked : Scalar.distance (sourceCoefficient 16 82 1 1) v1497_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1497_pg : Scalar.QComplex := ((-93086358418047524096130 : Int)/10^30,(108277878083143568361 : Int)/10^30)
theorem v1497_pg_checked : Scalar.distance (sourceCoefficient 16 82 1 2) v1497_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1497_mb : Scalar.QComplex := ((-874238575301419728022984 : Int)/10^30,(-431476556487945148755746823 : Int)/10^30)
theorem v1497_mb_checked : Scalar.distance (sourceCoefficient 16 82 3 1) v1497_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1497_mg : Scalar.QComplex := ((-93086230318809897158822 : Int)/10^30,(188607172627164085155 : Int)/10^30)
theorem v1497_mg_checked : Scalar.distance (sourceCoefficient 16 82 3 2) v1497_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1497_upper : Scalar.QComplex := ((999995826531126486015617509723 : Int)/10^30,(-2889103724199865167397990567 : Int)/10^30)
theorem v1497_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 82 5) 1) 14) v1497_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1497 : Material (16 : Basis) (82 : Basis) where
  plus := ![v1497_pa,v1497_pb,v1497_pg]
  minus := ![(Primitive.Addresses.material1497 1).one,v1497_mb,v1497_mg]
  upper := v1497_upper
  lower := (Primitive.Addresses.material1497 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1497_pa_checked.trans (by decide +kernel)
    · exact v1497_pb_checked.trans (by decide +kernel)
    · exact v1497_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 82 Primitive.Addresses.material1497
    · exact v1497_mb_checked.trans (by decide +kernel)
    · exact v1497_mg_checked.trans (by decide +kernel)
  upper_error := v1497_upper_checked
  lower_error := reuse_lower_error 16 82 Primitive.Addresses.material1497

def v1498_pa : Scalar.QComplex := ((999999307610703791290414105715 : Int)/10^30,(-1176765955071135488616055215 : Int)/10^30)
theorem v1498_pa_checked : Scalar.distance (sourceCoefficient 16 83 1 0) v1498_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1498_pb : Scalar.QComplex := ((-507747961893335134533613 : Int)/10^30,(-431477141351686887069990528 : Int)/10^30)
theorem v1498_pb_checked : Scalar.distance (sourceCoefficient 16 83 1 1) v1498_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1498_pg : Scalar.QComplex := ((-93086356718451568322015 : Int)/10^30,(109540931312849407137 : Int)/10^30)
theorem v1498_pg_checked : Scalar.distance (sourceCoefficient 16 83 1 2) v1498_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1498_mb : Scalar.QComplex := ((-880093112813010202370433 : Int)/10^30,(-431476542529404687666100461 : Int)/10^30)
theorem v1498_mb_checked : Scalar.distance (sourceCoefficient 16 83 3 1) v1498_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1498_mg : Scalar.QComplex := ((-93086227529256522791583 : Int)/10^30,(189870223919902719254 : Int)/10^30)
theorem v1498_mg_checked : Scalar.distance (sourceCoefficient 16 83 3 2) v1498_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1498_upper : Scalar.QComplex := ((999995787237920196244965456111 : Int)/10^30,(-2902672288124026073420227176 : Int)/10^30)
theorem v1498_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 83 5) 1) 14) v1498_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1498 : Material (16 : Basis) (83 : Basis) where
  plus := ![v1498_pa,v1498_pb,v1498_pg]
  minus := ![(Primitive.Addresses.material1498 1).one,v1498_mb,v1498_mg]
  upper := v1498_upper
  lower := (Primitive.Addresses.material1498 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1498_pa_checked.trans (by decide +kernel)
    · exact v1498_pb_checked.trans (by decide +kernel)
    · exact v1498_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 83 Primitive.Addresses.material1498
    · exact v1498_mb_checked.trans (by decide +kernel)
    · exact v1498_mg_checked.trans (by decide +kernel)
  upper_error := v1498_upper_checked
  lower_error := reuse_lower_error 16 83 Primitive.Addresses.material1498

def v1499_pa : Scalar.QComplex := ((999999265642881366986986389759 : Int)/10^30,(-1211904987193983099436533247 : Int)/10^30)
theorem v1499_pa_checked : Scalar.distance (sourceCoefficient 16 84 1 0) v1499_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1499_pb : Scalar.QComplex := ((-522909654917506015043025 : Int)/10^30,(-431477117794366544507395948 : Int)/10^30)
theorem v1499_pb_checked : Scalar.distance (sourceCoefficient 16 84 1 1) v1499_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1499_pg : Scalar.QComplex := ((-93086352224020507017115 : Int)/10^30,(112811897344206053978 : Int)/10^30)
theorem v1499_pg_checked : Scalar.distance (sourceCoefficient 16 84 1 2) v1499_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1499_mb : Scalar.QComplex := ((-895254779862883373069896 : Int)/10^30,(-431476505888234894015976225 : Int)/10^30)
theorem v1499_mb_checked : Scalar.distance (sourceCoefficient 16 84 3 1) v1499_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1499_mg : Scalar.QComplex := ((-93086220212130768749307 : Int)/10^30,(193141184854837637843 : Int)/10^30)
theorem v1499_mg_checked : Scalar.distance (sourceCoefficient 16 84 3 2) v1499_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1499_upper : Scalar.QComplex := ((999995684623378622140726454213 : Int)/10^30,(-2937811195478758844690591514 : Int)/10^30)
theorem v1499_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 84 5) 1) 14) v1499_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1499 : Material (16 : Basis) (84 : Basis) where
  plus := ![v1499_pa,v1499_pb,v1499_pg]
  minus := ![(Primitive.Addresses.material1499 1).one,v1499_mb,v1499_mg]
  upper := v1499_upper
  lower := (Primitive.Addresses.material1499 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1499_pa_checked.trans (by decide +kernel)
    · exact v1499_pb_checked.trans (by decide +kernel)
    · exact v1499_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 84 Primitive.Addresses.material1499
    · exact v1499_mb_checked.trans (by decide +kernel)
    · exact v1499_mg_checked.trans (by decide +kernel)
  upper_error := v1499_upper_checked
  lower_error := reuse_lower_error 16 84 Primitive.Addresses.material1499

def v1500_pa : Scalar.QComplex := ((999999166708542236798941966734 : Int)/10^30,(-1290961742714224872217677999 : Int)/10^30)
theorem v1500_pa_checked : Scalar.distance (sourceCoefficient 16 85 1 0) v1500_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1500_pb : Scalar.QComplex := ((-557020844316481003634697 : Int)/10^30,(-431477062197555029521755109 : Int)/10^30)
theorem v1500_pb_checked : Scalar.distance (sourceCoefficient 16 85 1 1) v1500_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1500_pg : Scalar.QComplex := ((-93086341622104367022264 : Int)/10^30,(120171005940836261117 : Int)/10^30)
theorem v1500_pg_checked : Scalar.distance (sourceCoefficient 16 85 1 2) v1500_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1500_mb : Scalar.QComplex := ((-929365908583159240059183 : Int)/10^30,(-431476420855023939888734067 : Int)/10^30)
theorem v1500_mb_checked : Scalar.distance (sourceCoefficient 16 85 3 1) v1500_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1500_mg : Scalar.QComplex := ((-93086203259639299387986 : Int)/10^30,(200500281562359250341 : Int)/10^30)
theorem v1500_mg_checked : Scalar.distance (sourceCoefficient 16 85 3 2) v1500_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1500_upper : Scalar.QComplex := ((999995449244398787928291839052 : Int)/10^30,(-3016867662501555843357723719 : Int)/10^30)
theorem v1500_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 85 5) 1) 14) v1500_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1500 : Material (16 : Basis) (85 : Basis) where
  plus := ![v1500_pa,v1500_pb,v1500_pg]
  minus := ![(Primitive.Addresses.material1500 1).one,v1500_mb,v1500_mg]
  upper := v1500_upper
  lower := (Primitive.Addresses.material1500 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1500_pa_checked.trans (by decide +kernel)
    · exact v1500_pb_checked.trans (by decide +kernel)
    · exact v1500_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 85 Primitive.Addresses.material1500
    · exact v1500_mb_checked.trans (by decide +kernel)
    · exact v1500_mg_checked.trans (by decide +kernel)
  upper_error := v1500_upper_checked
  lower_error := reuse_lower_error 16 85 Primitive.Addresses.material1500

def v1501_pa : Scalar.QComplex := ((999999147773968839343421754562 : Int)/10^30,(-1305546374523748952778358115 : Int)/10^30)
theorem v1501_pa_checked : Scalar.distance (sourceCoefficient 16 86 1 0) v1501_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1501_pb : Scalar.QComplex := ((-563313780409396888668874 : Int)/10^30,(-431477051548031688966085537 : Int)/10^30)
theorem v1501_pb_checked : Scalar.distance (sourceCoefficient 16 86 1 1) v1501_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1501_pg : Scalar.QComplex := ((-93086339592070901284236 : Int)/10^30,(121528636741982440187 : Int)/10^30)
theorem v1501_pg_checked : Scalar.distance (sourceCoefficient 16 86 1 2) v1501_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1501_mb : Scalar.QComplex := ((-935658833142868410140297 : Int)/10^30,(-431476404774984139771359385 : Int)/10^30)
theorem v1501_mb_checked : Scalar.distance (sourceCoefficient 16 86 3 1) v1501_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1501_mg : Scalar.QComplex := ((-93086200058032353556501 : Int)/10^30,(201857910106169983732 : Int)/10^30)
theorem v1501_mg_checked : Scalar.distance (sourceCoefficient 16 86 3 2) v1501_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1501_upper : Scalar.QComplex := ((999995405138102195519284583615 : Int)/10^30,(-3031452239909628121904770850 : Int)/10^30)
theorem v1501_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 86 5) 1) 14) v1501_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1501 : Material (16 : Basis) (86 : Basis) where
  plus := ![v1501_pa,v1501_pb,v1501_pg]
  minus := ![(Primitive.Addresses.material1501 1).one,v1501_mb,v1501_mg]
  upper := v1501_upper
  lower := (Primitive.Addresses.material1501 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1501_pa_checked.trans (by decide +kernel)
    · exact v1501_pb_checked.trans (by decide +kernel)
    · exact v1501_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 86 Primitive.Addresses.material1501
    · exact v1501_mb_checked.trans (by decide +kernel)
    · exact v1501_mg_checked.trans (by decide +kernel)
  upper_error := v1501_upper_checked
  lower_error := reuse_lower_error 16 86 Primitive.Addresses.material1501

def v1502_pa : Scalar.QComplex := ((999999146512662677532244350729 : Int)/10^30,(-1306512130140512909544489333 : Int)/10^30)
theorem v1502_pa_checked : Scalar.distance (sourceCoefficient 16 87 1 0) v1502_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1502_pb : Scalar.QComplex := ((-563730481934620363726563 : Int)/10^30,(-431477050838528589873038396 : Int)/10^30)
theorem v1502_pb_checked : Scalar.distance (sourceCoefficient 16 87 1 1) v1502_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1502_pg : Scalar.QComplex := ((-93086339456831993656883 : Int)/10^30,(121618535450608434279 : Int)/10^30)
theorem v1502_pg_checked : Scalar.distance (sourceCoefficient 16 87 1 2) v1502_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1502_mb : Scalar.QComplex := ((-936075533900665643472845 : Int)/10^30,(-431476403705886656130895187 : Int)/10^30)
theorem v1502_mb_checked : Scalar.distance (sourceCoefficient 16 87 3 1) v1502_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1502_mg : Scalar.QComplex := ((-93086199845214959628076 : Int)/10^30,(201947808664617493681 : Int)/10^30)
theorem v1502_mg_checked : Scalar.distance (sourceCoefficient 16 87 3 2) v1502_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1502_upper : Scalar.QComplex := ((999995402209991330406042633798 : Int)/10^30,(-3032417991911112522639923804 : Int)/10^30)
theorem v1502_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 87 5) 1) 14) v1502_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1502 : Material (16 : Basis) (87 : Basis) where
  plus := ![v1502_pa,v1502_pb,v1502_pg]
  minus := ![(Primitive.Addresses.material1502 1).one,v1502_mb,v1502_mg]
  upper := v1502_upper
  lower := (Primitive.Addresses.material1502 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1502_pa_checked.trans (by decide +kernel)
    · exact v1502_pb_checked.trans (by decide +kernel)
    · exact v1502_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 87 Primitive.Addresses.material1502
    · exact v1502_mb_checked.trans (by decide +kernel)
    · exact v1502_mg_checked.trans (by decide +kernel)
  upper_error := v1502_upper_checked
  lower_error := reuse_lower_error 16 87 Primitive.Addresses.material1502

def v1503_pa : Scalar.QComplex := ((999999131079467090897672351532 : Int)/10^30,(-1318271713568683132676439945 : Int)/10^30)
theorem v1503_pa_checked : Scalar.distance (sourceCoefficient 16 88 1 0) v1503_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1503_pb : Scalar.QComplex := ((-568804473974653467479018 : Int)/10^30,(-431477042156174297225600716 : Int)/10^30)
theorem v1503_pb_checked : Scalar.distance (sourceCoefficient 16 88 1 1) v1503_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1503_pg : Scalar.QComplex := ((-93086337801961225495847 : Int)/10^30,(122713192672037481249 : Int)/10^30)
theorem v1503_pg_checked : Scalar.distance (sourceCoefficient 16 88 1 2) v1503_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1503_mb : Scalar.QComplex := ((-941149516558938901995568 : Int)/10^30,(-431476390644908989890464379 : Int)/10^30)
theorem v1503_mb_checked : Scalar.distance (sourceCoefficient 16 88 3 1) v1503_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1503_mg : Scalar.QComplex := ((-93086197245704927088885 : Int)/10^30,(203042464050376688496 : Int)/10^30)
theorem v1503_mg_checked : Scalar.distance (sourceCoefficient 16 88 3 2) v1503_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1503_upper : Scalar.QComplex := ((999995366480844553756635993499 : Int)/10^30,(-3044177531188469113253747799 : Int)/10^30)
theorem v1503_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 88 5) 1) 14) v1503_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1503 : Material (16 : Basis) (88 : Basis) where
  plus := ![v1503_pa,v1503_pb,v1503_pg]
  minus := ![(Primitive.Addresses.material1503 1).one,v1503_mb,v1503_mg]
  upper := v1503_upper
  lower := (Primitive.Addresses.material1503 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1503_pa_checked.trans (by decide +kernel)
    · exact v1503_pb_checked.trans (by decide +kernel)
    · exact v1503_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 88 Primitive.Addresses.material1503
    · exact v1503_mb_checked.trans (by decide +kernel)
    · exact v1503_mg_checked.trans (by decide +kernel)
  upper_error := v1503_upper_checked
  lower_error := reuse_lower_error 16 88 Primitive.Addresses.material1503

def v1504_pa : Scalar.QComplex := ((999999109739719109744517239311 : Int)/10^30,(-1334361183944265981706524187 : Int)/10^30)
theorem v1504_pa_checked : Scalar.distance (sourceCoefficient 16 89 1 0) v1504_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1504_pb : Scalar.QComplex := ((-575746713357579659835482 : Int)/10^30,(-431477030148080846127710349 : Int)/10^30)
theorem v1504_pb_checked : Scalar.distance (sourceCoefficient 16 89 1 1) v1504_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1504_pg : Scalar.QComplex := ((-93086335513435077482802 : Int)/10^30,(124210903444774192748 : Int)/10^30)
theorem v1504_pg_checked : Scalar.distance (sourceCoefficient 16 89 1 2) v1504_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1504_mb : Scalar.QComplex := ((-948091742994508272230268 : Int)/10^30,(-431476372645980089344326590 : Int)/10^30)
theorem v1504_mb_checked : Scalar.distance (sourceCoefficient 16 89 3 1) v1504_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1504_mg : Scalar.QComplex := ((-93086193664722688716113 : Int)/10^30,(204540172290552236198 : Int)/10^30)
theorem v1504_mg_checked : Scalar.distance (sourceCoefficient 16 89 3 2) v1504_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1504_upper : Scalar.QComplex := ((999995317372162112745863855577 : Int)/10^30,(-3060266940770206751152764662 : Int)/10^30)
theorem v1504_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 89 5) 1) 14) v1504_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1504 : Material (16 : Basis) (89 : Basis) where
  plus := ![v1504_pa,v1504_pb,v1504_pg]
  minus := ![(Primitive.Addresses.material1504 1).one,v1504_mb,v1504_mg]
  upper := v1504_upper
  lower := (Primitive.Addresses.material1504 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1504_pa_checked.trans (by decide +kernel)
    · exact v1504_pb_checked.trans (by decide +kernel)
    · exact v1504_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 89 Primitive.Addresses.material1504
    · exact v1504_mb_checked.trans (by decide +kernel)
    · exact v1504_mg_checked.trans (by decide +kernel)
  upper_error := v1504_upper_checked
  lower_error := reuse_lower_error 16 89 Primitive.Addresses.material1504

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
