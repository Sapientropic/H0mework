import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B078

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1873_pa : Scalar.QComplex := ((999999439063167067068753258202 : Int)/10^30,(-1059185229889339021770596874 : Int)/10^30)
theorem v1873_pa_checked : Scalar.distance (sourceCoefficient 21 68 1 0) v1873_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1873_pb : Scalar.QComplex := ((-457014575325664016108078 : Int)/10^30,(-431477239365491550645458547 : Int)/10^30)
theorem v1873_pb_checked : Scalar.distance (sourceCoefficient 21 68 1 1) v1873_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1873_pg : Scalar.QComplex := ((-93086373409360762120606 : Int)/10^30,(98595767125155985616 : Int)/10^30)
theorem v1873_pg_checked : Scalar.distance (sourceCoefficient 21 68 1 2) v1873_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1873_mb : Scalar.QComplex := ((-829359829717196580170650 : Int)/10^30,(-431476684323800517213023709 : Int)/10^30)
theorem v1873_mb_checked : Scalar.distance (sourceCoefficient 21 68 3 1) v1873_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1873_mg : Scalar.QComplex := ((-93086253665343243885513 : Int)/10^30,(178925078211097047130 : Int)/10^30)
theorem v1873_mg_checked : Scalar.distance (sourceCoefficient 21 68 3 2) v1873_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1873_upper : Scalar.QComplex := ((999996121623852512737737426240 : Int)/10^30,(-2785091964939934102320680269 : Int)/10^30)
theorem v1873_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 68 5) 1) 14) v1873_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1873 : Material (21 : Basis) (68 : Basis) where
  plus := ![v1873_pa,v1873_pb,v1873_pg]
  minus := ![(Primitive.Addresses.material1873 1).one,v1873_mb,v1873_mg]
  upper := v1873_upper
  lower := (Primitive.Addresses.material1873 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1873_pa_checked.trans (by decide +kernel)
    · exact v1873_pb_checked.trans (by decide +kernel)
    · exact v1873_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 68 Primitive.Addresses.material1873
    · exact v1873_mb_checked.trans (by decide +kernel)
    · exact v1873_mg_checked.trans (by decide +kernel)
  upper_error := v1873_upper_checked
  lower_error := reuse_lower_error 21 68 Primitive.Addresses.material1873

def v1874_pa : Scalar.QComplex := ((999999415913239031046841661747 : Int)/10^30,(-1080820605272013667059711482 : Int)/10^30)
theorem v1874_pa_checked : Scalar.distance (sourceCoefficient 21 69 1 0) v1874_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1874_pb : Scalar.QComplex := ((-466349750072627279307788 : Int)/10^30,(-431477227033939252044362461 : Int)/10^30)
theorem v1874_pb_checked : Scalar.distance (sourceCoefficient 21 69 1 1) v1874_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1874_pg : Scalar.QComplex := ((-93086371001691717189772 : Int)/10^30,(100609726613433002538 : Int)/10^30)
theorem v1874_pg_checked : Scalar.distance (sourceCoefficient 21 69 1 2) v1874_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1874_mb : Scalar.QComplex := ((-838694990346673405319273 : Int)/10^30,(-431476663936417444246244207 : Int)/10^30)
theorem v1874_mb_checked : Scalar.distance (sourceCoefficient 21 69 3 1) v1874_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1874_mg : Scalar.QComplex := ((-93086249519718762425045 : Int)/10^30,(180939034871774955683 : Int)/10^30)
theorem v1874_mg_checked : Scalar.distance (sourceCoefficient 21 69 3 2) v1874_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1874_upper : Scalar.QComplex := ((999996061133263791240402641352 : Int)/10^30,(-2806727268144582939729045910 : Int)/10^30)
theorem v1874_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 69 5) 1) 14) v1874_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1874 : Material (21 : Basis) (69 : Basis) where
  plus := ![v1874_pa,v1874_pb,v1874_pg]
  minus := ![(Primitive.Addresses.material1874 1).one,v1874_mb,v1874_mg]
  upper := v1874_upper
  lower := (Primitive.Addresses.material1874 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1874_pa_checked.trans (by decide +kernel)
    · exact v1874_pb_checked.trans (by decide +kernel)
    · exact v1874_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 69 Primitive.Addresses.material1874
    · exact v1874_mb_checked.trans (by decide +kernel)
    · exact v1874_mg_checked.trans (by decide +kernel)
  upper_error := v1874_upper_checked
  lower_error := reuse_lower_error 21 69 Primitive.Addresses.material1874

def v1875_pa : Scalar.QComplex := ((999999400429762376142859222490 : Int)/10^30,(-1095052563013869411045938349 : Int)/10^30)
theorem v1875_pa_checked : Scalar.distance (sourceCoefficient 21 70 1 0) v1875_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1875_pb : Scalar.QComplex := ((-472490517593229471675054 : Int)/10^30,(-431477218775290176074455480 : Int)/10^30)
theorem v1875_pb_checked : Scalar.distance (sourceCoefficient 21 70 1 1) v1875_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1875_pg : Scalar.QComplex := ((-93086369390185534311764 : Int)/10^30,(101934528499287943907 : Int)/10^30)
theorem v1875_pg_checked : Scalar.distance (sourceCoefficient 21 70 1 2) v1875_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1875_mb : Scalar.QComplex := ((-844835748453945006011116 : Int)/10^30,(-431476650378565642971505658 : Int)/10^30)
theorem v1875_mb_checked : Scalar.distance (sourceCoefficient 21 70 3 1) v1875_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1875_mg : Scalar.QComplex := ((-93086246764968818953625 : Int)/10^30,(182263834873688352232 : Int)/10^30)
theorem v1875_mg_checked : Scalar.distance (sourceCoefficient 21 70 3 2) v1875_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1875_upper : Scalar.QComplex := ((999996021086742247833785565303 : Int)/10^30,(-2820959177966533374080604964 : Int)/10^30)
theorem v1875_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 70 5) 1) 14) v1875_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1875 : Material (21 : Basis) (70 : Basis) where
  plus := ![v1875_pa,v1875_pb,v1875_pg]
  minus := ![(Primitive.Addresses.material1875 1).one,v1875_mb,v1875_mg]
  upper := v1875_upper
  lower := (Primitive.Addresses.material1875 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1875_pa_checked.trans (by decide +kernel)
    · exact v1875_pb_checked.trans (by decide +kernel)
    · exact v1875_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 70 Primitive.Addresses.material1875
    · exact v1875_mb_checked.trans (by decide +kernel)
    · exact v1875_mg_checked.trans (by decide +kernel)
  upper_error := v1875_upper_checked
  lower_error := reuse_lower_error 21 70 Primitive.Addresses.material1875

def v1876_pa : Scalar.QComplex := ((999999373532781109524019979081 : Int)/10^30,(-1119345364630494914560064495 : Int)/10^30)
theorem v1876_pa_checked : Scalar.distance (sourceCoefficient 21 71 1 0) v1876_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1876_pb : Scalar.QComplex := ((-482972311265525219835196 : Int)/10^30,(-431477204409237538136345960 : Int)/10^30)
theorem v1876_pb_checked : Scalar.distance (sourceCoefficient 21 71 1 1) v1876_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1876_pg : Scalar.QComplex := ((-93086366588656283506199 : Int)/10^30,(104195858226596909804 : Int)/10^30)
theorem v1876_pg_checked : Scalar.distance (sourceCoefficient 21 71 1 2) v1876_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1876_mb : Scalar.QComplex := ((-855317525826133524791192 : Int)/10^30,(-431476626967202497442599067 : Int)/10^30)
theorem v1876_mb_checked : Scalar.distance (sourceCoefficient 21 71 3 1) v1876_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1876_mg : Scalar.QComplex := ((-93086242012014903127997 : Int)/10^30,(184525161341407345526 : Int)/10^30)
theorem v1876_mg_checked : Scalar.distance (sourceCoefficient 21 71 3 2) v1876_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1876_upper : Scalar.QComplex := ((999995952262629276560700797922 : Int)/10^30,(-2845251896980134911461283540 : Int)/10^30)
theorem v1876_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 71 5) 1) 14) v1876_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1876 : Material (21 : Basis) (71 : Basis) where
  plus := ![v1876_pa,v1876_pb,v1876_pg]
  minus := ![(Primitive.Addresses.material1876 1).one,v1876_mb,v1876_mg]
  upper := v1876_upper
  lower := (Primitive.Addresses.material1876 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1876_pa_checked.trans (by decide +kernel)
    · exact v1876_pb_checked.trans (by decide +kernel)
    · exact v1876_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 71 Primitive.Addresses.material1876
    · exact v1876_mb_checked.trans (by decide +kernel)
    · exact v1876_mg_checked.trans (by decide +kernel)
  upper_error := v1876_upper_checked
  lower_error := reuse_lower_error 21 71 Primitive.Addresses.material1876

def v1877_pa : Scalar.QComplex := ((999999343676403895791194493640 : Int)/10^30,(-1145707973895510080407798086 : Int)/10^30)
theorem v1877_pa_checked : Scalar.distance (sourceCoefficient 21 72 1 0) v1877_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1877_pb : Scalar.QComplex := ((-494347179795746044679728 : Int)/10^30,(-431477188435028116411847872 : Int)/10^30)
theorem v1877_pb_checked : Scalar.distance (sourceCoefficient 21 72 1 1) v1877_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1877_pg : Scalar.QComplex := ((-93086363475916346466912 : Int)/10^30,(106649858892112040547 : Int)/10^30)
theorem v1877_pg_checked : Scalar.distance (sourceCoefficient 21 72 1 2) v1877_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1877_mb : Scalar.QComplex := ((-866692376335947659398025 : Int)/10^30,(-431476601176999787126697633 : Int)/10^30)
theorem v1877_mb_checked : Scalar.distance (sourceCoefficient 21 72 3 1) v1877_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1877_mg : Scalar.QComplex := ((-93086236781584074851618 : Int)/10^30,(186979158407031502064 : Int)/10^30)
theorem v1877_mg_checked : Scalar.distance (sourceCoefficient 21 72 3 2) v1877_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1877_upper : Scalar.QComplex := ((999995876906824536208772338509 : Int)/10^30,(-2871614415451741825169343766 : Int)/10^30)
theorem v1877_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 72 5) 1) 14) v1877_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1877 : Material (21 : Basis) (72 : Basis) where
  plus := ![v1877_pa,v1877_pb,v1877_pg]
  minus := ![(Primitive.Addresses.material1877 1).one,v1877_mb,v1877_mg]
  upper := v1877_upper
  lower := (Primitive.Addresses.material1877 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1877_pa_checked.trans (by decide +kernel)
    · exact v1877_pb_checked.trans (by decide +kernel)
    · exact v1877_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 72 Primitive.Addresses.material1877
    · exact v1877_mb_checked.trans (by decide +kernel)
    · exact v1877_mg_checked.trans (by decide +kernel)
  upper_error := v1877_upper_checked
  lower_error := reuse_lower_error 21 72 Primitive.Addresses.material1877

def v1878_pa : Scalar.QComplex := ((999999332805225140421654208787 : Int)/10^30,(-1155157610272420397933739646 : Int)/10^30)
theorem v1878_pa_checked : Scalar.distance (sourceCoefficient 21 73 1 0) v1878_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1878_pb : Scalar.QComplex := ((-498424483699079874549186 : Int)/10^30,(-431477182611752436668437939 : Int)/10^30)
theorem v1878_pb_checked : Scalar.distance (sourceCoefficient 21 73 1 1) v1878_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1878_pg : Scalar.QComplex := ((-93086362341783567385250 : Int)/10^30,(107529491614802281412 : Int)/10^30)
theorem v1878_pg_checked : Scalar.distance (sourceCoefficient 21 73 1 2) v1878_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1878_mb : Scalar.QComplex := ((-870769673695890263044545 : Int)/10^30,(-431476591835196642028821285 : Int)/10^30)
theorem v1878_mb_checked : Scalar.distance (sourceCoefficient 21 73 3 1) v1878_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1878_mg : Scalar.QComplex := ((-93086234888368295564915 : Int)/10^30,(187858789823488770168 : Int)/10^30)
theorem v1878_mg_checked : Scalar.distance (sourceCoefficient 21 73 3 2) v1878_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1878_upper : Scalar.QComplex := ((999995849726446849951293733240 : Int)/10^30,(-2881064018991860485416601659 : Int)/10^30)
theorem v1878_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 73 5) 1) 14) v1878_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1878 : Material (21 : Basis) (73 : Basis) where
  plus := ![v1878_pa,v1878_pb,v1878_pg]
  minus := ![(Primitive.Addresses.material1878 1).one,v1878_mb,v1878_mg]
  upper := v1878_upper
  lower := (Primitive.Addresses.material1878 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1878_pa_checked.trans (by decide +kernel)
    · exact v1878_pb_checked.trans (by decide +kernel)
    · exact v1878_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 73 Primitive.Addresses.material1878
    · exact v1878_mb_checked.trans (by decide +kernel)
    · exact v1878_mg_checked.trans (by decide +kernel)
  upper_error := v1878_upper_checked
  lower_error := reuse_lower_error 21 73 Primitive.Addresses.material1878

def v1879_pa : Scalar.QComplex := ((999999320465704916891697587292 : Int)/10^30,(-1165790773852391752890437097 : Int)/10^30)
theorem v1879_pa_checked : Scalar.distance (sourceCoefficient 21 74 1 0) v1879_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1879_pb : Scalar.QComplex := ((-503012452720227092975455 : Int)/10^30,(-431477175997709693083743797 : Int)/10^30)
theorem v1879_pb_checked : Scalar.distance (sourceCoefficient 21 74 1 1) v1879_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1879_pg : Scalar.QComplex := ((-93086361054009898351470 : Int)/10^30,(108519294630839720502 : Int)/10^30)
theorem v1879_pg_checked : Scalar.distance (sourceCoefficient 21 74 1 2) v1879_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1879_mb : Scalar.QComplex := ((-875357635301105932068563 : Int)/10^30,(-431476581261945730358548737 : Int)/10^30)
theorem v1879_mb_checked : Scalar.distance (sourceCoefficient 21 74 3 1) v1879_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1879_mg : Scalar.QComplex := ((-93086232746439682260805 : Int)/10^30,(188848591359686632951 : Int)/10^30)
theorem v1879_mg_checked : Scalar.distance (sourceCoefficient 21 74 3 2) v1879_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1879_upper : Scalar.QComplex := ((999995819035069298721324562167 : Int)/10^30,(-2891697145438091273859134533 : Int)/10^30)
theorem v1879_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 74 5) 1) 14) v1879_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1879 : Material (21 : Basis) (74 : Basis) where
  plus := ![v1879_pa,v1879_pb,v1879_pg]
  minus := ![(Primitive.Addresses.material1879 1).one,v1879_mb,v1879_mg]
  upper := v1879_upper
  lower := (Primitive.Addresses.material1879 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1879_pa_checked.trans (by decide +kernel)
    · exact v1879_pb_checked.trans (by decide +kernel)
    · exact v1879_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 74 Primitive.Addresses.material1879
    · exact v1879_mb_checked.trans (by decide +kernel)
    · exact v1879_mg_checked.trans (by decide +kernel)
  upper_error := v1879_upper_checked
  lower_error := reuse_lower_error 21 74 Primitive.Addresses.material1879

def v1880_pa : Scalar.QComplex := ((999999303084620336149884326668 : Int)/10^30,(-1180605892597802435404474698 : Int)/10^30)
theorem v1880_pa_checked : Scalar.distance (sourceCoefficient 21 75 1 0) v1880_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1880_pb : Scalar.QComplex := ((-509404840508744299316301 : Int)/10^30,(-431477166673955894930125950 : Int)/10^30)
theorem v1880_pb_checked : Scalar.distance (sourceCoefficient 21 75 1 1) v1880_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1880_pg : Scalar.QComplex := ((-93086359239290749073391 : Int)/10^30,(109898380828254347879 : Int)/10^30)
theorem v1880_pg_checked : Scalar.distance (sourceCoefficient 21 75 1 2) v1880_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1880_mb : Scalar.QComplex := ((-881750012663465416666286 : Int)/10^30,(-431476566421852644832790656 : Int)/10^30)
theorem v1880_mb_checked : Scalar.distance (sourceCoefficient 21 75 3 1) v1880_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1880_mg : Scalar.QComplex := ((-93086229741631932053414 : Int)/10^30,(190227675477583547767 : Int)/10^30)
theorem v1880_mg_checked : Scalar.distance (sourceCoefficient 21 75 3 2) v1880_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1880_upper : Scalar.QComplex := ((999995776084459667558129118305 : Int)/10^30,(-2906512212119947704497144236 : Int)/10^30)
theorem v1880_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 75 5) 1) 14) v1880_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1880 : Material (21 : Basis) (75 : Basis) where
  plus := ![v1880_pa,v1880_pb,v1880_pg]
  minus := ![(Primitive.Addresses.material1880 1).one,v1880_mb,v1880_mg]
  upper := v1880_upper
  lower := (Primitive.Addresses.material1880 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1880_pa_checked.trans (by decide +kernel)
    · exact v1880_pb_checked.trans (by decide +kernel)
    · exact v1880_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 75 Primitive.Addresses.material1880
    · exact v1880_mb_checked.trans (by decide +kernel)
    · exact v1880_mg_checked.trans (by decide +kernel)
  upper_error := v1880_upper_checked
  lower_error := reuse_lower_error 21 75 Primitive.Addresses.material1880

def v1881_pa : Scalar.QComplex := ((999999288332216021587236625217 : Int)/10^30,(-1193036068811748362559084281 : Int)/10^30)
theorem v1881_pa_checked : Scalar.distance (sourceCoefficient 21 76 1 0) v1881_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1881_pb : Scalar.QComplex := ((-514768179605537094890852 : Int)/10^30,(-431477158753725604309821596 : Int)/10^30)
theorem v1881_pb_checked : Scalar.distance (sourceCoefficient 21 76 1 1) v1881_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1881_pg : Scalar.QComplex := ((-93086357698316048733611 : Int)/10^30,(111055461282997237412 : Int)/10^30)
theorem v1881_pg_checked : Scalar.distance (sourceCoefficient 21 76 1 2) v1881_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1881_mb : Scalar.QComplex := ((-887113342928439922924268 : Int)/10^30,(-431476553873305218569959117 : Int)/10^30)
theorem v1881_mb_checked : Scalar.distance (sourceCoefficient 21 76 3 1) v1881_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1881_mg : Scalar.QComplex := ((-93086227202149486014985 : Int)/10^30,(191384754171700739341 : Int)/10^30)
theorem v1881_mg_checked : Scalar.distance (sourceCoefficient 21 76 3 2) v1881_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1881_upper : Scalar.QComplex := ((999995739878720836475456386928 : Int)/10^30,(-2918942344359294792777248819 : Int)/10^30)
theorem v1881_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 76 5) 1) 14) v1881_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1881 : Material (21 : Basis) (76 : Basis) where
  plus := ![v1881_pa,v1881_pb,v1881_pg]
  minus := ![(Primitive.Addresses.material1881 1).one,v1881_mb,v1881_mg]
  upper := v1881_upper
  lower := (Primitive.Addresses.material1881 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1881_pa_checked.trans (by decide +kernel)
    · exact v1881_pb_checked.trans (by decide +kernel)
    · exact v1881_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 76 Primitive.Addresses.material1881
    · exact v1881_mb_checked.trans (by decide +kernel)
    · exact v1881_mg_checked.trans (by decide +kernel)
  upper_error := v1881_upper_checked
  lower_error := reuse_lower_error 21 76 Primitive.Addresses.material1881

def v1882_pa : Scalar.QComplex := ((999999284894883405466754997662 : Int)/10^30,(-1195913760190816898990809533 : Int)/10^30)
theorem v1882_pa_checked : Scalar.distance (sourceCoefficient 21 77 1 0) v1882_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1882_pb : Scalar.QComplex := ((-516009838154911372369191 : Int)/10^30,(-431477156907453562210550492 : Int)/10^30)
theorem v1882_pb_checked : Scalar.distance (sourceCoefficient 21 77 1 1) v1882_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1882_pg : Scalar.QComplex := ((-93086357339175307067709 : Int)/10^30,(111323335235845810342 : Int)/10^30)
theorem v1882_pg_checked : Scalar.distance (sourceCoefficient 21 77 1 2) v1882_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1882_mb : Scalar.QComplex := ((-888354999422238356545838 : Int)/10^30,(-431476550955538458037279865 : Int)/10^30)
theorem v1882_mb_checked : Scalar.distance (sourceCoefficient 21 77 3 1) v1882_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1882_mg : Scalar.QComplex := ((-93086226611845721360254 : Int)/10^30,(191652627714885312222 : Int)/10^30)
theorem v1882_mg_checked : Scalar.distance (sourceCoefficient 21 77 3 2) v1882_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1882_upper : Scalar.QComplex := ((999995731474759081708438846408 : Int)/10^30,(-2921820025519855794416687216 : Int)/10^30)
theorem v1882_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 77 5) 1) 14) v1882_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1882 : Material (21 : Basis) (77 : Basis) where
  plus := ![v1882_pa,v1882_pb,v1882_pg]
  minus := ![(Primitive.Addresses.material1882 1).one,v1882_mb,v1882_mg]
  upper := v1882_upper
  lower := (Primitive.Addresses.material1882 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1882_pa_checked.trans (by decide +kernel)
    · exact v1882_pb_checked.trans (by decide +kernel)
    · exact v1882_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 77 Primitive.Addresses.material1882
    · exact v1882_mb_checked.trans (by decide +kernel)
    · exact v1882_mg_checked.trans (by decide +kernel)
  upper_error := v1882_upper_checked
  lower_error := reuse_lower_error 21 77 Primitive.Addresses.material1882

def v1883_pa : Scalar.QComplex := ((999999264056428786169056098163 : Int)/10^30,(-1213213336892865630368988929 : Int)/10^30)
theorem v1883_pa_checked : Scalar.distance (sourceCoefficient 21 78 1 0) v1883_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1883_pb : Scalar.QComplex := ((-523474212984853521896556 : Int)/10^30,(-431477145707966950489856460 : Int)/10^30)
theorem v1883_pb_checked : Scalar.distance (sourceCoefficient 21 78 1 1) v1883_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1883_pg : Scalar.QComplex := ((-93086355161204894336230 : Int)/10^30,(112933690677143442112 : Int)/10^30)
theorem v1883_pg_checked : Scalar.distance (sourceCoefficient 21 78 1 2) v1883_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1883_mb : Scalar.QComplex := ((-895819361808200078341012 : Int)/10^30,(-431476533314636721119860565 : Int)/10^30)
theorem v1883_mb_checked : Scalar.distance (sourceCoefficient 21 78 3 1) v1883_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1883_mg : Scalar.QComplex := ((-93086223044211901463562 : Int)/10^30,(193262980677083642276 : Int)/10^30)
theorem v1883_mg_checked : Scalar.distance (sourceCoefficient 21 78 3 2) v1883_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1883_upper : Scalar.QComplex := ((999995680778835516443816336293 : Int)/10^30,(-2939119540490934956051378582 : Int)/10^30)
theorem v1883_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 78 5) 1) 14) v1883_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1883 : Material (21 : Basis) (78 : Basis) where
  plus := ![v1883_pa,v1883_pb,v1883_pg]
  minus := ![(Primitive.Addresses.material1883 1).one,v1883_mb,v1883_mg]
  upper := v1883_upper
  lower := (Primitive.Addresses.material1883 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1883_pa_checked.trans (by decide +kernel)
    · exact v1883_pb_checked.trans (by decide +kernel)
    · exact v1883_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 78 Primitive.Addresses.material1883
    · exact v1883_mb_checked.trans (by decide +kernel)
    · exact v1883_mg_checked.trans (by decide +kernel)
  upper_error := v1883_upper_checked
  lower_error := reuse_lower_error 21 78 Primitive.Addresses.material1883

def v1884_pa : Scalar.QComplex := ((999999257274687746072571910228 : Int)/10^30,(-1218790413839461322453333379 : Int)/10^30)
theorem v1884_pa_checked : Scalar.distance (sourceCoefficient 21 79 1 0) v1884_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1884_pb : Scalar.QComplex := ((-525880595119319842964100 : Int)/10^30,(-431477142060750893355921468 : Int)/10^30)
theorem v1884_pb_checked : Scalar.distance (sourceCoefficient 21 79 1 1) v1884_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1884_pg : Scalar.QComplex := ((-93086354452137907978394 : Int)/10^30,(113452840729824500963 : Int)/10^30)
theorem v1884_pg_checked : Scalar.distance (sourceCoefficient 21 79 1 2) v1884_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1884_mb : Scalar.QComplex := ((-898225739899277160857062 : Int)/10^30,(-431476527590822619394817449 : Int)/10^30)
theorem v1884_mb_checked : Scalar.distance (sourceCoefficient 21 79 3 1) v1884_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1884_mg : Scalar.QComplex := ((-93086221887142065310422 : Int)/10^30,(193782129924568536149 : Int)/10^30)
theorem v1884_mg_checked : Scalar.distance (sourceCoefficient 21 79 3 2) v1884_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1884_upper : Scalar.QComplex := ((999995664371575715598150190821 : Int)/10^30,(-2944696597426459865194598438 : Int)/10^30)
theorem v1884_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 79 5) 1) 14) v1884_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1884 : Material (21 : Basis) (79 : Basis) where
  plus := ![v1884_pa,v1884_pb,v1884_pg]
  minus := ![(Primitive.Addresses.material1884 1).one,v1884_mb,v1884_mg]
  upper := v1884_upper
  lower := (Primitive.Addresses.material1884 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1884_pa_checked.trans (by decide +kernel)
    · exact v1884_pb_checked.trans (by decide +kernel)
    · exact v1884_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 79 Primitive.Addresses.material1884
    · exact v1884_mb_checked.trans (by decide +kernel)
    · exact v1884_mg_checked.trans (by decide +kernel)
  upper_error := v1884_upper_checked
  lower_error := reuse_lower_error 21 79 Primitive.Addresses.material1884

def v1885_pa : Scalar.QComplex := ((999999246618695286014093426845 : Int)/10^30,(-1227502359201228387031610333 : Int)/10^30)
theorem v1885_pa_checked : Scalar.distance (sourceCoefficient 21 80 1 0) v1885_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1885_pb : Scalar.QComplex := ((-529639601804130771285521 : Int)/10^30,(-431477136327630542426753076 : Int)/10^30)
theorem v1885_pb_checked : Scalar.distance (sourceCoefficient 21 80 1 1) v1885_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1885_pg : Scalar.QComplex := ((-93086353337745590271127 : Int)/10^30,(114263804415735904847 : Int)/10^30)
theorem v1885_pg_checked : Scalar.distance (sourceCoefficient 21 80 1 2) v1885_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1885_mb : Scalar.QComplex := ((-901984740237013452634550 : Int)/10^30,(-431476518613850933552936728 : Int)/10^30)
theorem v1885_mb_checked : Scalar.distance (sourceCoefficient 21 80 3 1) v1885_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1885_mg : Scalar.QComplex := ((-93086220072925026049366 : Int)/10^30,(194593092346850717083 : Int)/10^30)
theorem v1885_mg_checked : Scalar.distance (sourceCoefficient 21 80 3 2) v1885_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1885_upper : Scalar.QComplex := ((999995638679571773488157143376 : Int)/10^30,(-2953408511421531408434903297 : Int)/10^30)
theorem v1885_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 80 5) 1) 14) v1885_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1885 : Material (21 : Basis) (80 : Basis) where
  plus := ![v1885_pa,v1885_pb,v1885_pg]
  minus := ![(Primitive.Addresses.material1885 1).one,v1885_mb,v1885_mg]
  upper := v1885_upper
  lower := (Primitive.Addresses.material1885 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1885_pa_checked.trans (by decide +kernel)
    · exact v1885_pb_checked.trans (by decide +kernel)
    · exact v1885_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 80 Primitive.Addresses.material1885
    · exact v1885_mb_checked.trans (by decide +kernel)
    · exact v1885_mg_checked.trans (by decide +kernel)
  upper_error := v1885_upper_checked
  lower_error := reuse_lower_error 21 80 Primitive.Addresses.material1885

def v1886_pa : Scalar.QComplex := ((999999214074619936966987723319 : Int)/10^30,(-1253734478447236050698469088 : Int)/10^30)
theorem v1886_pa_checked : Scalar.distance (sourceCoefficient 21 81 1 0) v1886_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1886_pb : Scalar.QComplex := ((-540958165654927641096673 : Int)/10^30,(-431477118801229599723171253 : Int)/10^30)
theorem v1886_pb_checked : Scalar.distance (sourceCoefficient 21 81 1 1) v1886_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1886_pg : Scalar.QComplex := ((-93086349932477593113230 : Int)/10^30,(116705658105090403716 : Int)/10^30)
theorem v1886_pg_checked : Scalar.distance (sourceCoefficient 21 81 1 2) v1886_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1886_mb : Scalar.QComplex := ((-913303284748897063114558 : Int)/10^30,(-431476491320045682684041285 : Int)/10^30)
theorem v1886_mb_checked : Scalar.distance (sourceCoefficient 21 81 3 1) v1886_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1886_mg : Scalar.QComplex := ((-93086214560448539923070 : Int)/10^30,(197034942188398575208 : Int)/10^30)
theorem v1886_mg_checked : Scalar.distance (sourceCoefficient 21 81 3 2) v1886_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1886_upper : Scalar.QComplex := ((999995560861286835677499303823 : Int)/10^30,(-2979640535429757219357090097 : Int)/10^30)
theorem v1886_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 81 5) 1) 14) v1886_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1886 : Material (21 : Basis) (81 : Basis) where
  plus := ![v1886_pa,v1886_pb,v1886_pg]
  minus := ![(Primitive.Addresses.material1886 1).one,v1886_mb,v1886_mg]
  upper := v1886_upper
  lower := (Primitive.Addresses.material1886 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1886_pa_checked.trans (by decide +kernel)
    · exact v1886_pb_checked.trans (by decide +kernel)
    · exact v1886_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 81 Primitive.Addresses.material1886
    · exact v1886_mb_checked.trans (by decide +kernel)
    · exact v1886_mg_checked.trans (by decide +kernel)
  upper_error := v1886_upper_checked
  lower_error := reuse_lower_error 21 81 Primitive.Addresses.material1886

def v1887_pa : Scalar.QComplex := ((999999201562770289649259675546 : Int)/10^30,(-1263674729476969359368273278 : Int)/10^30)
theorem v1887_pa_checked : Scalar.distance (sourceCoefficient 21 82 1 0) v1887_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1887_pb : Scalar.QComplex := ((-545247158199063101975305 : Int)/10^30,(-431477112056445373732225562 : Int)/10^30)
theorem v1887_pb_checked : Scalar.distance (sourceCoefficient 21 82 1 1) v1887_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1887_pg : Scalar.QComplex := ((-93086348622580154393274 : Int)/10^30,(117630960334575933659 : Int)/10^30)
theorem v1887_pg_checked : Scalar.distance (sourceCoefficient 21 82 1 2) v1887_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1887_mb : Scalar.QComplex := ((-917592269875599569943611 : Int)/10^30,(-431476480874056571549027593 : Int)/10^30)
theorem v1887_mb_checked : Scalar.distance (sourceCoefficient 21 82 3 1) v1887_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1887_mg : Scalar.QComplex := ((-93086212452057438957185 : Int)/10^30,(197960242942969302688 : Int)/10^30)
theorem v1887_mg_checked : Scalar.distance (sourceCoefficient 21 82 3 2) v1887_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1887_upper : Scalar.QComplex := ((999995531193484318499542053855 : Int)/10^30,(-2989580750060336858011955467 : Int)/10^30)
theorem v1887_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 82 5) 1) 14) v1887_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1887 : Material (21 : Basis) (82 : Basis) where
  plus := ![v1887_pa,v1887_pb,v1887_pg]
  minus := ![(Primitive.Addresses.material1887 1).one,v1887_mb,v1887_mg]
  upper := v1887_upper
  lower := (Primitive.Addresses.material1887 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1887_pa_checked.trans (by decide +kernel)
    · exact v1887_pb_checked.trans (by decide +kernel)
    · exact v1887_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 82 Primitive.Addresses.material1887
    · exact v1887_mb_checked.trans (by decide +kernel)
    · exact v1887_mg_checked.trans (by decide +kernel)
  upper_error := v1887_upper_checked
  lower_error := reuse_lower_error 21 82 Primitive.Addresses.material1887

def v1888_pa : Scalar.QComplex := ((999999184324393385709174324748 : Int)/10^30,(-1277243339345281700717472039 : Int)/10^30)
theorem v1888_pa_checked : Scalar.distance (sourceCoefficient 21 83 1 0) v1888_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1888_pb : Scalar.QComplex := ((-551101705097803097279820 : Int)/10^30,(-431477102757945436111103308 : Int)/10^30)
theorem v1888_pb_checked : Scalar.distance (sourceCoefficient 21 83 1 1) v1888_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1888_pg : Scalar.QComplex := ((-93086346817227196366179 : Int)/10^30,(118894013435234830744 : Int)/10^30)
theorem v1888_pg_checked : Scalar.distance (sourceCoefficient 21 83 1 2) v1888_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1888_mb : Scalar.QComplex := ((-923446806570237531559911 : Int)/10^30,(-431476466523349801575873126 : Int)/10^30)
theorem v1888_mb_checked : Scalar.distance (sourceCoefficient 21 83 3 1) v1888_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1888_mg : Scalar.QComplex := ((-93086209556747213076830 : Int)/10^30,(199223294015397513321 : Int)/10^30)
theorem v1888_mg_checked : Scalar.distance (sourceCoefficient 21 83 3 2) v1888_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1888_upper : Scalar.QComplex := ((999995490536943391061511281309 : Int)/10^30,(-3003149309967923998525065099 : Int)/10^30)
theorem v1888_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 83 5) 1) 14) v1888_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1888 : Material (21 : Basis) (83 : Basis) where
  plus := ![v1888_pa,v1888_pb,v1888_pg]
  minus := ![(Primitive.Addresses.material1888 1).one,v1888_mb,v1888_mg]
  upper := v1888_upper
  lower := (Primitive.Addresses.material1888 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1888_pa_checked.trans (by decide +kernel)
    · exact v1888_pb_checked.trans (by decide +kernel)
    · exact v1888_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 83 Primitive.Addresses.material1888
    · exact v1888_mb_checked.trans (by decide +kernel)
    · exact v1888_mg_checked.trans (by decide +kernel)
  upper_error := v1888_upper_checked
  lower_error := reuse_lower_error 21 83 Primitive.Addresses.material1888

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
