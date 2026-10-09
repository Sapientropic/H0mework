import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B162
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B163

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3905_pa : Scalar.QComplex := ((999998760755314653077178181156 : Int)/10^30,(-1574321388715295160092269902 : Int)/10^30)
theorem v3905_pa_checked : Scalar.distance (sourceCoefficient 56 70 1 0) v3905_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3905_pb : Scalar.QComplex := ((-679284279960025870575602 : Int)/10^30,(-431476979878239890242903192 : Int)/10^30)
theorem v3905_pb_checked : Scalar.distance (sourceCoefficient 56 70 1 1) v3905_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3905_pg : Scalar.QComplex := ((-93086313848002268622407 : Int)/10^30,(146547956496350978886 : Int)/10^30)
theorem v3905_pg_checked : Scalar.distance (sourceCoefficient 56 70 1 2) v3905_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3905_mb : Scalar.QComplex := ((-1051629227664577860987152 : Int)/10^30,(-431476233027901032202851804 : Int)/10^30)
theorem v3905_mb_checked : Scalar.distance (sourceCoefficient 56 70 3 1) v3905_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3905_mg : Scalar.QComplex := ((-93086152723427186899840 : Int)/10^30,(226877198328730578303 : Int)/10^30)
theorem v3905_mg_checked : Scalar.distance (sourceCoefficient 56 70 3 2) v3905_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3905_upper : Scalar.QComplex := ((999994554238733012284590996596 : Int)/10^30,(-3300226185833276154474404396 : Int)/10^30)
theorem v3905_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 70 5) 1) 14) v3905_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3905 : Material (56 : Basis) (70 : Basis) where
  plus := ![v3905_pa,v3905_pb,v3905_pg]
  minus := ![(Primitive.Addresses.material3905 1).one,v3905_mb,v3905_mg]
  upper := v3905_upper
  lower := (Primitive.Addresses.material3905 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3905_pa_checked.trans (by decide +kernel)
    · exact v3905_pb_checked.trans (by decide +kernel)
    · exact v3905_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 70 Primitive.Addresses.material3905
    · exact v3905_mb_checked.trans (by decide +kernel)
    · exact v3905_mg_checked.trans (by decide +kernel)
  upper_error := v3905_upper_checked
  lower_error := reuse_lower_error 56 70 Primitive.Addresses.material3905

def v3906_pa : Scalar.QComplex := ((999998722215543935879197365231 : Int)/10^30,(-1598614174651008605959182781 : Int)/10^30)
theorem v3906_pa_checked : Scalar.distance (sourceCoefficient 56 71 1 0) v3906_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3906_pb : Scalar.QComplex := ((-689766069121681077254685 : Int)/10^30,(-431476962163119427889773130 : Int)/10^30)
theorem v3906_pb_checked : Scalar.distance (sourceCoefficient 56 71 1 1) v3906_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3906_pg : Scalar.QComplex := ((-93086310143318282507715 : Int)/10^30,(148809285007259867103 : Int)/10^30)
theorem v3906_pg_checked : Scalar.distance (sourceCoefficient 56 71 1 2) v3906_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3906_mb : Scalar.QComplex := ((-1062110997636032821749127 : Int)/10^30,(-431476206267475201749571250 : Int)/10^30)
theorem v3906_mb_checked : Scalar.distance (sourceCoefficient 56 71 3 1) v3906_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3906_mg : Scalar.QComplex := ((-93086147067319921749351 : Int)/10^30,(229138522800668086846 : Int)/10^30)
theorem v3906_mg_checked : Scalar.distance (sourceCoefficient 56 71 3 2) v3906_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3906_upper : Scalar.QComplex := ((999994473771874994831243442380 : Int)/10^30,(-3324518869071590622992946769 : Int)/10^30)
theorem v3906_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 71 5) 1) 14) v3906_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3906 : Material (56 : Basis) (71 : Basis) where
  plus := ![v3906_pa,v3906_pb,v3906_pg]
  minus := ![(Primitive.Addresses.material3906 1).one,v3906_mb,v3906_mg]
  upper := v3906_upper
  lower := (Primitive.Addresses.material3906 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3906_pa_checked.trans (by decide +kernel)
    · exact v3906_pb_checked.trans (by decide +kernel)
    · exact v3906_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 71 Primitive.Addresses.material3906
    · exact v3906_mb_checked.trans (by decide +kernel)
    · exact v3906_mg_checked.trans (by decide +kernel)
  upper_error := v3906_upper_checked
  lower_error := reuse_lower_error 56 71 Primitive.Addresses.material3906

def v3907_pa : Scalar.QComplex := ((999998679724382475298154260639 : Int)/10^30,(-1624976766579047880648476455 : Int)/10^30)
theorem v3907_pa_checked : Scalar.distance (sourceCoefficient 56 72 1 0) v3907_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3907_pb : Scalar.QComplex := ((-701140932664891847205314 : Int)/10^30,(-431476942554493232726609080 : Int)/10^30)
theorem v3907_pb_checked : Scalar.distance (sourceCoefficient 56 72 1 1) v3907_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3907_pg : Scalar.QComplex := ((-93086306050472568321921 : Int)/10^30,(151263284327910699926 : Int)/10^30)
theorem v3907_pg_checked : Scalar.distance (sourceCoefficient 56 72 1 2) v3907_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3907_mb : Scalar.QComplex := ((-1073485840022500770931339 : Int)/10^30,(-431476176842861374819540436 : Int)/10^30)
theorem v3907_mb_checked : Scalar.distance (sourceCoefficient 56 72 3 1) v3907_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3907_mg : Scalar.QComplex := ((-93086140856784841821958 : Int)/10^30,(231592517675641302867 : Int)/10^30)
theorem v3907_mg_checked : Scalar.distance (sourceCoefficient 56 72 3 2) v3907_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3907_upper : Scalar.QComplex := ((999994385781334747705637000868 : Int)/10^30,(-3350881348399756075544694266 : Int)/10^30)
theorem v3907_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 72 5) 1) 14) v3907_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3907 : Material (56 : Basis) (72 : Basis) where
  plus := ![v3907_pa,v3907_pb,v3907_pg]
  minus := ![(Primitive.Addresses.material3907 1).one,v3907_mb,v3907_mg]
  upper := v3907_upper
  lower := (Primitive.Addresses.material3907 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3907_pa_checked.trans (by decide +kernel)
    · exact v3907_pb_checked.trans (by decide +kernel)
    · exact v3907_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 72 Primitive.Addresses.material3907
    · exact v3907_mb_checked.trans (by decide +kernel)
    · exact v3907_mg_checked.trans (by decide +kernel)
  upper_error := v3907_upper_checked
  lower_error := reuse_lower_error 56 72 Primitive.Addresses.material3907

def v3908_pa : Scalar.QComplex := ((999998664324284934959888574632 : Int)/10^30,(-1634426396660450540076912139 : Int)/10^30)
theorem v3908_pa_checked : Scalar.distance (sourceCoefficient 56 73 1 0) v3908_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3908_pb : Scalar.QComplex := ((-705218234757312394150563 : Int)/10^30,(-431476935428466509382992673 : Int)/10^30)
theorem v3908_pb_checked : Scalar.distance (sourceCoefficient 56 73 1 1) v3908_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3908_pg : Scalar.QComplex := ((-93086304565022396470491 : Int)/10^30,(152142916562245674605 : Int)/10^30)
theorem v3908_pg_checked : Scalar.distance (sourceCoefficient 56 73 1 2) v3908_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3908_mb : Scalar.QComplex := ((-1077563134447315289041382 : Int)/10^30,(-431476166198309233931812467 : Int)/10^30)
theorem v3908_mb_checked : Scalar.distance (sourceCoefficient 56 73 3 1) v3908_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3908_mg : Scalar.QComplex := ((-93086138612252222005608 : Int)/10^30,(232472148300572399408 : Int)/10^30)
theorem v3908_mg_checked : Scalar.distance (sourceCoefficient 56 73 3 2) v3908_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3908_upper : Scalar.QComplex := ((999994354072055887247052916551 : Int)/10^30,(-3360330937827873491560268506 : Int)/10^30)
theorem v3908_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 73 5) 1) 14) v3908_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3908 : Material (56 : Basis) (73 : Basis) where
  plus := ![v3908_pa,v3908_pb,v3908_pg]
  minus := ![(Primitive.Addresses.material3908 1).one,v3908_mb,v3908_mg]
  upper := v3908_upper
  lower := (Primitive.Addresses.material3908 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3908_pa_checked.trans (by decide +kernel)
    · exact v3908_pb_checked.trans (by decide +kernel)
    · exact v3908_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 73 Primitive.Addresses.material3908
    · exact v3908_mb_checked.trans (by decide +kernel)
    · exact v3908_mg_checked.trans (by decide +kernel)
  upper_error := v3908_upper_checked
  lower_error := reuse_lower_error 56 73 Primitive.Addresses.material3908

def v3909_pa : Scalar.QComplex := ((999998646888617913361833959005 : Int)/10^30,(-1645059553105255821902397048 : Int)/10^30)
theorem v3909_pa_checked : Scalar.distance (sourceCoefficient 56 74 1 0) v3909_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3909_pb : Scalar.QComplex := ((-709806201726017187898749 : Int)/10^30,(-431476927348508639748041444 : Int)/10^30)
theorem v3909_pb_checked : Scalar.distance (sourceCoefficient 56 74 1 1) v3909_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3909_pg : Scalar.QComplex := ((-93086302881930310396524 : Int)/10^30,(153132719024793845839 : Int)/10^30)
theorem v3909_pg_checked : Scalar.distance (sourceCoefficient 56 74 1 2) v3909_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3909_mb : Scalar.QComplex := ((-1082151092735070566190473 : Int)/10^30,(-431476154159145513203853815 : Int)/10^30)
theorem v3909_mb_checked : Scalar.distance (sourceCoefficient 56 74 3 1) v3909_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3909_mg : Scalar.QComplex := ((-93086136075005816492735 : Int)/10^30,(233461948942139211001 : Int)/10^30)
theorem v3909_mg_checked : Scalar.distance (sourceCoefficient 56 74 3 2) v3909_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3909_upper : Scalar.QComplex := ((999994318284551442710351033758 : Int)/10^30,(-3370964048343461779223846403 : Int)/10^30)
theorem v3909_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 74 5) 1) 14) v3909_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3909 : Material (56 : Basis) (74 : Basis) where
  plus := ![v3909_pa,v3909_pb,v3909_pg]
  minus := ![(Primitive.Addresses.material3909 1).one,v3909_mb,v3909_mg]
  upper := v3909_upper
  lower := (Primitive.Addresses.material3909 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3909_pa_checked.trans (by decide +kernel)
    · exact v3909_pb_checked.trans (by decide +kernel)
    · exact v3909_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 74 Primitive.Addresses.material3909
    · exact v3909_mb_checked.trans (by decide +kernel)
    · exact v3909_mg_checked.trans (by decide +kernel)
  upper_error := v3909_upper_checked
  lower_error := reuse_lower_error 56 74 Primitive.Addresses.material3909

def v3910_pa : Scalar.QComplex := ((999998622407104644640063600287 : Int)/10^30,(-1659874661818938225108881732 : Int)/10^30)
theorem v3910_pa_checked : Scalar.distance (sourceCoefficient 56 75 1 0) v3910_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3910_pb : Scalar.QComplex := ((-716198586628891022990188 : Int)/10^30,(-431476915982304690251324101 : Int)/10^30)
theorem v3910_pb_checked : Scalar.distance (sourceCoefficient 56 75 1 1) v3910_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3910_pg : Scalar.QComplex := ((-93086300516416543568055 : Int)/10^30,(154511804444027015545 : Int)/10^30)
theorem v3910_pg_checked : Scalar.distance (sourceCoefficient 56 75 1 2) v3910_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3910_mb : Scalar.QComplex := ((-1088543465449245261926643 : Int)/10^30,(-431476137276605527012797001 : Int)/10^30)
theorem v3910_mb_checked : Scalar.distance (sourceCoefficient 56 75 3 1) v3910_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3910_mg : Scalar.QComplex := ((-93086132519404325356512 : Int)/10^30,(234841031806544009821 : Int)/10^30)
theorem v3910_mg_checked : Scalar.distance (sourceCoefficient 56 75 3 2) v3910_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3910_upper : Scalar.QComplex := ((999994268233541012674593098112 : Int)/10^30,(-3385779092738909102040541913 : Int)/10^30)
theorem v3910_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 75 5) 1) 14) v3910_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3910 : Material (56 : Basis) (75 : Basis) where
  plus := ![v3910_pa,v3910_pb,v3910_pg]
  minus := ![(Primitive.Addresses.material3910 1).one,v3910_mb,v3910_mg]
  upper := v3910_upper
  lower := (Primitive.Addresses.material3910 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3910_pa_checked.trans (by decide +kernel)
    · exact v3910_pb_checked.trans (by decide +kernel)
    · exact v3910_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 75 Primitive.Addresses.material3910
    · exact v3910_mb_checked.trans (by decide +kernel)
    · exact v3910_mg_checked.trans (by decide +kernel)
  upper_error := v3910_upper_checked
  lower_error := reuse_lower_error 56 75 Primitive.Addresses.material3910

def v3911_pa : Scalar.QComplex := ((999998601697300931887120477941 : Int)/10^30,(-1672304829534910940147904120 : Int)/10^30)
theorem v3911_pa_checked : Scalar.distance (sourceCoefficient 56 76 1 0) v3911_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3911_pb : Scalar.QComplex := ((-721561923281227654608914 : Int)/10^30,(-431476906348418532290649993 : Int)/10^30)
theorem v3911_pb_checked : Scalar.distance (sourceCoefficient 56 76 1 1) v3911_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3911_pg : Scalar.QComplex := ((-93086298513314320514940 : Int)/10^30,(155668884239564931550 : Int)/10^30)
theorem v3911_pg_checked : Scalar.distance (sourceCoefficient 56 76 1 2) v3911_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3911_mb : Scalar.QComplex := ((-1093906791790956681092009 : Int)/10^30,(-431476123014404980937568336 : Int)/10^30)
theorem v3911_mb_checked : Scalar.distance (sourceCoefficient 56 76 3 1) v3911_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3911_mg : Scalar.QComplex := ((-93086129517795097540148 : Int)/10^30,(235998109442661234668 : Int)/10^30)
theorem v3911_mg_checked : Scalar.distance (sourceCoefficient 56 76 3 2) v3911_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3911_upper : Scalar.QComplex := ((999994226070426322979057262211 : Int)/10^30,(-3398209206198364724713098687 : Int)/10^30)
theorem v3911_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 76 5) 1) 14) v3911_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3911 : Material (56 : Basis) (76 : Basis) where
  plus := ![v3911_pa,v3911_pb,v3911_pg]
  minus := ![(Primitive.Addresses.material3911 1).one,v3911_mb,v3911_mg]
  upper := v3911_upper
  lower := (Primitive.Addresses.material3911 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3911_pa_checked.trans (by decide +kernel)
    · exact v3911_pb_checked.trans (by decide +kernel)
    · exact v3911_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 76 Primitive.Addresses.material3911
    · exact v3911_mb_checked.trans (by decide +kernel)
    · exact v3911_mg_checked.trans (by decide +kernel)
  upper_error := v3911_upper_checked
  lower_error := reuse_lower_error 56 76 Primitive.Addresses.material3911

def v3912_pa : Scalar.QComplex := ((999998596880779753728206340727 : Int)/10^30,(-1675182518936070250327356959 : Int)/10^30)
theorem v3912_pa_checked : Scalar.distance (sourceCoefficient 56 77 1 0) v3912_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3912_pb : Scalar.QComplex := ((-722803581261653045741189 : Int)/10^30,(-431476904105420601721789647 : Int)/10^30)
theorem v3912_pb_checked : Scalar.distance (sourceCoefficient 56 77 1 1) v3912_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3912_pg : Scalar.QComplex := ((-93086298047187132153460 : Int)/10^30,(155936758038983084563 : Int)/10^30)
theorem v3912_pg_checked : Scalar.distance (sourceCoefficient 56 77 1 2) v3912_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3912_mb : Scalar.QComplex := ((-1095148447373449866334663 : Int)/10^30,(-431476119699912970631743797 : Int)/10^30)
theorem v3912_mb_checked : Scalar.distance (sourceCoefficient 56 77 3 1) v3912_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3912_mg : Scalar.QComplex := ((-93086128820505058429324 : Int)/10^30,(236265982740090959753 : Int)/10^30)
theorem v3912_mg_checked : Scalar.distance (sourceCoefficient 56 77 3 2) v3912_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3912_upper : Scalar.QComplex := ((999994216287281474004849487219 : Int)/10^30,(-3401086883000665106894353190 : Int)/10^30)
theorem v3912_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 77 5) 1) 14) v3912_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3912 : Material (56 : Basis) (77 : Basis) where
  plus := ![v3912_pa,v3912_pb,v3912_pg]
  minus := ![(Primitive.Addresses.material3912 1).one,v3912_mb,v3912_mg]
  upper := v3912_upper
  lower := (Primitive.Addresses.material3912 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3912_pa_checked.trans (by decide +kernel)
    · exact v3912_pb_checked.trans (by decide +kernel)
    · exact v3912_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 77 Primitive.Addresses.material3912
    · exact v3912_mb_checked.trans (by decide +kernel)
    · exact v3912_mg_checked.trans (by decide +kernel)
  upper_error := v3912_upper_checked
  lower_error := reuse_lower_error 56 77 Primitive.Addresses.material3912

def v3913_pa : Scalar.QComplex := ((999998567751172569761525480842 : Int)/10^30,(-1692482083664040821135338303 : Int)/10^30)
theorem v3913_pa_checked : Scalar.distance (sourceCoefficient 56 78 1 0) v3913_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3913_pb : Scalar.QComplex := ((-730267952647231654571835 : Int)/10^30,(-431476890520970139576311244 : Int)/10^30)
theorem v3913_pb_checked : Scalar.distance (sourceCoefficient 56 78 1 1) v3913_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3913_pg : Scalar.QComplex := ((-93086295226055243443502 : Int)/10^30,(157547112551427251016 : Int)/10^30)
theorem v3913_pg_checked : Scalar.distance (sourceCoefficient 56 78 1 2) v3913_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3913_mb : Scalar.QComplex := ((-1102612804256932941794889 : Int)/10^30,(-431476099674051243651187118 : Int)/10^30)
theorem v3913_mb_checked : Scalar.distance (sourceCoefficient 56 78 3 1) v3913_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3913_mg : Scalar.QComplex := ((-93086124609710803591272 : Int)/10^30,(237876334218416783494 : Int)/10^30)
theorem v3913_mg_checked : Scalar.distance (sourceCoefficient 56 78 3 2) v3913_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3913_upper : Scalar.QComplex := ((999994157300238358941668153849 : Int)/10^30,(-3418386371687906782808086602 : Int)/10^30)
theorem v3913_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 78 5) 1) 14) v3913_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3913 : Material (56 : Basis) (78 : Basis) where
  plus := ![v3913_pa,v3913_pb,v3913_pg]
  minus := ![(Primitive.Addresses.material3913 1).one,v3913_mb,v3913_mg]
  upper := v3913_upper
  lower := (Primitive.Addresses.material3913 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3913_pa_checked.trans (by decide +kernel)
    · exact v3913_pb_checked.trans (by decide +kernel)
    · exact v3913_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 78 Primitive.Addresses.material3913
    · exact v3913_mb_checked.trans (by decide +kernel)
    · exact v3913_mg_checked.trans (by decide +kernel)
  upper_error := v3913_upper_checked
  lower_error := reuse_lower_error 56 78 Primitive.Addresses.material3913

def v3914_pa : Scalar.QComplex := ((999998558296510885491077132974 : Int)/10^30,(-1698059156719832102323691411 : Int)/10^30)
theorem v3914_pa_checked : Scalar.distance (sourceCoefficient 56 79 1 0) v3914_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3914_pb : Scalar.QComplex := ((-732674333662501603492416 : Int)/10^30,(-431476886104884006518674155 : Int)/10^30)
theorem v3914_pb_checked : Scalar.distance (sourceCoefficient 56 79 1 1) v3914_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3914_pg : Scalar.QComplex := ((-93086294309644396056494 : Int)/10^30,(158066262302290741260 : Int)/10^30)
theorem v3914_pg_checked : Scalar.distance (sourceCoefficient 56 79 1 2) v3914_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3914_mb : Scalar.QComplex := ((-1105019180565313821992525 : Int)/10^30,(-431476093181368318103972700 : Int)/10^30)
theorem v3914_mb_checked : Scalar.distance (sourceCoefficient 56 79 3 1) v3914_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3914_mg : Scalar.QComplex := ((-93086123245297444067524 : Int)/10^30,(238395482985155807493 : Int)/10^30)
theorem v3914_mg_checked : Scalar.distance (sourceCoefficient 56 79 3 2) v3914_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3914_upper : Scalar.QComplex := ((999994138220068610098796218157 : Int)/10^30,(-3423963420119414529573823960 : Int)/10^30)
theorem v3914_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 79 5) 1) 14) v3914_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3914 : Material (56 : Basis) (79 : Basis) where
  plus := ![v3914_pa,v3914_pb,v3914_pg]
  minus := ![(Primitive.Addresses.material3914 1).one,v3914_mb,v3914_mg]
  upper := v3914_upper
  lower := (Primitive.Addresses.material3914 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3914_pa_checked.trans (by decide +kernel)
    · exact v3914_pb_checked.trans (by decide +kernel)
    · exact v3914_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 79 Primitive.Addresses.material3914
    · exact v3914_mb_checked.trans (by decide +kernel)
    · exact v3914_mg_checked.trans (by decide +kernel)
  upper_error := v3914_upper_checked
  lower_error := reuse_lower_error 56 79 Primitive.Addresses.material3914

def v3915_pa : Scalar.QComplex := ((999998543465152227064287170675 : Int)/10^30,(-1706771095973947131082937107 : Int)/10^30)
theorem v3915_pa_checked : Scalar.distance (sourceCoefficient 56 80 1 0) v3915_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3915_pb : Scalar.QComplex := ((-736433338590436248011867 : Int)/10^30,(-431476879170712614323392130 : Int)/10^30)
theorem v3915_pb_checked : Scalar.distance (sourceCoefficient 56 80 1 1) v3915_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3915_pg : Scalar.QComplex := ((-93086292871360476787768 : Int)/10^30,(158877225514419222223 : Int)/10^30)
theorem v3915_pg_checked : Scalar.distance (sourceCoefficient 56 80 1 2) v3915_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3915_mb : Scalar.QComplex := ((-1108778178109721528851581 : Int)/10^30,(-431476083003347554307277904 : Int)/10^30)
theorem v3915_mb_checked : Scalar.distance (sourceCoefficient 56 80 3 1) v3915_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3915_mg : Scalar.QComplex := ((-93086121107189332697979 : Int)/10^30,(239206444654151377305 : Int)/10^30)
theorem v3915_mg_checked : Scalar.distance (sourceCoefficient 56 80 3 2) v3915_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3915_upper : Scalar.QComplex := ((999994108352715229591303153096 : Int)/10^30,(-3432675320800539861504244166 : Int)/10^30)
theorem v3915_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 80 5) 1) 14) v3915_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3915 : Material (56 : Basis) (80 : Basis) where
  plus := ![v3915_pa,v3915_pb,v3915_pg]
  minus := ![(Primitive.Addresses.material3915 1).one,v3915_mb,v3915_mg]
  upper := v3915_upper
  lower := (Primitive.Addresses.material3915 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3915_pa_checked.trans (by decide +kernel)
    · exact v3915_pb_checked.trans (by decide +kernel)
    · exact v3915_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 80 Primitive.Addresses.material3915
    · exact v3915_mb_checked.trans (by decide +kernel)
    · exact v3915_mg_checked.trans (by decide +kernel)
  upper_error := v3915_upper_checked
  lower_error := reuse_lower_error 56 80 Primitive.Addresses.material3915

def v3916_pa : Scalar.QComplex := ((999998498348832791933529385406 : Int)/10^30,(-1733003196609834578605383095 : Int)/10^30)
theorem v3916_pa_checked : Scalar.distance (sourceCoefficient 56 81 1 0) v3916_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3916_pb : Scalar.QComplex := ((-747751897088001044672116 : Int)/10^30,(-431476858027884729034243075 : Int)/10^30)
theorem v3916_pb_checked : Scalar.distance (sourceCoefficient 56 81 1 1) v3916_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3916_pg : Scalar.QComplex := ((-93086288490838077254876 : Int)/10^30,(161319077760149053574 : Int)/10^30)
theorem v3916_pg_checked : Scalar.distance (sourceCoefficient 56 81 1 2) v3916_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3916_mb : Scalar.QComplex := ((-1120096714147561485805481 : Int)/10^30,(-431476052093121327012023336 : Int)/10^30)
theorem v3916_mb_checked : Scalar.distance (sourceCoefficient 56 81 3 1) v3916_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3916_mg : Scalar.QComplex := ((-93086114619460053111543 : Int)/10^30,(241648292210474480018 : Int)/10^30)
theorem v3916_mg_checked : Scalar.distance (sourceCoefficient 56 81 3 2) v3916_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3916_upper : Scalar.QComplex := ((999994017962237049956916068230 : Int)/10^30,(-3458907304500120426363638693 : Int)/10^30)
theorem v3916_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 81 5) 1) 14) v3916_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3916 : Material (56 : Basis) (81 : Basis) where
  plus := ![v3916_pa,v3916_pb,v3916_pg]
  minus := ![(Primitive.Addresses.material3916 1).one,v3916_mb,v3916_mg]
  upper := v3916_upper
  lower := (Primitive.Addresses.material3916 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3916_pa_checked.trans (by decide +kernel)
    · exact v3916_pb_checked.trans (by decide +kernel)
    · exact v3916_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 81 Primitive.Addresses.material3916
    · exact v3916_mb_checked.trans (by decide +kernel)
    · exact v3916_mg_checked.trans (by decide +kernel)
  upper_error := v3916_upper_checked
  lower_error := reuse_lower_error 56 81 Primitive.Addresses.material3916

def v3917_pa : Scalar.QComplex := ((999998481072928036863315229312 : Int)/10^30,(-1742943440501390288023969027 : Int)/10^30)
theorem v3917_pa_checked : Scalar.distance (sourceCoefficient 56 82 1 0) v3917_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3917_pb : Scalar.QComplex := ((-752040887578827836403127 : Int)/10^30,(-431476849912712123166947289 : Int)/10^30)
theorem v3917_pb_checked : Scalar.distance (sourceCoefficient 56 82 1 1) v3917_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3917_pg : Scalar.QComplex := ((-93086286811383248604686 : Int)/10^30,(162244379435911709702 : Int)/10^30)
theorem v3917_pg_checked : Scalar.distance (sourceCoefficient 56 82 1 2) v3917_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3917_mb : Scalar.QComplex := ((-1124385696038372636195757 : Int)/10^30,(-431476040276746118171787105 : Int)/10^30)
theorem v3917_mb_checked : Scalar.distance (sourceCoefficient 56 82 3 1) v3917_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3917_mg : Scalar.QComplex := ((-93086112141512177656431 : Int)/10^30,(242573592092411156597 : Int)/10^30)
theorem v3917_mg_checked : Scalar.distance (sourceCoefficient 56 82 3 2) v3917_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3917_upper : Scalar.QComplex := ((999993983530398840373896377125 : Int)/10^30,(-3468847503770206172966798619 : Int)/10^30)
theorem v3917_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 82 5) 1) 14) v3917_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3917 : Material (56 : Basis) (82 : Basis) where
  plus := ![v3917_pa,v3917_pb,v3917_pg]
  minus := ![(Primitive.Addresses.material3917 1).one,v3917_mb,v3917_mg]
  upper := v3917_upper
  lower := (Primitive.Addresses.material3917 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3917_pa_checked.trans (by decide +kernel)
    · exact v3917_pb_checked.trans (by decide +kernel)
    · exact v3917_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 82 Primitive.Addresses.material3917
    · exact v3917_mb_checked.trans (by decide +kernel)
    · exact v3917_mg_checked.trans (by decide +kernel)
  upper_error := v3917_upper_checked
  lower_error := reuse_lower_error 56 82 Primitive.Addresses.material3917

def v3918_pa : Scalar.QComplex := ((999998457331535789266706737024 : Int)/10^30,(-1756512040549530681247553874 : Int)/10^30)
theorem v3918_pa_checked : Scalar.distance (sourceCoefficient 56 83 1 0) v3918_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3918_pb : Scalar.QComplex := ((-757895431652779028125863 : Int)/10^30,(-431476838743609003024619891 : Int)/10^30)
theorem v3918_pb_checked : Scalar.distance (sourceCoefficient 56 83 1 1) v3918_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3918_pg : Scalar.QComplex := ((-93086284501578238634145 : Int)/10^30,(163507431774800007572 : Int)/10^30)
theorem v3918_pg_checked : Scalar.distance (sourceCoefficient 56 83 1 2) v3918_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3918_mb : Scalar.QComplex := ((-1130240228293976548352326 : Int)/10^30,(-431476024055439299853996861 : Int)/10^30)
theorem v3918_mb_checked : Scalar.distance (sourceCoefficient 56 83 3 1) v3918_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3918_mg : Scalar.QComplex := ((-93086108741750745036903 : Int)/10^30,(243836641967749650506 : Int)/10^30)
theorem v3918_mg_checked : Scalar.distance (sourceCoefficient 56 83 3 2) v3918_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3918_upper : Scalar.QComplex := ((999993936370869203482702421158 : Int)/10^30,(-3482416042634021457139241973 : Int)/10^30)
theorem v3918_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 83 5) 1) 14) v3918_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3918 : Material (56 : Basis) (83 : Basis) where
  plus := ![v3918_pa,v3918_pb,v3918_pg]
  minus := ![(Primitive.Addresses.material3918 1).one,v3918_mb,v3918_mg]
  upper := v3918_upper
  lower := (Primitive.Addresses.material3918 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3918_pa_checked.trans (by decide +kernel)
    · exact v3918_pb_checked.trans (by decide +kernel)
    · exact v3918_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 83 Primitive.Addresses.material3918
    · exact v3918_mb_checked.trans (by decide +kernel)
    · exact v3918_mg_checked.trans (by decide +kernel)
  upper_error := v3918_upper_checked
  lower_error := reuse_lower_error 56 83 Primitive.Addresses.material3918

def v3919_pa : Scalar.QComplex := ((999998394991983042826850889657 : Int)/10^30,(-1791651042436448281660639265 : Int)/10^30)
theorem v3919_pa_checked : Scalar.distance (sourceCoefficient 56 84 1 0) v3919_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3919_pb : Scalar.QComplex := ((-773057115979534417768439 : Int)/10^30,(-431476809326326612220730749 : Int)/10^30)
theorem v3919_pb_checked : Scalar.distance (sourceCoefficient 56 84 1 1) v3919_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3919_pg : Scalar.QComplex := ((-93086278426870867808038 : Int)/10^30,(166778395460694427042 : Int)/10^30)
theorem v3919_pg_checked : Scalar.distance (sourceCoefficient 56 84 1 2) v3919_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3919_mb : Scalar.QComplex := ((-1145401881589554141891370 : Int)/10^30,(-431475981554317145372113686 : Int)/10^30)
theorem v3919_mb_checked : Scalar.distance (sourceCoefficient 56 84 3 1) v3919_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3919_mg : Scalar.QComplex := ((-93086099844351293910778 : Int)/10^30,(247107599193515932933 : Int)/10^30)
theorem v3919_mg_checked : Scalar.distance (sourceCoefficient 56 84 3 2) v3919_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3919_upper : Scalar.QComplex := ((999993813384679833013534384740 : Int)/10^30,(-3517554884593110823798916831 : Int)/10^30)
theorem v3919_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 84 5) 1) 14) v3919_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3919 : Material (56 : Basis) (84 : Basis) where
  plus := ![v3919_pa,v3919_pb,v3919_pg]
  minus := ![(Primitive.Addresses.material3919 1).one,v3919_mb,v3919_mg]
  upper := v3919_upper
  lower := (Primitive.Addresses.material3919 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3919_pa_checked.trans (by decide +kernel)
    · exact v3919_pb_checked.trans (by decide +kernel)
    · exact v3919_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 84 Primitive.Addresses.material3919
    · exact v3919_mb_checked.trans (by decide +kernel)
    · exact v3919_mg_checked.trans (by decide +kernel)
  upper_error := v3919_upper_checked
  lower_error := reuse_lower_error 56 84 Primitive.Addresses.material3919

def v3920_pa : Scalar.QComplex := ((999998250224768626976783803934 : Int)/10^30,(-1870707727314100262647961847 : Int)/10^30)
theorem v3920_pa_checked : Scalar.distance (sourceCoefficient 56 85 1 0) v3920_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3920_pb : Scalar.QComplex := ((-807168285058051301289624 : Int)/10^30,(-431476740545612553264279390 : Int)/10^30)
theorem v3920_pb_checked : Scalar.distance (sourceCoefficient 56 85 1 1) v3920_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3920_pg : Scalar.QComplex := ((-93086264269605945031385 : Int)/10^30,(174137498577436136724 : Int)/10^30)
theorem v3920_pg_checked : Scalar.distance (sourceCoefficient 56 85 1 2) v3920_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3920_mb : Scalar.QComplex := ((-1179512978612265355527001 : Int)/10^30,(-431475883337226091883657457 : Int)/10^30)
theorem v3920_mb_checked : Scalar.distance (sourceCoefficient 56 85 3 1) v3920_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3920_mg : Scalar.QComplex := ((-93086079336517094483463 : Int)/10^30,(254466687353045215811 : Int)/10^30)
theorem v3920_mg_checked : Scalar.distance (sourceCoefficient 56 85 3 2) v3920_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3920_upper : Scalar.QComplex := ((999993532173014898524242322338 : Int)/10^30,(-3596611201870038427424789169 : Int)/10^30)
theorem v3920_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 56 85 5) 1) 14) v3920_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3920 : Material (56 : Basis) (85 : Basis) where
  plus := ![v3920_pa,v3920_pb,v3920_pg]
  minus := ![(Primitive.Addresses.material3920 1).one,v3920_mb,v3920_mg]
  upper := v3920_upper
  lower := (Primitive.Addresses.material3920 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3920_pa_checked.trans (by decide +kernel)
    · exact v3920_pb_checked.trans (by decide +kernel)
    · exact v3920_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 56 85 Primitive.Addresses.material3920
    · exact v3920_mb_checked.trans (by decide +kernel)
    · exact v3920_mg_checked.trans (by decide +kernel)
  upper_error := v3920_upper_checked
  lower_error := reuse_lower_error 56 85 Primitive.Addresses.material3920

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
