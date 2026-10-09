import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B067
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B068

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1617_pa : Scalar.QComplex := ((999999829639708992660534722360 : Int)/10^30,(-583712731565836396953384501 : Int)/10^30)
theorem v1617_pa_checked : Scalar.distance (sourceCoefficient 18 43 1 0) v1617_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1617_pb : Scalar.QComplex := ((-251858915351396784173440 : Int)/10^30,(-431477435431321840889334939 : Int)/10^30)
theorem v1617_pb_checked : Scalar.distance (sourceCoefficient 18 43 1 1) v1617_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1617_pg : Scalar.QComplex := ((-93086412737549300727655 : Int)/10^30,(54335733507351141373 : Int)/10^30)
theorem v1617_pg_checked : Scalar.distance (sourceCoefficient 18 43 1 2) v1617_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1617_mb : Scalar.QComplex := ((-624204415327738696791035 : Int)/10^30,(-431477057429652493055032338 : Int)/10^30)
theorem v1617_mb_checked : Scalar.distance (sourceCoefficient 18 43 3 1) v1617_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1617_mg : Scalar.QComplex := ((-93086331187932753060426 : Int)/10^30,(134665095011780935218 : Int)/10^30)
theorem v1617_mg_checked : Scalar.distance (sourceCoefficient 18 43 3 2) v1617_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1617_upper : Scalar.QComplex := ((999997332822210298716728855348 : Int)/10^30,(-2309620848876543343727672514 : Int)/10^30)
theorem v1617_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 43 5) 1) 14) v1617_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1617 : Material (18 : Basis) (43 : Basis) where
  plus := ![v1617_pa,v1617_pb,v1617_pg]
  minus := ![(Primitive.Addresses.material1617 1).one,v1617_mb,v1617_mg]
  upper := v1617_upper
  lower := (Primitive.Addresses.material1617 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1617_pa_checked.trans (by decide +kernel)
    · exact v1617_pb_checked.trans (by decide +kernel)
    · exact v1617_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 43 Primitive.Addresses.material1617
    · exact v1617_mb_checked.trans (by decide +kernel)
    · exact v1617_mg_checked.trans (by decide +kernel)
  upper_error := v1617_upper_checked
  lower_error := reuse_lower_error 18 43 Primitive.Addresses.material1617

def v1618_pa : Scalar.QComplex := ((999999826204470915376620208599 : Int)/10^30,(-589568509983666639334557402 : Int)/10^30)
theorem v1618_pa_checked : Scalar.distance (sourceCoefficient 18 44 1 0) v1618_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1618_pb : Scalar.QComplex := ((-254385551831196732371962 : Int)/10^30,(-431477433601690559977937073 : Int)/10^30)
theorem v1618_pb_checked : Scalar.distance (sourceCoefficient 18 44 1 1) v1618_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1618_pg : Scalar.QComplex := ((-93086412380301075089635 : Int)/10^30,(54880826984821606674 : Int)/10^30)
theorem v1618_pg_checked : Scalar.distance (sourceCoefficient 18 44 1 2) v1618_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1618_mb : Scalar.QComplex := ((-626731049287867018675821 : Int)/10^30,(-431477053419648406814386645 : Int)/10^30)
theorem v1618_mb_checked : Scalar.distance (sourceCoefficient 18 44 3 1) v1618_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1618_mg : Scalar.QComplex := ((-93086330360293539484118 : Int)/10^30,(135210187977999057992 : Int)/10^30)
theorem v1618_mg_checked : Scalar.distance (sourceCoefficient 18 44 3 2) v1618_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1618_upper : Scalar.QComplex := ((999997319280435020709709068941 : Int)/10^30,(-2315476612643970221775671202 : Int)/10^30)
theorem v1618_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 44 5) 1) 14) v1618_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1618 : Material (18 : Basis) (44 : Basis) where
  plus := ![v1618_pa,v1618_pb,v1618_pg]
  minus := ![(Primitive.Addresses.material1618 1).one,v1618_mb,v1618_mg]
  upper := v1618_upper
  lower := (Primitive.Addresses.material1618 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1618_pa_checked.trans (by decide +kernel)
    · exact v1618_pb_checked.trans (by decide +kernel)
    · exact v1618_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 44 Primitive.Addresses.material1618
    · exact v1618_mb_checked.trans (by decide +kernel)
    · exact v1618_mg_checked.trans (by decide +kernel)
  upper_error := v1618_upper_checked
  lower_error := reuse_lower_error 18 44 Primitive.Addresses.material1618

def v1619_pa : Scalar.QComplex := ((999999824482623428734598733745 : Int)/10^30,(-592481832916572492667607127 : Int)/10^30)
theorem v1619_pa_checked : Scalar.distance (sourceCoefficient 18 45 1 0) v1619_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1619_pb : Scalar.QComplex := ((-255642585048515087395046 : Int)/10^30,(-431477432684077431386987823 : Int)/10^30)
theorem v1619_pb_checked : Scalar.distance (sourceCoefficient 18 45 1 1) v1619_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1619_pg : Scalar.QComplex := ((-93086412201178393379110 : Int)/10^30,(55152017800719248927 : Int)/10^30)
theorem v1619_pg_checked : Scalar.distance (sourceCoefficient 18 45 1 2) v1619_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1619_mb : Scalar.QComplex := ((-627988081245275655422363 : Int)/10^30,(-431477051417272568021474291 : Int)/10^30)
theorem v1619_mb_checked : Scalar.distance (sourceCoefficient 18 45 3 1) v1619_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1619_mg : Scalar.QComplex := ((-93086329947145464330432 : Int)/10^30,(135481378538345158523 : Int)/10^30)
theorem v1619_mg_checked : Scalar.distance (sourceCoefficient 18 45 3 2) v1619_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1619_upper : Scalar.QComplex := ((999997312530459010953670847066 : Int)/10^30,(-2318389928266071232336656977 : Int)/10^30)
theorem v1619_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 45 5) 1) 14) v1619_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1619 : Material (18 : Basis) (45 : Basis) where
  plus := ![v1619_pa,v1619_pb,v1619_pg]
  minus := ![(Primitive.Addresses.material1619 1).one,v1619_mb,v1619_mg]
  upper := v1619_upper
  lower := (Primitive.Addresses.material1619 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1619_pa_checked.trans (by decide +kernel)
    · exact v1619_pb_checked.trans (by decide +kernel)
    · exact v1619_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 45 Primitive.Addresses.material1619
    · exact v1619_mb_checked.trans (by decide +kernel)
    · exact v1619_mg_checked.trans (by decide +kernel)
  upper_error := v1619_upper_checked
  lower_error := reuse_lower_error 18 45 Primitive.Addresses.material1619

def v1620_pa : Scalar.QComplex := ((999999814653212397123364493383 : Int)/10^30,(-608846073201036253761756600 : Int)/10^30)
theorem v1620_pa_checked : Scalar.distance (sourceCoefficient 18 46 1 0) v1620_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1620_pb : Scalar.QComplex := ((-262703386062390241511087 : Int)/10^30,(-431477427439067898617505272 : Int)/10^30)
theorem v1620_pb_checked : Scalar.distance (sourceCoefficient 18 46 1 1) v1620_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1620_pg : Scalar.QComplex := ((-93086411177910049229841 : Int)/10^30,(56675306418633562303 : Int)/10^30)
theorem v1620_pg_checked : Scalar.distance (sourceCoefficient 18 46 1 2) v1620_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1620_mb : Scalar.QComplex := ((-635048875103884897205070 : Int)/10^30,(-431477040079111719907193914 : Int)/10^30)
theorem v1620_mb_checked : Scalar.distance (sourceCoefficient 18 46 3 1) v1620_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1620_mg : Scalar.QComplex := ((-93086327609348030303243 : Int)/10^30,(137004665706035007015 : Int)/10^30)
theorem v1620_mg_checked : Scalar.distance (sourceCoefficient 18 46 3 2) v1620_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1620_upper : Scalar.QComplex := ((999997274457868440392993347580 : Int)/10^30,(-2334754127213249645060645908 : Int)/10^30)
theorem v1620_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 46 5) 1) 14) v1620_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1620 : Material (18 : Basis) (46 : Basis) where
  plus := ![v1620_pa,v1620_pb,v1620_pg]
  minus := ![(Primitive.Addresses.material1620 1).one,v1620_mb,v1620_mg]
  upper := v1620_upper
  lower := (Primitive.Addresses.material1620 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1620_pa_checked.trans (by decide +kernel)
    · exact v1620_pb_checked.trans (by decide +kernel)
    · exact v1620_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 46 Primitive.Addresses.material1620
    · exact v1620_mb_checked.trans (by decide +kernel)
    · exact v1620_mg_checked.trans (by decide +kernel)
  upper_error := v1620_upper_checked
  lower_error := reuse_lower_error 18 46 Primitive.Addresses.material1620

def v1621_pa : Scalar.QComplex := ((999999812247796472265533350246 : Int)/10^30,(-612784115169917735833287387 : Int)/10^30)
theorem v1621_pa_checked : Scalar.distance (sourceCoefficient 18 47 1 0) v1621_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1621_pb : Scalar.QComplex := ((-264402562443651704996450 : Int)/10^30,(-431477426153862230103981453 : Int)/10^30)
theorem v1621_pb_checked : Scalar.distance (sourceCoefficient 18 47 1 1) v1621_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1621_pg : Scalar.QComplex := ((-93086410927319913468401 : Int)/10^30,(57041884664180633753 : Int)/10^30)
theorem v1621_pg_checked : Scalar.distance (sourceCoefficient 18 47 1 2) v1621_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1621_mb : Scalar.QComplex := ((-636748049743390729337274 : Int)/10^30,(-431477037327593840969191065 : Int)/10^30)
theorem v1621_mb_checked : Scalar.distance (sourceCoefficient 18 47 3 1) v1621_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1621_mg : Scalar.QComplex := ((-93086327042417472012138 : Int)/10^30,(137371243598840243193 : Int)/10^30)
theorem v1621_mg_checked : Scalar.distance (sourceCoefficient 18 47 3 2) v1621_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1621_upper : Scalar.QComplex := ((999997265255752916206867485806 : Int)/10^30,(-2338692159165350540711857690 : Int)/10^30)
theorem v1621_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 47 5) 1) 14) v1621_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1621 : Material (18 : Basis) (47 : Basis) where
  plus := ![v1621_pa,v1621_pb,v1621_pg]
  minus := ![(Primitive.Addresses.material1621 1).one,v1621_mb,v1621_mg]
  upper := v1621_upper
  lower := (Primitive.Addresses.material1621 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1621_pa_checked.trans (by decide +kernel)
    · exact v1621_pb_checked.trans (by decide +kernel)
    · exact v1621_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 47 Primitive.Addresses.material1621
    · exact v1621_mb_checked.trans (by decide +kernel)
    · exact v1621_mg_checked.trans (by decide +kernel)
  upper_error := v1621_upper_checked
  lower_error := reuse_lower_error 18 47 Primitive.Addresses.material1621

def v1622_pa : Scalar.QComplex := ((999999795062562287346337106789 : Int)/10^30,(-640214677608967310653970523 : Int)/10^30)
theorem v1622_pa_checked : Scalar.distance (sourceCoefficient 18 48 1 0) v1622_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1622_pb : Scalar.QComplex := ((-276238232002443029215946 : Int)/10^30,(-431477416954206943542439881 : Int)/10^30)
theorem v1622_pb_checked : Scalar.distance (sourceCoefficient 18 48 1 1) v1622_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1622_pg : Scalar.QComplex := ((-93086409135102704873143 : Int)/10^30,(59595297627513803297 : Int)/10^30)
theorem v1622_pg_checked : Scalar.distance (sourceCoefficient 18 48 1 2) v1622_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1622_mb : Scalar.QComplex := ((-648583706956333184788671 : Int)/10^30,(-431477017914292209391701210 : Int)/10^30)
theorem v1622_mb_checked : Scalar.distance (sourceCoefficient 18 48 3 1) v1622_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1622_mg : Scalar.QComplex := ((-93086323046720544835544 : Int)/10^30,(139924654064818337200 : Int)/10^30)
theorem v1622_mg_checked : Scalar.distance (sourceCoefficient 18 48 3 2) v1622_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1622_upper : Scalar.QComplex := ((999997200727882038061226458662 : Int)/10^30,(-2366122651089644411877145868 : Int)/10^30)
theorem v1622_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 48 5) 1) 14) v1622_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1622 : Material (18 : Basis) (48 : Basis) where
  plus := ![v1622_pa,v1622_pb,v1622_pg]
  minus := ![(Primitive.Addresses.material1622 1).one,v1622_mb,v1622_mg]
  upper := v1622_upper
  lower := (Primitive.Addresses.material1622 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1622_pa_checked.trans (by decide +kernel)
    · exact v1622_pb_checked.trans (by decide +kernel)
    · exact v1622_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 48 Primitive.Addresses.material1622
    · exact v1622_mb_checked.trans (by decide +kernel)
    · exact v1622_mg_checked.trans (by decide +kernel)
  upper_error := v1622_upper_checked
  lower_error := reuse_lower_error 18 48 Primitive.Addresses.material1622

def v1623_pa : Scalar.QComplex := ((999999780710420202591521611127 : Int)/10^30,(-662253057000794182860046212 : Int)/10^30)
theorem v1623_pa_checked : Scalar.distance (sourceCoefficient 18 49 1 0) v1623_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1623_pb : Scalar.QComplex := ((-285747295963587981225603 : Int)/10^30,(-431477409249378291902329798 : Int)/10^30)
theorem v1623_pb_checked : Scalar.distance (sourceCoefficient 18 49 1 1) v1623_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1623_pg : Scalar.QComplex := ((-93086407635992740862458 : Int)/10^30,(61646771540652890512 : Int)/10^30)
theorem v1623_pg_checked : Scalar.distance (sourceCoefficient 18 49 1 2) v1623_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1623_mb : Scalar.QComplex := ((-658092760727898924607411 : Int)/10^30,(-431477002003572500485925922 : Int)/10^30)
theorem v1623_mb_checked : Scalar.distance (sourceCoefficient 18 49 3 1) v1623_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1623_mg : Scalar.QComplex := ((-93086319777281546928165 : Int)/10^30,(141976125920435548029 : Int)/10^30)
theorem v1623_mg_checked : Scalar.distance (sourceCoefficient 18 49 3 2) v1623_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1623_upper : Scalar.QComplex := ((999997148339517805003647620763 : Int)/10^30,(-2388160972887398767726761426 : Int)/10^30)
theorem v1623_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 49 5) 1) 14) v1623_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1623 : Material (18 : Basis) (49 : Basis) where
  plus := ![v1623_pa,v1623_pb,v1623_pg]
  minus := ![(Primitive.Addresses.material1623 1).one,v1623_mb,v1623_mg]
  upper := v1623_upper
  lower := (Primitive.Addresses.material1623 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1623_pa_checked.trans (by decide +kernel)
    · exact v1623_pb_checked.trans (by decide +kernel)
    · exact v1623_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 49 Primitive.Addresses.material1623
    · exact v1623_mb_checked.trans (by decide +kernel)
    · exact v1623_mg_checked.trans (by decide +kernel)
  upper_error := v1623_upper_checked
  lower_error := reuse_lower_error 18 49 Primitive.Addresses.material1623

def v1624_pa : Scalar.QComplex := ((999999779001616385684466489910 : Int)/10^30,(-664828337534092710908888371 : Int)/10^30)
theorem v1624_pa_checked : Scalar.distance (sourceCoefficient 18 50 1 0) v1624_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1624_pb : Scalar.QComplex := ((-286858471459344582245518 : Int)/10^30,(-431477408330802128468480895 : Int)/10^30)
theorem v1624_pb_checked : Scalar.distance (sourceCoefficient 18 50 1 1) v1624_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1624_pg : Scalar.QComplex := ((-93086407457373271459293 : Int)/10^30,(61886495193722047528 : Int)/10^30)
theorem v1624_pg_checked : Scalar.distance (sourceCoefficient 18 50 1 2) v1624_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1624_mb : Scalar.QComplex := ((-659203935017224247419465 : Int)/10^30,(-431477000126102271728570082 : Int)/10^30)
theorem v1624_mb_checked : Scalar.distance (sourceCoefficient 18 50 3 1) v1624_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1624_mg : Scalar.QComplex := ((-93086319391791428187049 : Int)/10^30,(142215849330104075722 : Int)/10^30)
theorem v1624_mg_checked : Scalar.distance (sourceCoefficient 18 50 3 2) v1624_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1624_upper : Scalar.QComplex := ((999997142186015960310870162548 : Int)/10^30,(-2390736246635879088619047218 : Int)/10^30)
theorem v1624_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 50 5) 1) 14) v1624_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1624 : Material (18 : Basis) (50 : Basis) where
  plus := ![v1624_pa,v1624_pb,v1624_pg]
  minus := ![(Primitive.Addresses.material1624 1).one,v1624_mb,v1624_mg]
  upper := v1624_upper
  lower := (Primitive.Addresses.material1624 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1624_pa_checked.trans (by decide +kernel)
    · exact v1624_pb_checked.trans (by decide +kernel)
    · exact v1624_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 50 Primitive.Addresses.material1624
    · exact v1624_mb_checked.trans (by decide +kernel)
    · exact v1624_mg_checked.trans (by decide +kernel)
  upper_error := v1624_upper_checked
  lower_error := reuse_lower_error 18 50 Primitive.Addresses.material1624

def v1625_pa : Scalar.QComplex := ((999999771425717936133074853757 : Int)/10^30,(-676127585505525302613361412 : Int)/10^30)
theorem v1625_pa_checked : Scalar.distance (sourceCoefficient 18 51 1 0) v1625_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1625_pb : Scalar.QComplex := ((-291733842222235458293299 : Int)/10^30,(-431477404255380548118550543 : Int)/10^30)
theorem v1625_pb_checked : Scalar.distance (sourceCoefficient 18 51 1 1) v1625_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1625_pg : Scalar.QComplex := ((-93086406665153380997786 : Int)/10^30,(62938301767972733981 : Int)/10^30)
theorem v1625_pg_checked : Scalar.distance (sourceCoefficient 18 51 1 2) v1625_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1625_mb : Scalar.QComplex := ((-664079300447886499324088 : Int)/10^30,(-431476991843456819017545787 : Int)/10^30)
theorem v1625_mb_checked : Scalar.distance (sourceCoefficient 18 51 3 1) v1625_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1625_mg : Scalar.QComplex := ((-93086317691910130736459 : Int)/10^30,(143267654829069019437 : Int)/10^30)
theorem v1625_mg_checked : Scalar.distance (sourceCoefficient 18 51 3 2) v1625_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1625_upper : Scalar.QComplex := ((999997115108651855246279186735 : Int)/10^30,(-2402035464703095685992246627 : Int)/10^30)
theorem v1625_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 51 5) 1) 14) v1625_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1625 : Material (18 : Basis) (51 : Basis) where
  plus := ![v1625_pa,v1625_pb,v1625_pg]
  minus := ![(Primitive.Addresses.material1625 1).one,v1625_mb,v1625_mg]
  upper := v1625_upper
  lower := (Primitive.Addresses.material1625 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1625_pa_checked.trans (by decide +kernel)
    · exact v1625_pb_checked.trans (by decide +kernel)
    · exact v1625_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 51 Primitive.Addresses.material1625
    · exact v1625_mb_checked.trans (by decide +kernel)
    · exact v1625_mg_checked.trans (by decide +kernel)
  upper_error := v1625_upper_checked
  lower_error := reuse_lower_error 18 51 Primitive.Addresses.material1625

def v1626_pa : Scalar.QComplex := ((999999754778361521307619316017 : Int)/10^30,(-700316511888540853925374857 : Int)/10^30)
theorem v1626_pa_checked : Scalar.distance (sourceCoefficient 18 52 1 0) v1626_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1626_pb : Scalar.QComplex := ((-302170818522848609388149 : Int)/10^30,(-431477395283973388301973431 : Int)/10^30)
theorem v1626_pb_checked : Scalar.distance (sourceCoefficient 18 52 1 1) v1626_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1626_pg : Scalar.QComplex := ((-93086404922591717810904 : Int)/10^30,(65189962385623119180 : Int)/10^30)
theorem v1626_pg_checked : Scalar.distance (sourceCoefficient 18 52 1 2) v1626_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1626_mb : Scalar.QComplex := ((-674516265120416058577239 : Int)/10^30,(-431476973865412516199703527 : Int)/10^30)
theorem v1626_mb_checked : Scalar.distance (sourceCoefficient 18 52 3 1) v1626_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1626_mg : Scalar.QComplex := ((-93086314006267414382305 : Int)/10^30,(145519313104571017446 : Int)/10^30)
theorem v1626_mg_checked : Scalar.distance (sourceCoefficient 18 52 3 2) v1626_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1626_upper : Scalar.QComplex := ((999997056713427699877563541885 : Int)/10^30,(-2426224326327719885083076694 : Int)/10^30)
theorem v1626_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 52 5) 1) 14) v1626_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1626 : Material (18 : Basis) (52 : Basis) where
  plus := ![v1626_pa,v1626_pb,v1626_pg]
  minus := ![(Primitive.Addresses.material1626 1).one,v1626_mb,v1626_mg]
  upper := v1626_upper
  lower := (Primitive.Addresses.material1626 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1626_pa_checked.trans (by decide +kernel)
    · exact v1626_pb_checked.trans (by decide +kernel)
    · exact v1626_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 52 Primitive.Addresses.material1626
    · exact v1626_mb_checked.trans (by decide +kernel)
    · exact v1626_mg_checked.trans (by decide +kernel)
  upper_error := v1626_upper_checked
  lower_error := reuse_lower_error 18 52 Primitive.Addresses.material1626

def v1627_pa : Scalar.QComplex := ((999999752178451707027342898062 : Int)/10^30,(-704019200853517571075621147 : Int)/10^30)
theorem v1627_pa_checked : Scalar.distance (sourceCoefficient 18 53 1 0) v1627_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1627_pb : Scalar.QComplex := ((-303768445306812246098785 : Int)/10^30,(-431477393880979766483722700 : Int)/10^30)
theorem v1627_pb_checked : Scalar.distance (sourceCoefficient 18 53 1 1) v1627_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1627_pg : Scalar.QComplex := ((-93086404650243496954314 : Int)/10^30,(65534632453085669863 : Int)/10^30)
theorem v1627_pg_checked : Scalar.distance (sourceCoefficient 18 53 1 2) v1627_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1627_mb : Scalar.QComplex := ((-676113890098789921325072 : Int)/10^30,(-431476971083739456658755075 : Int)/10^30)
theorem v1627_mb_checked : Scalar.distance (sourceCoefficient 18 53 3 1) v1627_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1627_mg : Scalar.QComplex := ((-93086313436484550076807 : Int)/10^30,(145863982808672901321 : Int)/10^30)
theorem v1627_mg_checked : Scalar.distance (sourceCoefficient 18 53 3 2) v1627_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1627_upper : Scalar.QComplex := ((999997047723016509626689166804 : Int)/10^30,(-2429927005290767859827929337 : Int)/10^30)
theorem v1627_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 53 5) 1) 14) v1627_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1627 : Material (18 : Basis) (53 : Basis) where
  plus := ![v1627_pa,v1627_pb,v1627_pg]
  minus := ![(Primitive.Addresses.material1627 1).one,v1627_mb,v1627_mg]
  upper := v1627_upper
  lower := (Primitive.Addresses.material1627 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1627_pa_checked.trans (by decide +kernel)
    · exact v1627_pb_checked.trans (by decide +kernel)
    · exact v1627_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 53 Primitive.Addresses.material1627
    · exact v1627_mb_checked.trans (by decide +kernel)
    · exact v1627_mg_checked.trans (by decide +kernel)
  upper_error := v1627_upper_checked
  lower_error := reuse_lower_error 18 53 Primitive.Addresses.material1627

def v1628_pa : Scalar.QComplex := ((999999750851384834595768273323 : Int)/10^30,(-705901670387438610581945418 : Int)/10^30)
theorem v1628_pa_checked : Scalar.distance (sourceCoefficient 18 54 1 0) v1628_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1628_pb : Scalar.QComplex := ((-304580688455211314906739 : Int)/10^30,(-431477393164664957458136508 : Int)/10^30)
theorem v1628_pb_checked : Scalar.distance (sourceCoefficient 18 54 1 1) v1628_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1628_pg : Scalar.QComplex := ((-93086404511209100148496 : Int)/10^30,(65709864806345123949 : Int)/10^30)
theorem v1628_pg_checked : Scalar.distance (sourceCoefficient 18 54 1 2) v1628_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1628_mb : Scalar.QComplex := ((-676926132326606326070650 : Int)/10^30,(-431476969666495659354926602 : Int)/10^30)
theorem v1628_mb_checked : Scalar.distance (sourceCoefficient 18 54 3 1) v1628_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1628_mg : Scalar.QComplex := ((-93086313146232576349160 : Int)/10^30,(146039214976704919207 : Int)/10^30)
theorem v1628_mg_checked : Scalar.distance (sourceCoefficient 18 54 3 2) v1628_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1628_upper : Scalar.QComplex := ((999997043146979974459704669890 : Int)/10^30,(-2431809469730574627713213054 : Int)/10^30)
theorem v1628_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 54 5) 1) 14) v1628_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1628 : Material (18 : Basis) (54 : Basis) where
  plus := ![v1628_pa,v1628_pb,v1628_pg]
  minus := ![(Primitive.Addresses.material1628 1).one,v1628_mb,v1628_mg]
  upper := v1628_upper
  lower := (Primitive.Addresses.material1628 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1628_pa_checked.trans (by decide +kernel)
    · exact v1628_pb_checked.trans (by decide +kernel)
    · exact v1628_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 54 Primitive.Addresses.material1628
    · exact v1628_mb_checked.trans (by decide +kernel)
    · exact v1628_mg_checked.trans (by decide +kernel)
  upper_error := v1628_upper_checked
  lower_error := reuse_lower_error 18 54 Primitive.Addresses.material1628

def v1629_pa : Scalar.QComplex := ((999999739902601827298229199557 : Int)/10^30,(-721245262511128738014965475 : Int)/10^30)
theorem v1629_pa_checked : Scalar.distance (sourceCoefficient 18 55 1 0) v1629_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1629_pb : Scalar.QComplex := ((-311201102377420370015696 : Int)/10^30,(-431477387250112487733635180 : Int)/10^30)
theorem v1629_pb_checked : Scalar.distance (sourceCoefficient 18 55 1 1) v1629_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1629_pg : Scalar.QComplex := ((-93086403363618400104306 : Int)/10^30,(67138144892666574853 : Int)/10^30)
theorem v1629_pg_checked : Scalar.distance (sourceCoefficient 18 55 1 2) v1629_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1629_mb : Scalar.QComplex := ((-683546538679740310260218 : Int)/10^30,(-431476958038826349396581066 : Int)/10^30)
theorem v1629_mb_checked : Scalar.distance (sourceCoefficient 18 55 3 1) v1629_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1629_mg : Scalar.QComplex := ((-93086310766100916457168 : Int)/10^30,(147467493540893329778 : Int)/10^30)
theorem v1629_mg_checked : Scalar.distance (sourceCoefficient 18 55 3 2) v1629_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1629_upper : Scalar.QComplex := ((999997005716565228403228511677 : Int)/10^30,(-2447153020105180467091176234 : Int)/10^30)
theorem v1629_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 55 5) 1) 14) v1629_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1629 : Material (18 : Basis) (55 : Basis) where
  plus := ![v1629_pa,v1629_pb,v1629_pg]
  minus := ![(Primitive.Addresses.material1629 1).one,v1629_mb,v1629_mg]
  upper := v1629_upper
  lower := (Primitive.Addresses.material1629 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1629_pa_checked.trans (by decide +kernel)
    · exact v1629_pb_checked.trans (by decide +kernel)
    · exact v1629_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 55 Primitive.Addresses.material1629
    · exact v1629_mb_checked.trans (by decide +kernel)
    · exact v1629_mg_checked.trans (by decide +kernel)
  upper_error := v1629_upper_checked
  lower_error := reuse_lower_error 18 55 Primitive.Addresses.material1629

def v1630_pa : Scalar.QComplex := ((999999737269583095059212888887 : Int)/10^30,(-724886725483788678806456342 : Int)/10^30)
theorem v1630_pa_checked : Scalar.distance (sourceCoefficient 18 56 1 0) v1630_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1630_pb : Scalar.QComplex := ((-312772311506903965300892 : Int)/10^30,(-431477385826537646066176748 : Int)/10^30)
theorem v1630_pb_checked : Scalar.distance (sourceCoefficient 18 56 1 1) v1630_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1630_pg : Scalar.QComplex := ((-93086403087509100205940 : Int)/10^30,(67477115649459234146 : Int)/10^30)
theorem v1630_pg_checked : Scalar.distance (sourceCoefficient 18 56 1 2) v1630_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1630_mb : Scalar.QComplex := ((-685117745995709965905852 : Int)/10^30,(-431476955259369323679039352 : Int)/10^30)
theorem v1630_mb_checked : Scalar.distance (sourceCoefficient 18 56 3 1) v1630_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1630_mg : Scalar.QComplex := ((-93086310197475222931009 : Int)/10^30,(147806463933201794277 : Int)/10^30)
theorem v1630_mg_checked : Scalar.distance (sourceCoefficient 18 56 3 2) v1630_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1630_upper : Scalar.QComplex := ((999996996798715677865579738781 : Int)/10^30,(-2450794473109957600143625309 : Int)/10^30)
theorem v1630_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 56 5) 1) 14) v1630_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1630 : Material (18 : Basis) (56 : Basis) where
  plus := ![v1630_pa,v1630_pb,v1630_pg]
  minus := ![(Primitive.Addresses.material1630 1).one,v1630_mb,v1630_mg]
  upper := v1630_upper
  lower := (Primitive.Addresses.material1630 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1630_pa_checked.trans (by decide +kernel)
    · exact v1630_pb_checked.trans (by decide +kernel)
    · exact v1630_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 56 Primitive.Addresses.material1630
    · exact v1630_mb_checked.trans (by decide +kernel)
    · exact v1630_mg_checked.trans (by decide +kernel)
  upper_error := v1630_upper_checked
  lower_error := reuse_lower_error 18 56 Primitive.Addresses.material1630

def v1631_pa : Scalar.QComplex := ((999999728662612437541804641682 : Int)/10^30,(-736664578693002247908232953 : Int)/10^30)
theorem v1631_pa_checked : Scalar.distance (sourceCoefficient 18 57 1 0) v1631_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1631_pb : Scalar.QComplex := ((-317854189460827949543222 : Int)/10^30,(-431477381169924747470643023 : Int)/10^30)
theorem v1631_pb_checked : Scalar.distance (sourceCoefficient 18 57 1 1) v1631_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1631_pg : Scalar.QComplex := ((-93086402184607043918664 : Int)/10^30,(68573473853918163672 : Int)/10^30)
theorem v1631_pg_checked : Scalar.distance (sourceCoefficient 18 57 1 2) v1631_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1631_mb : Scalar.QComplex := ((-690199618038971329177853 : Int)/10^30,(-431476946217326364003553335 : Int)/10^30)
theorem v1631_mb_checked : Scalar.distance (sourceCoefficient 18 57 3 1) v1631_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1631_mg : Scalar.QComplex := ((-93086308348465750527902 : Int)/10^30,(148902820950272648861 : Int)/10^30)
theorem v1631_mg_checked : Scalar.distance (sourceCoefficient 18 57 3 2) v1631_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1631_upper : Scalar.QComplex := ((999996967864251678813943680042 : Int)/10^30,(-2462572293922591801350578630 : Int)/10^30)
theorem v1631_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 57 5) 1) 14) v1631_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1631 : Material (18 : Basis) (57 : Basis) where
  plus := ![v1631_pa,v1631_pb,v1631_pg]
  minus := ![(Primitive.Addresses.material1631 1).one,v1631_mb,v1631_mg]
  upper := v1631_upper
  lower := (Primitive.Addresses.material1631 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1631_pa_checked.trans (by decide +kernel)
    · exact v1631_pb_checked.trans (by decide +kernel)
    · exact v1631_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 57 Primitive.Addresses.material1631
    · exact v1631_mb_checked.trans (by decide +kernel)
    · exact v1631_mg_checked.trans (by decide +kernel)
  upper_error := v1631_upper_checked
  lower_error := reuse_lower_error 18 57 Primitive.Addresses.material1631

def v1632_pa : Scalar.QComplex := ((999999723934500839481251926834 : Int)/10^30,(-743055127234095377115374205 : Int)/10^30)
theorem v1632_pa_checked : Scalar.distance (sourceCoefficient 18 58 1 0) v1632_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1632_pb : Scalar.QComplex := ((-320611566971400841156075 : Int)/10^30,(-431477378609893783692013747 : Int)/10^30)
theorem v1632_pb_checked : Scalar.distance (sourceCoefficient 18 58 1 1) v1632_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1632_pg : Scalar.QComplex := ((-93086401688396563096567 : Int)/10^30,(69168347145329899709 : Int)/10^30)
theorem v1632_pg_checked : Scalar.distance (sourceCoefficient 18 58 1 2) v1632_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1632_mb : Scalar.QComplex := ((-692956992313655133000284 : Int)/10^30,(-431476941277803749490058690 : Int)/10^30)
theorem v1632_mb_checked : Scalar.distance (sourceCoefficient 18 58 3 1) v1632_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1632_mg : Scalar.QComplex := ((-93086307338906596077793 : Int)/10^30,(149497693591978574994 : Int)/10^30)
theorem v1632_mg_checked : Scalar.distance (sourceCoefficient 18 58 3 2) v1632_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1632_upper : Scalar.QComplex := ((999996952106640086828392734782 : Int)/10^30,(-2468962824785421877845033246 : Int)/10^30)
theorem v1632_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 58 5) 1) 14) v1632_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1632 : Material (18 : Basis) (58 : Basis) where
  plus := ![v1632_pa,v1632_pb,v1632_pg]
  minus := ![(Primitive.Addresses.material1632 1).one,v1632_mb,v1632_mg]
  upper := v1632_upper
  lower := (Primitive.Addresses.material1632 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1632_pa_checked.trans (by decide +kernel)
    · exact v1632_pb_checked.trans (by decide +kernel)
    · exact v1632_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 58 Primitive.Addresses.material1632
    · exact v1632_mb_checked.trans (by decide +kernel)
    · exact v1632_mg_checked.trans (by decide +kernel)
  upper_error := v1632_upper_checked
  lower_error := reuse_lower_error 18 58 Primitive.Addresses.material1632

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
