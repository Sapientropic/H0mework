import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B056

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1345_pa : Scalar.QComplex := ((999998998043199380290151790966 : Int)/10^30,(-1415596198540385099296889316 : Int)/10^30)
theorem v1345_pa_checked : Scalar.distance (sourceCoefficient 14 93 1 0) v1345_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1345_pb : Scalar.QComplex := ((-610797750558239929882125 : Int)/10^30,(-431476955925051331029762511 : Int)/10^30)
theorem v1345_pb_checked : Scalar.distance (sourceCoefficient 14 93 1 1) v1345_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1345_pg : Scalar.QComplex := ((-93086322308327254293832 : Int)/10^30,(131772776026402182633 : Int)/10^30)
theorem v1345_pg_checked : Scalar.distance (sourceCoefficient 14 93 1 2) v1345_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1345_mb : Scalar.QComplex := ((-983142703092933890561236 : Int)/10^30,(-431476268175511746816256313 : Int)/10^30)
theorem v1345_mb_checked : Scalar.distance (sourceCoefficient 14 93 3 1) v1345_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1345_mg : Scalar.QComplex := ((-93086173934064318545706 : Int)/10^30,(212102030661136153860 : Int)/10^30)
theorem v1345_mg_checked : Scalar.distance (sourceCoefficient 14 93 3 2) v1345_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1345_upper : Scalar.QComplex := ((999995065471543132191380689028 : Int)/10^30,(-3141501641598254139041439124 : Int)/10^30)
theorem v1345_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 93 5) 1) 14) v1345_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1345 : Material (14 : Basis) (93 : Basis) where
  plus := ![v1345_pa,v1345_pb,v1345_pg]
  minus := ![(Primitive.Addresses.material1345 1).one,v1345_mb,v1345_mg]
  upper := v1345_upper
  lower := (Primitive.Addresses.material1345 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1345_pa_checked.trans (by decide +kernel)
    · exact v1345_pb_checked.trans (by decide +kernel)
    · exact v1345_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 93 Primitive.Addresses.material1345
    · exact v1345_mb_checked.trans (by decide +kernel)
    · exact v1345_mg_checked.trans (by decide +kernel)
  upper_error := v1345_upper_checked
  lower_error := reuse_lower_error 14 93 Primitive.Addresses.material1345

def v1346_pa : Scalar.QComplex := ((999998933623077337587972608846 : Int)/10^30,(-1460394709715521691990207617 : Int)/10^30)
theorem v1346_pa_checked : Scalar.distance (sourceCoefficient 14 94 1 0) v1346_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1346_pb : Scalar.QComplex := ((-630127282161939783680891 : Int)/10^30,(-431476919230619213986438523 : Int)/10^30)
theorem v1346_pb_checked : Scalar.distance (sourceCoefficient 14 94 1 1) v1346_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1346_pg : Scalar.QComplex := ((-93086315351801779617131 : Int)/10^30,(135942907453061378008 : Int)/10^30)
theorem v1346_pg_checked : Scalar.distance (sourceCoefficient 14 94 1 2) v1346_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1346_mb : Scalar.QComplex := ((-1002472195833723463931946 : Int)/10^30,(-431476214800578088580415160 : Int)/10^30)
theorem v1346_mb_checked : Scalar.distance (sourceCoefficient 14 94 3 1) v1346_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1346_mg : Scalar.QComplex := ((-93086163378905828641891 : Int)/10^30,(216272154531896660299 : Int)/10^30)
theorem v1346_mg_checked : Scalar.distance (sourceCoefficient 14 94 3 2) v1346_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1346_upper : Scalar.QComplex := ((999994923733350836594791896596 : Int)/10^30,(-3186299974867984241270843096 : Int)/10^30)
theorem v1346_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 94 5) 1) 14) v1346_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1346 : Material (14 : Basis) (94 : Basis) where
  plus := ![v1346_pa,v1346_pb,v1346_pg]
  minus := ![(Primitive.Addresses.material1346 1).one,v1346_mb,v1346_mg]
  upper := v1346_upper
  lower := (Primitive.Addresses.material1346 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1346_pa_checked.trans (by decide +kernel)
    · exact v1346_pb_checked.trans (by decide +kernel)
    · exact v1346_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 94 Primitive.Addresses.material1346
    · exact v1346_mb_checked.trans (by decide +kernel)
    · exact v1346_mg_checked.trans (by decide +kernel)
  upper_error := v1346_upper_checked
  lower_error := reuse_lower_error 14 94 Primitive.Addresses.material1346

def v1347_pa : Scalar.QComplex := ((999998867985132932811668544334 : Int)/10^30,(-1504668884730696290930060324 : Int)/10^30)
theorem v1347_pa_checked : Scalar.distance (sourceCoefficient 14 95 1 0) v1347_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1347_pb : Scalar.QComplex := ((-649230573510811398430871 : Int)/10^30,(-431476881831279680040940712 : Int)/10^30)
theorem v1347_pb_checked : Scalar.distance (sourceCoefficient 14 95 1 1) v1347_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1347_pg : Scalar.QComplex := ((-93086308262557002108642 : Int)/10^30,(140064230191910365096 : Int)/10^30)
theorem v1347_pg_checked : Scalar.distance (sourceCoefficient 14 95 1 2) v1347_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1347_mb : Scalar.QComplex := ((-1021575447795621031881804 : Int)/10^30,(-431476160915972426345591575 : Int)/10^30)
theorem v1347_mb_checked : Scalar.distance (sourceCoefficient 14 95 3 1) v1347_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1347_mg : Scalar.QComplex := ((-93086152733147784642263 : Int)/10^30,(220393469618489882702 : Int)/10^30)
theorem v1347_mg_checked : Scalar.distance (sourceCoefficient 14 95 3 2) v1347_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1347_upper : Scalar.QComplex := ((999994781682294637416976709070 : Int)/10^30,(-3230573970656838550199885726 : Int)/10^30)
theorem v1347_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 95 5) 1) 14) v1347_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1347 : Material (14 : Basis) (95 : Basis) where
  plus := ![v1347_pa,v1347_pb,v1347_pg]
  minus := ![(Primitive.Addresses.material1347 1).one,v1347_mb,v1347_mg]
  upper := v1347_upper
  lower := (Primitive.Addresses.material1347 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1347_pa_checked.trans (by decide +kernel)
    · exact v1347_pb_checked.trans (by decide +kernel)
    · exact v1347_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 95 Primitive.Addresses.material1347
    · exact v1347_mb_checked.trans (by decide +kernel)
    · exact v1347_mg_checked.trans (by decide +kernel)
  upper_error := v1347_upper_checked
  lower_error := reuse_lower_error 14 95 Primitive.Addresses.material1347

def v1348_pa : Scalar.QComplex := ((999998835763627698474600278264 : Int)/10^30,(-1525932956966563524660243167 : Int)/10^30)
theorem v1348_pa_checked : Scalar.distance (sourceCoefficient 14 96 1 0) v1348_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1348_pb : Scalar.QComplex := ((-658405532674341504835463 : Int)/10^30,(-431476863468189517786062391 : Int)/10^30)
theorem v1348_pb_checked : Scalar.distance (sourceCoefficient 14 96 1 1) v1348_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1348_pg : Scalar.QComplex := ((-93086304782049280915789 : Int)/10^30,(142043625681518693820 : Int)/10^30)
theorem v1348_pg_checked : Scalar.distance (sourceCoefficient 14 96 1 2) v1348_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1348_mb : Scalar.QComplex := ((-1030750387696374758209390 : Int)/10^30,(-431476134635312568203032505 : Int)/10^30)
theorem v1348_mb_checked : Scalar.distance (sourceCoefficient 14 96 3 1) v1348_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1348_mg : Scalar.QComplex := ((-93086147544512200533012 : Int)/10^30,(222372861367557400661 : Int)/10^30)
theorem v1348_mg_checked : Scalar.distance (sourceCoefficient 14 96 3 2) v1348_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1348_upper : Scalar.QComplex := ((999994712760977775684341581140 : Int)/10^30,(-3251837955610973119650259844 : Int)/10^30)
theorem v1348_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 96 5) 1) 14) v1348_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1348 : Material (14 : Basis) (96 : Basis) where
  plus := ![v1348_pa,v1348_pb,v1348_pg]
  minus := ![(Primitive.Addresses.material1348 1).one,v1348_mb,v1348_mg]
  upper := v1348_upper
  lower := (Primitive.Addresses.material1348 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1348_pa_checked.trans (by decide +kernel)
    · exact v1348_pb_checked.trans (by decide +kernel)
    · exact v1348_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 96 Primitive.Addresses.material1348
    · exact v1348_mb_checked.trans (by decide +kernel)
    · exact v1348_mg_checked.trans (by decide +kernel)
  upper_error := v1348_upper_checked
  lower_error := reuse_lower_error 14 96 Primitive.Addresses.material1348

def v1349_pa : Scalar.QComplex := ((999998721446627713488858340738 : Int)/10^30,(-1599095090941841550280009257 : Int)/10^30)
theorem v1349_pa_checked : Scalar.distance (sourceCoefficient 14 97 1 0) v1349_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1349_pb : Scalar.QComplex := ((-689973312184671049983279 : Int)/10^30,(-431476798300083075083155180 : Int)/10^30)
theorem v1349_pb_checked : Scalar.distance (sourceCoefficient 14 97 1 1) v1349_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1349_pg : Scalar.QComplex := ((-93086292431724883814567 : Int)/10^30,(148854023579361785721 : Int)/10^30)
theorem v1349_pg_checked : Scalar.distance (sourceCoefficient 14 97 1 2) v1349_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1349_mb : Scalar.QComplex := ((-1062318099215436475373067 : Int)/10^30,(-431476042225658433161018822 : Int)/10^30)
theorem v1349_mb_checked : Scalar.distance (sourceCoefficient 14 97 3 1) v1349_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1349_mg : Scalar.QComplex := ((-93086129317125745118418 : Int)/10^30,(229183246071804387899 : Int)/10^30)
theorem v1349_mg_checked : Scalar.distance (sourceCoefficient 14 97 3 2) v1349_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1349_upper : Scalar.QComplex := ((999994472172942028058730649428 : Int)/10^30,(-3324999783319075600203068048 : Int)/10^30)
theorem v1349_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 97 5) 1) 14) v1349_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1349 : Material (14 : Basis) (97 : Basis) where
  plus := ![v1349_pa,v1349_pb,v1349_pg]
  minus := ![(Primitive.Addresses.material1349 1).one,v1349_mb,v1349_mg]
  upper := v1349_upper
  lower := (Primitive.Addresses.material1349 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1349_pa_checked.trans (by decide +kernel)
    · exact v1349_pb_checked.trans (by decide +kernel)
    · exact v1349_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 97 Primitive.Addresses.material1349
    · exact v1349_mb_checked.trans (by decide +kernel)
    · exact v1349_mg_checked.trans (by decide +kernel)
  upper_error := v1349_upper_checked
  lower_error := reuse_lower_error 14 97 Primitive.Addresses.material1349

def v1350_pa : Scalar.QComplex := ((999999993638524258836606022467 : Int)/10^30,(-112796061286990045101363690 : Int)/10^30)
theorem v1350_pa_checked : Scalar.distance (sourceCoefficient 15 16 1 0) v1350_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1350_pb : Scalar.QComplex := ((-48668964902658072941489 : Int)/10^30,(-431477518255020278956942550 : Int)/10^30)
theorem v1350_pb_checked : Scalar.distance (sourceCoefficient 15 16 1 1) v1350_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1350_pg : Scalar.QComplex := ((-93086429304722838849246 : Int)/10^30,(10499782651636696089 : Int)/10^30)
theorem v1350_pg_checked : Scalar.distance (sourceCoefficient 15 16 1 2) v1350_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1350_mb : Scalar.QComplex := ((-421014612009026288257298 : Int)/10^30,(-431477315597095993681325921 : Int)/10^30)
theorem v1350_mb_checked : Scalar.distance (sourceCoefficient 15 16 3 1) v1350_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1350_mg : Scalar.QComplex := ((-93086385583551413010560 : Int)/10^30,(90829174774919001043 : Int)/10^30)
theorem v1350_mg_checked : Scalar.distance (sourceCoefficient 15 16 3 2) v1350_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1350_upper : Scalar.QComplex := ((999998309580232982603129899417 : Int)/10^30,(-1838705163019836907384171071 : Int)/10^30)
theorem v1350_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 16 5) 1) 14) v1350_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1350 : Material (15 : Basis) (16 : Basis) where
  plus := ![v1350_pa,v1350_pb,v1350_pg]
  minus := ![(Primitive.Addresses.material1350 1).one,v1350_mb,v1350_mg]
  upper := v1350_upper
  lower := (Primitive.Addresses.material1350 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1350_pa_checked.trans (by decide +kernel)
    · exact v1350_pb_checked.trans (by decide +kernel)
    · exact v1350_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 16 Primitive.Addresses.material1350
    · exact v1350_mb_checked.trans (by decide +kernel)
    · exact v1350_mg_checked.trans (by decide +kernel)
  upper_error := v1350_upper_checked
  lower_error := reuse_lower_error 15 16 Primitive.Addresses.material1350

def v1351_pa : Scalar.QComplex := ((999999992861368103992513547655 : Int)/10^30,(-119487504539407414799771526 : Int)/10^30)
theorem v1351_pa_checked : Scalar.distance (sourceCoefficient 15 17 1 0) v1351_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1351_pb : Scalar.QComplex := ((-51556172248354362619727 : Int)/10^30,(-431477517913267771412741109 : Int)/10^30)
theorem v1351_pb_checked : Scalar.distance (sourceCoefficient 15 17 1 1) v1351_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1351_pg : Scalar.QComplex := ((-93086429231686859988718 : Int)/10^30,(11122665214779023425 : Int)/10^30)
theorem v1351_pg_checked : Scalar.distance (sourceCoefficient 15 17 1 2) v1351_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1351_mb : Scalar.QComplex := ((-423901817984766309189471 : Int)/10^30,(-431477312763813709043028275 : Int)/10^30)
theorem v1351_mb_checked : Scalar.distance (sourceCoefficient 15 17 3 1) v1351_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1351_mg : Scalar.QComplex := ((-93086384972995862942083 : Int)/10^30,(91452057043106922643 : Int)/10^30)
theorem v1351_mg_checked : Scalar.distance (sourceCoefficient 15 17 3 2) v1351_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1351_upper : Scalar.QComplex := ((999998297254253974559358488423 : Int)/10^30,(-1845396594964834564541806181 : Int)/10^30)
theorem v1351_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 17 5) 1) 14) v1351_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1351 : Material (15 : Basis) (17 : Basis) where
  plus := ![v1351_pa,v1351_pb,v1351_pg]
  minus := ![(Primitive.Addresses.material1351 1).one,v1351_mb,v1351_mg]
  upper := v1351_upper
  lower := (Primitive.Addresses.material1351 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1351_pa_checked.trans (by decide +kernel)
    · exact v1351_pb_checked.trans (by decide +kernel)
    · exact v1351_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 17 Primitive.Addresses.material1351
    · exact v1351_mb_checked.trans (by decide +kernel)
    · exact v1351_mg_checked.trans (by decide +kernel)
  upper_error := v1351_upper_checked
  lower_error := reuse_lower_error 15 17 Primitive.Addresses.material1351

def v1352_pa : Scalar.QComplex := ((999999989945300329812619778822 : Int)/10^30,(-141807613474304598018040153 : Int)/10^30)
theorem v1352_pa_checked : Scalar.distance (sourceCoefficient 15 18 1 0) v1352_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1352_pb : Scalar.QComplex := ((-61186797510243424122711 : Int)/10^30,(-431477516587045163209989040 : Int)/10^30)
theorem v1352_pb_checked : Scalar.distance (sourceCoefficient 15 18 1 1) v1352_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1352_pg : Scalar.QComplex := ((-93086428952904873359846 : Int)/10^30,(13200364469382551049 : Int)/10^30)
theorem v1352_pg_checked : Scalar.distance (sourceCoefficient 15 18 1 2) v1352_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1352_mb : Scalar.QComplex := ((-433532438516263064343252 : Int)/10^30,(-431477303126795740903644854 : Int)/10^30)
theorem v1352_mb_checked : Scalar.distance (sourceCoefficient 15 18 3 1) v1352_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1352_mg : Scalar.QComplex := ((-93086382901253099494360 : Int)/10^30,(93529755283511763645 : Int)/10^30)
theorem v1352_mg_checked : Scalar.distance (sourceCoefficient 15 18 3 2) v1352_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1352_upper : Scalar.QComplex := ((999998255815707386352531444860 : Int)/10^30,(-1867716665623682958772412028 : Int)/10^30)
theorem v1352_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 18 5) 1) 14) v1352_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1352 : Material (15 : Basis) (18 : Basis) where
  plus := ![v1352_pa,v1352_pb,v1352_pg]
  minus := ![(Primitive.Addresses.material1352 1).one,v1352_mb,v1352_mg]
  upper := v1352_upper
  lower := (Primitive.Addresses.material1352 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1352_pa_checked.trans (by decide +kernel)
    · exact v1352_pb_checked.trans (by decide +kernel)
    · exact v1352_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 18 Primitive.Addresses.material1352
    · exact v1352_mb_checked.trans (by decide +kernel)
    · exact v1352_mg_checked.trans (by decide +kernel)
  upper_error := v1352_upper_checked
  lower_error := reuse_lower_error 15 18 Primitive.Addresses.material1352

def v1353_pa : Scalar.QComplex := ((999999987603289850395627222397 : Int)/10^30,(-157459265035533310855472294 : Int)/10^30)
theorem v1353_pa_checked : Scalar.distance (sourceCoefficient 15 19 1 0) v1353_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1353_pb : Scalar.QComplex := ((-67940133310032363317935 : Int)/10^30,(-431477515486093488770370181 : Int)/10^30)
theorem v1353_pb_checked : Scalar.distance (sourceCoefficient 15 19 1 1) v1353_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1353_pg : Scalar.QComplex := ((-93086428725141195960378 : Int)/10^30,(14657320833545846689 : Int)/10^30)
theorem v1353_pg_checked : Scalar.distance (sourceCoefficient 15 19 1 2) v1353_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1353_mb : Scalar.QComplex := ((-440285770851404732565088 : Int)/10^30,(-431477296198019840134307246 : Int)/10^30)
theorem v1353_mb_checked : Scalar.distance (sourceCoefficient 15 19 3 1) v1353_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1353_mg : Scalar.QComplex := ((-93086381416201783507549 : Int)/10^30,(94986710908633823211 : Int)/10^30)
theorem v1353_mg_checked : Scalar.distance (sourceCoefficient 15 19 3 2) v1353_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1353_upper : Scalar.QComplex := ((999998226460369707142209673078 : Int)/10^30,(-1883368289831517621361981243 : Int)/10^30)
theorem v1353_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 19 5) 1) 14) v1353_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1353 : Material (15 : Basis) (19 : Basis) where
  plus := ![v1353_pa,v1353_pb,v1353_pg]
  minus := ![(Primitive.Addresses.material1353 1).one,v1353_mb,v1353_mg]
  upper := v1353_upper
  lower := (Primitive.Addresses.material1353 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1353_pa_checked.trans (by decide +kernel)
    · exact v1353_pb_checked.trans (by decide +kernel)
    · exact v1353_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 19 Primitive.Addresses.material1353
    · exact v1353_mb_checked.trans (by decide +kernel)
    · exact v1353_mg_checked.trans (by decide +kernel)
  upper_error := v1353_upper_checked
  lower_error := reuse_lower_error 15 19 Primitive.Addresses.material1353

def v1354_pa : Scalar.QComplex := ((999999987157613188659790749159 : Int)/10^30,(-160264698102088344743190162 : Int)/10^30)
theorem v1354_pa_checked : Scalar.distance (sourceCoefficient 15 20 1 0) v1354_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1354_pb : Scalar.QComplex := ((-69150614611263661475609 : Int)/10^30,(-431477515273862089501668138 : Int)/10^30)
theorem v1354_pb_checked : Scalar.distance (sourceCoefficient 15 20 1 1) v1354_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1354_pg : Scalar.QComplex := ((-93086428681504700741255 : Int)/10^30,(14918468581631672630 : Int)/10^30)
theorem v1354_pg_checked : Scalar.distance (sourceCoefficient 15 20 1 2) v1354_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1354_mb : Scalar.QComplex := ((-441496251518772381524438 : Int)/10^30,(-431477294941197674980446458 : Int)/10^30)
theorem v1354_mb_checked : Scalar.distance (sourceCoefficient 15 20 3 1) v1354_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1354_mg : Scalar.QComplex := ((-93086381147206559596181 : Int)/10^30,(95247858521826077439 : Int)/10^30)
theorem v1354_mg_checked : Scalar.distance (sourceCoefficient 15 20 3 2) v1354_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1354_upper : Scalar.QComplex := ((999998221172770743215118582780 : Int)/10^30,(-1886173717950512165248416241 : Int)/10^30)
theorem v1354_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 20 5) 1) 14) v1354_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1354 : Material (15 : Basis) (20 : Basis) where
  plus := ![v1354_pa,v1354_pb,v1354_pg]
  minus := ![(Primitive.Addresses.material1354 1).one,v1354_mb,v1354_mg]
  upper := v1354_upper
  lower := (Primitive.Addresses.material1354 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1354_pa_checked.trans (by decide +kernel)
    · exact v1354_pb_checked.trans (by decide +kernel)
    · exact v1354_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 20 Primitive.Addresses.material1354
    · exact v1354_mb_checked.trans (by decide +kernel)
    · exact v1354_mg_checked.trans (by decide +kernel)
  upper_error := v1354_upper_checked
  lower_error := reuse_lower_error 15 20 Primitive.Addresses.material1354

def v1355_pa : Scalar.QComplex := ((999999977257202604167934818307 : Int)/10^30,(-213273519862240040293195411 : Int)/10^30)
theorem v1355_pa_checked : Scalar.distance (sourceCoefficient 15 21 1 0) v1355_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1355_pb : Scalar.QComplex := ((-92022729479962313980509 : Int)/10^30,(-431477510412677326538740858 : Int)/10^30)
theorem v1355_pb_checked : Scalar.distance (sourceCoefficient 15 21 1 1) v1355_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1355_pg : Scalar.QComplex := ((-93086427696334751338266 : Int)/10^30,(19852870537709033352 : Int)/10^30)
theorem v1355_pg_checked : Scalar.distance (sourceCoefficient 15 21 1 2) v1355_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1355_mb : Scalar.QComplex := ((-464368353676153850321399 : Int)/10^30,(-431477270342409712185603414 : Int)/10^30)
theorem v1355_mb_checked : Scalar.distance (sourceCoefficient 15 21 3 1) v1355_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1355_mg : Scalar.QComplex := ((-93086375903870326136494 : Int)/10^30,(100182257790442780676 : Int)/10^30)
theorem v1355_mg_checked : Scalar.distance (sourceCoefficient 15 21 3 2) v1355_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1355_upper : Scalar.QComplex := ((999998119783957468944855810064 : Int)/10^30,(-1939182443673040192068282499 : Int)/10^30)
theorem v1355_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 21 5) 1) 14) v1355_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1355 : Material (15 : Basis) (21 : Basis) where
  plus := ![v1355_pa,v1355_pb,v1355_pg]
  minus := ![(Primitive.Addresses.material1355 1).one,v1355_mb,v1355_mg]
  upper := v1355_upper
  lower := (Primitive.Addresses.material1355 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1355_pa_checked.trans (by decide +kernel)
    · exact v1355_pb_checked.trans (by decide +kernel)
    · exact v1355_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 21 Primitive.Addresses.material1355
    · exact v1355_mb_checked.trans (by decide +kernel)
    · exact v1355_mg_checked.trans (by decide +kernel)
  upper_error := v1355_upper_checked
  lower_error := reuse_lower_error 15 21 Primitive.Addresses.material1355

def v1356_pa : Scalar.QComplex := ((999999976958906643483994080226 : Int)/10^30,(-214667617916955580997237265 : Int)/10^30)
theorem v1356_pa_checked : Scalar.distance (sourceCoefficient 15 22 1 0) v1356_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1356_pb : Scalar.QComplex := ((-92624251447064190303276 : Int)/10^30,(-431477510263014912601339880 : Int)/10^30)
theorem v1356_pb_checked : Scalar.distance (sourceCoefficient 15 22 1 1) v1356_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1356_pg : Scalar.QComplex := ((-93086427666307105752541 : Int)/10^30,(19982642147947060186 : Int)/10^30)
theorem v1356_pg_checked : Scalar.distance (sourceCoefficient 15 22 1 2) v1356_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1356_mb : Scalar.QComplex := ((-464969875290129684697087 : Int)/10^30,(-431477269673660987909152681 : Int)/10^30)
theorem v1356_mb_checked : Scalar.distance (sourceCoefficient 15 22 3 1) v1356_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1356_mg : Scalar.QComplex := ((-93086375761855636792376 : Int)/10^30,(100312029326448400417 : Int)/10^30)
theorem v1356_mg_checked : Scalar.distance (sourceCoefficient 15 22 3 2) v1356_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1356_upper : Scalar.QComplex := ((999998117079575181686266918868 : Int)/10^30,(-1940576539136578675592385836 : Int)/10^30)
theorem v1356_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 22 5) 1) 14) v1356_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1356 : Material (15 : Basis) (22 : Basis) where
  plus := ![v1356_pa,v1356_pb,v1356_pg]
  minus := ![(Primitive.Addresses.material1356 1).one,v1356_mb,v1356_mg]
  upper := v1356_upper
  lower := (Primitive.Addresses.material1356 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1356_pa_checked.trans (by decide +kernel)
    · exact v1356_pb_checked.trans (by decide +kernel)
    · exact v1356_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 22 Primitive.Addresses.material1356
    · exact v1356_mb_checked.trans (by decide +kernel)
    · exact v1356_mg_checked.trans (by decide +kernel)
  upper_error := v1356_upper_checked
  lower_error := reuse_lower_error 15 22 Primitive.Addresses.material1356

def v1357_pa : Scalar.QComplex := ((999999974692817370001603675998 : Int)/10^30,(-224976364579800471048021376 : Int)/10^30)
theorem v1357_pa_checked : Scalar.distance (sourceCoefficient 15 23 1 0) v1357_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1357_pb : Scalar.QComplex := ((-97072243856755646072044 : Int)/10^30,(-431477509121623902900505307 : Int)/10^30)
theorem v1357_pb_checked : Scalar.distance (sourceCoefficient 15 23 1 1) v1357_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1357_pg : Scalar.QComplex := ((-93086427437714879191513 : Int)/10^30,(20942246566647743010 : Int)/10^30)
theorem v1357_pg_checked : Scalar.distance (sourceCoefficient 15 23 1 2) v1357_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1357_mb : Scalar.QComplex := ((-469417865058661248013169 : Int)/10^30,(-431477264693853283778156927 : Int)/10^30)
theorem v1357_mb_checked : Scalar.distance (sourceCoefficient 15 23 3 1) v1357_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1357_mg : Scalar.QComplex := ((-93086374705168100986647 : Int)/10^30,(101271633190579705960 : Int)/10^30)
theorem v1357_mg_checked : Scalar.distance (sourceCoefficient 15 23 3 2) v1357_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1357_upper : Scalar.QComplex := ((999998097021527745399230268047 : Int)/10^30,(-1950885266534691853765750549 : Int)/10^30)
theorem v1357_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 23 5) 1) 14) v1357_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1357 : Material (15 : Basis) (23 : Basis) where
  plus := ![v1357_pa,v1357_pb,v1357_pg]
  minus := ![(Primitive.Addresses.material1357 1).one,v1357_mb,v1357_mg]
  upper := v1357_upper
  lower := (Primitive.Addresses.material1357 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1357_pa_checked.trans (by decide +kernel)
    · exact v1357_pb_checked.trans (by decide +kernel)
    · exact v1357_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 23 Primitive.Addresses.material1357
    · exact v1357_mb_checked.trans (by decide +kernel)
    · exact v1357_mg_checked.trans (by decide +kernel)
  upper_error := v1357_upper_checked
  lower_error := reuse_lower_error 15 23 Primitive.Addresses.material1357

def v1358_pa : Scalar.QComplex := ((999999961933430602184075294276 : Int)/10^30,(-275922339339474547904346332 : Int)/10^30)
theorem v1358_pa_checked : Scalar.distance (sourceCoefficient 15 24 1 0) v1358_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1358_pb : Scalar.QComplex := ((-119054286417094483067019 : Int)/10^30,(-431477502583183730342743178 : Int)/10^30)
theorem v1358_pb_checked : Scalar.distance (sourceCoefficient 15 24 1 1) v1358_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1358_pg : Scalar.QComplex := ((-93086426138554477163760 : Int)/10^30,(25684625438626738564 : Int)/10^30)
theorem v1358_pg_checked : Scalar.distance (sourceCoefficient 15 24 1 2) v1358_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1358_mb : Scalar.QComplex := ((-491399893791701622315705 : Int)/10^30,(-431477239185902850653187718 : Int)/10^30)
theorem v1358_mb_checked : Scalar.distance (sourceCoefficient 15 24 3 1) v1358_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1358_mg : Scalar.QComplex := ((-93086369313548804993417 : Int)/10^30,(106014009175637395117 : Int)/10^30)
theorem v1358_mg_checked : Scalar.distance (sourceCoefficient 15 24 3 2) v1358_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1358_upper : Scalar.QComplex := ((999997996334029328718825306306 : Int)/10^30,(-2001831143394777021945887939 : Int)/10^30)
theorem v1358_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 24 5) 1) 14) v1358_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1358 : Material (15 : Basis) (24 : Basis) where
  plus := ![v1358_pa,v1358_pb,v1358_pg]
  minus := ![(Primitive.Addresses.material1358 1).one,v1358_mb,v1358_mg]
  upper := v1358_upper
  lower := (Primitive.Addresses.material1358 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1358_pa_checked.trans (by decide +kernel)
    · exact v1358_pb_checked.trans (by decide +kernel)
    · exact v1358_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 24 Primitive.Addresses.material1358
    · exact v1358_mb_checked.trans (by decide +kernel)
    · exact v1358_mg_checked.trans (by decide +kernel)
  upper_error := v1358_upper_checked
  lower_error := reuse_lower_error 15 24 Primitive.Addresses.material1358

def v1359_pa : Scalar.QComplex := ((999999955327398074960301842119 : Int)/10^30,(-298906677500583839938973356 : Int)/10^30)
theorem v1359_pa_checked : Scalar.distance (sourceCoefficient 15 25 1 0) v1359_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1359_pb : Scalar.QComplex := ((-128971511447057251677390 : Int)/10^30,(-431477499144569452904014530 : Int)/10^30)
theorem v1359_pb_checked : Scalar.distance (sourceCoefficient 15 25 1 1) v1359_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1359_pg : Scalar.QComplex := ((-93086425460167277525359 : Int)/10^30,(27824155397681775073 : Int)/10^30)
theorem v1359_pg_checked : Scalar.distance (sourceCoefficient 15 25 1 2) v1359_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1359_mb : Scalar.QComplex := ((-501317112161659020704988 : Int)/10^30,(-431477227189171307944565516 : Int)/10^30)
theorem v1359_mb_checked : Scalar.distance (sourceCoefficient 15 25 3 1) v1359_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1359_mg : Scalar.QComplex := ((-93086366788843864137351 : Int)/10^30,(108153537752630046658 : Int)/10^30)
theorem v1359_mg_checked : Scalar.distance (sourceCoefficient 15 25 3 2) v1359_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1359_upper : Scalar.QComplex := ((999997950059124097199753849933 : Int)/10^30,(-2024815435922001705629572305 : Int)/10^30)
theorem v1359_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 25 5) 1) 14) v1359_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1359 : Material (15 : Basis) (25 : Basis) where
  plus := ![v1359_pa,v1359_pb,v1359_pg]
  minus := ![(Primitive.Addresses.material1359 1).one,v1359_mb,v1359_mg]
  upper := v1359_upper
  lower := (Primitive.Addresses.material1359 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1359_pa_checked.trans (by decide +kernel)
    · exact v1359_pb_checked.trans (by decide +kernel)
    · exact v1359_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 25 Primitive.Addresses.material1359
    · exact v1359_mb_checked.trans (by decide +kernel)
    · exact v1359_mg_checked.trans (by decide +kernel)
  upper_error := v1359_upper_checked
  lower_error := reuse_lower_error 15 25 Primitive.Addresses.material1359

def v1360_pa : Scalar.QComplex := ((999999953105281439731579991058 : Int)/10^30,(-306250608034371437345715867 : Int)/10^30)
theorem v1360_pa_checked : Scalar.distance (sourceCoefficient 15 26 1 0) v1360_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1360_pb : Scalar.QComplex := ((-132140252306755129680148 : Int)/10^30,(-431477497981798898123457221 : Int)/10^30)
theorem v1360_pb_checked : Scalar.distance (sourceCoefficient 15 26 1 1) v1360_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1360_pg : Scalar.QComplex := ((-93086425231315480553644 : Int)/10^30,(28507775663700537320 : Int)/10^30)
theorem v1360_pg_checked : Scalar.distance (sourceCoefficient 15 26 1 2) v1360_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1360_mb : Scalar.QComplex := ((-504485850838071238496882 : Int)/10^30,(-431477223291920538987857018 : Int)/10^30)
theorem v1360_mb_checked : Scalar.distance (sourceCoefficient 15 26 3 1) v1360_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1360_mg : Scalar.QComplex := ((-93086365970058651917263 : Int)/10^30,(108837157566616947192 : Int)/10^30)
theorem v1360_mg_checked : Scalar.distance (sourceCoefficient 15 26 3 2) v1360_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1360_upper : Scalar.QComplex := ((999997935162052906409012720341 : Int)/10^30,(-2032159351682695728081707643 : Int)/10^30)
theorem v1360_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 26 5) 1) 14) v1360_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1360 : Material (15 : Basis) (26 : Basis) where
  plus := ![v1360_pa,v1360_pb,v1360_pg]
  minus := ![(Primitive.Addresses.material1360 1).one,v1360_mb,v1360_mg]
  upper := v1360_upper
  lower := (Primitive.Addresses.material1360 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1360_pa_checked.trans (by decide +kernel)
    · exact v1360_pb_checked.trans (by decide +kernel)
    · exact v1360_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 26 Primitive.Addresses.material1360
    · exact v1360_mb_checked.trans (by decide +kernel)
    · exact v1360_mg_checked.trans (by decide +kernel)
  upper_error := v1360_upper_checked
  lower_error := reuse_lower_error 15 26 Primitive.Addresses.material1360

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
