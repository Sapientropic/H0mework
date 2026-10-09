import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B060
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B061

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1457_pa : Scalar.QComplex := ((999999854619053139135208403439 : Int)/10^30,(-539223397661961505718321440 : Int)/10^30)
theorem v1457_pa_checked : Scalar.distance (sourceCoefficient 16 42 1 0) v1457_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1457_pb : Scalar.QComplex := ((-232662767947265588404593 : Int)/10^30,(-431477445398962585300552720 : Int)/10^30)
theorem v1457_pb_checked : Scalar.distance (sourceCoefficient 16 42 1 1) v1457_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1457_pg : Scalar.QComplex := ((-93086414975371564617145 : Int)/10^30,(50194380256497678613 : Int)/10^30)
theorem v1457_pg_checked : Scalar.distance (sourceCoefficient 16 42 1 2) v1457_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1457_mb : Scalar.QComplex := ((-605008283672835523409124 : Int)/10^30,(-431477083962700173438261495 : Int)/10^30)
theorem v1457_mb_checked : Scalar.distance (sourceCoefficient 16 42 3 1) v1457_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1457_mg : Scalar.QComplex := ((-93086336999555519566467 : Int)/10^30,(130523745234082382908 : Int)/10^30)
theorem v1457_mg_checked : Scalar.distance (sourceCoefficient 16 42 3 2) v1457_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1457_upper : Scalar.QComplex := ((999997434586071518636699866112 : Int)/10^30,(-2265131624346387106457699453 : Int)/10^30)
theorem v1457_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 42 5) 1) 14) v1457_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1457 : Material (16 : Basis) (42 : Basis) where
  plus := ![v1457_pa,v1457_pb,v1457_pg]
  minus := ![(Primitive.Addresses.material1457 1).one,v1457_mb,v1457_mg]
  upper := v1457_upper
  lower := (Primitive.Addresses.material1457 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1457_pa_checked.trans (by decide +kernel)
    · exact v1457_pb_checked.trans (by decide +kernel)
    · exact v1457_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 42 Primitive.Addresses.material1457
    · exact v1457_mb_checked.trans (by decide +kernel)
    · exact v1457_mg_checked.trans (by decide +kernel)
  upper_error := v1457_upper_checked
  lower_error := reuse_lower_error 16 42 Primitive.Addresses.material1457

def v1458_pa : Scalar.QComplex := ((999999846153286487033572271205 : Int)/10^30,(-554701183843266731419358978 : Int)/10^30)
theorem v1458_pa_checked : Scalar.distance (sourceCoefficient 16 43 1 0) v1458_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1458_pb : Scalar.QComplex := ((-239341084028102785802917 : Int)/10^30,(-431477440787093162328519137 : Int)/10^30)
theorem v1458_pb_checked : Scalar.distance (sourceCoefficient 16 43 1 1) v1458_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1458_pg : Scalar.QComplex := ((-93086414083868048342387 : Int)/10^30,(51635152035944586248 : Int)/10^30)
theorem v1458_pg_checked : Scalar.distance (sourceCoefficient 16 43 1 2) v1458_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1458_mb : Scalar.QComplex := ((-611686593287194828652337 : Int)/10^30,(-431477073587746470104280961 : Int)/10^30)
theorem v1458_mb_checked : Scalar.distance (sourceCoefficient 16 43 3 1) v1458_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1458_mg : Scalar.QComplex := ((-93086334864731179528649 : Int)/10^30,(131964515707736727814 : Int)/10^30)
theorem v1458_mg_checked : Scalar.distance (sourceCoefficient 16 43 3 2) v1458_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1458_upper : Scalar.QComplex := ((999997399407062660161090416862 : Int)/10^30,(-2280609372864202730411327102 : Int)/10^30)
theorem v1458_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 43 5) 1) 14) v1458_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1458 : Material (16 : Basis) (43 : Basis) where
  plus := ![v1458_pa,v1458_pb,v1458_pg]
  minus := ![(Primitive.Addresses.material1458 1).one,v1458_mb,v1458_mg]
  upper := v1458_upper
  lower := (Primitive.Addresses.material1458 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1458_pa_checked.trans (by decide +kernel)
    · exact v1458_pb_checked.trans (by decide +kernel)
    · exact v1458_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 43 Primitive.Addresses.material1458
    · exact v1458_mb_checked.trans (by decide +kernel)
    · exact v1458_mg_checked.trans (by decide +kernel)
  upper_error := v1458_upper_checked
  lower_error := reuse_lower_error 16 43 Primitive.Addresses.material1458

def v1459_pa : Scalar.QComplex := ((999999842887933633720244768288 : Int)/10^30,(-560556962358294246332769853 : Int)/10^30)
theorem v1459_pa_checked : Scalar.distance (sourceCoefficient 16 44 1 0) v1459_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1459_pb : Scalar.QComplex := ((-241867720535861692118405 : Int)/10^30,(-431477439006329650418169661 : Int)/10^30)
theorem v1459_pb_checked : Scalar.distance (sourceCoefficient 16 44 1 1) v1459_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1459_pg : Scalar.QComplex := ((-93086413739798163378359 : Int)/10^30,(52180245520954840708 : Int)/10^30)
theorem v1459_pg_checked : Scalar.distance (sourceCoefficient 16 44 1 2) v1459_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1459_mb : Scalar.QComplex := ((-614213227317452781968982 : Int)/10^30,(-431477069626610110541658261 : Int)/10^30)
theorem v1459_mb_checked : Scalar.distance (sourceCoefficient 16 44 3 1) v1459_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1459_mg : Scalar.QComplex := ((-93086334050270295212936 : Int)/10^30,(132509608692866951411 : Int)/10^30)
theorem v1459_mg_checked : Scalar.distance (sourceCoefficient 16 44 3 2) v1459_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1459_upper : Scalar.QComplex := ((999997386035172185346897934401 : Int)/10^30,(-2286465137022033220933749388 : Int)/10^30)
theorem v1459_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 44 5) 1) 14) v1459_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1459 : Material (16 : Basis) (44 : Basis) where
  plus := ![v1459_pa,v1459_pb,v1459_pg]
  minus := ![(Primitive.Addresses.material1459 1).one,v1459_mb,v1459_mg]
  upper := v1459_upper
  lower := (Primitive.Addresses.material1459 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1459_pa_checked.trans (by decide +kernel)
    · exact v1459_pb_checked.trans (by decide +kernel)
    · exact v1459_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 44 Primitive.Addresses.material1459
    · exact v1459_mb_checked.trans (by decide +kernel)
    · exact v1459_mg_checked.trans (by decide +kernel)
  upper_error := v1459_upper_checked
  lower_error := reuse_lower_error 16 44 Primitive.Addresses.material1459

def v1460_pa : Scalar.QComplex := ((999999841250606168785298838055 : Int)/10^30,(-563470285339927539772776193 : Int)/10^30)
theorem v1460_pa_checked : Scalar.distance (sourceCoefficient 16 45 1 0) v1460_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1460_pb : Scalar.QComplex := ((-243124753767196576835093 : Int)/10^30,(-431477438113028847517808275 : Int)/10^30)
theorem v1460_pb_checked : Scalar.distance (sourceCoefficient 16 45 1 1) v1460_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1460_pg : Scalar.QComplex := ((-93086413567231870820138 : Int)/10^30,(52451436340632369114 : Int)/10^30)
theorem v1460_pg_checked : Scalar.distance (sourceCoefficient 16 45 1 2) v1460_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1460_mb : Scalar.QComplex := ((-615470259309858385274609 : Int)/10^30,(-431477067648546576291109944 : Int)/10^30)
theorem v1460_mb_checked : Scalar.distance (sourceCoefficient 16 45 3 1) v1460_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1460_mg : Scalar.QComplex := ((-93086333643678603508440 : Int)/10^30,(132780799262650805238 : Int)/10^30)
theorem v1460_mg_checked : Scalar.distance (sourceCoefficient 16 45 3 2) v1460_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1460_upper : Scalar.QComplex := ((999997379369715987316150237869 : Int)/10^30,(-2289378452838735488897832768 : Int)/10^30)
theorem v1460_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 45 5) 1) 14) v1460_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1460 : Material (16 : Basis) (45 : Basis) where
  plus := ![v1460_pa,v1460_pb,v1460_pg]
  minus := ![(Primitive.Addresses.material1460 1).one,v1460_mb,v1460_mg]
  upper := v1460_upper
  lower := (Primitive.Addresses.material1460 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1460_pa_checked.trans (by decide +kernel)
    · exact v1460_pb_checked.trans (by decide +kernel)
    · exact v1460_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 45 Primitive.Addresses.material1460
    · exact v1460_mb_checked.trans (by decide +kernel)
    · exact v1460_mg_checked.trans (by decide +kernel)
  upper_error := v1460_upper_checked
  lower_error := reuse_lower_error 16 45 Primitive.Addresses.material1460

def v1461_pa : Scalar.QComplex := ((999999831895947156126011218060 : Int)/10^30,(-579834525902671127778296917 : Int)/10^30)
theorem v1461_pa_checked : Scalar.distance (sourceCoefficient 16 46 1 0) v1461_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1461_pb : Scalar.QComplex := ((-250185554861119388804116 : Int)/10^30,(-431477433004582527395097898 : Int)/10^30)
theorem v1461_pb_checked : Scalar.distance (sourceCoefficient 16 46 1 1) v1461_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1461_pg : Scalar.QComplex := ((-93086412580791001660223 : Int)/10^30,(53974724980133411891 : Int)/10^30)
theorem v1461_pg_checked : Scalar.distance (sourceCoefficient 16 46 1 2) v1461_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1461_mb : Scalar.QComplex := ((-622531053366363157040284 : Int)/10^30,(-431477056446948820897352911 : Int)/10^30)
theorem v1461_mb_checked : Scalar.distance (sourceCoefficient 16 46 3 1) v1461_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1461_mg : Scalar.QComplex := ((-93086331342708612129678 : Int)/10^30,(134304086483707827361 : Int)/10^30)
theorem v1461_mg_checked : Scalar.distance (sourceCoefficient 16 46 3 2) v1461_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1461_upper : Scalar.QComplex := ((999997341771876248334319519144 : Int)/10^30,(-2305742652883572229612418224 : Int)/10^30)
theorem v1461_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 46 5) 1) 14) v1461_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1461 : Material (16 : Basis) (46 : Basis) where
  plus := ![v1461_pa,v1461_pb,v1461_pg]
  minus := ![(Primitive.Addresses.material1461 1).one,v1461_mb,v1461_mg]
  upper := v1461_upper
  lower := (Primitive.Addresses.material1461 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1461_pa_checked.trans (by decide +kernel)
    · exact v1461_pb_checked.trans (by decide +kernel)
    · exact v1461_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 46 Primitive.Addresses.material1461
    · exact v1461_mb_checked.trans (by decide +kernel)
    · exact v1461_mg_checked.trans (by decide +kernel)
  upper_error := v1461_upper_checked
  lower_error := reuse_lower_error 16 46 Primitive.Addresses.material1461

def v1462_pa : Scalar.QComplex := ((999999829604779943290227071907 : Int)/10^30,(-583772567939680193809654814 : Int)/10^30)
theorem v1462_pa_checked : Scalar.distance (sourceCoefficient 16 47 1 0) v1462_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1462_pb : Scalar.QComplex := ((-251884731261977865794857 : Int)/10^30,(-431477431752240692035632149 : Int)/10^30)
theorem v1462_pb_checked : Scalar.distance (sourceCoefficient 16 47 1 1) v1462_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1462_pg : Scalar.QComplex := ((-93086412339063369720389 : Int)/10^30,(54341303230965277914 : Int)/10^30)
theorem v1462_pg_checked : Scalar.distance (sourceCoefficient 16 47 1 2) v1462_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1462_mb : Scalar.QComplex := ((-624230228053826003260855 : Int)/10^30,(-431477053728294745965361059 : Int)/10^30)
theorem v1462_mb_checked : Scalar.distance (sourceCoefficient 16 47 3 1) v1462_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1462_mg : Scalar.QComplex := ((-93086330784640549799723 : Int)/10^30,(134670664389445797789 : Int)/10^30)
theorem v1462_mg_checked : Scalar.distance (sourceCoefficient 16 47 3 2) v1462_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1462_upper : Scalar.QComplex := ((999997332684009148428175265451 : Int)/10^30,(-2309680685100983520143285628 : Int)/10^30)
theorem v1462_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 47 5) 1) 14) v1462_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1462 : Material (16 : Basis) (47 : Basis) where
  plus := ![v1462_pa,v1462_pb,v1462_pg]
  minus := ![(Primitive.Addresses.material1462 1).one,v1462_mb,v1462_mg]
  upper := v1462_upper
  lower := (Primitive.Addresses.material1462 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1462_pa_checked.trans (by decide +kernel)
    · exact v1462_pb_checked.trans (by decide +kernel)
    · exact v1462_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 47 Primitive.Addresses.material1462
    · exact v1462_mb_checked.trans (by decide +kernel)
    · exact v1462_mg_checked.trans (by decide +kernel)
  upper_error := v1462_upper_checked
  lower_error := reuse_lower_error 16 47 Primitive.Addresses.material1462

def v1463_pa : Scalar.QComplex := ((999999813215348965695628971110 : Int)/10^30,(-611203130865756347894835222 : Int)/10^30)
theorem v1463_pa_checked : Scalar.distance (sourceCoefficient 16 48 1 0) v1463_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1463_pb : Scalar.QComplex := ((-263720400960863200144862 : Int)/10^30,(-431477422781499529128418175 : Int)/10^30)
theorem v1463_pb_checked : Scalar.distance (sourceCoefficient 16 48 1 1) v1463_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1463_pg : Scalar.QComplex := ((-93086410608578226504393 : Int)/10^30,(56894716232078084881 : Int)/10^30)
theorem v1463_pg_checked : Scalar.distance (sourceCoefficient 16 48 1 2) v1463_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1463_mb : Scalar.QComplex := ((-636065885604404995483635 : Int)/10^30,(-431477034543907031912187531 : Int)/10^30)
theorem v1463_mb_checked : Scalar.distance (sourceCoefficient 16 48 3 1) v1463_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1463_mg : Scalar.QComplex := ((-93086326850675632414596 : Int)/10^30,(137224074946475507265 : Int)/10^30)
theorem v1463_mg_checked : Scalar.distance (sourceCoefficient 16 48 3 2) v1463_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1463_upper : Scalar.QComplex := ((999997268951939451788043578047 : Int)/10^30,(-2337111178885787386343433403 : Int)/10^30)
theorem v1463_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 48 5) 1) 14) v1463_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1463 : Material (16 : Basis) (48 : Basis) where
  plus := ![v1463_pa,v1463_pb,v1463_pg]
  minus := ![(Primitive.Addresses.material1463 1).one,v1463_mb,v1463_mg]
  upper := v1463_upper
  lower := (Primitive.Addresses.material1463 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1463_pa_checked.trans (by decide +kernel)
    · exact v1463_pb_checked.trans (by decide +kernel)
    · exact v1463_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 48 Primitive.Addresses.material1463
    · exact v1463_mb_checked.trans (by decide +kernel)
    · exact v1463_mg_checked.trans (by decide +kernel)
  upper_error := v1463_upper_checked
  lower_error := reuse_lower_error 16 48 Primitive.Addresses.material1463

def v1464_pa : Scalar.QComplex := ((999999799502574485943972468780 : Int)/10^30,(-633241510664686619214355400 : Int)/10^30)
theorem v1464_pa_checked : Scalar.distance (sourceCoefficient 16 49 1 0) v1464_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1464_pb : Scalar.QComplex := ((-273229465039112125557393 : Int)/10^30,(-431477415260586038043726023 : Int)/10^30)
theorem v1464_pb_checked : Scalar.distance (sourceCoefficient 16 49 1 1) v1464_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1464_pg : Scalar.QComplex := ((-93086409159065301528069 : Int)/10^30,(58946190176797006637 : Int)/10^30)
theorem v1464_pg_checked : Scalar.distance (sourceCoefficient 16 49 1 2) v1464_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1464_mb : Scalar.QComplex := ((-645574939651785165430069 : Int)/10^30,(-431477018817102314026355681 : Int)/10^30)
theorem v1464_mb_checked : Scalar.distance (sourceCoefficient 16 49 3 1) v1464_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1464_mg : Scalar.QComplex := ((-93086323630833627822359 : Int)/10^30,(139275546876472551795 : Int)/10^30)
theorem v1464_mg_checked : Scalar.distance (sourceCoefficient 16 49 3 2) v1464_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1464_upper : Scalar.QComplex := ((999997217202941168847146738089 : Int)/10^30,(-2359149502194135018233223113 : Int)/10^30)
theorem v1464_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 49 5) 1) 14) v1464_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1464 : Material (16 : Basis) (49 : Basis) where
  plus := ![v1464_pa,v1464_pb,v1464_pg]
  minus := ![(Primitive.Addresses.material1464 1).one,v1464_mb,v1464_mg]
  upper := v1464_upper
  lower := (Primitive.Addresses.material1464 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1464_pa_checked.trans (by decide +kernel)
    · exact v1464_pb_checked.trans (by decide +kernel)
    · exact v1464_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 49 Primitive.Addresses.material1464
    · exact v1464_mb_checked.trans (by decide +kernel)
    · exact v1464_mg_checked.trans (by decide +kernel)
  upper_error := v1464_upper_checked
  lower_error := reuse_lower_error 16 49 Primitive.Addresses.material1464

def v1465_pa : Scalar.QComplex := ((999999797868483555942336470932 : Int)/10^30,(-635816791246476430364538847 : Int)/10^30)
theorem v1465_pa_checked : Scalar.distance (sourceCoefficient 16 50 1 0) v1465_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1465_pb : Scalar.QComplex := ((-274340640548817325218434 : Int)/10^30,(-431477414363501161416504862 : Int)/10^30)
theorem v1465_pb_checked : Scalar.distance (sourceCoefficient 16 50 1 1) v1465_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1465_pg : Scalar.QComplex := ((-93086408986241461957424 : Int)/10^30,(59185913833627730614 : Int)/10^30)
theorem v1465_pg_checked : Scalar.distance (sourceCoefficient 16 50 1 2) v1465_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1465_mb : Scalar.QComplex := ((-646686113973605094272043 : Int)/10^30,(-431477016961123352036426899 : Int)/10^30)
theorem v1465_mb_checked : Scalar.distance (sourceCoefficient 16 50 3 1) v1465_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1465_mg : Scalar.QComplex := ((-93086323251139133509722 : Int)/10^30,(139515270294904012569 : Int)/10^30)
theorem v1465_mg_checked : Scalar.distance (sourceCoefficient 16 50 3 2) v1465_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1465_upper : Scalar.QComplex := ((999997211124152016092164211750 : Int)/10^30,(-2361724776120054214903379598 : Int)/10^30)
theorem v1465_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 50 5) 1) 14) v1465_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1465 : Material (16 : Basis) (50 : Basis) where
  plus := ![v1465_pa,v1465_pb,v1465_pg]
  minus := ![(Primitive.Addresses.material1465 1).one,v1465_mb,v1465_mg]
  upper := v1465_upper
  lower := (Primitive.Addresses.material1465 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1465_pa_checked.trans (by decide +kernel)
    · exact v1465_pb_checked.trans (by decide +kernel)
    · exact v1465_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 50 Primitive.Addresses.material1465
    · exact v1465_mb_checked.trans (by decide +kernel)
    · exact v1465_mg_checked.trans (by decide +kernel)
  upper_error := v1465_upper_checked
  lower_error := reuse_lower_error 16 50 Primitive.Addresses.material1465

def v1466_pa : Scalar.QComplex := ((999999790620393834401479506497 : Int)/10^30,(-647116039432942477058913537 : Int)/10^30)
theorem v1466_pa_checked : Scalar.distance (sourceCoefficient 16 51 1 0) v1466_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1466_pb : Scalar.QComplex := ((-279216011373562933995835 : Int)/10^30,(-431477410382374309569600984 : Int)/10^30)
theorem v1466_pb_checked : Scalar.distance (sourceCoefficient 16 51 1 1) v1466_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1466_pg : Scalar.QComplex := ((-93086408219450357898184 : Int)/10^30,(60237720424558997323 : Int)/10^30)
theorem v1466_pg_checked : Scalar.distance (sourceCoefficient 16 51 1 2) v1466_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1466_mb : Scalar.QComplex := ((-651561479547494159696134 : Int)/10^30,(-431477008772772539340343662 : Int)/10^30)
theorem v1466_mb_checked : Scalar.distance (sourceCoefficient 16 51 3 1) v1466_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1466_mg : Scalar.QComplex := ((-93086321576686598598510 : Int)/10^30,(140567075832493427725 : Int)/10^30)
theorem v1466_mg_checked : Scalar.distance (sourceCoefficient 16 51 3 2) v1466_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1466_upper : Scalar.QComplex := ((999997184374595779677279024213 : Int)/10^30,(-2373023994968072072970091785 : Int)/10^30)
theorem v1466_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 51 5) 1) 14) v1466_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1466 : Material (16 : Basis) (51 : Basis) where
  plus := ![v1466_pa,v1466_pb,v1466_pg]
  minus := ![(Primitive.Addresses.material1466 1).one,v1466_mb,v1466_mg]
  upper := v1466_upper
  lower := (Primitive.Addresses.material1466 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1466_pa_checked.trans (by decide +kernel)
    · exact v1466_pb_checked.trans (by decide +kernel)
    · exact v1466_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 51 Primitive.Addresses.material1466
    · exact v1466_mb_checked.trans (by decide +kernel)
    · exact v1466_mg_checked.trans (by decide +kernel)
  upper_error := v1466_upper_checked
  lower_error := reuse_lower_error 16 51 Primitive.Addresses.material1466

def v1467_pa : Scalar.QComplex := ((999999774674795732310212632190 : Int)/10^30,(-671304966288744132704746331 : Int)/10^30)
theorem v1467_pa_checked : Scalar.distance (sourceCoefficient 16 52 1 0) v1467_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1467_pb : Scalar.QComplex := ((-289652987810173797953551 : Int)/10^30,(-431477401612829100938136556 : Int)/10^30)
theorem v1467_pb_checked : Scalar.distance (sourceCoefficient 16 52 1 1) v1467_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1467_pg : Scalar.QComplex := ((-93086406531325507083701 : Int)/10^30,(62489381078884357349 : Int)/10^30)
theorem v1467_pg_checked : Scalar.distance (sourceCoefficient 16 52 1 2) v1467_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1467_mb : Scalar.QComplex := ((-661998444530219153521950 : Int)/10^30,(-431476990996589995185283022 : Int)/10^30)
theorem v1467_mb_checked : Scalar.distance (sourceCoefficient 16 52 3 1) v1467_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1467_mg : Scalar.QComplex := ((-93086317945480642698591 : Int)/10^30,(142818734191646904239 : Int)/10^30)
theorem v1467_mg_checked : Scalar.distance (sourceCoefficient 16 52 3 2) v1467_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1467_upper : Scalar.QComplex := ((999997126681128075870254287501 : Int)/10^30,(-2397212858276652856997762735 : Int)/10^30)
theorem v1467_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 52 5) 1) 14) v1467_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1467 : Material (16 : Basis) (52 : Basis) where
  plus := ![v1467_pa,v1467_pb,v1467_pg]
  minus := ![(Primitive.Addresses.material1467 1).one,v1467_mb,v1467_mg]
  upper := v1467_upper
  lower := (Primitive.Addresses.material1467 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1467_pa_checked.trans (by decide +kernel)
    · exact v1467_pb_checked.trans (by decide +kernel)
    · exact v1467_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 52 Primitive.Addresses.material1467
    · exact v1467_mb_checked.trans (by decide +kernel)
    · exact v1467_mg_checked.trans (by decide +kernel)
  upper_error := v1467_upper_checked
  lower_error := reuse_lower_error 16 52 Primitive.Addresses.material1467

def v1468_pa : Scalar.QComplex := ((999999772182306674124000990766 : Int)/10^30,(-675007655327590048284909132 : Int)/10^30)
theorem v1468_pa_checked : Scalar.distance (sourceCoefficient 16 53 1 0) v1468_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1468_pb : Scalar.QComplex := ((-291250614615386032984889 : Int)/10^30,(-431477400240735239047424292 : Int)/10^30)
theorem v1468_pb_checked : Scalar.distance (sourceCoefficient 16 53 1 1) v1468_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1468_pg : Scalar.QComplex := ((-93086406267310131642773 : Int)/10^30,(62834051152077091228 : Int)/10^30)
theorem v1468_pg_checked : Scalar.distance (sourceCoefficient 16 53 1 2) v1468_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1468_mb : Scalar.QComplex := ((-663596069556506707822602 : Int)/10^30,(-431476988245816665729896878 : Int)/10^30)
theorem v1468_mb_checked : Scalar.distance (sourceCoefficient 16 53 3 1) v1468_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1468_mg : Scalar.QComplex := ((-93086317384030615761166 : Int)/10^30,(143163403908669839473 : Int)/10^30)
theorem v1468_mg_checked : Scalar.distance (sourceCoefficient 16 53 3 2) v1468_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1468_upper : Scalar.QComplex := ((999997117798137354231311886551 : Int)/10^30,(-2400915537498968400036525881 : Int)/10^30)
theorem v1468_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 53 5) 1) 14) v1468_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1468 : Material (16 : Basis) (53 : Basis) where
  plus := ![v1468_pa,v1468_pb,v1468_pg]
  minus := ![(Primitive.Addresses.material1468 1).one,v1468_mb,v1468_mg]
  upper := v1468_upper
  lower := (Primitive.Addresses.material1468 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1468_pa_checked.trans (by decide +kernel)
    · exact v1468_pb_checked.trans (by decide +kernel)
    · exact v1468_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 53 Primitive.Addresses.material1468
    · exact v1468_mb_checked.trans (by decide +kernel)
    · exact v1468_mg_checked.trans (by decide +kernel)
  upper_error := v1468_upper_checked
  lower_error := reuse_lower_error 16 53 Primitive.Addresses.material1468

def v1469_pa : Scalar.QComplex := ((999999770909853165812062277672 : Int)/10^30,(-676890124899219148694708591 : Int)/10^30)
theorem v1469_pa_checked : Scalar.distance (sourceCoefficient 16 54 1 0) v1469_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1469_pb : Scalar.QComplex := ((-292062857774631888496607 : Int)/10^30,(-431477399540130055432980808 : Int)/10^30)
theorem v1469_pb_checked : Scalar.distance (sourceCoefficient 16 54 1 1) v1469_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1469_pg : Scalar.QComplex := ((-93086406132512204000855 : Int)/10^30,(63009283508261635900 : Int)/10^30)
theorem v1469_pg_checked : Scalar.distance (sourceCoefficient 16 54 1 2) v1469_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1469_mb : Scalar.QComplex := ((-664408311808726594427741 : Int)/10^30,(-431476986844282478627511203 : Int)/10^30)
theorem v1469_mb_checked : Scalar.distance (sourceCoefficient 16 54 3 1) v1469_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1469_mg : Scalar.QComplex := ((-93086317098015107095766 : Int)/10^30,(143338636083282828941 : Int)/10^30)
theorem v1469_mg_checked : Scalar.distance (sourceCoefficient 16 54 3 2) v1469_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1469_upper : Scalar.QComplex := ((999997113276714036763080510652 : Int)/10^30,(-2402798002070740884648358538 : Int)/10^30)
theorem v1469_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 54 5) 1) 14) v1469_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1469 : Material (16 : Basis) (54 : Basis) where
  plus := ![v1469_pa,v1469_pb,v1469_pg]
  minus := ![(Primitive.Addresses.material1469 1).one,v1469_mb,v1469_mg]
  upper := v1469_upper
  lower := (Primitive.Addresses.material1469 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1469_pa_checked.trans (by decide +kernel)
    · exact v1469_pb_checked.trans (by decide +kernel)
    · exact v1469_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 54 Primitive.Addresses.material1469
    · exact v1469_mb_checked.trans (by decide +kernel)
    · exact v1469_mg_checked.trans (by decide +kernel)
  upper_error := v1469_upper_checked
  lower_error := reuse_lower_error 16 54 Primitive.Addresses.material1469

def v1470_pa : Scalar.QComplex := ((999999760406211590319554226785 : Int)/10^30,(-692233717334093346345976328 : Int)/10^30)
theorem v1470_pa_checked : Scalar.distance (sourceCoefficient 16 55 1 0) v1470_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1470_pb : Scalar.QComplex := ((-298683271786353561098524 : Int)/10^30,(-431477393753623261977085557 : Int)/10^30)
theorem v1470_pb_checked : Scalar.distance (sourceCoefficient 16 55 1 1) v1470_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1470_pg : Scalar.QComplex := ((-93086405019452025537637 : Int)/10^30,(64437563618722264793 : Int)/10^30)
theorem v1470_pg_checked : Scalar.distance (sourceCoefficient 16 55 1 2) v1470_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1470_mb : Scalar.QComplex := ((-671028718361870814437259 : Int)/10^30,(-431476975344658720015157095 : Int)/10^30)
theorem v1470_mb_checked : Scalar.distance (sourceCoefficient 16 55 3 1) v1470_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1470_mg : Scalar.QComplex := ((-93086314752413935096431 : Int)/10^30,(144766914701408693440 : Int)/10^30)
theorem v1470_mg_checked : Scalar.distance (sourceCoefficient 16 55 3 2) v1470_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1470_upper : Scalar.QComplex := ((999997076291439522450287889107 : Int)/10^30,(-2418141553524804059152695272 : Int)/10^30)
theorem v1470_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 55 5) 1) 14) v1470_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1470 : Material (16 : Basis) (55 : Basis) where
  plus := ![v1470_pa,v1470_pb,v1470_pg]
  minus := ![(Primitive.Addresses.material1470 1).one,v1470_mb,v1470_mg]
  upper := v1470_upper
  lower := (Primitive.Addresses.material1470 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1470_pa_checked.trans (by decide +kernel)
    · exact v1470_pb_checked.trans (by decide +kernel)
    · exact v1470_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 55 Primitive.Addresses.material1470
    · exact v1470_mb_checked.trans (by decide +kernel)
    · exact v1470_mg_checked.trans (by decide +kernel)
  upper_error := v1470_upper_checked
  lower_error := reuse_lower_error 16 55 Primitive.Addresses.material1470

def v1471_pa : Scalar.QComplex := ((999999757878837353103011859545 : Int)/10^30,(-695875180381608792722093277 : Int)/10^30)
theorem v1471_pa_checked : Scalar.distance (sourceCoefficient 16 56 1 0) v1471_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1471_pb : Scalar.QComplex := ((-300254480937369467555255 : Int)/10^30,(-431477392360437235702597080 : Int)/10^30)
theorem v1471_pb_checked : Scalar.distance (sourceCoefficient 16 56 1 1) v1471_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1471_pg : Scalar.QComplex := ((-93086404751537782877989 : Int)/10^30,(64776534381321617115 : Int)/10^30)
theorem v1471_pg_checked : Scalar.distance (sourceCoefficient 16 56 1 2) v1471_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1471_mb : Scalar.QComplex := ((-672599925725596952259659 : Int)/10^30,(-431476972595590479794025765 : Int)/10^30)
theorem v1471_mb_checked : Scalar.distance (sourceCoefficient 16 56 3 1) v1471_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1471_mg : Scalar.QComplex := ((-93086314191983290746680 : Int)/10^30,(145105885106595814111 : Int)/10^30)
theorem v1471_mg_checked : Scalar.distance (sourceCoefficient 16 56 3 2) v1471_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1471_upper : Scalar.QComplex := ((999997067479234180396235797152 : Int)/10^30,(-2421783006786769400716355644 : Int)/10^30)
theorem v1471_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 56 5) 1) 14) v1471_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1471 : Material (16 : Basis) (56 : Basis) where
  plus := ![v1471_pa,v1471_pb,v1471_pg]
  minus := ![(Primitive.Addresses.material1471 1).one,v1471_mb,v1471_mg]
  upper := v1471_upper
  lower := (Primitive.Addresses.material1471 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1471_pa_checked.trans (by decide +kernel)
    · exact v1471_pb_checked.trans (by decide +kernel)
    · exact v1471_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 56 Primitive.Addresses.material1471
    · exact v1471_mb_checked.trans (by decide +kernel)
    · exact v1471_mg_checked.trans (by decide +kernel)
  upper_error := v1471_upper_checked
  lower_error := reuse_lower_error 16 56 Primitive.Addresses.material1471

def v1472_pa : Scalar.QComplex := ((999999749613560504974102860479 : Int)/10^30,(-707653033835567408346431657 : Int)/10^30)
theorem v1472_pa_checked : Scalar.distance (sourceCoefficient 16 57 1 0) v1472_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1472_pb : Scalar.QComplex := ((-305336358961694773031520 : Int)/10^30,(-431477387802113131834373880 : Int)/10^30)
theorem v1472_pb_checked : Scalar.distance (sourceCoefficient 16 57 1 1) v1472_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1472_pg : Scalar.QComplex := ((-93086403875141606750271 : Int)/10^30,(65872892604765915105 : Int)/10^30)
theorem v1472_pg_checked : Scalar.distance (sourceCoefficient 16 57 1 2) v1472_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1472_mb : Scalar.QComplex := ((-677681797924078413638649 : Int)/10^30,(-431476963651836217495270510 : Int)/10^30)
theorem v1472_mb_checked : Scalar.distance (sourceCoefficient 16 57 3 1) v1472_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1472_mg : Scalar.QComplex := ((-93086312369479672250265 : Int)/10^30,(146202242165525410887 : Int)/10^30)
theorem v1472_mg_checked : Scalar.distance (sourceCoefficient 16 57 3 2) v1472_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1472_upper : Scalar.QComplex := ((999997038886463059412560876024 : Int)/10^30,(-2433560828433880800711180498 : Int)/10^30)
theorem v1472_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 57 5) 1) 14) v1472_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1472 : Material (16 : Basis) (57 : Basis) where
  plus := ![v1472_pa,v1472_pb,v1472_pg]
  minus := ![(Primitive.Addresses.material1472 1).one,v1472_mb,v1472_mg]
  upper := v1472_upper
  lower := (Primitive.Addresses.material1472 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1472_pa_checked.trans (by decide +kernel)
    · exact v1472_pb_checked.trans (by decide +kernel)
    · exact v1472_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 57 Primitive.Addresses.material1472
    · exact v1472_mb_checked.trans (by decide +kernel)
    · exact v1472_mg_checked.trans (by decide +kernel)
  upper_error := v1472_upper_checked
  lower_error := reuse_lower_error 16 57 Primitive.Addresses.material1472

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
