import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B064
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B065

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1553_pa : Scalar.QComplex := ((999999740270478797572441183863 : Int)/10^30,(-720735024086821337533937554 : Int)/10^30)
theorem v1553_pa_checked : Scalar.distance (sourceCoefficient 17 58 1 0) v1553_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1553_pb : Scalar.QComplex := ((-310980943374331269144143 : Int)/10^30,(-431477383796376044954075009 : Int)/10^30)
theorem v1553_pb_checked : Scalar.distance (sourceCoefficient 17 58 1 1) v1553_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1553_pg : Scalar.QComplex := ((-93086403008188149449846 : Int)/10^30,(67090648339684014532 : Int)/10^30)
theorem v1553_pg_checked : Scalar.distance (sourceCoefficient 17 58 1 2) v1553_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1553_mb : Scalar.QComplex := ((-683326376778207468398556 : Int)/10^30,(-431476954775078496673421143 : Int)/10^30)
theorem v1553_mb_checked : Scalar.distance (sourceCoefficient 17 58 3 1) v1553_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1553_mg : Scalar.QComplex := ((-93086310451658184204247 : Int)/10^30,(147419996698875608502 : Int)/10^30)
theorem v1553_mg_checked : Scalar.distance (sourceCoefficient 17 58 3 2) v1553_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1553_upper : Scalar.QComplex := ((999997006965066882654212870829 : Int)/10^30,(-2446642783075735539955616901 : Int)/10^30)
theorem v1553_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 58 5) 1) 14) v1553_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1553 : Material (17 : Basis) (58 : Basis) where
  plus := ![v1553_pa,v1553_pb,v1553_pg]
  minus := ![(Primitive.Addresses.material1553 1).one,v1553_mb,v1553_mg]
  upper := v1553_upper
  lower := (Primitive.Addresses.material1553 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1553_pa_checked.trans (by decide +kernel)
    · exact v1553_pb_checked.trans (by decide +kernel)
    · exact v1553_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 58 Primitive.Addresses.material1553
    · exact v1553_mb_checked.trans (by decide +kernel)
    · exact v1553_mg_checked.trans (by decide +kernel)
  upper_error := v1553_upper_checked
  lower_error := reuse_lower_error 17 58 Primitive.Addresses.material1553

def v1554_pa : Scalar.QComplex := ((999999727455819106477638067078 : Int)/10^30,(-738300946434930547112992387 : Int)/10^30)
theorem v1554_pa_checked : Scalar.distance (sourceCoefficient 17 59 1 0) v1554_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1554_pb : Scalar.QComplex := ((-318560242442458104610236 : Int)/10^30,(-431477376751261905265511640 : Int)/10^30)
theorem v1554_pb_checked : Scalar.distance (sourceCoefficient 17 59 1 1) v1554_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1554_pg : Scalar.QComplex := ((-93086401651800557104467 : Int)/10^30,(68725797170562529618 : Int)/10^30)
theorem v1554_pg_checked : Scalar.distance (sourceCoefficient 17 59 1 2) v1554_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1554_mb : Scalar.QComplex := ((-690905666944598667332434 : Int)/10^30,(-431476941189373243367558855 : Int)/10^30)
theorem v1554_mb_checked : Scalar.distance (sourceCoefficient 17 59 3 1) v1554_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1554_mg : Scalar.QComplex := ((-93086307684211300225335 : Int)/10^30,(149055143750412081094 : Int)/10^30)
theorem v1554_mg_checked : Scalar.distance (sourceCoefficient 17 59 3 2) v1554_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1554_upper : Scalar.QComplex := ((999996963833237872680358416773 : Int)/10^30,(-2464208657144526760229946406 : Int)/10^30)
theorem v1554_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 59 5) 1) 14) v1554_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1554 : Material (17 : Basis) (59 : Basis) where
  plus := ![v1554_pa,v1554_pb,v1554_pg]
  minus := ![(Primitive.Addresses.material1554 1).one,v1554_mb,v1554_mg]
  upper := v1554_upper
  lower := (Primitive.Addresses.material1554 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1554_pa_checked.trans (by decide +kernel)
    · exact v1554_pb_checked.trans (by decide +kernel)
    · exact v1554_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 59 Primitive.Addresses.material1554
    · exact v1554_mb_checked.trans (by decide +kernel)
    · exact v1554_mg_checked.trans (by decide +kernel)
  upper_error := v1554_upper_checked
  lower_error := reuse_lower_error 17 59 Primitive.Addresses.material1554

def v1555_pa : Scalar.QComplex := ((999999712289626884690311947919 : Int)/10^30,(-758564870959208457038991388 : Int)/10^30)
theorem v1555_pa_checked : Scalar.distance (sourceCoefficient 17 60 1 0) v1555_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1555_pb : Scalar.QComplex := ((-327303668453525377324790 : Int)/10^30,(-431477368403559294484285474 : Int)/10^30)
theorem v1555_pb_checked : Scalar.distance (sourceCoefficient 17 60 1 1) v1555_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1555_pg : Scalar.QComplex := ((-93086400045455662853781 : Int)/10^30,(70612093354370056581 : Int)/10^30)
theorem v1555_pg_checked : Scalar.distance (sourceCoefficient 17 60 1 2) v1555_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1555_mb : Scalar.QComplex := ((-699649082496397455282433 : Int)/10^30,(-431476925296490882555860102 : Int)/10^30)
theorem v1555_mb_checked : Scalar.distance (sourceCoefficient 17 60 3 1) v1555_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1555_mg : Scalar.QComplex := ((-93086304450078353090788 : Int)/10^30,(150941437845662034181 : Int)/10^30)
theorem v1555_mg_checked : Scalar.distance (sourceCoefficient 17 60 3 2) v1555_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1555_upper : Scalar.QComplex := ((999996913693372839123733438307 : Int)/10^30,(-2484472525312597550436095912 : Int)/10^30)
theorem v1555_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 60 5) 1) 14) v1555_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1555 : Material (17 : Basis) (60 : Basis) where
  plus := ![v1555_pa,v1555_pb,v1555_pg]
  minus := ![(Primitive.Addresses.material1555 1).one,v1555_mb,v1555_mg]
  upper := v1555_upper
  lower := (Primitive.Addresses.material1555 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1555_pa_checked.trans (by decide +kernel)
    · exact v1555_pb_checked.trans (by decide +kernel)
    · exact v1555_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 60 Primitive.Addresses.material1555
    · exact v1555_mb_checked.trans (by decide +kernel)
    · exact v1555_mg_checked.trans (by decide +kernel)
  upper_error := v1555_upper_checked
  lower_error := reuse_lower_error 17 60 Primitive.Addresses.material1555

def v1556_pa : Scalar.QComplex := ((999999707827774840028273373020 : Int)/10^30,(-764424204846585361135449807 : Int)/10^30)
theorem v1556_pa_checked : Scalar.distance (sourceCoefficient 17 61 1 0) v1556_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1556_pb : Scalar.QComplex := ((-329831838740106860122542 : Int)/10^30,(-431477365945783403202616664 : Int)/10^30)
theorem v1556_pb_checked : Scalar.distance (sourceCoefficient 17 61 1 1) v1556_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1556_pg : Scalar.QComplex := ((-93086399572667949314808 : Int)/10^30,(71157517765618522951 : Int)/10^30)
theorem v1556_pg_checked : Scalar.distance (sourceCoefficient 17 61 1 2) v1556_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1556_mb : Scalar.QComplex := ((-702177249720675697236763 : Int)/10^30,(-431476920657018813659518241 : Int)/10^30)
theorem v1556_mb_checked : Scalar.distance (sourceCoefficient 17 61 3 1) v1556_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1556_mg : Scalar.QComplex := ((-93086303506614113688449 : Int)/10^30,(151486861645829561900 : Int)/10^30)
theorem v1556_mg_checked : Scalar.distance (sourceCoefficient 17 61 3 2) v1556_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1556_upper : Scalar.QComplex := ((999996899118848704871638985325 : Int)/10^30,(-2490331842772433061961377032 : Int)/10^30)
theorem v1556_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 61 5) 1) 14) v1556_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1556 : Material (17 : Basis) (61 : Basis) where
  plus := ![v1556_pa,v1556_pb,v1556_pg]
  minus := ![(Primitive.Addresses.material1556 1).one,v1556_mb,v1556_mg]
  upper := v1556_upper
  lower := (Primitive.Addresses.material1556 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1556_pa_checked.trans (by decide +kernel)
    · exact v1556_pb_checked.trans (by decide +kernel)
    · exact v1556_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 61 Primitive.Addresses.material1556
    · exact v1556_mb_checked.trans (by decide +kernel)
    · exact v1556_mg_checked.trans (by decide +kernel)
  upper_error := v1556_upper_checked
  lower_error := reuse_lower_error 17 61 Primitive.Addresses.material1556

def v1557_pa : Scalar.QComplex := ((999999701283715246306826331699 : Int)/10^30,(-772937565574327335841961176 : Int)/10^30)
theorem v1557_pa_checked : Scalar.distance (sourceCoefficient 17 62 1 0) v1557_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1557_pb : Scalar.QComplex := ((-333505161670581487430570 : Int)/10^30,(-431477362339543431332756681 : Int)/10^30)
theorem v1557_pb_checked : Scalar.distance (sourceCoefficient 17 62 1 1) v1557_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1557_pg : Scalar.QComplex := ((-93086398879083487740256 : Int)/10^30,(71949996030315086136 : Int)/10^30)
theorem v1557_pg_checked : Scalar.distance (sourceCoefficient 17 62 1 2) v1557_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1557_mb : Scalar.QComplex := ((-705850568171381641673132 : Int)/10^30,(-431476913880867935881364821 : Int)/10^30)
theorem v1557_mb_checked : Scalar.distance (sourceCoefficient 17 62 3 1) v1557_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1557_mg : Scalar.QComplex := ((-93086302129156859830053 : Int)/10^30,(152279339016918096638 : Int)/10^30)
theorem v1557_mg_checked : Scalar.distance (sourceCoefficient 17 62 3 2) v1557_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1557_upper : Scalar.QComplex := ((999996877881510567727729927549 : Int)/10^30,(-2498845179526071095982560725 : Int)/10^30)
theorem v1557_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 62 5) 1) 14) v1557_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1557 : Material (17 : Basis) (62 : Basis) where
  plus := ![v1557_pa,v1557_pb,v1557_pg]
  minus := ![(Primitive.Addresses.material1557 1).one,v1557_mb,v1557_mg]
  upper := v1557_upper
  lower := (Primitive.Addresses.material1557 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1557_pa_checked.trans (by decide +kernel)
    · exact v1557_pb_checked.trans (by decide +kernel)
    · exact v1557_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 62 Primitive.Addresses.material1557
    · exact v1557_mb_checked.trans (by decide +kernel)
    · exact v1557_mg_checked.trans (by decide +kernel)
  upper_error := v1557_upper_checked
  lower_error := reuse_lower_error 17 62 Primitive.Addresses.material1557

def v1558_pa : Scalar.QComplex := ((999999681811193721604446336837 : Int)/10^30,(-797732731754611324131912705 : Int)/10^30)
theorem v1558_pa_checked : Scalar.distance (sourceCoefficient 17 63 1 0) v1558_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1558_pb : Scalar.QComplex := ((-344203715902924563048856 : Int)/10^30,(-431477351598799307241152545 : Int)/10^30)
theorem v1558_pb_checked : Scalar.distance (sourceCoefficient 17 63 1 1) v1558_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1558_pg : Scalar.QComplex := ((-93086396814172265540957 : Int)/10^30,(74258089247856164343 : Int)/10^30)
theorem v1558_pg_checked : Scalar.distance (sourceCoefficient 17 63 1 2) v1558_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1558_mb : Scalar.QComplex := ((-716549109151385594573978 : Int)/10^30,(-431476893907757353543297791 : Int)/10^30)
theorem v1558_mb_checked : Scalar.distance (sourceCoefficient 17 63 3 1) v1558_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1558_mg : Scalar.QComplex := ((-93086298072465912413237 : Int)/10^30,(154587429593125200275 : Int)/10^30)
theorem v1558_mg_checked : Scalar.distance (sourceCoefficient 17 63 3 2) v1558_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1558_upper : Scalar.QComplex := ((999996815614810617793121725378 : Int)/10^30,(-2523640275169062085278199133 : Int)/10^30)
theorem v1558_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 63 5) 1) 14) v1558_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1558 : Material (17 : Basis) (63 : Basis) where
  plus := ![v1558_pa,v1558_pb,v1558_pg]
  minus := ![(Primitive.Addresses.material1558 1).one,v1558_mb,v1558_mg]
  upper := v1558_upper
  lower := (Primitive.Addresses.material1558 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1558_pa_checked.trans (by decide +kernel)
    · exact v1558_pb_checked.trans (by decide +kernel)
    · exact v1558_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 63 Primitive.Addresses.material1558
    · exact v1558_mb_checked.trans (by decide +kernel)
    · exact v1558_mg_checked.trans (by decide +kernel)
  upper_error := v1558_upper_checked
  lower_error := reuse_lower_error 17 63 Primitive.Addresses.material1558

def v1559_pa : Scalar.QComplex := ((999999652913822458646086331690 : Int)/10^30,(-833169991426655492616232673 : Int)/10^30)
theorem v1559_pa_checked : Scalar.distance (sourceCoefficient 17 64 1 0) v1559_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1559_pb : Scalar.QComplex := ((-359494092806522615241072 : Int)/10^30,(-431477335634139419143673422 : Int)/10^30)
theorem v1559_pb_checked : Scalar.distance (sourceCoefficient 17 64 1 1) v1559_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1559_pg : Scalar.QComplex := ((-93086393747097652808978 : Int)/10^30,(77556816799106713924 : Int)/10^30)
theorem v1559_pg_checked : Scalar.distance (sourceCoefficient 17 64 1 2) v1559_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1559_mb : Scalar.QComplex := ((-731839466584895058972390 : Int)/10^30,(-431476864748196795024933581 : Int)/10^30)
theorem v1559_mb_checked : Scalar.distance (sourceCoefficient 17 64 3 1) v1559_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1559_mg : Scalar.QComplex := ((-93086292158739134137846 : Int)/10^30,(157886153269361468353 : Int)/10^30)
theorem v1559_mg_checked : Scalar.distance (sourceCoefficient 17 64 3 2) v1559_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1559_upper : Scalar.QComplex := ((999996725555987043210971242736 : Int)/10^30,(-2559077432187229474367682417 : Int)/10^30)
theorem v1559_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 64 5) 1) 14) v1559_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1559 : Material (17 : Basis) (64 : Basis) where
  plus := ![v1559_pa,v1559_pb,v1559_pg]
  minus := ![(Primitive.Addresses.material1559 1).one,v1559_mb,v1559_mg]
  upper := v1559_upper
  lower := (Primitive.Addresses.material1559 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1559_pa_checked.trans (by decide +kernel)
    · exact v1559_pb_checked.trans (by decide +kernel)
    · exact v1559_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 64 Primitive.Addresses.material1559
    · exact v1559_mb_checked.trans (by decide +kernel)
    · exact v1559_mg_checked.trans (by decide +kernel)
  upper_error := v1559_upper_checked
  lower_error := reuse_lower_error 17 64 Primitive.Addresses.material1559

def v1560_pa : Scalar.QComplex := ((999999622300716313244047205769 : Int)/10^30,(-869136597271546843531531171 : Int)/10^30)
theorem v1560_pa_checked : Scalar.distance (sourceCoefficient 17 65 1 0) v1560_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1560_pb : Scalar.QComplex := ((-375012870210144532702042 : Int)/10^30,(-431477318692272000910504947 : Int)/10^30)
theorem v1560_pb_checked : Scalar.distance (sourceCoefficient 17 65 1 1) v1560_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1560_pg : Scalar.QComplex := ((-93086390494756446253279 : Int)/10^30,(80904819244595355045 : Int)/10^30)
theorem v1560_pg_checked : Scalar.distance (sourceCoefficient 17 65 1 2) v1560_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1560_mb : Scalar.QComplex := ((-747358223590098357348414 : Int)/10^30,(-431476834414329725485966326 : Int)/10^30)
theorem v1560_mb_checked : Scalar.distance (sourceCoefficient 17 65 3 1) v1560_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1560_mg : Scalar.QComplex := ((-93086286017223816553334 : Int)/10^30,(161234151661611806501 : Int)/10^30)
theorem v1560_mg_checked : Scalar.distance (sourceCoefficient 17 65 3 2) v1560_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1560_upper : Scalar.QComplex := ((999996632867827669146141910656 : Int)/10^30,(-2595043931628642345956603677 : Int)/10^30)
theorem v1560_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 65 5) 1) 14) v1560_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1560 : Material (17 : Basis) (65 : Basis) where
  plus := ![v1560_pa,v1560_pb,v1560_pg]
  minus := ![(Primitive.Addresses.material1560 1).one,v1560_mb,v1560_mg]
  upper := v1560_upper
  lower := (Primitive.Addresses.material1560 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1560_pa_checked.trans (by decide +kernel)
    · exact v1560_pb_checked.trans (by decide +kernel)
    · exact v1560_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 65 Primitive.Addresses.material1560
    · exact v1560_mb_checked.trans (by decide +kernel)
    · exact v1560_mg_checked.trans (by decide +kernel)
  upper_error := v1560_upper_checked
  lower_error := reuse_lower_error 17 65 Primitive.Addresses.material1560

def v1561_pa : Scalar.QComplex := ((999999606860057405005044297462 : Int)/10^30,(-886724157013315752493347613 : Int)/10^30)
theorem v1561_pa_checked : Scalar.distance (sourceCoefficient 17 66 1 0) v1561_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1561_pb : Scalar.QComplex := ((-382601504517374075516689 : Int)/10^30,(-431477310136815306960521087 : Int)/10^30)
theorem v1561_pb_checked : Scalar.distance (sourceCoefficient 17 66 1 1) v1561_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1561_pg : Scalar.QComplex := ((-93086388853226683541448 : Int)/10^30,(82541982135841261569 : Int)/10^30)
theorem v1561_pg_checked : Scalar.distance (sourceCoefficient 17 66 1 2) v1561_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1561_mb : Scalar.QComplex := ((-754946847688758726447298 : Int)/10^30,(-431476819310226589386167708 : Int)/10^30)
theorem v1561_mb_checked : Scalar.distance (sourceCoefficient 17 66 3 1) v1561_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1561_mg : Scalar.QComplex := ((-93086282962896824992285 : Int)/10^30,(162871312526700893110 : Int)/10^30)
theorem v1561_mg_checked : Scalar.distance (sourceCoefficient 17 66 3 2) v1561_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1561_upper : Scalar.QComplex := ((999996587072659174617828177638 : Int)/10^30,(-2612631438526630489461526309 : Int)/10^30)
theorem v1561_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 66 5) 1) 14) v1561_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1561 : Material (17 : Basis) (66 : Basis) where
  plus := ![v1561_pa,v1561_pb,v1561_pg]
  minus := ![(Primitive.Addresses.material1561 1).one,v1561_mb,v1561_mg]
  upper := v1561_upper
  lower := (Primitive.Addresses.material1561 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1561_pa_checked.trans (by decide +kernel)
    · exact v1561_pb_checked.trans (by decide +kernel)
    · exact v1561_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 66 Primitive.Addresses.material1561
    · exact v1561_mb_checked.trans (by decide +kernel)
    · exact v1561_mg_checked.trans (by decide +kernel)
  upper_error := v1561_upper_checked
  lower_error := reuse_lower_error 17 66 Primitive.Addresses.material1561

def v1562_pa : Scalar.QComplex := ((999999580250851977785234538629 : Int)/10^30,(-916241300016039587795989458 : Int)/10^30)
theorem v1562_pa_checked : Scalar.distance (sourceCoefficient 17 67 1 0) v1562_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1562_pb : Scalar.QComplex := ((-395337483987363540427992 : Int)/10^30,(-431477295378270699568965100 : Int)/10^30)
theorem v1562_pb_checked : Scalar.distance (sourceCoefficient 17 67 1 1) v1562_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1562_pg : Scalar.QComplex := ((-93086386022753577709293 : Int)/10^30,(85289627143530963511 : Int)/10^30)
theorem v1562_pg_checked : Scalar.distance (sourceCoefficient 17 67 1 2) v1562_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1562_mb : Scalar.QComplex := ((-767682809680601675660622 : Int)/10^30,(-431476793561110801896386987 : Int)/10^30)
theorem v1562_mb_checked : Scalar.distance (sourceCoefficient 17 67 3 1) v1562_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1562_mg : Scalar.QComplex := ((-93086277761330880775769 : Int)/10^30,(165618954068745974551 : Int)/10^30)
theorem v1562_mg_checked : Scalar.distance (sourceCoefficient 17 67 3 2) v1562_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1562_upper : Scalar.QComplex := ((999996509519582330278007924684 : Int)/10^30,(-2642148491641962550268646110 : Int)/10^30)
theorem v1562_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 67 5) 1) 14) v1562_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1562 : Material (17 : Basis) (67 : Basis) where
  plus := ![v1562_pa,v1562_pb,v1562_pg]
  minus := ![(Primitive.Addresses.material1562 1).one,v1562_mb,v1562_mg]
  upper := v1562_upper
  lower := (Primitive.Addresses.material1562 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1562_pa_checked.trans (by decide +kernel)
    · exact v1562_pb_checked.trans (by decide +kernel)
    · exact v1562_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 67 Primitive.Addresses.material1562
    · exact v1562_mb_checked.trans (by decide +kernel)
    · exact v1562_mg_checked.trans (by decide +kernel)
  upper_error := v1562_upper_checked
  lower_error := reuse_lower_error 17 67 Primitive.Addresses.material1562

def v1563_pa : Scalar.QComplex := ((999999534002024543050096070539 : Int)/10^30,(-965399261321338839713270849 : Int)/10^30)
theorem v1563_pa_checked : Scalar.distance (sourceCoefficient 17 68 1 0) v1563_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1563_pb : Scalar.QComplex := ((-416548031543161753169875 : Int)/10^30,(-431477269686838892530467228 : Int)/10^30)
theorem v1563_pb_checked : Scalar.distance (sourceCoefficient 17 68 1 1) v1563_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1563_pg : Scalar.QComplex := ((-93086381098865497719646 : Int)/10^30,(89865565429092942384 : Int)/10^30)
theorem v1563_pg_checked : Scalar.distance (sourceCoefficient 17 68 1 2) v1563_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1563_mb : Scalar.QComplex := ((-788893327168195113128512 : Int)/10^30,(-431476749565941307898220255 : Int)/10^30)
theorem v1563_mb_checked : Scalar.distance (sourceCoefficient 17 68 3 1) v1563_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1563_mg : Scalar.QComplex := ((-93086268888615986344563 : Int)/10^30,(170194886401383349654 : Int)/10^30)
theorem v1563_mg_checked : Scalar.distance (sourceCoefficient 17 68 3 2) v1563_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1563_upper : Scalar.QComplex := ((999996378428642140205381162533 : Int)/10^30,(-2691306299910972446211423383 : Int)/10^30)
theorem v1563_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 68 5) 1) 14) v1563_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1563 : Material (17 : Basis) (68 : Basis) where
  plus := ![v1563_pa,v1563_pb,v1563_pg]
  minus := ![(Primitive.Addresses.material1563 1).one,v1563_mb,v1563_mg]
  upper := v1563_upper
  lower := (Primitive.Addresses.material1563 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1563_pa_checked.trans (by decide +kernel)
    · exact v1563_pb_checked.trans (by decide +kernel)
    · exact v1563_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 68 Primitive.Addresses.material1563
    · exact v1563_mb_checked.trans (by decide +kernel)
    · exact v1563_mg_checked.trans (by decide +kernel)
  upper_error := v1563_upper_checked
  lower_error := reuse_lower_error 17 68 Primitive.Addresses.material1563

def v1564_pa : Scalar.QComplex := ((999999512881192281848459806377 : Int)/10^30,(-987034638780002617813575647 : Int)/10^30)
theorem v1564_pa_checked : Scalar.distance (sourceCoefficient 17 69 1 0) v1564_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1564_pb : Scalar.QComplex := ((-425883206887286737581755 : Int)/10^30,(-431477257938959362786175813 : Int)/10^30)
theorem v1564_pb_checked : Scalar.distance (sourceCoefficient 17 69 1 1) v1564_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1564_pg : Scalar.QComplex := ((-93086378848597514640019 : Int)/10^30,(91879525078408633760 : Int)/10^30)
theorem v1564_pg_checked : Scalar.distance (sourceCoefficient 17 69 1 2) v1564_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1564_mb : Scalar.QComplex := ((-798228488898516749016461 : Int)/10^30,(-431476729762230271136528174 : Int)/10^30)
theorem v1564_mb_checked : Scalar.distance (sourceCoefficient 17 69 3 1) v1564_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1564_mg : Scalar.QComplex := ((-93086264900392369158571 : Int)/10^30,(172208843358929899997 : Int)/10^30)
theorem v1564_mg_checked : Scalar.distance (sourceCoefficient 17 69 3 2) v1564_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1564_upper : Scalar.QComplex := ((999996319967142588459608479170 : Int)/10^30,(-2712941608693642553698071679 : Int)/10^30)
theorem v1564_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 69 5) 1) 14) v1564_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1564 : Material (17 : Basis) (69 : Basis) where
  plus := ![v1564_pa,v1564_pb,v1564_pg]
  minus := ![(Primitive.Addresses.material1564 1).one,v1564_mb,v1564_mg]
  upper := v1564_upper
  lower := (Primitive.Addresses.material1564 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1564_pa_checked.trans (by decide +kernel)
    · exact v1564_pb_checked.trans (by decide +kernel)
    · exact v1564_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 69 Primitive.Addresses.material1564
    · exact v1564_mb_checked.trans (by decide +kernel)
    · exact v1564_mg_checked.trans (by decide +kernel)
  upper_error := v1564_upper_checked
  lower_error := reuse_lower_error 17 69 Primitive.Addresses.material1564

def v1565_pa : Scalar.QComplex := ((999999498732474318898154143437 : Int)/10^30,(-1001266597911401111800184589 : Int)/10^30)
theorem v1565_pa_checked : Scalar.distance (sourceCoefficient 17 70 1 0) v1565_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1565_pb : Scalar.QComplex := ((-432023974807593208151351 : Int)/10^30,(-431477250064255839755509895 : Int)/10^30)
theorem v1565_pb_checked : Scalar.distance (sourceCoefficient 17 70 1 1) v1565_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1565_pg : Scalar.QComplex := ((-93086377340631262045417 : Int)/10^30,(93204327072053215562 : Int)/10^30)
theorem v1565_pg_checked : Scalar.distance (sourceCoefficient 17 70 1 2) v1565_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1565_mb : Scalar.QComplex := ((-804369247736820199003244 : Int)/10^30,(-431476716588323534913764075 : Int)/10^30)
theorem v1565_mb_checked : Scalar.distance (sourceCoefficient 17 70 3 1) v1565_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1565_mg : Scalar.QComplex := ((-93086262249182224400303 : Int)/10^30,(173533643557983193413 : Int)/10^30)
theorem v1565_mg_checked : Scalar.distance (sourceCoefficient 17 70 3 2) v1565_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1565_upper : Scalar.QComplex := ((999996281255375350815660117322 : Int)/10^30,(-2727173522208806082438716300 : Int)/10^30)
theorem v1565_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 70 5) 1) 14) v1565_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1565 : Material (17 : Basis) (70 : Basis) where
  plus := ![v1565_pa,v1565_pb,v1565_pg]
  minus := ![(Primitive.Addresses.material1565 1).one,v1565_mb,v1565_mg]
  upper := v1565_upper
  lower := (Primitive.Addresses.material1565 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1565_pa_checked.trans (by decide +kernel)
    · exact v1565_pb_checked.trans (by decide +kernel)
    · exact v1565_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 70 Primitive.Addresses.material1565
    · exact v1565_mb_checked.trans (by decide +kernel)
    · exact v1565_mg_checked.trans (by decide +kernel)
  upper_error := v1565_upper_checked
  lower_error := reuse_lower_error 17 70 Primitive.Addresses.material1565

def v1566_pa : Scalar.QComplex := ((999999474113818264251021484389 : Int)/10^30,(-1025559401943749826995811260 : Int)/10^30)
theorem v1566_pa_checked : Scalar.distance (sourceCoefficient 17 71 1 0) v1566_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1566_pb : Scalar.QComplex := ((-442505769174775745203935 : Int)/10^30,(-431477236353567228115263286 : Int)/10^30)
theorem v1566_pb_checked : Scalar.distance (sourceCoefficient 17 71 1 1) v1566_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1566_pg : Scalar.QComplex := ((-93086374715836303798449 : Int)/10^30,(95465656986754714630 : Int)/10^30)
theorem v1566_pg_checked : Scalar.distance (sourceCoefficient 17 71 1 2) v1566_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1566_mb : Scalar.QComplex := ((-814851026369444886132668 : Int)/10^30,(-431476693832323572004739514 : Int)/10^30)
theorem v1566_mb_checked : Scalar.distance (sourceCoefficient 17 71 3 1) v1566_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1566_mg : Scalar.QComplex := ((-93086257672962373615702 : Int)/10^30,(175794970365608384765 : Int)/10^30)
theorem v1566_mg_checked : Scalar.distance (sourceCoefficient 17 71 3 2) v1566_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1566_upper : Scalar.QComplex := ((999996214709580028897398917453 : Int)/10^30,(-2751466247570309861379436306 : Int)/10^30)
theorem v1566_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 71 5) 1) 14) v1566_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1566 : Material (17 : Basis) (71 : Basis) where
  plus := ![v1566_pa,v1566_pb,v1566_pg]
  minus := ![(Primitive.Addresses.material1566 1).one,v1566_mb,v1566_mg]
  upper := v1566_upper
  lower := (Primitive.Addresses.material1566 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1566_pa_checked.trans (by decide +kernel)
    · exact v1566_pb_checked.trans (by decide +kernel)
    · exact v1566_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 71 Primitive.Addresses.material1566
    · exact v1566_mb_checked.trans (by decide +kernel)
    · exact v1566_mg_checked.trans (by decide +kernel)
  upper_error := v1566_upper_checked
  lower_error := reuse_lower_error 17 71 Primitive.Addresses.material1566

def v1567_pa : Scalar.QComplex := ((999999446729885289805662059178 : Int)/10^30,(-1051922013892935337143053874 : Int)/10^30)
theorem v1567_pa_checked : Scalar.distance (sourceCoefficient 17 72 1 0) v1567_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1567_pb : Scalar.QComplex := ((-453880638477102618597567 : Int)/10^30,(-431477221090560489820938414 : Int)/10^30)
theorem v1567_pb_checked : Scalar.distance (sourceCoefficient 17 72 1 1) v1567_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1567_pg : Scalar.QComplex := ((-93086371794888864202592 : Int)/10^30,(97919657860486364780 : Int)/10^30)
theorem v1567_pg_checked : Scalar.distance (sourceCoefficient 17 72 1 2) v1567_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1567_mb : Scalar.QComplex := ((-826225878265100666218670 : Int)/10^30,(-431476668753322614013003154 : Int)/10^30)
theorem v1567_mb_checked : Scalar.distance (sourceCoefficient 17 72 3 1) v1567_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1567_mg : Scalar.QComplex := ((-93086252634323791688162 : Int)/10^30,(178248967804957270461 : Int)/10^30)
theorem v1567_mg_checked : Scalar.distance (sourceCoefficient 17 72 3 2) v1567_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1567_upper : Scalar.QComplex := ((999996141826211212783167572309 : Int)/10^30,(-2777828772993297580251483642 : Int)/10^30)
theorem v1567_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 72 5) 1) 14) v1567_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1567 : Material (17 : Basis) (72 : Basis) where
  plus := ![v1567_pa,v1567_pb,v1567_pg]
  minus := ![(Primitive.Addresses.material1567 1).one,v1567_mb,v1567_mg]
  upper := v1567_upper
  lower := (Primitive.Addresses.material1567 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1567_pa_checked.trans (by decide +kernel)
    · exact v1567_pb_checked.trans (by decide +kernel)
    · exact v1567_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 72 Primitive.Addresses.material1567
    · exact v1567_mb_checked.trans (by decide +kernel)
    · exact v1567_mg_checked.trans (by decide +kernel)
  upper_error := v1567_upper_checked
  lower_error := reuse_lower_error 17 72 Primitive.Addresses.material1567

def v1568_pa : Scalar.QComplex := ((999999436744950335578983974053 : Int)/10^30,(-1061371651247851569252567989 : Int)/10^30)
theorem v1568_pa_checked : Scalar.distance (sourceCoefficient 17 73 1 0) v1568_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1568_pb : Scalar.QComplex := ((-457957942661761469967426 : Int)/10^30,(-431477215522214307603537354 : Int)/10^30)
theorem v1568_pb_checked : Scalar.distance (sourceCoefficient 17 73 1 1) v1568_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1568_pg : Scalar.QComplex := ((-93086370729503808101419 : Int)/10^30,(98799290659042501245 : Int)/10^30)
theorem v1568_pg_checked : Scalar.distance (sourceCoefficient 17 73 1 2) v1568_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1568_mb : Scalar.QComplex := ((-830303176126360861382023 : Int)/10^30,(-431476659666448628748409749 : Int)/10^30)
theorem v1568_mb_checked : Scalar.distance (sourceCoefficient 17 73 3 1) v1568_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1568_mg : Scalar.QComplex := ((-93086250809855644315177 : Int)/10^30,(179128599356606594566 : Int)/10^30)
theorem v1568_mg_checked : Scalar.distance (sourceCoefficient 17 73 3 2) v1568_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1568_upper : Scalar.QComplex := ((999996115532074319763030306620 : Int)/10^30,(-2787278379040997099820375161 : Int)/10^30)
theorem v1568_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 73 5) 1) 14) v1568_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1568 : Material (17 : Basis) (73 : Basis) where
  plus := ![v1568_pa,v1568_pb,v1568_pg]
  minus := ![(Primitive.Addresses.material1568 1).one,v1568_mb,v1568_mg]
  upper := v1568_upper
  lower := (Primitive.Addresses.material1568 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1568_pa_checked.trans (by decide +kernel)
    · exact v1568_pb_checked.trans (by decide +kernel)
    · exact v1568_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 73 Primitive.Addresses.material1568
    · exact v1568_mb_checked.trans (by decide +kernel)
    · exact v1568_mg_checked.trans (by decide +kernel)
  upper_error := v1568_upper_checked
  lower_error := reuse_lower_error 17 73 Primitive.Addresses.material1568

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
