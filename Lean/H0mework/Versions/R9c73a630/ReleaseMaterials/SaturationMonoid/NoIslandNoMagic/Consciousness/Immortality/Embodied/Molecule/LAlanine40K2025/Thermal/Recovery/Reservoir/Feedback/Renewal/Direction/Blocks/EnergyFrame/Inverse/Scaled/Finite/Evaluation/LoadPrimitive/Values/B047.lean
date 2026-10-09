import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B031
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B032

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v753_pa : Scalar.QComplex := ((999999996137975604757036832655 : Int)/10^30,(87886567662929549095724725 : Int)/10^30)
theorem v753_pa_checked : Scalar.distance (sourceCoefficient 8 14 1 0) v753_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v753_pb : Scalar.QComplex := ((37921078211952829981556 : Int)/10^30,(-431477517826603745886956293 : Int)/10^30)
theorem v753_pb_checked : Scalar.distance (sourceCoefficient 8 14 1 1) v753_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v753_pg : Scalar.QComplex := ((-93086429374842313489874 : Int)/10^30,(-8181046805347994092 : Int)/10^30)
theorem v753_pg_checked : Scalar.distance (sourceCoefficient 8 14 1 2) v753_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v753_mb : Scalar.QComplex := ((-334424600766141624496784 : Int)/10^30,(-431477389891986957267729701 : Int)/10^30)
theorem v753_mb_checked : Scalar.distance (sourceCoefficient 8 14 3 1) v753_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v753_mg : Scalar.QComplex := ((-93086401774385329594052 : Int)/10^30,(72148352334170822330 : Int)/10^30)
theorem v753_mg_checked : Scalar.distance (sourceCoefficient 8 14 3 2) v753_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v753_upper : Scalar.QComplex := ((999998658439692387563064759912 : Int)/10^30,(-1638022837276945571127914051 : Int)/10^30)
theorem v753_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 14 5) 1) 14) v753_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material753 : Material (8 : Basis) (14 : Basis) where
  plus := ![v753_pa,v753_pb,v753_pg]
  minus := ![(Primitive.Addresses.material753 1).one,v753_mb,v753_mg]
  upper := v753_upper
  lower := (Primitive.Addresses.material753 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v753_pa_checked.trans (by decide +kernel)
    · exact v753_pb_checked.trans (by decide +kernel)
    · exact v753_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 14 Primitive.Addresses.material753
    · exact v753_mb_checked.trans (by decide +kernel)
    · exact v753_mg_checked.trans (by decide +kernel)
  upper_error := v753_upper_checked
  lower_error := reuse_lower_error 8 14 Primitive.Addresses.material753

def v754_pa : Scalar.QComplex := ((999999998102203260309074762285 : Int)/10^30,(61608388031015857851090274 : Int)/10^30)
theorem v754_pa_checked : Scalar.distance (sourceCoefficient 8 15 1 0) v754_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v754_pb : Scalar.QComplex := ((26582634410809427304155 : Int)/10^30,(-431477518077219371821589364 : Int)/10^30)
theorem v754_pb_checked : Scalar.distance (sourceCoefficient 8 15 1 1) v754_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v754_pg : Scalar.QComplex := ((-93086429493297537524268 : Int)/10^30,(-5734904879528557339 : Int)/10^30)
theorem v754_pg_checked : Scalar.distance (sourceCoefficient 8 15 1 2) v754_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v754_mb : Scalar.QComplex := ((-345763040561734205400357 : Int)/10^30,(-431477380358036154051999284 : Int)/10^30)
theorem v754_mb_checked : Scalar.distance (sourceCoefficient 8 15 3 1) v754_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v754_mg : Scalar.QComplex := ((-93086399781930197682610 : Int)/10^30,(74594493451401349208 : Int)/10^30)
theorem v754_mg_checked : Scalar.distance (sourceCoefficient 8 15 3 2) v754_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v754_upper : Scalar.QComplex := ((999998615050163010779619858647 : Int)/10^30,(-1664300981160676292598059293 : Int)/10^30)
theorem v754_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 15 5) 1) 14) v754_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material754 : Material (8 : Basis) (15 : Basis) where
  plus := ![v754_pa,v754_pb,v754_pg]
  minus := ![(Primitive.Addresses.material754 1).one,v754_mb,v754_mg]
  upper := v754_upper
  lower := (Primitive.Addresses.material754 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v754_pa_checked.trans (by decide +kernel)
    · exact v754_pb_checked.trans (by decide +kernel)
    · exact v754_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 15 Primitive.Addresses.material754
    · exact v754_mb_checked.trans (by decide +kernel)
    · exact v754_mg_checked.trans (by decide +kernel)
  upper_error := v754_upper_checked
  lower_error := reuse_lower_error 8 15 Primitive.Addresses.material754

def v755_pa : Scalar.QComplex := ((999999998301957981507561146390 : Int)/10^30,(58275930143598145838546329 : Int)/10^30)
theorem v755_pa_checked : Scalar.distance (sourceCoefficient 8 16 1 0) v755_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v755_pb : Scalar.QComplex := ((25144753744895974680360 : Int)/10^30,(-431477518080616726485312197 : Int)/10^30)
theorem v755_pb_checked : Scalar.distance (sourceCoefficient 8 16 1 1) v755_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v755_pg : Scalar.QComplex := ((-93086429502961235083357 : Int)/10^30,(-5424698272242908012 : Int)/10^30)
theorem v755_pg_checked : Scalar.distance (sourceCoefficient 8 16 1 2) v755_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v755_mb : Scalar.QComplex := ((-347200920695190735775404 : Int)/10^30,(-431477379120607252508620242 : Int)/10^30)
theorem v755_mb_checked : Scalar.distance (sourceCoefficient 8 16 3 1) v755_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v755_mg : Scalar.QComplex := ((-93086399523899560742904 : Int)/10^30,(74904699951522237258 : Int)/10^30)
theorem v755_mg_checked : Scalar.distance (sourceCoefficient 8 16 3 2) v755_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v755_upper : Scalar.QComplex := ((999998609498397439001909137632 : Int)/10^30,(-1667633434429547966485640702 : Int)/10^30)
theorem v755_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 16 5) 1) 14) v755_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material755 : Material (8 : Basis) (16 : Basis) where
  plus := ![v755_pa,v755_pb,v755_pg]
  minus := ![(Primitive.Addresses.material755 1).one,v755_mb,v755_mg]
  upper := v755_upper
  lower := (Primitive.Addresses.material755 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v755_pa_checked.trans (by decide +kernel)
    · exact v755_pb_checked.trans (by decide +kernel)
    · exact v755_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 16 Primitive.Addresses.material755
    · exact v755_mb_checked.trans (by decide +kernel)
    · exact v755_mg_checked.trans (by decide +kernel)
  upper_error := v755_upper_checked
  lower_error := reuse_lower_error 8 16 Primitive.Addresses.material755

def v756_pa : Scalar.QComplex := ((999999998669520357008974403692 : Int)/10^30,(51584486856145764244089318 : Int)/10^30)
theorem v756_pa_checked : Scalar.distance (sourceCoefficient 8 17 1 0) v756_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v756_pb : Scalar.QComplex := ((22257546389121805006816 : Int)/10^30,(-431477518068144425681905848 : Int)/10^30)
theorem v756_pb_checked : Scalar.distance (sourceCoefficient 8 17 1 1) v756_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v756_pg : Scalar.QComplex := ((-93086429518723390465052 : Int)/10^30,(-4801815706382843861 : Int)/10^30)
theorem v756_pg_checked : Scalar.distance (sourceCoefficient 8 17 1 2) v756_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v756_mb : Scalar.QComplex := ((-350088126965162621137746 : Int)/10^30,(-431477376616605043308291324 : Int)/10^30)
theorem v756_mb_checked : Scalar.distance (sourceCoefficient 8 17 3 1) v756_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v756_mg : Scalar.QComplex := ((-93086399002142109507761 : Int)/10^30,(75527582299056685192 : Int)/10^30)
theorem v756_mg_checked : Scalar.distance (sourceCoefficient 8 17 3 2) v756_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v756_upper : Scalar.QComplex := ((999998598317135195912608412433 : Int)/10^30,(-1674324868385260918681276698 : Int)/10^30)
theorem v756_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 17 5) 1) 14) v756_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material756 : Material (8 : Basis) (17 : Basis) where
  plus := ![v756_pa,v756_pb,v756_pg]
  minus := ![(Primitive.Addresses.material756 1).one,v756_mb,v756_mg]
  upper := v756_upper
  lower := (Primitive.Addresses.material756 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v756_pa_checked.trans (by decide +kernel)
    · exact v756_pb_checked.trans (by decide +kernel)
    · exact v756_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 17 Primitive.Addresses.material756
    · exact v756_mb_checked.trans (by decide +kernel)
    · exact v756_mg_checked.trans (by decide +kernel)
  upper_error := v756_upper_checked
  lower_error := reuse_lower_error 8 17 Primitive.Addresses.material756

def v757_pa : Scalar.QComplex := ((999999999571798097390324898888 : Int)/10^30,(29264377748997044629194384 : Int)/10^30)
theorem v757_pa_checked : Scalar.distance (sourceCoefficient 8 18 1 0) v757_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v757_pb : Scalar.QComplex := ((12626921077684299881858 : Int)/10^30,(-431477517840275313770906941 : Int)/10^30)
theorem v757_pb_checked : Scalar.distance (sourceCoefficient 8 18 1 1) v757_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v757_pg : Scalar.QComplex := ((-93086429536138196792246 : Int)/10^30,(-2724116438417415775 : Int)/10^30)
theorem v757_pg_checked : Scalar.distance (sourceCoefficient 8 18 1 2) v757_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v757_mb : Scalar.QComplex := ((-359718748494037400758999 : Int)/10^30,(-431477368077940119735381895 : Int)/10^30)
theorem v757_mb_checked : Scalar.distance (sourceCoefficient 8 18 3 1) v757_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v757_mg : Scalar.QComplex := ((-93086397226596017197784 : Int)/10^30,(77605280808427913794 : Int)/10^30)
theorem v757_mg_checked : Scalar.distance (sourceCoefficient 8 18 3 2) v757_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v757_upper : Scalar.QComplex := ((999998560696928137999390782625 : Int)/10^30,(-1696644945806478553293615628 : Int)/10^30)
theorem v757_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 18 5) 1) 14) v757_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material757 : Material (8 : Basis) (18 : Basis) where
  plus := ![v757_pa,v757_pb,v757_pg]
  minus := ![(Primitive.Addresses.material757 1).one,v757_mb,v757_mg]
  upper := v757_upper
  lower := (Primitive.Addresses.material757 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v757_pa_checked.trans (by decide +kernel)
    · exact v757_pb_checked.trans (by decide +kernel)
    · exact v757_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 18 Primitive.Addresses.material757
    · exact v757_mb_checked.trans (by decide +kernel)
    · exact v757_mg_checked.trans (by decide +kernel)
  upper_error := v757_upper_checked
  lower_error := reuse_lower_error 8 18 Primitive.Addresses.material757

def v758_pa : Scalar.QComplex := ((999999999907346845200410897793 : Int)/10^30,(13612726016143629022526142 : Int)/10^30)
theorem v758_pa_checked : Scalar.distance (sourceCoefficient 8 19 1 0) v758_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v758_pb : Scalar.QComplex := ((5873585228527226840762 : Int)/10^30,(-431477517509528044942674477 : Int)/10^30)
theorem v758_pb_checked : Scalar.distance (sourceCoefficient 8 19 1 1) v758_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v758_pg : Scalar.QComplex := ((-93086429516078210119870 : Int)/10^30,(-1267160060940844431 : Int)/10^30)
theorem v758_pg_checked : Scalar.distance (sourceCoefficient 8 19 1 2) v758_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v758_mb : Scalar.QComplex := ((-366472081543198897768598 : Int)/10^30,(-431477361919368295192654342 : Int)/10^30)
theorem v758_mb_checked : Scalar.distance (sourceCoefficient 8 19 3 1) v758_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v758_mg : Scalar.QComplex := ((-93086395949248303111731 : Int)/10^30,(79062236626102174577 : Int)/10^30)
theorem v758_mg_checked : Scalar.distance (sourceCoefficient 8 19 3 2) v758_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v758_upper : Scalar.QComplex := ((999998534019145401897539504380 : Int)/10^30,(-1712296574807161982955909864 : Int)/10^30)
theorem v758_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 19 5) 1) 14) v758_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material758 : Material (8 : Basis) (19 : Basis) where
  plus := ![v758_pa,v758_pb,v758_pg]
  minus := ![(Primitive.Addresses.material758 1).one,v758_mb,v758_mg]
  upper := v758_upper
  lower := (Primitive.Addresses.material758 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v758_pa_checked.trans (by decide +kernel)
    · exact v758_pb_checked.trans (by decide +kernel)
    · exact v758_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 19 Primitive.Addresses.material758
    · exact v758_mb_checked.trans (by decide +kernel)
    · exact v758_mg_checked.trans (by decide +kernel)
  upper_error := v758_upper_checked
  lower_error := reuse_lower_error 8 19 Primitive.Addresses.material758

def v759_pa : Scalar.QComplex := ((999999999941601209929505053450 : Int)/10^30,(10807292914397179159050187 : Int)/10^30)
theorem v759_pa_checked : Scalar.distance (sourceCoefficient 8 20 1 0) v759_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v759_pb : Scalar.QComplex := ((4663103917173058807243 : Int)/10^30,(-431477517435349610899138734 : Int)/10^30)
theorem v759_pb_checked : Scalar.distance (sourceCoefficient 8 20 1 1) v759_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v759_pg : Scalar.QComplex := ((-93086429509670936373534 : Int)/10^30,(-1006012310125149097 : Int)/10^30)
theorem v759_pg_checked : Scalar.distance (sourceCoefficient 8 20 1 2) v759_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v759_mb : Scalar.QComplex := ((-367682562339822904149162 : Int)/10^30,(-431477360800599035124950783 : Int)/10^30)
theorem v759_mb_checked : Scalar.distance (sourceCoefficient 8 20 3 1) v759_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v759_mg : Scalar.QComplex := ((-93086395717482284455253 : Int)/10^30,(79323384274151438571 : Int)/10^30)
theorem v759_mg_checked : Scalar.distance (sourceCoefficient 8 20 3 2) v759_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v759_upper : Scalar.QComplex := ((999998529211476688897300348236 : Int)/10^30,(-1715102003789665303080480117 : Int)/10^30)
theorem v759_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 20 5) 1) 14) v759_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material759 : Material (8 : Basis) (20 : Basis) where
  plus := ![v759_pa,v759_pb,v759_pg]
  minus := ![(Primitive.Addresses.material759 1).one,v759_mb,v759_mg]
  upper := v759_upper
  lower := (Primitive.Addresses.material759 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v759_pa_checked.trans (by decide +kernel)
    · exact v759_pb_checked.trans (by decide +kernel)
    · exact v759_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 20 Primitive.Addresses.material759
    · exact v759_mb_checked.trans (by decide +kernel)
    · exact v759_mg_checked.trans (by decide +kernel)
  upper_error := v759_upper_checked
  lower_error := reuse_lower_error 8 20 Primitive.Addresses.material759

def v760_pa : Scalar.QComplex := ((999999999109515442402366328038 : Int)/10^30,(-42201529763769282071039452 : Int)/10^30)
theorem v760_pa_checked : Scalar.distance (sourceCoefficient 8 21 1 0) v760_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v760_pb : Scalar.QComplex := ((-18209011215594081700474 : Int)/10^30,(-431477515182683698569103005 : Int)/10^30)
theorem v760_pb_checked : Scalar.distance (sourceCoefficient 8 21 1 1) v760_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v760_pg : Scalar.QComplex := ((-93086429227949303933129 : Int)/10^30,(3928389717164475762 : Int)/10^30)
theorem v760_pg_checked : Scalar.distance (sourceCoefficient 8 21 1 2) v760_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v760_mb : Scalar.QComplex := ((-390554667012307047392512 : Int)/10^30,(-431477338810328723813004055 : Int)/10^30)
theorem v760_mb_checked : Scalar.distance (sourceCoefficient 8 21 3 1) v760_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v760_mg : Scalar.QComplex := ((-93086391177594044579218 : Int)/10^30,(84257784221024594832 : Int)/10^30)
theorem v760_mg_checked : Scalar.distance (sourceCoefficient 8 21 3 2) v760_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v760_upper : Scalar.QComplex := ((999998436890973140976976259218 : Int)/10^30,(-1768110746081312690385342736 : Int)/10^30)
theorem v760_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 21 5) 1) 14) v760_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material760 : Material (8 : Basis) (21 : Basis) where
  plus := ![v760_pa,v760_pb,v760_pg]
  minus := ![(Primitive.Addresses.material760 1).one,v760_mb,v760_mg]
  upper := v760_upper
  lower := (Primitive.Addresses.material760 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v760_pa_checked.trans (by decide +kernel)
    · exact v760_pb_checked.trans (by decide +kernel)
    · exact v760_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 21 Primitive.Addresses.material760
    · exact v760_mb_checked.trans (by decide +kernel)
    · exact v760_mg_checked.trans (by decide +kernel)
  upper_error := v760_upper_checked
  lower_error := reuse_lower_error 8 21 Primitive.Addresses.material760

def v761_pa : Scalar.QComplex := ((999999999049710615769194962516 : Int)/10^30,(-43595627849115330308114809 : Int)/10^30)
theorem v761_pa_checked : Scalar.distance (sourceCoefficient 8 22 1 0) v761_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v761_pb : Scalar.QComplex := ((-18810533191506874912514 : Int)/10^30,(-431477515101623659475380412 : Int)/10^30)
theorem v761_pb_checked : Scalar.distance (sourceCoefficient 8 22 1 1) v761_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v761_pg : Scalar.QComplex := ((-93086429216421898485516 : Int)/10^30,(4058161329778573083 : Int)/10^30)
theorem v761_pg_checked : Scalar.distance (sourceCoefficient 8 22 1 2) v761_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v761_mb : Scalar.QComplex := ((-391156188694294555130595 : Int)/10^30,(-431477338210182341233007823 : Int)/10^30)
theorem v761_mb_checked : Scalar.distance (sourceCoefficient 8 22 3 1) v761_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v761_mg : Scalar.QComplex := ((-93086391054079586434285 : Int)/10^30,(84387555775371158195 : Int)/10^30)
theorem v761_mg_checked : Scalar.distance (sourceCoefficient 8 22 3 2) v761_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v761_upper : Scalar.QComplex := ((999998434425081579699150484443 : Int)/10^30,(-1769504841987095697446892747 : Int)/10^30)
theorem v761_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 22 5) 1) 14) v761_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material761 : Material (8 : Basis) (22 : Basis) where
  plus := ![v761_pa,v761_pb,v761_pg]
  minus := ![(Primitive.Addresses.material761 1).one,v761_mb,v761_mg]
  upper := v761_upper
  lower := (Primitive.Addresses.material761 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v761_pa_checked.trans (by decide +kernel)
    · exact v761_pb_checked.trans (by decide +kernel)
    · exact v761_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 22 Primitive.Addresses.material761
    · exact v761_mb_checked.trans (by decide +kernel)
    · exact v761_mg_checked.trans (by decide +kernel)
  upper_error := v761_upper_checked
  lower_error := reuse_lower_error 8 22 Primitive.Addresses.material761

def v762_pa : Scalar.QComplex := ((999999998547159190416243564472 : Int)/10^30,(-53904374748778660265988778 : Int)/10^30)
theorem v762_pa_checked : Scalar.distance (sourceCoefficient 8 23 1 0) v762_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v762_pb : Scalar.QComplex := ((-23258525669319552280982 : Int)/10^30,(-431477514467517270490084396 : Int)/10^30)
theorem v762_pb_checked : Scalar.distance (sourceCoefficient 8 23 1 1) v762_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v762_pg : Scalar.QComplex := ((-93086429124630873396658 : Int)/10^30,(5017765766849741779 : Int)/10^30)
theorem v762_pg_checked : Scalar.distance (sourceCoefficient 8 23 1 2) v762_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v762_mb : Scalar.QComplex := ((-395604178968711095108055 : Int)/10^30,(-431477333737659010146756105 : Int)/10^30)
theorem v762_mb_checked : Scalar.distance (sourceCoefficient 8 23 3 1) v762_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v762_mg : Scalar.QComplex := ((-93086390134193185310484 : Int)/10^30,(85347159775926218343 : Int)/10^30)
theorem v762_mg_checked : Scalar.distance (sourceCoefficient 8 23 3 2) v762_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v762_upper : Scalar.QComplex := ((999998416130568956231944480231 : Int)/10^30,(-1779813572665733301781678255 : Int)/10^30)
theorem v762_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 23 5) 1) 14) v762_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material762 : Material (8 : Basis) (23 : Basis) where
  plus := ![v762_pa,v762_pb,v762_pg]
  minus := ![(Primitive.Addresses.material762 1).one,v762_mb,v762_mg]
  upper := v762_upper
  lower := (Primitive.Addresses.material762 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v762_pa_checked.trans (by decide +kernel)
    · exact v762_pb_checked.trans (by decide +kernel)
    · exact v762_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 23 Primitive.Addresses.material762
    · exact v762_mb_checked.trans (by decide +kernel)
    · exact v762_mg_checked.trans (by decide +kernel)
  upper_error := v762_upper_checked
  lower_error := reuse_lower_error 8 23 Primitive.Addresses.material762

def v763_pa : Scalar.QComplex := ((999999994503201938169817575250 : Int)/10^30,(-104850350945743505017052031 : Int)/10^30)
theorem v763_pa_checked : Scalar.distance (sourceCoefficient 8 24 1 0) v763_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v763_pb : Scalar.QComplex := ((-45240568643097489723697 : Int)/10^30,(-431477510436085016734500681 : Int)/10^30)
theorem v763_pb_checked : Scalar.distance (sourceCoefficient 8 24 1 1) v763_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v763_pg : Scalar.QComplex := ((-93086428501543984279574 : Int)/10^30,(9760144750322292199 : Int)/10^30)
theorem v763_pg_checked : Scalar.distance (sourceCoefficient 8 24 1 2) v763_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v763_mb : Scalar.QComplex := ((-417586210278625338397146 : Int)/10^30,(-431477310736715205571018138 : Int)/10^30)
theorem v763_mb_checked : Scalar.distance (sourceCoefficient 8 24 3 1) v763_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v763_mg : Scalar.QComplex := ((-93086385418647054280940 : Int)/10^30,(90089536455898413273 : Int)/10^30)
theorem v763_mg_checked : Scalar.distance (sourceCoefficient 8 24 3 2) v763_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v763_upper : Scalar.QComplex := ((999998324158484593880689349389 : Int)/10^30,(-1830759466005147783467139459 : Int)/10^30)
theorem v763_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 24 5) 1) 14) v763_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material763 : Material (8 : Basis) (24 : Basis) where
  plus := ![v763_pa,v763_pb,v763_pg]
  minus := ![(Primitive.Addresses.material763 1).one,v763_mb,v763_mg]
  upper := v763_upper
  lower := (Primitive.Addresses.material763 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v763_pa_checked.trans (by decide +kernel)
    · exact v763_pb_checked.trans (by decide +kernel)
    · exact v763_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 24 Primitive.Addresses.material763
    · exact v763_mb_checked.trans (by decide +kernel)
    · exact v763_mg_checked.trans (by decide +kernel)
  upper_error := v763_upper_checked
  lower_error := reuse_lower_error 8 24 Primitive.Addresses.material763

def v764_pa : Scalar.QComplex := ((999999991829145995622892085300 : Int)/10^30,(-127834689900634407838284194 : Int)/10^30)
theorem v764_pa_checked : Scalar.distance (sourceCoefficient 8 25 1 0) v764_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v764_pb : Scalar.QComplex := ((-55157793901392869843334 : Int)/10^30,(-431477508128510397069695099 : Int)/10^30)
theorem v764_pb_checked : Scalar.distance (sourceCoefficient 8 25 1 1) v764_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v764_pg : Scalar.QComplex := ((-93086428128168168724316 : Int)/10^30,(11899674770952575317 : Int)/10^30)
theorem v764_pg_checked : Scalar.distance (sourceCoefficient 8 25 1 2) v764_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v764_mb : Scalar.QComplex := ((-427503429852951547800724 : Int)/10^30,(-431477299871022702457803334 : Int)/10^30)
theorem v764_mb_checked : Scalar.distance (sourceCoefficient 8 25 3 1) v764_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v764_mg : Scalar.QComplex := ((-93086383198953330801674 : Int)/10^30,(92229065357677375756 : Int)/10^30)
theorem v764_mg_checked : Scalar.distance (sourceCoefficient 8 25 3 2) v764_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v764_upper : Scalar.QComplex := ((999998281815548720826176481692 : Int)/10^30,(-1853743766112387774715876902 : Int)/10^30)
theorem v764_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 25 5) 1) 14) v764_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material764 : Material (8 : Basis) (25 : Basis) where
  plus := ![v764_pa,v764_pb,v764_pg]
  minus := ![(Primitive.Addresses.material764 1).one,v764_mb,v764_mg]
  upper := v764_upper
  lower := (Primitive.Addresses.material764 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v764_pa_checked.trans (by decide +kernel)
    · exact v764_pb_checked.trans (by decide +kernel)
    · exact v764_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 25 Primitive.Addresses.material764
    · exact v764_mb_checked.trans (by decide +kernel)
    · exact v764_mg_checked.trans (by decide +kernel)
  upper_error := v764_upper_checked
  lower_error := reuse_lower_error 8 25 Primitive.Addresses.material764

def v765_pa : Scalar.QComplex := ((999999990863370210123784875100 : Int)/10^30,(-135178620707101558784053665 : Int)/10^30)
theorem v765_pa_checked : Scalar.distance (sourceCoefficient 8 26 1 0) v765_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v765_pb : Scalar.QComplex := ((-58326534839527478639218 : Int)/10^30,(-431477507327128394067554692 : Int)/10^30)
theorem v765_pb_checked : Scalar.distance (sourceCoefficient 8 26 1 1) v765_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v765_pg : Scalar.QComplex := ((-93086427996773274919689 : Int)/10^30,(12583295058123642578 : Int)/10^30)
theorem v765_pg_checked : Scalar.distance (sourceCoefficient 8 26 1 2) v765_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v765_mb : Scalar.QComplex := ((-430672168919662511028773 : Int)/10^30,(-431477296335160283030671622 : Int)/10^30)
theorem v765_mb_checked : Scalar.distance (sourceCoefficient 8 26 3 1) v765_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v765_mg : Scalar.QComplex := ((-93086382477624967207529 : Int)/10^30,(92912685276917491565 : Int)/10^30)
theorem v765_mg_checked : Scalar.distance (sourceCoefficient 8 26 3 2) v765_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v765_upper : Scalar.QComplex := ((999998268174816037972762371350 : Int)/10^30,(-1861087684314091276864621569 : Int)/10^30)
theorem v765_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 26 5) 1) 14) v765_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material765 : Material (8 : Basis) (26 : Basis) where
  plus := ![v765_pa,v765_pb,v765_pg]
  minus := ![(Primitive.Addresses.material765 1).one,v765_mb,v765_mg]
  upper := v765_upper
  lower := (Primitive.Addresses.material765 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v765_pa_checked.trans (by decide +kernel)
    · exact v765_pb_checked.trans (by decide +kernel)
    · exact v765_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 26 Primitive.Addresses.material765
    · exact v765_mb_checked.trans (by decide +kernel)
    · exact v765_mg_checked.trans (by decide +kernel)
  upper_error := v765_upper_checked
  lower_error := reuse_lower_error 8 26 Primitive.Addresses.material765

def v766_pa : Scalar.QComplex := ((999999990168635316784888958043 : Int)/10^30,(-140223854139638062330128223 : Int)/10^30)
theorem v766_pa_checked : Scalar.distance (sourceCoefficient 8 27 1 0) v766_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v766_pb : Scalar.QComplex := ((-60503439567084572248686 : Int)/10^30,(-431477506758604069554418328 : Int)/10^30)
theorem v766_pb_checked : Scalar.distance (sourceCoefficient 8 27 1 1) v766_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v766_pg : Scalar.QComplex := ((-93086427903111710187394 : Int)/10^30,(13052937816994062883 : Int)/10^30)
theorem v766_pg_checked : Scalar.distance (sourceCoefficient 8 27 1 2) v766_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v766_mb : Scalar.QComplex := ((-432849072346047598438029 : Int)/10^30,(-431477293888065434472711603 : Int)/10^30)
theorem v766_mb_checked : Scalar.distance (sourceCoefficient 8 27 3 1) v766_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v766_mg : Scalar.QComplex := ((-93086381978682888369205 : Int)/10^30,(93382327780092737005 : Int)/10^30)
theorem v766_mg_checked : Scalar.distance (sourceCoefficient 8 27 3 2) v766_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v766_upper : Scalar.QComplex := ((999998258772466974803519177302 : Int)/10^30,(-1866132909033295837352543789 : Int)/10^30)
theorem v766_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 27 5) 1) 14) v766_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material766 : Material (8 : Basis) (27 : Basis) where
  plus := ![v766_pa,v766_pb,v766_pg]
  minus := ![(Primitive.Addresses.material766 1).one,v766_mb,v766_mg]
  upper := v766_upper
  lower := (Primitive.Addresses.material766 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v766_pa_checked.trans (by decide +kernel)
    · exact v766_pb_checked.trans (by decide +kernel)
    · exact v766_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 27 Primitive.Addresses.material766
    · exact v766_mb_checked.trans (by decide +kernel)
    · exact v766_mg_checked.trans (by decide +kernel)
  upper_error := v766_upper_checked
  lower_error := reuse_lower_error 8 27 Primitive.Addresses.material766

def v767_pa : Scalar.QComplex := ((999999989192495255288326914362 : Int)/10^30,(-147020438622054135688807807 : Int)/10^30)
theorem v767_pa_checked : Scalar.distance (sourceCoefficient 8 28 1 0) v767_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v767_pb : Scalar.QComplex := ((-63436012868782151839565 : Int)/10^30,(-431477505969576656611130494 : Int)/10^30)
theorem v767_pb_checked : Scalar.distance (sourceCoefficient 8 28 1 1) v767_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v767_pg : Scalar.QComplex := ((-93086427772567111671419 : Int)/10^30,(13685607588790247465 : Int)/10^30)
theorem v767_pg_checked : Scalar.distance (sourceCoefficient 8 28 1 2) v767_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v767_mb : Scalar.QComplex := ((-435781643874918991691477 : Int)/10^30,(-431477290568359634153914018 : Int)/10^30)
theorem v767_mb_checked : Scalar.distance (sourceCoefficient 8 28 3 1) v767_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v767_mg : Scalar.QComplex := ((-93086381302172819789603 : Int)/10^30,(94014997203662942101 : Int)/10^30)
theorem v767_mg_checked : Scalar.distance (sourceCoefficient 8 28 3 2) v767_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v767_upper : Scalar.QComplex := ((999998246066040131830546422897 : Int)/10^30,(-1872929481708268515640687574 : Int)/10^30)
theorem v767_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 28 5) 1) 14) v767_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material767 : Material (8 : Basis) (28 : Basis) where
  plus := ![v767_pa,v767_pb,v767_pg]
  minus := ![(Primitive.Addresses.material767 1).one,v767_mb,v767_mg]
  upper := v767_upper
  lower := (Primitive.Addresses.material767 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v767_pa_checked.trans (by decide +kernel)
    · exact v767_pb_checked.trans (by decide +kernel)
    · exact v767_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 28 Primitive.Addresses.material767
    · exact v767_mb_checked.trans (by decide +kernel)
    · exact v767_mg_checked.trans (by decide +kernel)
  upper_error := v767_upper_checked
  lower_error := reuse_lower_error 8 28 Primitive.Addresses.material767

def v768_pa : Scalar.QComplex := ((999999987073963880364590582708 : Int)/10^30,(-160785795616989777261693191 : Int)/10^30)
theorem v768_pa_checked : Scalar.distance (sourceCoefficient 8 29 1 0) v768_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v768_pb : Scalar.QComplex := ((-69375454714868826206459 : Int)/10^30,(-431477504290114580585583848 : Int)/10^30)
theorem v768_pb_checked : Scalar.distance (sourceCoefficient 8 29 1 1) v768_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v768_pg : Scalar.QComplex := ((-93086427492801309143923 : Int)/10^30,(14966975499036955335 : Int)/10^30)
theorem v768_pg_checked : Scalar.distance (sourceCoefficient 8 29 1 2) v768_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v768_mb : Scalar.QComplex := ((-441721082060179889412199 : Int)/10^30,(-431477283763427372826640544 : Int)/10^30)
theorem v768_mb_checked : Scalar.distance (sourceCoefficient 8 29 3 1) v768_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v768_mg : Scalar.QComplex := ((-93086379916644325557149 : Int)/10^30,(95296364395372528183 : Int)/10^30)
theorem v768_mg_checked : Scalar.distance (sourceCoefficient 8 29 3 2) v768_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v768_upper : Scalar.QComplex := ((999998220189754522383135238723 : Int)/10^30,(-1886694814544928944223727534 : Int)/10^30)
theorem v768_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 29 5) 1) 14) v768_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material768 : Material (8 : Basis) (29 : Basis) where
  plus := ![v768_pa,v768_pb,v768_pg]
  minus := ![(Primitive.Addresses.material768 1).one,v768_mb,v768_mg]
  upper := v768_upper
  lower := (Primitive.Addresses.material768 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v768_pa_checked.trans (by decide +kernel)
    · exact v768_pb_checked.trans (by decide +kernel)
    · exact v768_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 29 Primitive.Addresses.material768
    · exact v768_mb_checked.trans (by decide +kernel)
    · exact v768_mg_checked.trans (by decide +kernel)
  upper_error := v768_upper_checked
  lower_error := reuse_lower_error 8 29 Primitive.Addresses.material768

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
