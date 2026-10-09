import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B148

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3553_pa : Scalar.QComplex := ((999998782594536806831228943683 : Int)/10^30,(-1560387594256720476551329587 : Int)/10^30)
theorem v3553_pa_checked : Scalar.distance (sourceCoefficient 48 74 1 0) v3553_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3553_pb : Scalar.QComplex := ((-673272147830116717851639 : Int)/10^30,(-431476980887965684194173048 : Int)/10^30)
theorem v3553_pb_checked : Scalar.distance (sourceCoefficient 48 74 1 1) v3553_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3553_pg : Scalar.QComplex := ((-93086314973388384297218 : Int)/10^30,(145250907908797660080 : Int)/10^30)
theorem v3553_pg_checked : Scalar.distance (sourceCoefficient 48 74 1 2) v3553_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3553_mb : Scalar.QComplex := ((-1045617098644608152058867 : Int)/10^30,(-431476239225825701919221205 : Int)/10^30)
theorem v3553_mb_checked : Scalar.distance (sourceCoefficient 48 74 3 1) v3553_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3553_mg : Scalar.QComplex := ((-93086154968107397700635 : Int)/10^30,(225580151195285259010 : Int)/10^30)
theorem v3553_mg_checked : Scalar.distance (sourceCoefficient 48 74 3 2) v3553_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3553_upper : Scalar.QComplex := ((999994600126387810623606643862 : Int)/10^30,(-3286292449819967737128225126 : Int)/10^30)
theorem v3553_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 74 5) 1) 14) v3553_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3553 : Material (48 : Basis) (74 : Basis) where
  plus := ![v3553_pa,v3553_pb,v3553_pg]
  minus := ![(Primitive.Addresses.material3553 1).one,v3553_mb,v3553_mg]
  upper := v3553_upper
  lower := (Primitive.Addresses.material3553 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3553_pa_checked.trans (by decide +kernel)
    · exact v3553_pb_checked.trans (by decide +kernel)
    · exact v3553_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 74 Primitive.Addresses.material3553
    · exact v3553_mb_checked.trans (by decide +kernel)
    · exact v3553_mg_checked.trans (by decide +kernel)
  upper_error := v3553_upper_checked
  lower_error := reuse_lower_error 48 74 Primitive.Addresses.material3553

def v3554_pa : Scalar.QComplex := ((999998759367449511222411798022 : Int)/10^30,(-1575202704990195807565791554 : Int)/10^30)
theorem v3554_pa_checked : Scalar.distance (sourceCoefficient 48 75 1 0) v3554_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3554_pb : Scalar.QComplex := ((-679664533313987369393888 : Int)/10^30,(-431476969882599465533963825 : Int)/10^30)
theorem v3554_pb_checked : Scalar.distance (sourceCoefficient 48 75 1 1) v3554_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3554_pg : Scalar.QComplex := ((-93086312705182979218133 : Int)/10^30,(146629993484710255351 : Int)/10^30)
theorem v3554_pg_checked : Scalar.distance (sourceCoefficient 48 75 1 2) v3554_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3554_mb : Scalar.QComplex := ((-1052009472251166158097974 : Int)/10^30,(-431476222704122810834208749 : Int)/10^30)
theorem v3554_mb_checked : Scalar.distance (sourceCoefficient 48 75 3 1) v3554_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3554_mg : Scalar.QComplex := ((-93086151509814096874159 : Int)/10^30,(226959234300342158640 : Int)/10^30)
theorem v3554_mg_checked : Scalar.distance (sourceCoefficient 48 75 3 2) v3554_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3554_upper : Scalar.QComplex := ((999994551329797999401310981967 : Int)/10^30,(-3301107498400230408466231711 : Int)/10^30)
theorem v3554_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 75 5) 1) 14) v3554_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3554 : Material (48 : Basis) (75 : Basis) where
  plus := ![v3554_pa,v3554_pb,v3554_pg]
  minus := ![(Primitive.Addresses.material3554 1).one,v3554_mb,v3554_mg]
  upper := v3554_upper
  lower := (Primitive.Addresses.material3554 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3554_pa_checked.trans (by decide +kernel)
    · exact v3554_pb_checked.trans (by decide +kernel)
    · exact v3554_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 75 Primitive.Addresses.material3554
    · exact v3554_mb_checked.trans (by decide +kernel)
    · exact v3554_mg_checked.trans (by decide +kernel)
  upper_error := v3554_upper_checked
  lower_error := reuse_lower_error 48 75 Primitive.Addresses.material3554

def v3555_pa : Scalar.QComplex := ((999998739710133872867365397692 : Int)/10^30,(-1587632874415152253356013296 : Int)/10^30)
theorem v3555_pa_checked : Scalar.distance (sourceCoefficient 48 76 1 0) v3555_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3555_pb : Scalar.QComplex := ((-685027870457916031122050 : Int)/10^30,(-431476960551463263487547737 : Int)/10^30)
theorem v3555_pb_checked : Scalar.distance (sourceCoefficient 48 76 1 1) v3555_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3555_pg : Scalar.QComplex := ((-93086310783724386322790 : Int)/10^30,(147787073412817498320 : Int)/10^30)
theorem v3555_pg_checked : Scalar.distance (sourceCoefficient 48 76 1 2) v3555_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3555_mb : Scalar.QComplex := ((-1057372799345729000932755 : Int)/10^30,(-431476208744671683723811660 : Int)/10^30)
theorem v3555_mb_checked : Scalar.distance (sourceCoefficient 48 76 3 1) v3555_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3555_mg : Scalar.QComplex := ((-93086148589848354414553 : Int)/10^30,(228116312139483436824 : Int)/10^30)
theorem v3555_mg_checked : Scalar.distance (sourceCoefficient 48 76 3 2) v3555_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3555_upper : Scalar.QComplex := ((999994510219166866995437502837 : Int)/10^30,(-3313537615385166151997989005 : Int)/10^30)
theorem v3555_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 76 5) 1) 14) v3555_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3555 : Material (48 : Basis) (76 : Basis) where
  plus := ![v3555_pa,v3555_pb,v3555_pg]
  minus := ![(Primitive.Addresses.material3555 1).one,v3555_mb,v3555_mg]
  upper := v3555_upper
  lower := (Primitive.Addresses.material3555 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3555_pa_checked.trans (by decide +kernel)
    · exact v3555_pb_checked.trans (by decide +kernel)
    · exact v3555_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 76 Primitive.Addresses.material3555
    · exact v3555_mb_checked.trans (by decide +kernel)
    · exact v3555_mg_checked.trans (by decide +kernel)
  upper_error := v3555_upper_checked
  lower_error := reuse_lower_error 48 76 Primitive.Addresses.material3555

def v3556_pa : Scalar.QComplex := ((999998735137272623257195947653 : Int)/10^30,(-1590510564213820775706141524 : Int)/10^30)
theorem v3556_pa_checked : Scalar.distance (sourceCoefficient 48 77 1 0) v3556_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3556_pb : Scalar.QComplex := ((-686269528552685612284807 : Int)/10^30,(-431476958378554519078054276 : Int)/10^30)
theorem v3556_pb_checked : Scalar.distance (sourceCoefficient 48 77 1 1) v3556_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3556_pg : Scalar.QComplex := ((-93086310336498391776851 : Int)/10^30,(148054947243071245465 : Int)/10^30)
theorem v3556_pg_checked : Scalar.distance (sourceCoefficient 48 77 1 2) v3556_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3556_mb : Scalar.QComplex := ((-1058614455103050144586095 : Int)/10^30,(-431476205500268734806060640 : Int)/10^30)
theorem v3556_mb_checked : Scalar.distance (sourceCoefficient 48 77 3 1) v3556_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3556_mg : Scalar.QComplex := ((-93086147911459475471763 : Int)/10^30,(228384185484059623544 : Int)/10^30)
theorem v3556_mg_checked : Scalar.distance (sourceCoefficient 48 77 3 2) v3556_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3556_upper : Scalar.QComplex := ((999994500679680897602294694923 : Int)/10^30,(-3316415293005510086325729565 : Int)/10^30)
theorem v3556_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 77 5) 1) 14) v3556_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3556 : Material (48 : Basis) (77 : Basis) where
  plus := ![v3556_pa,v3556_pb,v3556_pg]
  minus := ![(Primitive.Addresses.material3556 1).one,v3556_mb,v3556_mg]
  upper := v3556_upper
  lower := (Primitive.Addresses.material3556 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3556_pa_checked.trans (by decide +kernel)
    · exact v3556_pb_checked.trans (by decide +kernel)
    · exact v3556_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 77 Primitive.Addresses.material3556
    · exact v3556_mb_checked.trans (by decide +kernel)
    · exact v3556_mg_checked.trans (by decide +kernel)
  upper_error := v3556_upper_checked
  lower_error := reuse_lower_error 48 77 Primitive.Addresses.material3556

def v3557_pa : Scalar.QComplex := ((999998707472455456463293922468 : Int)/10^30,(-1607810131346242017581526591 : Int)/10^30)
theorem v3557_pa_checked : Scalar.distance (sourceCoefficient 48 78 1 0) v3557_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3557_pb : Scalar.QComplex := ((-693733900629908479375765 : Int)/10^30,(-431476945215453356002614858 : Int)/10^30)
theorem v3557_pb_checked : Scalar.distance (sourceCoefficient 48 78 1 1) v3557_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3557_pg : Scalar.QComplex := ((-93086307628993229314332 : Int)/10^30,(149665301942033516888 : Int)/10^30)
theorem v3557_pg_checked : Scalar.distance (sourceCoefficient 48 78 1 2) v3557_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3557_mb : Scalar.QComplex := ((-1066078813041782689005333 : Int)/10^30,(-431476185895755553150097911 : Int)/10^30)
theorem v3557_mb_checked : Scalar.distance (sourceCoefficient 48 78 3 1) v3557_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3557_mg : Scalar.QComplex := ((-93086143814291743616002 : Int)/10^30,(229994537246958229999 : Int)/10^30)
theorem v3557_mg_checked : Scalar.distance (sourceCoefficient 48 78 3 2) v3557_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3557_upper : Scalar.QComplex := ((999994443157421468215499738418 : Int)/10^30,(-3333714786625293537087935524 : Int)/10^30)
theorem v3557_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 78 5) 1) 14) v3557_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3557 : Material (48 : Basis) (78 : Basis) where
  plus := ![v3557_pa,v3557_pb,v3557_pg]
  minus := ![(Primitive.Addresses.material3557 1).one,v3557_mb,v3557_mg]
  upper := v3557_upper
  lower := (Primitive.Addresses.material3557 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3557_pa_checked.trans (by decide +kernel)
    · exact v3557_pb_checked.trans (by decide +kernel)
    · exact v3557_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 78 Primitive.Addresses.material3557
    · exact v3557_mb_checked.trans (by decide +kernel)
    · exact v3557_mg_checked.trans (by decide +kernel)
  upper_error := v3557_upper_checked
  lower_error := reuse_lower_error 48 78 Primitive.Addresses.material3557

def v3558_pa : Scalar.QComplex := ((999998698490016112441327146085 : Int)/10^30,(-1613387205182587031760071384 : Int)/10^30)
theorem v3558_pa_checked : Scalar.distance (sourceCoefficient 48 79 1 0) v3558_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3558_pb : Scalar.QComplex := ((-696140281869706015250477 : Int)/10^30,(-431476940935202769015745221 : Int)/10^30)
theorem v3558_pb_checked : Scalar.distance (sourceCoefficient 48 79 1 1) v3558_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3558_pg : Scalar.QComplex := ((-93086306749213624576951 : Int)/10^30,(150184451753446139940 : Int)/10^30)
theorem v3558_pg_checked : Scalar.distance (sourceCoefficient 48 79 1 2) v3558_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3558_mb : Scalar.QComplex := ((-1068485189691911031008400 : Int)/10^30,(-431476179538907929338673956 : Int)/10^30)
theorem v3558_mb_checked : Scalar.distance (sourceCoefficient 48 79 3 1) v3558_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3558_mg : Scalar.QComplex := ((-93086142486509560851221 : Int)/10^30,(230513686105857476858 : Int)/10^30)
theorem v3558_mg_checked : Scalar.distance (sourceCoefficient 48 79 3 2) v3558_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3558_upper : Scalar.QComplex := ((999994424549472009136472847258 : Int)/10^30,(-3339291836652366773893586595 : Int)/10^30)
theorem v3558_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 79 5) 1) 14) v3558_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3558 : Material (48 : Basis) (79 : Basis) where
  plus := ![v3558_pa,v3558_pb,v3558_pg]
  minus := ![(Primitive.Addresses.material3558 1).one,v3558_mb,v3558_mg]
  upper := v3558_upper
  lower := (Primitive.Addresses.material3558 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3558_pa_checked.trans (by decide +kernel)
    · exact v3558_pb_checked.trans (by decide +kernel)
    · exact v3558_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 79 Primitive.Addresses.material3558
    · exact v3558_mb_checked.trans (by decide +kernel)
    · exact v3558_mg_checked.trans (by decide +kernel)
  upper_error := v3558_upper_checked
  lower_error := reuse_lower_error 48 79 Primitive.Addresses.material3558

def v3559_pa : Scalar.QComplex := ((999998684396315415954480560588 : Int)/10^30,(-1622099145661274352106513853 : Int)/10^30)
theorem v3559_pa_checked : Scalar.distance (sourceCoefficient 48 80 1 0) v3559_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3559_pb : Scalar.QComplex := ((-699899287149890927595439 : Int)/10^30,(-431476934213219923330444889 : Int)/10^30)
theorem v3559_pb_checked : Scalar.distance (sourceCoefficient 48 80 1 1) v3559_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3559_pg : Scalar.QComplex := ((-93086305368151326316755 : Int)/10^30,(150995415060567171901 : Int)/10^30)
theorem v3559_pg_checked : Scalar.distance (sourceCoefficient 48 80 1 2) v3559_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3559_mb : Scalar.QComplex := ((-1072244187771678033554832 : Int)/10^30,(-431476169573075329068351123 : Int)/10^30)
theorem v3559_mb_checked : Scalar.distance (sourceCoefficient 48 80 3 1) v3559_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3559_mg : Scalar.QComplex := ((-93086140405622967209688 : Int)/10^30,(231324647919225244062 : Int)/10^30)
theorem v3559_mg_checked : Scalar.distance (sourceCoefficient 48 80 3 2) v3559_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3559_upper : Scalar.QComplex := ((999994395419773378413357291576 : Int)/10^30,(-3348003739831193296055407546 : Int)/10^30)
theorem v3559_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 80 5) 1) 14) v3559_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3559 : Material (48 : Basis) (80 : Basis) where
  plus := ![v3559_pa,v3559_pb,v3559_pg]
  minus := ![(Primitive.Addresses.material3559 1).one,v3559_mb,v3559_mg]
  upper := v3559_upper
  lower := (Primitive.Addresses.material3559 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3559_pa_checked.trans (by decide +kernel)
    · exact v3559_pb_checked.trans (by decide +kernel)
    · exact v3559_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 80 Primitive.Addresses.material3559
    · exact v3559_mb_checked.trans (by decide +kernel)
    · exact v3559_mg_checked.trans (by decide +kernel)
  upper_error := v3559_upper_checked
  lower_error := reuse_lower_error 48 80 Primitive.Addresses.material3559

def v3560_pa : Scalar.QComplex := ((999998641501122338843912550622 : Int)/10^30,(-1648331250023220171393790994 : Int)/10^30)
theorem v3560_pa_checked : Scalar.distance (sourceCoefficient 48 81 1 0) v3560_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3560_pb : Scalar.QComplex := ((-711217846719262645091175 : Int)/10^30,(-431476913709302748764809804 : Int)/10^30)
theorem v3560_pb_checked : Scalar.distance (sourceCoefficient 48 81 1 1) v3560_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3560_pg : Scalar.QComplex := ((-93086301159926193404171 : Int)/10^30,(153437267595334891806 : Int)/10^30)
theorem v3560_pg_checked : Scalar.distance (sourceCoefficient 48 81 1 2) v3560_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3560_mb : Scalar.QComplex := ((-1083562725432675680145695 : Int)/10^30,(-431476139301758649679852971 : Int)/10^30)
theorem v3560_mb_checked : Scalar.distance (sourceCoefficient 48 81 3 1) v3560_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3560_mg : Scalar.QComplex := ((-93086134090190640662734 : Int)/10^30,(233766495913270908819 : Int)/10^30)
theorem v3560_mg_checked : Scalar.distance (sourceCoefficient 48 81 3 2) v3560_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3560_upper : Scalar.QComplex := ((999994307250411817853637249888 : Int)/10^30,(-3374235731090289278087053885 : Int)/10^30)
theorem v3560_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 81 5) 1) 14) v3560_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3560 : Material (48 : Basis) (81 : Basis) where
  plus := ![v3560_pa,v3560_pb,v3560_pg]
  minus := ![(Primitive.Addresses.material3560 1).one,v3560_mb,v3560_mg]
  upper := v3560_upper
  lower := (Primitive.Addresses.material3560 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3560_pa_checked.trans (by decide +kernel)
    · exact v3560_pb_checked.trans (by decide +kernel)
    · exact v3560_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 81 Primitive.Addresses.material3560
    · exact v3560_mb_checked.trans (by decide +kernel)
    · exact v3560_mg_checked.trans (by decide +kernel)
  upper_error := v3560_upper_checked
  lower_error := reuse_lower_error 48 81 Primitive.Addresses.material3560

def v3561_pa : Scalar.QComplex := ((999998625066878647675841404444 : Int)/10^30,(-1658271495341929866083009801 : Int)/10^30)
theorem v3561_pa_checked : Scalar.distance (sourceCoefficient 48 82 1 0) v3561_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3561_pb : Scalar.QComplex := ((-715506837620612666241513 : Int)/10^30,(-431476905836235354797246960 : Int)/10^30)
theorem v3561_pb_checked : Scalar.distance (sourceCoefficient 48 82 1 1) v3561_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3561_pg : Scalar.QComplex := ((-93086299545760716731583 : Int)/10^30,(154362569381804770674 : Int)/10^30)
theorem v3561_pg_checked : Scalar.distance (sourceCoefficient 48 82 1 2) v3561_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3561_mb : Scalar.QComplex := ((-1087851707942935800954239 : Int)/10^30,(-431476127727488208329456827 : Int)/10^30)
theorem v3561_mb_checked : Scalar.distance (sourceCoefficient 48 82 3 1) v3561_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3561_mg : Scalar.QComplex := ((-93086131677531997339668 : Int)/10^30,(234691795962256537150 : Int)/10^30)
theorem v3561_mg_checked : Scalar.distance (sourceCoefficient 48 82 3 2) v3561_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3561_upper : Scalar.QComplex := ((999994273660230955479166161218 : Int)/10^30,(-3384175933240157525782464251 : Int)/10^30)
theorem v3561_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 82 5) 1) 14) v3561_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3561 : Material (48 : Basis) (82 : Basis) where
  plus := ![v3561_pa,v3561_pb,v3561_pg]
  minus := ![(Primitive.Addresses.material3561 1).one,v3561_mb,v3561_mg]
  upper := v3561_upper
  lower := (Primitive.Addresses.material3561 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3561_pa_checked.trans (by decide +kernel)
    · exact v3561_pb_checked.trans (by decide +kernel)
    · exact v3561_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 82 Primitive.Addresses.material3561
    · exact v3561_mb_checked.trans (by decide +kernel)
    · exact v3561_mg_checked.trans (by decide +kernel)
  upper_error := v3561_upper_checked
  lower_error := reuse_lower_error 48 82 Primitive.Addresses.material3561

def v3562_pa : Scalar.QComplex := ((999998602474367904643231228128 : Int)/10^30,(-1671840097351663944118692836 : Int)/10^30)
theorem v3562_pa_checked : Scalar.distance (sourceCoefficient 48 83 1 0) v3562_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3562_pb : Scalar.QComplex := ((-721361382258819559620640 : Int)/10^30,(-431476894997609919444712672 : Int)/10^30)
theorem v3562_pb_checked : Scalar.distance (sourceCoefficient 48 83 1 1) v3562_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3562_pg : Scalar.QComplex := ((-93086297325076769971715 : Int)/10^30,(155625621872857860201 : Int)/10^30)
theorem v3562_pg_checked : Scalar.distance (sourceCoefficient 48 83 1 2) v3562_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3562_mb : Scalar.QComplex := ((-1093706241047982562480209 : Int)/10^30,(-431476111836658464822256674 : Int)/10^30)
theorem v3562_mb_checked : Scalar.distance (sourceCoefficient 48 83 3 1) v3562_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3562_mg : Scalar.QComplex := ((-93086128366891463435605 : Int)/10^30,(235954846066667229746 : Int)/10^30)
theorem v3562_mg_checked : Scalar.distance (sourceCoefficient 48 83 3 2) v3562_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3562_upper : Scalar.QComplex := ((999994227649577726495180978194 : Int)/10^30,(-3397744476048428824365170907 : Int)/10^30)
theorem v3562_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 83 5) 1) 14) v3562_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3562 : Material (48 : Basis) (83 : Basis) where
  plus := ![v3562_pa,v3562_pb,v3562_pg]
  minus := ![(Primitive.Addresses.material3562 1).one,v3562_mb,v3562_mg]
  upper := v3562_upper
  lower := (Primitive.Addresses.material3562 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3562_pa_checked.trans (by decide +kernel)
    · exact v3562_pb_checked.trans (by decide +kernel)
    · exact v3562_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 83 Primitive.Addresses.material3562
    · exact v3562_mb_checked.trans (by decide +kernel)
    · exact v3562_mg_checked.trans (by decide +kernel)
  upper_error := v3562_upper_checked
  lower_error := reuse_lower_error 48 83 Primitive.Addresses.material3562

def v3563_pa : Scalar.QComplex := ((999998543110107322104685103923 : Int)/10^30,(-1706979104391038303720768616 : Int)/10^30)
theorem v3563_pa_checked : Scalar.distance (sourceCoefficient 48 84 1 0) v3563_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3563_pb : Scalar.QComplex := ((-736523068067687743006833 : Int)/10^30,(-431476866436175289661364366 : Int)/10^30)
theorem v3563_pb_checked : Scalar.distance (sourceCoefficient 48 84 1 1) v3563_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3563_pg : Scalar.QComplex := ((-93086291481168832807710 : Int)/10^30,(158896585958438776493 : Int)/10^30)
theorem v3563_pg_checked : Scalar.distance (sourceCoefficient 48 84 1 2) v3563_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3563_mb : Scalar.QComplex := ((-1108867896564230469713002 : Int)/10^30,(-431476070191382473693089614 : Int)/10^30)
theorem v3563_mb_checked : Scalar.distance (sourceCoefficient 48 84 3 1) v3563_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3563_mg : Scalar.QComplex := ((-93086119700291015122959 : Int)/10^30,(239225803891289376603 : Int)/10^30)
theorem v3563_mg_checked : Scalar.distance (sourceCoefficient 48 84 3 2) v3563_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3563_upper : Scalar.QComplex := ((999994107638667195906207768366 : Int)/10^30,(-3432883328295051634731766066 : Int)/10^30)
theorem v3563_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 84 5) 1) 14) v3563_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3563 : Material (48 : Basis) (84 : Basis) where
  plus := ![v3563_pa,v3563_pb,v3563_pg]
  minus := ![(Primitive.Addresses.material3563 1).one,v3563_mb,v3563_mg]
  upper := v3563_upper
  lower := (Primitive.Addresses.material3563 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3563_pa_checked.trans (by decide +kernel)
    · exact v3563_pb_checked.trans (by decide +kernel)
    · exact v3563_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 84 Primitive.Addresses.material3563
    · exact v3563_mb_checked.trans (by decide +kernel)
    · exact v3563_mg_checked.trans (by decide +kernel)
  upper_error := v3563_upper_checked
  lower_error := reuse_lower_error 48 84 Primitive.Addresses.material3563

def v3564_pa : Scalar.QComplex := ((999998405036786385245453215124 : Int)/10^30,(-1786035801243036759878908168 : Int)/10^30)
theorem v3564_pa_checked : Scalar.distance (sourceCoefficient 48 85 1 0) v3564_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3564_pb : Scalar.QComplex := ((-770634240590645370127043 : Int)/10^30,(-431476799580970859145897828 : Int)/10^30)
theorem v3564_pb_checked : Scalar.distance (sourceCoefficient 48 85 1 1) v3564_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3564_pg : Scalar.QComplex := ((-93086277843162770261487 : Int)/10^30,(166255690004054768719 : Int)/10^30)
theorem v3564_pg_checked : Scalar.distance (sourceCoefficient 48 85 1 2) v3564_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3564_mb : Scalar.QComplex := ((-1142978998693009232035119 : Int)/10^30,(-431475973899797359293153526 : Int)/10^30)
theorem v3564_mb_checked : Scalar.distance (sourceCoefficient 48 85 3 1) v3564_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3564_mg : Scalar.QComplex := ((-93086099711714681005598 : Int)/10^30,(246584893427789605991 : Int)/10^30)
theorem v3564_mg_checked : Scalar.distance (sourceCoefficient 48 85 3 2) v3564_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3564_upper : Scalar.QComplex := ((999993833120865104004021991701 : Int)/10^30,(-3511939669099360758611449637 : Int)/10^30)
theorem v3564_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 85 5) 1) 14) v3564_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3564 : Material (48 : Basis) (85 : Basis) where
  plus := ![v3564_pa,v3564_pb,v3564_pg]
  minus := ![(Primitive.Addresses.material3564 1).one,v3564_mb,v3564_mg]
  upper := v3564_upper
  lower := (Primitive.Addresses.material3564 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3564_pa_checked.trans (by decide +kernel)
    · exact v3564_pb_checked.trans (by decide +kernel)
    · exact v3564_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 85 Primitive.Addresses.material3564
    · exact v3564_mb_checked.trans (by decide +kernel)
    · exact v3564_mg_checked.trans (by decide +kernel)
  upper_error := v3564_upper_checked
  lower_error := reuse_lower_error 48 85 Primitive.Addresses.material3564

def v3565_pa : Scalar.QComplex := ((999998378881734121970936773278 : Int)/10^30,(-1800620421891195302419344683 : Int)/10^30)
theorem v3565_pa_checked : Scalar.distance (sourceCoefficient 48 86 1 0) v3565_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3565_pb : Scalar.QComplex := ((-776927173472975998605116 : Int)/10^30,(-431476786854464836166550767 : Int)/10^30)
theorem v3565_pb_checked : Scalar.distance (sourceCoefficient 48 86 1 1) v3565_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3565_pg : Scalar.QComplex := ((-93086275253022168440404 : Int)/10^30,(167613319939391267890 : Int)/10^30)
theorem v3565_pg_checked : Scalar.distance (sourceCoefficient 48 86 1 2) v3565_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3565_mb : Scalar.QComplex := ((-1149271918249791829903623 : Int)/10^30,(-431475955742778420698153835 : Int)/10^30)
theorem v3565_mb_checked : Scalar.distance (sourceCoefficient 48 86 3 1) v3565_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3565_mg : Scalar.QComplex := ((-93086095950001554799302 : Int)/10^30,(247942520622443749713 : Int)/10^30)
theorem v3565_mg_checked : Scalar.distance (sourceCoefficient 48 86 3 2) v3565_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3565_upper : Scalar.QComplex := ((999993781794119663335479566165 : Int)/10^30,(-3526524222884192637003369461 : Int)/10^30)
theorem v3565_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 86 5) 1) 14) v3565_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3565 : Material (48 : Basis) (86 : Basis) where
  plus := ![v3565_pa,v3565_pb,v3565_pg]
  minus := ![(Primitive.Addresses.material3565 1).one,v3565_mb,v3565_mg]
  upper := v3565_upper
  lower := (Primitive.Addresses.material3565 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3565_pa_checked.trans (by decide +kernel)
    · exact v3565_pb_checked.trans (by decide +kernel)
    · exact v3565_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 86 Primitive.Addresses.material3565
    · exact v3565_mb_checked.trans (by decide +kernel)
    · exact v3565_mg_checked.trans (by decide +kernel)
  upper_error := v3565_upper_checked
  lower_error := reuse_lower_error 48 86 Primitive.Addresses.material3565

def v3566_pa : Scalar.QComplex := ((999998377142307010790613826338 : Int)/10^30,(-1801586176765165757328406872 : Int)/10^30)
theorem v3566_pa_checked : Scalar.distance (sourceCoefficient 48 87 1 0) v3566_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3566_pb : Scalar.QComplex := ((-777343874784533694672534 : Int)/10^30,(-431476786007429455773269764 : Int)/10^30)
theorem v3566_pb_checked : Scalar.distance (sourceCoefficient 48 87 1 1) v3566_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3566_pg : Scalar.QComplex := ((-93086275080694452661283 : Int)/10^30,(167703218590397269041 : Int)/10^30)
theorem v3566_pg_checked : Scalar.distance (sourceCoefficient 48 87 1 2) v3566_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3566_mb : Scalar.QComplex := ((-1149688618675239199265343 : Int)/10^30,(-431475954536148891350953757 : Int)/10^30)
theorem v3566_mb_checked : Scalar.distance (sourceCoefficient 48 87 3 1) v3566_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3566_mg : Scalar.QComplex := ((-93086095700095416252426 : Int)/10^30,(248032419091265317158 : Int)/10^30)
theorem v3566_mg_checked : Scalar.distance (sourceCoefficient 48 87 3 2) v3566_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3566_upper : Scalar.QComplex := ((999993778387889842952280631764 : Int)/10^30,(-3527489973317691258367676016 : Int)/10^30)
theorem v3566_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 87 5) 1) 14) v3566_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3566 : Material (48 : Basis) (87 : Basis) where
  plus := ![v3566_pa,v3566_pb,v3566_pg]
  minus := ![(Primitive.Addresses.material3566 1).one,v3566_mb,v3566_mg]
  upper := v3566_upper
  lower := (Primitive.Addresses.material3566 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3566_pa_checked.trans (by decide +kernel)
    · exact v3566_pb_checked.trans (by decide +kernel)
    · exact v3566_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 87 Primitive.Addresses.material3566
    · exact v3566_mb_checked.trans (by decide +kernel)
    · exact v3566_mg_checked.trans (by decide +kernel)
  upper_error := v3566_upper_checked
  lower_error := reuse_lower_error 48 87 Primitive.Addresses.material3566

def v3567_pa : Scalar.QComplex := ((999998355887241909333253143664 : Int)/10^30,(-1813345751111621894494663911 : Int)/10^30)
theorem v3567_pa_checked : Scalar.distance (sourceCoefficient 48 88 1 0) v3567_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3567_pb : Scalar.QComplex := ((-782417864212196728457506 : Int)/10^30,(-431476775650404777111596857 : Int)/10^30)
theorem v3567_pb_checked : Scalar.distance (sourceCoefficient 48 88 1 1) v3567_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3567_pg : Scalar.QComplex := ((-93086272974209502672914 : Int)/10^30,(168797875107339402968 : Int)/10^30)
theorem v3567_pg_checked : Scalar.distance (sourceCoefficient 48 88 1 2) v3567_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3567_mb : Scalar.QComplex := ((-1154762597275978241749368 : Int)/10^30,(-431475939800503717010322254 : Int)/10^30)
theorem v3567_mb_checked : Scalar.distance (sourceCoefficient 48 88 3 1) v3567_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3567_mg : Scalar.QComplex := ((-93086092648971977982979 : Int)/10^30,(249127073382815162274 : Int)/10^30)
theorem v3567_mg_checked : Scalar.distance (sourceCoefficient 48 88 3 2) v3567_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3567_upper : Scalar.QComplex := ((999993736836897896685468513788 : Int)/10^30,(-3539249493465328662454648569 : Int)/10^30)
theorem v3567_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 88 5) 1) 14) v3567_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3567 : Material (48 : Basis) (88 : Basis) where
  plus := ![v3567_pa,v3567_pb,v3567_pg]
  minus := ![(Primitive.Addresses.material3567 1).one,v3567_mb,v3567_mg]
  upper := v3567_upper
  lower := (Primitive.Addresses.material3567 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3567_pa_checked.trans (by decide +kernel)
    · exact v3567_pb_checked.trans (by decide +kernel)
    · exact v3567_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 88 Primitive.Addresses.material3567
    · exact v3567_mb_checked.trans (by decide +kernel)
    · exact v3567_mg_checked.trans (by decide +kernel)
  upper_error := v3567_upper_checked
  lower_error := reuse_lower_error 48 88 Primitive.Addresses.material3567

def v3568_pa : Scalar.QComplex := ((999998326582007961900763871567 : Int)/10^30,(-1829435208950681148837142503 : Int)/10^30)
theorem v3568_pa_checked : Scalar.distance (sourceCoefficient 48 89 1 0) v3568_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3568_pb : Scalar.QComplex := ((-789360099988971194011775 : Int)/10^30,(-431476761351026131720013098 : Int)/10^30)
theorem v3568_pb_checked : Scalar.distance (sourceCoefficient 48 89 1 1) v3568_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3568_pg : Scalar.QComplex := ((-93086270067784514328148 : Int)/10^30,(170295584907592648255 : Int)/10^30)
theorem v3568_pg_checked : Scalar.distance (sourceCoefficient 48 89 1 2) v3568_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3568_mb : Scalar.QComplex := ((-1161704818128121300895861 : Int)/10^30,(-431475919510293587267211001 : Int)/10^30)
theorem v3568_mb_checked : Scalar.distance (sourceCoefficient 48 89 3 1) v3568_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3568_mg : Scalar.QComplex := ((-93086088450091968559896 : Int)/10^30,(250624780117288735788 : Int)/10^30)
theorem v3568_mg_checked : Scalar.distance (sourceCoefficient 48 89 3 2) v3568_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3568_upper : Scalar.QComplex := ((999993679762762989953437173134 : Int)/10^30,(-3555338876762855222789217673 : Int)/10^30)
theorem v3568_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 89 5) 1) 14) v3568_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3568 : Material (48 : Basis) (89 : Basis) where
  plus := ![v3568_pa,v3568_pb,v3568_pg]
  minus := ![(Primitive.Addresses.material3568 1).one,v3568_mb,v3568_mg]
  upper := v3568_upper
  lower := (Primitive.Addresses.material3568 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3568_pa_checked.trans (by decide +kernel)
    · exact v3568_pb_checked.trans (by decide +kernel)
    · exact v3568_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 89 Primitive.Addresses.material3568
    · exact v3568_mb_checked.trans (by decide +kernel)
    · exact v3568_mg_checked.trans (by decide +kernel)
  upper_error := v3568_upper_checked
  lower_error := reuse_lower_error 48 89 Primitive.Addresses.material3568

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
