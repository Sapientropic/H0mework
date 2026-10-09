import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B190

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4561_pa : Scalar.QComplex := ((999996787263748936146185760518 : Int)/10^30,(-2534849538030509756562147731 : Int)/10^30)
theorem v4561_pa_checked : Scalar.distance (sourceCoefficient 77 96 1 0) v4561_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4561_pb : Scalar.QComplex := ((-1093730556188774175022518 : Int)/10^30,(-431476119553334679916811263 : Int)/10^30)
theorem v4561_pb_checked : Scalar.distance (sourceCoefficient 77 96 1 1) v4561_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4561_pg : Scalar.QComplex := ((-93086129192641472354931 : Int)/10^30,(235960089658549434638 : Int)/10^30)
theorem v4561_pg_checked : Scalar.distance (sourceCoefficient 77 96 1 2) v4561_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4561_mb : Scalar.QComplex := ((-1466074607154390793777493 : Int)/10^30,(-431475015054845742116036946 : Int)/10^30)
theorem v4561_mb_checked : Scalar.distance (sourceCoefficient 77 96 3 1) v4561_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4561_mg : Scalar.QComplex := ((-93085890909491200274450 : Int)/10^30,(316289138849445722960 : Int)/10^30)
theorem v4561_mg_checked : Scalar.distance (sourceCoefficient 77 96 3 2) v4561_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4561_upper : Scalar.QComplex := ((999990922965659294175529078955 : Int)/10^30,(-4260749498487235237219661884 : Int)/10^30)
theorem v4561_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 96 5) 1) 14) v4561_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4561 : Material (77 : Basis) (96 : Basis) where
  plus := ![v4561_pa,v4561_pb,v4561_pg]
  minus := ![(Primitive.Addresses.material4561 1).one,v4561_mb,v4561_mg]
  upper := v4561_upper
  lower := (Primitive.Addresses.material4561 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4561_pa_checked.trans (by decide +kernel)
    · exact v4561_pb_checked.trans (by decide +kernel)
    · exact v4561_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 96 Primitive.Addresses.material4561
    · exact v4561_mb_checked.trans (by decide +kernel)
    · exact v4561_mg_checked.trans (by decide +kernel)
  upper_error := v4561_upper_checked
  lower_error := reuse_lower_error 77 96 Primitive.Addresses.material4561

def v4562_pa : Scalar.QComplex := ((999996599132174302021621701419 : Int)/10^30,(-2608011519432762952017244042 : Int)/10^30)
theorem v4562_pa_checked : Scalar.distance (sourceCoefficient 77 97 1 0) v4562_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4562_pb : Scalar.QComplex := ((-1125298291811221390043096 : Int)/10^30,(-431476033152344222653612133 : Int)/10^30)
theorem v4562_pb_checked : Scalar.distance (sourceCoefficient 77 97 1 1) v4562_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4562_pg : Scalar.QComplex := ((-93086111116371428739062 : Int)/10^30,(242770475720994764796 : Int)/10^30)
theorem v4562_pg_checked : Scalar.distance (sourceCoefficient 77 97 1 2) v4562_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4562_mb : Scalar.QComplex := ((-1497642256462563911309495 : Int)/10^30,(-431474901412353371752654758 : Int)/10^30)
theorem v4562_mb_checked : Scalar.distance (sourceCoefficient 77 97 3 1) v4562_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4562_mg : Scalar.QComplex := ((-93085866956171443791683 : Int)/10^30,(323099506777066149390 : Int)/10^30)
theorem v4562_mg_checked : Scalar.distance (sourceCoefficient 77 97 3 2) v4562_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4562_upper : Scalar.QComplex := ((999990608563422162748707058389 : Int)/10^30,(-4333911046225280688694908997 : Int)/10^30)
theorem v4562_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 97 5) 1) 14) v4562_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4562 : Material (77 : Basis) (97 : Basis) where
  plus := ![v4562_pa,v4562_pb,v4562_pg]
  minus := ![(Primitive.Addresses.material4562 1).one,v4562_mb,v4562_mg]
  upper := v4562_upper
  lower := (Primitive.Addresses.material4562 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4562_pa_checked.trans (by decide +kernel)
    · exact v4562_pb_checked.trans (by decide +kernel)
    · exact v4562_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 97 Primitive.Addresses.material4562
    · exact v4562_mb_checked.trans (by decide +kernel)
    · exact v4562_mg_checked.trans (by decide +kernel)
  upper_error := v4562_upper_checked
  lower_error := reuse_lower_error 77 97 Primitive.Addresses.material4562

def v4563_pa : Scalar.QComplex := ((999997763555604212160749970507 : Int)/10^30,(-2114919334133607812866057728 : Int)/10^30)
theorem v4563_pa_checked : Scalar.distance (sourceCoefficient 78 79 1 0) v4563_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4563_pb : Scalar.QComplex := ((-912540151403589552878652 : Int)/10^30,(-431476556022932161620336475 : Int)/10^30)
theorem v4563_pb_checked : Scalar.distance (sourceCoefficient 78 79 1 1) v4563_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4563_pg : Scalar.QComplex := ((-93086221714110305158065 : Int)/10^30,(196870290334077066250 : Int)/10^30)
theorem v4563_pg_checked : Scalar.distance (sourceCoefficient 78 79 1 2) v4563_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4563_mb : Scalar.QComplex := ((-1284884646488279449510553 : Int)/10^30,(-431475607883439522956056154 : Int)/10^30)
theorem v4563_mb_checked : Scalar.distance (sourceCoefficient 78 79 3 1) v4563_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4563_mg : Scalar.QComplex := ((-93086017163661860918664 : Int)/10^30,(277199433921752725596 : Int)/10^30)
theorem v4563_mg_checked : Scalar.distance (sourceCoefficient 78 79 3 2) v4563_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4563_upper : Scalar.QComplex := ((999992624017496653698013003862 : Int)/10^30,(-3840821605018217232223174549 : Int)/10^30)
theorem v4563_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 79 5) 1) 14) v4563_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4563 : Material (78 : Basis) (79 : Basis) where
  plus := ![v4563_pa,v4563_pb,v4563_pg]
  minus := ![(Primitive.Addresses.material4563 1).one,v4563_mb,v4563_mg]
  upper := v4563_upper
  lower := (Primitive.Addresses.material4563 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4563_pa_checked.trans (by decide +kernel)
    · exact v4563_pb_checked.trans (by decide +kernel)
    · exact v4563_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 79 Primitive.Addresses.material4563
    · exact v4563_mb_checked.trans (by decide +kernel)
    · exact v4563_mg_checked.trans (by decide +kernel)
  upper_error := v4563_upper_checked
  lower_error := reuse_lower_error 78 79 Primitive.Addresses.material4563

def v4564_pa : Scalar.QComplex := ((999997745092579778157573455731 : Int)/10^30,(-2123631266448158857857723801 : Int)/10^30)
theorem v4564_pa_checked : Scalar.distance (sourceCoefficient 78 80 1 0) v4564_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4564_pb : Scalar.QComplex := ((-916299154335346978508134 : Int)/10^30,(-431476548044106018436816443 : Int)/10^30)
theorem v4564_pb_checked : Scalar.distance (sourceCoefficient 78 80 1 1) v4564_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4564_pg : Scalar.QComplex := ((-93086219994110719092156 : Int)/10^30,(197681253007889519206 : Int)/10^30)
theorem v4564_pg_checked : Scalar.distance (sourceCoefficient 78 80 1 2) v4564_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4564_mb : Scalar.QComplex := ((-1288643641135020680148223 : Int)/10^30,(-431475596660766119754865643 : Int)/10^30)
theorem v4564_mb_checked : Scalar.distance (sourceCoefficient 78 80 3 1) v4564_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4564_mg : Scalar.QComplex := ((-93086014743838652190041 : Int)/10^30,(278010394809324535397 : Int)/10^30)
theorem v4564_mg_checked : Scalar.distance (sourceCoefficient 78 80 3 2) v4564_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4564_upper : Scalar.QComplex := ((999992590518494883611584333983 : Int)/10^30,(-3849533492491863249552090560 : Int)/10^30)
theorem v4564_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 80 5) 1) 14) v4564_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4564 : Material (78 : Basis) (80 : Basis) where
  plus := ![v4564_pa,v4564_pb,v4564_pg]
  minus := ![(Primitive.Addresses.material4564 1).one,v4564_mb,v4564_mg]
  upper := v4564_upper
  lower := (Primitive.Addresses.material4564 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4564_pa_checked.trans (by decide +kernel)
    · exact v4564_pb_checked.trans (by decide +kernel)
    · exact v4564_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 80 Primitive.Addresses.material4564
    · exact v4564_mb_checked.trans (by decide +kernel)
    · exact v4564_mg_checked.trans (by decide +kernel)
  upper_error := v4564_upper_checked
  lower_error := reuse_lower_error 78 80 Primitive.Addresses.material4564

def v4565_pa : Scalar.QComplex := ((999997689041126502544991919914 : Int)/10^30,(-2149863345997599685467149585 : Int)/10^30)
theorem v4565_pa_checked : Scalar.distance (sourceCoefficient 78 81 1 0) v4565_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4565_pb : Scalar.QComplex := ((-927617706767360043708673 : Int)/10^30,(-431476523755768547201564248 : Int)/10^30)
theorem v4565_pb_checked : Scalar.distance (sourceCoefficient 78 81 1 1) v4565_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4565_pg : Scalar.QComplex := ((-93086214765327848942968 : Int)/10^30,(200123103617900995560 : Int)/10^30)
theorem v4565_pg_checked : Scalar.distance (sourceCoefficient 78 81 1 2) v4565_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4565_mb : Scalar.QComplex := ((-1299962168392878059945815 : Int)/10^30,(-431475562605036712028445612 : Int)/10^30)
theorem v4565_mb_checked : Scalar.distance (sourceCoefficient 78 81 3 1) v4565_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4565_mg : Scalar.QComplex := ((-93086007407850629384720 : Int)/10^30,(280452239997919310258 : Int)/10^30)
theorem v4565_mg_checked : Scalar.distance (sourceCoefficient 78 81 3 2) v4565_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4565_upper : Scalar.QComplex := ((999992489192935543386616317597 : Int)/10^30,(-3875765436231979619204803657 : Int)/10^30)
theorem v4565_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 81 5) 1) 14) v4565_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4565 : Material (78 : Basis) (81 : Basis) where
  plus := ![v4565_pa,v4565_pb,v4565_pg]
  minus := ![(Primitive.Addresses.material4565 1).one,v4565_mb,v4565_mg]
  upper := v4565_upper
  lower := (Primitive.Addresses.material4565 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4565_pa_checked.trans (by decide +kernel)
    · exact v4565_pb_checked.trans (by decide +kernel)
    · exact v4565_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 81 Primitive.Addresses.material4565
    · exact v4565_mb_checked.trans (by decide +kernel)
    · exact v4565_mg_checked.trans (by decide +kernel)
  upper_error := v4565_upper_checked
  lower_error := reuse_lower_error 78 81 Primitive.Addresses.material4565

def v4566_pa : Scalar.QComplex := ((999997667621523975794023825194 : Int)/10^30,(-2159803581823832546852634275 : Int)/10^30)
theorem v4566_pa_checked : Scalar.distance (sourceCoefficient 78 82 1 0) v4566_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4566_pb : Scalar.QComplex := ((-931906694938183194921552 : Int)/10^30,(-431476514448654329942919974 : Int)/10^30)
theorem v4566_pb_checked : Scalar.distance (sourceCoefficient 78 82 1 1) v4566_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4566_pg : Scalar.QComplex := ((-93086212764437995233677 : Int)/10^30,(201048404668020229992 : Int)/10^30)
theorem v4566_pg_checked : Scalar.distance (sourceCoefficient 78 82 1 2) v4566_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4566_mb : Scalar.QComplex := ((-1304251146935094506087978 : Int)/10^30,(-431475549596722337669849918 : Int)/10^30)
theorem v4566_mb_checked : Scalar.distance (sourceCoefficient 78 82 3 1) v4566_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4566_mg : Scalar.QComplex := ((-93086004608468388457553 : Int)/10^30,(281377538976828848366 : Int)/10^30)
theorem v4566_mg_checked : Scalar.distance (sourceCoefficient 78 82 3 2) v4566_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4566_upper : Scalar.QComplex := ((999992450617419653689476005492 : Int)/10^30,(-3885705620285108089530216943 : Int)/10^30)
theorem v4566_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 82 5) 1) 14) v4566_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4566 : Material (78 : Basis) (82 : Basis) where
  plus := ![v4566_pa,v4566_pb,v4566_pg]
  minus := ![(Primitive.Addresses.material4566 1).one,v4566_mb,v4566_mg]
  upper := v4566_upper
  lower := (Primitive.Addresses.material4566 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4566_pa_checked.trans (by decide +kernel)
    · exact v4566_pb_checked.trans (by decide +kernel)
    · exact v4566_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 82 Primitive.Addresses.material4566
    · exact v4566_mb_checked.trans (by decide +kernel)
    · exact v4566_mg_checked.trans (by decide +kernel)
  upper_error := v4566_upper_checked
  lower_error := reuse_lower_error 78 82 Primitive.Addresses.material4566

def v4567_pa : Scalar.QComplex := ((999997638223914611198838953762 : Int)/10^30,(-2173372170796185751060015423 : Int)/10^30)
theorem v4567_pa_checked : Scalar.distance (sourceCoefficient 78 83 1 0) v4567_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4567_pb : Scalar.QComplex := ((-937761235826165632639703 : Int)/10^30,(-431476501652530873817561334 : Int)/10^30)
theorem v4567_pb_checked : Scalar.distance (sourceCoefficient 78 83 1 1) v4567_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4567_pg : Scalar.QComplex := ((-93086210015868772655598 : Int)/10^30,(202311456147737292808 : Int)/10^30)
theorem v4567_pg_checked : Scalar.distance (sourceCoefficient 78 83 1 2) v4567_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4567_mb : Scalar.QComplex := ((-1310105674600685578844095 : Int)/10^30,(-431475531748398538530602022 : Int)/10^30)
theorem v4567_mb_checked : Scalar.distance (sourceCoefficient 78 83 3 1) v4567_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4567_mg : Scalar.QComplex := ((-93086000769943648028535 : Int)/10^30,(282640587614362672856 : Int)/10^30)
theorem v4567_mg_checked : Scalar.distance (sourceCoefficient 78 83 3 2) v4567_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4567_upper : Scalar.QComplex := ((999992397801700439874576180972 : Int)/10^30,(-3899274138311035064839396530 : Int)/10^30)
theorem v4567_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 83 5) 1) 14) v4567_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4567 : Material (78 : Basis) (83 : Basis) where
  plus := ![v4567_pa,v4567_pb,v4567_pg]
  minus := ![(Primitive.Addresses.material4567 1).one,v4567_mb,v4567_mg]
  upper := v4567_upper
  lower := (Primitive.Addresses.material4567 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4567_pa_checked.trans (by decide +kernel)
    · exact v4567_pb_checked.trans (by decide +kernel)
    · exact v4567_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 83 Primitive.Addresses.material4567
    · exact v4567_mb_checked.trans (by decide +kernel)
    · exact v4567_mg_checked.trans (by decide +kernel)
  upper_error := v4567_upper_checked
  lower_error := reuse_lower_error 78 83 Primitive.Addresses.material4567

def v4568_pa : Scalar.QComplex := ((999997561236290417964881568821 : Int)/10^30,(-2208511143643074095895535990 : Int)/10^30)
theorem v4568_pa_checked : Scalar.distance (sourceCoefficient 78 84 1 0) v4568_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4568_pb : Scalar.QComplex := ((-952922911799507931068069 : Int)/10^30,(-431476468021706180548070971 : Int)/10^30)
theorem v4568_pb_checked : Scalar.distance (sourceCoefficient 78 84 1 1) v4568_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4568_pg : Scalar.QComplex := ((-93086202804880846048877 : Int)/10^30,(205582417580937853526 : Int)/10^30)
theorem v4568_pg_checked : Scalar.distance (sourceCoefficient 78 84 1 2) v4568_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4568_mb : Scalar.QComplex := ((-1325267315906755955399253 : Int)/10^30,(-431475485033742859096759189 : Int)/10^30)
theorem v4568_mb_checked : Scalar.distance (sourceCoefficient 78 84 3 1) v4568_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4568_mg : Scalar.QComplex := ((-93085990736266008184320 : Int)/10^30,(285911541606876991850 : Int)/10^30)
theorem v4568_mg_checked : Scalar.distance (sourceCoefficient 78 84 3 2) v4568_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4568_upper : Scalar.QComplex := ((999992260167511559649047515565 : Int)/10^30,(-3934412925948895973128329745 : Int)/10^30)
theorem v4568_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 84 5) 1) 14) v4568_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4568 : Material (78 : Basis) (84 : Basis) where
  plus := ![v4568_pa,v4568_pb,v4568_pg]
  minus := ![(Primitive.Addresses.material4568 1).one,v4568_mb,v4568_mg]
  upper := v4568_upper
  lower := (Primitive.Addresses.material4568 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4568_pa_checked.trans (by decide +kernel)
    · exact v4568_pb_checked.trans (by decide +kernel)
    · exact v4568_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 84 Primitive.Addresses.material4568
    · exact v4568_mb_checked.trans (by decide +kernel)
    · exact v4568_mg_checked.trans (by decide +kernel)
  upper_error := v4568_upper_checked
  lower_error := reuse_lower_error 78 84 Primitive.Addresses.material4568

def v4569_pa : Scalar.QComplex := ((999997383513445720425200512804 : Int)/10^30,(-2287567761303970832206458554 : Int)/10^30)
theorem v4569_pa_checked : Scalar.distance (sourceCoefficient 78 85 1 0) v4569_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4569_pb : Scalar.QComplex := ((-987034061543012572258543 : Int)/10^30,(-431476389761249870899295356 : Int)/10^30)
theorem v4569_pb_checked : Scalar.distance (sourceCoefficient 78 85 1 1) v4569_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4569_pg : Scalar.QComplex := ((-93086186091180972369835 : Int)/10^30,(212941515483539794861 : Int)/10^30)
theorem v4569_pg_checked : Scalar.distance (sourceCoefficient 78 85 1 2) v4569_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4569_mb : Scalar.QComplex := ((-1359378385413871515407188 : Int)/10^30,(-431475377336929769902012766 : Int)/10^30)
theorem v4569_mb_checked : Scalar.distance (sourceCoefficient 78 85 3 1) v4569_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4569_mg : Scalar.QComplex := ((-93085967672002309299967 : Int)/10^30,(293270622346180222771 : Int)/10^30)
theorem v4569_mg_checked : Scalar.distance (sourceCoefficient 78 85 3 2) v4569_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4569_upper : Scalar.QComplex := ((999991946000381437031901696374 : Int)/10^30,(-4013469119130740288767441453 : Int)/10^30)
theorem v4569_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 85 5) 1) 14) v4569_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4569 : Material (78 : Basis) (85 : Basis) where
  plus := ![v4569_pa,v4569_pb,v4569_pg]
  minus := ![(Primitive.Addresses.material4569 1).one,v4569_mb,v4569_mg]
  upper := v4569_upper
  lower := (Primitive.Addresses.material4569 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4569_pa_checked.trans (by decide +kernel)
    · exact v4569_pb_checked.trans (by decide +kernel)
    · exact v4569_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 85 Primitive.Addresses.material4569
    · exact v4569_mb_checked.trans (by decide +kernel)
    · exact v4569_mg_checked.trans (by decide +kernel)
  upper_error := v4569_upper_checked
  lower_error := reuse_lower_error 78 85 Primitive.Addresses.material4569

def v4570_pa : Scalar.QComplex := ((999997350043728423489047934486 : Int)/10^30,(-2302152367000234117312001883 : Int)/10^30)
theorem v4570_pa_checked : Scalar.distance (sourceCoefficient 78 86 1 0) v4570_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4570_pb : Scalar.QComplex := ((-993326990124405514511337 : Int)/10^30,(-431476374930668214991737766 : Int)/10^30)
theorem v4570_pb_checked : Scalar.distance (sourceCoefficient 78 86 1 1) v4570_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4570_pg : Scalar.QComplex := ((-93086182933626999865502 : Int)/10^30,(214299144259027517412 : Int)/10^30)
theorem v4570_pg_checked : Scalar.distance (sourceCoefficient 78 86 1 2) v4570_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4570_mb : Scalar.QComplex := ((-1365671298853995521317731 : Int)/10^30,(-431475357075839693337837861 : Int)/10^30)
theorem v4570_mb_checked : Scalar.distance (sourceCoefficient 78 86 3 1) v4570_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4570_mg : Scalar.QComplex := ((-93085963342877024581607 : Int)/10^30,(294628247891333838188 : Int)/10^30)
theorem v4570_mg_checked : Scalar.distance (sourceCoefficient 78 86 3 2) v4570_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4570_upper : Scalar.QComplex := ((999991887359007662650838850821 : Int)/10^30,(-4028053645339250911944338771 : Int)/10^30)
theorem v4570_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 86 5) 1) 14) v4570_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4570 : Material (78 : Basis) (86 : Basis) where
  plus := ![v4570_pa,v4570_pb,v4570_pg]
  minus := ![(Primitive.Addresses.material4570 1).one,v4570_mb,v4570_mg]
  upper := v4570_upper
  lower := (Primitive.Addresses.material4570 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4570_pa_checked.trans (by decide +kernel)
    · exact v4570_pb_checked.trans (by decide +kernel)
    · exact v4570_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 86 Primitive.Addresses.material4570
    · exact v4570_mb_checked.trans (by decide +kernel)
    · exact v4570_mg_checked.trans (by decide +kernel)
  upper_error := v4570_upper_checked
  lower_error := reuse_lower_error 78 86 Primitive.Addresses.material4570

def v4571_pa : Scalar.QComplex := ((999997347819943606725315201166 : Int)/10^30,(-2303118120880363756286399447 : Int)/10^30)
theorem v4571_pa_checked : Scalar.distance (sourceCoefficient 78 87 1 0) v4571_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4571_pb : Scalar.QComplex := ((-993743691150083237310806 : Int)/10^30,(-431476373944306530447365860 : Int)/10^30)
theorem v4571_pb_checked : Scalar.distance (sourceCoefficient 78 87 1 1) v4571_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4571_pg : Scalar.QComplex := ((-93086182723726676596611 : Int)/10^30,(214389042832939275043 : Int)/10^30)
theorem v4571_pg_checked : Scalar.distance (sourceCoefficient 78 87 1 2) v4571_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4571_mb : Scalar.QComplex := ((-1366087998873330698399088 : Int)/10^30,(-431475355729884158418638818 : Int)/10^30)
theorem v4571_mb_checked : Scalar.distance (sourceCoefficient 78 87 3 1) v4571_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4571_mg : Scalar.QComplex := ((-93085963055398359063821 : Int)/10^30,(294718146250637722763 : Int)/10^30)
theorem v4571_mg_checked : Scalar.distance (sourceCoefficient 78 87 3 2) v4571_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4571_upper : Scalar.QComplex := ((999991883468422573357223712364 : Int)/10^30,(-4029019393942952738333971493 : Int)/10^30)
theorem v4571_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 87 5) 1) 14) v4571_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4571 : Material (78 : Basis) (87 : Basis) where
  plus := ![v4571_pa,v4571_pb,v4571_pg]
  minus := ![(Primitive.Addresses.material4571 1).one,v4571_mb,v4571_mg]
  upper := v4571_upper
  lower := (Primitive.Addresses.material4571 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4571_pa_checked.trans (by decide +kernel)
    · exact v4571_pb_checked.trans (by decide +kernel)
    · exact v4571_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 87 Primitive.Addresses.material4571
    · exact v4571_mb_checked.trans (by decide +kernel)
    · exact v4571_mg_checked.trans (by decide +kernel)
  upper_error := v4571_upper_checked
  lower_error := reuse_lower_error 78 87 Primitive.Addresses.material4571

def v4572_pa : Scalar.QComplex := ((999997320667066758709517085813 : Int)/10^30,(-2314877683087729327649989920 : Int)/10^30)
theorem v4572_pa_checked : Scalar.distance (sourceCoefficient 78 88 1 0) v4572_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4572_pb : Scalar.QComplex := ((-998817677085916564705979 : Int)/10^30,(-431476361890766439135227644 : Int)/10^30)
theorem v4572_pb_checked : Scalar.distance (sourceCoefficient 78 88 1 1) v4572_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4572_pg : Scalar.QComplex := ((-93086180159736533294026 : Int)/10^30,(215483698408227585879 : Int)/10^30)
theorem v4572_pg_checked : Scalar.distance (sourceCoefficient 78 88 1 2) v4572_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4572_mb : Scalar.QComplex := ((-1371161972518224941761526 : Int)/10^30,(-431475339297727216409535162 : Int)/10^30)
theorem v4572_mb_checked : Scalar.distance (sourceCoefficient 78 88 3 1) v4572_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4572_mg : Scalar.QComplex := ((-93085959546770710435088 : Int)/10^30,(295812799205727718847 : Int)/10^30)
theorem v4572_mg_checked : Scalar.distance (sourceCoefficient 78 88 3 2) v4572_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4572_upper : Scalar.QComplex := ((999991836019648615598831907574 : Int)/10^30,(-4040778891772429627109957735 : Int)/10^30)
theorem v4572_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 88 5) 1) 14) v4572_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4572 : Material (78 : Basis) (88 : Basis) where
  plus := ![v4572_pa,v4572_pb,v4572_pg]
  minus := ![(Primitive.Addresses.material4572 1).one,v4572_mb,v4572_mg]
  upper := v4572_upper
  lower := (Primitive.Addresses.material4572 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4572_pa_checked.trans (by decide +kernel)
    · exact v4572_pb_checked.trans (by decide +kernel)
    · exact v4572_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 88 Primitive.Addresses.material4572
    · exact v4572_mb_checked.trans (by decide +kernel)
    · exact v4572_mg_checked.trans (by decide +kernel)
  upper_error := v4572_upper_checked
  lower_error := reuse_lower_error 78 88 Primitive.Addresses.material4572

def v4573_pa : Scalar.QComplex := ((999997283292442686097092695271 : Int)/10^30,(-2330967124205713427319468902 : Int)/10^30)
theorem v4573_pa_checked : Scalar.distance (sourceCoefficient 78 89 1 0) v4573_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4573_pb : Scalar.QComplex := ((-1005759908052845798593997 : Int)/10^30,(-431476345270214231601014602 : Int)/10^30)
theorem v4573_pb_checked : Scalar.distance (sourceCoefficient 78 89 1 1) v4573_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4573_pg : Scalar.QComplex := ((-93086176627352622391445 : Int)/10^30,(216981406911393191165 : Int)/10^30)
theorem v4573_pg_checked : Scalar.distance (sourceCoefficient 78 89 1 2) v4573_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4573_mb : Scalar.QComplex := ((-1378104186557456317814345 : Int)/10^30,(-431475316686348539482602225 : Int)/10^30)
theorem v4573_mb_checked : Scalar.distance (sourceCoefficient 78 89 3 1) v4573_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4573_mg : Scalar.QComplex := ((-93085954721933130855520 : Int)/10^30,(297310504102939777301 : Int)/10^30)
theorem v4573_mg_checked : Scalar.distance (sourceCoefficient 78 89 3 2) v4573_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4573_upper : Scalar.QComplex := ((999991770876164461154352630867 : Int)/10^30,(-4056868244421870630141907228 : Int)/10^30)
theorem v4573_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 89 5) 1) 14) v4573_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4573 : Material (78 : Basis) (89 : Basis) where
  plus := ![v4573_pa,v4573_pb,v4573_pg]
  minus := ![(Primitive.Addresses.material4573 1).one,v4573_mb,v4573_mg]
  upper := v4573_upper
  lower := (Primitive.Addresses.material4573 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4573_pa_checked.trans (by decide +kernel)
    · exact v4573_pb_checked.trans (by decide +kernel)
    · exact v4573_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 89 Primitive.Addresses.material4573
    · exact v4573_mb_checked.trans (by decide +kernel)
    · exact v4573_mg_checked.trans (by decide +kernel)
  upper_error := v4573_upper_checked
  lower_error := reuse_lower_error 78 89 Primitive.Addresses.material4573

def v4574_pa : Scalar.QComplex := ((999997221870950932361647576246 : Int)/10^30,(-2357169993898247346215075524 : Int)/10^30)
theorem v4574_pa_checked : Scalar.distance (sourceCoefficient 78 90 1 0) v4574_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4574_pb : Scalar.QComplex := ((-1017065855133163240281197 : Int)/10^30,(-431476317883618087670253345 : Int)/10^30)
theorem v4574_pb_checked : Scalar.distance (sourceCoefficient 78 90 1 1) v4574_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4574_pg : Scalar.QComplex := ((-93086170814423639248869 : Int)/10^30,(219420538269217507701 : Int)/10^30)
theorem v4574_pg_checked : Scalar.distance (sourceCoefficient 78 90 1 2) v4574_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4574_mb : Scalar.QComplex := ((-1389410105794653928482321 : Int)/10^30,(-431475279543239463473332019 : Int)/10^30)
theorem v4574_mb_checked : Scalar.distance (sourceCoefficient 78 90 3 1) v4574_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4574_mg : Scalar.QComplex := ((-93085946804145804728052 : Int)/10^30,(299749629536268107660 : Int)/10^30)
theorem v4574_mg_checked : Scalar.distance (sourceCoefficient 78 90 3 2) v4574_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4574_upper : Scalar.QComplex := ((999991664230988203971830872455 : Int)/10^30,(-4083070969080385494557958733 : Int)/10^30)
theorem v4574_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 90 5) 1) 14) v4574_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4574 : Material (78 : Basis) (90 : Basis) where
  plus := ![v4574_pa,v4574_pb,v4574_pg]
  minus := ![(Primitive.Addresses.material4574 1).one,v4574_mb,v4574_mg]
  upper := v4574_upper
  lower := (Primitive.Addresses.material4574 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4574_pa_checked.trans (by decide +kernel)
    · exact v4574_pb_checked.trans (by decide +kernel)
    · exact v4574_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 90 Primitive.Addresses.material4574
    · exact v4574_mb_checked.trans (by decide +kernel)
    · exact v4574_mg_checked.trans (by decide +kernel)
  upper_error := v4574_upper_checked
  lower_error := reuse_lower_error 78 90 Primitive.Addresses.material4574

def v4575_pa : Scalar.QComplex := ((999997186967653017517327471483 : Int)/10^30,(-2371931023620623790773925107 : Int)/10^30)
theorem v4575_pa_checked : Scalar.distance (sourceCoefficient 78 91 1 0) v4575_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4575_pb : Scalar.QComplex := ((-1023434906294848005875275 : Int)/10^30,(-431476302281816864254783947 : Int)/10^30)
theorem v4575_pb_checked : Scalar.distance (sourceCoefficient 78 91 1 1) v4575_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4575_pg : Scalar.QComplex := ((-93086167506955235317926 : Int)/10^30,(220794589682015995305 : Int)/10^30)
theorem v4575_pg_checked : Scalar.distance (sourceCoefficient 78 91 1 2) v4575_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4575_mb : Scalar.QComplex := ((-1395779141121198089798308 : Int)/10^30,(-431475258445239748203440122 : Int)/10^30)
theorem v4575_mb_checked : Scalar.distance (sourceCoefficient 78 91 3 1) v4575_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4575_mg : Scalar.QComplex := ((-93085942310934148052014 : Int)/10^30,(301123677583248187282 : Int)/10^30)
theorem v4575_mg_checked : Scalar.distance (sourceCoefficient 78 91 3 2) v4575_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4575_upper : Scalar.QComplex := ((999991603851544082823841747177 : Int)/10^30,(-4097831916578016321422753670 : Int)/10^30)
theorem v4575_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 91 5) 1) 14) v4575_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4575 : Material (78 : Basis) (91 : Basis) where
  plus := ![v4575_pa,v4575_pb,v4575_pg]
  minus := ![(Primitive.Addresses.material4575 1).one,v4575_mb,v4575_mg]
  upper := v4575_upper
  lower := (Primitive.Addresses.material4575 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4575_pa_checked.trans (by decide +kernel)
    · exact v4575_pb_checked.trans (by decide +kernel)
    · exact v4575_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 91 Primitive.Addresses.material4575
    · exact v4575_mb_checked.trans (by decide +kernel)
    · exact v4575_mg_checked.trans (by decide +kernel)
  upper_error := v4575_upper_checked
  lower_error := reuse_lower_error 78 91 Primitive.Addresses.material4575

def v4576_pa : Scalar.QComplex := ((999997110659382168101605712572 : Int)/10^30,(-2403887037149331386060514485 : Int)/10^30)
theorem v4576_pa_checked : Scalar.distance (sourceCoefficient 78 92 1 0) v4576_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4576_pb : Scalar.QComplex := ((-1037223204557056881108799 : Int)/10^30,(-431476268076189658106844121 : Int)/10^30)
theorem v4576_pb_checked : Scalar.distance (sourceCoefficient 78 92 1 1) v4576_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4576_pg : Scalar.QComplex := ((-93086160265583004225650 : Int)/10^30,(223769260546053664363 : Int)/10^30)
theorem v4576_pg_checked : Scalar.distance (sourceCoefficient 78 92 1 2) v4576_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4576_mb : Scalar.QComplex := ((-1409567404731477651005788 : Int)/10^30,(-431475212340944879988579928 : Int)/10^30)
theorem v4576_mb_checked : Scalar.distance (sourceCoefficient 78 92 3 1) v4576_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4576_mg : Scalar.QComplex := ((-93085932502557631791419 : Int)/10^30,(304098341090701848349 : Int)/10^30)
theorem v4576_mg_checked : Scalar.distance (sourceCoefficient 78 92 3 2) v4576_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4576_upper : Scalar.QComplex := ((999991472390206561965810534958 : Int)/10^30,(-4129787750810842728903014536 : Int)/10^30)
theorem v4576_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 92 5) 1) 14) v4576_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4576 : Material (78 : Basis) (92 : Basis) where
  plus := ![v4576_pa,v4576_pb,v4576_pg]
  minus := ![(Primitive.Addresses.material4576 1).one,v4576_mb,v4576_mg]
  upper := v4576_upper
  lower := (Primitive.Addresses.material4576 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4576_pa_checked.trans (by decide +kernel)
    · exact v4576_pb_checked.trans (by decide +kernel)
    · exact v4576_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 92 Primitive.Addresses.material4576
    · exact v4576_mb_checked.trans (by decide +kernel)
    · exact v4576_mg_checked.trans (by decide +kernel)
  upper_error := v4576_upper_checked
  lower_error := reuse_lower_error 78 92 Primitive.Addresses.material4576

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
