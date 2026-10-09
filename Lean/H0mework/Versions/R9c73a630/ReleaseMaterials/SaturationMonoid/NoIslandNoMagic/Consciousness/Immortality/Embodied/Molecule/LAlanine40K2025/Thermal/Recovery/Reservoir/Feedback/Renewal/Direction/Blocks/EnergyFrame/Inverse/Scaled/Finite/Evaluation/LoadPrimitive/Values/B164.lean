import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B109
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B110

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2625_pa : Scalar.QComplex := ((999999616341792414295056057785 : Int)/10^30,(-875965905716535088483346842 : Int)/10^30)
theorem v2625_pa_checked : Scalar.distance (sourceCoefficient 32 50 1 0) v2625_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2625_pb : Scalar.QComplex := ((-377959592557234233887668 : Int)/10^30,(-431477349841334010036286639 : Int)/10^30)
theorem v2625_pb_checked : Scalar.distance (sourceCoefficient 32 50 1 1) v2625_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2625_pg : Scalar.QComplex := ((-93086393577439145089400 : Int)/10^30,(81540538343644122065 : Int)/10^30)
theorem v2625_pg_checked : Scalar.distance (sourceCoefficient 32 50 1 2) v2625_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2625_mb : Scalar.QComplex := ((-750304971720226269049173 : Int)/10^30,(-431476863020491466301851354 : Int)/10^30)
theorem v2625_mb_checked : Scalar.distance (sourceCoefficient 32 50 3 1) v2625_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2625_mg : Scalar.QComplex := ((-93086288551308416812077 : Int)/10^30,(161869873184169629368 : Int)/10^30)
theorem v2625_mg_checked : Scalar.distance (sourceCoefficient 32 50 3 2) v2625_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2625_upper : Scalar.QComplex := ((999996615122145819287073238725 : Int)/10^30,(-2601873219617615828789046225 : Int)/10^30)
theorem v2625_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 50 5) 1) 14) v2625_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2625 : Material (32 : Basis) (50 : Basis) where
  plus := ![v2625_pa,v2625_pb,v2625_pg]
  minus := ![(Primitive.Addresses.material2625 1).one,v2625_mb,v2625_mg]
  upper := v2625_upper
  lower := (Primitive.Addresses.material2625 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2625_pa_checked.trans (by decide +kernel)
    · exact v2625_pb_checked.trans (by decide +kernel)
    · exact v2625_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 50 Primitive.Addresses.material2625
    · exact v2625_mb_checked.trans (by decide +kernel)
    · exact v2625_mg_checked.trans (by decide +kernel)
  upper_error := v2625_upper_checked
  lower_error := reuse_lower_error 32 50 Primitive.Addresses.material2625

def v2626_pa : Scalar.QComplex := ((999999606380197699952861078915 : Int)/10^30,(-887265151836555291133118228 : Int)/10^30)
theorem v2626_pa_checked : Scalar.distance (sourceCoefficient 32 51 1 0) v2626_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2626_pb : Scalar.QComplex := ((-382834962787563236052432 : Int)/10^30,(-431477345079662904550868691 : Int)/10^30)
theorem v2626_pb_checked : Scalar.distance (sourceCoefficient 32 51 1 1) v2626_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2626_pg : Scalar.QComplex := ((-93086392600155966389623 : Int)/10^30,(82592344774277001953 : Int)/10^30)
theorem v2626_pg_checked : Scalar.distance (sourceCoefficient 32 51 1 2) v2626_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2626_mb : Scalar.QComplex := ((-755180336026124412707249 : Int)/10^30,(-431476854051597203554312288 : Int)/10^30)
theorem v2626_mb_checked : Scalar.distance (sourceCoefficient 32 51 3 1) v2626_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2626_mg : Scalar.QComplex := ((-93086286666364023966435 : Int)/10^30,(162921678379815537185 : Int)/10^30)
theorem v2626_mg_checked : Scalar.distance (sourceCoefficient 32 51 3 2) v2626_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2626_upper : Scalar.QComplex := ((999996585659092198015846445299 : Int)/10^30,(-2613172431715927470214382526 : Int)/10^30)
theorem v2626_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 51 5) 1) 14) v2626_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2626 : Material (32 : Basis) (51 : Basis) where
  plus := ![v2626_pa,v2626_pb,v2626_pg]
  minus := ![(Primitive.Addresses.material2626 1).one,v2626_mb,v2626_mg]
  upper := v2626_upper
  lower := (Primitive.Addresses.material2626 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2626_pa_checked.trans (by decide +kernel)
    · exact v2626_pb_checked.trans (by decide +kernel)
    · exact v2626_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 51 Primitive.Addresses.material2626
    · exact v2626_mb_checked.trans (by decide +kernel)
    · exact v2626_mg_checked.trans (by decide +kernel)
  upper_error := v2626_upper_checked
  lower_error := reuse_lower_error 32 51 Primitive.Addresses.material2626

def v2627_pa : Scalar.QComplex := ((999999584625649075605122795472 : Int)/10^30,(-911454074165527195020971593 : Int)/10^30)
theorem v2627_pa_checked : Scalar.distance (sourceCoefficient 32 52 1 0) v2627_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2627_pb : Scalar.QComplex := ((-393271937922023945163677 : Int)/10^30,(-431477334639163356360311777 : Int)/10^30)
theorem v2627_pb_checked : Scalar.distance (sourceCoefficient 32 52 1 1) v2627_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2627_pg : Scalar.QComplex := ((-93086390461419066186336 : Int)/10^30,(84844005077447015675 : Int)/10^30)
theorem v2627_pg_checked : Scalar.distance (sourceCoefficient 32 52 1 2) v2627_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2627_mb : Scalar.QComplex := ((-765617298264741398486894 : Int)/10^30,(-431476834604462065709763132 : Int)/10^30)
theorem v2627_mb_checked : Scalar.distance (sourceCoefficient 32 52 3 1) v2627_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2627_mg : Scalar.QComplex := ((-93086282584546489492420 : Int)/10^30,(165173335998955894336 : Int)/10^30)
theorem v2627_mg_checked : Scalar.distance (sourceCoefficient 32 52 3 2) v2627_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2627_upper : Scalar.QComplex := ((999996522156690436599266685611 : Int)/10^30,(-2637361280471963627125367851 : Int)/10^30)
theorem v2627_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 52 5) 1) 14) v2627_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2627 : Material (32 : Basis) (52 : Basis) where
  plus := ![v2627_pa,v2627_pb,v2627_pg]
  minus := ![(Primitive.Addresses.material2627 1).one,v2627_mb,v2627_mg]
  upper := v2627_upper
  lower := (Primitive.Addresses.material2627 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2627_pa_checked.trans (by decide +kernel)
    · exact v2627_pb_checked.trans (by decide +kernel)
    · exact v2627_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 52 Primitive.Addresses.material2627
    · exact v2627_mb_checked.trans (by decide +kernel)
    · exact v2627_mg_checked.trans (by decide +kernel)
  upper_error := v2627_upper_checked
  lower_error := reuse_lower_error 32 52 Primitive.Addresses.material2627

def v2628_pa : Scalar.QComplex := ((999999581243962347833942897278 : Int)/10^30,(-915156762499033847391324019 : Int)/10^30)
theorem v2628_pa_checked : Scalar.distance (sourceCoefficient 32 53 1 0) v2628_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2628_pb : Scalar.QComplex := ((-394869564524344160815229 : Int)/10^30,(-431477333011290296962018892 : Int)/10^30)
theorem v2628_pb_checked : Scalar.distance (sourceCoefficient 32 53 1 1) v2628_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2628_pg : Scalar.QComplex := ((-93086390128426827819639 : Int)/10^30,(85188675095925155314 : Int)/10^30)
theorem v2628_pg_checked : Scalar.distance (sourceCoefficient 32 53 1 2) v2628_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2628_mb : Scalar.QComplex := ((-767214922867411081372108 : Int)/10^30,(-431476831597909809071756093 : Int)/10^30)
theorem v2628_mb_checked : Scalar.distance (sourceCoefficient 32 53 3 1) v2628_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2628_mg : Scalar.QComplex := ((-93086281954119672528695 : Int)/10^30,(165518005601740329601 : Int)/10^30)
theorem v2628_mg_checked : Scalar.distance (sourceCoefficient 32 53 3 2) v2628_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2628_upper : Scalar.QComplex := ((999996512384504587082412801065 : Int)/10^30,(-2641063957454266447153088729 : Int)/10^30)
theorem v2628_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 53 5) 1) 14) v2628_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2628 : Material (32 : Basis) (53 : Basis) where
  plus := ![v2628_pa,v2628_pb,v2628_pg]
  minus := ![(Primitive.Addresses.material2628 1).one,v2628_mb,v2628_mg]
  upper := v2628_upper
  lower := (Primitive.Addresses.material2628 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2628_pa_checked.trans (by decide +kernel)
    · exact v2628_pb_checked.trans (by decide +kernel)
    · exact v2628_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 53 Primitive.Addresses.material2628
    · exact v2628_mb_checked.trans (by decide +kernel)
    · exact v2628_mg_checked.trans (by decide +kernel)
  upper_error := v2628_upper_checked
  lower_error := reuse_lower_error 32 53 Primitive.Addresses.material2628

def v2629_pa : Scalar.QComplex := ((999999579519435349678618423026 : Int)/10^30,(-917039231710801735043552643 : Int)/10^30)
theorem v2629_pa_checked : Scalar.distance (sourceCoefficient 32 54 1 0) v2629_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2629_pb : Scalar.QComplex := ((-395681807580075336309237 : Int)/10^30,(-431477332180645417593240356 : Int)/10^30)
theorem v2629_pb_checked : Scalar.distance (sourceCoefficient 32 54 1 1) v2629_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2629_pg : Scalar.QComplex := ((-93086389958560644599322 : Int)/10^30,(85363907424194537365 : Int)/10^30)
theorem v2629_pg_checked : Scalar.distance (sourceCoefficient 32 54 1 2) v2629_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2629_mb : Scalar.QComplex := ((-768027164903897925837276 : Int)/10^30,(-431476830066336063963263931 : Int)/10^30)
theorem v2629_mb_checked : Scalar.distance (sourceCoefficient 32 54 3 1) v2629_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2629_mg : Scalar.QComplex := ((-93086281633035945431939 : Int)/10^30,(165693237718175841694 : Int)/10^30)
theorem v2629_mg_checked : Scalar.distance (sourceCoefficient 32 54 3 2) v2629_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2629_upper : Scalar.QComplex := ((999996507411009074168961368607 : Int)/10^30,(-2642946420885940423295302958 : Int)/10^30)
theorem v2629_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 54 5) 1) 14) v2629_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2629 : Material (32 : Basis) (54 : Basis) where
  plus := ![v2629_pa,v2629_pb,v2629_pg]
  minus := ![(Primitive.Addresses.material2629 1).one,v2629_mb,v2629_mg]
  upper := v2629_upper
  lower := (Primitive.Addresses.material2629 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2629_pa_checked.trans (by decide +kernel)
    · exact v2629_pb_checked.trans (by decide +kernel)
    · exact v2629_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 54 Primitive.Addresses.material2629
    · exact v2629_mb_checked.trans (by decide +kernel)
    · exact v2629_mg_checked.trans (by decide +kernel)
  upper_error := v2629_upper_checked
  lower_error := reuse_lower_error 32 54 Primitive.Addresses.material2629

def v2630_pa : Scalar.QComplex := ((999999565331042914924350177210 : Int)/10^30,(-932382821180790013282300812 : Int)/10^30)
theorem v2630_pa_checked : Scalar.distance (sourceCoefficient 32 55 1 0) v2630_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2630_pb : Scalar.QComplex := ((-402302220738942613599724 : Int)/10^30,(-431477325334213875027478686 : Int)/10^30)
theorem v2630_pb_checked : Scalar.distance (sourceCoefficient 32 55 1 1) v2630_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2630_pg : Scalar.QComplex := ((-93086388559666884386761 : Int)/10^30,(86792187304662964759 : Int)/10^30)
theorem v2630_pg_checked : Scalar.distance (sourceCoefficient 32 55 1 2) v2630_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2630_mb : Scalar.QComplex := ((-774647569689520746848828 : Int)/10^30,(-431476817506788686874400469 : Int)/10^30)
theorem v2630_mb_checked : Scalar.distance (sourceCoefficient 32 55 3 1) v2630_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2630_mg : Scalar.QComplex := ((-93086279001601496585078 : Int)/10^30,(167121515859648082747 : Int)/10^30)
theorem v2630_mg_checked : Scalar.distance (sourceCoefficient 32 55 3 2) v2630_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2630_upper : Scalar.QComplex := ((999996466740994305722096737653 : Int)/10^30,(-2658289963015576389137334923 : Int)/10^30)
theorem v2630_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 55 5) 1) 14) v2630_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2630 : Material (32 : Basis) (55 : Basis) where
  plus := ![v2630_pa,v2630_pb,v2630_pg]
  minus := ![(Primitive.Addresses.material2630 1).one,v2630_mb,v2630_mg]
  upper := v2630_upper
  lower := (Primitive.Addresses.material2630 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2630_pa_checked.trans (by decide +kernel)
    · exact v2630_pb_checked.trans (by decide +kernel)
    · exact v2630_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 55 Primitive.Addresses.material2630
    · exact v2630_mb_checked.trans (by decide +kernel)
    · exact v2630_mg_checked.trans (by decide +kernel)
  upper_error := v2630_upper_checked
  lower_error := reuse_lower_error 32 55 Primitive.Addresses.material2630

def v2631_pa : Scalar.QComplex := ((999999561929174380823896021461 : Int)/10^30,(-936024283516354050626621437 : Int)/10^30)
theorem v2631_pa_checked : Scalar.distance (sourceCoefficient 32 56 1 0) v2631_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2631_pb : Scalar.QComplex := ((-403873429685164506246873 : Int)/10^30,(-431477323689478101475702004 : Int)/10^30)
theorem v2631_pb_checked : Scalar.distance (sourceCoefficient 32 56 1 1) v2631_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2631_pg : Scalar.QComplex := ((-93086388223916349256841 : Int)/10^30,(87131158012034805370 : Int)/10^30)
theorem v2631_pg_checked : Scalar.distance (sourceCoefficient 32 56 1 2) v2631_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2631_mb : Scalar.QComplex := ((-776218776631376844595568 : Int)/10^30,(-431476814506170969767458575 : Int)/10^30)
theorem v2631_mb_checked : Scalar.distance (sourceCoefficient 32 56 3 1) v2631_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2631_mg : Scalar.QComplex := ((-93086278373334632682463 : Int)/10^30,(167460486151068047102 : Int)/10^30)
theorem v2631_mg_checked : Scalar.distance (sourceCoefficient 32 56 3 2) v2631_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2631_upper : Scalar.QComplex := ((999996457054297198004207011188 : Int)/10^30,(-2661931414056293559118453283 : Int)/10^30)
theorem v2631_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 56 5) 1) 14) v2631_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2631 : Material (32 : Basis) (56 : Basis) where
  plus := ![v2631_pa,v2631_pb,v2631_pg]
  minus := ![(Primitive.Addresses.material2631 1).one,v2631_mb,v2631_mg]
  upper := v2631_upper
  lower := (Primitive.Addresses.material2631 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2631_pa_checked.trans (by decide +kernel)
    · exact v2631_pb_checked.trans (by decide +kernel)
    · exact v2631_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 56 Primitive.Addresses.material2631
    · exact v2631_mb_checked.trans (by decide +kernel)
    · exact v2631_mg_checked.trans (by decide +kernel)
  upper_error := v2631_upper_checked
  lower_error := reuse_lower_error 32 56 Primitive.Addresses.material2631

def v2632_pa : Scalar.QComplex := ((999999550835455906048810517109 : Int)/10^30,(-947802134645789193497277240 : Int)/10^30)
theorem v2632_pa_checked : Scalar.distance (sourceCoefficient 32 57 1 0) v2632_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2632_pb : Scalar.QComplex := ((-408955307040836746636694 : Int)/10^30,(-431477318317548033109590855 : Int)/10^30)
theorem v2632_pb_checked : Scalar.distance (sourceCoefficient 32 57 1 1) v2632_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2632_pg : Scalar.QComplex := ((-93086387128112231851658 : Int)/10^30,(88227516055161113068 : Int)/10^30)
theorem v2632_pg_checked : Scalar.distance (sourceCoefficient 32 57 1 2) v2632_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2632_mb : Scalar.QComplex := ((-781300647459100185948904 : Int)/10^30,(-431476804748811622930979735 : Int)/10^30)
theorem v2632_mb_checked : Scalar.distance (sourceCoefficient 32 57 3 1) v2632_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2632_mg : Scalar.QComplex := ((-93086276331423310210490 : Int)/10^30,(168556842840340549171 : Int)/10^30)
theorem v2632_mg_checked : Scalar.distance (sourceCoefficient 32 57 3 2) v2632_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2632_upper : Scalar.QComplex := ((999996425633092674922541232057 : Int)/10^30,(-2673709228497251295092915162 : Int)/10^30)
theorem v2632_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 57 5) 1) 14) v2632_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2632 : Material (32 : Basis) (57 : Basis) where
  plus := ![v2632_pa,v2632_pb,v2632_pg]
  minus := ![(Primitive.Addresses.material2632 1).one,v2632_mb,v2632_mg]
  upper := v2632_upper
  lower := (Primitive.Addresses.material2632 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2632_pa_checked.trans (by decide +kernel)
    · exact v2632_pb_checked.trans (by decide +kernel)
    · exact v2632_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 57 Primitive.Addresses.material2632
    · exact v2632_mb_checked.trans (by decide +kernel)
    · exact v2632_mg_checked.trans (by decide +kernel)
  upper_error := v2632_upper_checked
  lower_error := reuse_lower_error 32 57 Primitive.Addresses.material2632

def v2633_pa : Scalar.QComplex := ((999999544758059142167837218556 : Int)/10^30,(-954192682046157598573366798 : Int)/10^30)
theorem v2633_pa_checked : Scalar.distance (sourceCoefficient 32 58 1 0) v2633_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2633_pb : Scalar.QComplex := ((-411712684223278263147953 : Int)/10^30,(-431477315369392934454140176 : Int)/10^30)
theorem v2633_pb_checked : Scalar.distance (sourceCoefficient 32 58 1 1) v2633_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2633_pg : Scalar.QComplex := ((-93086386527234969948212 : Int)/10^30,(88822389258084523561 : Int)/10^30)
theorem v2633_pg_checked : Scalar.distance (sourceCoefficient 32 58 1 2) v2633_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2633_mb : Scalar.QComplex := ((-784058021070719088911480 : Int)/10^30,(-431476799421165301219615476 : Int)/10^30)
theorem v2633_mb_checked : Scalar.distance (sourceCoefficient 32 58 3 1) v2633_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2633_mg : Scalar.QComplex := ((-93086275217197490012697 : Int)/10^30,(169151715303235464653 : Int)/10^30)
theorem v2633_mg_checked : Scalar.distance (sourceCoefficient 32 58 3 2) v2633_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2633_upper : Scalar.QComplex := ((999996408526199895505714134751 : Int)/10^30,(-2680099755890614556419808325 : Int)/10^30)
theorem v2633_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 58 5) 1) 14) v2633_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2633 : Material (32 : Basis) (58 : Basis) where
  plus := ![v2633_pa,v2633_pb,v2633_pg]
  minus := ![(Primitive.Addresses.material2633 1).one,v2633_mb,v2633_mg]
  upper := v2633_upper
  lower := (Primitive.Addresses.material2633 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2633_pa_checked.trans (by decide +kernel)
    · exact v2633_pb_checked.trans (by decide +kernel)
    · exact v2633_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 58 Primitive.Addresses.material2633
    · exact v2633_mb_checked.trans (by decide +kernel)
    · exact v2633_mg_checked.trans (by decide +kernel)
  upper_error := v2633_upper_checked
  lower_error := reuse_lower_error 32 58 Primitive.Addresses.material2633

def v2634_pa : Scalar.QComplex := ((999999527842499298867408880315 : Int)/10^30,(-971758600923891855984485259 : Int)/10^30)
theorem v2634_pa_checked : Scalar.distance (sourceCoefficient 32 59 1 0) v2634_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2634_pb : Scalar.QComplex := ((-419291982293145940529008 : Int)/10^30,(-431477307144648009146122378 : Int)/10^30)
theorem v2634_pb_checked : Scalar.distance (sourceCoefficient 32 59 1 1) v2634_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2634_pg : Scalar.QComplex := ((-93086384852732253567995 : Int)/10^30,(90457537819759030326 : Int)/10^30)
theorem v2634_pg_checked : Scalar.distance (sourceCoefficient 32 59 1 2) v2634_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2634_mb : Scalar.QComplex := ((-791637309220883262066596 : Int)/10^30,(-431476784655830562977445539 : Int)/10^30)
theorem v2634_mb_checked : Scalar.distance (sourceCoefficient 32 59 3 1) v2634_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2634_mg : Scalar.QComplex := ((-93086272131635832758681 : Int)/10^30,(170786861811049004492 : Int)/10^30)
theorem v2634_mg_checked : Scalar.distance (sourceCoefficient 32 59 3 2) v2634_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2634_upper : Scalar.QComplex := ((999996361293482830687623083778 : Int)/10^30,(-2697665619411254361290788018 : Int)/10^30)
theorem v2634_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 59 5) 1) 14) v2634_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2634 : Material (32 : Basis) (59 : Basis) where
  plus := ![v2634_pa,v2634_pb,v2634_pg]
  minus := ![(Primitive.Addresses.material2634 1).one,v2634_mb,v2634_mg]
  upper := v2634_upper
  lower := (Primitive.Addresses.material2634 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2634_pa_checked.trans (by decide +kernel)
    · exact v2634_pb_checked.trans (by decide +kernel)
    · exact v2634_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 59 Primitive.Addresses.material2634
    · exact v2634_mb_checked.trans (by decide +kernel)
    · exact v2634_mg_checked.trans (by decide +kernel)
  upper_error := v2634_upper_checked
  lower_error := reuse_lower_error 32 59 Primitive.Addresses.material2634

def v2635_pa : Scalar.QComplex := ((999999507945537503152151663681 : Int)/10^30,(-992022521355287393966614919 : Int)/10^30)
theorem v2635_pa_checked : Scalar.distance (sourceCoefficient 32 60 1 0) v2635_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2635_pb : Scalar.QComplex := ((-428035407126888757101836 : Int)/10^30,(-431477297436131622962732202 : Int)/10^30)
theorem v2635_pb_checked : Scalar.distance (sourceCoefficient 32 60 1 1) v2635_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2635_pg : Scalar.QComplex := ((-93086382879411989946995 : Int)/10^30,(92343833686073388951 : Int)/10^30)
theorem v2635_pg_checked : Scalar.distance (sourceCoefficient 32 60 1 2) v2635_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2635_mb : Scalar.QComplex := ((-800380722421037032851802 : Int)/10^30,(-431476767402135949434724545 : Int)/10^30)
theorem v2635_mb_checked : Scalar.distance (sourceCoefficient 32 60 3 1) v2635_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2635_mg : Scalar.QComplex := ((-93086268530527926877828 : Int)/10^30,(172673155272122691648 : Int)/10^30)
theorem v2635_mg_checked : Scalar.distance (sourceCoefficient 32 60 3 2) v2635_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2635_upper : Scalar.QComplex := ((999996306422862333072302729270 : Int)/10^30,(-2717929475321569762884206947 : Int)/10^30)
theorem v2635_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 60 5) 1) 14) v2635_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2635 : Material (32 : Basis) (60 : Basis) where
  plus := ![v2635_pa,v2635_pb,v2635_pg]
  minus := ![(Primitive.Addresses.material2635 1).one,v2635_mb,v2635_mg]
  upper := v2635_upper
  lower := (Primitive.Addresses.material2635 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2635_pa_checked.trans (by decide +kernel)
    · exact v2635_pb_checked.trans (by decide +kernel)
    · exact v2635_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 60 Primitive.Addresses.material2635
    · exact v2635_mb_checked.trans (by decide +kernel)
    · exact v2635_mg_checked.trans (by decide +kernel)
  upper_error := v2635_upper_checked
  lower_error := reuse_lower_error 32 60 Primitive.Addresses.material2635

def v2636_pa : Scalar.QComplex := ((999999502115778743163818759722 : Int)/10^30,(-997881854041336191064078871 : Int)/10^30)
theorem v2636_pa_checked : Scalar.distance (sourceCoefficient 32 61 1 0) v2636_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2636_pb : Scalar.QComplex := ((-430563577067906202180465 : Int)/10^30,(-431477294584875079088715571 : Int)/10^30)
theorem v2636_pb_checked : Scalar.distance (sourceCoefficient 32 61 1 1) v2636_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2636_pg : Scalar.QComplex := ((-93086382300512984391558 : Int)/10^30,(92889258004132403013 : Int)/10^30)
theorem v2636_pg_checked : Scalar.distance (sourceCoefficient 32 61 1 2) v2636_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2636_mb : Scalar.QComplex := ((-802908888960195284279827 : Int)/10^30,(-431476762369183672663065703 : Int)/10^30)
theorem v2636_mb_checked : Scalar.distance (sourceCoefficient 32 61 3 1) v2636_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2636_mg : Scalar.QComplex := ((-93086267480952515387408 : Int)/10^30,(173218578887531535823 : Int)/10^30)
theorem v2636_mg_checked : Scalar.distance (sourceCoefficient 32 61 3 2) v2636_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2636_upper : Scalar.QComplex := ((999996290480435594213609861143 : Int)/10^30,(-2723788789219196061522240386 : Int)/10^30)
theorem v2636_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 61 5) 1) 14) v2636_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2636 : Material (32 : Basis) (61 : Basis) where
  plus := ![v2636_pa,v2636_pb,v2636_pg]
  minus := ![(Primitive.Addresses.material2636 1).one,v2636_mb,v2636_mg]
  upper := v2636_upper
  lower := (Primitive.Addresses.material2636 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2636_pa_checked.trans (by decide +kernel)
    · exact v2636_pb_checked.trans (by decide +kernel)
    · exact v2636_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 61 Primitive.Addresses.material2636
    · exact v2636_mb_checked.trans (by decide +kernel)
    · exact v2636_mg_checked.trans (by decide +kernel)
  upper_error := v2636_upper_checked
  lower_error := reuse_lower_error 32 61 Primitive.Addresses.material2636

def v2637_pa : Scalar.QComplex := ((999999493584209387489217018227 : Int)/10^30,(-1006395213009317023286106469 : Int)/10^30)
theorem v2637_pa_checked : Scalar.distance (sourceCoefficient 32 62 1 0) v2637_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2637_pb : Scalar.QComplex := ((-434236899492182596197167 : Int)/10^30,(-431477290406924603263179193 : Int)/10^30)
theorem v2637_pb_checked : Scalar.distance (sourceCoefficient 32 62 1 1) v2637_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2637_pg : Scalar.QComplex := ((-93086381452753368708288 : Int)/10^30,(93681736132320733323 : Int)/10^30)
theorem v2637_pg_checked : Scalar.distance (sourceCoefficient 32 62 1 2) v2637_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2637_mb : Scalar.QComplex := ((-806582206411342767877113 : Int)/10^30,(-431476755021322940629461979 : Int)/10^30)
theorem v2637_mb_checked : Scalar.distance (sourceCoefficient 32 62 3 1) v2637_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2637_mg : Scalar.QComplex := ((-93086265949320282627206 : Int)/10^30,(174011055989065674310 : Int)/10^30)
theorem v2637_mg_checked : Scalar.distance (sourceCoefficient 32 62 3 2) v2637_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2637_upper : Scalar.QComplex := ((999996267255593692466954879900 : Int)/10^30,(-2732302120782814030362436259 : Int)/10^30)
theorem v2637_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 62 5) 1) 14) v2637_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2637 : Material (32 : Basis) (62 : Basis) where
  plus := ![v2637_pa,v2637_pb,v2637_pg]
  minus := ![(Primitive.Addresses.material2637 1).one,v2637_mb,v2637_mg]
  upper := v2637_upper
  lower := (Primitive.Addresses.material2637 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2637_pa_checked.trans (by decide +kernel)
    · exact v2637_pb_checked.trans (by decide +kernel)
    · exact v2637_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 62 Primitive.Addresses.material2637
    · exact v2637_mb_checked.trans (by decide +kernel)
    · exact v2637_mg_checked.trans (by decide +kernel)
  upper_error := v2637_upper_checked
  lower_error := reuse_lower_error 32 62 Primitive.Addresses.material2637

def v2638_pa : Scalar.QComplex := ((999999468323064977799241237546 : Int)/10^30,(-1031190373967890704399840151 : Int)/10^30)
theorem v2638_pa_checked : Scalar.distance (sourceCoefficient 32 63 1 0) v2638_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2638_pb : Scalar.QComplex := ((-444935452222491978857055 : Int)/10^30,(-431477278001073437046810274 : Int)/10^30)
theorem v2638_pb_checked : Scalar.distance (sourceCoefficient 32 63 1 1) v2638_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2638_pg : Scalar.QComplex := ((-93086378938806956088547 : Int)/10^30,(95989828944803176783 : Int)/10^30)
theorem v2638_pg_checked : Scalar.distance (sourceCoefficient 32 63 1 2) v2638_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2638_mb : Scalar.QComplex := ((-817280744452401203378962 : Int)/10^30,(-431476733383107232349509037 : Int)/10^30)
theorem v2638_mb_checked : Scalar.distance (sourceCoefficient 32 63 3 1) v2638_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2638_mg : Scalar.QComplex := ((-93086261443594661533630 : Int)/10^30,(176319145772717148483 : Int)/10^30)
theorem v2638_mg_checked : Scalar.distance (sourceCoefficient 32 63 3 2) v2638_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2638_upper : Scalar.QComplex := ((999996199200288491216838998418 : Int)/10^30,(-2757097201213464529883343195 : Int)/10^30)
theorem v2638_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 63 5) 1) 14) v2638_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2638 : Material (32 : Basis) (63 : Basis) where
  plus := ![v2638_pa,v2638_pb,v2638_pg]
  minus := ![(Primitive.Addresses.material2638 1).one,v2638_mb,v2638_mg]
  upper := v2638_upper
  lower := (Primitive.Addresses.material2638 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2638_pa_checked.trans (by decide +kernel)
    · exact v2638_pb_checked.trans (by decide +kernel)
    · exact v2638_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 63 Primitive.Addresses.material2638
    · exact v2638_mb_checked.trans (by decide +kernel)
    · exact v2638_mg_checked.trans (by decide +kernel)
  upper_error := v2638_upper_checked
  lower_error := reuse_lower_error 32 63 Primitive.Addresses.material2638

def v2639_pa : Scalar.QComplex := ((999999431152592010008431700013 : Int)/10^30,(-1066627625927910025678846325 : Int)/10^30)
theorem v2639_pa_checked : Scalar.distance (sourceCoefficient 32 64 1 0) v2639_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2639_pb : Scalar.QComplex := ((-460225826907713207875295 : Int)/10^30,(-431477259656642032203400845 : Int)/10^30)
theorem v2639_pb_checked : Scalar.distance (sourceCoefficient 32 64 1 1) v2639_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2639_pg : Scalar.QComplex := ((-93086375229971104845107 : Int)/10^30,(99288555897816354752 : Int)/10^30)
theorem v2639_pg_checked : Scalar.distance (sourceCoefficient 32 64 1 2) v2639_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2639_mb : Scalar.QComplex := ((-832571097613899032585107 : Int)/10^30,(-431476701843777957542197552 : Int)/10^30)
theorem v2639_mb_checked : Scalar.distance (sourceCoefficient 32 64 3 1) v2639_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2639_mg : Scalar.QComplex := ((-93086254888107399955725 : Int)/10^30,(179617868296905222718 : Int)/10^30)
theorem v2639_mg_checked : Scalar.distance (sourceCoefficient 32 64 3 2) v2639_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2639_upper : Scalar.QComplex := ((999996100868388843870658385403 : Int)/10^30,(-2792534336240995545305641005 : Int)/10^30)
theorem v2639_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 64 5) 1) 14) v2639_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2639 : Material (32 : Basis) (64 : Basis) where
  plus := ![v2639_pa,v2639_pb,v2639_pg]
  minus := ![(Primitive.Addresses.material2639 1).one,v2639_mb,v2639_mg]
  upper := v2639_upper
  lower := (Primitive.Addresses.material2639 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2639_pa_checked.trans (by decide +kernel)
    · exact v2639_pb_checked.trans (by decide +kernel)
    · exact v2639_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 64 Primitive.Addresses.material2639
    · exact v2639_mb_checked.trans (by decide +kernel)
    · exact v2639_mg_checked.trans (by decide +kernel)
  upper_error := v2639_upper_checked
  lower_error := reuse_lower_error 32 64 Primitive.Addresses.material2639

def v2640_pa : Scalar.QComplex := ((999999392142804246273017706587 : Int)/10^30,(-1102594223645799595117688178 : Int)/10^30)
theorem v2640_pa_checked : Scalar.distance (sourceCoefficient 32 65 1 0) v2640_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2640_pb : Scalar.QComplex := ((-475744601973589503951576 : Int)/10^30,(-431477240299455138923367801 : Int)/10^30)
theorem v2640_pb_checked : Scalar.distance (sourceCoefficient 32 65 1 1) v2640_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2640_pg : Scalar.QComplex := ((-93086371326282317482279 : Int)/10^30,(102636557712877025401 : Int)/10^30)
theorem v2640_pg_checked : Scalar.distance (sourceCoefficient 32 65 1 2) v2640_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2640_mb : Scalar.QComplex := ((-848089850197045655011513 : Int)/10^30,(-431476669094594329659374942 : Int)/10^30)
theorem v2640_mb_checked : Scalar.distance (sourceCoefficient 32 65 3 1) v2640_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2640_mg : Scalar.QComplex := ((-93086248095245288121503 : Int)/10^30,(182965865496644198501 : Int)/10^30)
theorem v2640_mg_checked : Scalar.distance (sourceCoefficient 32 65 3 2) v2640_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2640_upper : Scalar.QComplex := ((999995999783574383811180169670 : Int)/10^30,(-2828500813063508007395210430 : Int)/10^30)
theorem v2640_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 65 5) 1) 14) v2640_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2640 : Material (32 : Basis) (65 : Basis) where
  plus := ![v2640_pa,v2640_pb,v2640_pg]
  minus := ![(Primitive.Addresses.material2640 1).one,v2640_mb,v2640_mg]
  upper := v2640_upper
  lower := (Primitive.Addresses.material2640 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2640_pa_checked.trans (by decide +kernel)
    · exact v2640_pb_checked.trans (by decide +kernel)
    · exact v2640_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 65 Primitive.Addresses.material2640
    · exact v2640_mb_checked.trans (by decide +kernel)
    · exact v2640_mg_checked.trans (by decide +kernel)
  upper_error := v2640_upper_checked
  lower_error := reuse_lower_error 32 65 Primitive.Addresses.material2640

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
