import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B106
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B107

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2561_pa : Scalar.QComplex := ((999999610606450464664580224579 : Int)/10^30,(-882489063639507330876775434 : Int)/10^30)
theorem v2561_pa_checked : Scalar.distance (sourceCoefficient 31 51 1 0) v2561_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2561_pb : Scalar.QComplex := ((-380774187943517933492997 : Int)/10^30,(-431477346701771410405099020 : Int)/10^30)
theorem v2561_pb_checked : Scalar.distance (sourceCoefficient 31 51 1 1) v2561_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2561_pg : Scalar.QComplex := ((-93086392971835204753173 : Int)/10^30,(82147755759100267341 : Int)/10^30)
theorem v2561_pg_checked : Scalar.distance (sourceCoefficient 31 51 1 2) v2561_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2561_mb : Scalar.QComplex := ((-753119563349206350146044 : Int)/10^30,(-431476857452060981980944372 : Int)/10^30)
theorem v2561_mb_checked : Scalar.distance (sourceCoefficient 31 51 3 1) v2561_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2561_mg : Scalar.QComplex := ((-93086287421703420488405 : Int)/10^30,(162477089850922054542 : Int)/10^30)
theorem v2561_mg_checked : Scalar.distance (sourceCoefficient 31 51 3 2) v2561_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2561_upper : Scalar.QComplex := ((999996598128433612988689970755 : Int)/10^30,(-2608396357926430709967119778 : Int)/10^30)
theorem v2561_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 51 5) 1) 14) v2561_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2561 : Material (31 : Basis) (51 : Basis) where
  plus := ![v2561_pa,v2561_pb,v2561_pg]
  minus := ![(Primitive.Addresses.material2561 1).one,v2561_mb,v2561_mg]
  upper := v2561_upper
  lower := (Primitive.Addresses.material2561 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2561_pa_checked.trans (by decide +kernel)
    · exact v2561_pb_checked.trans (by decide +kernel)
    · exact v2561_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 51 Primitive.Addresses.material2561
    · exact v2561_mb_checked.trans (by decide +kernel)
    · exact v2561_mg_checked.trans (by decide +kernel)
  upper_error := v2561_upper_checked
  lower_error := reuse_lower_error 31 51 Primitive.Addresses.material2561

def v2562_pa : Scalar.QComplex := ((999999588967430312229185493158 : Int)/10^30,(-906677986072105031166111296 : Int)/10^30)
theorem v2562_pa_checked : Scalar.distance (sourceCoefficient 31 52 1 0) v2562_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2562_pb : Scalar.QComplex := ((-391211163107786776636493 : Int)/10^30,(-431477336294503820808840663 : Int)/10^30)
theorem v2562_pb_checked : Scalar.distance (sourceCoefficient 31 52 1 1) v2562_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2562_pg : Scalar.QComplex := ((-93086390842060081995648 : Int)/10^30,(84399416070308743874 : Int)/10^30)
theorem v2562_pg_checked : Scalar.distance (sourceCoefficient 31 52 1 2) v2562_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2562_mb : Scalar.QComplex := ((-763556525646309142414034 : Int)/10^30,(-431476838038157764633839652 : Int)/10^30)
theorem v2562_mb_checked : Scalar.distance (sourceCoefficient 31 52 3 1) v2562_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2562_mg : Scalar.QComplex := ((-93086283348847653186442 : Int)/10^30,(164728747485834481823 : Int)/10^30)
theorem v2562_mg_checked : Scalar.distance (sourceCoefficient 31 52 3 2) v2562_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2562_upper : Scalar.QComplex := ((999996534741559972569642047125 : Int)/10^30,(-2632585206985484170800740115 : Int)/10^30)
theorem v2562_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 52 5) 1) 14) v2562_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2562 : Material (31 : Basis) (52 : Basis) where
  plus := ![v2562_pa,v2562_pb,v2562_pg]
  minus := ![(Primitive.Addresses.material2562 1).one,v2562_mb,v2562_mg]
  upper := v2562_upper
  lower := (Primitive.Addresses.material2562 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2562_pa_checked.trans (by decide +kernel)
    · exact v2562_pb_checked.trans (by decide +kernel)
    · exact v2562_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 52 Primitive.Addresses.material2562
    · exact v2562_mb_checked.trans (by decide +kernel)
    · exact v2562_mg_checked.trans (by decide +kernel)
  upper_error := v2562_upper_checked
  lower_error := reuse_lower_error 31 52 Primitive.Addresses.material2562

def v2563_pa : Scalar.QComplex := ((999999585603427957467033015924 : Int)/10^30,(-910380674421720692847269776 : Int)/10^30)
theorem v2563_pa_checked : Scalar.distance (sourceCoefficient 31 53 1 0) v2563_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2563_pb : Scalar.QComplex := ((-392808789714740775814190 : Int)/10^30,(-431477334671717700944716762 : Int)/10^30)
theorem v2563_pb_checked : Scalar.distance (sourceCoefficient 31 53 1 1) v2563_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2563_pg : Scalar.QComplex := ((-93086390510439656243357 : Int)/10^30,(84744086090036491976 : Int)/10^30)
theorem v2563_pg_checked : Scalar.distance (sourceCoefficient 31 53 1 2) v2563_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2563_mb : Scalar.QComplex := ((-765154150258002406810760 : Int)/10^30,(-431476835036692441637155039 : Int)/10^30)
theorem v2563_mb_checked : Scalar.distance (sourceCoefficient 31 53 3 1) v2563_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2563_mg : Scalar.QComplex := ((-93086282719792647247979 : Int)/10^30,(165073417091052337587 : Int)/10^30)
theorem v2563_mg_checked : Scalar.distance (sourceCoefficient 31 53 3 2) v2563_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2563_upper : Scalar.QComplex := ((999996524987058441920330666430 : Int)/10^30,(-2636287884014417599646584137 : Int)/10^30)
theorem v2563_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 53 5) 1) 14) v2563_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2563 : Material (31 : Basis) (53 : Basis) where
  plus := ![v2563_pa,v2563_pb,v2563_pg]
  minus := ![(Primitive.Addresses.material2563 1).one,v2563_mb,v2563_mg]
  upper := v2563_upper
  lower := (Primitive.Addresses.material2563 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2563_pa_checked.trans (by decide +kernel)
    · exact v2563_pb_checked.trans (by decide +kernel)
    · exact v2563_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 53 Primitive.Addresses.material2563
    · exact v2563_mb_checked.trans (by decide +kernel)
    · exact v2563_mg_checked.trans (by decide +kernel)
  upper_error := v2563_upper_checked
  lower_error := reuse_lower_error 31 53 Primitive.Addresses.material2563

def v2564_pa : Scalar.QComplex := ((999999583887891801834932040775 : Int)/10^30,(-912263143641703606228687668 : Int)/10^30)
theorem v2564_pa_checked : Scalar.distance (sourceCoefficient 31 54 1 0) v2564_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2564_pb : Scalar.QComplex := ((-393621032772835017226748 : Int)/10^30,(-431477333843659052495481658 : Int)/10^30)
theorem v2564_pb_checked : Scalar.distance (sourceCoefficient 31 54 1 1) v2564_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2564_pg : Scalar.QComplex := ((-93086390341270910878478 : Int)/10^30,(84919318418943130203 : Int)/10^30)
theorem v2564_pg_checked : Scalar.distance (sourceCoefficient 31 54 1 2) v2564_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2564_mb : Scalar.QComplex := ((-765966392299084117118649 : Int)/10^30,(-431476833507704924446014880 : Int)/10^30)
theorem v2564_mb_checked : Scalar.distance (sourceCoefficient 31 54 3 1) v2564_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2564_mg : Scalar.QComplex := ((-93086282399406357197049 : Int)/10^30,(165248649208726963077 : Int)/10^30)
theorem v2564_mg_checked : Scalar.distance (sourceCoefficient 31 54 3 2) v2564_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2564_upper : Scalar.QComplex := ((999996520022553743960909786018 : Int)/10^30,(-2638170347469823967834893320 : Int)/10^30)
theorem v2564_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 54 5) 1) 14) v2564_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2564 : Material (31 : Basis) (54 : Basis) where
  plus := ![v2564_pa,v2564_pb,v2564_pg]
  minus := ![(Primitive.Addresses.material2564 1).one,v2564_mb,v2564_mg]
  upper := v2564_upper
  lower := (Primitive.Addresses.material2564 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2564_pa_checked.trans (by decide +kernel)
    · exact v2564_pb_checked.trans (by decide +kernel)
    · exact v2564_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 54 Primitive.Addresses.material2564
    · exact v2564_mb_checked.trans (by decide +kernel)
    · exact v2564_mg_checked.trans (by decide +kernel)
  upper_error := v2564_upper_checked
  lower_error := reuse_lower_error 31 54 Primitive.Addresses.material2564

def v2565_pa : Scalar.QComplex := ((999999569772781732500567460560 : Int)/10^30,(-927606733179281923051834722 : Int)/10^30)
theorem v2565_pa_checked : Scalar.distance (sourceCoefficient 31 55 1 0) v2565_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2565_pb : Scalar.QComplex := ((-400241445951144682379079 : Int)/10^30,(-431477327018307305144659119 : Int)/10^30)
theorem v2565_pb_checked : Scalar.distance (sourceCoefficient 31 55 1 1) v2565_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2565_pg : Scalar.QComplex := ((-93086388948061812101207 : Int)/10^30,(86347598304654653717 : Int)/10^30)
theorem v2565_pg_checked : Scalar.distance (sourceCoefficient 31 55 1 2) v2565_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2565_mb : Scalar.QComplex := ((-772586797122340232624515 : Int)/10^30,(-431476820969237317945214325 : Int)/10^30)
theorem v2565_mb_checked : Scalar.distance (sourceCoefficient 31 55 3 1) v2565_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2565_mg : Scalar.QComplex := ((-93086279773656563144263 : Int)/10^30,(166676927360347905088 : Int)/10^30)
theorem v2565_mg_checked : Scalar.distance (sourceCoefficient 31 55 3 2) v2565_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2565_upper : Scalar.QComplex := ((999996479425821115134199002794 : Int)/10^30,(-2653513889793528586184396512 : Int)/10^30)
theorem v2565_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 55 5) 1) 14) v2565_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2565 : Material (31 : Basis) (55 : Basis) where
  plus := ![v2565_pa,v2565_pb,v2565_pg]
  minus := ![(Primitive.Addresses.material2565 1).one,v2565_mb,v2565_mg]
  upper := v2565_upper
  lower := (Primitive.Addresses.material2565 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2565_pa_checked.trans (by decide +kernel)
    · exact v2565_pb_checked.trans (by decide +kernel)
    · exact v2565_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 55 Primitive.Addresses.material2565
    · exact v2565_mb_checked.trans (by decide +kernel)
    · exact v2565_mg_checked.trans (by decide +kernel)
  upper_error := v2565_upper_checked
  lower_error := reuse_lower_error 31 55 Primitive.Addresses.material2565

def v2566_pa : Scalar.QComplex := ((999999566388305150528761644075 : Int)/10^30,(-931248195531052058145934202 : Int)/10^30)
theorem v2566_pa_checked : Scalar.distance (sourceCoefficient 31 56 1 0) v2566_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2566_pb : Scalar.QComplex := ((-401812654902028286198135 : Int)/10^30,(-431477325378574355763833327 : Int)/10^30)
theorem v2566_pb_checked : Scalar.distance (sourceCoefficient 31 56 1 1) v2566_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2566_pg : Scalar.QComplex := ((-93086388613660405904912 : Int)/10^30,(86686569013283634136 : Int)/10^30)
theorem v2566_pg_checked : Scalar.distance (sourceCoefficient 31 56 1 2) v2566_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2566_mb : Scalar.QComplex := ((-774158004073175251748089 : Int)/10^30,(-431476817973622419123596456 : Int)/10^30)
theorem v2566_mb_checked : Scalar.distance (sourceCoefficient 31 56 3 1) v2566_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2566_mg : Scalar.QComplex := ((-93086279146738826588075 : Int)/10^30,(167015897654189246291 : Int)/10^30)
theorem v2566_mg_checked : Scalar.distance (sourceCoefficient 31 56 3 2) v2566_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2566_upper : Scalar.QComplex := ((999996469756515905671433411766 : Int)/10^30,(-2657155340880468761366689737 : Int)/10^30)
theorem v2566_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 56 5) 1) 14) v2566_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2566 : Material (31 : Basis) (56 : Basis) where
  plus := ![v2566_pa,v2566_pb,v2566_pg]
  minus := ![(Primitive.Addresses.material2566 1).one,v2566_mb,v2566_mg]
  upper := v2566_upper
  lower := (Primitive.Addresses.material2566 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2566_pa_checked.trans (by decide +kernel)
    · exact v2566_pb_checked.trans (by decide +kernel)
    · exact v2566_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 56 Primitive.Addresses.material2566
    · exact v2566_mb_checked.trans (by decide +kernel)
    · exact v2566_mg_checked.trans (by decide +kernel)
  upper_error := v2566_upper_checked
  lower_error := reuse_lower_error 31 56 Primitive.Addresses.material2566

def v2567_pa : Scalar.QComplex := ((999999555350838753668832117756 : Int)/10^30,(-943026046713337467133873200 : Int)/10^30)
theorem v2567_pa_checked : Scalar.distance (sourceCoefficient 31 57 1 0) v2567_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2567_pb : Scalar.QComplex := ((-406894532272902994181947 : Int)/10^30,(-431477320022825291854779170 : Int)/10^30)
theorem v2567_pb_checked : Scalar.distance (sourceCoefficient 31 57 1 1) v2567_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2567_pg : Scalar.QComplex := ((-93086387522219876054841 : Int)/10^30,(87782927060509643962 : Int)/10^30)
theorem v2567_pg_checked : Scalar.distance (sourceCoefficient 31 57 1 2) v2567_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2567_mb : Scalar.QComplex := ((-779239874930064533115894 : Int)/10^30,(-431476808232444057600202302 : Int)/10^30)
theorem v2567_mb_checked : Scalar.distance (sourceCoefficient 31 57 3 1) v2567_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2567_mg : Scalar.QComplex := ((-93086277109191086508593 : Int)/10^30,(168112254351327028493 : Int)/10^30)
theorem v2567_mg_checked : Scalar.distance (sourceCoefficient 31 57 3 2) v2567_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2567_upper : Scalar.QComplex := ((999996438391563285509296609549 : Int)/10^30,(-2668933155471362668077086023 : Int)/10^30)
theorem v2567_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 57 5) 1) 14) v2567_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2567 : Material (31 : Basis) (57 : Basis) where
  plus := ![v2567_pa,v2567_pb,v2567_pg]
  minus := ![(Primitive.Addresses.material2567 1).one,v2567_mb,v2567_mg]
  upper := v2567_upper
  lower := (Primitive.Addresses.material2567 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2567_pa_checked.trans (by decide +kernel)
    · exact v2567_pb_checked.trans (by decide +kernel)
    · exact v2567_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 57 Primitive.Addresses.material2567
    · exact v2567_mb_checked.trans (by decide +kernel)
    · exact v2567_mg_checked.trans (by decide +kernel)
  upper_error := v2567_upper_checked
  lower_error := reuse_lower_error 31 57 Primitive.Addresses.material2567

def v2568_pa : Scalar.QComplex := ((999999549303963819818075875951 : Int)/10^30,(-949416594142659179022045239 : Int)/10^30)
theorem v2568_pa_checked : Scalar.distance (sourceCoefficient 31 58 1 0) v2568_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2568_pb : Scalar.QComplex := ((-409651909463672977900760 : Int)/10^30,(-431477317083449848738196982 : Int)/10^30)
theorem v2568_pb_checked : Scalar.distance (sourceCoefficient 31 58 1 1) v2568_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2568_pg : Scalar.QComplex := ((-93086386923710254291353 : Int)/10^30,(88377800265679021074 : Int)/10^30)
theorem v2568_pg_checked : Scalar.distance (sourceCoefficient 31 58 1 2) v2568_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2568_mb : Scalar.QComplex := ((-781997248557588347493993 : Int)/10^30,(-431476802913577380971547425 : Int)/10^30)
theorem v2568_mb_checked : Scalar.distance (sourceCoefficient 31 58 3 1) v2568_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2568_mg : Scalar.QComplex := ((-93086275997332903631009 : Int)/10^30,(168707126818511076563 : Int)/10^30)
theorem v2568_mg_checked : Scalar.distance (sourceCoefficient 31 58 3 2) v2568_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2568_upper : Scalar.QComplex := ((999996421315192240693225150816 : Int)/10^30,(-2675323682946357102806876170 : Int)/10^30)
theorem v2568_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 58 5) 1) 14) v2568_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2568 : Material (31 : Basis) (58 : Basis) where
  plus := ![v2568_pa,v2568_pb,v2568_pg]
  minus := ![(Primitive.Addresses.material2568 1).one,v2568_mb,v2568_mg]
  upper := v2568_upper
  lower := (Primitive.Addresses.material2568 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2568_pa_checked.trans (by decide +kernel)
    · exact v2568_pb_checked.trans (by decide +kernel)
    · exact v2568_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 58 Primitive.Addresses.material2568
    · exact v2568_mb_checked.trans (by decide +kernel)
    · exact v2568_mg_checked.trans (by decide +kernel)
  upper_error := v2568_upper_checked
  lower_error := reuse_lower_error 31 58 Primitive.Addresses.material2568

def v2569_pa : Scalar.QComplex := ((999999532472300387378353222782 : Int)/10^30,(-966982513100983325369845599 : Int)/10^30)
theorem v2569_pa_checked : Scalar.distance (sourceCoefficient 31 59 1 0) v2569_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2569_pb : Scalar.QComplex := ((-417231207556722471819722 : Int)/10^30,(-431477308882837866537884627 : Int)/10^30)
theorem v2569_pb_checked : Scalar.distance (sourceCoefficient 31 59 1 1) v2569_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2569_pg : Scalar.QComplex := ((-93086385255715552327430 : Int)/10^30,(90012948833605048657 : Int)/10^30)
theorem v2569_pg_checked : Scalar.distance (sourceCoefficient 31 59 1 2) v2569_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2569_mb : Scalar.QComplex := ((-789576536751759971549906 : Int)/10^30,(-431476788172375556846421680 : Int)/10^30)
theorem v2569_mb_checked : Scalar.distance (sourceCoefficient 31 59 3 1) v2569_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2569_mg : Scalar.QComplex := ((-93086272918279252975276 : Int)/10^30,(170342273338192258223 : Int)/10^30)
theorem v2569_mg_checked : Scalar.distance (sourceCoefficient 31 59 3 2) v2569_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2569_upper : Scalar.QComplex := ((999996374166371322691153725501 : Int)/10^30,(-2692889546692384270708003721 : Int)/10^30)
theorem v2569_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 59 5) 1) 14) v2569_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2569 : Material (31 : Basis) (59 : Basis) where
  plus := ![v2569_pa,v2569_pb,v2569_pg]
  minus := ![(Primitive.Addresses.material2569 1).one,v2569_mb,v2569_mg]
  upper := v2569_upper
  lower := (Primitive.Addresses.material2569 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2569_pa_checked.trans (by decide +kernel)
    · exact v2569_pb_checked.trans (by decide +kernel)
    · exact v2569_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 59 Primitive.Addresses.material2569
    · exact v2569_mb_checked.trans (by decide +kernel)
    · exact v2569_mg_checked.trans (by decide +kernel)
  upper_error := v2569_upper_checked
  lower_error := reuse_lower_error 31 59 Primitive.Addresses.material2569

def v2570_pa : Scalar.QComplex := ((999999512672120900978706598292 : Int)/10^30,(-987246433627177424433271952 : Int)/10^30)
theorem v2570_pa_checked : Scalar.distance (sourceCoefficient 31 60 1 0) v2570_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2570_pb : Scalar.QComplex := ((-425974632417734253232811 : Int)/10^30,(-431477299202161073696318237 : Int)/10^30)
theorem v2570_pb_checked : Scalar.distance (sourceCoefficient 31 60 1 1) v2570_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2570_pg : Scalar.QComplex := ((-93086383289902888343473 : Int)/10^30,(91899244707273123552 : Int)/10^30)
theorem v2570_pg_checked : Scalar.distance (sourceCoefficient 31 60 1 2) v2570_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2570_mb : Scalar.QComplex := ((-798319950003207012227145 : Int)/10^30,(-431476770946520502747683031 : Int)/10^30)
theorem v2570_mb_checked : Scalar.distance (sourceCoefficient 31 60 3 1) v2570_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2570_mg : Scalar.QComplex := ((-93086269324678937590116 : Int)/10^30,(172228566813098379270 : Int)/10^30)
theorem v2570_mg_checked : Scalar.distance (sourceCoefficient 31 60 3 2) v2570_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2570_upper : Scalar.QComplex := ((999996319392532826631846718169 : Int)/10^30,(-2713153402864535578047626976 : Int)/10^30)
theorem v2570_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 60 5) 1) 14) v2570_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2570 : Material (31 : Basis) (60 : Basis) where
  plus := ![v2570_pa,v2570_pb,v2570_pg]
  minus := ![(Primitive.Addresses.material2570 1).one,v2570_mb,v2570_mg]
  upper := v2570_upper
  lower := (Primitive.Addresses.material2570 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2570_pa_checked.trans (by decide +kernel)
    · exact v2570_pb_checked.trans (by decide +kernel)
    · exact v2570_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 60 Primitive.Addresses.material2570
    · exact v2570_mb_checked.trans (by decide +kernel)
    · exact v2570_mg_checked.trans (by decide +kernel)
  upper_error := v2570_upper_checked
  lower_error := reuse_lower_error 31 60 Primitive.Addresses.material2570

def v2571_pa : Scalar.QComplex := ((999999506870346841697317629592 : Int)/10^30,(-993105766341002845711314756 : Int)/10^30)
theorem v2571_pa_checked : Scalar.distance (sourceCoefficient 31 61 1 0) v2571_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2571_pb : Scalar.QComplex := ((-428502802366741690762228 : Int)/10^30,(-431477296358954375834274096 : Int)/10^30)
theorem v2571_pb_checked : Scalar.distance (sourceCoefficient 31 61 1 1) v2571_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2571_pg : Scalar.QComplex := ((-93086382713174712666206 : Int)/10^30,(92444669027486826575 : Int)/10^30)
theorem v2571_pg_checked : Scalar.distance (sourceCoefficient 31 61 1 2) v2571_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2571_mb : Scalar.QComplex := ((-800848116557301907687647 : Int)/10^30,(-431476765921618062095667483 : Int)/10^30)
theorem v2571_mb_checked : Scalar.distance (sourceCoefficient 31 61 3 1) v2571_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2571_mg : Scalar.QComplex := ((-93086268277274353310169 : Int)/10^30,(172773990432535240017 : Int)/10^30)
theorem v2571_mg_checked : Scalar.distance (sourceCoefficient 31 61 3 2) v2571_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2571_upper : Scalar.QComplex := ((999996303478090698860239936157 : Int)/10^30,(-2719012716838237514164189165 : Int)/10^30)
theorem v2571_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 61 5) 1) 14) v2571_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2571 : Material (31 : Basis) (61 : Basis) where
  plus := ![v2571_pa,v2571_pb,v2571_pg]
  minus := ![(Primitive.Addresses.material2571 1).one,v2571_mb,v2571_mg]
  upper := v2571_upper
  lower := (Primitive.Addresses.material2571 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2571_pa_checked.trans (by decide +kernel)
    · exact v2571_pb_checked.trans (by decide +kernel)
    · exact v2571_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 61 Primitive.Addresses.material2571
    · exact v2571_mb_checked.trans (by decide +kernel)
    · exact v2571_mg_checked.trans (by decide +kernel)
  upper_error := v2571_upper_checked
  lower_error := reuse_lower_error 31 61 Primitive.Addresses.material2571

def v2572_pa : Scalar.QComplex := ((999999498379438055322880926117 : Int)/10^30,(-1001619125349634122317636362 : Int)/10^30)
theorem v2572_pa_checked : Scalar.distance (sourceCoefficient 31 62 1 0) v2572_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2572_pb : Scalar.QComplex := ((-432176124802711253158614 : Int)/10^30,(-431477292192699980837426006 : Int)/10^30)
theorem v2572_pb_checked : Scalar.distance (sourceCoefficient 31 62 1 1) v2572_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2572_pg : Scalar.QComplex := ((-93086381868569219644235 : Int)/10^30,(93237147158828494136 : Int)/10^30)
theorem v2572_pg_checked : Scalar.distance (sourceCoefficient 31 62 1 2) v2572_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2572_mb : Scalar.QComplex := ((-804521434030235746293948 : Int)/10^30,(-431476758585453396445088946 : Int)/10^30)
theorem v2572_mb_checked : Scalar.distance (sourceCoefficient 31 62 3 1) v2572_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2572_mg : Scalar.QComplex := ((-93086266748796239315654 : Int)/10^30,(173566467539944580381 : Int)/10^30)
theorem v2572_mg_checked : Scalar.distance (sourceCoefficient 31 62 3 2) v2572_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2572_upper : Scalar.QComplex := ((999996280293909235695629118542 : Int)/10^30,(-2727526048512682320758669744 : Int)/10^30)
theorem v2572_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 62 5) 1) 14) v2572_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2572 : Material (31 : Basis) (62 : Basis) where
  plus := ![v2572_pa,v2572_pb,v2572_pg]
  minus := ![(Primitive.Addresses.material2572 1).one,v2572_mb,v2572_mg]
  upper := v2572_upper
  lower := (Primitive.Addresses.material2572 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2572_pa_checked.trans (by decide +kernel)
    · exact v2572_pb_checked.trans (by decide +kernel)
    · exact v2572_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 62 Primitive.Addresses.material2572
    · exact v2572_mb_checked.trans (by decide +kernel)
    · exact v2572_mg_checked.trans (by decide +kernel)
  upper_error := v2572_upper_checked
  lower_error := reuse_lower_error 31 62 Primitive.Addresses.material2572

def v2573_pa : Scalar.QComplex := ((999999473236717567882250426776 : Int)/10^30,(-1026414286428574502666129098 : Int)/10^30)
theorem v2573_pa_checked : Scalar.distance (sourceCoefficient 31 63 1 0) v2573_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2573_pb : Scalar.QComplex := ((-442874677567644318309872 : Int)/10^30,(-431477279820913654061107690 : Int)/10^30)
theorem v2573_pb_checked : Scalar.distance (sourceCoefficient 31 63 1 1) v2573_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2573_pg : Scalar.QComplex := ((-93086379363809190366479 : Int)/10^30,(95545239980648026082 : Int)/10^30)
theorem v2573_pg_checked : Scalar.distance (sourceCoefficient 31 63 1 2) v2573_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2573_mb : Scalar.QComplex := ((-815219972135314273608536 : Int)/10^30,(-431476736981302485042611447 : Int)/10^30)
theorem v2573_mb_checked : Scalar.distance (sourceCoefficient 31 63 3 1) v2573_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2573_mg : Scalar.QComplex := ((-93086262252256990086065 : Int)/10^30,(175874557340860574648 : Int)/10^30)
theorem v2573_mg_checked : Scalar.distance (sourceCoefficient 31 63 3 2) v2573_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2573_upper : Scalar.QComplex := ((999996212357027572574334081568 : Int)/10^30,(-2752321129268088286710342306 : Int)/10^30)
theorem v2573_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 63 5) 1) 14) v2573_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2573 : Material (31 : Basis) (63 : Basis) where
  plus := ![v2573_pa,v2573_pb,v2573_pg]
  minus := ![(Primitive.Addresses.material2573 1).one,v2573_mb,v2573_mg]
  upper := v2573_upper
  lower := (Primitive.Addresses.material2573 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2573_pa_checked.trans (by decide +kernel)
    · exact v2573_pb_checked.trans (by decide +kernel)
    · exact v2573_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 63 Primitive.Addresses.material2573
    · exact v2573_mb_checked.trans (by decide +kernel)
    · exact v2573_mg_checked.trans (by decide +kernel)
  upper_error := v2573_upper_checked
  lower_error := reuse_lower_error 31 63 Primitive.Addresses.material2573

def v2574_pa : Scalar.QComplex := ((999999436235496107599582102168 : Int)/10^30,(-1061851538565719170447375750 : Int)/10^30)
theorem v2574_pa_checked : Scalar.distance (sourceCoefficient 31 64 1 0) v2574_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2574_pb : Scalar.QComplex := ((-458165052303815949566840 : Int)/10^30,(-431477261525167728497869568 : Int)/10^30)
theorem v2574_pb_checked : Scalar.distance (sourceCoefficient 31 64 1 1) v2574_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2574_pg : Scalar.QComplex := ((-93086375668102521108994 : Int)/10^30,(98843966947401175663 : Int)/10^30)
theorem v2574_pg_checked : Scalar.distance (sourceCoefficient 31 64 1 2) v2574_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2574_mb : Scalar.QComplex := ((-830510325389775861988444 : Int)/10^30,(-431476705490658627419739885 : Int)/10^30)
theorem v2574_mb_checked : Scalar.distance (sourceCoefficient 31 64 3 1) v2574_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2574_mg : Scalar.QComplex := ((-93086255709898893748544 : Int)/10^30,(179173279890118508117 : Int)/10^30)
theorem v2574_mg_checked : Scalar.distance (sourceCoefficient 31 64 3 2) v2574_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2574_upper : Scalar.QComplex := ((999996114194378874953776549830 : Int)/10^30,(-2787758264764857132409715989 : Int)/10^30)
theorem v2574_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 64 5) 1) 14) v2574_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2574 : Material (31 : Basis) (64 : Basis) where
  plus := ![v2574_pa,v2574_pb,v2574_pg]
  minus := ![(Primitive.Addresses.material2574 1).one,v2574_mb,v2574_mg]
  upper := v2574_upper
  lower := (Primitive.Addresses.material2574 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2574_pa_checked.trans (by decide +kernel)
    · exact v2574_pb_checked.trans (by decide +kernel)
    · exact v2574_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 64 Primitive.Addresses.material2574
    · exact v2574_mb_checked.trans (by decide +kernel)
    · exact v2574_mg_checked.trans (by decide +kernel)
  upper_error := v2574_upper_checked
  lower_error := reuse_lower_error 31 64 Primitive.Addresses.material2574

def v2575_pa : Scalar.QComplex := ((999999397397488054409403100790 : Int)/10^30,(-1097818136469512782052600141 : Int)/10^30)
theorem v2575_pa_checked : Scalar.distance (sourceCoefficient 31 65 1 0) v2575_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2575_pb : Scalar.QComplex := ((-473683827423167854195183 : Int)/10^30,(-431477242217393556164323579 : Int)/10^30)
theorem v2575_pb_checked : Scalar.distance (sourceCoefficient 31 65 1 1) v2575_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2575_pg : Scalar.QComplex := ((-93086371777739033531557 : Int)/10^30,(102191968776882799086 : Int)/10^30)
theorem v2575_pg_checked : Scalar.distance (sourceCoefficient 31 65 1 2) v2575_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2575_mb : Scalar.QComplex := ((-846029078069039025765978 : Int)/10^30,(-431476672790887655937748321 : Int)/10^30)
theorem v2575_mb_checked : Scalar.distance (sourceCoefficient 31 65 3 1) v2575_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2575_mg : Scalar.QComplex := ((-93086248930362064293461 : Int)/10^30,(182521277115777564869 : Int)/10^30)
theorem v2575_mg_checked : Scalar.distance (sourceCoefficient 31 65 3 2) v2575_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2575_upper : Scalar.QComplex := ((999996013281343548740321435079 : Int)/10^30,(-2823724742069749556450903346 : Int)/10^30)
theorem v2575_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 65 5) 1) 14) v2575_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2575 : Material (31 : Basis) (65 : Basis) where
  plus := ![v2575_pa,v2575_pb,v2575_pg]
  minus := ![(Primitive.Addresses.material2575 1).one,v2575_mb,v2575_mg]
  upper := v2575_upper
  lower := (Primitive.Addresses.material2575 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2575_pa_checked.trans (by decide +kernel)
    · exact v2575_pb_checked.trans (by decide +kernel)
    · exact v2575_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 65 Primitive.Addresses.material2575
    · exact v2575_mb_checked.trans (by decide +kernel)
    · exact v2575_mg_checked.trans (by decide +kernel)
  upper_error := v2575_upper_checked
  lower_error := reuse_lower_error 31 65 Primitive.Addresses.material2575

def v2576_pa : Scalar.QComplex := ((999999377934877398642239620707 : Int)/10^30,(-1115405692220413031417336189 : Int)/10^30)
theorem v2576_pa_checked : Scalar.distance (sourceCoefficient 31 66 1 0) v2576_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2576_pb : Scalar.QComplex := ((-481272460582417372901942 : Int)/10^30,(-431477232505015736677238867 : Int)/10^30)
theorem v2576_pb_checked : Scalar.distance (sourceCoefficient 31 66 1 1) v2576_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2576_pg : Scalar.QComplex := ((-93086369824218337458906 : Int)/10^30,(103829131358548950157 : Int)/10^30)
theorem v2576_pg_checked : Scalar.distance (sourceCoefficient 31 66 1 2) v2576_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2576_mb : Scalar.QComplex := ((-853617700021348972657121 : Int)/10^30,(-431476656529864815730515500 : Int)/10^30)
theorem v2576_mb_checked : Scalar.distance (sourceCoefficient 31 66 3 1) v2576_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2576_mg : Scalar.QComplex := ((-93086245564044522693462 : Int)/10^30,(184158437402052887355 : Int)/10^30)
theorem v2576_mg_checked : Scalar.distance (sourceCoefficient 31 66 3 2) v2576_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2576_upper : Scalar.QComplex := ((999995963464236184785781121229 : Int)/10^30,(-2841312238035351136667547112 : Int)/10^30)
theorem v2576_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 66 5) 1) 14) v2576_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2576 : Material (31 : Basis) (66 : Basis) where
  plus := ![v2576_pa,v2576_pb,v2576_pg]
  minus := ![(Primitive.Addresses.material2576 1).one,v2576_mb,v2576_mg]
  upper := v2576_upper
  lower := (Primitive.Addresses.material2576 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2576_pa_checked.trans (by decide +kernel)
    · exact v2576_pb_checked.trans (by decide +kernel)
    · exact v2576_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 66 Primitive.Addresses.material2576
    · exact v2576_mb_checked.trans (by decide +kernel)
    · exact v2576_mg_checked.trans (by decide +kernel)
  upper_error := v2576_upper_checked
  lower_error := reuse_lower_error 31 66 Primitive.Addresses.material2576

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
