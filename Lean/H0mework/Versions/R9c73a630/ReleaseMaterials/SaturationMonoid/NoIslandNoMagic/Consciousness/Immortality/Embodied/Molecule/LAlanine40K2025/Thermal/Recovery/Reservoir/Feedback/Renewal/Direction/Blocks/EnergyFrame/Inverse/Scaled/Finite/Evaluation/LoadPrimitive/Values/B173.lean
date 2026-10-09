import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B115
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B116

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2769_pa : Scalar.QComplex := ((999999312595863760755802822937 : Int)/10^30,(-1172521982716759931507614329 : Int)/10^30)
theorem v2769_pa_checked : Scalar.distance (sourceCoefficient 34 67 1 0) v2769_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2769_pb : Scalar.QComplex := ((-505916854695890060646426 : Int)/10^30,(-431477204166638795039091210 : Int)/10^30)
theorem v2769_pb_checked : Scalar.distance (sourceCoefficient 34 67 1 1) v2769_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2769_pg : Scalar.QComplex := ((-93086363726287280922652 : Int)/10^30,(109145882787571125478 : Int)/10^30)
theorem v2769_pg_checked : Scalar.distance (sourceCoefficient 34 67 1 2) v2769_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2769_mb : Scalar.QComplex := ((-878262060503844439988929 : Int)/10^30,(-431476606924496248146177077 : Int)/10^30)
theorem v2769_mb_checked : Scalar.distance (sourceCoefficient 34 67 3 1) v2769_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2769_mg : Scalar.QComplex := ((-93086234877998711044771 : Int)/10^30,(189475181589165656936 : Int)/10^30)
theorem v2769_mg_checked : Scalar.distance (sourceCoefficient 34 67 3 2) v2769_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2769_upper : Scalar.QComplex := ((999995799547784014387934655368 : Int)/10^30,(-2898428330694482663259085355 : Int)/10^30)
theorem v2769_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 67 5) 1) 14) v2769_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2769 : Material (34 : Basis) (67 : Basis) where
  plus := ![v2769_pa,v2769_pb,v2769_pg]
  minus := ![(Primitive.Addresses.material2769 1).one,v2769_mb,v2769_mg]
  upper := v2769_upper
  lower := (Primitive.Addresses.material2769 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2769_pa_checked.trans (by decide +kernel)
    · exact v2769_pb_checked.trans (by decide +kernel)
    · exact v2769_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 67 Primitive.Addresses.material2769
    · exact v2769_mb_checked.trans (by decide +kernel)
    · exact v2769_mg_checked.trans (by decide +kernel)
  upper_error := v2769_upper_checked
  lower_error := reuse_lower_error 34 67 Primitive.Addresses.material2769

def v2770_pa : Scalar.QComplex := ((999999253748795194100961860399 : Int)/10^30,(-1221679930555027740250785317 : Int)/10^30)
theorem v2770_pa_checked : Scalar.distance (sourceCoefficient 34 68 1 0) v2770_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2770_pb : Scalar.QComplex := ((-527127398377874249588820 : Int)/10^30,(-431477174851301946634696912 : Int)/10^30)
theorem v2770_pb_checked : Scalar.distance (sourceCoefficient 34 68 1 1) v2770_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2770_pg : Scalar.QComplex := ((-93086357825128154279195 : Int)/10^30,(113721820028468235557 : Int)/10^30)
theorem v2770_pg_checked : Scalar.distance (sourceCoefficient 34 68 1 2) v2770_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2770_mb : Scalar.QComplex := ((-899472570990358459980816 : Int)/10^30,(-431476559305426405054613893 : Int)/10^30)
theorem v2770_mb_checked : Scalar.distance (sourceCoefficient 34 68 3 1) v2770_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2770_mg : Scalar.QComplex := ((-93086225028014035341162 : Int)/10^30,(194051112033797653613 : Int)/10^30)
theorem v2770_mg_checked : Scalar.distance (sourceCoefficient 34 68 3 2) v2770_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2770_upper : Scalar.QComplex := ((999995655858644698870429402510 : Int)/10^30,(-2947586103753059883403347188 : Int)/10^30)
theorem v2770_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 68 5) 1) 14) v2770_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2770 : Material (34 : Basis) (68 : Basis) where
  plus := ![v2770_pa,v2770_pb,v2770_pg]
  minus := ![(Primitive.Addresses.material2770 1).one,v2770_mb,v2770_mg]
  upper := v2770_upper
  lower := (Primitive.Addresses.material2770 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2770_pa_checked.trans (by decide +kernel)
    · exact v2770_pb_checked.trans (by decide +kernel)
    · exact v2770_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 68 Primitive.Addresses.material2770
    · exact v2770_mb_checked.trans (by decide +kernel)
    · exact v2770_mg_checked.trans (by decide +kernel)
  upper_error := v2770_upper_checked
  lower_error := reuse_lower_error 34 68 Primitive.Addresses.material2770

def v2771_pa : Scalar.QComplex := ((999999227083231342521831035730 : Int)/10^30,(-1243315301890323018802065698 : Int)/10^30)
theorem v2771_pa_checked : Scalar.distance (sourceCoefficient 34 69 1 0) v2771_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2771_pb : Scalar.QComplex := ((-536462571960602095364851 : Int)/10^30,(-431477161508471149200517856 : Int)/10^30)
theorem v2771_pb_checked : Scalar.distance (sourceCoefficient 34 69 1 1) v2771_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2771_pg : Scalar.QComplex := ((-93086355144744127862791 : Int)/10^30,(115735779202781848093 : Int)/10^30)
theorem v2771_pg_checked : Scalar.distance (sourceCoefficient 34 69 1 2) v2771_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2771_mb : Scalar.QComplex := ((-908807729582912503003692 : Int)/10^30,(-431476537906766214482684266 : Int)/10^30)
theorem v2771_mb_checked : Scalar.distance (sourceCoefficient 34 69 3 1) v2771_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2771_mg : Scalar.QComplex := ((-93086220609674944875653 : Int)/10^30,(196065068145171528289 : Int)/10^30)
theorem v2771_mg_checked : Scalar.distance (sourceCoefficient 34 69 3 2) v2771_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2771_upper : Scalar.QComplex := ((999995591852432383352058670606 : Int)/10^30,(-2969221396842666900508042514 : Int)/10^30)
theorem v2771_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 69 5) 1) 14) v2771_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2771 : Material (34 : Basis) (69 : Basis) where
  plus := ![v2771_pa,v2771_pb,v2771_pg]
  minus := ![(Primitive.Addresses.material2771 1).one,v2771_mb,v2771_mg]
  upper := v2771_upper
  lower := (Primitive.Addresses.material2771 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2771_pa_checked.trans (by decide +kernel)
    · exact v2771_pb_checked.trans (by decide +kernel)
    · exact v2771_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 69 Primitive.Addresses.material2771
    · exact v2771_mb_checked.trans (by decide +kernel)
    · exact v2771_mg_checked.trans (by decide +kernel)
  upper_error := v2771_upper_checked
  lower_error := reuse_lower_error 34 69 Primitive.Addresses.material2771

def v2772_pa : Scalar.QComplex := ((999999209287135682637309955149 : Int)/10^30,(-1257547256928299924762406639 : Int)/10^30)
theorem v2772_pa_checked : Scalar.distance (sourceCoefficient 34 70 1 0) v2772_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2772_pb : Scalar.QComplex := ((-542603338703429037440166 : Int)/10^30,(-431477152584593365616404947 : Int)/10^30)
theorem v2772_pb_checked : Scalar.distance (sourceCoefficient 34 70 1 1) v2772_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2772_pg : Scalar.QComplex := ((-93086353353843411167430 : Int)/10^30,(117060580878891438985 : Int)/10^30)
theorem v2772_pg_checked : Scalar.distance (sourceCoefficient 34 70 1 2) v2772_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2772_mb : Scalar.QComplex := ((-914948486338346729122592 : Int)/10^30,(-431476523683686624473801394 : Int)/10^30)
theorem v2772_mb_checked : Scalar.distance (sourceCoefficient 34 70 3 1) v2772_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2772_mg : Scalar.QComplex := ((-93086217675530715384455 : Int)/10^30,(197389867782530249403 : Int)/10^30)
theorem v2772_mg_checked : Scalar.distance (sourceCoefficient 34 70 3 2) v2772_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2772_upper : Scalar.QComplex := ((999995549493299945988832021020 : Int)/10^30,(-2983453299969371920504486024 : Int)/10^30)
theorem v2772_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 70 5) 1) 14) v2772_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2772 : Material (34 : Basis) (70 : Basis) where
  plus := ![v2772_pa,v2772_pb,v2772_pg]
  minus := ![(Primitive.Addresses.material2772 1).one,v2772_mb,v2772_mg]
  upper := v2772_upper
  lower := (Primitive.Addresses.material2772 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2772_pa_checked.trans (by decide +kernel)
    · exact v2772_pb_checked.trans (by decide +kernel)
    · exact v2772_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 70 Primitive.Addresses.material2772
    · exact v2772_mb_checked.trans (by decide +kernel)
    · exact v2772_mg_checked.trans (by decide +kernel)
  upper_error := v2772_upper_checked
  lower_error := reuse_lower_error 34 70 Primitive.Addresses.material2772

def v2773_pa : Scalar.QComplex := ((999999178442700690120761546363 : Int)/10^30,(-1281840053853585286524107420 : Int)/10^30)
theorem v2773_pa_checked : Scalar.distance (sourceCoefficient 34 71 1 0) v2773_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2773_pb : Scalar.QComplex := ((-553085131026252985386146 : Int)/10^30,(-431477137083049093428047546 : Int)/10^30)
theorem v2773_pb_checked : Scalar.distance (sourceCoefficient 34 71 1 1) v2773_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2773_pg : Scalar.QComplex := ((-93086350246102191052633 : Int)/10^30,(119321910242283661715 : Int)/10^30)
theorem v2773_pg_checked : Scalar.distance (sourceCoefficient 34 71 1 2) v2773_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2773_mb : Scalar.QComplex := ((-925430261381185810445344 : Int)/10^30,(-431476499136833432023462515 : Int)/10^30)
theorem v2773_mb_checked : Scalar.distance (sourceCoefficient 34 71 3 1) v2773_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2773_mg : Scalar.QComplex := ((-93086212616365258310064 : Int)/10^30,(199651193622085496795 : Int)/10^30)
theorem v2773_mg_checked : Scalar.distance (sourceCoefficient 34 71 3 2) v2773_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2773_upper : Scalar.QComplex := ((999995476721747224914151936665 : Int)/10^30,(-3007746007478693282637960869 : Int)/10^30)
theorem v2773_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 71 5) 1) 14) v2773_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2773 : Material (34 : Basis) (71 : Basis) where
  plus := ![v2773_pa,v2773_pb,v2773_pg]
  minus := ![(Primitive.Addresses.material2773 1).one,v2773_mb,v2773_mg]
  upper := v2773_upper
  lower := (Primitive.Addresses.material2773 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2773_pa_checked.trans (by decide +kernel)
    · exact v2773_pb_checked.trans (by decide +kernel)
    · exact v2773_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 71 Primitive.Addresses.material2773
    · exact v2773_mb_checked.trans (by decide +kernel)
    · exact v2773_mg_checked.trans (by decide +kernel)
  upper_error := v2773_upper_checked
  lower_error := reuse_lower_error 34 71 Primitive.Addresses.material2773

def v2774_pa : Scalar.QComplex := ((999999144302536797695320714677 : Int)/10^30,(-1308202657919047658632918690 : Int)/10^30)
theorem v2774_pa_checked : Scalar.distance (sourceCoefficient 34 72 1 0) v2774_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2774_pb : Scalar.QComplex := ((-564459998060813800248808 : Int)/10^30,(-431477119876601308306588110 : Int)/10^30)
theorem v2774_pb_checked : Scalar.distance (sourceCoefficient 34 72 1 1) v2774_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2774_pg : Scalar.QComplex := ((-93086346801060258045679 : Int)/10^30,(121775910504458966887 : Int)/10^30)
theorem v2774_pg_checked : Scalar.distance (sourceCoefficient 34 72 1 2) v2774_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2774_mb : Scalar.QComplex := ((-936805109331974282317012 : Int)/10^30,(-431476472114394107816485089 : Int)/10^30)
theorem v2774_mb_checked : Scalar.distance (sourceCoefficient 34 72 3 1) v2774_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2774_mg : Scalar.QComplex := ((-93086207053632905861341 : Int)/10^30,(202105189997608321751 : Int)/10^30)
theorem v2774_mg_checked : Scalar.distance (sourceCoefficient 34 72 3 2) v2774_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2774_upper : Scalar.QComplex := ((999995397082171160023079360528 : Int)/10^30,(-3034108513357327961398490395 : Int)/10^30)
theorem v2774_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 72 5) 1) 14) v2774_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2774 : Material (34 : Basis) (72 : Basis) where
  plus := ![v2774_pa,v2774_pb,v2774_pg]
  minus := ![(Primitive.Addresses.material2774 1).one,v2774_mb,v2774_mg]
  upper := v2774_upper
  lower := (Primitive.Addresses.material2774 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2774_pa_checked.trans (by decide +kernel)
    · exact v2774_pb_checked.trans (by decide +kernel)
    · exact v2774_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 72 Primitive.Addresses.material2774
    · exact v2774_mb_checked.trans (by decide +kernel)
    · exact v2774_mg_checked.trans (by decide +kernel)
  upper_error := v2774_upper_checked
  lower_error := reuse_lower_error 34 72 Primitive.Addresses.material2774

def v2775_pa : Scalar.QComplex := ((999999131895841357916033508118 : Int)/10^30,(-1317652292404691140301034037 : Int)/10^30)
theorem v2775_pa_checked : Scalar.distance (sourceCoefficient 34 73 1 0) v2775_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2775_pb : Scalar.QComplex := ((-568537301420121580317575 : Int)/10^30,(-431477113611631701423664048 : Int)/10^30)
theorem v2775_pb_checked : Scalar.distance (sourceCoefficient 34 73 1 1) v2775_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2775_pg : Scalar.QComplex := ((-93086345547814344597230 : Int)/10^30,(122655543080439814708 : Int)/10^30)
theorem v2775_pg_checked : Scalar.distance (sourceCoefficient 34 73 1 2) v2775_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2775_mb : Scalar.QComplex := ((-940882405766729072763211 : Int)/10^30,(-431476462330897669511909049 : Int)/10^30)
theorem v2775_mb_checked : Scalar.distance (sourceCoefficient 34 73 3 1) v2775_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2775_mg : Scalar.QComplex := ((-93086205041304163162714 : Int)/10^30,(202984821164566981134 : Int)/10^30)
theorem v2775_mg_checked : Scalar.distance (sourceCoefficient 34 73 3 2) v2775_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2775_upper : Scalar.QComplex := ((999995368366282340482565105029 : Int)/10^30,(-3043558112356020106301937160 : Int)/10^30)
theorem v2775_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 73 5) 1) 14) v2775_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2775 : Material (34 : Basis) (73 : Basis) where
  plus := ![v2775_pa,v2775_pb,v2775_pg]
  minus := ![(Primitive.Addresses.material2775 1).one,v2775_mb,v2775_mg]
  upper := v2775_upper
  lower := (Primitive.Addresses.material2775 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2775_pa_checked.trans (by decide +kernel)
    · exact v2775_pb_checked.trans (by decide +kernel)
    · exact v2775_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 73 Primitive.Addresses.material2775
    · exact v2775_mb_checked.trans (by decide +kernel)
    · exact v2775_mg_checked.trans (by decide +kernel)
  upper_error := v2775_upper_checked
  lower_error := reuse_lower_error 34 73 Primitive.Addresses.material2775

def v2776_pa : Scalar.QComplex := ((999999117828487446342938528819 : Int)/10^30,(-1328285453839172538928284466 : Int)/10^30)
theorem v2776_pa_checked : Scalar.distance (sourceCoefficient 34 74 1 0) v2776_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2776_pb : Scalar.QComplex := ((-573125269824115046599767 : Int)/10^30,(-431477106500574725624020492 : Int)/10^30)
theorem v2776_pb_checked : Scalar.distance (sourceCoefficient 34 74 1 1) v2776_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2776_pg : Scalar.QComplex := ((-93086344126009122439250 : Int)/10^30,(123645345930047259351 : Int)/10^30)
theorem v2776_pg_checked : Scalar.distance (sourceCoefficient 34 74 1 2) v2776_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2776_mb : Scalar.QComplex := ((-945470366325890321726258 : Int)/10^30,(-431476451260633243263692942 : Int)/10^30)
theorem v2776_mb_checked : Scalar.distance (sourceCoefficient 34 74 3 1) v2776_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2776_mg : Scalar.QComplex := ((-93086202765344190262067 : Int)/10^30,(203974622418671717651 : Int)/10^30)
theorem v2776_mg_checked : Scalar.distance (sourceCoefficient 34 74 3 2) v2776_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2776_upper : Scalar.QComplex := ((999995335947077377535797610064 : Int)/10^30,(-3054191233674679936155561487 : Int)/10^30)
theorem v2776_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 74 5) 1) 14) v2776_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2776 : Material (34 : Basis) (74 : Basis) where
  plus := ![v2776_pa,v2776_pb,v2776_pg]
  minus := ![(Primitive.Addresses.material2776 1).one,v2776_mb,v2776_mg]
  upper := v2776_upper
  lower := (Primitive.Addresses.material2776 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2776_pa_checked.trans (by decide +kernel)
    · exact v2776_pb_checked.trans (by decide +kernel)
    · exact v2776_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 74 Primitive.Addresses.material2776
    · exact v2776_mb_checked.trans (by decide +kernel)
    · exact v2776_mg_checked.trans (by decide +kernel)
  upper_error := v2776_upper_checked
  lower_error := reuse_lower_error 34 74 Primitive.Addresses.material2776

def v2777_pa : Scalar.QComplex := ((999999098040023251651321637648 : Int)/10^30,(-1343100569564653896563191971 : Int)/10^30)
theorem v2777_pa_checked : Scalar.distance (sourceCoefficient 34 75 1 0) v2777_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2777_pb : Scalar.QComplex := ((-579517656743944564650446 : Int)/10^30,(-431477096484334181543366005 : Int)/10^30)
theorem v2777_pb_checked : Scalar.distance (sourceCoefficient 34 75 1 1) v2777_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2777_pg : Scalar.QComplex := ((-93086342124544668638335 : Int)/10^30,(125024431893199862478 : Int)/10^30)
theorem v2777_pg_checked : Scalar.distance (sourceCoefficient 34 75 1 2) v2777_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2777_mb : Scalar.QComplex := ((-951862742221977568196175 : Int)/10^30,(-431476435728054419293712690 : Int)/10^30)
theorem v2777_mb_checked : Scalar.distance (sourceCoefficient 34 75 3 1) v2777_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2777_mg : Scalar.QComplex := ((-93086199573791407223228 : Int)/10^30,(205353706141153908336 : Int)/10^30)
theorem v2777_mg_checked : Scalar.distance (sourceCoefficient 34 75 3 2) v2777_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2777_upper : Scalar.QComplex := ((999995290589096930055991732600 : Int)/10^30,(-3069006293181692721839626992 : Int)/10^30)
theorem v2777_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 75 5) 1) 14) v2777_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2777 : Material (34 : Basis) (75 : Basis) where
  plus := ![v2777_pa,v2777_pb,v2777_pg]
  minus := ![(Primitive.Addresses.material2777 1).one,v2777_mb,v2777_mg]
  upper := v2777_upper
  lower := (Primitive.Addresses.material2777 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2777_pa_checked.trans (by decide +kernel)
    · exact v2777_pb_checked.trans (by decide +kernel)
    · exact v2777_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 75 Primitive.Addresses.material2777
    · exact v2777_mb_checked.trans (by decide +kernel)
    · exact v2777_mg_checked.trans (by decide +kernel)
  upper_error := v2777_upper_checked
  lower_error := reuse_lower_error 34 75 Primitive.Addresses.material2777

def v2778_pa : Scalar.QComplex := ((999999081267780061925652153198 : Int)/10^30,(-1355530743217304069769875712 : Int)/10^30)
theorem v2778_pa_checked : Scalar.distance (sourceCoefficient 34 76 1 0) v2778_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2778_pb : Scalar.QComplex := ((-584880995103976382256859 : Int)/10^30,(-431477087983093883662262550 : Int)/10^30)
theorem v2778_pb_checked : Scalar.distance (sourceCoefficient 34 76 1 1) v2778_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2778_pg : Scalar.QComplex := ((-93086340426886982714638 : Int)/10^30,(126181512149257861502 : Int)/10^30)
theorem v2778_pg_checked : Scalar.distance (sourceCoefficient 34 76 1 2) v2778_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2778_mb : Scalar.QComplex := ((-957226071248805902269069 : Int)/10^30,(-431476422598497837898202727 : Int)/10^30)
theorem v2778_mb_checked : Scalar.distance (sourceCoefficient 34 76 3 1) v2778_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2778_mg : Scalar.QComplex := ((-93086196877626205397230 : Int)/10^30,(206510784501375923561 : Int)/10^30)
theorem v2778_mg_checked : Scalar.distance (sourceCoefficient 34 76 3 2) v2778_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2778_upper : Scalar.QComplex := ((999995252363526652687147210586 : Int)/10^30,(-3081436419373689210740960047 : Int)/10^30)
theorem v2778_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 76 5) 1) 14) v2778_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2778 : Material (34 : Basis) (76 : Basis) where
  plus := ![v2778_pa,v2778_pb,v2778_pg]
  minus := ![(Primitive.Addresses.material2778 1).one,v2778_mb,v2778_mg]
  upper := v2778_upper
  lower := (Primitive.Addresses.material2778 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2778_pa_checked.trans (by decide +kernel)
    · exact v2778_pb_checked.trans (by decide +kernel)
    · exact v2778_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 76 Primitive.Addresses.material2778
    · exact v2778_mb_checked.trans (by decide +kernel)
    · exact v2778_mg_checked.trans (by decide +kernel)
  upper_error := v2778_upper_checked
  lower_error := reuse_lower_error 34 76 Primitive.Addresses.material2778

def v2779_pa : Scalar.QComplex := ((999999077362837589395548668059 : Int)/10^30,(-1358408433999831819938401087 : Int)/10^30)
theorem v2779_pa_checked : Scalar.distance (sourceCoefficient 34 77 1 0) v2779_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2779_pb : Scalar.QComplex := ((-586122653481754711912193 : Int)/10^30,(-431477086002313089860378998 : Int)/10^30)
theorem v2779_pb_checked : Scalar.distance (sourceCoefficient 34 77 1 1) v2779_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2779_pg : Scalar.QComplex := ((-93086340031472799024035 : Int)/10^30,(126449386055831559485 : Int)/10^30)
theorem v2779_pg_checked : Scalar.distance (sourceCoefficient 34 77 1 2) v2779_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2779_mb : Scalar.QComplex := ((-958467727454933457290585 : Int)/10^30,(-431476419546222523826241214 : Int)/10^30)
theorem v2779_mb_checked : Scalar.distance (sourceCoefficient 34 77 3 1) v2779_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2779_mg : Scalar.QComplex := ((-93086196251049052157191 : Int)/10^30,(206778657966983291954 : Int)/10^30)
theorem v2779_mg_checked : Scalar.distance (sourceCoefficient 34 77 3 2) v2779_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2779_upper : Scalar.QComplex := ((999995243491956767535738955204 : Int)/10^30,(-3084314099130658123666414757 : Int)/10^30)
theorem v2779_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 77 5) 1) 14) v2779_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2779 : Material (34 : Basis) (77 : Basis) where
  plus := ![v2779_pa,v2779_pb,v2779_pg]
  minus := ![(Primitive.Addresses.material2779 1).one,v2779_mb,v2779_mg]
  upper := v2779_upper
  lower := (Primitive.Addresses.material2779 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2779_pa_checked.trans (by decide +kernel)
    · exact v2779_pb_checked.trans (by decide +kernel)
    · exact v2779_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 77 Primitive.Addresses.material2779
    · exact v2779_mb_checked.trans (by decide +kernel)
    · exact v2779_mg_checked.trans (by decide +kernel)
  upper_error := v2779_upper_checked
  lower_error := reuse_lower_error 34 77 Primitive.Addresses.material2779

def v2780_pa : Scalar.QComplex := ((999999053713291888614353006368 : Int)/10^30,(-1375708007087346041265301782 : Int)/10^30)
theorem v2780_pa_checked : Scalar.distance (sourceCoefficient 34 78 1 0) v2780_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2780_pb : Scalar.QComplex := ((-593587027271970008777551 : Int)/10^30,(-431477073994211461801592811 : Int)/10^30)
theorem v2780_pb_checked : Scalar.distance (sourceCoefficient 34 78 1 1) v2780_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2780_pg : Scalar.QComplex := ((-93086337635440367552794 : Int)/10^30,(128059741216742441289 : Int)/10^30)
theorem v2780_pg_checked : Scalar.distance (sourceCoefficient 34 78 1 2) v2780_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2780_mb : Scalar.QComplex := ((-965932088103370373130214 : Int)/10^30,(-431476401096706968892502163 : Int)/10^30)
theorem v2780_mb_checked : Scalar.distance (sourceCoefficient 34 78 3 1) v2780_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2780_mg : Scalar.QComplex := ((-93086192465353536676329 : Int)/10^30,(208389010460617275419 : Int)/10^30)
theorem v2780_mg_checked : Scalar.distance (sourceCoefficient 34 78 3 2) v2780_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2780_upper : Scalar.QComplex := ((999995189984952545936227937101 : Int)/10^30,(-3101613605635519972224675458 : Int)/10^30)
theorem v2780_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 78 5) 1) 14) v2780_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2780 : Material (34 : Basis) (78 : Basis) where
  plus := ![v2780_pa,v2780_pb,v2780_pg]
  minus := ![(Primitive.Addresses.material2780 1).one,v2780_mb,v2780_mg]
  upper := v2780_upper
  lower := (Primitive.Addresses.material2780 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2780_pa_checked.trans (by decide +kernel)
    · exact v2780_pb_checked.trans (by decide +kernel)
    · exact v2780_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 78 Primitive.Addresses.material2780
    · exact v2780_mb_checked.trans (by decide +kernel)
    · exact v2780_mg_checked.trans (by decide +kernel)
  upper_error := v2780_upper_checked
  lower_error := reuse_lower_error 34 78 Primitive.Addresses.material2780

def v2781_pa : Scalar.QComplex := ((999999046025304902691004997821 : Int)/10^30,(-1381285082858313902815318012 : Int)/10^30)
theorem v2781_pa_checked : Scalar.distance (sourceCoefficient 34 79 1 0) v2781_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2781_pb : Scalar.QComplex := ((-595993409068265033241967 : Int)/10^30,(-431477070086312254356900860 : Int)/10^30)
theorem v2781_pb_checked : Scalar.distance (sourceCoefficient 34 79 1 1) v2781_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2781_pg : Scalar.QComplex := ((-93086336856074050979921 : Int)/10^30,(128578891178227672491 : Int)/10^30)
theorem v2781_pg_checked : Scalar.distance (sourceCoefficient 34 79 1 2) v2781_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2781_mb : Scalar.QComplex := ((-968338465631318466974836 : Int)/10^30,(-431476395112210105747551057 : Int)/10^30)
theorem v2781_mb_checked : Scalar.distance (sourceCoefficient 34 79 3 1) v2781_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2781_mg : Scalar.QComplex := ((-93086191237984475181697 : Int)/10^30,(208908159556241219789 : Int)/10^30)
theorem v2781_mg_checked : Scalar.distance (sourceCoefficient 34 79 3 2) v2781_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2781_upper : Scalar.QComplex := ((999995172671450178037562531854 : Int)/10^30,(-3107190659831320513285939741 : Int)/10^30)
theorem v2781_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 79 5) 1) 14) v2781_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2781 : Material (34 : Basis) (79 : Basis) where
  plus := ![v2781_pa,v2781_pb,v2781_pg]
  minus := ![(Primitive.Addresses.material2781 1).one,v2781_mb,v2781_mg]
  upper := v2781_upper
  lower := (Primitive.Addresses.material2781 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2781_pa_checked.trans (by decide +kernel)
    · exact v2781_pb_checked.trans (by decide +kernel)
    · exact v2781_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 79 Primitive.Addresses.material2781
    · exact v2781_mb_checked.trans (by decide +kernel)
    · exact v2781_mg_checked.trans (by decide +kernel)
  upper_error := v2781_upper_checked
  lower_error := reuse_lower_error 34 79 Primitive.Addresses.material2781

def v2782_pa : Scalar.QComplex := ((999999033953666713626957394007 : Int)/10^30,(-1389997026373519990907636527 : Int)/10^30)
theorem v2782_pa_checked : Scalar.distance (sourceCoefficient 34 80 1 0) v2782_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2782_pb : Scalar.QComplex := ((-599752415221909632625409 : Int)/10^30,(-431477063945979060570556174 : Int)/10^30)
theorem v2782_pb_checked : Scalar.distance (sourceCoefficient 34 80 1 1) v2782_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2782_pg : Scalar.QComplex := ((-93086335631867232077864 : Int)/10^30,(129389854720897608234 : Int)/10^30)
theorem v2782_pg_checked : Scalar.distance (sourceCoefficient 34 80 1 2) v2782_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2782_mb : Scalar.QComplex := ((-972097465086482284391725 : Int)/10^30,(-431476385728026187045065014 : Int)/10^30)
theorem v2782_mb_checked : Scalar.distance (sourceCoefficient 34 80 3 1) v2782_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2782_mg : Scalar.QComplex := ((-93086189313953099225745 : Int)/10^30,(209719121740517017246 : Int)/10^30)
theorem v2782_mg_checked : Scalar.distance (sourceCoefficient 34 80 3 2) v2782_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2782_upper : Scalar.QComplex := ((999995145563805802356747000529 : Int)/10^30,(-3115902569536557728389659626 : Int)/10^30)
theorem v2782_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 80 5) 1) 14) v2782_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2782 : Material (34 : Basis) (80 : Basis) where
  plus := ![v2782_pa,v2782_pb,v2782_pg]
  minus := ![(Primitive.Addresses.material2782 1).one,v2782_mb,v2782_mg]
  upper := v2782_upper
  lower := (Primitive.Addresses.material2782 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2782_pa_checked.trans (by decide +kernel)
    · exact v2782_pb_checked.trans (by decide +kernel)
    · exact v2782_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 80 Primitive.Addresses.material2782
    · exact v2782_mb_checked.trans (by decide +kernel)
    · exact v2782_mg_checked.trans (by decide +kernel)
  upper_error := v2782_upper_checked
  lower_error := reuse_lower_error 34 80 Primitive.Addresses.material2782

def v2783_pa : Scalar.QComplex := ((999998997147008671668271509107 : Int)/10^30,(-1416229139984960640196460946 : Int)/10^30)
theorem v2783_pa_checked : Scalar.distance (sourceCoefficient 34 81 1 0) v2783_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2783_pb : Scalar.QComplex := ((-611070977451913955887795 : Int)/10^30,(-431477045193439137142713835 : Int)/10^30)
theorem v2783_pb_checked : Scalar.distance (sourceCoefficient 34 81 1 1) v2783_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2783_pg : Scalar.QComplex := ((-93086331895942078391871 : Int)/10^30,(131831707973167353147 : Int)/10^30)
theorem v2783_pg_checked : Scalar.distance (sourceCoefficient 34 81 1 2) v2783_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2783_mb : Scalar.QComplex := ((-983416006919471234702777 : Int)/10^30,(-431476357208083810670458782 : Int)/10^30)
theorem v2783_mb_checked : Scalar.distance (sourceCoefficient 34 81 3 1) v2783_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2783_mg : Scalar.QComplex := ((-93086183470819956874582 : Int)/10^30,(212160970859638050324 : Int)/10^30)
theorem v2783_mg_checked : Scalar.distance (sourceCoefficient 34 81 3 2) v2783_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2783_upper : Scalar.QComplex := ((999995063482954245002214824698 : Int)/10^30,(-3142134580553393887475288052 : Int)/10^30)
theorem v2783_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 81 5) 1) 14) v2783_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2783 : Material (34 : Basis) (81 : Basis) where
  plus := ![v2783_pa,v2783_pb,v2783_pg]
  minus := ![(Primitive.Addresses.material2783 1).one,v2783_mb,v2783_mg]
  upper := v2783_upper
  lower := (Primitive.Addresses.material2783 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2783_pa_checked.trans (by decide +kernel)
    · exact v2783_pb_checked.trans (by decide +kernel)
    · exact v2783_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 81 Primitive.Addresses.material2783
    · exact v2783_mb_checked.trans (by decide +kernel)
    · exact v2783_mg_checked.trans (by decide +kernel)
  upper_error := v2783_upper_checked
  lower_error := reuse_lower_error 34 81 Primitive.Addresses.material2783

def v2784_pa : Scalar.QComplex := ((999998983019920028868940151873 : Int)/10^30,(-1426169388850349382511439182 : Int)/10^30)
theorem v2784_pa_checked : Scalar.distance (sourceCoefficient 34 82 1 0) v2784_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2784_pb : Scalar.QComplex := ((-615359969373472114623447 : Int)/10^30,(-431477037984028736802078070 : Int)/10^30)
theorem v2784_pb_checked : Scalar.distance (sourceCoefficient 34 82 1 1) v2784_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2784_pg : Scalar.QComplex := ((-93086330460747285731509 : Int)/10^30,(132757010034760300021 : Int)/10^30)
theorem v2784_pg_checked : Scalar.distance (sourceCoefficient 34 82 1 2) v2784_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2784_mb : Scalar.QComplex := ((-987704991022645208725134 : Int)/10^30,(-431476346297469235443486100 : Int)/10^30)
theorem v2784_mb_checked : Scalar.distance (sourceCoefficient 34 82 3 1) v2784_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2784_mg : Scalar.QComplex := ((-93086181237131693505960 : Int)/10^30,(213086271338190283982 : Int)/10^30)
theorem v2784_mg_checked : Scalar.distance (sourceCoefficient 34 82 3 2) v2784_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2784_upper : Scalar.QComplex := ((999995032199918873513772457403 : Int)/10^30,(-3152074790231876210448084449 : Int)/10^30)
theorem v2784_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 82 5) 1) 14) v2784_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2784 : Material (34 : Basis) (82 : Basis) where
  plus := ![v2784_pa,v2784_pb,v2784_pg]
  minus := ![(Primitive.Addresses.material2784 1).one,v2784_mb,v2784_mg]
  upper := v2784_upper
  lower := (Primitive.Addresses.material2784 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2784_pa_checked.trans (by decide +kernel)
    · exact v2784_pb_checked.trans (by decide +kernel)
    · exact v2784_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 82 Primitive.Addresses.material2784
    · exact v2784_mb_checked.trans (by decide +kernel)
    · exact v2784_mg_checked.trans (by decide +kernel)
  upper_error := v2784_upper_checked
  lower_error := reuse_lower_error 34 82 Primitive.Addresses.material2784

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
