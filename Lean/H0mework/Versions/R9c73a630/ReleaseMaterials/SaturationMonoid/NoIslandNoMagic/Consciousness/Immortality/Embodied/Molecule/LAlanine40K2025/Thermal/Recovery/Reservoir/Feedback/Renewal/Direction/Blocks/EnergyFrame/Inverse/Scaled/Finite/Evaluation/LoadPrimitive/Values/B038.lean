import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B025
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B026

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v609_pa : Scalar.QComplex := ((999999934822558439900193680440 : Int)/10^30,(-361046920596341223411171881 : Int)/10^30)
theorem v609_pa_checked : Scalar.distance (sourceCoefficient 6 49 1 0) v609_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v609_pb : Scalar.QComplex := ((-155783614088124672165342 : Int)/10^30,(-431477448075833134528837672 : Int)/10^30)
theorem v609_pb_checked : Scalar.distance (sourceCoefficient 6 49 1 1) v609_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v609_pg : Scalar.QComplex := ((-93086418997052918070021 : Int)/10^30,(33608567118747133435 : Int)/10^30)
theorem v609_pg_checked : Scalar.distance (sourceCoefficient 6 49 1 2) v609_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v609_mb : Scalar.QComplex := ((-528129160749335862042271 : Int)/10^30,(-431477152982816997828456337 : Int)/10^30)
theorem v609_mb_checked : Scalar.distance (sourceCoefficient 6 49 3 1) v609_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v609_mg : Scalar.QComplex := ((-93086355334045116148414 : Int)/10^30,(113937941742517956246 : Int)/10^30)
theorem v609_mg_checked : Scalar.distance (sourceCoefficient 6 49 3 2) v609_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v609_upper : Scalar.QComplex := ((999997822305892737229699725199 : Int)/10^30,(-2086955551077673478094467491 : Int)/10^30)
theorem v609_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 49 5) 1) 14) v609_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material609 : Material (6 : Basis) (49 : Basis) where
  plus := ![v609_pa,v609_pb,v609_pg]
  minus := ![(Primitive.Addresses.material609 1).one,v609_mb,v609_mg]
  upper := v609_upper
  lower := (Primitive.Addresses.material609 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v609_pa_checked.trans (by decide +kernel)
    · exact v609_pb_checked.trans (by decide +kernel)
    · exact v609_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 49 Primitive.Addresses.material609
    · exact v609_mb_checked.trans (by decide +kernel)
    · exact v609_mg_checked.trans (by decide +kernel)
  upper_error := v609_upper_checked
  lower_error := reuse_lower_error 6 49 Primitive.Addresses.material609

def v610_pa : Scalar.QComplex := ((999999933889445092836848511117 : Int)/10^30,(-363622201527520638882076443 : Int)/10^30)
theorem v610_pa_checked : Scalar.distance (sourceCoefficient 6 50 1 0) v610_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v610_pb : Scalar.QComplex := ((-156894789698332373888846 : Int)/10^30,(-431477447380385627730467383 : Int)/10^30)
theorem v610_pb_checked : Scalar.distance (sourceCoefficient 6 50 1 1) v610_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v610_pg : Scalar.QComplex := ((-93086418878605327575852 : Int)/10^30,(33848290802680715806 : Int)/10^30)
theorem v610_pg_checked : Scalar.distance (sourceCoefficient 6 50 1 2) v610_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v610_mb : Scalar.QComplex := ((-529240335345662224277312 : Int)/10^30,(-431477151328475243859437540 : Int)/10^30)
theorem v610_mb_checked : Scalar.distance (sourceCoefficient 6 50 3 1) v610_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v610_mg : Scalar.QComplex := ((-93086355008726827276945 : Int)/10^30,(114177665234976519260 : Int)/10^30)
theorem v610_mg_checked : Scalar.distance (sourceCoefficient 6 50 3 2) v610_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v610_upper : Scalar.QComplex := ((999997816928079520374480171685 : Int)/10^30,(-2089530826562805474672492373 : Int)/10^30)
theorem v610_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 50 5) 1) 14) v610_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material610 : Material (6 : Basis) (50 : Basis) where
  plus := ![v610_pa,v610_pb,v610_pg]
  minus := ![(Primitive.Addresses.material610 1).one,v610_mb,v610_mg]
  upper := v610_upper
  lower := (Primitive.Addresses.material610 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v610_pa_checked.trans (by decide +kernel)
    · exact v610_pb_checked.trans (by decide +kernel)
    · exact v610_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 50 Primitive.Addresses.material610
    · exact v610_mb_checked.trans (by decide +kernel)
    · exact v610_mg_checked.trans (by decide +kernel)
  upper_error := v610_upper_checked
  lower_error := reuse_lower_error 6 50 Primitive.Addresses.material610

def v611_pa : Scalar.QComplex := ((999999929716950219583244585677 : Int)/10^30,(-374921451268297563107588418 : Int)/10^30)
theorem v611_pa_checked : Scalar.distance (sourceCoefficient 6 51 1 0) v611_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v611_pb : Scalar.QComplex := ((-161770160970178096976982 : Int)/10^30,(-431477444283958758301739972 : Int)/10^30)
theorem v611_pb_checked : Scalar.distance (sourceCoefficient 6 51 1 1) v611_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v611_pg : Scalar.QComplex := ((-93086418350394337214500 : Int)/10^30,(34900097514183021463 : Int)/10^30)
theorem v611_pg_checked : Scalar.distance (sourceCoefficient 6 51 1 2) v611_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v611_mb : Scalar.QComplex := ((-534115702130107476955141 : Int)/10^30,(-431477144024823698340032522 : Int)/10^30)
theorem v611_mb_checked : Scalar.distance (sourceCoefficient 6 51 3 1) v611_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v611_mg : Scalar.QComplex := ((-93086353572854213181965 : Int)/10^30,(115229471099020821342 : Int)/10^30)
theorem v611_mg_checked : Scalar.distance (sourceCoefficient 6 51 3 2) v611_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v611_upper : Scalar.QComplex := ((999997793254110868910037611618 : Int)/10^30,(-2100830052273329587665585772 : Int)/10^30)
theorem v611_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 51 5) 1) 14) v611_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material611 : Material (6 : Basis) (51 : Basis) where
  plus := ![v611_pa,v611_pb,v611_pg]
  minus := ![(Primitive.Addresses.material611 1).one,v611_mb,v611_mg]
  upper := v611_upper
  lower := (Primitive.Addresses.material611 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v611_pa_checked.trans (by decide +kernel)
    · exact v611_pb_checked.trans (by decide +kernel)
    · exact v611_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 51 Primitive.Addresses.material611
    · exact v611_mb_checked.trans (by decide +kernel)
    · exact v611_mg_checked.trans (by decide +kernel)
  upper_error := v611_upper_checked
  lower_error := reuse_lower_error 6 51 Primitive.Addresses.material611

def v612_pa : Scalar.QComplex := ((999999920355448490564718338825 : Int)/10^30,(-399110381568327508449679300 : Int)/10^30)
theorem v612_pa_checked : Scalar.distance (sourceCoefficient 6 52 1 0) v612_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v612_pb : Scalar.QComplex := ((-172207138397526966176813 : Int)/10^30,(-431477437408339836763083304 : Int)/10^30)
theorem v612_pb_checked : Scalar.distance (sourceCoefficient 6 52 1 1) v612_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v612_pg : Scalar.QComplex := ((-93086417173011159645672 : Int)/10^30,(37151758435684136783 : Int)/10^30)
theorem v612_pg_checked : Scalar.distance (sourceCoefficient 6 52 1 2) v612_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v612_mb : Scalar.QComplex := ((-544552669737943193613614 : Int)/10^30,(-431477128142565881120188910 : Int)/10^30)
theorem v612_mb_checked : Scalar.distance (sourceCoefficient 6 52 3 1) v612_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v612_mg : Scalar.QComplex := ((-93086350452389509794589 : Int)/10^30,(117481130166097014727 : Int)/10^30)
theorem v612_mg_checked : Scalar.distance (sourceCoefficient 6 52 3 2) v612_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v612_upper : Scalar.QComplex := ((999997742144723787512058034359 : Int)/10^30,(-2125018930389686566982537091 : Int)/10^30)
theorem v612_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 52 5) 1) 14) v612_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material612 : Material (6 : Basis) (52 : Basis) where
  plus := ![v612_pa,v612_pb,v612_pg]
  minus := ![(Primitive.Addresses.material612 1).one,v612_mb,v612_mg]
  upper := v612_upper
  lower := (Primitive.Addresses.material612 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v612_pa_checked.trans (by decide +kernel)
    · exact v612_pb_checked.trans (by decide +kernel)
    · exact v612_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 52 Primitive.Addresses.material612
    · exact v612_mb_checked.trans (by decide +kernel)
    · exact v612_mg_checked.trans (by decide +kernel)
  upper_error := v612_upper_checked
  lower_error := reuse_lower_error 6 52 Primitive.Addresses.material612

def v613_pa : Scalar.QComplex := ((999999918870811565004438475993 : Int)/10^30,(-402813071148449584329598655 : Int)/10^30)
theorem v613_pa_checked : Scalar.distance (sourceCoefficient 6 53 1 0) v613_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v613_pb : Scalar.QComplex := ((-173804765358438190128988 : Int)/10^30,(-431477436326156318780054593 : Int)/10^30)
theorem v613_pb_checked : Scalar.distance (sourceCoefficient 6 53 1 1) v613_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v613_pg : Scalar.QComplex := ((-93086416987176912615495 : Int)/10^30,(37496428550864757242 : Int)/10^30)
theorem v613_pg_checked : Scalar.distance (sourceCoefficient 6 53 1 2) v613_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v613_mb : Scalar.QComplex := ((-546150295170109248576397 : Int)/10^30,(-431477125681702653264400707 : Int)/10^30)
theorem v613_mb_checked : Scalar.distance (sourceCoefficient 6 53 3 1) v613_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v613_mg : Scalar.QComplex := ((-93086349969120545923854 : Int)/10^30,(117825799992574613579 : Int)/10^30)
theorem v613_mg_checked : Scalar.distance (sourceCoefficient 6 53 3 2) v613_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v613_upper : Scalar.QComplex := ((999997734269582763228138005965 : Int)/10^30,(-2128721611892738813434909921 : Int)/10^30)
theorem v613_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 53 5) 1) 14) v613_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material613 : Material (6 : Basis) (53 : Basis) where
  plus := ![v613_pa,v613_pb,v613_pg]
  minus := ![(Primitive.Addresses.material613 1).one,v613_mb,v613_mg]
  upper := v613_upper
  lower := (Primitive.Addresses.material613 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v613_pa_checked.trans (by decide +kernel)
    · exact v613_pb_checked.trans (by decide +kernel)
    · exact v613_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 53 Primitive.Addresses.material613
    · exact v613_mb_checked.trans (by decide +kernel)
    · exact v613_mg_checked.trans (by decide +kernel)
  upper_error := v613_upper_checked
  lower_error := reuse_lower_error 6 53 Primitive.Addresses.material613

def v614_pa : Scalar.QComplex := ((999999918110756195770967515372 : Int)/10^30,(-404695540996697681851628566 : Int)/10^30)
theorem v614_pa_checked : Scalar.distance (sourceCoefficient 6 54 1 0) v614_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v614_pb : Scalar.QComplex := ((-174617008597253960794637 : Int)/10^30,(-431477435772943312898314692 : Int)/10^30)
theorem v614_pb_checked : Scalar.distance (sourceCoefficient 6 54 1 1) v614_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v614_pg : Scalar.QComplex := ((-93086416892126744989748 : Int)/10^30,(37671660928507197025 : Int)/10^30)
theorem v614_pg_checked : Scalar.distance (sourceCoefficient 6 54 1 2) v614_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v614_mb : Scalar.QComplex := ((-546962537629091831794014 : Int)/10^30,(-431477124427560520348621608 : Int)/10^30)
theorem v614_mb_checked : Scalar.distance (sourceCoefficient 6 54 3 1) v614_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v614_mg : Scalar.QComplex := ((-93086349722852763957521 : Int)/10^30,(118001032222946016890 : Int)/10^30)
theorem v614_mg_checked : Scalar.distance (sourceCoefficient 6 54 3 2) v614_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v614_upper : Scalar.QComplex := ((999997730260556344262242402409 : Int)/10^30,(-2130604077625482586820845098 : Int)/10^30)
theorem v614_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 54 5) 1) 14) v614_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material614 : Material (6 : Basis) (54 : Basis) where
  plus := ![v614_pa,v614_pb,v614_pg]
  minus := ![(Primitive.Addresses.material614 1).one,v614_mb,v614_mg]
  upper := v614_upper
  lower := (Primitive.Addresses.material614 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v614_pa_checked.trans (by decide +kernel)
    · exact v614_pb_checked.trans (by decide +kernel)
    · exact v614_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 54 Primitive.Addresses.material614
    · exact v614_mb_checked.trans (by decide +kernel)
    · exact v614_mg_checked.trans (by decide +kernel)
  upper_error := v614_upper_checked
  lower_error := reuse_lower_error 6 54 Primitive.Addresses.material614

def v615_pa : Scalar.QComplex := ((999999911783558339801694700232 : Int)/10^30,(-420039135722203903561017019 : Int)/10^30)
theorem v615_pa_checked : Scalar.distance (sourceCoefficient 6 55 1 0) v615_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v615_pb : Scalar.QComplex := ((-181237423267879748745876 : Int)/10^30,(-431477431187797506744192681 : Int)/10^30)
theorem v615_pb_checked : Scalar.distance (sourceCoefficient 6 55 1 1) v615_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v615_pg : Scalar.QComplex := ((-93086416103041752819899 : Int)/10^30,(39099941216656785058 : Int)/10^30)
theorem v615_pg_checked : Scalar.distance (sourceCoefficient 6 55 1 2) v615_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v615_mb : Scalar.QComplex := ((-553582945877860346563857 : Int)/10^30,(-431477114129296733111864652 : Int)/10^30)
theorem v615_mb_checked : Scalar.distance (sourceCoefficient 6 55 3 1) v615_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v615_mg : Scalar.QComplex := ((-93086347701226504283217 : Int)/10^30,(119429311298336768837 : Int)/10^30)
theorem v615_mg_checked : Scalar.distance (sourceCoefficient 6 55 3 2) v615_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v615_upper : Scalar.QComplex := ((999997697451715375727295318411 : Int)/10^30,(-2145947638578337349638527621 : Int)/10^30)
theorem v615_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 55 5) 1) 14) v615_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material615 : Material (6 : Basis) (55 : Basis) where
  plus := ![v615_pa,v615_pb,v615_pg]
  minus := ![(Primitive.Addresses.material615 1).one,v615_mb,v615_mg]
  upper := v615_upper
  lower := (Primitive.Addresses.material615 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v615_pa_checked.trans (by decide +kernel)
    · exact v615_pb_checked.trans (by decide +kernel)
    · exact v615_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 55 Primitive.Addresses.material615
    · exact v615_mb_checked.trans (by decide +kernel)
    · exact v615_mg_checked.trans (by decide +kernel)
  upper_error := v615_upper_checked
  lower_error := reuse_lower_error 6 55 Primitive.Addresses.material615

def v616_pa : Scalar.QComplex := ((999999910247370850986576085418 : Int)/10^30,(-423680599322759182518828984 : Int)/10^30)
theorem v616_pa_checked : Scalar.distance (sourceCoefficient 6 56 1 0) v616_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v616_pb : Scalar.QComplex := ((-182808632577978483575949 : Int)/10^30,(-431477430079727998020825756 : Int)/10^30)
theorem v616_pb_checked : Scalar.distance (sourceCoefficient 6 56 1 1) v616_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v616_pg : Scalar.QComplex := ((-93086415912015870873618 : Int)/10^30,(39438912022156555738 : Int)/10^30)
theorem v616_pg_checked : Scalar.distance (sourceCoefficient 6 56 1 2) v616_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v616_mb : Scalar.QComplex := ((-555154153646711967001147 : Int)/10^30,(-431477111665344766998628860 : Int)/10^30)
theorem v616_mb_checked : Scalar.distance (sourceCoefficient 6 56 3 1) v616_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v616_mg : Scalar.QComplex := ((-93086347217684154996655 : Int)/10^30,(119768281812775484265 : Int)/10^30)
theorem v616_mg_checked : Scalar.distance (sourceCoefficient 6 56 3 2) v616_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v616_upper : Scalar.QComplex := ((999997689630694351321858555089 : Int)/10^30,(-2149589094104040108077474034 : Int)/10^30)
theorem v616_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 56 5) 1) 14) v616_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material616 : Material (6 : Basis) (56 : Basis) where
  plus := ![v616_pa,v616_pb,v616_pg]
  minus := ![(Primitive.Addresses.material616 1).one,v616_mb,v616_mg]
  upper := v616_upper
  lower := (Primitive.Addresses.material616 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v616_pa_checked.trans (by decide +kernel)
    · exact v616_pb_checked.trans (by decide +kernel)
    · exact v616_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 56 Primitive.Addresses.material616
    · exact v616_mb_checked.trans (by decide +kernel)
    · exact v616_mg_checked.trans (by decide +kernel)
  upper_error := v616_upper_checked
  lower_error := reuse_lower_error 6 56 Primitive.Addresses.material616

def v617_pa : Scalar.QComplex := ((999999905187962668308505211753 : Int)/10^30,(-435458454590171628912882146 : Int)/10^30)
theorem v617_pa_checked : Scalar.distance (sourceCoefficient 6 57 1 0) v617_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v617_pb : Scalar.QComplex := ((-187890511123946801373465 : Int)/10^30,(-431477426443577349438438638 : Int)/10^30)
theorem v617_pb_checked : Scalar.distance (sourceCoefficient 6 57 1 1) v617_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v617_pg : Scalar.QComplex := ((-93086415284305410714709 : Int)/10^30,(40535270386274135065 : Int)/10^30)
theorem v617_pg_checked : Scalar.distance (sourceCoefficient 6 57 1 2) v617_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v617_mb : Scalar.QComplex := ((-560236027162630405230887 : Int)/10^30,(-431477103643763166463961170 : Int)/10^30)
theorem v617_mb_checked : Scalar.distance (sourceCoefficient 6 57 3 1) v617_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v617_mg : Scalar.QComplex := ((-93086345643866038477283 : Int)/10^30,(120864639226982882491 : Int)/10^30)
theorem v617_mg_checked : Scalar.distance (sourceCoefficient 6 57 3 2) v617_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v617_upper : Scalar.QComplex := ((999997664243783991167435695508 : Int)/10^30,(-2161366923097641120350244467 : Int)/10^30)
theorem v617_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 57 5) 1) 14) v617_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material617 : Material (6 : Basis) (57 : Basis) where
  plus := ![v617_pa,v617_pb,v617_pg]
  minus := ![(Primitive.Addresses.material617 1).one,v617_mb,v617_mg]
  upper := v617_upper
  lower := (Primitive.Addresses.material617 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v617_pa_checked.trans (by decide +kernel)
    · exact v617_pb_checked.trans (by decide +kernel)
    · exact v617_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 57 Primitive.Addresses.material617
    · exact v617_mb_checked.trans (by decide +kernel)
    · exact v617_mg_checked.trans (by decide +kernel)
  upper_error := v617_upper_checked
  lower_error := reuse_lower_error 6 57 Primitive.Addresses.material617

def v618_pa : Scalar.QComplex := ((999999902384723950417875648581 : Int)/10^30,(-441849004265509384735674461 : Int)/10^30)
theorem v618_pa_checked : Scalar.distance (sourceCoefficient 6 58 1 0) v618_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v618_pb : Scalar.QComplex := ((-190647888960787047707023 : Int)/10^30,(-431477424437239272446227570 : Int)/10^30)
theorem v618_pb_checked : Scalar.distance (sourceCoefficient 6 58 1 1) v618_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v618_pg : Scalar.QComplex := ((-93086414937411212152423 : Int)/10^30,(41130143765671520830 : Int)/10^30)
theorem v618_pg_checked : Scalar.distance (sourceCoefficient 6 58 1 2) v618_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v618_mb : Scalar.QComplex := ((-562993402241393466184554 : Int)/10^30,(-431477099257932951017685380 : Int)/10^30)
theorem v618_mb_checked : Scalar.distance (sourceCoefficient 6 58 3 1) v618_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v618_mg : Scalar.QComplex := ((-93086344783623034762056 : Int)/10^30,(121459512085527652226 : Int)/10^30)
theorem v618_mg_checked : Scalar.distance (sourceCoefficient 6 58 3 2) v618_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v618_upper : Scalar.QComplex := ((999997650411040454876436670911 : Int)/10^30,(-2167757458416870102205895707 : Int)/10^30)
theorem v618_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 58 5) 1) 14) v618_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material618 : Material (6 : Basis) (58 : Basis) where
  plus := ![v618_pa,v618_pb,v618_pg]
  minus := ![(Primitive.Addresses.material618 1).one,v618_mb,v618_mg]
  upper := v618_upper
  lower := (Primitive.Addresses.material618 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v618_pa_checked.trans (by decide +kernel)
    · exact v618_pb_checked.trans (by decide +kernel)
    · exact v618_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 58 Primitive.Addresses.material618
    · exact v618_mb_checked.trans (by decide +kernel)
    · exact v618_mg_checked.trans (by decide +kernel)
  upper_error := v618_upper_checked
  lower_error := reuse_lower_error 6 58 Primitive.Addresses.material618

def v619_pa : Scalar.QComplex := ((999999894468955705864000428011 : Int)/10^30,(-459414929504332378888293093 : Int)/10^30)
theorem v619_pa_checked : Scalar.distance (sourceCoefficient 6 59 1 0) v619_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v619_pb : Scalar.QComplex := ((-198227188860432511811102 : Int)/10^30,(-431477418801299404047221228 : Int)/10^30)
theorem v619_pb_checked : Scalar.distance (sourceCoefficient 6 59 1 1) v619_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v619_pg : Scalar.QComplex := ((-93086413961040536298346 : Int)/10^30,(42765292820788550267 : Int)/10^30)
theorem v619_pg_checked : Scalar.distance (sourceCoefficient 6 59 1 2) v619_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v619_mb : Scalar.QComplex := ((-570572694455356913413739 : Int)/10^30,(-431477087081400726738270165 : Int)/10^30)
theorem v619_mb_checked : Scalar.distance (sourceCoefficient 6 59 3 1) v619_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v619_mg : Scalar.QComplex := ((-93086342396192732269042 : Int)/10^30,(123094659689240039280 : Int)/10^30)
theorem v619_mg_checked : Scalar.distance (sourceCoefficient 6 59 3 2) v619_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v619_upper : Scalar.QComplex := ((999997612178090606010416035856 : Int)/10^30,(-2185323343831413014444434798 : Int)/10^30)
theorem v619_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 59 5) 1) 14) v619_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material619 : Material (6 : Basis) (59 : Basis) where
  plus := ![v619_pa,v619_pb,v619_pg]
  minus := ![(Primitive.Addresses.material619 1).one,v619_mb,v619_mg]
  upper := v619_upper
  lower := (Primitive.Addresses.material619 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v619_pa_checked.trans (by decide +kernel)
    · exact v619_pb_checked.trans (by decide +kernel)
    · exact v619_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 59 Primitive.Addresses.material619
    · exact v619_mb_checked.trans (by decide +kernel)
    · exact v619_mg_checked.trans (by decide +kernel)
  upper_error := v619_upper_checked
  lower_error := reuse_lower_error 6 59 Primitive.Addresses.material619

def v620_pa : Scalar.QComplex := ((999999884954090230255402386367 : Int)/10^30,(-479678857470211876836954766 : Int)/10^30)
theorem v620_pa_checked : Scalar.distance (sourceCoefficient 6 60 1 0) v620_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v620_pb : Scalar.QComplex := ((-206970615861482203372382 : Int)/10^30,(-431477412079210325164098693 : Int)/10^30)
theorem v620_pb_checked : Scalar.distance (sourceCoefficient 6 60 1 1) v620_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v620_pg : Scalar.QComplex := ((-93086412793080485629434 : Int)/10^30,(44651589271568072136 : Int)/10^30)
theorem v620_pg_checked : Scalar.distance (sourceCoefficient 6 60 1 2) v620_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v620_mb : Scalar.QComplex := ((-579316112399969014707218 : Int)/10^30,(-431477072814130438224222598 : Int)/10^30)
theorem v620_mb_checked : Scalar.distance (sourceCoefficient 6 60 3 1) v620_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v620_mg : Scalar.QComplex := ((-93086339600444235100749 : Int)/10^30,(124980954429768263757 : Int)/10^30)
theorem v620_mg_checked : Scalar.distance (sourceCoefficient 6 60 3 2) v620_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v620_upper : Scalar.QComplex := ((999997567689537961753060904342 : Int)/10^30,(-2205587225194757546358902286 : Int)/10^30)
theorem v620_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 60 5) 1) 14) v620_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material620 : Material (6 : Basis) (60 : Basis) where
  plus := ![v620_pa,v620_pb,v620_pg]
  minus := ![(Primitive.Addresses.material620 1).one,v620_mb,v620_mg]
  upper := v620_upper
  lower := (Primitive.Addresses.material620 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v620_pa_checked.trans (by decide +kernel)
    · exact v620_pb_checked.trans (by decide +kernel)
    · exact v620_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 60 Primitive.Addresses.material620
    · exact v620_mb_checked.trans (by decide +kernel)
    · exact v620_mg_checked.trans (by decide +kernel)
  upper_error := v620_upper_checked
  lower_error := reuse_lower_error 6 60 Primitive.Addresses.material620

def v621_pa : Scalar.QComplex := ((999999882126324925956159756031 : Int)/10^30,(-485538192374075146787568022 : Int)/10^30)
theorem v621_pa_checked : Scalar.distance (sourceCoefficient 6 61 1 0) v621_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v621_pb : Scalar.QComplex := ((-209498786440457678748667 : Int)/10^30,(-431477410091482199909344509 : Int)/10^30)
theorem v621_pb_checked : Scalar.distance (sourceCoefficient 6 61 1 1) v621_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v621_pg : Scalar.QComplex := ((-93086412447052184771720 : Int)/10^30,(45197013761667441384 : Int)/10^30)
theorem v621_pg_checked : Scalar.distance (sourceCoefficient 6 61 1 2) v621_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v621_mb : Scalar.QComplex := ((-581844280322271192284152 : Int)/10^30,(-431477068644705708011683168 : Int)/10^30)
theorem v621_mb_checked : Scalar.distance (sourceCoefficient 6 61 3 1) v621_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v621_mg : Scalar.QComplex := ((-93086338783739293136569 : Int)/10^30,(125526378418174329106 : Int)/10^30)
theorem v621_mg_checked : Scalar.distance (sourceCoefficient 6 61 3 2) v621_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v621_upper : Scalar.QComplex := ((999997554749096379720263396542 : Int)/10^30,(-2211446546491363380476413527 : Int)/10^30)
theorem v621_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 61 5) 1) 14) v621_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material621 : Material (6 : Basis) (61 : Basis) where
  plus := ![v621_pa,v621_pb,v621_pg]
  minus := ![(Primitive.Addresses.material621 1).one,v621_mb,v621_mg]
  upper := v621_upper
  lower := (Primitive.Addresses.material621 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v621_pa_checked.trans (by decide +kernel)
    · exact v621_pb_checked.trans (by decide +kernel)
    · exact v621_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 61 Primitive.Addresses.material621
    · exact v621_mb_checked.trans (by decide +kernel)
    · exact v621_mg_checked.trans (by decide +kernel)
  upper_error := v621_upper_checked
  lower_error := reuse_lower_error 6 61 Primitive.Addresses.material621

def v622_pa : Scalar.QComplex := ((999999877956523253436235376124 : Int)/10^30,(-494051554595790451155766429 : Int)/10^30)
theorem v622_pa_checked : Scalar.distance (sourceCoefficient 6 62 1 0) v622_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v622_pb : Scalar.QComplex := ((-213172109800676216896003 : Int)/10^30,(-431477407168201463325372849 : Int)/10^30)
theorem v622_pb_checked : Scalar.distance (sourceCoefficient 6 62 1 1) v622_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v622_pg : Scalar.QComplex := ((-93086411937643710927973 : Int)/10^30,(45989492142254536697 : Int)/10^30)
theorem v622_pg_checked : Scalar.distance (sourceCoefficient 6 62 1 2) v622_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v622_mb : Scalar.QComplex := ((-585517599792083948256136 : Int)/10^30,(-431477062551513440372841888 : Int)/10^30)
theorem v622_mb_checked : Scalar.distance (sourceCoefficient 6 62 3 1) v622_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v622_mg : Scalar.QComplex := ((-93086337590457858423530 : Int)/10^30,(126318856064088935254 : Int)/10^30)
theorem v622_mg_checked : Scalar.distance (sourceCoefficient 6 62 3 2) v622_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v622_upper : Scalar.QComplex := ((999997535886010049137168503263 : Int)/10^30,(-2219959888836726300059262999 : Int)/10^30)
theorem v622_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 62 5) 1) 14) v622_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material622 : Material (6 : Basis) (62 : Basis) where
  plus := ![v622_pa,v622_pb,v622_pg]
  minus := ![(Primitive.Addresses.material622 1).one,v622_mb,v622_mg]
  upper := v622_upper
  lower := (Primitive.Addresses.material622 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v622_pa_checked.trans (by decide +kernel)
    · exact v622_pb_checked.trans (by decide +kernel)
    · exact v622_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 62 Primitive.Addresses.material622
    · exact v622_mb_checked.trans (by decide +kernel)
    · exact v622_mg_checked.trans (by decide +kernel)
  upper_error := v622_upper_checked
  lower_error := reuse_lower_error 6 62 Primitive.Addresses.material622

def v623_pa : Scalar.QComplex := ((999999865399028793888780901034 : Int)/10^30,(-518846725242437073791661977 : Int)/10^30)
theorem v623_pa_checked : Scalar.distance (sourceCoefficient 6 63 1 0) v623_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v623_pb : Scalar.QComplex := ((-223870665317775922720469 : Int)/10^30,(-431477398416576356938934184 : Int)/10^30)
theorem v623_pb_checked : Scalar.distance (sourceCoefficient 6 63 1 1) v623_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v623_pg : Scalar.QComplex := ((-93086410409145119610502 : Int)/10^30,(48297585706260395282 : Int)/10^30)
theorem v623_pg_checked : Scalar.distance (sourceCoefficient 6 63 1 2) v623_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v623_mb : Scalar.QComplex := ((-596216143773364178674164 : Int)/10^30,(-431477044567520026412914230 : Int)/10^30)
theorem v623_mb_checked : Scalar.distance (sourceCoefficient 6 63 3 1) v623_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v623_mg : Scalar.QComplex := ((-93086334070179043174103 : Int)/10^30,(128626947449660631588 : Int)/10^30)
theorem v623_mg_checked : Scalar.distance (sourceCoefficient 6 63 3 2) v623_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v623_upper : Scalar.QComplex := ((999997480534319156700246784322 : Int)/10^30,(-2244755000880782659680812529 : Int)/10^30)
theorem v623_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 63 5) 1) 14) v623_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material623 : Material (6 : Basis) (63 : Basis) where
  plus := ![v623_pa,v623_pb,v623_pg]
  minus := ![(Primitive.Addresses.material623 1).one,v623_mb,v623_mg]
  upper := v623_upper
  lower := (Primitive.Addresses.material623 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v623_pa_checked.trans (by decide +kernel)
    · exact v623_pb_checked.trans (by decide +kernel)
    · exact v623_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 63 Primitive.Addresses.material623
    · exact v623_mb_checked.trans (by decide +kernel)
    · exact v623_mg_checked.trans (by decide +kernel)
  upper_error := v623_upper_checked
  lower_error := reuse_lower_error 6 63 Primitive.Addresses.material623

def v624_pa : Scalar.QComplex := ((999999846384616531666898560759 : Int)/10^30,(-554283991595445740918846319 : Int)/10^30)
theorem v624_pa_checked : Scalar.distance (sourceCoefficient 6 64 1 0) v624_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v624_pb : Scalar.QComplex := ((-239161044143164500301841 : Int)/10^30,(-431477385294766022181790572 : Int)/10^30)
theorem v624_pb_checked : Scalar.distance (sourceCoefficient 6 64 1 1) v624_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v624_pg : Scalar.QComplex := ((-93086408108711616593645 : Int)/10^30,(51596313775766868176 : Int)/10^30)
theorem v624_pg_checked : Scalar.distance (sourceCoefficient 6 64 1 2) v624_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v624_mb : Scalar.QComplex := ((-611506505581914580233079 : Int)/10^30,(-431477018250806304293402999 : Int)/10^30)
theorem v624_mb_checked : Scalar.distance (sourceCoefficient 6 64 3 1) v624_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v624_mg : Scalar.QComplex := ((-93086328923092641926791 : Int)/10^30,(131925672305729379459 : Int)/10^30)
theorem v624_mg_checked : Scalar.distance (sourceCoefficient 6 64 3 2) v624_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v624_upper : Scalar.QComplex := ((999997400358428332609443992152 : Int)/10^30,(-2280192181636995257135614152 : Int)/10^30)
theorem v624_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 64 5) 1) 14) v624_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material624 : Material (6 : Basis) (64 : Basis) where
  plus := ![v624_pa,v624_pb,v624_pg]
  minus := ![(Primitive.Addresses.material624 1).one,v624_mb,v624_mg]
  upper := v624_upper
  lower := (Primitive.Addresses.material624 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v624_pa_checked.trans (by decide +kernel)
    · exact v624_pb_checked.trans (by decide +kernel)
    · exact v624_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 64 Primitive.Addresses.material624
    · exact v624_mb_checked.trans (by decide +kernel)
    · exact v624_mg_checked.trans (by decide +kernel)
  upper_error := v624_upper_checked
  lower_error := reuse_lower_error 6 64 Primitive.Addresses.material624

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
