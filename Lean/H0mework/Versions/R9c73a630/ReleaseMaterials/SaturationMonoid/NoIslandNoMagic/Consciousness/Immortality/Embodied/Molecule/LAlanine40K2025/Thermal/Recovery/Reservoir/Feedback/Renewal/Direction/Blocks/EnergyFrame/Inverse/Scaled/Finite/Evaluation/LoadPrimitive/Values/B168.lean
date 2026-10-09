import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B112

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2689_pa : Scalar.QComplex := ((999999610489108399376466468815 : Int)/10^30,(-882622020732834645918207743 : Int)/10^30)
theorem v2689_pa_checked : Scalar.distance (sourceCoefficient 33 50 1 0) v2689_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2689_pb : Scalar.QComplex := ((-380831556759944258906178 : Int)/10^30,(-431477347580455206013295170 : Int)/10^30)
theorem v2689_pb_checked : Scalar.distance (sourceCoefficient 33 50 1 1) v2689_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2689_pg : Scalar.QComplex := ((-93086393061156808002869 : Int)/10^30,(82160132348635544457 : Int)/10^30)
theorem v2689_pg_checked : Scalar.distance (sourceCoefficient 33 50 1 2) v2689_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2689_mb : Scalar.QComplex := ((-753176932902536184480061 : Int)/10^30,(-431476858281237745634663593 : Int)/10^30)
theorem v2689_mb_checked : Scalar.distance (sourceCoefficient 33 50 3 1) v2689_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2689_mg : Scalar.QComplex := ((-93086287500344551131542 : Int)/10^30,(162489466512929482444 : Int)/10^30)
theorem v2689_mg_checked : Scalar.distance (sourceCoefficient 33 50 3 2) v2689_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2689_upper : Scalar.QComplex := ((999996597781619841158137984700 : Int)/10^30,(-2608529314619212293236542834 : Int)/10^30)
theorem v2689_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 50 5) 1) 14) v2689_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2689 : Material (33 : Basis) (50 : Basis) where
  plus := ![v2689_pa,v2689_pb,v2689_pg]
  minus := ![(Primitive.Addresses.material2689 1).one,v2689_mb,v2689_mg]
  upper := v2689_upper
  lower := (Primitive.Addresses.material2689 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2689_pa_checked.trans (by decide +kernel)
    · exact v2689_pb_checked.trans (by decide +kernel)
    · exact v2689_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 50 Primitive.Addresses.material2689
    · exact v2689_mb_checked.trans (by decide +kernel)
    · exact v2689_mg_checked.trans (by decide +kernel)
  upper_error := v2689_upper_checked
  lower_error := reuse_lower_error 33 50 Primitive.Addresses.material2689

def v2690_pa : Scalar.QComplex := ((999999600452304574408762034670 : Int)/10^30,(-893921266786299002428795448 : Int)/10^30)
theorem v2690_pa_checked : Scalar.distance (sourceCoefficient 33 51 1 0) v2690_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2690_pb : Scalar.QComplex := ((-385706926971128360341726 : Int)/10^30,(-431477342797150073761130585 : Int)/10^30)
theorem v2690_pb_checked : Scalar.distance (sourceCoefficient 33 51 1 1) v2690_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2690_pg : Scalar.QComplex := ((-93086392078039506331314 : Int)/10^30,(83211938774105552618 : Int)/10^30)
theorem v2690_pg_checked : Scalar.distance (sourceCoefficient 33 51 1 2) v2690_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2690_mb : Scalar.QComplex := ((-758052297170620243798136 : Int)/10^30,(-431476849290709480696901855 : Int)/10^30)
theorem v2690_mb_checked : Scalar.distance (sourceCoefficient 33 51 3 1) v2690_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2690_mg : Scalar.QComplex := ((-93086285609566041941760 : Int)/10^30,(163541271698377935091 : Int)/10^30)
theorem v2690_mg_checked : Scalar.distance (sourceCoefficient 33 51 3 2) v2690_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2690_upper : Scalar.QComplex := ((999996568243357336145889866993 : Int)/10^30,(-2619828526521164085627399002 : Int)/10^30)
theorem v2690_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 51 5) 1) 14) v2690_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2690 : Material (33 : Basis) (51 : Basis) where
  plus := ![v2690_pa,v2690_pb,v2690_pg]
  minus := ![(Primitive.Addresses.material2690 1).one,v2690_mb,v2690_mg]
  upper := v2690_upper
  lower := (Primitive.Addresses.material2690 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2690_pa_checked.trans (by decide +kernel)
    · exact v2690_pb_checked.trans (by decide +kernel)
    · exact v2690_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 51 Primitive.Addresses.material2690
    · exact v2690_mb_checked.trans (by decide +kernel)
    · exact v2690_mg_checked.trans (by decide +kernel)
  upper_error := v2690_upper_checked
  lower_error := reuse_lower_error 33 51 Primitive.Addresses.material2690

def v2691_pa : Scalar.QComplex := ((999999578536751639160959967566 : Int)/10^30,(-918110188969934240754664118 : Int)/10^30)
theorem v2691_pa_checked : Scalar.distance (sourceCoefficient 33 52 1 0) v2691_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2691_pb : Scalar.QComplex := ((-396143902063782733976565 : Int)/10^30,(-431477332310337365648894085 : Int)/10^30)
theorem v2691_pb_checked : Scalar.distance (sourceCoefficient 33 52 1 1) v2691_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2691_pg : Scalar.QComplex := ((-93086389926813175786657 : Int)/10^30,(85463599066001506966 : Int)/10^30)
theorem v2691_pg_checked : Scalar.distance (sourceCoefficient 33 52 1 2) v2691_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2691_mb : Scalar.QComplex := ((-768489259327464738522667 : Int)/10^30,(-431476829797261236252163798 : Int)/10^30)
theorem v2691_mb_checked : Scalar.distance (sourceCoefficient 33 52 3 1) v2691_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2691_mg : Scalar.QComplex := ((-93086281515259091505766 : Int)/10^30,(165792929295466421185 : Int)/10^30)
theorem v2691_mg_checked : Scalar.distance (sourceCoefficient 33 52 3 2) v2691_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2691_upper : Scalar.QComplex := ((999996504579951754464154435053 : Int)/10^30,(-2644017374853984959021767956 : Int)/10^30)
theorem v2691_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 52 5) 1) 14) v2691_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2691 : Material (33 : Basis) (52 : Basis) where
  plus := ![v2691_pa,v2691_pb,v2691_pg]
  minus := ![(Primitive.Addresses.material2691 1).one,v2691_mb,v2691_mg]
  upper := v2691_upper
  lower := (Primitive.Addresses.material2691 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2691_pa_checked.trans (by decide +kernel)
    · exact v2691_pb_checked.trans (by decide +kernel)
    · exact v2691_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 52 Primitive.Addresses.material2691
    · exact v2691_mb_checked.trans (by decide +kernel)
    · exact v2691_mg_checked.trans (by decide +kernel)
  upper_error := v2691_upper_checked
  lower_error := reuse_lower_error 33 52 Primitive.Addresses.material2691

def v2692_pa : Scalar.QComplex := ((999999575130419382520052481008 : Int)/10^30,(-921812877280849966845177601 : Int)/10^30)
theorem v2692_pa_checked : Scalar.distance (sourceCoefficient 33 53 1 0) v2692_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2692_pb : Scalar.QComplex := ((-397741528659604631820111 : Int)/10^30,(-431477330675374978563990594 : Int)/10^30)
theorem v2692_pb_checked : Scalar.distance (sourceCoefficient 33 53 1 1) v2692_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2692_pg : Scalar.QComplex := ((-93086389591909133852920 : Int)/10^30,(85808269082727222720 : Int)/10^30)
theorem v2692_pg_checked : Scalar.distance (sourceCoefficient 33 53 1 2) v2692_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2692_mb : Scalar.QComplex := ((-770086883917518335517417 : Int)/10^30,(-431476826783619660174982444 : Int)/10^30)
theorem v2692_mb_checked : Scalar.distance (sourceCoefficient 33 53 3 1) v2692_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2692_mg : Scalar.QComplex := ((-93086280882920473199115 : Int)/10^30,(166137598894848632843 : Int)/10^30)
theorem v2692_mg_checked : Scalar.distance (sourceCoefficient 33 53 3 2) v2692_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2692_upper : Scalar.QComplex := ((999996494783120451774082472593 : Int)/10^30,(-2647720051771160939411944806 : Int)/10^30)
theorem v2692_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 53 5) 1) 14) v2692_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2692 : Material (33 : Basis) (53 : Basis) where
  plus := ![v2692_pa,v2692_pb,v2692_pg]
  minus := ![(Primitive.Addresses.material2692 1).one,v2692_mb,v2692_mg]
  upper := v2692_upper
  lower := (Primitive.Addresses.material2692 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2692_pa_checked.trans (by decide +kernel)
    · exact v2692_pb_checked.trans (by decide +kernel)
    · exact v2692_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 53 Primitive.Addresses.material2692
    · exact v2692_mb_checked.trans (by decide +kernel)
    · exact v2692_mg_checked.trans (by decide +kernel)
  upper_error := v2692_upper_checked
  lower_error := reuse_lower_error 33 53 Primitive.Addresses.material2692

def v2693_pa : Scalar.QComplex := ((999999573393362447971018764463 : Int)/10^30,(-923695346481097499646487655 : Int)/10^30)
theorem v2693_pa_checked : Scalar.distance (sourceCoefficient 33 54 1 0) v2693_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2693_pb : Scalar.QComplex := ((-398553771712021957933100 : Int)/10^30,(-431477329841125841991347198 : Int)/10^30)
theorem v2693_pb_checked : Scalar.distance (sourceCoefficient 33 54 1 1) v2693_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2693_pg : Scalar.QComplex := ((-93086389421070978100937 : Int)/10^30,(85983501410102947523 : Int)/10^30)
theorem v2693_pg_checked : Scalar.distance (sourceCoefficient 33 54 1 2) v2693_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2693_mb : Scalar.QComplex := ((-770899125947581020198245 : Int)/10^30,(-431476825248441662064357866 : Int)/10^30)
theorem v2693_mb_checked : Scalar.distance (sourceCoefficient 33 54 3 1) v2693_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2693_mg : Scalar.QComplex := ((-93086280560864774703789 : Int)/10^30,(166312831009551719502 : Int)/10^30)
theorem v2693_mg_checked : Scalar.distance (sourceCoefficient 33 54 3 2) v2693_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2693_upper : Scalar.QComplex := ((999996489797095041011877540808 : Int)/10^30,(-2649602515169689044352863758 : Int)/10^30)
theorem v2693_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 54 5) 1) 14) v2693_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2693 : Material (33 : Basis) (54 : Basis) where
  plus := ![v2693_pa,v2693_pb,v2693_pg]
  minus := ![(Primitive.Addresses.material2693 1).one,v2693_mb,v2693_mg]
  upper := v2693_upper
  lower := (Primitive.Addresses.material2693 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2693_pa_checked.trans (by decide +kernel)
    · exact v2693_pb_checked.trans (by decide +kernel)
    · exact v2693_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 54 Primitive.Addresses.material2693
    · exact v2693_mb_checked.trans (by decide +kernel)
    · exact v2693_mg_checked.trans (by decide +kernel)
  upper_error := v2693_upper_checked
  lower_error := reuse_lower_error 33 54 Primitive.Addresses.material2693

def v2694_pa : Scalar.QComplex := ((999999559102841277775666204095 : Int)/10^30,(-939038935856306278998044471 : Int)/10^30)
theorem v2694_pa_checked : Scalar.distance (sourceCoefficient 33 55 1 0) v2694_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2694_pb : Scalar.QComplex := ((-405174184843625753533078 : Int)/10^30,(-431477322965316797524146359 : Int)/10^30)
theorem v2694_pb_checked : Scalar.distance (sourceCoefficient 33 55 1 1) v2694_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2694_pg : Scalar.QComplex := ((-93086388014254885133412 : Int)/10^30,(87411781283219137320 : Int)/10^30)
theorem v2694_pg_checked : Scalar.distance (sourceCoefficient 33 55 1 2) v2694_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2694_mb : Scalar.QComplex := ((-777519530680588908643356 : Int)/10^30,(-431476812659516817539798608 : Int)/10^30)
theorem v2694_mb_checked : Scalar.distance (sourceCoefficient 33 55 3 1) v2694_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2694_mg : Scalar.QComplex := ((-93086277921508002396460 : Int)/10^30,(167741109136835109337 : Int)/10^30)
theorem v2694_mg_checked : Scalar.distance (sourceCoefficient 33 55 3 2) v2694_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2694_upper : Scalar.QComplex := ((999996449024951852813499901115 : Int)/10^30,(-2664946057028280720145827495 : Int)/10^30)
theorem v2694_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 55 5) 1) 14) v2694_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2694 : Material (33 : Basis) (55 : Basis) where
  plus := ![v2694_pa,v2694_pb,v2694_pg]
  minus := ![(Primitive.Addresses.material2694 1).one,v2694_mb,v2694_mg]
  upper := v2694_upper
  lower := (Primitive.Addresses.material2694 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2694_pa_checked.trans (by decide +kernel)
    · exact v2694_pb_checked.trans (by decide +kernel)
    · exact v2694_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 55 Primitive.Addresses.material2694
    · exact v2694_mb_checked.trans (by decide +kernel)
    · exact v2694_mg_checked.trans (by decide +kernel)
  upper_error := v2694_upper_checked
  lower_error := reuse_lower_error 33 55 Primitive.Addresses.material2694

def v2695_pa : Scalar.QComplex := ((999999555676734742247764590829 : Int)/10^30,(-942680398169146413861719333 : Int)/10^30)
theorem v2695_pa_checked : Scalar.distance (sourceCoefficient 33 56 1 0) v2695_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2695_pb : Scalar.QComplex := ((-406745393783311077554036 : Int)/10^30,(-431477321313608922247010469 : Int)/10^30)
theorem v2695_pb_checked : Scalar.distance (sourceCoefficient 33 56 1 1) v2695_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2695_pg : Scalar.QComplex := ((-93086387676624159166678 : Int)/10^30,(87750751988828238814 : Int)/10^30)
theorem v2695_pg_checked : Scalar.distance (sourceCoefficient 33 56 1 2) v2695_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2695_mb : Scalar.QComplex := ((-779090737609891830420589 : Int)/10^30,(-431476809651927006944293948 : Int)/10^30)
theorem v2695_mb_checked : Scalar.distance (sourceCoefficient 33 56 3 1) v2695_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2695_mg : Scalar.QComplex := ((-93086277291360949878277 : Int)/10^30,(168080079424869815220 : Int)/10^30)
theorem v2695_mg_checked : Scalar.distance (sourceCoefficient 33 56 3 2) v2695_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2695_upper : Scalar.QComplex := ((999996439314016818987212832930 : Int)/10^30,(-2668587508004441429881422179 : Int)/10^30)
theorem v2695_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 56 5) 1) 14) v2695_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2695 : Material (33 : Basis) (56 : Basis) where
  plus := ![v2695_pa,v2695_pb,v2695_pg]
  minus := ![(Primitive.Addresses.material2695 1).one,v2695_mb,v2695_mg]
  upper := v2695_upper
  lower := (Primitive.Addresses.material2695 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2695_pa_checked.trans (by decide +kernel)
    · exact v2695_pb_checked.trans (by decide +kernel)
    · exact v2695_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 56 Primitive.Addresses.material2695
    · exact v2695_mb_checked.trans (by decide +kernel)
    · exact v2695_mg_checked.trans (by decide +kernel)
  upper_error := v2695_upper_checked
  lower_error := reuse_lower_error 33 56 Primitive.Addresses.material2695

def v2696_pa : Scalar.QComplex := ((999999544504621505650717147786 : Int)/10^30,(-954458249224479559683456518 : Int)/10^30)
theorem v2696_pa_checked : Scalar.distance (sourceCoefficient 33 57 1 0) v2696_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2696_pb : Scalar.QComplex := ((-411827271117667754333817 : Int)/10^30,(-431477315919128469291294250 : Int)/10^30)
theorem v2696_pb_checked : Scalar.distance (sourceCoefficient 33 57 1 1) v2696_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2696_pg : Scalar.QComplex := ((-93086386574738801390800 : Int)/10^30,(88847110026206304595 : Int)/10^30)
theorem v2696_pg_checked : Scalar.distance (sourceCoefficient 33 57 1 2) v2696_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2696_mb : Scalar.QComplex := ((-784172608396839649831434 : Int)/10^30,(-431476799872017302309120203 : Int)/10^30)
theorem v2696_mb_checked : Scalar.distance (sourceCoefficient 33 57 3 1) v2696_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2696_mg : Scalar.QComplex := ((-93086275243368394260406 : Int)/10^30,(169176436103146240961 : Int)/10^30)
theorem v2696_mg_checked : Scalar.distance (sourceCoefficient 33 57 3 2) v2696_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2696_upper : Scalar.QComplex := ((999996407814417778736698379081 : Int)/10^30,(-2680365322235995032185716348 : Int)/10^30)
theorem v2696_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 57 5) 1) 14) v2696_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2696 : Material (33 : Basis) (57 : Basis) where
  plus := ![v2696_pa,v2696_pb,v2696_pg]
  minus := ![(Primitive.Addresses.material2696 1).one,v2696_mb,v2696_mg]
  upper := v2696_upper
  lower := (Primitive.Addresses.material2696 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2696_pa_checked.trans (by decide +kernel)
    · exact v2696_pb_checked.trans (by decide +kernel)
    · exact v2696_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 57 Primitive.Addresses.material2696
    · exact v2696_mb_checked.trans (by decide +kernel)
    · exact v2696_mg_checked.trans (by decide +kernel)
  upper_error := v2696_upper_checked
  lower_error := reuse_lower_error 33 57 Primitive.Addresses.material2696

def v2697_pa : Scalar.QComplex := ((999999538384688506947023699409 : Int)/10^30,(-960848796584254534171004338 : Int)/10^30)
theorem v2697_pa_checked : Scalar.distance (sourceCoefficient 33 58 1 0) v2697_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2697_pb : Scalar.QComplex := ((-414584648288432502528767 : Int)/10^30,(-431477312958737751426730158 : Int)/10^30)
theorem v2697_pb_checked : Scalar.distance (sourceCoefficient 33 58 1 1) v2697_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2697_pg : Scalar.QComplex := ((-93086385970561917646405 : Int)/10^30,(89441983225980800504 : Int)/10^30)
theorem v2697_pg_checked : Scalar.distance (sourceCoefficient 33 58 1 2) v2697_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2697_mb : Scalar.QComplex := ((-786929981986223000519864 : Int)/10^30,(-431476794532135376021047911 : Int)/10^30)
theorem v2697_mb_checked : Scalar.distance (sourceCoefficient 33 58 3 1) v2697_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2697_mg : Scalar.QComplex := ((-93086274125842956167636 : Int)/10^30,(169771308560044817992 : Int)/10^30)
theorem v2697_mg_checked : Scalar.distance (sourceCoefficient 33 58 3 2) v2697_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2697_upper : Scalar.QComplex := ((999996390664988897910454831822 : Int)/10^30,(-2686755849515351240936278596 : Int)/10^30)
theorem v2697_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 58 5) 1) 14) v2697_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2697 : Material (33 : Basis) (58 : Basis) where
  plus := ![v2697_pa,v2697_pb,v2697_pg]
  minus := ![(Primitive.Addresses.material2697 1).one,v2697_mb,v2697_mg]
  upper := v2697_upper
  lower := (Primitive.Addresses.material2697 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2697_pa_checked.trans (by decide +kernel)
    · exact v2697_pb_checked.trans (by decide +kernel)
    · exact v2697_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 58 Primitive.Addresses.material2697
    · exact v2697_mb_checked.trans (by decide +kernel)
    · exact v2697_mg_checked.trans (by decide +kernel)
  upper_error := v2697_upper_checked
  lower_error := reuse_lower_error 33 58 Primitive.Addresses.material2697

def v2698_pa : Scalar.QComplex := ((999999521352207842405632997443 : Int)/10^30,(-978414715349007716806289102 : Int)/10^30)
theorem v2698_pa_checked : Scalar.distance (sourceCoefficient 33 59 1 0) v2698_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2698_pb : Scalar.QComplex := ((-422163946325800984497570 : Int)/10^30,(-431477304700360356036296884 : Int)/10^30)
theorem v2698_pb_checked : Scalar.distance (sourceCoefficient 33 59 1 1) v2698_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2698_pg : Scalar.QComplex := ((-93086384286989416485341 : Int)/10^30,(91077131778891136597 : Int)/10^30)
theorem v2698_pg_checked : Scalar.distance (sourceCoefficient 33 59 1 2) v2698_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2698_mb : Scalar.QComplex := ((-794509270074864683432761 : Int)/10^30,(-431476779733168208264710122 : Int)/10^30)
theorem v2698_mb_checked : Scalar.distance (sourceCoefficient 33 59 3 1) v2698_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2698_mg : Scalar.QComplex := ((-93086271031211525072953 : Int)/10^30,(171406455051267374644 : Int)/10^30)
theorem v2698_mg_checked : Scalar.distance (sourceCoefficient 33 59 3 2) v2698_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2698_upper : Scalar.QComplex := ((999996343315351380986315671129 : Int)/10^30,(-2704321712721215408815608586 : Int)/10^30)
theorem v2698_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 59 5) 1) 14) v2698_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2698 : Material (33 : Basis) (59 : Basis) where
  plus := ![v2698_pa,v2698_pb,v2698_pg]
  minus := ![(Primitive.Addresses.material2698 1).one,v2698_mb,v2698_mg]
  upper := v2698_upper
  lower := (Primitive.Addresses.material2698 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2698_pa_checked.trans (by decide +kernel)
    · exact v2698_pb_checked.trans (by decide +kernel)
    · exact v2698_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 59 Primitive.Addresses.material2698
    · exact v2698_mb_checked.trans (by decide +kernel)
    · exact v2698_mg_checked.trans (by decide +kernel)
  upper_error := v2698_upper_checked
  lower_error := reuse_lower_error 33 59 Primitive.Addresses.material2698

def v2699_pa : Scalar.QComplex := ((999999501320367009917963116707 : Int)/10^30,(-998678635647517852038753823 : Int)/10^30)
theorem v2699_pa_checked : Scalar.distance (sourceCoefficient 33 60 1 0) v2699_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2699_pb : Scalar.QComplex := ((-430907371121319092428968 : Int)/10^30,(-431477294953045789046042872 : Int)/10^30)
theorem v2699_pb_checked : Scalar.distance (sourceCoefficient 33 60 1 1) v2699_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2699_pg : Scalar.QComplex := ((-93086382303206312961624 : Int)/10^30,(92963427634897305546 : Int)/10^30)
theorem v2699_pg_checked : Scalar.distance (sourceCoefficient 33 60 1 2) v2699_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2699_mb : Scalar.QComplex := ((-803252683203312677178216 : Int)/10^30,(-431476762440675461347663151 : Int)/10^30)
theorem v2699_mb_checked : Scalar.distance (sourceCoefficient 33 60 3 1) v2699_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2699_mg : Scalar.QComplex := ((-93086267419640792080679 : Int)/10^30,(173292748493003916355 : Int)/10^30)
theorem v2699_mg_checked : Scalar.distance (sourceCoefficient 33 60 3 2) v2699_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2699_upper : Scalar.QComplex := ((999996288309852276833213796743 : Int)/10^30,(-2724585568265856624238008485 : Int)/10^30)
theorem v2699_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 60 5) 1) 14) v2699_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2699 : Material (33 : Basis) (60 : Basis) where
  plus := ![v2699_pa,v2699_pb,v2699_pg]
  minus := ![(Primitive.Addresses.material2699 1).one,v2699_mb,v2699_mg]
  upper := v2699_upper
  lower := (Primitive.Addresses.material2699 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2699_pa_checked.trans (by decide +kernel)
    · exact v2699_pb_checked.trans (by decide +kernel)
    · exact v2699_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 60 Primitive.Addresses.material2699
    · exact v2699_mb_checked.trans (by decide +kernel)
    · exact v2699_mg_checked.trans (by decide +kernel)
  upper_error := v2699_upper_checked
  lower_error := reuse_lower_error 33 60 Primitive.Addresses.material2699

def v2700_pa : Scalar.QComplex := ((999999495451607842705143579180 : Int)/10^30,(-1004537968294633293663337503 : Int)/10^30)
theorem v2700_pa_checked : Scalar.distance (sourceCoefficient 33 61 1 0) v2700_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2700_pb : Scalar.QComplex := ((-433435541051137292616230 : Int)/10^30,(-431477292090570712732040334 : Int)/10^30)
theorem v2700_pb_checked : Scalar.distance (sourceCoefficient 33 61 1 1) v2700_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2700_pg : Scalar.QComplex := ((-93086381721281966875536 : Int)/10^30,(93508851949936180417 : Int)/10^30)
theorem v2700_pg_checked : Scalar.distance (sourceCoefficient 33 61 1 2) v2700_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2700_mb : Scalar.QComplex := ((-805780849721590599653103 : Int)/10^30,(-431476757396504665977634687 : Int)/10^30)
theorem v2700_mb_checked : Scalar.distance (sourceCoefficient 33 61 3 1) v2700_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2700_mg : Scalar.QComplex := ((-93086266367040043792325 : Int)/10^30,(173838172102781889842 : Int)/10^30)
theorem v2700_mg_checked : Scalar.distance (sourceCoefficient 33 61 3 2) v2700_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2700_upper : Scalar.QComplex := ((999996272328425256031999086043 : Int)/10^30,(-2730444882057238460609662635 : Int)/10^30)
theorem v2700_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 61 5) 1) 14) v2700_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2700 : Material (33 : Basis) (61 : Basis) where
  plus := ![v2700_pa,v2700_pb,v2700_pg]
  minus := ![(Primitive.Addresses.material2700 1).one,v2700_mb,v2700_mg]
  upper := v2700_upper
  lower := (Primitive.Addresses.material2700 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2700_pa_checked.trans (by decide +kernel)
    · exact v2700_pb_checked.trans (by decide +kernel)
    · exact v2700_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 61 Primitive.Addresses.material2700
    · exact v2700_mb_checked.trans (by decide +kernel)
    · exact v2700_mg_checked.trans (by decide +kernel)
  upper_error := v2700_upper_checked
  lower_error := reuse_lower_error 33 61 Primitive.Addresses.material2700

def v2701_pa : Scalar.QComplex := ((999999486863372568848066119921 : Int)/10^30,(-1013051327205638409524063208 : Int)/10^30)
theorem v2701_pa_checked : Scalar.distance (sourceCoefficient 33 62 1 0) v2701_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2701_pb : Scalar.QComplex := ((-437108863459024526431479 : Int)/10^30,(-431477287896320190669858843 : Int)/10^30)
theorem v2701_pb_checked : Scalar.distance (sourceCoefficient 33 62 1 1) v2701_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2701_pg : Scalar.QComplex := ((-93086380869126661220665 : Int)/10^30,(94301330073704789084 : Int)/10^30)
theorem v2701_pg_checked : Scalar.distance (sourceCoefficient 33 62 1 2) v2701_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2701_mb : Scalar.QComplex := ((-809454167142282723375975 : Int)/10^30,(-431476750032343907919745127 : Int)/10^30)
theorem v2701_mb_checked : Scalar.distance (sourceCoefficient 33 62 3 1) v2701_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2701_mg : Scalar.QComplex := ((-93086264831012126511260 : Int)/10^30,(174630649196103025861 : Int)/10^30)
theorem v2701_mg_checked : Scalar.distance (sourceCoefficient 33 62 3 2) v2701_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2701_upper : Scalar.QComplex := ((999996249046917618835014716489 : Int)/10^30,(-2738958213466080563856180841 : Int)/10^30)
theorem v2701_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 62 5) 1) 14) v2701_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2701 : Material (33 : Basis) (62 : Basis) where
  plus := ![v2701_pa,v2701_pb,v2701_pg]
  minus := ![(Primitive.Addresses.material2701 1).one,v2701_mb,v2701_mg]
  upper := v2701_upper
  lower := (Primitive.Addresses.material2701 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2701_pa_checked.trans (by decide +kernel)
    · exact v2701_pb_checked.trans (by decide +kernel)
    · exact v2701_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 62 Primitive.Addresses.material2701
    · exact v2701_mb_checked.trans (by decide +kernel)
    · exact v2701_mg_checked.trans (by decide +kernel)
  upper_error := v2701_upper_checked
  lower_error := reuse_lower_error 33 62 Primitive.Addresses.material2701

def v2702_pa : Scalar.QComplex := ((999999461437188652729851655596 : Int)/10^30,(-1037846487995521681821932276 : Int)/10^30)
theorem v2702_pa_checked : Scalar.distance (sourceCoefficient 33 63 1 0) v2702_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2702_pb : Scalar.QComplex := ((-447807416140809830636696 : Int)/10^30,(-431477275442995134181418214 : Int)/10^30)
theorem v2702_pb_checked : Scalar.distance (sourceCoefficient 33 63 1 1) v2702_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2702_pg : Scalar.QComplex := ((-93086378342377800039323 : Int)/10^30,(96609422873101576095 : Int)/10^30)
theorem v2702_pg_checked : Scalar.distance (sourceCoefficient 33 63 1 2) v2702_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2702_mb : Scalar.QComplex := ((-820152705093849269330733 : Int)/10^30,(-431476728346654368918513750 : Int)/10^30)
theorem v2702_mb_checked : Scalar.distance (sourceCoefficient 33 63 3 1) v2702_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2702_mg : Scalar.QComplex := ((-93086260312484072915351 : Int)/10^30,(176938738955620911949 : Int)/10^30)
theorem v2702_mg_checked : Scalar.distance (sourceCoefficient 33 63 3 2) v2702_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2702_upper : Scalar.QComplex := ((999996180826573448107960215783 : Int)/10^30,(-2763753293443197689977697597 : Int)/10^30)
theorem v2702_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 63 5) 1) 14) v2702_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2702 : Material (33 : Basis) (63 : Basis) where
  plus := ![v2702_pa,v2702_pb,v2702_pg]
  minus := ![(Primitive.Addresses.material2702 1).one,v2702_mb,v2702_mg]
  upper := v2702_upper
  lower := (Primitive.Addresses.material2702 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2702_pa_checked.trans (by decide +kernel)
    · exact v2702_pb_checked.trans (by decide +kernel)
    · exact v2702_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 63 Primitive.Addresses.material2702
    · exact v2702_mb_checked.trans (by decide +kernel)
    · exact v2702_mg_checked.trans (by decide +kernel)
  upper_error := v2702_upper_checked
  lower_error := reuse_lower_error 33 63 Primitive.Addresses.material2702

def v2703_pa : Scalar.QComplex := ((999999424030841169672134049801 : Int)/10^30,(-1073283739707344959916798479 : Int)/10^30)
theorem v2703_pa_checked : Scalar.distance (sourceCoefficient 33 64 1 0) v2703_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2703_pb : Scalar.QComplex := ((-463097790754637052582836 : Int)/10^30,(-431477257030714030385535646 : Int)/10^30)
theorem v2703_pb_checked : Scalar.distance (sourceCoefficient 33 64 1 1) v2703_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2703_pg : Scalar.QComplex := ((-93086374615244685253936 : Int)/10^30,(99908149806861684663 : Int)/10^30)
theorem v2703_pg_checked : Scalar.distance (sourceCoefficient 33 64 1 2) v2703_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2703_mb : Scalar.QComplex := ((-835443058125401883689048 : Int)/10^30,(-431476696739475482032085568 : Int)/10^30)
theorem v2703_mb_checked : Scalar.distance (sourceCoefficient 33 64 3 1) v2703_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2703_mg : Scalar.QComplex := ((-93086253738699571222939 : Int)/10^30,(180237461444766209594 : Int)/10^30)
theorem v2703_mg_checked : Scalar.distance (sourceCoefficient 33 64 3 2) v2703_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2703_upper : Scalar.QComplex := ((999996082258800065166108624311 : Int)/10^30,(-2799190427815435016892893407 : Int)/10^30)
theorem v2703_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 64 5) 1) 14) v2703_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2703 : Material (33 : Basis) (64 : Basis) where
  plus := ![v2703_pa,v2703_pb,v2703_pg]
  minus := ![(Primitive.Addresses.material2703 1).one,v2703_mb,v2703_mg]
  upper := v2703_upper
  lower := (Primitive.Addresses.material2703 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2703_pa_checked.trans (by decide +kernel)
    · exact v2703_pb_checked.trans (by decide +kernel)
    · exact v2703_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 64 Primitive.Addresses.material2703
    · exact v2703_mb_checked.trans (by decide +kernel)
    · exact v2703_mg_checked.trans (by decide +kernel)
  upper_error := v2703_upper_checked
  lower_error := reuse_lower_error 33 64 Primitive.Addresses.material2703

def v2704_pa : Scalar.QComplex := ((999999384781655503100733583101 : Int)/10^30,(-1109250337164784064564688073 : Int)/10^30)
theorem v2704_pa_checked : Scalar.distance (sourceCoefficient 33 65 1 0) v2704_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2704_pb : Scalar.QComplex := ((-478616565745594336959170 : Int)/10^30,(-431477237604663930053542402 : Int)/10^30)
theorem v2704_pb_checked : Scalar.distance (sourceCoefficient 33 65 1 1) v2704_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2704_pg : Scalar.QComplex := ((-93086370692985318081510 : Int)/10^30,(103256151601718685667 : Int)/10^30)
theorem v2704_pg_checked : Scalar.distance (sourceCoefficient 33 65 1 2) v2704_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2704_mb : Scalar.QComplex := ((-850961810574203676109150 : Int)/10^30,(-431476663921428737389954817 : Int)/10^30)
theorem v2704_mb_checked : Scalar.distance (sourceCoefficient 33 65 3 1) v2704_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2704_mg : Scalar.QComplex := ((-93086246927266903928651 : Int)/10^30,(183585458608275949266 : Int)/10^30)
theorem v2704_mg_checked : Scalar.distance (sourceCoefficient 33 65 3 2) v2704_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2704_upper : Scalar.QComplex := ((999995980934588508339572903989 : Int)/10^30,(-2835156903964318339815064077 : Int)/10^30)
theorem v2704_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 33 65 5) 1) 14) v2704_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2704 : Material (33 : Basis) (65 : Basis) where
  plus := ![v2704_pa,v2704_pb,v2704_pg]
  minus := ![(Primitive.Addresses.material2704 1).one,v2704_mb,v2704_mg]
  upper := v2704_upper
  lower := (Primitive.Addresses.material2704 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2704_pa_checked.trans (by decide +kernel)
    · exact v2704_pb_checked.trans (by decide +kernel)
    · exact v2704_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 33 65 Primitive.Addresses.material2704
    · exact v2704_mb_checked.trans (by decide +kernel)
    · exact v2704_mg_checked.trans (by decide +kernel)
  upper_error := v2704_upper_checked
  lower_error := reuse_lower_error 33 65 Primitive.Addresses.material2704

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
