import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B074
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B075

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1793_pa : Scalar.QComplex := ((999999618108098637199511342495 : Int)/10^30,(-873947170533881098633824574 : Int)/10^30)
theorem v1793_pa_checked : Scalar.distance (sourceCoefficient 20 64 1 0) v1793_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1793_pb : Scalar.QComplex := ((-377088531011296006301676 : Int)/10^30,(-431477324623503647465222885 : Int)/10^30)
theorem v1793_pb_checked : Scalar.distance (sourceCoefficient 20 64 1 1) v1793_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1793_pg : Scalar.QComplex := ((-93086390939416858127618 : Int)/10^30,(81352619044620437067 : Int)/10^30)
theorem v1793_pg_checked : Scalar.distance (sourceCoefficient 20 64 1 2) v1793_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1793_mb : Scalar.QComplex := ((-749433888736772230514239 : Int)/10^30,(-431476838554357376470533671 : Int)/10^30)
theorem v1793_mb_checked : Scalar.distance (sourceCoefficient 20 64 3 1) v1793_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1793_mg : Scalar.QComplex := ((-93086286075453003592950 : Int)/10^30,(161681951678622466198 : Int)/10^30)
theorem v1793_mg_checked : Scalar.distance (sourceCoefficient 20 64 3 2) v1793_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1793_upper : Scalar.QComplex := ((999996620372603198521507827700 : Int)/10^30,(-2599854490490115058894359925 : Int)/10^30)
theorem v1793_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 64 5) 1) 14) v1793_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1793 : Material (20 : Basis) (64 : Basis) where
  plus := ![v1793_pa,v1793_pb,v1793_pg]
  minus := ![(Primitive.Addresses.material1793 1).one,v1793_mb,v1793_mg]
  upper := v1793_upper
  lower := (Primitive.Addresses.material1793 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1793_pa_checked.trans (by decide +kernel)
    · exact v1793_pb_checked.trans (by decide +kernel)
    · exact v1793_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 64 Primitive.Addresses.material1793
    · exact v1793_mb_checked.trans (by decide +kernel)
    · exact v1793_mg_checked.trans (by decide +kernel)
  upper_error := v1793_upper_checked
  lower_error := reuse_lower_error 20 64 Primitive.Addresses.material1793

def v1794_pa : Scalar.QComplex := ((999999586028375254876521515848 : Int)/10^30,(-909913775100553614456964857 : Int)/10^30)
theorem v1794_pa_checked : Scalar.distance (sourceCoefficient 20 65 1 0) v1794_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1794_pb : Scalar.QComplex := ((-392607308047236147958011 : Int)/10^30,(-431477307259761339510816170 : Int)/10^30)
theorem v1794_pb_checked : Scalar.distance (sourceCoefficient 20 65 1 1) v1794_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1794_pg : Scalar.QComplex := ((-93086387573307186159035 : Int)/10^30,(84700621390955057855 : Int)/10^30)
theorem v1794_pg_checked : Scalar.distance (sourceCoefficient 20 65 1 2) v1794_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1794_mb : Scalar.QComplex := ((-764952645010234860700627 : Int)/10^30,(-431476807798615891586443002 : Int)/10^30)
theorem v1794_mb_checked : Scalar.distance (sourceCoefficient 20 65 3 1) v1794_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1794_mg : Scalar.QComplex := ((-93086279820169348522208 : Int)/10^30,(165029949873541759222 : Int)/10^30)
theorem v1794_mg_checked : Scalar.distance (sourceCoefficient 20 65 3 2) v1794_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1794_upper : Scalar.QComplex := ((999996526217830977979571488093 : Int)/10^30,(-2635820986122062698698766982 : Int)/10^30)
theorem v1794_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 65 5) 1) 14) v1794_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1794 : Material (20 : Basis) (65 : Basis) where
  plus := ![v1794_pa,v1794_pb,v1794_pg]
  minus := ![(Primitive.Addresses.material1794 1).one,v1794_mb,v1794_mg]
  upper := v1794_upper
  lower := (Primitive.Addresses.material1794 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1794_pa_checked.trans (by decide +kernel)
    · exact v1794_pb_checked.trans (by decide +kernel)
    · exact v1794_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 65 Primitive.Addresses.material1794
    · exact v1794_mb_checked.trans (by decide +kernel)
    · exact v1794_mg_checked.trans (by decide +kernel)
  upper_error := v1794_upper_checked
  lower_error := reuse_lower_error 20 65 Primitive.Addresses.material1794

def v1795_pa : Scalar.QComplex := ((999999569870545024722616615793 : Int)/10^30,(-927501334198073663040147751 : Int)/10^30)
theorem v1795_pa_checked : Scalar.distance (sourceCoefficient 20 66 1 0) v1795_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1795_pb : Scalar.QComplex := ((-400195942169146434289030 : Int)/10^30,(-431477298498009121703623933 : Int)/10^30)
theorem v1795_pb_checked : Scalar.distance (sourceCoefficient 20 66 1 1) v1795_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1795_pg : Scalar.QComplex := ((-93086385876144993600188 : Int)/10^30,(86337784232225277351 : Int)/10^30)
theorem v1795_pg_checked : Scalar.distance (sourceCoefficient 20 66 1 2) v1795_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1795_mb : Scalar.QComplex := ((-772541268745552296435431 : Int)/10^30,(-431476792488217468364859586 : Int)/10^30)
theorem v1795_mb_checked : Scalar.distance (sourceCoefficient 20 66 3 1) v1795_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1795_mg : Scalar.QComplex := ((-93086276710209990955407 : Int)/10^30,(166667110640646896045 : Int)/10^30)
theorem v1795_mg_checked : Scalar.distance (sourceCoefficient 20 66 3 2) v1795_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1795_upper : Scalar.QComplex := ((999996479705493341593882107684 : Int)/10^30,(-2653408491138030301007027312 : Int)/10^30)
theorem v1795_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 66 5) 1) 14) v1795_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1795 : Material (20 : Basis) (66 : Basis) where
  plus := ![v1795_pa,v1795_pb,v1795_pg]
  minus := ![(Primitive.Addresses.material1795 1).one,v1795_mb,v1795_mg]
  upper := v1795_upper
  lower := (Primitive.Addresses.material1795 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1795_pa_checked.trans (by decide +kernel)
    · exact v1795_pb_checked.trans (by decide +kernel)
    · exact v1795_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 66 Primitive.Addresses.material1795
    · exact v1795_mb_checked.trans (by decide +kernel)
    · exact v1795_mg_checked.trans (by decide +kernel)
  upper_error := v1795_upper_checked
  lower_error := reuse_lower_error 20 66 Primitive.Addresses.material1795

def v1796_pa : Scalar.QComplex := ((999999542057713354461527122164 : Int)/10^30,(-957018476091208516857740054 : Int)/10^30)
theorem v1796_pa_checked : Scalar.distance (sourceCoefficient 20 67 1 0) v1796_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1796_pb : Scalar.QComplex := ((-412931921319960783839956 : Int)/10^30,(-431477283393239424319568476 : Int)/10^30)
theorem v1796_pb_checked : Scalar.distance (sourceCoefficient 20 67 1 1) v1796_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1796_pg : Scalar.QComplex := ((-93086382952304166079115 : Int)/10^30,(89085429153841918148 : Int)/10^30)
theorem v1796_pg_checked : Scalar.distance (sourceCoefficient 20 67 1 2) v1796_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1796_mb : Scalar.QComplex := ((-785277230119443589867532 : Int)/10^30,(-431476766392876995231753111 : Int)/10^30)
theorem v1796_mb_checked : Scalar.distance (sourceCoefficient 20 67 3 1) v1796_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1796_mg : Scalar.QComplex := ((-93086271415276434092217 : Int)/10^30,(169414752016046809699 : Int)/10^30)
theorem v1796_mg_checked : Scalar.distance (sourceCoefficient 20 67 3 2) v1796_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1796_upper : Scalar.QComplex := ((999996400948793961922604176573 : Int)/10^30,(-2682925541066425329562101868 : Int)/10^30)
theorem v1796_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 67 5) 1) 14) v1796_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1796 : Material (20 : Basis) (67 : Basis) where
  plus := ![v1796_pa,v1796_pb,v1796_pg]
  minus := ![(Primitive.Addresses.material1796 1).one,v1796_mb,v1796_mg]
  upper := v1796_upper
  lower := (Primitive.Addresses.material1796 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1796_pa_checked.trans (by decide +kernel)
    · exact v1796_pb_checked.trans (by decide +kernel)
    · exact v1796_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 67 Primitive.Addresses.material1796
    · exact v1796_mb_checked.trans (by decide +kernel)
    · exact v1796_mg_checked.trans (by decide +kernel)
  upper_error := v1796_upper_checked
  lower_error := reuse_lower_error 20 67 Primitive.Addresses.material1796

def v1797_pa : Scalar.QComplex := ((999999493804362235691281183780 : Int)/10^30,(-1006176435469740936039977583 : Int)/10^30)
theorem v1797_pa_checked : Scalar.distance (sourceCoefficient 20 68 1 0) v1797_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1797_pb : Scalar.QComplex := ((-434142468321521317026635 : Int)/10^30,(-431477257125203050299028547 : Int)/10^30)
theorem v1797_pb_checked : Scalar.distance (sourceCoefficient 20 68 1 1) v1797_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1797_pg : Scalar.QComplex := ((-93086377872921130866407 : Int)/10^30,(93661367289940697975 : Int)/10^30)
theorem v1797_pg_checked : Scalar.distance (sourceCoefficient 20 68 1 2) v1797_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1797_mb : Scalar.QComplex := ((-806487746555215782148405 : Int)/10^30,(-431476721821103627229932257 : Int)/10^30)
theorem v1797_mb_checked : Scalar.distance (sourceCoefficient 20 68 3 1) v1797_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1797_mg : Scalar.QComplex := ((-93086262387066771315839 : Int)/10^30,(173990684065035898283 : Int)/10^30)
theorem v1797_mg_checked : Scalar.distance (sourceCoefficient 20 68 3 2) v1797_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1797_upper : Scalar.QComplex := ((999996267853336398742187800820 : Int)/10^30,(-2732083343949045232786192694 : Int)/10^30)
theorem v1797_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 68 5) 1) 14) v1797_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1797 : Material (20 : Basis) (68 : Basis) where
  plus := ![v1797_pa,v1797_pb,v1797_pg]
  minus := ![(Primitive.Addresses.material1797 1).one,v1797_mb,v1797_mg]
  upper := v1797_upper
  lower := (Primitive.Addresses.material1797 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1797_pa_checked.trans (by decide +kernel)
    · exact v1797_pb_checked.trans (by decide +kernel)
    · exact v1797_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 68 Primitive.Addresses.material1797
    · exact v1797_mb_checked.trans (by decide +kernel)
    · exact v1797_mg_checked.trans (by decide +kernel)
  upper_error := v1797_upper_checked
  lower_error := reuse_lower_error 20 68 Primitive.Addresses.material1797

def v1798_pa : Scalar.QComplex := ((999999471801300009168503756924 : Int)/10^30,(-1027811812049169009004986043 : Int)/10^30)
theorem v1798_pa_checked : Scalar.distance (sourceCoefficient 20 69 1 0) v1798_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1798_pb : Scalar.QComplex := ((-443477643412732691992601 : Int)/10^30,(-431477245123548607202356028 : Int)/10^30)
theorem v1798_pb_checked : Scalar.distance (sourceCoefficient 20 69 1 1) v1798_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1798_pg : Scalar.QComplex := ((-93086375554216785783782 : Int)/10^30,(95675326871052298163 : Int)/10^30)
theorem v1798_pg_checked : Scalar.distance (sourceCoefficient 20 69 1 2) v1798_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1798_mb : Scalar.QComplex := ((-815822907813627582136441 : Int)/10^30,(-431476701763617989860911546 : Int)/10^30)
theorem v1798_mb_checked : Scalar.distance (sourceCoefficient 20 69 3 1) v1798_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1798_mg : Scalar.QComplex := ((-93086258330406876465892 : Int)/10^30,(176004640895320884684 : Int)/10^30)
theorem v1798_mg_checked : Scalar.distance (sourceCoefficient 20 69 3 2) v1798_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1798_upper : Scalar.QComplex := ((999996208509609713134236712414 : Int)/10^30,(-2753718650329832059788808183 : Int)/10^30)
theorem v1798_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 69 5) 1) 14) v1798_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1798 : Material (20 : Basis) (69 : Basis) where
  plus := ![v1798_pa,v1798_pb,v1798_pg]
  minus := ![(Primitive.Addresses.material1798 1).one,v1798_mb,v1798_mg]
  upper := v1798_upper
  lower := (Primitive.Addresses.material1798 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1798_pa_checked.trans (by decide +kernel)
    · exact v1798_pb_checked.trans (by decide +kernel)
    · exact v1798_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 69 Primitive.Addresses.material1798
    · exact v1798_mb_checked.trans (by decide +kernel)
    · exact v1798_mg_checked.trans (by decide +kernel)
  upper_error := v1798_upper_checked
  lower_error := reuse_lower_error 20 69 Primitive.Addresses.material1798

def v1799_pa : Scalar.QComplex := ((999999457072242700147455089673 : Int)/10^30,(-1042043770591790181147021219 : Int)/10^30)
theorem v1799_pa_checked : Scalar.distance (sourceCoefficient 20 70 1 0) v1799_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1799_pb : Scalar.QComplex := ((-449618411163676389516649 : Int)/10^30,(-431477237081909508854241911 : Int)/10^30)
theorem v1799_pb_checked : Scalar.distance (sourceCoefficient 20 70 1 1) v1799_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1799_pg : Scalar.QComplex := ((-93086374001232436930701 : Int)/10^30,(97000128819024232868 : Int)/10^30)
theorem v1799_pg_checked : Scalar.distance (sourceCoefficient 20 70 1 2) v1799_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1799_mb : Scalar.QComplex := ((-821963666338510439139432 : Int)/10^30,(-431476688422775886630888593 : Int)/10^30)
theorem v1799_mb_checked : Scalar.distance (sourceCoefficient 20 70 3 1) v1799_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1799_mg : Scalar.QComplex := ((-93086255634178691624878 : Int)/10^30,(177329441009852958478 : Int)/10^30)
theorem v1799_mg_checked : Scalar.distance (sourceCoefficient 20 70 3 2) v1799_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1799_upper : Scalar.QComplex := ((999996169217505009943073912594 : Int)/10^30,(-2767950562254606080255646989 : Int)/10^30)
theorem v1799_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 70 5) 1) 14) v1799_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1799 : Material (20 : Basis) (70 : Basis) where
  plus := ![v1799_pa,v1799_pb,v1799_pg]
  minus := ![(Primitive.Addresses.material1799 1).one,v1799_mb,v1799_mg]
  upper := v1799_upper
  lower := (Primitive.Addresses.material1799 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1799_pa_checked.trans (by decide +kernel)
    · exact v1799_pb_checked.trans (by decide +kernel)
    · exact v1799_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 70 Primitive.Addresses.material1799
    · exact v1799_mb_checked.trans (by decide +kernel)
    · exact v1799_mg_checked.trans (by decide +kernel)
  upper_error := v1799_upper_checked
  lower_error := reuse_lower_error 20 70 Primitive.Addresses.material1799

def v1800_pa : Scalar.QComplex := ((999999431462994284275923678876 : Int)/10^30,(-1066336573600062394690508836 : Int)/10^30)
theorem v1800_pa_checked : Scalar.distance (sourceCoefficient 20 71 1 0) v1800_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1800_pb : Scalar.QComplex := ((-460100205236281623531823 : Int)/10^30,(-431477223086275362672565626 : Int)/10^30)
theorem v1800_pb_checked : Scalar.distance (sourceCoefficient 20 71 1 1) v1800_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1800_pg : Scalar.QComplex := ((-93086371299595226845492 : Int)/10^30,(99261458654286047640 : Int)/10^30)
theorem v1800_pg_checked : Scalar.distance (sourceCoefficient 20 71 1 2) v1800_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1800_mb : Scalar.QComplex := ((-832445444430662770077259 : Int)/10^30,(-431476665381830749485624771 : Int)/10^30)
theorem v1800_mb_checked : Scalar.distance (sourceCoefficient 20 71 3 1) v1800_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1800_mg : Scalar.QComplex := ((-93086250981116686166787 : Int)/10^30,(179590767671727092622 : Int)/10^30)
theorem v1800_mg_checked : Scalar.distance (sourceCoefficient 20 71 3 2) v1800_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1800_upper : Scalar.QComplex := ((999996101681120569634511208988 : Int)/10^30,(-2792243284882362333149585313 : Int)/10^30)
theorem v1800_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 71 5) 1) 14) v1800_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1800 : Material (20 : Basis) (71 : Basis) where
  plus := ![v1800_pa,v1800_pb,v1800_pg]
  minus := ![(Primitive.Addresses.material1800 1).one,v1800_mb,v1800_mg]
  upper := v1800_upper
  lower := (Primitive.Addresses.material1800 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1800_pa_checked.trans (by decide +kernel)
    · exact v1800_pb_checked.trans (by decide +kernel)
    · exact v1800_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 71 Primitive.Addresses.material1800
    · exact v1800_mb_checked.trans (by decide +kernel)
    · exact v1800_mg_checked.trans (by decide +kernel)
  upper_error := v1800_upper_checked
  lower_error := reuse_lower_error 20 71 Primitive.Addresses.material1800

def v1801_pa : Scalar.QComplex := ((999999403004067992034641551422 : Int)/10^30,(-1092699184410690352757365758 : Int)/10^30)
theorem v1801_pa_checked : Scalar.distance (sourceCoefficient 20 72 1 0) v1801_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1801_pb : Scalar.QComplex := ((-471475074211100531442128 : Int)/10^30,(-431477207514045016163229373 : Int)/10^30)
theorem v1801_pb_checked : Scalar.distance (sourceCoefficient 20 72 1 1) v1801_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1801_pg : Scalar.QComplex := ((-93086368295258382824610 : Int)/10^30,(101715459439697487234 : Int)/10^30)
theorem v1801_pg_checked : Scalar.distance (sourceCoefficient 20 72 1 2) v1801_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1801_mb : Scalar.QComplex := ((-843820295731964659650886 : Int)/10^30,(-431476639993606581041582388 : Int)/10^30)
theorem v1801_mb_checked : Scalar.distance (sourceCoefficient 20 72 3 1) v1801_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1801_mg : Scalar.QComplex := ((-93086245859088807080272 : Int)/10^30,(182044764950794500350 : Int)/10^30)
theorem v1801_mg_checked : Scalar.distance (sourceCoefficient 20 72 3 2) v1801_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1801_upper : Scalar.QComplex := ((999996027722762001847672189475 : Int)/10^30,(-2818605807311453251805199284 : Int)/10^30)
theorem v1801_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 72 5) 1) 14) v1801_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1801 : Material (20 : Basis) (72 : Basis) where
  plus := ![v1801_pa,v1801_pb,v1801_pg]
  minus := ![(Primitive.Addresses.material1801 1).one,v1801_mb,v1801_mg]
  upper := v1801_upper
  lower := (Primitive.Addresses.material1801 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1801_pa_checked.trans (by decide +kernel)
    · exact v1801_pb_checked.trans (by decide +kernel)
    · exact v1801_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 72 Primitive.Addresses.material1801
    · exact v1801_mb_checked.trans (by decide +kernel)
    · exact v1801_mg_checked.trans (by decide +kernel)
  upper_error := v1801_upper_checked
  lower_error := reuse_lower_error 20 72 Primitive.Addresses.material1801

def v1802_pa : Scalar.QComplex := ((999999392633803350901316506443 : Int)/10^30,(-1102148821350592623767179317 : Int)/10^30)
theorem v1802_pa_checked : Scalar.distance (sourceCoefficient 20 73 1 0) v1802_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1802_pb : Scalar.QComplex := ((-475552378276379929956557 : Int)/10^30,(-431477201834858111698888563 : Int)/10^30)
theorem v1802_pb_checked : Scalar.distance (sourceCoefficient 20 73 1 1) v1802_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1802_pg : Scalar.QComplex := ((-93086367199982524143921 : Int)/10^30,(102595092206060151978 : Int)/10^30)
theorem v1802_pg_checked : Scalar.distance (sourceCoefficient 20 73 1 2) v1802_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1802_mb : Scalar.QComplex := ((-847897593378194895190941 : Int)/10^30,(-431476630795892017820206960 : Int)/10^30)
theorem v1802_mb_checked : Scalar.distance (sourceCoefficient 20 73 3 1) v1802_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1802_mg : Scalar.QComplex := ((-93086244004729896039000 : Int)/10^30,(182924396444455948326 : Int)/10^30)
theorem v1802_mg_checked : Scalar.distance (sourceCoefficient 20 73 3 2) v1802_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1802_upper : Scalar.QComplex := ((999996001043296712100639692370 : Int)/10^30,(-2828055412279095345624190041 : Int)/10^30)
theorem v1802_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 73 5) 1) 14) v1802_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1802 : Material (20 : Basis) (73 : Basis) where
  plus := ![v1802_pa,v1802_pb,v1802_pg]
  minus := ![(Primitive.Addresses.material1802 1).one,v1802_mb,v1802_mg]
  upper := v1802_upper
  lower := (Primitive.Addresses.material1802 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1802_pa_checked.trans (by decide +kernel)
    · exact v1802_pb_checked.trans (by decide +kernel)
    · exact v1802_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 73 Primitive.Addresses.material1802
    · exact v1802_mb_checked.trans (by decide +kernel)
    · exact v1802_mg_checked.trans (by decide +kernel)
  upper_error := v1802_upper_checked
  lower_error := reuse_lower_error 20 73 Primitive.Addresses.material1802

def v1803_pa : Scalar.QComplex := ((999999380857934627298089449547 : Int)/10^30,(-1112781985569728167283922060 : Int)/10^30)
theorem v1803_pa_checked : Scalar.distance (sourceCoefficient 20 74 1 0) v1803_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1803_pb : Scalar.QComplex := ((-480140347481383786392474 : Int)/10^30,(-431477195382950656099457883 : Int)/10^30)
theorem v1803_pb_checked : Scalar.distance (sourceCoefficient 20 74 1 1) v1803_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1803_pg : Scalar.QComplex := ((-93086365955932441292394 : Int)/10^30,(103584895271678849145 : Int)/10^30)
theorem v1803_pg_checked : Scalar.distance (sourceCoefficient 20 74 1 2) v1803_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1803_mb : Scalar.QComplex := ((-852485555307182584995363 : Int)/10^30,(-431476620384776175104822202 : Int)/10^30)
theorem v1803_mb_checked : Scalar.distance (sourceCoefficient 20 74 3 1) v1803_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1803_mg : Scalar.QComplex := ((-93086241906524809850462 : Int)/10^30,(183914198067966536363 : Int)/10^30)
theorem v1803_mg_checked : Scalar.distance (sourceCoefficient 20 74 3 2) v1803_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1803_upper : Scalar.QComplex := ((999995970915568718165297168893 : Int)/10^30,(-2838688540337300725475690113 : Int)/10^30)
theorem v1803_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 74 5) 1) 14) v1803_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1803 : Material (20 : Basis) (74 : Basis) where
  plus := ![v1803_pa,v1803_pb,v1803_pg]
  minus := ![(Primitive.Addresses.material1803 1).one,v1803_mb,v1803_mg]
  upper := v1803_upper
  lower := (Primitive.Addresses.material1803 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1803_pa_checked.trans (by decide +kernel)
    · exact v1803_pb_checked.trans (by decide +kernel)
    · exact v1803_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 74 Primitive.Addresses.material1803
    · exact v1803_mb_checked.trans (by decide +kernel)
    · exact v1803_mg_checked.trans (by decide +kernel)
  upper_error := v1803_upper_checked
  lower_error := reuse_lower_error 20 74 Primitive.Addresses.material1803

def v1804_pa : Scalar.QComplex := ((999999364262182073328503636673 : Int)/10^30,(-1127597105215674917644640489 : Int)/10^30)
theorem v1804_pa_checked : Scalar.distance (sourceCoefficient 20 75 1 0) v1804_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1804_pb : Scalar.QComplex := ((-486532735528941684365565 : Int)/10^30,(-431477186285098916322812587 : Int)/10^30)
theorem v1804_pb_checked : Scalar.distance (sourceCoefficient 20 75 1 1) v1804_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1804_pg : Scalar.QComplex := ((-93086364202133084674786 : Int)/10^30,(104963981538949879505 : Int)/10^30)
theorem v1804_pg_checked : Scalar.distance (sourceCoefficient 20 75 1 2) v1804_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1804_mb : Scalar.QComplex := ((-858877933123525966900947 : Int)/10^30,(-431476605770584840301925985 : Int)/10^30)
theorem v1804_mb_checked : Scalar.distance (sourceCoefficient 20 75 3 1) v1804_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1804_mg : Scalar.QComplex := ((-93086238962636769337389 : Int)/10^30,(185293282308290865491 : Int)/10^30)
theorem v1804_mg_checked : Scalar.distance (sourceCoefficient 20 75 3 2) v1804_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1804_upper : Scalar.QComplex := ((999995928750288389870969766262 : Int)/10^30,(-2853503609275103716161621345 : Int)/10^30)
theorem v1804_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 75 5) 1) 14) v1804_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1804 : Material (20 : Basis) (75 : Basis) where
  plus := ![v1804_pa,v1804_pb,v1804_pg]
  minus := ![(Primitive.Addresses.material1804 1).one,v1804_mb,v1804_mg]
  upper := v1804_upper
  lower := (Primitive.Addresses.material1804 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1804_pa_checked.trans (by decide +kernel)
    · exact v1804_pb_checked.trans (by decide +kernel)
    · exact v1804_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 75 Primitive.Addresses.material1804
    · exact v1804_mb_checked.trans (by decide +kernel)
    · exact v1804_mg_checked.trans (by decide +kernel)
  upper_error := v1804_upper_checked
  lower_error := reuse_lower_error 20 75 Primitive.Addresses.material1804

def v1805_pa : Scalar.QComplex := ((999999350168686786125669788349 : Int)/10^30,(-1140027282194164433653070888 : Int)/10^30)
theorem v1805_pa_checked : Scalar.distance (sourceCoefficient 20 76 1 0) v1805_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1805_pb : Scalar.QComplex := ((-491896074845656709189218 : Int)/10^30,(-431477178554404898423879987 : Int)/10^30)
theorem v1805_pb_checked : Scalar.distance (sourceCoefficient 20 76 1 1) v1805_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1805_pg : Scalar.QComplex := ((-93086362712271289325653 : Int)/10^30,(106121062052999960465 : Int)/10^30)
theorem v1805_pg_checked : Scalar.distance (sourceCoefficient 20 76 1 2) v1805_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1805_mb : Scalar.QComplex := ((-864241263771983887482640 : Int)/10^30,(-431476593411573426404470719 : Int)/10^30)
theorem v1805_mb_checked : Scalar.distance (sourceCoefficient 20 76 3 1) v1805_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1805_mg : Scalar.QComplex := ((-93086236474267158078501 : Int)/10^30,(186450361105823361378 : Int)/10^30)
theorem v1805_mg_checked : Scalar.distance (sourceCoefficient 20 76 3 2) v1805_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1805_upper : Scalar.QComplex := ((999995893203456285247640017925 : Int)/10^30,(-2865933743416210460060699986 : Int)/10^30)
theorem v1805_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 76 5) 1) 14) v1805_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1805 : Material (20 : Basis) (76 : Basis) where
  plus := ![v1805_pa,v1805_pb,v1805_pg]
  minus := ![(Primitive.Addresses.material1805 1).one,v1805_mb,v1805_mg]
  upper := v1805_upper
  lower := (Primitive.Addresses.material1805 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1805_pa_checked.trans (by decide +kernel)
    · exact v1805_pb_checked.trans (by decide +kernel)
    · exact v1805_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 76 Primitive.Addresses.material1805
    · exact v1805_mb_checked.trans (by decide +kernel)
    · exact v1805_mg_checked.trans (by decide +kernel)
  upper_error := v1805_upper_checked
  lower_error := reuse_lower_error 20 76 Primitive.Addresses.material1805

def v1806_pa : Scalar.QComplex := ((999999346883897206835275370563 : Int)/10^30,(-1142904973751398861908076547 : Int)/10^30)
theorem v1806_pa_checked : Scalar.distance (sourceCoefficient 20 77 1 0) v1806_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1806_pb : Scalar.QComplex := ((-493137733446280700383435 : Int)/10^30,(-431477176752012113384452654 : Int)/10^30)
theorem v1806_pb_checked : Scalar.distance (sourceCoefficient 20 77 1 1) v1806_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1806_pg : Scalar.QComplex := ((-93086362364963619325627 : Int)/10^30,(106388936019669221709 : Int)/10^30)
theorem v1806_pg_checked : Scalar.distance (sourceCoefficient 20 77 1 2) v1806_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1806_mb : Scalar.QComplex := ((-865482920354897838331747 : Int)/10^30,(-431476590537685862367187717 : Int)/10^30)
theorem v1806_mb_checked : Scalar.distance (sourceCoefficient 20 77 3 1) v1806_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1806_mg : Scalar.QComplex := ((-93086235895796448757021 : Int)/10^30,(186718234673040025332 : Int)/10^30)
theorem v1806_mg_checked : Scalar.distance (sourceCoefficient 20 77 3 2) v1806_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1806_upper : Scalar.QComplex := ((999995884952037032617609089069 : Int)/10^30,(-2868811425018212531138782234 : Int)/10^30)
theorem v1806_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 77 5) 1) 14) v1806_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1806 : Material (20 : Basis) (77 : Basis) where
  plus := ![v1806_pa,v1806_pb,v1806_pg]
  minus := ![(Primitive.Addresses.material1806 1).one,v1806_mb,v1806_mg]
  upper := v1806_upper
  lower := (Primitive.Addresses.material1806 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1806_pa_checked.trans (by decide +kernel)
    · exact v1806_pb_checked.trans (by decide +kernel)
    · exact v1806_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 77 Primitive.Addresses.material1806
    · exact v1806_mb_checked.trans (by decide +kernel)
    · exact v1806_mg_checked.trans (by decide +kernel)
  upper_error := v1806_upper_checked
  lower_error := reuse_lower_error 20 77 Primitive.Addresses.material1806

def v1807_pa : Scalar.QComplex := ((999999326962472810412050319587 : Int)/10^30,(-1160204551533764193362737445 : Int)/10^30)
theorem v1807_pa_checked : Scalar.distance (sourceCoefficient 20 78 1 0) v1807_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1807_pb : Scalar.QComplex := ((-500602108586977707689460 : Int)/10^30,(-431477165816310762816520231 : Int)/10^30)
theorem v1807_pb_checked : Scalar.distance (sourceCoefficient 20 78 1 1) v1807_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1807_pg : Scalar.QComplex := ((-93086360258129094279261 : Int)/10^30,(107999291544769195443 : Int)/10^30)
theorem v1807_pg_checked : Scalar.distance (sourceCoefficient 20 78 1 2) v1807_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1807_mb : Scalar.QComplex := ((-872947283279249102125038 : Int)/10^30,(-431476573160569020215775334 : Int)/10^30)
theorem v1807_mb_checked : Scalar.distance (sourceCoefficient 20 78 3 1) v1807_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1807_mg : Scalar.QComplex := ((-93086232399298417740654 : Int)/10^30,(188328587780427733378 : Int)/10^30)
theorem v1807_mg_checked : Scalar.distance (sourceCoefficient 20 78 3 2) v1807_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1807_upper : Scalar.QComplex := ((999995835173140459890219217354 : Int)/10^30,(-2886110942652317656194667715 : Int)/10^30)
theorem v1807_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 78 5) 1) 14) v1807_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1807 : Material (20 : Basis) (78 : Basis) where
  plus := ![v1807_pa,v1807_pb,v1807_pg]
  minus := ![(Primitive.Addresses.material1807 1).one,v1807_mb,v1807_mg]
  upper := v1807_upper
  lower := (Primitive.Addresses.material1807 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1807_pa_checked.trans (by decide +kernel)
    · exact v1807_pb_checked.trans (by decide +kernel)
    · exact v1807_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 78 Primitive.Addresses.material1807
    · exact v1807_mb_checked.trans (by decide +kernel)
    · exact v1807_mg_checked.trans (by decide +kernel)
  upper_error := v1807_upper_checked
  lower_error := reuse_lower_error 20 78 Primitive.Addresses.material1807

def v1808_pa : Scalar.QComplex := ((999999320476366062700856852023 : Int)/10^30,(-1165781628832016380966322560 : Int)/10^30)
theorem v1808_pa_checked : Scalar.distance (sourceCoefficient 20 79 1 0) v1808_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1808_pb : Scalar.QComplex := ((-503008490822598601421165 : Int)/10^30,(-431477162254134398937426127 : Int)/10^30)
theorem v1808_pb_checked : Scalar.distance (sourceCoefficient 20 79 1 1) v1808_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1808_pg : Scalar.QComplex := ((-93086359571995057422858 : Int)/10^30,(108518441624728959307 : Int)/10^30)
theorem v1808_pg_checked : Scalar.distance (sourceCoefficient 20 79 1 2) v1808_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1808_mb : Scalar.QComplex := ((-875353661544866144874102 : Int)/10^30,(-431476567521794492789568424 : Int)/10^30)
theorem v1808_mb_checked : Scalar.distance (sourceCoefficient 20 79 3 1) v1808_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1808_mg : Scalar.QComplex := ((-93086231265161499009667 : Int)/10^30,(188847737074981424665 : Int)/10^30)
theorem v1808_mg_checked : Scalar.distance (sourceCoefficient 20 79 3 2) v1808_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1808_upper : Scalar.QComplex := ((999995819061513904190083689689 : Int)/10^30,(-2891688000449736506029597484 : Int)/10^30)
theorem v1808_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 79 5) 1) 14) v1808_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1808 : Material (20 : Basis) (79 : Basis) where
  plus := ![v1808_pa,v1808_pb,v1808_pg]
  minus := ![(Primitive.Addresses.material1808 1).one,v1808_mb,v1808_mg]
  upper := v1808_upper
  lower := (Primitive.Addresses.material1808 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1808_pa_checked.trans (by decide +kernel)
    · exact v1808_pb_checked.trans (by decide +kernel)
    · exact v1808_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 79 Primitive.Addresses.material1808
    · exact v1808_mb_checked.trans (by decide +kernel)
    · exact v1808_mg_checked.trans (by decide +kernel)
  upper_error := v1808_upper_checked
  lower_error := reuse_lower_error 20 79 Primitive.Addresses.material1808

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
