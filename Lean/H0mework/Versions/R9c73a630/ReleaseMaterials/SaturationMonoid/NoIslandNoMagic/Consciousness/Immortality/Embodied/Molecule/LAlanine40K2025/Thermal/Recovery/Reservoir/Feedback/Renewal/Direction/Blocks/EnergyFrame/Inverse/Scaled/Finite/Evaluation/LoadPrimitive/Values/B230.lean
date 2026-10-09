import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B153
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B154

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3681_pa : Scalar.QComplex := ((999999169599978725655347879518 : Int)/10^30,(-1288720044456705876920593887 : Int)/10^30)
theorem v3681_pa_checked : Scalar.distance (sourceCoefficient 51 61 1 0) v3681_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3681_pb : Scalar.QComplex := ((-556053728912045350194391 : Int)/10^30,(-431477161821779561296427842 : Int)/10^30)
theorem v3681_pb_checked : Scalar.distance (sourceCoefficient 51 61 1 1) v3681_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3681_pg : Scalar.QComplex := ((-93086352503085122846639 : Int)/10^30,(119962347952824746046 : Int)/10^30)
theorem v3681_pg_checked : Scalar.distance (sourceCoefficient 51 61 1 2) v3681_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3681_mb : Scalar.QComplex := ((-928398879510043713458251 : Int)/10^30,(-431476521313788413778636300 : Int)/10^30)
theorem v3681_mb_checked : Scalar.distance (sourceCoefficient 51 61 3 1) v3681_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3681_mg : Scalar.QComplex := ((-93086214320678449772954 : Int)/10^30,(200291633041836971443 : Int)/10^30)
theorem v3681_mg_checked : Scalar.distance (sourceCoefficient 51 61 3 2) v3681_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3681_upper : Scalar.QComplex := ((999995456004798797530165715446 : Int)/10^30,(-3014625972573140144956979018 : Int)/10^30)
theorem v3681_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 61 5) 1) 14) v3681_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3681 : Material (51 : Basis) (61 : Basis) where
  plus := ![v3681_pa,v3681_pb,v3681_pg]
  minus := ![(Primitive.Addresses.material3681 1).one,v3681_mb,v3681_mg]
  upper := v3681_upper
  lower := (Primitive.Addresses.material3681 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3681_pa_checked.trans (by decide +kernel)
    · exact v3681_pb_checked.trans (by decide +kernel)
    · exact v3681_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 61 Primitive.Addresses.material3681
    · exact v3681_mb_checked.trans (by decide +kernel)
    · exact v3681_mg_checked.trans (by decide +kernel)
  upper_error := v3681_upper_checked
  lower_error := reuse_lower_error 51 61 Primitive.Addresses.material3681

def v3682_pa : Scalar.QComplex := ((999999158592398222142519354478 : Int)/10^30,(-1297233400583319328420463144 : Int)/10^30)
theorem v3682_pa_checked : Scalar.distance (sourceCoefficient 51 62 1 0) v3682_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3682_pb : Scalar.QComplex := ((-559727050518997652678842 : Int)/10^30,(-431477156931600327192652614 : Int)/10^30)
theorem v3682_pb_checked : Scalar.distance (sourceCoefficient 51 62 1 1) v3682_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3682_pg : Scalar.QComplex := ((-93086351463256309696841 : Int)/10^30,(120754825860602456192 : Int)/10^30)
theorem v3682_pg_checked : Scalar.distance (sourceCoefficient 51 62 1 2) v3682_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3682_mb : Scalar.QComplex := ((-932072195529246069048776 : Int)/10^30,(-431476513253699893975990978 : Int)/10^30)
theorem v3682_mb_checked : Scalar.distance (sourceCoefficient 51 62 3 1) v3682_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3682_mg : Scalar.QComplex := ((-93086212596977281266802 : Int)/10^30,(201084109757213504897 : Int)/10^30)
theorem v3682_mg_checked : Scalar.distance (sourceCoefficient 51 62 3 2) v3682_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3682_upper : Scalar.QComplex := ((999995430303954339615368246213 : Int)/10^30,(-3023139297022024345765861542 : Int)/10^30)
theorem v3682_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 62 5) 1) 14) v3682_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3682 : Material (51 : Basis) (62 : Basis) where
  plus := ![v3682_pa,v3682_pb,v3682_pg]
  minus := ![(Primitive.Addresses.material3682 1).one,v3682_mb,v3682_mg]
  upper := v3682_upper
  lower := (Primitive.Addresses.material3682 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3682_pa_checked.trans (by decide +kernel)
    · exact v3682_pb_checked.trans (by decide +kernel)
    · exact v3682_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 62 Primitive.Addresses.material3682
    · exact v3682_mb_checked.trans (by decide +kernel)
    · exact v3682_mg_checked.trans (by decide +kernel)
  upper_error := v3682_upper_checked
  lower_error := reuse_lower_error 51 62 Primitive.Addresses.material3682

def v3683_pa : Scalar.QComplex := ((999999126119870499697960710210 : Int)/10^30,(-1322028553146309069201136386 : Int)/10^30)
theorem v3683_pa_checked : Scalar.distance (sourceCoefficient 51 63 1 0) v3683_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3683_pb : Scalar.QComplex := ((-570425600834303239140784 : Int)/10^30,(-431477142451382661383897326 : Int)/10^30)
theorem v3683_pb_checked : Scalar.distance (sourceCoefficient 51 63 1 1) v3683_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3683_pg : Scalar.QComplex := ((-93086348389908294234453 : Int)/10^30,(123062918021822456613 : Int)/10^30)
theorem v3683_pg_checked : Scalar.distance (sourceCoefficient 51 63 1 2) v3683_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3683_mb : Scalar.QComplex := ((-942770729365216744419740 : Int)/10^30,(-431476489541120542524611083 : Int)/10^30)
theorem v3683_mb_checked : Scalar.distance (sourceCoefficient 51 63 3 1) v3683_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3683_mg : Scalar.QComplex := ((-93086207531850827631519 : Int)/10^30,(203392198406864389785 : Int)/10^30)
theorem v3683_mg_checked : Scalar.distance (sourceCoefficient 51 63 3 2) v3683_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3683_upper : Scalar.QComplex := ((999995355037291056135244848459 : Int)/10^30,(-3047934356610910022959075231 : Int)/10^30)
theorem v3683_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 63 5) 1) 14) v3683_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3683 : Material (51 : Basis) (63 : Basis) where
  plus := ![v3683_pa,v3683_pb,v3683_pg]
  minus := ![(Primitive.Addresses.material3683 1).one,v3683_mb,v3683_mg]
  upper := v3683_upper
  lower := (Primitive.Addresses.material3683 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3683_pa_checked.trans (by decide +kernel)
    · exact v3683_pb_checked.trans (by decide +kernel)
    · exact v3683_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 63 Primitive.Addresses.material3683
    · exact v3683_mb_checked.trans (by decide +kernel)
    · exact v3683_mg_checked.trans (by decide +kernel)
  upper_error := v3683_upper_checked
  lower_error := reuse_lower_error 51 63 Primitive.Addresses.material3683

def v3684_pa : Scalar.QComplex := ((999999078642886243590043489331 : Int)/10^30,(-1357465792796963574181922957 : Int)/10^30)
theorem v3684_pa_checked : Scalar.distance (sourceCoefficient 51 64 1 0) v3684_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3684_pb : Scalar.QComplex := ((-585715971978715047433875 : Int)/10^30,(-431477121142266011113907911 : Int)/10^30)
theorem v3684_pb_checked : Scalar.distance (sourceCoefficient 51 64 1 1) v3684_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3684_pg : Scalar.QComplex := ((-93086343881575497918014 : Int)/10^30,(126361644019973286574 : Int)/10^30)
theorem v3684_pg_checked : Scalar.distance (sourceCoefficient 51 64 1 2) v3684_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3684_mb : Scalar.QComplex := ((-958061076427516628969560 : Int)/10^30,(-431476455037110181737587243 : Int)/10^30)
theorem v3684_mb_checked : Scalar.distance (sourceCoefficient 51 64 3 1) v3684_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3684_mg : Scalar.QComplex := ((-93086200176867742673067 : Int)/10^30,(206690919286260615959 : Int)/10^30)
theorem v3684_mg_checked : Scalar.distance (sourceCoefficient 51 64 3 2) v3684_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3684_upper : Scalar.QComplex := ((999995246398916715656808716069 : Int)/10^30,(-3083371461540991071201021523 : Int)/10^30)
theorem v3684_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 64 5) 1) 14) v3684_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3684 : Material (51 : Basis) (64 : Basis) where
  plus := ![v3684_pa,v3684_pb,v3684_pg]
  minus := ![(Primitive.Addresses.material3684 1).one,v3684_mb,v3684_mg]
  upper := v3684_upper
  lower := (Primitive.Addresses.material3684 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3684_pa_checked.trans (by decide +kernel)
    · exact v3684_pb_checked.trans (by decide +kernel)
    · exact v3684_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 64 Primitive.Addresses.material3684
    · exact v3684_mb_checked.trans (by decide +kernel)
    · exact v3684_mg_checked.trans (by decide +kernel)
  upper_error := v3684_upper_checked
  lower_error := reuse_lower_error 51 64 Primitive.Addresses.material3684

def v3685_pa : Scalar.QComplex := ((999999029172633208013760913282 : Int)/10^30,(-1393432377648157121331027974 : Int)/10^30)
theorem v3685_pa_checked : Scalar.distance (sourceCoefficient 51 65 1 0) v3685_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3685_pb : Scalar.QComplex := ((-601234743343464675734888 : Int)/10^30,(-431477098776108758007145248 : Int)/10^30)
theorem v3685_pb_checked : Scalar.distance (sourceCoefficient 51 65 1 1) v3685_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3685_pg : Scalar.QComplex := ((-93086339166447244446434 : Int)/10^30,(129709644836938300672 : Int)/10^30)
theorem v3685_pg_checked : Scalar.distance (sourceCoefficient 51 65 1 2) v3685_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3685_mb : Scalar.QComplex := ((-973579822712932060183143 : Int)/10^30,(-431476419278960508310838450 : Int)/10^30)
theorem v3685_mb_checked : Scalar.distance (sourceCoefficient 51 65 3 1) v3685_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3685_mg : Scalar.QComplex := ((-93086192572567328177689 : Int)/10^30,(210038914787668593452 : Int)/10^30)
theorem v3685_mg_checked : Scalar.distance (sourceCoefficient 51 65 3 2) v3685_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3685_upper : Scalar.QComplex := ((999995134853674770140788684350 : Int)/10^30,(-3119337907443012581232357699 : Int)/10^30)
theorem v3685_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 65 5) 1) 14) v3685_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3685 : Material (51 : Basis) (65 : Basis) where
  plus := ![v3685_pa,v3685_pb,v3685_pg]
  minus := ![(Primitive.Addresses.material3685 1).one,v3685_mb,v3685_mg]
  upper := v3685_upper
  lower := (Primitive.Addresses.material3685 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3685_pa_checked.trans (by decide +kernel)
    · exact v3685_pb_checked.trans (by decide +kernel)
    · exact v3685_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 65 Primitive.Addresses.material3685
    · exact v3685_mb_checked.trans (by decide +kernel)
    · exact v3685_mg_checked.trans (by decide +kernel)
  upper_error := v3685_upper_checked
  lower_error := reuse_lower_error 51 65 Primitive.Addresses.material3685

def v3686_pa : Scalar.QComplex := ((999999004510887478503024504139 : Int)/10^30,(-1411019926877158174655235219 : Int)/10^30)
theorem v3686_pa_checked : Scalar.distance (sourceCoefficient 51 66 1 0) v3686_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3686_pb : Scalar.QComplex := ((-608823374626678967716737 : Int)/10^30,(-431477087568191027604481753 : Int)/10^30)
theorem v3686_pb_checked : Scalar.distance (sourceCoefficient 51 66 1 1) v3686_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3686_pg : Scalar.QComplex := ((-93086336809619116675882 : Int)/10^30,(131346806912687529425 : Int)/10^30)
theorem v3686_pg_checked : Scalar.distance (sourceCoefficient 51 66 1 2) v3686_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3686_mb : Scalar.QComplex := ((-981168441498623892380078 : Int)/10^30,(-431476401522399932979792404 : Int)/10^30)
theorem v3686_mb_checked : Scalar.distance (sourceCoefficient 51 66 3 1) v3686_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3686_mg : Scalar.QComplex := ((-93086188802942941633095 : Int)/10^30,(211676074219991032733 : Int)/10^30)
theorem v3686_mg_checked : Scalar.distance (sourceCoefficient 51 66 3 2) v3686_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3686_upper : Scalar.QComplex := ((999995079837451332149984767754 : Int)/10^30,(-3136925387913489203579272036 : Int)/10^30)
theorem v3686_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 66 5) 1) 14) v3686_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3686 : Material (51 : Basis) (66 : Basis) where
  plus := ![v3686_pa,v3686_pb,v3686_pg]
  minus := ![(Primitive.Addresses.material3686 1).one,v3686_mb,v3686_mg]
  upper := v3686_upper
  lower := (Primitive.Addresses.material3686 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3686_pa_checked.trans (by decide +kernel)
    · exact v3686_pb_checked.trans (by decide +kernel)
    · exact v3686_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 66 Primitive.Addresses.material3686
    · exact v3686_mb_checked.trans (by decide +kernel)
    · exact v3686_mg_checked.trans (by decide +kernel)
  upper_error := v3686_upper_checked
  lower_error := reuse_lower_error 51 66 Primitive.Addresses.material3686

def v3687_pa : Scalar.QComplex := ((999998962425962812240171424003 : Int)/10^30,(-1440537051871848595473945468 : Int)/10^30)
theorem v3687_pa_checked : Scalar.distance (sourceCoefficient 51 67 1 0) v3687_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3687_pb : Scalar.QComplex := ((-621559348916627523766915 : Int)/10^30,(-431477068358029925131774952 : Int)/10^30)
theorem v3687_pb_checked : Scalar.distance (sourceCoefficient 51 67 1 1) v3687_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3687_pg : Scalar.QComplex := ((-93086332778663153590307 : Int)/10^30,(134094450523457637584 : Int)/10^30)
theorem v3687_pg_checked : Scalar.distance (sourceCoefficient 51 67 1 2) v3687_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3687_mb : Scalar.QComplex := ((-993904394468883319607489 : Int)/10^30,(-431476371321673778091134877 : Int)/10^30)
theorem v3687_mb_checked : Scalar.distance (sourceCoefficient 51 67 3 1) v3687_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3687_mg : Scalar.QComplex := ((-93086182400895792636487 : Int)/10^30,(214423713329154402460 : Int)/10^30)
theorem v3687_mg_checked : Scalar.distance (sourceCoefficient 51 67 3 2) v3687_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3687_upper : Scalar.QComplex := ((999994986808709378265019434864 : Int)/10^30,(-3166442396311127210446905621 : Int)/10^30)
theorem v3687_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 67 5) 1) 14) v3687_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3687 : Material (51 : Basis) (67 : Basis) where
  plus := ![v3687_pa,v3687_pb,v3687_pg]
  minus := ![(Primitive.Addresses.material3687 1).one,v3687_mb,v3687_mg]
  upper := v3687_upper
  lower := (Primitive.Addresses.material3687 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3687_pa_checked.trans (by decide +kernel)
    · exact v3687_pb_checked.trans (by decide +kernel)
    · exact v3687_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 67 Primitive.Addresses.material3687
    · exact v3687_mb_checked.trans (by decide +kernel)
    · exact v3687_mg_checked.trans (by decide +kernel)
  upper_error := v3687_upper_checked
  lower_error := reuse_lower_error 51 67 Primitive.Addresses.material3687

def v3688_pa : Scalar.QComplex := ((999998890403814442981149656898 : Int)/10^30,(-1489694982172640164659624087 : Int)/10^30)
theorem v3688_pa_checked : Scalar.distance (sourceCoefficient 51 68 1 0) v3688_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3688_pb : Scalar.QComplex := ((-642769887553927319743915 : Int)/10^30,(-431477035252859321626778253 : Int)/10^30)
theorem v3688_pb_checked : Scalar.distance (sourceCoefficient 51 68 1 1) v3688_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3688_pg : Scalar.QComplex := ((-93086325855486420136691 : Int)/10^30,(138670386403937219397 : Int)/10^30)
theorem v3688_pg_checked : Scalar.distance (sourceCoefficient 51 68 1 2) v3688_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3688_mb : Scalar.QComplex := ((-1015114896640258982124816 : Int)/10^30,(-431476319912775944362707255 : Int)/10^30)
theorem v3688_mb_checked : Scalar.distance (sourceCoefficient 51 68 3 1) v3688_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3688_mg : Scalar.QComplex := ((-93086171528895064645637 : Int)/10^30,(218999641531414212704 : Int)/10^30)
theorem v3688_mg_checked : Scalar.distance (sourceCoefficient 51 68 3 2) v3688_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3688_upper : Scalar.QComplex := ((999994829944540150970047825909 : Int)/10^30,(-3215600129093261805652658547 : Int)/10^30)
theorem v3688_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 68 5) 1) 14) v3688_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3688 : Material (51 : Basis) (68 : Basis) where
  plus := ![v3688_pa,v3688_pb,v3688_pg]
  minus := ![(Primitive.Addresses.material3688 1).one,v3688_mb,v3688_mg]
  upper := v3688_upper
  lower := (Primitive.Addresses.material3688 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3688_pa_checked.trans (by decide +kernel)
    · exact v3688_pb_checked.trans (by decide +kernel)
    · exact v3688_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 68 Primitive.Addresses.material3688
    · exact v3688_mb_checked.trans (by decide +kernel)
    · exact v3688_mg_checked.trans (by decide +kernel)
  upper_error := v3688_upper_checked
  lower_error := reuse_lower_error 51 68 Primitive.Addresses.material3688

def v3689_pa : Scalar.QComplex := ((999998857939641107393312551269 : Int)/10^30,(-1511330345584098308317464344 : Int)/10^30)
theorem v3689_pa_checked : Scalar.distance (sourceCoefficient 51 69 1 0) v3689_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3689_pb : Scalar.QComplex := ((-652105058857350158429809 : Int)/10^30,(-431477020242048806688149134 : Int)/10^30)
theorem v3689_pb_checked : Scalar.distance (sourceCoefficient 51 69 1 1) v3689_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3689_pg : Scalar.QComplex := ((-93086322725292520423279 : Int)/10^30,(140684344963582748429 : Int)/10^30)
theorem v3689_pg_checked : Scalar.distance (sourceCoefficient 51 69 1 2) v3689_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3689_mb : Scalar.QComplex := ((-1024450051514117493558418 : Int)/10^30,(-431476296846138624288971863 : Int)/10^30)
theorem v3689_mb_checked : Scalar.distance (sourceCoefficient 51 69 3 1) v3689_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3689_mg : Scalar.QComplex := ((-93086166660746798798766 : Int)/10^30,(221013596639954570774 : Int)/10^30)
theorem v3689_mg_checked : Scalar.distance (sourceCoefficient 51 69 3 2) v3689_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3689_upper : Scalar.QComplex := ((999994760139740663614694662175 : Int)/10^30,(-3237235404251169565832645270 : Int)/10^30)
theorem v3689_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 69 5) 1) 14) v3689_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3689 : Material (51 : Basis) (69 : Basis) where
  plus := ![v3689_pa,v3689_pb,v3689_pg]
  minus := ![(Primitive.Addresses.material3689 1).one,v3689_mb,v3689_mg]
  upper := v3689_upper
  lower := (Primitive.Addresses.material3689 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3689_pa_checked.trans (by decide +kernel)
    · exact v3689_pb_checked.trans (by decide +kernel)
    · exact v3689_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 69 Primitive.Addresses.material3689
    · exact v3689_mb_checked.trans (by decide +kernel)
    · exact v3689_mg_checked.trans (by decide +kernel)
  upper_error := v3689_upper_checked
  lower_error := reuse_lower_error 51 69 Primitive.Addresses.material3689

def v3690_pa : Scalar.QComplex := ((999998836329164451595914437564 : Int)/10^30,(-1525562295341293057484579736 : Int)/10^30)
theorem v3690_pa_checked : Scalar.distance (sourceCoefficient 51 70 1 0) v3690_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3690_pb : Scalar.QComplex := ((-658245824081151281763351 : Int)/10^30,(-431477010220957951080991755 : Int)/10^30)
theorem v3690_pb_checked : Scalar.distance (sourceCoefficient 51 70 1 1) v3690_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3690_pg : Scalar.QComplex := ((-93086320638502550365772 : Int)/10^30,(142009146230051380119 : Int)/10^30)
theorem v3690_pg_checked : Scalar.distance (sourceCoefficient 51 70 1 2) v3690_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3690_mb : Scalar.QComplex := ((-1030590805803681002024723 : Int)/10^30,(-431476281525847681650483540 : Int)/10^30)
theorem v3690_mb_checked : Scalar.distance (sourceCoefficient 51 70 3 1) v3690_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3690_mg : Scalar.QComplex := ((-93086163430713779620211 : Int)/10^30,(222338395612333385921 : Int)/10^30)
theorem v3690_mg_checked : Scalar.distance (sourceCoefficient 51 70 3 2) v3690_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3690_upper : Scalar.QComplex := ((999994713966242025561949534931 : Int)/10^30,(-3251467295513824733135784932 : Int)/10^30)
theorem v3690_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 70 5) 1) 14) v3690_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3690 : Material (51 : Basis) (70 : Basis) where
  plus := ![v3690_pa,v3690_pb,v3690_pg]
  minus := ![(Primitive.Addresses.material3690 1).one,v3690_mb,v3690_mg]
  upper := v3690_upper
  lower := (Primitive.Addresses.material3690 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3690_pa_checked.trans (by decide +kernel)
    · exact v3690_pb_checked.trans (by decide +kernel)
    · exact v3690_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 70 Primitive.Addresses.material3690
    · exact v3690_mb_checked.trans (by decide +kernel)
    · exact v3690_mg_checked.trans (by decide +kernel)
  upper_error := v3690_upper_checked
  lower_error := reuse_lower_error 51 70 Primitive.Addresses.material3690

def v3691_pa : Scalar.QComplex := ((999998798973889420382772604660 : Int)/10^30,(-1549855083127295537531081411 : Int)/10^30)
theorem v3691_pa_checked : Scalar.distance (sourceCoefficient 51 71 1 0) v3691_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3691_pb : Scalar.QComplex := ((-668727613775045229550280 : Int)/10^30,(-431476992846559657592548266 : Int)/10^30)
theorem v3691_pb_checked : Scalar.distance (sourceCoefficient 51 71 1 1) v3691_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3691_pg : Scalar.QComplex := ((-93086317025702292437076 : Int)/10^30,(144270474884490934335 : Int)/10^30)
theorem v3691_pg_checked : Scalar.distance (sourceCoefficient 51 71 1 2) v3691_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3691_mb : Scalar.QComplex := ((-1041072576601402391891130 : Int)/10^30,(-431476255106143433897391885 : Int)/10^30)
theorem v3691_mb_checked : Scalar.distance (sourceCoefficient 51 71 3 1) v3691_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3691_mg : Scalar.QComplex := ((-93086157866490084582707 : Int)/10^30,(224599720307093026155 : Int)/10^30)
theorem v3691_mg_checked : Scalar.distance (sourceCoefficient 51 71 3 2) v3691_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3691_upper : Scalar.QComplex := ((999994634683874736495241242675 : Int)/10^30,(-3275759982646757577446354415 : Int)/10^30)
theorem v3691_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 71 5) 1) 14) v3691_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3691 : Material (51 : Basis) (71 : Basis) where
  plus := ![v3691_pa,v3691_pb,v3691_pg]
  minus := ![(Primitive.Addresses.material3691 1).one,v3691_mb,v3691_mg]
  upper := v3691_upper
  lower := (Primitive.Addresses.material3691 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3691_pa_checked.trans (by decide +kernel)
    · exact v3691_pb_checked.trans (by decide +kernel)
    · exact v3691_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 71 Primitive.Addresses.material3691
    · exact v3691_mb_checked.trans (by decide +kernel)
    · exact v3691_mg_checked.trans (by decide +kernel)
  upper_error := v3691_upper_checked
  lower_error := reuse_lower_error 51 71 Primitive.Addresses.material3691

def v3692_pa : Scalar.QComplex := ((999998757768145635323096878887 : Int)/10^30,(-1576217677095829872782601852 : Int)/10^30)
theorem v3692_pa_checked : Scalar.distance (sourceCoefficient 51 72 1 0) v3692_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3692_pb : Scalar.QComplex := ((-680102477905207821780463 : Int)/10^30,(-431476973607686010041493806 : Int)/10^30)
theorem v3692_pb_checked : Scalar.distance (sourceCoefficient 51 72 1 1) v3692_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3692_pg : Scalar.QComplex := ((-93086313032569029360748 : Int)/10^30,(146724474363427099499 : Int)/10^30)
theorem v3692_pg_checked : Scalar.distance (sourceCoefficient 51 72 1 2) v3692_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3692_mb : Scalar.QComplex := ((-1052447419893901740356603 : Int)/10^30,(-431476226051281510390711361 : Int)/10^30)
theorem v3692_mb_checked : Scalar.distance (sourceCoefficient 51 72 3 1) v3692_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3692_mg : Scalar.QComplex := ((-93086151755667282044163 : Int)/10^30,(227053715426398870006 : Int)/10^30)
theorem v3692_mg_checked : Scalar.distance (sourceCoefficient 51 72 3 2) v3692_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3692_upper : Scalar.QComplex := ((999994547978746728703007993419 : Int)/10^30,(-3302122466233929347251910519 : Int)/10^30)
theorem v3692_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 72 5) 1) 14) v3692_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3692 : Material (51 : Basis) (72 : Basis) where
  plus := ![v3692_pa,v3692_pb,v3692_pg]
  minus := ![(Primitive.Addresses.material3692 1).one,v3692_mb,v3692_mg]
  upper := v3692_upper
  lower := (Primitive.Addresses.material3692 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3692_pa_checked.trans (by decide +kernel)
    · exact v3692_pb_checked.trans (by decide +kernel)
    · exact v3692_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 72 Primitive.Addresses.material3692
    · exact v3692_mb_checked.trans (by decide +kernel)
    · exact v3692_mg_checked.trans (by decide +kernel)
  upper_error := v3692_upper_checked
  lower_error := reuse_lower_error 51 72 Primitive.Addresses.material3692

def v3693_pa : Scalar.QComplex := ((999998742828804062085195275496 : Int)/10^30,(-1585667307916895193211337670 : Int)/10^30)
theorem v3693_pa_checked : Scalar.distance (sourceCoefficient 51 73 1 0) v3693_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3693_pb : Scalar.QComplex := ((-684179780210393571918841 : Int)/10^30,(-431476966614196512288117887 : Int)/10^30)
theorem v3693_pb_checked : Scalar.distance (sourceCoefficient 51 73 1 1) v3693_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3693_pg : Scalar.QComplex := ((-93086311582860630538786 : Int)/10^30,(147604106655139204016 : Int)/10^30)
theorem v3693_pg_checked : Scalar.distance (sourceCoefficient 51 73 1 2) v3693_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3693_mb : Scalar.QComplex := ((-1056524714645855038866892 : Int)/10^30,(-431476215539266362136769776 : Int)/10^30)
theorem v3693_mb_checked : Scalar.distance (sourceCoefficient 51 73 3 1) v3693_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3693_mg : Scalar.QComplex := ((-93086149546876372435107 : Int)/10^30,(227933346139550615395 : Int)/10^30)
theorem v3693_mg_checked : Scalar.distance (sourceCoefficient 51 73 3 2) v3693_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3693_upper : Scalar.QComplex := ((999994516730221872512247979558 : Int)/10^30,(-3311572057196931322387550698 : Int)/10^30)
theorem v3693_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 73 5) 1) 14) v3693_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3693 : Material (51 : Basis) (73 : Basis) where
  plus := ![v3693_pa,v3693_pb,v3693_pg]
  minus := ![(Primitive.Addresses.material3693 1).one,v3693_mb,v3693_mg]
  upper := v3693_upper
  lower := (Primitive.Addresses.material3693 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3693_pa_checked.trans (by decide +kernel)
    · exact v3693_pb_checked.trans (by decide +kernel)
    · exact v3693_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 73 Primitive.Addresses.material3693
    · exact v3693_mb_checked.trans (by decide +kernel)
    · exact v3693_mg_checked.trans (by decide +kernel)
  upper_error := v3693_upper_checked
  lower_error := reuse_lower_error 51 73 Primitive.Addresses.material3693

def v3694_pa : Scalar.QComplex := ((999998725911600751770098501330 : Int)/10^30,(-1596300465199208887357173976 : Int)/10^30)
theorem v3694_pa_checked : Scalar.distance (sourceCoefficient 51 74 1 0) v3694_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3694_pb : Scalar.QComplex := ((-688767747420009062909821 : Int)/10^30,(-431476958683375597389035672 : Int)/10^30)
theorem v3694_pb_checked : Scalar.distance (sourceCoefficient 51 74 1 1) v3694_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3694_pg : Scalar.QComplex := ((-93086309939986824003865 : Int)/10^30,(148593909182654598048 : Int)/10^30)
theorem v3694_pg_checked : Scalar.distance (sourceCoefficient 51 74 1 2) v3694_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3694_mb : Scalar.QComplex := ((-1061112673303219398614669 : Int)/10^30,(-431476203649239332719094488 : Int)/10^30)
theorem v3694_mb_checked : Scalar.distance (sourceCoefficient 51 74 3 1) v3694_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3694_mg : Scalar.QComplex := ((-93086147049848175422390 : Int)/10^30,(228923146880791189473 : Int)/10^30)
theorem v3694_mg_checked : Scalar.distance (sourceCoefficient 51 74 3 2) v3694_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3694_upper : Scalar.QComplex := ((999994481461178921604167512721 : Int)/10^30,(-3322205169444848106014992739 : Int)/10^30)
theorem v3694_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 74 5) 1) 14) v3694_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3694 : Material (51 : Basis) (74 : Basis) where
  plus := ![v3694_pa,v3694_pb,v3694_pg]
  minus := ![(Primitive.Addresses.material3694 1).one,v3694_mb,v3694_mg]
  upper := v3694_upper
  lower := (Primitive.Addresses.material3694 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3694_pa_checked.trans (by decide +kernel)
    · exact v3694_pb_checked.trans (by decide +kernel)
    · exact v3694_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 74 Primitive.Addresses.material3694
    · exact v3694_mb_checked.trans (by decide +kernel)
    · exact v3694_mg_checked.trans (by decide +kernel)
  upper_error := v3694_upper_checked
  lower_error := reuse_lower_error 51 74 Primitive.Addresses.material3694

def v3695_pa : Scalar.QComplex := ((999998702152459648736865593883 : Int)/10^30,(-1611115575088977989049831988 : Int)/10^30)
theorem v3695_pa_checked : Scalar.distance (sourceCoefficient 51 75 1 0) v3695_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3695_pb : Scalar.QComplex := ((-695160132661186205881207 : Int)/10^30,(-431476947524963210780690461 : Int)/10^30)
theorem v3695_pb_checked : Scalar.distance (sourceCoefficient 51 75 1 1) v3695_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3695_pg : Scalar.QComplex := ((-93086307630508928232726 : Int)/10^30,(149972994693119193491 : Int)/10^30)
theorem v3695_pg_checked : Scalar.distance (sourceCoefficient 51 75 1 2) v3695_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3695_mb : Scalar.QComplex := ((-1067505046535012036453084 : Int)/10^30,(-431476186974490540105596313 : Int)/10^30)
theorem v3695_mb_checked : Scalar.distance (sourceCoefficient 51 75 3 1) v3695_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3695_mg : Scalar.QComplex := ((-93086143550282455750170 : Int)/10^30,(230302229884783813021 : Int)/10^30)
theorem v3695_mg_checked : Scalar.distance (sourceCoefficient 51 75 3 2) v3695_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3695_upper : Scalar.QComplex := ((999994432132537551549514195351 : Int)/10^30,(-3337020216263129200562337820 : Int)/10^30)
theorem v3695_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 75 5) 1) 14) v3695_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3695 : Material (51 : Basis) (75 : Basis) where
  plus := ![v3695_pa,v3695_pb,v3695_pg]
  minus := ![(Primitive.Addresses.material3695 1).one,v3695_mb,v3695_mg]
  upper := v3695_upper
  lower := (Primitive.Addresses.material3695 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3695_pa_checked.trans (by decide +kernel)
    · exact v3695_pb_checked.trans (by decide +kernel)
    · exact v3695_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 75 Primitive.Addresses.material3695
    · exact v3695_mb_checked.trans (by decide +kernel)
    · exact v3695_mg_checked.trans (by decide +kernel)
  upper_error := v3695_upper_checked
  lower_error := reuse_lower_error 51 75 Primitive.Addresses.material3695

def v3696_pa : Scalar.QComplex := ((999998682048740396744469787906 : Int)/10^30,(-1623545743799967088139009318 : Int)/10^30)
theorem v3696_pa_checked : Scalar.distance (sourceCoefficient 51 76 1 0) v3696_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3696_pb : Scalar.QComplex := ((-700523469599740965957916 : Int)/10^30,(-431476938065418262498008753 : Int)/10^30)
theorem v3696_pb_checked : Scalar.distance (sourceCoefficient 51 76 1 1) v3696_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3696_pg : Scalar.QComplex := ((-93086305674421903554557 : Int)/10^30,(151130074565842544384 : Int)/10^30)
theorem v3696_pg_checked : Scalar.distance (sourceCoefficient 51 76 1 2) v3696_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3696_mb : Scalar.QComplex := ((-1072868373313390089419848 : Int)/10^30,(-431476172886630891799805825 : Int)/10^30)
theorem v3696_mb_checked : Scalar.distance (sourceCoefficient 51 76 3 1) v3696_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3696_mg : Scalar.QComplex := ((-93086140595688342195291 : Int)/10^30,(231459307638658442729 : Int)/10^30)
theorem v3696_mg_checked : Scalar.distance (sourceCoefficient 51 76 3 2) v3696_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3696_upper : Scalar.QComplex := ((999994390575504702614905365633 : Int)/10^30,(-3349450331763646521044960744 : Int)/10^30)
theorem v3696_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 76 5) 1) 14) v3696_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3696 : Material (51 : Basis) (76 : Basis) where
  plus := ![v3696_pa,v3696_pb,v3696_pg]
  minus := ![(Primitive.Addresses.material3696 1).one,v3696_mb,v3696_mg]
  upper := v3696_upper
  lower := (Primitive.Addresses.material3696 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3696_pa_checked.trans (by decide +kernel)
    · exact v3696_pb_checked.trans (by decide +kernel)
    · exact v3696_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 76 Primitive.Addresses.material3696
    · exact v3696_mb_checked.trans (by decide +kernel)
    · exact v3696_mg_checked.trans (by decide +kernel)
  upper_error := v3696_upper_checked
  lower_error := reuse_lower_error 51 76 Primitive.Addresses.material3696

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
