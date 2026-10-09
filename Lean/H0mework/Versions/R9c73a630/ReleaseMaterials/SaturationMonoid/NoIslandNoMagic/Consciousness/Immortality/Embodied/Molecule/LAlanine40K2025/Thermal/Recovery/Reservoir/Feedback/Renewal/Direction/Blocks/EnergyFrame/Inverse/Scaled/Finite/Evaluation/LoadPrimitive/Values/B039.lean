import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B026

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v625_pa : Scalar.QComplex := ((999999825802096724483465338855 : Int)/10^30,(-590250604579210544442400416 : Int)/10^30)
theorem v625_pa_checked : Scalar.distance (sourceCoefficient 6 65 1 0) v625_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v625_pb : Scalar.QComplex := ((-254679823600295201284710 : Int)/10^30,(-431477371238213388470182724 : Int)/10^30)
theorem v625_pb_checked : Scalar.distance (sourceCoefficient 6 65 1 1) v625_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v625_pg : Scalar.QComplex := ((-93086405634463267963418 : Int)/10^30,(54944316775032353935 : Int)/10^30)
theorem v625_pg_checked : Scalar.distance (sourceCoefficient 6 65 1 2) v625_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v625_mb : Scalar.QComplex := ((-627025267130522606804005 : Int)/10^30,(-431476990802251172855843118 : Int)/10^30)
theorem v625_mb_checked : Scalar.distance (sourceCoefficient 6 65 3 1) v625_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v625_mg : Scalar.QComplex := ((-93086323559669414663745 : Int)/10^30,(135273671923215448437 : Int)/10^30)
theorem v625_mg_checked : Scalar.distance (sourceCoefficient 6 65 3 2) v625_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v625_upper : Scalar.QComplex := ((999997317700828036335199566835 : Int)/10^30,(-2316158705529153000900362392 : Int)/10^30)
theorem v625_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 65 5) 1) 14) v625_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material625 : Material (6 : Basis) (65 : Basis) where
  plus := ![v625_pa,v625_pb,v625_pg]
  minus := ![(Primitive.Addresses.material625 1).one,v625_mb,v625_mg]
  upper := v625_upper
  lower := (Primitive.Addresses.material625 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v625_pa_checked.trans (by decide +kernel)
    · exact v625_pb_checked.trans (by decide +kernel)
    · exact v625_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 65 Primitive.Addresses.material625
    · exact v625_mb_checked.trans (by decide +kernel)
    · exact v625_mg_checked.trans (by decide +kernel)
  upper_error := v625_upper_checked
  lower_error := reuse_lower_error 6 65 Primitive.Addresses.material625

def v626_pa : Scalar.QComplex := ((999999815266363732465037396899 : Int)/10^30,(-607838167943206373786869652 : Int)/10^30)
theorem v626_pa_checked : Scalar.distance (sourceCoefficient 6 66 1 0) v626_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v626_pb : Scalar.QComplex := ((-262268458949464317842388 : Int)/10^30,(-431477364093666756972859656 : Int)/10^30)
theorem v626_pb_checked : Scalar.distance (sourceCoefficient 6 66 1 1) v626_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v626_pg : Scalar.QComplex := ((-93086404373418522245858 : Int)/10^30,(56581479947261724060 : Int)/10^30)
theorem v626_pg_checked : Scalar.distance (sourceCoefficient 6 66 1 2) v626_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v626_mb : Scalar.QComplex := ((-634613893488674000550534 : Int)/10^30,(-431476977109056674715482343 : Int)/10^30)
theorem v626_mb_checked : Scalar.distance (sourceCoefficient 6 66 3 1) v626_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v626_mg : Scalar.QComplex := ((-93086320885827055948932 : Int)/10^30,(136910833397629327280 : Int)/10^30)
theorem v626_mg_checked : Scalar.distance (sourceCoefficient 6 66 3 2) v626_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v626_upper : Scalar.QComplex := ((999997276810571901081422940522 : Int)/10^30,(-2333746224514819829899955281 : Int)/10^30)
theorem v626_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 66 5) 1) 14) v626_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material626 : Material (6 : Basis) (66 : Basis) where
  plus := ![v626_pa,v626_pb,v626_pg]
  minus := ![(Primitive.Addresses.material626 1).one,v626_mb,v626_mg]
  upper := v626_upper
  lower := (Primitive.Addresses.material626 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v626_pa_checked.trans (by decide +kernel)
    · exact v626_pb_checked.trans (by decide +kernel)
    · exact v626_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 66 Primitive.Addresses.material626
    · exact v626_mb_checked.trans (by decide +kernel)
    · exact v626_mg_checked.trans (by decide +kernel)
  upper_error := v626_upper_checked
  lower_error := reuse_lower_error 6 66 Primitive.Addresses.material626

def v627_pa : Scalar.QComplex := ((999999796889079179321762735478 : Int)/10^30,(-637355317218982898088277509 : Int)/10^30)
theorem v627_pa_checked : Scalar.distance (sourceCoefficient 6 67 1 0) v627_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v627_pb : Scalar.QComplex := ((-275004440223907772151337 : Int)/10^30,(-431477351703047811183279631 : Int)/10^30)
theorem v627_pb_checked : Scalar.distance (sourceCoefficient 6 67 1 1) v627_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v627_pg : Scalar.QComplex := ((-93086402181512155074922 : Int)/10^30,(59329125441564801181 : Int)/10^30)
theorem v627_pg_checked : Scalar.distance (sourceCoefficient 6 67 1 2) v627_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v627_mb : Scalar.QComplex := ((-647349859328383465830461 : Int)/10^30,(-431476953727864109978210961 : Int)/10^30)
theorem v627_mb_checked : Scalar.distance (sourceCoefficient 6 67 3 1) v627_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v627_mg : Scalar.QComplex := ((-93086316322827192700627 : Int)/10^30,(139658475977341938200 : Int)/10^30)
theorem v627_mg_checked : Scalar.distance (sourceCoefficient 6 67 3 2) v627_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v627_upper : Scalar.QComplex := ((999997207489392843619130883761 : Int)/10^30,(-2363263298110743871358783525 : Int)/10^30)
theorem v627_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 67 5) 1) 14) v627_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material627 : Material (6 : Basis) (67 : Basis) where
  plus := ![v627_pa,v627_pb,v627_pg]
  minus := ![(Primitive.Addresses.material627 1).one,v627_mb,v627_mg]
  upper := v627_upper
  lower := (Primitive.Addresses.material627 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v627_pa_checked.trans (by decide +kernel)
    · exact v627_pb_checked.trans (by decide +kernel)
    · exact v627_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 67 Primitive.Addresses.material627
    · exact v627_mb_checked.trans (by decide +kernel)
    · exact v627_mg_checked.trans (by decide +kernel)
  upper_error := v627_upper_checked
  lower_error := reuse_lower_error 6 67 Primitive.Addresses.material627

def v628_pa : Scalar.QComplex := ((999999764349723897041382530477 : Int)/10^30,(-686513289510745456434679162 : Int)/10^30)
theorem v628_pa_checked : Scalar.distance (sourceCoefficient 6 68 1 0) v628_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v628_pb : Scalar.QComplex := ((-296214990939980316893835 : Int)/10^30,(-431477329955168326279724740 : Int)/10^30)
theorem v628_pb_checked : Scalar.distance (sourceCoefficient 6 68 1 1) v628_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v628_pg : Scalar.QComplex := ((-93086398321095531690718 : Int)/10^30,(63905064579368939048 : Int)/10^30)
theorem v628_pg_checked : Scalar.distance (sourceCoefficient 6 68 1 2) v628_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v628_mb : Scalar.QComplex := ((-668560383379358101583498 : Int)/10^30,(-431476913676242742575813390 : Int)/10^30)
theorem v628_mb_checked : Scalar.distance (sourceCoefficient 6 68 3 1) v628_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v628_mg : Scalar.QComplex := ((-93086308513582623449238 : Int)/10^30,(144234410079949125042 : Int)/10^30)
theorem v628_mg_checked : Scalar.distance (sourceCoefficient 6 68 3 2) v628_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v628_upper : Scalar.QComplex := ((999997090107885425713936297569 : Int)/10^30,(-2412421141027505932222746303 : Int)/10^30)
theorem v628_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 68 5) 1) 14) v628_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material628 : Material (6 : Basis) (68 : Basis) where
  plus := ![v628_pa,v628_pb,v628_pg]
  minus := ![(Primitive.Addresses.material628 1).one,v628_mb,v628_mg]
  upper := v628_upper
  lower := (Primitive.Addresses.material628 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v628_pa_checked.trans (by decide +kernel)
    · exact v628_pb_checked.trans (by decide +kernel)
    · exact v628_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 68 Primitive.Addresses.material628
    · exact v628_mb_checked.trans (by decide +kernel)
    · exact v628_mg_checked.trans (by decide +kernel)
  upper_error := v628_upper_checked
  lower_error := reuse_lower_error 6 68 Primitive.Addresses.material628

def v629_pa : Scalar.QComplex := ((999999749262697724731332272890 : Int)/10^30,(-708148672018342899027870978 : Int)/10^30)
theorem v629_pa_checked : Scalar.distance (sourceCoefficient 6 69 1 0) v629_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v629_pb : Scalar.QComplex := ((-305550167736439406481392 : Int)/10^30,(-431477319942923078133246857 : Int)/10^30)
theorem v629_pb_checked : Scalar.distance (sourceCoefficient 6 69 1 1) v629_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v629_pg : Scalar.QComplex := ((-93086396538882077081457 : Int)/10^30,(65919024620340615544 : Int)/10^30)
theorem v629_pg_checked : Scalar.distance (sourceCoefficient 6 69 1 2) v629_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v629_mb : Scalar.QComplex := ((-677895548059787516829440 : Int)/10^30,(-431476895608164087857047330 : Int)/10^30)
theorem v629_mb_checked : Scalar.distance (sourceCoefficient 6 69 3 1) v629_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v629_mg : Scalar.QComplex := ((-93086304993413022474044 : Int)/10^30,(146248367833061492349 : Int)/10^30)
theorem v629_mg_checked : Scalar.distance (sourceCoefficient 6 69 3 2) v629_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v629_upper : Scalar.QComplex := ((999997037680174262212891638432 : Int)/10^30,(-2434056465272904111223089282 : Int)/10^30)
theorem v629_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 69 5) 1) 14) v629_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material629 : Material (6 : Basis) (69 : Basis) where
  plus := ![v629_pa,v629_pb,v629_pg]
  minus := ![(Primitive.Addresses.material629 1).one,v629_mb,v629_mg]
  upper := v629_upper
  lower := (Primitive.Addresses.material629 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v629_pa_checked.trans (by decide +kernel)
    · exact v629_pb_checked.trans (by decide +kernel)
    · exact v629_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 69 Primitive.Addresses.material629
    · exact v629_mb_checked.trans (by decide +kernel)
    · exact v629_mg_checked.trans (by decide +kernel)
  upper_error := v629_upper_checked
  lower_error := reuse_lower_error 6 69 Primitive.Addresses.material629

def v630_pa : Scalar.QComplex := ((999999739083075380413084878114 : Int)/10^30,(-722380634542158997722130601 : Int)/10^30)
theorem v630_pa_checked : Scalar.distance (sourceCoefficient 6 70 1 0) v630_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v630_pb : Scalar.QComplex := ((-311690936632580398980212 : Int)/10^30,(-431477313209936457597578326 : Int)/10^30)
theorem v630_pb_checked : Scalar.distance (sourceCoefficient 6 70 1 1) v630_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v630_pg : Scalar.QComplex := ((-93086395338806589766308 : Int)/10^30,(67243826877141884353 : Int)/10^30)
theorem v630_pg_checked : Scalar.distance (sourceCoefficient 6 70 1 2) v630_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v630_mb : Scalar.QComplex := ((-684036308859175391230389 : Int)/10^30,(-431476883575972986914656309 : Int)/10^30)
theorem v630_mb_checked : Scalar.distance (sourceCoefficient 6 70 3 1) v630_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v630_mg : Scalar.QComplex := ((-93086302650093301261057 : Int)/10^30,(147573168560967238338 : Int)/10^30)
theorem v630_mg_checked : Scalar.distance (sourceCoefficient 6 70 3 2) v630_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v630_upper : Scalar.QComplex := ((999997002937490876694292311049 : Int)/10^30,(-2448288389030779156281014156 : Int)/10^30)
theorem v630_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 70 5) 1) 14) v630_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material630 : Material (6 : Basis) (70 : Basis) where
  plus := ![v630_pa,v630_pb,v630_pg]
  minus := ![(Primitive.Addresses.material630 1).one,v630_mb,v630_mg]
  upper := v630_upper
  lower := (Primitive.Addresses.material630 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v630_pa_checked.trans (by decide +kernel)
    · exact v630_pb_checked.trans (by decide +kernel)
    · exact v630_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 70 Primitive.Addresses.material630
    · exact v630_mb_checked.trans (by decide +kernel)
    · exact v630_mg_checked.trans (by decide +kernel)
  upper_error := v630_upper_checked
  lower_error := reuse_lower_error 6 70 Primitive.Addresses.material630

def v631_pa : Scalar.QComplex := ((999999721239344788792769173547 : Int)/10^30,(-746673444495591772797626507 : Int)/10^30)
theorem v631_pa_checked : Scalar.distance (sourceCoefficient 6 71 1 0) v631_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v631_pb : Scalar.QComplex := ((-322172732702972529745990 : Int)/10^30,(-431477301448066324337702694 : Int)/10^30)
theorem v631_pb_checked : Scalar.distance (sourceCoefficient 6 71 1 1) v631_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v631_pg : Scalar.QComplex := ((-93086393239556284774561 : Int)/10^30,(69505157251153834723 : Int)/10^30)
theorem v631_pg_checked : Scalar.distance (sourceCoefficient 6 71 1 2) v631_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v631_mb : Scalar.QComplex := ((-694518090876751613206461 : Int)/10^30,(-431476862768789306958648157 : Int)/10^30)
theorem v631_mb_checked : Scalar.distance (sourceCoefficient 6 71 3 1) v631_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v631_mg : Scalar.QComplex := ((-93086298599417511683151 : Int)/10^30,(149834496281424076076 : Int)/10^30)
theorem v631_mg_checked : Scalar.distance (sourceCoefficient 6 71 3 2) v631_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v631_upper : Scalar.QComplex := ((999996943166600708093278733941 : Int)/10^30,(-2472581132006264909089835997 : Int)/10^30)
theorem v631_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 71 5) 1) 14) v631_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material631 : Material (6 : Basis) (71 : Basis) where
  plus := ![v631_pa,v631_pb,v631_pg]
  minus := ![(Primitive.Addresses.material631 1).one,v631_mb,v631_mg]
  upper := v631_upper
  lower := (Primitive.Addresses.material631 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v631_pa_checked.trans (by decide +kernel)
    · exact v631_pb_checked.trans (by decide +kernel)
    · exact v631_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 71 Primitive.Addresses.material631
    · exact v631_mb_checked.trans (by decide +kernel)
    · exact v631_mg_checked.trans (by decide +kernel)
  upper_error := v631_upper_checked
  lower_error := reuse_lower_error 6 71 Primitive.Addresses.material631

def v632_pa : Scalar.QComplex := ((999999701207577968546447028225 : Int)/10^30,(-773036063056566360680963547 : Int)/10^30)
theorem v632_pa_checked : Scalar.distance (sourceCoefficient 6 72 1 0) v632_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v632_pb : Scalar.QComplex := ((-333547603907191424215854 : Int)/10^30,(-431477288299922289760743332 : Int)/10^30)
theorem v632_pb_checked : Scalar.distance (sourceCoefficient 6 72 1 1) v632_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v632_pg : Scalar.QComplex := ((-93086390888931223055982 : Int)/10^30,(71959158637775318037 : Int)/10^30)
theorem v632_pg_checked : Scalar.distance (sourceCoefficient 6 72 1 2) v632_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v632_mb : Scalar.QComplex := ((-705892946499329969635128 : Int)/10^30,(-431476839804648623977082561 : Int)/10^30)
theorem v632_mb_checked : Scalar.distance (sourceCoefficient 6 72 3 1) v632_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v632_mg : Scalar.QComplex := ((-93086294131100652674976 : Int)/10^30,(152288494725825129706 : Int)/10^30)
theorem v632_mg_checked : Scalar.distance (sourceCoefficient 6 72 3 2) v632_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v632_upper : Scalar.QComplex := ((999996877635375684642112740644 : Int)/10^30,(-2498943676730203657059038823 : Int)/10^30)
theorem v632_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 72 5) 1) 14) v632_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material632 : Material (6 : Basis) (72 : Basis) where
  plus := ![v632_pa,v632_pb,v632_pg]
  minus := ![(Primitive.Addresses.material632 1).one,v632_mb,v632_mg]
  upper := v632_upper
  lower := (Primitive.Addresses.material632 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v632_pa_checked.trans (by decide +kernel)
    · exact v632_pb_checked.trans (by decide +kernel)
    · exact v632_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 72 Primitive.Addresses.material632
    · exact v632_mb_checked.trans (by decide +kernel)
    · exact v632_mg_checked.trans (by decide +kernel)
  upper_error := v632_upper_checked
  lower_error := reuse_lower_error 6 72 Primitive.Addresses.material632

def v633_pa : Scalar.QComplex := ((999999693858015572913629416506 : Int)/10^30,(-782485702828657510425615511 : Int)/10^30)
theorem v633_pa_checked : Scalar.distance (sourceCoefficient 6 73 1 0) v633_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v633_pb : Scalar.QComplex := ((-337624908787154620293519 : Int)/10^30,(-431477283489645361773314288 : Int)/10^30)
theorem v633_pb_checked : Scalar.distance (sourceCoefficient 6 73 1 1) v633_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v633_pg : Scalar.QComplex := ((-93086390027977338568121 : Int)/10^30,(72838791623836594617 : Int)/10^30)
theorem v633_pg_checked : Scalar.distance (sourceCoefficient 6 73 1 2) v633_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v633_mb : Scalar.QComplex := ((-709970245710073874841375 : Int)/10^30,(-431476831475843010662298209 : Int)/10^30)
theorem v633_mb_checked : Scalar.distance (sourceCoefficient 6 73 3 1) v633_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v633_mg : Scalar.QComplex := ((-93086292511063438987745 : Int)/10^30,(153168126641394417973 : Int)/10^30)
theorem v633_mg_checked : Scalar.distance (sourceCoefficient 6 73 3 2) v633_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v633_upper : Scalar.QComplex := ((999996853976603253313359087153 : Int)/10^30,(-2508393289743488451167040908 : Int)/10^30)
theorem v633_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 73 5) 1) 14) v633_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material633 : Material (6 : Basis) (73 : Basis) where
  plus := ![v633_pa,v633_pb,v633_pg]
  minus := ![(Primitive.Addresses.material633 1).one,v633_mb,v633_mg]
  upper := v633_upper
  lower := (Primitive.Addresses.material633 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v633_pa_checked.trans (by decide +kernel)
    · exact v633_pb_checked.trans (by decide +kernel)
    · exact v633_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 73 Primitive.Addresses.material633
    · exact v633_mb_checked.trans (by decide +kernel)
    · exact v633_mg_checked.trans (by decide +kernel)
  upper_error := v633_upper_checked
  lower_error := reuse_lower_error 6 73 Primitive.Addresses.material633

def v634_pa : Scalar.QComplex := ((999999685481179350700927973079 : Int)/10^30,(-793118870268832779981401457 : Int)/10^30)
theorem v634_pa_checked : Scalar.distance (sourceCoefficient 6 74 1 0) v634_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v634_pb : Scalar.QComplex := ((-342212878918695859270364 : Int)/10^30,(-431477278015475201861044349 : Int)/10^30)
theorem v634_pb_checked : Scalar.distance (sourceCoefficient 6 74 1 1) v634_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v634_pg : Scalar.QComplex := ((-93086389047597071650566 : Int)/10^30,(73828594939317848938 : Int)/10^30)
theorem v634_pg_checked : Scalar.distance (sourceCoefficient 6 74 1 2) v634_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v634_mb : Scalar.QComplex := ((-714558209409341852719415 : Int)/10^30,(-431476822042463300017762768 : Int)/10^30)
theorem v634_mb_checked : Scalar.distance (sourceCoefficient 6 74 3 1) v634_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v634_mg : Scalar.QComplex := ((-93086290676527854936722 : Int)/10^30,(154157928742302646032 : Int)/10^30)
theorem v634_mg_checked : Scalar.distance (sourceCoefficient 6 74 3 2) v634_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v634_upper : Scalar.QComplex := ((999996827247897139086553059282 : Int)/10^30,(-2519026426889150499277562313 : Int)/10^30)
theorem v634_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 74 5) 1) 14) v634_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material634 : Material (6 : Basis) (74 : Basis) where
  plus := ![v634_pa,v634_pb,v634_pg]
  minus := ![(Primitive.Addresses.material634 1).one,v634_mb,v634_mg]
  upper := v634_upper
  lower := (Primitive.Addresses.material634 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v634_pa_checked.trans (by decide +kernel)
    · exact v634_pb_checked.trans (by decide +kernel)
    · exact v634_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 74 Primitive.Addresses.material634
    · exact v634_mb_checked.trans (by decide +kernel)
    · exact v634_mg_checked.trans (by decide +kernel)
  upper_error := v634_upper_checked
  lower_error := reuse_lower_error 6 74 Primitive.Addresses.material634

def v635_pa : Scalar.QComplex := ((999999673621277034081350456111 : Int)/10^30,(-807933994462893295469898290 : Int)/10^30)
theorem v635_pa_checked : Scalar.distance (sourceCoefficient 6 75 1 0) v635_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v635_pb : Scalar.QComplex := ((-348605268274526169395222 : Int)/10^30,(-431477270279898576966768065 : Int)/10^30)
theorem v635_pb_checked : Scalar.distance (sourceCoefficient 6 75 1 1) v635_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v635_pg : Scalar.QComplex := ((-93086387661167182031418 : Int)/10^30,(75207681559395249411 : Int)/10^30)
theorem v635_pg_checked : Scalar.distance (sourceCoefficient 6 75 1 2) v635_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v635_mb : Scalar.QComplex := ((-720950589709539229197054 : Int)/10^30,(-431476808790545443879781959 : Int)/10^30)
theorem v635_mb_checked : Scalar.distance (sourceCoefficient 6 75 3 1) v635_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v635_mg : Scalar.QComplex := ((-93086288100008840177660 : Int)/10^30,(155537013652456518221 : Int)/10^30)
theorem v635_mg_checked : Scalar.distance (sourceCoefficient 6 75 3 2) v635_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v635_upper : Scalar.QComplex := ((999996789818452145017860514549 : Int)/10^30,(-2533841508548708357898768331 : Int)/10^30)
theorem v635_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 75 5) 1) 14) v635_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material635 : Material (6 : Basis) (75 : Basis) where
  plus := ![v635_pa,v635_pb,v635_pg]
  minus := ![(Primitive.Addresses.material635 1).one,v635_mb,v635_mg]
  upper := v635_upper
  lower := (Primitive.Addresses.material635 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v635_pa_checked.trans (by decide +kernel)
    · exact v635_pb_checked.trans (by decide +kernel)
    · exact v635_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 75 Primitive.Addresses.material635
    · exact v635_mb_checked.trans (by decide +kernel)
    · exact v635_mg_checked.trans (by decide +kernel)
  upper_error := v635_upper_checked
  lower_error := reuse_lower_error 6 75 Primitive.Addresses.material635

def v636_pa : Scalar.QComplex := ((999999663501253317063355634357 : Int)/10^30,(-820364175311469076795746627 : Int)/10^30)
theorem v636_pa_checked : Scalar.distance (sourceCoefficient 6 76 1 0) v636_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v636_pb : Scalar.QComplex := ((-353968608704477876541704 : Int)/10^30,(-431477263692180192292674729 : Int)/10^30)
theorem v636_pb_checked : Scalar.distance (sourceCoefficient 6 76 1 1) v636_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v636_pg : Scalar.QComplex := ((-93086386479535600297017 : Int)/10^30,(76364762373655737455 : Int)/10^30)
theorem v636_pg_checked : Scalar.distance (sourceCoefficient 6 76 1 2) v636_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v636_mb : Scalar.QComplex := ((-726313922457569911354141 : Int)/10^30,(-431476797574508276951982614 : Int)/10^30)
theorem v636_mb_checked : Scalar.distance (sourceCoefficient 6 76 3 1) v636_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v636_mg : Scalar.QComplex := ((-93086285919869068697248 : Int)/10^30,(156694093016188101585 : Int)/10^30)
theorem v636_mg_checked : Scalar.distance (sourceCoefficient 6 76 3 2) v636_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v636_upper : Scalar.QComplex := ((999996758245079013142420306521 : Int)/10^30,(-2546271653417747062690411191 : Int)/10^30)
theorem v636_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 76 5) 1) 14) v636_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material636 : Material (6 : Basis) (76 : Basis) where
  plus := ![v636_pa,v636_pb,v636_pg]
  minus := ![(Primitive.Addresses.material636 1).one,v636_mb,v636_mg]
  upper := v636_upper
  lower := (Primitive.Addresses.material636 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v636_pa_checked.trans (by decide +kernel)
    · exact v636_pb_checked.trans (by decide +kernel)
    · exact v636_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 76 Primitive.Addresses.material636
    · exact v636_mb_checked.trans (by decide +kernel)
    · exact v636_mg_checked.trans (by decide +kernel)
  upper_error := v636_upper_checked
  lower_error := reuse_lower_error 6 76 Primitive.Addresses.material636

def v637_pa : Scalar.QComplex := ((999999661136356159595071507675 : Int)/10^30,(-823241867771702157971227900 : Int)/10^30)
theorem v637_pa_checked : Scalar.distance (sourceCoefficient 6 77 1 0) v637_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v637_pb : Scalar.QComplex := ((-355210267564850915672813 : Int)/10^30,(-431477262154395975104323590 : Int)/10^30)
theorem v637_pb_checked : Scalar.distance (sourceCoefficient 6 77 1 1) v637_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v637_pg : Scalar.QComplex := ((-93086386203585842991178 : Int)/10^30,(76632636410372427706 : Int)/10^30)
theorem v637_pg_checked : Scalar.distance (sourceCoefficient 6 77 1 2) v637_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v637_mb : Scalar.QComplex := ((-727555579528578089951681 : Int)/10^30,(-431476794965228958088183080 : Int)/10^30)
theorem v637_mb_checked : Scalar.distance (sourceCoefficient 6 77 3 1) v637_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v637_mg : Scalar.QComplex := ((-93086285412756185052366 : Int)/10^30,(156961966715030833278 : Int)/10^30)
theorem v637_mg_checked : Scalar.distance (sourceCoefficient 6 77 3 2) v637_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v637_upper : Scalar.QComplex := ((999996750913549253769039976407 : Int)/10^30,(-2549149337510397309854895022 : Int)/10^30)
theorem v637_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 77 5) 1) 14) v637_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material637 : Material (6 : Basis) (77 : Basis) where
  plus := ![v637_pa,v637_pb,v637_pg]
  minus := ![(Primitive.Addresses.material637 1).one,v637_mb,v637_mg]
  upper := v637_upper
  lower := (Primitive.Addresses.material637 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v637_pa_checked.trans (by decide +kernel)
    · exact v637_pb_checked.trans (by decide +kernel)
    · exact v637_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 77 Primitive.Addresses.material637
    · exact v637_mb_checked.trans (by decide +kernel)
    · exact v637_mg_checked.trans (by decide +kernel)
  upper_error := v637_upper_checked
  lower_error := reuse_lower_error 6 77 Primitive.Addresses.material637

def v638_pa : Scalar.QComplex := ((999999646744972148623870907461 : Int)/10^30,(-840541451038339664766326461 : Int)/10^30)
theorem v638_pa_checked : Scalar.distance (sourceCoefficient 6 78 1 0) v638_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v638_pb : Scalar.QComplex := ((-362674644283107832290127 : Int)/10^30,(-431477252809419831748346623 : Int)/10^30)
theorem v638_pb_checked : Scalar.distance (sourceCoefficient 6 78 1 1) v638_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v638_pg : Scalar.QComplex := ((-93086384525727716853446 : Int)/10^30,(78242992360898468356 : Int)/10^30)
theorem v638_pg_checked : Scalar.distance (sourceCoefficient 6 78 1 2) v638_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v638_mb : Scalar.QComplex := ((-735019945403212885878730 : Int)/10^30,(-431476779178835369485880699 : Int)/10^30)
theorem v638_mb_checked : Scalar.distance (sourceCoefficient 6 78 3 1) v638_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v638_mg : Scalar.QComplex := ((-93086282345234026093579 : Int)/10^30,(158572320618031761713 : Int)/10^30)
theorem v638_mg_checked : Scalar.distance (sourceCoefficient 6 78 3 2) v638_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v638_upper : Scalar.QComplex := ((999996706664675364791879248210 : Int)/10^30,(-2566448870173114466017386457 : Int)/10^30)
theorem v638_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 78 5) 1) 14) v638_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material638 : Material (6 : Basis) (78 : Basis) where
  plus := ![v638_pa,v638_pb,v638_pg]
  minus := ![(Primitive.Addresses.material638 1).one,v638_mb,v638_mg]
  upper := v638_upper
  lower := (Primitive.Addresses.material638 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v638_pa_checked.trans (by decide +kernel)
    · exact v638_pb_checked.trans (by decide +kernel)
    · exact v638_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 78 Primitive.Addresses.material638
    · exact v638_mb_checked.trans (by decide +kernel)
    · exact v638_mg_checked.trans (by decide +kernel)
  upper_error := v638_upper_checked
  lower_error := reuse_lower_error 6 78 Primitive.Addresses.material638

def v639_pa : Scalar.QComplex := ((999999642041652422451768875491 : Int)/10^30,(-846118530125016149796742235 : Int)/10^30)
theorem v639_pa_checked : Scalar.distance (sourceCoefficient 6 79 1 0) v639_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v639_pb : Scalar.QComplex := ((-365081027033171914676894 : Int)/10^30,(-431477249760065083882005087 : Int)/10^30)
theorem v639_pb_checked : Scalar.distance (sourceCoefficient 6 79 1 1) v639_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v639_pg : Scalar.QComplex := ((-93086383977888068836006 : Int)/10^30,(78762142579589916089 : Int)/10^30)
theorem v639_pg_checked : Scalar.distance (sourceCoefficient 6 79 1 2) v639_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v639_mb : Scalar.QComplex := ((-737426324625814883722951 : Int)/10^30,(-431476774052881823184199463 : Int)/10^30)
theorem v639_mb_checked : Scalar.distance (sourceCoefficient 6 79 3 1) v639_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v639_mg : Scalar.QComplex := ((-93086281349391324989040 : Int)/10^30,(159091470170658914232 : Int)/10^30)
theorem v639_mg_checked : Scalar.distance (sourceCoefficient 6 79 3 2) v639_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v639_upper : Scalar.QComplex := ((999996692335830088720894674395 : Int)/10^30,(-2572025932835883615632506966 : Int)/10^30)
theorem v639_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 79 5) 1) 14) v639_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material639 : Material (6 : Basis) (79 : Basis) where
  plus := ![v639_pa,v639_pb,v639_pg]
  minus := ![(Primitive.Addresses.material639 1).one,v639_mb,v639_mg]
  upper := v639_upper
  lower := (Primitive.Addresses.material639 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v639_pa_checked.trans (by decide +kernel)
    · exact v639_pb_checked.trans (by decide +kernel)
    · exact v639_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 79 Primitive.Addresses.material639
    · exact v639_mb_checked.trans (by decide +kernel)
    · exact v639_mg_checked.trans (by decide +kernel)
  upper_error := v639_upper_checked
  lower_error := reuse_lower_error 6 79 Primitive.Addresses.material639

def v640_pa : Scalar.QComplex := ((999999634632359465221515145070 : Int)/10^30,(-854830478852997040093340196 : Int)/10^30)
theorem v640_pa_checked : Scalar.distance (sourceCoefficient 6 80 1 0) v640_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v640_pb : Scalar.QComplex := ((-368840034686279787130557 : Int)/10^30,(-431477244960863183237378889 : Int)/10^30)
theorem v640_pb_checked : Scalar.distance (sourceCoefficient 6 80 1 1) v640_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v640_pg : Scalar.QComplex := ((-93086383115348787486873 : Int)/10^30,(79573106526625324070 : Int)/10^30)
theorem v640_pg_checked : Scalar.distance (sourceCoefficient 6 80 1 2) v640_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v640_mb : Scalar.QComplex := ((-741185326737777319561454 : Int)/10^30,(-431476766009827404289687403 : Int)/10^30)
theorem v640_mb_checked : Scalar.distance (sourceCoefficient 6 80 3 1) v640_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v640_mg : Scalar.QComplex := ((-93086279787027002971467 : Int)/10^30,(159902433071402829372 : Int)/10^30)
theorem v640_mg_checked : Scalar.distance (sourceCoefficient 6 80 3 2) v640_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v640_upper : Scalar.QComplex := ((999996669890515004081918374590 : Int)/10^30,(-2580737855800672774614488789 : Int)/10^30)
theorem v640_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 80 5) 1) 14) v640_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material640 : Material (6 : Basis) (80 : Basis) where
  plus := ![v640_pa,v640_pb,v640_pg]
  minus := ![(Primitive.Addresses.material640 1).one,v640_mb,v640_mg]
  upper := v640_upper
  lower := (Primitive.Addresses.material640 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v640_pa_checked.trans (by decide +kernel)
    · exact v640_pb_checked.trans (by decide +kernel)
    · exact v640_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 80 Primitive.Addresses.material640
    · exact v640_mb_checked.trans (by decide +kernel)
    · exact v640_mg_checked.trans (by decide +kernel)
  upper_error := v640_upper_checked
  lower_error := reuse_lower_error 6 80 Primitive.Addresses.material640

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
