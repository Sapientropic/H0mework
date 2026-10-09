import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B196

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4705_pa : Scalar.QComplex := ((999996288105142328015219467756 : Int)/10^30,(-2724660701294848409503558501 : Int)/10^30)
theorem v4705_pa_checked : Scalar.distance (sourceCoefficient 87 95 1 0) v4705_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4705_pb : Scalar.QComplex := ((-1175629834797698831420059 : Int)/10^30,(-431475915670771269586479204 : Int)/10^30)
theorem v4705_pb_checked : Scalar.distance (sourceCoefficient 87 95 1 1) v4705_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4705_pg : Scalar.QComplex := ((-93086083967508363013365 : Int)/10^30,(253628936267646770090 : Int)/10^30)
theorem v4705_pg_checked : Scalar.distance (sourceCoefficient 87 95 1 2) v4705_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4705_mb : Scalar.QComplex := ((-1547973679327001348802293 : Int)/10^30,(-431474740496969413661010888 : Int)/10^30)
theorem v4705_mb_checked : Scalar.distance (sourceCoefficient 87 95 3 1) v4705_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4705_mg : Scalar.QComplex := ((-93085830436956081976536 : Int)/10^30,(333957939852370950684 : Int)/10^30)
theorem v4705_mg_checked : Scalar.distance (sourceCoefficient 87 95 3 2) v4705_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4705_upper : Scalar.QComplex := ((999990096210947864125023043223 : Int)/10^30,(-4450559517547671302853030328 : Int)/10^30)
theorem v4705_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 87 95 5) 1) 14) v4705_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4705 : Material (87 : Basis) (95 : Basis) where
  plus := ![v4705_pa,v4705_pb,v4705_pg]
  minus := ![(Primitive.Addresses.material4705 1).one,v4705_mb,v4705_mg]
  upper := v4705_upper
  lower := (Primitive.Addresses.material4705 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4705_pa_checked.trans (by decide +kernel)
    · exact v4705_pb_checked.trans (by decide +kernel)
    · exact v4705_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 87 95 Primitive.Addresses.material4705
    · exact v4705_mb_checked.trans (by decide +kernel)
    · exact v4705_mg_checked.trans (by decide +kernel)
  upper_error := v4705_upper_checked
  lower_error := reuse_lower_error 87 95 Primitive.Addresses.material4705

def v4706_pa : Scalar.QComplex := ((999996229941613780582964110860 : Int)/10^30,(-2745924718396081332821581715 : Int)/10^30)
theorem v4706_pa_checked : Scalar.distance (sourceCoefficient 87 96 1 0) v4706_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4706_pb : Scalar.QComplex := ((-1184804778101659995193727 : Int)/10^30,(-431475889845415177425341036 : Int)/10^30)
theorem v4706_pb_checked : Scalar.distance (sourceCoefficient 87 96 1 1) v4706_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4706_pg : Scalar.QComplex := ((-93086078474625466190846 : Int)/10^30,(255608327480350066248 : Int)/10^30)
theorem v4706_pg_checked : Scalar.distance (sourceCoefficient 87 96 1 2) v4706_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4706_mb : Scalar.QComplex := ((-1557148596928592628213499 : Int)/10^30,(-431474706754060090248549096 : Int)/10^30)
theorem v4706_mb_checked : Scalar.distance (sourceCoefficient 87 96 3 1) v4706_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4706_mg : Scalar.QComplex := ((-93085823235949762313285 : Int)/10^30,(335937325587945886010 : Int)/10^30)
theorem v4706_mg_checked : Scalar.distance (sourceCoefficient 87 96 3 2) v4706_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4706_upper : Scalar.QComplex := ((999990001347741484270606374206 : Int)/10^30,(-4471823402593674882021072365 : Int)/10^30)
theorem v4706_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 87 96 5) 1) 14) v4706_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4706 : Material (87 : Basis) (96 : Basis) where
  plus := ![v4706_pa,v4706_pb,v4706_pg]
  minus := ![(Primitive.Addresses.material4706 1).one,v4706_mb,v4706_mg]
  upper := v4706_upper
  lower := (Primitive.Addresses.material4706 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4706_pa_checked.trans (by decide +kernel)
    · exact v4706_pb_checked.trans (by decide +kernel)
    · exact v4706_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 87 96 Primitive.Addresses.material4706
    · exact v4706_mb_checked.trans (by decide +kernel)
    · exact v4706_mg_checked.trans (by decide +kernel)
  upper_error := v4706_upper_checked
  lower_error := reuse_lower_error 87 96 Primitive.Addresses.material4706

def v4707_pa : Scalar.QComplex := ((999996026367311172283124667900 : Int)/10^30,(-2819086658458495849875178389 : Int)/10^30)
theorem v4707_pa_checked : Scalar.distance (sourceCoefficient 87 97 1 0) v4707_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4707_pb : Scalar.QComplex := ((-1216372501832633395409413 : Int)/10^30,(-431475799002298161683992853 : Int)/10^30)
theorem v4707_pb_checked : Scalar.distance (sourceCoefficient 87 97 1 1) v4707_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4707_pg : Scalar.QComplex := ((-93086059200431755459043 : Int)/10^30,(262418710335980432542 : Int)/10^30)
theorem v4707_pg_checked : Scalar.distance (sourceCoefficient 87 97 1 2) v4707_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4707_mb : Scalar.QComplex := ((-1588716230511941204666531 : Int)/10^30,(-431474588669453077220080867 : Int)/10^30)
theorem v4707_mb_checked : Scalar.distance (sourceCoefficient 87 97 3 1) v4707_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4707_mg : Scalar.QComplex := ((-93085798084709552093199 : Int)/10^30,(342747689274998370379 : Int)/10^30)
theorem v4707_mg_checked : Scalar.distance (sourceCoefficient 87 97 3 2) v4707_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4707_upper : Scalar.QComplex := ((999989671502870727609034299313 : Int)/10^30,(-4544984882339195695840057704 : Int)/10^30)
theorem v4707_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 87 97 5) 1) 14) v4707_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4707 : Material (87 : Basis) (97 : Basis) where
  plus := ![v4707_pa,v4707_pb,v4707_pg]
  minus := ![(Primitive.Addresses.material4707 1).one,v4707_mb,v4707_mg]
  upper := v4707_upper
  lower := (Primitive.Addresses.material4707 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4707_pa_checked.trans (by decide +kernel)
    · exact v4707_pb_checked.trans (by decide +kernel)
    · exact v4707_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 87 97 Primitive.Addresses.material4707
    · exact v4707_mb_checked.trans (by decide +kernel)
    · exact v4707_mg_checked.trans (by decide +kernel)
  upper_error := v4707_upper_checked
  lower_error := reuse_lower_error 87 97 Primitive.Addresses.material4707

def v4708_pa : Scalar.QComplex := ((999996783072521832566706081160 : Int)/10^30,(-2536502435976056144255777803 : Int)/10^30)
theorem v4708_pa_checked : Scalar.distance (sourceCoefficient 88 89 1 0) v4708_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4708_pb : Scalar.QComplex := ((-1094443783039845377374398 : Int)/10^30,(-431476132950143009152442178 : Int)/10^30)
theorem v4708_pb_checked : Scalar.distance (sourceCoefficient 88 89 1 1) v4708_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4708_pg : Scalar.QComplex := ((-93086130442673757966137 : Int)/10^30,(236113956184900534583 : Int)/10^30)
theorem v4708_pg_checked : Scalar.distance (sourceCoefficient 88 89 1 2) v4708_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4708_mb : Scalar.QComplex := ((-1466787845300737261679533 : Int)/10^30,(-431475027836166433178142197 : Int)/10^30)
theorem v4708_mb_checked : Scalar.distance (sourceCoefficient 88 89 3 1) v4708_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4708_mg : Scalar.QComplex := ((-93085892026743138091605 : Int)/10^30,(316443006397226846215 : Int)/10^30)
theorem v4708_mg_checked : Scalar.distance (sourceCoefficient 88 89 3 2) v4708_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4708_upper : Scalar.QComplex := ((999990915921686528653695858502 : Int)/10^30,(-4262402386737306542428339362 : Int)/10^30)
theorem v4708_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 88 89 5) 1) 14) v4708_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4708 : Material (88 : Basis) (89 : Basis) where
  plus := ![v4708_pa,v4708_pb,v4708_pg]
  minus := ![(Primitive.Addresses.material4708 1).one,v4708_mb,v4708_mg]
  upper := v4708_upper
  lower := (Primitive.Addresses.material4708 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4708_pa_checked.trans (by decide +kernel)
    · exact v4708_pb_checked.trans (by decide +kernel)
    · exact v4708_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 88 89 Primitive.Addresses.material4708
    · exact v4708_mb_checked.trans (by decide +kernel)
    · exact v4708_mg_checked.trans (by decide +kernel)
  upper_error := v4708_upper_checked
  lower_error := reuse_lower_error 88 89 Primitive.Addresses.material4708

def v4709_pa : Scalar.QComplex := ((999996716265400463369255516497 : Int)/10^30,(-2562705292490796978993681100 : Int)/10^30)
theorem v4709_pa_checked : Scalar.distance (sourceCoefficient 88 90 1 0) v4709_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4709_pb : Scalar.QComplex := ((-1105749726329548522259178 : Int)/10^30,(-431476104014361467749257064 : Int)/10^30)
theorem v4709_pb_checked : Scalar.distance (sourceCoefficient 88 90 1 1) v4709_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4709_pg : Scalar.QComplex := ((-93086124211970580900002 : Int)/10^30,(238553086520496759581 : Int)/10^30)
theorem v4709_pg_checked : Scalar.distance (sourceCoefficient 88 90 1 2) v4709_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4709_mb : Scalar.QComplex := ((-1478093759410444761665547 : Int)/10^30,(-431474989143875807658388094 : Int)/10^30)
theorem v4709_mb_checked : Scalar.distance (sourceCoefficient 88 90 3 1) v4709_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4709_mg : Scalar.QComplex := ((-93085883691182655733806 : Int)/10^30,(318882130447807152153 : Int)/10^30)
theorem v4709_mg_checked : Scalar.distance (sourceCoefficient 88 90 3 2) v4709_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4709_upper : Scalar.QComplex := ((999990803890911420947223596085 : Int)/10^30,(-4288605088922939813676225959 : Int)/10^30)
theorem v4709_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 88 90 5) 1) 14) v4709_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4709 : Material (88 : Basis) (90 : Basis) where
  plus := ![v4709_pa,v4709_pb,v4709_pg]
  minus := ![(Primitive.Addresses.material4709 1).one,v4709_mb,v4709_mg]
  upper := v4709_upper
  lower := (Primitive.Addresses.material4709 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4709_pa_checked.trans (by decide +kernel)
    · exact v4709_pb_checked.trans (by decide +kernel)
    · exact v4709_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 88 90 Primitive.Addresses.material4709
    · exact v4709_mb_checked.trans (by decide +kernel)
    · exact v4709_mg_checked.trans (by decide +kernel)
  upper_error := v4709_upper_checked
  lower_error := reuse_lower_error 88 90 Primitive.Addresses.material4709

def v4710_pa : Scalar.QComplex := ((999996678328181470679697214734 : Int)/10^30,(-2577466314727502038880086768 : Int)/10^30)
theorem v4710_pa_checked : Scalar.distance (sourceCoefficient 88 91 1 0) v4710_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4710_pb : Scalar.QComplex := ((-1112118775337967352165826 : Int)/10^30,(-431476087539847755032952098 : Int)/10^30)
theorem v4710_pb_checked : Scalar.distance (sourceCoefficient 88 91 1 1) v4710_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4710_pg : Scalar.QComplex := ((-93086120669154776055055 : Int)/10^30,(239927137352616561312 : Int)/10^30)
theorem v4710_pg_checked : Scalar.distance (sourceCoefficient 88 91 1 2) v4710_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4710_mb : Scalar.QComplex := ((-1484462791830612216298229 : Int)/10^30,(-431474967173165786209928327 : Int)/10^30)
theorem v4710_mb_checked : Scalar.distance (sourceCoefficient 88 91 3 1) v4710_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4710_mg : Scalar.QComplex := ((-93085878962624186873912 : Int)/10^30,(320256177711014554780 : Int)/10^30)
theorem v4710_mg_checked : Scalar.distance (sourceCoefficient 88 91 3 2) v4710_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4710_upper : Scalar.QComplex := ((999990740477563660212767460913 : Int)/10^30,(-4303366023698637859706057551 : Int)/10^30)
theorem v4710_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 88 91 5) 1) 14) v4710_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4710 : Material (88 : Basis) (91 : Basis) where
  plus := ![v4710_pa,v4710_pb,v4710_pg]
  minus := ![(Primitive.Addresses.material4710 1).one,v4710_mb,v4710_mg]
  upper := v4710_upper
  lower := (Primitive.Addresses.material4710 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4710_pa_checked.trans (by decide +kernel)
    · exact v4710_pb_checked.trans (by decide +kernel)
    · exact v4710_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 88 91 Primitive.Addresses.material4710
    · exact v4710_mb_checked.trans (by decide +kernel)
    · exact v4710_mg_checked.trans (by decide +kernel)
  upper_error := v4710_upper_checked
  lower_error := reuse_lower_error 88 91 Primitive.Addresses.material4710

def v4711_pa : Scalar.QComplex := ((999996595451803612513320528818 : Int)/10^30,(-2609422311897127899173725896 : Int)/10^30)
theorem v4711_pa_checked : Scalar.distance (sourceCoefficient 88 92 1 0) v4711_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4711_pb : Scalar.QComplex := ((-1125907068894458917372395 : Int)/10^30,(-431476051444893547261484211 : Int)/10^30)
theorem v4711_pb_checked : Scalar.distance (sourceCoefficient 88 92 1 1) v4711_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4711_pg : Scalar.QComplex := ((-93086112918281185812380 : Int)/10^30,(242901806947647137829 : Int)/10^30)
theorem v4711_pg_checked : Scalar.distance (sourceCoefficient 88 92 1 2) v4711_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4711_mb : Scalar.QComplex := ((-1498251049104772109360650 : Int)/10^30,(-431474919179548680676430200 : Int)/10^30)
theorem v4711_mb_checked : Scalar.distance (sourceCoefficient 88 92 3 1) v4711_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4711_mg : Scalar.QComplex := ((-93085868644747596269525 : Int)/10^30,(323230839509784869958 : Int)/10^30)
theorem v4711_mg_checked : Scalar.distance (sourceCoefficient 88 92 3 2) v4711_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4711_upper : Scalar.QComplex := ((999990602448157147318917104393 : Int)/10^30,(-4335321830236450054033587047 : Int)/10^30)
theorem v4711_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 88 92 5) 1) 14) v4711_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4711 : Material (88 : Basis) (92 : Basis) where
  plus := ![v4711_pa,v4711_pb,v4711_pg]
  minus := ![(Primitive.Addresses.material4711 1).one,v4711_mb,v4711_mg]
  upper := v4711_upper
  lower := (Primitive.Addresses.material4711 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4711_pa_checked.trans (by decide +kernel)
    · exact v4711_pb_checked.trans (by decide +kernel)
    · exact v4711_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 88 92 Primitive.Addresses.material4711
    · exact v4711_mb_checked.trans (by decide +kernel)
    · exact v4711_mg_checked.trans (by decide +kernel)
  upper_error := v4711_upper_checked
  lower_error := reuse_lower_error 88 92 Primitive.Addresses.material4711

def v4712_pa : Scalar.QComplex := ((999996495768692711071688415998 : Int)/10^30,(-2647347792591823708319588760 : Int)/10^30)
theorem v4712_pa_checked : Scalar.distance (sourceCoefficient 88 93 1 0) v4712_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4712_pb : Scalar.QComplex := ((-1142271059706587108366135 : Int)/10^30,(-431476007844918830154672576 : Int)/10^30)
theorem v4712_pb_checked : Scalar.distance (sourceCoefficient 88 93 1 1) v4712_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4712_pg : Scalar.QComplex := ((-93086103575606258403937 : Int)/10^30,(246432154377125587240 : Int)/10^30)
theorem v4712_pg_checked : Scalar.distance (sourceCoefficient 88 93 1 2) v4712_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4712_mb : Scalar.QComplex := ((-1514614996199024138776582 : Int)/10^30,(-431474861458203133753394491 : Int)/10^30)
theorem v4712_mb_checked : Scalar.distance (sourceCoefficient 88 93 3 1) v4712_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4712_mg : Scalar.QComplex := ((-93085856255545316871868 : Int)/10^30,(326761177562445942632 : Int)/10^30)
theorem v4712_mg_checked : Scalar.distance (sourceCoefficient 88 93 3 2) v4712_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4712_upper : Scalar.QComplex := ((999990437309255605848748887755 : Int)/10^30,(-4373247082401591173633193311 : Int)/10^30)
theorem v4712_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 88 93 5) 1) 14) v4712_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4712 : Material (88 : Basis) (93 : Basis) where
  plus := ![v4712_pa,v4712_pb,v4712_pg]
  minus := ![(Primitive.Addresses.material4712 1).one,v4712_mb,v4712_mg]
  upper := v4712_upper
  lower := (Primitive.Addresses.material4712 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4712_pa_checked.trans (by decide +kernel)
    · exact v4712_pb_checked.trans (by decide +kernel)
    · exact v4712_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 88 93 Primitive.Addresses.material4712
    · exact v4712_mb_checked.trans (by decide +kernel)
    · exact v4712_mg_checked.trans (by decide +kernel)
  upper_error := v4712_upper_checked
  lower_error := reuse_lower_error 88 93 Primitive.Addresses.material4712

def v4713_pa : Scalar.QComplex := ((999996376167878589824539647198 : Int)/10^30,(-2692146190432664218792989599 : Int)/10^30)
theorem v4713_pa_checked : Scalar.distance (sourceCoefficient 88 94 1 0) v4713_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4713_pb : Scalar.QComplex := ((-1161600558709488434142142 : Int)/10^30,(-431475955277669125231802851 : Int)/10^30)
theorem v4713_pb_checked : Scalar.distance (sourceCoefficient 88 94 1 1) v4713_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4713_pg : Scalar.QComplex := ((-93086092338602948587723 : Int)/10^30,(250602277012214274778 : Int)/10^30)
theorem v4713_pg_checked : Scalar.distance (sourceCoefficient 88 94 1 2) v4713_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4713_mb : Scalar.QComplex := ((-1533944442641500629718079 : Int)/10^30,(-431474792210485930834263393 : Int)/10^30)
theorem v4713_mb_checked : Scalar.distance (sourceCoefficient 88 94 3 1) v4713_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4713_mg : Scalar.QComplex := ((-93085841419918172375456 : Int)/10^30,(330931288947779628578 : Int)/10^30)
theorem v4713_mg_checked : Scalar.distance (sourceCoefficient 88 94 3 2) v4713_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4713_upper : Scalar.QComplex := ((999990240390649021579492962115 : Int)/10^30,(-4418045207100325417475899717 : Int)/10^30)
theorem v4713_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 88 94 5) 1) 14) v4713_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4713 : Material (88 : Basis) (94 : Basis) where
  plus := ![v4713_pa,v4713_pb,v4713_pg]
  minus := ![(Primitive.Addresses.material4713 1).one,v4713_mb,v4713_mg]
  upper := v4713_upper
  lower := (Primitive.Addresses.material4713 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4713_pa_checked.trans (by decide +kernel)
    · exact v4713_pb_checked.trans (by decide +kernel)
    · exact v4713_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 88 94 Primitive.Addresses.material4713
    · exact v4713_mb_checked.trans (by decide +kernel)
    · exact v4713_mg_checked.trans (by decide +kernel)
  upper_error := v4713_upper_checked
  lower_error := reuse_lower_error 88 94 Primitive.Addresses.material4713

def v4714_pa : Scalar.QComplex := ((999996255995096141399650303488 : Int)/10^30,(-2736420251011251484694857757 : Int)/10^30)
theorem v4714_pa_checked : Scalar.distance (sourceCoefficient 88 95 1 0) v4714_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4714_pb : Scalar.QComplex := ((-1180703817140485831355251 : Int)/10^30,(-431475902191293097654554487 : Int)/10^30)
theorem v4714_pb_checked : Scalar.distance (sourceCoefficient 88 95 1 1) v4714_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4714_pg : Scalar.QComplex := ((-93086081018980556856686 : Int)/10^30,(254723590873985828449 : Int)/10^30)
theorem v4714_pg_checked : Scalar.distance (sourceCoefficient 88 95 1 2) v4714_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4714_mb : Scalar.QComplex := ((-1553047648148330260852356 : Int)/10^30,(-431474722638878022611192534 : Int)/10^30)
theorem v4714_mb_checked : Scalar.distance (sourceCoefficient 88 95 3 1) v4714_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4714_mg : Scalar.QComplex := ((-93085826543791749834221 : Int)/10^30,(335052591506673370966 : Int)/10^30)
theorem v4714_mg_checked : Scalar.distance (sourceCoefficient 88 95 3 2) v4714_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4714_upper : Scalar.QComplex := ((999990043805033509156377145887 : Int)/10^30,(-4462318994330579731744316133 : Int)/10^30)
theorem v4714_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 88 95 5) 1) 14) v4714_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4714 : Material (88 : Basis) (95 : Basis) where
  plus := ![v4714_pa,v4714_pb,v4714_pg]
  minus := ![(Primitive.Addresses.material4714 1).one,v4714_mb,v4714_mg]
  upper := v4714_upper
  lower := (Primitive.Addresses.material4714 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4714_pa_checked.trans (by decide +kernel)
    · exact v4714_pb_checked.trans (by decide +kernel)
    · exact v4714_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 88 95 Primitive.Addresses.material4714
    · exact v4714_mb_checked.trans (by decide +kernel)
    · exact v4714_mg_checked.trans (by decide +kernel)
  upper_error := v4714_upper_checked
  lower_error := reuse_lower_error 88 95 Primitive.Addresses.material4714

def v4715_pa : Scalar.QComplex := ((999996197581511399528331057344 : Int)/10^30,(-2757684267427034672930463291 : Int)/10^30)
theorem v4715_pa_checked : Scalar.distance (sourceCoefficient 88 96 1 0) v4715_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4715_pb : Scalar.QComplex := ((-1189878760247276229110308 : Int)/10^30,(-431475876294007921737416734 : Int)/10^30)
theorem v4715_pb_checked : Scalar.distance (sourceCoefficient 88 96 1 1) v4715_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4715_pg : Scalar.QComplex := ((-93086075506700294764222 : Int)/10^30,(256702982033517400885 : Int)/10^30)
theorem v4715_pg_checked : Scalar.distance (sourceCoefficient 88 96 1 2) v4715_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4715_mb : Scalar.QComplex := ((-1562222565490679287944884 : Int)/10^30,(-431474688824039812374707195 : Int)/10^30)
theorem v4715_mb_checked : Scalar.distance (sourceCoefficient 88 96 3 1) v4715_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4715_mg : Scalar.QComplex := ((-93085819323388118008354 : Int)/10^30,(337031977172337549765 : Int)/10^30)
theorem v4715_mg_checked : Scalar.distance (sourceCoefficient 88 96 3 2) v4715_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4715_upper : Scalar.QComplex := ((999989948691772490316283778659 : Int)/10^30,(-4483582878259560290045732675 : Int)/10^30)
theorem v4715_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 88 96 5) 1) 14) v4715_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4715 : Material (88 : Basis) (96 : Basis) where
  plus := ![v4715_pa,v4715_pb,v4715_pg]
  minus := ![(Primitive.Addresses.material4715 1).one,v4715_mb,v4715_mg]
  upper := v4715_upper
  lower := (Primitive.Addresses.material4715 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4715_pa_checked.trans (by decide +kernel)
    · exact v4715_pb_checked.trans (by decide +kernel)
    · exact v4715_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 88 96 Primitive.Addresses.material4715
    · exact v4715_mb_checked.trans (by decide +kernel)
    · exact v4715_mg_checked.trans (by decide +kernel)
  upper_error := v4715_upper_checked
  lower_error := reuse_lower_error 88 96 Primitive.Addresses.material4715

def v4716_pa : Scalar.QComplex := ((999995993146854126462593581442 : Int)/10^30,(-2830846205090439422364469685 : Int)/10^30)
theorem v4716_pa_checked : Scalar.distance (sourceCoefficient 88 97 1 0) v4716_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4716_pb : Scalar.QComplex := ((-1221446483288170447453394 : Int)/10^30,(-431475785203408444190082673 : Int)/10^30)
theorem v4716_pb_checked : Scalar.distance (sourceCoefficient 88 97 1 1) v4716_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4716_pg : Scalar.QComplex := ((-93086056165767130898789 : Int)/10^30,(263513364703051722712 : Int)/10^30)
theorem v4716_pg_checked : Scalar.distance (sourceCoefficient 88 97 1 2) v4716_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4716_mb : Scalar.QComplex := ((-1593790198170382721131081 : Int)/10^30,(-431474570491951025196538069 : Int)/10^30)
theorem v4716_mb_checked : Scalar.distance (sourceCoefficient 88 97 3 1) v4716_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4716_mg : Scalar.QComplex := ((-93085794105408640097291 : Int)/10^30,(343842340615700916738 : Int)/10^30)
theorem v4716_mg_checked : Scalar.distance (sourceCoefficient 88 97 3 2) v4716_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4716_upper : Scalar.QComplex := ((999989617986552490759244926698 : Int)/10^30,(-4556744354121180808667917558 : Int)/10^30)
theorem v4716_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 88 97 5) 1) 14) v4716_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4716 : Material (88 : Basis) (97 : Basis) where
  plus := ![v4716_pa,v4716_pb,v4716_pg]
  minus := ![(Primitive.Addresses.material4716 1).one,v4716_mb,v4716_mg]
  upper := v4716_upper
  lower := (Primitive.Addresses.material4716 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4716_pa_checked.trans (by decide +kernel)
    · exact v4716_pb_checked.trans (by decide +kernel)
    · exact v4716_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 88 97 Primitive.Addresses.material4716
    · exact v4716_mb_checked.trans (by decide +kernel)
    · exact v4716_mg_checked.trans (by decide +kernel)
  upper_error := v4716_upper_checked
  lower_error := reuse_lower_error 88 97 Primitive.Addresses.material4716

def v4717_pa : Scalar.QComplex := ((999996674903357982208851115777 : Int)/10^30,(-2578794723852192066869579964 : Int)/10^30)
theorem v4717_pa_checked : Scalar.distance (sourceCoefficient 89 90 1 0) v4717_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4717_pb : Scalar.QComplex := ((-1112691954489978550337163 : Int)/10^30,(-431476086246821662102927243 : Int)/10^30)
theorem v4717_pb_checked : Scalar.distance (sourceCoefficient 89 90 1 1) v4717_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4717_pg : Scalar.QComplex := ((-93086120370274550302963 : Int)/10^30,(240050794266824000018 : Int)/10^30)
theorem v4717_pg_checked : Scalar.distance (sourceCoefficient 89 90 1 2) v4717_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4717_mb : Scalar.QComplex := ((-1485035969653379338129263 : Int)/10^30,(-431474965385512381577655659 : Int)/10^30)
theorem v4717_mb_checked : Scalar.distance (sourceCoefficient 89 90 3 1) v4717_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4717_mg : Scalar.QComplex := ((-93085878557033724748241 : Int)/10^30,(320379834321258699168 : Int)/10^30)
theorem v4717_mg_checked : Scalar.distance (sourceCoefficient 89 90 3 2) v4717_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4717_upper : Scalar.QComplex := ((999990734760031635733612286866 : Int)/10^30,(-4304694424933883898826324141 : Int)/10^30)
theorem v4717_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 89 90 5) 1) 14) v4717_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4717 : Material (89 : Basis) (90 : Basis) where
  plus := ![v4717_pa,v4717_pb,v4717_pg]
  minus := ![(Primitive.Addresses.material4717 1).one,v4717_mb,v4717_mg]
  upper := v4717_upper
  lower := (Primitive.Addresses.material4717 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4717_pa_checked.trans (by decide +kernel)
    · exact v4717_pb_checked.trans (by decide +kernel)
    · exact v4717_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 89 90 Primitive.Addresses.material4717
    · exact v4717_mb_checked.trans (by decide +kernel)
    · exact v4717_mg_checked.trans (by decide +kernel)
  upper_error := v4717_upper_checked
  lower_error := reuse_lower_error 89 90 Primitive.Addresses.material4717

def v4718_pa : Scalar.QComplex := ((999996636728641755554017018990 : Int)/10^30,(-2593555745476596224712024810 : Int)/10^30)
theorem v4718_pa_checked : Scalar.distance (sourceCoefficient 89 91 1 0) v4718_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4718_pb : Scalar.QComplex := ((-1119061003322267997821120 : Int)/10^30,(-431476069703991471318788668 : Int)/10^30)
theorem v4718_pb_checked : Scalar.distance (sourceCoefficient 89 91 1 1) v4718_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4718_pg : Scalar.QComplex := ((-93086116809035604121214 : Int)/10^30,(241424845051446380955 : Int)/10^30)
theorem v4718_pg_checked : Scalar.distance (sourceCoefficient 89 91 1 2) v4718_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4718_mb : Scalar.QComplex := ((-1491405001838463432207686 : Int)/10^30,(-431474943346486059490433743 : Int)/10^30)
theorem v4718_mb_checked : Scalar.distance (sourceCoefficient 89 91 3 1) v4718_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4718_mg : Scalar.QComplex := ((-93085873810052162399456 : Int)/10^30,(321753881521070357460 : Int)/10^30)
theorem v4718_mg_checked : Scalar.distance (sourceCoefficient 89 91 3 2) v4718_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4718_upper : Scalar.QComplex := ((999990671109188051533921387048 : Int)/10^30,(-4319455358687383274519157056 : Int)/10^30)
theorem v4718_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 89 91 5) 1) 14) v4718_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4718 : Material (89 : Basis) (91 : Basis) where
  plus := ![v4718_pa,v4718_pb,v4718_pg]
  minus := ![(Primitive.Addresses.material4718 1).one,v4718_mb,v4718_mg]
  upper := v4718_upper
  lower := (Primitive.Addresses.material4718 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4718_pa_checked.trans (by decide +kernel)
    · exact v4718_pb_checked.trans (by decide +kernel)
    · exact v4718_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 89 91 Primitive.Addresses.material4718
    · exact v4718_mb_checked.trans (by decide +kernel)
    · exact v4718_mg_checked.trans (by decide +kernel)
  upper_error := v4718_upper_checked
  lower_error := reuse_lower_error 89 91 Primitive.Addresses.material4718

def v4719_pa : Scalar.QComplex := ((999996553338108386118912542312 : Int)/10^30,(-2625511741308647637169932397 : Int)/10^30)
theorem v4719_pa_checked : Scalar.distance (sourceCoefficient 89 92 1 0) v4719_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4719_pb : Scalar.QComplex := ((-1132849296494004027644790 : Int)/10^30,(-431476033461139567588475249 : Int)/10^30)
theorem v4719_pb_checked : Scalar.distance (sourceCoefficient 89 92 1 1) v4719_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4719_pg : Scalar.QComplex := ((-93086109018277929783768 : Int)/10^30,(244399514542718599171 : Int)/10^30)
theorem v4719_pg_checked : Scalar.distance (sourceCoefficient 89 92 1 2) v4719_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4719_mb : Scalar.QComplex := ((-1505193258600238882601751 : Int)/10^30,(-431474895204971645093859837 : Int)/10^30)
theorem v4719_mb_checked : Scalar.distance (sourceCoefficient 89 92 3 1) v4719_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4719_mg : Scalar.QComplex := ((-93085863452291592089756 : Int)/10^30,(324728543181664184711 : Int)/10^30)
theorem v4719_mg_checked : Scalar.distance (sourceCoefficient 89 92 3 2) v4719_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4719_upper : Scalar.QComplex := ((999990532565629101677733483979 : Int)/10^30,(-4351411163000237244544769108 : Int)/10^30)
theorem v4719_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 89 92 5) 1) 14) v4719_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4719 : Material (89 : Basis) (92 : Basis) where
  plus := ![v4719_pa,v4719_pb,v4719_pg]
  minus := ![(Primitive.Addresses.material4719 1).one,v4719_mb,v4719_mg]
  upper := v4719_upper
  lower := (Primitive.Addresses.material4719 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4719_pa_checked.trans (by decide +kernel)
    · exact v4719_pb_checked.trans (by decide +kernel)
    · exact v4719_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 89 92 Primitive.Addresses.material4719
    · exact v4719_mb_checked.trans (by decide +kernel)
    · exact v4719_mg_checked.trans (by decide +kernel)
  upper_error := v4719_upper_checked
  lower_error := reuse_lower_error 89 92 Primitive.Addresses.material4719

def v4720_pa : Scalar.QComplex := ((999996453044796062774954372985 : Int)/10^30,(-2663437220394584662621899216 : Int)/10^30)
theorem v4720_pa_checked : Scalar.distance (sourceCoefficient 89 93 1 0) v4720_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4720_pb : Scalar.QComplex := ((-1149213286843370054061794 : Int)/10^30,(-431475989685639387193027738 : Int)/10^30)
theorem v4720_pb_checked : Scalar.distance (sourceCoefficient 89 93 1 1) v4720_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4720_pg : Scalar.QComplex := ((-93086099628268442531006 : Int)/10^30,(247929861847402372286 : Int)/10^30)
theorem v4720_pg_checked : Scalar.distance (sourceCoefficient 89 93 1 2) v4720_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4720_mb : Scalar.QComplex := ((-1521557205080258350303762 : Int)/10^30,(-431474837308101099581246141 : Int)/10^30)
theorem v4720_mb_checked : Scalar.distance (sourceCoefficient 89 93 3 1) v4720_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4720_mg : Scalar.QComplex := ((-93085851015754878164785 : Int)/10^30,(328258881068683034279 : Int)/10^30)
theorem v4720_mg_checked : Scalar.distance (sourceCoefficient 89 93 3 2) v4720_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4720_upper : Scalar.QComplex := ((999990366816529823700293039009 : Int)/10^30,(-4389336412503469679344864293 : Int)/10^30)
theorem v4720_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 89 93 5) 1) 14) v4720_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4720 : Material (89 : Basis) (93 : Basis) where
  plus := ![v4720_pa,v4720_pb,v4720_pg]
  minus := ![(Primitive.Addresses.material4720 1).one,v4720_mb,v4720_mg]
  upper := v4720_upper
  lower := (Primitive.Addresses.material4720 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4720_pa_checked.trans (by decide +kernel)
    · exact v4720_pb_checked.trans (by decide +kernel)
    · exact v4720_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 89 93 Primitive.Addresses.material4720
    · exact v4720_mb_checked.trans (by decide +kernel)
    · exact v4720_mg_checked.trans (by decide +kernel)
  upper_error := v4720_upper_checked
  lower_error := reuse_lower_error 89 93 Primitive.Addresses.material4720

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
