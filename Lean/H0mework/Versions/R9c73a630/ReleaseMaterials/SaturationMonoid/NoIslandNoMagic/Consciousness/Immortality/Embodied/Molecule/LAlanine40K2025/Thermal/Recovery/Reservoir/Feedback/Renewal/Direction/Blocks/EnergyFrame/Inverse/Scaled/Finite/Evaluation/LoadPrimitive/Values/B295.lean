import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B196
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B197

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4721_pa : Scalar.QComplex := ((999996332723198828127371252842 : Int)/10^30,(-2708235616305311210411039048 : Int)/10^30)
theorem v4721_pa_checked : Scalar.distance (sourceCoefficient 89 94 1 0) v4721_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4721_pb : Scalar.QComplex := ((-1168542785291070859157747 : Int)/10^30,(-431475936911055210008537618 : Int)/10^30)
theorem v4721_pb_checked : Scalar.distance (sourceCoefficient 89 94 1 1) v4721_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4721_pg : Scalar.QComplex := ((-93086088335352527186700 : Int)/10^30,(252099984332768211698 : Int)/10^30)
theorem v4721_pg_checked : Scalar.distance (sourceCoefficient 89 94 1 2) v4721_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4721_mb : Scalar.QComplex := ((-1540886650788614215727943 : Int)/10^30,(-431474767853049980713638367 : Int)/10^30)
theorem v4721_mb_checked : Scalar.distance (sourceCoefficient 89 94 3 1) v4721_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4721_mg : Scalar.QComplex := ((-93085836124215278163174 : Int)/10^30,(332428992256043867486 : Int)/10^30)
theorem v4721_mg_checked : Scalar.distance (sourceCoefficient 89 94 3 2) v4721_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4721_upper : Scalar.QComplex := ((999990169177144530753982061924 : Int)/10^30,(-4434134534028086570385437678 : Int)/10^30)
theorem v4721_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 89 94 5) 1) 14) v4721_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4721 : Material (89 : Basis) (94 : Basis) where
  plus := ![v4721_pa,v4721_pb,v4721_pg]
  minus := ![(Primitive.Addresses.material4721 1).one,v4721_mb,v4721_mg]
  upper := v4721_upper
  lower := (Primitive.Addresses.material4721 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4721_pa_checked.trans (by decide +kernel)
    · exact v4721_pb_checked.trans (by decide +kernel)
    · exact v4721_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 89 94 Primitive.Addresses.material4721
    · exact v4721_mb_checked.trans (by decide +kernel)
    · exact v4721_mg_checked.trans (by decide +kernel)
  upper_error := v4721_upper_checked
  lower_error := reuse_lower_error 89 94 Primitive.Addresses.material4721

def v4722_pa : Scalar.QComplex := ((999996211838069582643875383186 : Int)/10^30,(-2752509674944649706068789605 : Int)/10^30)
theorem v4722_pa_checked : Scalar.distance (sourceCoefficient 89 95 1 0) v4722_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4722_pb : Scalar.QComplex := ((-1187646043164240093777927 : Int)/10^30,(-431475883619771431022526447 : Int)/10^30)
theorem v4722_pb_checked : Scalar.distance (sourceCoefficient 89 95 1 1) v4722_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4722_pg : Scalar.QComplex := ((-93086076960471952116113 : Int)/10^30,(256221298044108311855 : Int)/10^30)
theorem v4722_pg_checked : Scalar.distance (sourceCoefficient 89 95 1 2) v4722_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4722_mb : Scalar.QComplex := ((-1559989855560789731210984 : Int)/10^30,(-431474698076534878758905968 : Int)/10^30)
theorem v4722_mb_checked : Scalar.distance (sourceCoefficient 89 95 3 1) v4722_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4722_mg : Scalar.QComplex := ((-93085821192830822673105 : Int)/10^30,(336550294616820888888 : Int)/10^30)
theorem v4722_mg_checked : Scalar.distance (sourceCoefficient 89 95 3 2) v4722_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4722_upper : Scalar.QComplex := ((999989971879186629196585972873 : Int)/10^30,(-4478408318089649054566442069 : Int)/10^30)
theorem v4722_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 89 95 5) 1) 14) v4722_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4722 : Material (89 : Basis) (95 : Basis) where
  plus := ![v4722_pa,v4722_pb,v4722_pg]
  minus := ![(Primitive.Addresses.material4722 1).one,v4722_mb,v4722_mg]
  upper := v4722_upper
  lower := (Primitive.Addresses.material4722 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4722_pa_checked.trans (by decide +kernel)
    · exact v4722_pb_checked.trans (by decide +kernel)
    · exact v4722_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 89 95 Primitive.Addresses.material4722
    · exact v4722_mb_checked.trans (by decide +kernel)
    · exact v4722_mg_checked.trans (by decide +kernel)
  upper_error := v4722_upper_checked
  lower_error := reuse_lower_error 89 95 Primitive.Addresses.material4722

def v4723_pa : Scalar.QComplex := ((999996153082357785236170725197 : Int)/10^30,(-2773773690417836102406993467 : Int)/10^30)
theorem v4723_pa_checked : Scalar.distance (sourceCoefficient 89 96 1 0) v4723_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4723_pb : Scalar.QComplex := ((-1196820985999890943132192 : Int)/10^30,(-431475857624072833660231755 : Int)/10^30)
theorem v4723_pb_checked : Scalar.distance (sourceCoefficient 89 96 1 1) v4723_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4723_pg : Scalar.QComplex := ((-93086071421652201640430 : Int)/10^30,(258200689130520742722 : Int)/10^30)
theorem v4723_pg_checked : Scalar.distance (sourceCoefficient 89 96 1 2) v4723_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4723_mb : Scalar.QComplex := ((-1569164772547072960529160 : Int)/10^30,(-431474664163283517702296806 : Int)/10^30)
theorem v4723_mb_checked : Scalar.distance (sourceCoefficient 89 96 3 1) v4723_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4723_mg : Scalar.QComplex := ((-93085813945887775444410 : Int)/10^30,(338529680186463570162 : Int)/10^30)
theorem v4723_mg_checked : Scalar.distance (sourceCoefficient 89 96 3 2) v4723_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4723_upper : Scalar.QComplex := ((999989876423800691214718450110 : Int)/10^30,(-4499672200485553964525878481 : Int)/10^30)
theorem v4723_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 89 96 5) 1) 14) v4723_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4723 : Material (89 : Basis) (96 : Basis) where
  plus := ![v4723_pa,v4723_pb,v4723_pg]
  minus := ![(Primitive.Addresses.material4723 1).one,v4723_mb,v4723_mg]
  upper := v4723_upper
  lower := (Primitive.Addresses.material4723 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4723_pa_checked.trans (by decide +kernel)
    · exact v4723_pb_checked.trans (by decide +kernel)
    · exact v4723_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 89 96 Primitive.Addresses.material4723
    · exact v4723_mb_checked.trans (by decide +kernel)
    · exact v4723_mg_checked.trans (by decide +kernel)
  upper_error := v4723_upper_checked
  lower_error := reuse_lower_error 89 96 Primitive.Addresses.material4723

def v4724_pa : Scalar.QComplex := ((999995947470562674653006943747 : Int)/10^30,(-2846935624782522826200488287 : Int)/10^30)
theorem v4724_pa_checked : Scalar.distance (sourceCoefficient 89 97 1 0) v4724_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4724_pb : Scalar.QComplex := ((-1228388708091903389997711 : Int)/10^30,(-431475766194867683283702032 : Int)/10^30)
theorem v4724_pb_checked : Scalar.distance (sourceCoefficient 89 97 1 1) v4724_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4724_pg : Scalar.QComplex := ((-93086051989406072562039 : Int)/10^30,(265011071544166828931 : Int)/10^30)
theorem v4724_pg_checked : Scalar.distance (sourceCoefficient 89 97 1 2) v4724_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4724_mb : Scalar.QComplex := ((-1600732403985693530131634 : Int)/10^30,(-431474545492590002615531794 : Int)/10^30)
theorem v4724_mb_checked : Scalar.distance (sourceCoefficient 89 97 3 1) v4724_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4724_mg : Scalar.QComplex := ((-93085788636595587140400 : Int)/10^30,(345340043295139820401 : Int)/10^30)
theorem v4724_mg_checked : Scalar.distance (sourceCoefficient 89 97 3 2) v4724_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4724_upper : Scalar.QComplex := ((999989544541450300636840844938 : Int)/10^30,(-4572833671016828252115907367 : Int)/10^30)
theorem v4724_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 89 97 5) 1) 14) v4724_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4724 : Material (89 : Basis) (97 : Basis) where
  plus := ![v4724_pa,v4724_pb,v4724_pg]
  minus := ![(Primitive.Addresses.material4724 1).one,v4724_mb,v4724_mg]
  upper := v4724_upper
  lower := (Primitive.Addresses.material4724 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4724_pa_checked.trans (by decide +kernel)
    · exact v4724_pb_checked.trans (by decide +kernel)
    · exact v4724_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 89 97 Primitive.Addresses.material4724
    · exact v4724_mb_checked.trans (by decide +kernel)
    · exact v4724_mg_checked.trans (by decide +kernel)
  upper_error := v4724_upper_checked
  lower_error := reuse_lower_error 89 97 Primitive.Addresses.material4724

def v4725_pa : Scalar.QComplex := ((999996568426555895189197547359 : Int)/10^30,(-2619758598137110670441516204 : Int)/10^30)
theorem v4725_pa_checked : Scalar.distance (sourceCoefficient 90 91 1 0) v4725_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4725_pb : Scalar.QComplex := ((-1130366945503296451152760 : Int)/10^30,(-431476040338180884176473598 : Int)/10^30)
theorem v4725_pb_checked : Scalar.distance (sourceCoefficient 90 91 1 1) v4725_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4725_pg : Scalar.QComplex := ((-93086110462365004374734 : Int)/10^30,(243863975088062460672 : Int)/10^30)
theorem v4725_pg_checked : Scalar.distance (sourceCoefficient 90 91 1 2) v4725_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4725_mb : Scalar.QComplex := ((-1502710914468400954767202 : Int)/10^30,(-431474904224167505087342666 : Int)/10^30)
theorem v4725_mb_checked : Scalar.distance (sourceCoefficient 90 91 3 1) v4725_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4725_mg : Scalar.QComplex := ((-93085865358524558547684 : Int)/10^30,(324193005172595966647 : Int)/10^30)
theorem v4725_mg_checked : Scalar.distance (sourceCoefficient 90 91 3 2) v4725_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4725_upper : Scalar.QComplex := ((999990557583457331279173688182 : Int)/10^30,(-4345658054438622807540427058 : Int)/10^30)
theorem v4725_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 90 91 5) 1) 14) v4725_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4725 : Material (90 : Basis) (91 : Basis) where
  plus := ![v4725_pa,v4725_pb,v4725_pg]
  minus := ![(Primitive.Addresses.material4725 1).one,v4725_mb,v4725_mg]
  upper := v4725_upper
  lower := (Primitive.Addresses.material4725 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4725_pa_checked.trans (by decide +kernel)
    · exact v4725_pb_checked.trans (by decide +kernel)
    · exact v4725_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 90 91 Primitive.Addresses.material4725
    · exact v4725_mb_checked.trans (by decide +kernel)
    · exact v4725_mg_checked.trans (by decide +kernel)
  upper_error := v4725_upper_checked
  lower_error := reuse_lower_error 90 91 Primitive.Addresses.material4725

def v4726_pa : Scalar.QComplex := ((999996484198681459316896569874 : Int)/10^30,(-2651714591773114400541586458 : Int)/10^30)
theorem v4726_pa_checked : Scalar.distance (sourceCoefficient 90 92 1 0) v4726_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4726_pb : Scalar.QComplex := ((-1144155238043335678371727 : Int)/10^30,(-431476003854466416938374653 : Int)/10^30)
theorem v4726_pb_checked : Scalar.distance (sourceCoefficient 90 92 1 1) v4726_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4726_pg : Scalar.QComplex := ((-93086102606653088018338 : Int)/10^30,(246838644408982813486 : Int)/10^30)
theorem v4726_pg_checked : Scalar.distance (sourceCoefficient 90 92 1 2) v4726_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4726_mb : Scalar.QComplex := ((-1516499170390626293506095 : Int)/10^30,(-431474855841791161993013671 : Int)/10^30)
theorem v4726_mb_checked : Scalar.distance (sourceCoefficient 90 92 3 1) v4726_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4726_mg : Scalar.QComplex := ((-93085854935809917410455 : Int)/10^30,(327167666606785406493 : Int)/10^30)
theorem v4726_mg_checked : Scalar.distance (sourceCoefficient 90 92 3 2) v4726_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4726_upper : Scalar.QComplex := ((999990418202562352286022611498 : Int)/10^30,(-4377613855110257648280814490 : Int)/10^30)
theorem v4726_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 90 92 5) 1) 14) v4726_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4726 : Material (90 : Basis) (92 : Basis) where
  plus := ![v4726_pa,v4726_pb,v4726_pg]
  minus := ![(Primitive.Addresses.material4726 1).one,v4726_mb,v4726_mg]
  upper := v4726_upper
  lower := (Primitive.Addresses.material4726 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4726_pa_checked.trans (by decide +kernel)
    · exact v4726_pb_checked.trans (by decide +kernel)
    · exact v4726_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 90 92 Primitive.Addresses.material4726
    · exact v4726_mb_checked.trans (by decide +kernel)
    · exact v4726_mg_checked.trans (by decide +kernel)
  upper_error := v4726_upper_checked
  lower_error := reuse_lower_error 90 92 Primitive.Addresses.material4726

def v4727_pa : Scalar.QComplex := ((999996382911610053786201896684 : Int)/10^30,(-2689640068218051906353790720 : Int)/10^30)
theorem v4727_pa_checked : Scalar.distance (sourceCoefficient 90 93 1 0) v4727_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4727_pb : Scalar.QComplex := ((-1160519227633013759523023 : Int)/10^30,(-431475959793109768330152359 : Int)/10^30)
theorem v4727_pb_checked : Scalar.distance (sourceCoefficient 90 93 1 1) v4727_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4727_pg : Scalar.QComplex := ((-93086093139555696560891 : Int)/10^30,(250368991508798906271 : Int)/10^30)
theorem v4727_pg_checked : Scalar.distance (sourceCoefficient 90 93 1 2) v4727_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4727_mb : Scalar.QComplex := ((-1532863115864276841238720 : Int)/10^30,(-431474797659064910281534282 : Int)/10^30)
theorem v4727_mb_checked : Scalar.distance (sourceCoefficient 90 93 3 1) v4727_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4727_mg : Scalar.QComplex := ((-93085842422185504775731 : Int)/10^30,(330698004222413262594 : Int)/10^30)
theorem v4727_mg_checked : Scalar.distance (sourceCoefficient 90 93 3 2) v4727_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4727_upper : Scalar.QComplex := ((999990251459710030334844731198 : Int)/10^30,(-4415539100257356474165089275 : Int)/10^30)
theorem v4727_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 90 93 5) 1) 14) v4727_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4727 : Material (90 : Basis) (93 : Basis) where
  plus := ![v4727_pa,v4727_pb,v4727_pg]
  minus := ![(Primitive.Addresses.material4727 1).one,v4727_mb,v4727_mg]
  upper := v4727_upper
  lower := (Primitive.Addresses.material4727 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4727_pa_checked.trans (by decide +kernel)
    · exact v4727_pb_checked.trans (by decide +kernel)
    · exact v4727_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 90 93 Primitive.Addresses.material4727
    · exact v4727_mb_checked.trans (by decide +kernel)
    · exact v4727_mg_checked.trans (by decide +kernel)
  upper_error := v4727_upper_checked
  lower_error := reuse_lower_error 90 93 Primitive.Addresses.material4727

def v4728_pa : Scalar.QComplex := ((999996261416163105106545252572 : Int)/10^30,(-2734438460960619500800314264 : Int)/10^30)
theorem v4728_pa_checked : Scalar.distance (sourceCoefficient 90 94 1 0) v4728_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4728_pb : Scalar.QComplex := ((-1179848725169388324061720 : Int)/10^30,(-431475906680865750644149308 : Int)/10^30)
theorem v4728_pb_checked : Scalar.distance (sourceCoefficient 90 94 1 1) v4728_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4728_pg : Scalar.QComplex := ((-93086081755581882090822 : Int)/10^30,(254539113748404240791 : Int)/10^30)
theorem v4728_pg_checked : Scalar.distance (sourceCoefficient 90 94 1 2) v4728_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4728_mb : Scalar.QComplex := ((-1552192560369921570715931 : Int)/10^30,(-431474727866354863072105005 : Int)/10^30)
theorem v4728_mb_checked : Scalar.distance (sourceCoefficient 90 94 3 1) v4728_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4728_mg : Scalar.QComplex := ((-93085827439588251633621 : Int)/10^30,(334868115085434816568 : Int)/10^30)
theorem v4728_mg_checked : Scalar.distance (sourceCoefficient 90 94 3 2) v4728_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4728_upper : Scalar.QComplex := ((999990052646482239622659541515 : Int)/10^30,(-4460337216587861014858486782 : Int)/10^30)
theorem v4728_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 90 94 5) 1) 14) v4728_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4728 : Material (90 : Basis) (94 : Basis) where
  plus := ![v4728_pa,v4728_pb,v4728_pg]
  minus := ![(Primitive.Addresses.material4728 1).one,v4728_mb,v4728_mg]
  upper := v4728_upper
  lower := (Primitive.Addresses.material4728 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4728_pa_checked.trans (by decide +kernel)
    · exact v4728_pb_checked.trans (by decide +kernel)
    · exact v4728_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 90 94 Primitive.Addresses.material4728
    · exact v4728_mb_checked.trans (by decide +kernel)
    · exact v4728_mg_checked.trans (by decide +kernel)
  upper_error := v4728_upper_checked
  lower_error := reuse_lower_error 90 94 Primitive.Addresses.material4728

def v4729_pa : Scalar.QComplex := ((999996139370923324726468066898 : Int)/10^30,(-2778712516417212850153854826 : Int)/10^30)
theorem v4729_pa_checked : Scalar.distance (sourceCoefficient 90 95 1 0) v4729_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4729_pb : Scalar.QComplex := ((-1198951982127035576398152 : Int)/10^30,(-431475853055874229518795485 : Int)/10^30)
theorem v4729_pb_checked : Scalar.distance (sourceCoefficient 90 95 1 1) v4729_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4729_pg : Scalar.QComplex := ((-93086070290709183907544 : Int)/10^30,(258660427212852355722 : Int)/10^30)
theorem v4729_pg_checked : Scalar.distance (sourceCoefficient 90 95 1 2) v4729_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4729_mb : Scalar.QComplex := ((-1571295763938600692978427 : Int)/10^30,(-431474657756132933286910681 : Int)/10^30)
theorem v4729_mb_checked : Scalar.distance (sourceCoefficient 90 95 3 1) v4729_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4729_mg : Scalar.QComplex := ((-93085812418211919595705 : Int)/10^30,(338989417121660795521 : Int)/10^30)
theorem v4729_mg_checked : Scalar.distance (sourceCoefficient 90 95 3 2) v4729_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4729_upper : Scalar.QComplex := ((999989854188421024146433845476 : Int)/10^30,(-4504610995464437554234407376 : Int)/10^30)
theorem v4729_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 90 95 5) 1) 14) v4729_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4729 : Material (90 : Basis) (95 : Basis) where
  plus := ![v4729_pa,v4729_pb,v4729_pg]
  minus := ![(Primitive.Addresses.material4729 1).one,v4729_mb,v4729_mg]
  upper := v4729_upper
  lower := (Primitive.Addresses.material4729 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4729_pa_checked.trans (by decide +kernel)
    · exact v4729_pb_checked.trans (by decide +kernel)
    · exact v4729_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 90 95 Primitive.Addresses.material4729
    · exact v4729_mb_checked.trans (by decide +kernel)
    · exact v4729_mg_checked.trans (by decide +kernel)
  upper_error := v4729_upper_checked
  lower_error := reuse_lower_error 90 95 Primitive.Addresses.material4729

def v4730_pa : Scalar.QComplex := ((999996080058031790195274836332 : Int)/10^30,(-2799976530343526882643478039 : Int)/10^30)
theorem v4730_pa_checked : Scalar.distance (sourceCoefficient 90 96 1 0) v4730_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4730_pb : Scalar.QComplex := ((-1208126924517725995014027 : Int)/10^30,(-431475826899901945960261954 : Int)/10^30)
theorem v4730_pb_checked : Scalar.distance (sourceCoefficient 90 96 1 1) v4730_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4730_pg : Scalar.QComplex := ((-93086064708667873110231 : Int)/10^30,(260639818179270765397 : Int)/10^30)
theorem v4730_pg_checked : Scalar.distance (sourceCoefficient 90 96 1 2) v4730_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4730_mb : Scalar.QComplex := ((-1580470680341614684508827 : Int)/10^30,(-431474623682608329692092374 : Int)/10^30)
theorem v4730_mb_checked : Scalar.distance (sourceCoefficient 90 96 3 1) v4730_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4730_mg : Scalar.QComplex := ((-93085805128047431688177 : Int)/10^30,(340968802534011240352 : Int)/10^30)
theorem v4730_mg_checked : Scalar.distance (sourceCoefficient 90 96 3 2) v4730_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4730_upper : Scalar.QComplex := ((999989758175858848656214103982 : Int)/10^30,(-4525874875351830724905700155 : Int)/10^30)
theorem v4730_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 90 96 5) 1) 14) v4730_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4730 : Material (90 : Basis) (96 : Basis) where
  plus := ![v4730_pa,v4730_pb,v4730_pg]
  minus := ![(Primitive.Addresses.material4730 1).one,v4730_mb,v4730_mg]
  upper := v4730_upper
  lower := (Primitive.Addresses.material4730 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4730_pa_checked.trans (by decide +kernel)
    · exact v4730_pb_checked.trans (by decide +kernel)
    · exact v4730_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 90 96 Primitive.Addresses.material4730
    · exact v4730_mb_checked.trans (by decide +kernel)
    · exact v4730_mg_checked.trans (by decide +kernel)
  upper_error := v4730_upper_checked
  lower_error := reuse_lower_error 90 96 Primitive.Addresses.material4730

def v4731_pa : Scalar.QComplex := ((999995872529178850955532239376 : Int)/10^30,(-2873138459295463452578865982 : Int)/10^30)
theorem v4731_pa_checked : Scalar.distance (sourceCoefficient 90 97 1 0) v4731_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4731_pb : Scalar.QComplex := ((-1239694645052751782162352 : Int)/10^30,(-431475734919251895985459299 : Int)/10^30)
theorem v4731_pb_checked : Scalar.distance (sourceCoefficient 90 97 1 1) v4731_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4731_pg : Scalar.QComplex := ((-93086045127711687016311 : Int)/10^30,(267450200173038863600 : Int)/10^30)
theorem v4731_pg_checked : Scalar.distance (sourceCoefficient 90 97 1 2) v4731_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4731_mb : Scalar.QComplex := ((-1612038309747377061934404 : Int)/10^30,(-431474504460471463944556086 : Int)/10^30)
theorem v4731_mb_checked : Scalar.distance (sourceCoefficient 90 97 3 1) v4731_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4731_mg : Scalar.QComplex := ((-93085779670045604075983 : Int)/10^30,(347779165094479577372 : Int)/10^30)
theorem v4731_mg_checked : Scalar.distance (sourceCoefficient 90 97 3 2) v4731_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4731_upper : Scalar.QComplex := ((999989424376462826569924736683 : Int)/10^30,(-4599036337161695022159568117 : Int)/10^30)
theorem v4731_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 90 97 5) 1) 14) v4731_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4731 : Material (90 : Basis) (97 : Basis) where
  plus := ![v4731_pa,v4731_pb,v4731_pg]
  minus := ![(Primitive.Addresses.material4731 1).one,v4731_mb,v4731_mg]
  upper := v4731_upper
  lower := (Primitive.Addresses.material4731 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4731_pa_checked.trans (by decide +kernel)
    · exact v4731_pb_checked.trans (by decide +kernel)
    · exact v4731_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 90 97 Primitive.Addresses.material4731
    · exact v4731_mb_checked.trans (by decide +kernel)
    · exact v4731_mg_checked.trans (by decide +kernel)
  upper_error := v4731_upper_checked
  lower_error := reuse_lower_error 90 97 Primitive.Addresses.material4731

def v4732_pa : Scalar.QComplex := ((999996444947589906670298794083 : Int)/10^30,(-2666475610574569064160621732 : Int)/10^30)
theorem v4732_pa_checked : Scalar.distance (sourceCoefficient 91 92 1 0) v4732_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4732_pb : Scalar.QComplex := ((-1150524286063598964481420 : Int)/10^30,(-431475987002015056540079132 : Int)/10^30)
theorem v4732_pb_checked : Scalar.distance (sourceCoefficient 91 92 1 1) v4732_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4732_pg : Scalar.QComplex := ((-93086098961917528285951 : Int)/10^30,(248212694974623286068 : Int)/10^30)
theorem v4732_pg_checked : Scalar.distance (sourceCoefficient 91 92 1 2) v4732_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4732_mb : Scalar.QComplex := ((-1522868201496495404007511 : Int)/10^30,(-431474833493144486319751609 : Int)/10^30)
theorem v4732_mb_checked : Scalar.distance (sourceCoefficient 91 92 3 1) v4732_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4732_mg : Scalar.QComplex := ((-93085850105331961572161 : Int)/10^30,(328541713515561421021 : Int)/10^30)
theorem v4732_mg_checked : Scalar.distance (sourceCoefficient 91 92 3 2) v4732_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4732_upper : Scalar.QComplex := ((999990353475349917383907221697 : Int)/10^30,(-4392374784183085569546908031 : Int)/10^30)
theorem v4732_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 91 92 5) 1) 14) v4732_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4732 : Material (91 : Basis) (92 : Basis) where
  plus := ![v4732_pa,v4732_pb,v4732_pg]
  minus := ![(Primitive.Addresses.material4732 1).one,v4732_mb,v4732_mg]
  upper := v4732_upper
  lower := (Primitive.Addresses.material4732 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4732_pa_checked.trans (by decide +kernel)
    · exact v4732_pb_checked.trans (by decide +kernel)
    · exact v4732_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 91 92 Primitive.Addresses.material4732
    · exact v4732_mb_checked.trans (by decide +kernel)
    · exact v4732_mg_checked.trans (by decide +kernel)
  upper_error := v4732_upper_checked
  lower_error := reuse_lower_error 91 92 Primitive.Addresses.material4732

def v4733_pa : Scalar.QComplex := ((999996343100697862141965236658 : Int)/10^30,(-2704401085520269142678386666 : Int)/10^30)
theorem v4733_pa_checked : Scalar.distance (sourceCoefficient 91 93 1 0) v4733_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4733_pb : Scalar.QComplex := ((-1166888275222018882781455 : Int)/10^30,(-431475942779625061308344820 : Int)/10^30)
theorem v4733_pb_checked : Scalar.distance (sourceCoefficient 91 93 1 1) v4733_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4733_pg : Scalar.QComplex := ((-93086089451393716308891 : Int)/10^30,(251743041958140495888 : Int)/10^30)
theorem v4733_pg_checked : Scalar.distance (sourceCoefficient 91 93 1 2) v4733_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4733_mb : Scalar.QComplex := ((-1539232146399923424002608 : Int)/10^30,(-431474775149385320101206131 : Int)/10^30)
theorem v4733_mb_checked : Scalar.distance (sourceCoefficient 91 93 3 1) v4733_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4733_mg : Scalar.QComplex := ((-93085837548281244948163 : Int)/10^30,(332072050977415392405 : Int)/10^30)
theorem v4733_mg_checked : Scalar.distance (sourceCoefficient 91 93 3 2) v4733_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4733_upper : Scalar.QComplex := ((999990186172680377769960845669 : Int)/10^30,(-4430300026864749564696501183 : Int)/10^30)
theorem v4733_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 91 93 5) 1) 14) v4733_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4733 : Material (91 : Basis) (93 : Basis) where
  plus := ![v4733_pa,v4733_pb,v4733_pg]
  minus := ![(Primitive.Addresses.material4733 1).one,v4733_mb,v4733_mg]
  upper := v4733_upper
  lower := (Primitive.Addresses.material4733 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4733_pa_checked.trans (by decide +kernel)
    · exact v4733_pb_checked.trans (by decide +kernel)
    · exact v4733_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 91 93 Primitive.Addresses.material4733
    · exact v4733_mb_checked.trans (by decide +kernel)
    · exact v4733_mg_checked.trans (by decide +kernel)
  upper_error := v4733_upper_checked
  lower_error := reuse_lower_error 91 93 Primitive.Addresses.material4733

def v4734_pa : Scalar.QComplex := ((999996220943978671306916619877 : Int)/10^30,(-2749199476464553276724988691 : Int)/10^30)
theorem v4734_pa_checked : Scalar.distance (sourceCoefficient 91 94 1 0) v4734_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4734_pb : Scalar.QComplex := ((-1186217772241114191354314 : Int)/10^30,(-431475889477164973160733473 : Int)/10^30)
theorem v4734_pb_checked : Scalar.distance (sourceCoefficient 91 94 1 1) v4734_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4734_pg : Scalar.QComplex := ((-93086078016123675058284 : Int)/10^30,(255913164058249341186 : Int)/10^30)
theorem v4734_pg_checked : Scalar.distance (sourceCoefficient 91 94 1 2) v4734_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4734_mb : Scalar.QComplex := ((-1558561590224141188326111 : Int)/10^30,(-431474705166459719645005400 : Int)/10^30)
theorem v4734_mb_checked : Scalar.distance (sourceCoefficient 91 94 3 1) v4734_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4734_mg : Scalar.QComplex := ((-93085822514387904504632 : Int)/10^30,(336242161656674175683 : Int)/10^30)
theorem v4734_mg_checked : Scalar.distance (sourceCoefficient 91 94 3 2) v4734_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4734_upper : Scalar.QComplex := ((999989986698184433463823528702 : Int)/10^30,(-4475098140255677423510934685 : Int)/10^30)
theorem v4734_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 91 94 5) 1) 14) v4734_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4734 : Material (91 : Basis) (94 : Basis) where
  plus := ![v4734_pa,v4734_pb,v4734_pg]
  minus := ![(Primitive.Addresses.material4734 1).one,v4734_mb,v4734_mg]
  upper := v4734_upper
  lower := (Primitive.Addresses.material4734 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4734_pa_checked.trans (by decide +kernel)
    · exact v4734_pb_checked.trans (by decide +kernel)
    · exact v4734_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 91 94 Primitive.Addresses.material4734
    · exact v4734_mb_checked.trans (by decide +kernel)
    · exact v4734_mg_checked.trans (by decide +kernel)
  upper_error := v4734_upper_checked
  lower_error := reuse_lower_error 91 94 Primitive.Addresses.material4734

def v4735_pa : Scalar.QComplex := ((999996098245206428730918147465 : Int)/10^30,(-2793473530114804758381813620 : Int)/10^30)
theorem v4735_pa_checked : Scalar.distance (sourceCoefficient 91 95 1 0) v4735_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4735_pb : Scalar.QComplex := ((-1205321028679164173903551 : Int)/10^30,(-431475835664183742475133105 : Int)/10^30)
theorem v4735_pb_checked : Scalar.distance (sourceCoefficient 91 95 1 1) v4735_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4735_pg : Scalar.QComplex := ((-93086066500555140530600 : Int)/10^30,(260034477382575860016 : Int)/10^30)
theorem v4735_pg_checked : Scalar.distance (sourceCoefficient 91 95 1 2) v4735_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4735_mb : Scalar.QComplex := ((-1577664793110996581662947 : Int)/10^30,(-431474634868248598685766989 : Int)/10^30)
theorem v4735_mb_checked : Scalar.distance (sourceCoefficient 91 95 3 1) v4735_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4735_mg : Scalar.QComplex := ((-93085807442315875917314 : Int)/10^30,(340363463509030387199 : Int)/10^30)
theorem v4735_mg_checked : Scalar.distance (sourceCoefficient 91 95 3 2) v4735_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4735_upper : Scalar.QComplex := ((999989787586594846733703261366 : Int)/10^30,(-4519371916197977043775841579 : Int)/10^30)
theorem v4735_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 91 95 5) 1) 14) v4735_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4735 : Material (91 : Basis) (95 : Basis) where
  plus := ![v4735_pa,v4735_pb,v4735_pg]
  minus := ![(Primitive.Addresses.material4735 1).one,v4735_mb,v4735_mg]
  upper := v4735_upper
  lower := (Primitive.Addresses.material4735 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4735_pa_checked.trans (by decide +kernel)
    · exact v4735_pb_checked.trans (by decide +kernel)
    · exact v4735_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 91 95 Primitive.Addresses.material4735
    · exact v4735_mb_checked.trans (by decide +kernel)
    · exact v4735_mg_checked.trans (by decide +kernel)
  upper_error := v4735_upper_checked
  lower_error := reuse_lower_error 91 95 Primitive.Addresses.material4735

def v4736_pa : Scalar.QComplex := ((999996038618435281619489782417 : Int)/10^30,(-2814737543163280388796766433 : Int)/10^30)
theorem v4736_pa_checked : Scalar.distance (sourceCoefficient 91 96 1 0) v4736_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4736_pb : Scalar.QComplex := ((-1214495970817342903167823 : Int)/10^30,(-431475809417923461674324212 : Int)/10^30)
theorem v4736_pb_checked : Scalar.distance (sourceCoefficient 91 96 1 1) v4736_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4736_pg : Scalar.QComplex := ((-93086060894165552667113 : Int)/10^30,(262013868280898567465 : Int)/10^30)
theorem v4736_pg_checked : Scalar.distance (sourceCoefficient 91 96 1 2) v4736_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4736_mb : Scalar.QComplex := ((-1586839709183584502663747 : Int)/10^30,(-431474600704436249373236264 : Int)/10^30)
theorem v4736_mb_checked : Scalar.distance (sourceCoefficient 91 96 3 1) v4736_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4736_mg : Scalar.QComplex := ((-93085800127803178773113 : Int)/10^30,(342342848832273688657 : Int)/10^30)
theorem v4736_mg_checked : Scalar.distance (sourceCoefficient 91 96 3 2) v4736_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4736_upper : Scalar.QComplex := ((999989691260155041219505537451 : Int)/10^30,(-4540635794665805383432179148 : Int)/10^30)
theorem v4736_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 91 96 5) 1) 14) v4736_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4736 : Material (91 : Basis) (96 : Basis) where
  plus := ![v4736_pa,v4736_pb,v4736_pg]
  minus := ![(Primitive.Addresses.material4736 1).one,v4736_mb,v4736_mg]
  upper := v4736_upper
  lower := (Primitive.Addresses.material4736 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4736_pa_checked.trans (by decide +kernel)
    · exact v4736_pb_checked.trans (by decide +kernel)
    · exact v4736_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 91 96 Primitive.Addresses.material4736
    · exact v4736_mb_checked.trans (by decide +kernel)
    · exact v4736_mg_checked.trans (by decide +kernel)
  upper_error := v4736_upper_checked
  lower_error := reuse_lower_error 91 96 Primitive.Addresses.material4736

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
