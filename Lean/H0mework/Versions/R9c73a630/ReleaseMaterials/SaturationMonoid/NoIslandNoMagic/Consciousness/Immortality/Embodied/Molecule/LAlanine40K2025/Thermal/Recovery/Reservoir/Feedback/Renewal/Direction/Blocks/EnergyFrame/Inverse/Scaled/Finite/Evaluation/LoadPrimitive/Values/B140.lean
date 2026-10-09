import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B093
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B094

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2241_pa : Scalar.QComplex := ((999999265136938002101928603274 : Int)/10^30,(-1212322392753708172577740625 : Int)/10^30)
theorem v2241_pa_checked : Scalar.distance (sourceCoefficient 26 71 1 0) v2241_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2241_pb : Scalar.QComplex := ((-523089816819146294841709 : Int)/10^30,(-431477167745453916843775512 : Int)/10^30)
theorem v2241_pb_checked : Scalar.distance (sourceCoefficient 26 71 1 1) v2241_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2241_pg : Scalar.QComplex := ((-93086357588665467993550 : Int)/10^30,(112850758694472303722 : Int)/10^30)
theorem v2241_pg_checked : Scalar.distance (sourceCoefficient 26 71 1 2) v2241_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2241_mb : Scalar.QComplex := ((-895434984802979831946575 : Int)/10^30,(-431476555683832060354925089 : Int)/10^30)
theorem v2241_mb_checked : Scalar.distance (sourceCoefficient 26 71 3 1) v2241_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2241_mg : Scalar.QComplex := ((-93086225543238137193717 : Int)/10^30,(193180050820081017514 : Int)/10^30)
theorem v2241_mg_checked : Scalar.distance (sourceCoefficient 26 71 3 2) v2241_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2241_upper : Scalar.QComplex := ((999995683397031881449981685202 : Int)/10^30,(-2938228599543595019554561668 : Int)/10^30)
theorem v2241_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 71 5) 1) 14) v2241_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2241 : Material (26 : Basis) (71 : Basis) where
  plus := ![v2241_pa,v2241_pb,v2241_pg]
  minus := ![(Primitive.Addresses.material2241 1).one,v2241_mb,v2241_mg]
  upper := v2241_upper
  lower := (Primitive.Addresses.material2241 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2241_pa_checked.trans (by decide +kernel)
    · exact v2241_pb_checked.trans (by decide +kernel)
    · exact v2241_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 71 Primitive.Addresses.material2241
    · exact v2241_mb_checked.trans (by decide +kernel)
    · exact v2241_mg_checked.trans (by decide +kernel)
  upper_error := v2241_upper_checked
  lower_error := reuse_lower_error 26 71 Primitive.Addresses.material2241

def v2242_pa : Scalar.QComplex := ((999999232829442191291052644910 : Int)/10^30,(-1238684999128815286140375065 : Int)/10^30)
theorem v2242_pa_checked : Scalar.distance (sourceCoefficient 26 72 1 0) v2242_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2242_pb : Scalar.QComplex := ((-534464684518080265777978 : Int)/10^30,(-431477151066176157275856709 : Int)/10^30)
theorem v2242_pb_checked : Scalar.distance (sourceCoefficient 26 72 1 1) v2242_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2242_pg : Scalar.QComplex := ((-93086354285787304946700 : Int)/10^30,(115304759135811423124 : Int)/10^30)
theorem v2242_pg_checked : Scalar.distance (sourceCoefficient 26 72 1 2) v2242_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2242_mb : Scalar.QComplex := ((-906809833873065201711492 : Int)/10^30,(-431476529188561992087883487 : Int)/10^30)
theorem v2242_mb_checked : Scalar.distance (sourceCoefficient 26 72 3 1) v2242_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2242_mg : Scalar.QComplex := ((-93086220122669347160727 : Int)/10^30,(195634047497448520646 : Int)/10^30)
theorem v2242_mg_checked : Scalar.distance (sourceCoefficient 26 72 3 2) v2242_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2242_upper : Scalar.QComplex := ((999995605590117182392352317868 : Int)/10^30,(-2964591110894889850341495751 : Int)/10^30)
theorem v2242_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 72 5) 1) 14) v2242_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2242 : Material (26 : Basis) (72 : Basis) where
  plus := ![v2242_pa,v2242_pb,v2242_pg]
  minus := ![(Primitive.Addresses.material2242 1).one,v2242_mb,v2242_mg]
  upper := v2242_upper
  lower := (Primitive.Addresses.material2242 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2242_pa_checked.trans (by decide +kernel)
    · exact v2242_pb_checked.trans (by decide +kernel)
    · exact v2242_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 72 Primitive.Addresses.material2242
    · exact v2242_mb_checked.trans (by decide +kernel)
    · exact v2242_mg_checked.trans (by decide +kernel)
  upper_error := v2242_upper_checked
  lower_error := reuse_lower_error 26 72 Primitive.Addresses.material2242

def v2243_pa : Scalar.QComplex := ((999999221079663779607261633079 : Int)/10^30,(-1248134634454110202520811865 : Int)/10^30)
theorem v2243_pa_checked : Scalar.distance (sourceCoefficient 26 73 1 0) v2243_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2243_pb : Scalar.QComplex := ((-538541988118915178692652 : Int)/10^30,(-431477144990169826994722997 : Int)/10^30)
theorem v2243_pb_checked : Scalar.distance (sourceCoefficient 26 73 1 1) v2243_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2243_pg : Scalar.QComplex := ((-93086353083499774013022 : Int)/10^30,(116184391776925730972 : Int)/10^30)
theorem v2243_pg_checked : Scalar.distance (sourceCoefficient 26 73 1 2) v2243_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2243_mb : Scalar.QComplex := ((-910887130712413832189303 : Int)/10^30,(-431476519594028551598396202 : Int)/10^30)
theorem v2243_mb_checked : Scalar.distance (sourceCoefficient 26 73 3 1) v2243_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2243_mg : Scalar.QComplex := ((-93086218161298911795493 : Int)/10^30,(196513678773515404834 : Int)/10^30)
theorem v2243_mg_checked : Scalar.distance (sourceCoefficient 26 73 3 2) v2243_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2243_upper : Scalar.QComplex := ((999995577531142963384384073317 : Int)/10^30,(-2974040711867011374840652920 : Int)/10^30)
theorem v2243_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 73 5) 1) 14) v2243_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2243 : Material (26 : Basis) (73 : Basis) where
  plus := ![v2243_pa,v2243_pb,v2243_pg]
  minus := ![(Primitive.Addresses.material2243 1).one,v2243_mb,v2243_mg]
  upper := v2243_upper
  lower := (Primitive.Addresses.material2243 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2243_pa_checked.trans (by decide +kernel)
    · exact v2243_pb_checked.trans (by decide +kernel)
    · exact v2243_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 73 Primitive.Addresses.material2243
    · exact v2243_mb_checked.trans (by decide +kernel)
    · exact v2243_mg_checked.trans (by decide +kernel)
  upper_error := v2243_upper_checked
  lower_error := reuse_lower_error 26 73 Primitive.Addresses.material2243

def v2244_pa : Scalar.QComplex := ((999999207751502989402977608633 : Int)/10^30,(-1258767796840828395535860517 : Int)/10^30)
theorem v2244_pa_checked : Scalar.distance (sourceCoefficient 26 74 1 0) v2244_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2244_pb : Scalar.QComplex := ((-543129956796821143545630 : Int)/10^30,(-431477138091742982675971776 : Int)/10^30)
theorem v2244_pb_checked : Scalar.distance (sourceCoefficient 26 74 1 1) v2244_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2244_pg : Scalar.QComplex := ((-93086351719035257283163 : Int)/10^30,(117174194700400109638 : Int)/10^30)
theorem v2244_pg_checked : Scalar.distance (sourceCoefficient 26 74 1 2) v2244_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2244_mb : Scalar.QComplex := ((-915475091728977704695379 : Int)/10^30,(-431476508736393941285007097 : Int)/10^30)
theorem v2244_mb_checked : Scalar.distance (sourceCoefficient 26 74 3 1) v2244_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2244_mg : Scalar.QComplex := ((-93086215942679559228564 : Int)/10^30,(197503480150969494125 : Int)/10^30)
theorem v2244_mg_checked : Scalar.distance (sourceCoefficient 26 74 3 2) v2244_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2244_upper : Scalar.QComplex := ((999995545851128377390784111828 : Int)/10^30,(-2984673835413686849243661706 : Int)/10^30)
theorem v2244_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 74 5) 1) 14) v2244_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2244 : Material (26 : Basis) (74 : Basis) where
  plus := ![v2244_pa,v2244_pb,v2244_pg]
  minus := ![(Primitive.Addresses.material2244 1).one,v2244_mb,v2244_mg]
  upper := v2244_upper
  lower := (Primitive.Addresses.material2244 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2244_pa_checked.trans (by decide +kernel)
    · exact v2244_pb_checked.trans (by decide +kernel)
    · exact v2244_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 74 Primitive.Addresses.material2244
    · exact v2244_mb_checked.trans (by decide +kernel)
    · exact v2244_mg_checked.trans (by decide +kernel)
  upper_error := v2244_upper_checked
  lower_error := reuse_lower_error 26 74 Primitive.Addresses.material2244

def v2245_pa : Scalar.QComplex := ((999999188992951836931275111468 : Int)/10^30,(-1273582913906159970513778506 : Int)/10^30)
theorem v2245_pa_checked : Scalar.distance (sourceCoefficient 26 75 1 0) v2245_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2245_pb : Scalar.QComplex := ((-549522344102060805618401 : Int)/10^30,(-431477128371758638562407964 : Int)/10^30)
theorem v2245_pb_checked : Scalar.distance (sourceCoefficient 26 75 1 1) v2245_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2245_pg : Scalar.QComplex := ((-93086349797463241057988 : Int)/10^30,(118553280767487603832 : Int)/10^30)
theorem v2245_pg_checked : Scalar.distance (sourceCoefficient 26 75 1 2) v2245_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2245_mb : Scalar.QComplex := ((-921867468266130709369241 : Int)/10^30,(-431476493500070874380798633 : Int)/10^30)
theorem v2245_mb_checked : Scalar.distance (sourceCoefficient 26 75 3 1) v2245_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2245_mg : Scalar.QComplex := ((-93086212831019094326730 : Int)/10^30,(198882564046330112584 : Int)/10^30)
theorem v2245_mg_checked : Scalar.distance (sourceCoefficient 26 75 3 2) v2245_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2245_upper : Scalar.QComplex := ((999995501523057125736473454458 : Int)/10^30,(-2999488898038084334611469275 : Int)/10^30)
theorem v2245_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 75 5) 1) 14) v2245_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2245 : Material (26 : Basis) (75 : Basis) where
  plus := ![v2245_pa,v2245_pb,v2245_pg]
  minus := ![(Primitive.Addresses.material2245 1).one,v2245_mb,v2245_mg]
  upper := v2245_upper
  lower := (Primitive.Addresses.material2245 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2245_pa_checked.trans (by decide +kernel)
    · exact v2245_pb_checked.trans (by decide +kernel)
    · exact v2245_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 75 Primitive.Addresses.material2245
    · exact v2245_mb_checked.trans (by decide +kernel)
    · exact v2245_mg_checked.trans (by decide +kernel)
  upper_error := v2245_upper_checked
  lower_error := reuse_lower_error 26 75 Primitive.Addresses.material2245

def v2246_pa : Scalar.QComplex := ((999999173084825958551729107822 : Int)/10^30,(-1286013088694742438462261163 : Int)/10^30)
theorem v2246_pa_checked : Scalar.distance (sourceCoefficient 26 76 1 0) v2246_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2246_pb : Scalar.QComplex := ((-554885682788845436914455 : Int)/10^30,(-431477120119083122345538057 : Int)/10^30)
theorem v2246_pb_checked : Scalar.distance (sourceCoefficient 26 76 1 1) v2246_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2246_pg : Scalar.QComplex := ((-93086348166836882481195 : Int)/10^30,(119710361111662168160 : Int)/10^30)
theorem v2246_pg_checked : Scalar.distance (sourceCoefficient 26 76 1 2) v2246_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2246_mb : Scalar.QComplex := ((-927230797834211947100813 : Int)/10^30,(-431476480619078700124532218 : Int)/10^30)
theorem v2246_mb_checked : Scalar.distance (sourceCoefficient 26 76 3 1) v2246_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2246_mg : Scalar.QComplex := ((-93086210201885118848182 : Int)/10^30,(200039642552513676824 : Int)/10^30)
theorem v2246_mg_checked : Scalar.distance (sourceCoefficient 26 76 3 2) v2246_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2246_upper : Scalar.QComplex := ((999995464161600912196433761464 : Int)/10^30,(-3011919026857399513690173575 : Int)/10^30)
theorem v2246_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 76 5) 1) 14) v2246_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2246 : Material (26 : Basis) (76 : Basis) where
  plus := ![v2246_pa,v2246_pb,v2246_pg]
  minus := ![(Primitive.Addresses.material2246 1).one,v2246_mb,v2246_mg]
  upper := v2246_upper
  lower := (Primitive.Addresses.material2246 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2246_pa_checked.trans (by decide +kernel)
    · exact v2246_pb_checked.trans (by decide +kernel)
    · exact v2246_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 76 Primitive.Addresses.material2246
    · exact v2246_mb_checked.trans (by decide +kernel)
    · exact v2246_mg_checked.trans (by decide +kernel)
  upper_error := v2246_upper_checked
  lower_error := reuse_lower_error 26 76 Primitive.Addresses.material2246

def v2247_pa : Scalar.QComplex := ((999999169379933983466992479585 : Int)/10^30,(-1288890779741779340552230947 : Int)/10^30)
theorem v2247_pa_checked : Scalar.distance (sourceCoefficient 26 77 1 0) v2247_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2247_pb : Scalar.QComplex := ((-556127341242710263924108 : Int)/10^30,(-431477118195847186758744692 : Int)/10^30)
theorem v2247_pb_checked : Scalar.distance (sourceCoefficient 26 77 1 1) v2247_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2247_pg : Scalar.QComplex := ((-93086347786941020429243 : Int)/10^30,(119978235038754375961 : Int)/10^30)
theorem v2247_pg_checked : Scalar.distance (sourceCoefficient 26 77 1 2) v2247_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2247_mb : Scalar.QComplex := ((-928472454166084592061587 : Int)/10^30,(-431476477624348157181859841 : Int)/10^30)
theorem v2247_mb_checked : Scalar.distance (sourceCoefficient 26 77 3 1) v2247_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2247_mg : Scalar.QComplex := ((-93086209590826263762064 : Int)/10^30,(200307516052031160050 : Int)/10^30)
theorem v2247_mg_checked : Scalar.distance (sourceCoefficient 26 77 3 2) v2247_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2247_upper : Scalar.QComplex := ((999995455490080770019875866697 : Int)/10^30,(-3014796707224146194733105114 : Int)/10^30)
theorem v2247_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 77 5) 1) 14) v2247_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2247 : Material (26 : Basis) (77 : Basis) where
  plus := ![v2247_pa,v2247_pb,v2247_pg]
  minus := ![(Primitive.Addresses.material2247 1).one,v2247_mb,v2247_mg]
  upper := v2247_upper
  lower := (Primitive.Addresses.material2247 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2247_pa_checked.trans (by decide +kernel)
    · exact v2247_pb_checked.trans (by decide +kernel)
    · exact v2247_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 77 Primitive.Addresses.material2247
    · exact v2247_mb_checked.trans (by decide +kernel)
    · exact v2247_mg_checked.trans (by decide +kernel)
  upper_error := v2247_upper_checked
  lower_error := reuse_lower_error 26 77 Primitive.Addresses.material2247

def v2248_pa : Scalar.QComplex := ((999999146933015133345323312331 : Int)/10^30,(-1306190354431554009050605912 : Int)/10^30)
theorem v2248_pa_checked : Scalar.distance (sourceCoefficient 26 78 1 0) v2248_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2248_pb : Scalar.QComplex := ((-563591715493818441821445 : Int)/10^30,(-431477106533683171378031292 : Int)/10^30)
theorem v2248_pb_checked : Scalar.distance (sourceCoefficient 26 78 1 1) v2248_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2248_pg : Scalar.QComplex := ((-93086345484198785688606 : Int)/10^30,(121588590323955840710 : Int)/10^30)
theorem v2248_pg_checked : Scalar.distance (sourceCoefficient 26 78 1 2) v2248_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2248_mb : Scalar.QComplex := ((-935936815573942796611186 : Int)/10^30,(-431476459520769688388011761 : Int)/10^30)
theorem v2248_mb_checked : Scalar.distance (sourceCoefficient 26 78 3 1) v2248_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2248_mg : Scalar.QComplex := ((-93086205898420803018427 : Int)/10^30,(201917868750460918325 : Int)/10^30)
theorem v2248_mg_checked : Scalar.distance (sourceCoefficient 26 78 3 2) v2248_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2248_upper : Scalar.QComplex := ((999995403185698842552291873600 : Int)/10^30,(-3032096217406890946866823455 : Int)/10^30)
theorem v2248_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 78 5) 1) 14) v2248_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2248 : Material (26 : Basis) (78 : Basis) where
  plus := ![v2248_pa,v2248_pb,v2248_pg]
  minus := ![(Primitive.Addresses.material2248 1).one,v2248_mb,v2248_mg]
  upper := v2248_upper
  lower := (Primitive.Addresses.material2248 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2248_pa_checked.trans (by decide +kernel)
    · exact v2248_pb_checked.trans (by decide +kernel)
    · exact v2248_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 78 Primitive.Addresses.material2248
    · exact v2248_mb_checked.trans (by decide +kernel)
    · exact v2248_mg_checked.trans (by decide +kernel)
  upper_error := v2248_upper_checked
  lower_error := reuse_lower_error 26 78 Primitive.Addresses.material2248

def v2249_pa : Scalar.QComplex := ((999999139632733730621371674687 : Int)/10^30,(-1311767430723496957186730497 : Int)/10^30)
theorem v2249_pa_checked : Scalar.distance (sourceCoefficient 26 79 1 0) v2249_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2249_pb : Scalar.QComplex := ((-565998097439972815686381 : Int)/10^30,(-431477102737308119215454726 : Int)/10^30)
theorem v2249_pb_checked : Scalar.distance (sourceCoefficient 26 79 1 1) v2249_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2249_pg : Scalar.QComplex := ((-93086344734907575182453 : Int)/10^30,(122107740325854162842 : Int)/10^30)
theorem v2249_pg_checked : Scalar.distance (sourceCoefficient 26 79 1 2) v2249_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2249_mb : Scalar.QComplex := ((-938343193347990507203813 : Int)/10^30,(-431476453647796809677767005 : Int)/10^30)
theorem v2249_mb_checked : Scalar.distance (sourceCoefficient 26 79 3 1) v2249_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2249_mg : Scalar.QComplex := ((-93086204701126801517502 : Int)/10^30,(202437017912451400580 : Int)/10^30)
theorem v2249_mg_checked : Scalar.distance (sourceCoefficient 26 79 3 2) v2249_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2249_upper : Scalar.QComplex := ((999995386259900581255362803823 : Int)/10^30,(-3037673272792810462809404465 : Int)/10^30)
theorem v2249_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 79 5) 1) 14) v2249_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2249 : Material (26 : Basis) (79 : Basis) where
  plus := ![v2249_pa,v2249_pb,v2249_pg]
  minus := ![(Primitive.Addresses.material2249 1).one,v2249_mb,v2249_mg]
  upper := v2249_upper
  lower := (Primitive.Addresses.material2249 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2249_pa_checked.trans (by decide +kernel)
    · exact v2249_pb_checked.trans (by decide +kernel)
    · exact v2249_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 79 Primitive.Addresses.material2249
    · exact v2249_mb_checked.trans (by decide +kernel)
    · exact v2249_mg_checked.trans (by decide +kernel)
  upper_error := v2249_upper_checked
  lower_error := reuse_lower_error 26 79 Primitive.Addresses.material2249

def v2250_pa : Scalar.QComplex := ((999999128166729978117220619049 : Int)/10^30,(-1320479375056844589757223935 : Int)/10^30)
theorem v2250_pa_checked : Scalar.distance (sourceCoefficient 26 80 1 0) v2250_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2250_pb : Scalar.QComplex := ((-569757103828957189646480 : Int)/10^30,(-431477096771186677333561259 : Int)/10^30)
theorem v2250_pb_checked : Scalar.distance (sourceCoefficient 26 80 1 1) v2250_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2250_pg : Scalar.QComplex := ((-93086343557681044144157 : Int)/10^30,(122918703931988992510 : Int)/10^30)
theorem v2250_pg_checked : Scalar.distance (sourceCoefficient 26 80 1 2) v2250_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2250_mb : Scalar.QComplex := ((-942102193188830907257106 : Int)/10^30,(-431476444437824374925108927 : Int)/10^30)
theorem v2250_mb_checked : Scalar.distance (sourceCoefficient 26 80 3 1) v2250_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2250_mg : Scalar.QComplex := ((-93086202824075641165057 : Int)/10^30,(203247980200733940845 : Int)/10^30)
theorem v2250_mg_checked : Scalar.distance (sourceCoefficient 26 80 3 2) v2250_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2250_upper : Scalar.QComplex := ((999995359757888328075008834938 : Int)/10^30,(-3046385184361458098641060188 : Int)/10^30)
theorem v2250_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 80 5) 1) 14) v2250_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2250 : Material (26 : Basis) (80 : Basis) where
  plus := ![v2250_pa,v2250_pb,v2250_pg]
  minus := ![(Primitive.Addresses.material2250 1).one,v2250_mb,v2250_mg]
  upper := v2250_upper
  lower := (Primitive.Addresses.material2250 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2250_pa_checked.trans (by decide +kernel)
    · exact v2250_pb_checked.trans (by decide +kernel)
    · exact v2250_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 80 Primitive.Addresses.material2250
    · exact v2250_mb_checked.trans (by decide +kernel)
    · exact v2250_mg_checked.trans (by decide +kernel)
  upper_error := v2250_upper_checked
  lower_error := reuse_lower_error 26 80 Primitive.Addresses.material2250

def v2251_pa : Scalar.QComplex := ((999999093183668626008353900608 : Int)/10^30,(-1346711491163613872582226808 : Int)/10^30)
theorem v2251_pa_checked : Scalar.distance (sourceCoefficient 26 81 1 0) v2251_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2251_pb : Scalar.QComplex := ((-581075666776746938246588 : Int)/10^30,(-431477078543207370100303418 : Int)/10^30)
theorem v2251_pb_checked : Scalar.distance (sourceCoefficient 26 81 1 1) v2251_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2251_pg : Scalar.QComplex := ((-93086339963215972849687 : Int)/10^30,(125360557377826424877 : Int)/10^30)
theorem v2251_pg_checked : Scalar.distance (sourceCoefficient 26 81 1 2) v2251_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2251_mb : Scalar.QComplex := ((-953420736192277202084348 : Int)/10^30,(-431476416442441800010701969 : Int)/10^30)
theorem v2251_mb_checked : Scalar.distance (sourceCoefficient 26 81 3 1) v2251_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2251_mg : Scalar.QComplex := ((-93086197122402361493166 : Int)/10^30,(205689829635496269280 : Int)/10^30)
theorem v2251_mg_checked : Scalar.distance (sourceCoefficient 26 81 3 2) v2251_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2251_upper : Scalar.QComplex := ((999995279500626437826393971063 : Int)/10^30,(-3072617201020981626045384433 : Int)/10^30)
theorem v2251_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 81 5) 1) 14) v2251_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2251 : Material (26 : Basis) (81 : Basis) where
  plus := ![v2251_pa,v2251_pb,v2251_pg]
  minus := ![(Primitive.Addresses.material2251 1).one,v2251_mb,v2251_mg]
  upper := v2251_upper
  lower := (Primitive.Addresses.material2251 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2251_pa_checked.trans (by decide +kernel)
    · exact v2251_pb_checked.trans (by decide +kernel)
    · exact v2251_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 81 Primitive.Addresses.material2251
    · exact v2251_mb_checked.trans (by decide +kernel)
    · exact v2251_mg_checked.trans (by decide +kernel)
  upper_error := v2251_upper_checked
  lower_error := reuse_lower_error 26 81 Primitive.Addresses.material2251

def v2252_pa : Scalar.QComplex := ((999999079747603406144193130368 : Int)/10^30,(-1356651740987066355006366043 : Int)/10^30)
theorem v2252_pa_checked : Scalar.distance (sourceCoefficient 26 82 1 0) v2252_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2252_pb : Scalar.QComplex := ((-585364658973893722046792 : Int)/10^30,(-431477071532571004338604372 : Int)/10^30)
theorem v2252_pb_checked : Scalar.distance (sourceCoefficient 26 82 1 1) v2252_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2252_pg : Scalar.QComplex := ((-93086338581625264204452 : Int)/10^30,(126285859513738313068 : Int)/10^30)
theorem v2252_pg_checked : Scalar.distance (sourceCoefficient 26 82 1 2) v2252_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2252_mb : Scalar.QComplex := ((-957709720742572737948452 : Int)/10^30,(-431476405730600947529437130 : Int)/10^30)
theorem v2252_mb_checked : Scalar.distance (sourceCoefficient 26 82 3 1) v2252_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2252_mg : Scalar.QComplex := ((-93086194942318098046522 : Int)/10^30,(206615130234625326850 : Int)/10^30)
theorem v2252_mg_checked : Scalar.distance (sourceCoefficient 26 82 3 2) v2252_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2252_upper : Scalar.QComplex := ((999995248908611806543806477348 : Int)/10^30,(-3082557412850170001034819570 : Int)/10^30)
theorem v2252_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 82 5) 1) 14) v2252_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2252 : Material (26 : Basis) (82 : Basis) where
  plus := ![v2252_pa,v2252_pb,v2252_pg]
  minus := ![(Primitive.Addresses.material2252 1).one,v2252_mb,v2252_mg]
  upper := v2252_upper
  lower := (Primitive.Addresses.material2252 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2252_pa_checked.trans (by decide +kernel)
    · exact v2252_pb_checked.trans (by decide +kernel)
    · exact v2252_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 82 Primitive.Addresses.material2252
    · exact v2252_mb_checked.trans (by decide +kernel)
    · exact v2252_mg_checked.trans (by decide +kernel)
  upper_error := v2252_upper_checked
  lower_error := reuse_lower_error 26 82 Primitive.Addresses.material2252

def v2253_pa : Scalar.QComplex := ((999999061247656699415607394923 : Int)/10^30,(-1370220349193956005770237070 : Int)/10^30)
theorem v2253_pa_checked : Scalar.distance (sourceCoefficient 26 83 1 0) v2253_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2253_pb : Scalar.QComplex := ((-591219205394722730366076 : Int)/10^30,(-431477061871178424791147258 : Int)/10^30)
theorem v2253_pb_checked : Scalar.distance (sourceCoefficient 26 83 1 1) v2253_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2253_pg : Scalar.QComplex := ((-93086336678409786898754 : Int)/10^30,(127548912485517294244 : Int)/10^30)
theorem v2253_pg_checked : Scalar.distance (sourceCoefficient 26 83 1 2) v2253_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2253_mb : Scalar.QComplex := ((-963564256646139884623068 : Int)/10^30,(-431476391017002083167120861 : Int)/10^30)
theorem v2253_mb_checked : Scalar.distance (sourceCoefficient 26 83 3 1) v2253_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2253_mg : Scalar.QComplex := ((-93086191949145500543815 : Int)/10^30,(207878181093722722988 : Int)/10^30)
theorem v2253_mg_checked : Scalar.distance (sourceCoefficient 26 83 3 2) v2253_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2253_upper : Scalar.QComplex := ((999995206990505822742143035671 : Int)/10^30,(-3096125968918981894562067659 : Int)/10^30)
theorem v2253_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 83 5) 1) 14) v2253_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2253 : Material (26 : Basis) (83 : Basis) where
  plus := ![v2253_pa,v2253_pb,v2253_pg]
  minus := ![(Primitive.Addresses.material2253 1).one,v2253_mb,v2253_mg]
  upper := v2253_upper
  lower := (Primitive.Addresses.material2253 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2253_pa_checked.trans (by decide +kernel)
    · exact v2253_pb_checked.trans (by decide +kernel)
    · exact v2253_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 83 Primitive.Addresses.material2253
    · exact v2253_mb_checked.trans (by decide +kernel)
    · exact v2253_mg_checked.trans (by decide +kernel)
  upper_error := v2253_upper_checked
  lower_error := reuse_lower_error 26 83 Primitive.Addresses.material2253

def v2254_pa : Scalar.QComplex := ((999999012482029410549598537555 : Int)/10^30,(-1405359372540404188348140722 : Int)/10^30)
theorem v2254_pa_checked : Scalar.distance (sourceCoefficient 26 84 1 0) v2254_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2254_pb : Scalar.QComplex := ((-606380895894347823648428 : Int)/10^30,(-431477036358458289219075183 : Int)/10^30)
theorem v2254_pb_checked : Scalar.distance (sourceCoefficient 26 84 1 1) v2254_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2254_pg : Scalar.QComplex := ((-93086331656659268185773 : Int)/10^30,(130819877836070905697 : Int)/10^30)
theorem v2254_pg_checked : Scalar.distance (sourceCoefficient 26 84 1 2) v2254_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2254_mb : Scalar.QComplex := ((-978725919484046254669507 : Int)/10^30,(-431476352420435403161541310 : Int)/10^30)
theorem v2254_mb_checked : Scalar.distance (sourceCoefficient 26 84 3 1) v2254_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2254_mg : Scalar.QComplex := ((-93086184104701072940949 : Int)/10^30,(211149140892801917527 : Int)/10^30)
theorem v2254_mg_checked : Scalar.distance (sourceCoefficient 26 84 3 2) v2254_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2254_upper : Scalar.QComplex := ((999995097578184655876366815563 : Int)/10^30,(-3131264855764933804810821906 : Int)/10^30)
theorem v2254_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 84 5) 1) 14) v2254_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2254 : Material (26 : Basis) (84 : Basis) where
  plus := ![v2254_pa,v2254_pb,v2254_pg]
  minus := ![(Primitive.Addresses.material2254 1).one,v2254_mb,v2254_mg]
  upper := v2254_upper
  lower := (Primitive.Addresses.material2254 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2254_pa_checked.trans (by decide +kernel)
    · exact v2254_pb_checked.trans (by decide +kernel)
    · exact v2254_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 84 Primitive.Addresses.material2254
    · exact v2254_mb_checked.trans (by decide +kernel)
    · exact v2254_mg_checked.trans (by decide +kernel)
  upper_error := v2254_upper_checked
  lower_error := reuse_lower_error 26 84 Primitive.Addresses.material2254

def v2255_pa : Scalar.QComplex := ((999998898253803061011801328322 : Int)/10^30,(-1484416107442011667899603468 : Int)/10^30)
theorem v2255_pa_checked : Scalar.distance (sourceCoefficient 26 85 1 0) v2255_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2255_pb : Scalar.QComplex := ((-640492079362338681065293 : Int)/10^30,(-431476976362334915085806417 : Int)/10^30)
theorem v2255_pb_checked : Scalar.distance (sourceCoefficient 26 85 1 1) v2255_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2255_pg : Scalar.QComplex := ((-93086319868365405553443 : Int)/10^30,(138178984833272004216 : Int)/10^30)
theorem v2255_pg_checked : Scalar.distance (sourceCoefficient 26 85 1 2) v2255_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2255_mb : Scalar.QComplex := ((-1012837038476932202066959 : Int)/10^30,(-431476262987919346123718464 : Int)/10^30)
theorem v2255_mb_checked : Scalar.distance (sourceCoefficient 26 85 3 1) v2255_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2255_mg : Scalar.QComplex := ((-93086165965833702920081 : Int)/10^30,(218508234977104474779 : Int)/10^30)
theorem v2255_mg_checked : Scalar.distance (sourceCoefficient 26 85 3 2) v2255_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2255_upper : Scalar.QComplex := ((999994846905375966654928665335 : Int)/10^30,(-3210321275773265329294713662 : Int)/10^30)
theorem v2255_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 85 5) 1) 14) v2255_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2255 : Material (26 : Basis) (85 : Basis) where
  plus := ![v2255_pa,v2255_pb,v2255_pg]
  minus := ![(Primitive.Addresses.material2255 1).one,v2255_mb,v2255_mg]
  upper := v2255_upper
  lower := (Primitive.Addresses.material2255 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2255_pa_checked.trans (by decide +kernel)
    · exact v2255_pb_checked.trans (by decide +kernel)
    · exact v2255_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 85 Primitive.Addresses.material2255
    · exact v2255_mb_checked.trans (by decide +kernel)
    · exact v2255_mg_checked.trans (by decide +kernel)
  upper_error := v2255_upper_checked
  lower_error := reuse_lower_error 26 85 Primitive.Addresses.material2255

def v2256_pa : Scalar.QComplex := ((999998876497766632945253995991 : Int)/10^30,(-1499000735315643903319515452 : Int)/10^30)
theorem v2256_pa_checked : Scalar.distance (sourceCoefficient 26 86 1 0) v2256_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2256_pb : Scalar.QComplex := ((-646785014323088802134849 : Int)/10^30,(-431476964901213092739551246 : Int)/10^30)
theorem v2256_pb_checked : Scalar.distance (sourceCoefficient 26 86 1 1) v2256_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2256_pg : Scalar.QComplex := ((-93086317619465354958199 : Int)/10^30,(139536615329103104755 : Int)/10^30)
theorem v2256_pg_checked : Scalar.distance (sourceCoefficient 26 86 1 2) v2256_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2256_mb : Scalar.QComplex := ((-1019129961204103092993939 : Int)/10^30,(-431476246096282343419028285 : Int)/10^30)
theorem v2256_mb_checked : Scalar.distance (sourceCoefficient 26 86 3 1) v2256_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2256_mg : Scalar.QComplex := ((-93086162545360517198574 : Int)/10^30,(219865863026728237976 : Int)/10^30)
theorem v2256_mg_checked : Scalar.distance (sourceCoefficient 26 86 3 2) v2256_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2256_upper : Scalar.QComplex := ((999994799977627338864909449420 : Int)/10^30,(-3224905844375862395041599291 : Int)/10^30)
theorem v2256_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 86 5) 1) 14) v2256_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2256 : Material (26 : Basis) (86 : Basis) where
  plus := ![v2256_pa,v2256_pb,v2256_pg]
  minus := ![(Primitive.Addresses.material2256 1).one,v2256_mb,v2256_mg]
  upper := v2256_upper
  lower := (Primitive.Addresses.material2256 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2256_pa_checked.trans (by decide +kernel)
    · exact v2256_pb_checked.trans (by decide +kernel)
    · exact v2256_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 86 Primitive.Addresses.material2256
    · exact v2256_mb_checked.trans (by decide +kernel)
    · exact v2256_mg_checked.trans (by decide +kernel)
  upper_error := v2256_upper_checked
  lower_error := reuse_lower_error 26 86 Primitive.Addresses.material2256

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
