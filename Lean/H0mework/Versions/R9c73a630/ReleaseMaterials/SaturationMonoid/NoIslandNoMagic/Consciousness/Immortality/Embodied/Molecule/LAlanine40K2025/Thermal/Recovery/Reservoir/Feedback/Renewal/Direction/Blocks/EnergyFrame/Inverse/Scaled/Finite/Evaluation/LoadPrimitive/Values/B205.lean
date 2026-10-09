import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B136
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B137

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3281_pa : Scalar.QComplex := ((999999343083295943741772797060 : Int)/10^30,(-1146225534776188968438150271 : Int)/10^30)
theorem v3281_pa_checked : Scalar.distance (sourceCoefficient 43 57 1 0) v3281_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3281_pb : Scalar.QComplex := ((-494570550324523916053356 : Int)/10^30,(-431477235873511960134109412 : Int)/10^30)
theorem v3281_pb_checked : Scalar.distance (sourceCoefficient 43 57 1 1) v3281_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3281_pg : Scalar.QComplex := ((-93086368565471298955879 : Int)/10^30,(106698042681057293294 : Int)/10^30)
theorem v3281_pg_checked : Scalar.distance (sourceCoefficient 43 57 1 2) v3281_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3281_mb : Scalar.QComplex := ((-866915787718829481502629 : Int)/10^30,(-431476648422707261233238016 : Int)/10^30)
theorem v3281_mb_checked : Scalar.distance (sourceCoefficient 43 57 3 1) v3281_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3281_mg : Scalar.QComplex := ((-93086241829556692524214 : Int)/10^30,(187027346570092427032 : Int)/10^30)
theorem v3281_mg_checked : Scalar.distance (sourceCoefficient 43 57 3 2) v3281_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3281_upper : Scalar.QComplex := ((999995875420454340228533509321 : Int)/10^30,(-2872131974537924059496087175 : Int)/10^30)
theorem v3281_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 57 5) 1) 14) v3281_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3281 : Material (43 : Basis) (57 : Basis) where
  plus := ![v3281_pa,v3281_pb,v3281_pg]
  minus := ![(Primitive.Addresses.material3281 1).one,v3281_mb,v3281_mg]
  upper := v3281_upper
  lower := (Primitive.Addresses.material3281 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3281_pa_checked.trans (by decide +kernel)
    · exact v3281_pb_checked.trans (by decide +kernel)
    · exact v3281_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 57 Primitive.Addresses.material3281
    · exact v3281_mb_checked.trans (by decide +kernel)
    · exact v3281_mg_checked.trans (by decide +kernel)
  upper_error := v3281_upper_checked
  lower_error := reuse_lower_error 43 57 Primitive.Addresses.material3281

def v3282_pa : Scalar.QComplex := ((999999335737864466830958046343 : Int)/10^30,(-1152616080844855027576613821 : Int)/10^30)
theorem v3282_pa_checked : Scalar.distance (sourceCoefficient 43 58 1 0) v3282_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3282_pb : Scalar.QComplex := ((-497327927123899019547216 : Int)/10^30,(-431477232560604549893247187 : Int)/10^30)
theorem v3282_pb_checked : Scalar.distance (sourceCoefficient 43 58 1 1) v3282_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3282_pg : Scalar.QComplex := ((-93086367866230017166554 : Int)/10^30,(107292915780677856709 : Int)/10^30)
theorem v3282_pg_checked : Scalar.distance (sourceCoefficient 43 58 1 2) v3282_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3282_mb : Scalar.QComplex := ((-869673160632617297017013 : Int)/10^30,(-431476642730309094319479581 : Int)/10^30)
theorem v3282_mb_checked : Scalar.distance (sourceCoefficient 43 58 3 1) v3282_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3282_mg : Scalar.QComplex := ((-93086240616966978211666 : Int)/10^30,(187622218844800814888 : Int)/10^30)
theorem v3282_mg_checked : Scalar.distance (sourceCoefficient 43 58 3 2) v3282_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3282_upper : Scalar.QComplex := ((999995857045531034768054192215 : Int)/10^30,(-2878522498411074078820619827 : Int)/10^30)
theorem v3282_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 58 5) 1) 14) v3282_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3282 : Material (43 : Basis) (58 : Basis) where
  plus := ![v3282_pa,v3282_pb,v3282_pg]
  minus := ![(Primitive.Addresses.material3282 1).one,v3282_mb,v3282_mg]
  upper := v3282_upper
  lower := (Primitive.Addresses.material3282 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3282_pa_checked.trans (by decide +kernel)
    · exact v3282_pb_checked.trans (by decide +kernel)
    · exact v3282_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 58 Primitive.Addresses.material3282
    · exact v3282_mb_checked.trans (by decide +kernel)
    · exact v3282_mg_checked.trans (by decide +kernel)
  upper_error := v3282_upper_checked
  lower_error := reuse_lower_error 43 58 Primitive.Addresses.material3282

def v3283_pa : Scalar.QComplex := ((999999315336813713083815800119 : Int)/10^30,(-1170181996020342859490915375 : Int)/10^30)
theorem v3283_pa_checked : Scalar.distance (sourceCoefficient 43 59 1 0) v3283_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3283_pb : Scalar.QComplex := ((-504907224128809304788020 : Int)/10^30,(-431477223333252319964350168 : Int)/10^30)
theorem v3283_pb_checked : Scalar.distance (sourceCoefficient 43 59 1 1) v3283_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3283_pg : Scalar.QComplex := ((-93086365921350714423980 : Int)/10^30,(108928064055161612955 : Int)/10^30)
theorem v3283_pg_checked : Scalar.distance (sourceCoefficient 43 59 1 2) v3283_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3283_mb : Scalar.QComplex := ((-877252446852619526433107 : Int)/10^30,(-431476626962368343783216867 : Int)/10^30)
theorem v3283_mb_checked : Scalar.distance (sourceCoefficient 43 59 3 1) v3283_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3283_mg : Scalar.QComplex := ((-93086237261029083101537 : Int)/10^30,(189257364832100894422 : Int)/10^30)
theorem v3283_mg_checked : Scalar.distance (sourceCoefficient 43 59 3 2) v3283_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3283_upper : Scalar.QComplex := ((999995806327334640473991055511 : Int)/10^30,(-2896088352213831862090275762 : Int)/10^30)
theorem v3283_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 59 5) 1) 14) v3283_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3283 : Material (43 : Basis) (59 : Basis) where
  plus := ![v3283_pa,v3283_pb,v3283_pg]
  minus := ![(Primitive.Addresses.material3283 1).one,v3283_mb,v3283_mg]
  upper := v3283_upper
  lower := (Primitive.Addresses.material3283 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3283_pa_checked.trans (by decide +kernel)
    · exact v3283_pb_checked.trans (by decide +kernel)
    · exact v3283_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 59 Primitive.Addresses.material3283
    · exact v3283_mb_checked.trans (by decide +kernel)
    · exact v3283_mg_checked.trans (by decide +kernel)
  upper_error := v3283_upper_checked
  lower_error := reuse_lower_error 43 59 Primitive.Addresses.material3283

def v3284_pa : Scalar.QComplex := ((999999291419014132979785733017 : Int)/10^30,(-1190445912104799029392896200 : Int)/10^30)
theorem v3284_pa_checked : Scalar.distance (sourceCoefficient 43 60 1 0) v3284_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3284_pb : Scalar.QComplex := ((-513650647712147724579709 : Int)/10^30,(-431477212468135204449986138 : Int)/10^30)
theorem v3284_pb_checked : Scalar.distance (sourceCoefficient 43 60 1 1) v3284_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3284_pg : Scalar.QComplex := ((-93086363636125923805687 : Int)/10^30,(110814359584275084519 : Int)/10^30)
theorem v3284_pg_checked : Scalar.distance (sourceCoefficient 43 60 1 2) v3284_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3284_mb : Scalar.QComplex := ((-885995857804275027970373 : Int)/10^30,(-431476608552074510607511113 : Int)/10^30)
theorem v3284_mb_checked : Scalar.distance (sourceCoefficient 43 60 3 1) v3284_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3284_mg : Scalar.QComplex := ((-93086233348017057348878 : Int)/10^30,(191143657686814260932 : Int)/10^30)
theorem v3284_mg_checked : Scalar.distance (sourceCoefficient 43 60 3 2) v3284_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3284_upper : Scalar.QComplex := ((999995747435889849458454960100 : Int)/10^30,(-2916352196837613121558477289 : Int)/10^30)
theorem v3284_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 60 5) 1) 14) v3284_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3284 : Material (43 : Basis) (60 : Basis) where
  plus := ![v3284_pa,v3284_pb,v3284_pg]
  minus := ![(Primitive.Addresses.material3284 1).one,v3284_mb,v3284_mg]
  upper := v3284_upper
  lower := (Primitive.Addresses.material3284 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3284_pa_checked.trans (by decide +kernel)
    · exact v3284_pb_checked.trans (by decide +kernel)
    · exact v3284_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 60 Primitive.Addresses.material3284
    · exact v3284_mb_checked.trans (by decide +kernel)
    · exact v3284_mg_checked.trans (by decide +kernel)
  upper_error := v3284_upper_checked
  lower_error := reuse_lower_error 43 60 Primitive.Addresses.material3284

def v3285_pa : Scalar.QComplex := ((999999284426626142157232604936 : Int)/10^30,(-1196305243518740145329707364 : Int)/10^30)
theorem v3285_pa_checked : Scalar.distance (sourceCoefficient 43 61 1 0) v3285_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3285_pb : Scalar.QComplex := ((-516178817287241262786583 : Int)/10^30,(-431477209282446413515170903 : Int)/10^30)
theorem v3285_pb_checked : Scalar.distance (sourceCoefficient 43 61 1 1) v3285_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3285_pg : Scalar.QComplex := ((-93086362967039415148587 : Int)/10^30,(111359783803654130444 : Int)/10^30)
theorem v3285_pg_checked : Scalar.distance (sourceCoefficient 43 61 1 2) v3285_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3285_mb : Scalar.QComplex := ((-888524023688909541832639 : Int)/10^30,(-431476603184690427075314585 : Int)/10^30)
theorem v3285_mb_checked : Scalar.distance (sourceCoefficient 43 61 3 1) v3285_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3285_mg : Scalar.QComplex := ((-93086232208254261494093 : Int)/10^30,(191689081125715420431 : Int)/10^30)
theorem v3285_mg_checked : Scalar.distance (sourceCoefficient 43 61 3 2) v3285_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3285_upper : Scalar.QComplex := ((999995730330837806907662148251 : Int)/10^30,(-2922211507456541054170864860 : Int)/10^30)
theorem v3285_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 61 5) 1) 14) v3285_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3285 : Material (43 : Basis) (61 : Basis) where
  plus := ![v3285_pa,v3285_pb,v3285_pg]
  minus := ![(Primitive.Addresses.material3285 1).one,v3285_mb,v3285_mg]
  upper := v3285_upper
  lower := (Primitive.Addresses.material3285 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3285_pa_checked.trans (by decide +kernel)
    · exact v3285_pb_checked.trans (by decide +kernel)
    · exact v3285_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 61 Primitive.Addresses.material3285
    · exact v3285_mb_checked.trans (by decide +kernel)
    · exact v3285_mg_checked.trans (by decide +kernel)
  upper_error := v3285_upper_checked
  lower_error := reuse_lower_error 43 61 Primitive.Addresses.material3285

def v3286_pa : Scalar.QComplex := ((999999274205806403880301740842 : Int)/10^30,(-1204818600626263546348151219 : Int)/10^30)
theorem v3286_pa_checked : Scalar.distance (sourceCoefficient 43 62 1 0) v3286_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3286_pb : Scalar.QComplex := ((-519852139176353958334884 : Int)/10^30,(-431477204618580233806532593 : Int)/10^30)
theorem v3286_pb_checked : Scalar.distance (sourceCoefficient 43 62 1 1) v3286_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3286_pg : Scalar.QComplex := ((-93086361988241227545624 : Int)/10^30,(112152261787523011465 : Int)/10^30)
theorem v3286_pg_checked : Scalar.distance (sourceCoefficient 43 62 1 2) v3286_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3286_mb : Scalar.QComplex := ((-892197340185570158607210 : Int)/10^30,(-431476595350914633909401830 : Int)/10^30)
theorem v3286_mb_checked : Scalar.distance (sourceCoefficient 43 62 3 1) v3286_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3286_mg : Scalar.QComplex := ((-93086230545583630147033 : Int)/10^30,(192481557969849777557 : Int)/10^30)
theorem v3286_mg_checked : Scalar.distance (sourceCoefficient 43 62 3 2) v3286_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3286_upper : Scalar.QComplex := ((999995705416751249479436519119 : Int)/10^30,(-2930724834244211449966261165 : Int)/10^30)
theorem v3286_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 62 5) 1) 14) v3286_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3286 : Material (43 : Basis) (62 : Basis) where
  plus := ![v3286_pa,v3286_pb,v3286_pg]
  minus := ![(Primitive.Addresses.material3286 1).one,v3286_mb,v3286_mg]
  upper := v3286_upper
  lower := (Primitive.Addresses.material3286 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3286_pa_checked.trans (by decide +kernel)
    · exact v3286_pb_checked.trans (by decide +kernel)
    · exact v3286_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 62 Primitive.Addresses.material3286
    · exact v3286_mb_checked.trans (by decide +kernel)
    · exact v3286_mg_checked.trans (by decide +kernel)
  upper_error := v3286_upper_checked
  lower_error := reuse_lower_error 43 62 Primitive.Addresses.material3286

def v3287_pa : Scalar.QComplex := ((999999244024719674797667349648 : Int)/10^30,(-1229613756084316178764897591 : Int)/10^30)
theorem v3287_pa_checked : Scalar.distance (sourceCoefficient 43 63 1 0) v3287_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3287_pb : Scalar.QComplex := ((-530550690324429243366170 : Int)/10^30,(-431477190797499414664894333 : Int)/10^30)
theorem v3287_pb_checked : Scalar.distance (sourceCoefficient 43 63 1 1) v3287_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3287_pg : Scalar.QComplex := ((-93086359092644929454251 : Int)/10^30,(114460354173318902071 : Int)/10^30)
theorem v3287_pg_checked : Scalar.distance (sourceCoefficient 43 63 1 2) v3287_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3287_mb : Scalar.QComplex := ((-902895875423115634721459 : Int)/10^30,(-431476572297471165055623597 : Int)/10^30)
theorem v3287_mb_checked : Scalar.distance (sourceCoefficient 43 63 3 1) v3287_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3287_mg : Scalar.QComplex := ((-93086225658208633898797 : Int)/10^30,(194789646997468195461 : Int)/10^30)
theorem v3287_mg_checked : Scalar.distance (sourceCoefficient 43 63 3 2) v3287_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3287_upper : Scalar.QComplex := ((999995632441520549913136419254 : Int)/10^30,(-2955519900682974983579065398 : Int)/10^30)
theorem v3287_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 63 5) 1) 14) v3287_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3287 : Material (43 : Basis) (63 : Basis) where
  plus := ![v3287_pa,v3287_pb,v3287_pg]
  minus := ![(Primitive.Addresses.material3287 1).one,v3287_mb,v3287_mg]
  upper := v3287_upper
  lower := (Primitive.Addresses.material3287 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3287_pa_checked.trans (by decide +kernel)
    · exact v3287_pb_checked.trans (by decide +kernel)
    · exact v3287_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 63 Primitive.Addresses.material3287
    · exact v3287_mb_checked.trans (by decide +kernel)
    · exact v3287_mg_checked.trans (by decide +kernel)
  upper_error := v3287_upper_checked
  lower_error := reuse_lower_error 43 63 Primitive.Addresses.material3287

def v3288_pa : Scalar.QComplex := ((999999199822663594018145123745 : Int)/10^30,(-1265050999971224089771806279 : Int)/10^30)
theorem v3288_pa_checked : Scalar.distance (sourceCoefficient 43 64 1 0) v3288_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3288_pb : Scalar.QComplex := ((-545841062687406450732107 : Int)/10^30,(-431477170430421348099378160 : Int)/10^30)
theorem v3288_pb_checked : Scalar.distance (sourceCoefficient 43 64 1 1) v3288_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3288_pg : Scalar.QComplex := ((-93086354838354942317819 : Int)/10^30,(117759080500084485719 : Int)/10^30)
theorem v3288_pg_checked : Scalar.distance (sourceCoefficient 43 64 1 2) v3288_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3288_mb : Scalar.QComplex := ((-918186224516917334510682 : Int)/10^30,(-431476538735497985641997743 : Int)/10^30)
theorem v3288_mb_checked : Scalar.distance (sourceCoefficient 43 64 3 1) v3288_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3288_mg : Scalar.QComplex := ((-93086218557267979948872 : Int)/10^30,(198088368424706555623 : Int)/10^30)
theorem v3288_mg_checked : Scalar.distance (sourceCoefficient 43 64 3 2) v3288_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3288_upper : Scalar.QComplex := ((999995527078062195753209323221 : Int)/10^30,(-2990957015501532059898866084 : Int)/10^30)
theorem v3288_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 64 5) 1) 14) v3288_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3288 : Material (43 : Basis) (64 : Basis) where
  plus := ![v3288_pa,v3288_pb,v3288_pg]
  minus := ![(Primitive.Addresses.material3288 1).one,v3288_mb,v3288_mg]
  upper := v3288_upper
  lower := (Primitive.Addresses.material3288 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3288_pa_checked.trans (by decide +kernel)
    · exact v3288_pb_checked.trans (by decide +kernel)
    · exact v3288_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 64 Primitive.Addresses.material3288
    · exact v3288_mb_checked.trans (by decide +kernel)
    · exact v3288_mg_checked.trans (by decide +kernel)
  upper_error := v3288_upper_checked
  lower_error := reuse_lower_error 43 64 Primitive.Addresses.material3288

def v3289_pa : Scalar.QComplex := ((999999153676258111326877801513 : Int)/10^30,(-1301017589240618283790809019 : Int)/10^30)
theorem v3289_pa_checked : Scalar.distance (sourceCoefficient 43 65 1 0) v3289_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3289_pb : Scalar.QComplex := ((-561359835323058905128007 : Int)/10^30,(-431477149020374418178000483 : Int)/10^30)
theorem v3289_pb_checked : Scalar.distance (sourceCoefficient 43 65 1 1) v3289_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3289_pg : Scalar.QComplex := ((-93086350381064272939107 : Int)/10^30,(121107081659778269027 : Int)/10^30)
theorem v3289_pg_checked : Scalar.distance (sourceCoefficient 43 65 1 2) v3289_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3289_mb : Scalar.QComplex := ((-933704972898315265902500 : Int)/10^30,(-431476503933457182665164632 : Int)/10^30)
theorem v3289_mb_checked : Scalar.distance (sourceCoefficient 43 65 3 1) v3289_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3289_mg : Scalar.QComplex := ((-93086211210804757782154 : Int)/10^30,(201436364491345397211 : Int)/10^30)
theorem v3289_mg_checked : Scalar.distance (sourceCoefficient 43 65 3 2) v3289_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3289_upper : Scalar.QComplex := ((999995418856655227228220618264 : Int)/10^30,(-3026923471558406975594251893 : Int)/10^30)
theorem v3289_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 65 5) 1) 14) v3289_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3289 : Material (43 : Basis) (65 : Basis) where
  plus := ![v3289_pa,v3289_pb,v3289_pg]
  minus := ![(Primitive.Addresses.material3289 1).one,v3289_mb,v3289_mg]
  upper := v3289_upper
  lower := (Primitive.Addresses.material3289 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3289_pa_checked.trans (by decide +kernel)
    · exact v3289_pb_checked.trans (by decide +kernel)
    · exact v3289_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 65 Primitive.Addresses.material3289
    · exact v3289_mb_checked.trans (by decide +kernel)
    · exact v3289_mg_checked.trans (by decide +kernel)
  upper_error := v3289_upper_checked
  lower_error := reuse_lower_error 43 65 Primitive.Addresses.material3289

def v3290_pa : Scalar.QComplex := ((999999130639863601017333665163 : Int)/10^30,(-1318605140673628108471559975 : Int)/10^30)
theorem v3290_pa_checked : Scalar.distance (sourceCoefficient 43 66 1 0) v3290_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3290_pb : Scalar.QComplex := ((-568948467240260015798729 : Int)/10^30,(-431477138279991691300314877 : Int)/10^30)
theorem v3290_pb_checked : Scalar.distance (sourceCoefficient 43 66 1 1) v3290_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3290_pg : Scalar.QComplex := ((-93086348150317929802014 : Int)/10^30,(122744243906496920242 : Int)/10^30)
theorem v3290_pg_checked : Scalar.distance (sourceCoefficient 43 66 1 2) v3290_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3290_mb : Scalar.QComplex := ((-941293592721455331773211 : Int)/10^30,(-431476486644430889672376436 : Int)/10^30)
theorem v3290_mb_checked : Scalar.distance (sourceCoefficient 43 66 3 1) v3290_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3290_mg : Scalar.QComplex := ((-93086207567261961386097 : Int)/10^30,(203073524203440096920 : Int)/10^30)
theorem v3290_mg_checked : Scalar.distance (sourceCoefficient 43 66 3 2) v3290_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3290_upper : Scalar.QComplex := ((999995365465776783749701892844 : Int)/10^30,(-3044510957038097840316019736 : Int)/10^30)
theorem v3290_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 66 5) 1) 14) v3290_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3290 : Material (43 : Basis) (66 : Basis) where
  plus := ![v3290_pa,v3290_pb,v3290_pg]
  minus := ![(Primitive.Addresses.material3290 1).one,v3290_mb,v3290_mg]
  upper := v3290_upper
  lower := (Primitive.Addresses.material3290 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3290_pa_checked.trans (by decide +kernel)
    · exact v3290_pb_checked.trans (by decide +kernel)
    · exact v3290_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 66 Primitive.Addresses.material3290
    · exact v3290_mb_checked.trans (by decide +kernel)
    · exact v3290_mg_checked.trans (by decide +kernel)
  upper_error := v3290_upper_checked
  lower_error := reuse_lower_error 43 66 Primitive.Addresses.material3290

def v3291_pa : Scalar.QComplex := ((999999091282760447858542654277 : Int)/10^30,(-1348122269431545832672974937 : Int)/10^30)
theorem v3291_pa_checked : Scalar.distance (sourceCoefficient 43 67 1 0) v3291_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3291_pb : Scalar.QComplex := ((-581684442612707214276888 : Int)/10^30,(-431477119854493019923997285 : Int)/10^30)
theorem v3291_pb_checked : Scalar.distance (sourceCoefficient 43 67 1 1) v3291_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3291_pg : Scalar.QComplex := ((-93086344330964603854490 : Int)/10^30,(125491887809188188834 : Int)/10^30)
theorem v3291_pg_checked : Scalar.distance (sourceCoefficient 43 67 1 2) v3291_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3291_mb : Scalar.QComplex := ((-954029547451341336517050 : Int)/10^30,(-431476457228365939566849690 : Int)/10^30)
theorem v3291_mb_checked : Scalar.distance (sourceCoefficient 43 67 3 1) v3291_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3291_mg : Scalar.QComplex := ((-93086201376817118823392 : Int)/10^30,(205821163787128064006 : Int)/10^30)
theorem v3291_mg_checked : Scalar.distance (sourceCoefficient 43 67 3 2) v3291_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3291_upper : Scalar.QComplex := ((999995275164845785210158960348 : Int)/10^30,(-3074027973906930011264390285 : Int)/10^30)
theorem v3291_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 67 5) 1) 14) v3291_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3291 : Material (43 : Basis) (67 : Basis) where
  plus := ![v3291_pa,v3291_pb,v3291_pg]
  minus := ![(Primitive.Addresses.material3291 1).one,v3291_mb,v3291_mg]
  upper := v3291_upper
  lower := (Primitive.Addresses.material3291 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3291_pa_checked.trans (by decide +kernel)
    · exact v3291_pb_checked.trans (by decide +kernel)
    · exact v3291_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 67 Primitive.Addresses.material3291
    · exact v3291_mb_checked.trans (by decide +kernel)
    · exact v3291_mg_checked.trans (by decide +kernel)
  upper_error := v3291_upper_checked
  lower_error := reuse_lower_error 43 67 Primitive.Addresses.material3291

def v3292_pa : Scalar.QComplex := ((999999023803536231342444857305 : Int)/10^30,(-1397280206178338173575201351 : Int)/10^30)
theorem v3292_pa_checked : Scalar.distance (sourceCoefficient 43 68 1 0) v3292_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3292_pb : Scalar.QComplex := ((-602894983104209933599697 : Int)/10^30,(-431477088056102161359855475 : Int)/10^30)
theorem v3292_pb_checked : Scalar.distance (sourceCoefficient 43 68 1 1) v3292_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3292_pg : Scalar.QComplex := ((-93086337760191693374760 : Int)/10^30,(130067824189697099445 : Int)/10^30)
theorem v3292_pg_checked : Scalar.distance (sourceCoefficient 43 68 1 2) v3292_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3292_mb : Scalar.QComplex := ((-975240052604611296684750 : Int)/10^30,(-431476407126245764111842482 : Int)/10^30)
theorem v3292_mb_checked : Scalar.distance (sourceCoefficient 43 68 3 1) v3292_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3292_mg : Scalar.QComplex := ((-93086190857219651087591 : Int)/10^30,(210397092793525644412 : Int)/10^30)
theorem v3292_mg_checked : Scalar.distance (sourceCoefficient 43 68 3 2) v3292_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3292_upper : Scalar.QComplex := ((999995122843582819293679807969 : Int)/10^30,(-3123185720975730734400281511 : Int)/10^30)
theorem v3292_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 68 5) 1) 14) v3292_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3292 : Material (43 : Basis) (68 : Basis) where
  plus := ![v3292_pa,v3292_pb,v3292_pg]
  minus := ![(Primitive.Addresses.material3292 1).one,v3292_mb,v3292_mg]
  upper := v3292_upper
  lower := (Primitive.Addresses.material3292 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3292_pa_checked.trans (by decide +kernel)
    · exact v3292_pb_checked.trans (by decide +kernel)
    · exact v3292_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 68 Primitive.Addresses.material3292
    · exact v3292_mb_checked.trans (by decide +kernel)
    · exact v3292_mg_checked.trans (by decide +kernel)
  upper_error := v3292_upper_checked
  lower_error := reuse_lower_error 43 68 Primitive.Addresses.material3292

def v3293_pa : Scalar.QComplex := ((999998993338792378538588502888 : Int)/10^30,(-1418915572497580242514809508 : Int)/10^30)
theorem v3293_pa_checked : Scalar.distance (sourceCoefficient 43 69 1 0) v3293_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3293_pb : Scalar.QComplex := ((-612230155244061688819455 : Int)/10^30,(-431477073620430886092132330 : Int)/10^30)
theorem v3293_pb_checked : Scalar.distance (sourceCoefficient 43 69 1 1) v3293_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3293_pg : Scalar.QComplex := ((-93086334785097585946226 : Int)/10^30,(132081782974905313590 : Int)/10^30)
theorem v3293_pg_checked : Scalar.distance (sourceCoefficient 43 69 1 2) v3293_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3293_mb : Scalar.QComplex := ((-984575208811217673737716 : Int)/10^30,(-431476384634746747757905365 : Int)/10^30)
theorem v3293_mb_checked : Scalar.distance (sourceCoefficient 43 69 3 1) v3293_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3293_mg : Scalar.QComplex := ((-93086186144170925124418 : Int)/10^30,(212411048261472738914 : Int)/10^30)
theorem v3293_mg_checked : Scalar.distance (sourceCoefficient 43 69 3 2) v3293_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3293_upper : Scalar.QComplex := ((999995055038204818235699335176 : Int)/10^30,(-3144821002492251989518840460 : Int)/10^30)
theorem v3293_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 69 5) 1) 14) v3293_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3293 : Material (43 : Basis) (69 : Basis) where
  plus := ![v3293_pa,v3293_pb,v3293_pg]
  minus := ![(Primitive.Addresses.material3293 1).one,v3293_mb,v3293_mg]
  upper := v3293_upper
  lower := (Primitive.Addresses.material3293 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3293_pa_checked.trans (by decide +kernel)
    · exact v3293_pb_checked.trans (by decide +kernel)
    · exact v3293_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 69 Primitive.Addresses.material3293
    · exact v3293_mb_checked.trans (by decide +kernel)
    · exact v3293_mg_checked.trans (by decide +kernel)
  upper_error := v3293_upper_checked
  lower_error := reuse_lower_error 43 69 Primitive.Addresses.material3293

def v3294_pa : Scalar.QComplex := ((999998973043559632651468372301 : Int)/10^30,(-1433147524191130384719342375 : Int)/10^30)
theorem v3294_pa_checked : Scalar.distance (sourceCoefficient 43 70 1 0) v3294_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3294_pb : Scalar.QComplex := ((-618370921024858683529460 : Int)/10^30,(-431477063977672143629339698 : Int)/10^30)
theorem v3294_pb_checked : Scalar.distance (sourceCoefficient 43 70 1 1) v3294_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3294_pg : Scalar.QComplex := ((-93086332800333748253989 : Int)/10^30,(133406584391580952628 : Int)/10^30)
theorem v3294_pg_checked : Scalar.distance (sourceCoefficient 43 70 1 2) v3294_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3294_mb : Scalar.QComplex := ((-990715963984260420383211 : Int)/10^30,(-431476369692787296731094599 : Int)/10^30)
theorem v3294_mb_checked : Scalar.distance (sourceCoefficient 43 70 3 1) v3294_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3294_mg : Scalar.QComplex := ((-93086183016163870700259 : Int)/10^30,(213735847472102462625 : Int)/10^30)
theorem v3294_mg_checked : Scalar.distance (sourceCoefficient 43 70 3 2) v3294_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3294_upper : Scalar.QComplex := ((999995010179944789218184188795 : Int)/10^30,(-3159052897961251336395193718 : Int)/10^30)
theorem v3294_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 70 5) 1) 14) v3294_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3294 : Material (43 : Basis) (70 : Basis) where
  plus := ![v3294_pa,v3294_pb,v3294_pg]
  minus := ![(Primitive.Addresses.material3294 1).one,v3294_mb,v3294_mg]
  upper := v3294_upper
  lower := (Primitive.Addresses.material3294 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3294_pa_checked.trans (by decide +kernel)
    · exact v3294_pb_checked.trans (by decide +kernel)
    · exact v3294_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 70 Primitive.Addresses.material3294
    · exact v3294_mb_checked.trans (by decide +kernel)
    · exact v3294_mg_checked.trans (by decide +kernel)
  upper_error := v3294_upper_checked
  lower_error := reuse_lower_error 43 70 Primitive.Addresses.material3294

def v3295_pa : Scalar.QComplex := ((999998937933299638999763191783 : Int)/10^30,(-1457440315325579450163546293 : Int)/10^30)
theorem v3295_pa_checked : Scalar.distance (sourceCoefficient 43 71 1 0) v3295_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3295_pb : Scalar.QComplex := ((-628852711681938897352028 : Int)/10^30,(-431477047249056184126632960 : Int)/10^30)
theorem v3295_pb_checked : Scalar.distance (sourceCoefficient 43 71 1 1) v3295_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3295_pg : Scalar.QComplex := ((-93086329361683850914830 : Int)/10^30,(135667913305766286056 : Int)/10^30)
theorem v3295_pg_checked : Scalar.distance (sourceCoefficient 43 71 1 2) v3295_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3295_mb : Scalar.QComplex := ((-1001197736302448786920042 : Int)/10^30,(-431476343918864311323095752 : Int)/10^30)
theorem v3295_mb_checked : Scalar.distance (sourceCoefficient 43 71 3 1) v3295_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3295_mg : Scalar.QComplex := ((-93086177626090247259244 : Int)/10^30,(215997172576891703103 : Int)/10^30)
theorem v3295_mg_checked : Scalar.distance (sourceCoefficient 43 71 3 2) v3295_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3295_upper : Scalar.QComplex := ((999994933142583414911694397539 : Int)/10^30,(-3183345592317318067643397585 : Int)/10^30)
theorem v3295_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 71 5) 1) 14) v3295_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3295 : Material (43 : Basis) (71 : Basis) where
  plus := ![v3295_pa,v3295_pb,v3295_pg]
  minus := ![(Primitive.Addresses.material3295 1).one,v3295_mb,v3295_mg]
  upper := v3295_upper
  lower := (Primitive.Addresses.material3295 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3295_pa_checked.trans (by decide +kernel)
    · exact v3295_pb_checked.trans (by decide +kernel)
    · exact v3295_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 71 Primitive.Addresses.material3295
    · exact v3295_mb_checked.trans (by decide +kernel)
    · exact v3295_mg_checked.trans (by decide +kernel)
  upper_error := v3295_upper_checked
  lower_error := reuse_lower_error 43 71 Primitive.Addresses.material3295

def v3296_pa : Scalar.QComplex := ((999998899163851781732019332024 : Int)/10^30,(-1483802912989562349748323079 : Int)/10^30)
theorem v3296_pa_checked : Scalar.distance (sourceCoefficient 43 72 1 0) v3296_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3296_pb : Scalar.QComplex := ((-640227576875103453533124 : Int)/10^30,(-431477028710987137377657374 : Int)/10^30)
theorem v3296_pb_checked : Scalar.distance (sourceCoefficient 43 72 1 1) v3296_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3296_pg : Scalar.QComplex := ((-93086325557538994013626 : Int)/10^30,(138121913071365875940 : Int)/10^30)
theorem v3296_pg_checked : Scalar.distance (sourceCoefficient 43 72 1 2) v3296_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3296_mb : Scalar.QComplex := ((-1012572581262712510956865 : Int)/10^30,(-431476315564805810354093811 : Int)/10^30)
theorem v3296_mb_checked : Scalar.distance (sourceCoefficient 43 72 3 1) v3296_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3296_mg : Scalar.QComplex := ((-93086171704255533149179 : Int)/10^30,(218451168145949347743 : Int)/10^30)
theorem v3296_mg_checked : Scalar.distance (sourceCoefficient 43 72 3 2) v3296_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3296_upper : Scalar.QComplex := ((999994848873741328325822427201 : Int)/10^30,(-3209708083804758650174482454 : Int)/10^30)
theorem v3296_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 72 5) 1) 14) v3296_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3296 : Material (43 : Basis) (72 : Basis) where
  plus := ![v3296_pa,v3296_pb,v3296_pg]
  minus := ![(Primitive.Addresses.material3296 1).one,v3296_mb,v3296_mg]
  upper := v3296_upper
  lower := (Primitive.Addresses.material3296 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3296_pa_checked.trans (by decide +kernel)
    · exact v3296_pb_checked.trans (by decide +kernel)
    · exact v3296_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 72 Primitive.Addresses.material3296
    · exact v3296_mb_checked.trans (by decide +kernel)
    · exact v3296_mg_checked.trans (by decide +kernel)
  upper_error := v3296_upper_checked
  lower_error := reuse_lower_error 43 72 Primitive.Addresses.material3296

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
