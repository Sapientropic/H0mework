import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B096

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2305_pa : Scalar.QComplex := ((999999437197855168748873066540 : Int)/10^30,(-1060944849139788239921417903 : Int)/10^30)
theorem v2305_pa_checked : Scalar.distance (sourceCoefficient 27 65 1 0) v2305_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2305_pb : Scalar.QComplex := ((-457773830528664096353398 : Int)/10^30,(-431477256582877269749331367 : Int)/10^30)
theorem v2305_pb_checked : Scalar.distance (sourceCoefficient 27 65 1 1) v2305_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2305_pg : Scalar.QComplex := ((-93086375179771972451029 : Int)/10^30,(98759565854168389043 : Int)/10^30)
theorem v2305_pg_checked : Scalar.distance (sourceCoefficient 27 65 1 2) v2305_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2305_mb : Scalar.QComplex := ((-830119099495319681981689 : Int)/10^30,(-431476700885976780893193998 : Int)/10^30)
theorem v2305_mb_checked : Scalar.distance (sourceCoefficient 27 65 3 1) v2305_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2305_mg : Scalar.QComplex := ((-93086255294402869094125 : Int)/10^30,(179088878406904835927 : Int)/10^30)
theorem v2305_mg_checked : Scalar.distance (sourceCoefficient 27 65 3 2) v2305_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2305_upper : Scalar.QComplex := ((999996116721600197716892924979 : Int)/10^30,(-2786851578350278029597819372 : Int)/10^30)
theorem v2305_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 65 5) 1) 14) v2305_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2305 : Material (27 : Basis) (65 : Basis) where
  plus := ![v2305_pa,v2305_pb,v2305_pg]
  minus := ![(Primitive.Addresses.material2305 1).one,v2305_mb,v2305_mg]
  upper := v2305_upper
  lower := (Primitive.Addresses.material2305 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2305_pa_checked.trans (by decide +kernel)
    · exact v2305_pb_checked.trans (by decide +kernel)
    · exact v2305_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 65 Primitive.Addresses.material2305
    · exact v2305_mb_checked.trans (by decide +kernel)
    · exact v2305_mg_checked.trans (by decide +kernel)
  upper_error := v2305_upper_checked
  lower_error := reuse_lower_error 27 65 Primitive.Addresses.material2305

def v2306_pa : Scalar.QComplex := ((999999418383755900511936787302 : Int)/10^30,(-1078532405596382962028127355 : Int)/10^30)
theorem v2306_pa_checked : Scalar.distance (sourceCoefficient 27 66 1 0) v2306_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2306_pb : Scalar.QComplex := ((-465362463890907809041723 : Int)/10^30,(-431477247057044834253880568 : Int)/10^30)
theorem v2306_pb_checked : Scalar.distance (sourceCoefficient 27 66 1 1) v2306_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2306_pg : Scalar.QComplex := ((-93086373276557616983124 : Int)/10^30,(100396728490576688350 : Int)/10^30)
theorem v2306_pg_checked : Scalar.distance (sourceCoefficient 27 66 1 2) v2306_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2306_mb : Scalar.QComplex := ((-837707721811604011962952 : Int)/10^30,(-431476684811499080043376198 : Int)/10^30)
theorem v2306_mb_checked : Scalar.distance (sourceCoefficient 27 66 3 1) v2306_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2306_mg : Scalar.QComplex := ((-93086251978391602127514 : Int)/10^30,(180726038791334392495 : Int)/10^30)
theorem v2306_mg_checked : Scalar.distance (sourceCoefficient 27 66 3 2) v2306_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2306_upper : Scalar.QComplex := ((999996067553002037446407734422 : Int)/10^30,(-2804439076140844853891085714 : Int)/10^30)
theorem v2306_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 66 5) 1) 14) v2306_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2306 : Material (27 : Basis) (66 : Basis) where
  plus := ![v2306_pa,v2306_pb,v2306_pg]
  minus := ![(Primitive.Addresses.material2306 1).one,v2306_mb,v2306_mg]
  upper := v2306_upper
  lower := (Primitive.Addresses.material2306 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2306_pa_checked.trans (by decide +kernel)
    · exact v2306_pb_checked.trans (by decide +kernel)
    · exact v2306_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 66 Primitive.Addresses.material2306
    · exact v2306_mb_checked.trans (by decide +kernel)
    · exact v2306_mg_checked.trans (by decide +kernel)
  upper_error := v2306_upper_checked
  lower_error := reuse_lower_error 27 66 Primitive.Addresses.material2306

def v2307_pa : Scalar.QComplex := ((999999386112916752962907010572 : Int)/10^30,(-1108049542952264931994077736 : Int)/10^30)
theorem v2307_pa_checked : Scalar.distance (sourceCoefficient 27 67 1 0) v2307_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2307_pb : Scalar.QComplex := ((-478098441736573805100858 : Int)/10^30,(-431477230669921856942724165 : Int)/10^30)
theorem v2307_pb_checked : Scalar.distance (sourceCoefficient 27 67 1 1) v2307_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2307_pg : Scalar.QComplex := ((-93086370006900131542268 : Int)/10^30,(103144373060229444688 : Int)/10^30)
theorem v2307_pg_checked : Scalar.distance (sourceCoefficient 27 67 1 2) v2307_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2307_mb : Scalar.QComplex := ((-850443680773734312340315 : Int)/10^30,(-431476657433806930746148697 : Int)/10^30)
theorem v2307_mb_checked : Scalar.distance (sourceCoefficient 27 67 3 1) v2307_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2307_mg : Scalar.QComplex := ((-93086246337641819836868 : Int)/10^30,(183473679516346351962 : Int)/10^30)
theorem v2307_mg_checked : Scalar.distance (sourceCoefficient 27 67 3 2) v2307_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2307_upper : Scalar.QComplex := ((999995984338309651052513757880 : Int)/10^30,(-2833956113837877277779847783 : Int)/10^30)
theorem v2307_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 67 5) 1) 14) v2307_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2307 : Material (27 : Basis) (67 : Basis) where
  plus := ![v2307_pa,v2307_pb,v2307_pg]
  minus := ![(Primitive.Addresses.material2307 1).one,v2307_mb,v2307_mg]
  upper := v2307_upper
  lower := (Primitive.Addresses.material2307 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2307_pa_checked.trans (by decide +kernel)
    · exact v2307_pb_checked.trans (by decide +kernel)
    · exact v2307_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 67 Primitive.Addresses.material2307
    · exact v2307_mb_checked.trans (by decide +kernel)
    · exact v2307_mg_checked.trans (by decide +kernel)
  upper_error := v2307_upper_checked
  lower_error := reuse_lower_error 27 67 Primitive.Addresses.material2307

def v2308_pa : Scalar.QComplex := ((999999330435183198382145461299 : Int)/10^30,(-1157207494482381845973696645 : Int)/10^30)
theorem v2308_pa_checked : Scalar.distance (sourceCoefficient 27 68 1 0) v2308_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2308_pb : Scalar.QComplex := ((-499308986480524550675846 : Int)/10^30,(-431477202266249514209574700 : Int)/10^30)
theorem v2308_pb_checked : Scalar.distance (sourceCoefficient 27 68 1 1) v2308_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2308_pg : Scalar.QComplex := ((-93086364351592734168695 : Int)/10^30,(107720310587510759427 : Int)/10^30)
theorem v2308_pg_checked : Scalar.distance (sourceCoefficient 27 68 1 2) v2308_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2308_mb : Scalar.QComplex := ((-871654193108939902095274 : Int)/10^30,(-431476610726400337442160583 : Int)/10^30)
theorem v2308_mb_checked : Scalar.distance (sourceCoefficient 27 68 3 1) v2308_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2308_mg : Scalar.QComplex := ((-93086236733508534724638 : Int)/10^30,(188049610459521416274 : Int)/10^30)
theorem v2308_mg_checked : Scalar.distance (sourceCoefficient 27 68 3 2) v2308_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2308_upper : Scalar.QComplex := ((999995843818494255460249973300 : Int)/10^30,(-2883113896058282815598537682 : Int)/10^30)
theorem v2308_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 68 5) 1) 14) v2308_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2308 : Material (27 : Basis) (68 : Basis) where
  plus := ![v2308_pa,v2308_pb,v2308_pg]
  minus := ![(Primitive.Addresses.material2308 1).one,v2308_mb,v2308_mg]
  upper := v2308_upper
  lower := (Primitive.Addresses.material2308 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2308_pa_checked.trans (by decide +kernel)
    · exact v2308_pb_checked.trans (by decide +kernel)
    · exact v2308_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 68 Primitive.Addresses.material2308
    · exact v2308_mb_checked.trans (by decide +kernel)
    · exact v2308_mg_checked.trans (by decide +kernel)
  upper_error := v2308_upper_checked
  lower_error := reuse_lower_error 27 68 Primitive.Addresses.material2308

def v2309_pa : Scalar.QComplex := ((999999305164505483547682569935 : Int)/10^30,(-1178842867491906316847281634 : Int)/10^30)
theorem v2309_pa_checked : Scalar.distance (sourceCoefficient 27 69 1 0) v2309_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2309_pb : Scalar.QComplex := ((-508644160544847215781684 : Int)/10^30,(-431477189324660040287365781 : Int)/10^30)
theorem v2309_pb_checked : Scalar.distance (sourceCoefficient 27 69 1 1) v2309_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2309_pg : Scalar.QComplex := ((-93086361779412847317507 : Int)/10^30,(109734269891697717480 : Int)/10^30)
theorem v2309_pg_checked : Scalar.distance (sourceCoefficient 27 69 1 2) v2309_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2309_mb : Scalar.QComplex := ((-880989352529341776080652 : Int)/10^30,(-431476589728980905387079859 : Int)/10^30)
theorem v2309_mb_checked : Scalar.distance (sourceCoefficient 27 69 3 1) v2309_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2309_mg : Scalar.QComplex := ((-93086232423373431460150 : Int)/10^30,(190063566794143887220 : Int)/10^30)
theorem v2309_mg_checked : Scalar.distance (sourceCoefficient 27 69 3 2) v2309_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2309_upper : Scalar.QComplex := ((999995781207163109599800266885 : Int)/10^30,(-2904749193229563460397296113 : Int)/10^30)
theorem v2309_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 69 5) 1) 14) v2309_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2309 : Material (27 : Basis) (69 : Basis) where
  plus := ![v2309_pa,v2309_pb,v2309_pg]
  minus := ![(Primitive.Addresses.material2309 1).one,v2309_mb,v2309_mg]
  upper := v2309_upper
  lower := (Primitive.Addresses.material2309 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2309_pa_checked.trans (by decide +kernel)
    · exact v2309_pb_checked.trans (by decide +kernel)
    · exact v2309_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 69 Primitive.Addresses.material2309
    · exact v2309_mb_checked.trans (by decide +kernel)
    · exact v2309_mg_checked.trans (by decide +kernel)
  upper_error := v2309_upper_checked
  lower_error := reuse_lower_error 27 69 Primitive.Addresses.material2309

def v2310_pa : Scalar.QComplex := ((999999288285979320625678009739 : Int)/10^30,(-1193074823647662683499690099 : Int)/10^30)
theorem v2310_pa_checked : Scalar.distance (sourceCoefficient 27 70 1 0) v2310_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2310_pb : Scalar.QComplex := ((-514784927609205283149950 : Int)/10^30,(-431477180664722652154745220 : Int)/10^30)
theorem v2310_pb_checked : Scalar.distance (sourceCoefficient 27 70 1 1) v2310_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2310_pg : Scalar.QComplex := ((-93086360059689852702744 : Int)/10^30,(111059071654515722356 : Int)/10^30)
theorem v2310_pg_checked : Scalar.distance (sourceCoefficient 27 70 1 2) v2310_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2310_mb : Scalar.QComplex := ((-887130109834075681612278 : Int)/10^30,(-431476575769841335085737532 : Int)/10^30)
theorem v2310_mb_checked : Scalar.distance (sourceCoefficient 27 70 3 1) v2310_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2310_mg : Scalar.QComplex := ((-93086229560406822721375 : Int)/10^30,(191388366579634158464 : Int)/10^30)
theorem v2310_mg_checked : Scalar.distance (sourceCoefficient 27 70 3 2) v2310_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2310_upper : Scalar.QComplex := ((999995739765596873401164702670 : Int)/10^30,(-2918981099057687986787388115 : Int)/10^30)
theorem v2310_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 70 5) 1) 14) v2310_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2310 : Material (27 : Basis) (70 : Basis) where
  plus := ![v2310_pa,v2310_pb,v2310_pg]
  minus := ![(Primitive.Addresses.material2310 1).one,v2310_mb,v2310_mg]
  upper := v2310_upper
  lower := (Primitive.Addresses.material2310 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2310_pa_checked.trans (by decide +kernel)
    · exact v2310_pb_checked.trans (by decide +kernel)
    · exact v2310_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 70 Primitive.Addresses.material2310
    · exact v2310_mb_checked.trans (by decide +kernel)
    · exact v2310_mg_checked.trans (by decide +kernel)
  upper_error := v2310_upper_checked
  lower_error := reuse_lower_error 27 70 Primitive.Addresses.material2310

def v2311_pa : Scalar.QComplex := ((999999259007761296115824356515 : Int)/10^30,(-1217367622511076368857009875 : Int)/10^30)
theorem v2311_pa_checked : Scalar.distance (sourceCoefficient 27 71 1 0) v2311_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2311_pb : Scalar.QComplex := ((-525266720489535072988145 : Int)/10^30,(-431477165613703300672799719 : Int)/10^30)
theorem v2311_pb_checked : Scalar.distance (sourceCoefficient 27 71 1 1) v2311_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2311_pg : Scalar.QComplex := ((-93086357073443250998832 : Int)/10^30,(113320401168252479669 : Int)/10^30)
theorem v2311_pg_checked : Scalar.distance (sourceCoefficient 27 71 1 2) v2311_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2311_mb : Scalar.QComplex := ((-897611885823203112922779 : Int)/10^30,(-431476551673512414488360147 : Int)/10^30)
theorem v2311_mb_checked : Scalar.distance (sourceCoefficient 27 71 3 1) v2311_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2311_mg : Scalar.QComplex := ((-93086224622735809079308 : Int)/10^30,(193649692674378268232 : Int)/10^30)
theorem v2311_mg_checked : Scalar.distance (sourceCoefficient 27 71 3 2) v2311_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2311_upper : Scalar.QComplex := ((999995668560255442603325398916 : Int)/10^30,(-2943273811208283186588145737 : Int)/10^30)
theorem v2311_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 71 5) 1) 14) v2311_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2311 : Material (27 : Basis) (71 : Basis) where
  plus := ![v2311_pa,v2311_pb,v2311_pg]
  minus := ![(Primitive.Addresses.material2311 1).one,v2311_mb,v2311_mg]
  upper := v2311_upper
  lower := (Primitive.Addresses.material2311 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2311_pa_checked.trans (by decide +kernel)
    · exact v2311_pb_checked.trans (by decide +kernel)
    · exact v2311_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 71 Primitive.Addresses.material2311
    · exact v2311_mb_checked.trans (by decide +kernel)
    · exact v2311_mg_checked.trans (by decide +kernel)
  upper_error := v2311_upper_checked
  lower_error := reuse_lower_error 27 71 Primitive.Addresses.material2311

def v2312_pa : Scalar.QComplex := ((999999226567259981403064233937 : Int)/10^30,(-1243730228722849100976846853 : Int)/10^30)
theorem v2312_pa_checked : Scalar.distance (sourceCoefficient 27 72 1 0) v2312_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2312_pb : Scalar.QComplex := ((-536641588141485637319069 : Int)/10^30,(-431477148896166286590236749 : Int)/10^30)
theorem v2312_pb_checked : Scalar.distance (sourceCoefficient 27 72 1 1) v2312_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2312_pg : Scalar.QComplex := ((-93086353760247582016892 : Int)/10^30,(115774401596921420767 : Int)/10^30)
theorem v2312_pg_checked : Scalar.distance (sourceCoefficient 27 72 1 2) v2312_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2312_mb : Scalar.QComplex := ((-908986734813289080063140 : Int)/10^30,(-431476525139983146496907214 : Int)/10^30)
theorem v2312_mb_checked : Scalar.distance (sourceCoefficient 27 72 3 1) v2312_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2312_mg : Scalar.QComplex := ((-93086219191849527886700 : Int)/10^30,(196103689330172054839 : Int)/10^30)
theorem v2312_mg_checked : Scalar.distance (sourceCoefficient 27 72 3 2) v2312_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2312_upper : Scalar.QComplex := ((999995590620335719640210796149 : Int)/10^30,(-2969636322166688445630063116 : Int)/10^30)
theorem v2312_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 72 5) 1) 14) v2312_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2312 : Material (27 : Basis) (72 : Basis) where
  plus := ![v2312_pa,v2312_pb,v2312_pg]
  minus := ![(Primitive.Addresses.material2312 1).one,v2312_mb,v2312_mg]
  upper := v2312_upper
  lower := (Primitive.Addresses.material2312 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2312_pa_checked.trans (by decide +kernel)
    · exact v2312_pb_checked.trans (by decide +kernel)
    · exact v2312_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 72 Primitive.Addresses.material2312
    · exact v2312_mb_checked.trans (by decide +kernel)
    · exact v2312_mg_checked.trans (by decide +kernel)
  upper_error := v2312_upper_checked
  lower_error := reuse_lower_error 27 72 Primitive.Addresses.material2312

def v2313_pa : Scalar.QComplex := ((999999214769805953348506992279 : Int)/10^30,(-1253179863988743374619590114 : Int)/10^30)
theorem v2313_pa_checked : Scalar.distance (sourceCoefficient 27 73 1 0) v2313_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2313_pb : Scalar.QComplex := ((-540718891725233856553840 : Int)/10^30,(-431477142806445985964950295 : Int)/10^30)
theorem v2313_pb_checked : Scalar.distance (sourceCoefficient 27 73 1 1) v2313_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2313_pg : Scalar.QComplex := ((-93086352554261757105407 : Int)/10^30,(116654034233427900630 : Int)/10^30)
theorem v2313_pg_checked : Scalar.distance (sourceCoefficient 27 73 1 2) v2313_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2313_mb : Scalar.QComplex := ((-913064031623716484470498 : Int)/10^30,(-431476515531735755514652196 : Int)/10^30)
theorem v2313_mb_checked : Scalar.distance (sourceCoefficient 27 73 3 1) v2313_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2313_mg : Scalar.QComplex := ((-93086217226780803897051 : Int)/10^30,(196983320598439651620 : Int)/10^30)
theorem v2313_mg_checked : Scalar.distance (sourceCoefficient 27 73 3 2) v2313_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2313_upper : Scalar.QComplex := ((999995562513686057788827115768 : Int)/10^30,(-2979085922997125627103995246 : Int)/10^30)
theorem v2313_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 73 5) 1) 14) v2313_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2313 : Material (27 : Basis) (73 : Basis) where
  plus := ![v2313_pa,v2313_pb,v2313_pg]
  minus := ![(Primitive.Addresses.material2313 1).one,v2313_mb,v2313_mg]
  upper := v2313_upper
  lower := (Primitive.Addresses.material2313 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2313_pa_checked.trans (by decide +kernel)
    · exact v2313_pb_checked.trans (by decide +kernel)
    · exact v2313_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 73 Primitive.Addresses.material2313
    · exact v2313_mb_checked.trans (by decide +kernel)
    · exact v2313_mg_checked.trans (by decide +kernel)
  upper_error := v2313_upper_checked
  lower_error := reuse_lower_error 27 73 Primitive.Addresses.material2313

def v2314_pa : Scalar.QComplex := ((999999201387998376438348146835 : Int)/10^30,(-1263813026308082554301737275 : Int)/10^30)
theorem v2314_pa_checked : Scalar.distance (sourceCoefficient 27 74 1 0) v2314_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2314_pb : Scalar.QComplex := ((-545306860383758136184333 : Int)/10^30,(-431477135892587554246799847 : Int)/10^30)
theorem v2314_pb_checked : Scalar.distance (sourceCoefficient 27 74 1 1) v2314_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2314_pg : Scalar.QComplex := ((-93086351185635750642882 : Int)/10^30,(117643837151675552974 : Int)/10^30)
theorem v2314_pg_checked : Scalar.distance (sourceCoefficient 27 74 1 2) v2314_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2314_mb : Scalar.QComplex := ((-917651992607581914057990 : Int)/10^30,(-431476504658669580273270538 : Int)/10^30)
theorem v2314_mb_checked : Scalar.distance (sourceCoefficient 27 74 3 1) v2314_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2314_mg : Scalar.QComplex := ((-93086215003999967657400 : Int)/10^30,(197973121967075838322 : Int)/10^30)
theorem v2314_mg_checked : Scalar.distance (sourceCoefficient 27 74 3 2) v2314_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2314_upper : Scalar.QComplex := ((999995530780024881280003773686 : Int)/10^30,(-2989719046383832701471360678 : Int)/10^30)
theorem v2314_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 74 5) 1) 14) v2314_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2314 : Material (27 : Basis) (74 : Basis) where
  plus := ![v2314_pa,v2314_pb,v2314_pg]
  minus := ![(Primitive.Addresses.material2314 1).one,v2314_mb,v2314_mg]
  upper := v2314_upper
  lower := (Primitive.Addresses.material2314 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2314_pa_checked.trans (by decide +kernel)
    · exact v2314_pb_checked.trans (by decide +kernel)
    · exact v2314_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 74 Primitive.Addresses.material2314
    · exact v2314_mb_checked.trans (by decide +kernel)
    · exact v2314_mg_checked.trans (by decide +kernel)
  upper_error := v2314_upper_checked
  lower_error := reuse_lower_error 27 74 Primitive.Addresses.material2314

def v2315_pa : Scalar.QComplex := ((999999182554701499572023755066 : Int)/10^30,(-1278628143278584304146065620 : Int)/10^30)
theorem v2315_pa_checked : Scalar.distance (sourceCoefficient 27 75 1 0) v2315_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2315_pb : Scalar.QComplex := ((-551699247661719841427576 : Int)/10^30,(-431477126151102478265809905 : Int)/10^30)
theorem v2315_pb_checked : Scalar.distance (sourceCoefficient 27 75 1 1) v2315_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2315_pg : Scalar.QComplex := ((-93086349258265557427615 : Int)/10^30,(119022923211406905870 : Int)/10^30)
theorem v2315_pg_checked : Scalar.distance (sourceCoefficient 27 75 1 2) v2315_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2315_mb : Scalar.QComplex := ((-924044369098902808814583 : Int)/10^30,(-431476489400845813046989240 : Int)/10^30)
theorem v2315_mb_checked : Scalar.distance (sourceCoefficient 27 75 3 1) v2315_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2315_mg : Scalar.QComplex := ((-93086211886541334272417 : Int)/10^30,(199352205850076752620 : Int)/10^30)
theorem v2315_mg_checked : Scalar.distance (sourceCoefficient 27 75 3 2) v2315_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2315_upper : Scalar.QComplex := ((999995486377208180223722743976 : Int)/10^30,(-3004534108784396163517494014 : Int)/10^30)
theorem v2315_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 75 5) 1) 14) v2315_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2315 : Material (27 : Basis) (75 : Basis) where
  plus := ![v2315_pa,v2315_pb,v2315_pg]
  minus := ![(Primitive.Addresses.material2315 1).one,v2315_mb,v2315_mg]
  upper := v2315_upper
  lower := (Primitive.Addresses.material2315 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2315_pa_checked.trans (by decide +kernel)
    · exact v2315_pb_checked.trans (by decide +kernel)
    · exact v2315_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 75 Primitive.Addresses.material2315
    · exact v2315_mb_checked.trans (by decide +kernel)
    · exact v2315_mg_checked.trans (by decide +kernel)
  upper_error := v2315_upper_checked
  lower_error := reuse_lower_error 27 75 Primitive.Addresses.material2315

def v2316_pa : Scalar.QComplex := ((999999166583862487384942758265 : Int)/10^30,(-1291058317986748361601588221 : Int)/10^30)
theorem v2316_pa_checked : Scalar.distance (sourceCoefficient 27 76 1 0) v2316_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2316_pb : Scalar.QComplex := ((-557062586325371983319038 : Int)/10^30,(-431477117880387424902648319 : Int)/10^30)
theorem v2316_pb_checked : Scalar.distance (sourceCoefficient 27 76 1 1) v2316_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2316_pg : Scalar.QComplex := ((-93086347622774414250653 : Int)/10^30,(120180003549343251483 : Int)/10^30)
theorem v2316_pg_checked : Scalar.distance (sourceCoefficient 27 76 1 2) v2316_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2316_mb : Scalar.QComplex := ((-929407698628284257668188 : Int)/10^30,(-431476476501814128323671782 : Int)/10^30)
theorem v2316_mb_checked : Scalar.distance (sourceCoefficient 27 76 3 1) v2316_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2316_mg : Scalar.QComplex := ((-93086209252542581388384 : Int)/10^30,(200509284345824010461 : Int)/10^30)
theorem v2316_mg_checked : Scalar.distance (sourceCoefficient 27 76 3 2) v2316_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2316_upper : Scalar.QComplex := ((999995448953039065074875071602 : Int)/10^30,(-3016964237415055872216265396 : Int)/10^30)
theorem v2316_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 76 5) 1) 14) v2316_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2316 : Material (27 : Basis) (76 : Basis) where
  plus := ![v2316_pa,v2316_pb,v2316_pg]
  minus := ![(Primitive.Addresses.material2316 1).one,v2316_mb,v2316_mg]
  upper := v2316_upper
  lower := (Primitive.Addresses.material2316 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2316_pa_checked.trans (by decide +kernel)
    · exact v2316_pb_checked.trans (by decide +kernel)
    · exact v2316_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 76 Primitive.Addresses.material2316
    · exact v2316_mb_checked.trans (by decide +kernel)
    · exact v2316_mg_checked.trans (by decide +kernel)
  upper_error := v2316_upper_checked
  lower_error := reuse_lower_error 27 76 Primitive.Addresses.material2316

def v2317_pa : Scalar.QComplex := ((999999162864451889130735249500 : Int)/10^30,(-1293936009015056593735797132 : Int)/10^30)
theorem v2317_pa_checked : Scalar.distance (sourceCoefficient 27 77 1 0) v2317_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2317_pb : Scalar.QComplex := ((-558304244773849477302048 : Int)/10^30,(-431477115952975183241423317 : Int)/10^30)
theorem v2317_pb_checked : Scalar.distance (sourceCoefficient 27 77 1 1) v2317_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2317_pg : Scalar.QComplex := ((-93086347241752313242490 : Int)/10^30,(120447877474982638487 : Int)/10^30)
theorem v2317_pg_checked : Scalar.distance (sourceCoefficient 27 77 1 2) v2317_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2317_mb : Scalar.QComplex := ((-930649354951165607559877 : Int)/10^30,(-431476473502907285510623152 : Int)/10^30)
theorem v2317_mb_checked : Scalar.distance (sourceCoefficient 27 77 3 1) v2317_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2317_mg : Scalar.QComplex := ((-93086208640357489019124 : Int)/10^30,(200777157842916779934 : Int)/10^30)
theorem v2317_mg_checked : Scalar.distance (sourceCoefficient 27 77 3 2) v2317_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2317_upper : Scalar.QComplex := ((999995440267000353676615321931 : Int)/10^30,(-3019841917738016084726288361 : Int)/10^30)
theorem v2317_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 77 5) 1) 14) v2317_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2317 : Material (27 : Basis) (77 : Basis) where
  plus := ![v2317_pa,v2317_pb,v2317_pg]
  minus := ![(Primitive.Addresses.material2317 1).one,v2317_mb,v2317_mg]
  upper := v2317_upper
  lower := (Primitive.Addresses.material2317 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2317_pa_checked.trans (by decide +kernel)
    · exact v2317_pb_checked.trans (by decide +kernel)
    · exact v2317_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 77 Primitive.Addresses.material2317
    · exact v2317_mb_checked.trans (by decide +kernel)
    · exact v2317_mg_checked.trans (by decide +kernel)
  upper_error := v2317_upper_checked
  lower_error := reuse_lower_error 27 77 Primitive.Addresses.material2317

def v2318_pa : Scalar.QComplex := ((999999140330252645874027231008 : Int)/10^30,(-1311235583591361140739229171 : Int)/10^30)
theorem v2318_pa_checked : Scalar.distance (sourceCoefficient 27 78 1 0) v2318_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2318_pb : Scalar.QComplex := ((-565768618992317786295879 : Int)/10^30,(-431477104265704817816756861 : Int)/10^30)
theorem v2318_pb_checked : Scalar.distance (sourceCoefficient 27 78 1 1) v2318_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2318_pg : Scalar.QComplex := ((-93086344932239561930079 : Int)/10^30,(122058232751381996481 : Int)/10^30)
theorem v2318_pg_checked : Scalar.distance (sourceCoefficient 27 78 1 2) v2318_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2318_mb : Scalar.QComplex := ((-938113716304718306019386 : Int)/10^30,(-431476455374222504187800373 : Int)/10^30)
theorem v2318_mb_checked : Scalar.distance (sourceCoefficient 27 78 3 1) v2318_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2318_mg : Scalar.QComplex := ((-93086204941181521820508 : Int)/10^30,(202387510526701783863 : Int)/10^30)
theorem v2318_mg_checked : Scalar.distance (sourceCoefficient 27 78 3 2) v2318_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2318_upper : Scalar.QComplex := ((999995387875338358907021148308 : Int)/10^30,(-3037141427656652843829816617 : Int)/10^30)
theorem v2318_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 78 5) 1) 14) v2318_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2318 : Material (27 : Basis) (78 : Basis) where
  plus := ![v2318_pa,v2318_pb,v2318_pg]
  minus := ![(Primitive.Addresses.material2318 1).one,v2318_mb,v2318_mg]
  upper := v2318_upper
  lower := (Primitive.Addresses.material2318 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2318_pa_checked.trans (by decide +kernel)
    · exact v2318_pb_checked.trans (by decide +kernel)
    · exact v2318_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 78 Primitive.Addresses.material2318
    · exact v2318_mb_checked.trans (by decide +kernel)
    · exact v2318_mg_checked.trans (by decide +kernel)
  upper_error := v2318_upper_checked
  lower_error := reuse_lower_error 27 78 Primitive.Addresses.material2318

def v2319_pa : Scalar.QComplex := ((999999133001833591212392032155 : Int)/10^30,(-1316812659846401484214287654 : Int)/10^30)
theorem v2319_pa_checked : Scalar.distance (sourceCoefficient 27 79 1 0) v2319_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2319_pb : Scalar.QComplex := ((-568175000927857064660132 : Int)/10^30,(-431477100461235923356955052 : Int)/10^30)
theorem v2319_pb_checked : Scalar.distance (sourceCoefficient 27 79 1 1) v2319_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2319_pg : Scalar.QComplex := ((-93086344180765656872680 : Int)/10^30,(122577382750417708957 : Int)/10^30)
theorem v2319_pg_checked : Scalar.distance (sourceCoefficient 27 79 1 2) v2319_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2319_mb : Scalar.QComplex := ((-940520094061166303694434 : Int)/10^30,(-431476449493155795354387097 : Int)/10^30)
theorem v2319_mb_checked : Scalar.distance (sourceCoefficient 27 79 3 1) v2319_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2319_mg : Scalar.QComplex := ((-93086203741704829051357 : Int)/10^30,(202906659683946090435 : Int)/10^30)
theorem v2319_mg_checked : Scalar.distance (sourceCoefficient 27 79 3 2) v2319_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2319_upper : Scalar.QComplex := ((999995370921402551270683664579 : Int)/10^30,(-3042718482957106775456828208 : Int)/10^30)
theorem v2319_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 79 5) 1) 14) v2319_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2319 : Material (27 : Basis) (79 : Basis) where
  plus := ![v2319_pa,v2319_pb,v2319_pg]
  minus := ![(Primitive.Addresses.material2319 1).one,v2319_mb,v2319_mg]
  upper := v2319_upper
  lower := (Primitive.Addresses.material2319 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2319_pa_checked.trans (by decide +kernel)
    · exact v2319_pb_checked.trans (by decide +kernel)
    · exact v2319_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 79 Primitive.Addresses.material2319
    · exact v2319_mb_checked.trans (by decide +kernel)
    · exact v2319_mg_checked.trans (by decide +kernel)
  upper_error := v2319_upper_checked
  lower_error := reuse_lower_error 27 79 Primitive.Addresses.material2319

def v2320_pa : Scalar.QComplex := ((999999121491876045624590623082 : Int)/10^30,(-1325524604121789572192193770 : Int)/10^30)
theorem v2320_pa_checked : Scalar.distance (sourceCoefficient 27 80 1 0) v2320_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2320_pb : Scalar.QComplex := ((-571934007300169279406343 : Int)/10^30,(-431477094482471099932015005 : Int)/10^30)
theorem v2320_pb_checked : Scalar.distance (sourceCoefficient 27 80 1 1) v2320_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2320_pg : Scalar.QComplex := ((-93086343000129541238754 : Int)/10^30,(123388346352056499568 : Int)/10^30)
theorem v2320_pg_checked : Scalar.distance (sourceCoefficient 27 80 1 2) v2320_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2320_mb : Scalar.QComplex := ((-944279093874423881906762 : Int)/10^30,(-431476440270539998153713735 : Int)/10^30)
theorem v2320_mb_checked : Scalar.distance (sourceCoefficient 27 80 3 1) v2320_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2320_mg : Scalar.QComplex := ((-93086201861244089252705 : Int)/10^30,(203717621964790275373 : Int)/10^30)
theorem v2320_mg_checked : Scalar.distance (sourceCoefficient 27 80 3 2) v2320_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2320_upper : Scalar.QComplex := ((999995344375436670503606883121 : Int)/10^30,(-3051430394391934693614409608 : Int)/10^30)
theorem v2320_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 80 5) 1) 14) v2320_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2320 : Material (27 : Basis) (80 : Basis) where
  plus := ![v2320_pa,v2320_pb,v2320_pg]
  minus := ![(Primitive.Addresses.material2320 1).one,v2320_mb,v2320_mg]
  upper := v2320_upper
  lower := (Primitive.Addresses.material2320 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2320_pa_checked.trans (by decide +kernel)
    · exact v2320_pb_checked.trans (by decide +kernel)
    · exact v2320_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 80 Primitive.Addresses.material2320
    · exact v2320_mb_checked.trans (by decide +kernel)
    · exact v2320_mg_checked.trans (by decide +kernel)
  upper_error := v2320_upper_checked
  lower_error := reuse_lower_error 27 80 Primitive.Addresses.material2320

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
