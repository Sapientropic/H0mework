import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B046

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1105_pa : Scalar.QComplex := ((999999997811360904442521396135 : Int)/10^30,(-66161002005145116432039714 : Int)/10^30)
theorem v1105_pa_checked : Scalar.distance (sourceCoefficient 12 20 1 0) v1105_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1105_pb : Scalar.QComplex := ((-28546985032197153067314 : Int)/10^30,(-431477518546319831958182899 : Int)/10^30)
theorem v1105_pb_checked : Scalar.distance (sourceCoefficient 12 20 1 1) v1105_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1105_pg : Scalar.QComplex := ((-93086429530362376960897 : Int)/10^30,(6158691464289257717 : Int)/10^30)
theorem v1105_pg_checked : Scalar.distance (sourceCoefficient 12 20 1 2) v1105_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1105_mb : Scalar.QComplex := ((-400892639882276488661176 : Int)/10^30,(-431477333252757806094802788 : Int)/10^30)
theorem v1105_mb_checked : Scalar.distance (sourceCoefficient 12 20 3 1) v1105_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1105_mg : Scalar.QComplex := ((-93086389555357046297936 : Int)/10^30,(86488085398674968351 : Int)/10^30)
theorem v1105_mg_checked : Scalar.distance (sourceCoefficient 12 20 3 2) v1105_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1105_upper : Scalar.QComplex := ((999998394240945034193746461664 : Int)/10^30,(-1792070180397372133673798851 : Int)/10^30)
theorem v1105_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 20 5) 1) 14) v1105_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1105 : Material (12 : Basis) (20 : Basis) where
  plus := ![v1105_pa,v1105_pb,v1105_pg]
  minus := ![(Primitive.Addresses.material1105 1).one,v1105_mb,v1105_mg]
  upper := v1105_upper
  lower := (Primitive.Addresses.material1105 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1105_pa_checked.trans (by decide +kernel)
    · exact v1105_pb_checked.trans (by decide +kernel)
    · exact v1105_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 20 Primitive.Addresses.material1105
    · exact v1105_mb_checked.trans (by decide +kernel)
    · exact v1105_mg_checked.trans (by decide +kernel)
  upper_error := v1105_upper_checked
  lower_error := reuse_lower_error 12 20 Primitive.Addresses.material1105

def v1106_pa : Scalar.QComplex := ((999999992899276443607874969150 : Int)/10^30,(-119169824462252083311462576 : Int)/10^30)
theorem v1106_pa_checked : Scalar.distance (sourceCoefficient 12 21 1 0) v1106_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1106_pb : Scalar.QComplex := ((-51419100101376159164237 : Int)/10^30,(-431477515120035450917682917 : Int)/10^30)
theorem v1106_pb_checked : Scalar.distance (sourceCoefficient 12 21 1 1) v1106_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1106_pg : Scalar.QComplex := ((-93086428932146985280379 : Int)/10^30,(11093093474430850027 : Int)/10^30)
theorem v1106_pg_checked : Scalar.distance (sourceCoefficient 12 21 1 2) v1106_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1106_mb : Scalar.QComplex := ((-423764743478392640487026 : Int)/10^30,(-431477310088869517937880815 : Int)/10^30)
theorem v1106_mb_checked : Scalar.distance (sourceCoefficient 12 21 3 1) v1106_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1106_mg : Scalar.QComplex := ((-93086384698975179824858 : Int)/10^30,(91422485055280238573 : Int)/10^30)
theorem v1106_mg_checked : Scalar.distance (sourceCoefficient 12 21 3 2) v1106_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1106_upper : Scalar.QComplex := ((999998297840449251173330927767 : Int)/10^30,(-1845078915426252745811509874 : Int)/10^30)
theorem v1106_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 21 5) 1) 14) v1106_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1106 : Material (12 : Basis) (21 : Basis) where
  plus := ![v1106_pa,v1106_pb,v1106_pg]
  minus := ![(Primitive.Addresses.material1106 1).one,v1106_mb,v1106_mg]
  upper := v1106_upper
  lower := (Primitive.Addresses.material1106 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1106_pa_checked.trans (by decide +kernel)
    · exact v1106_pb_checked.trans (by decide +kernel)
    · exact v1106_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 21 Primitive.Addresses.material1106
    · exact v1106_mb_checked.trans (by decide +kernel)
    · exact v1106_mg_checked.trans (by decide +kernel)
  upper_error := v1106_upper_checked
  lower_error := reuse_lower_error 12 21 Primitive.Addresses.material1106

def v1107_pa : Scalar.QComplex := ((999999992732170264610526533107 : Int)/10^30,(-120563922538865654937796944 : Int)/10^30)
theorem v1107_pa_checked : Scalar.distance (sourceCoefficient 12 22 1 0) v1107_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1107_pb : Scalar.QComplex := ((-52020622074777040831921 : Int)/10^30,(-431477515008109997845126253 : Int)/10^30)
theorem v1107_pb_checked : Scalar.distance (sourceCoefficient 12 22 1 1) v1107_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1107_pg : Scalar.QComplex := ((-93086428912295996687336 : Int)/10^30,(11222865086367551458 : Int)/10^30)
theorem v1107_pg_checked : Scalar.distance (sourceCoefficient 12 22 1 2) v1107_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1107_mb : Scalar.QComplex := ((-424366265131232775478961 : Int)/10^30,(-431477309457857735039321287 : Int)/10^30)
theorem v1107_mb_checked : Scalar.distance (sourceCoefficient 12 22 3 1) v1107_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1107_mg : Scalar.QComplex := ((-93086384567137142218308 : Int)/10^30,(91552256601766528924 : Int)/10^30)
theorem v1107_mg_checked : Scalar.distance (sourceCoefficient 12 22 3 2) v1107_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1107_upper : Scalar.QComplex := ((999998295267256512415550352694 : Int)/10^30,(-1846473011138110889390393674 : Int)/10^30)
theorem v1107_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 22 5) 1) 14) v1107_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1107 : Material (12 : Basis) (22 : Basis) where
  plus := ![v1107_pa,v1107_pb,v1107_pg]
  minus := ![(Primitive.Addresses.material1107 1).one,v1107_mb,v1107_mg]
  upper := v1107_upper
  lower := (Primitive.Addresses.material1107 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1107_pa_checked.trans (by decide +kernel)
    · exact v1107_pb_checked.trans (by decide +kernel)
    · exact v1107_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 22 Primitive.Addresses.material1107
    · exact v1107_mb_checked.trans (by decide +kernel)
    · exact v1107_mg_checked.trans (by decide +kernel)
  upper_error := v1107_upper_checked
  lower_error := reuse_lower_error 12 22 Primitive.Addresses.material1107

def v1108_pa : Scalar.QComplex := ((999999991436172169405623391637 : Int)/10^30,(-130872669369313339855056652 : Int)/10^30)
theorem v1108_pa_checked : Scalar.distance (sourceCoefficient 12 23 1 0) v1108_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1108_pb : Scalar.QComplex := ((-56468614532679721812694 : Int)/10^30,(-431477514145767343532166912 : Int)/10^30)
theorem v1108_pb_checked : Scalar.distance (sourceCoefficient 12 23 1 1) v1108_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1108_pg : Scalar.QComplex := ((-93086428758955707014697 : Int)/10^30,(12182469518069522434 : Int)/10^30)
theorem v1108_pg_checked : Scalar.distance (sourceCoefficient 12 23 1 2) v1108_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1108_mb : Scalar.QComplex := ((-428814255188781708884156 : Int)/10^30,(-431477304757098240789628908 : Int)/10^30)
theorem v1108_mb_checked : Scalar.distance (sourceCoefficient 12 23 3 1) v1108_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1108_mg : Scalar.QComplex := ((-93086383585701504061706 : Int)/10^30,(92511860543838150092 : Int)/10^30)
theorem v1108_mg_checked : Scalar.distance (sourceCoefficient 12 23 3 2) v1108_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1108_upper : Scalar.QComplex := ((999998276179298520301926702250 : Int)/10^30,(-1856781740378115980528273741 : Int)/10^30)
theorem v1108_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 23 5) 1) 14) v1108_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1108 : Material (12 : Basis) (23 : Basis) where
  plus := ![v1108_pa,v1108_pb,v1108_pg]
  minus := ![(Primitive.Addresses.material1108 1).one,v1108_mb,v1108_mg]
  upper := v1108_upper
  lower := (Primitive.Addresses.material1108 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1108_pa_checked.trans (by decide +kernel)
    · exact v1108_pb_checked.trans (by decide +kernel)
    · exact v1108_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 23 Primitive.Addresses.material1108
    · exact v1108_mb_checked.trans (by decide +kernel)
    · exact v1108_mg_checked.trans (by decide +kernel)
  upper_error := v1108_upper_checked
  lower_error := reuse_lower_error 12 23 Primitive.Addresses.material1108

def v1109_pa : Scalar.QComplex := ((999999983470990009647545986246 : Int)/10^30,(-181818645104116692090342028 : Int)/10^30)
theorem v1109_pa_checked : Scalar.distance (sourceCoefficient 12 24 1 0) v1109_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1109_pb : Scalar.QComplex := ((-78450657373516131005920 : Int)/10^30,(-431477508986388170378845167 : Int)/10^30)
theorem v1109_pb_checked : Scalar.distance (sourceCoefficient 12 24 1 1) v1109_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1109_pg : Scalar.QComplex := ((-93086427831691463245792 : Int)/10^30,(16924848465691270224 : Int)/10^30)
theorem v1109_pg_checked : Scalar.distance (sourceCoefficient 12 24 1 2) v1109_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1109_mb : Scalar.QComplex := ((-450796285392387082827150 : Int)/10^30,(-431477280628208051524892137 : Int)/10^30)
theorem v1109_mb_checked : Scalar.distance (sourceCoefficient 12 24 3 1) v1109_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1109_mg : Scalar.QComplex := ((-93086378565978162577100 : Int)/10^30,(97254236925468198316 : Int)/10^30)
theorem v1109_mg_checked : Scalar.distance (sourceCoefficient 12 24 3 2) v1109_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1109_upper : Scalar.QComplex := ((999998180285995888291709578605 : Int)/10^30,(-1907727626487691198412893900 : Int)/10^30)
theorem v1109_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 24 5) 1) 14) v1109_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1109 : Material (12 : Basis) (24 : Basis) where
  plus := ![v1109_pa,v1109_pb,v1109_pg]
  minus := ![(Primitive.Addresses.material1109 1).one,v1109_mb,v1109_mg]
  upper := v1109_upper
  lower := (Primitive.Addresses.material1109 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1109_pa_checked.trans (by decide +kernel)
    · exact v1109_pb_checked.trans (by decide +kernel)
    · exact v1109_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 24 Primitive.Addresses.material1109
    · exact v1109_mb_checked.trans (by decide +kernel)
    · exact v1109_mg_checked.trans (by decide +kernel)
  upper_error := v1109_upper_checked
  lower_error := reuse_lower_error 12 24 Primitive.Addresses.material1109

def v1110_pa : Scalar.QComplex := ((999999979027868696443024726456 : Int)/10^30,(-204802983785109095596176011 : Int)/10^30)
theorem v1110_pa_checked : Scalar.distance (sourceCoefficient 12 25 1 0) v1110_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1110_pb : Scalar.QComplex := ((-88367882553024148704027 : Int)/10^30,(-431477506169938931727027623 : Int)/10^30)
theorem v1110_pb_checked : Scalar.distance (sourceCoefficient 12 25 1 1) v1110_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1110_pg : Scalar.QComplex := ((-93086427321085665566738 : Int)/10^30,(19064378465074692263 : Int)/10^30)
theorem v1110_pg_checked : Scalar.distance (sourceCoefficient 12 25 1 2) v1110_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1110_mb : Scalar.QComplex := ((-460713504448790081821594 : Int)/10^30,(-431477269253641186891888058 : Int)/10^30)
theorem v1110_mb_checked : Scalar.distance (sourceCoefficient 12 25 3 1) v1110_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1110_mg : Scalar.QComplex := ((-93086376209054526406116 : Int)/10^30,(99393765687577013667 : Int)/10^30)
theorem v1110_mg_checked : Scalar.distance (sourceCoefficient 12 25 3 2) v1110_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1110_upper : Scalar.QComplex := ((999998136173997752118623459952 : Int)/10^30,(-1930711923267786756887623029 : Int)/10^30)
theorem v1110_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 25 5) 1) 14) v1110_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1110 : Material (12 : Basis) (25 : Basis) where
  plus := ![v1110_pa,v1110_pb,v1110_pg]
  minus := ![(Primitive.Addresses.material1110 1).one,v1110_mb,v1110_mg]
  upper := v1110_upper
  lower := (Primitive.Addresses.material1110 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1110_pa_checked.trans (by decide +kernel)
    · exact v1110_pb_checked.trans (by decide +kernel)
    · exact v1110_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 25 Primitive.Addresses.material1110
    · exact v1110_mb_checked.trans (by decide +kernel)
    · exact v1110_mg_checked.trans (by decide +kernel)
  upper_error := v1110_upper_checked
  lower_error := reuse_lower_error 12 25 Primitive.Addresses.material1110

def v1111_pa : Scalar.QComplex := ((999999977496843081825809655335 : Int)/10^30,(-212146914495488973174150001 : Int)/10^30)
theorem v1111_pa_checked : Scalar.distance (sourceCoefficient 12 26 1 0) v1111_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1111_pb : Scalar.QComplex := ((-91536623463519092285875 : Int)/10^30,(-431477505205961868124244703 : Int)/10^30)
theorem v1111_pb_checked : Scalar.distance (sourceCoefficient 12 26 1 1) v1111_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1111_pg : Scalar.QComplex := ((-93086427145843198242653 : Int)/10^30,(19747998744792075212 : Int)/10^30)
theorem v1111_pg_checked : Scalar.distance (sourceCoefficient 12 26 1 2) v1111_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1111_mb : Scalar.QComplex := ((-463882243347549175838449 : Int)/10^30,(-431477265555183791257472092 : Int)/10^30)
theorem v1111_mb_checked : Scalar.distance (sourceCoefficient 12 26 3 1) v1111_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1111_mg : Scalar.QComplex := ((-93086375443878612051163 : Int)/10^30,(100077385561524966814 : Int)/10^30)
theorem v1111_mg_checked : Scalar.distance (sourceCoefficient 12 26 3 2) v1111_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1111_upper : Scalar.QComplex := ((999998121968016247858239914383 : Int)/10^30,(-1938055840397833202785352055 : Int)/10^30)
theorem v1111_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 26 5) 1) 14) v1111_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1111 : Material (12 : Basis) (26 : Basis) where
  plus := ![v1111_pa,v1111_pb,v1111_pg]
  minus := ![(Primitive.Addresses.material1111 1).one,v1111_mb,v1111_mg]
  upper := v1111_upper
  lower := (Primitive.Addresses.material1111 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1111_pa_checked.trans (by decide +kernel)
    · exact v1111_pb_checked.trans (by decide +kernel)
    · exact v1111_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 26 Primitive.Addresses.material1111
    · exact v1111_mb_checked.trans (by decide +kernel)
    · exact v1111_mg_checked.trans (by decide +kernel)
  upper_error := v1111_upper_checked
  lower_error := reuse_lower_error 12 26 Primitive.Addresses.material1111

def v1112_pa : Scalar.QComplex := ((999999976413785175910184946168 : Int)/10^30,(-217192147859608636403926645 : Int)/10^30)
theorem v1112_pa_checked : Scalar.distance (sourceCoefficient 12 27 1 0) v1112_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1112_pb : Scalar.QComplex := ((-93713528171395967128678 : Int)/10^30,(-431477504525735778330894166 : Int)/10^30)
theorem v1112_pb_checked : Scalar.distance (sourceCoefficient 12 27 1 1) v1112_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1112_pg : Scalar.QComplex := ((-93086427022058631322703 : Int)/10^30,(20217641498355262714 : Int)/10^30)
theorem v1112_pg_checked : Scalar.distance (sourceCoefficient 12 27 1 2) v1112_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1112_mb : Scalar.QComplex := ((-466059146657860459232814 : Int)/10^30,(-431477262996387235994112567 : Int)/10^30)
theorem v1112_mb_checked : Scalar.distance (sourceCoefficient 12 27 3 1) v1112_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1112_mg : Scalar.QComplex := ((-93086374914813546821257 : Int)/10^30,(100547028033398187228 : Int)/10^30)
theorem v1112_mg_checked : Scalar.distance (sourceCoefficient 12 27 3 2) v1112_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1112_upper : Scalar.QComplex := ((999998112177344868555039194542 : Int)/10^30,(-1943101064378410733536901201 : Int)/10^30)
theorem v1112_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 27 5) 1) 14) v1112_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1112 : Material (12 : Basis) (27 : Basis) where
  plus := ![v1112_pa,v1112_pb,v1112_pg]
  minus := ![(Primitive.Addresses.material1112 1).one,v1112_mb,v1112_mg]
  upper := v1112_upper
  lower := (Primitive.Addresses.material1112 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1112_pa_checked.trans (by decide +kernel)
    · exact v1112_pb_checked.trans (by decide +kernel)
    · exact v1112_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 27 Primitive.Addresses.material1112
    · exact v1112_mb_checked.trans (by decide +kernel)
    · exact v1112_mg_checked.trans (by decide +kernel)
  upper_error := v1112_upper_checked
  lower_error := reuse_lower_error 12 27 Primitive.Addresses.material1112

def v1113_pa : Scalar.QComplex := ((999999974914523598603844025543 : Int)/10^30,(-223988732246760987965725558 : Int)/10^30)
theorem v1113_pa_checked : Scalar.distance (sourceCoefficient 12 28 1 0) v1113_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1113_pb : Scalar.QComplex := ((-96646101445690777517244 : Int)/10^30,(-431477503586231584830371297 : Int)/10^30)
theorem v1113_pb_checked : Scalar.distance (sourceCoefficient 12 28 1 1) v1113_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1113_pg : Scalar.QComplex := ((-93086426850934437853460 : Int)/10^30,(20850311262761647550 : Int)/10^30)
theorem v1113_pg_checked : Scalar.distance (sourceCoefficient 12 28 1 2) v1113_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1113_mb : Scalar.QComplex := ((-468991718029474409088973 : Int)/10^30,(-431477259526204734794818124 : Int)/10^30)
theorem v1113_mb_checked : Scalar.distance (sourceCoefficient 12 28 3 1) v1113_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1113_mg : Scalar.QComplex := ((-93086374197723904775089 : Int)/10^30,(101179697414560232522 : Int)/10^30)
theorem v1113_mg_checked : Scalar.distance (sourceCoefficient 12 28 3 2) v1113_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1113_upper : Scalar.QComplex := ((999998098947797453316876756057 : Int)/10^30,(-1949897636055259552837807985 : Int)/10^30)
theorem v1113_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 28 5) 1) 14) v1113_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1113 : Material (12 : Basis) (28 : Basis) where
  plus := ![v1113_pa,v1113_pb,v1113_pg]
  minus := ![(Primitive.Addresses.material1113 1).one,v1113_mb,v1113_mg]
  upper := v1113_upper
  lower := (Primitive.Addresses.material1113 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1113_pa_checked.trans (by decide +kernel)
    · exact v1113_pb_checked.trans (by decide +kernel)
    · exact v1113_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 28 Primitive.Addresses.material1113
    · exact v1113_mb_checked.trans (by decide +kernel)
    · exact v1113_mg_checked.trans (by decide +kernel)
  upper_error := v1113_upper_checked
  lower_error := reuse_lower_error 12 28 Primitive.Addresses.material1113

def v1114_pa : Scalar.QComplex := ((999999971736496173475113269283 : Int)/10^30,(-237754089037863079419032418 : Int)/10^30)
theorem v1114_pa_checked : Scalar.distance (sourceCoefficient 12 29 1 0) v1114_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1114_pb : Scalar.QComplex := ((-102585543233144389683084 : Int)/10^30,(-431477501602003694902976636 : Int)/10^30)
theorem v1114_pb_checked : Scalar.distance (sourceCoefficient 12 29 1 1) v1114_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1114_pg : Scalar.QComplex := ((-93086426488981381974071 : Int)/10^30,(22131679157196574315 : Int)/10^30)
theorem v1114_pg_checked : Scalar.distance (sourceCoefficient 12 29 1 2) v1114_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1114_mb : Scalar.QComplex := ((-474931155893103095185835 : Int)/10^30,(-431477252416506823641629581 : Int)/10^30)
theorem v1114_mb_checked : Scalar.distance (sourceCoefficient 12 29 3 1) v1114_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1114_mg : Scalar.QComplex := ((-93086372730008201437668 : Int)/10^30,(102461064519534145321 : Int)/10^30)
theorem v1114_mg_checked : Scalar.distance (sourceCoefficient 12 29 3 2) v1114_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1114_upper : Scalar.QComplex := ((999998072012017723457596650095 : Int)/10^30,(-1963662966859492668964429876 : Int)/10^30)
theorem v1114_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 29 5) 1) 14) v1114_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1114 : Material (12 : Basis) (29 : Basis) where
  plus := ![v1114_pa,v1114_pb,v1114_pg]
  minus := ![(Primitive.Addresses.material1114 1).one,v1114_mb,v1114_mg]
  upper := v1114_upper
  lower := (Primitive.Addresses.material1114 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1114_pa_checked.trans (by decide +kernel)
    · exact v1114_pb_checked.trans (by decide +kernel)
    · exact v1114_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 29 Primitive.Addresses.material1114
    · exact v1114_mb_checked.trans (by decide +kernel)
    · exact v1114_mg_checked.trans (by decide +kernel)
  upper_error := v1114_upper_checked
  lower_error := reuse_lower_error 12 29 Primitive.Addresses.material1114

def v1115_pa : Scalar.QComplex := ((999999970482695206430294081228 : Int)/10^30,(-242970386499812214380806643 : Int)/10^30)
theorem v1115_pa_checked : Scalar.distance (sourceCoefficient 12 30 1 0) v1115_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1115_pb : Scalar.QComplex := ((-104836258235083699408803 : Int)/10^30,(-431477500821611184028450023 : Int)/10^30)
theorem v1115_pb_checked : Scalar.distance (sourceCoefficient 12 30 1 1) v1115_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1115_pg : Scalar.QComplex := ((-93086426346444993797078 : Int)/10^30,(22617245654882176338 : Int)/10^30)
theorem v1115_pg_checked : Scalar.distance (sourceCoefficient 12 30 1 2) v1115_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1115_mb : Scalar.QComplex := ((-477181869383554757621671 : Int)/10^30,(-431477249693848925109990120 : Int)/10^30)
theorem v1115_mb_checked : Scalar.distance (sourceCoefficient 12 30 3 1) v1115_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1115_mg : Scalar.QComplex := ((-93086372168449847934048 : Int)/10^30,(102946630713418665374 : Int)/10^30)
theorem v1115_mg_checked : Scalar.distance (sourceCoefficient 12 30 3 2) v1115_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1115_upper : Scalar.QComplex := ((999998061755362423286994674526 : Int)/10^30,(-1968879254388432758511995360 : Int)/10^30)
theorem v1115_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 30 5) 1) 14) v1115_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1115 : Material (12 : Basis) (30 : Basis) where
  plus := ![v1115_pa,v1115_pb,v1115_pg]
  minus := ![(Primitive.Addresses.material1115 1).one,v1115_mb,v1115_mg]
  upper := v1115_upper
  lower := (Primitive.Addresses.material1115 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1115_pa_checked.trans (by decide +kernel)
    · exact v1115_pb_checked.trans (by decide +kernel)
    · exact v1115_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 30 Primitive.Addresses.material1115
    · exact v1115_mb_checked.trans (by decide +kernel)
    · exact v1115_mg_checked.trans (by decide +kernel)
  upper_error := v1115_upper_checked
  lower_error := reuse_lower_error 12 30 Primitive.Addresses.material1115

def v1116_pa : Scalar.QComplex := ((999999967725371602968718908388 : Int)/10^30,(-254065455645609019533873136 : Int)/10^30)
theorem v1116_pa_checked : Scalar.distance (sourceCoefficient 12 31 1 0) v1116_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1116_pb : Scalar.QComplex := ((-109623530950181761136751 : Int)/10^30,(-431477499109657670689874796 : Int)/10^30)
theorem v1116_pb_checked : Scalar.distance (sourceCoefficient 12 31 1 1) v1116_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1116_pg : Scalar.QComplex := ((-93086426033442915865906 : Int)/10^30,(23650046007904402357 : Int)/10^30)
theorem v1116_pg_checked : Scalar.distance (sourceCoefficient 12 31 1 2) v1116_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1116_mb : Scalar.QComplex := ((-481969138838793619859959 : Int)/10^30,(-431477243850695306839561188 : Int)/10^30)
theorem v1116_mb_checked : Scalar.distance (sourceCoefficient 12 31 3 1) v1116_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1116_mg : Scalar.QComplex := ((-93086370964187697490834 : Int)/10^30,(103979430411775422491 : Int)/10^30)
theorem v1116_mg_checked : Scalar.distance (sourceCoefficient 12 31 3 2) v1116_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1116_upper : Scalar.QComplex := ((999998039848960117700015793477 : Int)/10^30,(-1979974302250536992244330022 : Int)/10^30)
theorem v1116_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 31 5) 1) 14) v1116_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1116 : Material (12 : Basis) (31 : Basis) where
  plus := ![v1116_pa,v1116_pb,v1116_pg]
  minus := ![(Primitive.Addresses.material1116 1).one,v1116_mb,v1116_mg]
  upper := v1116_upper
  lower := (Primitive.Addresses.material1116 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1116_pa_checked.trans (by decide +kernel)
    · exact v1116_pb_checked.trans (by decide +kernel)
    · exact v1116_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 31 Primitive.Addresses.material1116
    · exact v1116_mb_checked.trans (by decide +kernel)
    · exact v1116_mg_checked.trans (by decide +kernel)
  upper_error := v1116_upper_checked
  lower_error := reuse_lower_error 12 31 Primitive.Addresses.material1116

def v1117_pa : Scalar.QComplex := ((999999966500526586123881088280 : Int)/10^30,(-258841545555456608613418496 : Int)/10^30)
theorem v1117_pa_checked : Scalar.distance (sourceCoefficient 12 32 1 0) v1117_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1117_pb : Scalar.QComplex := ((-111684306286916750991680 : Int)/10^30,(-431477498350909139639529883 : Int)/10^30)
theorem v1117_pb_checked : Scalar.distance (sourceCoefficient 12 32 1 1) v1117_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1117_pg : Scalar.QComplex := ((-93086425894588953487003 : Int)/10^30,(24094635155946472120 : Int)/10^30)
theorem v1117_pg_checked : Scalar.distance (sourceCoefficient 12 32 1 2) v1117_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1117_mb : Scalar.QComplex := ((-484029912753441960231711 : Int)/10^30,(-431477241313590756579428184 : Int)/10^30)
theorem v1117_mb_checked : Scalar.distance (sourceCoefficient 12 32 3 1) v1117_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1117_mg : Scalar.QComplex := ((-93086370441673375605219 : Int)/10^30,(104424019274451917926 : Int)/10^30)
theorem v1117_mg_checked : Scalar.distance (sourceCoefficient 12 32 3 2) v1117_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1117_upper : Scalar.QComplex := ((999998030381019024213007886308 : Int)/10^30,(-1984750382932988317535276722 : Int)/10^30)
theorem v1117_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 32 5) 1) 14) v1117_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1117 : Material (12 : Basis) (32 : Basis) where
  plus := ![v1117_pa,v1117_pb,v1117_pg]
  minus := ![(Primitive.Addresses.material1117 1).one,v1117_mb,v1117_mg]
  upper := v1117_upper
  lower := (Primitive.Addresses.material1117 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1117_pa_checked.trans (by decide +kernel)
    · exact v1117_pb_checked.trans (by decide +kernel)
    · exact v1117_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 32 Primitive.Addresses.material1117
    · exact v1117_mb_checked.trans (by decide +kernel)
    · exact v1117_mg_checked.trans (by decide +kernel)
  upper_error := v1117_upper_checked
  lower_error := reuse_lower_error 12 32 Primitive.Addresses.material1117

def v1118_pa : Scalar.QComplex := ((999999964755494871950424657391 : Int)/10^30,(-265497662916124384034729400 : Int)/10^30)
theorem v1118_pa_checked : Scalar.distance (sourceCoefficient 12 33 1 0) v1118_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1118_pb : Scalar.QComplex := ((-114556271163988227863165 : Int)/10^30,(-431477497271603412315357454 : Int)/10^30)
theorem v1118_pb_checked : Scalar.distance (sourceCoefficient 12 33 1 1) v1118_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1118_pg : Scalar.QComplex := ((-93086425696945522187949 : Int)/10^30,(24714229342795283894 : Int)/10^30)
theorem v1118_pg_checked : Scalar.distance (sourceCoefficient 12 33 1 2) v1118_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1118_mb : Scalar.QComplex := ((-486901875629757425535166 : Int)/10^30,(-431477237755909090713841615 : Int)/10^30)
theorem v1118_mb_checked : Scalar.distance (sourceCoefficient 12 33 3 1) v1118_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1118_mg : Scalar.QComplex := ((-93086369709348140133599 : Int)/10^30,(105043613060040117402 : Int)/10^30)
theorem v1118_mg_checked : Scalar.distance (sourceCoefficient 12 33 3 2) v1118_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1118_upper : Scalar.QComplex := ((999998017148135182796757743589 : Int)/10^30,(-1991406487368384736088457470 : Int)/10^30)
theorem v1118_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 33 5) 1) 14) v1118_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1118 : Material (12 : Basis) (33 : Basis) where
  plus := ![v1118_pa,v1118_pb,v1118_pg]
  minus := ![(Primitive.Addresses.material1118 1).one,v1118_mb,v1118_mg]
  upper := v1118_upper
  lower := (Primitive.Addresses.material1118 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1118_pa_checked.trans (by decide +kernel)
    · exact v1118_pb_checked.trans (by decide +kernel)
    · exact v1118_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 33 Primitive.Addresses.material1118
    · exact v1118_mb_checked.trans (by decide +kernel)
    · exact v1118_mg_checked.trans (by decide +kernel)
  upper_error := v1118_upper_checked
  lower_error := reuse_lower_error 12 33 Primitive.Addresses.material1118

def v1119_pa : Scalar.QComplex := ((999999960332518011374094308473 : Int)/10^30,(-281664627533779406350823733 : Int)/10^30)
theorem v1119_pa_checked : Scalar.distance (sourceCoefficient 12 34 1 0) v1119_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1119_pb : Scalar.QComplex := ((-121531952610797344079724 : Int)/10^30,(-431477494543952805110209468 : Int)/10^30)
theorem v1119_pb_checked : Scalar.distance (sourceCoefficient 12 34 1 1) v1119_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1119_pg : Scalar.QComplex := ((-93086425196855965678106 : Int)/10^30,(26219154321571285734 : Int)/10^30)
theorem v1119_pg_checked : Scalar.distance (sourceCoefficient 12 34 1 2) v1119_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1119_mb : Scalar.QComplex := ((-493877552125361909518258 : Int)/10^30,(-431477229008560583571120400 : Int)/10^30)
theorem v1119_mb_checked : Scalar.distance (sourceCoefficient 12 34 3 1) v1119_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1119_mg : Scalar.QComplex := ((-93086367910576292451221 : Int)/10^30,(106548537046909007105 : Int)/10^30)
theorem v1119_mg_checked : Scalar.distance (sourceCoefficient 12 34 3 2) v1119_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1119_upper : Scalar.QComplex := ((999997984822450635225562407393 : Int)/10^30,(-2007573420273588253447898384 : Int)/10^30)
theorem v1119_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 34 5) 1) 14) v1119_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1119 : Material (12 : Basis) (34 : Basis) where
  plus := ![v1119_pa,v1119_pb,v1119_pg]
  minus := ![(Primitive.Addresses.material1119 1).one,v1119_mb,v1119_mg]
  upper := v1119_upper
  lower := (Primitive.Addresses.material1119 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1119_pa_checked.trans (by decide +kernel)
    · exact v1119_pb_checked.trans (by decide +kernel)
    · exact v1119_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 34 Primitive.Addresses.material1119
    · exact v1119_mb_checked.trans (by decide +kernel)
    · exact v1119_mg_checked.trans (by decide +kernel)
  upper_error := v1119_upper_checked
  lower_error := reuse_lower_error 12 34 Primitive.Addresses.material1119

def v1120_pa : Scalar.QComplex := ((999999944546597282244881916079 : Int)/10^30,(-333026729198168661337452948 : Int)/10^30)
theorem v1120_pa_checked : Scalar.distance (sourceCoefficient 12 35 1 0) v1120_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1120_pb : Scalar.QComplex := ((-143693543480722393159159 : Int)/10^30,(-431477484880563875115778964 : Int)/10^30)
theorem v1120_pb_checked : Scalar.distance (sourceCoefficient 12 35 1 1) v1120_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1120_pg : Scalar.QComplex := ((-93086423419744641840177 : Int)/10^30,(31000268843303756531 : Int)/10^30)
theorem v1120_pg_checked : Scalar.distance (sourceCoefficient 12 35 1 2) v1120_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1120_mb : Scalar.QComplex := ((-516039126404444419282772 : Int)/10^30,(-431477200220720451953498100 : Int)/10^30)
theorem v1120_mb_checked : Scalar.distance (sourceCoefficient 12 35 3 1) v1120_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1120_mg : Scalar.QComplex := ((-93086362007579131462441 : Int)/10^30,(111329648254846999383 : Int)/10^30)
theorem v1120_mg_checked : Scalar.distance (sourceCoefficient 12 35 3 2) v1120_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1120_upper : Scalar.QComplex := ((999997880390225478099792882389 : Int)/10^30,(-2058935418195093404677281583 : Int)/10^30)
theorem v1120_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 35 5) 1) 14) v1120_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1120 : Material (12 : Basis) (35 : Basis) where
  plus := ![v1120_pa,v1120_pb,v1120_pg]
  minus := ![(Primitive.Addresses.material1120 1).one,v1120_mb,v1120_mg]
  upper := v1120_upper
  lower := (Primitive.Addresses.material1120 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1120_pa_checked.trans (by decide +kernel)
    · exact v1120_pb_checked.trans (by decide +kernel)
    · exact v1120_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 35 Primitive.Addresses.material1120
    · exact v1120_mb_checked.trans (by decide +kernel)
    · exact v1120_mg_checked.trans (by decide +kernel)
  upper_error := v1120_upper_checked
  lower_error := reuse_lower_error 12 35 Primitive.Addresses.material1120

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
