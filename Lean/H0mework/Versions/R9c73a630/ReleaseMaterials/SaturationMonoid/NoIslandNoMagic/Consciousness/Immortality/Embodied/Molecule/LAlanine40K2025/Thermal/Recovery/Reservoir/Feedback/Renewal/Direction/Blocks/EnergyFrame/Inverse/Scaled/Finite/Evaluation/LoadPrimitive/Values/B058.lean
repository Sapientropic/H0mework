import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B038
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B039

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v929_pa : Scalar.QComplex := ((999999999998983826133199749623 : Int)/10^30,(-1425604339779964385210154 : Int)/10^30)
theorem v929_pa_checked : Scalar.distance (sourceCoefficient 10 15 1 0) v929_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v929_pb : Scalar.QComplex := ((-615116225259403604188 : Int)/10^30,(-431477520160831553424749813 : Int)/10^30)
theorem v929_pb_checked : Scalar.distance (sourceCoefficient 10 15 1 1) v929_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v929_pg : Scalar.QComplex := ((-93086429806337767104431 : Int)/10^30,(132704418306673001 : Int)/10^30)
theorem v929_pg_checked : Scalar.distance (sourceCoefficient 10 15 1 2) v929_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v929_mb : Scalar.QComplex := ((-372960782868900946205291 : Int)/10^30,(-431477358971213702120410815 : Int)/10^30)
theorem v929_mb_checked : Scalar.distance (sourceCoefficient 10 15 3 1) v929_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v929_mg : Scalar.QComplex := ((-93086395031487753984495 : Int)/10^30,(80462100834597094291 : Int)/10^30)
theorem v929_mg_checked : Scalar.distance (sourceCoefficient 10 15 3 2) v929_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v929_upper : Scalar.QComplex := ((999998508155988318696510453968 : Int)/10^30,(-1727334882923416153438793102 : Int)/10^30)
theorem v929_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 15 5) 1) 14) v929_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material929 : Material (10 : Basis) (15 : Basis) where
  plus := ![v929_pa,v929_pb,v929_pg]
  minus := ![(Primitive.Addresses.material929 1).one,v929_mb,v929_mg]
  upper := v929_upper
  lower := (Primitive.Addresses.material929 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v929_pa_checked.trans (by decide +kernel)
    · exact v929_pb_checked.trans (by decide +kernel)
    · exact v929_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 15 Primitive.Addresses.material929
    · exact v929_mb_checked.trans (by decide +kernel)
    · exact v929_mg_checked.trans (by decide +kernel)
  upper_error := v929_upper_checked
  lower_error := reuse_lower_error 10 15 Primitive.Addresses.material929

def v930_pa : Scalar.QComplex := ((999999999988680421892583190058 : Int)/10^30,(-4758062233168612837302738 : Int)/10^30)
theorem v930_pa_checked : Scalar.distance (sourceCoefficient 10 16 1 0) v930_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v930_pb : Scalar.QComplex := ((-2052996892890406115271 : Int)/10^30,(-431477520103805335765619735 : Int)/10^30)
theorem v930_pb_checked : Scalar.distance (sourceCoefficient 10 16 1 1) v930_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v930_pg : Scalar.QComplex := ((-93086429799706830553473 : Int)/10^30,(442911026055499958 : Int)/10^30)
theorem v930_pg_checked : Scalar.distance (sourceCoefficient 10 16 1 2) v930_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v930_mb : Scalar.QComplex := ((-374398662951932204290156 : Int)/10^30,(-431477357673361249270468135 : Int)/10^30)
theorem v930_mb_checked : Scalar.distance (sourceCoefficient 10 16 3 1) v930_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v930_mg : Scalar.QComplex := ((-93086394757162488602279 : Int)/10^30,(80772307321119624443 : Int)/10^30)
theorem v930_mg_checked : Scalar.distance (sourceCoefficient 10 16 3 2) v930_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v930_upper : Scalar.QComplex := ((999998502394164924031304854540 : Int)/10^30,(-1730667335835717486689303039 : Int)/10^30)
theorem v930_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 16 5) 1) 14) v930_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material930 : Material (10 : Basis) (16 : Basis) where
  plus := ![v930_pa,v930_pb,v930_pg]
  minus := ![(Primitive.Addresses.material930 1).one,v930_mb,v930_mg]
  upper := v930_upper
  lower := (Primitive.Addresses.material930 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v930_pa_checked.trans (by decide +kernel)
    · exact v930_pb_checked.trans (by decide +kernel)
    · exact v930_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 16 Primitive.Addresses.material930
    · exact v930_mb_checked.trans (by decide +kernel)
    · exact v930_mg_checked.trans (by decide +kernel)
  upper_error := v930_upper_checked
  lower_error := reuse_lower_error 10 16 Primitive.Addresses.material930

def v931_pa : Scalar.QComplex := ((999999999934454411551417885837 : Int)/10^30,(-11449505530496415466637519 : Int)/10^30)
theorem v931_pa_checked : Scalar.distance (sourceCoefficient 10 17 1 0) v931_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v931_pb : Scalar.QComplex := ((-4940204251505257221833 : Int)/10^30,(-431477519970004897905177574 : Int)/10^30)
theorem v931_pb_checked : Scalar.distance (sourceCoefficient 10 17 1 1) v931_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v931_pg : Scalar.QComplex := ((-93086429782750006823031 : Int)/10^30,(1065793592681620513 : Int)/10^30)
theorem v931_pg_checked : Scalar.distance (sourceCoefficient 10 17 1 2) v931_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v931_mb : Scalar.QComplex := ((-377285869120044052164023 : Int)/10^30,(-431477355048030945737733664 : Int)/10^30)
theorem v931_mb_checked : Scalar.distance (sourceCoefficient 10 17 3 1) v931_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v931_mg : Scalar.QComplex := ((-93086394202686069776698 : Int)/10^30,(81395189641185123132 : Int)/10^30)
theorem v931_mg_checked : Scalar.distance (sourceCoefficient 10 17 3 2) v931_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v931_upper : Scalar.QComplex := ((999998490791114906259598721068 : Int)/10^30,(-1737358769073337355590705615 : Int)/10^30)
theorem v931_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 17 5) 1) 14) v931_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material931 : Material (10 : Basis) (17 : Basis) where
  plus := ![v931_pa,v931_pb,v931_pg]
  minus := ![(Primitive.Addresses.material931 1).one,v931_mb,v931_mg]
  upper := v931_upper
  lower := (Primitive.Addresses.material931 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v931_pa_checked.trans (by decide +kernel)
    · exact v931_pb_checked.trans (by decide +kernel)
    · exact v931_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 17 Primitive.Addresses.material931
    · exact v931_mb_checked.trans (by decide +kernel)
    · exact v931_mg_checked.trans (by decide +kernel)
  upper_error := v931_upper_checked
  lower_error := reuse_lower_error 10 17 Primitive.Addresses.material931

def v932_pa : Scalar.QComplex := ((999999999429806563026707257424 : Int)/10^30,(-33769614650177234878276413 : Int)/10^30)
theorem v932_pa_checked : Scalar.distance (sourceCoefficient 10 18 1 0) v932_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v932_pb : Scalar.QComplex := ((-14570829566547641880025 : Int)/10^30,(-431477519337431279344013881 : Int)/10^30)
theorem v932_pb_checked : Scalar.distance (sourceCoefficient 10 18 1 1) v932_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v932_pg : Scalar.QComplex := ((-93086429691026746554611 : Int)/10^30,(3143492861619188955 : Int)/10^30)
theorem v932_pg_checked : Scalar.distance (sourceCoefficient 10 18 1 2) v932_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v932_mb : Scalar.QComplex := ((-386916490303281947951510 : Int)/10^30,(-431477346104661663093794505 : Int)/10^30)
theorem v932_mb_checked : Scalar.distance (sourceCoefficient 10 18 3 1) v932_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v932_mg : Scalar.QComplex := ((-93086392318001950669283 : Int)/10^30,(83472888057347255651 : Int)/10^30)
theorem v932_mg_checked : Scalar.distance (sourceCoefficient 10 18 3 2) v932_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v932_upper : Scalar.QComplex := ((999998451763984333261448208069 : Int)/10^30,(-1759678844078861140175229852 : Int)/10^30)
theorem v932_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 18 5) 1) 14) v932_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material932 : Material (10 : Basis) (18 : Basis) where
  plus := ![v932_pa,v932_pb,v932_pg]
  minus := ![(Primitive.Addresses.material932 1).one,v932_mb,v932_mg]
  upper := v932_upper
  lower := (Primitive.Addresses.material932 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v932_pa_checked.trans (by decide +kernel)
    · exact v932_pb_checked.trans (by decide +kernel)
    · exact v932_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 18 Primitive.Addresses.material932
    · exact v932_mb_checked.trans (by decide +kernel)
    · exact v932_mg_checked.trans (by decide +kernel)
  upper_error := v932_upper_checked
  lower_error := reuse_lower_error 10 18 Primitive.Addresses.material932

def v933_pa : Scalar.QComplex := ((999999998778769214294468104112 : Int)/10^30,(-49421266373087397443704441 : Int)/10^30)
theorem v933_pa_checked : Scalar.distance (sourceCoefficient 10 19 1 0) v933_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v933_pb : Scalar.QComplex := ((-21324165412844521496430 : Int)/10^30,(-431477518722890864410395469 : Int)/10^30)
theorem v933_pb_checked : Scalar.distance (sourceCoefficient 10 19 1 1) v933_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v933_pg : Scalar.QComplex := ((-93086429594435278818733 : Int)/10^30,(4600449238324442027 : Int)/10^30)
theorem v933_pg_checked : Scalar.distance (sourceCoefficient 10 19 1 2) v933_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v933_mb : Scalar.QComplex := ((-393669823104682549081278 : Int)/10^30,(-431477339662296800583057394 : Int)/10^30)
theorem v933_mb_checked : Scalar.distance (sourceCoefficient 10 19 3 1) v933_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v933_mg : Scalar.QComplex := ((-93086390964122784681509 : Int)/10^30,(84929843808206977142 : Int)/10^30)
theorem v933_mg_checked : Scalar.distance (sourceCoefficient 10 19 3 2) v933_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v933_upper : Scalar.QComplex := ((999998424099616987182522737804 : Int)/10^30,(-1775330471366843231365062055 : Int)/10^30)
theorem v933_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 19 5) 1) 14) v933_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material933 : Material (10 : Basis) (19 : Basis) where
  plus := ![v933_pa,v933_pb,v933_pg]
  minus := ![(Primitive.Addresses.material933 1).one,v933_mb,v933_mg]
  upper := v933_upper
  lower := (Primitive.Addresses.material933 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v933_pa_checked.trans (by decide +kernel)
    · exact v933_pb_checked.trans (by decide +kernel)
    · exact v933_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 19 Primitive.Addresses.material933
    · exact v933_mb_checked.trans (by decide +kernel)
    · exact v933_mg_checked.trans (by decide +kernel)
  upper_error := v933_upper_checked
  lower_error := reuse_lower_error 10 19 Primitive.Addresses.material933

def v934_pa : Scalar.QComplex := ((999999998636185930231013069634 : Int)/10^30,(-52226699471419645166509600 : Int)/10^30)
theorem v934_pa_checked : Scalar.distance (sourceCoefficient 10 20 1 0) v934_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v934_pb : Scalar.QComplex := ((-22534646723216588555046 : Int)/10^30,(-431477518597844783985439070 : Int)/10^30)
theorem v934_pb_checked : Scalar.distance (sourceCoefficient 10 20 1 1) v934_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v934_pg : Scalar.QComplex := ((-93086429574310350612674 : Int)/10^30,(4861596988875290789 : Int)/10^30)
theorem v934_pg_checked : Scalar.distance (sourceCoefficient 10 20 1 2) v934_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v934_mb : Scalar.QComplex := ((-394880303856427967019201 : Int)/10^30,(-431477338492659913921791602 : Int)/10^30)
theorem v934_mb_checked : Scalar.distance (sourceCoefficient 10 20 3 1) v934_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v934_mg : Scalar.QComplex := ((-93086390718639116901569 : Int)/10^30,(85190991444153676683 : Int)/10^30)
theorem v934_mg_checked : Scalar.distance (sourceCoefficient 10 20 3 2) v934_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v934_upper : Scalar.QComplex := ((999998419115110894661242619388 : Int)/10^30,(-1778135900040726615204255293 : Int)/10^30)
theorem v934_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 20 5) 1) 14) v934_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material934 : Material (10 : Basis) (20 : Basis) where
  plus := ![v934_pa,v934_pb,v934_pg]
  minus := ![(Primitive.Addresses.material934 1).one,v934_mb,v934_mg]
  upper := v934_upper
  lower := (Primitive.Addresses.material934 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v934_pa_checked.trans (by decide +kernel)
    · exact v934_pb_checked.trans (by decide +kernel)
    · exact v934_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 20 Primitive.Addresses.material934
    · exact v934_mb_checked.trans (by decide +kernel)
    · exact v934_mg_checked.trans (by decide +kernel)
  upper_error := v934_upper_checked
  lower_error := reuse_lower_error 10 20 Primitive.Addresses.material934

def v935_pa : Scalar.QComplex := ((999999994462742440223252040881 : Int)/10^30,(-105235521991826859731196519 : Int)/10^30)
theorem v935_pa_checked : Scalar.distance (sourceCoefficient 10 21 1 0) v935_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v935_pb : Scalar.QComplex := ((-45406761810604017112237 : Int)/10^30,(-431477515384031717612962993 : Int)/10^30)
theorem v935_pb_checked : Scalar.distance (sourceCoefficient 10 21 1 1) v935_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v935_pg : Scalar.QComplex := ((-93086429033392834577944 : Int)/10^30,(9795999003927211476 : Int)/10^30)
theorem v935_pg_checked : Scalar.distance (sourceCoefficient 10 21 1 2) v935_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v935_mb : Scalar.QComplex := ((-417752407654105709731215 : Int)/10^30,(-431477315541242845607064158 : Int)/10^30)
theorem v935_mb_checked : Scalar.distance (sourceCoefficient 10 21 3 1) v935_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v935_mg : Scalar.QComplex := ((-93086385919555100502268 : Int)/10^30,(90125391155114759537 : Int)/10^30)
theorem v935_mg_checked : Scalar.distance (sourceCoefficient 10 21 3 2) v935_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v935_upper : Scalar.QComplex := ((999998323453254873098268349396 : Int)/10^30,(-1831144636407734687410723464 : Int)/10^30)
theorem v935_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 21 5) 1) 14) v935_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material935 : Material (10 : Basis) (21 : Basis) where
  plus := ![v935_pa,v935_pb,v935_pg]
  minus := ![(Primitive.Addresses.material935 1).one,v935_mb,v935_mg]
  upper := v935_upper
  lower := (Primitive.Addresses.material935 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v935_pa_checked.trans (by decide +kernel)
    · exact v935_pb_checked.trans (by decide +kernel)
    · exact v935_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 21 Primitive.Addresses.material935
    · exact v935_mb_checked.trans (by decide +kernel)
    · exact v935_mg_checked.trans (by decide +kernel)
  upper_error := v935_upper_checked
  lower_error := reuse_lower_error 10 21 Primitive.Addresses.material935

def v936_pa : Scalar.QComplex := ((999999994315062045636906613806 : Int)/10^30,(-106629620070633597036361459 : Int)/10^30)
theorem v936_pa_checked : Scalar.distance (sourceCoefficient 10 22 1 0) v936_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v936_pb : Scalar.QComplex := ((-46008283784635766566840 : Int)/10^30,(-431477515277694124016206527 : Int)/10^30)
theorem v936_pb_checked : Scalar.distance (sourceCoefficient 10 22 1 1) v936_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v936_pg : Scalar.QComplex := ((-93086429015048743412450 : Int)/10^30,(9925770616034041210 : Int)/10^30)
theorem v936_pg_checked : Scalar.distance (sourceCoefficient 10 22 1 2) v936_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v936_mb : Scalar.QComplex := ((-418353929312398783334934 : Int)/10^30,(-431477314915818919559278879 : Int)/10^30)
theorem v936_mb_checked : Scalar.distance (sourceCoefficient 10 22 3 1) v936_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v936_mg : Scalar.QComplex := ((-93086385789223959615368 : Int)/10^30,(90255162703071562739 : Int)/10^30)
theorem v936_mg_checked : Scalar.distance (sourceCoefficient 10 22 3 2) v936_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v936_upper : Scalar.QComplex := ((999998320899487886033861816809 : Int)/10^30,(-1832538732155313135001970893 : Int)/10^30)
theorem v936_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 22 5) 1) 14) v936_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material936 : Material (10 : Basis) (22 : Basis) where
  plus := ![v936_pa,v936_pb,v936_pg]
  minus := ![(Primitive.Addresses.material936 1).one,v936_mb,v936_mg]
  upper := v936_upper
  lower := (Primitive.Addresses.material936 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v936_pa_checked.trans (by decide +kernel)
    · exact v936_pb_checked.trans (by decide +kernel)
    · exact v936_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 22 Primitive.Addresses.material936
    · exact v936_mb_checked.trans (by decide +kernel)
    · exact v936_mg_checked.trans (by decide +kernel)
  upper_error := v936_upper_checked
  lower_error := reuse_lower_error 10 22 Primitive.Addresses.material936

def v937_pa : Scalar.QComplex := ((999999993162709147885037375135 : Int)/10^30,(-116938366918139313706223509 : Int)/10^30)
theorem v937_pa_checked : Scalar.distance (sourceCoefficient 10 23 1 0) v937_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v937_pb : Scalar.QComplex := ((-50456276247445218997738 : Int)/10^30,(-431477514456671251729136859 : Int)/10^30)
theorem v937_pb_checked : Scalar.distance (sourceCoefficient 10 23 1 1) v937_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v937_pg : Scalar.QComplex := ((-93086428872851302538617 : Int)/10^30,(10885375049059238245 : Int)/10^30)
theorem v937_pg_checked : Scalar.distance (sourceCoefficient 10 23 1 2) v937_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v937_mb : Scalar.QComplex := ((-422801919410511597277681 : Int)/10^30,(-431477310256379187715910149 : Int)/10^30)
theorem v937_mb_checked : Scalar.distance (sourceCoefficient 10 23 3 1) v937_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v937_mg : Scalar.QComplex := ((-93086384818931164966695 : Int)/10^30,(91214766656082186131 : Int)/10^30)
theorem v937_mg_checked : Scalar.distance (sourceCoefficient 10 23 3 2) v937_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v937_upper : Scalar.QComplex := ((999998301955174847990008900641 : Int)/10^30,(-1842847461660294811899937998 : Int)/10^30)
theorem v937_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 23 5) 1) 14) v937_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material937 : Material (10 : Basis) (23 : Basis) where
  plus := ![v937_pa,v937_pb,v937_pg]
  minus := ![(Primitive.Addresses.material937 1).one,v937_mb,v937_mg]
  upper := v937_upper
  lower := (Primitive.Addresses.material937 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v937_pa_checked.trans (by decide +kernel)
    · exact v937_pb_checked.trans (by decide +kernel)
    · exact v937_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 23 Primitive.Addresses.material937
    · exact v937_mb_checked.trans (by decide +kernel)
    · exact v937_mg_checked.trans (by decide +kernel)
  upper_error := v937_upper_checked
  lower_error := reuse_lower_error 10 23 Primitive.Addresses.material937

def v938_pa : Scalar.QComplex := ((999999985907423628891303700732 : Int)/10^30,(-167884342758985966800124817 : Int)/10^30)
theorem v938_pa_checked : Scalar.distance (sourceCoefficient 10 24 1 0) v938_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v938_pb : Scalar.QComplex := ((-72438319118785161535722 : Int)/10^30,(-431477509501495037923172543 : Int)/10^30)
theorem v938_pb_checked : Scalar.distance (sourceCoefficient 10 24 1 1) v938_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v938_pg : Scalar.QComplex := ((-93086428000655178445020 : Int)/10^30,(15627754004906979577 : Int)/10^30)
theorem v938_pg_checked : Scalar.distance (sourceCoefficient 10 24 1 2) v938_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v938_mb : Scalar.QComplex := ((-444783949820838450164463 : Int)/10^30,(-431477286331691855441261059 : Int)/10^30)
theorem v938_mb_checked : Scalar.distance (sourceCoefficient 10 24 3 1) v938_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v938_mg : Scalar.QComplex := ((-93086379854275915554358 : Int)/10^30,(95957143093459531938 : Int)/10^30)
theorem v938_mg_checked : Scalar.distance (sourceCoefficient 10 24 3 2) v938_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v938_upper : Scalar.QComplex := ((999998206771767616415362297902 : Int)/10^30,(-1893793349101130373343216824 : Int)/10^30)
theorem v938_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 24 5) 1) 14) v938_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material938 : Material (10 : Basis) (24 : Basis) where
  plus := ![v938_pa,v938_pb,v938_pg]
  minus := ![(Primitive.Addresses.material938 1).one,v938_mb,v938_mg]
  upper := v938_upper
  lower := (Primitive.Addresses.material938 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v938_pa_checked.trans (by decide +kernel)
    · exact v938_pb_checked.trans (by decide +kernel)
    · exact v938_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 24 Primitive.Addresses.material938
    · exact v938_mb_checked.trans (by decide +kernel)
    · exact v938_mg_checked.trans (by decide +kernel)
  upper_error := v938_upper_checked
  lower_error := reuse_lower_error 10 24 Primitive.Addresses.material938

def v939_pa : Scalar.QComplex := ((999999981784573045390015157233 : Int)/10^30,(-190868681499658792364009225 : Int)/10^30)
theorem v939_pa_checked : Scalar.distance (sourceCoefficient 10 25 1 0) v939_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v939_pb : Scalar.QComplex := ((-82355544315460352701316 : Int)/10^30,(-431477506777172211649466649 : Int)/10^30)
theorem v939_pb_checked : Scalar.distance (sourceCoefficient 10 25 1 1) v939_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v939_pg : Scalar.QComplex := ((-93086427514893429658219 : Int)/10^30,(17767284008919932778 : Int)/10^30)
theorem v939_pg_checked : Scalar.distance (sourceCoefficient 10 25 1 2) v939_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v939_mb : Scalar.QComplex := ((-454701168973909560896993 : Int)/10^30,(-431477275049251354068997395 : Int)/10^30)
theorem v939_mb_checked : Scalar.distance (sourceCoefficient 10 25 3 1) v939_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v939_mg : Scalar.QComplex := ((-93086377522196315029975 : Int)/10^30,(98096671881637171987 : Int)/10^30)
theorem v939_mg_checked : Scalar.distance (sourceCoefficient 10 25 3 2) v939_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v939_upper : Scalar.QComplex := ((999998162980039629936884338663 : Int)/10^30,(-1916777646493664489723162393 : Int)/10^30)
theorem v939_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 25 5) 1) 14) v939_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material939 : Material (10 : Basis) (25 : Basis) where
  plus := ![v939_pa,v939_pb,v939_pg]
  minus := ![(Primitive.Addresses.material939 1).one,v939_mb,v939_mg]
  upper := v939_upper
  lower := (Primitive.Addresses.material939 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v939_pa_checked.trans (by decide +kernel)
    · exact v939_pb_checked.trans (by decide +kernel)
    · exact v939_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 25 Primitive.Addresses.material939
    · exact v939_mb_checked.trans (by decide +kernel)
    · exact v939_mg_checked.trans (by decide +kernel)
  upper_error := v939_upper_checked
  lower_error := reuse_lower_error 10 25 Primitive.Addresses.material939

def v940_pa : Scalar.QComplex := ((999999980355879983403384801536 : Int)/10^30,(-198212612230659477705868223 : Int)/10^30)
theorem v940_pa_checked : Scalar.distance (sourceCoefficient 10 26 1 0) v940_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v940_pb : Scalar.QComplex := ((-85524285231886906205021 : Int)/10^30,(-431477505842631278360335592 : Int)/10^30)
theorem v940_pb_checked : Scalar.distance (sourceCoefficient 10 26 1 1) v940_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v940_pg : Scalar.QComplex := ((-93086427347589105610165 : Int)/10^30,(18450904290236913531 : Int)/10^30)
theorem v940_pg_checked : Scalar.distance (sourceCoefficient 10 26 1 2) v940_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v940_mb : Scalar.QComplex := ((-457869907904002317333682 : Int)/10^30,(-431477271380230072669104466 : Int)/10^30)
theorem v940_mb_checked : Scalar.distance (sourceCoefficient 10 26 3 1) v940_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v940_mg : Scalar.QComplex := ((-93086376764958539614938 : Int)/10^30,(98780291764034982469 : Int)/10^30)
theorem v940_mg_checked : Scalar.distance (sourceCoefficient 10 26 3 2) v940_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v940_upper : Scalar.QComplex := ((999998148876390490305125695912 : Int)/10^30,(-1924121563820948414976239133 : Int)/10^30)
theorem v940_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 26 5) 1) 14) v940_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material940 : Material (10 : Basis) (26 : Basis) where
  plus := ![v940_pa,v940_pb,v940_pg]
  minus := ![(Primitive.Addresses.material940 1).one,v940_mb,v940_mg]
  upper := v940_upper
  lower := (Primitive.Addresses.material940 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v940_pa_checked.trans (by decide +kernel)
    · exact v940_pb_checked.trans (by decide +kernel)
    · exact v940_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 26 Primitive.Addresses.material940
    · exact v940_mb_checked.trans (by decide +kernel)
    · exact v940_mg_checked.trans (by decide +kernel)
  upper_error := v940_upper_checked
  lower_error := reuse_lower_error 10 26 Primitive.Addresses.material940

def v941_pa : Scalar.QComplex := ((999999979343123885763254259661 : Int)/10^30,(-203257845609380994151563209 : Int)/10^30)
theorem v941_pa_checked : Scalar.distance (sourceCoefficient 10 27 1 0) v941_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v941_pb : Scalar.QComplex := ((-87701189943964028602283 : Int)/10^30,(-431477505182627621563370855 : Int)/10^30)
theorem v941_pb_checked : Scalar.distance (sourceCoefficient 10 27 1 1) v941_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v941_pg : Scalar.QComplex := ((-93086427229257992280357 : Int)/10^30,(18920547044932796348 : Int)/10^30)
theorem v941_pg_checked : Scalar.distance (sourceCoefficient 10 27 1 2) v941_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v941_mb : Scalar.QComplex := ((-460046811235964895609871 : Int)/10^30,(-431477268841655939247770258 : Int)/10^30)
theorem v941_mb_checked : Scalar.distance (sourceCoefficient 10 27 3 1) v941_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v941_mg : Scalar.QComplex := ((-93086376241346924967140 : Int)/10^30,(99249934241746982610 : Int)/10^30)
theorem v941_mg_checked : Scalar.distance (sourceCoefficient 10 27 3 2) v941_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v941_upper : Scalar.QComplex := ((999998139156020789369659966624 : Int)/10^30,(-1929166787937462320549237785 : Int)/10^30)
theorem v941_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 27 5) 1) 14) v941_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material941 : Material (10 : Basis) (27 : Basis) where
  plus := ![v941_pa,v941_pb,v941_pg]
  minus := ![(Primitive.Addresses.material941 1).one,v941_mb,v941_mg]
  upper := v941_upper
  lower := (Primitive.Addresses.material941 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v941_pa_checked.trans (by decide +kernel)
    · exact v941_pb_checked.trans (by decide +kernel)
    · exact v941_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 27 Primitive.Addresses.material941
    · exact v941_mb_checked.trans (by decide +kernel)
    · exact v941_mg_checked.trans (by decide +kernel)
  upper_error := v941_upper_checked
  lower_error := reuse_lower_error 10 27 Primitive.Addresses.material941

def v942_pa : Scalar.QComplex := ((999999977938567971812662824011 : Int)/10^30,(-210054430016764681462246466 : Int)/10^30)
theorem v942_pa_checked : Scalar.distance (sourceCoefficient 10 28 1 0) v942_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v942_pb : Scalar.QComplex := ((-90633763224078416630450 : Int)/10^30,(-431477504270365670871120441 : Int)/10^30)
theorem v942_pb_checked : Scalar.distance (sourceCoefficient 10 28 1 1) v942_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v942_pg : Scalar.QComplex := ((-93086427065480308842534 : Int)/10^30,(19553216810908566855 : Int)/10^30)
theorem v942_pg_checked : Scalar.distance (sourceCoefficient 10 28 1 2) v942_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v942_mb : Scalar.QComplex := ((-462979382636907249537205 : Int)/10^30,(-431477265398715665691182842 : Int)/10^30)
theorem v942_mb_checked : Scalar.distance (sourceCoefficient 10 28 3 1) v942_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v942_mg : Scalar.QComplex := ((-93086375531603788862641 : Int)/10^30,(99882603630818120274 : Int)/10^30)
theorem v942_mg_checked : Scalar.distance (sourceCoefficient 10 28 3 2) v942_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v942_upper : Scalar.QComplex := ((999998126021178861516836223294 : Int)/10^30,(-1935963359797995828788188967 : Int)/10^30)
theorem v942_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 28 5) 1) 14) v942_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material942 : Material (10 : Basis) (28 : Basis) where
  plus := ![v942_pa,v942_pb,v942_pg]
  minus := ![(Primitive.Addresses.material942 1).one,v942_mb,v942_mg]
  upper := v942_upper
  lower := (Primitive.Addresses.material942 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v942_pa_checked.trans (by decide +kernel)
    · exact v942_pb_checked.trans (by decide +kernel)
    · exact v942_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 28 Primitive.Addresses.material942
    · exact v942_mb_checked.trans (by decide +kernel)
    · exact v942_mg_checked.trans (by decide +kernel)
  upper_error := v942_upper_checked
  lower_error := reuse_lower_error 10 28 Primitive.Addresses.material942

def v943_pa : Scalar.QComplex := ((999999974952351193335740024173 : Int)/10^30,(-223819786850813994804239727 : Int)/10^30)
theorem v943_pa_checked : Scalar.distance (sourceCoefficient 10 29 1 0) v943_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v943_pb : Scalar.QComplex := ((-96573205023885869152035 : Int)/10^30,(-431477502341312434927400158 : Int)/10^30)
theorem v943_pb_checked : Scalar.distance (sourceCoefficient 10 29 1 1) v943_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v943_pg : Scalar.QComplex := ((-93086426718406393125280 : Int)/10^30,(20834584708674996564 : Int)/10^30)
theorem v943_pg_checked : Scalar.distance (sourceCoefficient 10 29 1 2) v943_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v943_mb : Scalar.QComplex := ((-468918820560503012803655 : Int)/10^30,(-431477258344192377316815561 : Int)/10^30)
theorem v943_mb_checked : Scalar.distance (sourceCoefficient 10 29 3 1) v943_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v943_mg : Scalar.QComplex := ((-93086374078767217272234 : Int)/10^30,(101163970751963562604 : Int)/10^30)
theorem v943_mg_checked : Scalar.distance (sourceCoefficient 10 29 3 2) v943_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v943_upper : Scalar.QComplex := ((999998099277209418506928708867 : Int)/10^30,(-1949728690976223878033740046 : Int)/10^30)
theorem v943_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 29 5) 1) 14) v943_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material943 : Material (10 : Basis) (29 : Basis) where
  plus := ![v943_pa,v943_pb,v943_pg]
  minus := ![(Primitive.Addresses.material943 1).one,v943_mb,v943_mg]
  upper := v943_upper
  lower := (Primitive.Addresses.material943 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v943_pa_checked.trans (by decide +kernel)
    · exact v943_pb_checked.trans (by decide +kernel)
    · exact v943_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 29 Primitive.Addresses.material943
    · exact v943_mb_checked.trans (by decide +kernel)
    · exact v943_mg_checked.trans (by decide +kernel)
  upper_error := v943_upper_checked
  lower_error := reuse_lower_error 10 29 Primitive.Addresses.material943

def v944_pa : Scalar.QComplex := ((999999973771235693478924031008 : Int)/10^30,(-229036084329727561143225290 : Int)/10^30)
theorem v944_pa_checked : Scalar.distance (sourceCoefficient 10 30 1 0) v944_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v944_pb : Scalar.QComplex := ((-98823920030705025992813 : Int)/10^30,(-431477501581828020497484235 : Int)/10^30)
theorem v944_pb_checked : Scalar.distance (sourceCoefficient 10 30 1 1) v944_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v944_pg : Scalar.QComplex := ((-93086426581508363780417 : Int)/10^30,(21320151207676563871 : Int)/10^30)
theorem v944_pg_checked : Scalar.distance (sourceCoefficient 10 30 1 2) v944_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v944_mb : Scalar.QComplex := ((-471169534073877266103551 : Int)/10^30,(-431477255642442563233658656 : Int)/10^30)
theorem v944_mb_checked : Scalar.distance (sourceCoefficient 10 30 3 1) v944_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v944_mg : Scalar.QComplex := ((-93086373522847219365707 : Int)/10^30,(101649536952029697181 : Int)/10^30)
theorem v944_mg_checked : Scalar.distance (sourceCoefficient 10 30 3 2) v944_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v944_upper : Scalar.QComplex := ((999998089093239447988795230537 : Int)/10^30,(-1954944978647576896084408631 : Int)/10^30)
theorem v944_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 30 5) 1) 14) v944_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material944 : Material (10 : Basis) (30 : Basis) where
  plus := ![v944_pa,v944_pb,v944_pg]
  minus := ![(Primitive.Addresses.material944 1).one,v944_mb,v944_mg]
  upper := v944_upper
  lower := (Primitive.Addresses.material944 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v944_pa_checked.trans (by decide +kernel)
    · exact v944_pb_checked.trans (by decide +kernel)
    · exact v944_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 30 Primitive.Addresses.material944
    · exact v944_mb_checked.trans (by decide +kernel)
    · exact v944_mg_checked.trans (by decide +kernel)
  upper_error := v944_upper_checked
  lower_error := reuse_lower_error 10 30 Primitive.Addresses.material944

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
