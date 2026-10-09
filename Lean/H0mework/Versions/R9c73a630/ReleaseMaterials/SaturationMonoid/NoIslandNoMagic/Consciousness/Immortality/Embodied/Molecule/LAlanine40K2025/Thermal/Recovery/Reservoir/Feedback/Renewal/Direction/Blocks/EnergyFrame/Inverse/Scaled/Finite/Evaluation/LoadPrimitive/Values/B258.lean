import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B172

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4129_pa : Scalar.QComplex := ((999998670798700206143110037775 : Int)/10^30,(-1630460313166689257286461932 : Int)/10^30)
theorem v4129_pa_checked : Scalar.distance (sourceCoefficient 62 69 1 0) v4129_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4129_pb : Scalar.QComplex := ((-703506968640599855326370 : Int)/10^30,(-431476944183860151916916939 : Int)/10^30)
theorem v4129_pb_checked : Scalar.distance (sourceCoefficient 62 69 1 1) v4129_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4129_pg : Scalar.QComplex := ((-93086305810801424011334 : Int)/10^30,(151773729061647439056 : Int)/10^30)
theorem v4129_pg_checked : Scalar.distance (sourceCoefficient 62 69 1 2) v4129_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4129_mb : Scalar.QComplex := ((-1075851876523295719409662 : Int)/10^30,(-431476176430445202590634726 : Int)/10^30)
theorem v4129_mb_checked : Scalar.distance (sourceCoefficient 62 69 3 1) v4129_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4129_mg : Scalar.QComplex := ((-93086140176622971114480 : Int)/10^30,(232102962012490735998 : Int)/10^30)
theorem v4129_mg_checked : Scalar.distance (sourceCoefficient 62 69 3 2) v4129_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4129_upper : Scalar.QComplex := ((999994367391561825497291844372 : Int)/10^30,(-3356364871415381087530160994 : Int)/10^30)
theorem v4129_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 69 5) 1) 14) v4129_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4129 : Material (62 : Basis) (69 : Basis) where
  plus := ![v4129_pa,v4129_pb,v4129_pg]
  minus := ![(Primitive.Addresses.material4129 1).one,v4129_mb,v4129_mg]
  upper := v4129_upper
  lower := (Primitive.Addresses.material4129 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4129_pa_checked.trans (by decide +kernel)
    · exact v4129_pb_checked.trans (by decide +kernel)
    · exact v4129_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 69 Primitive.Addresses.material4129
    · exact v4129_mb_checked.trans (by decide +kernel)
    · exact v4129_mg_checked.trans (by decide +kernel)
  upper_error := v4129_upper_checked
  lower_error := reuse_lower_error 62 69 Primitive.Addresses.material4129

def v4130_pa : Scalar.QComplex := ((999998647492769901542278248582 : Int)/10^30,(-1644692260248435648027751542 : Int)/10^30)
theorem v4130_pa_checked : Scalar.distance (sourceCoefficient 62 70 1 0) v4130_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4130_pb : Scalar.QComplex := ((-709647733094803772724237 : Int)/10^30,(-431476933675069211668186112 : Int)/10^30)
theorem v4130_pb_checked : Scalar.distance (sourceCoefficient 62 70 1 1) v4130_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4130_pg : Scalar.QComplex := ((-93086303592491681981262 : Int)/10^30,(153098530120576125150 : Int)/10^30)
theorem v4130_pg_checked : Scalar.distance (sourceCoefficient 62 70 1 2) v4130_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4130_mb : Scalar.QComplex := ((-1081992629622399100647253 : Int)/10^30,(-431476160622455021031330812 : Int)/10^30)
theorem v4130_mb_checked : Scalar.distance (sourceCoefficient 62 70 3 1) v4130_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4130_mg : Scalar.QComplex := ((-93086136815070408031808 : Int)/10^30,(233427760663834043043 : Int)/10^30)
theorem v4130_mg_checked : Scalar.distance (sourceCoefficient 62 70 3 2) v4130_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4130_upper : Scalar.QComplex := ((999994319522616681401312822283 : Int)/10^30,(-3370596757076392693692316886 : Int)/10^30)
theorem v4130_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 70 5) 1) 14) v4130_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4130 : Material (62 : Basis) (70 : Basis) where
  plus := ![v4130_pa,v4130_pb,v4130_pg]
  minus := ![(Primitive.Addresses.material4130 1).one,v4130_mb,v4130_mg]
  upper := v4130_upper
  lower := (Primitive.Addresses.material4130 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4130_pa_checked.trans (by decide +kernel)
    · exact v4130_pb_checked.trans (by decide +kernel)
    · exact v4130_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 70 Primitive.Addresses.material4130
    · exact v4130_mb_checked.trans (by decide +kernel)
    · exact v4130_mg_checked.trans (by decide +kernel)
  upper_error := v4130_upper_checked
  lower_error := reuse_lower_error 62 70 Primitive.Addresses.material4130

def v4131_pa : Scalar.QComplex := ((999998607243492548313716383292 : Int)/10^30,(-1668985043411918511436495009 : Int)/10^30)
theorem v4131_pa_checked : Scalar.distance (sourceCoefficient 62 71 1 0) v4131_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4131_pb : Scalar.QComplex := ((-720129521459022204197810 : Int)/10^30,(-431476915468206299160345354 : Int)/10^30)
theorem v4131_pb_checked : Scalar.distance (sourceCoefficient 62 71 1 1) v4131_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4131_pg : Scalar.QComplex := ((-93086299755197805196090 : Int)/10^30,(155359858416437474675 : Int)/10^30)
theorem v4131_pg_checked : Scalar.distance (sourceCoefficient 62 71 1 2) v4131_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4131_mb : Scalar.QComplex := ((-1092474398372065995900169 : Int)/10^30,(-431476133370287611673549279 : Int)/10^30)
theorem v4131_mb_checked : Scalar.distance (sourceCoefficient 62 71 3 1) v4131_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4131_mg : Scalar.QComplex := ((-93086131026353487163902 : Int)/10^30,(235689084806287729845 : Int)/10^30)
theorem v4131_mg_checked : Scalar.distance (sourceCoefficient 62 71 3 2) v4131_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4131_upper : Scalar.QComplex := ((999994237346259358645196359387 : Int)/10^30,(-3394889434592027340106271803 : Int)/10^30)
theorem v4131_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 71 5) 1) 14) v4131_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4131 : Material (62 : Basis) (71 : Basis) where
  plus := ![v4131_pa,v4131_pb,v4131_pg]
  minus := ![(Primitive.Addresses.material4131 1).one,v4131_mb,v4131_mg]
  upper := v4131_upper
  lower := (Primitive.Addresses.material4131 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4131_pa_checked.trans (by decide +kernel)
    · exact v4131_pb_checked.trans (by decide +kernel)
    · exact v4131_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 71 Primitive.Addresses.material4131
    · exact v4131_mb_checked.trans (by decide +kernel)
    · exact v4131_mg_checked.trans (by decide +kernel)
  upper_error := v4131_upper_checked
  lower_error := reuse_lower_error 62 71 Primitive.Addresses.material4131

def v4132_pa : Scalar.QComplex := ((999998562897170221331887857204 : Int)/10^30,(-1695347632284539118744318486 : Int)/10^30)
theorem v4132_pa_checked : Scalar.distance (sourceCoefficient 62 72 1 0) v4132_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4132_pb : Scalar.QComplex := ((-731504384123336672781000 : Int)/10^30,(-431476895325939971040386142 : Int)/10^30)
theorem v4132_pb_checked : Scalar.distance (sourceCoefficient 62 72 1 1) v4132_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4132_pg : Scalar.QComplex := ((-93086295518443506937711 : Int)/10^30,(157813857500073295949 : Int)/10^30)
theorem v4132_pg_checked : Scalar.distance (sourceCoefficient 62 72 1 2) v4132_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4132_mb : Scalar.QComplex := ((-1103849239419130570485883 : Int)/10^30,(-431476103412034608933257422 : Int)/10^30)
theorem v4132_mb_checked : Scalar.distance (sourceCoefficient 62 72 3 1) v4132_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4132_mg : Scalar.QComplex := ((-93086124671910081280946 : Int)/10^30,(238143079320059395917 : Int)/10^30)
theorem v4132_mg_checked : Scalar.distance (sourceCoefficient 62 72 3 2) v4132_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4132_upper : Scalar.QComplex := ((999994147500566281538426980927 : Int)/10^30,(-3421251907662939319435105023 : Int)/10^30)
theorem v4132_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 72 5) 1) 14) v4132_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4132 : Material (62 : Basis) (72 : Basis) where
  plus := ![v4132_pa,v4132_pb,v4132_pg]
  minus := ![(Primitive.Addresses.material4132 1).one,v4132_mb,v4132_mg]
  upper := v4132_upper
  lower := (Primitive.Addresses.material4132 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4132_pa_checked.trans (by decide +kernel)
    · exact v4132_pb_checked.trans (by decide +kernel)
    · exact v4132_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 72 Primitive.Addresses.material4132
    · exact v4132_mb_checked.trans (by decide +kernel)
    · exact v4132_mg_checked.trans (by decide +kernel)
  upper_error := v4132_upper_checked
  lower_error := reuse_lower_error 62 72 Primitive.Addresses.material4132

def v4133_pa : Scalar.QComplex := ((999998546832093153722959129031 : Int)/10^30,(-1704797261258824463434200553 : Int)/10^30)
theorem v4133_pa_checked : Scalar.distance (sourceCoefficient 62 73 1 0) v4133_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4133_pb : Scalar.QComplex := ((-735581685897293068669391 : Int)/10^30,(-431476888008630772208465128 : Int)/10^30)
theorem v4133_pb_checked : Scalar.distance (sourceCoefficient 62 73 1 1) v4133_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4133_pg : Scalar.QComplex := ((-93086293981409526977501 : Int)/10^30,(158693489648526939285 : Int)/10^30)
theorem v4133_pg_checked : Scalar.distance (sourceCoefficient 62 73 1 2) v4133_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4133_mb : Scalar.QComplex := ((-1107926533360412894814310 : Int)/10^30,(-431476092576200338600651780 : Int)/10^30)
theorem v4133_mb_checked : Scalar.distance (sourceCoefficient 62 73 3 1) v4133_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4133_mg : Scalar.QComplex := ((-93086122375793746674547 : Int)/10^30,(239022709814594689942 : Int)/10^30)
theorem v4133_mg_checked : Scalar.distance (sourceCoefficient 62 73 3 2) v4133_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4133_upper : Scalar.QComplex := ((999994115126310795002120082137 : Int)/10^30,(-3430701494836246732035619865 : Int)/10^30)
theorem v4133_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 73 5) 1) 14) v4133_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4133 : Material (62 : Basis) (73 : Basis) where
  plus := ![v4133_pa,v4133_pb,v4133_pg]
  minus := ![(Primitive.Addresses.material4133 1).one,v4133_mb,v4133_mg]
  upper := v4133_upper
  lower := (Primitive.Addresses.material4133 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4133_pa_checked.trans (by decide +kernel)
    · exact v4133_pb_checked.trans (by decide +kernel)
    · exact v4133_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 73 Primitive.Addresses.material4133
    · exact v4133_mb_checked.trans (by decide +kernel)
    · exact v4133_mg_checked.trans (by decide +kernel)
  upper_error := v4133_upper_checked
  lower_error := reuse_lower_error 62 73 Primitive.Addresses.material4133

def v4134_pa : Scalar.QComplex := ((999998528648160720394221782500 : Int)/10^30,(-1715430416450336992495452054 : Int)/10^30)
theorem v4134_pa_checked : Scalar.distance (sourceCoefficient 62 74 1 0) v4134_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4134_pb : Scalar.QComplex := ((-740169652505486101864508 : Int)/10^30,(-431476879713433102977809033 : Int)/10^30)
theorem v4134_pb_checked : Scalar.distance (sourceCoefficient 62 74 1 1) v4134_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4134_pg : Scalar.QComplex := ((-93086292240272978156679 : Int)/10^30,(159683292013854654570 : Int)/10^30)
theorem v4134_pg_checked : Scalar.distance (sourceCoefficient 62 74 1 2) v4134_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4134_mb : Scalar.QComplex := ((-1112514491101914292634957 : Int)/10^30,(-431476080321797209526015106 : Int)/10^30)
theorem v4134_mb_checked : Scalar.distance (sourceCoefficient 62 74 3 1) v4134_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4134_mg : Scalar.QComplex := ((-93086119780502983924301 : Int)/10^30,(240012510308851324661 : Int)/10^30)
theorem v4134_mg_checked : Scalar.distance (sourceCoefficient 62 74 3 2) v4134_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4134_upper : Scalar.QComplex := ((999994078590544216257762252265 : Int)/10^30,(-3441334602807105915028025375 : Int)/10^30)
theorem v4134_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 74 5) 1) 14) v4134_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4134 : Material (62 : Basis) (74 : Basis) where
  plus := ![v4134_pa,v4134_pb,v4134_pg]
  minus := ![(Primitive.Addresses.material4134 1).one,v4134_mb,v4134_mg]
  upper := v4134_upper
  lower := (Primitive.Addresses.material4134 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4134_pa_checked.trans (by decide +kernel)
    · exact v4134_pb_checked.trans (by decide +kernel)
    · exact v4134_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 74 Primitive.Addresses.material4134
    · exact v4134_mb_checked.trans (by decide +kernel)
    · exact v4134_mg_checked.trans (by decide +kernel)
  upper_error := v4134_upper_checked
  lower_error := reuse_lower_error 62 74 Primitive.Addresses.material4134

def v4135_pa : Scalar.QComplex := ((999998503124094050520242385153 : Int)/10^30,(-1730245523404548994746991458 : Int)/10^30)
theorem v4135_pa_checked : Scalar.distance (sourceCoefficient 62 75 1 0) v4135_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4135_pb : Scalar.QComplex := ((-746562036902245328099764 : Int)/10^30,(-431476868047336920829137223 : Int)/10^30)
theorem v4135_pb_checked : Scalar.distance (sourceCoefficient 62 75 1 1) v4135_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4135_pg : Scalar.QComplex := ((-93086289793886233538409 : Int)/10^30,(161062377296602143540 : Int)/10^30)
theorem v4135_pg_checked : Scalar.distance (sourceCoefficient 62 75 1 2) v4135_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4135_mb : Scalar.QComplex := ((-1118906863051181077830675 : Int)/10^30,(-431476063139365539100700681 : Int)/10^30)
theorem v4135_mb_checked : Scalar.distance (sourceCoefficient 62 75 3 1) v4135_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4135_mg : Scalar.QComplex := ((-93086116144028662891978 : Int)/10^30,(241391592966980756116 : Int)/10^30)
theorem v4135_mg_checked : Scalar.distance (sourceCoefficient 62 75 3 2) v4135_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4135_upper : Scalar.QComplex := ((999994027496984974516913509202 : Int)/10^30,(-3456149643643732866731279528 : Int)/10^30)
theorem v4135_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 75 5) 1) 14) v4135_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4135 : Material (62 : Basis) (75 : Basis) where
  plus := ![v4135_pa,v4135_pb,v4135_pg]
  minus := ![(Primitive.Addresses.material4135 1).one,v4135_mb,v4135_mg]
  upper := v4135_upper
  lower := (Primitive.Addresses.material4135 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4135_pa_checked.trans (by decide +kernel)
    · exact v4135_pb_checked.trans (by decide +kernel)
    · exact v4135_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 75 Primitive.Addresses.material4135
    · exact v4135_mb_checked.trans (by decide +kernel)
    · exact v4135_mg_checked.trans (by decide +kernel)
  upper_error := v4135_upper_checked
  lower_error := reuse_lower_error 62 75 Primitive.Addresses.material4135

def v4136_pa : Scalar.QComplex := ((999998481539567521120003706714 : Int)/10^30,(-1742675689632375341307523272 : Int)/10^30)
theorem v4136_pa_checked : Scalar.distance (sourceCoefficient 62 76 1 0) v4136_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4136_pb : Scalar.QComplex := ((-751925373126514163817895 : Int)/10^30,(-431476858161835279290224161 : Int)/10^30)
theorem v4136_pb_checked : Scalar.distance (sourceCoefficient 62 76 1 1) v4136_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4136_pg : Scalar.QComplex := ((-93086287722929990917095 : Int)/10^30,(162219456976701533321 : Int)/10^30)
theorem v4136_pg_checked : Scalar.distance (sourceCoefficient 62 76 1 2) v4136_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4136_mb : Scalar.QComplex := ((-1124270188747692030497334 : Int)/10^30,(-431476048625549972538405398 : Int)/10^30)
theorem v4136_mb_checked : Scalar.distance (sourceCoefficient 62 76 3 1) v4136_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4136_mg : Scalar.QComplex := ((-93086113074565540390816 : Int)/10^30,(242548670429104534867 : Int)/10^30)
theorem v4136_mg_checked : Scalar.distance (sourceCoefficient 62 76 3 2) v4136_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4136_upper : Scalar.QComplex := ((999993984459151339376593763282 : Int)/10^30,(-3468579754105352110045364479 : Int)/10^30)
theorem v4136_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 76 5) 1) 14) v4136_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4136 : Material (62 : Basis) (76 : Basis) where
  plus := ![v4136_pa,v4136_pb,v4136_pg]
  minus := ![(Primitive.Addresses.material4136 1).one,v4136_mb,v4136_mg]
  upper := v4136_upper
  lower := (Primitive.Addresses.material4136 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4136_pa_checked.trans (by decide +kernel)
    · exact v4136_pb_checked.trans (by decide +kernel)
    · exact v4136_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 76 Primitive.Addresses.material4136
    · exact v4136_mb_checked.trans (by decide +kernel)
    · exact v4136_mg_checked.trans (by decide +kernel)
  upper_error := v4136_upper_checked
  lower_error := reuse_lower_error 62 76 Primitive.Addresses.material4136

def v4137_pa : Scalar.QComplex := ((999998476520540581554051064444 : Int)/10^30,(-1745553378687466156499914564 : Int)/10^30)
theorem v4137_pa_checked : Scalar.distance (sourceCoefficient 62 77 1 0) v4137_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4137_pb : Scalar.QComplex := ((-753167031007392372672614 : Int)/10^30,(-431476855860586227239061472 : Int)/10^30)
theorem v4137_pb_checked : Scalar.distance (sourceCoefficient 62 77 1 1) v4137_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4137_pg : Scalar.QComplex := ((-93086287241094020720781 : Int)/10^30,(162487330749274452648 : Int)/10^30)
theorem v4137_pg_checked : Scalar.distance (sourceCoefficient 62 77 1 2) v4137_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4137_mb : Scalar.QComplex := ((-1125511844180369976222292 : Int)/10^30,(-431476045252806948344568119 : Int)/10^30)
theorem v4137_mb_checked : Scalar.distance (sourceCoefficient 62 77 3 1) v4137_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4137_mg : Scalar.QComplex := ((-93086112361566748460483 : Int)/10^30,(242816543686133065036 : Int)/10^30)
theorem v4137_mg_checked : Scalar.distance (sourceCoefficient 62 77 3 2) v4137_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4137_upper : Scalar.QComplex := ((999993974473501627886718360315 : Int)/10^30,(-3471457430212077939658547267 : Int)/10^30)
theorem v4137_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 77 5) 1) 14) v4137_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4137 : Material (62 : Basis) (77 : Basis) where
  plus := ![v4137_pa,v4137_pb,v4137_pg]
  minus := ![(Primitive.Addresses.material4137 1).one,v4137_mb,v4137_mg]
  upper := v4137_upper
  lower := (Primitive.Addresses.material4137 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4137_pa_checked.trans (by decide +kernel)
    · exact v4137_pb_checked.trans (by decide +kernel)
    · exact v4137_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 77 Primitive.Addresses.material4137
    · exact v4137_mb_checked.trans (by decide +kernel)
    · exact v4137_mg_checked.trans (by decide +kernel)
  upper_error := v4137_upper_checked
  lower_error := reuse_lower_error 62 77 Primitive.Addresses.material4137

def v4138_pa : Scalar.QComplex := ((999998446173546446586637110760 : Int)/10^30,(-1762852941322723880090368136 : Int)/10^30)
theorem v4138_pa_checked : Scalar.distance (sourceCoefficient 62 78 1 0) v4138_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4138_pb : Scalar.QComplex := ((-760631401790998625975748 : Int)/10^30,(-431476841925952369677239972 : Int)/10^30)
theorem v4138_pb_checked : Scalar.distance (sourceCoefficient 62 78 1 1) v4138_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4138_pg : Scalar.QComplex := ((-93086284325526961967150 : Int)/10^30,(164097685099382647438 : Int)/10^30)
theorem v4138_pg_checked : Scalar.distance (sourceCoefficient 62 78 1 2) v4138_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4138_mb : Scalar.QComplex := ((-1132976200159688421727178 : Int)/10^30,(-431476024876762475811981621 : Int)/10^30)
theorem v4138_mb_checked : Scalar.distance (sourceCoefficient 62 78 3 1) v4138_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4138_mg : Scalar.QComplex := ((-93086108056337498829919 : Int)/10^30,(244426894920629679012 : Int)/10^30)
theorem v4138_mg_checked : Scalar.distance (sourceCoefficient 62 78 3 2) v4138_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4138_upper : Scalar.QComplex := ((999993914269076986810188002944 : Int)/10^30,(-3488756914705510448258927288 : Int)/10^30)
theorem v4138_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 78 5) 1) 14) v4138_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4138 : Material (62 : Basis) (78 : Basis) where
  plus := ![v4138_pa,v4138_pb,v4138_pg]
  minus := ![(Primitive.Addresses.material4138 1).one,v4138_mb,v4138_mg]
  upper := v4138_upper
  lower := (Primitive.Addresses.material4138 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4138_pa_checked.trans (by decide +kernel)
    · exact v4138_pb_checked.trans (by decide +kernel)
    · exact v4138_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 78 Primitive.Addresses.material4138
    · exact v4138_mb_checked.trans (by decide +kernel)
    · exact v4138_mg_checked.trans (by decide +kernel)
  upper_error := v4138_upper_checked
  lower_error := reuse_lower_error 62 78 Primitive.Addresses.material4138

def v4139_pa : Scalar.QComplex := ((999998436326420786087461298400 : Int)/10^30,(-1768430013699372482394661780 : Int)/10^30)
theorem v4139_pa_checked : Scalar.distance (sourceCoefficient 62 79 1 0) v4139_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4139_pb : Scalar.QComplex := ((-763037782610912046007075 : Int)/10^30,(-431476837396973316630089869 : Int)/10^30)
theorem v4139_pb_checked : Scalar.distance (sourceCoefficient 62 79 1 1) v4139_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4139_pg : Scalar.QComplex := ((-93086283378671889527876 : Int)/10^30,(164616834797563665376 : Int)/10^30)
theorem v4139_pg_checked : Scalar.distance (sourceCoefficient 62 79 1 2) v4139_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4139_mb : Scalar.QComplex := ((-1135382576175291340333145 : Int)/10^30,(-431476018271186840894333662 : Int)/10^30)
theorem v4139_mb_checked : Scalar.distance (sourceCoefficient 62 79 3 1) v4139_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4139_mg : Scalar.QComplex := ((-93086106661479971052283 : Int)/10^30,(244946043608414255258 : Int)/10^30)
theorem v4139_mg_checked : Scalar.distance (sourceCoefficient 62 79 3 2) v4139_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4139_upper : Scalar.QComplex := ((999993894796445018406231549648 : Int)/10^30,(-3494333961780519308726863937 : Int)/10^30)
theorem v4139_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 79 5) 1) 14) v4139_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4139 : Material (62 : Basis) (79 : Basis) where
  plus := ![v4139_pa,v4139_pb,v4139_pg]
  minus := ![(Primitive.Addresses.material4139 1).one,v4139_mb,v4139_mg]
  upper := v4139_upper
  lower := (Primitive.Addresses.material4139 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4139_pa_checked.trans (by decide +kernel)
    · exact v4139_pb_checked.trans (by decide +kernel)
    · exact v4139_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 79 Primitive.Addresses.material4139
    · exact v4139_mb_checked.trans (by decide +kernel)
    · exact v4139_mg_checked.trans (by decide +kernel)
  upper_error := v4139_upper_checked
  lower_error := reuse_lower_error 62 79 Primitive.Addresses.material4139

def v4140_pa : Scalar.QComplex := ((999998420881994612627286693521 : Int)/10^30,(-1777141951888219448213775699 : Int)/10^30)
theorem v4140_pa_checked : Scalar.distance (sourceCoefficient 62 80 1 0) v4140_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4140_pb : Scalar.QComplex := ((-766796787232420548468910 : Int)/10^30,(-431476830286452027179278835 : Int)/10^30)
theorem v4140_pb_checked : Scalar.distance (sourceCoefficient 62 80 1 1) v4140_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4140_pg : Scalar.QComplex := ((-93086281892831082177226 : Int)/10^30,(165427797927057146433 : Int)/10^30)
theorem v4140_pg_checked : Scalar.distance (sourceCoefficient 62 80 1 2) v4140_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4140_mb : Scalar.QComplex := ((-1139141573261091000404054 : Int)/10^30,(-431476007916816509937195869 : Int)/10^30)
theorem v4140_mb_checked : Scalar.distance (sourceCoefficient 62 80 3 1) v4140_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4140_mg : Scalar.QComplex := ((-93086104475815060618699 : Int)/10^30,(245757005153735403401 : Int)/10^30)
theorem v4140_mg_checked : Scalar.distance (sourceCoefficient 62 80 3 2) v4140_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4140_upper : Scalar.QComplex := ((999993864316026874513437785983 : Int)/10^30,(-3503045860338279250411682317 : Int)/10^30)
theorem v4140_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 80 5) 1) 14) v4140_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4140 : Material (62 : Basis) (80 : Basis) where
  plus := ![v4140_pa,v4140_pb,v4140_pg]
  minus := ![(Primitive.Addresses.material4140 1).one,v4140_mb,v4140_mg]
  upper := v4140_upper
  lower := (Primitive.Addresses.material4140 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4140_pa_checked.trans (by decide +kernel)
    · exact v4140_pb_checked.trans (by decide +kernel)
    · exact v4140_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 80 Primitive.Addresses.material4140
    · exact v4140_mb_checked.trans (by decide +kernel)
    · exact v4140_mg_checked.trans (by decide +kernel)
  upper_error := v4140_upper_checked
  lower_error := reuse_lower_error 62 80 Primitive.Addresses.material4140

def v4141_pa : Scalar.QComplex := ((999998373919697115440337877078 : Int)/10^30,(-1803374049284276435771129609 : Int)/10^30)
theorem v4141_pa_checked : Scalar.distance (sourceCoefficient 62 81 1 0) v4141_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4141_pb : Scalar.QComplex := ((-778115344798042689651283 : Int)/10^30,(-431476808612625462071375071 : Int)/10^30)
theorem v4141_pb_checked : Scalar.distance (sourceCoefficient 62 81 1 1) v4141_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4141_pg : Scalar.QComplex := ((-93086277369112427954252 : Int)/10^30,(167869649921466771309 : Int)/10^30)
theorem v4141_pg_checked : Scalar.distance (sourceCoefficient 62 81 1 2) v4141_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4141_mb : Scalar.QComplex := ((-1150460107908760703494097 : Int)/10^30,(-431475976475592604762801464 : Int)/10^30)
theorem v4141_mb_checked : Scalar.distance (sourceCoefficient 62 81 3 1) v4141_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4141_mg : Scalar.QComplex := ((-93086097844889796538711 : Int)/10^30,(248198852335166474740 : Int)/10^30)
theorem v4141_mg_checked : Scalar.distance (sourceCoefficient 62 81 3 2) v4141_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4141_upper : Scalar.QComplex := ((999993772079578973843798063383 : Int)/10^30,(-3529277837612043511365510475 : Int)/10^30)
theorem v4141_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 81 5) 1) 14) v4141_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4141 : Material (62 : Basis) (81 : Basis) where
  plus := ![v4141_pa,v4141_pb,v4141_pg]
  minus := ![(Primitive.Addresses.material4141 1).one,v4141_mb,v4141_mg]
  upper := v4141_upper
  lower := (Primitive.Addresses.material4141 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4141_pa_checked.trans (by decide +kernel)
    · exact v4141_pb_checked.trans (by decide +kernel)
    · exact v4141_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 81 Primitive.Addresses.material4141
    · exact v4141_mb_checked.trans (by decide +kernel)
    · exact v4141_mg_checked.trans (by decide +kernel)
  upper_error := v4141_upper_checked
  lower_error := reuse_lower_error 62 81 Primitive.Addresses.material4141

def v4142_pa : Scalar.QComplex := ((999998355944287871640031341053 : Int)/10^30,(-1813314291935497693475662878 : Int)/10^30)
theorem v4142_pa_checked : Scalar.distance (sourceCoefficient 62 82 1 0) v4142_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4142_pb : Scalar.QComplex := ((-782404334932085200489916 : Int)/10^30,(-431476800296239219315413977 : Int)/10^30)
theorem v4142_pb_checked : Scalar.distance (sourceCoefficient 62 82 1 1) v4142_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4142_pg : Scalar.QComplex := ((-93086275635395620305854 : Int)/10^30,(168794951501014173562 : Int)/10^30)
theorem v4142_pg_checked : Scalar.distance (sourceCoefficient 62 82 1 2) v4142_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4142_mb : Scalar.QComplex := ((-1154749089269149399529967 : Int)/10^30,(-431475964458004141843698299 : Int)/10^30)
theorem v4142_mb_checked : Scalar.distance (sourceCoefficient 62 82 3 1) v4142_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4142_mg : Scalar.QComplex := ((-93086095312680045319037 : Int)/10^30,(249124152074062289262 : Int)/10^30)
theorem v4142_mg_checked : Scalar.distance (sourceCoefficient 62 82 3 2) v4142_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4142_upper : Scalar.QComplex := ((999993736948239458065193782448 : Int)/10^30,(-3539218034434515364590450791 : Int)/10^30)
theorem v4142_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 82 5) 1) 14) v4142_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4142 : Material (62 : Basis) (82 : Basis) where
  plus := ![v4142_pa,v4142_pb,v4142_pg]
  minus := ![(Primitive.Addresses.material4142 1).one,v4142_mb,v4142_mg]
  upper := v4142_upper
  lower := (Primitive.Addresses.material4142 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4142_pa_checked.trans (by decide +kernel)
    · exact v4142_pb_checked.trans (by decide +kernel)
    · exact v4142_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 82 Primitive.Addresses.material4142
    · exact v4142_mb_checked.trans (by decide +kernel)
    · exact v4142_mg_checked.trans (by decide +kernel)
  upper_error := v4142_upper_checked
  lower_error := reuse_lower_error 62 82 Primitive.Addresses.material4142

def v4143_pa : Scalar.QComplex := ((999998331248060235789520541178 : Int)/10^30,(-1826882890279337115042019547 : Int)/10^30)
theorem v4143_pa_checked : Scalar.distance (sourceCoefficient 62 83 1 0) v4143_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4143_pb : Scalar.QComplex := ((-788258878515791365851283 : Int)/10^30,(-431476788852476101989032383 : Int)/10^30)
theorem v4143_pb_checked : Scalar.distance (sourceCoefficient 62 83 1 1) v4143_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4143_pg : Scalar.QComplex := ((-93086273251522096712806 : Int)/10^30,(170058003707696395609 : Int)/10^30)
theorem v4143_pg_checked : Scalar.distance (sourceCoefficient 62 83 1 2) v4143_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4143_mb : Scalar.QComplex := ((-1160603620797489260523025 : Int)/10^30,(-431475947962037851669701326 : Int)/10^30)
theorem v4143_mb_checked : Scalar.distance (sourceCoefficient 62 83 3 1) v4143_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4143_mg : Scalar.QComplex := ((-93086091838850240743983 : Int)/10^30,(250387201753276965241 : Int)/10^30)
theorem v4143_mg_checked : Scalar.distance (sourceCoefficient 62 83 3 2) v4143_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4143_upper : Scalar.QComplex := ((999993688833878796504109583364 : Int)/10^30,(-3552786569946072957325295157 : Int)/10^30)
theorem v4143_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 83 5) 1) 14) v4143_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4143 : Material (62 : Basis) (83 : Basis) where
  plus := ![v4143_pa,v4143_pb,v4143_pg]
  minus := ![(Primitive.Addresses.material4143 1).one,v4143_mb,v4143_mg]
  upper := v4143_upper
  lower := (Primitive.Addresses.material4143 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4143_pa_checked.trans (by decide +kernel)
    · exact v4143_pb_checked.trans (by decide +kernel)
    · exact v4143_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 83 Primitive.Addresses.material4143
    · exact v4143_mb_checked.trans (by decide +kernel)
    · exact v4143_mg_checked.trans (by decide +kernel)
  upper_error := v4143_upper_checked
  lower_error := reuse_lower_error 62 83 Primitive.Addresses.material4143

def v4144_pa : Scalar.QComplex := ((999998266435742254781701721125 : Int)/10^30,(-1862021887692354937756092320 : Int)/10^30)
theorem v4144_pa_checked : Scalar.distance (sourceCoefficient 62 84 1 0) v4144_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4144_pb : Scalar.QComplex := ((-803420561555622000955312 : Int)/10^30,(-431476758723898655283371133 : Int)/10^30)
theorem v4144_pb_checked : Scalar.distance (sourceCoefficient 62 84 1 1) v4144_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4144_pg : Scalar.QComplex := ((-93086266984997322099042 : Int)/10^30,(173328967046541354752 : Int)/10^30)
theorem v4144_pg_checked : Scalar.distance (sourceCoefficient 62 84 1 2) v4144_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4144_mb : Scalar.QComplex := ((-1175765272192326981001296 : Int)/10^30,(-431475904749622016691805373 : Int)/10^30)
theorem v4144_mb_checked : Scalar.distance (sourceCoefficient 62 84 3 1) v4144_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4144_mg : Scalar.QComplex := ((-93086082749633756740641 : Int)/10^30,(253658158466464136229 : Int)/10^30)
theorem v4144_mg_checked : Scalar.distance (sourceCoefficient 62 84 3 2) v4144_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4144_upper : Scalar.QComplex := ((999993563374935595905471345422 : Int)/10^30,(-3587925403163500742279560669 : Int)/10^30)
theorem v4144_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 62 84 5) 1) 14) v4144_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4144 : Material (62 : Basis) (84 : Basis) where
  plus := ![v4144_pa,v4144_pb,v4144_pg]
  minus := ![(Primitive.Addresses.material4144 1).one,v4144_mb,v4144_mg]
  upper := v4144_upper
  lower := (Primitive.Addresses.material4144 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4144_pa_checked.trans (by decide +kernel)
    · exact v4144_pb_checked.trans (by decide +kernel)
    · exact v4144_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 62 84 Primitive.Addresses.material4144
    · exact v4144_mb_checked.trans (by decide +kernel)
    · exact v4144_mg_checked.trans (by decide +kernel)
  upper_error := v4144_upper_checked
  lower_error := reuse_lower_error 62 84 Primitive.Addresses.material4144

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
