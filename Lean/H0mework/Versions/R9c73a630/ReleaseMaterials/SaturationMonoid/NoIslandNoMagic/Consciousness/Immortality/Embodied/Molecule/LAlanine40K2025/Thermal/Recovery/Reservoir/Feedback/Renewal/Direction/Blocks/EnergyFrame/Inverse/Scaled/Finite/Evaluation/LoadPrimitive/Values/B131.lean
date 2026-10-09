import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B087
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B088

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2097_pa : Scalar.QComplex := ((999999329863573787508412207971 : Int)/10^30,(-1157701344623108502820227701 : Int)/10^30)
theorem v2097_pa_checked : Scalar.distance (sourceCoefficient 24 70 1 0) v2097_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2097_pb : Scalar.QComplex := ((-499522063637569418913085 : Int)/10^30,(-431477195055222955266420828 : Int)/10^30)
theorem v2097_pb_checked : Scalar.distance (sourceCoefficient 24 70 1 1) v2097_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2097_pg : Scalar.QComplex := ((-93086363547139187799886 : Int)/10^30,(107766280462708605186 : Int)/10^30)
theorem v2097_pg_checked : Scalar.distance (sourceCoefficient 24 70 1 2) v2097_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2097_mb : Scalar.QComplex := ((-871867263963855258869707 : Int)/10^30,(-431476603331500473602942830 : Int)/10^30)
theorem v2097_mb_checked : Scalar.distance (sourceCoefficient 24 70 3 1) v2097_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2097_mg : Scalar.QComplex := ((-93086235889385356001230 : Int)/10^30,(188095579623395397297 : Int)/10^30)
theorem v2097_mg_checked : Scalar.distance (sourceCoefficient 24 70 3 2) v2097_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2097_upper : Scalar.QComplex := ((999995842394545154772173317128 : Int)/10^30,(-2883607744476931712377957691 : Int)/10^30)
theorem v2097_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 70 5) 1) 14) v2097_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2097 : Material (24 : Basis) (70 : Basis) where
  plus := ![v2097_pa,v2097_pb,v2097_pg]
  minus := ![(Primitive.Addresses.material2097 1).one,v2097_mb,v2097_mg]
  upper := v2097_upper
  lower := (Primitive.Addresses.material2097 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2097_pa_checked.trans (by decide +kernel)
    · exact v2097_pb_checked.trans (by decide +kernel)
    · exact v2097_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 70 Primitive.Addresses.material2097
    · exact v2097_mb_checked.trans (by decide +kernel)
    · exact v2097_mg_checked.trans (by decide +kernel)
  upper_error := v2097_upper_checked
  lower_error := reuse_lower_error 24 70 Primitive.Addresses.material2097

def v2098_pa : Scalar.QComplex := ((999999301444677185816949671818 : Int)/10^30,(-1181994144506996730252763724 : Int)/10^30)
theorem v2098_pa_checked : Scalar.distance (sourceCoefficient 24 71 1 0) v2098_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2098_pb : Scalar.QComplex := ((-510003856811440409244737 : Int)/10^30,(-431477180251388841300770994 : Int)/10^30)
theorem v2098_pb_checked : Scalar.distance (sourceCoefficient 24 71 1 1) v2098_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2098_pg : Scalar.QComplex := ((-93086360627551886859192 : Int)/10^30,(110027610055605636660 : Int)/10^30)
theorem v2098_pg_checked : Scalar.distance (sourceCoefficient 24 71 1 2) v2098_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2098_mb : Scalar.QComplex := ((-882349040459833508541596 : Int)/10^30,(-431476579482356445170664839 : Int)/10^30)
theorem v2098_mb_checked : Scalar.distance (sourceCoefficient 24 71 3 1) v2098_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2098_mg : Scalar.QComplex := ((-93086231018373549990326 : Int)/10^30,(190356905854823726086 : Int)/10^30)
theorem v2098_mg_checked : Scalar.distance (sourceCoefficient 24 71 3 2) v2098_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2098_upper : Scalar.QComplex := ((999995772048522105687925933096 : Int)/10^30,(-2907900459131110753131006386 : Int)/10^30)
theorem v2098_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 71 5) 1) 14) v2098_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2098 : Material (24 : Basis) (71 : Basis) where
  plus := ![v2098_pa,v2098_pb,v2098_pg]
  minus := ![(Primitive.Addresses.material2098 1).one,v2098_mb,v2098_mg]
  upper := v2098_upper
  lower := (Primitive.Addresses.material2098 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2098_pa_checked.trans (by decide +kernel)
    · exact v2098_pb_checked.trans (by decide +kernel)
    · exact v2098_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 71 Primitive.Addresses.material2098
    · exact v2098_mb_checked.trans (by decide +kernel)
    · exact v2098_mg_checked.trans (by decide +kernel)
  upper_error := v2098_upper_checked
  lower_error := reuse_lower_error 24 71 Primitive.Addresses.material2098

def v2099_pa : Scalar.QComplex := ((999999269936713633287196601075 : Int)/10^30,(-1208356751849810084154016527 : Int)/10^30)
theorem v2099_pa_checked : Scalar.distance (sourceCoefficient 24 72 1 0) v2099_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2099_pb : Scalar.QComplex := ((-521378724788736689730232 : Int)/10^30,(-431477163802097865631088906 : Int)/10^30)
theorem v2099_pb_checked : Scalar.distance (sourceCoefficient 24 72 1 1) v2099_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2099_pg : Scalar.QComplex := ((-93086357386695058007656 : Int)/10^30,(112481610572011686150 : Int)/10^30)
theorem v2099_pg_checked : Scalar.distance (sourceCoefficient 24 72 1 2) v2099_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2099_mb : Scalar.QComplex := ((-893723890006749320492675 : Int)/10^30,(-431476553217072834953133223 : Int)/10^30)
theorem v2099_mb_checked : Scalar.distance (sourceCoefficient 24 72 3 1) v2099_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2099_mg : Scalar.QComplex := ((-93086225659826006279893 : Int)/10^30,(192810902660779749429 : Int)/10^30)
theorem v2099_mg_checked : Scalar.distance (sourceCoefficient 24 72 3 2) v2099_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2099_upper : Scalar.QComplex := ((999995695041136803928859200100 : Int)/10^30,(-2934262972830030527765132150 : Int)/10^30)
theorem v2099_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 72 5) 1) 14) v2099_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2099 : Material (24 : Basis) (72 : Basis) where
  plus := ![v2099_pa,v2099_pb,v2099_pg]
  minus := ![(Primitive.Addresses.material2099 1).one,v2099_mb,v2099_mg]
  upper := v2099_upper
  lower := (Primitive.Addresses.material2099 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2099_pa_checked.trans (by decide +kernel)
    · exact v2099_pb_checked.trans (by decide +kernel)
    · exact v2099_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 72 Primitive.Addresses.material2099
    · exact v2099_mb_checked.trans (by decide +kernel)
    · exact v2099_mg_checked.trans (by decide +kernel)
  upper_error := v2099_upper_checked
  lower_error := reuse_lower_error 24 72 Primitive.Addresses.material2099

def v2100_pa : Scalar.QComplex := ((999999258473526318330157757735 : Int)/10^30,(-1217806387527109546369330870 : Int)/10^30)
theorem v2100_pa_checked : Scalar.distance (sourceCoefficient 24 73 1 0) v2100_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2100_pb : Scalar.QComplex := ((-525456028490826295448437 : Int)/10^30,(-431477157808529940769468845 : Int)/10^30)
theorem v2100_pb_checked : Scalar.distance (sourceCoefficient 24 73 1 1) v2100_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2100_pg : Scalar.QComplex := ((-93086356206638977994099 : Int)/10^30,(113361243240431698445 : Int)/10^30)
theorem v2100_pg_checked : Scalar.distance (sourceCoefficient 24 73 1 2) v2100_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2100_mb : Scalar.QComplex := ((-897801187018493237061358 : Int)/10^30,(-431476543704977681809334084 : Int)/10^30)
theorem v2100_mb_checked : Scalar.distance (sourceCoefficient 24 73 3 1) v2100_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2100_mg : Scalar.QComplex := ((-93086223720686989993402 : Int)/10^30,(193690533983337068773 : Int)/10^30)
theorem v2100_mg_checked : Scalar.distance (sourceCoefficient 24 73 3 2) v2100_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2100_upper : Scalar.QComplex := ((999995667268752647275957396574 : Int)/10^30,(-2943712574648786307438920100 : Int)/10^30)
theorem v2100_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 73 5) 1) 14) v2100_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2100 : Material (24 : Basis) (73 : Basis) where
  plus := ![v2100_pa,v2100_pb,v2100_pg]
  minus := ![(Primitive.Addresses.material2100 1).one,v2100_mb,v2100_mg]
  upper := v2100_upper
  lower := (Primitive.Addresses.material2100 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2100_pa_checked.trans (by decide +kernel)
    · exact v2100_pb_checked.trans (by decide +kernel)
    · exact v2100_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 73 Primitive.Addresses.material2100
    · exact v2100_mb_checked.trans (by decide +kernel)
    · exact v2100_mg_checked.trans (by decide +kernel)
  upper_error := v2100_upper_checked
  lower_error := reuse_lower_error 24 73 Primitive.Addresses.material2100

def v2101_pa : Scalar.QComplex := ((999999245467850953821614194594 : Int)/10^30,(-1228439550313157585681929017 : Int)/10^30)
theorem v2101_pa_checked : Scalar.distance (sourceCoefficient 24 74 1 0) v2101_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2101_pb : Scalar.QComplex := ((-530043997283600154284044 : Int)/10^30,(-431477151002866565129318927 : Int)/10^30)
theorem v2101_pb_checked : Scalar.distance (sourceCoefficient 24 74 1 1) v2101_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2101_pg : Scalar.QComplex := ((-93086354867190307845384 : Int)/10^30,(114351046194882900788 : Int)/10^30)
theorem v2101_pg_checked : Scalar.distance (sourceCoefficient 24 74 1 2) v2101_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2101_mb : Scalar.QComplex := ((-902389148229975656337591 : Int)/10^30,(-431476532940106406508648343 : Int)/10^30)
theorem v2101_mb_checked : Scalar.distance (sourceCoefficient 24 74 3 1) v2101_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2101_mg : Scalar.QComplex := ((-93086221527083447961471 : Int)/10^30,(194680335413355519134 : Int)/10^30)
theorem v2101_mg_checked : Scalar.distance (sourceCoefficient 24 74 3 2) v2101_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2101_upper : Scalar.QComplex := ((999995635911222317466850332834 : Int)/10^30,(-2954345699151371622486142409 : Int)/10^30)
theorem v2101_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 74 5) 1) 14) v2101_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2101 : Material (24 : Basis) (74 : Basis) where
  plus := ![v2101_pa,v2101_pb,v2101_pg]
  minus := ![(Primitive.Addresses.material2101 1).one,v2101_mb,v2101_mg]
  upper := v2101_upper
  lower := (Primitive.Addresses.material2101 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2101_pa_checked.trans (by decide +kernel)
    · exact v2101_pb_checked.trans (by decide +kernel)
    · exact v2101_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 74 Primitive.Addresses.material2101
    · exact v2101_mb_checked.trans (by decide +kernel)
    · exact v2101_mg_checked.trans (by decide +kernel)
  upper_error := v2101_upper_checked
  lower_error := reuse_lower_error 24 74 Primitive.Addresses.material2101

def v2102_pa : Scalar.QComplex := ((999999227158616680064683931505 : Int)/10^30,(-1243254667940590062703977804 : Int)/10^30)
theorem v2102_pa_checked : Scalar.distance (sourceCoefficient 24 75 1 0) v2102_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2102_pb : Scalar.QComplex := ((-536436384750529074736140 : Int)/10^30,(-431477141412128967697676001 : Int)/10^30)
theorem v2102_pb_checked : Scalar.distance (sourceCoefficient 24 75 1 1) v2102_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2102_pg : Scalar.QComplex := ((-93086352980472710441597 : Int)/10^30,(115730132305573698548 : Int)/10^30)
theorem v2102_pg_checked : Scalar.distance (sourceCoefficient 24 75 1 2) v2102_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2102_mb : Scalar.QComplex := ((-908781525040351980515592 : Int)/10^30,(-431476517833029898631342339 : Int)/10^30)
theorem v2102_mb_checked : Scalar.distance (sourceCoefficient 24 75 3 1) v2102_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2102_mg : Scalar.QComplex := ((-93086218450277351275444 : Int)/10^30,(196059419382397218582 : Int)/10^30)
theorem v2102_mg_checked : Scalar.distance (sourceCoefficient 24 75 3 2) v2102_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2102_upper : Scalar.QComplex := ((999995592032466305187437999412 : Int)/10^30,(-2969160763113349343667689058 : Int)/10^30)
theorem v2102_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 75 5) 1) 14) v2102_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2102 : Material (24 : Basis) (75 : Basis) where
  plus := ![v2102_pa,v2102_pb,v2102_pg]
  minus := ![(Primitive.Addresses.material2102 1).one,v2102_mb,v2102_mg]
  upper := v2102_upper
  lower := (Primitive.Addresses.material2102 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2102_pa_checked.trans (by decide +kernel)
    · exact v2102_pb_checked.trans (by decide +kernel)
    · exact v2102_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 75 Primitive.Addresses.material2102
    · exact v2102_mb_checked.trans (by decide +kernel)
    · exact v2102_mg_checked.trans (by decide +kernel)
  upper_error := v2102_upper_checked
  lower_error := reuse_lower_error 24 75 Primitive.Addresses.material2102

def v2103_pa : Scalar.QComplex := ((999999211627476505841885683124 : Int)/10^30,(-1255684843205921805111913746 : Int)/10^30)
theorem v2103_pa_checked : Scalar.distance (sourceCoefficient 24 76 1 0) v2103_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2103_pb : Scalar.QComplex := ((-541799723574451426635576 : Int)/10^30,(-431477133267894015394242198 : Int)/10^30)
theorem v2103_pb_checked : Scalar.distance (sourceCoefficient 24 76 1 1) v2103_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2103_pg : Scalar.QComplex := ((-93086351379089895181227 : Int)/10^30,(116887212686730668057 : Int)/10^30)
theorem v2103_pg_checked : Scalar.distance (sourceCoefficient 24 76 1 2) v2103_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2103_mb : Scalar.QComplex := ((-914144854839150210463505 : Int)/10^30,(-431476505060478129567457678 : Int)/10^30)
theorem v2103_mb_checked : Scalar.distance (sourceCoefficient 24 76 3 1) v2103_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2103_mg : Scalar.QComplex := ((-93086215850386876310461 : Int)/10^30,(197216497950799035036 : Int)/10^30)
theorem v2103_mg_checked : Scalar.distance (sourceCoefficient 24 76 3 2) v2103_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2103_upper : Scalar.QComplex := ((999995555047994411502226211097 : Int)/10^30,(-2981590893060056212642425535 : Int)/10^30)
theorem v2103_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 76 5) 1) 14) v2103_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2103 : Material (24 : Basis) (76 : Basis) where
  plus := ![v2103_pa,v2103_pb,v2103_pg]
  minus := ![(Primitive.Addresses.material2103 1).one,v2103_mb,v2103_mg]
  upper := v2103_upper
  lower := (Primitive.Addresses.material2103 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2103_pa_checked.trans (by decide +kernel)
    · exact v2103_pb_checked.trans (by decide +kernel)
    · exact v2103_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 76 Primitive.Addresses.material2103
    · exact v2103_mb_checked.trans (by decide +kernel)
    · exact v2103_mg_checked.trans (by decide +kernel)
  upper_error := v2103_upper_checked
  lower_error := reuse_lower_error 24 76 Primitive.Addresses.material2103

def v2104_pa : Scalar.QComplex := ((999999208009859923443916290450 : Int)/10^30,(-1258562534363998215444922014 : Int)/10^30)
theorem v2104_pa_checked : Scalar.distance (sourceCoefficient 24 77 1 0) v2104_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2104_pb : Scalar.QComplex := ((-543041382060256952571577 : Int)/10^30,(-431477131369762991433666412 : Int)/10^30)
theorem v2104_pb_checked : Scalar.distance (sourceCoefficient 24 77 1 1) v2104_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2104_pg : Scalar.QComplex := ((-93086351005964161801233 : Int)/10^30,(117155086622436435023 : Int)/10^30)
theorem v2104_pg_checked : Scalar.distance (sourceCoefficient 24 77 1 2) v2104_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2104_mb : Scalar.QComplex := ((-915386511224627950507823 : Int)/10^30,(-431476502090852461339912314 : Int)/10^30)
theorem v2104_mb_checked : Scalar.distance (sourceCoefficient 24 77 3 1) v2104_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2104_mg : Scalar.QComplex := ((-93086215246098139942358 : Int)/10^30,(197484371464772390347 : Int)/10^30)
theorem v2104_mg_checked : Scalar.distance (sourceCoefficient 24 77 3 2) v2104_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2104_upper : Scalar.QComplex := ((999995546463749340381872430763 : Int)/10^30,(-2984468573688471646763675951 : Int)/10^30)
theorem v2104_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 77 5) 1) 14) v2104_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2104 : Material (24 : Basis) (77 : Basis) where
  plus := ![v2104_pa,v2104_pb,v2104_pg]
  minus := ![(Primitive.Addresses.material2104 1).one,v2104_mb,v2104_mg]
  upper := v2104_upper
  lower := (Primitive.Addresses.material2104 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2104_pa_checked.trans (by decide +kernel)
    · exact v2104_pb_checked.trans (by decide +kernel)
    · exact v2104_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 77 Primitive.Addresses.material2104
    · exact v2104_mb_checked.trans (by decide +kernel)
    · exact v2104_mg_checked.trans (by decide +kernel)
  upper_error := v2104_upper_checked
  lower_error := reuse_lower_error 24 77 Primitive.Addresses.material2104

def v2105_pa : Scalar.QComplex := ((999999186087607255312062539215 : Int)/10^30,(-1275862109726592990312907885 : Int)/10^30)
theorem v2105_pa_checked : Scalar.distance (sourceCoefficient 24 78 1 0) v2105_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2105_pb : Scalar.QComplex := ((-550505756504902950963405 : Int)/10^30,(-431477119858520074259596467 : Int)/10^30)
theorem v2105_pb_checked : Scalar.distance (sourceCoefficient 24 78 1 1) v2105_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2105_pg : Scalar.QComplex := ((-93086348743921343575156 : Int)/10^30,(118765441959829915741 : Int)/10^30)
theorem v2105_pg_checked : Scalar.distance (sourceCoefficient 24 78 1 2) v2105_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2105_mb : Scalar.QComplex := ((-922850872956262014007333 : Int)/10^30,(-431476484138194867543462924 : Int)/10^30)
theorem v2105_mb_checked : Scalar.distance (sourceCoefficient 24 78 3 1) v2105_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2105_mg : Scalar.QComplex := ((-93086211594392035519671 : Int)/10^30,(199094724250515908576 : Int)/10^30)
theorem v2105_mg_checked : Scalar.distance (sourceCoefficient 24 78 3 2) v2105_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2105_upper : Scalar.QComplex := ((999995494684031652248991568276 : Int)/10^30,(-3001768085449561735950693102 : Int)/10^30)
theorem v2105_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 78 5) 1) 14) v2105_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2105 : Material (24 : Basis) (78 : Basis) where
  plus := ![v2105_pa,v2105_pb,v2105_pg]
  minus := ![(Primitive.Addresses.material2105 1).one,v2105_mb,v2105_mg]
  upper := v2105_upper
  lower := (Primitive.Addresses.material2105 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2105_pa_checked.trans (by decide +kernel)
    · exact v2105_pb_checked.trans (by decide +kernel)
    · exact v2105_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 78 Primitive.Addresses.material2105
    · exact v2105_mb_checked.trans (by decide +kernel)
    · exact v2105_mg_checked.trans (by decide +kernel)
  upper_error := v2105_upper_checked
  lower_error := reuse_lower_error 24 78 Primitive.Addresses.material2105

def v2106_pa : Scalar.QComplex := ((999999178956468931405921866492 : Int)/10^30,(-1281439186237375935304532892 : Int)/10^30)
theorem v2106_pa_checked : Scalar.distance (sourceCoefficient 24 79 1 0) v2106_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2106_pb : Scalar.QComplex := ((-552912138514007013086291 : Int)/10^30,(-431477116110799309409505027 : Int)/10^30)
theorem v2106_pb_checked : Scalar.distance (sourceCoefficient 24 79 1 1) v2106_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2106_pg : Scalar.QComplex := ((-93086348007750903654136 : Int)/10^30,(119284591978704098863 : Int)/10^30)
theorem v2106_pg_checked : Scalar.distance (sourceCoefficient 24 79 1 2) v2106_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2106_mb : Scalar.QComplex := ((-925257250835245848061783 : Int)/10^30,(-431476478313876203706742698 : Int)/10^30)
theorem v2106_mb_checked : Scalar.distance (sourceCoefficient 24 79 3 1) v2106_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2106_mg : Scalar.QComplex := ((-93086210410218785069013 : Int)/10^30,(199613873440804879578 : Int)/10^30)
theorem v2106_mg_checked : Scalar.distance (sourceCoefficient 24 79 3 2) v2106_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2106_upper : Scalar.QComplex := ((999995477927375840153144942885 : Int)/10^30,(-3007345141346246532311602314 : Int)/10^30)
theorem v2106_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 79 5) 1) 14) v2106_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2106 : Material (24 : Basis) (79 : Basis) where
  plus := ![v2106_pa,v2106_pb,v2106_pg]
  minus := ![(Primitive.Addresses.material2106 1).one,v2106_mb,v2106_mg]
  upper := v2106_upper
  lower := (Primitive.Addresses.material2106 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2106_pa_checked.trans (by decide +kernel)
    · exact v2106_pb_checked.trans (by decide +kernel)
    · exact v2106_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 79 Primitive.Addresses.material2106
    · exact v2106_mb_checked.trans (by decide +kernel)
    · exact v2106_mg_checked.trans (by decide +kernel)
  upper_error := v2106_upper_checked
  lower_error := reuse_lower_error 24 79 Primitive.Addresses.material2106

def v2107_pa : Scalar.QComplex := ((999999167754683383935162037870 : Int)/10^30,(-1290151130914460984781687043 : Int)/10^30)
theorem v2107_pa_checked : Scalar.distance (sourceCoefficient 24 80 1 0) v2107_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2107_pb : Scalar.QComplex := ((-556671145001868025331296 : Int)/10^30,(-431477110220680672582243721 : Int)/10^30)
theorem v2107_pb_checked : Scalar.distance (sourceCoefficient 24 80 1 1) v2107_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2107_pg : Scalar.QComplex := ((-93086346851020312943029 : Int)/10^30,(120095555611503334885 : Int)/10^30)
theorem v2107_pg_checked : Scalar.distance (sourceCoefficient 24 80 1 2) v2107_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2107_mb : Scalar.QComplex := ((-929016250840549847306567 : Int)/10^30,(-431476469179906460383313359 : Int)/10^30)
theorem v2107_mb_checked : Scalar.distance (sourceCoefficient 24 80 3 1) v2107_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2107_mg : Scalar.QComplex := ((-93086208553663534401999 : Int)/10^30,(200424835773438889668 : Int)/10^30)
theorem v2107_mg_checked : Scalar.distance (sourceCoefficient 24 80 3 2) v2107_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2107_upper : Scalar.QComplex := ((999995451689580805224605088362 : Int)/10^30,(-3016057053714647725292728058 : Int)/10^30)
theorem v2107_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 80 5) 1) 14) v2107_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2107 : Material (24 : Basis) (80 : Basis) where
  plus := ![v2107_pa,v2107_pb,v2107_pg]
  minus := ![(Primitive.Addresses.material2107 1).one,v2107_mb,v2107_mg]
  upper := v2107_upper
  lower := (Primitive.Addresses.material2107 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2107_pa_checked.trans (by decide +kernel)
    · exact v2107_pb_checked.trans (by decide +kernel)
    · exact v2107_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 80 Primitive.Addresses.material2107
    · exact v2107_mb_checked.trans (by decide +kernel)
    · exact v2107_mg_checked.trans (by decide +kernel)
  upper_error := v2107_upper_checked
  lower_error := reuse_lower_error 24 80 Primitive.Addresses.material2107

def v2108_pa : Scalar.QComplex := ((999999133567196747250488190082 : Int)/10^30,(-1316383248070141794753822133 : Int)/10^30)
theorem v2108_pa_checked : Scalar.distance (sourceCoefficient 24 81 1 0) v2108_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2108_pb : Scalar.QComplex := ((-567989708251378914130174 : Int)/10^30,(-431477092221549751545464381 : Int)/10^30)
theorem v2108_pb_checked : Scalar.distance (sourceCoefficient 24 81 1 1) v2108_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2108_pg : Scalar.QComplex := ((-93086343318269580607258 : Int)/10^30,(122537409138706954826 : Int)/10^30)
theorem v2108_pg_checked : Scalar.distance (sourceCoefficient 24 81 1 2) v2108_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2108_mb : Scalar.QComplex := ((-940334794343203020326868 : Int)/10^30,(-431476441413371926082916857 : Int)/10^30)
theorem v2108_mb_checked : Scalar.distance (sourceCoefficient 24 81 3 1) v2108_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2108_mg : Scalar.QComplex := ((-93086202913704500494383 : Int)/10^30,(202866685342824070392 : Int)/10^30)
theorem v2108_mg_checked : Scalar.distance (sourceCoefficient 24 81 3 2) v2108_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2108_upper : Scalar.QComplex := ((999995372227890635158959896188 : Int)/10^30,(-3042289072796171002461444398 : Int)/10^30)
theorem v2108_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 81 5) 1) 14) v2108_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2108 : Material (24 : Basis) (81 : Basis) where
  plus := ![v2108_pa,v2108_pb,v2108_pg]
  minus := ![(Primitive.Addresses.material2108 1).one,v2108_mb,v2108_mg]
  upper := v2108_upper
  lower := (Primitive.Addresses.material2108 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2108_pa_checked.trans (by decide +kernel)
    · exact v2108_pb_checked.trans (by decide +kernel)
    · exact v2108_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 81 Primitive.Addresses.material2108
    · exact v2108_mb_checked.trans (by decide +kernel)
    · exact v2108_mg_checked.trans (by decide +kernel)
  upper_error := v2108_upper_checked
  lower_error := reuse_lower_error 24 81 Primitive.Addresses.material2108

def v2109_pa : Scalar.QComplex := ((999999120432602113843009607912 : Int)/10^30,(-1326323498296515350009673933 : Int)/10^30)
theorem v2109_pa_checked : Scalar.distance (sourceCoefficient 24 82 1 0) v2109_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2109_pb : Scalar.QComplex := ((-572278700564426612339276 : Int)/10^30,(-431477085297631899640202096 : Int)/10^30)
theorem v2109_pb_checked : Scalar.distance (sourceCoefficient 24 82 1 1) v2109_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2109_pg : Scalar.QComplex := ((-93086341960064554743916 : Int)/10^30,(123462711305874245099 : Int)/10^30)
theorem v2109_pg_checked : Scalar.distance (sourceCoefficient 24 82 1 2) v2109_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2109_mb : Scalar.QComplex := ((-944623779084233599245889 : Int)/10^30,(-431476430788249455151553687 : Int)/10^30)
theorem v2109_mb_checked : Scalar.distance (sourceCoefficient 24 82 3 1) v2109_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2109_mg : Scalar.QComplex := ((-93086200757005884150070 : Int)/10^30,(203791985993389309394 : Int)/10^30)
theorem v2109_mg_checked : Scalar.distance (sourceCoefficient 24 82 3 2) v2109_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2109_upper : Scalar.QComplex := ((999995341937345445922810292700 : Int)/10^30,(-3052229285548590733205254869 : Int)/10^30)
theorem v2109_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 82 5) 1) 14) v2109_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2109 : Material (24 : Basis) (82 : Basis) where
  plus := ![v2109_pa,v2109_pb,v2109_pg]
  minus := ![(Primitive.Addresses.material2109 1).one,v2109_mb,v2109_mg]
  upper := v2109_upper
  lower := (Primitive.Addresses.material2109 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2109_pa_checked.trans (by decide +kernel)
    · exact v2109_pb_checked.trans (by decide +kernel)
    · exact v2109_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 82 Primitive.Addresses.material2109
    · exact v2109_mb_checked.trans (by decide +kernel)
    · exact v2109_mg_checked.trans (by decide +kernel)
  upper_error := v2109_upper_checked
  lower_error := reuse_lower_error 24 82 Primitive.Addresses.material2109

def v2110_pa : Scalar.QComplex := ((999999102344167828523603026943 : Int)/10^30,(-1339892107058236149262174208 : Int)/10^30)
theorem v2110_pa_checked : Scalar.distance (sourceCoefficient 24 83 1 0) v2110_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2110_pb : Scalar.QComplex := ((-578133247144853719782188 : Int)/10^30,(-431477075754611549916264732 : Int)/10^30)
theorem v2110_pb_checked : Scalar.distance (sourceCoefficient 24 83 1 1) v2110_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2110_pg : Scalar.QComplex := ((-93086340088770927755968 : Int)/10^30,(124725764320692599942 : Int)/10^30)
theorem v2110_pg_checked : Scalar.distance (sourceCoefficient 24 83 1 2) v2110_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2110_mb : Scalar.QComplex := ((-950478315249548688668840 : Int)/10^30,(-431476416193022638811394615 : Int)/10^30)
theorem v2110_mb_checked : Scalar.distance (sourceCoefficient 24 83 3 1) v2110_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2110_mg : Scalar.QComplex := ((-93086197795755087938109 : Int)/10^30,(205055036923073182291 : Int)/10^30)
theorem v2110_mg_checked : Scalar.distance (sourceCoefficient 24 83 3 2) v2110_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2110_upper : Scalar.QComplex := ((999995300430750313042685558452 : Int)/10^30,(-3065797842882466056102307037 : Int)/10^30)
theorem v2110_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 83 5) 1) 14) v2110_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2110 : Material (24 : Basis) (83 : Basis) where
  plus := ![v2110_pa,v2110_pb,v2110_pg]
  minus := ![(Primitive.Addresses.material2110 1).one,v2110_mb,v2110_mg]
  upper := v2110_upper
  lower := (Primitive.Addresses.material2110 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2110_pa_checked.trans (by decide +kernel)
    · exact v2110_pb_checked.trans (by decide +kernel)
    · exact v2110_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 83 Primitive.Addresses.material2110
    · exact v2110_mb_checked.trans (by decide +kernel)
    · exact v2110_mg_checked.trans (by decide +kernel)
  upper_error := v2110_upper_checked
  lower_error := reuse_lower_error 24 83 Primitive.Addresses.material2110

def v2111_pa : Scalar.QComplex := ((999999054644246348839146088788 : Int)/10^30,(-1375031131867500935408108341 : Int)/10^30)
theorem v2111_pa_checked : Scalar.distance (sourceCoefficient 24 84 1 0) v2111_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2111_pb : Scalar.QComplex := ((-593294938065260430891338 : Int)/10^30,(-431477050548443454717939282 : Int)/10^30)
theorem v2111_pb_checked : Scalar.distance (sourceCoefficient 24 84 1 1) v2111_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2111_pg : Scalar.QComplex := ((-93086335149689362554808 : Int)/10^30,(127996729784719851826 : Int)/10^30)
theorem v2111_pg_checked : Scalar.distance (sourceCoefficient 24 84 1 2) v2111_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2111_mb : Scalar.QComplex := ((-965639978772777124117020 : Int)/10^30,(-431476377903007521920642053 : Int)/10^30)
theorem v2111_mb_checked : Scalar.distance (sourceCoefficient 24 84 3 1) v2111_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2111_mg : Scalar.QComplex := ((-93086190033979485142992 : Int)/10^30,(208325996906965558619 : Int)/10^30)
theorem v2111_mg_checked : Scalar.distance (sourceCoefficient 24 84 3 2) v2111_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2111_upper : Scalar.QComplex := ((999995192084130843426093007075 : Int)/10^30,(-3100936733030543937797168227 : Int)/10^30)
theorem v2111_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 84 5) 1) 14) v2111_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2111 : Material (24 : Basis) (84 : Basis) where
  plus := ![v2111_pa,v2111_pb,v2111_pg]
  minus := ![(Primitive.Addresses.material2111 1).one,v2111_mb,v2111_mg]
  upper := v2111_upper
  lower := (Primitive.Addresses.material2111 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2111_pa_checked.trans (by decide +kernel)
    · exact v2111_pb_checked.trans (by decide +kernel)
    · exact v2111_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 84 Primitive.Addresses.material2111
    · exact v2111_mb_checked.trans (by decide +kernel)
    · exact v2111_mg_checked.trans (by decide +kernel)
  upper_error := v2111_upper_checked
  lower_error := reuse_lower_error 24 84 Primitive.Addresses.material2111

def v2112_pa : Scalar.QComplex := ((999998942813674051374863842635 : Int)/10^30,(-1454087870197094553688566048 : Int)/10^30)
theorem v2112_pa_checked : Scalar.distance (sourceCoefficient 24 85 1 0) v2112_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2112_pb : Scalar.QComplex := ((-627406122519317165868749 : Int)/10^30,(-431476991242009230833584729 : Int)/10^30)
theorem v2112_pb_checked : Scalar.distance (sourceCoefficient 24 85 1 1) v2112_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2112_pg : Scalar.QComplex := ((-93086323547386369442652 : Int)/10^30,(135355837047836761707 : Int)/10^30)
theorem v2112_pg_checked : Scalar.distance (sourceCoefficient 24 85 1 2) v2112_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2112_mb : Scalar.QComplex := ((-999751099346899256136203 : Int)/10^30,(-431476289160179507398500855 : Int)/10^30)
theorem v2112_mb_checked : Scalar.distance (sourceCoefficient 24 85 3 1) v2112_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2112_mg : Scalar.QComplex := ((-93086172081102685916028 : Int)/10^30,(215685091417685571898 : Int)/10^30)
theorem v2112_mg_checked : Scalar.distance (sourceCoefficient 24 85 3 2) v2112_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2112_upper : Scalar.QComplex := ((999994943808966718861016513074 : Int)/10^30,(-3179993160604989875829785596 : Int)/10^30)
theorem v2112_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 85 5) 1) 14) v2112_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2112 : Material (24 : Basis) (85 : Basis) where
  plus := ![v2112_pa,v2112_pb,v2112_pg]
  minus := ![(Primitive.Addresses.material2112 1).one,v2112_mb,v2112_mg]
  upper := v2112_upper
  lower := (Primitive.Addresses.material2112 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2112_pa_checked.trans (by decide +kernel)
    · exact v2112_pb_checked.trans (by decide +kernel)
    · exact v2112_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 85 Primitive.Addresses.material2112
    · exact v2112_mb_checked.trans (by decide +kernel)
    · exact v2112_mg_checked.trans (by decide +kernel)
  upper_error := v2112_upper_checked
  lower_error := reuse_lower_error 24 85 Primitive.Addresses.material2112

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
