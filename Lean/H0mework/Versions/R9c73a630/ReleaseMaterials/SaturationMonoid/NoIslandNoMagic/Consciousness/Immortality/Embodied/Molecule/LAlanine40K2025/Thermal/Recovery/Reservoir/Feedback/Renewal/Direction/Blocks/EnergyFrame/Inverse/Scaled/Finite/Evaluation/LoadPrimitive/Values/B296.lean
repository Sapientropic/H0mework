import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B197
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B198

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4737_pa : Scalar.QComplex := ((999995830009633938158817568484 : Int)/10^30,(-2887899469043898230879324223 : Int)/10^30)
theorem v4737_pa_checked : Scalar.distance (sourceCoefficient 91 97 1 0) v4737_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4737_pb : Scalar.QComplex := ((-1246063690468898706354549 : Int)/10^30,(-431475717126624441695072772 : Int)/10^30)
theorem v4737_pb_checked : Scalar.distance (sourceCoefficient 91 97 1 1) v4737_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4737_pg : Scalar.QComplex := ((-93086041229435582361908 : Int)/10^30,(268824250036418253666 : Int)/10^30)
theorem v4737_pg_checked : Scalar.distance (sourceCoefficient 91 97 1 2) v4737_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4737_mb : Scalar.QComplex := ((-1618407337437801155080372 : Int)/10^30,(-431474481171651291684866231 : Int)/10^30)
theorem v4737_mb_checked : Scalar.distance (sourceCoefficient 91 97 3 1) v4737_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4737_mg : Scalar.QComplex := ((-93085774586027803740091 : Int)/10^30,(349153211082200699643 : Int)/10^30)
theorem v4737_mg_checked : Scalar.distance (sourceCoefficient 91 97 3 2) v4737_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4737_upper : Scalar.QComplex := ((999989356380817524186071404801 : Int)/10^30,(-4613797251540462553670269590 : Int)/10^30)
theorem v4737_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 91 97 5) 1) 14) v4737_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4737 : Material (91 : Basis) (97 : Basis) where
  plus := ![v4737_pa,v4737_pb,v4737_pg]
  minus := ![(Primitive.Addresses.material4737 1).one,v4737_mb,v4737_mg]
  upper := v4737_upper
  lower := (Primitive.Addresses.material4737 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4737_pa_checked.trans (by decide +kernel)
    · exact v4737_pb_checked.trans (by decide +kernel)
    · exact v4737_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 91 97 Primitive.Addresses.material4737
    · exact v4737_mb_checked.trans (by decide +kernel)
    · exact v4737_mg_checked.trans (by decide +kernel)
  upper_error := v4737_upper_checked
  lower_error := reuse_lower_error 91 97 Primitive.Addresses.material4737

def v4738_pa : Scalar.QComplex := ((999996256167979358075909720041 : Int)/10^30,(-2736357071912518034992755157 : Int)/10^30)
theorem v4738_pa_checked : Scalar.distance (sourceCoefficient 92 93 1 0) v4738_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4738_pb : Scalar.QComplex := ((-1180676565678379869672737 : Int)/10^30,(-431475905517857656803794098 : Int)/10^30)
theorem v4738_pb_checked : Scalar.distance (sourceCoefficient 92 93 1 1) v4738_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4738_pg : Scalar.QComplex := ((-93086081385861568646173 : Int)/10^30,(254717710717148118329 : Int)/10^30)
theorem v4738_pg_checked : Scalar.distance (sourceCoefficient 92 93 1 2) v4738_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4738_mb : Scalar.QComplex := ((-1553020399567046655604973 : Int)/10^30,(-431474725988958127565568698 : Int)/10^30)
theorem v4738_mb_checked : Scalar.distance (sourceCoefficient 92 93 3 1) v4738_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4738_mg : Scalar.QComplex := ((-93085826915746935535651 : Int)/10^30,(335046711668626901440 : Int)/10^30)
theorem v4738_mg_checked : Scalar.distance (sourceCoefficient 92 93 3 2) v4738_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4738_upper : Scalar.QComplex := ((999990044086957861194263213251 : Int)/10^30,(-4462255815624324876207737344 : Int)/10^30)
theorem v4738_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 92 93 5) 1) 14) v4738_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4738 : Material (92 : Basis) (93 : Basis) where
  plus := ![v4738_pa,v4738_pb,v4738_pg]
  minus := ![(Primitive.Addresses.material4738 1).one,v4738_mb,v4738_mg]
  upper := v4738_upper
  lower := (Primitive.Addresses.material4738 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4738_pa_checked.trans (by decide +kernel)
    · exact v4738_pb_checked.trans (by decide +kernel)
    · exact v4738_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 92 93 Primitive.Addresses.material4738
    · exact v4738_mb_checked.trans (by decide +kernel)
    · exact v4738_mg_checked.trans (by decide +kernel)
  upper_error := v4738_upper_checked
  lower_error := reuse_lower_error 92 93 Primitive.Addresses.material4738

def v4739_pa : Scalar.QComplex := ((999996132579678161191793050745 : Int)/10^30,(-2781155458930275375718002520 : Int)/10^30)
theorem v4739_pa_checked : Scalar.distance (sourceCoefficient 92 94 1 0) v4739_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4739_pb : Scalar.QComplex := ((-1200006061568003154658149 : Int)/10^30,(-431475851803600601409046613 : Int)/10^30)
theorem v4739_pb_checked : Scalar.distance (sourceCoefficient 92 94 1 1) v4739_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4739_pg : Scalar.QComplex := ((-93086069839540812465073 : Int)/10^30,(258887832512668329690 : Int)/10^30)
theorem v4739_pg_checked : Scalar.distance (sourceCoefficient 92 94 1 2) v4739_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4739_mb : Scalar.QComplex := ((-1572349841906430580807726 : Int)/10^30,(-431474655594236687876549611 : Int)/10^30)
theorem v4739_mb_checked : Scalar.distance (sourceCoefficient 92 94 3 1) v4739_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4739_mg : Scalar.QComplex := ((-93085811770803184357157 : Int)/10^30,(339216821947465398746 : Int)/10^30)
theorem v4739_mg_checked : Scalar.distance (sourceCoefficient 92 94 3 2) v4739_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4739_upper : Scalar.QComplex := ((999989843180888819841323962990 : Int)/10^30,(-4507053922617951119465624702 : Int)/10^30)
theorem v4739_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 92 94 5) 1) 14) v4739_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4739 : Material (92 : Basis) (94 : Basis) where
  plus := ![v4739_pa,v4739_pb,v4739_pg]
  minus := ![(Primitive.Addresses.material4739 1).one,v4739_mb,v4739_mg]
  upper := v4739_upper
  lower := (Primitive.Addresses.material4739 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4739_pa_checked.trans (by decide +kernel)
    · exact v4739_pb_checked.trans (by decide +kernel)
    · exact v4739_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 92 94 Primitive.Addresses.material4739
    · exact v4739_mb_checked.trans (by decide +kernel)
    · exact v4739_mg_checked.trans (by decide +kernel)
  upper_error := v4739_upper_checked
  lower_error := reuse_lower_error 92 94 Primitive.Addresses.material4739

def v4740_pa : Scalar.QComplex := ((999996008466079690274778594287 : Int)/10^30,(-2825429508636945884703677389 : Int)/10^30)
theorem v4740_pa_checked : Scalar.distance (sourceCoefficient 92 95 1 0) v4740_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4740_pb : Scalar.QComplex := ((-1219109316871675451296791 : Int)/10^30,(-431475797583642231419244901 : Int)/10^30)
theorem v4740_pb_checked : Scalar.distance (sourceCoefficient 92 95 1 1) v4740_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4740_pg : Scalar.QComplex := ((-93086058214221342669232 : Int)/10^30,(263009145531083287520 : Int)/10^30)
theorem v4740_pg_checked : Scalar.distance (sourceCoefficient 92 95 1 2) v4740_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4740_mb : Scalar.QComplex := ((-1591453043307705768965027 : Int)/10^30,(-431474584889049558066151058 : Int)/10^30)
theorem v4740_mb_checked : Scalar.distance (sourceCoefficient 92 95 3 1) v4740_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4740_mg : Scalar.QComplex := ((-93085796588980525354870 : Int)/10^30,(343338123399200049029 : Int)/10^30)
theorem v4740_mg_checked : Scalar.distance (sourceCoefficient 92 95 3 2) v4740_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4740_upper : Scalar.QComplex := ((999989642654481918250657621279 : Int)/10^30,(-4551327692174813922476205217 : Int)/10^30)
theorem v4740_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 92 95 5) 1) 14) v4740_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4740 : Material (92 : Basis) (95 : Basis) where
  plus := ![v4740_pa,v4740_pb,v4740_pg]
  minus := ![(Primitive.Addresses.material4740 1).one,v4740_mb,v4740_mg]
  upper := v4740_upper
  lower := (Primitive.Addresses.material4740 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4740_pa_checked.trans (by decide +kernel)
    · exact v4740_pb_checked.trans (by decide +kernel)
    · exact v4740_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 92 95 Primitive.Addresses.material4740
    · exact v4740_mb_checked.trans (by decide +kernel)
    · exact v4740_mg_checked.trans (by decide +kernel)
  upper_error := v4740_upper_checked
  lower_error := reuse_lower_error 92 95 Primitive.Addresses.material4740

def v4741_pa : Scalar.QComplex := ((999995948159793547706279574035 : Int)/10^30,(-2846693519769124850755347068 : Int)/10^30)
theorem v4741_pa_checked : Scalar.distance (sourceCoefficient 92 96 1 0) v4741_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4741_pb : Scalar.QComplex := ((-1228284258458628229128114 : Int)/10^30,(-431475771141918321813319869 : Int)/10^30)
theorem v4741_pb_checked : Scalar.distance (sourceCoefficient 92 96 1 1) v4741_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4741_pg : Scalar.QComplex := ((-93086052555120400756339 : Int)/10^30,(264988536280754982682 : Int)/10^30)
theorem v4741_pg_checked : Scalar.distance (sourceCoefficient 92 96 1 2) v4741_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4741_mb : Scalar.QComplex := ((-1600627958660391635475720 : Int)/10^30,(-431474550529774128411716120 : Int)/10^30)
theorem v4741_mb_checked : Scalar.distance (sourceCoefficient 92 96 3 1) v4741_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4741_mg : Scalar.QComplex := ((-93085789221756622067238 : Int)/10^30,(345317508528304869036 : Int)/10^30)
theorem v4741_mg_checked : Scalar.distance (sourceCoefficient 92 96 3 2) v4741_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4741_upper : Scalar.QComplex := ((999989545648531436691351152590 : Int)/10^30,(-4572591567553567214827975875 : Int)/10^30)
theorem v4741_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 92 96 5) 1) 14) v4741_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4741 : Material (92 : Basis) (96 : Basis) where
  plus := ![v4741_pa,v4741_pb,v4741_pg]
  minus := ![(Primitive.Addresses.material4741 1).one,v4741_mb,v4741_mg]
  upper := v4741_upper
  lower := (Primitive.Addresses.material4741 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4741_pa_checked.trans (by decide +kernel)
    · exact v4741_pb_checked.trans (by decide +kernel)
    · exact v4741_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 92 96 Primitive.Addresses.material4741
    · exact v4741_mb_checked.trans (by decide +kernel)
    · exact v4741_mg_checked.trans (by decide +kernel)
  upper_error := v4741_upper_checked
  lower_error := reuse_lower_error 92 96 Primitive.Addresses.material4741

def v4742_pa : Scalar.QComplex := ((999995737213022152141131067968 : Int)/10^30,(-2919855438946061800147074903 : Int)/10^30)
theorem v4742_pa_checked : Scalar.distance (sourceCoefficient 92 97 1 0) v4742_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4742_pb : Scalar.QComplex := ((-1259851976181858976732093 : Int)/10^30,(-431475678178098293918323936 : Int)/10^30)
theorem v4742_pb_checked : Scalar.distance (sourceCoefficient 92 97 1 1) v4742_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4742_pg : Scalar.QComplex := ((-93086032709029359877935 : Int)/10^30,(271798917516256569257 : Int)/10^30)
theorem v4742_pg_checked : Scalar.distance (sourceCoefficient 92 97 1 2) v4742_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4742_mb : Scalar.QComplex := ((-1632195584405928609703667 : Int)/10^30,(-431474430324470077275583001 : Int)/10^30)
theorem v4742_mb_checked : Scalar.distance (sourceCoefficient 92 97 3 1) v4742_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4742_mg : Scalar.QComplex := ((-93085763498620692742231 : Int)/10^30,(352127870101707538318 : Int)/10^30)
theorem v4742_mg_checked : Scalar.distance (sourceCoefficient 92 97 3 2) v4742_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4742_upper : Scalar.QComplex := ((999989208431238919630263687308 : Int)/10^30,(-4645753013689429265774430831 : Int)/10^30)
theorem v4742_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 92 97 5) 1) 14) v4742_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4742 : Material (92 : Basis) (97 : Basis) where
  plus := ![v4742_pa,v4742_pb,v4742_pg]
  minus := ![(Primitive.Addresses.material4742 1).one,v4742_mb,v4742_mg]
  upper := v4742_upper
  lower := (Primitive.Addresses.material4742 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4742_pa_checked.trans (by decide +kernel)
    · exact v4742_pb_checked.trans (by decide +kernel)
    · exact v4742_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 92 97 Primitive.Addresses.material4742
    · exact v4742_mb_checked.trans (by decide +kernel)
    · exact v4742_mg_checked.trans (by decide +kernel)
  upper_error := v4742_upper_checked
  lower_error := reuse_lower_error 92 97 Primitive.Addresses.material4742

def v4743_pa : Scalar.QComplex := ((999996026383482943800853615480 : Int)/10^30,(-2819080921946756332759007436 : Int)/10^30)
theorem v4743_pa_checked : Scalar.distance (sourceCoefficient 93 94 1 0) v4743_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4743_pb : Scalar.QComplex := ((-1216370047294963165347014 : Int)/10^30,(-431475806330126246693826116 : Int)/10^30)
theorem v4743_pb_checked : Scalar.distance (sourceCoefficient 93 94 1 1) v4743_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4743_pg : Scalar.QComplex := ((-93086059991632746638357 : Int)/10^30,(262418178570811857257 : Int)/10^30)
theorem v4743_pg_checked : Scalar.distance (sourceCoefficient 93 94 1 2) v4743_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4743_mb : Scalar.QComplex := ((-1588713782298770515394614 : Int)/10^30,(-431474595999396589205755415 : Int)/10^30)
theorem v4743_mb_checked : Scalar.distance (sourceCoefficient 93 94 3 1) v4743_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4743_mg : Scalar.QComplex := ((-93085798876369138062890 : Int)/10^30,(342747158192798616587 : Int)/10^30)
theorem v4743_mg_checked : Scalar.distance (sourceCoefficient 93 94 3 2) v4743_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4743_upper : Scalar.QComplex := ((999989671528943173890936012117 : Int)/10^30,(-4544979145863911049649840995 : Int)/10^30)
theorem v4743_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 93 94 5) 1) 14) v4743_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4743 : Material (93 : Basis) (94 : Basis) where
  plus := ![v4743_pa,v4743_pb,v4743_pg]
  minus := ![(Primitive.Addresses.material4743 1).one,v4743_mb,v4743_mg]
  upper := v4743_upper
  lower := (Primitive.Addresses.material4743 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4743_pa_checked.trans (by decide +kernel)
    · exact v4743_pb_checked.trans (by decide +kernel)
    · exact v4743_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 93 94 Primitive.Addresses.material4743
    · exact v4743_mb_checked.trans (by decide +kernel)
    · exact v4743_mg_checked.trans (by decide +kernel)
  upper_error := v4743_upper_checked
  lower_error := reuse_lower_error 93 94 Primitive.Addresses.material4743

def v4744_pa : Scalar.QComplex := ((999995900590764144984455158571 : Int)/10^30,(-2863354966914501866102911497 : Int)/10^30)
theorem v4744_pa_checked : Scalar.distance (sourceCoefficient 93 95 1 0) v4744_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4744_pb : Scalar.QComplex := ((-1235473301235475737691223 : Int)/10^30,(-431475751627166095708930213 : Int)/10^30)
theorem v4744_pb_checked : Scalar.distance (sourceCoefficient 93 95 1 1) v4744_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4744_pg : Scalar.QComplex := ((-93086048236060513073565 : Int)/10^30,(266539491221618809207 : Int)/10^30)
theorem v4744_pg_checked : Scalar.distance (sourceCoefficient 93 95 1 2) v4744_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4744_mb : Scalar.QComplex := ((-1607816981920077703418065 : Int)/10^30,(-431474524811209034589347640 : Int)/10^30)
theorem v4744_mb_checked : Scalar.distance (sourceCoefficient 93 95 3 1) v4744_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4744_mg : Scalar.QComplex := ((-93085783564294081019861 : Int)/10^30,(346868459164523129101 : Int)/10^30)
theorem v4744_mg_checked : Scalar.distance (sourceCoefficient 93 95 3 2) v4744_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4744_upper : Scalar.QComplex := ((999989469323426624207966788978 : Int)/10^30,(-4589252907783846577742613165 : Int)/10^30)
theorem v4744_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 93 95 5) 1) 14) v4744_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4744 : Material (93 : Basis) (95 : Basis) where
  plus := ![v4744_pa,v4744_pb,v4744_pg]
  minus := ![(Primitive.Addresses.material4744 1).one,v4744_mb,v4744_mg]
  upper := v4744_upper
  lower := (Primitive.Addresses.material4744 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4744_pa_checked.trans (by decide +kernel)
    · exact v4744_pb_checked.trans (by decide +kernel)
    · exact v4744_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 93 95 Primitive.Addresses.material4744
    · exact v4744_mb_checked.trans (by decide +kernel)
    · exact v4744_mg_checked.trans (by decide +kernel)
  upper_error := v4744_upper_checked
  lower_error := reuse_lower_error 93 95 Primitive.Addresses.material4744

def v4745_pa : Scalar.QComplex := ((999995839478027416596740445674 : Int)/10^30,(-2884618975744235474680294747 : Int)/10^30)
theorem v4745_pa_checked : Scalar.distance (sourceCoefficient 93 96 1 0) v4745_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4745_pb : Scalar.QComplex := ((-1244648242160126243853627 : Int)/10^30,(-431475724953465321487056889 : Int)/10^30)
theorem v4745_pb_checked : Scalar.distance (sourceCoefficient 93 96 1 1) v4745_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4745_pg : Scalar.QComplex := ((-93086042514401566317745 : Int)/10^30,(268518881792685155999 : Int)/10^30)
theorem v4745_pg_checked : Scalar.distance (sourceCoefficient 93 96 1 2) v4745_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4745_mb : Scalar.QComplex := ((-1616991896410275958551821 : Int)/10^30,(-431474490219957398231584435 : Int)/10^30)
theorem v4745_mb_checked : Scalar.distance (sourceCoefficient 93 96 3 1) v4745_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4745_mg : Scalar.QComplex := ((-93085776134512350310878 : Int)/10^30,(348847844061037926570 : Int)/10^30)
theorem v4745_mg_checked : Scalar.distance (sourceCoefficient 93 96 3 2) v4745_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4745_upper : Scalar.QComplex := ((999989371511030731754670654411 : Int)/10^30,(-4610516779468297391343672911 : Int)/10^30)
theorem v4745_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 93 96 5) 1) 14) v4745_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4745 : Material (93 : Basis) (96 : Basis) where
  plus := ![v4745_pa,v4745_pb,v4745_pg]
  minus := ![(Primitive.Addresses.material4745 1).one,v4745_mb,v4745_mg]
  upper := v4745_upper
  lower := (Primitive.Addresses.material4745 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4745_pa_checked.trans (by decide +kernel)
    · exact v4745_pb_checked.trans (by decide +kernel)
    · exact v4745_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 93 96 Primitive.Addresses.material4745
    · exact v4745_mb_checked.trans (by decide +kernel)
    · exact v4745_mg_checked.trans (by decide +kernel)
  upper_error := v4745_upper_checked
  lower_error := reuse_lower_error 93 96 Primitive.Addresses.material4745

def v4746_pa : Scalar.QComplex := ((999995625756545635473737150619 : Int)/10^30,(-2957780886868270787459797144 : Int)/10^30)
theorem v4746_pa_checked : Scalar.distance (sourceCoefficient 93 97 1 0) v4746_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4746_pb : Scalar.QComplex := ((-1276215957566926322328186 : Int)/10^30,(-431475631191495195016405656 : Int)/10^30)
theorem v4746_pb_checked : Scalar.distance (sourceCoefficient 93 97 1 1) v4746_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4746_pg : Scalar.QComplex := ((-93086022453070622777545 : Int)/10^30,(275329262403506857629 : Int)/10^30)
theorem v4746_pg_checked : Scalar.distance (sourceCoefficient 93 97 1 2) v4746_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4746_mb : Scalar.QComplex := ((-1648559519150615538438572 : Int)/10^30,(-431474369216505544682894271 : Int)/10^30)
theorem v4746_mb_checked : Scalar.distance (sourceCoefficient 93 97 3 1) v4746_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4746_mg : Scalar.QComplex := ((-93085750196137137538334 : Int)/10^30,(355658204824018601551 : Int)/10^30)
theorem v4746_mg_checked : Scalar.distance (sourceCoefficient 93 97 3 2) v4746_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4746_upper : Scalar.QComplex := ((999989031519045860318578573614 : Int)/10^30,(-4683678212762371393815923475 : Int)/10^30)
theorem v4746_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 93 97 5) 1) 14) v4746_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4746 : Material (93 : Basis) (97 : Basis) where
  plus := ![v4746_pa,v4746_pb,v4746_pg]
  minus := ![(Primitive.Addresses.material4746 1).one,v4746_mb,v4746_mg]
  upper := v4746_upper
  lower := (Primitive.Addresses.material4746 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4746_pa_checked.trans (by decide +kernel)
    · exact v4746_pb_checked.trans (by decide +kernel)
    · exact v4746_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 93 97 Primitive.Addresses.material4746
    · exact v4746_mb_checked.trans (by decide +kernel)
    · exact v4746_mg_checked.trans (by decide +kernel)
  upper_error := v4746_upper_checked
  lower_error := reuse_lower_error 93 97 Primitive.Addresses.material4746

def v4747_pa : Scalar.QComplex := ((999995771313140805586704338255 : Int)/10^30,(-2908153337875476171297437620 : Int)/10^30)
theorem v4747_pa_checked : Scalar.distance (sourceCoefficient 94 95 1 0) v4747_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4747_pb : Scalar.QComplex := ((-1254802792506338425766051 : Int)/10^30,(-431475696276365974568555097 : Int)/10^30)
theorem v4747_pb_checked : Scalar.distance (sourceCoefficient 94 95 1 1) v4747_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4747_pg : Scalar.QComplex := ((-93086036248407518222957 : Int)/10^30,(270709611771581847781 : Int)/10^30)
theorem v4747_pg_checked : Scalar.distance (sourceCoefficient 94 95 1 2) v4747_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4747_mb : Scalar.QComplex := ((-1627146418228439792910958 : Int)/10^30,(-431474452779949124296851889 : Int)/10^30)
theorem v4747_mb_checked : Scalar.distance (sourceCoefficient 94 95 3 1) v4747_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4747_mg : Scalar.QComplex := ((-93085767978019330359764 : Int)/10^30,(351038567816955072293 : Int)/10^30)
theorem v4747_mg_checked : Scalar.distance (sourceCoefficient 94 95 3 2) v4747_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4747_upper : Scalar.QComplex := ((999989262728071626469269284191 : Int)/10^30,(-4634050988901459813456388521 : Int)/10^30)
theorem v4747_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 94 95 5) 1) 14) v4747_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4747 : Material (94 : Basis) (95 : Basis) where
  plus := ![v4747_pa,v4747_pb,v4747_pg]
  minus := ![(Primitive.Addresses.material4747 1).one,v4747_mb,v4747_mg]
  upper := v4747_upper
  lower := (Primitive.Addresses.material4747 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4747_pa_checked.trans (by decide +kernel)
    · exact v4747_pb_checked.trans (by decide +kernel)
    · exact v4747_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 94 95 Primitive.Addresses.material4747
    · exact v4747_mb_checked.trans (by decide +kernel)
    · exact v4747_mg_checked.trans (by decide +kernel)
  upper_error := v4747_upper_checked
  lower_error := reuse_lower_error 94 95 Primitive.Addresses.material4747

def v4748_pa : Scalar.QComplex := ((999995709247807216669644313410 : Int)/10^30,(-2929417343946109846684332522 : Int)/10^30)
theorem v4748_pa_checked : Scalar.distance (sourceCoefficient 94 96 1 0) v4748_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4748_pb : Scalar.QComplex := ((-1263977732637329204433005 : Int)/10^30,(-431475669328649114287060809 : Int)/10^30)
theorem v4748_pb_checked : Scalar.distance (sourceCoefficient 94 96 1 1) v4748_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4748_pg : Scalar.QComplex := ((-93086030452853704142279 : Int)/10^30,(272689002128619226028 : Int)/10^30)
theorem v4748_pg_checked : Scalar.distance (sourceCoefficient 94 96 1 2) v4748_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4748_mb : Scalar.QComplex := ((-1636321331688515075021988 : Int)/10^30,(-431474417914682188800779437 : Int)/10^30)
theorem v4748_mb_checked : Scalar.distance (sourceCoefficient 94 96 3 1) v4748_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4748_mg : Scalar.QComplex := ((-93085760474342944537719 : Int)/10^30,(353017952435673038508 : Int)/10^30)
theorem v4748_mg_checked : Scalar.distance (sourceCoefficient 94 96 3 2) v4748_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4748_upper : Scalar.QComplex := ((999989163963085054223932804468 : Int)/10^30,(-4655314856182719040860673480 : Int)/10^30)
theorem v4748_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 94 96 5) 1) 14) v4748_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4748 : Material (94 : Basis) (96 : Basis) where
  plus := ![v4748_pa,v4748_pb,v4748_pg]
  minus := ![(Primitive.Addresses.material4748 1).one,v4748_mb,v4748_mg]
  upper := v4748_upper
  lower := (Primitive.Addresses.material4748 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4748_pa_checked.trans (by decide +kernel)
    · exact v4748_pb_checked.trans (by decide +kernel)
    · exact v4748_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 94 96 Primitive.Addresses.material4748
    · exact v4748_mb_checked.trans (by decide +kernel)
    · exact v4748_mg_checked.trans (by decide +kernel)
  upper_error := v4748_upper_checked
  lower_error := reuse_lower_error 94 96 Primitive.Addresses.material4748

def v4749_pa : Scalar.QComplex := ((999995492248777569034987027561 : Int)/10^30,(-3002579245422316359698129142 : Int)/10^30)
theorem v4749_pa_checked : Scalar.distance (sourceCoefficient 94 97 1 0) v4749_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4749_pb : Scalar.QComplex := ((-1295545445268915135568505 : Int)/10^30,(-431475574623886842917814723 : Int)/10^30)
theorem v4749_pb_checked : Scalar.distance (sourceCoefficient 94 97 1 1) v4749_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4749_pg : Scalar.QComplex := ((-93086010137276736247387 : Int)/10^30,(279499381991039312824 : Int)/10^30)
theorem v4749_pg_checked : Scalar.distance (sourceCoefficient 94 97 1 2) v4749_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4749_mb : Scalar.QComplex := ((-1667888950840054381643204 : Int)/10^30,(-431474295968440936282915844 : Int)/10^30)
theorem v4749_mb_checked : Scalar.distance (sourceCoefficient 94 97 3 1) v4749_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4749_mg : Scalar.QComplex := ((-93085734281722447914785 : Int)/10^30,(359828312230849509118 : Int)/10^30)
theorem v4749_mg_checked : Scalar.distance (sourceCoefficient 94 97 3 2) v4749_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4749_upper : Scalar.QComplex := ((999988820693573849075990288187 : Int)/10^30,(-4728476274172228332095569312 : Int)/10^30)
theorem v4749_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 94 97 5) 1) 14) v4749_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4749 : Material (94 : Basis) (97 : Basis) where
  plus := ![v4749_pa,v4749_pb,v4749_pg]
  minus := ![(Primitive.Addresses.material4749 1).one,v4749_mb,v4749_mg]
  upper := v4749_upper
  lower := (Primitive.Addresses.material4749 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4749_pa_checked.trans (by decide +kernel)
    · exact v4749_pb_checked.trans (by decide +kernel)
    · exact v4749_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 94 97 Primitive.Addresses.material4749
    · exact v4749_mb_checked.trans (by decide +kernel)
    · exact v4749_mg_checked.trans (by decide +kernel)
  upper_error := v4749_upper_checked
  lower_error := reuse_lower_error 94 97 Primitive.Addresses.material4749

def v4750_pa : Scalar.QComplex := ((999995578570029303288137109840 : Int)/10^30,(-2973691374764778435623412326 : Int)/10^30)
theorem v4750_pa_checked : Scalar.distance (sourceCoefficient 95 96 1 0) v4750_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4750_pb : Scalar.QComplex := ((-1283080982507836039621448 : Int)/10^30,(-431475613220493507744647268 : Int)/10^30)
theorem v4750_pb_checked : Scalar.distance (sourceCoefficient 95 96 1 1) v4750_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4750_pg : Scalar.QComplex := ((-93086018318337543500455 : Int)/10^30,(276810313681853629501 : Int)/10^30)
theorem v4750_pg_checked : Scalar.distance (sourceCoefficient 95 96 1 2) v4750_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4750_mb : Scalar.QComplex := ((-1655424526027197650846650 : Int)/10^30,(-431474345321303214076987644 : Int)/10^30)
theorem v4750_mb_checked : Scalar.distance (sourceCoefficient 95 96 3 1) v4750_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4750_mg : Scalar.QComplex := ((-93085744783325048671478 : Int)/10^30,(357139251982813869156 : Int)/10^30)
theorem v4750_mg_checked : Scalar.distance (sourceCoefficient 95 96 3 2) v4750_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4750_upper : Scalar.QComplex := ((999988956872541085720778435003 : Int)/10^30,(-4699588595522429835298311366 : Int)/10^30)
theorem v4750_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 95 96 5) 1) 14) v4750_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4750 : Material (95 : Basis) (96 : Basis) where
  plus := ![v4750_pa,v4750_pb,v4750_pg]
  minus := ![(Primitive.Addresses.material4750 1).one,v4750_mb,v4750_mg]
  upper := v4750_upper
  lower := (Primitive.Addresses.material4750 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4750_pa_checked.trans (by decide +kernel)
    · exact v4750_pb_checked.trans (by decide +kernel)
    · exact v4750_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 95 96 Primitive.Addresses.material4750
    · exact v4750_mb_checked.trans (by decide +kernel)
    · exact v4750_mg_checked.trans (by decide +kernel)
  upper_error := v4750_upper_checked
  lower_error := reuse_lower_error 95 96 Primitive.Addresses.material4750

def v4751_pa : Scalar.QComplex := ((999995358331813479021432710892 : Int)/10^30,(-3046853266561815144745585653 : Int)/10^30)
theorem v4751_pa_checked : Scalar.distance (sourceCoefficient 95 97 1 0) v4751_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4751_pb : Scalar.QComplex := ((-1314648692355192528438533 : Int)/10^30,(-431475517583973895108657098 : Int)/10^30)
theorem v4751_pb_checked : Scalar.distance (sourceCoefficient 95 97 1 1) v4751_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4751_pg : Scalar.QComplex := ((-93085997751490345071867 : Int)/10^30,(283620692793440915905 : Int)/10^30)
theorem v4751_pg_checked : Scalar.distance (sourceCoefficient 95 97 1 2) v4751_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4751_mb : Scalar.QComplex := ((-1686992141590443931124962 : Int)/10^30,(-431474222443307369892833216 : Int)/10^30)
theorem v4751_mb_checked : Scalar.distance (sourceCoefficient 95 97 3 1) v4751_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4751_mg : Scalar.QComplex := ((-93085718339435063009129 : Int)/10^30,(363949610810322926783 : Int)/10^30)
theorem v4751_mg_checked : Scalar.distance (sourceCoefficient 95 97 3 2) v4751_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4751_upper : Scalar.QComplex := ((999988610363865233697091453550 : Int)/10^30,(-4772749998242242254435560021 : Int)/10^30)
theorem v4751_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 95 97 5) 1) 14) v4751_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4751 : Material (95 : Basis) (97 : Basis) where
  plus := ![v4751_pa,v4751_pb,v4751_pg]
  minus := ![(Primitive.Addresses.material4751 1).one,v4751_mb,v4751_mg]
  upper := v4751_upper
  lower := (Primitive.Addresses.material4751 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4751_pa_checked.trans (by decide +kernel)
    · exact v4751_pb_checked.trans (by decide +kernel)
    · exact v4751_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 95 97 Primitive.Addresses.material4751
    · exact v4751_mb_checked.trans (by decide +kernel)
    · exact v4751_mg_checked.trans (by decide +kernel)
  upper_error := v4751_upper_checked
  lower_error := reuse_lower_error 95 97 Primitive.Addresses.material4751

def v4752_pa : Scalar.QComplex := ((999995293317151294909183157372 : Int)/10^30,(-3068117263819416557180167977 : Int)/10^30)
theorem v4752_pa_checked : Scalar.distance (sourceCoefficient 96 97 1 0) v4752_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4752_pb : Scalar.QComplex := ((-1323823629951099781098680 : Int)/10^30,(-431475489787877713001469189 : Int)/10^30)
theorem v4752_pb_checked : Scalar.distance (sourceCoefficient 96 97 1 1) v4752_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4752_pg : Scalar.QComplex := ((-93085991727151139892069 : Int)/10^30,(285600082466833536381 : Int)/10^30)
theorem v4752_pg_checked : Scalar.distance (sourceCoefficient 96 97 1 2) v4752_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4752_mb : Scalar.QComplex := ((-1696167051783323486007315 : Int)/10^30,(-431474186729663616124368529 : Int)/10^30)
theorem v4752_mb_checked : Scalar.distance (sourceCoefficient 96 97 3 1) v4752_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4752_mg : Scalar.QComplex := ((-93085710606973961229857 : Int)/10^30,(365928994547964901373 : Int)/10^30)
theorem v4752_mg_checked : Scalar.distance (sourceCoefficient 96 97 3 2) v4752_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4752_upper : Scalar.QComplex := ((999988508649569669429229328877 : Int)/10^30,(-4794013851620208750557023726 : Int)/10^30)
theorem v4752_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 96 97 5) 1) 14) v4752_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4752 : Material (96 : Basis) (97 : Basis) where
  plus := ![v4752_pa,v4752_pb,v4752_pg]
  minus := ![(Primitive.Addresses.material4752 1).one,v4752_mb,v4752_mg]
  upper := v4752_upper
  lower := (Primitive.Addresses.material4752 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4752_pa_checked.trans (by decide +kernel)
    · exact v4752_pb_checked.trans (by decide +kernel)
    · exact v4752_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 96 97 Primitive.Addresses.material4752
    · exact v4752_mb_checked.trans (by decide +kernel)
    · exact v4752_mg_checked.trans (by decide +kernel)
  upper_error := v4752_upper_checked
  lower_error := reuse_lower_error 96 97 Primitive.Addresses.material4752

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
