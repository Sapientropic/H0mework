import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B155
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B156

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3729_pa : Scalar.QComplex := ((999999045514686391463863569575 : Int)/10^30,(-1381654702222975238868890893 : Int)/10^30)
theorem v3729_pa_checked : Scalar.distance (sourceCoefficient 52 64 1 0) v3729_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3729_pb : Scalar.QComplex := ((-596152943401617588939734 : Int)/10^30,(-431477107430116599783545636 : Int)/10^30)
theorem v3729_pb_checked : Scalar.distance (sourceCoefficient 52 64 1 1) v3729_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3729_pg : Scalar.QComplex := ((-93086340860561443077666 : Int)/10^30,(128613303322234549030 : Int)/10^30)
theorem v3729_pg_checked : Scalar.distance (sourceCoefficient 52 64 1 2) v3729_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3729_mb : Scalar.QComplex := ((-968498032131290346876859 : Int)/10^30,(-431476432318329601845534827 : Int)/10^30)
theorem v3729_mb_checked : Scalar.distance (sourceCoefficient 52 64 3 1) v3729_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3729_mg : Scalar.QComplex := ((-93086195212774245813270 : Int)/10^30,(208942575143127146364 : Int)/10^30)
theorem v3729_mg_checked : Scalar.distance (sourceCoefficient 52 64 3 2) v3729_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3729_upper : Scalar.QComplex := ((999995171522902935518073622589 : Int)/10^30,(-3107560277764195996788449212 : Int)/10^30)
theorem v3729_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 64 5) 1) 14) v3729_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3729 : Material (52 : Basis) (64 : Basis) where
  plus := ![v3729_pa,v3729_pb,v3729_pg]
  minus := ![(Primitive.Addresses.material3729 1).one,v3729_mb,v3729_mg]
  upper := v3729_upper
  lower := (Primitive.Addresses.material3729 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3729_pa_checked.trans (by decide +kernel)
    · exact v3729_pb_checked.trans (by decide +kernel)
    · exact v3729_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 64 Primitive.Addresses.material3729
    · exact v3729_mb_checked.trans (by decide +kernel)
    · exact v3729_mg_checked.trans (by decide +kernel)
  upper_error := v3729_upper_checked
  lower_error := reuse_lower_error 52 64 Primitive.Addresses.material3729

def v3730_pa : Scalar.QComplex := ((999998995174440091173836124882 : Int)/10^30,(-1417621285867014089701864246 : Int)/10^30)
theorem v3730_pa_checked : Scalar.distance (sourceCoefficient 52 65 1 0) v3730_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3730_pb : Scalar.QComplex := ((-611671714419127143372762 : Int)/10^30,(-431477084813704324328583872 : Int)/10^30)
theorem v3730_pb_checked : Scalar.distance (sourceCoefficient 52 65 1 1) v3730_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3730_pg : Scalar.QComplex := ((-93086336077946050582047 : Int)/10^30,(131961304045558129202 : Int)/10^30)
theorem v3730_pg_checked : Scalar.distance (sourceCoefficient 52 65 1 2) v3730_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3730_mb : Scalar.QComplex := ((-984016777853507020297115 : Int)/10^30,(-431476396309925298904513608 : Int)/10^30)
theorem v3730_mb_checked : Scalar.distance (sourceCoefficient 52 65 3 1) v3730_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3730_mg : Scalar.QComplex := ((-93086187540986798230741 : Int)/10^30,(212290570492655363328 : Int)/10^30)
theorem v3730_mg_checked : Scalar.distance (sourceCoefficient 52 65 3 2) v3730_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3730_upper : Scalar.QComplex := ((999995059107671104480573548613 : Int)/10^30,(-3143526720957535158695293110 : Int)/10^30)
theorem v3730_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 65 5) 1) 14) v3730_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3730 : Material (52 : Basis) (65 : Basis) where
  plus := ![v3730_pa,v3730_pb,v3730_pg]
  minus := ![(Primitive.Addresses.material3730 1).one,v3730_mb,v3730_mg]
  upper := v3730_upper
  lower := (Primitive.Addresses.material3730 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3730_pa_checked.trans (by decide +kernel)
    · exact v3730_pb_checked.trans (by decide +kernel)
    · exact v3730_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 65 Primitive.Addresses.material3730
    · exact v3730_mb_checked.trans (by decide +kernel)
    · exact v3730_mg_checked.trans (by decide +kernel)
  upper_error := v3730_upper_checked
  lower_error := reuse_lower_error 52 65 Primitive.Addresses.material3730

def v3731_pa : Scalar.QComplex := ((999998970087270334600123127260 : Int)/10^30,(-1435208834494328573323870871 : Int)/10^30)
theorem v3731_pa_checked : Scalar.distance (sourceCoefficient 52 66 1 0) v3731_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3731_pb : Scalar.QComplex := ((-619260345529265284198272 : Int)/10^30,(-431477073483412658855569526 : Int)/10^30)
theorem v3731_pb_checked : Scalar.distance (sourceCoefficient 52 66 1 1) v3731_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3731_pg : Scalar.QComplex := ((-93086333688116919694733 : Int)/10^30,(133598466074633312535 : Int)/10^30)
theorem v3731_pg_checked : Scalar.distance (sourceCoefficient 52 66 1 2) v3731_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3731_mb : Scalar.QComplex := ((-991605396360519571333598 : Int)/10^30,(-431476378430990983425448891 : Int)/10^30)
theorem v3731_mb_checked : Scalar.distance (sourceCoefficient 52 66 3 1) v3731_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3731_mg : Scalar.QComplex := ((-93086183738361461134765 : Int)/10^30,(213927729849825395188 : Int)/10^30)
theorem v3731_mg_checked : Scalar.distance (sourceCoefficient 52 66 3 2) v3731_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3731_upper : Scalar.QComplex := ((999995003666025311502342263940 : Int)/10^30,(-3161114200092082830937029809 : Int)/10^30)
theorem v3731_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 66 5) 1) 14) v3731_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3731 : Material (52 : Basis) (66 : Basis) where
  plus := ![v3731_pa,v3731_pb,v3731_pg]
  minus := ![(Primitive.Addresses.material3731 1).one,v3731_mb,v3731_mg]
  upper := v3731_upper
  lower := (Primitive.Addresses.material3731 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3731_pa_checked.trans (by decide +kernel)
    · exact v3731_pb_checked.trans (by decide +kernel)
    · exact v3731_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 66 Primitive.Addresses.material3731
    · exact v3731_mb_checked.trans (by decide +kernel)
    · exact v3731_mg_checked.trans (by decide +kernel)
  upper_error := v3731_upper_checked
  lower_error := reuse_lower_error 52 66 Primitive.Addresses.material3731

def v3732_pa : Scalar.QComplex := ((999998927288357948076675049818 : Int)/10^30,(-1464725958462394308148419255 : Int)/10^30)
theorem v3732_pa_checked : Scalar.distance (sourceCoefficient 52 67 1 0) v3732_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3732_pb : Scalar.QComplex := ((-631996319523903527383257 : Int)/10^30,(-431477054067871791091084244 : Int)/10^30)
theorem v3732_pb_checked : Scalar.distance (sourceCoefficient 52 67 1 1) v3732_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3732_pg : Scalar.QComplex := ((-93086329601775483603911 : Int)/10^30,(136346109605766065290 : Int)/10^30)
theorem v3732_pg_checked : Scalar.distance (sourceCoefficient 52 67 1 2) v3732_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3732_mb : Scalar.QComplex := ((-1004341348858235308167791 : Int)/10^30,(-431476348024885394556785540 : Int)/10^30)
theorem v3732_mb_checked : Scalar.distance (sourceCoefficient 52 67 3 1) v3732_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3732_mg : Scalar.QComplex := ((-93086177280928928478903 : Int)/10^30,(216675368831556270430 : Int)/10^30)
theorem v3732_mg_checked : Scalar.distance (sourceCoefficient 52 67 3 2) v3732_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3732_upper : Scalar.QComplex := ((999994909923298472618693734608 : Int)/10^30,(-3190631206230819648137595896 : Int)/10^30)
theorem v3732_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 67 5) 1) 14) v3732_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3732 : Material (52 : Basis) (67 : Basis) where
  plus := ![v3732_pa,v3732_pb,v3732_pg]
  minus := ![(Primitive.Addresses.material3732 1).one,v3732_mb,v3732_mg]
  upper := v3732_upper
  lower := (Primitive.Addresses.material3732 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3732_pa_checked.trans (by decide +kernel)
    · exact v3732_pb_checked.trans (by decide +kernel)
    · exact v3732_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 67 Primitive.Addresses.material3732
    · exact v3732_mb_checked.trans (by decide +kernel)
    · exact v3732_mg_checked.trans (by decide +kernel)
  upper_error := v3732_upper_checked
  lower_error := reuse_lower_error 52 67 Primitive.Addresses.material3732

def v3733_pa : Scalar.QComplex := ((999998854077131761184454820354 : Int)/10^30,(-1513883887006665758470231408 : Int)/10^30)
theorem v3733_pa_checked : Scalar.distance (sourceCoefficient 52 68 1 0) v3733_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3733_pb : Scalar.QComplex := ((-653206857655937366013365 : Int)/10^30,(-431477020620660959616249294 : Int)/10^30)
theorem v3733_pb_checked : Scalar.distance (sourceCoefficient 52 68 1 1) v3733_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3733_pg : Scalar.QComplex := ((-93086322586359576532906 : Int)/10^30,(140922045349988825384 : Int)/10^30)
theorem v3733_pg_checked : Scalar.distance (sourceCoefficient 52 68 1 2) v3733_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3733_mb : Scalar.QComplex := ((-1025551850229179889653874 : Int)/10^30,(-431476296273947896237493407 : Int)/10^30)
theorem v3733_mb_checked : Scalar.distance (sourceCoefficient 52 68 3 1) v3733_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3733_mg : Scalar.QComplex := ((-93086166316689178799025 : Int)/10^30,(221251296817961057156 : Int)/10^30)
theorem v3733_mg_checked : Scalar.distance (sourceCoefficient 52 68 3 2) v3733_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3733_upper : Scalar.QComplex := ((999994751870056230276629034203 : Int)/10^30,(-3239788935204196299671927053 : Int)/10^30)
theorem v3733_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 68 5) 1) 14) v3733_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3733 : Material (52 : Basis) (68 : Basis) where
  plus := ![v3733_pa,v3733_pb,v3733_pg]
  minus := ![(Primitive.Addresses.material3733 1).one,v3733_mb,v3733_mg]
  upper := v3733_upper
  lower := (Primitive.Addresses.material3733 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3733_pa_checked.trans (by decide +kernel)
    · exact v3733_pb_checked.trans (by decide +kernel)
    · exact v3733_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 68 Primitive.Addresses.material3733
    · exact v3733_mb_checked.trans (by decide +kernel)
    · exact v3733_mg_checked.trans (by decide +kernel)
  upper_error := v3733_upper_checked
  lower_error := reuse_lower_error 52 68 Primitive.Addresses.material3733

def v3734_pa : Scalar.QComplex := ((999998821089622098363775284746 : Int)/10^30,(-1535519249626520743752411014 : Int)/10^30)
theorem v3734_pa_checked : Scalar.distance (sourceCoefficient 52 69 1 0) v3734_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3734_pb : Scalar.QComplex := ((-662542028731654229378816 : Int)/10^30,(-431477005459311872980090764 : Int)/10^30)
theorem v3734_pb_checked : Scalar.distance (sourceCoefficient 52 69 1 1) v3734_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3734_pg : Scalar.QComplex := ((-93086319415569418464871 : Int)/10^30,(142936003848228094886 : Int)/10^30)
theorem v3734_pg_checked : Scalar.distance (sourceCoefficient 52 69 1 2) v3734_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3734_mb : Scalar.QComplex := ((-1034887004745424503182990 : Int)/10^30,(-431476273056772257018620004 : Int)/10^30)
theorem v3734_mb_checked : Scalar.distance (sourceCoefficient 52 69 3 1) v3734_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3734_mg : Scalar.QComplex := ((-93086161407944722704209 : Int)/10^30,(223265251830062435988 : Int)/10^30)
theorem v3734_mg_checked : Scalar.distance (sourceCoefficient 52 69 3 2) v3734_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3734_upper : Scalar.QComplex := ((999994681541922561371655129239 : Int)/10^30,(-3261424208667271056373022183 : Int)/10^30)
theorem v3734_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 69 5) 1) 14) v3734_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3734 : Material (52 : Basis) (69 : Basis) where
  plus := ![v3734_pa,v3734_pb,v3734_pg]
  minus := ![(Primitive.Addresses.material3734 1).one,v3734_mb,v3734_mg]
  upper := v3734_upper
  lower := (Primitive.Addresses.material3734 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3734_pa_checked.trans (by decide +kernel)
    · exact v3734_pb_checked.trans (by decide +kernel)
    · exact v3734_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 69 Primitive.Addresses.material3734
    · exact v3734_mb_checked.trans (by decide +kernel)
    · exact v3734_mg_checked.trans (by decide +kernel)
  upper_error := v3734_upper_checked
  lower_error := reuse_lower_error 52 69 Primitive.Addresses.material3734

def v3735_pa : Scalar.QComplex := ((999998799134889782421901388325 : Int)/10^30,(-1549751198856817551759433938 : Int)/10^30)
theorem v3735_pa_checked : Scalar.distance (sourceCoefficient 52 70 1 0) v3735_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3735_pb : Scalar.QComplex := ((-668682793803892276972024 : Int)/10^30,(-431476995339195299835367428 : Int)/10^30)
theorem v3735_pb_checked : Scalar.distance (sourceCoefficient 52 70 1 1) v3735_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3735_pg : Scalar.QComplex := ((-93086317302074839951118 : Int)/10^30,(144260805073824186647 : Int)/10^30)
theorem v3735_pg_checked : Scalar.distance (sourceCoefficient 52 70 1 2) v3735_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3735_mb : Scalar.QComplex := ((-1041027758797970258060659 : Int)/10^30,(-431476257637455764506474279 : Int)/10^30)
theorem v3735_mb_checked : Scalar.distance (sourceCoefficient 52 70 3 1) v3735_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3735_mg : Scalar.QComplex := ((-93086158151207140283916 : Int)/10^30,(224590050738523852058 : Int)/10^30)
theorem v3735_mg_checked : Scalar.distance (sourceCoefficient 52 70 3 2) v3735_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3735_upper : Scalar.QComplex := ((999994635024169685280847528432 : Int)/10^30,(-3275656098808875028488821770 : Int)/10^30)
theorem v3735_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 70 5) 1) 14) v3735_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3735 : Material (52 : Basis) (70 : Basis) where
  plus := ![v3735_pa,v3735_pb,v3735_pg]
  minus := ![(Primitive.Addresses.material3735 1).one,v3735_mb,v3735_mg]
  upper := v3735_upper
  lower := (Primitive.Addresses.material3735 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3735_pa_checked.trans (by decide +kernel)
    · exact v3735_pb_checked.trans (by decide +kernel)
    · exact v3735_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 70 Primitive.Addresses.material3735
    · exact v3735_mb_checked.trans (by decide +kernel)
    · exact v3735_mg_checked.trans (by decide +kernel)
  upper_error := v3735_upper_checked
  lower_error := reuse_lower_error 52 70 Primitive.Addresses.material3735

def v3736_pa : Scalar.QComplex := ((999998761191998167624076387490 : Int)/10^30,(-1574043985732128911176868557 : Int)/10^30)
theorem v3736_pa_checked : Scalar.distance (sourceCoefficient 52 71 1 0) v3736_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3736_pb : Scalar.QComplex := ((-679164583235824398133196 : Int)/10^30,(-431476977795768111582798816 : Int)/10^30)
theorem v3736_pb_checked : Scalar.distance (sourceCoefficient 52 71 1 1) v3736_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3736_pg : Scalar.QComplex := ((-93086313643691974119465 : Int)/10^30,(146522133657619587121 : Int)/10^30)
theorem v3736_pg_checked : Scalar.distance (sourceCoefficient 52 71 1 2) v3736_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3736_mb : Scalar.QComplex := ((-1051509529187865595439048 : Int)/10^30,(-431476231048722910987698080 : Int)/10^30)
theorem v3736_mb_checked : Scalar.distance (sourceCoefficient 52 71 3 1) v3736_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3736_mg : Scalar.QComplex := ((-93086152541400915278666 : Int)/10^30,(226851375323303627198 : Int)/10^30)
theorem v3736_mg_checked : Scalar.distance (sourceCoefficient 52 71 3 2) v3736_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3736_upper : Scalar.QComplex := ((999994555154188259585587977567 : Int)/10^30,(-3299948784016945193430650241 : Int)/10^30)
theorem v3736_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 71 5) 1) 14) v3736_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3736 : Material (52 : Basis) (71 : Basis) where
  plus := ![v3736_pa,v3736_pb,v3736_pg]
  minus := ![(Primitive.Addresses.material3736 1).one,v3736_mb,v3736_mg]
  upper := v3736_upper
  lower := (Primitive.Addresses.material3736 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3736_pa_checked.trans (by decide +kernel)
    · exact v3736_pb_checked.trans (by decide +kernel)
    · exact v3736_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 71 Primitive.Addresses.material3736
    · exact v3736_mb_checked.trans (by decide +kernel)
    · exact v3736_mg_checked.trans (by decide +kernel)
  upper_error := v3736_upper_checked
  lower_error := reuse_lower_error 52 71 Primitive.Addresses.material3736

def v3737_pa : Scalar.QComplex := ((999998719348571398876502362301 : Int)/10^30,(-1600406578696227872131424388 : Int)/10^30)
theorem v3737_pa_checked : Scalar.distance (sourceCoefficient 52 72 1 0) v3737_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3737_pb : Scalar.QComplex := ((-690539447077059472637939 : Int)/10^30,(-431476958373463885731239016 : Int)/10^30)
theorem v3737_pb_checked : Scalar.distance (sourceCoefficient 52 72 1 1) v3737_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3737_pg : Scalar.QComplex := ((-93086309601092351188762 : Int)/10^30,(148976133058639667104 : Int)/10^30)
theorem v3737_pg_checked : Scalar.distance (sourceCoefficient 52 72 1 2) v3737_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3737_mb : Scalar.QComplex := ((-1062884372033145206093233 : Int)/10^30,(-431476201810430726811534693 : Int)/10^30)
theorem v3737_mb_checked : Scalar.distance (sourceCoefficient 52 72 3 1) v3737_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3737_mg : Scalar.QComplex := ((-93086146381111838542407 : Int)/10^30,(229305370322006174207 : Int)/10^30)
theorem v3737_mg_checked : Scalar.distance (sourceCoefficient 52 72 3 2) v3737_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3737_upper : Scalar.QComplex := ((999994467811379951423687497999 : Int)/10^30,(-3326311265499100105230809626 : Int)/10^30)
theorem v3737_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 72 5) 1) 14) v3737_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3737 : Material (52 : Basis) (72 : Basis) where
  plus := ![v3737_pa,v3737_pb,v3737_pg]
  minus := ![(Primitive.Addresses.material3737 1).one,v3737_mb,v3737_mg]
  upper := v3737_upper
  lower := (Primitive.Addresses.material3737 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3737_pa_checked.trans (by decide +kernel)
    · exact v3737_pb_checked.trans (by decide +kernel)
    · exact v3737_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 72 Primitive.Addresses.material3737
    · exact v3737_mb_checked.trans (by decide +kernel)
    · exact v3737_mg_checked.trans (by decide +kernel)
  upper_error := v3737_upper_checked
  lower_error := reuse_lower_error 52 72 Primitive.Addresses.material3737

def v3738_pa : Scalar.QComplex := ((999998704180653351615848213818 : Int)/10^30,(-1609856209153161963020926512 : Int)/10^30)
theorem v3738_pa_checked : Scalar.distance (sourceCoefficient 52 73 1 0) v3738_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3738_pb : Scalar.QComplex := ((-694616749277502264865597 : Int)/10^30,(-431476951314223982476547378 : Int)/10^30)
theorem v3738_pb_checked : Scalar.distance (sourceCoefficient 52 73 1 1) v3738_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3738_pg : Scalar.QComplex := ((-93086308133652812602616 : Int)/10^30,(149855765322105375087 : Int)/10^30)
theorem v3738_pg_checked : Scalar.distance (sourceCoefficient 52 73 1 2) v3738_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3738_mb : Scalar.QComplex := ((-1066961666623615947034094 : Int)/10^30,(-431476191232665287926613528 : Int)/10^30)
theorem v3738_mb_checked : Scalar.distance (sourceCoefficient 52 73 3 1) v3738_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3738_mg : Scalar.QComplex := ((-93086144154589820146648 : Int)/10^30,(230185000991610358544 : Int)/10^30)
theorem v3738_mg_checked : Scalar.distance (sourceCoefficient 52 73 3 2) v3738_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3738_upper : Scalar.QComplex := ((999994436334279590105450974772 : Int)/10^30,(-3335760855703469135290378049 : Int)/10^30)
theorem v3738_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 73 5) 1) 14) v3738_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3738 : Material (52 : Basis) (73 : Basis) where
  plus := ![v3738_pa,v3738_pb,v3738_pg]
  minus := ![(Primitive.Addresses.material3738 1).one,v3738_mb,v3738_mg]
  upper := v3738_upper
  lower := (Primitive.Addresses.material3738 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3738_pa_checked.trans (by decide +kernel)
    · exact v3738_pb_checked.trans (by decide +kernel)
    · exact v3738_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 73 Primitive.Addresses.material3738
    · exact v3738_mb_checked.trans (by decide +kernel)
    · exact v3738_mg_checked.trans (by decide +kernel)
  upper_error := v3738_upper_checked
  lower_error := reuse_lower_error 52 73 Primitive.Addresses.material3738

def v3739_pa : Scalar.QComplex := ((999998687006245326635354589091 : Int)/10^30,(-1620489366023155821055112897 : Int)/10^30)
theorem v3739_pa_checked : Scalar.distance (sourceCoefficient 52 74 1 0) v3739_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3739_pb : Scalar.QComplex := ((-699204716368513264668306 : Int)/10^30,(-431476943309417700776452738 : Int)/10^30)
theorem v3739_pb_checked : Scalar.distance (sourceCoefficient 52 74 1 1) v3739_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3739_pg : Scalar.QComplex := ((-93086306470827115738379 : Int)/10^30,(150845567817636284848 : Int)/10^30)
theorem v3739_pg_checked : Scalar.distance (sourceCoefficient 52 74 1 2) v3739_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3739_mb : Scalar.QComplex := ((-1071549625098529820383423 : Int)/10^30,(-431476179268653021606393321 : Int)/10^30)
theorem v3739_mb_checked : Scalar.distance (sourceCoefficient 52 74 3 1) v3739_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3739_mg : Scalar.QComplex := ((-93086141637609767834784 : Int)/10^30,(231174801683648877506 : Int)/10^30)
theorem v3739_mg_checked : Scalar.distance (sourceCoefficient 52 74 3 2) v3739_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3739_upper : Scalar.QComplex := ((999994400808033019234814528693 : Int)/10^30,(-3346393967095154692825100299 : Int)/10^30)
theorem v3739_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 74 5) 1) 14) v3739_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3739 : Material (52 : Basis) (74 : Basis) where
  plus := ![v3739_pa,v3739_pb,v3739_pg]
  minus := ![(Primitive.Addresses.material3739 1).one,v3739_mb,v3739_mg]
  upper := v3739_upper
  lower := (Primitive.Addresses.material3739 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3739_pa_checked.trans (by decide +kernel)
    · exact v3739_pb_checked.trans (by decide +kernel)
    · exact v3739_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 74 Primitive.Addresses.material3739
    · exact v3739_mb_checked.trans (by decide +kernel)
    · exact v3739_mg_checked.trans (by decide +kernel)
  upper_error := v3739_upper_checked
  lower_error := reuse_lower_error 52 74 Primitive.Addresses.material3739

def v3740_pa : Scalar.QComplex := ((999998662888742543230267652067 : Int)/10^30,(-1635304475333882478356342884 : Int)/10^30)
theorem v3740_pa_checked : Scalar.distance (sourceCoefficient 52 75 1 0) v3740_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3740_pb : Scalar.QComplex := ((-705597101443127879215486 : Int)/10^30,(-431476932047921976925491263 : Int)/10^30)
theorem v3740_pb_checked : Scalar.distance (sourceCoefficient 52 75 1 1) v3740_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3740_pg : Scalar.QComplex := ((-93086304133550379071722 : Int)/10^30,(152224653283183385857 : Int)/10^30)
theorem v3740_pg_checked : Scalar.distance (sourceCoefficient 52 75 1 2) v3740_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3740_mb : Scalar.QComplex := ((-1077941998074803714477259 : Int)/10^30,(-431476162490821073868876812 : Int)/10^30)
theorem v3740_mb_checked : Scalar.distance (sourceCoefficient 52 75 3 1) v3740_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3740_mg : Scalar.QComplex := ((-93086138110245256379601 : Int)/10^30,(232553884618734875666 : Int)/10^30)
theorem v3740_mg_checked : Scalar.distance (sourceCoefficient 52 75 3 2) v3740_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3740_upper : Scalar.QComplex := ((999994351121031501920662674951 : Int)/10^30,(-3361209012715894455392585787 : Int)/10^30)
theorem v3740_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 75 5) 1) 14) v3740_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3740 : Material (52 : Basis) (75 : Basis) where
  plus := ![v3740_pa,v3740_pb,v3740_pg]
  minus := ![(Primitive.Addresses.material3740 1).one,v3740_mb,v3740_mg]
  upper := v3740_upper
  lower := (Primitive.Addresses.material3740 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3740_pa_checked.trans (by decide +kernel)
    · exact v3740_pb_checked.trans (by decide +kernel)
    · exact v3740_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 75 Primitive.Addresses.material3740
    · exact v3740_mb_checked.trans (by decide +kernel)
    · exact v3740_mg_checked.trans (by decide +kernel)
  upper_error := v3740_upper_checked
  lower_error := reuse_lower_error 52 75 Primitive.Addresses.material3740

def v3741_pa : Scalar.QComplex := ((999998642484350790055958445013 : Int)/10^30,(-1647734643554947603874030430 : Int)/10^30)
theorem v3741_pa_checked : Scalar.distance (sourceCoefficient 52 76 1 0) v3741_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3741_pb : Scalar.QComplex := ((-710960438240755188341537 : Int)/10^30,(-431476922501888080462642675 : Int)/10^30)
theorem v3741_pb_checked : Scalar.distance (sourceCoefficient 52 76 1 1) v3741_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3741_pg : Scalar.QComplex := ((-93086302154139579910747 : Int)/10^30,(153381733117902342506 : Int)/10^30)
theorem v3741_pg_checked : Scalar.distance (sourceCoefficient 52 76 1 2) v3741_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3741_mb : Scalar.QComplex := ((-1083305324637618302005237 : Int)/10^30,(-431476148316472631200750625 : Int)/10^30)
theorem v3741_mb_checked : Scalar.distance (sourceCoefficient 52 76 3 1) v3741_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3741_mg : Scalar.QComplex := ((-93086135132327409822503 : Int)/10^30,(233710962314477758365 : Int)/10^30)
theorem v3741_mg_checked : Scalar.distance (sourceCoefficient 52 76 3 2) v3741_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3741_upper : Scalar.QComplex := ((999994309263327445184844310268 : Int)/10^30,(-3373639127207555071744177103 : Int)/10^30)
theorem v3741_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 76 5) 1) 14) v3741_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3741 : Material (52 : Basis) (76 : Basis) where
  plus := ![v3741_pa,v3741_pb,v3741_pg]
  minus := ![(Primitive.Addresses.material3741 1).one,v3741_mb,v3741_mg]
  upper := v3741_upper
  lower := (Primitive.Addresses.material3741 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3741_pa_checked.trans (by decide +kernel)
    · exact v3741_pb_checked.trans (by decide +kernel)
    · exact v3741_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 76 Primitive.Addresses.material3741
    · exact v3741_mb_checked.trans (by decide +kernel)
    · exact v3741_mg_checked.trans (by decide +kernel)
  upper_error := v3741_upper_checked
  lower_error := reuse_lower_error 52 76 Primitive.Addresses.material3741

def v3742_pa : Scalar.QComplex := ((999998637738535074544986958241 : Int)/10^30,(-1650612333073581273862748369 : Int)/10^30)
theorem v3742_pa_checked : Scalar.distance (sourceCoefficient 52 77 1 0) v3742_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3742_pb : Scalar.QComplex := ((-712202096254972275729277 : Int)/10^30,(-431476920279228694587917043 : Int)/10^30)
theorem v3742_pb_checked : Scalar.distance (sourceCoefficient 52 77 1 1) v3742_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3742_pg : Scalar.QComplex := ((-93086301693497157400510 : Int)/10^30,(153649606926433219387 : Int)/10^30)
theorem v3742_pg_checked : Scalar.distance (sourceCoefficient 52 77 1 2) v3742_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3742_mb : Scalar.QComplex := ((-1084546980271454418978152 : Int)/10^30,(-431476145022319128855379147 : Int)/10^30)
theorem v3742_mb_checked : Scalar.distance (sourceCoefficient 52 77 3 1) v3742_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3742_mg : Scalar.QComplex := ((-93086134440522126656823 : Int)/10^30,(233978835625753309830 : Int)/10^30)
theorem v3742_mg_checked : Scalar.distance (sourceCoefficient 52 77 3 2) v3742_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3742_upper : Scalar.QComplex := ((999994299550887750801010378570 : Int)/10^30,(-3376516804249360852951321018 : Int)/10^30)
theorem v3742_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 77 5) 1) 14) v3742_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3742 : Material (52 : Basis) (77 : Basis) where
  plus := ![v3742_pa,v3742_pb,v3742_pg]
  minus := ![(Primitive.Addresses.material3742 1).one,v3742_mb,v3742_mg]
  upper := v3742_upper
  lower := (Primitive.Addresses.material3742 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3742_pa_checked.trans (by decide +kernel)
    · exact v3742_pb_checked.trans (by decide +kernel)
    · exact v3742_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 77 Primitive.Addresses.material3742
    · exact v3742_mb_checked.trans (by decide +kernel)
    · exact v3742_mg_checked.trans (by decide +kernel)
  upper_error := v3742_upper_checked
  lower_error := reuse_lower_error 52 77 Primitive.Addresses.material3742

def v3743_pa : Scalar.QComplex := ((999998609033982007731470872419 : Int)/10^30,(-1667911898512050860352177868 : Int)/10^30)
theorem v3743_pa_checked : Scalar.distance (sourceCoefficient 52 78 1 0) v3743_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3743_pb : Scalar.QComplex := ((-719666467844927115649706 : Int)/10^30,(-431476906817045760694435393 : Int)/10^30)
theorem v3743_pb_checked : Scalar.distance (sourceCoefficient 52 78 1 1) v3743_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3743_pg : Scalar.QComplex := ((-93086298905337576885804 : Int)/10^30,(155259961493992232567 : Int)/10^30)
theorem v3743_pg_checked : Scalar.distance (sourceCoefficient 52 78 1 2) v3743_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3743_mb : Scalar.QComplex := ((-1092011337464825019585969 : Int)/10^30,(-431476125118724708233547884 : Int)/10^30)
theorem v3743_mb_checked : Scalar.distance (sourceCoefficient 52 78 3 1) v3743_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3743_mg : Scalar.QComplex := ((-93086130262700120175294 : Int)/10^30,(235589187187647576731 : Int)/10^30)
theorem v3743_mg_checked : Scalar.distance (sourceCoefficient 52 78 3 2) v3743_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3743_upper : Scalar.QComplex := ((999994240988896893565971584663 : Int)/10^30,(-3393816294380705331939753012 : Int)/10^30)
theorem v3743_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 78 5) 1) 14) v3743_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3743 : Material (52 : Basis) (78 : Basis) where
  plus := ![v3743_pa,v3743_pb,v3743_pg]
  minus := ![(Primitive.Addresses.material3743 1).one,v3743_mb,v3743_mg]
  upper := v3743_upper
  lower := (Primitive.Addresses.material3743 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3743_pa_checked.trans (by decide +kernel)
    · exact v3743_pb_checked.trans (by decide +kernel)
    · exact v3743_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 78 Primitive.Addresses.material3743
    · exact v3743_mb_checked.trans (by decide +kernel)
    · exact v3743_mg_checked.trans (by decide +kernel)
  upper_error := v3743_upper_checked
  lower_error := reuse_lower_error 52 78 Primitive.Addresses.material3743

def v3744_pa : Scalar.QComplex := ((999998599716350237313616490634 : Int)/10^30,(-1673488971798461830039585516 : Int)/10^30)
theorem v3744_pa_checked : Scalar.distance (sourceCoefficient 52 79 1 0) v3744_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3744_pb : Scalar.QComplex := ((-722072848926535203912441 : Int)/10^30,(-431476902440376511677953877 : Int)/10^30)
theorem v3744_pb_checked : Scalar.distance (sourceCoefficient 52 79 1 1) v3744_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3744_pg : Scalar.QComplex := ((-93086297999556417264533 : Int)/10^30,(155779111262745358821 : Int)/10^30)
theorem v3744_pg_checked : Scalar.distance (sourceCoefficient 52 79 1 2) v3744_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3744_mb : Scalar.QComplex := ((-1094417713873559010082000 : Int)/10^30,(-431476118665458594803955176 : Int)/10^30)
theorem v3744_mb_checked : Scalar.distance (sourceCoefficient 52 79 3 1) v3744_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3744_mg : Scalar.QComplex := ((-93086128908916429021415 : Int)/10^30,(236108335981449171878 : Int)/10^30)
theorem v3744_mg_checked : Scalar.distance (sourceCoefficient 52 79 3 2) v3744_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3744_upper : Scalar.QComplex := ((999994222045756456457072901367 : Int)/10^30,(-3399393343279333623776509508 : Int)/10^30)
theorem v3744_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 79 5) 1) 14) v3744_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3744 : Material (52 : Basis) (79 : Basis) where
  plus := ![v3744_pa,v3744_pb,v3744_pg]
  minus := ![(Primitive.Addresses.material3744 1).one,v3744_mb,v3744_mg]
  upper := v3744_upper
  lower := (Primitive.Addresses.material3744 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3744_pa_checked.trans (by decide +kernel)
    · exact v3744_pb_checked.trans (by decide +kernel)
    · exact v3744_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 79 Primitive.Addresses.material3744
    · exact v3744_mb_checked.trans (by decide +kernel)
    · exact v3744_mg_checked.trans (by decide +kernel)
  upper_error := v3744_upper_checked
  lower_error := reuse_lower_error 52 79 Primitive.Addresses.material3744

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
