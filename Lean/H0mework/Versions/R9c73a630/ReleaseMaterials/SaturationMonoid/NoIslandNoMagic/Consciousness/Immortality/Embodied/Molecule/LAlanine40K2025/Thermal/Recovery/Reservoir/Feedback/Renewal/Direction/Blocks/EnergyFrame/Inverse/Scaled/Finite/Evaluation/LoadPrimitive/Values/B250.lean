import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B166
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B167

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4001_pa : Scalar.QComplex := ((999998186578257497232259029016 : Int)/10^30,(-1904426474429275334675698655 : Int)/10^30)
theorem v4001_pa_checked : Scalar.distance (sourceCoefficient 58 87 1 0) v4001_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4001_pb : Scalar.QComplex := ((-821717166041649974659116 : Int)/10^30,(-431476713307154212803907875 : Int)/10^30)
theorem v4001_pb_checked : Scalar.distance (sourceCoefficient 58 87 1 1) v4001_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4001_pg : Scalar.QComplex := ((-93086258369096939948863 : Int)/10^30,(177276256320289551333 : Int)/10^30)
theorem v4001_pg_checked : Scalar.distance (sourceCoefficient 58 87 1 2) v4001_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4001_mb : Scalar.QComplex := ((-1194061830673087948800544 : Int)/10^30,(-431475843543748861975737876 : Int)/10^30)
theorem v4001_mb_checked : Scalar.distance (sourceCoefficient 58 87 3 1) v4001_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4001_mg : Scalar.QComplex := ((-93086070727403718748658 : Int)/10^30,(257605438835322152114 : Int)/10^30)
theorem v4001_mg_checked : Scalar.distance (sourceCoefficient 58 87 3 2) v4001_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4001_upper : Scalar.QComplex := ((999993410331099982832580735498 : Int)/10^30,(-3630329788916996310119099357 : Int)/10^30)
theorem v4001_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 87 5) 1) 14) v4001_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4001 : Material (58 : Basis) (87 : Basis) where
  plus := ![v4001_pa,v4001_pb,v4001_pg]
  minus := ![(Primitive.Addresses.material4001 1).one,v4001_mb,v4001_mg]
  upper := v4001_upper
  lower := (Primitive.Addresses.material4001 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4001_pa_checked.trans (by decide +kernel)
    · exact v4001_pb_checked.trans (by decide +kernel)
    · exact v4001_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 87 Primitive.Addresses.material4001
    · exact v4001_mb_checked.trans (by decide +kernel)
    · exact v4001_mg_checked.trans (by decide +kernel)
  upper_error := v4001_upper_checked
  lower_error := reuse_lower_error 58 87 Primitive.Addresses.material4001

def v4002_pa : Scalar.QComplex := ((999998164113832307328438443566 : Int)/10^30,(-1916186046527664911706144271 : Int)/10^30)
theorem v4002_pa_checked : Scalar.distance (sourceCoefficient 58 88 1 0) v4002_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4002_pb : Scalar.QComplex := ((-826791154822652915502912 : Int)/10^30,(-431476702602255089046029063 : Int)/10^30)
theorem v4002_pb_checked : Scalar.distance (sourceCoefficient 58 88 1 1) v4002_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4002_pg : Scalar.QComplex := ((-93086256168799481489050 : Int)/10^30,(178370912662844614578 : Int)/10^30)
theorem v4002_pg_checked : Scalar.distance (sourceCoefficient 58 88 1 2) v4002_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4002_mb : Scalar.QComplex := ((-1199135808326967160689869 : Int)/10^30,(-431475828460229930106990744 : Int)/10^30)
theorem v4002_mb_checked : Scalar.distance (sourceCoefficient 58 88 3 1) v4002_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4002_mg : Scalar.QComplex := ((-93086067582467957426639 : Int)/10^30,(258700092871529021828 : Int)/10^30)
theorem v4002_mg_checked : Scalar.distance (sourceCoefficient 58 88 3 2) v4002_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4002_upper : Scalar.QComplex := ((999993367570753629278038829680 : Int)/10^30,(-3642089304729324701932934052 : Int)/10^30)
theorem v4002_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 88 5) 1) 14) v4002_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4002 : Material (58 : Basis) (88 : Basis) where
  plus := ![v4002_pa,v4002_pb,v4002_pg]
  minus := ![(Primitive.Addresses.material4002 1).one,v4002_mb,v4002_mg]
  upper := v4002_upper
  lower := (Primitive.Addresses.material4002 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4002_pa_checked.trans (by decide +kernel)
    · exact v4002_pb_checked.trans (by decide +kernel)
    · exact v4002_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 88 Primitive.Addresses.material4002
    · exact v4002_mb_checked.trans (by decide +kernel)
    · exact v4002_mg_checked.trans (by decide +kernel)
  upper_error := v4002_upper_checked
  lower_error := reuse_lower_error 58 88 Primitive.Addresses.material4002

def v4003_pa : Scalar.QComplex := ((999998133153951042900829172203 : Int)/10^30,(-1932275501267877648222566062 : Int)/10^30)
theorem v4003_pa_checked : Scalar.distance (sourceCoefficient 58 89 1 0) v4003_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4003_pb : Scalar.QComplex := ((-833733389708039016897705 : Int)/10^30,(-431476687826914385971775977 : Int)/10^30)
theorem v4003_pb_checked : Scalar.distance (sourceCoefficient 58 89 1 1) v4003_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4003_pg : Scalar.QComplex := ((-93086253134020153725140 : Int)/10^30,(179868622222714067086 : Int)/10^30)
theorem v4003_pg_checked : Scalar.distance (sourceCoefficient 58 89 1 2) v4003_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4003_mb : Scalar.QComplex := ((-1206078027876988368336686 : Int)/10^30,(-431475807694058689131648408 : Int)/10^30)
theorem v4003_mb_checked : Scalar.distance (sourceCoefficient 58 89 3 1) v4003_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4003_mg : Scalar.QComplex := ((-93086063255233863816986 : Int)/10^30,(260197799254854878015 : Int)/10^30)
theorem v4003_mg_checked : Scalar.distance (sourceCoefficient 58 89 3 2) v4003_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4003_upper : Scalar.QComplex := ((999993308841979218281662234199 : Int)/10^30,(-3658178682072238199107756533 : Int)/10^30)
theorem v4003_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 89 5) 1) 14) v4003_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4003 : Material (58 : Basis) (89 : Basis) where
  plus := ![v4003_pa,v4003_pb,v4003_pg]
  minus := ![(Primitive.Addresses.material4003 1).one,v4003_mb,v4003_mg]
  upper := v4003_upper
  lower := (Primitive.Addresses.material4003 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4003_pa_checked.trans (by decide +kernel)
    · exact v4003_pb_checked.trans (by decide +kernel)
    · exact v4003_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 89 Primitive.Addresses.material4003
    · exact v4003_mb_checked.trans (by decide +kernel)
    · exact v4003_mg_checked.trans (by decide +kernel)
  upper_error := v4003_upper_checked
  lower_error := reuse_lower_error 58 89 Primitive.Addresses.material4003

def v4004_pa : Scalar.QComplex := ((999998082179352340948185521952 : Int)/10^30,(-1958478393366152773899166591 : Int)/10^30)
theorem v4004_pa_checked : Scalar.distance (sourceCoefficient 58 90 1 0) v4004_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4004_pb : Scalar.QComplex := ((-845039343233405406740497 : Int)/10^30,(-431476663445384506867965538 : Int)/10^30)
theorem v4004_pb_checked : Scalar.distance (sourceCoefficient 58 90 1 1) v4004_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4004_pg : Scalar.QComplex := ((-93086248131477808359559 : Int)/10^30,(182307755318597077176 : Int)/10^30)
theorem v4004_pg_checked : Scalar.distance (sourceCoefficient 58 90 1 2) v4004_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4004_mb : Scalar.QComplex := ((-1217383956152469370759242 : Int)/10^30,(-431475773556009197238852283 : Int)/10^30)
theorem v4004_mb_checked : Scalar.distance (sourceCoefficient 58 90 3 1) v4004_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4004_mg : Scalar.QComplex := ((-93086056147831373856159 : Int)/10^30,(262636927125568424712 : Int)/10^30)
theorem v4004_mg_checked : Scalar.distance (sourceCoefficient 58 90 3 2) v4004_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4004_upper : Scalar.QComplex := ((999993212643641783185229636738 : Int)/10^30,(-3684381447166850572227992755 : Int)/10^30)
theorem v4004_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 90 5) 1) 14) v4004_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4004 : Material (58 : Basis) (90 : Basis) where
  plus := ![v4004_pa,v4004_pb,v4004_pg]
  minus := ![(Primitive.Addresses.material4004 1).one,v4004_mb,v4004_mg]
  upper := v4004_upper
  lower := (Primitive.Addresses.material4004 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4004_pa_checked.trans (by decide +kernel)
    · exact v4004_pb_checked.trans (by decide +kernel)
    · exact v4004_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 90 Primitive.Addresses.material4004
    · exact v4004_mb_checked.trans (by decide +kernel)
    · exact v4004_mg_checked.trans (by decide +kernel)
  upper_error := v4004_upper_checked
  lower_error := reuse_lower_error 58 90 Primitive.Addresses.material4004

def v4005_pa : Scalar.QComplex := ((999998053161169349887361571567 : Int)/10^30,(-1973239435831037902926434546 : Int)/10^30)
theorem v4005_pa_checked : Scalar.distance (sourceCoefficient 58 91 1 0) v4005_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4005_pb : Scalar.QComplex := ((-851408398060494110029560 : Int)/10^30,(-431476649536446434468853481 : Int)/10^30)
theorem v4005_pb_checked : Scalar.distance (sourceCoefficient 58 91 1 1) v4005_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4005_pg : Scalar.QComplex := ((-93086245280529679612747 : Int)/10^30,(183681807719857752596 : Int)/10^30)
theorem v4005_pg_checked : Scalar.distance (sourceCoefficient 58 91 1 2) v4005_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4005_mb : Scalar.QComplex := ((-1223752996605280760573905 : Int)/10^30,(-431475754150868839576484369 : Int)/10^30)
theorem v4005_mb_checked : Scalar.distance (sourceCoefficient 58 91 3 1) v4005_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4005_mg : Scalar.QComplex := ((-93086052111138969382539 : Int)/10^30,(264010976554966760674 : Int)/10^30)
theorem v4005_mg_checked : Scalar.distance (sourceCoefficient 58 91 3 2) v4005_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4005_upper : Scalar.QComplex := ((999993158149281828219373816694 : Int)/10^30,(-3699142417564145570086336288 : Int)/10^30)
theorem v4005_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 91 5) 1) 14) v4005_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4005 : Material (58 : Basis) (91 : Basis) where
  plus := ![v4005_pa,v4005_pb,v4005_pg]
  minus := ![(Primitive.Addresses.material4005 1).one,v4005_mb,v4005_mg]
  upper := v4005_upper
  lower := (Primitive.Addresses.material4005 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4005_pa_checked.trans (by decide +kernel)
    · exact v4005_pb_checked.trans (by decide +kernel)
    · exact v4005_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 91 Primitive.Addresses.material4005
    · exact v4005_mb_checked.trans (by decide +kernel)
    · exact v4005_mg_checked.trans (by decide +kernel)
  upper_error := v4005_upper_checked
  lower_error := reuse_lower_error 58 91 Primitive.Addresses.material4005

def v4006_pa : Scalar.QComplex := ((999997989593528154042000136310 : Int)/10^30,(-2005195477243486593141606728 : Int)/10^30)
theorem v4006_pa_checked : Scalar.distance (sourceCoefficient 58 92 1 0) v4006_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4006_pb : Scalar.QComplex := ((-865196704343507735451475 : Int)/10^30,(-431476618995682649592434254 : Int)/10^30)
theorem v4006_pb_checked : Scalar.distance (sourceCoefficient 58 92 1 1) v4006_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4006_pg : Scalar.QComplex := ((-93086239027473874481301 : Int)/10^30,(186656480746893648600 : Int)/10^30)
theorem v4006_pg_checked : Scalar.distance (sourceCoefficient 58 92 1 2) v4006_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4006_mb : Scalar.QComplex := ((-1237541271398974158693717 : Int)/10^30,(-431475711711429106443744727 : Int)/10^30)
theorem v4006_mb_checked : Scalar.distance (sourceCoefficient 58 92 3 1) v4006_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4006_mg : Scalar.QComplex := ((-93086043291076644517348 : Int)/10^30,(266985643078290406790 : Int)/10^30)
theorem v4006_mg_checked : Scalar.distance (sourceCoefficient 58 92 3 2) v4006_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4006_upper : Scalar.QComplex := ((999993039428506860452916811272 : Int)/10^30,(-3731098301669842504107320730 : Int)/10^30)
theorem v4006_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 92 5) 1) 14) v4006_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4006 : Material (58 : Basis) (92 : Basis) where
  plus := ![v4006_pa,v4006_pb,v4006_pg]
  minus := ![(Primitive.Addresses.material4006 1).one,v4006_mb,v4006_mg]
  upper := v4006_upper
  lower := (Primitive.Addresses.material4006 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4006_pa_checked.trans (by decide +kernel)
    · exact v4006_pb_checked.trans (by decide +kernel)
    · exact v4006_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 92 Primitive.Addresses.material4006
    · exact v4006_mb_checked.trans (by decide +kernel)
    · exact v4006_mg_checked.trans (by decide +kernel)
  upper_error := v4006_upper_checked
  lower_error := reuse_lower_error 58 92 Primitive.Addresses.material4006

def v4007_pa : Scalar.QComplex := ((999997912826088554264305441526 : Int)/10^30,(-2043121011246405534215438951 : Int)/10^30)
theorem v4007_pa_checked : Scalar.distance (sourceCoefficient 58 93 1 0) v4007_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4007_pb : Scalar.QComplex := ((-881560710489835520230535 : Int)/10^30,(-431476581987439124129620504 : Int)/10^30)
theorem v4007_pb_checked : Scalar.distance (sourceCoefficient 58 93 1 1) v4007_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4007_pg : Scalar.QComplex := ((-93086231462413949912426 : Int)/10^30,(190186832311598861711 : Int)/10^30)
theorem v4007_pg_checked : Scalar.distance (sourceCoefficient 58 93 1 2) v4007_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4007_mb : Scalar.QComplex := ((-1253905239515787210108276 : Int)/10^30,(-431475660581799064038304531 : Int)/10^30)
theorem v4007_mb_checked : Scalar.distance (sourceCoefficient 58 93 3 1) v4007_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4007_mg : Scalar.QComplex := ((-93086032679485137557499 : Int)/10^30,(270515986800178390072 : Int)/10^30)
theorem v4007_mg_checked : Scalar.distance (sourceCoefficient 58 93 3 2) v4007_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4007_upper : Scalar.QComplex := ((999992897205150485289104545888 : Int)/10^30,(-3769023646693497132509458675 : Int)/10^30)
theorem v4007_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 93 5) 1) 14) v4007_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4007 : Material (58 : Basis) (93 : Basis) where
  plus := ![v4007_pa,v4007_pb,v4007_pg]
  minus := ![(Primitive.Addresses.material4007 1).one,v4007_mb,v4007_mg]
  upper := v4007_upper
  lower := (Primitive.Addresses.material4007 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4007_pa_checked.trans (by decide +kernel)
    · exact v4007_pb_checked.trans (by decide +kernel)
    · exact v4007_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 93 Primitive.Addresses.material4007
    · exact v4007_mb_checked.trans (by decide +kernel)
    · exact v4007_mg_checked.trans (by decide +kernel)
  upper_error := v4007_upper_checked
  lower_error := reuse_lower_error 58 93 Primitive.Addresses.material4007

def v4008_pa : Scalar.QComplex := ((999997820293761207235315480605 : Int)/10^30,(-2087919473175687859947226654 : Int)/10^30)
theorem v4008_pa_checked : Scalar.distance (sourceCoefficient 58 94 1 0) v4008_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4008_pb : Scalar.QComplex := ((-900890227927884320253358 : Int)/10^30,(-431476537206484902097029431 : Int)/10^30)
theorem v4008_pb_checked : Scalar.distance (sourceCoefficient 58 94 1 1) v4008_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4008_pg : Scalar.QComplex := ((-93086222325167939700371 : Int)/10^30,(194356959918157684890 : Int)/10^30)
theorem v4008_pg_checked : Scalar.distance (sourceCoefficient 58 94 1 2) v4008_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4008_mb : Scalar.QComplex := ((-1273234711112626631052335 : Int)/10^30,(-431475599120358536113810468 : Int)/10^30)
theorem v4008_mb_checked : Scalar.distance (sourceCoefficient 58 94 3 1) v4008_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4008_mg : Scalar.QComplex := ((-93086019943610220674820 : Int)/10^30,(274686104968976340553 : Int)/10^30)
theorem v4008_mg_checked : Scalar.distance (sourceCoefficient 58 94 3 2) v4008_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4008_upper : Scalar.QComplex := ((999992727354879749070129936141 : Int)/10^30,(-3813821882198330277767569986 : Int)/10^30)
theorem v4008_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 94 5) 1) 14) v4008_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4008 : Material (58 : Basis) (94 : Basis) where
  plus := ![v4008_pa,v4008_pb,v4008_pg]
  minus := ![(Primitive.Addresses.material4008 1).one,v4008_mb,v4008_mg]
  upper := v4008_upper
  lower := (Primitive.Addresses.material4008 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4008_pa_checked.trans (by decide +kernel)
    · exact v4008_pb_checked.trans (by decide +kernel)
    · exact v4008_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 94 Primitive.Addresses.material4008
    · exact v4008_mb_checked.trans (by decide +kernel)
    · exact v4008_mg_checked.trans (by decide +kernel)
  upper_error := v4008_upper_checked
  lower_error := reuse_lower_error 58 94 Primitive.Addresses.material4008

def v4009_pa : Scalar.QComplex := ((999997726872646164312330795033 : Int)/10^30,(-2132193598284032129969290743 : Int)/10^30)
theorem v4009_pa_checked : Scalar.distance (sourceCoefficient 58 95 1 0) v4009_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4009_pb : Scalar.QComplex := ((-919993504920974167241813 : Int)/10^30,(-431476491815270703765678132 : Int)/10^30)
theorem v4009_pb_checked : Scalar.distance (sourceCoefficient 58 95 1 1) v4009_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4009_pg : Scalar.QComplex := ((-93086213080726522717754 : Int)/10^30,(198478278785633074148 : Int)/10^30)
theorem v4009_pg_checked : Scalar.distance (sourceCoefficient 58 95 1 2) v4009_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4009_mb : Scalar.QComplex := ((-1292337941822119881862580 : Int)/10^30,(-431475537243893573626422831 : Int)/10^30)
theorem v4009_mb_checked : Scalar.distance (sourceCoefficient 58 95 3 1) v4009_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4009_mg : Scalar.QComplex := ((-93086007142659680500325 : Int)/10^30,(278807414324359773202 : Int)/10^30)
theorem v4009_mg_checked : Scalar.distance (sourceCoefficient 58 95 3 2) v4009_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4009_upper : Scalar.QComplex := ((999992557520780426176294597289 : Int)/10^30,(-3858095780129196536250425085 : Int)/10^30)
theorem v4009_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 95 5) 1) 14) v4009_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4009 : Material (58 : Basis) (95 : Basis) where
  plus := ![v4009_pa,v4009_pb,v4009_pg]
  minus := ![(Primitive.Addresses.material4009 1).one,v4009_mb,v4009_mg]
  upper := v4009_upper
  lower := (Primitive.Addresses.material4009 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4009_pa_checked.trans (by decide +kernel)
    · exact v4009_pb_checked.trans (by decide +kernel)
    · exact v4009_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 95 Primitive.Addresses.material4009
    · exact v4009_mb_checked.trans (by decide +kernel)
    · exact v4009_mg_checked.trans (by decide +kernel)
  upper_error := v4009_upper_checked
  lower_error := reuse_lower_error 58 95 Primitive.Addresses.material4009

def v4010_pa : Scalar.QComplex := ((999997681307395030380531994973 : Int)/10^30,(-2153457646113301805611045164 : Int)/10^30)
theorem v4010_pa_checked : Scalar.distance (sourceCoefficient 58 96 1 0) v4010_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4010_pb : Scalar.QComplex := ((-929168457063906424353329 : Int)/10^30,(-431476469613830146421275919 : Int)/10^30)
theorem v4010_pb_checked : Scalar.distance (sourceCoefficient 58 96 1 1) v4010_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4010_pg : Scalar.QComplex := ((-93086208565117496206465 : Int)/10^30,(200457672381972358104 : Int)/10^30)
theorem v4010_pg_checked : Scalar.distance (sourceCoefficient 58 96 1 2) v4010_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4010_mb : Scalar.QComplex := ((-1301512871389954854908718 : Int)/10^30,(-431475507124890808047361190 : Int)/10^30)
theorem v4010_mb_checked : Scalar.distance (sourceCoefficient 58 96 3 1) v4010_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4010_mg : Scalar.QComplex := ((-93086000918924810294077 : Int)/10^30,(280786803286913144087 : Int)/10^30)
theorem v4010_mg_checked : Scalar.distance (sourceCoefficient 58 96 3 2) v4010_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4010_upper : Scalar.QComplex := ((999992475255779662364215905979 : Int)/10^30,(-3879359717646675010843757718 : Int)/10^30)
theorem v4010_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 96 5) 1) 14) v4010_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4010 : Material (58 : Basis) (96 : Basis) where
  plus := ![v4010_pa,v4010_pb,v4010_pg]
  minus := ![(Primitive.Addresses.material4010 1).one,v4010_mb,v4010_mg]
  upper := v4010_upper
  lower := (Primitive.Addresses.material4010 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4010_pa_checked.trans (by decide +kernel)
    · exact v4010_pb_checked.trans (by decide +kernel)
    · exact v4010_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 96 Primitive.Addresses.material4010
    · exact v4010_mb_checked.trans (by decide +kernel)
    · exact v4010_mg_checked.trans (by decide +kernel)
  upper_error := v4010_upper_checked
  lower_error := reuse_lower_error 58 96 Primitive.Addresses.material4010

def v4011_pa : Scalar.QComplex := ((999997521079296740834981088744 : Int)/10^30,(-2226619693946516092142850887 : Int)/10^30)
theorem v4011_pa_checked : Scalar.distance (sourceCoefficient 58 97 1 0) v4011_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4011_pb : Scalar.QComplex := ((-960736211795330212938944 : Int)/10^30,(-431476391239321116983006912 : Int)/10^30)
theorem v4011_pb_checked : Scalar.distance (sourceCoefficient 58 97 1 1) v4011_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4011_pg : Scalar.QComplex := ((-93086192653376550443931 : Int)/10^30,(207268063597601705998 : Int)/10^30)
theorem v4011_pg_checked : Scalar.distance (sourceCoefficient 58 97 1 2) v4011_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4011_mb : Scalar.QComplex := ((-1333080546733589403769346 : Int)/10^30,(-431475401508860386696898593 : Int)/10^30)
theorem v4011_mb_checked : Scalar.distance (sourceCoefficient 58 97 3 1) v4011_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4011_mg : Scalar.QComplex := ((-93085979130128898745822 : Int)/10^30,(287597178235606794163 : Int)/10^30)
theorem v4011_mg_checked : Scalar.distance (sourceCoefficient 58 97 3 2) v4011_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4011_upper : Scalar.QComplex := ((999992188756862662753890885046 : Int)/10^30,(-3952521379974451399426177947 : Int)/10^30)
theorem v4011_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 97 5) 1) 14) v4011_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4011 : Material (58 : Basis) (97 : Basis) where
  plus := ![v4011_pa,v4011_pb,v4011_pg]
  minus := ![(Primitive.Addresses.material4011 1).one,v4011_mb,v4011_mg]
  upper := v4011_upper
  lower := (Primitive.Addresses.material4011 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4011_pa_checked.trans (by decide +kernel)
    · exact v4011_pb_checked.trans (by decide +kernel)
    · exact v4011_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 97 Primitive.Addresses.material4011
    · exact v4011_mb_checked.trans (by decide +kernel)
    · exact v4011_mg_checked.trans (by decide +kernel)
  upper_error := v4011_upper_checked
  lower_error := reuse_lower_error 58 97 Primitive.Addresses.material4011

def v4012_pa : Scalar.QComplex := ((999999065170911304996295571456 : Int)/10^30,(-1367354125120695402703896189 : Int)/10^30)
theorem v4012_pa_checked : Scalar.distance (sourceCoefficient 59 60 1 0) v4012_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4012_pb : Scalar.QComplex := ((-589982568196716799162408 : Int)/10^30,(-431477117613385575166860249 : Int)/10^30)
theorem v4012_pb_checked : Scalar.distance (sourceCoefficient 59 60 1 1) v4012_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4012_pg : Scalar.QComplex := ((-93086342873888307091221 : Int)/10^30,(127282113908033176950 : Int)/10^30)
theorem v4012_pg_checked : Scalar.distance (sourceCoefficient 59 60 1 2) v4012_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4012_mb : Scalar.QComplex := ((-962327668011604734308617 : Int)/10^30,(-431476447826350683978822864 : Int)/10^30)
theorem v4012_mb_checked : Scalar.distance (sourceCoefficient 59 60 3 1) v4012_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4012_mg : Scalar.QComplex := ((-93086198374856870083406 : Int)/10^30,(207611387961998838321 : Int)/10^30)
theorem v4012_mg_checked : Scalar.distance (sourceCoefficient 59 60 3 2) v4012_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4012_upper : Scalar.QComplex := ((999995215860597313727007714430 : Int)/10^30,(-3093259755885806892641248045 : Int)/10^30)
theorem v4012_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 60 5) 1) 14) v4012_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4012 : Material (59 : Basis) (60 : Basis) where
  plus := ![v4012_pa,v4012_pb,v4012_pg]
  minus := ![(Primitive.Addresses.material4012 1).one,v4012_mb,v4012_mg]
  upper := v4012_upper
  lower := (Primitive.Addresses.material4012 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4012_pa_checked.trans (by decide +kernel)
    · exact v4012_pb_checked.trans (by decide +kernel)
    · exact v4012_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 60 Primitive.Addresses.material4012
    · exact v4012_mb_checked.trans (by decide +kernel)
    · exact v4012_mg_checked.trans (by decide +kernel)
  upper_error := v4012_upper_checked
  lower_error := reuse_lower_error 59 60 Primitive.Addresses.material4012

def v4013_pa : Scalar.QComplex := ((999999057141958730044176254522 : Int)/10^30,(-1373213455205936168543741092 : Int)/10^30)
theorem v4013_pa_checked : Scalar.distance (sourceCoefficient 59 61 1 0) v4013_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4013_pb : Scalar.QComplex := ((-592510737389607451491653 : Int)/10^30,(-431477114129527241787073605 : Int)/10^30)
theorem v4013_pb_checked : Scalar.distance (sourceCoefficient 59 61 1 1) v4013_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4013_pg : Scalar.QComplex := ((-93086342124393384811534 : Int)/10^30,(127827538024342246369 : Int)/10^30)
theorem v4013_pg_checked : Scalar.distance (sourceCoefficient 59 61 1 2) v4013_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4013_mb : Scalar.QComplex := ((-964855833256729618532527 : Int)/10^30,(-431476442160797498847679334 : Int)/10^30)
theorem v4013_mb_checked : Scalar.distance (sourceCoefficient 59 61 3 1) v4013_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4013_mg : Scalar.QComplex := ((-93086197154685779490509 : Int)/10^30,(208156811228441220196 : Int)/10^30)
theorem v4013_mg_checked : Scalar.distance (sourceCoefficient 59 61 3 2) v4013_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4013_upper : Scalar.QComplex := ((999995197718984524104098858450 : Int)/10^30,(-3099119063387020018296629629 : Int)/10^30)
theorem v4013_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 61 5) 1) 14) v4013_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4013 : Material (59 : Basis) (61 : Basis) where
  plus := ![v4013_pa,v4013_pb,v4013_pg]
  minus := ![(Primitive.Addresses.material4013 1).one,v4013_mb,v4013_mg]
  upper := v4013_upper
  lower := (Primitive.Addresses.material4013 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4013_pa_checked.trans (by decide +kernel)
    · exact v4013_pb_checked.trans (by decide +kernel)
    · exact v4013_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 61 Primitive.Addresses.material4013
    · exact v4013_mb_checked.trans (by decide +kernel)
    · exact v4013_mg_checked.trans (by decide +kernel)
  upper_error := v4013_upper_checked
  lower_error := reuse_lower_error 59 61 Primitive.Addresses.material4013

def v4014_pa : Scalar.QComplex := ((999999045415055133274365881972 : Int)/10^30,(-1381726810372091716845236920 : Int)/10^30)
theorem v4014_pa_checked : Scalar.distance (sourceCoefficient 59 62 1 0) v4014_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4014_pb : Scalar.QComplex := ((-596184058720282425786163 : Int)/10^30,(-431477109032433512370906109 : Int)/10^30)
theorem v4014_pb_checked : Scalar.distance (sourceCoefficient 59 62 1 1) v4014_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4014_pg : Scalar.QComplex := ((-93086341028765222804583 : Int)/10^30,(128620015857615292192 : Int)/10^30)
theorem v4014_pg_checked : Scalar.distance (sourceCoefficient 59 62 1 2) v4014_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4014_mb : Scalar.QComplex := ((-968529148821096858432120 : Int)/10^30,(-431476433893794799191255967 : Int)/10^30)
theorem v4014_mb_checked : Scalar.distance (sourceCoefficient 59 62 3 1) v4014_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4014_mg : Scalar.QComplex := ((-93086195375185347198023 : Int)/10^30,(208949287821160792113 : Int)/10^30)
theorem v4014_mg_checked : Scalar.distance (sourceCoefficient 59 62 3 2) v4014_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4014_upper : Scalar.QComplex := ((999995171298819701942778181867 : Int)/10^30,(-3107632385633961343916076174 : Int)/10^30)
theorem v4014_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 62 5) 1) 14) v4014_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4014 : Material (59 : Basis) (62 : Basis) where
  plus := ![v4014_pa,v4014_pb,v4014_pg]
  minus := ![(Primitive.Addresses.material4014 1).one,v4014_mb,v4014_mg]
  upper := v4014_upper
  lower := (Primitive.Addresses.material4014 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4014_pa_checked.trans (by decide +kernel)
    · exact v4014_pb_checked.trans (by decide +kernel)
    · exact v4014_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 62 Primitive.Addresses.material4014
    · exact v4014_mb_checked.trans (by decide +kernel)
    · exact v4014_mg_checked.trans (by decide +kernel)
  upper_error := v4014_upper_checked
  lower_error := reuse_lower_error 59 62 Primitive.Addresses.material4014

def v4015_pa : Scalar.QComplex := ((999999010847498662874158994689 : Int)/10^30,(-1406521960102856261308321171 : Int)/10^30)
theorem v4015_pa_checked : Scalar.distance (sourceCoefficient 59 63 1 0) v4015_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4015_pb : Scalar.QComplex := ((-606882608220893680251629 : Int)/10^30,(-431477093949577310425954931 : Int)/10^30)
theorem v4015_pb_checked : Scalar.distance (sourceCoefficient 59 63 1 1) v4015_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4015_pg : Scalar.QComplex := ((-93086337792901585294806 : Int)/10^30,(130928107799133849370 : Int)/10^30)
theorem v4015_pg_checked : Scalar.distance (sourceCoefficient 59 63 1 2) v4015_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4015_mb : Scalar.QComplex := ((-979227681322323590301119 : Int)/10^30,(-431476409578577839038065170 : Int)/10^30)
theorem v4015_mb_checked : Scalar.distance (sourceCoefficient 59 63 3 1) v4015_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4015_mg : Scalar.QComplex := ((-93086190147543521619794 : Int)/10^30,(211257376110866653169 : Int)/10^30)
theorem v4015_mg_checked : Scalar.distance (sourceCoefficient 59 63 3 2) v4015_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4015_upper : Scalar.QComplex := ((999995093937135678969978638196 : Int)/10^30,(-3132427438774796483610336393 : Int)/10^30)
theorem v4015_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 63 5) 1) 14) v4015_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4015 : Material (59 : Basis) (63 : Basis) where
  plus := ![v4015_pa,v4015_pb,v4015_pg]
  minus := ![(Primitive.Addresses.material4015 1).one,v4015_mb,v4015_mg]
  upper := v4015_upper
  lower := (Primitive.Addresses.material4015 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4015_pa_checked.trans (by decide +kernel)
    · exact v4015_pb_checked.trans (by decide +kernel)
    · exact v4015_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 63 Primitive.Addresses.material4015
    · exact v4015_mb_checked.trans (by decide +kernel)
    · exact v4015_mg_checked.trans (by decide +kernel)
  upper_error := v4015_upper_checked
  lower_error := reuse_lower_error 59 63 Primitive.Addresses.material4015

def v4016_pa : Scalar.QComplex := ((999998960376298681202510660949 : Int)/10^30,(-1441959195615519015953494249 : Int)/10^30)
theorem v4016_pa_checked : Scalar.distance (sourceCoefficient 59 64 1 0) v4016_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4016_pb : Scalar.QComplex := ((-622172978175005216130841 : Int)/10^30,(-431477071779169481050744848 : Int)/10^30)
theorem v4016_pb_checked : Scalar.distance (sourceCoefficient 59 64 1 1) v4016_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4016_pg : Scalar.QComplex := ((-93086333052301412469165 : Int)/10^30,(134226833476292280665 : Int)/10^30)
theorem v4016_pg_checked : Scalar.distance (sourceCoefficient 59 64 1 2) v4016_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4016_mb : Scalar.QComplex := ((-994518026451068149187159 : Int)/10^30,(-431476374213277647019415553 : Int)/10^30)
theorem v4016_mb_checked : Scalar.distance (sourceCoefficient 59 64 3 1) v4016_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4016_mg : Scalar.QComplex := ((-93086182560293423637882 : Int)/10^30,(214556096468834315204 : Int)/10^30)
theorem v4016_mg_checked : Scalar.distance (sourceCoefficient 59 64 3 2) v4016_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4016_upper : Scalar.QComplex := ((999994982304557214258774733753 : Int)/10^30,(-3167864534399147235375040345 : Int)/10^30)
theorem v4016_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 59 64 5) 1) 14) v4016_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4016 : Material (59 : Basis) (64 : Basis) where
  plus := ![v4016_pa,v4016_pb,v4016_pg]
  minus := ![(Primitive.Addresses.material4016 1).one,v4016_mb,v4016_mg]
  upper := v4016_upper
  lower := (Primitive.Addresses.material4016 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4016_pa_checked.trans (by decide +kernel)
    · exact v4016_pb_checked.trans (by decide +kernel)
    · exact v4016_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 59 64 Primitive.Addresses.material4016
    · exact v4016_mb_checked.trans (by decide +kernel)
    · exact v4016_mg_checked.trans (by decide +kernel)
  upper_error := v4016_upper_checked
  lower_error := reuse_lower_error 59 64 Primitive.Addresses.material4016

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
