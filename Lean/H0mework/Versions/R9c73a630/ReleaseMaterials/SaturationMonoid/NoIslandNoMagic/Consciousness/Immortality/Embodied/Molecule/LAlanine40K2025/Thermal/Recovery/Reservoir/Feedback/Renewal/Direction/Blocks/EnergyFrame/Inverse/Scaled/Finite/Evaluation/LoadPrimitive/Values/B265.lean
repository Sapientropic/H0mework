import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B176
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B177

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4241_pa : Scalar.QComplex := ((999998176878027869978937620605 : Int)/10^30,(-1909513189398365182578165372 : Int)/10^30)
theorem v4241_pa_checked : Scalar.distance (sourceCoefficient 65 82 1 0) v4241_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4241_pb : Scalar.QComplex := ((-823912004858911900366997 : Int)/10^30,(-431476727859850060933995633 : Int)/10^30)
theorem v4241_pb_checked : Scalar.distance (sourceCoefficient 65 82 1 1) v4241_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4241_pg : Scalar.QComplex := ((-93086259487407418584856 : Int)/10^30,(177749764302464010715 : Int)/10^30)
theorem v4241_pg_checked : Scalar.distance (sourceCoefficient 65 82 1 2) v4241_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4241_mb : Scalar.QComplex := ((-1196256681231432161598429 : Int)/10^30,(-431475856202392244045803978 : Int)/10^30)
theorem v4241_mb_checked : Scalar.distance (sourceCoefficient 65 82 3 1) v4241_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4241_mg : Scalar.QComplex := ((-93086071437097718377850 : Int)/10^30,(258078947606239525578 : Int)/10^30)
theorem v4241_mg_checked : Scalar.distance (sourceCoefficient 65 82 3 2) v4241_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4241_upper : Scalar.QComplex := ((999993391851676229459985939298 : Int)/10^30,(-3635416479568305400394910340 : Int)/10^30)
theorem v4241_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 82 5) 1) 14) v4241_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4241 : Material (65 : Basis) (82 : Basis) where
  plus := ![v4241_pa,v4241_pb,v4241_pg]
  minus := ![(Primitive.Addresses.material4241 1).one,v4241_mb,v4241_mg]
  upper := v4241_upper
  lower := (Primitive.Addresses.material4241 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4241_pa_checked.trans (by decide +kernel)
    · exact v4241_pb_checked.trans (by decide +kernel)
    · exact v4241_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 82 Primitive.Addresses.material4241
    · exact v4241_mb_checked.trans (by decide +kernel)
    · exact v4241_mg_checked.trans (by decide +kernel)
  upper_error := v4241_upper_checked
  lower_error := reuse_lower_error 65 82 Primitive.Addresses.material4241

def v4242_pa : Scalar.QComplex := ((999998150876513887797055623724 : Int)/10^30,(-1923081785303666952966834917 : Int)/10^30)
theorem v4242_pa_checked : Scalar.distance (sourceCoefficient 65 83 1 0) v4242_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4242_pb : Scalar.QComplex := ((-829766547741168625256838 : Int)/10^30,(-431476716040619139441977951 : Int)/10^30)
theorem v4242_pb_checked : Scalar.distance (sourceCoefficient 65 83 1 1) v4242_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4242_pg : Scalar.QComplex := ((-93086257002280190850086 : Int)/10^30,(179012816319983930889 : Int)/10^30)
theorem v4242_pg_checked : Scalar.distance (sourceCoefficient 65 83 1 2) v4242_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4242_mb : Scalar.QComplex := ((-1202111211734311038748857 : Int)/10^30,(-431475839330958894829269152 : Int)/10^30)
theorem v4242_mb_checked : Scalar.distance (sourceCoefficient 65 83 3 1) v4242_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4242_mg : Scalar.QComplex := ((-93086067862014410601003 : Int)/10^30,(259341997008914583741 : Int)/10^30)
theorem v4242_mg_checked : Scalar.distance (sourceCoefficient 65 83 3 2) v4242_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4242_upper : Scalar.QComplex := ((999993342432035374332977223789 : Int)/10^30,(-3648985010388523154751836250 : Int)/10^30)
theorem v4242_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 83 5) 1) 14) v4242_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4242 : Material (65 : Basis) (83 : Basis) where
  plus := ![v4242_pa,v4242_pb,v4242_pg]
  minus := ![(Primitive.Addresses.material4242 1).one,v4242_mb,v4242_mg]
  upper := v4242_upper
  lower := (Primitive.Addresses.material4242 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4242_pa_checked.trans (by decide +kernel)
    · exact v4242_pb_checked.trans (by decide +kernel)
    · exact v4242_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 83 Primitive.Addresses.material4242
    · exact v4242_mb_checked.trans (by decide +kernel)
    · exact v4242_mg_checked.trans (by decide +kernel)
  upper_error := v4242_upper_checked
  lower_error := reuse_lower_error 65 83 Primitive.Addresses.material4242

def v4243_pa : Scalar.QComplex := ((999998082683857545304621836007 : Int)/10^30,(-1958220776319207741587241615 : Int)/10^30)
theorem v4243_pa_checked : Scalar.distance (sourceCoefficient 65 84 1 0) v4243_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4243_pb : Scalar.QComplex := ((-844928228940754277577972 : Int)/10^30,(-431476684939681701991159062 : Int)/10^30)
theorem v4243_pb_checked : Scalar.distance (sourceCoefficient 65 84 1 1) v4243_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4243_pg : Scalar.QComplex := ((-93086250473535727089223 : Int)/10^30,(182283779162563646781 : Int)/10^30)
theorem v4243_pg_checked : Scalar.distance (sourceCoefficient 65 84 1 2) v4243_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4243_mb : Scalar.QComplex := ((-1217272860449801583106766 : Int)/10^30,(-431475795146185019208817746 : Int)/10^30)
theorem v4243_mb_checked : Scalar.distance (sourceCoefficient 65 84 3 1) v4243_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4243_mg : Scalar.QComplex := ((-93086058510578763341490 : Int)/10^30,(262612952999552914463 : Int)/10^30)
theorem v4243_mg_checked : Scalar.distance (sourceCoefficient 65 84 3 2) v4243_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4243_upper : Scalar.QComplex := ((999993213592769888331617274830 : Int)/10^30,(-3684123831374326083881174672 : Int)/10^30)
theorem v4243_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 84 5) 1) 14) v4243_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4243 : Material (65 : Basis) (84 : Basis) where
  plus := ![v4243_pa,v4243_pb,v4243_pg]
  minus := ![(Primitive.Addresses.material4243 1).one,v4243_mb,v4243_mg]
  upper := v4243_upper
  lower := (Primitive.Addresses.material4243 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4243_pa_checked.trans (by decide +kernel)
    · exact v4243_pb_checked.trans (by decide +kernel)
    · exact v4243_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 84 Primitive.Addresses.material4243
    · exact v4243_mb_checked.trans (by decide +kernel)
    · exact v4243_mg_checked.trans (by decide +kernel)
  upper_error := v4243_upper_checked
  lower_error := reuse_lower_error 65 84 Primitive.Addresses.material4243

def v4244_pa : Scalar.QComplex := ((999997924748171075579995571160 : Int)/10^30,(-2037277435986244499570282622 : Int)/10^30)
theorem v4244_pa_checked : Scalar.distance (sourceCoefficient 65 85 1 0) v4244_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4244_pb : Scalar.QComplex := ((-879039390767395529714732 : Int)/10^30,(-431476612371034633986944831 : Int)/10^30)
theorem v4244_pb_checked : Scalar.distance (sourceCoefficient 65 85 1 1) v4244_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4244_pg : Scalar.QComplex := ((-93086235294765776546048 : Int)/10^30,(189642880323666911897 : Int)/10^30)
theorem v4244_pg_checked : Scalar.distance (sourceCoefficient 65 85 1 2) v4244_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4244_mb : Scalar.QComplex := ((-1251383946951824280924155 : Int)/10^30,(-431475693141168625135232534 : Int)/10^30)
theorem v4244_mb_checked : Scalar.distance (sourceCoefficient 65 85 3 1) v4244_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4244_mg : Scalar.QComplex := ((-93086036981241604128559 : Int)/10^30,(269972038321931648865 : Int)/10^30)
theorem v4244_mg_checked : Scalar.distance (sourceCoefficient 65 85 3 2) v4244_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4244_upper : Scalar.QComplex := ((999992919212696024094798647921 : Int)/10^30,(-3763180100713087882217959340 : Int)/10^30)
theorem v4244_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 85 5) 1) 14) v4244_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4244 : Material (65 : Basis) (85 : Basis) where
  plus := ![v4244_pa,v4244_pb,v4244_pg]
  minus := ![(Primitive.Addresses.material4244 1).one,v4244_mb,v4244_mg]
  upper := v4244_upper
  lower := (Primitive.Addresses.material4244 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4244_pa_checked.trans (by decide +kernel)
    · exact v4244_pb_checked.trans (by decide +kernel)
    · exact v4244_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 85 Primitive.Addresses.material4244
    · exact v4244_mb_checked.trans (by decide +kernel)
    · exact v4244_mg_checked.trans (by decide +kernel)
  upper_error := v4244_upper_checked
  lower_error := reuse_lower_error 65 85 Primitive.Addresses.material4244

def v4245_pa : Scalar.QComplex := ((999997894928849037533819949288 : Int)/10^30,(-2051862049602843486846889399 : Int)/10^30)
theorem v4245_pa_checked : Scalar.distance (sourceCoefficient 65 86 1 0) v4245_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4245_pb : Scalar.QComplex := ((-885332321627086311163835 : Int)/10^30,(-431476598590495292197801656 : Int)/10^30)
theorem v4245_pb_checked : Scalar.distance (sourceCoefficient 65 86 1 1) v4245_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4245_pg : Scalar.QComplex := ((-93086232420380354106337 : Int)/10^30,(191000509713551108788 : Int)/10^30)
theorem v4245_pg_checked : Scalar.distance (sourceCoefficient 65 86 1 2) v4245_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4245_mb : Scalar.QComplex := ((-1257676863576384502650528 : Int)/10^30,(-431475673930118505642304692 : Int)/10^30)
theorem v4245_mb_checked : Scalar.distance (sourceCoefficient 65 86 3 1) v4245_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4245_mg : Scalar.QComplex := ((-93086032935284233841743 : Int)/10^30,(271329664725843215122 : Int)/10^30)
theorem v4245_mg_checked : Scalar.distance (sourceCoefficient 65 86 3 2) v4245_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4245_upper : Scalar.QComplex := ((999992864221698401987885486068 : Int)/10^30,(-3777764641142173466729383322 : Int)/10^30)
theorem v4245_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 86 5) 1) 14) v4245_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4245 : Material (65 : Basis) (86 : Basis) where
  plus := ![v4245_pa,v4245_pb,v4245_pg]
  minus := ![(Primitive.Addresses.material4245 1).one,v4245_mb,v4245_mg]
  upper := v4245_upper
  lower := (Primitive.Addresses.material4245 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4245_pa_checked.trans (by decide +kernel)
    · exact v4245_pb_checked.trans (by decide +kernel)
    · exact v4245_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 86 Primitive.Addresses.material4245
    · exact v4245_mb_checked.trans (by decide +kernel)
    · exact v4245_mg_checked.trans (by decide +kernel)
  upper_error := v4245_upper_checked
  lower_error := reuse_lower_error 65 86 Primitive.Addresses.material4245

def v4246_pa : Scalar.QComplex := ((999997892946783706516170461053 : Int)/10^30,(-2052827804009316161416103143 : Int)/10^30)
theorem v4246_pa_checked : Scalar.distance (sourceCoefficient 65 87 1 0) v4246_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4246_pb : Scalar.QComplex := ((-885749022804167490228798 : Int)/10^30,(-431476597673664622805418504 : Int)/10^30)
theorem v4246_pb_checked : Scalar.distance (sourceCoefficient 65 87 1 1) v4246_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4246_pg : Scalar.QComplex := ((-93086232229230700676384 : Int)/10^30,(191090408328292361207 : Int)/10^30)
theorem v4246_pg_checked : Scalar.distance (sourceCoefficient 65 87 1 2) v4246_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4246_mb : Scalar.QComplex := ((-1258093563807125214138447 : Int)/10^30,(-431475672653693829331155939 : Int)/10^30)
theorem v4246_mb_checked : Scalar.distance (sourceCoefficient 65 87 3 1) v4246_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4246_mg : Scalar.QComplex := ((-93086032666556195947148 : Int)/10^30,(271419563142157562854 : Int)/10^30)
theorem v4246_mg_checked : Scalar.distance (sourceCoefficient 65 87 3 2) v4246_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4246_upper : Scalar.QComplex := ((999992860572831530007243969834 : Int)/10^30,(-3778730390689403448564999081 : Int)/10^30)
theorem v4246_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 87 5) 1) 14) v4246_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4246 : Material (65 : Basis) (87 : Basis) where
  plus := ![v4246_pa,v4246_pb,v4246_pg]
  minus := ![(Primitive.Addresses.material4246 1).one,v4246_mb,v4246_mg]
  upper := v4246_upper
  lower := (Primitive.Addresses.material4246 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4246_pa_checked.trans (by decide +kernel)
    · exact v4246_pb_checked.trans (by decide +kernel)
    · exact v4246_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 87 Primitive.Addresses.material4246
    · exact v4246_mb_checked.trans (by decide +kernel)
    · exact v4246_mg_checked.trans (by decide +kernel)
  upper_error := v4246_upper_checked
  lower_error := reuse_lower_error 65 87 Primitive.Addresses.material4246

def v4247_pa : Scalar.QComplex := ((999997868737219218006818966580 : Int)/10^30,(-2064587372644457887117501685 : Int)/10^30)
theorem v4247_pa_checked : Scalar.distance (sourceCoefficient 65 88 1 0) v4247_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4247_pb : Scalar.QComplex := ((-890823010588961399710255 : Int)/10^30,(-431476586466773263804684506 : Int)/10^30)
theorem v4247_pb_checked : Scalar.distance (sourceCoefficient 65 88 1 1) v4247_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4247_pg : Scalar.QComplex := ((-93086229893559255396982 : Int)/10^30,(192185064402196280455 : Int)/10^30)
theorem v4247_pg_checked : Scalar.distance (sourceCoefficient 65 88 1 2) v4247_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4247_mb : Scalar.QComplex := ((-1263167540031599075475993 : Int)/10^30,(-431475657068183708817731457 : Int)/10^30)
theorem v4247_mb_checked : Scalar.distance (sourceCoefficient 65 88 3 1) v4247_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4247_mg : Scalar.QComplex := ((-93086029386246730045300 : Int)/10^30,(272514216792891734994 : Int)/10^30)
theorem v4247_mg_checked : Scalar.distance (sourceCoefficient 65 88 3 2) v4247_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4247_upper : Scalar.QComplex := ((999992816067354454278765968689 : Int)/10^30,(-3790489900026537035557951942 : Int)/10^30)
theorem v4247_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 88 5) 1) 14) v4247_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4247 : Material (65 : Basis) (88 : Basis) where
  plus := ![v4247_pa,v4247_pb,v4247_pg]
  minus := ![(Primitive.Addresses.material4247 1).one,v4247_mb,v4247_mg]
  upper := v4247_upper
  lower := (Primitive.Addresses.material4247 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4247_pa_checked.trans (by decide +kernel)
    · exact v4247_pb_checked.trans (by decide +kernel)
    · exact v4247_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 88 Primitive.Addresses.material4247
    · exact v4247_mb_checked.trans (by decide +kernel)
    · exact v4247_mg_checked.trans (by decide +kernel)
  upper_error := v4247_upper_checked
  lower_error := reuse_lower_error 65 88 Primitive.Addresses.material4247

def v4248_pa : Scalar.QComplex := ((999997835389637151513928154132 : Int)/10^30,(-2080676822613004739921457457 : Int)/10^30)
theorem v4248_pa_checked : Scalar.distance (sourceCoefficient 65 89 1 0) v4248_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4248_pb : Scalar.QComplex := ((-897765244101769838451117 : Int)/10^30,(-431476571004606436361098336 : Int)/10^30)
theorem v4248_pb_checked : Scalar.distance (sourceCoefficient 65 89 1 1) v4248_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4248_pg : Scalar.QComplex := ((-93086226673561144880808 : Int)/10^30,(193682773591917954828 : Int)/10^30)
theorem v4248_pg_checked : Scalar.distance (sourceCoefficient 65 89 1 2) v4248_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4248_mb : Scalar.QComplex := ((-1270109757616343119711874 : Int)/10^30,(-431475635615187783682515911 : Int)/10^30)
theorem v4248_mb_checked : Scalar.distance (sourceCoefficient 65 89 3 1) v4248_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4248_mg : Scalar.QComplex := ((-93086024873794242069661 : Int)/10^30,(274011922646234483298 : Int)/10^30)
theorem v4248_mg_checked : Scalar.distance (sourceCoefficient 65 89 3 2) v4248_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4248_upper : Scalar.QComplex := ((999992754950891032879406609808 : Int)/10^30,(-3806579268476836782016141805 : Int)/10^30)
theorem v4248_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 89 5) 1) 14) v4248_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4248 : Material (65 : Basis) (89 : Basis) where
  plus := ![v4248_pa,v4248_pb,v4248_pg]
  minus := ![(Primitive.Addresses.material4248 1).one,v4248_mb,v4248_mg]
  upper := v4248_upper
  lower := (Primitive.Addresses.material4248 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4248_pa_checked.trans (by decide +kernel)
    · exact v4248_pb_checked.trans (by decide +kernel)
    · exact v4248_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 89 Primitive.Addresses.material4248
    · exact v4248_mb_checked.trans (by decide +kernel)
    · exact v4248_mg_checked.trans (by decide +kernel)
  upper_error := v4248_upper_checked
  lower_error := reuse_lower_error 65 89 Primitive.Addresses.material4248

def v4249_pa : Scalar.QComplex := ((999997780526487383567495136215 : Int)/10^30,(-2106879706858033175024082865 : Int)/10^30)
theorem v4249_pa_checked : Scalar.distance (sourceCoefficient 65 90 1 0) v4249_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4249_pb : Scalar.QComplex := ((-909071195368136703925499 : Int)/10^30,(-431476545504528349897299987 : Int)/10^30)
theorem v4249_pb_checked : Scalar.distance (sourceCoefficient 65 90 1 1) v4249_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4249_pg : Scalar.QComplex := ((-93086221369376025225350 : Int)/10^30,(196121906078608728823 : Int)/10^30)
theorem v4249_pg_checked : Scalar.distance (sourceCoefficient 65 90 1 2) v4249_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4249_mb : Scalar.QComplex := ((-1281415682667568713484274 : Int)/10^30,(-431475600358592450331197623 : Int)/10^30)
theorem v4249_mb_checked : Scalar.distance (sourceCoefficient 65 90 3 1) v4249_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4249_mg : Scalar.QComplex := ((-93086017464749615839810 : Int)/10^30,(276451049647451892003 : Int)/10^30)
theorem v4249_mg_checked : Scalar.distance (sourceCoefficient 65 90 3 2) v4249_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4249_upper : Scalar.QComplex := ((999992654864021877320563103278 : Int)/10^30,(-3832782019006927787742606436 : Int)/10^30)
theorem v4249_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 90 5) 1) 14) v4249_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4249 : Material (65 : Basis) (90 : Basis) where
  plus := ![v4249_pa,v4249_pb,v4249_pg]
  minus := ![(Primitive.Addresses.material4249 1).one,v4249_mb,v4249_mg]
  upper := v4249_upper
  lower := (Primitive.Addresses.material4249 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4249_pa_checked.trans (by decide +kernel)
    · exact v4249_pb_checked.trans (by decide +kernel)
    · exact v4249_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 90 Primitive.Addresses.material4249
    · exact v4249_mb_checked.trans (by decide +kernel)
    · exact v4249_mg_checked.trans (by decide +kernel)
  upper_error := v4249_upper_checked
  lower_error := reuse_lower_error 65 90 Primitive.Addresses.material4249

def v4250_pa : Scalar.QComplex := ((999997749317742102302349797765 : Int)/10^30,(-2121640744854031427904342491 : Int)/10^30)
theorem v4250_pa_checked : Scalar.distance (sourceCoefficient 65 91 1 0) v4250_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4250_pb : Scalar.QComplex := ((-915440248909742637861633 : Int)/10^30,(-431476530965471378317416819 : Int)/10^30)
theorem v4250_pb_checked : Scalar.distance (sourceCoefficient 65 91 1 1) v4250_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4250_pg : Scalar.QComplex := ((-93086218348501547477420 : Int)/10^30,(197495958133208807369 : Int)/10^30)
theorem v4250_pg_checked : Scalar.distance (sourceCoefficient 65 91 1 2) v4250_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4250_mb : Scalar.QComplex := ((-1287784721291133582098709 : Int)/10^30,(-431475580323334537423856577 : Int)/10^30)
theorem v4250_mb_checked : Scalar.distance (sourceCoefficient 65 91 3 1) v4250_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4250_mg : Scalar.QComplex := ((-93086013258131224788901 : Int)/10^30,(277825098583550974180 : Int)/10^30)
theorem v4250_mg_checked : Scalar.distance (sourceCoefficient 65 91 3 2) v4250_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4250_upper : Scalar.QComplex := ((999992598179110607628929611302 : Int)/10^30,(-3847542981154630778701935612 : Int)/10^30)
theorem v4250_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 91 5) 1) 14) v4250_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4250 : Material (65 : Basis) (91 : Basis) where
  plus := ![v4250_pa,v4250_pb,v4250_pg]
  minus := ![(Primitive.Addresses.material4250 1).one,v4250_mb,v4250_mg]
  upper := v4250_upper
  lower := (Primitive.Addresses.material4250 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4250_pa_checked.trans (by decide +kernel)
    · exact v4250_pb_checked.trans (by decide +kernel)
    · exact v4250_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 91 Primitive.Addresses.material4250
    · exact v4250_mb_checked.trans (by decide +kernel)
    · exact v4250_mg_checked.trans (by decide +kernel)
  upper_error := v4250_upper_checked
  lower_error := reuse_lower_error 65 91 Primitive.Addresses.material4250

def v4251_pa : Scalar.QComplex := ((999997681007773302731526920103 : Int)/10^30,(-2153596776481054603782747816 : Int)/10^30)
theorem v4251_pa_checked : Scalar.distance (sourceCoefficient 65 92 1 0) v4251_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4251_pb : Scalar.QComplex := ((-929228552377962288130906 : Int)/10^30,(-431476499060569146293903368 : Int)/10^30)
theorem v4251_pb_checked : Scalar.distance (sourceCoefficient 65 92 1 1) v4251_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4251_pg : Scalar.QComplex := ((-93086211727573795616685 : Int)/10^30,(200470630401169448655 : Int)/10^30)
theorem v4251_pg_checked : Scalar.distance (sourceCoefficient 65 92 1 2) v4251_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4251_mb : Scalar.QComplex := ((-1301572992092844011769330 : Int)/10^30,(-431475536519759294115537732 : Int)/10^30)
theorem v4251_mb_checked : Scalar.distance (sourceCoefficient 65 92 3 1) v4251_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4251_mg : Scalar.QComplex := ((-93086004070197745217716 : Int)/10^30,(280799764030342726527 : Int)/10^30)
theorem v4251_mg_checked : Scalar.distance (sourceCoefficient 65 92 3 2) v4251_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4251_upper : Scalar.QComplex := ((999992474716031988033614857118 : Int)/10^30,(-3879498847290089549197344605 : Int)/10^30)
theorem v4251_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 92 5) 1) 14) v4251_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4251 : Material (65 : Basis) (92 : Basis) where
  plus := ![v4251_pa,v4251_pb,v4251_pg]
  minus := ![(Primitive.Addresses.material4251 1).one,v4251_mb,v4251_mg]
  upper := v4251_upper
  lower := (Primitive.Addresses.material4251 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4251_pa_checked.trans (by decide +kernel)
    · exact v4251_pb_checked.trans (by decide +kernel)
    · exact v4251_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 92 Primitive.Addresses.material4251
    · exact v4251_mb_checked.trans (by decide +kernel)
    · exact v4251_mg_checked.trans (by decide +kernel)
  upper_error := v4251_upper_checked
  lower_error := reuse_lower_error 65 92 Primitive.Addresses.material4251

def v4252_pa : Scalar.QComplex := ((999997598612123875571857371400 : Int)/10^30,(-2191522298673943378560859545 : Int)/10^30)
theorem v4252_pa_checked : Scalar.distance (sourceCoefficient 65 93 1 0) v4252_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4252_pb : Scalar.QComplex := ((-945592555127115206517705 : Int)/10^30,(-431476460433361681099966917 : Int)/10^30)
theorem v4252_pb_checked : Scalar.distance (sourceCoefficient 65 93 1 1) v4252_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4252_pg : Scalar.QComplex := ((-93086203725922249080966 : Int)/10^30,(204000981049746730463 : Int)/10^30)
theorem v4252_pg_checked : Scalar.distance (sourceCoefficient 65 93 1 2) v4252_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4252_mb : Scalar.QComplex := ((-1317936955415390497156227 : Int)/10^30,(-431475483771168846402146525 : Int)/10^30)
theorem v4252_mb_checked : Scalar.distance (sourceCoefficient 65 93 3 1) v4252_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4252_mg : Scalar.QComplex := ((-93085993022015569431181 : Int)/10^30,(284330106459344213221 : Int)/10^30)
theorem v4252_mg_checked : Scalar.distance (sourceCoefficient 65 93 3 2) v4252_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4252_upper : Scalar.QComplex := ((999992326864494551085899113699 : Int)/10^30,(-3917424170789952026102154271 : Int)/10^30)
theorem v4252_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 93 5) 1) 14) v4252_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4252 : Material (65 : Basis) (93 : Basis) where
  plus := ![v4252_pa,v4252_pb,v4252_pg]
  minus := ![(Primitive.Addresses.material4252 1).one,v4252_mb,v4252_mg]
  upper := v4252_upper
  lower := (Primitive.Addresses.material4252 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4252_pa_checked.trans (by decide +kernel)
    · exact v4252_pb_checked.trans (by decide +kernel)
    · exact v4252_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 93 Primitive.Addresses.material4252
    · exact v4252_mb_checked.trans (by decide +kernel)
    · exact v4252_mg_checked.trans (by decide +kernel)
  upper_error := v4252_upper_checked
  lower_error := reuse_lower_error 65 93 Primitive.Addresses.material4252

def v4253_pa : Scalar.QComplex := ((999997499431633238640421098364 : Int)/10^30,(-2236320746377979276253400641 : Int)/10^30)
theorem v4253_pa_checked : Scalar.distance (sourceCoefficient 65 94 1 0) v4253_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4253_pb : Scalar.QComplex := ((-964922068473248178246193 : Int)/10^30,(-431476413740052215889671863 : Int)/10^30)
theorem v4253_pb_checked : Scalar.distance (sourceCoefficient 65 94 1 1) v4253_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4253_pg : Scalar.QComplex := ((-93086194072964765174354 : Int)/10^30,(208171107552824414621 : Int)/10^30)
theorem v4253_pg_checked : Scalar.distance (sourceCoefficient 65 94 1 2) v4253_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4253_mb : Scalar.QComplex := ((-1337266421270039167833750 : Int)/10^30,(-431475420397377318496271238 : Int)/10^30)
theorem v4253_mb_checked : Scalar.distance (sourceCoefficient 65 94 3 1) v4253_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4253_mg : Scalar.QComplex := ((-93085979770430323131419 : Int)/10^30,(288500223079625660542 : Int)/10^30)
theorem v4253_mg_checked : Scalar.distance (sourceCoefficient 65 94 3 2) v4253_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4253_upper : Scalar.QComplex := ((999992150366094978107580903540 : Int)/10^30,(-3962222380595433208445307511 : Int)/10^30)
theorem v4253_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 94 5) 1) 14) v4253_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4253 : Material (65 : Basis) (94 : Basis) where
  plus := ![v4253_pa,v4253_pb,v4253_pg]
  minus := ![(Primitive.Addresses.material4253 1).one,v4253_mb,v4253_mg]
  upper := v4253_upper
  lower := (Primitive.Addresses.material4253 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4253_pa_checked.trans (by decide +kernel)
    · exact v4253_pb_checked.trans (by decide +kernel)
    · exact v4253_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 94 Primitive.Addresses.material4253
    · exact v4253_mb_checked.trans (by decide +kernel)
    · exact v4253_mg_checked.trans (by decide +kernel)
  upper_error := v4253_upper_checked
  lower_error := reuse_lower_error 65 94 Primitive.Addresses.material4253

def v4254_pa : Scalar.QComplex := ((999997399440167349079305923358 : Int)/10^30,(-2280594857134953330237740018 : Int)/10^30)
theorem v4254_pa_checked : Scalar.distance (sourceCoefficient 65 95 1 0) v4254_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4254_pb : Scalar.QComplex := ((-984025341338142505031248 : Int)/10^30,(-431476366458865665096849162 : Int)/10^30)
theorem v4254_pb_checked : Scalar.distance (sourceCoefficient 65 95 1 1) v4254_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4254_pg : Scalar.QComplex := ((-93086184318847945024133 : Int)/10^30,(212292425307034991681 : Int)/10^30)
theorem v4254_pg_checked : Scalar.distance (sourceCoefficient 65 95 1 2) v4254_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4254_mb : Scalar.QComplex := ((-1356369646220377416577113 : Int)/10^30,(-431475356630944269717301935 : Int)/10^30)
theorem v4254_mb_checked : Scalar.distance (sourceCoefficient 65 95 3 1) v4254_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4254_mg : Scalar.QComplex := ((-93085966459805530262161 : Int)/10^30,(292621530881917777507 : Int)/10^30)
theorem v4254_mg_checked : Scalar.distance (sourceCoefficient 65 95 3 2) v4254_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4254_upper : Scalar.QComplex := ((999991973961679363504440261133 : Int)/10^30,(-4006496252835121121845791866 : Int)/10^30)
theorem v4254_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 95 5) 1) 14) v4254_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4254 : Material (65 : Basis) (95 : Basis) where
  plus := ![v4254_pa,v4254_pb,v4254_pg]
  minus := ![(Primitive.Addresses.material4254 1).one,v4254_mb,v4254_mg]
  upper := v4254_upper
  lower := (Primitive.Addresses.material4254 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4254_pa_checked.trans (by decide +kernel)
    · exact v4254_pb_checked.trans (by decide +kernel)
    · exact v4254_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 95 Primitive.Addresses.material4254
    · exact v4254_mb_checked.trans (by decide +kernel)
    · exact v4254_mg_checked.trans (by decide +kernel)
  upper_error := v4254_upper_checked
  lower_error := reuse_lower_error 65 95 Primitive.Addresses.material4254

def v4255_pa : Scalar.QComplex := ((999997350719297578384141916422 : Int)/10^30,(-2301858897968116440253633111 : Int)/10^30)
theorem v4255_pa_checked : Scalar.distance (sourceCoefficient 65 96 1 0) v4255_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4255_pb : Scalar.QComplex := ((-993200291468633078254609 : Int)/10^30,(-431476343349706161117221298 : Int)/10^30)
theorem v4255_pb_checked : Scalar.distance (sourceCoefficient 65 96 1 1) v4255_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4255_pg : Scalar.QComplex := ((-93086179558451199590843 : Int)/10^30,(214271818360672141828 : Int)/10^30)
theorem v4255_pg_checked : Scalar.distance (sourceCoefficient 65 96 1 2) v4255_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4255_mb : Scalar.QComplex := ((-1365544572992450886256648 : Int)/10^30,(-431475325604224632134799468 : Int)/10^30)
theorem v4255_mb_checked : Scalar.distance (sourceCoefficient 65 96 3 1) v4255_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4255_mg : Scalar.QComplex := ((-93085959991283500607065 : Int)/10^30,(294600919090528440055 : Int)/10^30)
theorem v4255_mg_checked : Scalar.distance (sourceCoefficient 65 96 3 2) v4255_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4255_upper : Scalar.QComplex := ((999991888541076737497521258170 : Int)/10^30,(-4027760177910191959125069712 : Int)/10^30)
theorem v4255_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 96 5) 1) 14) v4255_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4255 : Material (65 : Basis) (96 : Basis) where
  plus := ![v4255_pa,v4255_pb,v4255_pg]
  minus := ![(Primitive.Addresses.material4255 1).one,v4255_mb,v4255_mg]
  upper := v4255_upper
  lower := (Primitive.Addresses.material4255 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4255_pa_checked.trans (by decide +kernel)
    · exact v4255_pb_checked.trans (by decide +kernel)
    · exact v4255_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 96 Primitive.Addresses.material4255
    · exact v4255_mb_checked.trans (by decide +kernel)
    · exact v4255_mg_checked.trans (by decide +kernel)
  upper_error := v4255_upper_checked
  lower_error := reuse_lower_error 65 96 Primitive.Addresses.material4255

def v4256_pa : Scalar.QComplex := ((999997179633834656707423147083 : Int)/10^30,(-2375020921217596041005510943 : Int)/10^30)
theorem v4256_pa_checked : Scalar.distance (sourceCoefficient 65 97 1 0) v4256_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4256_pb : Scalar.QComplex := ((-1024768039128504769182552 : Int)/10^30,(-431476261852058169549693709 : Int)/10^30)
theorem v4256_pb_checked : Scalar.distance (sourceCoefficient 65 97 1 1) v4256_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4256_pg : Scalar.QComplex := ((-93086162804482527376692 : Int)/10^30,(221082207669291485466 : Int)/10^30)
theorem v4256_pg_checked : Scalar.distance (sourceCoefficient 65 97 1 2) v4256_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4256_mb : Scalar.QComplex := ((-1397112238569407707161359 : Int)/10^30,(-431475216865062513973417787 : Int)/10^30)
theorem v4256_mb_checked : Scalar.distance (sourceCoefficient 65 97 3 1) v4256_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4256_mg : Scalar.QComplex := ((-93085937360261821870813 : Int)/10^30,(301411291405408200544 : Int)/10^30)
theorem v4256_mg_checked : Scalar.distance (sourceCoefficient 65 97 3 2) v4256_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4256_upper : Scalar.QComplex := ((999991591184853705821100959129 : Int)/10^30,(-4100921796915443893879417053 : Int)/10^30)
theorem v4256_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 97 5) 1) 14) v4256_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4256 : Material (65 : Basis) (97 : Basis) where
  plus := ![v4256_pa,v4256_pb,v4256_pg]
  minus := ![(Primitive.Addresses.material4256 1).one,v4256_mb,v4256_mg]
  upper := v4256_upper
  lower := (Primitive.Addresses.material4256 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4256_pa_checked.trans (by decide +kernel)
    · exact v4256_pb_checked.trans (by decide +kernel)
    · exact v4256_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 97 Primitive.Addresses.material4256
    · exact v4256_mb_checked.trans (by decide +kernel)
    · exact v4256_mg_checked.trans (by decide +kernel)
  upper_error := v4256_upper_checked
  lower_error := reuse_lower_error 65 97 Primitive.Addresses.material4256

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
