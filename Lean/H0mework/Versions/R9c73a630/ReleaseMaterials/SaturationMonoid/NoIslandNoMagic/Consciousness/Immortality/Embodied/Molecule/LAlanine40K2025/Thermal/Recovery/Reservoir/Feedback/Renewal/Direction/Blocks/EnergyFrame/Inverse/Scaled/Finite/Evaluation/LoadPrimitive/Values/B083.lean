import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B055
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B056

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1329_pa : Scalar.QComplex := ((999999432007578366958013207955 : Int)/10^30,(-1065825745912854622020527131 : Int)/10^30)
theorem v1329_pa_checked : Scalar.distance (sourceCoefficient 14 77 1 0) v1329_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1329_pb : Scalar.QComplex := ((-459879772645237189529123 : Int)/10^30,(-431477202723354656727278339 : Int)/10^30)
theorem v1329_pb_checked : Scalar.distance (sourceCoefficient 14 77 1 1) v1329_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1329_pg : Scalar.QComplex := ((-93086369128406137895744 : Int)/10^30,(99213905163349048293 : Int)/10^30)
theorem v1329_pg_checked : Scalar.distance (sourceCoefficient 14 77 1 2) v1329_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1329_mb : Scalar.QComplex := ((-832224994349412006660511 : Int)/10^30,(-431476645209141023742335203 : Int)/10^30)
theorem v1329_mb_checked : Scalar.distance (sourceCoefficient 14 77 3 1) v1329_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1329_mg : Scalar.QComplex := ((-93086248850964926598869 : Int)/10^30,(179543212324858034216 : Int)/10^30)
theorem v1329_mg_checked : Scalar.distance (sourceCoefficient 14 77 3 2) v1329_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1329_upper : Scalar.QComplex := ((999996103107346087417416320478 : Int)/10^30,(-2791732458895875116967478177 : Int)/10^30)
theorem v1329_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 77 5) 1) 14) v1329_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1329 : Material (14 : Basis) (77 : Basis) where
  plus := ![v1329_pa,v1329_pb,v1329_pg]
  minus := ![(Primitive.Addresses.material1329 1).one,v1329_mb,v1329_mg]
  upper := v1329_upper
  lower := (Primitive.Addresses.material1329 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1329_pa_checked.trans (by decide +kernel)
    · exact v1329_pb_checked.trans (by decide +kernel)
    · exact v1329_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 77 Primitive.Addresses.material1329
    · exact v1329_mb_checked.trans (by decide +kernel)
    · exact v1329_mg_checked.trans (by decide +kernel)
  upper_error := v1329_upper_checked
  lower_error := reuse_lower_error 14 77 Primitive.Addresses.material1329

def v1330_pa : Scalar.QComplex := ((999999413419592939267321431621 : Int)/10^30,(-1083125325179358646502768002 : Int)/10^30)
theorem v1330_pa_checked : Scalar.distance (sourceCoefficient 14 78 1 0) v1330_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1330_pb : Scalar.QComplex := ((-467344148212849142671690 : Int)/10^30,(-431477192171219227417299221 : Int)/10^30)
theorem v1330_pb_checked : Scalar.distance (sourceCoefficient 14 78 1 1) v1330_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1330_pg : Scalar.QComplex := ((-93086367125009167737296 : Int)/10^30,(100824260803576659008 : Int)/10^30)
theorem v1330_pg_checked : Scalar.distance (sourceCoefficient 14 78 1 2) v1330_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1330_mb : Scalar.QComplex := ((-839689358031678172208203 : Int)/10^30,(-431476628215589591621383090 : Int)/10^30)
theorem v1330_mb_checked : Scalar.distance (sourceCoefficient 14 78 3 1) v1330_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1330_mg : Scalar.QComplex := ((-93086245457904312605924 : Int)/10^30,(181153565636635287590 : Int)/10^30)
theorem v1330_mg_checked : Scalar.distance (sourceCoefficient 14 78 3 2) v1330_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1330_upper : Scalar.QComplex := ((999996054661883935933108385574 : Int)/10^30,(-2809031980315511415994763704 : Int)/10^30)
theorem v1330_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 78 5) 1) 14) v1330_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1330 : Material (14 : Basis) (78 : Basis) where
  plus := ![v1330_pa,v1330_pb,v1330_pg]
  minus := ![(Primitive.Addresses.material1330 1).one,v1330_mb,v1330_mg]
  upper := v1330_upper
  lower := (Primitive.Addresses.material1330 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1330_pa_checked.trans (by decide +kernel)
    · exact v1330_pb_checked.trans (by decide +kernel)
    · exact v1330_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 78 Primitive.Addresses.material1330
    · exact v1330_mb_checked.trans (by decide +kernel)
    · exact v1330_mg_checked.trans (by decide +kernel)
  upper_error := v1330_upper_checked
  lower_error := reuse_lower_error 14 78 Primitive.Addresses.material1330

def v1331_pa : Scalar.QComplex := ((999999407363363284393739063140 : Int)/10^30,(-1088702402960987931835550026 : Int)/10^30)
theorem v1331_pa_checked : Scalar.distance (sourceCoefficient 14 79 1 0) v1331_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1331_pb : Scalar.QComplex := ((-469750530587514256462864 : Int)/10^30,(-431477188732697718868850123 : Int)/10^30)
theorem v1331_pb_checked : Scalar.distance (sourceCoefficient 14 79 1 1) v1331_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1331_pg : Scalar.QComplex := ((-93086366472221565452001 : Int)/10^30,(101343410921032960911 : Int)/10^30)
theorem v1331_pg_checked : Scalar.distance (sourceCoefficient 14 79 1 2) v1331_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1331_mb : Scalar.QComplex := ((-842095736543047954186618 : Int)/10^30,(-431476622700469753494567650 : Int)/10^30)
theorem v1331_mb_checked : Scalar.distance (sourceCoefficient 14 79 3 1) v1331_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1331_mg : Scalar.QComplex := ((-93086244357113783671821 : Int)/10^30,(181672714997461974120 : Int)/10^30)
theorem v1331_mg_checked : Scalar.distance (sourceCoefficient 14 79 3 2) v1331_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1331_upper : Scalar.QComplex := ((999996038980132998554132033072 : Int)/10^30,(-2814609039338235507717976098 : Int)/10^30)
theorem v1331_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 79 5) 1) 14) v1331_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1331 : Material (14 : Basis) (79 : Basis) where
  plus := ![v1331_pa,v1331_pb,v1331_pg]
  minus := ![(Primitive.Addresses.material1331 1).one,v1331_mb,v1331_mg]
  upper := v1331_upper
  lower := (Primitive.Addresses.material1331 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1331_pa_checked.trans (by decide +kernel)
    · exact v1331_pb_checked.trans (by decide +kernel)
    · exact v1331_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 79 Primitive.Addresses.material1331
    · exact v1331_mb_checked.trans (by decide +kernel)
    · exact v1331_mg_checked.trans (by decide +kernel)
  upper_error := v1331_upper_checked
  lower_error := reuse_lower_error 14 79 Primitive.Addresses.material1331

def v1332_pa : Scalar.QComplex := ((999999397840691309396395687050 : Int)/10^30,(-1097414349635257032016768059 : Int)/10^30)
theorem v1332_pa_checked : Scalar.distance (sourceCoefficient 14 80 1 0) v1332_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1332_pb : Scalar.QComplex := ((-473509537649868563292720 : Int)/10^30,(-431477183325578877389149142 : Int)/10^30)
theorem v1332_pb_checked : Scalar.distance (sourceCoefficient 14 80 1 1) v1332_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1332_pg : Scalar.QComplex := ((-93086365445743207611147 : Int)/10^30,(102154374708757799583 : Int)/10^30)
theorem v1332_pg_checked : Scalar.distance (sourceCoefficient 14 80 1 2) v1332_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1332_mb : Scalar.QComplex := ((-845854737539652103987835 : Int)/10^30,(-431476614049499129913961637 : Int)/10^30)
theorem v1332_mb_checked : Scalar.distance (sourceCoefficient 14 80 3 1) v1332_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1332_mg : Scalar.QComplex := ((-93086242630810583682384 : Int)/10^30,(182483677597423339799 : Int)/10^30)
theorem v1332_mg_checked : Scalar.distance (sourceCoefficient 14 80 3 2) v1332_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1332_upper : Scalar.QComplex := ((999996014421445588298096574224 : Int)/10^30,(-2823320956601815474927870912 : Int)/10^30)
theorem v1332_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 80 5) 1) 14) v1332_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1332 : Material (14 : Basis) (80 : Basis) where
  plus := ![v1332_pa,v1332_pb,v1332_pg]
  minus := ![(Primitive.Addresses.material1332 1).one,v1332_mb,v1332_mg]
  upper := v1332_upper
  lower := (Primitive.Addresses.material1332 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1332_pa_checked.trans (by decide +kernel)
    · exact v1332_pb_checked.trans (by decide +kernel)
    · exact v1332_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 80 Primitive.Addresses.material1332
    · exact v1332_mb_checked.trans (by decide +kernel)
    · exact v1332_mg_checked.trans (by decide +kernel)
  upper_error := v1332_upper_checked
  lower_error := reuse_lower_error 14 80 Primitive.Addresses.material1332

def v1333_pa : Scalar.QComplex := ((999999368709102713574629170899 : Int)/10^30,(-1123646472892899595274511311 : Int)/10^30)
theorem v1333_pa_checked : Scalar.distance (sourceCoefficient 14 81 1 0) v1333_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1333_pb : Scalar.QComplex := ((-484828102654618834351427 : Int)/10^30,(-431477166780785382337939464 : Int)/10^30)
theorem v1333_pb_checked : Scalar.distance (sourceCoefficient 14 81 1 1) v1333_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1333_pg : Scalar.QComplex := ((-93086362305188702183960 : Int)/10^30,(104596228709302922403 : Int)/10^30)
theorem v1333_pg_checked : Scalar.distance (sourceCoefficient 14 81 1 2) v1333_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1333_mb : Scalar.QComplex := ((-857173284052571703411513 : Int)/10^30,(-431476587737299965390310755 : Int)/10^30)
theorem v1333_mb_checked : Scalar.distance (sourceCoefficient 14 81 3 1) v1333_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1333_mg : Scalar.QComplex := ((-93086237383047222178375 : Int)/10^30,(184925527978597527116 : Int)/10^30)
theorem v1333_mg_checked : Scalar.distance (sourceCoefficient 14 81 3 2) v1333_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1333_upper : Scalar.QComplex := ((999995940015635397496713827074 : Int)/10^30,(-2849552990511312768268975433 : Int)/10^30)
theorem v1333_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 81 5) 1) 14) v1333_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1333 : Material (14 : Basis) (81 : Basis) where
  plus := ![v1333_pa,v1333_pb,v1333_pg]
  minus := ![(Primitive.Addresses.material1333 1).one,v1333_mb,v1333_mg]
  upper := v1333_upper
  lower := (Primitive.Addresses.material1333 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1333_pa_checked.trans (by decide +kernel)
    · exact v1333_pb_checked.trans (by decide +kernel)
    · exact v1333_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 81 Primitive.Addresses.material1333
    · exact v1333_mb_checked.trans (by decide +kernel)
    · exact v1333_mg_checked.trans (by decide +kernel)
  upper_error := v1333_upper_checked
  lower_error := reuse_lower_error 14 81 Primitive.Addresses.material1333

def v1334_pa : Scalar.QComplex := ((999999357490361514129127768689 : Int)/10^30,(-1133586725466166614645575644 : Int)/10^30)
theorem v1334_pa_checked : Scalar.distance (sourceCoefficient 14 82 1 0) v1334_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1334_pb : Scalar.QComplex := ((-489117095642754313572382 : Int)/10^30,(-431477160407965934607176512 : Int)/10^30)
theorem v1334_pb_checked : Scalar.distance (sourceCoefficient 14 82 1 1) v1334_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1334_pg : Scalar.QComplex := ((-93086361095600298029212 : Int)/10^30,(105521531058523480461 : Int)/10^30)
theorem v1334_pg_checked : Scalar.distance (sourceCoefficient 14 82 1 2) v1334_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1334_mb : Scalar.QComplex := ((-861462269944262914228204 : Int)/10^30,(-431476577663275110863974415 : Int)/10^30)
theorem v1334_mb_checked : Scalar.distance (sourceCoefficient 14 82 3 1) v1334_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1334_mg : Scalar.QComplex := ((-93086235374965015102123 : Int)/10^30,(185850828939465417207 : Int)/10^30)
theorem v1334_mg_checked : Scalar.distance (sourceCoefficient 14 82 3 2) v1334_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1334_upper : Scalar.QComplex := ((999995911640936738258692919629 : Int)/10^30,(-2859493208917211689858401794 : Int)/10^30)
theorem v1334_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 82 5) 1) 14) v1334_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1334 : Material (14 : Basis) (82 : Basis) where
  plus := ![v1334_pa,v1334_pb,v1334_pg]
  minus := ![(Primitive.Addresses.material1334 1).one,v1334_mb,v1334_mg]
  upper := v1334_upper
  lower := (Primitive.Addresses.material1334 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1334_pa_checked.trans (by decide +kernel)
    · exact v1334_pb_checked.trans (by decide +kernel)
    · exact v1334_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 82 Primitive.Addresses.material1334
    · exact v1334_mb_checked.trans (by decide +kernel)
    · exact v1334_mg_checked.trans (by decide +kernel)
  upper_error := v1334_upper_checked
  lower_error := reuse_lower_error 14 82 Primitive.Addresses.material1334

def v1335_pa : Scalar.QComplex := ((999999342017099395271343786021 : Int)/10^30,(-1147155337462176403143091275 : Int)/10^30)
theorem v1335_pa_checked : Scalar.distance (sourceCoefficient 14 83 1 0) v1335_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1335_pb : Scalar.QComplex := ((-494971643153529988279994 : Int)/10^30,(-431477151617204175600487819 : Int)/10^30)
theorem v1335_pb_checked : Scalar.distance (sourceCoefficient 14 83 1 1) v1335_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1335_pg : Scalar.QComplex := ((-93086359427170859469312 : Int)/10^30,(106784584324232166561 : Int)/10^30)
theorem v1335_pg_checked : Scalar.distance (sourceCoefficient 14 83 1 2) v1335_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1335_mb : Scalar.QComplex := ((-867316807689091507824326 : Int)/10^30,(-431476563820305802291898569 : Int)/10^30)
theorem v1335_mb_checked : Scalar.distance (sourceCoefficient 14 83 3 1) v1335_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1335_mg : Scalar.QComplex := ((-93086232616578115275545 : Int)/10^30,(187113880295102185893 : Int)/10^30)
theorem v1335_mg_checked : Scalar.distance (sourceCoefficient 14 83 3 2) v1335_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1335_upper : Scalar.QComplex := ((999995872749504294759065509565 : Int)/10^30,(-2873061773998921097654033784 : Int)/10^30)
theorem v1335_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 83 5) 1) 14) v1335_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1335 : Material (14 : Basis) (83 : Basis) where
  plus := ![v1335_pa,v1335_pb,v1335_pg]
  minus := ![(Primitive.Addresses.material1335 1).one,v1335_mb,v1335_mg]
  upper := v1335_upper
  lower := (Primitive.Addresses.material1335 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1335_pa_checked.trans (by decide +kernel)
    · exact v1335_pb_checked.trans (by decide +kernel)
    · exact v1335_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 83 Primitive.Addresses.material1335
    · exact v1335_mb_checked.trans (by decide +kernel)
    · exact v1335_mg_checked.trans (by decide +kernel)
  upper_error := v1335_upper_checked
  lower_error := reuse_lower_error 14 83 Primitive.Addresses.material1335

def v1336_pa : Scalar.QComplex := ((999999301089766135000701288496 : Int)/10^30,(-1182294370812313220917707466 : Int)/10^30)
theorem v1336_pa_checked : Scalar.distance (sourceCoefficient 14 84 1 0) v1336_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1336_pb : Scalar.QComplex := ((-510133336530732627459487 : Int)/10^30,(-431477128359182252168709848 : Int)/10^30)
theorem v1336_pb_checked : Scalar.distance (sourceCoefficient 14 84 1 1) v1336_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1336_pg : Scalar.QComplex := ((-93086355013452643683178 : Int)/10^30,(110055550450792115457 : Int)/10^30)
theorem v1336_pg_checked : Scalar.distance (sourceCoefficient 14 84 1 2) v1336_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1336_mb : Scalar.QComplex := ((-882478475350277361553506 : Int)/10^30,(-431476527478434011679603115 : Int)/10^30)
theorem v1336_mb_checked : Scalar.distance (sourceCoefficient 14 84 3 1) v1336_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1336_mg : Scalar.QComplex := ((-93086225380165094542791 : Int)/10^30,(190384841394891921599 : Int)/10^30)
theorem v1336_mg_checked : Scalar.distance (sourceCoefficient 14 84 3 2) v1336_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1336_upper : Scalar.QComplex := ((999995771175448216811393946552 : Int)/10^30,(-2908200684376731152656409546 : Int)/10^30)
theorem v1336_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 84 5) 1) 14) v1336_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1336 : Material (14 : Basis) (84 : Basis) where
  plus := ![v1336_pa,v1336_pb,v1336_pg]
  minus := ![(Primitive.Addresses.material1336 1).one,v1336_mb,v1336_mg]
  upper := v1336_upper
  lower := (Primitive.Addresses.material1336 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1336_pa_checked.trans (by decide +kernel)
    · exact v1336_pb_checked.trans (by decide +kernel)
    · exact v1336_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 84 Primitive.Addresses.material1336
    · exact v1336_mb_checked.trans (by decide +kernel)
    · exact v1336_mg_checked.trans (by decide +kernel)
  upper_error := v1336_upper_checked
  lower_error := reuse_lower_error 14 84 Primitive.Addresses.material1336

def v1337_pa : Scalar.QComplex := ((999999204496347985343964566807 : Int)/10^30,(-1261351129227405774637281415 : Int)/10^30)
theorem v1337_pa_checked : Scalar.distance (sourceCoefficient 14 85 1 0) v1337_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1337_pb : Scalar.QComplex := ((-544244526762416193035286 : Int)/10^30,(-431477073435740498252742465 : Int)/10^30)
theorem v1337_pb_checked : Scalar.distance (sourceCoefficient 14 85 1 1) v1337_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1337_pg : Scalar.QComplex := ((-93086344593126469781055 : Int)/10^30,(117414659271981741516 : Int)/10^30)
theorem v1337_pg_checked : Scalar.distance (sourceCoefficient 14 85 1 2) v1337_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1337_mb : Scalar.QComplex := ((-916589605484349271826359 : Int)/10^30,(-431476443118591849305699713 : Int)/10^30)
theorem v1337_mb_checked : Scalar.distance (sourceCoefficient 14 85 3 1) v1337_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1337_mg : Scalar.QComplex := ((-93086208609263329875291 : Int)/10^30,(197743938483676831633 : Int)/10^30)
theorem v1337_mg_checked : Scalar.distance (sourceCoefficient 14 85 3 2) v1337_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1337_upper : Scalar.QComplex := ((999995538137380880353621337936 : Int)/10^30,(-2987257158334591866426386655 : Int)/10^30)
theorem v1337_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 85 5) 1) 14) v1337_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1337 : Material (14 : Basis) (85 : Basis) where
  plus := ![v1337_pa,v1337_pb,v1337_pg]
  minus := ![(Primitive.Addresses.material1337 1).one,v1337_mb,v1337_mg]
  upper := v1337_upper
  lower := (Primitive.Addresses.material1337 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1337_pa_checked.trans (by decide +kernel)
    · exact v1337_pb_checked.trans (by decide +kernel)
    · exact v1337_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 85 Primitive.Addresses.material1337
    · exact v1337_mb_checked.trans (by decide +kernel)
    · exact v1337_mg_checked.trans (by decide +kernel)
  upper_error := v1337_upper_checked
  lower_error := reuse_lower_error 14 85 Primitive.Addresses.material1337

def v1338_pa : Scalar.QComplex := ((999999185993634843159916476331 : Int)/10^30,(-1275935761591200817455159173 : Int)/10^30)
theorem v1338_pa_checked : Scalar.distance (sourceCoefficient 14 86 1 0) v1338_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1338_pb : Scalar.QComplex := ((-550537463014769028076841 : Int)/10^30,(-431477062910442467370124083 : Int)/10^30)
theorem v1338_pb_checked : Scalar.distance (sourceCoefficient 14 86 1 1) v1338_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1338_pg : Scalar.QComplex := ((-93086342596593275623765 : Int)/10^30,(118772290116123837757 : Int)/10^30)
theorem v1338_pg_checked : Scalar.distance (sourceCoefficient 14 86 1 2) v1338_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1338_mb : Scalar.QComplex := ((-922882530310696179896776 : Int)/10^30,(-431476427162777175019708969 : Int)/10^30)
theorem v1338_mb_checked : Scalar.distance (sourceCoefficient 14 86 3 1) v1338_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1338_mg : Scalar.QComplex := ((-93086205441156606047322 : Int)/10^30,(199101567099392691764 : Int)/10^30)
theorem v1338_mg_checked : Scalar.distance (sourceCoefficient 14 86 3 2) v1338_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1338_upper : Scalar.QComplex := ((999995494462942943389568059483 : Int)/10^30,(-3001841737042285904251387221 : Int)/10^30)
theorem v1338_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 86 5) 1) 14) v1338_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1338 : Material (14 : Basis) (86 : Basis) where
  plus := ![v1338_pa,v1338_pb,v1338_pg]
  minus := ![(Primitive.Addresses.material1338 1).one,v1338_mb,v1338_mg]
  upper := v1338_upper
  lower := (Primitive.Addresses.material1338 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1338_pa_checked.trans (by decide +kernel)
    · exact v1338_pb_checked.trans (by decide +kernel)
    · exact v1338_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 86 Primitive.Addresses.material1338
    · exact v1338_mb_checked.trans (by decide +kernel)
    · exact v1338_mg_checked.trans (by decide +kernel)
  upper_error := v1338_upper_checked
  lower_error := reuse_lower_error 14 86 Primitive.Addresses.material1338

def v1339_pa : Scalar.QComplex := ((999999184760925321475176453257 : Int)/10^30,(-1276901517244889471509704858 : Int)/10^30)
theorem v1339_pa_checked : Scalar.distance (sourceCoefficient 14 87 1 0) v1339_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1339_pb : Scalar.QComplex := ((-550954164550613952760309 : Int)/10^30,(-431477062209165238625935830 : Int)/10^30)
theorem v1339_pb_checked : Scalar.distance (sourceCoefficient 14 87 1 1) v1339_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1339_pg : Scalar.QComplex := ((-93086342463572667082207 : Int)/10^30,(118862188827614155136 : Int)/10^30)
theorem v1339_pg_checked : Scalar.distance (sourceCoefficient 14 87 1 2) v1339_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1339_mb : Scalar.QComplex := ((-923299231086213414531870 : Int)/10^30,(-431476426101905549499403533 : Int)/10^30)
theorem v1339_mb_checked : Scalar.distance (sourceCoefficient 14 87 3 1) v1339_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1339_mg : Scalar.QComplex := ((-93086205230557507906936 : Int)/10^30,(199191465662618816136 : Int)/10^30)
theorem v1339_mg_checked : Scalar.distance (sourceCoefficient 14 87 3 2) v1339_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1339_upper : Scalar.QComplex := ((999995491563428612082749481984 : Int)/10^30,(-3002807489130050153871259462 : Int)/10^30)
theorem v1339_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 87 5) 1) 14) v1339_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1339 : Material (14 : Basis) (87 : Basis) where
  plus := ![v1339_pa,v1339_pb,v1339_pg]
  minus := ![(Primitive.Addresses.material1339 1).one,v1339_mb,v1339_mg]
  upper := v1339_upper
  lower := (Primitive.Addresses.material1339 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1339_pa_checked.trans (by decide +kernel)
    · exact v1339_pb_checked.trans (by decide +kernel)
    · exact v1339_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 87 Primitive.Addresses.material1339
    · exact v1339_mb_checked.trans (by decide +kernel)
    · exact v1339_mg_checked.trans (by decide +kernel)
  upper_error := v1339_upper_checked
  lower_error := reuse_lower_error 14 87 Primitive.Addresses.material1339

def v1340_pa : Scalar.QComplex := ((999999169675938504768029606560 : Int)/10^30,(-1288661101124891114344856679 : Int)/10^30)
theorem v1340_pa_checked : Scalar.distance (sourceCoefficient 14 88 1 0) v1340_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1340_pb : Scalar.QComplex := ((-556028156720617103899866 : Int)/10^30,(-431477053626973768557945993 : Int)/10^30)
theorem v1340_pb_checked : Scalar.distance (sourceCoefficient 14 88 1 1) v1340_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1340_pg : Scalar.QComplex := ((-93086340835713155903380 : Int)/10^30,(119956846084092677146 : Int)/10^30)
theorem v1340_pg_checked : Scalar.distance (sourceCoefficient 14 88 1 2) v1340_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1340_mb : Scalar.QComplex := ((-928373213960892676767902 : Int)/10^30,(-431476413141090556384926793 : Int)/10^30)
theorem v1340_mb_checked : Scalar.distance (sourceCoefficient 14 88 3 1) v1340_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1340_mg : Scalar.QComplex := ((-93086202658058692046310 : Int)/10^30,(200286121106736971174 : Int)/10^30)
theorem v1340_mg_checked : Scalar.distance (sourceCoefficient 14 88 3 2) v1340_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1340_upper : Scalar.QComplex := ((999995456182489306924668081188 : Int)/10^30,(-3014567029460214238880350563 : Int)/10^30)
theorem v1340_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 88 5) 1) 14) v1340_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1340 : Material (14 : Basis) (88 : Basis) where
  plus := ![v1340_pa,v1340_pb,v1340_pg]
  minus := ![(Primitive.Addresses.material1340 1).one,v1340_mb,v1340_mg]
  upper := v1340_upper
  lower := (Primitive.Addresses.material1340 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1340_pa_checked.trans (by decide +kernel)
    · exact v1340_pb_checked.trans (by decide +kernel)
    · exact v1340_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 88 Primitive.Addresses.material1340
    · exact v1340_mb_checked.trans (by decide +kernel)
    · exact v1340_mg_checked.trans (by decide +kernel)
  upper_error := v1340_upper_checked
  lower_error := reuse_lower_error 14 88 Primitive.Addresses.material1340

def v1341_pa : Scalar.QComplex := ((999999148812610009359548463434 : Int)/10^30,(-1304750572125303964986033348 : Int)/10^30)
theorem v1341_pa_checked : Scalar.distance (sourceCoefficient 14 89 1 0) v1341_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1341_pb : Scalar.QComplex := ((-562970396283276668264672 : Int)/10^30,(-431477041755923161820534647 : Int)/10^30)
theorem v1341_pb_checked : Scalar.distance (sourceCoefficient 14 89 1 1) v1341_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1341_pg : Scalar.QComplex := ((-93086338584143828757496 : Int)/10^30,(121454556905298712703 : Int)/10^30)
theorem v1341_pg_checked : Scalar.distance (sourceCoefficient 14 89 1 2) v1341_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1341_mb : Scalar.QComplex := ((-935315440694457154590501 : Int)/10^30,(-431476395279204294070148749 : Int)/10^30)
theorem v1341_mb_checked : Scalar.distance (sourceCoefficient 14 89 3 1) v1341_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1341_mg : Scalar.QComplex := ((-93086199114033218953141 : Int)/10^30,(201783829427273896821 : Int)/10^30)
theorem v1341_mg_checked : Scalar.distance (sourceCoefficient 14 89 3 2) v1341_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1341_upper : Scalar.QComplex := ((999995407550224563687811413941 : Int)/10^30,(-3030656440489037759736750190 : Int)/10^30)
theorem v1341_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 89 5) 1) 14) v1341_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1341 : Material (14 : Basis) (89 : Basis) where
  plus := ![v1341_pa,v1341_pb,v1341_pg]
  minus := ![(Primitive.Addresses.material1341 1).one,v1341_mb,v1341_mg]
  upper := v1341_upper
  lower := (Primitive.Addresses.material1341 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1341_pa_checked.trans (by decide +kernel)
    · exact v1341_pb_checked.trans (by decide +kernel)
    · exact v1341_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 89 Primitive.Addresses.material1341
    · exact v1341_mb_checked.trans (by decide +kernel)
    · exact v1341_mg_checked.trans (by decide +kernel)
  upper_error := v1341_upper_checked
  lower_error := reuse_lower_error 14 89 Primitive.Addresses.material1341

def v1342_pa : Scalar.QComplex := ((999999114281010078848028478871 : Int)/10^30,(-1330953491052251170320503942 : Int)/10^30)
theorem v1342_pa_checked : Scalar.distance (sourceCoefficient 14 90 1 0) v1342_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1342_pb : Scalar.QComplex := ((-574276357525954935616587 : Int)/10^30,(-431477022104249045286953715 : Int)/10^30)
theorem v1342_pb_checked : Scalar.distance (sourceCoefficient 14 90 1 1) v1342_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1342_pg : Scalar.QComplex := ((-93086334857118121785953 : Int)/10^30,(123893692082336029096 : Int)/10^30)
theorem v1342_pg_checked : Scalar.distance (sourceCoefficient 14 90 1 2) v1342_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1342_mb : Scalar.QComplex := ((-946621380768899659316684 : Int)/10^30,(-431476365871002143913541173 : Int)/10^30)
theorem v1342_mb_checked : Scalar.distance (sourceCoefficient 14 90 3 1) v1342_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1342_mg : Scalar.QComplex := ((-93086193282145096510779 : Int)/10^30,(204222960479854386709 : Int)/10^30)
theorem v1342_mg_checked : Scalar.distance (sourceCoefficient 14 90 3 2) v1342_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1342_upper : Scalar.QComplex := ((999995327794815106263231368083 : Int)/10^30,(-3056859260791406436670644365 : Int)/10^30)
theorem v1342_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 90 5) 1) 14) v1342_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1342 : Material (14 : Basis) (90 : Basis) where
  plus := ![v1342_pa,v1342_pb,v1342_pg]
  minus := ![(Primitive.Addresses.material1342 1).one,v1342_mb,v1342_mg]
  upper := v1342_upper
  lower := (Primitive.Addresses.material1342 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1342_pa_checked.trans (by decide +kernel)
    · exact v1342_pb_checked.trans (by decide +kernel)
    · exact v1342_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 90 Primitive.Addresses.material1342
    · exact v1342_mb_checked.trans (by decide +kernel)
    · exact v1342_mg_checked.trans (by decide +kernel)
  upper_error := v1342_upper_checked
  lower_error := reuse_lower_error 14 90 Primitive.Addresses.material1342

def v1343_pa : Scalar.QComplex := ((999999094525766604722832730194 : Int)/10^30,(-1345714548820427590079691500 : Int)/10^30)
theorem v1343_pa_checked : Scalar.distance (sourceCoefficient 14 91 1 0) v1343_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1343_pb : Scalar.QComplex := ((-580645416755060661370630 : Int)/10^30,(-431477010859810818071314953 : Int)/10^30)
theorem v1343_pb_checked : Scalar.distance (sourceCoefficient 14 91 1 1) v1343_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1343_pg : Scalar.QComplex := ((-93086332724714925794015 : Int)/10^30,(125267745670703930756 : Int)/10^30)
theorem v1343_pg_checked : Scalar.distance (sourceCoefficient 14 91 1 2) v1343_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1343_mb : Scalar.QComplex := ((-952990427923069794299299 : Int)/10^30,(-431476349130356840577149634 : Int)/10^30)
theorem v1343_mb_checked : Scalar.distance (sourceCoefficient 14 91 3 1) v1343_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1343_mg : Scalar.QComplex := ((-93086189963996332824845 : Int)/10^30,(205597011716431421802 : Int)/10^30)
theorem v1343_mg_checked : Scalar.distance (sourceCoefficient 14 91 3 2) v1343_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1343_upper : Scalar.QComplex := ((999995282563354460080230522505 : Int)/10^30,(-3071620262478963211728375404 : Int)/10^30)
theorem v1343_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 91 5) 1) 14) v1343_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1343 : Material (14 : Basis) (91 : Basis) where
  plus := ![v1343_pa,v1343_pb,v1343_pg]
  minus := ![(Primitive.Addresses.material1343 1).one,v1343_mb,v1343_mg]
  upper := v1343_upper
  lower := (Primitive.Addresses.material1343 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1343_pa_checked.trans (by decide +kernel)
    · exact v1343_pb_checked.trans (by decide +kernel)
    · exact v1343_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 91 Primitive.Addresses.material1343
    · exact v1343_mb_checked.trans (by decide +kernel)
    · exact v1343_mg_checked.trans (by decide +kernel)
  upper_error := v1343_upper_checked
  lower_error := reuse_lower_error 14 91 Primitive.Addresses.material1343

def v1344_pa : Scalar.QComplex := ((999999051011375826510808702069 : Int)/10^30,(-1377670623831244204520204920 : Int)/10^30)
theorem v1344_pa_checked : Scalar.distance (sourceCoefficient 14 92 1 0) v1344_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1344_pb : Scalar.QComplex := ((-594433732702700284326726 : Int)/10^30,(-431476986087397597365012337 : Int)/10^30)
theorem v1344_pb_checked : Scalar.distance (sourceCoefficient 14 92 1 1) v1344_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1344_pg : Scalar.QComplex := ((-93086328027230265966663 : Int)/10^30,(128242421304033106163 : Int)/10^30)
theorem v1344_pg_checked : Scalar.distance (sourceCoefficient 14 92 1 2) v1344_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1344_mb : Scalar.QComplex := ((-966778717359212331384851 : Int)/10^30,(-431476312459257183657027642 : Int)/10^30)
theorem v1344_mb_checked : Scalar.distance (sourceCoefficient 14 92 3 1) v1344_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1344_mg : Scalar.QComplex := ((-93086182699502324939800 : Int)/10^30,(208571682188435214952 : Int)/10^30)
theorem v1344_mg_checked : Scalar.distance (sourceCoefficient 14 92 3 2) v1344_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1344_upper : Scalar.QComplex := ((999995183895742055251217042033 : Int)/10^30,(-3103576214793069033320612886 : Int)/10^30)
theorem v1344_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 92 5) 1) 14) v1344_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1344 : Material (14 : Basis) (92 : Basis) where
  plus := ![v1344_pa,v1344_pb,v1344_pg]
  minus := ![(Primitive.Addresses.material1344 1).one,v1344_mb,v1344_mg]
  upper := v1344_upper
  lower := (Primitive.Addresses.material1344 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1344_pa_checked.trans (by decide +kernel)
    · exact v1344_pb_checked.trans (by decide +kernel)
    · exact v1344_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 92 Primitive.Addresses.material1344
    · exact v1344_mb_checked.trans (by decide +kernel)
    · exact v1344_mg_checked.trans (by decide +kernel)
  upper_error := v1344_upper_checked
  lower_error := reuse_lower_error 14 92 Primitive.Addresses.material1344

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
