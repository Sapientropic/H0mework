import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B192
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B193

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4625_pa : Scalar.QComplex := ((999997125534678875496757264587 : Int)/10^30,(-2397691051761699372188442068 : Int)/10^30)
theorem v4625_pa_checked : Scalar.distance (sourceCoefficient 81 90 1 0) v4625_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4625_pb : Scalar.QComplex := ((-1034549783729404624555995 : Int)/10^30,(-431476277642941875305316832 : Int)/10^30)
theorem v4625_pb_checked : Scalar.distance (sourceCoefficient 81 90 1 1) v4625_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4625_pg : Scalar.QComplex := ((-93086161989886814580238 : Int)/10^30,(223192499205090539110 : Int)/10^30)
theorem v4625_pg_checked : Scalar.distance (sourceCoefficient 81 90 1 2) v4625_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4625_mb : Scalar.QComplex := ((-1406893993154938442872710 : Int)/10^30,(-431475224214735302907495779 : Int)/10^30)
theorem v4625_mb_checked : Scalar.distance (sourceCoefficient 81 90 3 1) v4625_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4625_mg : Scalar.QComplex := ((-93085934724579860993562 : Int)/10^30,(303521581452489858208 : Int)/10^30)
theorem v4625_mg_checked : Scalar.distance (sourceCoefficient 81 90 3 2) v4625_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4625_upper : Scalar.QComplex := ((999991497959189798003229816038 : Int)/10^30,(-4123591800324815758926083860 : Int)/10^30)
theorem v4625_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 90 5) 1) 14) v4625_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4625 : Material (81 : Basis) (90 : Basis) where
  plus := ![v4625_pa,v4625_pb,v4625_pg]
  minus := ![(Primitive.Addresses.material4625 1).one,v4625_mb,v4625_mg]
  upper := v4625_upper
  lower := (Primitive.Addresses.material4625 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4625_pa_checked.trans (by decide +kernel)
    · exact v4625_pb_checked.trans (by decide +kernel)
    · exact v4625_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 90 Primitive.Addresses.material4625
    · exact v4625_mb_checked.trans (by decide +kernel)
    · exact v4625_mg_checked.trans (by decide +kernel)
  upper_error := v4625_upper_checked
  lower_error := reuse_lower_error 81 90 Primitive.Addresses.material4625

def v4626_pa : Scalar.QComplex := ((999997090033246759543328352397 : Int)/10^30,(-2412452080057634715481485375 : Int)/10^30)
theorem v4626_pa_checked : Scalar.distance (sourceCoefficient 81 91 1 0) v4626_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4626_pb : Scalar.QComplex := ((-1040918834480771214815054 : Int)/10^30,(-431476261869086345696484650 : Int)/10^30)
theorem v4626_pb_checked : Scalar.distance (sourceCoefficient 81 91 1 1) v4626_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4626_pg : Scalar.QComplex := ((-93086158636019929681755 : Int)/10^30,(224566550507237102504 : Int)/10^30)
theorem v4626_pg_checked : Scalar.distance (sourceCoefficient 81 91 1 2) v4626_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4626_mb : Scalar.QComplex := ((-1413263027922689464427308 : Int)/10^30,(-431475202944681699594027833 : Int)/10^30)
theorem v4626_mb_checked : Scalar.distance (sourceCoefficient 81 91 3 1) v4626_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4626_mg : Scalar.QComplex := ((-93085930184969836113886 : Int)/10^30,(304895629348778255456 : Int)/10^30)
theorem v4626_mg_checked : Scalar.distance (sourceCoefficient 81 91 3 2) v4626_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4626_upper : Scalar.QComplex := ((999991436981614828504697715403 : Int)/10^30,(-4138352745363682240238060220 : Int)/10^30)
theorem v4626_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 91 5) 1) 14) v4626_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4626 : Material (81 : Basis) (91 : Basis) where
  plus := ![v4626_pa,v4626_pb,v4626_pg]
  minus := ![(Primitive.Addresses.material4626 1).one,v4626_mb,v4626_mg]
  upper := v4626_upper
  lower := (Primitive.Addresses.material4626 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4626_pa_checked.trans (by decide +kernel)
    · exact v4626_pb_checked.trans (by decide +kernel)
    · exact v4626_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 91 Primitive.Addresses.material4626
    · exact v4626_mb_checked.trans (by decide +kernel)
    · exact v4626_mg_checked.trans (by decide +kernel)
  upper_error := v4626_upper_checked
  lower_error := reuse_lower_error 81 91 Primitive.Addresses.material4626

def v4627_pa : Scalar.QComplex := ((999997012430080840266434768979 : Int)/10^30,(-2444408090468006379848395420 : Int)/10^30)
theorem v4627_pa_checked : Scalar.distance (sourceCoefficient 81 92 1 0) v4627_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4627_pb : Scalar.QComplex := ((-1054707131845985530205335 : Int)/10^30,(-431476227290980401220484795 : Int)/10^30)
theorem v4627_pb_checked : Scalar.distance (sourceCoefficient 81 92 1 1) v4627_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4627_pg : Scalar.QComplex := ((-93086151294200066434802 : Int)/10^30,(227541221129379140159 : Int)/10^30)
theorem v4627_pg_checked : Scalar.distance (sourceCoefficient 81 92 1 2) v4627_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4627_mb : Scalar.QComplex := ((-1427051290314542424426126 : Int)/10^30,(-431475156467909005807871020 : Int)/10^30)
theorem v4627_mb_checked : Scalar.distance (sourceCoefficient 81 92 3 1) v4627_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4627_mg : Scalar.QComplex := ((-93085920276145933844893 : Int)/10^30,(307870292527654592634 : Int)/10^30)
theorem v4627_mg_checked : Scalar.distance (sourceCoefficient 81 92 3 2) v4627_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4627_upper : Scalar.QComplex := ((999991304225389548344515718462 : Int)/10^30,(-4170308574243305942576420007 : Int)/10^30)
theorem v4627_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 92 5) 1) 14) v4627_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4627 : Material (81 : Basis) (92 : Basis) where
  plus := ![v4627_pa,v4627_pb,v4627_pg]
  minus := ![(Primitive.Addresses.material4627 1).one,v4627_mb,v4627_mg]
  upper := v4627_upper
  lower := (Primitive.Addresses.material4627 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4627_pa_checked.trans (by decide +kernel)
    · exact v4627_pb_checked.trans (by decide +kernel)
    · exact v4627_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 92 Primitive.Addresses.material4627
    · exact v4627_mb_checked.trans (by decide +kernel)
    · exact v4627_mg_checked.trans (by decide +kernel)
  upper_error := v4627_upper_checked
  lower_error := reuse_lower_error 81 92 Primitive.Addresses.material4627

def v4628_pa : Scalar.QComplex := ((999996919005234924341512908063 : Int)/10^30,(-2482333587095532684254559132 : Int)/10^30)
theorem v4628_pa_checked : Scalar.distance (sourceCoefficient 81 93 1 0) v4628_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4628_pb : Scalar.QComplex := ((-1071071127241219144926903 : Int)/10^30,(-431476185491206107124357076 : Int)/10^30)
theorem v4628_pb_checked : Scalar.distance (sourceCoefficient 81 93 1 1) v4628_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4628_pg : Scalar.QComplex := ((-93086142436991424974500 : Int)/10^30,(231071569794799510091 : Int)/10^30)
theorem v4628_pg_checked : Scalar.distance (sourceCoefficient 81 93 1 2) v4628_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4628_mb : Scalar.QComplex := ((-1443415243545390058111203 : Int)/10^30,(-431475100546759256585063245 : Int)/10^30)
theorem v4628_mb_checked : Scalar.distance (sourceCoefficient 81 93 3 1) v4628_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4628_mg : Scalar.QComplex := ((-93085908372408693071879 : Int)/10^30,(311400632235192665814 : Int)/10^30)
theorem v4628_mg_checked : Scalar.distance (sourceCoefficient 81 93 3 2) v4628_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4628_upper : Scalar.QComplex := ((999991145344716172820489545368 : Int)/10^30,(-4208233853142451446994245393 : Int)/10^30)
theorem v4628_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 93 5) 1) 14) v4628_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4628 : Material (81 : Basis) (93 : Basis) where
  plus := ![v4628_pa,v4628_pb,v4628_pg]
  minus := ![(Primitive.Addresses.material4628 1).one,v4628_mb,v4628_mg]
  upper := v4628_upper
  lower := (Primitive.Addresses.material4628 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4628_pa_checked.trans (by decide +kernel)
    · exact v4628_pb_checked.trans (by decide +kernel)
    · exact v4628_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 93 Primitive.Addresses.material4628
    · exact v4628_mb_checked.trans (by decide +kernel)
    · exact v4628_mg_checked.trans (by decide +kernel)
  upper_error := v4628_upper_checked
  lower_error := reuse_lower_error 81 93 Primitive.Addresses.material4628

def v4629_pa : Scalar.QComplex := ((999996806796818748641715270137 : Int)/10^30,(-2527132004062344151227988277 : Int)/10^30)
theorem v4629_pa_checked : Scalar.distance (sourceCoefficient 81 94 1 0) v4629_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4629_pb : Scalar.QComplex := ((-1090400631745738095883869 : Int)/10^30,(-431476135050392070254243770 : Int)/10^30)
theorem v4629_pb_checked : Scalar.distance (sourceCoefficient 81 94 1 1) v4629_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4629_pg : Scalar.QComplex := ((-93086131773431390476502 : Int)/10^30,(235241693913528487285 : Int)/10^30)
theorem v4629_pg_checked : Scalar.distance (sourceCoefficient 81 94 1 2) v4629_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4629_mb : Scalar.QComplex := ((-1462744697324500336152211 : Int)/10^30,(-431475033425472182301279568 : Int)/10^30)
theorem v4629_mb_checked : Scalar.distance (sourceCoefficient 81 94 3 1) v4629_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4629_mg : Scalar.QComplex := ((-93085894110223330059795 : Int)/10^30,(315570745599021808662 : Int)/10^30)
theorem v4629_mg_checked : Scalar.distance (sourceCoefficient 81 94 3 2) v4629_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4629_upper : Scalar.QComplex := ((999990955818463514299440532625 : Int)/10^30,(-4253032009725736382361741074 : Int)/10^30)
theorem v4629_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 94 5) 1) 14) v4629_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4629 : Material (81 : Basis) (94 : Basis) where
  plus := ![v4629_pa,v4629_pb,v4629_pg]
  minus := ![(Primitive.Addresses.material4629 1).one,v4629_mb,v4629_mg]
  upper := v4629_upper
  lower := (Primitive.Addresses.material4629 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4629_pa_checked.trans (by decide +kernel)
    · exact v4629_pb_checked.trans (by decide +kernel)
    · exact v4629_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 94 Primitive.Addresses.material4629
    · exact v4629_mb_checked.trans (by decide +kernel)
    · exact v4629_mg_checked.trans (by decide +kernel)
  upper_error := v4629_upper_checked
  lower_error := reuse_lower_error 81 94 Primitive.Addresses.material4629

def v4630_pa : Scalar.QComplex := ((999996693929910872509659053264 : Int)/10^30,(-2571406083868424399828135825 : Int)/10^30)
theorem v4630_pa_checked : Scalar.distance (sourceCoefficient 81 95 1 0) v4630_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4630_pb : Scalar.QComplex := ((-1109503895707556086914190 : Int)/10^30,(-431476084065563112534512297 : Int)/10^30)
theorem v4630_pb_checked : Scalar.distance (sourceCoefficient 81 95 1 1) v4630_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4630_pg : Scalar.QComplex := ((-93086121020540480055195 : Int)/10^30,(239363009266815597707 : Int)/10^30)
theorem v4630_pg_checked : Scalar.distance (sourceCoefficient 81 95 1 2) v4630_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4630_mb : Scalar.QComplex := ((-1481847910175688972847011 : Int)/10^30,(-431474965955405788584632494 : Int)/10^30)
theorem v4630_mb_checked : Scalar.distance (sourceCoefficient 81 95 3 1) v4630_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4630_mg : Scalar.QComplex := ((-93085879800826890697508 : Int)/10^30,(319692050138494296173 : Int)/10^30)
theorem v4630_mg_checked : Scalar.distance (sourceCoefficient 81 95 3 2) v4630_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4630_upper : Scalar.QComplex := ((999990766538678508018607126568 : Int)/10^30,(-4297305828792731770249873343 : Int)/10^30)
theorem v4630_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 95 5) 1) 14) v4630_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4630 : Material (81 : Basis) (95 : Basis) where
  plus := ![v4630_pa,v4630_pb,v4630_pg]
  minus := ![(Primitive.Addresses.material4630 1).one,v4630_mb,v4630_mg]
  upper := v4630_upper
  lower := (Primitive.Addresses.material4630 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4630_pa_checked.trans (by decide +kernel)
    · exact v4630_pb_checked.trans (by decide +kernel)
    · exact v4630_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 95 Primitive.Addresses.material4630
    · exact v4630_mb_checked.trans (by decide +kernel)
    · exact v4630_mg_checked.trans (by decide +kernel)
  upper_error := v4630_upper_checked
  lower_error := reuse_lower_error 81 95 Primitive.Addresses.material4630

def v4631_pa : Scalar.QComplex := ((999996639025203229931349012030 : Int)/10^30,(-2592670109633802365669569782 : Int)/10^30)
theorem v4631_pa_checked : Scalar.distance (sourceCoefficient 81 96 1 0) v4631_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4631_pb : Scalar.QComplex := ((-1118678841503773093129409 : Int)/10^30,(-431476059177612315340363790 : Int)/10^30)
theorem v4631_pb_checked : Scalar.distance (sourceCoefficient 81 96 1 1) v4631_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4631_pg : Scalar.QComplex := ((-93086115780450917962347 : Int)/10^30,(241342401151614164482 : Int)/10^30)
theorem v4631_pg_checked : Scalar.distance (sourceCoefficient 81 96 1 2) v4631_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4631_mb : Scalar.QComplex := ((-1491022831078473717108291 : Int)/10^30,(-431474933149899260395782519 : Int)/10^30)
theorem v4631_mb_checked : Scalar.distance (sourceCoefficient 81 96 3 1) v4631_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4631_mg : Scalar.QComplex := ((-93085872852613231649469 : Int)/10^30,(321671436764313514346 : Int)/10^30)
theorem v4631_mg_checked : Scalar.distance (sourceCoefficient 81 96 3 2) v4631_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4631_upper : Scalar.QComplex := ((999990674934273225858867690458 : Int)/10^30,(-4318569728127296731569865238 : Int)/10^30)
theorem v4631_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 96 5) 1) 14) v4631_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4631 : Material (81 : Basis) (96 : Basis) where
  plus := ![v4631_pa,v4631_pb,v4631_pg]
  minus := ![(Primitive.Addresses.material4631 1).one,v4631_mb,v4631_mg]
  upper := v4631_upper
  lower := (Primitive.Addresses.material4631 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4631_pa_checked.trans (by decide +kernel)
    · exact v4631_pb_checked.trans (by decide +kernel)
    · exact v4631_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 96 Primitive.Addresses.material4631
    · exact v4631_mb_checked.trans (by decide +kernel)
    · exact v4631_mg_checked.trans (by decide +kernel)
  upper_error := v4631_upper_checked
  lower_error := reuse_lower_error 81 96 Primitive.Addresses.material4631

def v4632_pa : Scalar.QComplex := ((999996446663347425195222787671 : Int)/10^30,(-2665832080035845585387453046 : Int)/10^30)
theorem v4632_pa_checked : Scalar.distance (sourceCoefficient 81 97 1 0) v4632_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4632_pb : Scalar.QComplex := ((-1150246573961991510061544 : Int)/10^30,(-431475971559774403922639593 : Int)/10^30)
theorem v4632_pb_checked : Scalar.distance (sourceCoefficient 81 97 1 1) v4632_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4632_pg : Scalar.QComplex := ((-93086097376029402512162 : Int)/10^30,(248152786360750944113 : Int)/10^30)
theorem v4632_pg_checked : Scalar.distance (sourceCoefficient 81 97 1 2) v4632_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4632_mb : Scalar.QComplex := ((-1522590476172334666578376 : Int)/10^30,(-431474818290562619552736297 : Int)/10^30)
theorem v4632_mb_checked : Scalar.distance (sourceCoefficient 81 97 3 1) v4632_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4632_mg : Scalar.QComplex := ((-93085848571142861885024 : Int)/10^30,(328481803555445767177 : Int)/10^30)
theorem v4632_mg_checked : Scalar.distance (sourceCoefficient 81 97 3 2) v4632_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4632_upper : Scalar.QComplex := ((999990356301780209691850266107 : Int)/10^30,(-4391731257564067058462892354 : Int)/10^30)
theorem v4632_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 97 5) 1) 14) v4632_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4632 : Material (81 : Basis) (97 : Basis) where
  plus := ![v4632_pa,v4632_pb,v4632_pg]
  minus := ![(Primitive.Addresses.material4632 1).one,v4632_mb,v4632_mg]
  upper := v4632_upper
  lower := (Primitive.Addresses.material4632 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4632_pa_checked.trans (by decide +kernel)
    · exact v4632_pb_checked.trans (by decide +kernel)
    · exact v4632_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 97 Primitive.Addresses.material4632
    · exact v4632_mb_checked.trans (by decide +kernel)
    · exact v4632_mg_checked.trans (by decide +kernel)
  upper_error := v4632_upper_checked
  lower_error := reuse_lower_error 81 97 Primitive.Addresses.material4632

def v4633_pa : Scalar.QComplex := ((999997527279269183672276547759 : Int)/10^30,(-2223833480116000690406270317 : Int)/10^30)
theorem v4633_pa_checked : Scalar.distance (sourceCoefficient 82 83 1 0) v4633_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4633_pb : Scalar.QComplex := ((-959534157089263308133319 : Int)/10^30,(-431476454064001941627242925 : Int)/10^30)
theorem v4633_pb_checked : Scalar.distance (sourceCoefficient 82 83 1 1) v4633_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4633_pg : Scalar.QComplex := ((-93086199718802931003132 : Int)/10^30,(207008719346190393986 : Int)/10^30)
theorem v4633_pg_checked : Scalar.distance (sourceCoefficient 82 83 1 2) v4633_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4633_mb : Scalar.QComplex := ((-1331878546689972435726721 : Int)/10^30,(-431475465370836891642728289 : Int)/10^30)
theorem v4633_mb_checked : Scalar.distance (sourceCoefficient 82 83 3 1) v4633_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4633_mg : Scalar.QComplex := ((-93085986419355057060352 : Int)/10^30,(287337840177905951000 : Int)/10^30)
theorem v4633_mg_checked : Scalar.distance (sourceCoefficient 82 83 3 2) v4633_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4633_upper : Scalar.QComplex := ((999992199765578179585890590281 : Int)/10^30,(-3949735180994264185805601804 : Int)/10^30)
theorem v4633_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 83 5) 1) 14) v4633_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4633 : Material (82 : Basis) (83 : Basis) where
  plus := ![v4633_pa,v4633_pb,v4633_pg]
  minus := ![(Primitive.Addresses.material4633 1).one,v4633_mb,v4633_mg]
  upper := v4633_upper
  lower := (Primitive.Addresses.material4633 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4633_pa_checked.trans (by decide +kernel)
    · exact v4633_pb_checked.trans (by decide +kernel)
    · exact v4633_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 83 Primitive.Addresses.material4633
    · exact v4633_mb_checked.trans (by decide +kernel)
    · exact v4633_mg_checked.trans (by decide +kernel)
  upper_error := v4633_upper_checked
  lower_error := reuse_lower_error 82 83 Primitive.Addresses.material4633

def v4634_pa : Scalar.QComplex := ((999997448518482225403524683149 : Int)/10^30,(-2258972449033245160723544450 : Int)/10^30)
theorem v4634_pa_checked : Scalar.distance (sourceCoefficient 82 84 1 0) v4634_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4634_pb : Scalar.QComplex := ((-974695831932236949042285 : Int)/10^30,(-431476419923124002242576016 : Int)/10^30)
theorem v4634_pb_checked : Scalar.distance (sourceCoefficient 82 84 1 1) v4634_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4634_pg : Scalar.QComplex := ((-93086192370267178324477 : Int)/10^30,(210279680474560522419 : Int)/10^30)
theorem v4634_pg_checked : Scalar.distance (sourceCoefficient 82 84 1 2) v4634_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4634_mb : Scalar.QComplex := ((-1347040186425521596198441 : Int)/10^30,(-431475418146129131467084548 : Int)/10^30)
theorem v4634_mb_checked : Scalar.distance (sourceCoefficient 82 84 3 1) v4634_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4634_mg : Scalar.QComplex := ((-93085976248129905414480 : Int)/10^30,(290608793746892372236 : Int)/10^30)
theorem v4634_mg_checked : Scalar.distance (sourceCoefficient 82 84 3 2) v4634_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4634_upper : Scalar.QComplex := ((999992060358235957452048545532 : Int)/10^30,(-3984873961642168999938650063 : Int)/10^30)
theorem v4634_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 84 5) 1) 14) v4634_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4634 : Material (82 : Basis) (84 : Basis) where
  plus := ![v4634_pa,v4634_pb,v4634_pg]
  minus := ![(Primitive.Addresses.material4634 1).one,v4634_mb,v4634_mg]
  upper := v4634_upper
  lower := (Primitive.Addresses.material4634 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4634_pa_checked.trans (by decide +kernel)
    · exact v4634_pb_checked.trans (by decide +kernel)
    · exact v4634_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 84 Primitive.Addresses.material4634
    · exact v4634_mb_checked.trans (by decide +kernel)
    · exact v4634_mg_checked.trans (by decide +kernel)
  upper_error := v4634_upper_checked
  lower_error := reuse_lower_error 82 84 Primitive.Addresses.material4634

def v4635_pa : Scalar.QComplex := ((999997266806327675957917876356 : Int)/10^30,(-2338029057625339636801852863 : Int)/10^30)
theorem v4635_pa_checked : Scalar.distance (sourceCoefficient 82 85 1 0) v4635_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4635_pb : Scalar.QComplex := ((-1008806979067085398185767 : Int)/10^30,(-431476340515136017674074329 : Int)/10^30)
theorem v4635_pb_checked : Scalar.distance (sourceCoefficient 82 85 1 1) v4635_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4635_pg : Scalar.QComplex := ((-93086175347108461867843 : Int)/10^30,(217638777673677109894 : Int)/10^30)
theorem v4635_pg_checked : Scalar.distance (sourceCoefficient 82 85 1 2) v4635_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4635_mb : Scalar.QComplex := ((-1381151252333713782933660 : Int)/10^30,(-431475309301787045783903637 : Int)/10^30)
theorem v4635_mb_checked : Scalar.distance (sourceCoefficient 82 85 3 1) v4635_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4635_mg : Scalar.QComplex := ((-93085952874408086054381 : Int)/10^30,(297967873515661467428 : Int)/10^30)
theorem v4635_mg_checked : Scalar.distance (sourceCoefficient 82 85 3 2) v4635_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4635_upper : Scalar.QComplex := ((999991742201817576467369982813 : Int)/10^30,(-4063930138870037665233889779 : Int)/10^30)
theorem v4635_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 85 5) 1) 14) v4635_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4635 : Material (82 : Basis) (85 : Basis) where
  plus := ![v4635_pa,v4635_pb,v4635_pg]
  minus := ![(Primitive.Addresses.material4635 1).one,v4635_mb,v4635_mg]
  upper := v4635_upper
  lower := (Primitive.Addresses.material4635 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4635_pa_checked.trans (by decide +kernel)
    · exact v4635_pb_checked.trans (by decide +kernel)
    · exact v4635_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 85 Primitive.Addresses.material4635
    · exact v4635_mb_checked.trans (by decide +kernel)
    · exact v4635_mg_checked.trans (by decide +kernel)
  upper_error := v4635_upper_checked
  lower_error := reuse_lower_error 82 85 Primitive.Addresses.material4635

def v4636_pa : Scalar.QComplex := ((999997232600650343758173544246 : Int)/10^30,(-2352613661614104283598346339 : Int)/10^30)
theorem v4636_pa_checked : Scalar.distance (sourceCoefficient 82 86 1 0) v4636_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4636_pb : Scalar.QComplex := ((-1015099907157313491712106 : Int)/10^30,(-431476325472854222581655251 : Int)/10^30)
theorem v4636_pb_checked : Scalar.distance (sourceCoefficient 82 86 1 1) v4636_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4636_pg : Scalar.QComplex := ((-93086172132464579296448 : Int)/10^30,(218996406316710705821 : Int)/10^30)
theorem v4636_pg_checked : Scalar.distance (sourceCoefficient 82 86 1 2) v4636_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4636_mb : Scalar.QComplex := ((-1387444165099985437504659 : Int)/10^30,(-431475288828997332713647444 : Int)/10^30)
theorem v4636_mb_checked : Scalar.distance (sourceCoefficient 82 86 3 1) v4636_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4636_mg : Scalar.QComplex := ((-93085948488193026828088 : Int)/10^30,(299325498879094984386 : Int)/10^30)
theorem v4636_mg_checked : Scalar.distance (sourceCoefficient 82 86 3 2) v4636_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4636_upper : Scalar.QComplex := ((999991682824487809936482624918 : Int)/10^30,(-4078514662100851938128276275 : Int)/10^30)
theorem v4636_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 86 5) 1) 14) v4636_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4636 : Material (82 : Basis) (86 : Basis) where
  plus := ![v4636_pa,v4636_pb,v4636_pg]
  minus := ![(Primitive.Addresses.material4636 1).one,v4636_mb,v4636_mg]
  upper := v4636_upper
  lower := (Primitive.Addresses.material4636 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4636_pa_checked.trans (by decide +kernel)
    · exact v4636_pb_checked.trans (by decide +kernel)
    · exact v4636_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 86 Primitive.Addresses.material4636
    · exact v4636_mb_checked.trans (by decide +kernel)
    · exact v4636_mg_checked.trans (by decide +kernel)
  upper_error := v4636_upper_checked
  lower_error := reuse_lower_error 82 86 Primitive.Addresses.material4636

def v4637_pa : Scalar.QComplex := ((999997230328132206784157056893 : Int)/10^30,(-2353579415380788981276061084 : Int)/10^30)
theorem v4637_pa_checked : Scalar.distance (sourceCoefficient 82 87 1 0) v4637_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4637_pb : Scalar.QComplex := ((-1015516608150358586779678 : Int)/10^30,(-431476324472474316701193087 : Int)/10^30)
theorem v4637_pb_checked : Scalar.distance (sourceCoefficient 82 87 1 1) v4637_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4637_pg : Scalar.QComplex := ((-93086171918783913706857 : Int)/10^30,(219086304881822309660 : Int)/10^30)
theorem v4637_pg_checked : Scalar.distance (sourceCoefficient 82 87 1 2) v4637_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4637_mb : Scalar.QComplex := ((-1387860865074590905348945 : Int)/10^30,(-431475287469023609838470624 : Int)/10^30)
theorem v4637_mb_checked : Scalar.distance (sourceCoefficient 82 87 3 1) v4637_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4637_mg : Scalar.QComplex := ((-93085948196934027991331 : Int)/10^30,(299415397226336453283 : Int)/10^30)
theorem v4637_mg_checked : Scalar.distance (sourceCoefficient 82 87 3 2) v4637_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4637_upper : Scalar.QComplex := ((999991678885169668810816601115 : Int)/10^30,(-4079480410506999702553464413 : Int)/10^30)
theorem v4637_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 87 5) 1) 14) v4637_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4637 : Material (82 : Basis) (87 : Basis) where
  plus := ![v4637_pa,v4637_pb,v4637_pg]
  minus := ![(Primitive.Addresses.material4637 1).one,v4637_mb,v4637_mg]
  upper := v4637_upper
  lower := (Primitive.Addresses.material4637 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4637_pa_checked.trans (by decide +kernel)
    · exact v4637_pb_checked.trans (by decide +kernel)
    · exact v4637_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 87 Primitive.Addresses.material4637
    · exact v4637_mb_checked.trans (by decide +kernel)
    · exact v4637_mg_checked.trans (by decide +kernel)
  upper_error := v4637_upper_checked
  lower_error := reuse_lower_error 82 87 Primitive.Addresses.material4637

def v4638_pa : Scalar.QComplex := ((999997202581851053299382620456 : Int)/10^30,(-2365338976203009507744439922 : Int)/10^30)
theorem v4638_pa_checked : Scalar.distance (sourceCoefficient 82 88 1 0) v4638_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4638_pb : Scalar.QComplex := ((-1020590593687752617735593 : Int)/10^30,(-431476312248240481188235600 : Int)/10^30)
theorem v4638_pb_checked : Scalar.distance (sourceCoefficient 82 88 1 1) v4638_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4638_pg : Scalar.QComplex := ((-93086169308762196949482 : Int)/10^30,(220180960349662114828 : Int)/10^30)
theorem v4638_pg_checked : Scalar.distance (sourceCoefficient 82 88 1 2) v4638_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4638_mb : Scalar.QComplex := ((-1392934838173744987144833 : Int)/10^30,(-431475270866173331020797541 : Int)/10^30)
theorem v4638_mb_checked : Scalar.distance (sourceCoefficient 82 88 3 1) v4638_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4638_mg : Scalar.QComplex := ((-93085944642274915770690 : Int)/10^30,(300510050034254809001 : Int)/10^30)
theorem v4638_mg_checked : Scalar.distance (sourceCoefficient 82 88 3 2) v4638_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4638_upper : Scalar.QComplex := ((999991630842994680024143417229 : Int)/10^30,(-4091239905927171611423689818 : Int)/10^30)
theorem v4638_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 88 5) 1) 14) v4638_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4638 : Material (82 : Basis) (88 : Basis) where
  plus := ![v4638_pa,v4638_pb,v4638_pg]
  minus := ![(Primitive.Addresses.material4638 1).one,v4638_mb,v4638_mg]
  upper := v4638_upper
  lower := (Primitive.Addresses.material4638 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4638_pa_checked.trans (by decide +kernel)
    · exact v4638_pb_checked.trans (by decide +kernel)
    · exact v4638_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 88 Primitive.Addresses.material4638
    · exact v4638_mb_checked.trans (by decide +kernel)
    · exact v4638_mg_checked.trans (by decide +kernel)
  upper_error := v4638_upper_checked
  lower_error := reuse_lower_error 82 88 Primitive.Addresses.material4638

def v4639_pa : Scalar.QComplex := ((999997164395330801195944014611 : Int)/10^30,(-2381428415414531860857963789 : Int)/10^30)
theorem v4639_pa_checked : Scalar.distance (sourceCoefficient 82 89 1 0) v4639_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4639_pb : Scalar.QComplex := ((-1027532824106284931459093 : Int)/10^30,(-431476295394144975379518366 : Int)/10^30)
theorem v4639_pb_checked : Scalar.distance (sourceCoefficient 82 89 1 1) v4639_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4639_pg : Scalar.QComplex := ((-93086165713397855557748 : Int)/10^30,(221678668704939622420 : Int)/10^30)
theorem v4639_pg_checked : Scalar.distance (sourceCoefficient 82 89 1 2) v4639_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4639_mb : Scalar.QComplex := ((-1399877051463042299215167 : Int)/10^30,(-431475248021251916020047036 : Int)/10^30)
theorem v4639_mb_checked : Scalar.distance (sourceCoefficient 82 89 3 1) v4639_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4639_mg : Scalar.QComplex := ((-93085939754457056773228 : Int)/10^30,(302007754729229549848 : Int)/10^30)
theorem v4639_mg_checked : Scalar.distance (sourceCoefficient 82 89 3 2) v4639_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4639_upper : Scalar.QComplex := ((999991564887618845692658949287 : Int)/10^30,(-4107329255268894556195061332 : Int)/10^30)
theorem v4639_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 89 5) 1) 14) v4639_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4639 : Material (82 : Basis) (89 : Basis) where
  plus := ![v4639_pa,v4639_pb,v4639_pg]
  minus := ![(Primitive.Addresses.material4639 1).one,v4639_mb,v4639_mg]
  upper := v4639_upper
  lower := (Primitive.Addresses.material4639 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4639_pa_checked.trans (by decide +kernel)
    · exact v4639_pb_checked.trans (by decide +kernel)
    · exact v4639_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 89 Primitive.Addresses.material4639
    · exact v4639_mb_checked.trans (by decide +kernel)
    · exact v4639_mg_checked.trans (by decide +kernel)
  upper_error := v4639_upper_checked
  lower_error := reuse_lower_error 82 89 Primitive.Addresses.material4639

def v4640_pa : Scalar.QComplex := ((999997101651604817712175880172 : Int)/10^30,(-2407631281974288477552628175 : Int)/10^30)
theorem v4640_pa_checked : Scalar.distance (sourceCoefficient 82 90 1 0) v4640_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4640_pb : Scalar.QComplex := ((-1038838770285453726581584 : Int)/10^30,(-431476267627205937065919014 : Int)/10^30)
theorem v4640_pb_checked : Scalar.distance (sourceCoefficient 82 90 1 1) v4640_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4640_pg : Scalar.QComplex := ((-93086159797900486138202 : Int)/10^30,(224117799819748060814 : Int)/10^30)
theorem v4640_pg_checked : Scalar.distance (sourceCoefficient 82 90 1 2) v4640_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4640_mb : Scalar.QComplex := ((-1411182969470872811012938 : Int)/10^30,(-431475210497800864897676600 : Int)/10^30)
theorem v4640_mb_checked : Scalar.distance (sourceCoefficient 82 90 3 1) v4640_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4640_mg : Scalar.QComplex := ((-93085931734101592271446 : Int)/10^30,(304446879831030194702 : Int)/10^30)
theorem v4640_mg_checked : Scalar.distance (sourceCoefficient 82 90 3 2) v4640_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4640_upper : Scalar.QComplex := ((999991456920215734963799104335 : Int)/10^30,(-4133531974512580455920662809 : Int)/10^30)
theorem v4640_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 90 5) 1) 14) v4640_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4640 : Material (82 : Basis) (90 : Basis) where
  plus := ![v4640_pa,v4640_pb,v4640_pg]
  minus := ![(Primitive.Addresses.material4640 1).one,v4640_mb,v4640_mg]
  upper := v4640_upper
  lower := (Primitive.Addresses.material4640 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4640_pa_checked.trans (by decide +kernel)
    · exact v4640_pb_checked.trans (by decide +kernel)
    · exact v4640_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 90 Primitive.Addresses.material4640
    · exact v4640_mb_checked.trans (by decide +kernel)
    · exact v4640_mg_checked.trans (by decide +kernel)
  upper_error := v4640_upper_checked
  lower_error := reuse_lower_error 82 90 Primitive.Addresses.material4640

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
