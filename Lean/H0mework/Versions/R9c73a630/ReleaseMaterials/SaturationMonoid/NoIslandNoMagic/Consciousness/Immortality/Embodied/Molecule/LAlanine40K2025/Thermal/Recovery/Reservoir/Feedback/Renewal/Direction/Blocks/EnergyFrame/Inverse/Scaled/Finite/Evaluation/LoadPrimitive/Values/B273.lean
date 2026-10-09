import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B182

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4369_pa : Scalar.QComplex := ((999997420152858283079698324621 : Int)/10^30,(-2271494580187803569038677680 : Int)/10^30)
theorem v4369_pa_checked : Scalar.distance (sourceCoefficient 69 92 1 0) v4369_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4369_pb : Scalar.QComplex := ((-980098820651045218288377 : Int)/10^30,(-431476394746612758669014480 : Int)/10^30)
theorem v4369_pb_checked : Scalar.distance (sourceCoefficient 69 92 1 1) v4369_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4369_pg : Scalar.QComplex := ((-93086188334265063618371 : Int)/10^30,(211445317788222964063 : Int)/10^30)
theorem v4369_pg_checked : Scalar.distance (sourceCoefficient 69 92 1 2) v4369_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4369_mb : Scalar.QComplex := ((-1352443151406354941419020 : Int)/10^30,(-431475388307091339506377153 : Int)/10^30)
theorem v4369_mb_checked : Scalar.distance (sourceCoefficient 69 92 3 1) v4369_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4369_mg : Scalar.QComplex := ((-93085971206236790161504 : Int)/10^30,(291774427143646719542 : Int)/10^30)
theorem v4369_mg_checked : Scalar.distance (sourceCoefficient 69 92 3 2) v4369_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4369_upper : Scalar.QComplex := ((999992010380591888489616671098 : Int)/10^30,(-3997396025189990391244785036 : Int)/10^30)
theorem v4369_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 92 5) 1) 14) v4369_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4369 : Material (69 : Basis) (92 : Basis) where
  plus := ![v4369_pa,v4369_pb,v4369_pg]
  minus := ![(Primitive.Addresses.material4369 1).one,v4369_mb,v4369_mg]
  upper := v4369_upper
  lower := (Primitive.Addresses.material4369 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4369_pa_checked.trans (by decide +kernel)
    · exact v4369_pb_checked.trans (by decide +kernel)
    · exact v4369_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 92 Primitive.Addresses.material4369
    · exact v4369_mb_checked.trans (by decide +kernel)
    · exact v4369_mg_checked.trans (by decide +kernel)
  upper_error := v4369_upper_checked
  lower_error := reuse_lower_error 69 92 Primitive.Addresses.material4369

def v4370_pa : Scalar.QComplex := ((999997333285862720928205474895 : Int)/10^30,(-2309420092402820856904491011 : Int)/10^30)
theorem v4370_pa_checked : Scalar.distance (sourceCoefficient 69 93 1 0) v4370_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4370_pb : Scalar.QComplex := ((-996462820530046725180593 : Int)/10^30,(-431476354833215103828129636 : Int)/10^30)
theorem v4370_pb_checked : Scalar.distance (sourceCoefficient 69 93 1 1) v4370_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4370_pg : Scalar.QComplex := ((-93086179985762148845338 : Int)/10^30,(214975667662796562651 : Int)/10^30)
theorem v4370_pg_checked : Scalar.distance (sourceCoefficient 69 93 1 2) v4370_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4370_mb : Scalar.QComplex := ((-1368807110748826878190319 : Int)/10^30,(-431475334272313657864828254 : Int)/10^30)
theorem v4370_mb_checked : Scalar.distance (sourceCoefficient 69 93 3 1) v4370_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4370_mg : Scalar.QComplex := ((-93085959811204043216591 : Int)/10^30,(295304768499327702031 : Int)/10^30)
theorem v4370_mg_checked : Scalar.distance (sourceCoefficient 69 93 3 2) v4370_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4370_upper : Scalar.QComplex := ((999991858057732196995905464033 : Int)/10^30,(-4035321330994858450461607274 : Int)/10^30)
theorem v4370_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 93 5) 1) 14) v4370_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4370 : Material (69 : Basis) (93 : Basis) where
  plus := ![v4370_pa,v4370_pb,v4370_pg]
  minus := ![(Primitive.Addresses.material4370 1).one,v4370_mb,v4370_mg]
  upper := v4370_upper
  lower := (Primitive.Addresses.material4370 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4370_pa_checked.trans (by decide +kernel)
    · exact v4370_pb_checked.trans (by decide +kernel)
    · exact v4370_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 93 Primitive.Addresses.material4370
    · exact v4370_mb_checked.trans (by decide +kernel)
    · exact v4370_mg_checked.trans (by decide +kernel)
  upper_error := v4370_upper_checked
  lower_error := reuse_lower_error 69 93 Primitive.Addresses.material4370

def v4371_pa : Scalar.QComplex := ((999997228823721260894182435283 : Int)/10^30,(-2354218528102317817796195409 : Int)/10^30)
theorem v4371_pa_checked : Scalar.distance (sourceCoefficient 69 94 1 0) v4371_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4371_pb : Scalar.QComplex := ((-1015792330423054020850449 : Int)/10^30,(-431476306620629957612514399 : Int)/10^30)
theorem v4371_pb_checked : Scalar.distance (sourceCoefficient 69 94 1 1) v4371_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4371_pg : Scalar.QComplex := ((-93086169923096323322166 : Int)/10^30,(219145793234657870616 : Int)/10^30)
theorem v4371_pg_checked : Scalar.distance (sourceCoefficient 69 94 1 2) v4371_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4371_mb : Scalar.QComplex := ((-1388136571839284671494716 : Int)/10^30,(-431475269379249994541338583 : Int)/10^30)
theorem v4371_mb_checked : Scalar.distance (sourceCoefficient 69 94 3 1) v4371_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4371_mg : Scalar.QComplex := ((-93085946149911411451202 : Int)/10^30,(299474883834833273657 : Int)/10^30)
theorem v4371_mg_checked : Scalar.distance (sourceCoefficient 69 94 3 2) v4371_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4371_upper : Scalar.QComplex := ((999991676277710386058636863386 : Int)/10^30,(-4080119519680168402299229284 : Int)/10^30)
theorem v4371_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 94 5) 1) 14) v4371_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4371 : Material (69 : Basis) (94 : Basis) where
  plus := ![v4371_pa,v4371_pb,v4371_pg]
  minus := ![(Primitive.Addresses.material4371 1).one,v4371_mb,v4371_mg]
  upper := v4371_upper
  lower := (Primitive.Addresses.material4371 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4371_pa_checked.trans (by decide +kernel)
    · exact v4371_pb_checked.trans (by decide +kernel)
    · exact v4371_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 94 Primitive.Addresses.material4371
    · exact v4371_mb_checked.trans (by decide +kernel)
    · exact v4371_mg_checked.trans (by decide +kernel)
  upper_error := v4371_upper_checked
  lower_error := reuse_lower_error 69 94 Primitive.Addresses.material4371

def v4372_pa : Scalar.QComplex := ((999997123612422879531841807858 : Int)/10^30,(-2398492626762784631309783055 : Int)/10^30)
theorem v4372_pa_checked : Scalar.distance (sourceCoefficient 69 95 1 0) v4372_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4372_pb : Scalar.QComplex := ((-1034895599808367853020948 : Int)/10^30,(-431476257837949879668407334 : Int)/10^30)
theorem v4372_pb_checked : Scalar.distance (sourceCoefficient 69 95 1 1) v4372_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4372_pg : Scalar.QComplex := ((-93086159764066535832146 : Int)/10^30,(223267110050517906921 : Int)/10^30)
theorem v4372_pg_checked : Scalar.distance (sourceCoefficient 69 95 1 2) v4372_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4372_mb : Scalar.QComplex := ((-1407239792014322432056921 : Int)/10^30,(-431475204111326980406999083 : Int)/10^30)
theorem v4372_mb_checked : Scalar.distance (sourceCoefficient 69 95 3 1) v4372_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4372_mg : Scalar.QComplex := ((-93085932434374611764002 : Int)/10^30,(303596190349353545046 : Int)/10^30)
theorem v4372_mg_checked : Scalar.distance (sourceCoefficient 69 95 3 2) v4372_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4372_upper : Scalar.QComplex := ((999991494653490931455713197511 : Int)/10^30,(-4124393370814409750211194500 : Int)/10^30)
theorem v4372_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 95 5) 1) 14) v4372_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4372 : Material (69 : Basis) (95 : Basis) where
  plus := ![v4372_pa,v4372_pb,v4372_pg]
  minus := ![(Primitive.Addresses.material4372 1).one,v4372_mb,v4372_mg]
  upper := v4372_upper
  lower := (Primitive.Addresses.material4372 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4372_pa_checked.trans (by decide +kernel)
    · exact v4372_pb_checked.trans (by decide +kernel)
    · exact v4372_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 95 Primitive.Addresses.material4372
    · exact v4372_mb_checked.trans (by decide +kernel)
    · exact v4372_mg_checked.trans (by decide +kernel)
  upper_error := v4372_upper_checked
  lower_error := reuse_lower_error 69 95 Primitive.Addresses.material4372

def v4373_pa : Scalar.QComplex := ((999997072384563603326664361632 : Int)/10^30,(-2419756661704065490678066856 : Int)/10^30)
theorem v4373_pa_checked : Scalar.distance (sourceCoefficient 69 96 1 0) v4373_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4373_pb : Scalar.QComplex := ((-1044070548244048671062247 : Int)/10^30,(-431476234007650663611581591 : Int)/10^30)
theorem v4373_pb_checked : Scalar.distance (sourceCoefficient 69 96 1 1) v4373_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4373_pg : Scalar.QComplex := ((-93086154809197542688920 : Int)/10^30,(225246502647109831290 : Int)/10^30)
theorem v4373_pg_checked : Scalar.distance (sourceCoefficient 69 96 1 2) v4373_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4373_mb : Scalar.QComplex := ((-1416414716469275685013859 : Int)/10^30,(-431475172363469361805058580 : Int)/10^30)
theorem v4373_mb_checked : Scalar.distance (sourceCoefficient 69 96 3 1) v4373_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4373_mg : Scalar.QComplex := ((-93085925771380801219322 : Int)/10^30,(305575577933098360927 : Int)/10^30)
theorem v4373_mg_checked : Scalar.distance (sourceCoefficient 69 96 3 2) v4373_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4373_upper : Scalar.QComplex := ((999991406725912702659414773530 : Int)/10^30,(-4145657285670770657910419240 : Int)/10^30)
theorem v4373_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 96 5) 1) 14) v4373_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4373 : Material (69 : Basis) (96 : Basis) where
  plus := ![v4373_pa,v4373_pb,v4373_pg]
  minus := ![(Primitive.Addresses.material4373 1).one,v4373_mb,v4373_mg]
  upper := v4373_upper
  lower := (Primitive.Addresses.material4373 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4373_pa_checked.trans (by decide +kernel)
    · exact v4373_pb_checked.trans (by decide +kernel)
    · exact v4373_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 96 Primitive.Addresses.material4373
    · exact v4373_mb_checked.trans (by decide +kernel)
    · exact v4373_mg_checked.trans (by decide +kernel)
  upper_error := v4373_upper_checked
  lower_error := reuse_lower_error 69 96 Primitive.Addresses.material4373

def v4374_pa : Scalar.QComplex := ((999996892673438916940146476616 : Int)/10^30,(-2492918664274420826169514198 : Int)/10^30)
theorem v4374_pa_checked : Scalar.distance (sourceCoefficient 69 97 1 0) v4374_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4374_pb : Scalar.QComplex := ((-1075638289955535817601692 : Int)/10^30,(-431476150028816695978665383 : Int)/10^30)
theorem v4374_pb_checked : Scalar.distance (sourceCoefficient 69 97 1 1) v4374_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4374_pg : Scalar.QComplex := ((-93086137386118839702499 : Int)/10^30,(232056890351607676633 : Int)/10^30)
theorem v4374_pg_checked : Scalar.distance (sourceCoefficient 69 97 1 2) v4374_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4374_mb : Scalar.QComplex := ((-1447982373956698427509126 : Int)/10^30,(-431475061143127324625179482 : Int)/10^30)
theorem v4374_mb_checked : Scalar.distance (sourceCoefficient 69 97 3 1) v4374_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4374_mg : Scalar.QComplex := ((-93085902471250725135650 : Int)/10^30,(312385948066445399448 : Int)/10^30)
theorem v4374_mg_checked : Scalar.distance (sourceCoefficient 69 97 3 2) v4374_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4374_upper : Scalar.QComplex := ((999991100744076443475638827481 : Int)/10^30,(-4218818869109819434564306510 : Int)/10^30)
theorem v4374_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 97 5) 1) 14) v4374_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4374 : Material (69 : Basis) (97 : Basis) where
  plus := ![v4374_pa,v4374_pb,v4374_pg]
  minus := ![(Primitive.Addresses.material4374 1).one,v4374_mb,v4374_mg]
  upper := v4374_upper
  lower := (Primitive.Addresses.material4374 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4374_pa_checked.trans (by decide +kernel)
    · exact v4374_pb_checked.trans (by decide +kernel)
    · exact v4374_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 97 Primitive.Addresses.material4374
    · exact v4374_mb_checked.trans (by decide +kernel)
    · exact v4374_mg_checked.trans (by decide +kernel)
  upper_error := v4374_upper_checked
  lower_error := reuse_lower_error 69 97 Primitive.Addresses.material4374

def v4375_pa : Scalar.QComplex := ((999998200098547427365693190057 : Int)/10^30,(-1897313802590396389313878049 : Int)/10^30)
theorem v4375_pa_checked : Scalar.distance (sourceCoefficient 70 71 1 0) v4375_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4375_pb : Scalar.QComplex := ((-818648256021506298679156 : Int)/10^30,(-431476744341197190945327135 : Int)/10^30)
theorem v4375_pb_checked : Scalar.distance (sourceCoefficient 70 71 1 1) v4375_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4375_pg : Scalar.QComplex := ((-93086262345997829476955 : Int)/10^30,(176614168268710386272 : Int)/10^30)
theorem v4375_pg_checked : Scalar.distance (sourceCoefficient 70 71 1 2) v4375_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4375_mb : Scalar.QComplex := ((-1190992948576621098162954 : Int)/10^30,(-431475877226111413532230380 : Int)/10^30)
theorem v4375_mb_checked : Scalar.distance (sourceCoefficient 70 71 3 1) v4375_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4375_mg : Scalar.QComplex := ((-93086075275655296668718 : Int)/10^30,(256943354462154982271 : Int)/10^30)
theorem v4375_mg_checked : Scalar.distance (sourceCoefficient 70 71 3 2) v4375_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4375_upper : Scalar.QComplex := ((999993436127196113438672925994 : Int)/10^30,(-3623217151006400423930814396 : Int)/10^30)
theorem v4375_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 71 5) 1) 14) v4375_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4375 : Material (70 : Basis) (71 : Basis) where
  plus := ![v4375_pa,v4375_pb,v4375_pg]
  minus := ![(Primitive.Addresses.material4375 1).one,v4375_mb,v4375_mg]
  upper := v4375_upper
  lower := (Primitive.Addresses.material4375 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4375_pa_checked.trans (by decide +kernel)
    · exact v4375_pb_checked.trans (by decide +kernel)
    · exact v4375_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 71 Primitive.Addresses.material4375
    · exact v4375_mb_checked.trans (by decide +kernel)
    · exact v4375_mg_checked.trans (by decide +kernel)
  upper_error := v4375_upper_checked
  lower_error := reuse_lower_error 70 71 Primitive.Addresses.material4375

def v4376_pa : Scalar.QComplex := ((999998149732879519941485173641 : Int)/10^30,(-1923676380650264131137926418 : Int)/10^30)
theorem v4376_pa_checked : Scalar.distance (sourceCoefficient 70 72 1 0) v4376_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4376_pb : Scalar.QComplex := ((-830023115575514260465864 : Int)/10^30,(-431476722467456005583821793 : Int)/10^30)
theorem v4376_pb_checked : Scalar.distance (sourceCoefficient 70 72 1 1) v4376_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4376_pg : Scalar.QComplex := ((-93086257642310706942954 : Int)/10^30,(179068166513579074738 : Int)/10^30)
theorem v4376_pg_checked : Scalar.distance (sourceCoefficient 70 72 1 2) v4376_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4376_mb : Scalar.QComplex := ((-1202367785019195504994708 : Int)/10^30,(-431475845536386882312046414 : Int)/10^30)
theorem v4376_mb_checked : Scalar.distance (sourceCoefficient 70 72 3 1) v4376_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4376_mg : Scalar.QComplex := ((-93086068454279964188829 : Int)/10^30,(259397347734217830369 : Int)/10^30)
theorem v4376_mg_checked : Scalar.distance (sourceCoefficient 70 72 3 2) v4376_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4376_upper : Scalar.QComplex := ((999993340262185082828204672056 : Int)/10^30,(-3649579602875731241022950478 : Int)/10^30)
theorem v4376_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 72 5) 1) 14) v4376_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4376 : Material (70 : Basis) (72 : Basis) where
  plus := ![v4376_pa,v4376_pb,v4376_pg]
  minus := ![(Primitive.Addresses.material4376 1).one,v4376_mb,v4376_mg]
  upper := v4376_upper
  lower := (Primitive.Addresses.material4376 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4376_pa_checked.trans (by decide +kernel)
    · exact v4376_pb_checked.trans (by decide +kernel)
    · exact v4376_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 72 Primitive.Addresses.material4376
    · exact v4376_mb_checked.trans (by decide +kernel)
    · exact v4376_mg_checked.trans (by decide +kernel)
  upper_error := v4376_upper_checked
  lower_error := reuse_lower_error 70 72 Primitive.Addresses.material4376

def v4377_pa : Scalar.QComplex := ((999998131510177396548260856041 : Int)/10^30,(-1933126005710100188245392110 : Int)/10^30)
theorem v4377_pa_checked : Scalar.distance (sourceCoefficient 70 73 1 0) v4377_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4377_pb : Scalar.QComplex := ((-834100416223472750518194 : Int)/10^30,(-431476714529502339111843235 : Int)/10^30)
theorem v4377_pb_checked : Scalar.distance (sourceCoefficient 70 73 1 1) v4377_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4377_pg : Scalar.QComplex := ((-93086255937905382836298 : Int)/10^30,(179947798358380961188 : Int)/10^30)
theorem v4377_pg_checked : Scalar.distance (sourceCoefficient 70 73 1 2) v4377_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4377_mb : Scalar.QComplex := ((-1206445077298892119963352 : Int)/10^30,(-431475834079909347119163057 : Int)/10^30)
theorem v4377_mb_checked : Scalar.distance (sourceCoefficient 70 73 3 1) v4377_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4377_mg : Scalar.QComplex := ((-93086065990792609793775 : Int)/10^30,(260276977780667548700 : Int)/10^30)
theorem v4377_mg_checked : Scalar.distance (sourceCoefficient 70 73 3 2) v4377_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4377_upper : Scalar.QComplex := ((999993305730314510021024633327 : Int)/10^30,(-3659029182410730088085782816 : Int)/10^30)
theorem v4377_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 73 5) 1) 14) v4377_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4377 : Material (70 : Basis) (73 : Basis) where
  plus := ![v4377_pa,v4377_pb,v4377_pg]
  minus := ![(Primitive.Addresses.material4377 1).one,v4377_mb,v4377_mg]
  upper := v4377_upper
  lower := (Primitive.Addresses.material4377 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4377_pa_checked.trans (by decide +kernel)
    · exact v4377_pb_checked.trans (by decide +kernel)
    · exact v4377_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 73 Primitive.Addresses.material4377
    · exact v4377_mb_checked.trans (by decide +kernel)
    · exact v4377_mg_checked.trans (by decide +kernel)
  upper_error := v4377_upper_checked
  lower_error := reuse_lower_error 70 73 Primitive.Addresses.material4377

def v4378_pa : Scalar.QComplex := ((999998110898386462173476518087 : Int)/10^30,(-1943759156472515958021519404 : Int)/10^30)
theorem v4378_pa_checked : Scalar.distance (sourceCoefficient 70 74 1 0) v4378_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4378_pb : Scalar.QComplex := ((-838688381557628669528995 : Int)/10^30,(-431476705535927098523768383 : Int)/10^30)
theorem v4378_pb_checked : Scalar.distance (sourceCoefficient 70 74 1 1) v4378_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4378_pg : Scalar.QComplex := ((-93086254008434934414825 : Int)/10^30,(180937600380134673265 : Int)/10^30)
theorem v4378_pg_checked : Scalar.distance (sourceCoefficient 70 74 1 2) v4378_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4378_mb : Scalar.QComplex := ((-1211033033163688487658670 : Int)/10^30,(-431475821127130006161643914 : Int)/10^30)
theorem v4378_mb_checked : Scalar.distance (sourceCoefficient 70 74 3 1) v4378_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4378_mg : Scalar.QComplex := ((-93086063207168314057086 : Int)/10^30,(261266777768826635027 : Int)/10^30)
theorem v4378_mg_checked : Scalar.distance (sourceCoefficient 70 74 3 2) v4378_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4378_upper : Scalar.QComplex := ((999993266766700690459862833486 : Int)/10^30,(-3669662281762235589209619887 : Int)/10^30)
theorem v4378_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 74 5) 1) 14) v4378_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4378 : Material (70 : Basis) (74 : Basis) where
  plus := ![v4378_pa,v4378_pb,v4378_pg]
  minus := ![(Primitive.Addresses.material4378 1).one,v4378_mb,v4378_mg]
  upper := v4378_upper
  lower := (Primitive.Addresses.material4378 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4378_pa_checked.trans (by decide +kernel)
    · exact v4378_pb_checked.trans (by decide +kernel)
    · exact v4378_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 74 Primitive.Addresses.material4378
    · exact v4378_mb_checked.trans (by decide +kernel)
    · exact v4378_mg_checked.trans (by decide +kernel)
  upper_error := v4378_upper_checked
  lower_error := reuse_lower_error 70 74 Primitive.Addresses.material4378

def v4379_pa : Scalar.QComplex := ((999998081991600113840336298603 : Int)/10^30,(-1958574257212653475229204797 : Int)/10^30)
theorem v4379_pa_checked : Scalar.distance (sourceCoefficient 70 75 1 0) v4379_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4379_pb : Scalar.QComplex := ((-845080764166898944672220 : Int)/10^30,(-431476692896785925702287565 : Int)/10^30)
theorem v4379_pb_checked : Scalar.distance (sourceCoefficient 70 75 1 1) v4379_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4379_pg : Scalar.QComplex := ((-93086251299643775435351 : Int)/10^30,(182316685180843822932 : Int)/10^30)
theorem v4379_pg_checked : Scalar.distance (sourceCoefficient 70 75 1 2) v4379_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4379_mb : Scalar.QComplex := ((-1217425402485772984695096 : Int)/10^30,(-431475802971655249895100139 : Int)/10^30)
theorem v4379_mb_checked : Scalar.distance (sourceCoefficient 70 75 3 1) v4379_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4379_mg : Scalar.QComplex := ((-93086059308290092346093 : Int)/10^30,(262645859718474715326 : Int)/10^30)
theorem v4379_mg_checked : Scalar.distance (sourceCoefficient 70 75 3 2) v4379_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4379_upper : Scalar.QComplex := ((999993212290437533352276918681 : Int)/10^30,(-3684477310546530023914528420 : Int)/10^30)
theorem v4379_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 75 5) 1) 14) v4379_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4379 : Material (70 : Basis) (75 : Basis) where
  plus := ![v4379_pa,v4379_pb,v4379_pg]
  minus := ![(Primitive.Addresses.material4379 1).one,v4379_mb,v4379_mg]
  upper := v4379_upper
  lower := (Primitive.Addresses.material4379 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4379_pa_checked.trans (by decide +kernel)
    · exact v4379_pb_checked.trans (by decide +kernel)
    · exact v4379_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 75 Primitive.Addresses.material4379
    · exact v4379_mb_checked.trans (by decide +kernel)
    · exact v4379_mg_checked.trans (by decide +kernel)
  upper_error := v4379_upper_checked
  lower_error := reuse_lower_error 70 75 Primitive.Addresses.material4379

def v4380_pa : Scalar.QComplex := ((999998057568905222244213954973 : Int)/10^30,(-1971004418188085547087748003 : Int)/10^30)
theorem v4380_pa_checked : Scalar.distance (sourceCoefficient 70 76 1 0) v4380_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4380_pb : Scalar.QComplex := ((-850444098880307756042107 : Int)/10^30,(-431476682194880393645920435 : Int)/10^30)
theorem v4380_pb_checked : Scalar.distance (sourceCoefficient 70 76 1 1) v4380_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4380_pg : Scalar.QComplex := ((-93086249008525066665628 : Int)/10^30,(183473764453504354549 : Int)/10^30)
theorem v4380_pg_checked : Scalar.distance (sourceCoefficient 70 76 1 2) v4380_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4380_mb : Scalar.QComplex := ((-1222788725966904687525467 : Int)/10^30,(-431475787641437400603985133 : Int)/10^30)
theorem v4380_mb_checked : Scalar.distance (sourceCoefficient 70 76 3 1) v4380_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4380_mg : Scalar.QComplex := ((-93086056018664937274453 : Int)/10^30,(263802936583169495085 : Int)/10^30)
theorem v4380_mg_checked : Scalar.distance (sourceCoefficient 70 76 3 2) v4380_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4380_upper : Scalar.QComplex := ((999993166414448828290478972010 : Int)/10^30,(-3696907410857341698823333565 : Int)/10^30)
theorem v4380_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 76 5) 1) 14) v4380_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4380 : Material (70 : Basis) (76 : Basis) where
  plus := ![v4380_pa,v4380_pb,v4380_pg]
  minus := ![(Primitive.Addresses.material4380 1).one,v4380_mb,v4380_mg]
  upper := v4380_upper
  lower := (Primitive.Addresses.material4380 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4380_pa_checked.trans (by decide +kernel)
    · exact v4380_pb_checked.trans (by decide +kernel)
    · exact v4380_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 76 Primitive.Addresses.material4380
    · exact v4380_mb_checked.trans (by decide +kernel)
    · exact v4380_mg_checked.trans (by decide +kernel)
  upper_error := v4380_upper_checked
  lower_error := reuse_lower_error 70 76 Primitive.Addresses.material4380

def v4381_pa : Scalar.QComplex := ((999998051892818201938890374389 : Int)/10^30,(-1973882106022173363292754558 : Int)/10^30)
theorem v4381_pa_checked : Scalar.distance (sourceCoefficient 70 77 1 0) v4381_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4381_pb : Scalar.QComplex := ((-851685756409962404037947 : Int)/10^30,(-431476679704626907188085920 : Int)/10^30)
theorem v4381_pb_checked : Scalar.distance (sourceCoefficient 70 77 1 1) v4381_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4381_pg : Scalar.QComplex := ((-93086248475719615700539 : Int)/10^30,(183741638131361599156 : Int)/10^30)
theorem v4381_pg_checked : Scalar.distance (sourceCoefficient 70 77 1 2) v4381_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4381_mb : Scalar.QComplex := ((-1224030380885256888718901 : Int)/10^30,(-431475784079690315468579386 : Int)/10^30)
theorem v4381_mb_checked : Scalar.distance (sourceCoefficient 70 77 3 1) v4381_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4381_mg : Scalar.QComplex := ((-93086055254696765288974 : Int)/10^30,(264070809701498019477 : Int)/10^30)
theorem v4381_mg_checked : Scalar.distance (sourceCoefficient 70 77 3 2) v4381_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4381_upper : Scalar.QComplex := ((999993155771742122015446918514 : Int)/10^30,(-3699785084609040256658407620 : Int)/10^30)
theorem v4381_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 77 5) 1) 14) v4381_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4381 : Material (70 : Basis) (77 : Basis) where
  plus := ![v4381_pa,v4381_pb,v4381_pg]
  minus := ![(Primitive.Addresses.material4381 1).one,v4381_mb,v4381_mg]
  upper := v4381_upper
  lower := (Primitive.Addresses.material4381 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4381_pa_checked.trans (by decide +kernel)
    · exact v4381_pb_checked.trans (by decide +kernel)
    · exact v4381_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 77 Primitive.Addresses.material4381
    · exact v4381_mb_checked.trans (by decide +kernel)
    · exact v4381_mg_checked.trans (by decide +kernel)
  upper_error := v4381_upper_checked
  lower_error := reuse_lower_error 70 77 Primitive.Addresses.material4381

def v4382_pa : Scalar.QComplex := ((999998017595830933183247673265 : Int)/10^30,(-1991181661277379274758284381 : Int)/10^30)
theorem v4382_pa_checked : Scalar.distance (sourceCoefficient 70 78 1 0) v4382_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4382_pb : Scalar.QComplex := ((-859150125070684374676153 : Int)/10^30,(-431476664633770899300768784 : Int)/10^30)
theorem v4382_pb_checked : Scalar.distance (sourceCoefficient 70 78 1 1) v4382_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4382_pg : Scalar.QComplex := ((-93086245253743592352252 : Int)/10^30,(185351991908984233096 : Int)/10^30)
theorem v4382_pg_checked : Scalar.distance (sourceCoefficient 70 78 1 2) v4382_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4382_mb : Scalar.QComplex := ((-1231494733761183299820794 : Int)/10^30,(-431475762567425947631456516 : Int)/10^30)
theorem v4382_mb_checked : Scalar.distance (sourceCoefficient 70 78 3 1) v4382_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4382_mg : Scalar.QComplex := ((-93086050643059159183071 : Int)/10^30,(265681160099092149468 : Int)/10^30)
theorem v4382_mg_checked : Scalar.distance (sourceCoefficient 70 78 3 2) v4382_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4382_upper : Scalar.QComplex := ((999993091617342967501376460810 : Int)/10^30,(-3717084554905102136513527740 : Int)/10^30)
theorem v4382_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 78 5) 1) 14) v4382_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4382 : Material (70 : Basis) (78 : Basis) where
  plus := ![v4382_pa,v4382_pb,v4382_pg]
  minus := ![(Primitive.Addresses.material4382 1).one,v4382_mb,v4382_mg]
  upper := v4382_upper
  lower := (Primitive.Addresses.material4382 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4382_pa_checked.trans (by decide +kernel)
    · exact v4382_pb_checked.trans (by decide +kernel)
    · exact v4382_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 78 Primitive.Addresses.material4382
    · exact v4382_mb_checked.trans (by decide +kernel)
    · exact v4382_mg_checked.trans (by decide +kernel)
  upper_error := v4382_upper_checked
  lower_error := reuse_lower_error 70 78 Primitive.Addresses.material4382

def v4383_pa : Scalar.QComplex := ((999998006475297497580134908661 : Int)/10^30,(-1996758731260264263683170395 : Int)/10^30)
theorem v4383_pa_checked : Scalar.distance (sourceCoefficient 70 79 1 0) v4383_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4383_pb : Scalar.QComplex := ((-861556505202027676503100 : Int)/10^30,(-431476659738493964027650199 : Int)/10^30)
theorem v4383_pb_checked : Scalar.distance (sourceCoefficient 70 79 1 1) v4383_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4383_pg : Scalar.QComplex := ((-93086244208107700671441 : Int)/10^30,(185871141421476161145 : Int)/10^30)
theorem v4383_pg_checked : Scalar.distance (sourceCoefficient 70 79 1 2) v4383_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4383_mb : Scalar.QComplex := ((-1233901108772117781691697 : Int)/10^30,(-431475755595553161082282231 : Int)/10^30)
theorem v4383_mb_checked : Scalar.distance (sourceCoefficient 70 79 3 1) v4383_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4383_mg : Scalar.QComplex := ((-93086049149421009185832 : Int)/10^30,(266200308515944306884 : Int)/10^30)
theorem v4383_mg_checked : Scalar.distance (sourceCoefficient 70 79 3 2) v4383_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4383_upper : Scalar.QComplex := ((999993070871309252003615241765 : Int)/10^30,(-3722661597388564651653316485 : Int)/10^30)
theorem v4383_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 79 5) 1) 14) v4383_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4383 : Material (70 : Basis) (79 : Basis) where
  plus := ![v4383_pa,v4383_pb,v4383_pg]
  minus := ![(Primitive.Addresses.material4383 1).one,v4383_mb,v4383_mg]
  upper := v4383_upper
  lower := (Primitive.Addresses.material4383 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4383_pa_checked.trans (by decide +kernel)
    · exact v4383_pb_checked.trans (by decide +kernel)
    · exact v4383_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 79 Primitive.Addresses.material4383
    · exact v4383_mb_checked.trans (by decide +kernel)
    · exact v4383_mg_checked.trans (by decide +kernel)
  upper_error := v4383_upper_checked
  lower_error := reuse_lower_error 70 79 Primitive.Addresses.material4383

def v4384_pa : Scalar.QComplex := ((999997989041682540538050930437 : Int)/10^30,(-2005470665695604069896758373 : Int)/10^30)
theorem v4384_pa_checked : Scalar.distance (sourceCoefficient 70 80 1 0) v4384_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4384_pb : Scalar.QComplex := ((-865315508743833549494960 : Int)/10^30,(-431476652055779184973360358 : Int)/10^30)
theorem v4384_pb_checked : Scalar.distance (sourceCoefficient 70 80 1 1) v4384_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4384_pg : Scalar.QComplex := ((-93086242567961492121237 : Int)/10^30,(186682104259802492565 : Int)/10^30)
theorem v4384_pg_checked : Scalar.distance (sourceCoefficient 70 80 1 2) v4384_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4384_mb : Scalar.QComplex := ((-1237660104284438003425582 : Int)/10^30,(-431475744668990485310193577 : Int)/10^30)
theorem v4384_mb_checked : Scalar.distance (sourceCoefficient 70 80 3 1) v4384_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4384_mg : Scalar.QComplex := ((-93086046809451006271784 : Int)/10^30,(267011269636939802226 : Int)/10^30)
theorem v4384_mg_checked : Scalar.distance (sourceCoefficient 70 80 3 2) v4384_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4384_upper : Scalar.QComplex := ((999993038401711765404780690890 : Int)/10^30,(-3731373488759663641475017256 : Int)/10^30)
theorem v4384_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 70 80 5) 1) 14) v4384_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4384 : Material (70 : Basis) (80 : Basis) where
  plus := ![v4384_pa,v4384_pb,v4384_pg]
  minus := ![(Primitive.Addresses.material4384 1).one,v4384_mb,v4384_mg]
  upper := v4384_upper
  lower := (Primitive.Addresses.material4384 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4384_pa_checked.trans (by decide +kernel)
    · exact v4384_pb_checked.trans (by decide +kernel)
    · exact v4384_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 70 80 Primitive.Addresses.material4384
    · exact v4384_mb_checked.trans (by decide +kernel)
    · exact v4384_mg_checked.trans (by decide +kernel)
  upper_error := v4384_upper_checked
  lower_error := reuse_lower_error 70 80 Primitive.Addresses.material4384

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
