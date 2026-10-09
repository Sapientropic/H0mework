import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B181
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B182

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4353_pa : Scalar.QComplex := ((999998085518899177294127023696 : Int)/10^30,(-1956772479469068559864207841 : Int)/10^30)
theorem v4353_pa_checked : Scalar.distance (sourceCoefficient 69 76 1 0) v4353_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4353_pb : Scalar.QComplex := ((-844303336831656988789993 : Int)/10^30,(-431476694039544038143329739 : Int)/10^30)
theorem v4353_pb_checked : Scalar.distance (sourceCoefficient 69 76 1 1) v4353_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4353_pg : Scalar.QComplex := ((-93086251587084229402640 : Int)/10^30,(182148964043289521238 : Int)/10^30)
theorem v4353_pg_checked : Scalar.distance (sourceCoefficient 69 76 1 2) v4353_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4353_mb : Scalar.QComplex := ((-1216647976426151539029710 : Int)/10^30,(-431475804785297713121480848 : Int)/10^30)
theorem v4353_mb_checked : Scalar.distance (sourceCoefficient 69 76 3 1) v4353_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4353_mg : Scalar.QComplex := ((-93086059740466227115904 : Int)/10^30,(262478138891418824314 : Int)/10^30)
theorem v4353_mg_checked : Scalar.distance (sourceCoefficient 69 76 3 2) v4353_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4353_upper : Scalar.QComplex := ((999993218927436272735972381018 : Int)/10^30,(-3682675541574279595387644472 : Int)/10^30)
theorem v4353_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 76 5) 1) 14) v4353_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4353 : Material (69 : Basis) (76 : Basis) where
  plus := ![v4353_pa,v4353_pb,v4353_pg]
  minus := ![(Primitive.Addresses.material4353 1).one,v4353_mb,v4353_mg]
  upper := v4353_upper
  lower := (Primitive.Addresses.material4353 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4353_pa_checked.trans (by decide +kernel)
    · exact v4353_pb_checked.trans (by decide +kernel)
    · exact v4353_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 76 Primitive.Addresses.material4353
    · exact v4353_mb_checked.trans (by decide +kernel)
    · exact v4353_mg_checked.trans (by decide +kernel)
  upper_error := v4353_upper_checked
  lower_error := reuse_lower_error 69 76 Primitive.Addresses.material4353

def v4354_pa : Scalar.QComplex := ((999998079883767313448990699119 : Int)/10^30,(-1959650167383646818289807038 : Int)/10^30)
theorem v4354_pa_checked : Scalar.distance (sourceCoefficient 69 77 1 0) v4354_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4354_pb : Scalar.QComplex := ((-845544994384464847598224 : Int)/10^30,(-431476691561071371186750798 : Int)/10^30)
theorem v4354_pb_checked : Scalar.distance (sourceCoefficient 69 77 1 1) v4354_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4354_pg : Scalar.QComplex := ((-93086251057455752850705 : Int)/10^30,(182416837727390572425 : Int)/10^30)
theorem v4354_pg_checked : Scalar.distance (sourceCoefficient 69 77 1 2) v4354_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4354_mb : Scalar.QComplex := ((-1217889631377823259055706 : Int)/10^30,(-431475801235331423120615016 : Int)/10^30)
theorem v4354_mb_checked : Scalar.distance (sourceCoefficient 69 77 3 1) v4354_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4354_mg : Scalar.QComplex := ((-93086058979675022972522 : Int)/10^30,(262746012018732738795 : Int)/10^30)
theorem v4354_mg_checked : Scalar.distance (sourceCoefficient 69 77 3 2) v4354_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4354_upper : Scalar.QComplex := ((999993208325684523004031729842 : Int)/10^30,(-3685553215477153360189764977 : Int)/10^30)
theorem v4354_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 77 5) 1) 14) v4354_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4354 : Material (69 : Basis) (77 : Basis) where
  plus := ![v4354_pa,v4354_pb,v4354_pg]
  minus := ![(Primitive.Addresses.material4354 1).one,v4354_mb,v4354_mg]
  upper := v4354_upper
  lower := (Primitive.Addresses.material4354 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4354_pa_checked.trans (by decide +kernel)
    · exact v4354_pb_checked.trans (by decide +kernel)
    · exact v4354_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 77 Primitive.Addresses.material4354
    · exact v4354_mb_checked.trans (by decide +kernel)
    · exact v4354_mg_checked.trans (by decide +kernel)
  upper_error := v4354_upper_checked
  lower_error := reuse_lower_error 69 77 Primitive.Addresses.material4354

def v4355_pa : Scalar.QComplex := ((999998045832986733211410555661 : Int)/10^30,(-1976949723125214289486487976 : Int)/10^30)
theorem v4355_pa_checked : Scalar.distance (sourceCoefficient 69 78 1 0) v4355_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4355_pb : Scalar.QComplex := ((-853009363185089537245874 : Int)/10^30,(-431476676561037130507005946 : Int)/10^30)
theorem v4355_pb_checked : Scalar.distance (sourceCoefficient 69 78 1 1) v4355_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4355_pg : Scalar.QComplex := ((-93086247854578480850684 : Int)/10^30,(184027191542741257339 : Int)/10^30)
theorem v4355_pg_checked : Scalar.distance (sourceCoefficient 69 78 1 2) v4355_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4355_mb : Scalar.QComplex := ((-1225353984454768332481014 : Int)/10^30,(-431475779793888675391138264 : Int)/10^30)
theorem v4355_mb_checked : Scalar.distance (sourceCoefficient 69 78 3 1) v4355_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4355_mg : Scalar.QComplex := ((-93086054387136128545938 : Int)/10^30,(264356362470536267951 : Int)/10^30)
theorem v4355_mg_checked : Scalar.distance (sourceCoefficient 69 78 3 2) v4355_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4355_upper : Scalar.QComplex := ((999993144417490850896153031472 : Int)/10^30,(-3702852686684506484083495536 : Int)/10^30)
theorem v4355_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 78 5) 1) 14) v4355_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4355 : Material (69 : Basis) (78 : Basis) where
  plus := ![v4355_pa,v4355_pb,v4355_pg]
  minus := ![(Primitive.Addresses.material4355 1).one,v4355_mb,v4355_mg]
  upper := v4355_upper
  lower := (Primitive.Addresses.material4355 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4355_pa_checked.trans (by decide +kernel)
    · exact v4355_pb_checked.trans (by decide +kernel)
    · exact v4355_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 78 Primitive.Addresses.material4355
    · exact v4355_mb_checked.trans (by decide +kernel)
    · exact v4355_mg_checked.trans (by decide +kernel)
  upper_error := v4355_upper_checked
  lower_error := reuse_lower_error 69 78 Primitive.Addresses.material4355

def v4356_pa : Scalar.QComplex := ((999998034791825970025304507319 : Int)/10^30,(-1982526793265801519406603490 : Int)/10^30)
theorem v4356_pa_checked : Scalar.distance (sourceCoefficient 69 79 1 0) v4356_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4356_pb : Scalar.QComplex := ((-855415743361796153384074 : Int)/10^30,(-431476671688591877674500556 : Int)/10^30)
theorem v4356_pb_checked : Scalar.distance (sourceCoefficient 69 79 1 1) v4356_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4356_pg : Scalar.QComplex := ((-93086246815099688082220 : Int)/10^30,(184546341067466467537 : Int)/10^30)
theorem v4356_pg_checked : Scalar.distance (sourceCoefficient 69 79 1 2) v4356_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4356_mb : Scalar.QComplex := ((-1227760359530768825417779 : Int)/10^30,(-431475772844847523634801179 : Int)/10^30)
theorem v4356_mb_checked : Scalar.distance (sourceCoefficient 69 79 3 1) v4356_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4356_mg : Scalar.QComplex := ((-93086052899655064611706 : Int)/10^30,(264875510904935002016 : Int)/10^30)
theorem v4356_mg_checked : Scalar.distance (sourceCoefficient 69 79 3 2) v4356_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4356_upper : Scalar.QComplex := ((999993123750829417419365410399 : Int)/10^30,(-3708429729462661037298711001 : Int)/10^30)
theorem v4356_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 79 5) 1) 14) v4356_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4356 : Material (69 : Basis) (79 : Basis) where
  plus := ![v4356_pa,v4356_pb,v4356_pg]
  minus := ![(Primitive.Addresses.material4356 1).one,v4356_mb,v4356_mg]
  upper := v4356_upper
  lower := (Primitive.Addresses.material4356 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4356_pa_checked.trans (by decide +kernel)
    · exact v4356_pb_checked.trans (by decide +kernel)
    · exact v4356_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 79 Primitive.Addresses.material4356
    · exact v4356_mb_checked.trans (by decide +kernel)
    · exact v4356_mg_checked.trans (by decide +kernel)
  upper_error := v4356_upper_checked
  lower_error := reuse_lower_error 69 79 Primitive.Addresses.material4356

def v4357_pa : Scalar.QComplex := ((999998017482198970855701551570 : Int)/10^30,(-1991238727948373647607262678 : Int)/10^30)
theorem v4357_pa_checked : Scalar.distance (sourceCoefficient 69 80 1 0) v4357_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4357_pb : Scalar.QComplex := ((-859174746974718818739242 : Int)/10^30,(-431476664041542442798095924 : Int)/10^30)
theorem v4357_pb_checked : Scalar.distance (sourceCoefficient 69 80 1 1) v4357_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4357_pg : Scalar.QComplex := ((-93086245184571476472622 : Int)/10^30,(185357303924971110764 : Int)/10^30)
theorem v4357_pg_checked : Scalar.distance (sourceCoefficient 69 80 1 2) v4357_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4357_mb : Scalar.QComplex := ((-1231519355144983398752983 : Int)/10^30,(-431475761953950117390171281 : Int)/10^30)
theorem v4357_mb_checked : Scalar.distance (sourceCoefficient 69 80 3 1) v4357_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4357_mg : Scalar.QComplex := ((-93086050569303038507025 : Int)/10^30,(265686472053408700206 : Int)/10^30)
theorem v4357_mg_checked : Scalar.distance (sourceCoefficient 69 80 3 2) v4357_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4357_upper : Scalar.QComplex := ((999993091405219277326954270943 : Int)/10^30,(-3717141621294983948072210717 : Int)/10^30)
theorem v4357_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 80 5) 1) 14) v4357_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4357 : Material (69 : Basis) (80 : Basis) where
  plus := ![v4357_pa,v4357_pb,v4357_pg]
  minus := ![(Primitive.Addresses.material4357 1).one,v4357_mb,v4357_mg]
  upper := v4357_upper
  lower := (Primitive.Addresses.material4357 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4357_pa_checked.trans (by decide +kernel)
    · exact v4357_pb_checked.trans (by decide +kernel)
    · exact v4357_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 80 Primitive.Addresses.material4357
    · exact v4357_mb_checked.trans (by decide +kernel)
    · exact v4357_mg_checked.trans (by decide +kernel)
  upper_error := v4357_upper_checked
  lower_error := reuse_lower_error 69 80 Primitive.Addresses.material4357

def v4358_pa : Scalar.QComplex := ((999997964903685131094136946810 : Int)/10^30,(-2017470814688728262472697932 : Int)/10^30)
theorem v4358_pa_checked : Scalar.distance (sourceCoefficient 69 81 1 0) v4358_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4358_pb : Scalar.QComplex := ((-870493301475210305439726 : Int)/10^30,(-431476640752201829914015001 : Int)/10^30)
theorem v4358_pb_checked : Scalar.distance (sourceCoefficient 69 81 1 1) v4358_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4358_pg : Scalar.QComplex := ((-93086240225191550433251 : Int)/10^30,(187799155092796329893 : Int)/10^30)
theorem v4358_pg_checked : Scalar.distance (sourceCoefficient 69 81 1 2) v4358_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4358_mb : Scalar.QComplex := ((-1242837885333407725470254 : Int)/10^30,(-431475728897215411039018802 : Int)/10^30)
theorem v4358_mb_checked : Scalar.distance (sourceCoefficient 69 81 3 1) v4358_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4358_mg : Scalar.QComplex := ((-93086043502717378132355 : Int)/10^30,(268128318032299617450 : Int)/10^30)
theorem v4358_mg_checked : Scalar.distance (sourceCoefficient 69 81 3 2) v4358_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4358_upper : Scalar.QComplex := ((999992993552581789552831408288 : Int)/10^30,(-3743373578219981798633920060 : Int)/10^30)
theorem v4358_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 81 5) 1) 14) v4358_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4358 : Material (69 : Basis) (81 : Basis) where
  plus := ![v4358_pa,v4358_pb,v4358_pg]
  minus := ![(Primitive.Addresses.material4358 1).one,v4358_mb,v4358_mg]
  upper := v4358_upper
  lower := (Primitive.Addresses.material4358 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4358_pa_checked.trans (by decide +kernel)
    · exact v4358_pb_checked.trans (by decide +kernel)
    · exact v4358_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 81 Primitive.Addresses.material4358
    · exact v4358_mb_checked.trans (by decide +kernel)
    · exact v4358_mg_checked.trans (by decide +kernel)
  upper_error := v4358_upper_checked
  lower_error := reuse_lower_error 69 81 Primitive.Addresses.material4358

def v4359_pa : Scalar.QComplex := ((999997944800098628877154345520 : Int)/10^30,(-2027411053263647148609675050 : Int)/10^30)
theorem v4359_pa_checked : Scalar.distance (sourceCoefficient 69 82 1 0) v4359_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4359_pb : Scalar.QComplex := ((-874782290436697605301730 : Int)/10^30,(-431476631823641831020372574 : Int)/10^30)
theorem v4359_pb_checked : Scalar.distance (sourceCoefficient 69 82 1 1) v4359_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4359_pg : Scalar.QComplex := ((-93086238326387724417771 : Int)/10^30,(188724456356136704809 : Int)/10^30)
theorem v4359_pg_checked : Scalar.distance (sourceCoefficient 69 82 1 2) v4359_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4359_mb : Scalar.QComplex := ((-1247126864992963266861050 : Int)/10^30,(-431475716267454431784838582 : Int)/10^30)
theorem v4359_mb_checked : Scalar.distance (sourceCoefficient 69 82 3 1) v4359_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4359_mg : Scalar.QComplex := ((-93086040805420942887465 : Int)/10^30,(269053617312525860766 : Int)/10^30)
theorem v4359_mg_checked : Scalar.distance (sourceCoefficient 69 82 3 2) v4359_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4359_upper : Scalar.QComplex := ((999992956293075220355678275051 : Int)/10^30,(-3753313767293116470170396683 : Int)/10^30)
theorem v4359_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 82 5) 1) 14) v4359_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4359 : Material (69 : Basis) (82 : Basis) where
  plus := ![v4359_pa,v4359_pb,v4359_pg]
  minus := ![(Primitive.Addresses.material4359 1).one,v4359_mb,v4359_mg]
  upper := v4359_upper
  lower := (Primitive.Addresses.material4359 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4359_pa_checked.trans (by decide +kernel)
    · exact v4359_pb_checked.trans (by decide +kernel)
    · exact v4359_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 82 Primitive.Addresses.material4359
    · exact v4359_mb_checked.trans (by decide +kernel)
    · exact v4359_mg_checked.trans (by decide +kernel)
  upper_error := v4359_upper_checked
  lower_error := reuse_lower_error 69 82 Primitive.Addresses.material4359

def v4360_pa : Scalar.QComplex := ((999997917198873257979771702541 : Int)/10^30,(-2040979646009118558050976155 : Int)/10^30)
theorem v4360_pa_checked : Scalar.distance (sourceCoefficient 69 83 1 0) v4360_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4360_pb : Scalar.QComplex := ((-880636832410023827580070 : Int)/10^30,(-431476619544251245735280384 : Int)/10^30)
theorem v4360_pb_checked : Scalar.distance (sourceCoefficient 69 83 1 1) v4360_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4360_pg : Scalar.QComplex := ((-93086235717167645527971 : Int)/10^30,(189987508128542186573 : Int)/10^30)
theorem v4360_pg_checked : Scalar.distance (sourceCoefficient 69 83 1 2) v4360_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4360_mb : Scalar.QComplex := ((-1252981394189814914804836 : Int)/10^30,(-431475698935862374479789457 : Int)/10^30)
theorem v4360_mb_checked : Scalar.distance (sourceCoefficient 69 83 3 1) v4360_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4360_mg : Scalar.QComplex := ((-93086037106245041683747 : Int)/10^30,(270316666363000030174 : Int)/10^30)
theorem v4360_mg_checked : Scalar.distance (sourceCoefficient 69 83 3 2) v4360_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4360_upper : Scalar.QComplex := ((999992905273730812675912529194 : Int)/10^30,(-3766882292192551837536675378 : Int)/10^30)
theorem v4360_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 83 5) 1) 14) v4360_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4360 : Material (69 : Basis) (83 : Basis) where
  plus := ![v4360_pa,v4360_pb,v4360_pg]
  minus := ![(Primitive.Addresses.material4360 1).one,v4360_mb,v4360_mg]
  upper := v4360_upper
  lower := (Primitive.Addresses.material4360 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4360_pa_checked.trans (by decide +kernel)
    · exact v4360_pb_checked.trans (by decide +kernel)
    · exact v4360_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 83 Primitive.Addresses.material4360
    · exact v4360_mb_checked.trans (by decide +kernel)
    · exact v4360_mg_checked.trans (by decide +kernel)
  upper_error := v4360_upper_checked
  lower_error := reuse_lower_error 69 83 Primitive.Addresses.material4360

def v4361_pa : Scalar.QComplex := ((999997844863397391112868894845 : Int)/10^30,(-2076118628740659982432719203 : Int)/10^30)
theorem v4361_pa_checked : Scalar.distance (sourceCoefficient 69 84 1 0) v4361_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4361_pb : Scalar.QComplex := ((-895798511226703172904326 : Int)/10^30,(-431476587251624825821029305 : Int)/10^30)
theorem v4361_pb_checked : Scalar.distance (sourceCoefficient 69 84 1 1) v4361_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4361_pg : Scalar.QComplex := ((-93086228867056284067723 : Int)/10^30,(193258470328515300702 : Int)/10^30)
theorem v4361_pg_checked : Scalar.distance (sourceCoefficient 69 84 1 2) v4361_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4361_mb : Scalar.QComplex := ((-1268143039494026119244230 : Int)/10^30,(-431475653559402016456997731 : Int)/10^30)
theorem v4361_mb_checked : Scalar.distance (sourceCoefficient 69 84 3 1) v4361_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4361_mg : Scalar.QComplex := ((-93086027433443170924988 : Int)/10^30,(273587621433706839518 : Int)/10^30)
theorem v4361_mg_checked : Scalar.distance (sourceCoefficient 69 84 3 2) v4361_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4361_upper : Scalar.QComplex := ((999992772291666269974499473562 : Int)/10^30,(-3802021097744237075052362613 : Int)/10^30)
theorem v4361_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 84 5) 1) 14) v4361_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4361 : Material (69 : Basis) (84 : Basis) where
  plus := ![v4361_pa,v4361_pb,v4361_pg]
  minus := ![(Primitive.Addresses.material4361 1).one,v4361_mb,v4361_mg]
  upper := v4361_upper
  lower := (Primitive.Addresses.material4361 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4361_pa_checked.trans (by decide +kernel)
    · exact v4361_pb_checked.trans (by decide +kernel)
    · exact v4361_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 84 Primitive.Addresses.material4361
    · exact v4361_mb_checked.trans (by decide +kernel)
    · exact v4361_mg_checked.trans (by decide +kernel)
  upper_error := v4361_upper_checked
  lower_error := reuse_lower_error 69 84 Primitive.Addresses.material4361

def v4362_pa : Scalar.QComplex := ((999997677607082678158598307009 : Int)/10^30,(-2155175269237938424412222529 : Int)/10^30)
theorem v4362_pa_checked : Scalar.distance (sourceCoefficient 69 85 1 0) v4362_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4362_pb : Scalar.QComplex := ((-929909667539131322557634 : Int)/10^30,(-431476512001883425071072146 : Int)/10^30)
theorem v4362_pb_checked : Scalar.distance (sourceCoefficient 69 85 1 1) v4362_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4362_pg : Scalar.QComplex := ((-93086212965266332472112 : Int)/10^30,(200617570002581606904 : Int)/10^30)
theorem v4362_pg_checked : Scalar.distance (sourceCoefficient 69 85 1 2) v4362_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4362_mb : Scalar.QComplex := ((-1302254118168174110618363 : Int)/10^30,(-431475548873297046449178242 : Int)/10^30)
theorem v4362_mb_checked : Scalar.distance (sourceCoefficient 69 85 3 1) v4362_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4362_mg : Scalar.QComplex := ((-93086005181087563118933 : Int)/10^30,(280946704645115471402 : Int)/10^30)
theorem v4362_mg_checked : Scalar.distance (sourceCoefficient 69 85 3 2) v4362_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4362_upper : Scalar.QComplex := ((999992468591011129752713442314 : Int)/10^30,(-3881077331826710321463484581 : Int)/10^30)
theorem v4362_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 85 5) 1) 14) v4362_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4362 : Material (69 : Basis) (85 : Basis) where
  plus := ![v4362_pa,v4362_pb,v4362_pg]
  minus := ![(Primitive.Addresses.material4362 1).one,v4362_mb,v4362_mg]
  upper := v4362_upper
  lower := (Primitive.Addresses.material4362 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4362_pa_checked.trans (by decide +kernel)
    · exact v4362_pb_checked.trans (by decide +kernel)
    · exact v4362_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 85 Primitive.Addresses.material4362
    · exact v4362_mb_checked.trans (by decide +kernel)
    · exact v4362_mg_checked.trans (by decide +kernel)
  upper_error := v4362_upper_checked
  lower_error := reuse_lower_error 69 85 Primitive.Addresses.material4362

def v4363_pa : Scalar.QComplex := ((999997646068262728250235725944 : Int)/10^30,(-2169759879237533462174809572 : Int)/10^30)
theorem v4363_pa_checked : Scalar.distance (sourceCoefficient 69 86 1 0) v4363_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4363_pb : Scalar.QComplex := ((-936202597358384860262688 : Int)/10^30,(-431476497726727629183559132 : Int)/10^30)
theorem v4363_pb_checked : Scalar.distance (sourceCoefficient 69 86 1 1) v4363_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4363_pg : Scalar.QComplex := ((-93086209957495976402420 : Int)/10^30,(201975199111887485887 : Int)/10^30)
theorem v4363_pg_checked : Scalar.distance (sourceCoefficient 69 86 1 2) v4363_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4363_mb : Scalar.QComplex := ((-1308547033325465752814274 : Int)/10^30,(-431475529167631554876673307 : Int)/10^30)
theorem v4363_mb_checked : Scalar.distance (sourceCoefficient 69 86 3 1) v4363_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4363_mg : Scalar.QComplex := ((-93086001001745550993894 : Int)/10^30,(282304330653343633935 : Int)/10^30)
theorem v4363_mg_checked : Scalar.distance (sourceCoefficient 69 86 3 2) v4363_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4363_upper : Scalar.QComplex := ((999992411880524399394451452623 : Int)/10^30,(-3895661865671099939321278189 : Int)/10^30)
theorem v4363_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 86 5) 1) 14) v4363_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4363 : Material (69 : Basis) (86 : Basis) where
  plus := ![v4363_pa,v4363_pb,v4363_pg]
  minus := ![(Primitive.Addresses.material4363 1).one,v4363_mb,v4363_mg]
  upper := v4363_upper
  lower := (Primitive.Addresses.material4363 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4363_pa_checked.trans (by decide +kernel)
    · exact v4363_pb_checked.trans (by decide +kernel)
    · exact v4363_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 86 Primitive.Addresses.material4363
    · exact v4363_mb_checked.trans (by decide +kernel)
    · exact v4363_mg_checked.trans (by decide +kernel)
  upper_error := v4363_upper_checked
  lower_error := reuse_lower_error 69 86 Primitive.Addresses.material4363

def v4364_pa : Scalar.QComplex := ((999997643972336809067921413536 : Int)/10^30,(-2170725633403612441952017764 : Int)/10^30)
theorem v4364_pa_checked : Scalar.distance (sourceCoefficient 69 87 1 0) v4364_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4364_pb : Scalar.QComplex := ((-936619298466316390456205 : Int)/10^30,(-431476496777144770935461826 : Int)/10^30)
theorem v4364_pb_checked : Scalar.distance (sourceCoefficient 69 87 1 1) v4364_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4364_pg : Scalar.QComplex := ((-93086209757513926675116 : Int)/10^30,(202065097707980912802 : Int)/10^30)
theorem v4364_pg_checked : Scalar.distance (sourceCoefficient 69 87 1 2) v4364_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4364_mb : Scalar.QComplex := ((-1308963733458793177299667 : Int)/10^30,(-431475527858454761577979752 : Int)/10^30)
theorem v4364_mb_checked : Scalar.distance (sourceCoefficient 69 87 3 1) v4364_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4364_mg : Scalar.QComplex := ((-93086000724185136182886 : Int)/10^30,(282394229043388202898 : Int)/10^30)
theorem v4364_mg_checked : Scalar.distance (sourceCoefficient 69 87 3 2) v4364_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4364_upper : Scalar.QComplex := ((999992408117797523728825044622 : Int)/10^30,(-3896627614781423538582716504 : Int)/10^30)
theorem v4364_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 87 5) 1) 14) v4364_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4364 : Material (69 : Basis) (87 : Basis) where
  plus := ![v4364_pa,v4364_pb,v4364_pg]
  minus := ![(Primitive.Addresses.material4364 1).one,v4364_mb,v4364_mg]
  upper := v4364_upper
  lower := (Primitive.Addresses.material4364 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4364_pa_checked.trans (by decide +kernel)
    · exact v4364_pb_checked.trans (by decide +kernel)
    · exact v4364_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 87 Primitive.Addresses.material4364
    · exact v4364_mb_checked.trans (by decide +kernel)
    · exact v4364_mg_checked.trans (by decide +kernel)
  upper_error := v4364_upper_checked
  lower_error := reuse_lower_error 69 87 Primitive.Addresses.material4364

def v4365_pa : Scalar.QComplex := ((999997618376341783059739537434 : Int)/10^30,(-2182485199102763936607456022 : Int)/10^30)
theorem v4365_pa_checked : Scalar.distance (sourceCoefficient 69 88 1 0) v4365_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4365_pb : Scalar.QComplex := ((-941693285406567793770480 : Int)/10^30,(-431476485171444346313535466 : Int)/10^30)
theorem v4365_pb_checked : Scalar.distance (sourceCoefficient 69 88 1 1) v4365_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4365_pg : Scalar.QComplex := ((-93086207314294258259926 : Int)/10^30,(203159753554134126939 : Int)/10^30)
theorem v4365_pg_checked : Scalar.distance (sourceCoefficient 69 88 1 2) v4365_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4365_mb : Scalar.QComplex := ((-1314037708494570584994262 : Int)/10^30,(-431475511874136452740350553 : Int)/10^30)
theorem v4365_mb_checked : Scalar.distance (sourceCoefficient 69 88 3 1) v4365_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4365_mg : Scalar.QComplex := ((-93085997336327683728970 : Int)/10^30,(283488882373562481956 : Int)/10^30)
theorem v4365_mg_checked : Scalar.distance (sourceCoefficient 69 88 3 2) v4365_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4365_upper : Scalar.QComplex := ((999992362225897042679728527207 : Int)/10^30,(-3908387118789717935615145078 : Int)/10^30)
theorem v4365_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 88 5) 1) 14) v4365_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4365 : Material (69 : Basis) (88 : Basis) where
  plus := ![v4365_pa,v4365_pb,v4365_pg]
  minus := ![(Primitive.Addresses.material4365 1).one,v4365_mb,v4365_mg]
  upper := v4365_upper
  lower := (Primitive.Addresses.material4365 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4365_pa_checked.trans (by decide +kernel)
    · exact v4365_pb_checked.trans (by decide +kernel)
    · exact v4365_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 88 Primitive.Addresses.material4365
    · exact v4365_mb_checked.trans (by decide +kernel)
    · exact v4365_mg_checked.trans (by decide +kernel)
  upper_error := v4365_upper_checked
  lower_error := reuse_lower_error 69 88 Primitive.Addresses.material4365

def v4366_pa : Scalar.QComplex := ((999997583131844494440278856872 : Int)/10^30,(-2198574645027873131512228588 : Int)/10^30)
theorem v4366_pa_checked : Scalar.distance (sourceCoefficient 69 89 1 0) v4366_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4366_pb : Scalar.QComplex := ((-948635517756274620919403 : Int)/10^30,(-431476469163626679539408125 : Int)/10^30)
theorem v4366_pb_checked : Scalar.distance (sourceCoefficient 69 89 1 1) v4366_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4366_pg : Scalar.QComplex := ((-93086203947148594422257 : Int)/10^30,(204657462430198157870 : Int)/10^30)
theorem v4366_pg_checked : Scalar.distance (sourceCoefficient 69 89 1 2) v4366_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4366_mb : Scalar.QComplex := ((-1320979924445341351573363 : Int)/10^30,(-431475489875490895149645445 : Int)/10^30)
theorem v4366_mb_checked : Scalar.distance (sourceCoefficient 69 89 3 1) v4366_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4366_mg : Scalar.QComplex := ((-93085992676727967894015 : Int)/10^30,(284986587786265992370 : Int)/10^30)
theorem v4366_mg_checked : Scalar.distance (sourceCoefficient 69 89 3 2) v4366_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4366_upper : Scalar.QComplex := ((999992299212528202992775078070 : Int)/10^30,(-3924476479922682459813791007 : Int)/10^30)
theorem v4366_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 89 5) 1) 14) v4366_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4366 : Material (69 : Basis) (89 : Basis) where
  plus := ![v4366_pa,v4366_pb,v4366_pg]
  minus := ![(Primitive.Addresses.material4366 1).one,v4366_mb,v4366_mg]
  upper := v4366_upper
  lower := (Primitive.Addresses.material4366 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4366_pa_checked.trans (by decide +kernel)
    · exact v4366_pb_checked.trans (by decide +kernel)
    · exact v4366_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 89 Primitive.Addresses.material4366
    · exact v4366_mb_checked.trans (by decide +kernel)
    · exact v4366_mg_checked.trans (by decide +kernel)
  upper_error := v4366_upper_checked
  lower_error := reuse_lower_error 69 89 Primitive.Addresses.material4366

def v4367_pa : Scalar.QComplex := ((999997525179425048336879441286 : Int)/10^30,(-2224777522622531359935563099 : Int)/10^30)
theorem v4367_pa_checked : Scalar.distance (sourceCoefficient 69 90 1 0) v4367_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4367_pb : Scalar.QComplex := ((-959941467109651366132166 : Int)/10^30,(-431476442774914999874280653 : Int)/10^30)
theorem v4367_pb_checked : Scalar.distance (sourceCoefficient 69 90 1 1) v4367_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4367_pg : Scalar.QComplex := ((-93086198403322573102669 : Int)/10^30,(207096594401006254467 : Int)/10^30)
theorem v4367_pg_checked : Scalar.distance (sourceCoefficient 69 90 1 2) v4367_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4367_mb : Scalar.QComplex := ((-1332285846816726769016375 : Int)/10^30,(-431475453730263950300213253 : Int)/10^30)
theorem v4367_mb_checked : Scalar.distance (sourceCoefficient 69 90 3 1) v4367_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4367_mg : Scalar.QComplex := ((-93085985028042974412810 : Int)/10^30,(287425714064801610653 : Int)/10^30)
theorem v4367_mg_checked : Scalar.distance (sourceCoefficient 69 90 3 2) v4367_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4367_upper : Scalar.QComplex := ((999992196036405448316919536726 : Int)/10^30,(-3950679218470613955663216116 : Int)/10^30)
theorem v4367_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 90 5) 1) 14) v4367_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4367 : Material (69 : Basis) (90 : Basis) where
  plus := ![v4367_pa,v4367_pb,v4367_pg]
  minus := ![(Primitive.Addresses.material4367 1).one,v4367_mb,v4367_mg]
  upper := v4367_upper
  lower := (Primitive.Addresses.material4367 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4367_pa_checked.trans (by decide +kernel)
    · exact v4367_pb_checked.trans (by decide +kernel)
    · exact v4367_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 90 Primitive.Addresses.material4367
    · exact v4367_mb_checked.trans (by decide +kernel)
    · exact v4367_mg_checked.trans (by decide +kernel)
  upper_error := v4367_upper_checked
  lower_error := reuse_lower_error 69 90 Primitive.Addresses.material4367

def v4368_pa : Scalar.QComplex := ((999997492230381767138622536292 : Int)/10^30,(-2239538556836489167913303477 : Int)/10^30)
theorem v4368_pa_checked : Scalar.distance (sourceCoefficient 69 91 1 0) v4368_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4368_pb : Scalar.QComplex := ((-966310519563347038263220 : Int)/10^30,(-431476427735258396899875381 : Int)/10^30)
theorem v4368_pb_checked : Scalar.distance (sourceCoefficient 69 91 1 1) v4368_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4368_pg : Scalar.QComplex := ((-93086195247449657254377 : Int)/10^30,(208470646162225801100 : Int)/10^30)
theorem v4368_pg_checked : Scalar.distance (sourceCoefficient 69 91 1 2) v4368_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4368_mb : Scalar.QComplex := ((-1338654883920386845181413 : Int)/10^30,(-431475433194407531212029683 : Int)/10^30)
theorem v4368_mb_checked : Scalar.distance (sourceCoefficient 69 91 3 1) v4368_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4368_mg : Scalar.QComplex := ((-93085980686426448701813 : Int)/10^30,(288799762591022698179 : Int)/10^30)
theorem v4368_mg_checked : Scalar.distance (sourceCoefficient 69 91 3 2) v4368_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4368_upper : Scalar.QComplex := ((999992137611205298120319487864 : Int)/10^30,(-3965440173832685665341722463 : Int)/10^30)
theorem v4368_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 91 5) 1) 14) v4368_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4368 : Material (69 : Basis) (91 : Basis) where
  plus := ![v4368_pa,v4368_pb,v4368_pg]
  minus := ![(Primitive.Addresses.material4368 1).one,v4368_mb,v4368_mg]
  upper := v4368_upper
  lower := (Primitive.Addresses.material4368 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4368_pa_checked.trans (by decide +kernel)
    · exact v4368_pb_checked.trans (by decide +kernel)
    · exact v4368_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 91 Primitive.Addresses.material4368
    · exact v4368_mb_checked.trans (by decide +kernel)
    · exact v4368_mg_checked.trans (by decide +kernel)
  upper_error := v4368_upper_checked
  lower_error := reuse_lower_error 69 91 Primitive.Addresses.material4368

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
