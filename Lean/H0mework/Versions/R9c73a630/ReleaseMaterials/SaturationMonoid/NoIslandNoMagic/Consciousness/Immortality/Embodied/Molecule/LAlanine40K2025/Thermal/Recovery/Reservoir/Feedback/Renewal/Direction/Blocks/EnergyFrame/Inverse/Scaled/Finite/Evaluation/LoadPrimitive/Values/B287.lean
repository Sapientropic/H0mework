import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B191
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B192

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4593_pa : Scalar.QComplex := ((999997173723649533738515815339 : Int)/10^30,(-2377508088965106710195927595 : Int)/10^30)
theorem v4593_pa_checked : Scalar.distance (sourceCoefficient 79 91 1 0) v4593_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4593_pb : Scalar.QComplex := ((-1025841285091947167437726 : Int)/10^30,(-431476296775720205600770168 : Int)/10^30)
theorem v4593_pb_checked : Scalar.distance (sourceCoefficient 79 91 1 1) v4593_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4593_pg : Scalar.QComplex := ((-93086166296597472424869 : Int)/10^30,(221313738834697683062 : Int)/10^30)
theorem v4593_pg_checked : Scalar.distance (sourceCoefficient 79 91 1 2) v4593_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4593_mb : Scalar.QComplex := ((-1398185514270779017226184 : Int)/10^30,(-431475250862548617102070421 : Int)/10^30)
theorem v4593_mb_checked : Scalar.distance (sourceCoefficient 79 91 3 1) v4593_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4593_mg : Scalar.QComplex := ((-93085940652574498676043 : Int)/10^30,(301642825498142682321 : Int)/10^30)
theorem v4593_mg_checked : Scalar.distance (sourceCoefficient 79 91 3 2) v4593_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4593_upper : Scalar.QComplex := ((999991580982051487270757493494 : Int)/10^30,(-4103408950758167011961371906 : Int)/10^30)
theorem v4593_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 91 5) 1) 14) v4593_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4593 : Material (79 : Basis) (91 : Basis) where
  plus := ![v4593_pa,v4593_pb,v4593_pg]
  minus := ![(Primitive.Addresses.material4593 1).one,v4593_mb,v4593_mg]
  upper := v4593_upper
  lower := (Primitive.Addresses.material4593 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4593_pa_checked.trans (by decide +kernel)
    · exact v4593_pb_checked.trans (by decide +kernel)
    · exact v4593_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 91 Primitive.Addresses.material4593
    · exact v4593_mb_checked.trans (by decide +kernel)
    · exact v4593_mg_checked.trans (by decide +kernel)
  upper_error := v4593_upper_checked
  lower_error := reuse_lower_error 79 91 Primitive.Addresses.material4593

def v4594_pa : Scalar.QComplex := ((999997097237157407389735416118 : Int)/10^30,(-2409464102067739915394701043 : Int)/10^30)
theorem v4594_pa_checked : Scalar.distance (sourceCoefficient 79 92 1 0) v4594_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4594_pb : Scalar.QComplex := ((-1039629583231595029967298 : Int)/10^30,(-431476262518827350320886899 : Int)/10^30)
theorem v4594_pb_checked : Scalar.distance (sourceCoefficient 79 92 1 1) v4594_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4594_pg : Scalar.QComplex := ((-93086159041400256069850 : Int)/10^30,(224288409665683899088 : Int)/10^30)
theorem v4594_pg_checked : Scalar.distance (sourceCoefficient 79 92 1 2) v4594_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4594_mb : Scalar.QComplex := ((-1411973777714257665083037 : Int)/10^30,(-431475204706988224608444933 : Int)/10^30)
theorem v4594_mb_checked : Scalar.distance (sourceCoefficient 79 92 3 1) v4594_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4594_mg : Scalar.QComplex := ((-93085930830373030822293 : Int)/10^30,(304617488960614563036 : Int)/10^30)
theorem v4594_mg_checked : Scalar.distance (sourceCoefficient 79 92 3 2) v4594_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4594_upper : Scalar.QComplex := ((999991449342493690285068415784 : Int)/10^30,(-4135364784257325908063056490 : Int)/10^30)
theorem v4594_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 92 5) 1) 14) v4594_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4594 : Material (79 : Basis) (92 : Basis) where
  plus := ![v4594_pa,v4594_pb,v4594_pg]
  minus := ![(Primitive.Addresses.material4594 1).one,v4594_mb,v4594_mg]
  upper := v4594_upper
  lower := (Primitive.Addresses.material4594 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4594_pa_checked.trans (by decide +kernel)
    · exact v4594_pb_checked.trans (by decide +kernel)
    · exact v4594_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 92 Primitive.Addresses.material4594
    · exact v4594_mb_checked.trans (by decide +kernel)
    · exact v4594_mg_checked.trans (by decide +kernel)
  upper_error := v4594_upper_checked
  lower_error := reuse_lower_error 79 92 Primitive.Addresses.material4594

def v4595_pa : Scalar.QComplex := ((999997005137583565473509808972 : Int)/10^30,(-2447389601936757352523656523 : Int)/10^30)
theorem v4595_pa_checked : Scalar.distance (sourceCoefficient 79 93 1 0) v4595_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4595_pb : Scalar.QComplex := ((-1055993579559249003210131 : Int)/10^30,(-431476221100269790064153359 : Int)/10^30)
theorem v4595_pb_checked : Scalar.distance (sourceCoefficient 79 93 1 1) v4595_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4595_pg : Scalar.QComplex := ((-93086150286995652367015 : Int)/10^30,(227818758582553298494 : Int)/10^30)
theorem v4595_pg_checked : Scalar.distance (sourceCoefficient 79 93 1 2) v4595_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4595_mb : Scalar.QComplex := ((-1428337732206498182045729 : Int)/10^30,(-431475149167054262643844113 : Int)/10^30)
theorem v4595_mb_checked : Scalar.distance (sourceCoefficient 79 93 3 1) v4595_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4595_mg : Scalar.QComplex := ((-93085919029439572538918 : Int)/10^30,(308147829008316826526 : Int)/10^30)
theorem v4595_mg_checked : Scalar.distance (sourceCoefficient 79 93 3 2) v4595_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4595_upper : Scalar.QComplex := ((999991291787084820413032352966 : Int)/10^30,(-4173290068685257089379027006 : Int)/10^30)
theorem v4595_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 93 5) 1) 14) v4595_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4595 : Material (79 : Basis) (93 : Basis) where
  plus := ![v4595_pa,v4595_pb,v4595_pg]
  minus := ![(Primitive.Addresses.material4595 1).one,v4595_mb,v4595_mg]
  upper := v4595_upper
  lower := (Primitive.Addresses.material4595 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4595_pa_checked.trans (by decide +kernel)
    · exact v4595_pb_checked.trans (by decide +kernel)
    · exact v4595_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 93 Primitive.Addresses.material4595
    · exact v4595_mb_checked.trans (by decide +kernel)
    · exact v4595_mg_checked.trans (by decide +kernel)
  upper_error := v4595_upper_checked
  lower_error := reuse_lower_error 79 93 Primitive.Addresses.material4595

def v4596_pa : Scalar.QComplex := ((999996894494607431123827946179 : Int)/10^30,(-2492188022797238520934988674 : Int)/10^30)
theorem v4596_pa_checked : Scalar.distance (sourceCoefficient 79 94 1 0) v4596_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4596_pb : Scalar.QComplex := ((-1075323085183788568433587 : Int)/10^30,(-431476171109757204307340589 : Int)/10^30)
theorem v4596_pb_checked : Scalar.distance (sourceCoefficient 79 94 1 1) v4596_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4596_pg : Scalar.QComplex := ((-93086139744869970878678 : Int)/10^30,(231988883003322116588 : Int)/10^30)
theorem v4596_pg_checked : Scalar.distance (sourceCoefficient 79 94 1 2) v4596_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4596_mb : Scalar.QComplex := ((-1447667187494218528804645 : Int)/10^30,(-431475082496067505278204673 : Int)/10^30)
theorem v4596_mb_checked : Scalar.distance (sourceCoefficient 79 94 3 1) v4596_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4596_mg : Scalar.QComplex := ((-93085904888688256674155 : Int)/10^30,(312317942778978075258 : Int)/10^30)
theorem v4596_mg_checked : Scalar.distance (sourceCoefficient 79 94 3 2) v4596_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4596_upper : Scalar.QComplex := ((999991103826263151582373303354 : Int)/10^30,(-4218088231864013422779901593 : Int)/10^30)
theorem v4596_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 94 5) 1) 14) v4596_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4596 : Material (79 : Basis) (94 : Basis) where
  plus := ![v4596_pa,v4596_pb,v4596_pg]
  minus := ![(Primitive.Addresses.material4596 1).one,v4596_mb,v4596_mg]
  upper := v4596_upper
  lower := (Primitive.Addresses.material4596 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4596_pa_checked.trans (by decide +kernel)
    · exact v4596_pb_checked.trans (by decide +kernel)
    · exact v4596_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 94 Primitive.Addresses.material4596
    · exact v4596_mb_checked.trans (by decide +kernel)
    · exact v4596_mg_checked.trans (by decide +kernel)
  upper_error := v4596_upper_checked
  lower_error := reuse_lower_error 79 94 Primitive.Addresses.material4596

def v4597_pa : Scalar.QComplex := ((999996783174817111124330484657 : Int)/10^30,(-2536462106520318996382348078 : Int)/10^30)
theorem v4597_pa_checked : Scalar.distance (sourceCoefficient 79 95 1 0) v4597_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4597_pb : Scalar.QComplex := ((-1094426350272338234906161 : Int)/10^30,(-431476120569959202721518761 : Int)/10^30)
theorem v4597_pb_checked : Scalar.distance (sourceCoefficient 79 95 1 1) v4597_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4597_pg : Scalar.QComplex := ((-93086129111992100970458 : Int)/10^30,(236110198660458863419 : Int)/10^30)
theorem v4597_pg_checked : Scalar.distance (sourceCoefficient 79 95 1 2) v4597_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4597_mb : Scalar.QComplex := ((-1466770401856180093101349 : Int)/10^30,(-431475015471030929671413561 : Int)/10^30)
theorem v4597_mb_checked : Scalar.distance (sourceCoefficient 79 95 3 1) v4597_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4597_mg : Scalar.QComplex := ((-93085890699304550930064 : Int)/10^30,(316439247725865934817 : Int)/10^30)
theorem v4597_mg_checked : Scalar.distance (sourceCoefficient 79 95 3 2) v4597_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4597_upper : Scalar.QComplex := ((999990916093586636797191934157 : Int)/10^30,(-4262362057518187752080015722 : Int)/10^30)
theorem v4597_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 95 5) 1) 14) v4597_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4597 : Material (79 : Basis) (95 : Basis) where
  plus := ![v4597_pa,v4597_pb,v4597_pg]
  minus := ![(Primitive.Addresses.material4597 1).one,v4597_mb,v4597_mg]
  upper := v4597_upper
  lower := (Primitive.Addresses.material4597 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4597_pa_checked.trans (by decide +kernel)
    · exact v4597_pb_checked.trans (by decide +kernel)
    · exact v4597_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 95 Primitive.Addresses.material4597
    · exact v4597_mb_checked.trans (by decide +kernel)
    · exact v4597_mg_checked.trans (by decide +kernel)
  upper_error := v4597_upper_checked
  lower_error := reuse_lower_error 79 95 Primitive.Addresses.material4597

def v4598_pa : Scalar.QComplex := ((999996729013161559941244281880 : Int)/10^30,(-2557726134191309439720609482 : Int)/10^30)
theorem v4598_pa_checked : Scalar.distance (sourceCoefficient 79 96 1 0) v4598_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4598_pb : Scalar.QComplex := ((-1103601296616707860390075 : Int)/10^30,(-431476095895748583533325113 : Int)/10^30)
theorem v4598_pb_checked : Scalar.distance (sourceCoefficient 79 96 1 1) v4598_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4598_pg : Scalar.QComplex := ((-93086123929542593608693 : Int)/10^30,(238089590693079647198 : Int)/10^30)
theorem v4598_pg_checked : Scalar.distance (sourceCoefficient 79 96 1 2) v4598_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4598_mb : Scalar.QComplex := ((-1475945323491565399647926 : Int)/10^30,(-431474982879264026872259213 : Int)/10^30)
theorem v4598_mb_checked : Scalar.distance (sourceCoefficient 79 96 3 1) v4598_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4598_mg : Scalar.QComplex := ((-93085883808730797587165 : Int)/10^30,(318418634549248086175 : Int)/10^30)
theorem v4598_mg_checked : Scalar.distance (sourceCoefficient 79 96 3 2) v4598_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4598_upper : Scalar.QComplex := ((999990825232229050429610887413 : Int)/10^30,(-4283625960040802853299895224 : Int)/10^30)
theorem v4598_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 96 5) 1) 14) v4598_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4598 : Material (79 : Basis) (96 : Basis) where
  plus := ![v4598_pa,v4598_pb,v4598_pg]
  minus := ![(Primitive.Addresses.material4598 1).one,v4598_mb,v4598_mg]
  upper := v4598_upper
  lower := (Primitive.Addresses.material4598 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4598_pa_checked.trans (by decide +kernel)
    · exact v4598_pb_checked.trans (by decide +kernel)
    · exact v4598_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 96 Primitive.Addresses.material4598
    · exact v4598_mb_checked.trans (by decide +kernel)
    · exact v4598_mg_checked.trans (by decide +kernel)
  upper_error := v4598_upper_checked
  lower_error := reuse_lower_error 79 96 Primitive.Addresses.material4598

def v4599_pa : Scalar.QComplex := ((999996539207884446489092790069 : Int)/10^30,(-2630888111270594254854088193 : Int)/10^30)
theorem v4599_pa_checked : Scalar.distance (sourceCoefficient 79 97 1 0) v4599_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4599_pb : Scalar.QComplex := ((-1135169030995645992417669 : Int)/10^30,(-431476009013314809502594321 : Int)/10^30)
theorem v4599_pb_checked : Scalar.distance (sourceCoefficient 79 97 1 1) v4599_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4599_pg : Scalar.QComplex := ((-93086105723440061486223 : Int)/10^30,(244899976420183571413 : Int)/10^30)
theorem v4599_pg_checked : Scalar.distance (sourceCoefficient 79 97 1 2) v4599_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4599_mb : Scalar.QComplex := ((-1507512971140765998233888 : Int)/10^30,(-431474868755329592097028296 : Int)/10^30)
theorem v4599_mb_checked : Scalar.distance (sourceCoefficient 79 97 3 1) v4599_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4599_mg : Scalar.QComplex := ((-93085859725578890324898 : Int)/10^30,(325229002029487641383 : Int)/10^30)
theorem v4599_mg_checked : Scalar.distance (sourceCoefficient 79 97 3 2) v4599_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4599_upper : Scalar.QComplex := ((999990509156299393509685295638 : Int)/10^30,(-4356787500567227720790538020 : Int)/10^30)
theorem v4599_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 97 5) 1) 14) v4599_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4599 : Material (79 : Basis) (97 : Basis) where
  plus := ![v4599_pa,v4599_pb,v4599_pg]
  minus := ![(Primitive.Addresses.material4599 1).one,v4599_mb,v4599_mg]
  upper := v4599_upper
  lower := (Primitive.Addresses.material4599 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4599_pa_checked.trans (by decide +kernel)
    · exact v4599_pb_checked.trans (by decide +kernel)
    · exact v4599_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 97 Primitive.Addresses.material4599
    · exact v4599_mb_checked.trans (by decide +kernel)
    · exact v4599_mg_checked.trans (by decide +kernel)
  upper_error := v4599_upper_checked
  lower_error := reuse_lower_error 79 97 Primitive.Addresses.material4599

def v4600_pa : Scalar.QComplex := ((999997658219570322207850535297 : Int)/10^30,(-2164152345704895951196935090 : Int)/10^30)
theorem v4600_pa_checked : Scalar.distance (sourceCoefficient 80 81 1 0) v4600_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4600_pb : Scalar.QComplex := ((-933783089085402718510410 : Int)/10^30,(-431476510525553176310202469 : Int)/10^30)
theorem v4600_pb_checked : Scalar.distance (sourceCoefficient 80 81 1 1) v4600_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4600_pg : Scalar.QComplex := ((-93086211903658335468354 : Int)/10^30,(201453215603282990095 : Int)/10^30)
theorem v4600_pg_checked : Scalar.distance (sourceCoefficient 80 81 1 2) v4600_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4600_mb : Scalar.QComplex := ((-1306127536998187127549961 : Int)/10^30,(-431475544054379005391782535 : Int)/10^30)
theorem v4600_mb_checked : Scalar.distance (sourceCoefficient 80 81 3 1) v4600_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4600_mg : Scalar.QComplex := ((-93086003398355444075795 : Int)/10^30,(281782349018547918196 : Int)/10^30)
theorem v4600_mg_checked : Scalar.distance (sourceCoefficient 80 81 3 2) v4600_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4600_upper : Scalar.QComplex := ((999992433709908061270896905998 : Int)/10^30,(-3890054361462279467203645976 : Int)/10^30)
theorem v4600_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 81 5) 1) 14) v4600_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4600 : Material (80 : Basis) (81 : Basis) where
  plus := ![v4600_pa,v4600_pb,v4600_pg]
  minus := ![(Primitive.Addresses.material4600 1).one,v4600_mb,v4600_mg]
  upper := v4600_upper
  lower := (Primitive.Addresses.material4600 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4600_pa_checked.trans (by decide +kernel)
    · exact v4600_pb_checked.trans (by decide +kernel)
    · exact v4600_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 81 Primitive.Addresses.material4600
    · exact v4600_mb_checked.trans (by decide +kernel)
    · exact v4600_mg_checked.trans (by decide +kernel)
  upper_error := v4600_upper_checked
  lower_error := reuse_lower_error 80 81 Primitive.Addresses.material4600

def v4601_pa : Scalar.QComplex := ((999997636657931440410253780977 : Int)/10^30,(-2174092581224048625247401070 : Int)/10^30)
theorem v4601_pa_checked : Scalar.distance (sourceCoefficient 80 82 1 0) v4601_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4601_pb : Scalar.QComplex := ((-938072077167893738298180 : Int)/10^30,(-431476501177581963066226162 : Int)/10^30)
theorem v4601_pb_checked : Scalar.distance (sourceCoefficient 80 82 1 1) v4601_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4601_pg : Scalar.QComplex := ((-93086209891750434094498 : Int)/10^30,(202378516629581392600 : Int)/10^30)
theorem v4601_pg_checked : Scalar.distance (sourceCoefficient 80 82 1 2) v4601_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4601_mb : Scalar.QComplex := ((-1310416515416813727752554 : Int)/10^30,(-431475531005207726487432759 : Int)/10^30)
theorem v4601_mb_checked : Scalar.distance (sourceCoefficient 80 82 3 1) v4601_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4601_mg : Scalar.QComplex := ((-93086000587955180142891 : Int)/10^30,(282707647964128554347 : Int)/10^30)
theorem v4601_mg_checked : Scalar.distance (sourceCoefficient 80 82 3 2) v4601_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4601_upper : Scalar.QComplex := ((999992394992356558066139257204 : Int)/10^30,(-3899994544963186344180900665 : Int)/10^30)
theorem v4601_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 82 5) 1) 14) v4601_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4601 : Material (80 : Basis) (82 : Basis) where
  plus := ![v4601_pa,v4601_pb,v4601_pg]
  minus := ![(Primitive.Addresses.material4601 1).one,v4601_mb,v4601_mg]
  upper := v4601_upper
  lower := (Primitive.Addresses.material4601 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4601_pa_checked.trans (by decide +kernel)
    · exact v4601_pb_checked.trans (by decide +kernel)
    · exact v4601_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 82 Primitive.Addresses.material4601
    · exact v4601_mb_checked.trans (by decide +kernel)
    · exact v4601_mg_checked.trans (by decide +kernel)
  upper_error := v4601_upper_checked
  lower_error := reuse_lower_error 80 82 Primitive.Addresses.material4601

def v4602_pa : Scalar.QComplex := ((999997607066440063930501674317 : Int)/10^30,(-2187661169774953227398099836 : Int)/10^30)
theorem v4602_pa_checked : Scalar.distance (sourceCoefficient 80 83 1 0) v4602_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4602_pb : Scalar.QComplex := ((-943926617934645778103075 : Int)/10^30,(-431476488325688020731430721 : Int)/10^30)
theorem v4602_pb_checked : Scalar.distance (sourceCoefficient 80 83 1 1) v4602_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4602_pg : Scalar.QComplex := ((-93086207128141391271732 : Int)/10^30,(203641568076605833983 : Int)/10^30)
theorem v4602_pg_checked : Scalar.distance (sourceCoefficient 80 83 1 2) v4602_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4602_mb : Scalar.QComplex := ((-1316271042913047029945744 : Int)/10^30,(-431475513101113566521022300 : Int)/10^30)
theorem v4602_mb_checked : Scalar.distance (sourceCoefficient 80 83 3 1) v4602_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4602_mg : Scalar.QComplex := ((-93085996734390653281458 : Int)/10^30,(283970696555991082074 : Int)/10^30)
theorem v4602_mg_checked : Scalar.distance (sourceCoefficient 80 83 3 2) v4602_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4602_upper : Scalar.QComplex := ((999992341982756348513207549866 : Int)/10^30,(-3913563062233042581457542455 : Int)/10^30)
theorem v4602_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 83 5) 1) 14) v4602_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4602 : Material (80 : Basis) (83 : Basis) where
  plus := ![v4602_pa,v4602_pb,v4602_pg]
  minus := ![(Primitive.Addresses.material4602 1).one,v4602_mb,v4602_mg]
  upper := v4602_upper
  lower := (Primitive.Addresses.material4602 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4602_pa_checked.trans (by decide +kernel)
    · exact v4602_pb_checked.trans (by decide +kernel)
    · exact v4602_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 83 Primitive.Addresses.material4602
    · exact v4602_mb_checked.trans (by decide +kernel)
    · exact v4602_mg_checked.trans (by decide +kernel)
  upper_error := v4602_upper_checked
  lower_error := reuse_lower_error 80 83 Primitive.Addresses.material4602

def v4603_pa : Scalar.QComplex := ((999997529576713937783107959169 : Int)/10^30,(-2222800141518175597949820926 : Int)/10^30)
theorem v4603_pa_checked : Scalar.distance (sourceCoefficient 80 84 1 0) v4603_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4603_pb : Scalar.QComplex := ((-959088293590516706283747 : Int)/10^30,(-431476454550432863571288851 : Int)/10^30)
theorem v4603_pb_checked : Scalar.distance (sourceCoefficient 80 84 1 1) v4603_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4603_pg : Scalar.QComplex := ((-93086199878204401053015 : Int)/10^30,(206912529424192790330 : Int)/10^30)
theorem v4603_pg_checked : Scalar.distance (sourceCoefficient 80 84 1 2) v4603_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4603_mb : Scalar.QComplex := ((-1331432683777009169031297 : Int)/10^30,(-431475466242027750938084608 : Int)/10^30)
theorem v4603_mb_checked : Scalar.distance (sourceCoefficient 80 84 3 1) v4603_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4603_mg : Scalar.QComplex := ((-93085986661764038208448 : Int)/10^30,(287241650429280540878 : Int)/10^30)
theorem v4603_mg_checked : Scalar.distance (sourceCoefficient 80 84 3 2) v4603_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4603_upper : Scalar.QComplex := ((999992203846468188023438411359 : Int)/10^30,(-3948701847900656773366442314 : Int)/10^30)
theorem v4603_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 84 5) 1) 14) v4603_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4603 : Material (80 : Basis) (84 : Basis) where
  plus := ![v4603_pa,v4603_pb,v4603_pg]
  minus := ![(Primitive.Addresses.material4603 1).one,v4603_mb,v4603_mg]
  upper := v4603_upper
  lower := (Primitive.Addresses.material4603 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4603_pa_checked.trans (by decide +kernel)
    · exact v4603_pb_checked.trans (by decide +kernel)
    · exact v4603_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 84 Primitive.Addresses.material4603
    · exact v4603_mb_checked.trans (by decide +kernel)
    · exact v4603_mg_checked.trans (by decide +kernel)
  upper_error := v4603_upper_checked
  lower_error := reuse_lower_error 80 84 Primitive.Addresses.material4603

def v4604_pa : Scalar.QComplex := ((999997350724226643861817426221 : Int)/10^30,(-2301856756631514000470822811 : Int)/10^30)
theorem v4604_pa_checked : Scalar.distance (sourceCoefficient 80 85 1 0) v4604_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4604_pb : Scalar.QComplex := ((-993199442601211917021646 : Int)/10^30,(-431476375965032965116548006 : Int)/10^30)
theorem v4604_pb_checked : Scalar.distance (sourceCoefficient 80 85 1 1) v4604_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4604_pg : Scalar.QComplex := ((-93086183076875863891576 : Int)/10^30,(214271627129175473460 : Int)/10^30)
theorem v4604_pg_checked : Scalar.distance (sourceCoefficient 80 85 1 2) v4604_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4604_mb : Scalar.QComplex := ((-1365543752270903889221516 : Int)/10^30,(-431475358220271826310255693 : Int)/10^30)
theorem v4604_mb_checked : Scalar.distance (sourceCoefficient 80 85 3 1) v4604_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4604_mg : Scalar.QComplex := ((-93085963509871879006374 : Int)/10^30,(294600730895344997240 : Int)/10^30)
theorem v4604_mg_checked : Scalar.distance (sourceCoefficient 80 85 3 2) v4604_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4604_upper : Scalar.QComplex := ((999991888549701548349204719523 : Int)/10^30,(-4027758036585285908525667319 : Int)/10^30)
theorem v4604_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 85 5) 1) 14) v4604_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4604 : Material (80 : Basis) (85 : Basis) where
  plus := ![v4604_pa,v4604_pb,v4604_pg]
  minus := ![(Primitive.Addresses.material4604 1).one,v4604_mb,v4604_mg]
  upper := v4604_upper
  lower := (Primitive.Addresses.material4604 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4604_pa_checked.trans (by decide +kernel)
    · exact v4604_pb_checked.trans (by decide +kernel)
    · exact v4604_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 85 Primitive.Addresses.material4604
    · exact v4604_mb_checked.trans (by decide +kernel)
    · exact v4604_mg_checked.trans (by decide +kernel)
  upper_error := v4604_upper_checked
  lower_error := reuse_lower_error 80 85 Primitive.Addresses.material4604

def v4605_pa : Scalar.QComplex := ((999997317046109439013000012058 : Int)/10^30,(-2316441361848038475755766521 : Int)/10^30)
theorem v4605_pa_checked : Scalar.distance (sourceCoefficient 80 86 1 0) v4605_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4605_pb : Scalar.QComplex := ((-999492371044607185644240 : Int)/10^30,(-431476361074504726009998811 : Int)/10^30)
theorem v4605_pb_checked : Scalar.distance (sourceCoefficient 80 86 1 1) v4605_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4605_pg : Scalar.QComplex := ((-93086179903155888579463 : Int)/10^30,(215629255867448885198 : Int)/10^30)
theorem v4605_pg_checked : Scalar.distance (sourceCoefficient 80 86 1 2) v4605_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4605_mb : Scalar.QComplex := ((-1371836665521299071477853 : Int)/10^30,(-431475337899235307953718960 : Int)/10^30)
theorem v4605_mb_checked : Scalar.distance (sourceCoefficient 80 86 3 1) v4605_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4605_mg : Scalar.QComplex := ((-93085959164580629613851 : Int)/10^30,(295958356389333783367 : Int)/10^30)
theorem v4605_mg_checked : Scalar.distance (sourceCoefficient 80 86 3 2) v4605_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4605_upper : Scalar.QComplex := ((999991829699929004428323686704 : Int)/10^30,(-4042342561954379101231269772 : Int)/10^30)
theorem v4605_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 86 5) 1) 14) v4605_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4605 : Material (80 : Basis) (86 : Basis) where
  plus := ![v4605_pa,v4605_pb,v4605_pg]
  minus := ![(Primitive.Addresses.material4605 1).one,v4605_mb,v4605_mg]
  upper := v4605_upper
  lower := (Primitive.Addresses.material4605 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4605_pa_checked.trans (by decide +kernel)
    · exact v4605_pb_checked.trans (by decide +kernel)
    · exact v4605_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 86 Primitive.Addresses.material4605
    · exact v4605_mb_checked.trans (by decide +kernel)
    · exact v4605_mg_checked.trans (by decide +kernel)
  upper_error := v4605_upper_checked
  lower_error := reuse_lower_error 80 86 Primitive.Addresses.material4605

def v4606_pa : Scalar.QComplex := ((999997314808524933463323563444 : Int)/10^30,(-2317407115696293788108359545 : Int)/10^30)
theorem v4606_pa_checked : Scalar.distance (sourceCoefficient 80 87 1 0) v4606_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4606_pb : Scalar.QComplex := ((-999909072061116204909498 : Int)/10^30,(-431476360084173537832062715 : Int)/10^30)
theorem v4606_pb_checked : Scalar.distance (sourceCoefficient 80 87 1 1) v4606_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4606_pg : Scalar.QComplex := ((-93086179692185095511154 : Int)/10^30,(215719154438888086777 : Int)/10^30)
theorem v4606_pg_checked : Scalar.distance (sourceCoefficient 80 87 1 2) v4606_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4606_mb : Scalar.QComplex := ((-1372253365528040045582967 : Int)/10^30,(-431475336549310278791161552 : Int)/10^30)
theorem v4606_mb_checked : Scalar.distance (sourceCoefficient 80 87 3 1) v4606_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4606_mg : Scalar.QComplex := ((-93085958876031496828934 : Int)/10^30,(296048254745241345586 : Int)/10^30)
theorem v4606_mg_checked : Scalar.distance (sourceCoefficient 80 87 3 2) v4606_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4606_upper : Scalar.QComplex := ((999991825795544301913976387212 : Int)/10^30,(-4043308310502389637525611754 : Int)/10^30)
theorem v4606_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 87 5) 1) 14) v4606_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4606 : Material (80 : Basis) (87 : Basis) where
  plus := ![v4606_pa,v4606_pb,v4606_pg]
  minus := ![(Primitive.Addresses.material4606 1).one,v4606_mb,v4606_mg]
  upper := v4606_upper
  lower := (Primitive.Addresses.material4606 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4606_pa_checked.trans (by decide +kernel)
    · exact v4606_pb_checked.trans (by decide +kernel)
    · exact v4606_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 87 Primitive.Addresses.material4606
    · exact v4606_mb_checked.trans (by decide +kernel)
    · exact v4606_mg_checked.trans (by decide +kernel)
  upper_error := v4606_upper_checked
  lower_error := reuse_lower_error 80 87 Primitive.Addresses.material4606

def v4607_pa : Scalar.QComplex := ((999997287487615316382771933663 : Int)/10^30,(-2329166677514470494647245642 : Int)/10^30)
theorem v4607_pa_checked : Scalar.distance (sourceCoefficient 80 88 1 0) v4607_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4607_pb : Scalar.QComplex := ((-1004983057884998702350870 : Int)/10^30,(-431476347982298538570526697 : Int)/10^30)
theorem v4607_pb_checked : Scalar.distance (sourceCoefficient 80 88 1 1) v4607_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4607_pg : Scalar.QComplex := ((-93086177115160310097379 : Int)/10^30,(216813809983986229380 : Int)/10^30)
theorem v4607_pg_checked : Scalar.distance (sourceCoefficient 80 88 1 2) v4607_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4607_mb : Scalar.QComplex := ((-1377327339019272652039127 : Int)/10^30,(-431475320068818543438479511 : Int)/10^30)
theorem v4607_mb_checked : Scalar.distance (sourceCoefficient 80 88 3 1) v4607_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4607_mg : Scalar.QComplex := ((-93085955354369236995161 : Int)/10^30,(297142907658892875595 : Int)/10^30)
theorem v4607_mg_checked : Scalar.distance (sourceCoefficient 80 88 3 2) v4607_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4607_upper : Scalar.QComplex := ((999991778178738497060575823760 : Int)/10^30,(-4055067807652668925535957292 : Int)/10^30)
theorem v4607_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 88 5) 1) 14) v4607_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4607 : Material (80 : Basis) (88 : Basis) where
  plus := ![v4607_pa,v4607_pb,v4607_pg]
  minus := ![(Primitive.Addresses.material4607 1).one,v4607_mb,v4607_mg]
  upper := v4607_upper
  lower := (Primitive.Addresses.material4607 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4607_pa_checked.trans (by decide +kernel)
    · exact v4607_pb_checked.trans (by decide +kernel)
    · exact v4607_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 88 Primitive.Addresses.material4607
    · exact v4607_mb_checked.trans (by decide +kernel)
    · exact v4607_mg_checked.trans (by decide +kernel)
  upper_error := v4607_upper_checked
  lower_error := reuse_lower_error 80 88 Primitive.Addresses.material4607

def v4608_pa : Scalar.QComplex := ((999997249883088693333831618517 : Int)/10^30,(-2345256118096764816932469932 : Int)/10^30)
theorem v4608_pa_checked : Scalar.distance (sourceCoefficient 80 89 1 0) v4608_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4608_pb : Scalar.QComplex := ((-1011925288697835873071665 : Int)/10^30,(-431476331295614476706077205 : Int)/10^30)
theorem v4608_pb_checked : Scalar.distance (sourceCoefficient 80 89 1 1) v4608_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4608_pg : Scalar.QComplex := ((-93086173564942392881221 : Int)/10^30,(218311518445597294041 : Int)/10^30)
theorem v4608_pg_checked : Scalar.distance (sourceCoefficient 80 89 1 2) v4608_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4608_mb : Scalar.QComplex := ((-1384269552847343210481400 : Int)/10^30,(-431475297391308169779732329 : Int)/10^30)
theorem v4608_mb_checked : Scalar.distance (sourceCoefficient 80 89 3 1) v4608_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4608_mg : Scalar.QComplex := ((-93085950511697693602128 : Int)/10^30,(298640612499160464661 : Int)/10^30)
theorem v4608_mg_checked : Scalar.distance (sourceCoefficient 80 89 3 2) v4608_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4608_upper : Scalar.QComplex := ((999991712805353059144381615221 : Int)/10^30,(-4071157159369630003573675290 : Int)/10^30)
theorem v4608_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 89 5) 1) 14) v4608_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4608 : Material (80 : Basis) (89 : Basis) where
  plus := ![v4608_pa,v4608_pb,v4608_pg]
  minus := ![(Primitive.Addresses.material4608 1).one,v4608_mb,v4608_mg]
  upper := v4608_upper
  lower := (Primitive.Addresses.material4608 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4608_pa_checked.trans (by decide +kernel)
    · exact v4608_pb_checked.trans (by decide +kernel)
    · exact v4608_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 89 Primitive.Addresses.material4608
    · exact v4608_mb_checked.trans (by decide +kernel)
    · exact v4608_mg_checked.trans (by decide +kernel)
  upper_error := v4608_upper_checked
  lower_error := reuse_lower_error 80 89 Primitive.Addresses.material4608

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
