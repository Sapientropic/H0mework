import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B156

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3745_pa : Scalar.QComplex := ((999998585099045845998415979468 : Int)/10^30,(-1682200911414356921295615847 : Int)/10^30)
theorem v3745_pa_checked : Scalar.distance (sourceCoefficient 52 80 1 0) v3745_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3745_pb : Scalar.QComplex := ((-725831853958536488788472 : Int)/10^30,(-431476895567778187601758711 : Int)/10^30)
theorem v3745_pb_checked : Scalar.distance (sourceCoefficient 52 80 1 1) v3745_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3745_pg : Scalar.QComplex := ((-93086296577877120734733 : Int)/10^30,(156590074502937851464 : Int)/10^30)
theorem v3745_pg_checked : Scalar.distance (sourceCoefficient 52 80 1 2) v3745_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3745_mb : Scalar.QComplex := ((-1098176711575168103187598 : Int)/10^30,(-431476108549010786395056310 : Int)/10^30)
theorem v3745_mb_checked : Scalar.distance (sourceCoefficient 52 80 3 1) v3745_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3745_mg : Scalar.QComplex := ((-93086126787412909990157 : Int)/10^30,(236919297692837784499 : Int)/10^30)
theorem v3745_mg_checked : Scalar.distance (sourceCoefficient 52 80 3 2) v3745_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3745_upper : Scalar.QComplex := ((999994192392456399852915566692 : Int)/10^30,(-3408105244691676725557991703 : Int)/10^30)
theorem v3745_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 80 5) 1) 14) v3745_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3745 : Material (52 : Basis) (80 : Basis) where
  plus := ![v3745_pa,v3745_pb,v3745_pg]
  minus := ![(Primitive.Addresses.material3745 1).one,v3745_mb,v3745_mg]
  upper := v3745_upper
  lower := (Primitive.Addresses.material3745 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3745_pa_checked.trans (by decide +kernel)
    · exact v3745_pb_checked.trans (by decide +kernel)
    · exact v3745_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 80 Primitive.Addresses.material3745
    · exact v3745_mb_checked.trans (by decide +kernel)
    · exact v3745_mg_checked.trans (by decide +kernel)
  upper_error := v3745_upper_checked
  lower_error := reuse_lower_error 52 80 Primitive.Addresses.material3745

def v3746_pa : Scalar.QComplex := ((999998540627254903759221307613 : Int)/10^30,(-1708433013150844152127331852 : Int)/10^30)
theorem v3746_pa_checked : Scalar.distance (sourceCoefficient 52 81 1 0) v3746_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3746_pb : Scalar.QComplex := ((-737150412772690654292318 : Int)/10^30,(-431476874610350001513707601 : Int)/10^30)
theorem v3746_pb_checked : Scalar.distance (sourceCoefficient 52 81 1 1) v3746_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3746_pg : Scalar.QComplex := ((-93086292247352100853668 : Int)/10^30,(159031926834043435505 : Int)/10^30)
theorem v3746_pg_checked : Scalar.distance (sourceCoefficient 52 81 1 2) v3746_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3746_mb : Scalar.QComplex := ((-1109495248089588901422470 : Int)/10^30,(-431476077824183916065751833 : Int)/10^30)
theorem v3746_mb_checked : Scalar.distance (sourceCoefficient 52 81 3 1) v3746_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3746_mg : Scalar.QComplex := ((-93086120349680917763810 : Int)/10^30,(239361145377682094953 : Int)/10^30)
theorem v3746_mg_checked : Scalar.distance (sourceCoefficient 52 81 3 2) v3746_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3746_upper : Scalar.QComplex := ((999994102646503853625232709075 : Int)/10^30,(-3434337230604253142075279052 : Int)/10^30)
theorem v3746_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 81 5) 1) 14) v3746_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3746 : Material (52 : Basis) (81 : Basis) where
  plus := ![v3746_pa,v3746_pb,v3746_pg]
  minus := ![(Primitive.Addresses.material3746 1).one,v3746_mb,v3746_mg]
  upper := v3746_upper
  lower := (Primitive.Addresses.material3746 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3746_pa_checked.trans (by decide +kernel)
    · exact v3746_pb_checked.trans (by decide +kernel)
    · exact v3746_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 81 Primitive.Addresses.material3746
    · exact v3746_mb_checked.trans (by decide +kernel)
    · exact v3746_mg_checked.trans (by decide +kernel)
  upper_error := v3746_upper_checked
  lower_error := reuse_lower_error 52 81 Primitive.Addresses.material3746

def v3747_pa : Scalar.QComplex := ((999998523595584131500797834910 : Int)/10^30,(-1718373257463872197910568385 : Int)/10^30)
theorem v3747_pa_checked : Scalar.distance (sourceCoefficient 52 82 1 0) v3747_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3747_pb : Scalar.QComplex := ((-741439403384754668449273 : Int)/10^30,(-431476866565431709259157065 : Int)/10^30)
theorem v3747_pb_checked : Scalar.distance (sourceCoefficient 52 82 1 1) v3747_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3747_pg : Scalar.QComplex := ((-93086290586842996535126 : Int)/10^30,(159957228542500553748 : Int)/10^30)
theorem v3747_pg_checked : Scalar.distance (sourceCoefficient 52 82 1 2) v3747_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3747_mb : Scalar.QComplex := ((-1113784230162263537607503 : Int)/10^30,(-431476066078062890057106482 : Int)/10^30)
theorem v3747_mb_checked : Scalar.distance (sourceCoefficient 52 82 3 1) v3747_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3747_mg : Scalar.QComplex := ((-93086117890678731372139 : Int)/10^30,(240286445308662528288 : Int)/10^30)
theorem v3747_mg_checked : Scalar.distance (sourceCoefficient 52 82 3 2) v3747_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3747_upper : Scalar.QComplex := ((999994068458898535673159148452 : Int)/10^30,(-3444277430717336294908863122 : Int)/10^30)
theorem v3747_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 82 5) 1) 14) v3747_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3747 : Material (52 : Basis) (82 : Basis) where
  plus := ![v3747_pa,v3747_pb,v3747_pg]
  minus := ![(Primitive.Addresses.material3747 1).one,v3747_mb,v3747_mg]
  upper := v3747_upper
  lower := (Primitive.Addresses.material3747 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3747_pa_checked.trans (by decide +kernel)
    · exact v3747_pb_checked.trans (by decide +kernel)
    · exact v3747_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 82 Primitive.Addresses.material3747
    · exact v3747_mb_checked.trans (by decide +kernel)
    · exact v3747_mg_checked.trans (by decide +kernel)
  upper_error := v3747_upper_checked
  lower_error := reuse_lower_error 52 82 Primitive.Addresses.material3747

def v3748_pa : Scalar.QComplex := ((999998500187575377062874899757 : Int)/10^30,(-1731941858091248165000093510 : Int)/10^30)
theorem v3748_pa_checked : Scalar.distance (sourceCoefficient 52 83 1 0) v3748_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3748_pb : Scalar.QComplex := ((-747293947625323941520160 : Int)/10^30,(-431476855492226908366109572 : Int)/10^30)
theorem v3748_pb_checked : Scalar.distance (sourceCoefficient 52 83 1 1) v3748_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3748_pg : Scalar.QComplex := ((-93086288302899218818615 : Int)/10^30,(161220280926321327319 : Int)/10^30)
theorem v3748_pg_checked : Scalar.distance (sourceCoefficient 52 83 1 2) v3748_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3748_mb : Scalar.QComplex := ((-1119638762667241399484859 : Int)/10^30,(-431476049952654211497369113 : Int)/10^30)
theorem v3748_mb_checked : Scalar.distance (sourceCoefficient 52 83 3 1) v3748_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3748_mg : Scalar.QComplex := ((-93086114516778482602618 : Int)/10^30,(241549495251250559857 : Int)/10^30)
theorem v3748_mg_checked : Scalar.distance (sourceCoefficient 52 83 3 2) v3748_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3748_upper : Scalar.QComplex := ((999994021632750895697047014010 : Int)/10^30,(-3457845970735775955121548805 : Int)/10^30)
theorem v3748_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 83 5) 1) 14) v3748_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3748 : Material (52 : Basis) (83 : Basis) where
  plus := ![v3748_pa,v3748_pb,v3748_pg]
  minus := ![(Primitive.Addresses.material3748 1).one,v3748_mb,v3748_mg]
  upper := v3748_upper
  lower := (Primitive.Addresses.material3748 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3748_pa_checked.trans (by decide +kernel)
    · exact v3748_pb_checked.trans (by decide +kernel)
    · exact v3748_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 83 Primitive.Addresses.material3748
    · exact v3748_mb_checked.trans (by decide +kernel)
    · exact v3748_mg_checked.trans (by decide +kernel)
  upper_error := v3748_upper_checked
  lower_error := reuse_lower_error 52 83 Primitive.Addresses.material3748

def v3749_pa : Scalar.QComplex := ((999998438711395650471202508163 : Int)/10^30,(-1767080861499255648390768565 : Int)/10^30)
theorem v3749_pa_checked : Scalar.distance (sourceCoefficient 52 84 1 0) v3749_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3749_pb : Scalar.QComplex := ((-762455632389623378309811 : Int)/10^30,(-431476826323295209740667625 : Int)/10^30)
theorem v3749_pb_checked : Scalar.distance (sourceCoefficient 52 84 1 1) v3749_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3749_pg : Scalar.QComplex := ((-93086282295165440307947 : Int)/10^30,(164491244730209767166 : Int)/10^30)
theorem v3749_pg_checked : Scalar.distance (sourceCoefficient 52 84 1 2) v3749_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3749_mb : Scalar.QComplex := ((-1134800416614678339303374 : Int)/10^30,(-431476007699882279140813813 : Int)/10^30)
theorem v3749_mb_checked : Scalar.distance (sourceCoefficient 52 84 3 1) v3749_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3749_mg : Scalar.QComplex := ((-93086105686352497031078 : Int)/10^30,(244820452652806012516 : Int)/10^30)
theorem v3749_mg_checked : Scalar.distance (sourceCoefficient 52 84 3 2) v3749_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3749_upper : Scalar.QComplex := ((999993899509930633920222465625 : Int)/10^30,(-3492984815706056446943554527 : Int)/10^30)
theorem v3749_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 84 5) 1) 14) v3749_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3749 : Material (52 : Basis) (84 : Basis) where
  plus := ![v3749_pa,v3749_pb,v3749_pg]
  minus := ![(Primitive.Addresses.material3749 1).one,v3749_mb,v3749_mg]
  upper := v3749_upper
  lower := (Primitive.Addresses.material3749 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3749_pa_checked.trans (by decide +kernel)
    · exact v3749_pb_checked.trans (by decide +kernel)
    · exact v3749_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 84 Primitive.Addresses.material3749
    · exact v3749_mb_checked.trans (by decide +kernel)
    · exact v3749_mg_checked.trans (by decide +kernel)
  upper_error := v3749_upper_checked
  lower_error := reuse_lower_error 52 84 Primitive.Addresses.material3749

def v3750_pa : Scalar.QComplex := ((999998295886621404934982638619 : Int)/10^30,(-1846137549910006821546765240 : Int)/10^30)
theorem v3750_pa_checked : Scalar.distance (sourceCoefficient 52 85 1 0) v3750_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3750_pb : Scalar.QComplex := ((-796566802484442143256783 : Int)/10^30,(-431476758101327308854363215 : Int)/10^30)
theorem v3750_pb_checked : Scalar.distance (sourceCoefficient 52 85 1 1) v3750_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3750_pg : Scalar.QComplex := ((-93086268288579531803294 : Int)/10^30,(171850348121021129921 : Int)/10^30)
theorem v3750_pg_checked : Scalar.distance (sourceCoefficient 52 85 1 2) v3750_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3750_mb : Scalar.QComplex := ((-1168911515135863825370900 : Int)/10^30,(-431475910041536298653022788 : Int)/10^30)
theorem v3750_mb_checked : Scalar.distance (sourceCoefficient 52 85 3 1) v3750_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3750_mg : Scalar.QComplex := ((-93086085329197019261313 : Int)/10^30,(252179541216434049404 : Int)/10^30)
theorem v3750_mg_checked : Scalar.distance (sourceCoefficient 52 85 3 2) v3750_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3750_upper : Scalar.QComplex := ((999993620240696878899633559570 : Int)/10^30,(-3572041139868553497767860697 : Int)/10^30)
theorem v3750_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 85 5) 1) 14) v3750_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3750 : Material (52 : Basis) (85 : Basis) where
  plus := ![v3750_pa,v3750_pb,v3750_pg]
  minus := ![(Primitive.Addresses.material3750 1).one,v3750_mb,v3750_mg]
  upper := v3750_upper
  lower := (Primitive.Addresses.material3750 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3750_pa_checked.trans (by decide +kernel)
    · exact v3750_pb_checked.trans (by decide +kernel)
    · exact v3750_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 85 Primitive.Addresses.material3750
    · exact v3750_mb_checked.trans (by decide +kernel)
    · exact v3750_mg_checked.trans (by decide +kernel)
  upper_error := v3750_upper_checked
  lower_error := reuse_lower_error 52 85 Primitive.Addresses.material3750

def v3751_pa : Scalar.QComplex := ((999998268855006539168725208785 : Int)/10^30,(-1860722168959856877504440784 : Int)/10^30)
theorem v3751_pa_checked : Scalar.distance (sourceCoefficient 52 86 1 0) v3751_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3751_pb : Scalar.QComplex := ((-802859734907016672048586 : Int)/10^30,(-431476745122676592514937136 : Int)/10^30)
theorem v3751_pb_checked : Scalar.distance (sourceCoefficient 52 86 1 1) v3751_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3751_pg : Scalar.QComplex := ((-93086265630442195747456 : Int)/10^30,(173207977932373606639 : Int)/10^30)
theorem v3751_pg_checked : Scalar.distance (sourceCoefficient 52 86 1 2) v3751_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3751_mb : Scalar.QComplex := ((-1175204434015300980547021 : Int)/10^30,(-431475891632373157331744382 : Int)/10^30)
theorem v3751_mb_checked : Scalar.distance (sourceCoefficient 52 86 3 1) v3751_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3751_mg : Scalar.QComplex := ((-93086081499487291131181 : Int)/10^30,(253537168228426097653 : Int)/10^30)
theorem v3751_mg_checked : Scalar.distance (sourceCoefficient 52 86 3 2) v3751_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3751_upper : Scalar.QComplex := ((999993568037392899811828709680 : Int)/10^30,(-3586625690542211739307127875 : Int)/10^30)
theorem v3751_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 86 5) 1) 14) v3751_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3751 : Material (52 : Basis) (86 : Basis) where
  plus := ![v3751_pa,v3751_pb,v3751_pg]
  minus := ![(Primitive.Addresses.material3751 1).one,v3751_mb,v3751_mg]
  upper := v3751_upper
  lower := (Primitive.Addresses.material3751 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3751_pa_checked.trans (by decide +kernel)
    · exact v3751_pb_checked.trans (by decide +kernel)
    · exact v3751_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 86 Primitive.Addresses.material3751
    · exact v3751_mb_checked.trans (by decide +kernel)
    · exact v3751_mg_checked.trans (by decide +kernel)
  upper_error := v3751_upper_checked
  lower_error := reuse_lower_error 52 86 Primitive.Addresses.material3751

def v3752_pa : Scalar.QComplex := ((999998267057535778727925079385 : Int)/10^30,(-1861687923727540283618488564 : Int)/10^30)
theorem v3752_pa_checked : Scalar.distance (sourceCoefficient 52 87 1 0) v3752_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3752_pb : Scalar.QComplex := ((-803276436188000721438087 : Int)/10^30,(-431476744258944859701800511 : Int)/10^30)
theorem v3752_pb_checked : Scalar.distance (sourceCoefficient 52 87 1 1) v3752_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3752_pg : Scalar.QComplex := ((-93086265453611916684057 : Int)/10^30,(173297876575134706416 : Int)/10^30)
theorem v3752_pg_checked : Scalar.distance (sourceCoefficient 52 87 1 2) v3752_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3752_mb : Scalar.QComplex := ((-1175621134395766514452253 : Int)/10^30,(-431475890409047308165183847 : Int)/10^30)
theorem v3752_mb_checked : Scalar.distance (sourceCoefficient 52 87 3 1) v3752_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3752_mg : Scalar.QComplex := ((-93086081245078598091515 : Int)/10^30,(253627066685117257468 : Int)/10^30)
theorem v3752_mg_checked : Scalar.distance (sourceCoefficient 52 87 3 2) v3752_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3752_upper : Scalar.QComplex := ((999993564573119700059153814748 : Int)/10^30,(-3587591440769245397233637916 : Int)/10^30)
theorem v3752_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 87 5) 1) 14) v3752_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3752 : Material (52 : Basis) (87 : Basis) where
  plus := ![v3752_pa,v3752_pb,v3752_pg]
  minus := ![(Primitive.Addresses.material3752 1).one,v3752_mb,v3752_mg]
  upper := v3752_upper
  lower := (Primitive.Addresses.material3752 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3752_pa_checked.trans (by decide +kernel)
    · exact v3752_pb_checked.trans (by decide +kernel)
    · exact v3752_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 87 Primitive.Addresses.material3752
    · exact v3752_mb_checked.trans (by decide +kernel)
    · exact v3752_mg_checked.trans (by decide +kernel)
  upper_error := v3752_upper_checked
  lower_error := reuse_lower_error 52 87 Primitive.Addresses.material3752

def v3753_pa : Scalar.QComplex := ((999998245095698568648955307818 : Int)/10^30,(-1873447496775288578069946581 : Int)/10^30)
theorem v3753_pa_checked : Scalar.distance (sourceCoefficient 52 88 1 0) v3753_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3753_pb : Scalar.QComplex := ((-808350425242088280719528 : Int)/10^30,(-431476733698616006571860868 : Int)/10^30)
theorem v3753_pb_checked : Scalar.distance (sourceCoefficient 52 88 1 1) v3753_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3753_pg : Scalar.QComplex := ((-93086263292301224593817 : Int)/10^30,(174392532991333445999 : Int)/10^30)
theorem v3753_pg_checked : Scalar.distance (sourceCoefficient 52 88 1 2) v3753_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3753_mb : Scalar.QComplex := ((-1180695112447487875445968 : Int)/10^30,(-431475875470098357434530504 : Int)/10^30)
theorem v3753_mb_checked : Scalar.distance (sourceCoefficient 52 88 3 1) v3753_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3753_mg : Scalar.QComplex := ((-93086078139129525071339 : Int)/10^30,(254721720828611599576 : Int)/10^30)
theorem v3753_mg_checked : Scalar.distance (sourceCoefficient 52 88 3 2) v3753_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3753_upper : Scalar.QComplex := ((999993522315358939276683786414 : Int)/10^30,(-3599350958398352351262521822 : Int)/10^30)
theorem v3753_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 88 5) 1) 14) v3753_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3753 : Material (52 : Basis) (88 : Basis) where
  plus := ![v3753_pa,v3753_pb,v3753_pg]
  minus := ![(Primitive.Addresses.material3753 1).one,v3753_mb,v3753_mg]
  upper := v3753_upper
  lower := (Primitive.Addresses.material3753 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3753_pa_checked.trans (by decide +kernel)
    · exact v3753_pb_checked.trans (by decide +kernel)
    · exact v3753_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 88 Primitive.Addresses.material3753
    · exact v3753_mb_checked.trans (by decide +kernel)
    · exact v3753_mg_checked.trans (by decide +kernel)
  upper_error := v3753_upper_checked
  lower_error := reuse_lower_error 52 88 Primitive.Addresses.material3753

def v3754_pa : Scalar.QComplex := ((999998214823458528673760662999 : Int)/10^30,(-1889536952823989695246052528 : Int)/10^30)
theorem v3754_pa_checked : Scalar.distance (sourceCoefficient 52 89 1 0) v3754_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3754_pb : Scalar.QComplex := ((-815292660503863246493288 : Int)/10^30,(-431476719121076448234611950 : Int)/10^30)
theorem v3754_pb_checked : Scalar.distance (sourceCoefficient 52 89 1 1) v3754_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3754_pg : Scalar.QComplex := ((-93086260310863617706455 : Int)/10^30,(175890242652704989262 : Int)/10^30)
theorem v3754_pg_checked : Scalar.distance (sourceCoefficient 52 89 1 2) v3754_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3754_mb : Scalar.QComplex := ((-1187637332544591286600156 : Int)/10^30,(-431475854901727862739148158 : Int)/10^30)
theorem v3754_mb_checked : Scalar.distance (sourceCoefficient 52 89 3 1) v3754_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3754_mg : Scalar.QComplex := ((-93086073865237044884940 : Int)/10^30,(256219427359471011419 : Int)/10^30)
theorem v3754_mg_checked : Scalar.distance (sourceCoefficient 52 89 3 2) v3754_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3754_upper : Scalar.QComplex := ((999993464274222470239654128041 : Int)/10^30,(-3615440338236558651337580607 : Int)/10^30)
theorem v3754_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 89 5) 1) 14) v3754_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3754 : Material (52 : Basis) (89 : Basis) where
  plus := ![v3754_pa,v3754_pb,v3754_pg]
  minus := ![(Primitive.Addresses.material3754 1).one,v3754_mb,v3754_mg]
  upper := v3754_upper
  lower := (Primitive.Addresses.material3754 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3754_pa_checked.trans (by decide +kernel)
    · exact v3754_pb_checked.trans (by decide +kernel)
    · exact v3754_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 89 Primitive.Addresses.material3754
    · exact v3754_mb_checked.trans (by decide +kernel)
    · exact v3754_mg_checked.trans (by decide +kernel)
  upper_error := v3754_upper_checked
  lower_error := reuse_lower_error 52 89 Primitive.Addresses.material3754

def v3755_pa : Scalar.QComplex := ((999998164968735490982208009760 : Int)/10^30,(-1915739847076918181211100321 : Int)/10^30)
theorem v3755_pa_checked : Scalar.distance (sourceCoefficient 52 90 1 0) v3755_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3755_pb : Scalar.QComplex := ((-826598614649019266249456 : Int)/10^30,(-431476695061680670276412744 : Int)/10^30)
theorem v3755_pb_checked : Scalar.distance (sourceCoefficient 52 90 1 1) v3755_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3755_pg : Scalar.QComplex := ((-93086255395192292979932 : Int)/10^30,(178329375915728819094 : Int)/10^30)
theorem v3755_pg_checked : Scalar.distance (sourceCoefficient 52 90 1 2) v3755_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3755_mb : Scalar.QComplex := ((-1198943261717848909067406 : Int)/10^30,(-431475821085811817196178827 : Int)/10^30)
theorem v3755_mb_checked : Scalar.distance (sourceCoefficient 52 90 3 1) v3755_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3755_mg : Scalar.QComplex := ((-93086066844705398982120 : Int)/10^30,(258658555472291093909 : Int)/10^30)
theorem v3755_mg_checked : Scalar.distance (sourceCoefficient 52 90 3 2) v3755_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3755_upper : Scalar.QComplex := ((999993369195755312744829215161 : Int)/10^30,(-3641643107418624977831179930 : Int)/10^30)
theorem v3755_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 90 5) 1) 14) v3755_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3755 : Material (52 : Basis) (90 : Basis) where
  plus := ![v3755_pa,v3755_pb,v3755_pg]
  minus := ![(Primitive.Addresses.material3755 1).one,v3755_mb,v3755_mg]
  upper := v3755_upper
  lower := (Primitive.Addresses.material3755 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3755_pa_checked.trans (by decide +kernel)
    · exact v3755_pb_checked.trans (by decide +kernel)
    · exact v3755_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 90 Primitive.Addresses.material3755
    · exact v3755_mb_checked.trans (by decide +kernel)
    · exact v3755_mg_checked.trans (by decide +kernel)
  upper_error := v3755_upper_checked
  lower_error := reuse_lower_error 52 90 Primitive.Addresses.material3755

def v3756_pa : Scalar.QComplex := ((999998136581419206572929149603 : Int)/10^30,(-1930500890768519406100942230 : Int)/10^30)
theorem v3756_pa_checked : Scalar.distance (sourceCoefficient 52 91 1 0) v3756_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3756_pb : Scalar.QComplex := ((-832967669828974897931840 : Int)/10^30,(-431476681334212456918431990 : Int)/10^30)
theorem v3756_pb_checked : Scalar.distance (sourceCoefficient 52 91 1 1) v3756_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3756_pg : Scalar.QComplex := ((-93086252593181770749224 : Int)/10^30,(179703428412148343401 : Int)/10^30)
theorem v3756_pg_checked : Scalar.distance (sourceCoefficient 52 91 1 2) v3756_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3756_mb : Scalar.QComplex := ((-1205312302680127411140351 : Int)/10^30,(-431475801862140946497153446 : Int)/10^30)
theorem v3756_mb_checked : Scalar.distance (sourceCoefficient 52 91 3 1) v3756_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3756_mg : Scalar.QComplex := ((-93086062856950500685096 : Int)/10^30,(260032605039079193682 : Int)/10^30)
theorem v3756_mg_checked : Scalar.distance (sourceCoefficient 52 91 3 2) v3756_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3756_upper : Scalar.QComplex := ((999993315332259007627971093040 : Int)/10^30,(-3656404080131452948402582358 : Int)/10^30)
theorem v3756_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 91 5) 1) 14) v3756_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3756 : Material (52 : Basis) (91 : Basis) where
  plus := ![v3756_pa,v3756_pb,v3756_pg]
  minus := ![(Primitive.Addresses.material3756 1).one,v3756_mb,v3756_mg]
  upper := v3756_upper
  lower := (Primitive.Addresses.material3756 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3756_pa_checked.trans (by decide +kernel)
    · exact v3756_pb_checked.trans (by decide +kernel)
    · exact v3756_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 91 Primitive.Addresses.material3756
    · exact v3756_mb_checked.trans (by decide +kernel)
    · exact v3756_mg_checked.trans (by decide +kernel)
  upper_error := v3756_upper_checked
  lower_error := reuse_lower_error 52 91 Primitive.Addresses.material3756

def v3757_pa : Scalar.QComplex := ((999998074379535386029029886420 : Int)/10^30,(-1962456934868576472758232013 : Int)/10^30)
theorem v3757_pa_checked : Scalar.distance (sourceCoefficient 52 92 1 0) v3757_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3757_pb : Scalar.QComplex := ((-846755976885083547266554 : Int)/10^30,(-431476651186311054808691466 : Int)/10^30)
theorem v3757_pb_checked : Scalar.distance (sourceCoefficient 52 92 1 1) v3757_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3757_pg : Scalar.QComplex := ((-93086246446070527591503 : Int)/10^30,(182678101647667457105 : Int)/10^30)
theorem v3757_pg_checked : Scalar.distance (sourceCoefficient 52 92 1 2) v3757_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3757_mb : Scalar.QComplex := ((-1219100578585938087777104 : Int)/10^30,(-431475759815562782704285975 : Int)/10^30)
theorem v3757_mb_checked : Scalar.distance (sourceCoefficient 52 92 3 1) v3757_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3757_mg : Scalar.QComplex := ((-93086054142832518434001 : Int)/10^30,(263007271862311365288 : Int)/10^30)
theorem v3757_mg_checked : Scalar.distance (sourceCoefficient 52 92 3 2) v3757_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3757_upper : Scalar.QComplex := ((999993197977234742459559067495 : Int)/10^30,(-3688359969281927585217810621 : Int)/10^30)
theorem v3757_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 92 5) 1) 14) v3757_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3757 : Material (52 : Basis) (92 : Basis) where
  plus := ![v3757_pa,v3757_pb,v3757_pg]
  minus := ![(Primitive.Addresses.material3757 1).one,v3757_mb,v3757_mg]
  upper := v3757_upper
  lower := (Primitive.Addresses.material3757 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3757_pa_checked.trans (by decide +kernel)
    · exact v3757_pb_checked.trans (by decide +kernel)
    · exact v3757_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 92 Primitive.Addresses.material3757
    · exact v3757_mb_checked.trans (by decide +kernel)
    · exact v3757_mg_checked.trans (by decide +kernel)
  upper_error := v3757_upper_checked
  lower_error := reuse_lower_error 52 92 Primitive.Addresses.material3757

def v3758_pa : Scalar.QComplex := ((999997999232981087621300914780 : Int)/10^30,(-2000382472117793135369419703 : Int)/10^30)
theorem v3758_pa_checked : Scalar.distance (sourceCoefficient 52 93 1 0) v3758_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3758_pb : Scalar.QComplex := ((-863119983965214271523174 : Int)/10^30,(-431476614644317882457317931 : Int)/10^30)
theorem v3758_pb_checked : Scalar.distance (sourceCoefficient 52 93 1 1) v3758_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3758_pg : Scalar.QComplex := ((-93086239006745953863711 : Int)/10^30,(186208453464194549659 : Int)/10^30)
theorem v3758_pg_checked : Scalar.distance (sourceCoefficient 52 93 1 2) v3758_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3758_mb : Scalar.QComplex := ((-1235464548038906786570504 : Int)/10^30,(-431475709152182113974090992 : Int)/10^30)
theorem v3758_mb_checked : Scalar.distance (sourceCoefficient 52 93 3 1) v3758_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3758_mg : Scalar.QComplex := ((-93086043656976098187276 : Int)/10^30,(266537615944525079114 : Int)/10^30)
theorem v3758_mg_checked : Scalar.distance (sourceCoefficient 52 93 3 2) v3758_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3758_upper : Scalar.QComplex := ((999993057374755651732093152541 : Int)/10^30,(-3726285320349376084776862199 : Int)/10^30)
theorem v3758_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 93 5) 1) 14) v3758_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3758 : Material (52 : Basis) (93 : Basis) where
  plus := ![v3758_pa,v3758_pb,v3758_pg]
  minus := ![(Primitive.Addresses.material3758 1).one,v3758_mb,v3758_mg]
  upper := v3758_upper
  lower := (Primitive.Addresses.material3758 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3758_pa_checked.trans (by decide +kernel)
    · exact v3758_pb_checked.trans (by decide +kernel)
    · exact v3758_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 93 Primitive.Addresses.material3758
    · exact v3758_mb_checked.trans (by decide +kernel)
    · exact v3758_mg_checked.trans (by decide +kernel)
  upper_error := v3758_upper_checked
  lower_error := reuse_lower_error 52 93 Primitive.Addresses.material3758

def v3759_pa : Scalar.QComplex := ((999997908615278555730011764643 : Int)/10^30,(-2045180937960865819966489988 : Int)/10^30)
theorem v3759_pa_checked : Scalar.distance (sourceCoefficient 52 94 1 0) v3759_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3759_pb : Scalar.QComplex := ((-882449502529071371421504 : Int)/10^30,(-431476570414108669837297600 : Int)/10^30)
theorem v3759_pb_checked : Scalar.distance (sourceCoefficient 52 94 1 1) v3759_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3759_pg : Scalar.QComplex := ((-93086230018021262066344 : Int)/10^30,(190378581374354004931 : Int)/10^30)
theorem v3759_pg_checked : Scalar.distance (sourceCoefficient 52 94 1 2) v3759_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3759_mb : Scalar.QComplex := ((-1254794021236822226688805 : Int)/10^30,(-431475648241485418872772107 : Int)/10^30)
theorem v3759_mb_checked : Scalar.distance (sourceCoefficient 52 94 3 1) v3759_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3759_mg : Scalar.QComplex := ((-93086031069622182424339 : Int)/10^30,(270707734545090757284 : Int)/10^30)
theorem v3759_mg_checked : Scalar.distance (sourceCoefficient 52 94 3 2) v3759_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3759_upper : Scalar.QComplex := ((999992889439100124194961721989 : Int)/10^30,(-3771083563072462497290523412 : Int)/10^30)
theorem v3759_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 94 5) 1) 14) v3759_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3759 : Material (52 : Basis) (94 : Basis) where
  plus := ![v3759_pa,v3759_pb,v3759_pg]
  minus := ![(Primitive.Addresses.material3759 1).one,v3759_mb,v3759_mg]
  upper := v3759_upper
  lower := (Primitive.Addresses.material3759 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3759_pa_checked.trans (by decide +kernel)
    · exact v3759_pb_checked.trans (by decide +kernel)
    · exact v3759_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 94 Primitive.Addresses.material3759
    · exact v3759_mb_checked.trans (by decide +kernel)
    · exact v3759_mg_checked.trans (by decide +kernel)
  upper_error := v3759_upper_checked
  lower_error := reuse_lower_error 52 94 Primitive.Addresses.material3759

def v3760_pa : Scalar.QComplex := ((999997817086378893224228831146 : Int)/10^30,(-2089455067021464888443335959 : Int)/10^30)
theorem v3760_pa_checked : Scalar.distance (sourceCoefficient 52 95 1 0) v3760_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3760_pb : Scalar.QComplex := ((-901552780659033870173779 : Int)/10^30,(-431476525567193365920883868 : Int)/10^30)
theorem v3760_pb_checked : Scalar.distance (sourceCoefficient 52 95 1 1) v3760_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3760_pg : Scalar.QComplex := ((-93086220920362817708372 : Int)/10^30,(194499900548413789333 : Int)/10^30)
theorem v3760_pg_checked : Scalar.distance (sourceCoefficient 52 95 1 2) v3760_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3760_mb : Scalar.QComplex := ((-1273897253552893137521124 : Int)/10^30,(-431475586909318167063072329 : Int)/10^30)
theorem v3760_mb_checked : Scalar.distance (sourceCoefficient 52 95 3 1) v3760_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3760_mg : Scalar.QComplex := ((-93086018415454295651956 : Int)/10^30,(274829044333725565437 : Int)/10^30)
theorem v3760_mg_checked : Scalar.distance (sourceCoefficient 52 95 3 2) v3760_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3760_upper : Scalar.QComplex := ((999992721497206542252557857913 : Int)/10^30,(-3815357468221369753970619087 : Int)/10^30)
theorem v3760_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 95 5) 1) 14) v3760_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3760 : Material (52 : Basis) (95 : Basis) where
  plus := ![v3760_pa,v3760_pb,v3760_pg]
  minus := ![(Primitive.Addresses.material3760 1).one,v3760_mb,v3760_mg]
  upper := v3760_upper
  lower := (Primitive.Addresses.material3760 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3760_pa_checked.trans (by decide +kernel)
    · exact v3760_pb_checked.trans (by decide +kernel)
    · exact v3760_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 95 Primitive.Addresses.material3760
    · exact v3760_mb_checked.trans (by decide +kernel)
    · exact v3760_mg_checked.trans (by decide +kernel)
  upper_error := v3760_upper_checked
  lower_error := reuse_lower_error 52 95 Primitive.Addresses.material3760

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
