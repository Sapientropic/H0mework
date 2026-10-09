import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B152

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3649_pa : Scalar.QComplex := ((999998720293021685616382212585 : Int)/10^30,(-1599816339139845417601079544 : Int)/10^30)
theorem v3649_pa_checked : Scalar.distance (sourceCoefficient 50 75 1 0) v3649_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3649_pb : Scalar.QComplex := ((-690284765356530090475056 : Int)/10^30,(-431476954639327986454475298 : Int)/10^30)
theorem v3649_pb_checked : Scalar.distance (sourceCoefficient 50 75 1 1) v3649_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3649_pg : Scalar.QComplex := ((-93086309242251161567906 : Int)/10^30,(148921189051462659239 : Int)/10^30)
theorem v3649_pg_checked : Scalar.distance (sourceCoefficient 50 75 1 2) v3649_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3649_mb : Scalar.QComplex := ((-1062629687185054366175021 : Int)/10^30,(-431476198296075072302191587 : Int)/10^30)
theorem v3649_mb_checked : Scalar.distance (sourceCoefficient 50 75 3 1) v3649_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3649_mg : Scalar.QComplex := ((-93086146069684986142061 : Int)/10^30,(229250426025623546244 : Int)/10^30)
theorem v3649_mg_checked : Scalar.distance (sourceCoefficient 50 75 3 2) v3649_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3649_upper : Scalar.QComplex := ((999994469774528759717648966555 : Int)/10^30,(-3325721028451845650575675471 : Int)/10^30)
theorem v3649_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 75 5) 1) 14) v3649_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3649 : Material (50 : Basis) (75 : Basis) where
  plus := ![v3649_pa,v3649_pb,v3649_pg]
  minus := ![(Primitive.Addresses.material3649 1).one,v3649_mb,v3649_mg]
  upper := v3649_upper
  lower := (Primitive.Addresses.material3649 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3649_pa_checked.trans (by decide +kernel)
    · exact v3649_pb_checked.trans (by decide +kernel)
    · exact v3649_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 75 Primitive.Addresses.material3649
    · exact v3649_mb_checked.trans (by decide +kernel)
    · exact v3649_mg_checked.trans (by decide +kernel)
  upper_error := v3649_upper_checked
  lower_error := reuse_lower_error 50 75 Primitive.Addresses.material3649

def v3650_pa : Scalar.QComplex := ((999998700329754025066661479349 : Int)/10^30,(-1612246508077197977870148057 : Int)/10^30)
theorem v3650_pa_checked : Scalar.distance (sourceCoefficient 50 76 1 0) v3650_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3650_pb : Scalar.QComplex := ((-695648102360198678908834 : Int)/10^30,(-431476945220184173452230844 : Int)/10^30)
theorem v3650_pb_checked : Scalar.distance (sourceCoefficient 50 76 1 1) v3650_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3650_pg : Scalar.QComplex := ((-93086307297059251104205 : Int)/10^30,(150078268941745481963 : Int)/10^30)
theorem v3650_pg_checked : Scalar.distance (sourceCoefficient 50 76 1 2) v3650_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3650_mb : Scalar.QComplex := ((-1067993014063410583401432 : Int)/10^30,(-431476184248616488043348011 : Int)/10^30)
theorem v3650_mb_checked : Scalar.distance (sourceCoefficient 50 76 3 1) v3650_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3650_mg : Scalar.QComplex := ((-93086143125985967591866 : Int)/10^30,(230407503806459634113 : Int)/10^30)
theorem v3650_mg_checked : Scalar.distance (sourceCoefficient 50 76 3 2) v3650_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3650_upper : Scalar.QComplex := ((999994428357946902356769894899 : Int)/10^30,(-3338151144421132800257618620 : Int)/10^30)
theorem v3650_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 76 5) 1) 14) v3650_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3650 : Material (50 : Basis) (76 : Basis) where
  plus := ![v3650_pa,v3650_pb,v3650_pg]
  minus := ![(Primitive.Addresses.material3650 1).one,v3650_mb,v3650_mg]
  upper := v3650_upper
  lower := (Primitive.Addresses.material3650 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3650_pa_checked.trans (by decide +kernel)
    · exact v3650_pb_checked.trans (by decide +kernel)
    · exact v3650_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 76 Primitive.Addresses.material3650
    · exact v3650_mb_checked.trans (by decide +kernel)
    · exact v3650_mg_checked.trans (by decide +kernel)
  upper_error := v3650_upper_checked
  lower_error := reuse_lower_error 50 76 Primitive.Addresses.material3650

def v3651_pa : Scalar.QComplex := ((999998695686062283693362164828 : Int)/10^30,(-1615124197762439925563073443 : Int)/10^30)
theorem v3651_pa_checked : Scalar.distance (sourceCoefficient 50 77 1 0) v3651_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3651_pb : Scalar.QComplex := ((-696889760422340916163919 : Int)/10^30,(-431476943026900919622146926 : Int)/10^30)
theorem v3651_pb_checked : Scalar.distance (sourceCoefficient 50 77 1 1) v3651_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3651_pg : Scalar.QComplex := ((-93086306844338791962936 : Int)/10^30,(150346142763200500154 : Int)/10^30)
theorem v3651_pg_checked : Scalar.distance (sourceCoefficient 50 77 1 2) v3651_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3651_mb : Scalar.QComplex := ((-1069234669770522111299621 : Int)/10^30,(-431476180983839065447295863 : Int)/10^30)
theorem v3651_mb_checked : Scalar.distance (sourceCoefficient 50 77 3 1) v3651_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3651_mg : Scalar.QComplex := ((-93086142442102633692494 : Int)/10^30,(230675377137495619672 : Int)/10^30)
theorem v3651_mg_checked : Scalar.distance (sourceCoefficient 50 77 3 2) v3651_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3651_upper : Scalar.QComplex := ((999994418747630742458172249512 : Int)/10^30,(-3341028821805803325772571122 : Int)/10^30)
theorem v3651_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 77 5) 1) 14) v3651_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3651 : Material (50 : Basis) (77 : Basis) where
  plus := ![v3651_pa,v3651_pb,v3651_pg]
  minus := ![(Primitive.Addresses.material3651 1).one,v3651_mb,v3651_mg]
  upper := v3651_upper
  lower := (Primitive.Addresses.material3651 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3651_pa_checked.trans (by decide +kernel)
    · exact v3651_pb_checked.trans (by decide +kernel)
    · exact v3651_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 77 Primitive.Addresses.material3651
    · exact v3651_mb_checked.trans (by decide +kernel)
    · exact v3651_mg_checked.trans (by decide +kernel)
  upper_error := v3651_upper_checked
  lower_error := reuse_lower_error 50 77 Primitive.Addresses.material3651

def v3652_pa : Scalar.QComplex := ((999998667595439372411819923033 : Int)/10^30,(-1632423764208688300776928652 : Int)/10^30)
theorem v3652_pa_checked : Scalar.distance (sourceCoefficient 50 78 1 0) v3652_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3652_pb : Scalar.QComplex := ((-704354132302185010716133 : Int)/10^30,(-431476929741316022096966776 : Int)/10^30)
theorem v3652_pb_checked : Scalar.distance (sourceCoefficient 50 78 1 1) v3652_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3652_pg : Scalar.QComplex := ((-93086304103803016158795 : Int)/10^30,(151956497408934953641 : Int)/10^30)
theorem v3652_pg_checked : Scalar.distance (sourceCoefficient 50 78 1 2) v3652_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3652_mb : Scalar.QComplex := ((-1076699027406178010305746 : Int)/10^30,(-431476161256842365276875613 : Int)/10^30)
theorem v3652_mb_checked : Scalar.distance (sourceCoefficient 50 78 3 1) v3652_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3652_mg : Scalar.QComplex := ((-93086138311904346727127 : Int)/10^30,(232285728818662496339 : Int)/10^30)
theorem v3652_mg_checked : Scalar.distance (sourceCoefficient 50 78 3 2) v3652_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3652_upper : Scalar.QComplex := ((999994360799567387043493575971 : Int)/10^30,(-3358328314004512845656849904 : Int)/10^30)
theorem v3652_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 78 5) 1) 14) v3652_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3652 : Material (50 : Basis) (78 : Basis) where
  plus := ![v3652_pa,v3652_pb,v3652_pg]
  minus := ![(Primitive.Addresses.material3652 1).one,v3652_mb,v3652_mg]
  upper := v3652_upper
  lower := (Primitive.Addresses.material3652 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3652_pa_checked.trans (by decide +kernel)
    · exact v3652_pb_checked.trans (by decide +kernel)
    · exact v3652_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 78 Primitive.Addresses.material3652
    · exact v3652_mb_checked.trans (by decide +kernel)
    · exact v3652_mg_checked.trans (by decide +kernel)
  upper_error := v3652_upper_checked
  lower_error := reuse_lower_error 50 78 Primitive.Addresses.material3652

def v3653_pa : Scalar.QComplex := ((999998658475727803111880797164 : Int)/10^30,(-1638000837822253174263550566 : Int)/10^30)
theorem v3653_pa_checked : Scalar.distance (sourceCoefficient 50 79 1 0) v3653_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3653_pb : Scalar.QComplex := ((-706760513477899466650712 : Int)/10^30,(-431476925421578850001114600 : Int)/10^30)
theorem v3653_pb_checked : Scalar.distance (sourceCoefficient 50 79 1 1) v3653_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3653_pg : Scalar.QComplex := ((-93086303213374927103439 : Int)/10^30,(152475647203066070331 : Int)/10^30)
theorem v3653_pg_checked : Scalar.distance (sourceCoefficient 50 79 1 2) v3653_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3653_mb : Scalar.QComplex := ((-1079105403958148151690462 : Int)/10^30,(-431476154860508226359941175 : Int)/10^30)
theorem v3653_mb_checked : Scalar.distance (sourceCoefficient 50 79 3 1) v3653_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3653_mg : Scalar.QComplex := ((-93086136973473698522450 : Int)/10^30,(232804877651091080893 : Int)/10^30)
theorem v3653_mg_checked : Scalar.distance (sourceCoefficient 50 79 3 2) v3653_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3653_upper : Scalar.QComplex := ((999994342054346291635661136324 : Int)/10^30,(-3363905363571886865984645641 : Int)/10^30)
theorem v3653_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 79 5) 1) 14) v3653_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3653 : Material (50 : Basis) (79 : Basis) where
  plus := ![v3653_pa,v3653_pb,v3653_pg]
  minus := ![(Primitive.Addresses.material3653 1).one,v3653_mb,v3653_mg]
  upper := v3653_upper
  lower := (Primitive.Addresses.material3653 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3653_pa_checked.trans (by decide +kernel)
    · exact v3653_pb_checked.trans (by decide +kernel)
    · exact v3653_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 79 Primitive.Addresses.material3653
    · exact v3653_mb_checked.trans (by decide +kernel)
    · exact v3653_mg_checked.trans (by decide +kernel)
  upper_error := v3653_upper_checked
  lower_error := reuse_lower_error 50 79 Primitive.Addresses.material3653

def v3654_pa : Scalar.QComplex := ((999998644167594325029076570952 : Int)/10^30,(-1646712777951403876358578713 : Int)/10^30)
theorem v3654_pa_checked : Scalar.distance (sourceCoefficient 50 80 1 0) v3654_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3654_pb : Scalar.QComplex := ((-710519518657539586430390 : Int)/10^30,(-431476918637914056219616487 : Int)/10^30)
theorem v3654_pb_checked : Scalar.distance (sourceCoefficient 50 80 1 1) v3654_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3654_pg : Scalar.QComplex := ((-93086301815678644025922 : Int)/10^30,(153286610483072839454 : Int)/10^30)
theorem v3654_pg_checked : Scalar.distance (sourceCoefficient 50 80 1 2) v3654_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3654_mb : Scalar.QComplex := ((-1082864401884141655953829 : Int)/10^30,(-431476144832993787726056455 : Int)/10^30)
theorem v3654_mb_checked : Scalar.distance (sourceCoefficient 50 80 3 1) v3654_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3654_mg : Scalar.QComplex := ((-93086134875953149655577 : Int)/10^30,(233615839422990215625 : Int)/10^30)
theorem v3654_mg_checked : Scalar.distance (sourceCoefficient 50 80 3 2) v3654_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3654_upper : Scalar.QComplex := ((999994312710215801957520470783 : Int)/10^30,(-3372617266031085762644149216 : Int)/10^30)
theorem v3654_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 80 5) 1) 14) v3654_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3654 : Material (50 : Basis) (80 : Basis) where
  plus := ![v3654_pa,v3654_pb,v3654_pg]
  minus := ![(Primitive.Addresses.material3654 1).one,v3654_mb,v3654_mg]
  upper := v3654_upper
  lower := (Primitive.Addresses.material3654 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3654_pa_checked.trans (by decide +kernel)
    · exact v3654_pb_checked.trans (by decide +kernel)
    · exact v3654_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 80 Primitive.Addresses.material3654
    · exact v3654_mb_checked.trans (by decide +kernel)
    · exact v3654_mg_checked.trans (by decide +kernel)
  upper_error := v3654_upper_checked
  lower_error := reuse_lower_error 50 80 Primitive.Addresses.material3654

def v3655_pa : Scalar.QComplex := ((999998600626733027618003901851 : Int)/10^30,(-1672944881249595645278316611 : Int)/10^30)
theorem v3655_pa_checked : Scalar.distance (sourceCoefficient 50 81 1 0) v3655_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3655_pb : Scalar.QComplex := ((-721838077920920673590934 : Int)/10^30,(-431476897948269339043002920 : Int)/10^30)
theorem v3655_pb_checked : Scalar.distance (sourceCoefficient 50 81 1 1) v3655_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3655_pg : Scalar.QComplex := ((-93086297557367720675419 : Int)/10^30,(155728462935323005034 : Int)/10^30)
theorem v3655_pg_checked : Scalar.distance (sourceCoefficient 50 81 1 2) v3655_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3655_mb : Scalar.QComplex := ((-1094182939078874281728523 : Int)/10^30,(-431476114375949898937564776 : Int)/10^30)
theorem v3655_mb_checked : Scalar.distance (sourceCoefficient 50 81 3 1) v3655_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3655_mg : Scalar.QComplex := ((-93086128510435122528865 : Int)/10^30,(236057687291296575416 : Int)/10^30)
theorem v3655_mg_checked : Scalar.distance (sourceCoefficient 50 81 3 2) v3655_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3655_upper : Scalar.QComplex := ((999994223895188818687252311312 : Int)/10^30,(-3398849255112064504969672248 : Int)/10^30)
theorem v3655_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 81 5) 1) 14) v3655_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3655 : Material (50 : Basis) (81 : Basis) where
  plus := ![v3655_pa,v3655_pb,v3655_pg]
  minus := ![(Primitive.Addresses.material3655 1).one,v3655_mb,v3655_mg]
  upper := v3655_upper
  lower := (Primitive.Addresses.material3655 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3655_pa_checked.trans (by decide +kernel)
    · exact v3655_pb_checked.trans (by decide +kernel)
    · exact v3655_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 81 Primitive.Addresses.material3655
    · exact v3655_mb_checked.trans (by decide +kernel)
    · exact v3655_mg_checked.trans (by decide +kernel)
  upper_error := v3655_upper_checked
  lower_error := reuse_lower_error 50 81 Primitive.Addresses.material3655

def v3656_pa : Scalar.QComplex := ((999998583947823471512169657856 : Int)/10^30,(-1682885126160787306640790434 : Int)/10^30)
theorem v3656_pa_checked : Scalar.distance (sourceCoefficient 50 82 1 0) v3656_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3656_pb : Scalar.QComplex := ((-726127068705047451632191 : Int)/10^30,(-431476890004823400273671146 : Int)/10^30)
theorem v3656_pb_checked : Scalar.distance (sourceCoefficient 50 82 1 1) v3656_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3656_pg : Scalar.QComplex := ((-93086295924223017769678 : Int)/10^30,(156653764690180885430 : Int)/10^30)
theorem v3656_pg_checked : Scalar.distance (sourceCoefficient 50 82 1 2) v3656_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3656_mb : Scalar.QComplex := ((-1098471921411177688643623 : Int)/10^30,(-431476102731301040148927654 : Int)/10^30)
theorem v3656_mb_checked : Scalar.distance (sourceCoefficient 50 82 3 1) v3656_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3656_mg : Scalar.QComplex := ((-93086126078797287319210 : Int)/10^30,(236982987292291999598 : Int)/10^30)
theorem v3656_mg_checked : Scalar.distance (sourceCoefficient 50 82 3 2) v3656_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3656_upper : Scalar.QComplex := ((999994190060343159115239252989 : Int)/10^30,(-3408789456432144239319880921 : Int)/10^30)
theorem v3656_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 82 5) 1) 14) v3656_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3656 : Material (50 : Basis) (82 : Basis) where
  plus := ![v3656_pa,v3656_pb,v3656_pg]
  minus := ![(Primitive.Addresses.material3656 1).one,v3656_mb,v3656_mg]
  upper := v3656_upper
  lower := (Primitive.Addresses.material3656 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3656_pa_checked.trans (by decide +kernel)
    · exact v3656_pb_checked.trans (by decide +kernel)
    · exact v3656_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 82 Primitive.Addresses.material3656
    · exact v3656_mb_checked.trans (by decide +kernel)
    · exact v3656_mg_checked.trans (by decide +kernel)
  upper_error := v3656_upper_checked
  lower_error := reuse_lower_error 50 82 Primitive.Addresses.material3656

def v3657_pa : Scalar.QComplex := ((999998561021339708721275841958 : Int)/10^30,(-1696453727610326739922994784 : Int)/10^30)
theorem v3657_pa_checked : Scalar.distance (sourceCoefficient 50 83 1 0) v3657_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3657_pb : Scalar.QComplex := ((-731981613182113419760141 : Int)/10^30,(-431476879070130067955896940 : Int)/10^30)
theorem v3657_pb_checked : Scalar.distance (sourceCoefficient 50 83 1 1) v3657_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3657_pg : Scalar.QComplex := ((-93086293677632108080845 : Int)/10^30,(157916817137778542824 : Int)/10^30)
theorem v3657_pg_checked : Scalar.distance (sourceCoefficient 50 83 1 2) v3657_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3657_mb : Scalar.QComplex := ((-1104326454272181316575007 : Int)/10^30,(-431476086744403574504317118 : Int)/10^30)
theorem v3657_mb_checked : Scalar.distance (sourceCoefficient 50 83 3 1) v3657_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3657_mg : Scalar.QComplex := ((-93086122742249837632610 : Int)/10^30,(238246037330890734040 : Int)/10^30)
theorem v3657_mg_checked : Scalar.distance (sourceCoefficient 50 83 3 2) v3657_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3657_upper : Scalar.QComplex := ((999994143715718374631688516923 : Int)/10^30,(-3422357998103814593186108685 : Int)/10^30)
theorem v3657_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 83 5) 1) 14) v3657_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3657 : Material (50 : Basis) (83 : Basis) where
  plus := ![v3657_pa,v3657_pb,v3657_pg]
  minus := ![(Primitive.Addresses.material3657 1).one,v3657_mb,v3657_mg]
  upper := v3657_upper
  lower := (Primitive.Addresses.material3657 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3657_pa_checked.trans (by decide +kernel)
    · exact v3657_pb_checked.trans (by decide +kernel)
    · exact v3657_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 83 Primitive.Addresses.material3657
    · exact v3657_mb_checked.trans (by decide +kernel)
    · exact v3657_mg_checked.trans (by decide +kernel)
  upper_error := v3657_upper_checked
  lower_error := reuse_lower_error 50 83 Primitive.Addresses.material3657

def v3658_pa : Scalar.QComplex := ((999998500792179390726483933491 : Int)/10^30,(-1731592733177884890411391690 : Int)/10^30)
theorem v3658_pa_checked : Scalar.distance (sourceCoefficient 50 84 1 0) v3658_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3658_pb : Scalar.QComplex := ((-747143298567611213392207 : Int)/10^30,(-431476850259905585314394129 : Int)/10^30)
theorem v3658_pb_checked : Scalar.distance (sourceCoefficient 50 84 1 1) v3658_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3658_pg : Scalar.QComplex := ((-93086287766632148443727 : Int)/10^30,(161187781109187697777 : Int)/10^30)
theorem v3658_pg_checked : Scalar.distance (sourceCoefficient 50 84 1 2) v3658_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3658_mb : Scalar.QComplex := ((-1119488109150364553756253 : Int)/10^30,(-431476044850338188502406493 : Int)/10^30)
theorem v3658_mb_checked : Scalar.distance (sourceCoefficient 50 84 3 1) v3658_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3658_mg : Scalar.QComplex := ((-93086114008557490353364 : Int)/10^30,(241516994983443768388 : Int)/10^30)
theorem v3658_mg_checked : Scalar.distance (sourceCoefficient 50 84 3 2) v3658_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3658_upper : Scalar.QComplex := ((999994022839911936974282031832 : Int)/10^30,(-3457496847385884906229977103 : Int)/10^30)
theorem v3658_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 84 5) 1) 14) v3658_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3658 : Material (50 : Basis) (84 : Basis) where
  plus := ![v3658_pa,v3658_pb,v3658_pg]
  minus := ![(Primitive.Addresses.material3658 1).one,v3658_mb,v3658_mg]
  upper := v3658_upper
  lower := (Primitive.Addresses.material3658 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3658_pa_checked.trans (by decide +kernel)
    · exact v3658_pb_checked.trans (by decide +kernel)
    · exact v3658_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 84 Primitive.Addresses.material3658
    · exact v3658_mb_checked.trans (by decide +kernel)
    · exact v3658_mg_checked.trans (by decide +kernel)
  upper_error := v3658_upper_checked
  lower_error := reuse_lower_error 50 84 Primitive.Addresses.material3658

def v3659_pa : Scalar.QComplex := ((999998360772983430458855227107 : Int)/10^30,(-1810649426607445298386015930 : Int)/10^30)
theorem v3659_pa_checked : Scalar.distance (sourceCoefficient 50 85 1 0) v3659_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3659_pb : Scalar.QComplex := ((-781254470106098828988575 : Int)/10^30,(-431476782844966959522579733 : Int)/10^30)
theorem v3659_pb_checked : Scalar.distance (sourceCoefficient 50 85 1 1) v3659_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3659_pg : Scalar.QComplex := ((-93086273977680623771659 : Int)/10^30,(168546884889318246923 : Int)/10^30)
theorem v3659_pg_checked : Scalar.distance (sourceCoefficient 50 85 1 2) v3659_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3659_mb : Scalar.QComplex := ((-1153599209811648270086552 : Int)/10^30,(-431475947999019936794025626 : Int)/10^30)
theorem v3659_mb_checked : Scalar.distance (sourceCoefficient 50 85 3 1) v3659_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3659_mg : Scalar.QComplex := ((-93086093869035979416034 : Int)/10^30,(248876084124199518064 : Int)/10^30)
theorem v3659_mg_checked : Scalar.distance (sourceCoefficient 50 85 3 2) v3659_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3659_upper : Scalar.QComplex := ((999993746376243626633558277735 : Int)/10^30,(-3536553181409357317245856810 : Int)/10^30)
theorem v3659_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 85 5) 1) 14) v3659_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3659 : Material (50 : Basis) (85 : Basis) where
  plus := ![v3659_pa,v3659_pb,v3659_pg]
  minus := ![(Primitive.Addresses.material3659 1).one,v3659_mb,v3659_mg]
  upper := v3659_upper
  lower := (Primitive.Addresses.material3659 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3659_pa_checked.trans (by decide +kernel)
    · exact v3659_pb_checked.trans (by decide +kernel)
    · exact v3659_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 85 Primitive.Addresses.material3659
    · exact v3659_mb_checked.trans (by decide +kernel)
    · exact v3659_mg_checked.trans (by decide +kernel)
  upper_error := v3659_upper_checked
  lower_error := reuse_lower_error 50 85 Primitive.Addresses.material3659

def v3660_pa : Scalar.QComplex := ((999998334258950205939336547377 : Int)/10^30,(-1825234046607414223500903990 : Int)/10^30)
theorem v3660_pa_checked : Scalar.distance (sourceCoefficient 50 86 1 0) v3660_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3660_pb : Scalar.QComplex := ((-787547402801976634269947 : Int)/10^30,(-431476770015199465056425406 : Int)/10^30)
theorem v3660_pb_checked : Scalar.distance (sourceCoefficient 50 86 1 1) v3660_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3660_pg : Scalar.QComplex := ((-93086271359693142659258 : Int)/10^30,(169904514774373366346 : Int)/10^30)
theorem v3660_pg_checked : Scalar.distance (sourceCoefficient 50 86 1 2) v3660_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3660_mb : Scalar.QComplex := ((-1159892129092868115014180 : Int)/10^30,(-431475929738739726061572681 : Int)/10^30)
theorem v3660_mb_checked : Scalar.distance (sourceCoefficient 50 86 3 1) v3660_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3660_mg : Scalar.QComplex := ((-93086090079476027677651 : Int)/10^30,(250233711244541698110 : Int)/10^30)
theorem v3660_mg_checked : Scalar.distance (sourceCoefficient 50 86 3 2) v3660_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3660_upper : Scalar.QComplex := ((999993694690518878096462896587 : Int)/10^30,(-3551137733926431971004056393 : Int)/10^30)
theorem v3660_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 86 5) 1) 14) v3660_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3660 : Material (50 : Basis) (86 : Basis) where
  plus := ![v3660_pa,v3660_pb,v3660_pg]
  minus := ![(Primitive.Addresses.material3660 1).one,v3660_mb,v3660_mg]
  upper := v3660_upper
  lower := (Primitive.Addresses.material3660 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3660_pa_checked.trans (by decide +kernel)
    · exact v3660_pb_checked.trans (by decide +kernel)
    · exact v3660_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 86 Primitive.Addresses.material3660
    · exact v3660_mb_checked.trans (by decide +kernel)
    · exact v3660_mg_checked.trans (by decide +kernel)
  upper_error := v3660_upper_checked
  lower_error := reuse_lower_error 50 86 Primitive.Addresses.material3660

def v3661_pa : Scalar.QComplex := ((999998332495752328188162903204 : Int)/10^30,(-1826199801438278459068321721 : Int)/10^30)
theorem v3661_pa_checked : Scalar.distance (sourceCoefficient 50 87 1 0) v3661_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3661_pb : Scalar.QComplex := ((-787964104101134754551114 : Int)/10^30,(-431476769161326384069284254 : Int)/10^30)
theorem v3661_pb_checked : Scalar.distance (sourceCoefficient 50 87 1 1) v3661_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3661_pg : Scalar.QComplex := ((-93086271185521480436163 : Int)/10^30,(169994413422035530872 : Int)/10^30)
theorem v3661_pg_checked : Scalar.distance (sourceCoefficient 50 87 1 2) v3661_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3661_mb : Scalar.QComplex := ((-1160308829500015285552678 : Int)/10^30,(-431475928525272509366776332 : Int)/10^30)
theorem v3661_mb_checked : Scalar.distance (sourceCoefficient 50 87 3 1) v3661_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3661_mg : Scalar.QComplex := ((-93086089827725946258967 : Int)/10^30,(250323609708428187441 : Int)/10^30)
theorem v3661_mg_checked : Scalar.distance (sourceCoefficient 50 87 3 2) v3661_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3661_upper : Scalar.QComplex := ((999993691260518400943601779851 : Int)/10^30,(-3552103484275798250594178195 : Int)/10^30)
theorem v3661_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 87 5) 1) 14) v3661_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3661 : Material (50 : Basis) (87 : Basis) where
  plus := ![v3661_pa,v3661_pb,v3661_pg]
  minus := ![(Primitive.Addresses.material3661 1).one,v3661_mb,v3661_mg]
  upper := v3661_upper
  lower := (Primitive.Addresses.material3661 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3661_pa_checked.trans (by decide +kernel)
    · exact v3661_pb_checked.trans (by decide +kernel)
    · exact v3661_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 87 Primitive.Addresses.material3661
    · exact v3661_mb_checked.trans (by decide +kernel)
    · exact v3661_mg_checked.trans (by decide +kernel)
  upper_error := v3661_upper_checked
  lower_error := reuse_lower_error 50 87 Primitive.Addresses.material3661

def v3662_pa : Scalar.QComplex := ((999998310951241007742487924129 : Int)/10^30,(-1837959375258007374564514513 : Int)/10^30)
theorem v3662_pa_checked : Scalar.distance (sourceCoefficient 50 88 1 0) v3662_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3662_pb : Scalar.QComplex := ((-793038093377283825900560 : Int)/10^30,(-431476758721042018521252923 : Int)/10^30)
theorem v3662_pb_checked : Scalar.distance (sourceCoefficient 50 88 1 1) v3662_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3662_pg : Scalar.QComplex := ((-93086269056583601790458 : Int)/10^30,(171089069898118368826 : Int)/10^30)
theorem v3662_pg_checked : Scalar.distance (sourceCoefficient 50 88 1 2) v3662_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3662_mb : Scalar.QComplex := ((-1165382807877391062110918 : Int)/10^30,(-431475913706367809890898635 : Int)/10^30)
theorem v3662_mb_checked : Scalar.distance (sourceCoefficient 50 88 3 1) v3662_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3662_mg : Scalar.QComplex := ((-93086086754149622952167 : Int)/10^30,(251418263939742885609 : Int)/10^30)
theorem v3662_mg_checked : Scalar.distance (sourceCoefficient 50 88 3 2) v3662_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3662_upper : Scalar.QComplex := ((999993649420081575868018089516 : Int)/10^30,(-3563863003397151301891446576 : Int)/10^30)
theorem v3662_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 88 5) 1) 14) v3662_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3662 : Material (50 : Basis) (88 : Basis) where
  plus := ![v3662_pa,v3662_pb,v3662_pg]
  minus := ![(Primitive.Addresses.material3662 1).one,v3662_mb,v3662_mg]
  upper := v3662_upper
  lower := (Primitive.Addresses.material3662 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3662_pa_checked.trans (by decide +kernel)
    · exact v3662_pb_checked.trans (by decide +kernel)
    · exact v3662_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 88 Primitive.Addresses.material3662
    · exact v3662_mb_checked.trans (by decide +kernel)
    · exact v3662_mg_checked.trans (by decide +kernel)
  upper_error := v3662_upper_checked
  lower_error := reuse_lower_error 50 88 Primitive.Addresses.material3662

def v3663_pa : Scalar.QComplex := ((999998281249986541277099029123 : Int)/10^30,(-1854048832370883654655555096 : Int)/10^30)
theorem v3663_pa_checked : Scalar.distance (sourceCoefficient 50 89 1 0) v3663_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3663_pb : Scalar.QComplex := ((-799980328945170550054666 : Int)/10^30,(-431476744307747411585690073 : Int)/10^30)
theorem v3663_pb_checked : Scalar.distance (sourceCoefficient 50 89 1 1) v3663_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3663_pg : Scalar.QComplex := ((-93086266119438500806384 : Int)/10^30,(172586779642040132047 : Int)/10^30)
theorem v3663_pg_checked : Scalar.distance (sourceCoefficient 50 89 1 2) v3663_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3663_mb : Scalar.QComplex := ((-1172325028422342113407700 : Int)/10^30,(-431475893302241941280639863 : Int)/10^30)
theorem v3663_mb_checked : Scalar.distance (sourceCoefficient 50 89 3 1) v3663_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3663_mg : Scalar.QComplex := ((-93086082524549560939811 : Int)/10^30,(252915970591374924406 : Int)/10^30)
theorem v3663_mg_checked : Scalar.distance (sourceCoefficient 50 89 3 2) v3663_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3663_upper : Scalar.QComplex := ((999993591949927993255065140626 : Int)/10^30,(-3579952385285000480388872305 : Int)/10^30)
theorem v3663_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 89 5) 1) 14) v3663_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3663 : Material (50 : Basis) (89 : Basis) where
  plus := ![v3663_pa,v3663_pb,v3663_pg]
  minus := ![(Primitive.Addresses.material3663 1).one,v3663_mb,v3663_mg]
  upper := v3663_upper
  lower := (Primitive.Addresses.material3663 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3663_pa_checked.trans (by decide +kernel)
    · exact v3663_pb_checked.trans (by decide +kernel)
    · exact v3663_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 89 Primitive.Addresses.material3663
    · exact v3663_mb_checked.trans (by decide +kernel)
    · exact v3663_mg_checked.trans (by decide +kernel)
  upper_error := v3663_upper_checked
  lower_error := reuse_lower_error 50 89 Primitive.Addresses.material3663

def v3664_pa : Scalar.QComplex := ((999998232325156631293046238290 : Int)/10^30,(-1880251728376565548035745999 : Int)/10^30)
theorem v3664_pa_checked : Scalar.distance (sourceCoefficient 50 90 1 0) v3664_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3664_pb : Scalar.QComplex := ((-811286283594509005837155 : Int)/10^30,(-431476720515836940109630773 : Int)/10^30)
theorem v3664_pb_checked : Scalar.distance (sourceCoefficient 50 90 1 1) v3664_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3664_pg : Scalar.QComplex := ((-93086261275900866820472 : Int)/10^30,(175025913041028588853 : Int)/10^30)
theorem v3664_pg_checked : Scalar.distance (sourceCoefficient 50 90 1 2) v3664_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3664_mb : Scalar.QComplex := ((-1183630958330609756574200 : Int)/10^30,(-431475859753810667536071396 : Int)/10^30)
theorem v3664_mb_checked : Scalar.distance (sourceCoefficient 50 90 3 1) v3664_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3664_mg : Scalar.QComplex := ((-93086075576151461587582 : Int)/10^30,(255355098902407709573 : Int)/10^30)
theorem v3664_mg_checked : Scalar.distance (sourceCoefficient 50 90 3 2) v3664_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3664_upper : Scalar.QComplex := ((999993497801349553407786638283 : Int)/10^30,(-3606155157824728782954884673 : Int)/10^30)
theorem v3664_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 90 5) 1) 14) v3664_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3664 : Material (50 : Basis) (90 : Basis) where
  plus := ![v3664_pa,v3664_pb,v3664_pg]
  minus := ![(Primitive.Addresses.material3664 1).one,v3664_mb,v3664_mg]
  upper := v3664_upper
  lower := (Primitive.Addresses.material3664 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3664_pa_checked.trans (by decide +kernel)
    · exact v3664_pb_checked.trans (by decide +kernel)
    · exact v3664_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 90 Primitive.Addresses.material3664
    · exact v3664_mb_checked.trans (by decide +kernel)
    · exact v3664_mg_checked.trans (by decide +kernel)
  upper_error := v3664_upper_checked
  lower_error := reuse_lower_error 50 90 Primitive.Addresses.material3664

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
