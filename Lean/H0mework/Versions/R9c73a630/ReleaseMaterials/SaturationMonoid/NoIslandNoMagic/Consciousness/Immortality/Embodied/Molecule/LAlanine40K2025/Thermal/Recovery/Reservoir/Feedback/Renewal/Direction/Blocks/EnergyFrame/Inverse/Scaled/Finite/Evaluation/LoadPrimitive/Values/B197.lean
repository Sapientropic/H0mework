import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B131
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B132

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3153_pa : Scalar.QComplex := ((999998219742216285136145691185 : Int)/10^30,(-1886932006753807552589267537 : Int)/10^30)
theorem v3153_pa_checked : Scalar.distance (sourceCoefficient 40 94 1 0) v3153_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3153_pb : Scalar.QComplex := ((-814168615059545326715008 : Int)/10^30,(-431476684223607751595256771 : Int)/10^30)
theorem v3153_pb_checked : Scalar.distance (sourceCoefficient 40 94 1 1) v3153_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3153_pg : Scalar.QComplex := ((-93086256775429865822720 : Int)/10^30,(175647749996736215321 : Int)/10^30)
theorem v3153_pg_checked : Scalar.distance (sourceCoefficient 40 94 1 2) v3153_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3153_mb : Scalar.QComplex := ((-1186513257403863095601251 : Int)/10^30,(-431475820974272753341127606 : Int)/10^30)
theorem v3153_mb_checked : Scalar.distance (sourceCoefficient 40 94 3 1) v3153_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3153_mg : Scalar.QComplex := ((-93086070539064850042019 : Int)/10^30,(255976931742873237907 : Int)/10^30)
theorem v3153_mg_checked : Scalar.distance (sourceCoefficient 40 94 3 2) v3153_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3153_upper : Scalar.QComplex := ((999993473688873499063071720363 : Int)/10^30,(-3612835404535467343192612246 : Int)/10^30)
theorem v3153_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 94 5) 1) 14) v3153_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3153 : Material (40 : Basis) (94 : Basis) where
  plus := ![v3153_pa,v3153_pb,v3153_pg]
  minus := ![(Primitive.Addresses.material3153 1).one,v3153_mb,v3153_mg]
  upper := v3153_upper
  lower := (Primitive.Addresses.material3153 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3153_pa_checked.trans (by decide +kernel)
    · exact v3153_pb_checked.trans (by decide +kernel)
    · exact v3153_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 94 Primitive.Addresses.material3153
    · exact v3153_mb_checked.trans (by decide +kernel)
    · exact v3153_mg_checked.trans (by decide +kernel)
  upper_error := v3153_upper_checked
  lower_error := reuse_lower_error 40 94 Primitive.Addresses.material3153

def v3154_pa : Scalar.QComplex := ((999998135219664891835524878450 : Int)/10^30,(-1931206149744410570580354075 : Int)/10^30)
theorem v3154_pa_checked : Scalar.distance (sourceCoefficient 40 95 1 0) v3154_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3154_pb : Scalar.QComplex := ((-833271897196496509065654 : Int)/10^30,(-431476641392080119125667905 : Int)/10^30)
theorem v3154_pb_checked : Scalar.distance (sourceCoefficient 40 95 1 1) v3154_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3154_pg : Scalar.QComplex := ((-93086248221268015951371 : Int)/10^30,(179769070251374557575 : Int)/10^30)
theorem v3154_pg_checked : Scalar.distance (sourceCoefficient 40 95 1 2) v3154_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3154_mb : Scalar.QComplex := ((-1205616495466109988814343 : Int)/10^30,(-431475761657488964706548973 : Int)/10^30)
theorem v3154_mb_checked : Scalar.distance (sourceCoefficient 40 95 3 1) v3154_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3154_mg : Scalar.QComplex := ((-93086058428392422897010 : Int)/10^30,(260098243081099284428 : Int)/10^30)
theorem v3154_mg_checked : Scalar.distance (sourceCoefficient 40 95 3 2) v3154_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3154_upper : Scalar.QComplex := ((999993312753293709270009702989 : Int)/10^30,(-3657109335706679303980646687 : Int)/10^30)
theorem v3154_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 95 5) 1) 14) v3154_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3154 : Material (40 : Basis) (95 : Basis) where
  plus := ![v3154_pa,v3154_pb,v3154_pg]
  minus := ![(Primitive.Addresses.material3154 1).one,v3154_mb,v3154_mg]
  upper := v3154_upper
  lower := (Primitive.Addresses.material3154 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3154_pa_checked.trans (by decide +kernel)
    · exact v3154_pb_checked.trans (by decide +kernel)
    · exact v3154_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 95 Primitive.Addresses.material3154
    · exact v3154_mb_checked.trans (by decide +kernel)
    · exact v3154_mg_checked.trans (by decide +kernel)
  upper_error := v3154_upper_checked
  lower_error := reuse_lower_error 40 95 Primitive.Addresses.material3154

def v3155_pa : Scalar.QComplex := ((999998093928230196228563550873 : Int)/10^30,(-1952470206302250141973600386 : Int)/10^30)
theorem v3155_pa_checked : Scalar.distance (sourceCoefficient 40 96 1 0) v3155_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3155_pb : Scalar.QComplex := ((-842446851850216333041824 : Int)/10^30,(-431476620420009928440414348 : Int)/10^30)
theorem v3155_pb_checked : Scalar.distance (sourceCoefficient 40 96 1 1) v3155_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3155_pg : Scalar.QComplex := ((-93086244037187567144066 : Int)/10^30,(181748464524806647275 : Int)/10^30)
theorem v3155_pg_checked : Scalar.distance (sourceCoefficient 40 96 1 2) v3155_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3155_mb : Scalar.QComplex := ((-1214791428605622851485092 : Int)/10^30,(-431475732767853941339274950 : Int)/10^30)
theorem v3155_mb_checked : Scalar.distance (sourceCoefficient 40 96 3 1) v3155_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3155_mg : Scalar.QComplex := ((-93086052536185422650908 : Int)/10^30,(262077633006839440009 : Int)/10^30)
theorem v3155_mg_checked : Scalar.distance (sourceCoefficient 40 96 3 2) v3155_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3155_upper : Scalar.QComplex := ((999993234762087953715430952668 : Int)/10^30,(-3678373289328934129096009653 : Int)/10^30)
theorem v3155_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 96 5) 1) 14) v3155_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3155 : Material (40 : Basis) (96 : Basis) where
  plus := ![v3155_pa,v3155_pb,v3155_pg]
  minus := ![(Primitive.Addresses.material3155 1).one,v3155_mb,v3155_mg]
  upper := v3155_upper
  lower := (Primitive.Addresses.material3155 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3155_pa_checked.trans (by decide +kernel)
    · exact v3155_pb_checked.trans (by decide +kernel)
    · exact v3155_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 96 Primitive.Addresses.material3155
    · exact v3155_mb_checked.trans (by decide +kernel)
    · exact v3155_mg_checked.trans (by decide +kernel)
  upper_error := v3155_upper_checked
  lower_error := reuse_lower_error 40 96 Primitive.Addresses.material3155

def v3156_pa : Scalar.QComplex := ((999997948404818741720264391662 : Int)/10^30,(-2025632284861635914833340137 : Int)/10^30)
theorem v3156_pa_checked : Scalar.distance (sourceCoefficient 40 97 1 0) v3156_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3156_pb : Scalar.QComplex := ((-874014615420074087956495 : Int)/10^30,(-431476546275328347869513356 : Int)/10^30)
theorem v3156_pb_checked : Scalar.distance (sourceCoefficient 40 97 1 1) v3156_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3156_pg : Scalar.QComplex := ((-93086229266118888395806 : Int)/10^30,(188558858123927196642 : Int)/10^30)
theorem v3156_pg_checked : Scalar.distance (sourceCoefficient 40 97 1 2) v3156_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3156_mb : Scalar.QComplex := ((-1246359116437838659737970 : Int)/10^30,(-431475631381641766727663838 : Int)/10^30)
theorem v3156_mb_checked : Scalar.distance (sourceCoefficient 40 97 3 1) v3156_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3156_mg : Scalar.QComplex := ((-93086031888059296546952 : Int)/10^30,(268888011323372196537 : Int)/10^30)
theorem v3156_mg_checked : Scalar.distance (sourceCoefficient 40 97 3 2) v3156_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3156_upper : Scalar.QComplex := ((999992962967782857654121845806 : Int)/10^30,(-3751535007761791719488533123 : Int)/10^30)
theorem v3156_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 97 5) 1) 14) v3156_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3156 : Material (40 : Basis) (97 : Basis) where
  plus := ![v3156_pa,v3156_pb,v3156_pg]
  minus := ![(Primitive.Addresses.material3156 1).one,v3156_mb,v3156_mg]
  upper := v3156_upper
  lower := (Primitive.Addresses.material3156 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3156_pa_checked.trans (by decide +kernel)
    · exact v3156_pb_checked.trans (by decide +kernel)
    · exact v3156_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 97 Primitive.Addresses.material3156
    · exact v3156_mb_checked.trans (by decide +kernel)
    · exact v3156_mg_checked.trans (by decide +kernel)
  upper_error := v3156_upper_checked
  lower_error := reuse_lower_error 40 97 Primitive.Addresses.material3156

def v3157_pa : Scalar.QComplex := ((999999548146888309971818841986 : Int)/10^30,(-950634535039003208185270484 : Int)/10^30)
theorem v3157_pa_checked : Scalar.distance (sourceCoefficient 41 42 1 0) v3157_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3157_pb : Scalar.QComplex := ((-410177432546905136001388 : Int)/10^30,(-431477326026375524724052763 : Int)/10^30)
theorem v3157_pb_checked : Scalar.distance (sourceCoefficient 41 42 1 1) v3157_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3157_pg : Scalar.QComplex := ((-93086387834524128068005 : Int)/10^30,(88491175002545951203 : Int)/10^30)
theorem v3157_pg_checked : Scalar.distance (sourceCoefficient 41 42 1 2) v3157_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3157_mb : Scalar.QComplex := ((-782522779162486328070928 : Int)/10^30,(-431476811402996974949155738 : Int)/10^30)
theorem v3157_mb_checked : Scalar.distance (sourceCoefficient 41 42 3 1) v3157_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3157_mg : Scalar.QComplex := ((-93086276810309146562466 : Int)/10^30,(168820502299154762210 : Int)/10^30)
theorem v3157_mg_checked : Scalar.distance (sourceCoefficient 41 42 3 2) v3157_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3157_upper : Scalar.QComplex := ((999996418056062957820236134213 : Int)/10^30,(-2676541620031713875329071124 : Int)/10^30)
theorem v3157_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 42 5) 1) 14) v3157_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3157 : Material (41 : Basis) (42 : Basis) where
  plus := ![v3157_pa,v3157_pb,v3157_pg]
  minus := ![(Primitive.Addresses.material3157 1).one,v3157_mb,v3157_mg]
  upper := v3157_upper
  lower := (Primitive.Addresses.material3157 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3157_pa_checked.trans (by decide +kernel)
    · exact v3157_pb_checked.trans (by decide +kernel)
    · exact v3157_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 42 Primitive.Addresses.material3157
    · exact v3157_mb_checked.trans (by decide +kernel)
    · exact v3157_mg_checked.trans (by decide +kernel)
  upper_error := v3157_upper_checked
  lower_error := reuse_lower_error 41 42 Primitive.Addresses.material3157

def v3158_pa : Scalar.QComplex := ((999999533313387125330481620515 : Int)/10^30,(-966112316427517862294049265 : Int)/10^30)
theorem v3158_pa_checked : Scalar.distance (sourceCoefficient 41 43 1 0) v3158_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3158_pb : Scalar.QComplex := ((-416855747249088086724457 : Int)/10^30,(-431477319582816584662801865 : Int)/10^30)
theorem v3158_pb_checked : Scalar.distance (sourceCoefficient 41 43 1 1) v3158_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3158_pg : Scalar.QComplex := ((-93086386449062552215678 : Int)/10^30,(89931946410206390699 : Int)/10^30)
theorem v3158_pg_checked : Scalar.distance (sourceCoefficient 41 43 1 2) v3158_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3158_mb : Scalar.QComplex := ((-789201085817526342960320 : Int)/10^30,(-431476799196355626264200047 : Int)/10^30)
theorem v3158_mb_checked : Scalar.distance (sourceCoefficient 41 43 3 1) v3158_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3158_mg : Scalar.QComplex := ((-93086274181527251705217 : Int)/10^30,(170261271974759219040 : Int)/10^30)
theorem v3158_mg_checked : Scalar.distance (sourceCoefficient 41 43 3 2) v3158_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3158_upper : Scalar.QComplex := ((999996376509337322719233174862 : Int)/10^30,(-2692019352766613939189703481 : Int)/10^30)
theorem v3158_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 43 5) 1) 14) v3158_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3158 : Material (41 : Basis) (43 : Basis) where
  plus := ![v3158_pa,v3158_pb,v3158_pg]
  minus := ![(Primitive.Addresses.material3158 1).one,v3158_mb,v3158_mg]
  upper := v3158_upper
  lower := (Primitive.Addresses.material3158 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3158_pa_checked.trans (by decide +kernel)
    · exact v3158_pb_checked.trans (by decide +kernel)
    · exact v3158_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 43 Primitive.Addresses.material3158
    · exact v3158_mb_checked.trans (by decide +kernel)
    · exact v3158_mg_checked.trans (by decide +kernel)
  upper_error := v3158_upper_checked
  lower_error := reuse_lower_error 41 43 Primitive.Addresses.material3158

def v3159_pa : Scalar.QComplex := ((999999527638901431800971198859 : Int)/10^30,(-971968093103570255796306645 : Int)/10^30)
theorem v3159_pa_checked : Scalar.distance (sourceCoefficient 41 44 1 0) v3159_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3159_pb : Scalar.QComplex := ((-419382383227862715170316 : Int)/10^30,(-431477317109061971445134223 : Int)/10^30)
theorem v3159_pb_checked : Scalar.distance (sourceCoefficient 41 44 1 1) v3159_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3159_pg : Scalar.QComplex := ((-93086385918111355446502 : Int)/10^30,(90477039752563621835 : Int)/10^30)
theorem v3159_pg_checked : Scalar.distance (sourceCoefficient 41 44 1 2) v3159_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3159_mb : Scalar.QComplex := ((-791727718720780106104733 : Int)/10^30,(-431476794542228879916124689 : Int)/10^30)
theorem v3159_mb_checked : Scalar.distance (sourceCoefficient 41 44 3 1) v3159_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3159_mg : Scalar.QComplex := ((-93086273180185248271944 : Int)/10^30,(170806364655966317163 : Int)/10^30)
theorem v3159_mg_checked : Scalar.distance (sourceCoefficient 41 44 3 2) v3159_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3159_upper : Scalar.QComplex := ((999996360728320769713455688671 : Int)/10^30,(-2697875110927527319849270522 : Int)/10^30)
theorem v3159_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 44 5) 1) 14) v3159_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3159 : Material (41 : Basis) (44 : Basis) where
  plus := ![v3159_pa,v3159_pb,v3159_pg]
  minus := ![(Primitive.Addresses.material3159 1).one,v3159_mb,v3159_mg]
  upper := v3159_upper
  lower := (Primitive.Addresses.material3159 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3159_pa_checked.trans (by decide +kernel)
    · exact v3159_pb_checked.trans (by decide +kernel)
    · exact v3159_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 44 Primitive.Addresses.material3159
    · exact v3159_mb_checked.trans (by decide +kernel)
    · exact v3159_mg_checked.trans (by decide +kernel)
  upper_error := v3159_upper_checked
  lower_error := reuse_lower_error 41 44 Primitive.Addresses.material3159

def v3160_pa : Scalar.QComplex := ((999999524803000276814828840919 : Int)/10^30,(-974881415165035237323750490 : Int)/10^30)
theorem v3160_pa_checked : Scalar.distance (sourceCoefficient 41 45 1 0) v3160_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3160_pb : Scalar.QComplex := ((-420639416194509641777994 : Int)/10^30,(-431477315870989436812927496 : Int)/10^30)
theorem v3160_pb_checked : Scalar.distance (sourceCoefficient 41 45 1 1) v3160_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3160_pg : Scalar.QComplex := ((-93086385652569275200382 : Int)/10^30,(90748230500861831338 : Int)/10^30)
theorem v3160_pg_checked : Scalar.distance (sourceCoefficient 41 45 1 2) v3160_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3160_mb : Scalar.QComplex := ((-792984750150975373314564 : Int)/10^30,(-431476792219393970721790346 : Int)/10^30)
theorem v3160_mb_checked : Scalar.distance (sourceCoefficient 41 45 3 1) v3160_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3160_mg : Scalar.QComplex := ((-93086272680617865095821 : Int)/10^30,(171077555074136961364 : Int)/10^30)
theorem v3160_mg_checked : Scalar.distance (sourceCoefficient 41 45 3 2) v3160_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3160_upper : Scalar.QComplex := ((999996352864294254893257883705 : Int)/10^30,(-2700788423755433191110816359 : Int)/10^30)
theorem v3160_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 45 5) 1) 14) v3160_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3160 : Material (41 : Basis) (45 : Basis) where
  plus := ![v3160_pa,v3160_pb,v3160_pg]
  minus := ![(Primitive.Addresses.material3160 1).one,v3160_mb,v3160_mg]
  upper := v3160_upper
  lower := (Primitive.Addresses.material3160 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3160_pa_checked.trans (by decide +kernel)
    · exact v3160_pb_checked.trans (by decide +kernel)
    · exact v3160_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 45 Primitive.Addresses.material3160
    · exact v3160_mb_checked.trans (by decide +kernel)
    · exact v3160_mg_checked.trans (by decide +kernel)
  upper_error := v3160_upper_checked
  lower_error := reuse_lower_error 41 45 Primitive.Addresses.material3160

def v3161_pa : Scalar.QComplex := ((999999508715909508069301385455 : Int)/10^30,(-991245650494267655298784400 : Int)/10^30)
theorem v3161_pa_checked : Scalar.distance (sourceCoefficient 41 46 1 0) v3161_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3161_pb : Scalar.QComplex := ((-427700215783004189399412 : Int)/10^30,(-431477308825947833915502695 : Int)/10^30)
theorem v3161_pb_checked : Scalar.distance (sourceCoefficient 41 46 1 1) v3161_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3161_pg : Scalar.QComplex := ((-93086384143880044846908 : Int)/10^30,(92271518734388817141 : Int)/10^30)
theorem v3161_pg_checked : Scalar.distance (sourceCoefficient 41 46 1 2) v3161_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3161_mb : Scalar.QComplex := ((-800045541030857933251540 : Int)/10^30,(-431476779081202952753039603 : Int)/10^30)
theorem v3161_mb_checked : Scalar.distance (sourceCoefficient 41 46 3 1) v3161_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3161_mg : Scalar.QComplex := ((-93086269857400057317760 : Int)/10^30,(172600841438543263158 : Int)/10^30)
theorem v3161_mg_checked : Scalar.distance (sourceCoefficient 41 46 3 2) v3161_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3161_upper : Scalar.QComplex := ((999996308534041819556940079981 : Int)/10^30,(-2717152606947200106928087015 : Int)/10^30)
theorem v3161_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 46 5) 1) 14) v3161_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3161 : Material (41 : Basis) (46 : Basis) where
  plus := ![v3161_pa,v3161_pb,v3161_pg]
  minus := ![(Primitive.Addresses.material3161 1).one,v3161_mb,v3161_mg]
  upper := v3161_upper
  lower := (Primitive.Addresses.material3161 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3161_pa_checked.trans (by decide +kernel)
    · exact v3161_pb_checked.trans (by decide +kernel)
    · exact v3161_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 46 Primitive.Addresses.material3161
    · exact v3161_mb_checked.trans (by decide +kernel)
    · exact v3161_mg_checked.trans (by decide +kernel)
  upper_error := v3161_upper_checked
  lower_error := reuse_lower_error 41 46 Primitive.Addresses.material3161

def v3162_pa : Scalar.QComplex := ((999999504804587720400311146380 : Int)/10^30,(-995183691255389813195454190 : Int)/10^30)
theorem v3162_pa_checked : Scalar.distance (sourceCoefficient 41 47 1 0) v3162_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3162_pb : Scalar.QComplex := ((-429399391816851657858018 : Int)/10^30,(-431477307107565818864004151 : Int)/10^30)
theorem v3162_pb_checked : Scalar.distance (sourceCoefficient 41 47 1 1) v3162_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3162_pg : Scalar.QComplex := ((-93086383776473742557342 : Int)/10^30,(92638096886247552629 : Int)/10^30)
theorem v3162_pg_checked : Scalar.distance (sourceCoefficient 41 47 1 2) v3162_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3162_mb : Scalar.QComplex := ((-801744714949138222191242 : Int)/10^30,(-431476775896509188371043744 : Int)/10^30)
theorem v3162_mb_checked : Scalar.distance (sourceCoefficient 41 47 3 1) v3162_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3162_mg : Scalar.QComplex := ((-93086269173653456843339 : Int)/10^30,(172967419136853107750 : Int)/10^30)
theorem v3162_mg_checked : Scalar.distance (sourceCoefficient 41 47 3 2) v3162_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3162_upper : Scalar.QComplex := ((999996297826024759912568106382 : Int)/10^30,(-2721090635092486572720715839 : Int)/10^30)
theorem v3162_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 47 5) 1) 14) v3162_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3162 : Material (41 : Basis) (47 : Basis) where
  plus := ![v3162_pa,v3162_pb,v3162_pg]
  minus := ![(Primitive.Addresses.material3162 1).one,v3162_mb,v3162_mg]
  upper := v3162_upper
  lower := (Primitive.Addresses.material3162 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3162_pa_checked.trans (by decide +kernel)
    · exact v3162_pb_checked.trans (by decide +kernel)
    · exact v3162_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 47 Primitive.Addresses.material3162
    · exact v3162_mb_checked.trans (by decide +kernel)
    · exact v3162_mg_checked.trans (by decide +kernel)
  upper_error := v3162_upper_checked
  lower_error := reuse_lower_error 41 47 Primitive.Addresses.material3162

def v3163_pa : Scalar.QComplex := ((999999477129916145094593266189 : Int)/10^30,(-1022614245117231986152347552 : Int)/10^30)
theorem v3163_pa_checked : Scalar.distance (sourceCoefficient 41 48 1 0) v3163_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3163_pb : Scalar.QComplex := ((-441235058908394890749946 : Int)/10^30,(-431477294890606280703349958 : Int)/10^30)
theorem v3163_pb_checked : Scalar.distance (sourceCoefficient 41 48 1 1) v3163_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3163_pg : Scalar.QComplex := ((-93086381170569639812102 : Int)/10^30,(95191509184229379218 : Int)/10^30)
theorem v3163_pg_checked : Scalar.distance (sourceCoefficient 41 48 1 2) v3163_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3163_mb : Scalar.QComplex := ((-813580367091035830193117 : Int)/10^30,(-431476753465906557798693843 : Int)/10^30)
theorem v3163_mb_checked : Scalar.distance (sourceCoefficient 41 48 3 1) v3163_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3163_mg : Scalar.QComplex := ((-93086264364270512657824 : Int)/10^30,(175520828235304963988 : Int)/10^30)
theorem v3163_mg_checked : Scalar.distance (sourceCoefficient 41 48 3 2) v3163_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3163_upper : Scalar.QComplex := ((999996222808746917647079991448 : Int)/10^30,(-2748521100335768475284562338 : Int)/10^30)
theorem v3163_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 48 5) 1) 14) v3163_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3163 : Material (41 : Basis) (48 : Basis) where
  plus := ![v3163_pa,v3163_pb,v3163_pg]
  minus := ![(Primitive.Addresses.material3163 1).one,v3163_mb,v3163_mg]
  upper := v3163_upper
  lower := (Primitive.Addresses.material3163 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3163_pa_checked.trans (by decide +kernel)
    · exact v3163_pb_checked.trans (by decide +kernel)
    · exact v3163_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 48 Primitive.Addresses.material3163
    · exact v3163_mb_checked.trans (by decide +kernel)
    · exact v3163_mg_checked.trans (by decide +kernel)
  upper_error := v3163_upper_checked
  lower_error := reuse_lower_error 41 48 Primitive.Addresses.material3163

def v3164_pa : Scalar.QComplex := ((999999454350305602973905444093 : Int)/10^30,(-1044652617409473202121971314 : Int)/10^30)
theorem v3164_pa_checked : Scalar.distance (sourceCoefficient 41 49 1 0) v3164_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3164_pb : Scalar.QComplex := ((-450744120827332126880753 : Int)/10^30,(-431477284761602201353166499 : Int)/10^30)
theorem v3164_pb_checked : Scalar.distance (sourceCoefficient 41 49 1 1) v3164_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3164_pg : Scalar.QComplex := ((-93086379017723886754445 : Int)/10^30,(97242982546639234201 : Int)/10^30)
theorem v3164_pg_checked : Scalar.distance (sourceCoefficient 41 49 1 2) v3164_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3164_mb : Scalar.QComplex := ((-823089416728440401234762 : Int)/10^30,(-431476735131014086147428388 : Int)/10^30)
theorem v3164_mb_checked : Scalar.distance (sourceCoefficient 41 49 3 1) v3164_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3164_mg : Scalar.QComplex := ((-93086260441096444373708 : Int)/10^30,(177572298976048604866 : Int)/10^30)
theorem v3164_mg_checked : Scalar.distance (sourceCoefficient 41 49 3 2) v3164_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3164_upper : Scalar.QComplex := ((999996161992939032188709372260 : Int)/10^30,(-2770559400488901725449330016 : Int)/10^30)
theorem v3164_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 49 5) 1) 14) v3164_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3164 : Material (41 : Basis) (49 : Basis) where
  plus := ![v3164_pa,v3164_pb,v3164_pg]
  minus := ![(Primitive.Addresses.material3164 1).one,v3164_mb,v3164_mg]
  upper := v3164_upper
  lower := (Primitive.Addresses.material3164 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3164_pa_checked.trans (by decide +kernel)
    · exact v3164_pb_checked.trans (by decide +kernel)
    · exact v3164_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 49 Primitive.Addresses.material3164
    · exact v3164_mb_checked.trans (by decide +kernel)
    · exact v3164_mg_checked.trans (by decide +kernel)
  upper_error := v3164_upper_checked
  lower_error := reuse_lower_error 41 49 Primitive.Addresses.material3164

def v3165_pa : Scalar.QComplex := ((999999451656715426493528965257 : Int)/10^30,(-1047227897101034644323354312 : Int)/10^30)
theorem v3165_pa_checked : Scalar.distance (sourceCoefficient 41 50 1 0) v3165_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3165_pb : Scalar.QComplex := ((-451855296080961644221526 : Int)/10^30,(-431477283559750591111960276 : Int)/10^30)
theorem v3165_pb_checked : Scalar.distance (sourceCoefficient 41 50 1 1) v3165_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3165_pg : Scalar.QComplex := ((-93086378762712545842161 : Int)/10^30,(97482706134413141425 : Int)/10^30)
theorem v3165_pg_checked : Scalar.distance (sourceCoefficient 41 50 1 2) v3165_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3165_mb : Scalar.QComplex := ((-824200590531184778180420 : Int)/10^30,(-431476732970268725003878616 : Int)/10^30)
theorem v3165_mb_checked : Scalar.distance (sourceCoefficient 41 50 3 1) v3165_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3165_mg : Scalar.QComplex := ((-93086259979214538914519 : Int)/10^30,(177812022254499162530 : Int)/10^30)
theorem v3165_mg_checked : Scalar.distance (sourceCoefficient 41 50 3 2) v3165_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3165_upper : Scalar.QComplex := ((999996154854653747408060389728 : Int)/10^30,(-2773134671695994296659777548 : Int)/10^30)
theorem v3165_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 50 5) 1) 14) v3165_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3165 : Material (41 : Basis) (50 : Basis) where
  plus := ![v3165_pa,v3165_pb,v3165_pg]
  minus := ![(Primitive.Addresses.material3165 1).one,v3165_mb,v3165_mg]
  upper := v3165_upper
  lower := (Primitive.Addresses.material3165 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3165_pa_checked.trans (by decide +kernel)
    · exact v3165_pb_checked.trans (by decide +kernel)
    · exact v3165_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 50 Primitive.Addresses.material3165
    · exact v3165_mb_checked.trans (by decide +kernel)
    · exact v3165_mg_checked.trans (by decide +kernel)
  upper_error := v3165_upper_checked
  lower_error := reuse_lower_error 41 50 Primitive.Addresses.material3165

def v3166_pa : Scalar.QComplex := ((999999439759988578999953328579 : Int)/10^30,(-1058527141349304135234528241 : Int)/10^30)
theorem v3166_pa_checked : Scalar.distance (sourceCoefficient 41 51 1 0) v3166_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3166_pb : Scalar.QComplex := ((-456730665772878413928337 : Int)/10^30,(-431477278241435481020422101 : Int)/10^30)
theorem v3166_pb_checked : Scalar.distance (sourceCoefficient 41 51 1 1) v3166_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3166_pg : Scalar.QComplex := ((-93086377635317249571344 : Int)/10^30,(98534512419850528918 : Int)/10^30)
theorem v3166_pg_checked : Scalar.distance (sourceCoefficient 41 51 1 2) v3166_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3166_mb : Scalar.QComplex := ((-829075953818312184196256 : Int)/10^30,(-431476723444731129539729551 : Int)/10^30)
theorem v3166_mb_checked : Scalar.distance (sourceCoefficient 41 51 3 1) v3166_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3166_mg : Scalar.QComplex := ((-93086257944158209688608 : Int)/10^30,(178863827175409635351 : Int)/10^30)
theorem v3166_mg_checked : Scalar.distance (sourceCoefficient 41 51 3 2) v3166_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3166_upper : Scalar.QComplex := ((999996123456474105609373241683 : Int)/10^30,(-2784433878582695506095815571 : Int)/10^30)
theorem v3166_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 51 5) 1) 14) v3166_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3166 : Material (41 : Basis) (51 : Basis) where
  plus := ![v3166_pa,v3166_pb,v3166_pg]
  minus := ![(Primitive.Addresses.material3166 1).one,v3166_mb,v3166_mg]
  upper := v3166_upper
  lower := (Primitive.Addresses.material3166 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3166_pa_checked.trans (by decide +kernel)
    · exact v3166_pb_checked.trans (by decide +kernel)
    · exact v3166_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 51 Primitive.Addresses.material3166
    · exact v3166_mb_checked.trans (by decide +kernel)
    · exact v3166_mg_checked.trans (by decide +kernel)
  upper_error := v3166_upper_checked
  lower_error := reuse_lower_error 41 51 Primitive.Addresses.material3166

def v3167_pa : Scalar.QComplex := ((999999413862795366086568754724 : Int)/10^30,(-1082716059597808037626542825 : Int)/10^30)
theorem v3167_pa_checked : Scalar.distance (sourceCoefficient 41 52 1 0) v3167_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3167_pb : Scalar.QComplex := ((-467167639733585657496039 : Int)/10^30,(-431477266609297267841509684 : Int)/10^30)
theorem v3167_pb_checked : Scalar.distance (sourceCoefficient 41 52 1 1) v3167_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3167_pg : Scalar.QComplex := ((-93086375175227021291338 : Int)/10^30,(100786172406490378288 : Int)/10^30)
theorem v3167_pg_checked : Scalar.distance (sourceCoefficient 41 52 1 2) v3167_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3167_mb : Scalar.QComplex := ((-839512913854845643002634 : Int)/10^30,(-431476702805958783304737315 : Int)/10^30)
theorem v3167_mb_checked : Scalar.distance (sourceCoefficient 41 52 3 1) v3167_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3167_mg : Scalar.QComplex := ((-93086253540987739943682 : Int)/10^30,(181115484200706497095 : Int)/10^30)
theorem v3167_mg_checked : Scalar.distance (sourceCoefficient 41 52 3 2) v3167_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3167_upper : Scalar.QComplex := ((999996055811440968127226059290 : Int)/10^30,(-2808622716108440996805766680 : Int)/10^30)
theorem v3167_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 52 5) 1) 14) v3167_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3167 : Material (41 : Basis) (52 : Basis) where
  plus := ![v3167_pa,v3167_pb,v3167_pg]
  minus := ![(Primitive.Addresses.material3167 1).one,v3167_mb,v3167_mg]
  upper := v3167_upper
  lower := (Primitive.Addresses.material3167 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3167_pa_checked.trans (by decide +kernel)
    · exact v3167_pb_checked.trans (by decide +kernel)
    · exact v3167_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 52 Primitive.Addresses.material3167
    · exact v3167_mb_checked.trans (by decide +kernel)
    · exact v3167_mg_checked.trans (by decide +kernel)
  upper_error := v3167_upper_checked
  lower_error := reuse_lower_error 41 52 Primitive.Addresses.material3167

def v3168_pa : Scalar.QComplex := ((999999409846978619581281715293 : Int)/10^30,(-1086418747297858806666810105 : Int)/10^30)
theorem v3168_pa_checked : Scalar.distance (sourceCoefficient 41 53 1 0) v3168_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3168_pb : Scalar.QComplex := ((-468765266153691225808358 : Int)/10^30,(-431477264799015644944918192 : Int)/10^30)
theorem v3168_pb_checked : Scalar.distance (sourceCoefficient 41 53 1 1) v3168_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3168_pg : Scalar.QComplex := ((-93086374793044033508165 : Int)/10^30,(101130842375830062556 : Int)/10^30)
theorem v3168_pg_checked : Scalar.distance (sourceCoefficient 41 53 1 2) v3168_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3168_mb : Scalar.QComplex := ((-841110538117890371473155 : Int)/10^30,(-431476699616998188330510353 : Int)/10^30)
theorem v3168_mb_checked : Scalar.distance (sourceCoefficient 41 53 3 1) v3168_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3168_mg : Scalar.QComplex := ((-93086252861370234283719 : Int)/10^30,(181460153711903094007 : Int)/10^30)
theorem v3168_mg_checked : Scalar.distance (sourceCoefficient 41 53 3 2) v3168_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3168_upper : Scalar.QComplex := ((999996045405127137625825752207 : Int)/10^30,(-2812325391362837992452377594 : Int)/10^30)
theorem v3168_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 53 5) 1) 14) v3168_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3168 : Material (41 : Basis) (53 : Basis) where
  plus := ![v3168_pa,v3168_pb,v3168_pg]
  minus := ![(Primitive.Addresses.material3168 1).one,v3168_mb,v3168_mg]
  upper := v3168_upper
  lower := (Primitive.Addresses.material3168 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3168_pa_checked.trans (by decide +kernel)
    · exact v3168_pb_checked.trans (by decide +kernel)
    · exact v3168_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 53 Primitive.Addresses.material3168
    · exact v3168_mb_checked.trans (by decide +kernel)
    · exact v3168_mg_checked.trans (by decide +kernel)
  upper_error := v3168_upper_checked
  lower_error := reuse_lower_error 41 53 Primitive.Addresses.material3168

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
