import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B010

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v241_pa : Scalar.QComplex := ((999985980716425489771079456417 : Int)/10^30,(5295127062565025484223837019 : Int)/10^30)
theorem v241_pa_checked : Scalar.distance (sourceCoefficient 2 51 1 0) v241_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v241_pb : Scalar.QComplex := ((2284712342196820608668386 : Int)/10^30,(-431468458673753066815149025 : Int)/10^30)
theorem v241_pb_checked : Scalar.distance (sourceCoefficient 2 51 1 1) v241_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v241_pg : Scalar.QComplex := ((-93084799846591454149343 : Int)/10^30,(-492902752924603048193 : Int)/10^30)
theorem v241_pg_checked : Scalar.distance (sourceCoefficient 2 51 1 2) v241_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v241_mb : Scalar.QComplex := ((1912373644276556176849193 : Int)/10^30,(-431470269622178511650279992 : Int)/10^30)
theorem v241_mb_checked : Scalar.distance (sourceCoefficient 2 51 3 1) v241_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v241_mg : Scalar.QComplex := ((-93085190539742543774800 : Int)/10^30,(-412574579510529430830 : Int)/10^30)
theorem v241_mg_checked : Scalar.distance (sourceCoefficient 2 51 3 2) v241_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v241_upper : Scalar.QComplex := ((999993630263713630093165786049 : Int)/10^30,(3569234091398245032028852900 : Int)/10^30)
theorem v241_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 51 5) 1) 14) v241_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material241 : Material (2 : Basis) (51 : Basis) where
  plus := ![v241_pa,v241_pb,v241_pg]
  minus := ![(Primitive.Addresses.material241 1).one,v241_mb,v241_mg]
  upper := v241_upper
  lower := (Primitive.Addresses.material241 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v241_pa_checked.trans (by decide +kernel)
    · exact v241_pb_checked.trans (by decide +kernel)
    · exact v241_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 51 Primitive.Addresses.material241
    · exact v241_mb_checked.trans (by decide +kernel)
    · exact v241_mg_checked.trans (by decide +kernel)
  upper_error := v241_upper_checked
  lower_error := reuse_lower_error 2 51 Primitive.Addresses.material241

def v242_pa : Scalar.QComplex := ((999986108507346401870671292757 : Int)/10^30,(5270938468017636960073256456 : Int)/10^30)
theorem v242_pa_checked : Scalar.distance (sourceCoefficient 2 52 1 0) v242_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v242_pb : Scalar.QComplex := ((2274275461349051002718754 : Int)/10^30,(-431468491250195641883061097 : Int)/10^30)
theorem v242_pb_checked : Scalar.distance (sourceCoefficient 2 52 1 1) v242_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v242_pg : Scalar.QComplex := ((-93084809308389200005316 : Int)/10^30,(-490651118048076687055 : Int)/10^30)
theorem v242_pg_checked : Scalar.distance (sourceCoefficient 2 52 1 2) v242_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v242_mb : Scalar.QComplex := ((1901936739202911545768040 : Int)/10^30,(-431470293192050845058583057 : Int)/10^30)
theorem v242_mb_checked : Scalar.distance (sourceCoefficient 2 52 3 1) v242_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v242_mg : Scalar.QComplex := ((-93085198058477277999125 : Int)/10^30,(-410322937307284327898 : Int)/10^30)
theorem v242_mg_checked : Scalar.distance (sourceCoefficient 2 52 3 2) v242_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v242_upper : Scalar.QComplex := ((999993716307124395990686931235 : Int)/10^30,(3545045312321390301801956094 : Int)/10^30)
theorem v242_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 52 5) 1) 14) v242_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material242 : Material (2 : Basis) (52 : Basis) where
  plus := ![v242_pa,v242_pb,v242_pg]
  minus := ![(Primitive.Addresses.material242 1).one,v242_mb,v242_mg]
  upper := v242_upper
  lower := (Primitive.Addresses.material242 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v242_pa_checked.trans (by decide +kernel)
    · exact v242_pb_checked.trans (by decide +kernel)
    · exact v242_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 52 Primitive.Addresses.material242
    · exact v242_mb_checked.trans (by decide +kernel)
    · exact v242_mg_checked.trans (by decide +kernel)
  upper_error := v242_upper_checked
  lower_error := reuse_lower_error 2 52 Primitive.Addresses.material242

def v243_pa : Scalar.QComplex := ((999986128017142052739874987364 : Int)/10^30,(5267235829539637108595008394 : Int)/10^30)
theorem v243_pa_checked : Scalar.distance (sourceCoefficient 2 53 1 0) v243_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v243_pb : Scalar.QComplex := ((2272677849087715498750580 : Int)/10^30,(-431468496207086175212140874 : Int)/10^30)
theorem v243_pb_checked : Scalar.distance (sourceCoefficient 2 53 1 1) v243_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v243_pg : Scalar.QComplex := ((-93084810751134025058277 : Int)/10^30,(-490306451896985413220 : Int)/10^30)
theorem v243_pg_checked : Scalar.distance (sourceCoefficient 2 53 1 2) v243_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v243_mb : Scalar.QComplex := ((1900339123258866820981599 : Int)/10^30,(-431470296770272104963436752 : Int)/10^30)
theorem v243_mb_checked : Scalar.distance (sourceCoefficient 2 53 3 1) v243_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v243_mg : Scalar.QComplex := ((-93085199203790200647679 : Int)/10^30,(-409978270039504208931 : Int)/10^30)
theorem v243_mg_checked : Scalar.distance (sourceCoefficient 2 53 3 2) v243_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v243_upper : Scalar.QComplex := ((999993729426472877022118161764 : Int)/10^30,(3541342645685898142271204251 : Int)/10^30)
theorem v243_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 53 5) 1) 14) v243_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material243 : Material (2 : Basis) (53 : Basis) where
  plus := ![v243_pa,v243_pb,v243_pg]
  minus := ![(Primitive.Addresses.material243 1).one,v243_mb,v243_mg]
  upper := v243_upper
  lower := (Primitive.Addresses.material243 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v243_pa_checked.trans (by decide +kernel)
    · exact v243_pb_checked.trans (by decide +kernel)
    · exact v243_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 53 Primitive.Addresses.material243
    · exact v243_mb_checked.trans (by decide +kernel)
    · exact v243_mg_checked.trans (by decide +kernel)
  upper_error := v243_upper_checked
  lower_error := reuse_lower_error 2 53 Primitive.Addresses.material243

def v244_pa : Scalar.QComplex := ((999986137930783671574493213615 : Int)/10^30,(5265353385642210884387911210 : Int)/10^30)
theorem v244_pa_checked : Scalar.distance (sourceCoefficient 2 54 1 0) v244_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v244_pb : Scalar.QComplex := ((2271865613313679137406577 : Int)/10^30,(-431468498724175076542457405 : Int)/10^30)
theorem v244_pb_checked : Scalar.distance (sourceCoefficient 2 54 1 1) v244_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v244_pg : Scalar.QComplex := ((-93084811484063344465112 : Int)/10^30,(-490131221532397849140 : Int)/10^30)
theorem v244_pg_checked : Scalar.distance (sourceCoefficient 2 54 1 2) v244_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v244_mb : Scalar.QComplex := ((1899526885615128602947750 : Int)/10^30,(-431470298586437177814423361 : Int)/10^30)
theorem v244_mb_checked : Scalar.distance (sourceCoefficient 2 54 3 1) v244_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v244_mg : Scalar.QComplex := ((-93085199785503334595017 : Int)/10^30,(-409803039107677925273 : Int)/10^30)
theorem v244_mg_checked : Scalar.distance (sourceCoefficient 2 54 3 2) v244_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v244_upper : Scalar.QComplex := ((999993736091172337670781713511 : Int)/10^30,(3539460187482104900320630384 : Int)/10^30)
theorem v244_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 54 5) 1) 14) v244_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material244 : Material (2 : Basis) (54 : Basis) where
  plus := ![v244_pa,v244_pb,v244_pg]
  minus := ![(Primitive.Addresses.material244 1).one,v244_mb,v244_mg]
  upper := v244_upper
  lower := (Primitive.Addresses.material244 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v244_pa_checked.trans (by decide +kernel)
    · exact v244_pb_checked.trans (by decide +kernel)
    · exact v244_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 54 Primitive.Addresses.material244
    · exact v244_mb_checked.trans (by decide +kernel)
    · exact v244_mg_checked.trans (by decide +kernel)
  upper_error := v244_upper_checked
  lower_error := reuse_lower_error 2 54 Primitive.Addresses.material244

def v245_pa : Scalar.QComplex := ((999986218602527636236824658472 : Int)/10^30,(5250010001686781079799584272 : Int)/10^30)
theorem v245_pa_checked : Scalar.distance (sourceCoefficient 2 55 1 0) v245_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v245_pb : Scalar.QComplex := ((2265245259271272245889085 : Int)/10^30,(-431468519164380430918181836 : Int)/10^30)
theorem v245_pb_checked : Scalar.distance (sourceCoefficient 2 55 1 1) v245_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v245_pg : Scalar.QComplex := ((-93084817443655875006314 : Int)/10^30,(-488702957594086013055 : Int)/10^30)
theorem v245_pg_checked : Scalar.distance (sourceCoefficient 2 55 1 2) v245_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v245_mb : Scalar.QComplex := ((1892906516398805458394007 : Int)/10^30,(-431470313313567552447874741 : Int)/10^30)
theorem v245_mb_checked : Scalar.distance (sourceCoefficient 2 55 3 1) v245_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v245_mg : Scalar.QComplex := ((-93085204512566193964303 : Int)/10^30,(-408374770558314084534 : Int)/10^30)
theorem v245_mg_checked : Scalar.distance (sourceCoefficient 2 55 3 2) v245_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v245_upper : Scalar.QComplex := ((999993790281507385094194636446 : Int)/10^30,(3524116687146731537293108495 : Int)/10^30)
theorem v245_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 55 5) 1) 14) v245_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material245 : Material (2 : Basis) (55 : Basis) where
  plus := ![v245_pa,v245_pb,v245_pg]
  minus := ![(Primitive.Addresses.material245 1).one,v245_mb,v245_mg]
  upper := v245_upper
  lower := (Primitive.Addresses.material245 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v245_pa_checked.trans (by decide +kernel)
    · exact v245_pb_checked.trans (by decide +kernel)
    · exact v245_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 55 Primitive.Addresses.material245
    · exact v245_mb_checked.trans (by decide +kernel)
    · exact v245_mg_checked.trans (by decide +kernel)
  upper_error := v245_upper_checked
  lower_error := reuse_lower_error 2 55 Primitive.Addresses.material245

def v246_pa : Scalar.QComplex := ((999986237713619622664065499385 : Int)/10^30,(5246368587911857375343704785 : Int)/10^30)
theorem v246_pa_checked : Scalar.distance (sourceCoefficient 2 56 1 0) v246_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v246_pb : Scalar.QComplex := ((2263674064293565053335313 : Int)/10^30,(-431468523995525870733318794 : Int)/10^30)
theorem v246_pb_checked : Scalar.distance (sourceCoefficient 2 56 1 1) v246_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v246_pg : Scalar.QComplex := ((-93084818854279707409071 : Int)/10^30,(-488363990653655705598 : Int)/10^30)
theorem v246_pg_checked : Scalar.distance (sourceCoefficient 2 56 1 2) v246_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v246_mb : Scalar.QComplex := ((1891335317837065035351397 : Int)/10^30,(-431470316788840691640375990 : Int)/10^30)
theorem v246_mb_checked : Scalar.distance (sourceCoefficient 2 56 3 1) v246_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v246_mg : Scalar.QComplex := ((-93085205630676298040262 : Int)/10^30,(-408035802526791825329 : Int)/10^30)
theorem v246_mg_checked : Scalar.distance (sourceCoefficient 2 56 3 2) v246_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v246_upper : Scalar.QComplex := ((999993803107821078753690380902 : Int)/10^30,(3520475245811254876224570249 : Int)/10^30)
theorem v246_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 56 5) 1) 14) v246_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material246 : Material (2 : Basis) (56 : Basis) where
  plus := ![v246_pa,v246_pb,v246_pg]
  minus := ![(Primitive.Addresses.material246 1).one,v246_mb,v246_mg]
  upper := v246_upper
  lower := (Primitive.Addresses.material246 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v246_pa_checked.trans (by decide +kernel)
    · exact v246_pb_checked.trans (by decide +kernel)
    · exact v246_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 56 Primitive.Addresses.material246
    · exact v246_mb_checked.trans (by decide +kernel)
    · exact v246_mg_checked.trans (by decide +kernel)
  upper_error := v246_upper_checked
  lower_error := reuse_lower_error 2 56 Primitive.Addresses.material246

def v247_pa : Scalar.QComplex := ((999986299435237235050328985162 : Int)/10^30,(5234590893284314785738804216 : Int)/10^30)
theorem v247_pa_checked : Scalar.distance (sourceCoefficient 2 57 1 0) v247_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v247_pb : Scalar.QComplex := ((2258592231955811589007928 : Int)/10^30,(-431468539569018066374293308 : Int)/10^30)
theorem v247_pb_checked : Scalar.distance (sourceCoefficient 2 57 1 1) v247_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v247_pg : Scalar.QComplex := ((-93084823406903569345253 : Int)/10^30,(-487267644750679755679 : Int)/10^30)
theorem v247_pg_checked : Scalar.distance (sourceCoefficient 2 57 1 2) v247_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v247_mb : Scalar.QComplex := ((1886253473952287640793893 : Int)/10^30,(-431470327976934658309392783 : Int)/10^30)
theorem v247_mb_checked : Scalar.distance (sourceCoefficient 2 57 3 1) v247_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v247_mg : Scalar.QComplex := ((-93085209237201328144758 : Int)/10^30,(-406939453103326210288 : Int)/10^30)
theorem v247_mg_checked : Scalar.distance (sourceCoefficient 2 57 3 2) v247_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v247_upper : Scalar.QComplex := ((999993844502114301012568142711 : Int)/10^30,(3508697462199292271578916499 : Int)/10^30)
theorem v247_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 57 5) 1) 14) v247_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material247 : Material (2 : Basis) (57 : Basis) where
  plus := ![v247_pa,v247_pb,v247_pg]
  minus := ![(Primitive.Addresses.material247 1).one,v247_mb,v247_mg]
  upper := v247_upper
  lower := (Primitive.Addresses.material247 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v247_pa_checked.trans (by decide +kernel)
    · exact v247_pb_checked.trans (by decide +kernel)
    · exact v247_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 57 Primitive.Addresses.material247
    · exact v247_mb_checked.trans (by decide +kernel)
    · exact v247_mg_checked.trans (by decide +kernel)
  upper_error := v247_upper_checked
  lower_error := reuse_lower_error 2 57 Primitive.Addresses.material247

def v248_pa : Scalar.QComplex := ((999986332866734300098078742804 : Int)/10^30,(5228200430441444107131680235 : Int)/10^30)
theorem v248_pa_checked : Scalar.distance (sourceCoefficient 2 58 1 0) v248_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v248_pb : Scalar.QComplex := ((2255834879096414681713930 : Int)/10^30,(-431468547985645494671213299 : Int)/10^30)
theorem v248_pb_checked : Scalar.distance (sourceCoefficient 2 58 1 1) v248_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v248_pg : Scalar.QComplex := ((-93084825870808432899177 : Int)/10^30,(-486672778107042698525 : Int)/10^30)
theorem v248_pg_checked : Scalar.distance (sourceCoefficient 2 58 1 2) v248_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v248_mb : Scalar.QComplex := ((1883496114856408820511775 : Int)/10^30,(-431470334014087621614496679 : Int)/10^30)
theorem v248_mb_checked : Scalar.distance (sourceCoefficient 2 58 3 1) v248_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v248_mg : Scalar.QComplex := ((-93085211187762152614586 : Int)/10^30,(-406344584554946264217 : Int)/10^30)
theorem v248_mg_checked : Scalar.distance (sourceCoefficient 2 58 3 2) v248_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v248_upper : Scalar.QComplex := ((999993866904202445238226210963 : Int)/10^30,(3502306951174534268379750034 : Int)/10^30)
theorem v248_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 58 5) 1) 14) v248_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material248 : Material (2 : Basis) (58 : Basis) where
  plus := ![v248_pa,v248_pb,v248_pg]
  minus := ![(Primitive.Addresses.material248 1).one,v248_mb,v248_mg]
  upper := v248_upper
  lower := (Primitive.Addresses.material248 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v248_pa_checked.trans (by decide +kernel)
    · exact v248_pb_checked.trans (by decide +kernel)
    · exact v248_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 58 Primitive.Addresses.material248
    · exact v248_mb_checked.trans (by decide +kernel)
    · exact v248_mg_checked.trans (by decide +kernel)
  upper_error := v248_upper_checked
  lower_error := reuse_lower_error 2 58 Primitive.Addresses.material248

def v249_pa : Scalar.QComplex := ((999986424550642728525059697133 : Int)/10^30,(5210634742689003531158368753 : Int)/10^30)
theorem v249_pa_checked : Scalar.distance (sourceCoefficient 2 59 1 0) v249_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v249_pb : Scalar.QComplex := ((2248255647509956289350544 : Int)/10^30,(-431468570999672643979789337 : Int)/10^30)
theorem v249_pb_checked : Scalar.distance (sourceCoefficient 2 59 1 1) v249_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v249_pg : Scalar.QComplex := ((-93084832620578716484579 : Int)/10^30,(-485037647474197798700 : Int)/10^30)
theorem v249_pg_checked : Scalar.distance (sourceCoefficient 2 59 1 2) v249_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v249_mb : Scalar.QComplex := ((1875916866231975819234585 : Int)/10^30,(-431470350487570698554306155 : Int)/10^30)
theorem v249_mb_checked : Scalar.distance (sourceCoefficient 2 59 3 1) v249_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v249_mg : Scalar.QComplex := ((-93085216526485830356809 : Int)/10^30,(-404709448706187471796 : Int)/10^30)
theorem v249_mg_checked : Scalar.distance (sourceCoefficient 2 59 3 2) v249_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v249_upper : Scalar.QComplex := ((999993928271190807285914695604 : Int)/10^30,(3484741131346013740771503256 : Int)/10^30)
theorem v249_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 59 5) 1) 14) v249_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material249 : Material (2 : Basis) (59 : Basis) where
  plus := ![v249_pa,v249_pb,v249_pg]
  minus := ![(Primitive.Addresses.material249 1).one,v249_mb,v249_mg]
  upper := v249_upper
  lower := (Primitive.Addresses.material249 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v249_pa_checked.trans (by decide +kernel)
    · exact v249_pb_checked.trans (by decide +kernel)
    · exact v249_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 59 Primitive.Addresses.material249
    · exact v249_mb_checked.trans (by decide +kernel)
    · exact v249_mg_checked.trans (by decide +kernel)
  upper_error := v249_upper_checked
  lower_error := reuse_lower_error 2 59 Primitive.Addresses.material249

def v250_pa : Scalar.QComplex := ((999986529933270798830334969899 : Int)/10^30,(5190371086512471142559508143 : Int)/10^30)
theorem v250_pa_checked : Scalar.distance (sourceCoefficient 2 60 1 0) v250_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v250_pb : Scalar.QComplex := ((2239512298689372606770157 : Int)/10^30,(-431468597327985575397593117 : Int)/10^30)
theorem v250_pb_checked : Scalar.distance (sourceCoefficient 2 60 1 1) v250_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v250_pg : Scalar.QComplex := ((-93084840365441007939057 : Int)/10^30,(-483151372106636557242 : Int)/10^30)
theorem v250_pg_checked : Scalar.distance (sourceCoefficient 2 60 1 2) v250_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v250_mb : Scalar.QComplex := ((1867173497946792216721313 : Int)/10^30,(-431470369270757580387086748 : Int)/10^30)
theorem v250_mb_checked : Scalar.distance (sourceCoefficient 2 60 3 1) v250_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v250_mg : Scalar.QComplex := ((-93085222643574550528636 : Int)/10^30,(-402823167357505414848 : Int)/10^30)
theorem v250_mg_checked : Scalar.distance (sourceCoefficient 2 60 3 2) v250_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v250_upper : Scalar.QComplex := ((999993998680429666379177705012 : Int)/10^30,(3464477323468961078844794511 : Int)/10^30)
theorem v250_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 60 5) 1) 14) v250_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material250 : Material (2 : Basis) (60 : Basis) where
  plus := ![v250_pa,v250_pb,v250_pg]
  minus := ![(Primitive.Addresses.material250 1).one,v250_mb,v250_mg]
  upper := v250_upper
  lower := (Primitive.Addresses.material250 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v250_pa_checked.trans (by decide +kernel)
    · exact v250_pb_checked.trans (by decide +kernel)
    · exact v250_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 60 Primitive.Addresses.material250
    · exact v250_mb_checked.trans (by decide +kernel)
    · exact v250_mg_checked.trans (by decide +kernel)
  upper_error := v250_upper_checked
  lower_error := reuse_lower_error 2 60 Primitive.Addresses.material250

def v251_pa : Scalar.QComplex := ((999986560328231136034403758252 : Int)/10^30,(5184511829762825065571636951 : Int)/10^30)
theorem v251_pa_checked : Scalar.distance (sourceCoefficient 2 61 1 0) v251_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v251_pb : Scalar.QComplex := ((2236984150591532168896518 : Int)/10^30,(-431468604896814288071184132 : Int)/10^30)
theorem v251_pb_checked : Scalar.distance (sourceCoefficient 2 61 1 1) v251_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v251_pg : Scalar.QComplex := ((-93084842596564222667194 : Int)/10^30,(-482605953679108885124 : Int)/10^30)
theorem v251_pg_checked : Scalar.distance (sourceCoefficient 2 61 1 2) v251_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v251_mb : Scalar.QComplex := ((1864645344258738566103211 : Int)/10^30,(-431470374657905529967050162 : Int)/10^30)
theorem v251_mb_checked : Scalar.distance (sourceCoefficient 2 61 3 1) v251_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v251_mg : Scalar.QComplex := ((-93085224404025396285342 : Int)/10^30,(-402277747207703101901 : Int)/10^30)
theorem v251_mg_checked : Scalar.distance (sourceCoefficient 2 61 3 2) v251_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v251_upper : Scalar.QComplex := ((999994018962799131591243949087 : Int)/10^30,(3458618022987045521056013489 : Int)/10^30)
theorem v251_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 61 5) 1) 14) v251_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material251 : Material (2 : Basis) (61 : Basis) where
  plus := ![v251_pa,v251_pb,v251_pg]
  minus := ![(Primitive.Addresses.material251 1).one,v251_mb,v251_mg]
  upper := v251_upper
  lower := (Primitive.Addresses.material251 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v251_pa_checked.trans (by decide +kernel)
    · exact v251_pb_checked.trans (by decide +kernel)
    · exact v251_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 61 Primitive.Addresses.material251
    · exact v251_mb_checked.trans (by decide +kernel)
    · exact v251_mg_checked.trans (by decide +kernel)
  upper_error := v251_upper_checked
  lower_error := reuse_lower_error 2 61 Primitive.Addresses.material251

def v252_pa : Scalar.QComplex := ((999986604429625389644347955130 : Int)/10^30,(5175998580748940870546449408 : Int)/10^30)
theorem v252_pa_checked : Scalar.distance (sourceCoefficient 2 62 1 0) v252_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v252_pb : Scalar.QComplex := ((2233310859795653794786280 : Int)/10^30,(-431468615858800822887773118 : Int)/10^30)
theorem v252_pb_checked : Scalar.distance (sourceCoefficient 2 62 1 1) v252_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v252_pg : Scalar.QComplex := ((-93084845831646392977253 : Int)/10^30,(-481813484080269128036 : Int)/10^30)
theorem v252_pg_checked : Scalar.distance (sourceCoefficient 2 62 1 2) v252_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v252_mb : Scalar.QComplex := ((1860972045370893562980641 : Int)/10^30,(-431470382450003465168094449 : Int)/10^30)
theorem v252_mb_checked : Scalar.distance (sourceCoefficient 2 62 3 1) v252_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v252_mg : Scalar.QComplex := ((-93085226955240789733548 : Int)/10^30,(-401485275112205783825 : Int)/10^30)
theorem v252_mg_checked : Scalar.distance (sourceCoefficient 2 62 3 2) v252_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v252_upper : Scalar.QComplex := ((999994048371032219308379168488 : Int)/10^30,(3450104710537640061236452825 : Int)/10^30)
theorem v252_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 62 5) 1) 14) v252_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material252 : Material (2 : Basis) (62 : Basis) where
  plus := ![v252_pa,v252_pb,v252_pg]
  minus := ![(Primitive.Addresses.material252 1).one,v252_mb,v252_mg]
  upper := v252_upper
  lower := (Primitive.Addresses.material252 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v252_pa_checked.trans (by decide +kernel)
    · exact v252_pb_checked.trans (by decide +kernel)
    · exact v252_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 62 Primitive.Addresses.material252
    · exact v252_mb_checked.trans (by decide +kernel)
    · exact v252_mg_checked.trans (by decide +kernel)
  upper_error := v252_upper_checked
  lower_error := reuse_lower_error 2 62 Primitive.Addresses.material252

def v253_pa : Scalar.QComplex := ((999986732462013710494954197965 : Int)/10^30,(5151203737478725705603003882 : Int)/10^30)
theorem v253_pa_checked : Scalar.distance (sourceCoefficient 2 63 1 0) v253_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v253_pb : Scalar.QComplex := ((2222612398448693482280886 : Int)/10^30,(-431468647548023226919811588 : Int)/10^30)
theorem v253_pb_checked : Scalar.distance (sourceCoefficient 2 63 1 1) v253_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v253_pg : Scalar.QComplex := ((-93084855208978632549212 : Int)/10^30,(-479505415911476998001 : Int)/10^30)
theorem v253_pg_checked : Scalar.distance (sourceCoefficient 2 63 1 2) v253_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v253_mb : Scalar.QComplex := ((1850273560661087648702618 : Int)/10^30,(-431470404906923768239908561 : Int)/10^30)
theorem v253_mb_checked : Scalar.distance (sourceCoefficient 2 63 3 1) v253_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v253_mg : Scalar.QComplex := ((-93085234340810659560001 : Int)/10^30,(-399177199710597533573 : Int)/10^30)
theorem v253_mg_checked : Scalar.distance (sourceCoefficient 2 63 3 2) v253_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v253_upper : Scalar.QComplex := ((999994133609579737175302614705 : Int)/10^30,(3425309683224144106137362655 : Int)/10^30)
theorem v253_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 63 5) 1) 14) v253_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material253 : Material (2 : Basis) (63 : Basis) where
  plus := ![v253_pa,v253_pb,v253_pg]
  minus := ![(Primitive.Addresses.material253 1).one,v253_mb,v253_mg]
  upper := v253_upper
  lower := (Primitive.Addresses.material253 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v253_pa_checked.trans (by decide +kernel)
    · exact v253_pb_checked.trans (by decide +kernel)
    · exact v253_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 63 Primitive.Addresses.material253
    · exact v253_mb_checked.trans (by decide +kernel)
    · exact v253_mg_checked.trans (by decide +kernel)
  upper_error := v253_upper_checked
  lower_error := reuse_lower_error 2 63 Primitive.Addresses.material253

def v254_pa : Scalar.QComplex := ((999986914378727069630245472292 : Int)/10^30,(5115766932960945684878741130 : Int)/10^30)
theorem v254_pa_checked : Scalar.distance (sourceCoefficient 2 64 1 0) v254_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v254_pb : Scalar.QComplex := ((2207322152470638703763405 : Int)/10^30,(-431468692224289577070055178 : Int)/10^30)
theorem v254_pb_checked : Scalar.distance (sourceCoefficient 2 64 1 1) v254_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v254_pg : Scalar.QComplex := ((-93084868495163393731694 : Int)/10^30,(-476206723667408529013 : Int)/10^30)
theorem v254_pg_checked : Scalar.distance (sourceCoefficient 2 64 1 2) v254_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v254_mb : Scalar.QComplex := ((1834983281822684530739929 : Int)/10^30,(-431470436388379851428178930 : Int)/10^30)
theorem v254_mb_checked : Scalar.distance (sourceCoefficient 2 64 3 1) v254_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v254_mg : Scalar.QComplex := ((-93085244780367634641184 : Int)/10^30,(-395878497229403883383 : Int)/10^30)
theorem v254_mg_checked : Scalar.distance (sourceCoefficient 2 64 3 2) v254_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v254_upper : Scalar.QComplex := ((999994254365312356840367496294 : Int)/10^30,(3389872617513577812625384105 : Int)/10^30)
theorem v254_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 64 5) 1) 14) v254_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material254 : Material (2 : Basis) (64 : Basis) where
  plus := ![v254_pa,v254_pb,v254_pg]
  minus := ![(Primitive.Addresses.material254 1).one,v254_mb,v254_mg]
  upper := v254_upper
  lower := (Primitive.Addresses.material254 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v254_pa_checked.trans (by decide +kernel)
    · exact v254_pb_checked.trans (by decide +kernel)
    · exact v254_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 64 Primitive.Addresses.material254
    · exact v254_mb_checked.trans (by decide +kernel)
    · exact v254_mg_checked.trans (by decide +kernel)
  upper_error := v254_upper_checked
  lower_error := reuse_lower_error 2 64 Primitive.Addresses.material254

def v255_pa : Scalar.QComplex := ((999987097728776188560527766384 : Int)/10^30,(5079800781430325555964161974 : Int)/10^30)
theorem v255_pa_checked : Scalar.distance (sourceCoefficient 2 65 1 0) v255_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v255_pb : Scalar.QComplex := ((2191803505750928395730936 : Int)/10^30,(-431468736829180756889890758 : Int)/10^30)
theorem v255_pb_checked : Scalar.distance (sourceCoefficient 2 65 1 1) v255_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v255_pg : Scalar.QComplex := ((-93084881840360846090531 : Int)/10^30,(-472858756463940998790 : Int)/10^30)
theorem v255_pg_checked : Scalar.distance (sourceCoefficient 2 65 1 2) v255_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v255_mb : Scalar.QComplex := ((1819464602389263475186970 : Int)/10^30,(-431470467601361237601097900 : Int)/10^30)
theorem v255_mb_checked : Scalar.distance (sourceCoefficient 2 65 3 1) v255_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v255_mg : Scalar.QComplex := ((-93085255236415208225998 : Int)/10^30,(-392530519756233196667 : Int)/10^30)
theorem v255_mg_checked : Scalar.distance (sourceCoefficient 2 65 3 2) v255_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v255_upper : Scalar.QComplex := ((999994375640773679339031579631 : Int)/10^30,(3353906203104764114878518276 : Int)/10^30)
theorem v255_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 65 5) 1) 14) v255_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material255 : Material (2 : Basis) (65 : Basis) where
  plus := ![v255_pa,v255_pb,v255_pg]
  minus := ![(Primitive.Addresses.material255 1).one,v255_mb,v255_mg]
  upper := v255_upper
  lower := (Primitive.Addresses.material255 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v255_pa_checked.trans (by decide +kernel)
    · exact v255_pb_checked.trans (by decide +kernel)
    · exact v255_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 65 Primitive.Addresses.material255
    · exact v255_mb_checked.trans (by decide +kernel)
    · exact v255_mg_checked.trans (by decide +kernel)
  upper_error := v255_upper_checked
  lower_error := reuse_lower_error 2 65 Primitive.Addresses.material255

def v256_pa : Scalar.QComplex := ((999987186915451082683643168935 : Int)/10^30,(5062213441045228686455904174 : Int)/10^30)
theorem v256_pa_checked : Scalar.distance (sourceCoefficient 2 66 1 0) v256_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v256_pb : Scalar.QComplex := ((2184214934541841688490236 : Int)/10^30,(-431468758369901699050686309 : Int)/10^30)
theorem v256_pb_checked : Scalar.distance (sourceCoefficient 2 66 1 1) v256_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v256_pg : Scalar.QComplex := ((-93084888314977037236926 : Int)/10^30,(-471221610588608455566 : Int)/10^30)
theorem v256_pg_checked : Scalar.distance (sourceCoefficient 2 66 1 2) v256_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v256_mb : Scalar.QComplex := ((1811876015417076628899016 : Int)/10^30,(-431470482593478982285113742 : Int)/10^30)
theorem v256_mb_checked : Scalar.distance (sourceCoefficient 2 66 3 1) v256_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v256_mg : Scalar.QComplex := ((-93085260298245832477975 : Int)/10^30,(-390893368903182717021 : Int)/10^30)
theorem v256_mg_checked : Scalar.distance (sourceCoefficient 2 66 3 2) v256_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v256_upper : Scalar.QComplex := ((999994434473161746765585779098 : Int)/10^30,(3336318734985834879531901626 : Int)/10^30)
theorem v256_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 66 5) 1) 14) v256_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material256 : Material (2 : Basis) (66 : Basis) where
  plus := ![v256_pa,v256_pb,v256_pg]
  minus := ![(Primitive.Addresses.material256 1).one,v256_mb,v256_mg]
  upper := v256_upper
  lower := (Primitive.Addresses.material256 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v256_pa_checked.trans (by decide +kernel)
    · exact v256_pb_checked.trans (by decide +kernel)
    · exact v256_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 66 Primitive.Addresses.material256
    · exact v256_mb_checked.trans (by decide +kernel)
    · exact v256_mg_checked.trans (by decide +kernel)
  upper_error := v256_upper_checked
  lower_error := reuse_lower_error 2 66 Primitive.Addresses.material256

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
