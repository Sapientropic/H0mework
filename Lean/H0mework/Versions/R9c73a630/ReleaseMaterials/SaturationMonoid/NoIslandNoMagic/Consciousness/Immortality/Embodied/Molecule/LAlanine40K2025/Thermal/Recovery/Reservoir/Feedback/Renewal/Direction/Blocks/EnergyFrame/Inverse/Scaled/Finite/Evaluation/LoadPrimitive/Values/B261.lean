import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B174

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4177_pa : Scalar.QComplex := ((999998285642781604543484746056 : Int)/10^30,(-1851678022165365758678739459 : Int)/10^30)
theorem v4177_pa_checked : Scalar.distance (sourceCoefficient 63 83 1 0) v4177_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4177_pb : Scalar.QComplex := ((-798957422883334405393992 : Int)/10^30,(-431476770594600604487131327 : Int)/10^30)
theorem v4177_pb_checked : Scalar.distance (sourceCoefficient 63 83 1 1) v4177_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4177_pg : Scalar.QComplex := ((-93086269159440003711908 : Int)/10^30,(172366094264962659993 : Int)/10^30)
theorem v4177_pg_checked : Scalar.distance (sourceCoefficient 63 83 1 2) v4177_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4177_mb : Scalar.QComplex := ((-1171302145425751034240262 : Int)/10^30,(-431475920471807207771034606 : Int)/10^30)
theorem v4177_mb_checked : Scalar.distance (sourceCoefficient 63 83 3 1) v4177_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4177_mg : Scalar.QComplex := ((-93086085754991473031279 : Int)/10^30,(252695287919853084481 : Int)/10^30)
theorem v4177_mg_checked : Scalar.distance (sourceCoefficient 63 83 3 2) v4177_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4177_upper : Scalar.QComplex := ((999993600434519850471360818028 : Int)/10^30,(-3577581586192091658543662081 : Int)/10^30)
theorem v4177_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 83 5) 1) 14) v4177_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4177 : Material (63 : Basis) (83 : Basis) where
  plus := ![v4177_pa,v4177_pb,v4177_pg]
  minus := ![(Primitive.Addresses.material4177 1).one,v4177_mb,v4177_mg]
  upper := v4177_upper
  lower := (Primitive.Addresses.material4177 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4177_pa_checked.trans (by decide +kernel)
    · exact v4177_pb_checked.trans (by decide +kernel)
    · exact v4177_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 83 Primitive.Addresses.material4177
    · exact v4177_mb_checked.trans (by decide +kernel)
    · exact v4177_mg_checked.trans (by decide +kernel)
  upper_error := v4177_upper_checked
  lower_error := reuse_lower_error 63 83 Primitive.Addresses.material4177

def v4178_pa : Scalar.QComplex := ((999998219959186094580784960900 : Int)/10^30,(-1886817017960549151939375618 : Int)/10^30)
theorem v4178_pa_checked : Scalar.distance (sourceCoefficient 63 84 1 0) v4178_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4178_pb : Scalar.QComplex := ((-814119105457792258762514 : Int)/10^30,(-431476740215398718140083429 : Int)/10^30)
theorem v4178_pb_checked : Scalar.distance (sourceCoefficient 63 84 1 1) v4178_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4178_pg : Scalar.QComplex := ((-93086262825328467658226 : Int)/10^30,(175637057478308927848 : Int)/10^30)
theorem v4178_pg_checked : Scalar.distance (sourceCoefficient 63 84 1 2) v4178_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4178_mb : Scalar.QComplex := ((-1186463796138938542557806 : Int)/10^30,(-431475877008767428066436012 : Int)/10^30)
theorem v4178_mb_checked : Scalar.distance (sourceCoefficient 63 84 3 1) v4178_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4178_mg : Scalar.QComplex := ((-93086076598188361053378 : Int)/10^30,(255966244449217279783 : Int)/10^30)
theorem v4178_mg_checked : Scalar.distance (sourceCoefficient 63 84 3 2) v4178_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4178_upper : Scalar.QComplex := ((999993474104303210818829988897 : Int)/10^30,(-3612720416287941450322691990 : Int)/10^30)
theorem v4178_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 84 5) 1) 14) v4178_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4178 : Material (63 : Basis) (84 : Basis) where
  plus := ![v4178_pa,v4178_pb,v4178_pg]
  minus := ![(Primitive.Addresses.material4178 1).one,v4178_mb,v4178_mg]
  upper := v4178_upper
  lower := (Primitive.Addresses.material4178 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4178_pa_checked.trans (by decide +kernel)
    · exact v4178_pb_checked.trans (by decide +kernel)
    · exact v4178_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 84 Primitive.Addresses.material4178
    · exact v4178_mb_checked.trans (by decide +kernel)
    · exact v4178_mg_checked.trans (by decide +kernel)
  upper_error := v4178_upper_checked
  lower_error := reuse_lower_error 63 84 Primitive.Addresses.material4178

def v4179_pa : Scalar.QComplex := ((999998067668453079490749518886 : Int)/10^30,(-1965873688703272531988686338 : Int)/10^30)
theorem v4179_pa_checked : Scalar.distance (sourceCoefficient 63 85 1 0) v4179_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4179_pb : Scalar.QComplex := ((-848230270470373304730834 : Int)/10^30,(-431476669270531959131901560 : Int)/10^30)
theorem v4179_pb_checked : Scalar.distance (sourceCoefficient 63 85 1 1) v4179_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4179_pg : Scalar.QComplex := ((-93086248084448982101846 : Int)/10^30,(182996159498575621671 : Int)/10^30)
theorem v4179_pg_checked : Scalar.distance (sourceCoefficient 63 85 1 2) v4179_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4179_mb : Scalar.QComplex := ((-1220574887228149122249025 : Int)/10^30,(-431475776627527989058711021 : Int)/10^30)
theorem v4179_mb_checked : Scalar.distance (sourceCoefficient 63 85 3 1) v4179_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4179_mg : Scalar.QComplex := ((-93086055506740762361265 : Int)/10^30,(263325331008638872415 : Int)/10^30)
theorem v4179_mg_checked : Scalar.distance (sourceCoefficient 63 85 3 2) v4179_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4179_upper : Scalar.QComplex := ((999993185369155278091203074885 : Int)/10^30,(-3691776706445050931313817579 : Int)/10^30)
theorem v4179_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 85 5) 1) 14) v4179_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4179 : Material (63 : Basis) (85 : Basis) where
  plus := ![v4179_pa,v4179_pb,v4179_pg]
  minus := ![(Primitive.Addresses.material4179 1).one,v4179_mb,v4179_mg]
  upper := v4179_upper
  lower := (Primitive.Addresses.material4179 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4179_pa_checked.trans (by decide +kernel)
    · exact v4179_pb_checked.trans (by decide +kernel)
    · exact v4179_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 85 Primitive.Addresses.material4179
    · exact v4179_mb_checked.trans (by decide +kernel)
    · exact v4179_mg_checked.trans (by decide +kernel)
  upper_error := v4179_upper_checked
  lower_error := reuse_lower_error 63 85 Primitive.Addresses.material4179

def v4180_pa : Scalar.QComplex := ((999998038890529267778702295628 : Int)/10^30,(-1980458304411907178336114652 : Int)/10^30)
theorem v4180_pa_checked : Scalar.distance (sourceCoefficient 63 86 1 0) v4180_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4180_pb : Scalar.QComplex := ((-854523201931841642398662 : Int)/10^30,(-431476655789552558859354511 : Int)/10^30)
theorem v4180_pb_checked : Scalar.distance (sourceCoefficient 63 86 1 1) v4180_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4180_pg : Scalar.QComplex := ((-93086245290846927690999 : Int)/10^30,(184353789050743258561 : Int)/10^30)
theorem v4180_pg_checked : Scalar.distance (sourceCoefficient 63 86 1 2) v4180_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4180_mb : Scalar.QComplex := ((-1226867804712993413974728 : Int)/10^30,(-431475757716037180235594552 : Int)/10^30)
theorem v4180_mb_checked : Scalar.distance (sourceCoefficient 63 86 3 1) v4180_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4180_mg : Scalar.QComplex := ((-93086051541566589980673 : Int)/10^30,(264682957644546226506 : Int)/10^30)
theorem v4180_mg_checked : Scalar.distance (sourceCoefficient 63 86 3 2) v4180_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4180_upper : Scalar.QComplex := ((999993131419550720614331852138 : Int)/10^30,(-3706361250763527922798306757 : Int)/10^30)
theorem v4180_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 86 5) 1) 14) v4180_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4180 : Material (63 : Basis) (86 : Basis) where
  plus := ![v4180_pa,v4180_pb,v4180_pg]
  minus := ![(Primitive.Addresses.material4180 1).one,v4180_mb,v4180_mg]
  upper := v4180_upper
  lower := (Primitive.Addresses.material4180 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4180_pa_checked.trans (by decide +kernel)
    · exact v4180_pb_checked.trans (by decide +kernel)
    · exact v4180_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 86 Primitive.Addresses.material4180
    · exact v4180_mb_checked.trans (by decide +kernel)
    · exact v4180_mg_checked.trans (by decide +kernel)
  upper_error := v4180_upper_checked
  lower_error := reuse_lower_error 63 86 Primitive.Addresses.material4180

def v4181_pa : Scalar.QComplex := ((999998036977422563481856140938 : Int)/10^30,(-1981424058957445071379705158 : Int)/10^30)
theorem v4181_pa_checked : Scalar.distance (sourceCoefficient 63 87 1 0) v4181_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4181_pb : Scalar.QComplex := ((-854939903148925164112065 : Int)/10^30,(-431476654892557953760100025 : Int)/10^30)
theorem v4181_pb_checked : Scalar.distance (sourceCoefficient 63 87 1 1) v4181_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4181_pg : Scalar.QComplex := ((-93086245105046534493893 : Int)/10^30,(184443687676272081417 : Int)/10^30)
theorem v4181_pg_checked : Scalar.distance (sourceCoefficient 63 87 1 2) v4181_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4181_mb : Scalar.QComplex := ((-1227284505000854083318184 : Int)/10^30,(-431475756459448526311481108 : Int)/10^30)
theorem v4181_mb_checked : Scalar.distance (sourceCoefficient 63 87 3 1) v4181_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4181_mg : Scalar.QComplex := ((-93086051278187801017963 : Int)/10^30,(264772856076264311317 : Int)/10^30)
theorem v4181_mg_checked : Scalar.distance (sourceCoefficient 63 87 3 2) v4181_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4181_upper : Scalar.QComplex := ((999993127839642132634768429429 : Int)/10^30,(-3707327000568839249829350786 : Int)/10^30)
theorem v4181_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 87 5) 1) 14) v4181_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4181 : Material (63 : Basis) (87 : Basis) where
  plus := ![v4181_pa,v4181_pb,v4181_pg]
  minus := ![(Primitive.Addresses.material4181 1).one,v4181_mb,v4181_mg]
  upper := v4181_upper
  lower := (Primitive.Addresses.material4181 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4181_pa_checked.trans (by decide +kernel)
    · exact v4181_pb_checked.trans (by decide +kernel)
    · exact v4181_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 87 Primitive.Addresses.material4181
    · exact v4181_mb_checked.trans (by decide +kernel)
    · exact v4181_mg_checked.trans (by decide +kernel)
  upper_error := v4181_upper_checked
  lower_error := reuse_lower_error 63 87 Primitive.Addresses.material4181

def v4182_pa : Scalar.QComplex := ((999998013607537085140769071348 : Int)/10^30,(-1993183629291265711527691755 : Int)/10^30)
theorem v4182_pa_checked : Scalar.distance (sourceCoefficient 63 88 1 0) v4182_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4182_pb : Scalar.QComplex := ((-860013891422346903679388 : Int)/10^30,(-431476643927201666048981927 : Int)/10^30)
theorem v4182_pb_checked : Scalar.distance (sourceCoefficient 63 88 1 1) v4182_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4182_pg : Scalar.QComplex := ((-93086242834510689347270 : Int)/10^30,(185538343881945961788 : Int)/10^30)
theorem v4182_pg_checked : Scalar.distance (sourceCoefficient 63 88 1 2) v4182_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4182_mb : Scalar.QComplex := ((-1232358481922389480990274 : Int)/10^30,(-431475741115472965489316404 : Int)/10^30)
theorem v4182_mb_checked : Scalar.distance (sourceCoefficient 63 88 3 1) v4182_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4182_mg : Scalar.QComplex := ((-93086048063013797284391 : Int)/10^30,(265867509914977484833 : Int)/10^30)
theorem v4182_mg_checked : Scalar.distance (sourceCoefficient 63 88 3 2) v4182_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4182_upper : Scalar.QComplex := ((999993084173839884705601445367 : Int)/10^30,(-3719086513053859017751858515 : Int)/10^30)
theorem v4182_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 88 5) 1) 14) v4182_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4182 : Material (63 : Basis) (88 : Basis) where
  plus := ![v4182_pa,v4182_pb,v4182_pg]
  minus := ![(Primitive.Addresses.material4182 1).one,v4182_mb,v4182_mg]
  upper := v4182_upper
  lower := (Primitive.Addresses.material4182 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4182_pa_checked.trans (by decide +kernel)
    · exact v4182_pb_checked.trans (by decide +kernel)
    · exact v4182_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 88 Primitive.Addresses.material4182
    · exact v4182_mb_checked.trans (by decide +kernel)
    · exact v4182_mg_checked.trans (by decide +kernel)
  upper_error := v4182_upper_checked
  lower_error := reuse_lower_error 63 88 Primitive.Addresses.material4182

def v4183_pa : Scalar.QComplex := ((999997981408804423725966532812 : Int)/10^30,(-2009273081599943499547396373 : Int)/10^30)
theorem v4183_pa_checked : Scalar.distance (sourceCoefficient 63 89 1 0) v4183_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4183_pb : Scalar.QComplex := ((-866956125608297917922169 : Int)/10^30,(-431476628795503290496321730 : Int)/10^30)
theorem v4183_pb_checked : Scalar.distance (sourceCoefficient 63 89 1 1) v4183_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4183_pg : Scalar.QComplex := ((-93086239703631152112224 : Int)/10^30,(187036053253196328537 : Int)/10^30)
theorem v4183_pg_checked : Scalar.distance (sourceCoefficient 63 89 1 2) v4183_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4183_mb : Scalar.QComplex := ((-1239300700465455240321636 : Int)/10^30,(-431475719992944788304793595 : Int)/10^30)
theorem v4183_mb_checked : Scalar.distance (sourceCoefficient 63 89 3 1) v4183_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4183_mg : Scalar.QComplex := ((-93086043639679692755877 : Int)/10^30,(267365216026754172912 : Int)/10^30)
theorem v4183_mg_checked : Scalar.distance (sourceCoefficient 63 89 3 2) v4183_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4183_upper : Scalar.QComplex := ((999993024206220118454395665363 : Int)/10^30,(-3735175885827096064436555853 : Int)/10^30)
theorem v4183_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 89 5) 1) 14) v4183_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4183 : Material (63 : Basis) (89 : Basis) where
  plus := ![v4183_pa,v4183_pb,v4183_pg]
  minus := ![(Primitive.Addresses.material4183 1).one,v4183_mb,v4183_mg]
  upper := v4183_upper
  lower := (Primitive.Addresses.material4183 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4183_pa_checked.trans (by decide +kernel)
    · exact v4183_pb_checked.trans (by decide +kernel)
    · exact v4183_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 89 Primitive.Addresses.material4183
    · exact v4183_mb_checked.trans (by decide +kernel)
    · exact v4183_mg_checked.trans (by decide +kernel)
  upper_error := v4183_upper_checked
  lower_error := reuse_lower_error 63 89 Primitive.Addresses.material4183

def v4184_pa : Scalar.QComplex := ((999997928416642667041957287575 : Int)/10^30,(-2035475969695616354154765772 : Int)/10^30)
theorem v4184_pa_checked : Scalar.distance (sourceCoefficient 63 90 1 0) v4184_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4184_pb : Scalar.QComplex := ((-878262077982309085378249 : Int)/10^30,(-431476603833618032021267939 : Int)/10^30)
theorem v4184_pb_checked : Scalar.distance (sourceCoefficient 63 90 1 1) v4184_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4184_pg : Scalar.QComplex := ((-93086234544582358625004 : Int)/10^30,(189475186038589382326 : Int)/10^30)
theorem v4184_pg_checked : Scalar.distance (sourceCoefficient 63 90 1 2) v4184_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4184_mb : Scalar.QComplex := ((-1250606627088760894898257 : Int)/10^30,(-431475685274541126701287214 : Int)/10^30)
theorem v4184_mb_checked : Scalar.distance (sourceCoefficient 63 90 3 1) v4184_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4184_mg : Scalar.QComplex := ((-93086036375771080886763 : Int)/10^30,(269804343451919862977 : Int)/10^30)
theorem v4184_mg_checked : Scalar.distance (sourceCoefficient 63 90 3 2) v4184_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4184_upper : Scalar.QComplex := ((999992925990329541678174514509 : Int)/10^30,(-3761378643436981327317686558 : Int)/10^30)
theorem v4184_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 90 5) 1) 14) v4184_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4184 : Material (63 : Basis) (90 : Basis) where
  plus := ![v4184_pa,v4184_pb,v4184_pg]
  minus := ![(Primitive.Addresses.material4184 1).one,v4184_mb,v4184_mg]
  upper := v4184_upper
  lower := (Primitive.Addresses.material4184 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4184_pa_checked.trans (by decide +kernel)
    · exact v4184_pb_checked.trans (by decide +kernel)
    · exact v4184_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 90 Primitive.Addresses.material4184
    · exact v4184_mb_checked.trans (by decide +kernel)
    · exact v4184_mg_checked.trans (by decide +kernel)
  upper_error := v4184_upper_checked
  lower_error := reuse_lower_error 63 90 Primitive.Addresses.material4184

def v4185_pa : Scalar.QComplex := ((999997898261893002680601136076 : Int)/10^30,(-2050237009882410739682827116 : Int)/10^30)
theorem v4185_pa_checked : Scalar.distance (sourceCoefficient 63 91 1 0) v4185_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4185_pb : Scalar.QComplex := ((-884631132154101186486042 : Int)/10^30,(-431476589597744660284373661 : Int)/10^30)
theorem v4185_pb_checked : Scalar.distance (sourceCoefficient 63 91 1 1) v4185_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4185_pg : Scalar.QComplex := ((-93086231605468453641167 : Int)/10^30,(190849238263133949962 : Int)/10^30)
theorem v4185_pg_checked : Scalar.distance (sourceCoefficient 63 91 1 2) v4185_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4185_mb : Scalar.QComplex := ((-1256975666604145487819295 : Int)/10^30,(-431475665542466156925544924 : Int)/10^30)
theorem v4185_mb_checked : Scalar.distance (sourceCoefficient 63 91 3 1) v4185_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4185_mg : Scalar.QComplex := ((-93086032250913085502309 : Int)/10^30,(271178392628519062901 : Int)/10^30)
theorem v4185_mg_checked : Scalar.distance (sourceCoefficient 63 91 3 2) v4185_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4185_upper : Scalar.QComplex := ((999992870359408537972292376219 : Int)/10^30,(-3776139609594578005031826249 : Int)/10^30)
theorem v4185_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 91 5) 1) 14) v4185_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4185 : Material (63 : Basis) (91 : Basis) where
  plus := ![v4185_pa,v4185_pb,v4185_pg]
  minus := ![(Primitive.Addresses.material4185 1).one,v4185_mb,v4185_mg]
  upper := v4185_upper
  lower := (Primitive.Addresses.material4185 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4185_pa_checked.trans (by decide +kernel)
    · exact v4185_pb_checked.trans (by decide +kernel)
    · exact v4185_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 91 Primitive.Addresses.material4185
    · exact v4185_mb_checked.trans (by decide +kernel)
    · exact v4185_mg_checked.trans (by decide +kernel)
  upper_error := v4185_upper_checked
  lower_error := reuse_lower_error 63 91 Primitive.Addresses.material4185

def v4186_pa : Scalar.QComplex := ((999997832233709353025464630939 : Int)/10^30,(-2082193046305567269986328240 : Int)/10^30)
theorem v4186_pa_checked : Scalar.distance (sourceCoefficient 63 92 1 0) v4186_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4186_pb : Scalar.QComplex := ((-898419437001936604280225 : Int)/10^30,(-431476558349201736528626071 : Int)/10^30)
theorem v4186_pb_checked : Scalar.distance (sourceCoefficient 63 92 1 1) v4186_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4186_pg : Scalar.QComplex := ((-93086225161543392778215 : Int)/10^30,(193823910903140359956 : Int)/10^30)
theorem v4186_pg_checked : Scalar.distance (sourceCoefficient 63 92 1 2) v4186_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4186_mb : Scalar.QComplex := ((-1270763939351879693030031 : Int)/10^30,(-431475622395248786946152584 : Int)/10^30)
theorem v4186_mb_checked : Scalar.distance (sourceCoefficient 63 92 3 1) v4186_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4186_mg : Scalar.QComplex := ((-93086023239981909963974 : Int)/10^30,(274153058600101795852 : Int)/10^30)
theorem v4186_mg_checked : Scalar.distance (sourceCoefficient 63 92 3 2) v4186_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4186_upper : Scalar.QComplex := ((999992749178103392150652588817 : Int)/10^30,(-3808095484464317153497777705 : Int)/10^30)
theorem v4186_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 92 5) 1) 14) v4186_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4186 : Material (63 : Basis) (92 : Basis) where
  plus := ![v4186_pa,v4186_pb,v4186_pg]
  minus := ![(Primitive.Addresses.material4186 1).one,v4186_mb,v4186_mg]
  upper := v4186_upper
  lower := (Primitive.Addresses.material4186 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4186_pa_checked.trans (by decide +kernel)
    · exact v4186_pb_checked.trans (by decide +kernel)
    · exact v4186_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 92 Primitive.Addresses.material4186
    · exact v4186_mb_checked.trans (by decide +kernel)
    · exact v4186_mg_checked.trans (by decide +kernel)
  upper_error := v4186_upper_checked
  lower_error := reuse_lower_error 63 92 Primitive.Addresses.material4186

def v4187_pa : Scalar.QComplex := ((999997752546089961025248085763 : Int)/10^30,(-2120118574285144022862362457 : Int)/10^30)
theorem v4187_pa_checked : Scalar.distance (sourceCoefficient 63 93 1 0) v4187_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4187_pb : Scalar.QComplex := ((-914783441415639974846790 : Int)/10^30,(-431476520500963629372474842 : Int)/10^30)
theorem v4187_pb_checked : Scalar.distance (sourceCoefficient 63 93 1 1) v4187_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4187_pg : Scalar.QComplex := ((-93086217369959214931000 : Int)/10^30,(197354262000602735802 : Int)/10^30)
theorem v4187_pg_checked : Scalar.distance (sourceCoefficient 63 93 1 2) v4187_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4187_mb : Scalar.QComplex := ((-1287127905011191483317569 : Int)/10^30,(-431475570425625970792582281 : Int)/10^30)
theorem v4187_mb_checked : Scalar.distance (sourceCoefficient 63 93 3 1) v4187_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4187_mg : Scalar.QComplex := ((-93086012401866637280642 : Int)/10^30,(277683401659266887539 : Int)/10^30)
theorem v4187_mg_checked : Scalar.distance (sourceCoefficient 63 93 3 2) v4187_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4187_upper : Scalar.QComplex := ((999992604034581969771274068250 : Int)/10^30,(-3846020818424673160028017965 : Int)/10^30)
theorem v4187_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 93 5) 1) 14) v4187_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4187 : Material (63 : Basis) (93 : Basis) where
  plus := ![v4187_pa,v4187_pb,v4187_pg]
  minus := ![(Primitive.Addresses.material4187 1).one,v4187_mb,v4187_mg]
  upper := v4187_upper
  lower := (Primitive.Addresses.material4187 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4187_pa_checked.trans (by decide +kernel)
    · exact v4187_pb_checked.trans (by decide +kernel)
    · exact v4187_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 93 Primitive.Addresses.material4187
    · exact v4187_mb_checked.trans (by decide +kernel)
    · exact v4187_mg_checked.trans (by decide +kernel)
  upper_error := v4187_upper_checked
  lower_error := reuse_lower_error 63 93 Primitive.Addresses.material4187

def v4188_pa : Scalar.QComplex := ((999997656564383021077287044002 : Int)/10^30,(-2164917028956849999798762819 : Int)/10^30)
theorem v4188_pa_checked : Scalar.distance (sourceCoefficient 63 94 1 0) v4188_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4188_pb : Scalar.QComplex := ((-934112956766034860361199 : Int)/10^30,(-431476474727789627134884398 : Int)/10^30)
theorem v4188_pb_checked : Scalar.distance (sourceCoefficient 63 94 1 1) v4188_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4188_pg : Scalar.QComplex := ((-93086207965137853384297 : Int)/10^30,(201524389044176683272 : Int)/10^30)
theorem v4188_pg_checked : Scalar.distance (sourceCoefficient 63 94 1 2) v4188_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4188_mb : Scalar.QComplex := ((-1306457373664136784685271 : Int)/10^30,(-431475507971967833663163480 : Int)/10^30)
theorem v4188_mb_checked : Scalar.distance (sourceCoefficient 63 94 3 1) v4188_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4188_mg : Scalar.QComplex := ((-93085999398416954524439 : Int)/10^30,(281853519034174694881 : Int)/10^30)
theorem v4188_mg_checked : Scalar.distance (sourceCoefficient 63 94 3 2) v4188_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4188_upper : Scalar.QComplex := ((999992430734949303997415277890 : Int)/10^30,(-3890819040718624513692266106 : Int)/10^30)
theorem v4188_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 94 5) 1) 14) v4188_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4188 : Material (63 : Basis) (94 : Basis) where
  plus := ![v4188_pa,v4188_pb,v4188_pg]
  minus := ![(Primitive.Addresses.material4188 1).one,v4188_mb,v4188_mg]
  upper := v4188_upper
  lower := (Primitive.Addresses.material4188 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4188_pa_checked.trans (by decide +kernel)
    · exact v4188_pb_checked.trans (by decide +kernel)
    · exact v4188_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 94 Primitive.Addresses.material4188
    · exact v4188_mb_checked.trans (by decide +kernel)
    · exact v4188_mg_checked.trans (by decide +kernel)
  upper_error := v4188_upper_checked
  lower_error := reuse_lower_error 63 94 Primitive.Addresses.material4188

def v4189_pa : Scalar.QComplex := ((999997559734261132734269439441 : Int)/10^30,(-2209191146740737591017415277 : Int)/10^30)
theorem v4189_pa_checked : Scalar.distance (sourceCoefficient 63 95 1 0) v4189_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4189_pb : Scalar.QComplex := ((-953216231652232568448769 : Int)/10^30,(-431476428355968943042980646 : Int)/10^30)
theorem v4189_pb_checked : Scalar.distance (sourceCoefficient 63 95 1 1) v4189_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4189_pg : Scalar.QComplex := ((-93086198456252881785721 : Int)/10^30,(205645707343479156596 : Int)/10^30)
theorem v4189_pg_checked : Scalar.distance (sourceCoefficient 63 95 1 2) v4189_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4189_mb : Scalar.QComplex := ((-1325560601420519448752148 : Int)/10^30,(-431475445114898568692858941 : Int)/10^30)
theorem v4189_mb_checked : Scalar.distance (sourceCoefficient 63 95 3 1) v4189_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4189_mg : Scalar.QComplex := ((-93085986333023448506044 : Int)/10^30,(285974827593182545615 : Int)/10^30)
theorem v4189_mg_checked : Scalar.distance (sourceCoefficient 63 95 3 2) v4189_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4189_upper : Scalar.QComplex := ((999992257491860854346551294380 : Int)/10^30,(-3935092925441408449779753697 : Int)/10^30)
theorem v4189_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 95 5) 1) 14) v4189_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4189 : Material (63 : Basis) (95 : Basis) where
  plus := ![v4189_pa,v4189_pb,v4189_pg]
  minus := ![(Primitive.Addresses.material4189 1).one,v4189_mb,v4189_mg]
  upper := v4189_upper
  lower := (Primitive.Addresses.material4189 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4189_pa_checked.trans (by decide +kernel)
    · exact v4189_pb_checked.trans (by decide +kernel)
    · exact v4189_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 95 Primitive.Addresses.material4189
    · exact v4189_mb_checked.trans (by decide +kernel)
    · exact v4189_mg_checked.trans (by decide +kernel)
  upper_error := v4189_upper_checked
  lower_error := reuse_lower_error 63 95 Primitive.Addresses.material4189

def v4190_pa : Scalar.QComplex := ((999997512531726724599356966658 : Int)/10^30,(-2230455190998552818576535507 : Int)/10^30)
theorem v4190_pa_checked : Scalar.distance (sourceCoefficient 63 96 1 0) v4190_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4190_pb : Scalar.QComplex := ((-962391182767830022040461 : Int)/10^30,(-431476405683561132663334643 : Int)/10^30)
theorem v4190_pb_checked : Scalar.distance (sourceCoefficient 63 96 1 1) v4190_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4190_pg : Scalar.QComplex := ((-93086193813636481203795 : Int)/10^30,(207625100662773497738 : Int)/10^30)
theorem v4190_pg_checked : Scalar.distance (sourceCoefficient 63 96 1 2) v4190_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4190_mb : Scalar.QComplex := ((-1334735529554596473010412 : Int)/10^30,(-431475414524929611984852077 : Int)/10^30)
theorem v4190_mb_checked : Scalar.distance (sourceCoefficient 63 96 3 1) v4190_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4190_mg : Scalar.QComplex := ((-93085979982281490597116 : Int)/10^30,(287954216169089433218 : Int)/10^30)
theorem v4190_mg_checked : Scalar.distance (sourceCoefficient 63 96 3 2) v4190_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4190_upper : Scalar.QComplex := ((999992173589585418878844626180 : Int)/10^30,(-3956356856561635397456104040 : Int)/10^30)
theorem v4190_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 96 5) 1) 14) v4190_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4190 : Material (63 : Basis) (96 : Basis) where
  plus := ![v4190_pa,v4190_pb,v4190_pg]
  minus := ![(Primitive.Addresses.material4190 1).one,v4190_mb,v4190_mg]
  upper := v4190_upper
  lower := (Primitive.Addresses.material4190 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4190_pa_checked.trans (by decide +kernel)
    · exact v4190_pb_checked.trans (by decide +kernel)
    · exact v4190_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 96 Primitive.Addresses.material4190
    · exact v4190_mb_checked.trans (by decide +kernel)
    · exact v4190_mg_checked.trans (by decide +kernel)
  upper_error := v4190_upper_checked
  lower_error := reuse_lower_error 63 96 Primitive.Addresses.material4190

def v4191_pa : Scalar.QComplex := ((999997346670317319135769377865 : Int)/10^30,(-2303617226277691183976128035 : Int)/10^30)
theorem v4191_pa_checked : Scalar.distance (sourceCoefficient 63 97 1 0) v4191_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4191_pb : Scalar.QComplex := ((-993958933888053049979980 : Int)/10^30,(-431476325688620817443014791 : Int)/10^30)
theorem v4191_pb_checked : Scalar.distance (sourceCoefficient 63 97 1 1) v4191_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4191_pg : Scalar.QComplex := ((-93086177464908203985884 : Int)/10^30,(214435490904557797348 : Int)/10^30)
theorem v4191_pg_checked : Scalar.distance (sourceCoefficient 63 97 1 2) v4191_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4191_mb : Scalar.QComplex := ((-1366303199888672387726028 : Int)/10^30,(-431475307288471624516577693 : Int)/10^30)
theorem v4191_mb_checked : Scalar.distance (sourceCoefficient 63 97 3 1) v4191_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4191_mg : Scalar.QComplex := ((-93085957756499250688255 : Int)/10^30,(294764589766838011751 : Int)/10^30)
theorem v4191_mg_checked : Scalar.distance (sourceCoefficient 63 97 3 2) v4191_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4191_upper : Scalar.QComplex := ((999991881457387360701797877769 : Int)/10^30,(-4029518496612770626645491561 : Int)/10^30)
theorem v4191_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 97 5) 1) 14) v4191_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4191 : Material (63 : Basis) (97 : Basis) where
  plus := ![v4191_pa,v4191_pb,v4191_pg]
  minus := ![(Primitive.Addresses.material4191 1).one,v4191_mb,v4191_mg]
  upper := v4191_upper
  lower := (Primitive.Addresses.material4191 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4191_pa_checked.trans (by decide +kernel)
    · exact v4191_pb_checked.trans (by decide +kernel)
    · exact v4191_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 97 Primitive.Addresses.material4191
    · exact v4191_mb_checked.trans (by decide +kernel)
    · exact v4191_mg_checked.trans (by decide +kernel)
  upper_error := v4191_upper_checked
  lower_error := reuse_lower_error 63 97 Primitive.Addresses.material4191

def v4192_pa : Scalar.QComplex := ((999998763157587917401884809594 : Int)/10^30,(-1572794740068151392748401186 : Int)/10^30)
theorem v4192_pa_checked : Scalar.distance (sourceCoefficient 64 65 1 0) v4192_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4192_pb : Scalar.QComplex := ((-678625575341160444236204 : Int)/10^30,(-431476987237928568298273060 : Int)/10^30)
theorem v4192_pb_checked : Scalar.distance (sourceCoefficient 64 65 1 1) v4192_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4192_pg : Scalar.QComplex := ((-93086314753696877694592 : Int)/10^30,(146405847297904121725 : Int)/10^30)
theorem v4192_pg_checked : Scalar.distance (sourceCoefficient 64 65 1 2) v4192_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4192_mb : Scalar.QComplex := ((-1050970529642058129628014 : Int)/10^30,(-431476240956019389035890802 : Int)/10^30)
theorem v4192_mb_checked : Scalar.distance (sourceCoefficient 64 65 3 1) v4192_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4192_mg : Scalar.QComplex := ((-93086153751755296639462 : Int)/10^30,(226735089964771127093 : Int)/10^30)
theorem v4192_mg_checked : Scalar.distance (sourceCoefficient 64 65 3 2) v4192_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4192_upper : Scalar.QComplex := ((999994559275859767192209963484 : Int)/10^30,(-3298699543606001935999944789 : Int)/10^30)
theorem v4192_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 65 5) 1) 14) v4192_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4192 : Material (64 : Basis) (65 : Basis) where
  plus := ![v4192_pa,v4192_pb,v4192_pg]
  minus := ![(Primitive.Addresses.material4192 1).one,v4192_mb,v4192_mg]
  upper := v4192_upper
  lower := (Primitive.Addresses.material4192 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4192_pa_checked.trans (by decide +kernel)
    · exact v4192_pb_checked.trans (by decide +kernel)
    · exact v4192_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 65 Primitive.Addresses.material4192
    · exact v4192_mb_checked.trans (by decide +kernel)
    · exact v4192_mg_checked.trans (by decide +kernel)
  upper_error := v4192_upper_checked
  lower_error := reuse_lower_error 64 65 Primitive.Addresses.material4192

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
