import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B080

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1921_pa : Scalar.QComplex := ((999999801920694184969144080012 : Int)/10^30,(-629411290329821077380639661 : Int)/10^30)
theorem v1921_pa_checked : Scalar.distance (sourceCoefficient 22 41 1 0) v1921_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1921_pb : Scalar.QComplex := ((-271576818904485667843731 : Int)/10^30,(-431477428643562388924123081 : Int)/10^30)
theorem v1921_pb_checked : Scalar.distance (sourceCoefficient 22 41 1 1) v1921_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1921_pg : Scalar.QComplex := ((-93086410715225794180866 : Int)/10^30,(58589649485839048129 : Int)/10^30)
theorem v1921_pg_checked : Scalar.distance (sourceCoefficient 22 41 1 2) v1921_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1921_mb : Scalar.QComplex := ((-643922305681420237227387 : Int)/10^30,(-431477033626232863576815770 : Int)/10^30)
theorem v1921_mb_checked : Scalar.distance (sourceCoefficient 22 41 3 1) v1921_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1921_mg : Scalar.QComplex := ((-93086325494672099345582 : Int)/10^30,(138919007661167405539 : Int)/10^30)
theorem v1921_mg_checked : Scalar.distance (sourceCoefficient 22 41 3 2) v1921_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1921_upper : Scalar.QComplex := ((999997226231670089470549909260 : Int)/10^30,(-2355319291737387966307365952 : Int)/10^30)
theorem v1921_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 41 5) 1) 14) v1921_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1921 : Material (22 : Basis) (41 : Basis) where
  plus := ![v1921_pa,v1921_pb,v1921_pg]
  minus := ![(Primitive.Addresses.material1921 1).one,v1921_mb,v1921_mg]
  upper := v1921_upper
  lower := (Primitive.Addresses.material1921 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1921_pa_checked.trans (by decide +kernel)
    · exact v1921_pb_checked.trans (by decide +kernel)
    · exact v1921_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 41 Primitive.Addresses.material1921
    · exact v1921_mb_checked.trans (by decide +kernel)
    · exact v1921_mg_checked.trans (by decide +kernel)
  upper_error := v1921_upper_checked
  lower_error := reuse_lower_error 22 41 Primitive.Addresses.material1921

def v1922_pa : Scalar.QComplex := ((999999794498619173122827778026 : Int)/10^30,(-641094937917105084585674026 : Int)/10^30)
theorem v1922_pa_checked : Scalar.distance (sourceCoefficient 22 42 1 0) v1922_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1922_pb : Scalar.QComplex := ((-276618049781426703553828 : Int)/10^30,(-431477424911133515257909047 : Int)/10^30)
theorem v1922_pb_checked : Scalar.distance (sourceCoefficient 22 42 1 1) v1922_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1922_pg : Scalar.QComplex := ((-93086409967163753714072 : Int)/10^30,(59677238482579950748 : Int)/10^30)
theorem v1922_pg_checked : Scalar.distance (sourceCoefficient 22 42 1 2) v1922_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1922_mb : Scalar.QComplex := ((-648963531460362606201759 : Int)/10^30,(-431477025543450181474594840 : Int)/10^30)
theorem v1922_mb_checked : Scalar.distance (sourceCoefficient 22 42 3 1) v1922_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1922_mg : Scalar.QComplex := ((-93086323808070016419147 : Int)/10^30,(140006595607405369939 : Int)/10^30)
theorem v1922_mg_checked : Scalar.distance (sourceCoefficient 22 42 3 2) v1922_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1922_upper : Scalar.QComplex := ((999997198644690328510291348687 : Int)/10^30,(-2367002909113423204846969420 : Int)/10^30)
theorem v1922_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 42 5) 1) 14) v1922_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1922 : Material (22 : Basis) (42 : Basis) where
  plus := ![v1922_pa,v1922_pb,v1922_pg]
  minus := ![(Primitive.Addresses.material1922 1).one,v1922_mb,v1922_mg]
  upper := v1922_upper
  lower := (Primitive.Addresses.material1922 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1922_pa_checked.trans (by decide +kernel)
    · exact v1922_pb_checked.trans (by decide +kernel)
    · exact v1922_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 42 Primitive.Addresses.material1922
    · exact v1922_mb_checked.trans (by decide +kernel)
    · exact v1922_mg_checked.trans (by decide +kernel)
  upper_error := v1922_upper_checked
  lower_error := reuse_lower_error 22 42 Primitive.Addresses.material1922

def v1923_pa : Scalar.QComplex := ((999999784456106374384535902002 : Int)/10^30,(-656572723155676677327582594 : Int)/10^30)
theorem v1923_pa_checked : Scalar.distance (sourceCoefficient 22 43 1 0) v1923_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1923_pb : Scalar.QComplex := ((-283296365591084992601529 : Int)/10^30,(-431477419845710422621041122 : Int)/10^30)
theorem v1923_pb_checked : Scalar.distance (sourceCoefficient 22 43 1 1) v1923_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1923_pg : Scalar.QComplex := ((-93086408953348847210665 : Int)/10^30,(61118010188897102197 : Int)/10^30)
theorem v1923_pg_checked : Scalar.distance (sourceCoefficient 22 43 1 2) v1923_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1923_mb : Scalar.QComplex := ((-655641840412146714444882 : Int)/10^30,(-431477014714943211369724069 : Int)/10^30)
theorem v1923_mb_checked : Scalar.distance (sourceCoefficient 22 43 3 1) v1923_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1923_mg : Scalar.QComplex := ((-93086321550934394802486 : Int)/10^30,(141447365902380764822 : Int)/10^30)
theorem v1923_mg_checked : Scalar.distance (sourceCoefficient 22 43 3 2) v1923_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1923_upper : Scalar.QComplex := ((999997161888939298848920318086 : Int)/10^30,(-2382480653967185792130650922 : Int)/10^30)
theorem v1923_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 43 5) 1) 14) v1923_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1923 : Material (22 : Basis) (43 : Basis) where
  plus := ![v1923_pa,v1923_pb,v1923_pg]
  minus := ![(Primitive.Addresses.material1923 1).one,v1923_mb,v1923_mg]
  upper := v1923_upper
  lower := (Primitive.Addresses.material1923 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1923_pa_checked.trans (by decide +kernel)
    · exact v1923_pb_checked.trans (by decide +kernel)
    · exact v1923_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 43 Primitive.Addresses.material1923
    · exact v1923_mb_checked.trans (by decide +kernel)
    · exact v1923_mg_checked.trans (by decide +kernel)
  upper_error := v1923_upper_checked
  lower_error := reuse_lower_error 22 43 Primitive.Addresses.material1923

def v1924_pa : Scalar.QComplex := ((999999780594216258186484204995 : Int)/10^30,(-662428501307672519011910442 : Int)/10^30)
theorem v1924_pa_checked : Scalar.distance (sourceCoefficient 22 44 1 0) v1924_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1924_pb : Scalar.QComplex := ((-285823001994417230215769 : Int)/10^30,(-431477417893351968158638485 : Int)/10^30)
theorem v1924_pb_checked : Scalar.distance (sourceCoefficient 22 44 1 1) v1924_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1924_pg : Scalar.QComplex := ((-93086408563004359282578 : Int)/10^30,(61663103645746254932 : Int)/10^30)
theorem v1924_pg_checked : Scalar.distance (sourceCoefficient 22 44 1 2) v1924_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1924_mb : Scalar.QComplex := ((-658168474189899330870001 : Int)/10^30,(-431477010582212063263199484 : Int)/10^30)
theorem v1924_mb_checked : Scalar.distance (sourceCoefficient 22 44 3 1) v1924_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1924_mg : Scalar.QComplex := ((-93086320690198949054627 : Int)/10^30,(141992458819416998952 : Int)/10^30)
theorem v1924_mg_checked : Scalar.distance (sourceCoefficient 22 44 3 2) v1924_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1924_upper : Scalar.QComplex := ((999997147920513076181916536258 : Int)/10^30,(-2388336416732415951815735480 : Int)/10^30)
theorem v1924_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 44 5) 1) 14) v1924_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1924 : Material (22 : Basis) (44 : Basis) where
  plus := ![v1924_pa,v1924_pb,v1924_pg]
  minus := ![(Primitive.Addresses.material1924 1).one,v1924_mb,v1924_mg]
  upper := v1924_upper
  lower := (Primitive.Addresses.material1924 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1924_pa_checked.trans (by decide +kernel)
    · exact v1924_pb_checked.trans (by decide +kernel)
    · exact v1924_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 44 Primitive.Addresses.material1924
    · exact v1924_mb_checked.trans (by decide +kernel)
    · exact v1924_mg_checked.trans (by decide +kernel)
  upper_error := v1924_upper_checked
  lower_error := reuse_lower_error 22 44 Primitive.Addresses.material1924

def v1925_pa : Scalar.QComplex := ((999999778660104051049519570695 : Int)/10^30,(-665341824107391750375556803 : Int)/10^30)
theorem v1925_pa_checked : Scalar.distance (sourceCoefficient 22 45 1 0) v1925_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1925_pb : Scalar.QComplex := ((-287080035173424230378885 : Int)/10^30,(-431477416914680537236346472 : Int)/10^30)
theorem v1925_pb_checked : Scalar.distance (sourceCoefficient 22 45 1 1) v1925_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1925_pg : Scalar.QComplex := ((-93086408367415873539073 : Int)/10^30,(61934294451312341323 : Int)/10^30)
theorem v1925_pg_checked : Scalar.distance (sourceCoefficient 22 45 1 2) v1925_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1925_mb : Scalar.QComplex := ((-659425506056306062073549 : Int)/10^30,(-431477008518777977934714592 : Int)/10^30)
theorem v1925_mb_checked : Scalar.distance (sourceCoefficient 22 45 3 1) v1925_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1925_mg : Scalar.QComplex := ((-93086320260585084914600 : Int)/10^30,(142263649355222300180 : Int)/10^30)
theorem v1925_mg_checked : Scalar.distance (sourceCoefficient 22 45 3 2) v1925_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1925_upper : Scalar.QComplex := ((999997140958272891942328889771 : Int)/10^30,(-2391249731854980887703893960 : Int)/10^30)
theorem v1925_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 45 5) 1) 14) v1925_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1925 : Material (22 : Basis) (45 : Basis) where
  plus := ![v1925_pa,v1925_pb,v1925_pg]
  minus := ![(Primitive.Addresses.material1925 1).one,v1925_mb,v1925_mg]
  upper := v1925_upper
  lower := (Primitive.Addresses.material1925 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1925_pa_checked.trans (by decide +kernel)
    · exact v1925_pb_checked.trans (by decide +kernel)
    · exact v1925_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 45 Primitive.Addresses.material1925
    · exact v1925_mb_checked.trans (by decide +kernel)
    · exact v1925_mg_checked.trans (by decide +kernel)
  upper_error := v1925_upper_checked
  lower_error := reuse_lower_error 22 45 Primitive.Addresses.material1925

def v1926_pa : Scalar.QComplex := ((999999767638394407554075764900 : Int)/10^30,(-681706063632249126388556262 : Int)/10^30)
theorem v1926_pa_checked : Scalar.distance (sourceCoefficient 22 46 1 0) v1926_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1926_pb : Scalar.QComplex := ((-294140835968797335860578 : Int)/10^30,(-431477411326704312264352934 : Int)/10^30)
theorem v1926_pb_checked : Scalar.distance (sourceCoefficient 22 46 1 1) v1926_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1926_pg : Scalar.QComplex := ((-93086407251658512668006 : Int)/10^30,(63457583010302449845 : Int)/10^30)
theorem v1926_pg_checked : Scalar.distance (sourceCoefficient 22 46 1 2) v1926_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1926_mb : Scalar.QComplex := ((-666486299400448527855849 : Int)/10^30,(-431476996837650753877524092 : Int)/10^30)
theorem v1926_mb_checked : Scalar.distance (sourceCoefficient 22 46 3 1) v1926_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1926_mg : Scalar.QComplex := ((-93086317830298719452436 : Int)/10^30,(143786936384174109878 : Int)/10^30)
theorem v1926_mg_checked : Scalar.distance (sourceCoefficient 22 46 3 2) v1926_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1926_upper : Scalar.QComplex := ((999997101693386796297876690059 : Int)/10^30,(-2407613927984754807064203658 : Int)/10^30)
theorem v1926_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 46 5) 1) 14) v1926_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1926 : Material (22 : Basis) (46 : Basis) where
  plus := ![v1926_pa,v1926_pb,v1926_pg]
  minus := ![(Primitive.Addresses.material1926 1).one,v1926_mb,v1926_mg]
  upper := v1926_upper
  lower := (Primitive.Addresses.material1926 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1926_pa_checked.trans (by decide +kernel)
    · exact v1926_pb_checked.trans (by decide +kernel)
    · exact v1926_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 46 Primitive.Addresses.material1926
    · exact v1926_mb_checked.trans (by decide +kernel)
    · exact v1926_mg_checked.trans (by decide +kernel)
  upper_error := v1926_upper_checked
  lower_error := reuse_lower_error 22 46 Primitive.Addresses.material1926

def v1927_pa : Scalar.QComplex := ((999999764946052729365640082160 : Int)/10^30,(-685644105415419284584200866 : Int)/10^30)
theorem v1927_pa_checked : Scalar.distance (sourceCoefficient 22 47 1 0) v1927_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1927_pb : Scalar.QComplex := ((-295840012296638626100819 : Int)/10^30,(-431477409958963970416555893 : Int)/10^30)
theorem v1927_pb_checked : Scalar.distance (sourceCoefficient 22 47 1 1) v1927_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1927_pg : Scalar.QComplex := ((-93086406978810965449020 : Int)/10^30,(63824161241443518000 : Int)/10^30)
theorem v1927_pg_checked : Scalar.distance (sourceCoefficient 22 47 1 2) v1927_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1927_mb : Scalar.QComplex := ((-668185473915310500769923 : Int)/10^30,(-431476994003598278435882479 : Int)/10^30)
theorem v1927_mb_checked : Scalar.distance (sourceCoefficient 22 47 3 1) v1927_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1927_mg : Scalar.QComplex := ((-93086317241110770422968 : Int)/10^30,(144153514243366204474 : Int)/10^30)
theorem v1927_mg_checked : Scalar.distance (sourceCoefficient 22 47 3 2) v1927_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1927_upper : Scalar.QComplex := ((999997092204346266644248618091 : Int)/10^30,(-2411551959255936834887116837 : Int)/10^30)
theorem v1927_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 47 5) 1) 14) v1927_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1927 : Material (22 : Basis) (47 : Basis) where
  plus := ![v1927_pa,v1927_pb,v1927_pg]
  minus := ![(Primitive.Addresses.material1927 1).one,v1927_mb,v1927_mg]
  upper := v1927_upper
  lower := (Primitive.Addresses.material1927 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1927_pa_checked.trans (by decide +kernel)
    · exact v1927_pb_checked.trans (by decide +kernel)
    · exact v1927_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 47 Primitive.Addresses.material1927
    · exact v1927_mb_checked.trans (by decide +kernel)
    · exact v1927_mg_checked.trans (by decide +kernel)
  upper_error := v1927_upper_checked
  lower_error := reuse_lower_error 22 47 Primitive.Addresses.material1927

def v1928_pa : Scalar.QComplex := ((999999745762227658467419674096 : Int)/10^30,(-713074666529543928003216434 : Int)/10^30)
theorem v1928_pa_checked : Scalar.distance (sourceCoefficient 22 48 1 0) v1928_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1928_pb : Scalar.QComplex := ((-307675681474313076003945 : Int)/10^30,(-431477400184410670078938127 : Int)/10^30)
theorem v1928_pb_checked : Scalar.distance (sourceCoefficient 22 48 1 1) v1928_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1928_pg : Scalar.QComplex := ((-93086405031559016563466 : Int)/10^30,(66377574101999578887 : Int)/10^30)
theorem v1928_pg_checked : Scalar.distance (sourceCoefficient 22 48 1 2) v1928_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1928_mb : Scalar.QComplex := ((-680021130251025130368793 : Int)/10^30,(-431476974015399176029818764 : Int)/10^30)
theorem v1928_mb_checked : Scalar.distance (sourceCoefficient 22 48 3 1) v1928_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1928_mg : Scalar.QComplex := ((-93086313090379249374613 : Int)/10^30,(146706924472779229727 : Int)/10^30)
theorem v1928_mg_checked : Scalar.distance (sourceCoefficient 22 48 3 2) v1928_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1928_upper : Scalar.QComplex := ((999997025677889765886172463290 : Int)/10^30,(-2438982446405921189519844619 : Int)/10^30)
theorem v1928_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 48 5) 1) 14) v1928_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1928 : Material (22 : Basis) (48 : Basis) where
  plus := ![v1928_pa,v1928_pb,v1928_pg]
  minus := ![(Primitive.Addresses.material1928 1).one,v1928_mb,v1928_mg]
  upper := v1928_upper
  lower := (Primitive.Addresses.material1928 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1928_pa_checked.trans (by decide +kernel)
    · exact v1928_pb_checked.trans (by decide +kernel)
    · exact v1928_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 48 Primitive.Addresses.material1928
    · exact v1928_mb_checked.trans (by decide +kernel)
    · exact v1928_mg_checked.trans (by decide +kernel)
  upper_error := v1928_upper_checked
  lower_error := reuse_lower_error 22 48 Primitive.Addresses.material1928

def v1929_pa : Scalar.QComplex := ((999999729804369166969809727528 : Int)/10^30,(-735113044817177393615961115 : Int)/10^30)
theorem v1929_pa_checked : Scalar.distance (sourceCoefficient 22 49 1 0) v1929_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1929_pb : Scalar.QComplex := ((-317184745117834946962997 : Int)/10^30,(-431477392017695007221852404 : Int)/10^30)
theorem v1929_pb_checked : Scalar.distance (sourceCoefficient 22 49 1 1) v1929_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1929_pg : Scalar.QComplex := ((-93086403407890380975948 : Int)/10^30,(68429047929484148706 : Int)/10^30)
theorem v1929_pg_checked : Scalar.distance (sourceCoefficient 22 49 1 2) v1929_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1929_mb : Scalar.QComplex := ((-689530183306380219341023 : Int)/10^30,(-431476957642792901983125126 : Int)/10^30)
theorem v1929_mb_checked : Scalar.distance (sourceCoefficient 22 49 3 1) v1929_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1929_mg : Scalar.QComplex := ((-93086309696381700185277 : Int)/10^30,(148758396135253431397 : Int)/10^30)
theorem v1929_mg_checked : Scalar.distance (sourceCoefficient 22 49 3 2) v1929_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1929_upper : Scalar.QComplex := ((999996971683813423349414455602 : Int)/10^30,(-2461020764328162934758949772 : Int)/10^30)
theorem v1929_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 49 5) 1) 14) v1929_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1929 : Material (22 : Basis) (49 : Basis) where
  plus := ![v1929_pa,v1929_pb,v1929_pg]
  minus := ![(Primitive.Addresses.material1929 1).one,v1929_mb,v1929_mg]
  upper := v1929_upper
  lower := (Primitive.Addresses.material1929 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1929_pa_checked.trans (by decide +kernel)
    · exact v1929_pb_checked.trans (by decide +kernel)
    · exact v1929_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 49 Primitive.Addresses.material1929
    · exact v1929_mb_checked.trans (by decide +kernel)
    · exact v1929_mg_checked.trans (by decide +kernel)
  upper_error := v1929_upper_checked
  lower_error := reuse_lower_error 22 49 Primitive.Addresses.material1929

def v1930_pa : Scalar.QComplex := ((999999727907930400645267504987 : Int)/10^30,(-737688325219136924175874791 : Int)/10^30)
theorem v1930_pa_checked : Scalar.distance (sourceCoefficient 22 50 1 0) v1930_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1930_pb : Scalar.QComplex := ((-318295920575811665627192 : Int)/10^30,(-431477391045145336680899208 : Int)/10^30)
theorem v1930_pb_checked : Scalar.distance (sourceCoefficient 22 50 1 1) v1930_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1930_pg : Scalar.QComplex := ((-93086403214715688790404 : Int)/10^30,(68668771572365073868 : Int)/10^30)
theorem v1930_pg_checked : Scalar.distance (sourceCoefficient 22 50 1 2) v1930_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1930_mb : Scalar.QComplex := ((-690641357511348968107625 : Int)/10^30,(-431476955711349218817805329 : Int)/10^30)
theorem v1930_mb_checked : Scalar.distance (sourceCoefficient 22 50 3 1) v1930_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1930_mg : Scalar.QComplex := ((-93086309296336372873343 : Int)/10^30,(148998119522173229312 : Int)/10^30)
theorem v1930_mg_checked : Scalar.distance (sourceCoefficient 22 50 3 2) v1930_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1930_upper : Scalar.QComplex := ((999996965342677135378560589058 : Int)/10^30,(-2463596037621463553191374673 : Int)/10^30)
theorem v1930_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 50 5) 1) 14) v1930_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1930 : Material (22 : Basis) (50 : Basis) where
  plus := ![v1930_pa,v1930_pb,v1930_pg]
  minus := ![(Primitive.Addresses.material1930 1).one,v1930_mb,v1930_mg]
  upper := v1930_upper
  lower := (Primitive.Addresses.material1930 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1930_pa_checked.trans (by decide +kernel)
    · exact v1930_pb_checked.trans (by decide +kernel)
    · exact v1930_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 50 Primitive.Addresses.material1930
    · exact v1930_mb_checked.trans (by decide +kernel)
    · exact v1930_mg_checked.trans (by decide +kernel)
  upper_error := v1930_upper_checked
  lower_error := reuse_lower_error 22 50 Primitive.Addresses.material1930

def v1931_pa : Scalar.QComplex := ((999999719508768701274629608947 : Int)/10^30,(-748987572608598029538906029 : Int)/10^30)
theorem v1931_pa_checked : Scalar.distance (sourceCoefficient 22 51 1 0) v1931_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1931_pb : Scalar.QComplex := ((-323171291171297470106277 : Int)/10^30,(-431477386732910705378043337 : Int)/10^30)
theorem v1931_pb_checked : Scalar.distance (sourceCoefficient 22 51 1 1) v1931_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1931_pg : Scalar.QComplex := ((-93086402358633601854814 : Int)/10^30,(69720578101471054284 : Int)/10^30)
theorem v1931_pg_checked : Scalar.distance (sourceCoefficient 22 51 1 2) v1931_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1931_mb : Scalar.QComplex := ((-695516722570247213467624 : Int)/10^30,(-431476947191890947793214395 : Int)/10^30)
theorem v1931_mb_checked : Scalar.distance (sourceCoefficient 22 51 3 1) v1931_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1931_mg : Scalar.QComplex := ((-93086307532592941685331 : Int)/10^30,(150049924920883284488 : Int)/10^30)
theorem v1931_mg_checked : Scalar.distance (sourceCoefficient 22 51 3 2) v1931_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1931_upper : Scalar.QComplex := ((999996937442052011078616048993 : Int)/10^30,(-2474895253685831847671888658 : Int)/10^30)
theorem v1931_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 51 5) 1) 14) v1931_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1931 : Material (22 : Basis) (51 : Basis) where
  plus := ![v1931_pa,v1931_pb,v1931_pg]
  minus := ![(Primitive.Addresses.material1931 1).one,v1931_mb,v1931_mg]
  upper := v1931_upper
  lower := (Primitive.Addresses.material1931 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1931_pa_checked.trans (by decide +kernel)
    · exact v1931_pb_checked.trans (by decide +kernel)
    · exact v1931_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 51 Primitive.Addresses.material1931
    · exact v1931_mb_checked.trans (by decide +kernel)
    · exact v1931_mg_checked.trans (by decide +kernel)
  upper_error := v1931_upper_checked
  lower_error := reuse_lower_error 22 51 Primitive.Addresses.material1931

def v1932_pa : Scalar.QComplex := ((999999701099007020081485401040 : Int)/10^30,(-773176497714482669605861647 : Int)/10^30)
theorem v1932_pa_checked : Scalar.distance (sourceCoefficient 22 52 1 0) v1932_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1932_pb : Scalar.QComplex := ((-333608267104541778809532 : Int)/10^30,(-431477377254544723410994554 : Int)/10^30)
theorem v1932_pb_checked : Scalar.distance (sourceCoefficient 22 52 1 1) v1932_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1932_pg : Scalar.QComplex := ((-93086400479358595396694 : Int)/10^30,(71972238620051810035 : Int)/10^30)
theorem v1932_pg_checked : Scalar.distance (sourceCoefficient 22 52 1 2) v1932_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1932_mb : Scalar.QComplex := ((-705953686437925436179296 : Int)/10^30,(-431476928706888328611604420 : Int)/10^30)
theorem v1932_mb_checked : Scalar.distance (sourceCoefficient 22 52 3 1) v1932_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1932_mg : Scalar.QComplex := ((-93086303710237018457194 : Int)/10^30,(152301582979338232034 : Int)/10^30)
theorem v1932_mg_checked : Scalar.distance (sourceCoefficient 22 52 3 2) v1932_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1932_upper : Scalar.QComplex := ((999996877284427418449921720985 : Int)/10^30,(-2499084110991575432060318602 : Int)/10^30)
theorem v1932_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 52 5) 1) 14) v1932_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1932 : Material (22 : Basis) (52 : Basis) where
  plus := ![v1932_pa,v1932_pb,v1932_pg]
  minus := ![(Primitive.Addresses.material1932 1).one,v1932_mb,v1932_mg]
  upper := v1932_upper
  lower := (Primitive.Addresses.material1932 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1932_pa_checked.trans (by decide +kernel)
    · exact v1932_pb_checked.trans (by decide +kernel)
    · exact v1932_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 52 Primitive.Addresses.material1932
    · exact v1932_mb_checked.trans (by decide +kernel)
    · exact v1932_mg_checked.trans (by decide +kernel)
  upper_error := v1932_upper_checked
  lower_error := reuse_lower_error 22 52 Primitive.Addresses.material1932

def v1933_pa : Scalar.QComplex := ((999999698229319274157942819609 : Int)/10^30,(-776879186480201932190834585 : Int)/10^30)
theorem v1933_pa_checked : Scalar.distance (sourceCoefficient 22 53 1 0) v1933_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1933_pb : Scalar.QComplex := ((-335205893831188675568987 : Int)/10^30,(-431477375773949028508994749 : Int)/10^30)
theorem v1933_pb_checked : Scalar.distance (sourceCoefficient 22 53 1 1) v1933_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1933_pg : Scalar.QComplex := ((-93086400186083154422362 : Int)/10^30,(72316908672057556721 : Int)/10^30)
theorem v1933_pg_checked : Scalar.distance (sourceCoefficient 22 53 1 2) v1933_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1933_mb : Scalar.QComplex := ((-707551311292015486313944 : Int)/10^30,(-431476925847613274343470420 : Int)/10^30)
theorem v1933_mb_checked : Scalar.distance (sourceCoefficient 22 53 3 1) v1933_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1933_mg : Scalar.QComplex := ((-93086303119526955164640 : Int)/10^30,(152646252649924069233 : Int)/10^30)
theorem v1933_mg_checked : Scalar.distance (sourceCoefficient 22 53 3 2) v1933_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1933_upper : Scalar.QComplex := ((999996868024239042258610107684 : Int)/10^30,(-2502786789289754013056970435 : Int)/10^30)
theorem v1933_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 53 5) 1) 14) v1933_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1933 : Material (22 : Basis) (53 : Basis) where
  plus := ![v1933_pa,v1933_pb,v1933_pg]
  minus := ![(Primitive.Addresses.material1933 1).one,v1933_mb,v1933_mg]
  upper := v1933_upper
  lower := (Primitive.Addresses.material1933 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1933_pa_checked.trans (by decide +kernel)
    · exact v1933_pb_checked.trans (by decide +kernel)
    · exact v1933_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 53 Primitive.Addresses.material1933
    · exact v1933_mb_checked.trans (by decide +kernel)
    · exact v1933_mg_checked.trans (by decide +kernel)
  upper_error := v1933_upper_checked
  lower_error := reuse_lower_error 22 53 Primitive.Addresses.material1933

def v1934_pa : Scalar.QComplex := ((999999696765095664556518079048 : Int)/10^30,(-778761655912436251553630665 : Int)/10^30)
theorem v1934_pa_checked : Scalar.distance (sourceCoefficient 22 54 1 0) v1934_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1934_pb : Scalar.QComplex := ((-336018136950337389322130 : Int)/10^30,(-431477375018180854732551484 : Int)/10^30)
theorem v1934_pb_checked : Scalar.distance (sourceCoefficient 22 54 1 1) v1934_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1934_pg : Scalar.QComplex := ((-93086400036409231946571 : Int)/10^30,(72492141017428966139 : Int)/10^30)
theorem v1934_pg_checked : Scalar.distance (sourceCoefficient 22 54 1 2) v1934_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1934_mb : Scalar.QComplex := ((-708363553456535070029551 : Int)/10^30,(-431476924390916152220814704 : Int)/10^30)
theorem v1934_mb_checked : Scalar.distance (sourceCoefficient 22 54 3 1) v1934_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1934_mg : Scalar.QComplex := ((-93086302818635466535630 : Int)/10^30,(152821484800886613922 : Int)/10^30)
theorem v1934_mg_checked : Scalar.distance (sourceCoefficient 22 54 3 2) v1934_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1934_upper : Scalar.QComplex := ((999996863311046149702677967857 : Int)/10^30,(-2504669253391154126655987880 : Int)/10^30)
theorem v1934_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 54 5) 1) 14) v1934_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1934 : Material (22 : Basis) (54 : Basis) where
  plus := ![v1934_pa,v1934_pb,v1934_pg]
  minus := ![(Primitive.Addresses.material1934 1).one,v1934_mb,v1934_mg]
  upper := v1934_upper
  lower := (Primitive.Addresses.material1934 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1934_pa_checked.trans (by decide +kernel)
    · exact v1934_pb_checked.trans (by decide +kernel)
    · exact v1934_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 54 Primitive.Addresses.material1934
    · exact v1934_mb_checked.trans (by decide +kernel)
    · exact v1934_mg_checked.trans (by decide +kernel)
  upper_error := v1934_upper_checked
  lower_error := reuse_lower_error 22 54 Primitive.Addresses.material1934

def v1935_pa : Scalar.QComplex := ((999999684698378479006140531605 : Int)/10^30,(-794105247197671641961621622 : Int)/10^30)
theorem v1935_pa_checked : Scalar.distance (sourceCoefficient 22 55 1 0) v1935_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1935_pb : Scalar.QComplex := ((-342638550631363537758683 : Int)/10^30,(-431477368782052749904795793 : Int)/10^30)
theorem v1935_pb_checked : Scalar.distance (sourceCoefficient 22 55 1 1) v1935_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1935_pg : Scalar.QComplex := ((-93086398802098115347217 : Int)/10^30,(73920421038709786321 : Int)/10^30)
theorem v1935_pg_checked : Scalar.distance (sourceCoefficient 22 55 1 2) v1935_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1935_mb : Scalar.QComplex := ((-714983959290980947484989 : Int)/10^30,(-431476912441671535026506470 : Int)/10^30)
theorem v1935_mb_checked : Scalar.distance (sourceCoefficient 22 55 3 1) v1935_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1935_mg : Scalar.QComplex := ((-93086300351783478505582 : Int)/10^30,(154249763225198604244 : Int)/10^30)
theorem v1935_mg_checked : Scalar.distance (sourceCoefficient 22 55 3 2) v1935_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1935_upper : Scalar.QComplex := ((999996824762700337521812155777 : Int)/10^30,(-2520012800997853504320777365 : Int)/10^30)
theorem v1935_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 55 5) 1) 14) v1935_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1935 : Material (22 : Basis) (55 : Basis) where
  plus := ![v1935_pa,v1935_pb,v1935_pg]
  minus := ![(Primitive.Addresses.material1935 1).one,v1935_mb,v1935_mg]
  upper := v1935_upper
  lower := (Primitive.Addresses.material1935 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1935_pa_checked.trans (by decide +kernel)
    · exact v1935_pb_checked.trans (by decide +kernel)
    · exact v1935_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 55 Primitive.Addresses.material1935
    · exact v1935_mb_checked.trans (by decide +kernel)
    · exact v1935_mg_checked.trans (by decide +kernel)
  upper_error := v1935_upper_checked
  lower_error := reuse_lower_error 22 55 Primitive.Addresses.material1935

def v1936_pa : Scalar.QComplex := ((999999681800042741351843422566 : Int)/10^30,(-797746709968824323793439127 : Int)/10^30)
theorem v1936_pa_checked : Scalar.distance (sourceCoefficient 22 56 1 0) v1936_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1936_pb : Scalar.QComplex := ((-344209759702883233218703 : Int)/10^30,(-431477367282159028201512114 : Int)/10^30)
theorem v1936_pb_checked : Scalar.distance (sourceCoefficient 22 56 1 1) v1936_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1936_pg : Scalar.QComplex := ((-93086398505407638432277 : Int)/10^30,(74259391779871119757 : Int)/10^30)
theorem v1936_pg_checked : Scalar.distance (sourceCoefficient 22 56 1 2) v1936_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1936_mb : Scalar.QComplex := ((-716555166483126968691897 : Int)/10^30,(-431476909585895707710381444 : Int)/10^30)
theorem v1936_mb_checked : Scalar.distance (sourceCoefficient 22 56 3 1) v1936_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1936_mg : Scalar.QComplex := ((-93086299762576629115292 : Int)/10^30,(154588733584115119883 : Int)/10^30)
theorem v1936_mg_checked : Scalar.distance (sourceCoefficient 22 56 3 2) v1936_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1936_upper : Scalar.QComplex := ((999996815579534524510644194466 : Int)/10^30,(-2523654253343210596558881603 : Int)/10^30)
theorem v1936_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 56 5) 1) 14) v1936_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1936 : Material (22 : Basis) (56 : Basis) where
  plus := ![v1936_pa,v1936_pb,v1936_pg]
  minus := ![(Primitive.Addresses.material1936 1).one,v1936_mb,v1936_mg]
  upper := v1936_upper
  lower := (Primitive.Addresses.material1936 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1936_pa_checked.trans (by decide +kernel)
    · exact v1936_pb_checked.trans (by decide +kernel)
    · exact v1936_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 56 Primitive.Addresses.material1936
    · exact v1936_mb_checked.trans (by decide +kernel)
    · exact v1936_mg_checked.trans (by decide +kernel)
  upper_error := v1936_upper_checked
  lower_error := reuse_lower_error 22 56 Primitive.Addresses.material1936

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
