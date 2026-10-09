import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B076
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B077

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1841_pa : Scalar.QComplex := ((999999850348855074516004199101 : Int)/10^30,(-547085246972994889672884316 : Int)/10^30)
theorem v1841_pa_checked : Scalar.distance (sourceCoefficient 21 36 1 0) v1841_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1841_pb : Scalar.QComplex := ((-236054984058686301366455 : Int)/10^30,(-431477452625294002543237798 : Int)/10^30)
theorem v1841_pb_checked : Scalar.distance (sourceCoefficient 21 36 1 1) v1841_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1841_pg : Scalar.QComplex := ((-93086415556122740638568 : Int)/10^30,(50926212265518215256 : Int)/10^30)
theorem v1841_pg_checked : Scalar.distance (sourceCoefficient 21 36 1 2) v1841_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1841_mb : Scalar.QComplex := ((-608400504757177697349148 : Int)/10^30,(-431477088261699175573632756 : Int)/10^30)
theorem v1841_mb_checked : Scalar.distance (sourceCoefficient 21 36 3 1) v1841_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1841_mg : Scalar.QComplex := ((-93086336948768416053098 : Int)/10^30,(131255577471770525061 : Int)/10^30)
theorem v1841_mg_checked : Scalar.distance (sourceCoefficient 21 36 3 2) v1841_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1841_upper : Scalar.QComplex := ((999997416747041124530396640324 : Int)/10^30,(-2272993454578144989131246912 : Int)/10^30)
theorem v1841_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 36 5) 1) 14) v1841_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1841 : Material (21 : Basis) (36 : Basis) where
  plus := ![v1841_pa,v1841_pb,v1841_pg]
  minus := ![(Primitive.Addresses.material1841 1).one,v1841_mb,v1841_mg]
  upper := v1841_upper
  lower := (Primitive.Addresses.material1841 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1841_pa_checked.trans (by decide +kernel)
    · exact v1841_pb_checked.trans (by decide +kernel)
    · exact v1841_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 36 Primitive.Addresses.material1841
    · exact v1841_mb_checked.trans (by decide +kernel)
    · exact v1841_mg_checked.trans (by decide +kernel)
  upper_error := v1841_upper_checked
  lower_error := reuse_lower_error 21 36 Primitive.Addresses.material1841

def v1842_pa : Scalar.QComplex := ((999999846553454285467111669033 : Int)/10^30,(-553979302757082599781434577 : Int)/10^30)
theorem v1842_pa_checked : Scalar.distance (sourceCoefficient 21 37 1 0) v1842_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1842_pb : Scalar.QComplex := ((-239029614003585738927249 : Int)/10^30,(-431477450756189220284836389 : Int)/10^30)
theorem v1842_pb_checked : Scalar.distance (sourceCoefficient 21 37 1 1) v1842_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1842_pg : Scalar.QComplex := ((-93086415177853402216429 : Int)/10^30,(51567955289308147531 : Int)/10^30)
theorem v1842_pg_checked : Scalar.distance (sourceCoefficient 21 37 1 2) v1842_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1842_mb : Scalar.QComplex := ((-611375131981533213384900 : Int)/10^30,(-431477083825623419179579992 : Int)/10^30)
theorem v1842_mb_checked : Scalar.distance (sourceCoefficient 21 37 3 1) v1842_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1842_mg : Scalar.QComplex := ((-93086336016703891980070 : Int)/10^30,(131897319930180798035 : Int)/10^30)
theorem v1842_mg_checked : Scalar.distance (sourceCoefficient 21 37 3 2) v1842_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1842_upper : Scalar.QComplex := ((999997401053131128804942047118 : Int)/10^30,(-2279887493543828995692739419 : Int)/10^30)
theorem v1842_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 37 5) 1) 14) v1842_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1842 : Material (21 : Basis) (37 : Basis) where
  plus := ![v1842_pa,v1842_pb,v1842_pg]
  minus := ![(Primitive.Addresses.material1842 1).one,v1842_mb,v1842_mg]
  upper := v1842_upper
  lower := (Primitive.Addresses.material1842 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1842_pa_checked.trans (by decide +kernel)
    · exact v1842_pb_checked.trans (by decide +kernel)
    · exact v1842_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 37 Primitive.Addresses.material1842
    · exact v1842_mb_checked.trans (by decide +kernel)
    · exact v1842_mg_checked.trans (by decide +kernel)
  upper_error := v1842_upper_checked
  lower_error := reuse_lower_error 21 37 Primitive.Addresses.material1842

def v1843_pa : Scalar.QComplex := ((999999833373705051926128409262 : Int)/10^30,(-577280315039258527339033413 : Int)/10^30)
theorem v1843_pa_checked : Scalar.distance (sourceCoefficient 21 38 1 0) v1843_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1843_pb : Scalar.QComplex := ((-249083476445022200816874 : Int)/10^30,(-431477444236473261618595975 : Int)/10^30)
theorem v1843_pb_checked : Scalar.distance (sourceCoefficient 21 38 1 1) v1843_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1843_pg : Scalar.QComplex := ((-93086413861147748722284 : Int)/10^30,(53736963273629266213 : Int)/10^30)
theorem v1843_pg_checked : Scalar.distance (sourceCoefficient 21 38 1 2) v1843_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1843_mb : Scalar.QComplex := ((-621428985053235968892667 : Int)/10^30,(-431477068629879410297186454 : Int)/10^30)
theorem v1843_mb_checked : Scalar.distance (sourceCoefficient 21 38 3 1) v1843_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1843_mg : Scalar.QComplex := ((-93086332828242526779738 : Int)/10^30,(134066325970623438848 : Int)/10^30)
theorem v1843_mg_checked : Scalar.distance (sourceCoefficient 21 38 3 2) v1843_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1843_upper : Scalar.QComplex := ((999997347657968177238327736168 : Int)/10^30,(-2303188448374832738543562097 : Int)/10^30)
theorem v1843_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 38 5) 1) 14) v1843_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1843 : Material (21 : Basis) (38 : Basis) where
  plus := ![v1843_pa,v1843_pb,v1843_pg]
  minus := ![(Primitive.Addresses.material1843 1).one,v1843_mb,v1843_mg]
  upper := v1843_upper
  lower := (Primitive.Addresses.material1843 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1843_pa_checked.trans (by decide +kernel)
    · exact v1843_pb_checked.trans (by decide +kernel)
    · exact v1843_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 38 Primitive.Addresses.material1843
    · exact v1843_mb_checked.trans (by decide +kernel)
    · exact v1843_mg_checked.trans (by decide +kernel)
  upper_error := v1843_upper_checked
  lower_error := reuse_lower_error 21 38 Primitive.Addresses.material1843

def v1844_pa : Scalar.QComplex := ((999999825479019812033821930382 : Int)/10^30,(-590797706426116578547765137 : Int)/10^30)
theorem v1844_pa_checked : Scalar.distance (sourceCoefficient 21 39 1 0) v1844_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1844_pb : Scalar.QComplex := ((-254915926598582321780375 : Int)/10^30,(-431477440311092297447476990 : Int)/10^30)
theorem v1844_pb_checked : Scalar.distance (sourceCoefficient 21 39 1 1) v1844_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1844_pg : Scalar.QComplex := ((-93086413070275285480736 : Int)/10^30,(54995248939177469844 : Int)/10^30)
theorem v1844_pg_checked : Scalar.distance (sourceCoefficient 21 39 1 2) v1844_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1844_mb : Scalar.QComplex := ((-627261429647681362061678 : Int)/10^30,(-431477059671358109006050005 : Int)/10^30)
theorem v1844_mb_checked : Scalar.distance (sourceCoefficient 21 39 3 1) v1844_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1844_mg : Scalar.QComplex := ((-93086330951526499730699 : Int)/10^30,(135324610485167066496 : Int)/10^30)
theorem v1844_mg_checked : Scalar.distance (sourceCoefficient 21 39 3 2) v1844_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1844_upper : Scalar.QComplex := ((999997316433503450002693109786 : Int)/10^30,(-2316705806003613659557105418 : Int)/10^30)
theorem v1844_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 39 5) 1) 14) v1844_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1844 : Material (21 : Basis) (39 : Basis) where
  plus := ![v1844_pa,v1844_pb,v1844_pg]
  minus := ![(Primitive.Addresses.material1844 1).one,v1844_mb,v1844_mg]
  upper := v1844_upper
  lower := (Primitive.Addresses.material1844 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1844_pa_checked.trans (by decide +kernel)
    · exact v1844_pb_checked.trans (by decide +kernel)
    · exact v1844_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 39 Primitive.Addresses.material1844
    · exact v1844_mb_checked.trans (by decide +kernel)
    · exact v1844_mg_checked.trans (by decide +kernel)
  upper_error := v1844_upper_checked
  lower_error := reuse_lower_error 21 39 Primitive.Addresses.material1844

def v1845_pa : Scalar.QComplex := ((999999811788487953079927474394 : Int)/10^30,(-613533200951885633212013965 : Int)/10^30)
theorem v1845_pa_checked : Scalar.distance (sourceCoefficient 21 40 1 0) v1845_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1845_pb : Scalar.QComplex := ((-264725780720854938545175 : Int)/10^30,(-431477433471731116253742332 : Int)/10^30)
theorem v1845_pb_checked : Scalar.distance (sourceCoefficient 21 40 1 1) v1845_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1845_pg : Scalar.QComplex := ((-93086411695316232813511 : Int)/10^30,(57111614881615803580 : Int)/10^30)
theorem v1845_pg_checked : Scalar.distance (sourceCoefficient 21 40 1 2) v1845_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1845_mb : Scalar.QComplex := ((-637071274215236290645591 : Int)/10^30,(-431477044366537186326348115 : Int)/10^30)
theorem v1845_mb_checked : Scalar.distance (sourceCoefficient 21 40 3 1) v1845_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1845_mg : Scalar.QComplex := ((-93086327750239468282979 : Int)/10^30,(137440974453057900566 : Int)/10^30)
theorem v1845_mg_checked : Scalar.distance (sourceCoefficient 21 40 3 2) v1845_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1845_upper : Scalar.QComplex := ((999997263503590977962048729731 : Int)/10^30,(-2339441243038918323675589292 : Int)/10^30)
theorem v1845_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 40 5) 1) 14) v1845_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1845 : Material (21 : Basis) (40 : Basis) where
  plus := ![v1845_pa,v1845_pb,v1845_pg]
  minus := ![(Primitive.Addresses.material1845 1).one,v1845_mb,v1845_mg]
  upper := v1845_upper
  lower := (Primitive.Addresses.material1845 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1845_pa_checked.trans (by decide +kernel)
    · exact v1845_pb_checked.trans (by decide +kernel)
    · exact v1845_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 40 Primitive.Addresses.material1845
    · exact v1845_mb_checked.trans (by decide +kernel)
    · exact v1845_mg_checked.trans (by decide +kernel)
  upper_error := v1845_upper_checked
  lower_error := reuse_lower_error 21 40 Primitive.Addresses.material1845

def v1846_pa : Scalar.QComplex := ((999999802797183505975224169138 : Int)/10^30,(-628017192518722944623338008 : Int)/10^30)
theorem v1846_pa_checked : Scalar.distance (sourceCoefficient 21 41 1 0) v1846_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1846_pb : Scalar.QComplex := ((-270975297007460747698078 : Int)/10^30,(-431477428959543093262221031 : Int)/10^30)
theorem v1846_pb_checked : Scalar.distance (sourceCoefficient 21 41 1 1) v1846_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1846_pg : Scalar.QComplex := ((-93086410790105069423809 : Int)/10^30,(58459877894498916886 : Int)/10^30)
theorem v1846_pg_checked : Scalar.distance (sourceCoefficient 21 41 1 2) v1846_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1846_mb : Scalar.QComplex := ((-643320784281046526854027 : Int)/10^30,(-431477034461299755852805805 : Int)/10^30)
theorem v1846_mb_checked : Scalar.distance (sourceCoefficient 21 41 3 1) v1846_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1846_mg : Scalar.QComplex := ((-93086325681538385338574 : Int)/10^30,(138789236182764610703 : Int)/10^30)
theorem v1846_mg_checked : Scalar.distance (sourceCoefficient 21 41 3 2) v1846_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1846_upper : Scalar.QComplex := ((999997229514244455438641997386 : Int)/10^30,(-2353925197515375814514597716 : Int)/10^30)
theorem v1846_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 41 5) 1) 14) v1846_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1846 : Material (21 : Basis) (41 : Basis) where
  plus := ![v1846_pa,v1846_pb,v1846_pg]
  minus := ![(Primitive.Addresses.material1846 1).one,v1846_mb,v1846_mg]
  upper := v1846_upper
  lower := (Primitive.Addresses.material1846 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1846_pa_checked.trans (by decide +kernel)
    · exact v1846_pb_checked.trans (by decide +kernel)
    · exact v1846_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 41 Primitive.Addresses.material1846
    · exact v1846_mb_checked.trans (by decide +kernel)
    · exact v1846_mg_checked.trans (by decide +kernel)
  upper_error := v1846_upper_checked
  lower_error := reuse_lower_error 21 41 Primitive.Addresses.material1846

def v1847_pa : Scalar.QComplex := ((999999795391396644882394401836 : Int)/10^30,(-639700840116342698761305326 : Int)/10^30)
theorem v1847_pa_checked : Scalar.distance (sourceCoefficient 21 42 1 0) v1847_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1847_pb : Scalar.QComplex := ((-276016527887374878336223 : Int)/10^30,(-431477425231799533459316231 : Int)/10^30)
theorem v1847_pb_checked : Scalar.distance (sourceCoefficient 21 42 1 1) v1847_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1847_pg : Scalar.QComplex := ((-93086410043306533784711 : Int)/10^30,(59547466892041584318 : Int)/10^30)
theorem v1847_pg_checked : Scalar.distance (sourceCoefficient 21 42 1 2) v1847_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1847_mb : Scalar.QComplex := ((-648362010067005204494761 : Int)/10^30,(-431477026383202383303690608 : Int)/10^30)
theorem v1847_mb_checked : Scalar.distance (sourceCoefficient 21 42 3 1) v1847_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1847_mg : Scalar.QComplex := ((-93086323996199806077487 : Int)/10^30,(139876824130894687378 : Int)/10^30)
theorem v1847_mg_checked : Scalar.distance (sourceCoefficient 21 42 3 2) v1847_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1847_upper : Scalar.QComplex := ((999997201943552803134021210167 : Int)/10^30,(-2365608814929858655144277370 : Int)/10^30)
theorem v1847_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 42 5) 1) 14) v1847_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1847 : Material (21 : Basis) (42 : Basis) where
  plus := ![v1847_pa,v1847_pb,v1847_pg]
  minus := ![(Primitive.Addresses.material1847 1).one,v1847_mb,v1847_mg]
  upper := v1847_upper
  lower := (Primitive.Addresses.material1847 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1847_pa_checked.trans (by decide +kernel)
    · exact v1847_pb_checked.trans (by decide +kernel)
    · exact v1847_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 42 Primitive.Addresses.material1847
    · exact v1847_mb_checked.trans (by decide +kernel)
    · exact v1847_mg_checked.trans (by decide +kernel)
  upper_error := v1847_upper_checked
  lower_error := reuse_lower_error 21 42 Primitive.Addresses.material1847

def v1848_pa : Scalar.QComplex := ((999999785370461396940200583638 : Int)/10^30,(-655178625368899498769744285 : Int)/10^30)
theorem v1848_pa_checked : Scalar.distance (sourceCoefficient 21 43 1 0) v1848_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1848_pb : Scalar.QComplex := ((-282694843701056035689919 : Int)/10^30,(-431477420172583259467642383 : Int)/10^30)
theorem v1848_pb_checked : Scalar.distance (sourceCoefficient 21 43 1 1) v1848_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1848_pg : Scalar.QComplex := ((-93086409031165441577290 : Int)/10^30,(60988238599443596606 : Int)/10^30)
theorem v1848_pg_checked : Scalar.distance (sourceCoefficient 21 43 1 2) v1848_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1848_mb : Scalar.QComplex := ((-655040319028168384492050 : Int)/10^30,(-431477015560902226061377502 : Int)/10^30)
theorem v1848_mb_checked : Scalar.distance (sourceCoefficient 21 43 3 1) v1848_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1848_mg : Scalar.QComplex := ((-93086321740737997197389 : Int)/10^30,(141317594428399369048 : Int)/10^30)
theorem v1848_mg_checked : Scalar.distance (sourceCoefficient 21 43 3 2) v1848_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1848_upper : Scalar.QComplex := ((999997165209379267994321989833 : Int)/10^30,(-2381086559834847324039114035 : Int)/10^30)
theorem v1848_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 43 5) 1) 14) v1848_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1848 : Material (21 : Basis) (43 : Basis) where
  plus := ![v1848_pa,v1848_pb,v1848_pg]
  minus := ![(Primitive.Addresses.material1848 1).one,v1848_mb,v1848_mg]
  upper := v1848_upper
  lower := (Primitive.Addresses.material1848 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1848_pa_checked.trans (by decide +kernel)
    · exact v1848_pb_checked.trans (by decide +kernel)
    · exact v1848_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 43 Primitive.Addresses.material1848
    · exact v1848_mb_checked.trans (by decide +kernel)
    · exact v1848_mg_checked.trans (by decide +kernel)
  upper_error := v1848_upper_checked
  lower_error := reuse_lower_error 21 43 Primitive.Addresses.material1848

def v1849_pa : Scalar.QComplex := ((999999781516734809863319959536 : Int)/10^30,(-661034403526273503695671911 : Int)/10^30)
theorem v1849_pa_checked : Scalar.distance (sourceCoefficient 21 44 1 0) v1849_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1849_pb : Scalar.QComplex := ((-285221480105935310971988 : Int)/10^30,(-431477418222573057835348130 : Int)/10^30)
theorem v1849_pb_checked : Scalar.distance (sourceCoefficient 21 44 1 1) v1849_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1849_pg : Scalar.QComplex := ((-93086408641454215128784 : Int)/10^30,(61533332056709944351 : Int)/10^30)
theorem v1849_pg_checked : Scalar.distance (sourceCoefficient 21 44 1 2) v1849_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1849_mb : Scalar.QComplex := ((-657566952809494474439967 : Int)/10^30,(-431477011430519328575575620 : Int)/10^30)
theorem v1849_mb_checked : Scalar.distance (sourceCoefficient 21 44 3 1) v1849_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1849_mg : Scalar.QComplex := ((-93086320880635812333298 : Int)/10^30,(141862687346399274168 : Int)/10^30)
theorem v1849_mg_checked : Scalar.distance (sourceCoefficient 21 44 3 2) v1849_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1849_upper : Scalar.QComplex := ((999997151249116553007649758576 : Int)/10^30,(-2386942322619545149629220553 : Int)/10^30)
theorem v1849_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 44 5) 1) 14) v1849_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1849 : Material (21 : Basis) (44 : Basis) where
  plus := ![v1849_pa,v1849_pb,v1849_pg]
  minus := ![(Primitive.Addresses.material1849 1).one,v1849_mb,v1849_mg]
  upper := v1849_upper
  lower := (Primitive.Addresses.material1849 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1849_pa_checked.trans (by decide +kernel)
    · exact v1849_pb_checked.trans (by decide +kernel)
    · exact v1849_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 44 Primitive.Addresses.material1849
    · exact v1849_mb_checked.trans (by decide +kernel)
    · exact v1849_mg_checked.trans (by decide +kernel)
  upper_error := v1849_upper_checked
  lower_error := reuse_lower_error 21 44 Primitive.Addresses.material1849

def v1850_pa : Scalar.QComplex := ((999999779586684060469054516554 : Int)/10^30,(-663947726328686246151380000 : Int)/10^30)
theorem v1850_pa_checked : Scalar.distance (sourceCoefficient 21 45 1 0) v1850_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1850_pb : Scalar.QComplex := ((-286478513285717104113617 : Int)/10^30,(-431477417245069912037569554 : Int)/10^30)
theorem v1850_pb_checked : Scalar.distance (sourceCoefficient 21 45 1 1) v1850_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1850_pg : Scalar.QComplex := ((-93086408446180784884043 : Int)/10^30,(61804522862484971849 : Int)/10^30)
theorem v1850_pg_checked : Scalar.distance (sourceCoefficient 21 45 1 2) v1850_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1850_mb : Scalar.QComplex := ((-658823984677684175778382 : Int)/10^30,(-431477009368253527267986775 : Int)/10^30)
theorem v1850_mb_checked : Scalar.distance (sourceCoefficient 21 45 3 1) v1850_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1850_mg : Scalar.QComplex := ((-93086320451337003394418 : Int)/10^30,(142133877882685395132 : Int)/10^30)
theorem v1850_mg_checked : Scalar.distance (sourceCoefficient 21 45 3 2) v1850_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1850_upper : Scalar.QComplex := ((999997144290937815812941296516 : Int)/10^30,(-2389855637751813300209102972 : Int)/10^30)
theorem v1850_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 45 5) 1) 14) v1850_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1850 : Material (21 : Basis) (45 : Basis) where
  plus := ![v1850_pa,v1850_pb,v1850_pg]
  minus := ![(Primitive.Addresses.material1850 1).one,v1850_mb,v1850_mg]
  upper := v1850_upper
  lower := (Primitive.Addresses.material1850 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1850_pa_checked.trans (by decide +kernel)
    · exact v1850_pb_checked.trans (by decide +kernel)
    · exact v1850_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 45 Primitive.Addresses.material1850
    · exact v1850_mb_checked.trans (by decide +kernel)
    · exact v1850_mg_checked.trans (by decide +kernel)
  upper_error := v1850_upper_checked
  lower_error := reuse_lower_error 21 45 Primitive.Addresses.material1850

def v1851_pa : Scalar.QComplex := ((999999768587787771995054933580 : Int)/10^30,(-680311965868893064462466102 : Int)/10^30)
theorem v1851_pa_checked : Scalar.distance (sourceCoefficient 21 46 1 0) v1851_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1851_pb : Scalar.QComplex := ((-293539314085505502386796 : Int)/10^30,(-431477411663655986856012353 : Int)/10^30)
theorem v1851_pb_checked : Scalar.distance (sourceCoefficient 21 46 1 1) v1851_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1851_pg : Scalar.QComplex := ((-93086407332193102142642 : Int)/10^30,(63327811422665767682 : Int)/10^30)
theorem v1851_pg_checked : Scalar.distance (sourceCoefficient 21 46 1 2) v1851_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1851_mb : Scalar.QComplex := ((-665884778031904901872290 : Int)/10^30,(-431476997693688596747589667 : Int)/10^30)
theorem v1851_mb_checked : Scalar.distance (sourceCoefficient 21 46 3 1) v1851_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1851_mg : Scalar.QComplex := ((-93086318022820314375478 : Int)/10^30,(143657164914355044220 : Int)/10^30)
theorem v1851_mg_checked : Scalar.distance (sourceCoefficient 21 46 3 2) v1851_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1851_upper : Scalar.QComplex := ((999997105048865014720375944143 : Int)/10^30,(-2406219833936310420161920183 : Int)/10^30)
theorem v1851_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 46 5) 1) 14) v1851_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1851 : Material (21 : Basis) (46 : Basis) where
  plus := ![v1851_pa,v1851_pb,v1851_pg]
  minus := ![(Primitive.Addresses.material1851 1).one,v1851_mb,v1851_mg]
  upper := v1851_upper
  lower := (Primitive.Addresses.material1851 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1851_pa_checked.trans (by decide +kernel)
    · exact v1851_pb_checked.trans (by decide +kernel)
    · exact v1851_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 46 Primitive.Addresses.material1851
    · exact v1851_mb_checked.trans (by decide +kernel)
    · exact v1851_mg_checked.trans (by decide +kernel)
  upper_error := v1851_upper_checked
  lower_error := reuse_lower_error 21 46 Primitive.Addresses.material1851

def v1852_pa : Scalar.QComplex := ((999999765900936110324216074002 : Int)/10^30,(-684250007655812784229463769 : Int)/10^30)
theorem v1852_pa_checked : Scalar.distance (sourceCoefficient 21 47 1 0) v1852_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1852_pb : Scalar.QComplex := ((-295238490414425360293778 : Int)/10^30,(-431477410297494857455610221 : Int)/10^30)
theorem v1852_pb_checked : Scalar.distance (sourceCoefficient 21 47 1 1) v1852_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1852_pg : Scalar.QComplex := ((-93086407059771426618079 : Int)/10^30,(63694389654097696918 : Int)/10^30)
theorem v1852_pg_checked : Scalar.distance (sourceCoefficient 21 47 1 2) v1852_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1852_mb : Scalar.QComplex := ((-667583952549208231268518 : Int)/10^30,(-431476994861215332234574675 : Int)/10^30)
theorem v1852_mb_checked : Scalar.distance (sourceCoefficient 21 47 3 1) v1852_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1852_mg : Scalar.QComplex := ((-93086317434058236630861 : Int)/10^30,(144023742774205507880 : Int)/10^30)
theorem v1852_mg_checked : Scalar.distance (sourceCoefficient 21 47 3 2) v1852_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1852_upper : Scalar.QComplex := ((999997095565314486936206880433 : Int)/10^30,(-2410157865220717274430619115 : Int)/10^30)
theorem v1852_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 47 5) 1) 14) v1852_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1852 : Material (21 : Basis) (47 : Basis) where
  plus := ![v1852_pa,v1852_pb,v1852_pg]
  minus := ![(Primitive.Addresses.material1852 1).one,v1852_mb,v1852_mg]
  upper := v1852_upper
  lower := (Primitive.Addresses.material1852 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1852_pa_checked.trans (by decide +kernel)
    · exact v1852_pb_checked.trans (by decide +kernel)
    · exact v1852_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 47 Primitive.Addresses.material1852
    · exact v1852_mb_checked.trans (by decide +kernel)
    · exact v1852_mg_checked.trans (by decide +kernel)
  upper_error := v1852_upper_checked
  lower_error := reuse_lower_error 21 47 Primitive.Addresses.material1852

def v1853_pa : Scalar.QComplex := ((999999746755351932208984407065 : Int)/10^30,(-711680568796654905696317139 : Int)/10^30)
theorem v1853_pa_checked : Scalar.distance (sourceCoefficient 21 48 1 0) v1853_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1853_pb : Scalar.QComplex := ((-307074159599785137501673 : Int)/10^30,(-431477400533941613969901317 : Int)/10^30)
theorem v1853_pb_checked : Scalar.distance (sourceCoefficient 21 48 1 1) v1853_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1853_pg : Scalar.QComplex := ((-93086405115485901192647 : Int)/10^30,(66247802516726286659 : Int)/10^30)
theorem v1853_pg_checked : Scalar.distance (sourceCoefficient 21 48 1 2) v1853_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1853_mb : Scalar.QComplex := ((-679419608902100738949587 : Int)/10^30,(-431476974884016275952504600 : Int)/10^30)
theorem v1853_mb_checked : Scalar.distance (sourceCoefficient 21 48 3 1) v1853_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1853_mg : Scalar.QComplex := ((-93086313286293136149595 : Int)/10^30,(146577153008250951059 : Int)/10^30)
theorem v1853_mg_checked : Scalar.distance (sourceCoefficient 21 48 3 2) v1853_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1853_upper : Scalar.QComplex := ((999997029077098775893858437422 : Int)/10^30,(-2437588352463419379075384695 : Int)/10^30)
theorem v1853_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 48 5) 1) 14) v1853_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1853 : Material (21 : Basis) (48 : Basis) where
  plus := ![v1853_pa,v1853_pb,v1853_pg]
  minus := ![(Primitive.Addresses.material1853 1).one,v1853_mb,v1853_mg]
  upper := v1853_upper
  lower := (Primitive.Addresses.material1853 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1853_pa_checked.trans (by decide +kernel)
    · exact v1853_pb_checked.trans (by decide +kernel)
    · exact v1853_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 48 Primitive.Addresses.material1853
    · exact v1853_mb_checked.trans (by decide +kernel)
    · exact v1853_mg_checked.trans (by decide +kernel)
  upper_error := v1853_upper_checked
  lower_error := reuse_lower_error 21 48 Primitive.Addresses.material1853

def v1854_pa : Scalar.QComplex := ((999999730828217101730066049990 : Int)/10^30,(-733718947106513775400237298 : Int)/10^30)
theorem v1854_pa_checked : Scalar.distance (sourceCoefficient 21 49 1 0) v1854_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1854_pb : Scalar.QComplex := ((-316583223249700183156505 : Int)/10^30,(-431477392376063663641305051 : Int)/10^30)
theorem v1854_pb_checked : Scalar.distance (sourceCoefficient 21 49 1 1) v1854_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1854_pg : Scalar.QComplex := ((-93086403494200562178194 : Int)/10^30,(68299276345934926060 : Int)/10^30)
theorem v1854_pg_checked : Scalar.distance (sourceCoefficient 21 49 1 2) v1854_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1854_mb : Scalar.QComplex := ((-688928661971475548113416 : Int)/10^30,(-431476958520247705626594316 : Int)/10^30)
theorem v1854_mb_checked : Scalar.distance (sourceCoefficient 21 49 3 1) v1854_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1854_mg : Scalar.QComplex := ((-93086309894678881158120 : Int)/10^30,(148628624674505899271 : Int)/10^30)
theorem v1854_mg_checked : Scalar.distance (sourceCoefficient 21 49 3 2) v1854_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1854_upper : Scalar.QComplex := ((999996975113746010257476798170 : Int)/10^30,(-2459626670460912746993043416 : Int)/10^30)
theorem v1854_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 49 5) 1) 14) v1854_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1854 : Material (21 : Basis) (49 : Basis) where
  plus := ![v1854_pa,v1854_pb,v1854_pg]
  minus := ![(Primitive.Addresses.material1854 1).one,v1854_mb,v1854_mg]
  upper := v1854_upper
  lower := (Primitive.Addresses.material1854 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1854_pa_checked.trans (by decide +kernel)
    · exact v1854_pb_checked.trans (by decide +kernel)
    · exact v1854_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 49 Primitive.Addresses.material1854
    · exact v1854_mb_checked.trans (by decide +kernel)
    · exact v1854_mg_checked.trans (by decide +kernel)
  upper_error := v1854_upper_checked
  lower_error := reuse_lower_error 21 49 Primitive.Addresses.material1854

def v1855_pa : Scalar.QComplex := ((999999728935368528888270306757 : Int)/10^30,(-736294227511114625074760916 : Int)/10^30)
theorem v1855_pa_checked : Scalar.distance (sourceCoefficient 21 50 1 0) v1855_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1855_pb : Scalar.QComplex := ((-317694398708436681685255 : Int)/10^30,(-431477391404546718265197594 : Int)/10^30)
theorem v1855_pb_checked : Scalar.distance (sourceCoefficient 21 50 1 1) v1855_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1855_pg : Scalar.QComplex := ((-93086403301304368567859 : Int)/10^30,(68538999989020743692 : Int)/10^30)
theorem v1855_pg_checked : Scalar.distance (sourceCoefficient 21 50 1 2) v1855_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1855_mb : Scalar.QComplex := ((-690039836178095271766719 : Int)/10^30,(-431476956589836746585933678 : Int)/10^30)
theorem v1855_mb_checked : Scalar.distance (sourceCoefficient 21 50 3 1) v1855_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1855_mg : Scalar.QComplex := ((-93086309494912052140883 : Int)/10^30,(148868348061870921307 : Int)/10^30)
theorem v1855_mg_checked : Scalar.distance (sourceCoefficient 21 50 3 2) v1855_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1855_upper : Scalar.QComplex := ((999996968776199905863520778918 : Int)/10^30,(-2462201943763051028857555605 : Int)/10^30)
theorem v1855_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 50 5) 1) 14) v1855_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1855 : Material (21 : Basis) (50 : Basis) where
  plus := ![v1855_pa,v1855_pb,v1855_pg]
  minus := ![(Primitive.Addresses.material1855 1).one,v1855_mb,v1855_mg]
  upper := v1855_upper
  lower := (Primitive.Addresses.material1855 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1855_pa_checked.trans (by decide +kernel)
    · exact v1855_pb_checked.trans (by decide +kernel)
    · exact v1855_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 50 Primitive.Addresses.material1855
    · exact v1855_mb_checked.trans (by decide +kernel)
    · exact v1855_mg_checked.trans (by decide +kernel)
  upper_error := v1855_upper_checked
  lower_error := reuse_lower_error 21 50 Primitive.Addresses.material1855

def v1856_pa : Scalar.QComplex := ((999999720551959088691783917132 : Int)/10^30,(-747593474912274005594986282 : Int)/10^30)
theorem v1856_pa_checked : Scalar.distance (sourceCoefficient 21 51 1 0) v1856_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1856_pb : Scalar.QComplex := ((-322569769307287514592781 : Int)/10^30,(-431477387096843250678443697 : Int)/10^30)
theorem v1856_pb_checked : Scalar.distance (sourceCoefficient 21 51 1 1) v1856_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1856_pg : Scalar.QComplex := ((-93086402446444216259430 : Int)/10^30,(69590806519034182989 : Int)/10^30)
theorem v1856_pg_checked : Scalar.distance (sourceCoefficient 21 51 1 2) v1856_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1856_mb : Scalar.QComplex := ((-694915201244268734513163 : Int)/10^30,(-431476948074909634686417404 : Int)/10^30)
theorem v1856_mb_checked : Scalar.distance (sourceCoefficient 21 51 3 1) v1856_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1856_mg : Scalar.QComplex := ((-93086307732390554341955 : Int)/10^30,(149920153462542909577 : Int)/10^30)
theorem v1856_mg_checked : Scalar.distance (sourceCoefficient 21 51 3 2) v1856_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1856_upper : Scalar.QComplex := ((999996940891326997086426433628 : Int)/10^30,(-2473501159866304551372853268 : Int)/10^30)
theorem v1856_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 51 5) 1) 14) v1856_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1856 : Material (21 : Basis) (51 : Basis) where
  plus := ![v1856_pa,v1856_pb,v1856_pg]
  minus := ![(Primitive.Addresses.material1856 1).one,v1856_mb,v1856_mg]
  upper := v1856_upper
  lower := (Primitive.Addresses.material1856 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1856_pa_checked.trans (by decide +kernel)
    · exact v1856_pb_checked.trans (by decide +kernel)
    · exact v1856_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 51 Primitive.Addresses.material1856
    · exact v1856_mb_checked.trans (by decide +kernel)
    · exact v1856_mg_checked.trans (by decide +kernel)
  upper_error := v1856_upper_checked
  lower_error := reuse_lower_error 21 51 Primitive.Addresses.material1856

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
