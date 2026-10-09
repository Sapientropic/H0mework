import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B169
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B170

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4065_pa : Scalar.QComplex := ((999998506483233285227532868577 : Int)/10^30,(-1728303012448110175460933252 : Int)/10^30)
theorem v4065_pa_checked : Scalar.distance (sourceCoefficient 60 76 1 0) v4065_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4065_pb : Scalar.QComplex := ((-745723884923472347310126 : Int)/10^30,(-431476868235069475938919379 : Int)/10^30)
theorem v4065_pb_checked : Scalar.distance (sourceCoefficient 60 76 1 1) v4065_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4065_pg : Scalar.QComplex := ((-93086289970481969076406 : Int)/10^30,(160881555652903114745 : Int)/10^30)
theorem v4065_pg_checked : Scalar.distance (sourceCoefficient 60 76 1 2) v4065_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4065_mb : Scalar.QComplex := ((-1118068711546495124075304 : Int)/10^30,(-431476064050385433026338661 : Int)/10^30)
theorem v4065_mb_checked : Scalar.distance (sourceCoefficient 60 76 3 1) v4065_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4065_mg : Scalar.QComplex := ((-93086116476665267283057 : Int)/10^30,(241210771543004055419 : Int)/10^30)
theorem v4065_mg_checked : Scalar.distance (sourceCoefficient 60 76 3 2) v4065_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4065_upper : Scalar.QComplex := ((999994034208716893776920296994 : Int)/10^30,(-3454207141378005514068791189 : Int)/10^30)
theorem v4065_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 76 5) 1) 14) v4065_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4065 : Material (60 : Basis) (76 : Basis) where
  plus := ![v4065_pa,v4065_pb,v4065_pg]
  minus := ![(Primitive.Addresses.material4065 1).one,v4065_mb,v4065_mg]
  upper := v4065_upper
  lower := (Primitive.Addresses.material4065 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4065_pa_checked.trans (by decide +kernel)
    · exact v4065_pb_checked.trans (by decide +kernel)
    · exact v4065_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 76 Primitive.Addresses.material4065
    · exact v4065_mb_checked.trans (by decide +kernel)
    · exact v4065_mg_checked.trans (by decide +kernel)
  upper_error := v4065_upper_checked
  lower_error := reuse_lower_error 60 76 Primitive.Addresses.material4065

def v4066_pa : Scalar.QComplex := ((999998501505566504291285596954 : Int)/10^30,(-1731180701575040724720519459 : Int)/10^30)
theorem v4066_pa_checked : Scalar.distance (sourceCoefficient 60 77 1 0) v4066_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4066_pb : Scalar.QComplex := ((-746965542825015376047861 : Int)/10^30,(-431476865945717742822927980 : Int)/10^30)
theorem v4066_pb_checked : Scalar.distance (sourceCoefficient 60 77 1 1) v4066_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4066_pg : Scalar.QComplex := ((-93086289491854390112178 : Int)/10^30,(161149429431048787671 : Int)/10^30)
theorem v4066_pg_checked : Scalar.distance (sourceCoefficient 60 77 1 2) v4066_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4066_mb : Scalar.QComplex := ((-1119310367010104732394521 : Int)/10^30,(-431476060689539705504948247 : Int)/10^30)
theorem v4066_mb_checked : Scalar.distance (sourceCoefficient 60 77 3 1) v4066_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4066_mg : Scalar.QComplex := ((-93086115766874860581145 : Int)/10^30,(241478644808374034246 : Int)/10^30)
theorem v4066_mg_checked : Scalar.distance (sourceCoefficient 60 77 3 2) v4066_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4066_upper : Scalar.QComplex := ((999994024264427155326788741038 : Int)/10^30,(-3457084817627954852382914769 : Int)/10^30)
theorem v4066_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 77 5) 1) 14) v4066_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4066 : Material (60 : Basis) (77 : Basis) where
  plus := ![v4066_pa,v4066_pb,v4066_pg]
  minus := ![(Primitive.Addresses.material4066 1).one,v4066_mb,v4066_mg]
  upper := v4066_upper
  lower := (Primitive.Addresses.material4066 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4066_pa_checked.trans (by decide +kernel)
    · exact v4066_pb_checked.trans (by decide +kernel)
    · exact v4066_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 77 Primitive.Addresses.material4066
    · exact v4066_mb_checked.trans (by decide +kernel)
    · exact v4066_mg_checked.trans (by decide +kernel)
  upper_error := v4066_upper_checked
  lower_error := reuse_lower_error 60 77 Primitive.Addresses.material4066

def v4067_pa : Scalar.QComplex := ((999998471407213776082142156647 : Int)/10^30,(-1748480264644679831362069641 : Int)/10^30)
theorem v4067_pa_checked : Scalar.distance (sourceCoefficient 60 78 1 0) v4067_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4067_pb : Scalar.QComplex := ((-754429913733572161972712 : Int)/10^30,(-431476852082606002502981770 : Int)/10^30)
theorem v4067_pb_checked : Scalar.distance (sourceCoefficient 60 78 1 1) v4067_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4067_pg : Scalar.QComplex := ((-93086286595574948608506 : Int)/10^30,(162759783814852825668 : Int)/10^30)
theorem v4067_pg_checked : Scalar.distance (sourceCoefficient 60 78 1 2) v4067_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4067_mb : Scalar.QComplex := ((-1126774723176094029939486 : Int)/10^30,(-431476040385017215756601978 : Int)/10^30)
theorem v4067_mb_checked : Scalar.distance (sourceCoefficient 60 78 3 1) v4067_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4067_mg : Scalar.QComplex := ((-93086111480933191940884 : Int)/10^30,(243088996093210823887 : Int)/10^30)
theorem v4067_mg_checked : Scalar.distance (sourceCoefficient 60 78 3 2) v4067_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4067_upper : Scalar.QComplex := ((999993964308642800983500627000 : Int)/10^30,(-3474384302984900608566903436 : Int)/10^30)
theorem v4067_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 78 5) 1) 14) v4067_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4067 : Material (60 : Basis) (78 : Basis) where
  plus := ![v4067_pa,v4067_pb,v4067_pg]
  minus := ![(Primitive.Addresses.material4067 1).one,v4067_mb,v4067_mg]
  upper := v4067_upper
  lower := (Primitive.Addresses.material4067 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4067_pa_checked.trans (by decide +kernel)
    · exact v4067_pb_checked.trans (by decide +kernel)
    · exact v4067_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 78 Primitive.Addresses.material4067
    · exact v4067_mb_checked.trans (by decide +kernel)
    · exact v4067_mg_checked.trans (by decide +kernel)
  upper_error := v4067_upper_checked
  lower_error := reuse_lower_error 60 78 Primitive.Addresses.material4067

def v4068_pa : Scalar.QComplex := ((999998461640245698215166066658 : Int)/10^30,(-1754057337162282164722802049 : Int)/10^30)
theorem v4068_pa_checked : Scalar.distance (sourceCoefficient 60 79 1 0) v4068_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4068_pb : Scalar.QComplex := ((-756836294594031158871849 : Int)/10^30,(-431476847576684412382076471 : Int)/10^30)
theorem v4068_pb_checked : Scalar.distance (sourceCoefficient 60 79 1 1) v4068_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4068_pg : Scalar.QComplex := ((-93086285654937862114962 : Int)/10^30,(163278933523967909853 : Int)/10^30)
theorem v4068_pg_checked : Scalar.distance (sourceCoefficient 60 79 1 2) v4068_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4068_mb : Scalar.QComplex := ((-1129181099252140062352060 : Int)/10^30,(-431476033802499000190844865 : Int)/10^30)
theorem v4068_mb_checked : Scalar.distance (sourceCoefficient 60 79 3 1) v4068_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4068_mg : Scalar.QComplex := ((-93086110092293638358130 : Int)/10^30,(243608144797295304132 : Int)/10^30)
theorem v4068_mg_checked : Scalar.distance (sourceCoefficient 60 79 3 2) v4068_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4068_upper : Scalar.QComplex := ((999993944916168052553087955686 : Int)/10^30,(-3479961350339207705941338847 : Int)/10^30)
theorem v4068_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 79 5) 1) 14) v4068_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4068 : Material (60 : Basis) (79 : Basis) where
  plus := ![v4068_pa,v4068_pb,v4068_pg]
  minus := ![(Primitive.Addresses.material4068 1).one,v4068_mb,v4068_mg]
  upper := v4068_upper
  lower := (Primitive.Addresses.material4068 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4068_pa_checked.trans (by decide +kernel)
    · exact v4068_pb_checked.trans (by decide +kernel)
    · exact v4068_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 79 Primitive.Addresses.material4068
    · exact v4068_mb_checked.trans (by decide +kernel)
    · exact v4068_mg_checked.trans (by decide +kernel)
  upper_error := v4068_upper_checked
  lower_error := reuse_lower_error 60 79 Primitive.Addresses.material4068

def v4069_pa : Scalar.QComplex := ((999998446321033590152258824899 : Int)/10^30,(-1762769275572207384500162665 : Int)/10^30)
theorem v4069_pa_checked : Scalar.distance (sourceCoefficient 60 80 1 0) v4069_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4069_pb : Scalar.QComplex := ((-760595299279133191408173 : Int)/10^30,(-431476840502181158586144756 : Int)/10^30)
theorem v4069_pb_checked : Scalar.distance (sourceCoefficient 60 80 1 1) v4069_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4069_pg : Scalar.QComplex := ((-93086284178810163281818 : Int)/10^30,(164089896670610878587 : Int)/10^30)
theorem v4069_pg_checked : Scalar.distance (sourceCoefficient 60 80 1 2) v4069_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4069_mb : Scalar.QComplex := ((-1132940096432615171396734 : Int)/10^30,(-431476023484146636599073303 : Int)/10^30)
theorem v4069_mb_checked : Scalar.distance (sourceCoefficient 60 80 3 1) v4069_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4069_mg : Scalar.QComplex := ((-93086107916341818026183 : Int)/10^30,(244419106368147908756 : Int)/10^30)
theorem v4069_mg_checked : Scalar.distance (sourceCoefficient 60 80 3 2) v4069_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4069_upper : Scalar.QComplex := ((999993914560963406004909553856 : Int)/10^30,(-3488673249334153689858719183 : Int)/10^30)
theorem v4069_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 80 5) 1) 14) v4069_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4069 : Material (60 : Basis) (80 : Basis) where
  plus := ![v4069_pa,v4069_pb,v4069_pg]
  minus := ![(Primitive.Addresses.material4069 1).one,v4069_mb,v4069_mg]
  upper := v4069_upper
  lower := (Primitive.Addresses.material4069 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4069_pa_checked.trans (by decide +kernel)
    · exact v4069_pb_checked.trans (by decide +kernel)
    · exact v4069_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 80 Primitive.Addresses.material4069
    · exact v4069_mb_checked.trans (by decide +kernel)
    · exact v4069_mg_checked.trans (by decide +kernel)
  upper_error := v4069_upper_checked
  lower_error := reuse_lower_error 60 80 Primitive.Addresses.material4069

def v4070_pa : Scalar.QComplex := ((999998399735762133333086118243 : Int)/10^30,(-1789001373640529889456079753 : Int)/10^30)
theorem v4070_pa_checked : Scalar.distance (sourceCoefficient 60 81 1 0) v4070_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4070_pb : Scalar.QComplex := ((-771913857038133634514649 : Int)/10^30,(-431476818936806765396481752 : Int)/10^30)
theorem v4070_pb_checked : Scalar.distance (sourceCoefficient 60 81 1 1) v4070_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4070_pg : Scalar.QComplex := ((-93086279684338182182418 : Int)/10^30,(166531748717169500441 : Int)/10^30)
theorem v4070_pg_checked : Scalar.distance (sourceCoefficient 60 81 1 2) v4070_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4070_mb : Scalar.QComplex := ((-1144258631367252444268241 : Int)/10^30,(-431475992151374696084454419 : Int)/10^30)
theorem v4070_mb_checked : Scalar.distance (sourceCoefficient 60 81 3 1) v4070_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4070_mg : Scalar.QComplex := ((-93086101314663171177660 : Int)/10^30,(246860953626966519339 : Int)/10^30)
theorem v4070_mg_checked : Scalar.distance (sourceCoefficient 60 81 3 2) v4070_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4070_upper : Scalar.QComplex := ((999993822701539823897751824457 : Int)/10^30,(-3514905227930895209090174965 : Int)/10^30)
theorem v4070_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 81 5) 1) 14) v4070_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4070 : Material (60 : Basis) (81 : Basis) where
  plus := ![v4070_pa,v4070_pb,v4070_pg]
  minus := ![(Primitive.Addresses.material4070 1).one,v4070_mb,v4070_mg]
  upper := v4070_upper
  lower := (Primitive.Addresses.material4070 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4070_pa_checked.trans (by decide +kernel)
    · exact v4070_pb_checked.trans (by decide +kernel)
    · exact v4070_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 81 Primitive.Addresses.material4070
    · exact v4070_mb_checked.trans (by decide +kernel)
    · exact v4070_mg_checked.trans (by decide +kernel)
  upper_error := v4070_upper_checked
  lower_error := reuse_lower_error 60 81 Primitive.Addresses.material4070

def v4071_pa : Scalar.QComplex := ((999998381903221005299049747497 : Int)/10^30,(-1798941616549079590356596239 : Int)/10^30)
theorem v4071_pa_checked : Scalar.distance (sourceCoefficient 60 82 1 0) v4071_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4071_pb : Scalar.QComplex := ((-776202847246197102883129 : Int)/10^30,(-431476810661516775344485862 : Int)/10^30)
theorem v4071_pb_checked : Scalar.distance (sourceCoefficient 60 82 1 1) v4071_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4071_pg : Scalar.QComplex := ((-93086277961703943456832 : Int)/10^30,(167457050316678390898 : Int)/10^30)
theorem v4071_pg_checked : Scalar.distance (sourceCoefficient 60 82 1 2) v4071_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4071_mb : Scalar.QComplex := ((-1148547612837126285449581 : Int)/10^30,(-431475980174882406690550816 : Int)/10^30)
theorem v4071_mb_checked : Scalar.distance (sourceCoefficient 60 82 3 1) v4071_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4071_mg : Scalar.QComplex := ((-93086098793535967528386 : Int)/10^30,(247786253395387572472 : Int)/10^30)
theorem v4071_mg_checked : Scalar.distance (sourceCoefficient 60 82 3 2) v4071_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4071_upper : Scalar.QComplex := ((999993787713067766974593440464 : Int)/10^30,(-3524845425257272529168975218 : Int)/10^30)
theorem v4071_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 82 5) 1) 14) v4071_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4071 : Material (60 : Basis) (82 : Basis) where
  plus := ![v4071_pa,v4071_pb,v4071_pg]
  minus := ![(Primitive.Addresses.material4071 1).one,v4071_mb,v4071_mg]
  upper := v4071_upper
  lower := (Primitive.Addresses.material4071 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4071_pa_checked.trans (by decide +kernel)
    · exact v4071_pb_checked.trans (by decide +kernel)
    · exact v4071_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 82 Primitive.Addresses.material4071
    · exact v4071_mb_checked.trans (by decide +kernel)
    · exact v4071_mg_checked.trans (by decide +kernel)
  upper_error := v4071_upper_checked
  lower_error := reuse_lower_error 60 82 Primitive.Addresses.material4071

def v4072_pa : Scalar.QComplex := ((999998357402010749522178890251 : Int)/10^30,(-1812510215246468990919838372 : Int)/10^30)
theorem v4072_pa_checked : Scalar.distance (sourceCoefficient 60 83 1 0) v4072_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4072_pb : Scalar.QComplex := ((-782057390931602511554062 : Int)/10^30,(-431476799273850733860035904 : Int)/10^30)
theorem v4072_pb_checked : Scalar.distance (sourceCoefficient 60 83 1 1) v4072_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4072_pg : Scalar.QComplex := ((-93086275592958312766864 : Int)/10^30,(168720102550786200429 : Int)/10^30)
theorem v4072_pg_checked : Scalar.distance (sourceCoefficient 60 83 1 2) v4072_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4072_mb : Scalar.QComplex := ((-1154402144515574601818009 : Int)/10^30,(-431475963735013083709113769 : Int)/10^30)
theorem v4072_mb_checked : Scalar.distance (sourceCoefficient 60 83 3 1) v4072_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4072_mg : Scalar.QComplex := ((-93086095334834026556559 : Int)/10^30,(249049303115082515964 : Int)/10^30)
theorem v4072_mg_checked : Scalar.distance (sourceCoefficient 60 83 3 2) v4072_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4072_upper : Scalar.QComplex := ((999993739793723584836479969934 : Int)/10^30,(-3538413961458961880498125548 : Int)/10^30)
theorem v4072_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 83 5) 1) 14) v4072_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4072 : Material (60 : Basis) (83 : Basis) where
  plus := ![v4072_pa,v4072_pb,v4072_pg]
  minus := ![(Primitive.Addresses.material4072 1).one,v4072_mb,v4072_mg]
  upper := v4072_upper
  lower := (Primitive.Addresses.material4072 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4072_pa_checked.trans (by decide +kernel)
    · exact v4072_pb_checked.trans (by decide +kernel)
    · exact v4072_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 83 Primitive.Addresses.material4072
    · exact v4072_mb_checked.trans (by decide +kernel)
    · exact v4072_mg_checked.trans (by decide +kernel)
  upper_error := v4072_upper_checked
  lower_error := reuse_lower_error 60 83 Primitive.Addresses.material4072

def v4073_pa : Scalar.QComplex := ((999998293094735002166433133214 : Int)/10^30,(-1847649213587385330449118353 : Int)/10^30)
theorem v4073_pa_checked : Scalar.distance (sourceCoefficient 60 84 1 0) v4073_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4073_pb : Scalar.QComplex := ((-797219074238344707790775 : Int)/10^30,(-431476769290549530816487748 : Int)/10^30)
theorem v4073_pb_checked : Scalar.distance (sourceCoefficient 60 84 1 1) v4073_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4073_pg : Scalar.QComplex := ((-93086269365610686414698 : Int)/10^30,(171991065961610125572 : Int)/10^30)
theorem v4073_pg_checked : Scalar.distance (sourceCoefficient 60 84 1 2) v4073_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4073_mb : Scalar.QComplex := ((-1169563796302690639326868 : Int)/10^30,(-431475920667873207967689935 : Int)/10^30)
theorem v4073_mb_checked : Scalar.distance (sourceCoefficient 60 84 3 1) v4073_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4073_mg : Scalar.QComplex := ((-93086086284794614112766 : Int)/10^30,(252320259934056740628 : Int)/10^30)
theorem v4073_mg_checked : Scalar.distance (sourceCoefficient 60 84 3 2) v4073_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4073_upper : Scalar.QComplex := ((999993614839820264220172471297 : Int)/10^30,(-3573552796475943878481700617 : Int)/10^30)
theorem v4073_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 84 5) 1) 14) v4073_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4073 : Material (60 : Basis) (84 : Basis) where
  plus := ![v4073_pa,v4073_pb,v4073_pg]
  minus := ![(Primitive.Addresses.material4073 1).one,v4073_mb,v4073_mg]
  upper := v4073_upper
  lower := (Primitive.Addresses.material4073 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4073_pa_checked.trans (by decide +kernel)
    · exact v4073_pb_checked.trans (by decide +kernel)
    · exact v4073_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 84 Primitive.Addresses.material4073
    · exact v4073_mb_checked.trans (by decide +kernel)
    · exact v4073_mg_checked.trans (by decide +kernel)
  upper_error := v4073_upper_checked
  lower_error := reuse_lower_error 60 84 Primitive.Addresses.material4073

def v4074_pa : Scalar.QComplex := ((999998143900483715381925220583 : Int)/10^30,(-1926705890234371447712423149 : Int)/10^30)
theorem v4074_pa_checked : Scalar.distance (sourceCoefficient 60 85 1 0) v4074_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4074_pb : Scalar.QComplex := ((-831330240949296803408786 : Int)/10^30,(-431476699236390919005175860 : Int)/10^30)
theorem v4074_pb_checked : Scalar.distance (sourceCoefficient 60 85 1 1) v4074_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4074_pg : Scalar.QComplex := ((-93086254864931555154022 : Int)/10^30,(179350168439882428907 : Int)/10^30)
theorem v4074_pg_checked : Scalar.distance (sourceCoefficient 60 85 1 2) v4074_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4074_mb : Scalar.QComplex := ((-1203674889858912651311741 : Int)/10^30,(-431475821177340118887760297 : Int)/10^30)
theorem v4074_mb_checked : Scalar.distance (sourceCoefficient 60 85 3 1) v4074_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4074_mg : Scalar.QComplex := ((-93086065433546885040575 : Int)/10^30,(259679347158765859771 : Int)/10^30)
theorem v4074_mg_checked : Scalar.distance (sourceCoefficient 60 85 3 2) v4074_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4074_upper : Scalar.QComplex := ((999993329201139257730423170664 : Int)/10^30,(-3652609097881553855408338666 : Int)/10^30)
theorem v4074_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 85 5) 1) 14) v4074_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4074 : Material (60 : Basis) (85 : Basis) where
  plus := ![v4074_pa,v4074_pb,v4074_pg]
  minus := ![(Primitive.Addresses.material4074 1).one,v4074_mb,v4074_mg]
  upper := v4074_upper
  lower := (Primitive.Addresses.material4074 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4074_pa_checked.trans (by decide +kernel)
    · exact v4074_pb_checked.trans (by decide +kernel)
    · exact v4074_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 85 Primitive.Addresses.material4074
    · exact v4074_mb_checked.trans (by decide +kernel)
    · exact v4074_mg_checked.trans (by decide +kernel)
  upper_error := v4074_upper_checked
  lower_error := reuse_lower_error 60 85 Primitive.Addresses.material4074

def v4075_pa : Scalar.QComplex := ((999998115693808296414920722585 : Int)/10^30,(-1941290507058988857220900877 : Int)/10^30)
theorem v4075_pa_checked : Scalar.distance (sourceCoefficient 60 86 1 0) v4075_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4075_pb : Scalar.QComplex := ((-837623172731779447591870 : Int)/10^30,(-431476685919732073401851580 : Int)/10^30)
theorem v4075_pb_checked : Scalar.distance (sourceCoefficient 60 86 1 1) v4075_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4075_pg : Scalar.QComplex := ((-93086252115642394531623 : Int)/10^30,(180707798078619107009 : Int)/10^30)
theorem v4075_pg_checked : Scalar.distance (sourceCoefficient 60 86 1 2) v4075_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4075_mb : Scalar.QComplex := ((-1209967807806572367980888 : Int)/10^30,(-431475802430169526528925697 : Int)/10^30)
theorem v4075_mb_checked : Scalar.distance (sourceCoefficient 60 86 3 1) v4075_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4075_mg : Scalar.QComplex := ((-93086061512685515243532 : Int)/10^30,(261036973919482254402 : Int)/10^30)
theorem v4075_mg_checked : Scalar.distance (sourceCoefficient 60 86 3 2) v4075_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4075_upper : Scalar.QComplex := ((999993275822780316106209178865 : Int)/10^30,(-3667193644301934850557218996 : Int)/10^30)
theorem v4075_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 86 5) 1) 14) v4075_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4075 : Material (60 : Basis) (86 : Basis) where
  plus := ![v4075_pa,v4075_pb,v4075_pg]
  minus := ![(Primitive.Addresses.material4075 1).one,v4075_mb,v4075_mg]
  upper := v4075_upper
  lower := (Primitive.Addresses.material4075 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4075_pa_checked.trans (by decide +kernel)
    · exact v4075_pb_checked.trans (by decide +kernel)
    · exact v4075_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 86 Primitive.Addresses.material4075
    · exact v4075_mb_checked.trans (by decide +kernel)
    · exact v4075_mg_checked.trans (by decide +kernel)
  upper_error := v4075_upper_checked
  lower_error := reuse_lower_error 60 86 Primitive.Addresses.material4075

def v4076_pa : Scalar.QComplex := ((999998113818528144632730586292 : Int)/10^30,(-1942256261678718277249802847 : Int)/10^30)
theorem v4076_pa_checked : Scalar.distance (sourceCoefficient 60 87 1 0) v4076_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4076_pb : Scalar.QComplex := ((-838039873970204285991428 : Int)/10^30,(-431476685033618339328677137 : Int)/10^30)
theorem v4076_pb_checked : Scalar.distance (sourceCoefficient 60 87 1 1) v4076_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4076_pg : Scalar.QComplex := ((-93086251932776283556446 : Int)/10^30,(180797696709903116743 : Int)/10^30)
theorem v4076_pg_checked : Scalar.distance (sourceCoefficient 60 87 1 2) v4076_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4076_mb : Scalar.QComplex := ((-1210384508125164047703419 : Int)/10^30,(-431475801184461721162851610 : Int)/10^30)
theorem v4076_mb_checked : Scalar.distance (sourceCoefficient 60 87 3 1) v4076_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4076_mg : Scalar.QComplex := ((-93086061252241002443716 : Int)/10^30,(261126872359487677350 : Int)/10^30)
theorem v4076_mg_checked : Scalar.distance (sourceCoefficient 60 87 3 2) v4076_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4076_upper : Scalar.QComplex := ((999993272280698096255250249067 : Int)/10^30,(-3668159394246722792116268523 : Int)/10^30)
theorem v4076_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 87 5) 1) 14) v4076_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4076 : Material (60 : Basis) (87 : Basis) where
  plus := ![v4076_pa,v4076_pb,v4076_pg]
  minus := ![(Primitive.Addresses.material4076 1).one,v4076_mb,v4076_mg]
  upper := v4076_upper
  lower := (Primitive.Addresses.material4076 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4076_pa_checked.trans (by decide +kernel)
    · exact v4076_pb_checked.trans (by decide +kernel)
    · exact v4076_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 87 Primitive.Addresses.material4076
    · exact v4076_mb_checked.trans (by decide +kernel)
    · exact v4076_mg_checked.trans (by decide +kernel)
  upper_error := v4076_upper_checked
  lower_error := reuse_lower_error 60 87 Primitive.Addresses.material4076

def v4077_pa : Scalar.QComplex := ((999998090909240037427736261908 : Int)/10^30,(-1954015832918867306332080150 : Int)/10^30)
theorem v4077_pa_checked : Scalar.distance (sourceCoefficient 60 88 1 0) v4077_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4077_pb : Scalar.QComplex := ((-843113862504332900623597 : Int)/10^30,(-431476674200753654834803167 : Int)/10^30)
theorem v4077_pb_checked : Scalar.distance (sourceCoefficient 60 88 1 1) v4077_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4077_pg : Scalar.QComplex := ((-93086249697969908509221 : Int)/10^30,(181892352985882724202 : Int)/10^30)
theorem v4077_pg_checked : Scalar.distance (sourceCoefficient 60 88 1 2) v4077_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4077_mb : Scalar.QComplex := ((-1215458485421740509743457 : Int)/10^30,(-431475785972977489246960610 : Int)/10^30)
theorem v4077_mb_checked : Scalar.distance (sourceCoefficient 60 88 3 1) v4077_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4077_mg : Scalar.QComplex := ((-93086058072796394835152 : Int)/10^30,(262221526299339475276 : Int)/10^30)
theorem v4077_mg_checked : Scalar.distance (sourceCoefficient 60 88 3 2) v4077_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4077_upper : Scalar.QComplex := ((999993229075490969215919439504 : Int)/10^30,(-3679918908433018876617190096 : Int)/10^30)
theorem v4077_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 88 5) 1) 14) v4077_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4077 : Material (60 : Basis) (88 : Basis) where
  plus := ![v4077_pa,v4077_pb,v4077_pg]
  minus := ![(Primitive.Addresses.material4077 1).one,v4077_mb,v4077_mg]
  upper := v4077_upper
  lower := (Primitive.Addresses.material4077 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4077_pa_checked.trans (by decide +kernel)
    · exact v4077_pb_checked.trans (by decide +kernel)
    · exact v4077_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 88 Primitive.Addresses.material4077
    · exact v4077_mb_checked.trans (by decide +kernel)
    · exact v4077_mg_checked.trans (by decide +kernel)
  upper_error := v4077_upper_checked
  lower_error := reuse_lower_error 60 88 Primitive.Addresses.material4077

def v4078_pa : Scalar.QComplex := ((999998059340697019685884270064 : Int)/10^30,(-1970105286476359361231197860 : Int)/10^30)
theorem v4078_pa_checked : Scalar.distance (sourceCoefficient 60 89 1 0) v4078_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4078_pb : Scalar.QComplex := ((-850056097049507424283434 : Int)/10^30,(-431476659250330382715112594 : Int)/10^30)
theorem v4078_pb_checked : Scalar.distance (sourceCoefficient 60 89 1 1) v4078_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4078_pg : Scalar.QComplex := ((-93086246615975457080023 : Int)/10^30,(183390062454006140525 : Int)/10^30)
theorem v4078_pg_checked : Scalar.distance (sourceCoefficient 60 89 1 2) v4078_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4078_mb : Scalar.QComplex := ((-1222400704480461894671613 : Int)/10^30,(-431475765031724038004691936 : Int)/10^30)
theorem v4078_mb_checked : Scalar.distance (sourceCoefficient 60 89 3 1) v4078_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4078_mg : Scalar.QComplex := ((-93086053698347274313256 : Int)/10^30,(263719232550174804206 : Int)/10^30)
theorem v4078_mg_checked : Scalar.distance (sourceCoefficient 60 89 3 2) v4078_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4078_upper : Scalar.QComplex := ((999993169738057752704084142449 : Int)/10^30,(-3696008283542718484840774998 : Int)/10^30)
theorem v4078_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 89 5) 1) 14) v4078_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4078 : Material (60 : Basis) (89 : Basis) where
  plus := ![v4078_pa,v4078_pb,v4078_pg]
  minus := ![(Primitive.Addresses.material4078 1).one,v4078_mb,v4078_mg]
  upper := v4078_upper
  lower := (Primitive.Addresses.material4078 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4078_pa_checked.trans (by decide +kernel)
    · exact v4078_pb_checked.trans (by decide +kernel)
    · exact v4078_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 89 Primitive.Addresses.material4078
    · exact v4078_mb_checked.trans (by decide +kernel)
    · exact v4078_mg_checked.trans (by decide +kernel)
  upper_error := v4078_upper_checked
  lower_error := reuse_lower_error 60 89 Primitive.Addresses.material4078

def v4079_pa : Scalar.QComplex := ((999998007374846687545926473118 : Int)/10^30,(-1996308176627523241977364476 : Int)/10^30)
theorem v4079_pa_checked : Scalar.distance (sourceCoefficient 60 90 1 0) v4079_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4079_pb : Scalar.QComplex := ((-861362050014784016709541 : Int)/10^30,(-431476634583665318765584112 : Int)/10^30)
theorem v4079_pb_checked : Scalar.distance (sourceCoefficient 60 90 1 1) v4079_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4079_pg : Scalar.QComplex := ((-93086241536539717352065 : Int)/10^30,(185829195398847792130 : Int)/10^30)
theorem v4079_pg_checked : Scalar.distance (sourceCoefficient 60 90 1 2) v4079_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4079_mb : Scalar.QComplex := ((-1233706631949794485714666 : Int)/10^30,(-431475730608539950767308070 : Int)/10^30)
theorem v4079_mb_checked : Scalar.distance (sourceCoefficient 60 90 3 1) v4079_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4079_mg : Scalar.QComplex := ((-93086046514051548962866 : Int)/10^30,(266158360203491512472 : Int)/10^30)
theorem v4079_mg_checked : Scalar.distance (sourceCoefficient 60 90 3 2) v4079_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4079_upper : Scalar.QComplex := ((999993072548473524310568163939 : Int)/10^30,(-3722211044979412124966178661 : Int)/10^30)
theorem v4079_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 90 5) 1) 14) v4079_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4079 : Material (60 : Basis) (90 : Basis) where
  plus := ![v4079_pa,v4079_pb,v4079_pg]
  minus := ![(Primitive.Addresses.material4079 1).one,v4079_mb,v4079_mg]
  upper := v4079_upper
  lower := (Primitive.Addresses.material4079 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4079_pa_checked.trans (by decide +kernel)
    · exact v4079_pb_checked.trans (by decide +kernel)
    · exact v4079_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 90 Primitive.Addresses.material4079
    · exact v4079_mb_checked.trans (by decide +kernel)
    · exact v4079_mg_checked.trans (by decide +kernel)
  upper_error := v4079_upper_checked
  lower_error := reuse_lower_error 60 90 Primitive.Addresses.material4079

def v4080_pa : Scalar.QComplex := ((999997977798255588477968247890 : Int)/10^30,(-2011069217984092401960599880 : Int)/10^30)
theorem v4080_pa_checked : Scalar.distance (sourceCoefficient 60 91 1 0) v4080_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4080_pb : Scalar.QComplex := ((-867731104523063783628298 : Int)/10^30,(-431476620514100223075711501 : Int)/10^30)
theorem v4080_pb_checked : Scalar.distance (sourceCoefficient 60 91 1 1) v4080_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4080_pg : Scalar.QComplex := ((-93086238642274742013842 : Int)/10^30,(187203247714134155720 : Int)/10^30)
theorem v4080_pg_checked : Scalar.distance (sourceCoefficient 60 91 1 2) v4080_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4080_mb : Scalar.QComplex := ((-1240075671945183171138811 : Int)/10^30,(-431475711042772904740714858 : Int)/10^30)
theorem v4080_mb_checked : Scalar.distance (sourceCoefficient 60 91 3 1) v4080_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4080_mg : Scalar.QComplex := ((-93086042434042388218636 : Int)/10^30,(267532409509535080927 : Int)/10^30)
theorem v4080_mg_checked : Scalar.distance (sourceCoefficient 60 91 3 2) v4080_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4080_upper : Scalar.QComplex := ((999993017495708205873676652207 : Int)/10^30,(-3736972013304631068454456635 : Int)/10^30)
theorem v4080_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 91 5) 1) 14) v4080_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4080 : Material (60 : Basis) (91 : Basis) where
  plus := ![v4080_pa,v4080_pb,v4080_pg]
  minus := ![(Primitive.Addresses.material4080 1).one,v4080_mb,v4080_mg]
  upper := v4080_upper
  lower := (Primitive.Addresses.material4080 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4080_pa_checked.trans (by decide +kernel)
    · exact v4080_pb_checked.trans (by decide +kernel)
    · exact v4080_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 91 Primitive.Addresses.material4080
    · exact v4080_mb_checked.trans (by decide +kernel)
    · exact v4080_mg_checked.trans (by decide +kernel)
  upper_error := v4080_upper_checked
  lower_error := reuse_lower_error 60 91 Primitive.Addresses.material4080

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
