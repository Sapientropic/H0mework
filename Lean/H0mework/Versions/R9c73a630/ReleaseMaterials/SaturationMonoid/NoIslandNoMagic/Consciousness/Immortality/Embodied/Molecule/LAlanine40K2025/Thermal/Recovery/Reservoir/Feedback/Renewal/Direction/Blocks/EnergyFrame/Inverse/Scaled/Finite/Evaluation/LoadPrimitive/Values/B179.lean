import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B119
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B120

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2865_pa : Scalar.QComplex := ((999999644224310240132753343326 : Int)/10^30,(-843534974345102699372452865 : Int)/10^30)
theorem v2865_pa_checked : Scalar.distance (sourceCoefficient 36 40 1 0) v2865_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2865_pb : Scalar.QComplex := ((-363966379339935323244986 : Int)/10^30,(-431477367173920710545620352 : Int)/10^30)
theorem v2865_pb_checked : Scalar.distance (sourceCoefficient 36 40 1 1) v2865_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2865_pg : Scalar.QComplex := ((-93086396744836633561542 : Int)/10^30,(78521659226131293383 : Int)/10^30)
theorem v2865_pg_checked : Scalar.distance (sourceCoefficient 36 40 1 2) v2865_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2865_mb : Scalar.QComplex := ((-736311778670481852456845 : Int)/10^30,(-431476892428584488697942617 : Int)/10^30)
theorem v2865_mb_checked : Scalar.distance (sourceCoefficient 36 40 3 1) v2865_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2865_mg : Scalar.QComplex := ((-93086294323861439062763 : Int)/10^30,(158850997924044843992 : Int)/10^30)
theorem v2865_mg_checked : Scalar.distance (sourceCoefficient 36 40 3 2) v2865_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2865_upper : Scalar.QComplex := ((999996698977467553370577579789 : Int)/10^30,(-2569442384670942397755601963 : Int)/10^30)
theorem v2865_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 40 5) 1) 14) v2865_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2865 : Material (36 : Basis) (40 : Basis) where
  plus := ![v2865_pa,v2865_pb,v2865_pg]
  minus := ![(Primitive.Addresses.material2865 1).one,v2865_mb,v2865_mg]
  upper := v2865_upper
  lower := (Primitive.Addresses.material2865 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2865_pa_checked.trans (by decide +kernel)
    · exact v2865_pb_checked.trans (by decide +kernel)
    · exact v2865_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 40 Primitive.Addresses.material2865
    · exact v2865_mb_checked.trans (by decide +kernel)
    · exact v2865_mg_checked.trans (by decide +kernel)
  upper_error := v2865_upper_checked
  lower_error := reuse_lower_error 36 40 Primitive.Addresses.material2865

def v2866_pa : Scalar.QComplex := ((999999631901661422620171967811 : Int)/10^30,(-858018963460815819652619994 : Int)/10^30)
theorem v2866_pa_checked : Scalar.distance (sourceCoefficient 36 41 1 0) v2866_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2866_pb : Scalar.QComplex := ((-370215894921471146334333 : Int)/10^30,(-431477361703465890308115791 : Int)/10^30)
theorem v2866_pb_checked : Scalar.distance (sourceCoefficient 36 41 1 1) v2866_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2866_pg : Scalar.QComplex := ((-93086395581206342454000 : Int)/10^30,(79869922048875740416 : Int)/10^30)
theorem v2866_pg_checked : Scalar.distance (sourceCoefficient 36 41 1 2) v2866_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2866_mb : Scalar.QComplex := ((-742561287204281277842640 : Int)/10^30,(-431476881565081226228583417 : Int)/10^30)
theorem v2866_mb_checked : Scalar.distance (sourceCoefficient 36 41 3 1) v2866_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2866_mg : Scalar.QComplex := ((-93086291996741488702875 : Int)/10^30,(160199259240608890198 : Int)/10^30)
theorem v2866_mg_checked : Scalar.distance (sourceCoefficient 36 41 3 2) v2866_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2866_upper : Scalar.QComplex := ((999996661656785852503394943507 : Int)/10^30,(-2583926330946681182001501529 : Int)/10^30)
theorem v2866_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 41 5) 1) 14) v2866_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2866 : Material (36 : Basis) (41 : Basis) where
  plus := ![v2866_pa,v2866_pb,v2866_pg]
  minus := ![(Primitive.Addresses.material2866 1).one,v2866_mb,v2866_mg]
  upper := v2866_upper
  lower := (Primitive.Addresses.material2866 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2866_pa_checked.trans (by decide +kernel)
    · exact v2866_pb_checked.trans (by decide +kernel)
    · exact v2866_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 41 Primitive.Addresses.material2866
    · exact v2866_mb_checked.trans (by decide +kernel)
    · exact v2866_mg_checked.trans (by decide +kernel)
  upper_error := v2866_upper_checked
  lower_error := reuse_lower_error 36 41 Primitive.Addresses.material2866

def v2867_pa : Scalar.QComplex := ((999999621808614394881539104218 : Int)/10^30,(-869702609046053613063290708 : Int)/10^30)
theorem v2867_pa_checked : Scalar.distance (sourceCoefficient 36 42 1 0) v2867_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2867_pb : Scalar.QComplex := ((-375257125222520229892831 : Int)/10^30,(-431477357202727435465555562 : Int)/10^30)
theorem v2867_pb_checked : Scalar.distance (sourceCoefficient 36 42 1 1) v2867_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2867_pg : Scalar.QComplex := ((-93086394625951594910916 : Int)/10^30,(80957510890313864751 : Int)/10^30)
theorem v2867_pg_checked : Scalar.distance (sourceCoefficient 36 42 1 2) v2867_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2867_mb : Scalar.QComplex := ((-747602511744315343920119 : Int)/10^30,(-431476872713989745995604343 : Int)/10^30)
theorem v2867_mb_checked : Scalar.distance (sourceCoefficient 36 42 3 1) v2867_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2867_mg : Scalar.QComplex := ((-93086290102946909866766 : Int)/10^30,(161286846852746159547 : Int)/10^30)
theorem v2867_mg_checked : Scalar.distance (sourceCoefficient 36 42 3 2) v2867_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2867_upper : Scalar.QComplex := ((999996631398841509100023875226 : Int)/10^30,(-2595609941710817797817731690 : Int)/10^30)
theorem v2867_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 42 5) 1) 14) v2867_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2867 : Material (36 : Basis) (42 : Basis) where
  plus := ![v2867_pa,v2867_pb,v2867_pg]
  minus := ![(Primitive.Addresses.material2867 1).one,v2867_mb,v2867_mg]
  upper := v2867_upper
  lower := (Primitive.Addresses.material2867 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2867_pa_checked.trans (by decide +kernel)
    · exact v2867_pb_checked.trans (by decide +kernel)
    · exact v2867_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 42 Primitive.Addresses.material2867
    · exact v2867_mb_checked.trans (by decide +kernel)
    · exact v2867_mg_checked.trans (by decide +kernel)
  upper_error := v2867_upper_checked
  lower_error := reuse_lower_error 36 42 Primitive.Addresses.material2867

def v2868_pa : Scalar.QComplex := ((999999608227760434515350229833 : Int)/10^30,(-885180391584382988237328386 : Int)/10^30)
theorem v2868_pa_checked : Scalar.distance (sourceCoefficient 36 43 1 0) v2868_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2868_pb : Scalar.QComplex := ((-381935440255449315398494 : Int)/10^30,(-431477351119494572364310195 : Int)/10^30)
theorem v2868_pb_checked : Scalar.distance (sourceCoefficient 36 43 1 1) v2868_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2868_pg : Scalar.QComplex := ((-93086393337660400664186 : Int)/10^30,(82398282387167760358 : Int)/10^30)
theorem v2868_pg_checked : Scalar.distance (sourceCoefficient 36 43 1 2) v2868_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2868_mb : Scalar.QComplex := ((-754280819041046546372611 : Int)/10^30,(-431476860867674054685769950 : Int)/10^30)
theorem v2868_mb_checked : Scalar.distance (sourceCoefficient 36 43 3 1) v2868_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2868_mg : Scalar.QComplex := ((-93086287571335283464205 : Int)/10^30,(162727616701397702212 : Int)/10^30)
theorem v2868_mg_checked : Scalar.distance (sourceCoefficient 36 43 3 2) v2868_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2868_upper : Scalar.QComplex := ((999996591104759248127376802585 : Int)/10^30,(-2611087677757486340060083696 : Int)/10^30)
theorem v2868_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 43 5) 1) 14) v2868_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2868 : Material (36 : Basis) (43 : Basis) where
  plus := ![v2868_pa,v2868_pb,v2868_pg]
  minus := ![(Primitive.Addresses.material2868 1).one,v2868_mb,v2868_mg]
  upper := v2868_upper
  lower := (Primitive.Addresses.material2868 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2868_pa_checked.trans (by decide +kernel)
    · exact v2868_pb_checked.trans (by decide +kernel)
    · exact v2868_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 43 Primitive.Addresses.material2868
    · exact v2868_mb_checked.trans (by decide +kernel)
    · exact v2868_mg_checked.trans (by decide +kernel)
  upper_error := v2868_upper_checked
  lower_error := reuse_lower_error 36 43 Primitive.Addresses.material2868

def v2869_pa : Scalar.QComplex := ((999999603027194240058330038104 : Int)/10^30,(-891036168700505011662279470 : Int)/10^30)
theorem v2869_pa_checked : Scalar.distance (sourceCoefficient 36 44 1 0) v2869_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2869_pb : Scalar.QComplex := ((-384462076360810711647682 : Int)/10^30,(-431477348782063698634420037 : Int)/10^30)
theorem v2869_pb_checked : Scalar.distance (sourceCoefficient 36 44 1 1) v2869_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2869_pg : Scalar.QComplex := ((-93086392843472099049356 : Int)/10^30,(82943375763662083758 : Int)/10^30)
theorem v2869_pg_checked : Scalar.distance (sourceCoefficient 36 44 1 2) v2869_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2869_mb : Scalar.QComplex := ((-756807452188528277570960 : Int)/10^30,(-431476856349870887827234206 : Int)/10^30)
theorem v2869_mb_checked : Scalar.distance (sourceCoefficient 36 44 3 1) v2869_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2869_mg : Scalar.QComplex := ((-93086286606756132037999 : Int)/10^30,(163272709448466602667 : Int)/10^30)
theorem v2869_mg_checked : Scalar.distance (sourceCoefficient 36 44 3 2) v2869_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2869_upper : Scalar.QComplex := ((999996575797660728826407731244 : Int)/10^30,(-2616943437176410756968335057 : Int)/10^30)
theorem v2869_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 44 5) 1) 14) v2869_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2869 : Material (36 : Basis) (44 : Basis) where
  plus := ![v2869_pa,v2869_pb,v2869_pg]
  minus := ![(Primitive.Addresses.material2869 1).one,v2869_mb,v2869_mg]
  upper := v2869_upper
  lower := (Primitive.Addresses.material2869 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2869_pa_checked.trans (by decide +kernel)
    · exact v2869_pb_checked.trans (by decide +kernel)
    · exact v2869_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 44 Primitive.Addresses.material2869
    · exact v2869_mb_checked.trans (by decide +kernel)
    · exact v2869_mg_checked.trans (by decide +kernel)
  upper_error := v2869_upper_checked
  lower_error := reuse_lower_error 36 44 Primitive.Addresses.material2869

def v2870_pa : Scalar.QComplex := ((999999600427073957300063755703 : Int)/10^30,(-893949490981943926831608867 : Int)/10^30)
theorem v2870_pa_checked : Scalar.distance (sourceCoefficient 36 45 1 0) v2870_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2870_pb : Scalar.QComplex := ((-385719109390733509539286 : Int)/10^30,(-431477347611813927705029174 : Int)/10^30)
theorem v2870_pb_checked : Scalar.distance (sourceCoefficient 36 45 1 1) v2870_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2870_pg : Scalar.QComplex := ((-93086392596220018479863 : Int)/10^30,(83214566529024116705 : Int)/10^30)
theorem v2870_pg_checked : Scalar.distance (sourceCoefficient 36 45 1 2) v2870_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2870_mb : Scalar.QComplex := ((-758064483740527382955865 : Int)/10^30,(-431476854094858662477974068 : Int)/10^30)
theorem v2870_mb_checked : Scalar.distance (sourceCoefficient 36 45 3 1) v2870_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2870_mg : Scalar.QComplex := ((-93086286125478727002989 : Int)/10^30,(163543899899484509929 : Int)/10^30)
theorem v2870_mg_checked : Scalar.distance (sourceCoefficient 36 45 3 2) v2870_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2870_upper : Scalar.QComplex := ((999996568169414355411119998716 : Int)/10^30,(-2619856750631226629838106356 : Int)/10^30)
theorem v2870_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 45 5) 1) 14) v2870_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2870 : Material (36 : Basis) (45 : Basis) where
  plus := ![v2870_pa,v2870_pb,v2870_pg]
  minus := ![(Primitive.Addresses.material2870 1).one,v2870_mb,v2870_mg]
  upper := v2870_upper
  lower := (Primitive.Addresses.material2870 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2870_pa_checked.trans (by decide +kernel)
    · exact v2870_pb_checked.trans (by decide +kernel)
    · exact v2870_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 45 Primitive.Addresses.material2870
    · exact v2870_mb_checked.trans (by decide +kernel)
    · exact v2870_mg_checked.trans (by decide +kernel)
  upper_error := v2870_upper_checked
  lower_error := reuse_lower_error 36 45 Primitive.Addresses.material2870

def v2871_pa : Scalar.QComplex := ((999999585664372871318744733212 : Int)/10^30,(-910313727559543398549070742 : Int)/10^30)
theorem v2871_pa_checked : Scalar.distance (sourceCoefficient 36 46 1 0) v2871_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2871_pb : Scalar.QComplex := ((-392779909338322935756786 : Int)/10^30,(-431477340947735240254565490 : Int)/10^30)
theorem v2871_pb_checked : Scalar.distance (sourceCoefficient 36 46 1 1) v2871_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2871_pg : Scalar.QComplex := ((-93086391190266377482461 : Int)/10^30,(84737854859389462598 : Int)/10^30)
theorem v2871_pg_checked : Scalar.distance (sourceCoefficient 36 46 1 2) v2871_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2871_mb : Scalar.QComplex := ((-765125275308258525879435 : Int)/10^30,(-431476841337630108223572960 : Int)/10^30)
theorem v2871_mb_checked : Scalar.distance (sourceCoefficient 36 46 3 1) v2871_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2871_mg : Scalar.QComplex := ((-93086283404996386760701 : Int)/10^30,(165067186449385322331 : Int)/10^30)
theorem v2871_mg_checked : Scalar.distance (sourceCoefficient 36 46 3 2) v2871_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2871_upper : Scalar.QComplex := ((999996525163547475747868106291 : Int)/10^30,(-2636220937357135184859267585 : Int)/10^30)
theorem v2871_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 46 5) 1) 14) v2871_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2871 : Material (36 : Basis) (46 : Basis) where
  plus := ![v2871_pa,v2871_pb,v2871_pg]
  minus := ![(Primitive.Addresses.material2871 1).one,v2871_mb,v2871_mg]
  upper := v2871_upper
  lower := (Primitive.Addresses.material2871 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2871_pa_checked.trans (by decide +kernel)
    · exact v2871_pb_checked.trans (by decide +kernel)
    · exact v2871_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 46 Primitive.Addresses.material2871
    · exact v2871_mb_checked.trans (by decide +kernel)
    · exact v2871_mg_checked.trans (by decide +kernel)
  upper_error := v2871_upper_checked
  lower_error := reuse_lower_error 36 46 Primitive.Addresses.material2871

def v2872_pa : Scalar.QComplex := ((999999582071764451646897532875 : Int)/10^30,(-914251768624319444567243774 : Int)/10^30)
theorem v2872_pa_checked : Scalar.distance (sourceCoefficient 36 47 1 0) v2872_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2872_pb : Scalar.QComplex := ((-394479085459516954850375 : Int)/10^30,(-431477339321031660502297335 : Int)/10^30)
theorem v2872_pb_checked : Scalar.distance (sourceCoefficient 36 47 1 1) v2872_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2872_pg : Scalar.QComplex := ((-93086390847583316486174 : Int)/10^30,(85104433034803245034 : Int)/10^30)
theorem v2872_pg_checked : Scalar.distance (sourceCoefficient 36 47 1 2) v2872_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2872_mb : Scalar.QComplex := ((-766824449392999693550796 : Int)/10^30,(-431476838244614669628596862 : Int)/10^30)
theorem v2872_mb_checked : Scalar.distance (sourceCoefficient 36 47 3 1) v2872_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2872_mg : Scalar.QComplex := ((-93086282745972998047023 : Int)/10^30,(165433764192585248842 : Int)/10^30)
theorem v2872_mg_checked : Scalar.distance (sourceCoefficient 36 47 3 2) v2872_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2872_upper : Scalar.QComplex := ((999996514774242785335452609644 : Int)/10^30,(-2640158966356145446228786653 : Int)/10^30)
theorem v2872_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 47 5) 1) 14) v2872_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2872 : Material (36 : Basis) (47 : Basis) where
  plus := ![v2872_pa,v2872_pb,v2872_pg]
  minus := ![(Primitive.Addresses.material2872 1).one,v2872_mb,v2872_mg]
  upper := v2872_upper
  lower := (Primitive.Addresses.material2872 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2872_pa_checked.trans (by decide +kernel)
    · exact v2872_pb_checked.trans (by decide +kernel)
    · exact v2872_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 47 Primitive.Addresses.material2872
    · exact v2872_mb_checked.trans (by decide +kernel)
    · exact v2872_mg_checked.trans (by decide +kernel)
  upper_error := v2872_upper_checked
  lower_error := reuse_lower_error 36 47 Primitive.Addresses.material2872

def v2873_pa : Scalar.QComplex := ((999999556617101439785365407988 : Int)/10^30,(-941682324636092197224799313 : Int)/10^30)
theorem v2873_pa_checked : Scalar.distance (sourceCoefficient 36 48 1 0) v2873_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2873_pb : Scalar.QComplex := ((-406314753169491327688192 : Int)/10^30,(-431477327742661311931406939 : Int)/10^30)
theorem v2873_pb_checked : Scalar.distance (sourceCoefficient 36 48 1 1) v2873_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2873_pg : Scalar.QComplex := ((-93086388413889773094921 : Int)/10^30,(87657845499559539884 : Int)/10^30)
theorem v2873_pg_checked : Scalar.distance (sourceCoefficient 36 48 1 2) v2873_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2873_mb : Scalar.QComplex := ((-778660102704401920854907 : Int)/10^30,(-431476816452600457191849835 : Int)/10^30)
theorem v2873_mb_checked : Scalar.distance (sourceCoefficient 36 48 3 1) v2873_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2873_mg : Scalar.QComplex := ((-93086278108800405174777 : Int)/10^30,(167987173606421467891 : Int)/10^30)
theorem v2873_mg_checked : Scalar.distance (sourceCoefficient 36 48 3 2) v2873_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2873_upper : Scalar.QComplex := ((999996441976966489487035139871 : Int)/10^30,(-2667589437580888109325266151 : Int)/10^30)
theorem v2873_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 48 5) 1) 14) v2873_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2873 : Material (36 : Basis) (48 : Basis) where
  plus := ![v2873_pa,v2873_pb,v2873_pg]
  minus := ![(Primitive.Addresses.material2873 1).one,v2873_mb,v2873_mg]
  upper := v2873_upper
  lower := (Primitive.Addresses.material2873 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2873_pa_checked.trans (by decide +kernel)
    · exact v2873_pb_checked.trans (by decide +kernel)
    · exact v2873_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 48 Primitive.Addresses.material2873
    · exact v2873_mb_checked.trans (by decide +kernel)
    · exact v2873_mg_checked.trans (by decide +kernel)
  upper_error := v2873_upper_checked
  lower_error := reuse_lower_error 36 48 Primitive.Addresses.material2873

def v2874_pa : Scalar.QComplex := ((999999535621099624945058695371 : Int)/10^30,(-963720698699756458159207004 : Int)/10^30)
theorem v2874_pa_checked : Scalar.distance (sourceCoefficient 36 49 1 0) v2874_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2874_pb : Scalar.QComplex := ((-415823815597981375759818 : Int)/10^30,(-431477318126715276484830887 : Int)/10^30)
theorem v2874_pb_checked : Scalar.distance (sourceCoefficient 36 49 1 1) v2874_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2874_pg : Scalar.QComplex := ((-93086386399402160424590 : Int)/10^30,(89709318999382267205 : Int)/10^30)
theorem v2874_pg_checked : Scalar.distance (sourceCoefficient 36 49 1 2) v2874_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2874_mb : Scalar.QComplex := ((-788169153294105098719870 : Int)/10^30,(-431476798630765398688106833 : Int)/10^30)
theorem v2874_mb_checked : Scalar.distance (sourceCoefficient 36 49 3 1) v2874_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2874_mg : Scalar.QComplex := ((-93086274323984307179809 : Int)/10^30,(170038644603974773676 : Int)/10^30)
theorem v2874_mg_checked : Scalar.distance (sourceCoefficient 36 49 3 2) v2874_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2874_upper : Scalar.QComplex := ((999996382944761617517890379020 : Int)/10^30,(-2689627742583788621694449712 : Int)/10^30)
theorem v2874_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 49 5) 1) 14) v2874_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2874 : Material (36 : Basis) (49 : Basis) where
  plus := ![v2874_pa,v2874_pb,v2874_pg]
  minus := ![(Primitive.Addresses.material2874 1).one,v2874_mb,v2874_mg]
  upper := v2874_upper
  lower := (Primitive.Addresses.material2874 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2874_pa_checked.trans (by decide +kernel)
    · exact v2874_pb_checked.trans (by decide +kernel)
    · exact v2874_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 49 Primitive.Addresses.material2874
    · exact v2874_mb_checked.trans (by decide +kernel)
    · exact v2874_mg_checked.trans (by decide +kernel)
  upper_error := v2874_upper_checked
  lower_error := reuse_lower_error 36 49 Primitive.Addresses.material2874

def v2875_pa : Scalar.QComplex := ((999999533135931888853418159216 : Int)/10^30,(-966295978600881413391950720 : Int)/10^30)
theorem v2875_pa_checked : Scalar.distance (sourceCoefficient 36 50 1 0) v2875_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2875_pb : Scalar.QComplex := ((-416934990911892189323073 : Int)/10^30,(-431477316984816731004496664 : Int)/10^30)
theorem v2875_pb_checked : Scalar.distance (sourceCoefficient 36 50 1 1) v2875_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2875_pg : Scalar.QComplex := ((-93086386160558570219153 : Int)/10^30,(89949042603412440452 : Int)/10^30)
theorem v2875_pg_checked : Scalar.distance (sourceCoefficient 36 50 1 2) v2875_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2875_mb : Scalar.QComplex := ((-789280327208867544145359 : Int)/10^30,(-431476796529973027962119390 : Int)/10^30)
theorem v2875_mb_checked : Scalar.distance (sourceCoefficient 36 50 3 1) v2875_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2875_mg : Scalar.QComplex := ((-93086273878270132379048 : Int)/10^30,(170278367912633632002 : Int)/10^30)
theorem v2875_mg_checked : Scalar.distance (sourceCoefficient 36 50 3 2) v2875_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2875_upper : Scalar.QComplex := ((999996376014898101017623361099 : Int)/10^30,(-2692203014360162617990889225 : Int)/10^30)
theorem v2875_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 50 5) 1) 14) v2875_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2875 : Material (36 : Basis) (50 : Basis) where
  plus := ![v2875_pa,v2875_pb,v2875_pg]
  minus := ![(Primitive.Addresses.material2875 1).one,v2875_mb,v2875_mg]
  upper := v2875_upper
  lower := (Primitive.Addresses.material2875 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2875_pa_checked.trans (by decide +kernel)
    · exact v2875_pb_checked.trans (by decide +kernel)
    · exact v2875_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 50 Primitive.Addresses.material2875
    · exact v2875_mb_checked.trans (by decide +kernel)
    · exact v2875_mg_checked.trans (by decide +kernel)
  upper_error := v2875_upper_checked
  lower_error := reuse_lower_error 36 50 Primitive.Addresses.material2875

def v2876_pa : Scalar.QComplex := ((999999522153675057626670551408 : Int)/10^30,(-977595223774971395479274180 : Int)/10^30)
theorem v2876_pa_checked : Scalar.distance (sourceCoefficient 36 51 1 0) v2876_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2876_pb : Scalar.QComplex := ((-421810360870122777014778 : Int)/10^30,(-431477311929550455737695015 : Int)/10^30)
theorem v2876_pb_checked : Scalar.distance (sourceCoefficient 36 51 1 1) v2876_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2876_pg : Scalar.QComplex := ((-93086385104100564685579 : Int)/10^30,(91000848960667598003 : Int)/10^30)
theorem v2876_pg_checked : Scalar.distance (sourceCoefficient 36 51 1 2) v2876_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2876_mb : Scalar.QComplex := ((-794155690989307966159302 : Int)/10^30,(-431476787267483939560773128 : Int)/10^30)
theorem v2876_mb_checked : Scalar.distance (sourceCoefficient 36 51 3 1) v2876_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2876_mg : Scalar.QComplex := ((-93086271914151005501685 : Int)/10^30,(171330172966577535149 : Int)/10^30)
theorem v2876_mg_checked : Scalar.distance (sourceCoefficient 36 51 3 2) v2876_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2876_upper : Scalar.QComplex := ((999996345531185515607918215353 : Int)/10^30,(-2703502223750975227706927654 : Int)/10^30)
theorem v2876_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 51 5) 1) 14) v2876_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2876 : Material (36 : Basis) (51 : Basis) where
  plus := ![v2876_pa,v2876_pb,v2876_pg]
  minus := ![(Primitive.Addresses.material2876 1).one,v2876_mb,v2876_mg]
  upper := v2876_upper
  lower := (Primitive.Addresses.material2876 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2876_pa_checked.trans (by decide +kernel)
    · exact v2876_pb_checked.trans (by decide +kernel)
    · exact v2876_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 51 Primitive.Addresses.material2876
    · exact v2876_mb_checked.trans (by decide +kernel)
    · exact v2876_mg_checked.trans (by decide +kernel)
  upper_error := v2876_upper_checked
  lower_error := reuse_lower_error 36 51 Primitive.Addresses.material2876

def v2877_pa : Scalar.QComplex := ((999999498214138480329158657836 : Int)/10^30,(-1001784144040167398399366492 : Int)/10^30)
theorem v2877_pa_checked : Scalar.distance (sourceCoefficient 36 52 1 0) v2877_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2877_pb : Scalar.QComplex := ((-432247335410934887343688 : Int)/10^30,(-431477300860535458766106887 : Int)/10^30)
theorem v2877_pb_checked : Scalar.distance (sourceCoefficient 36 52 1 1) v2877_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2877_pg : Scalar.QComplex := ((-93086382795869725347270 : Int)/10^30,(93252509103746336860 : Int)/10^30)
theorem v2877_pg_checked : Scalar.distance (sourceCoefficient 36 52 1 2) v2877_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2877_mb : Scalar.QComplex := ((-804592652091896049186083 : Int)/10^30,(-431476767191834099252222724 : Int)/10^30)
theorem v2877_mb_checked : Scalar.distance (sourceCoefficient 36 52 3 1) v2877_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2877_mg : Scalar.QComplex := ((-93086267662839733154548 : Int)/10^30,(173581830279361041294 : Int)/10^30)
theorem v2877_mg_checked : Scalar.distance (sourceCoefficient 36 52 3 2) v2877_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2877_upper : Scalar.QComplex := ((999996279843802617414434832554 : Int)/10^30,(-2727691066672147571169296594 : Int)/10^30)
theorem v2877_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 52 5) 1) 14) v2877_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2877 : Material (36 : Basis) (52 : Basis) where
  plus := ![v2877_pa,v2877_pb,v2877_pg]
  minus := ![(Primitive.Addresses.material2877 1).one,v2877_mb,v2877_mg]
  upper := v2877_upper
  lower := (Primitive.Addresses.material2877 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2877_pa_checked.trans (by decide +kernel)
    · exact v2877_pb_checked.trans (by decide +kernel)
    · exact v2877_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 52 Primitive.Addresses.material2877
    · exact v2877_mb_checked.trans (by decide +kernel)
    · exact v2877_mg_checked.trans (by decide +kernel)
  upper_error := v2877_upper_checked
  lower_error := reuse_lower_error 36 52 Primitive.Addresses.material2877

def v2878_pa : Scalar.QComplex := ((999999494497987517768409935643 : Int)/10^30,(-1005486832053099816497483541 : Int)/10^30)
theorem v2878_pa_checked : Scalar.distance (sourceCoefficient 36 53 1 0) v2878_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2878_pb : Scalar.QComplex := ((-433844961921041386984048 : Int)/10^30,(-431477299136453201421458642 : Int)/10^30)
theorem v2878_pb_checked : Scalar.distance (sourceCoefficient 36 53 1 1) v2878_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2878_pg : Scalar.QComplex := ((-93086382436932419158675 : Int)/10^30,(93597179097356884138 : Int)/10^30)
theorem v2878_pg_checked : Scalar.distance (sourceCoefficient 36 53 1 2) v2878_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2878_mb : Scalar.QComplex := ((-806190276519327845669205 : Int)/10^30,(-431476764089072760067225464 : Int)/10^30)
theorem v2878_mb_checked : Scalar.distance (sourceCoefficient 36 53 3 1) v2878_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2878_mg : Scalar.QComplex := ((-93086267006467879489072 : Int)/10^30,(173926499834888468449 : Int)/10^30)
theorem v2878_mg_checked : Scalar.distance (sourceCoefficient 36 53 3 2) v2878_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2878_upper : Scalar.QComplex := ((999996269737153584535247000680 : Int)/10^30,(-2731393742756621707494009571 : Int)/10^30)
theorem v2878_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 53 5) 1) 14) v2878_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2878 : Material (36 : Basis) (53 : Basis) where
  plus := ![v2878_pa,v2878_pb,v2878_pg]
  minus := ![(Primitive.Addresses.material2878 1).one,v2878_mb,v2878_mg]
  upper := v2878_upper
  lower := (Primitive.Addresses.material2878 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2878_pa_checked.trans (by decide +kernel)
    · exact v2878_pb_checked.trans (by decide +kernel)
    · exact v2878_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 53 Primitive.Addresses.material2878
    · exact v2878_mb_checked.trans (by decide +kernel)
    · exact v2878_mg_checked.trans (by decide +kernel)
  upper_error := v2878_upper_checked
  lower_error := reuse_lower_error 36 53 Primitive.Addresses.material2878

def v2879_pa : Scalar.QComplex := ((999999492603416873581129706449 : Int)/10^30,(-1007369301101410957733723479 : Int)/10^30)
theorem v2879_pa_checked : Scalar.distance (sourceCoefficient 36 54 1 0) v2879_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2879_pb : Scalar.QComplex := ((-434657204929753955302583 : Int)/10^30,(-431477298256894982160278050 : Int)/10^30)
theorem v2879_pb_checked : Scalar.distance (sourceCoefficient 36 54 1 1) v2879_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2879_pg : Scalar.QComplex := ((-93086382253875606060237 : Int)/10^30,(93772411412946595448 : Int)/10^30)
theorem v2879_pg_checked : Scalar.distance (sourceCoefficient 36 54 1 2) v2879_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2879_mb : Scalar.QComplex := ((-807002518466586091113983 : Int)/10^30,(-431476762508585733853943490 : Int)/10^30)
theorem v2879_mb_checked : Scalar.distance (sourceCoefficient 36 54 3 1) v2879_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2879_mg : Scalar.QComplex := ((-93086266672193538367654 : Int)/10^30,(174101731927261395022 : Int)/10^30)
theorem v2879_mg_checked : Scalar.distance (sourceCoefficient 36 54 3 2) v2879_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2879_upper : Scalar.QComplex := ((999996264593614960961391481863 : Int)/10^30,(-2733276205731359273857767142 : Int)/10^30)
theorem v2879_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 54 5) 1) 14) v2879_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2879 : Material (36 : Basis) (54 : Basis) where
  plus := ![v2879_pa,v2879_pb,v2879_pg]
  minus := ![(Primitive.Addresses.material2879 1).one,v2879_mb,v2879_mg]
  upper := v2879_upper
  lower := (Primitive.Addresses.material2879 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2879_pa_checked.trans (by decide +kernel)
    · exact v2879_pb_checked.trans (by decide +kernel)
    · exact v2879_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 54 Primitive.Addresses.material2879
    · exact v2879_mb_checked.trans (by decide +kernel)
    · exact v2879_mg_checked.trans (by decide +kernel)
  upper_error := v2879_upper_checked
  lower_error := reuse_lower_error 36 54 Primitive.Addresses.material2879

def v2880_pa : Scalar.QComplex := ((999999477029036355000988410137 : Int)/10^30,(-1022712889227161939263114945 : Int)/10^30)
theorem v2880_pa_checked : Scalar.distance (sourceCoefficient 36 55 1 0) v2880_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2880_pb : Scalar.QComplex := ((-441277617701949120490388 : Int)/10^30,(-431477291011781643595136888 : Int)/10^30)
theorem v2880_pb_checked : Scalar.distance (sourceCoefficient 36 55 1 1) v2880_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2880_pg : Scalar.QComplex := ((-93086380747467944266735 : Int)/10^30,(95200691189139814340 : Int)/10^30)
theorem v2880_pg_checked : Scalar.distance (sourceCoefficient 36 55 1 2) v2880_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2880_mb : Scalar.QComplex := ((-813622922521492510012623 : Int)/10^30,(-431476749550357042893771524 : Int)/10^30)
theorem v2880_mb_checked : Scalar.distance (sourceCoefficient 36 55 3 1) v2880_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2880_mg : Scalar.QComplex := ((-93086263933245317956999 : Int)/10^30,(175530009871678811581 : Int)/10^30)
theorem v2880_mg_checked : Scalar.distance (sourceCoefficient 36 55 3 2) v2880_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2880_upper : Scalar.QComplex := ((999996222537616492986720927374 : Int)/10^30,(-2748619744124670248247303832 : Int)/10^30)
theorem v2880_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 55 5) 1) 14) v2880_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2880 : Material (36 : Basis) (55 : Basis) where
  plus := ![v2880_pa,v2880_pb,v2880_pg]
  minus := ![(Primitive.Addresses.material2880 1).one,v2880_mb,v2880_mg]
  upper := v2880_upper
  lower := (Primitive.Addresses.material2880 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2880_pa_checked.trans (by decide +kernel)
    · exact v2880_pb_checked.trans (by decide +kernel)
    · exact v2880_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 55 Primitive.Addresses.material2880
    · exact v2880_mb_checked.trans (by decide +kernel)
    · exact v2880_mg_checked.trans (by decide +kernel)
  upper_error := v2880_upper_checked
  lower_error := reuse_lower_error 36 55 Primitive.Addresses.material2880

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
