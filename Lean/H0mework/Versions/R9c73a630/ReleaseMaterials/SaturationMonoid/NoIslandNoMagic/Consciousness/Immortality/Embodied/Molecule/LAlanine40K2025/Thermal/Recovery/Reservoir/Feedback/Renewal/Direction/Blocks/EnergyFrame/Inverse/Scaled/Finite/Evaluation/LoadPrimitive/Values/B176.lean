import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B117
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B118

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2817_pa : Scalar.QComplex := ((999999510601167109089542677109 : Int)/10^30,(-989341915755419350695267336 : Int)/10^30)
theorem v2817_pa_checked : Scalar.distance (sourceCoefficient 35 53 1 0) v2817_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2817_pb : Scalar.QComplex := ((-426878792977471985035331 : Int)/10^30,(-431477305535511057360366225 : Int)/10^30)
theorem v2817_pb_checked : Scalar.distance (sourceCoefficient 35 53 1 1) v2817_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2817_pg : Scalar.QComplex := ((-93086383876688605904570 : Int)/10^30,(92094306426153565748 : Int)/10^30)
theorem v2817_pg_checked : Scalar.distance (sourceCoefficient 35 53 1 2) v2817_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2817_mb : Scalar.QComplex := ((-799224115691680237867916 : Int)/10^30,(-431476776499618287042364509 : Int)/10^30)
theorem v2817_mb_checked : Scalar.distance (sourceCoefficient 35 53 3 1) v2817_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2817_mg : Scalar.QComplex := ((-93086269743134958523946 : Int)/10^30,(172423628965718075173 : Int)/10^30)
theorem v2817_mg_checked : Scalar.distance (sourceCoefficient 35 53 3 2) v2817_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2817_upper : Scalar.QComplex := ((999996313704970066493209060925 : Int)/10^30,(-2715248878297524657575035797 : Int)/10^30)
theorem v2817_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 53 5) 1) 14) v2817_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2817 : Material (35 : Basis) (53 : Basis) where
  plus := ![v2817_pa,v2817_pb,v2817_pg]
  minus := ![(Primitive.Addresses.material2817 1).one,v2817_mb,v2817_mg]
  upper := v2817_upper
  lower := (Primitive.Addresses.material2817 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2817_pa_checked.trans (by decide +kernel)
    · exact v2817_pb_checked.trans (by decide +kernel)
    · exact v2817_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 53 Primitive.Addresses.material2817
    · exact v2817_mb_checked.trans (by decide +kernel)
    · exact v2817_mg_checked.trans (by decide +kernel)
  upper_error := v2817_upper_checked
  lower_error := reuse_lower_error 35 53 Primitive.Addresses.material2817

def v2818_pa : Scalar.QComplex := ((999999508736988785483830169703 : Int)/10^30,(-991224384834072850759831856 : Int)/10^30)
theorem v2818_pa_checked : Scalar.distance (sourceCoefficient 35 54 1 0) v2818_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2818_pb : Scalar.QComplex := ((-427691035994912583762868 : Int)/10^30,(-431477304664695240090297684 : Int)/10^30)
theorem v2818_pb_checked : Scalar.distance (sourceCoefficient 35 54 1 1) v2818_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2818_pg : Scalar.QComplex := ((-93086383695989386646045 : Int)/10^30,(92269538744096995265 : Int)/10^30)
theorem v2818_pg_checked : Scalar.distance (sourceCoefficient 35 54 1 2) v2818_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2818_mb : Scalar.QComplex := ((-800036357655210809647012 : Int)/10^30,(-431476774927873652033101631 : Int)/10^30)
theorem v2818_mb_checked : Scalar.distance (sourceCoefficient 35 54 3 1) v2818_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2818_mg : Scalar.QComplex := ((-93086269411218208333448 : Int)/10^30,(172598861062479216377 : Int)/10^30)
theorem v2818_mg_checked : Scalar.distance (sourceCoefficient 35 54 3 2) v2818_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2818_upper : Scalar.QComplex := ((999996308591823665866971190018 : Int)/10^30,(-2717131341355058925729739297 : Int)/10^30)
theorem v2818_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 54 5) 1) 14) v2818_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2818 : Material (35 : Basis) (54 : Basis) where
  plus := ![v2818_pa,v2818_pb,v2818_pg]
  minus := ![(Primitive.Addresses.material2818 1).one,v2818_mb,v2818_mg]
  upper := v2818_upper
  lower := (Primitive.Addresses.material2818 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2818_pa_checked.trans (by decide +kernel)
    · exact v2818_pb_checked.trans (by decide +kernel)
    · exact v2818_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 54 Primitive.Addresses.material2818
    · exact v2818_mb_checked.trans (by decide +kernel)
    · exact v2818_mg_checked.trans (by decide +kernel)
  upper_error := v2818_upper_checked
  lower_error := reuse_lower_error 35 54 Primitive.Addresses.material2818

def v2819_pa : Scalar.QComplex := ((999999493410329338142628273720 : Int)/10^30,(-1006567973209271308257515140 : Int)/10^30)
theorem v2819_pa_checked : Scalar.distance (sourceCoefficient 35 55 1 0) v2819_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2819_pb : Scalar.QComplex := ((-434311448838861733771221 : Int)/10^30,(-431477297490839283129876823 : Int)/10^30)
theorem v2819_pb_checked : Scalar.distance (sourceCoefficient 35 55 1 1) v2819_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2819_pg : Scalar.QComplex := ((-93086382208797949880687 : Int)/10^30,(93697818539640359895 : Int)/10^30)
theorem v2819_pg_checked : Scalar.distance (sourceCoefficient 35 55 1 2) v2819_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2819_mb : Scalar.QComplex := ((-806656761843363097660454 : Int)/10^30,(-431476762040902254224812950 : Int)/10^30)
theorem v2819_mb_checked : Scalar.distance (sourceCoefficient 35 55 3 1) v2819_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2819_mg : Scalar.QComplex := ((-93086266691486189097555 : Int)/10^30,(174027139042829508202 : Int)/10^30)
theorem v2819_mg_checked : Scalar.distance (sourceCoefficient 35 55 3 2) v2819_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2819_upper : Scalar.QComplex := ((999996266783545469656089963579 : Int)/10^30,(-2732474880425361100443231185 : Int)/10^30)
theorem v2819_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 55 5) 1) 14) v2819_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2819 : Material (35 : Basis) (55 : Basis) where
  plus := ![v2819_pa,v2819_pb,v2819_pg]
  minus := ![(Primitive.Addresses.material2819 1).one,v2819_mb,v2819_mg]
  upper := v2819_upper
  lower := (Primitive.Addresses.material2819 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2819_pa_checked.trans (by decide +kernel)
    · exact v2819_pb_checked.trans (by decide +kernel)
    · exact v2819_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 55 Primitive.Addresses.material2819
    · exact v2819_mb_checked.trans (by decide +kernel)
    · exact v2819_mg_checked.trans (by decide +kernel)
  upper_error := v2819_upper_checked
  lower_error := reuse_lower_error 35 55 Primitive.Addresses.material2819

def v2820_pa : Scalar.QComplex := ((999999489738318249668029331953 : Int)/10^30,(-1010209435282446804498143599 : Int)/10^30)
theorem v2820_pa_checked : Scalar.distance (sourceCoefficient 35 56 1 0) v2820_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2820_pb : Scalar.QComplex := ((-435882657709607122734216 : Int)/10^30,(-431477295768396550981033105 : Int)/10^30)
theorem v2820_pb_checked : Scalar.distance (sourceCoefficient 35 56 1 1) v2820_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2820_pg : Scalar.QComplex := ((-93086381852091909919743 : Int)/10^30,(94036789226658190181 : Int)/10^30)
theorem v2820_pg_checked : Scalar.distance (sourceCoefficient 35 56 1 2) v2820_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2820_mb : Scalar.QComplex := ((-808227968642685114348620 : Int)/10^30,(-431476758962577672587479433 : Int)/10^30)
theorem v2820_mb_checked : Scalar.distance (sourceCoefficient 35 56 3 1) v2820_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2820_mg : Scalar.QComplex := ((-93086266042263845731202 : Int)/10^30,(174366109295811812943 : Int)/10^30)
theorem v2820_mg_checked : Scalar.distance (sourceCoefficient 35 56 3 2) v2820_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2820_upper : Scalar.QComplex := ((999996256826706662768475260283 : Int)/10^30,(-2736116330737448578408886670 : Int)/10^30)
theorem v2820_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 56 5) 1) 14) v2820_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2820 : Material (35 : Basis) (56 : Basis) where
  plus := ![v2820_pa,v2820_pb,v2820_pg]
  minus := ![(Primitive.Addresses.material2820 1).one,v2820_mb,v2820_mg]
  upper := v2820_upper
  lower := (Primitive.Addresses.material2820 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2820_pa_checked.trans (by decide +kernel)
    · exact v2820_pb_checked.trans (by decide +kernel)
    · exact v2820_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 56 Primitive.Addresses.material2820
    · exact v2820_mb_checked.trans (by decide +kernel)
    · exact v2820_mg_checked.trans (by decide +kernel)
  upper_error := v2820_upper_checked
  lower_error := reuse_lower_error 35 56 Primitive.Addresses.material2820

def v2821_pa : Scalar.QComplex := ((999999477770857718807303393034 : Int)/10^30,(-1021987285556483009548427321 : Int)/10^30)
theorem v2821_pa_checked : Scalar.distance (sourceCoefficient 35 57 1 0) v2821_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2821_pb : Scalar.QComplex := ((-440964534819222424890931 : Int)/10^30,(-431477290145133115674241421 : Int)/10^30)
theorem v2821_pb_checked : Scalar.distance (sourceCoefficient 35 57 1 1) v2821_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2821_pg : Scalar.QComplex := ((-93086380688509852402090 : Int)/10^30,(95133147203429470583 : Int)/10^30)
theorem v2821_pg_checked : Scalar.distance (sourceCoefficient 35 57 1 2) v2821_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2821_mb : Scalar.QComplex := ((-813309839007462233051929 : Int)/10^30,(-431476748953885264729274775 : Int)/10^30)
theorem v2821_mb_checked : Scalar.distance (sourceCoefficient 35 57 3 1) v2821_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2821_mg : Scalar.QComplex := ((-93086263932574665644984 : Int)/10^30,(175462465860240002711 : Int)/10^30)
theorem v2821_mg_checked : Scalar.distance (sourceCoefficient 35 57 3 2) v2821_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2821_upper : Scalar.QComplex := ((999996224531762861278290126896 : Int)/10^30,(-2747894142815009127035538603 : Int)/10^30)
theorem v2821_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 57 5) 1) 14) v2821_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2821 : Material (35 : Basis) (57 : Basis) where
  plus := ![v2821_pa,v2821_pb,v2821_pg]
  minus := ![(Primitive.Addresses.material2821 1).one,v2821_mb,v2821_mg]
  upper := v2821_upper
  lower := (Primitive.Addresses.material2821 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2821_pa_checked.trans (by decide +kernel)
    · exact v2821_pb_checked.trans (by decide +kernel)
    · exact v2821_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 57 Primitive.Addresses.material2821
    · exact v2821_mb_checked.trans (by decide +kernel)
    · exact v2821_mg_checked.trans (by decide +kernel)
  upper_error := v2821_upper_checked
  lower_error := reuse_lower_error 35 57 Primitive.Addresses.material2821

def v2822_pa : Scalar.QComplex := ((999999471219377018742551801197 : Int)/10^30,(-1028377832488413596858010659 : Int)/10^30)
theorem v2822_pa_checked : Scalar.distance (sourceCoefficient 35 58 1 0) v2822_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2822_pb : Scalar.QComplex := ((-443721911866917018030261 : Int)/10^30,(-431477287060606978225354247 : Int)/10^30)
theorem v2822_pb_checked : Scalar.distance (sourceCoefficient 35 58 1 1) v2822_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2822_pg : Scalar.QComplex := ((-93086380050856939835842 : Int)/10^30,(95728020370015211249 : Int)/10^30)
theorem v2822_pg_checked : Scalar.distance (sourceCoefficient 35 58 1 2) v2822_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2822_mb : Scalar.QComplex := ((-816067212366652198259867 : Int)/10^30,(-431476743489868071282170321 : Int)/10^30)
theorem v2822_mb_checked : Scalar.distance (sourceCoefficient 35 58 3 1) v2822_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2822_mg : Scalar.QComplex := ((-93086262781573239835417 : Int)/10^30,(176057338255061531687 : Int)/10^30)
theorem v2822_mg_checked : Scalar.distance (sourceCoefficient 35 58 3 2) v2822_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2822_upper : Scalar.QComplex := ((999996206950787660251194989028 : Int)/10^30,(-2754284668921709402984553372 : Int)/10^30)
theorem v2822_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 58 5) 1) 14) v2822_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2822 : Material (35 : Basis) (58 : Basis) where
  plus := ![v2822_pa,v2822_pb,v2822_pg]
  minus := ![(Primitive.Addresses.material2822 1).one,v2822_mb,v2822_mg]
  upper := v2822_upper
  lower := (Primitive.Addresses.material2822 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2822_pa_checked.trans (by decide +kernel)
    · exact v2822_pb_checked.trans (by decide +kernel)
    · exact v2822_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 58 Primitive.Addresses.material2822
    · exact v2822_mb_checked.trans (by decide +kernel)
    · exact v2822_mg_checked.trans (by decide +kernel)
  upper_error := v2822_upper_checked
  lower_error := reuse_lower_error 35 58 Primitive.Addresses.material2822

def v2823_pa : Scalar.QComplex := ((999999453000686248025628316855 : Int)/10^30,(-1045943750062927379331551409 : Int)/10^30)
theorem v2823_pa_checked : Scalar.distance (sourceCoefficient 35 59 1 0) v2823_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2823_pb : Scalar.QComplex := ((-451301209561911141918517 : Int)/10^30,(-431477278461014257929726841 : Int)/10^30)
theorem v2823_pb_checked : Scalar.distance (sourceCoefficient 35 59 1 1) v2823_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2823_pg : Scalar.QComplex := ((-93086378275267719411672 : Int)/10^30,(97363168830596267585 : Int)/10^30)
theorem v2823_pg_checked : Scalar.distance (sourceCoefficient 35 59 1 2) v2823_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2823_mb : Scalar.QComplex := ((-823646499818466192948410 : Int)/10^30,(-431476728349686001124349227 : Int)/10^30)
theorem v2823_mb_checked : Scalar.distance (sourceCoefficient 35 59 3 1) v2823_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2823_mg : Scalar.QComplex := ((-93086259594925203415668 : Int)/10^30,(177692484574548558517 : Int)/10^30)
theorem v2823_mg_checked : Scalar.distance (sourceCoefficient 35 59 3 2) v2823_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2823_upper : Scalar.QComplex := ((999996158414943858117361171364 : Int)/10^30,(-2771850528890044912305153303 : Int)/10^30)
theorem v2823_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 59 5) 1) 14) v2823_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2823 : Material (35 : Basis) (59 : Basis) where
  plus := ![v2823_pa,v2823_pb,v2823_pg]
  minus := ![(Primitive.Addresses.material2823 1).one,v2823_mb,v2823_mg]
  upper := v2823_upper
  lower := (Primitive.Addresses.material2823 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2823_pa_checked.trans (by decide +kernel)
    · exact v2823_pb_checked.trans (by decide +kernel)
    · exact v2823_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 59 Primitive.Addresses.material2823
    · exact v2823_mb_checked.trans (by decide +kernel)
    · exact v2823_mg_checked.trans (by decide +kernel)
  upper_error := v2823_upper_checked
  lower_error := reuse_lower_error 35 59 Primitive.Addresses.material2823

def v2824_pa : Scalar.QComplex := ((999999431600441783744521699480 : Int)/10^30,(-1066207668962502434019368197 : Int)/10^30)
theorem v2824_pa_checked : Scalar.distance (sourceCoefficient 35 60 1 0) v2824_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2824_pb : Scalar.QComplex := ((-460044633955023230082428 : Int)/10^30,(-431477268320076093568442336 : Int)/10^30)
theorem v2824_pb_checked : Scalar.distance (sourceCoefficient 35 60 1 1) v2824_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2824_pg : Scalar.QComplex := ((-93086376185334776096637 : Int)/10^30,(99249464578084210457 : Int)/10^30)
theorem v2824_pg_checked : Scalar.distance (sourceCoefficient 35 60 1 2) v2824_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2824_mb : Scalar.QComplex := ((-832389912204828880378057 : Int)/10^30,(-431476710663570150658597917 : Int)/10^30)
theorem v2824_mb_checked : Scalar.distance (sourceCoefficient 35 60 3 1) v2824_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2824_mg : Scalar.QComplex := ((-93086255877204763802855 : Int)/10^30,(179578777816164383628 : Int)/10^30)
theorem v2824_mg_checked : Scalar.distance (sourceCoefficient 35 60 3 2) v2824_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2824_upper : Scalar.QComplex := ((999996102041045574682326755348 : Int)/10^30,(-2792114380674012602864648563 : Int)/10^30)
theorem v2824_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 60 5) 1) 14) v2824_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2824 : Material (35 : Basis) (60 : Basis) where
  plus := ![v2824_pa,v2824_pb,v2824_pg]
  minus := ![(Primitive.Addresses.material2824 1).one,v2824_mb,v2824_mg]
  upper := v2824_upper
  lower := (Primitive.Addresses.material2824 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2824_pa_checked.trans (by decide +kernel)
    · exact v2824_pb_checked.trans (by decide +kernel)
    · exact v2824_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 60 Primitive.Addresses.material2824
    · exact v2824_mb_checked.trans (by decide +kernel)
    · exact v2824_mg_checked.trans (by decide +kernel)
  upper_error := v2824_upper_checked
  lower_error := reuse_lower_error 35 60 Primitive.Addresses.material2824

def v2825_pa : Scalar.QComplex := ((999999425336007349725009641874 : Int)/10^30,(-1072067001199946239610524920 : Int)/10^30)
theorem v2825_pa_checked : Scalar.distance (sourceCoefficient 35 61 1 0) v2825_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2825_pb : Scalar.QComplex := ((-462572803766998697886979 : Int)/10^30,(-431477265343784363929341703 : Int)/10^30)
theorem v2825_pb_checked : Scalar.distance (sourceCoefficient 35 61 1 1) v2825_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2825_pg : Scalar.QComplex := ((-93086375572717098611826 : Int)/10^30,(99794888861344027235 : Int)/10^30)
theorem v2825_pg_checked : Scalar.distance (sourceCoefficient 35 61 1 2) v2825_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2825_mb : Scalar.QComplex := ((-834918078507045468640684 : Int)/10^30,(-431476705505582846035583676 : Int)/10^30)
theorem v2825_mb_checked : Scalar.distance (sourceCoefficient 35 61 3 1) v2825_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2825_mg : Scalar.QComplex := ((-93086254793910722968203 : Int)/10^30,(180124201367676348235 : Int)/10^30)
theorem v2825_mg_checked : Scalar.distance (sourceCoefficient 35 61 3 2) v2825_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2825_upper : Scalar.QComplex := ((999996085663944583442328824498 : Int)/10^30,(-2797973693372823798232108312 : Int)/10^30)
theorem v2825_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 61 5) 1) 14) v2825_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2825 : Material (35 : Basis) (61 : Basis) where
  plus := ![v2825_pa,v2825_pb,v2825_pg]
  minus := ![(Primitive.Addresses.material2825 1).one,v2825_mb,v2825_mg]
  upper := v2825_upper
  lower := (Primitive.Addresses.material2825 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2825_pa_checked.trans (by decide +kernel)
    · exact v2825_pb_checked.trans (by decide +kernel)
    · exact v2825_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 61 Primitive.Addresses.material2825
    · exact v2825_mb_checked.trans (by decide +kernel)
    · exact v2825_mg_checked.trans (by decide +kernel)
  upper_error := v2825_upper_checked
  lower_error := reuse_lower_error 35 61 Primitive.Addresses.material2825

def v2826_pa : Scalar.QComplex := ((999999416172872891850096934881 : Int)/10^30,(-1080580359511584616684993952 : Int)/10^30)
theorem v2826_pa_checked : Scalar.distance (sourceCoefficient 35 62 1 0) v2826_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2826_pb : Scalar.QComplex := ((-466246126002477085327051 : Int)/10^30,(-431477260984163128609587739 : Int)/10^30)
theorem v2826_pb_checked : Scalar.distance (sourceCoefficient 35 62 1 1) v2826_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2826_pg : Scalar.QComplex := ((-93086374675965699516958 : Int)/10^30,(100587366938618544710 : Int)/10^30)
theorem v2826_pg_checked : Scalar.distance (sourceCoefficient 35 62 1 2) v2826_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2826_mb : Scalar.QComplex := ((-838591395612621332663228 : Int)/10^30,(-431476697976051585076265419 : Int)/10^30)
theorem v2826_mb_checked : Scalar.distance (sourceCoefficient 35 62 3 1) v2826_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2826_mg : Scalar.QComplex := ((-93086253213286768974611 : Int)/10^30,(180916678376018990268 : Int)/10^30)
theorem v2826_mg_checked : Scalar.distance (sourceCoefficient 35 62 3 2) v2826_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2826_upper : Scalar.QComplex := ((999996061807539652924928419013 : Int)/10^30,(-2806487023190076218210502986 : Int)/10^30)
theorem v2826_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 62 5) 1) 14) v2826_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2826 : Material (35 : Basis) (62 : Basis) where
  plus := ![v2826_pa,v2826_pb,v2826_pg]
  minus := ![(Primitive.Addresses.material2826 1).one,v2826_mb,v2826_mg]
  upper := v2826_upper
  lower := (Primitive.Addresses.material2826 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2826_pa_checked.trans (by decide +kernel)
    · exact v2826_pb_checked.trans (by decide +kernel)
    · exact v2826_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 62 Primitive.Addresses.material2826
    · exact v2826_mb_checked.trans (by decide +kernel)
    · exact v2826_mg_checked.trans (by decide +kernel)
  upper_error := v2826_upper_checked
  lower_error := reuse_lower_error 35 62 Primitive.Addresses.material2826

def v2827_pa : Scalar.QComplex := ((999999389072294903228696608553 : Int)/10^30,(-1105375518527926215431443506 : Int)/10^30)
theorem v2827_pa_checked : Scalar.distance (sourceCoefficient 35 63 1 0) v2827_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2827_pb : Scalar.QComplex := ((-476944678174100157020272 : Int)/10^30,(-431477248049195813102609523 : Int)/10^30)
theorem v2827_pb_checked : Scalar.distance (sourceCoefficient 35 63 1 1) v2827_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2827_pg : Scalar.QComplex := ((-93086372019330700848149 : Int)/10^30,(102895459600438114125 : Int)/10^30)
theorem v2827_pg_checked : Scalar.distance (sourceCoefficient 35 63 1 2) v2827_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2827_mb : Scalar.QComplex := ((-849289932638390258891795 : Int)/10^30,(-431476675808720406640951430 : Int)/10^30)
theorem v2827_mb_checked : Scalar.distance (sourceCoefficient 35 63 3 1) v2827_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2827_mg : Scalar.QComplex := ((-93086248564872744976724 : Int)/10^30,(183224767885873823189 : Int)/10^30)
theorem v2827_mg_checked : Scalar.distance (sourceCoefficient 35 63 3 2) v2827_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2827_upper : Scalar.QComplex := ((999995991912806964480005011418 : Int)/10^30,(-2831282098503802042965770372 : Int)/10^30)
theorem v2827_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 63 5) 1) 14) v2827_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2827 : Material (35 : Basis) (63 : Basis) where
  plus := ![v2827_pa,v2827_pb,v2827_pg]
  minus := ![(Primitive.Addresses.material2827 1).one,v2827_mb,v2827_mg]
  upper := v2827_upper
  lower := (Primitive.Addresses.material2827 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2827_pa_checked.trans (by decide +kernel)
    · exact v2827_pb_checked.trans (by decide +kernel)
    · exact v2827_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 63 Primitive.Addresses.material2827
    · exact v2827_mb_checked.trans (by decide +kernel)
    · exact v2827_mg_checked.trans (by decide +kernel)
  upper_error := v2827_upper_checked
  lower_error := reuse_lower_error 35 63 Primitive.Addresses.material2827

def v2828_pa : Scalar.QComplex := ((999999349272902879965632021051 : Int)/10^30,(-1140812767632933625071646744 : Int)/10^30)
theorem v2828_pa_checked : Scalar.distance (sourceCoefficient 35 64 1 0) v2828_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2828_pb : Scalar.QComplex := ((-492235052038072430622048 : Int)/10^30,(-431477228948551441398659491 : Int)/10^30)
theorem v2828_pb_checked : Scalar.distance (sourceCoefficient 35 64 1 1) v2828_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2828_pg : Scalar.QComplex := ((-93086368106564277381063 : Int)/10^30,(106194186331982239388 : Int)/10^30)
theorem v2828_pg_checked : Scalar.distance (sourceCoefficient 35 64 1 2) v2828_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2828_mb : Scalar.QComplex := ((-864580284326061706637062 : Int)/10^30,(-431476643513179155246608388 : Int)/10^30)
theorem v2828_mb_checked : Scalar.distance (sourceCoefficient 35 64 3 1) v2828_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2828_mg : Scalar.QComplex := ((-93086241805455178225662 : Int)/10^30,(186523490012610028045 : Int)/10^30)
theorem v2828_mg_checked : Scalar.distance (sourceCoefficient 35 64 3 2) v2828_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2828_upper : Scalar.QComplex := ((999995890951997104619242780248 : Int)/10^30,(-2866719226139049602882724262 : Int)/10^30)
theorem v2828_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 64 5) 1) 14) v2828_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2828 : Material (35 : Basis) (64 : Basis) where
  plus := ![v2828_pa,v2828_pb,v2828_pg]
  minus := ![(Primitive.Addresses.material2828 1).one,v2828_mb,v2828_mg]
  upper := v2828_upper
  lower := (Primitive.Addresses.material2828 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2828_pa_checked.trans (by decide +kernel)
    · exact v2828_pb_checked.trans (by decide +kernel)
    · exact v2828_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 64 Primitive.Addresses.material2828
    · exact v2828_mb_checked.trans (by decide +kernel)
    · exact v2828_mg_checked.trans (by decide +kernel)
  upper_error := v2828_upper_checked
  lower_error := reuse_lower_error 35 64 Primitive.Addresses.material2828

def v2829_pa : Scalar.QComplex := ((999999307594926451868606091563 : Int)/10^30,(-1176779362357904759250669569 : Int)/10^30)
theorem v2829_pa_checked : Scalar.distance (sourceCoefficient 35 65 1 0) v2829_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2829_pb : Scalar.QComplex := ((-507753826243030731581692 : Int)/10^30,(-431477208823855614902105397 : Int)/10^30)
theorem v2829_pb_checked : Scalar.distance (sourceCoefficient 35 65 1 1) v2829_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2829_pg : Scalar.QComplex := ((-93086363995898695133195 : Int)/10^30,(109542187914876169594 : Int)/10^30)
theorem v2829_pg_checked : Scalar.distance (sourceCoefficient 35 65 1 2) v2829_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2829_mb : Scalar.QComplex := ((-880099035385965012459241 : Int)/10^30,(-431476609996487622859372935 : Int)/10^30)
theorem v2829_mb_checked : Scalar.distance (sourceCoefficient 35 65 3 1) v2829_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2829_mg : Scalar.QComplex := ((-93086234805616548922761 : Int)/10^30,(189871486801570697733 : Int)/10^30)
theorem v2829_mg_checked : Scalar.distance (sourceCoefficient 35 65 3 2) v2829_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2829_upper : Scalar.QComplex := ((999995787199003119657444556443 : Int)/10^30,(-2902685695363596508809560616 : Int)/10^30)
theorem v2829_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 65 5) 1) 14) v2829_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2829 : Material (35 : Basis) (65 : Basis) where
  plus := ![v2829_pa,v2829_pb,v2829_pg]
  minus := ![(Primitive.Addresses.material2829 1).one,v2829_mb,v2829_mg]
  upper := v2829_upper
  lower := (Primitive.Addresses.material2829 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2829_pa_checked.trans (by decide +kernel)
    · exact v2829_pb_checked.trans (by decide +kernel)
    · exact v2829_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 65 Primitive.Addresses.material2829
    · exact v2829_mb_checked.trans (by decide +kernel)
    · exact v2829_mg_checked.trans (by decide +kernel)
  upper_error := v2829_upper_checked
  lower_error := reuse_lower_error 35 65 Primitive.Addresses.material2829

def v2830_pa : Scalar.QComplex := ((999999286743579997256387241477 : Int)/10^30,(-1194366916517184241111115888 : Int)/10^30)
theorem v2830_pa_checked : Scalar.distance (sourceCoefficient 35 66 1 0) v2830_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2830_pb : Scalar.QComplex := ((-515342458944447874938148 : Int)/10^30,(-431477198712005620589174670 : Int)/10^30)
theorem v2830_pb_checked : Scalar.distance (sourceCoefficient 35 66 1 1) v2830_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2830_pg : Scalar.QComplex := ((-93086361934650952634559 : Int)/10^30,(111179350373077076621 : Int)/10^30)
theorem v2830_pg_checked : Scalar.distance (sourceCoefficient 35 66 1 2) v2830_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2830_mb : Scalar.QComplex := ((-887687656535716259156170 : Int)/10^30,(-431476593335993151656761490 : Int)/10^30)
theorem v2830_mb_checked : Scalar.distance (sourceCoefficient 35 66 3 1) v2830_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2830_mg : Scalar.QComplex := ((-93086231331572107553424 : Int)/10^30,(191508646871417232928 : Int)/10^30)
theorem v2830_mg_checked : Scalar.distance (sourceCoefficient 35 66 3 2) v2830_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2830_upper : Scalar.QComplex := ((999995735993164772209742890239 : Int)/10^30,(-2920273187340747688375046788 : Int)/10^30)
theorem v2830_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 66 5) 1) 14) v2830_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2830 : Material (35 : Basis) (66 : Basis) where
  plus := ![v2830_pa,v2830_pb,v2830_pg]
  minus := ![(Primitive.Addresses.material2830 1).one,v2830_mb,v2830_mg]
  upper := v2830_upper
  lower := (Primitive.Addresses.material2830 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2830_pa_checked.trans (by decide +kernel)
    · exact v2830_pb_checked.trans (by decide +kernel)
    · exact v2830_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 66 Primitive.Addresses.material2830
    · exact v2830_mb_checked.trans (by decide +kernel)
    · exact v2830_mg_checked.trans (by decide +kernel)
  upper_error := v2830_upper_checked
  lower_error := reuse_lower_error 35 66 Primitive.Addresses.material2830

def v2831_pa : Scalar.QComplex := ((999999251053635694622131430487 : Int)/10^30,(-1223884049936961606326705088 : Int)/10^30)
theorem v2831_pa_checked : Scalar.distance (sourceCoefficient 35 67 1 0) v2831_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2831_pb : Scalar.QComplex := ((-528078435657886804093510 : Int)/10^30,(-431477181341371332085105625 : Int)/10^30)
theorem v2831_pb_checked : Scalar.distance (sourceCoefficient 35 67 1 1) v2831_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2831_pg : Scalar.QComplex := ((-93086358399766561443177 : Int)/10^30,(113926994637398233685 : Int)/10^30)
theorem v2831_pg_checked : Scalar.distance (sourceCoefficient 35 67 1 2) v2831_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2831_mb : Scalar.QComplex := ((-900423613516893948355280 : Int)/10^30,(-431476564974791034433796315 : Int)/10^30)
theorem v2831_mb_checked : Scalar.distance (sourceCoefficient 35 67 3 1) v2831_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2831_mg : Scalar.QComplex := ((-93086225425595781755769 : Int)/10^30,(194256287062218832523 : Int)/10^30)
theorem v2831_mg_checked : Scalar.distance (sourceCoefficient 35 67 3 2) v2831_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2831_upper : Scalar.QComplex := ((999995649359379116445582252695 : Int)/10^30,(-2949790215200616050998474531 : Int)/10^30)
theorem v2831_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 67 5) 1) 14) v2831_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2831 : Material (35 : Basis) (67 : Basis) where
  plus := ![v2831_pa,v2831_pb,v2831_pg]
  minus := ![(Primitive.Addresses.material2831 1).one,v2831_mb,v2831_mg]
  upper := v2831_upper
  lower := (Primitive.Addresses.material2831 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2831_pa_checked.trans (by decide +kernel)
    · exact v2831_pb_checked.trans (by decide +kernel)
    · exact v2831_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 67 Primitive.Addresses.material2831
    · exact v2831_mb_checked.trans (by decide +kernel)
    · exact v2831_mg_checked.trans (by decide +kernel)
  upper_error := v2831_upper_checked
  lower_error := reuse_lower_error 35 67 Primitive.Addresses.material2831

def v2832_pa : Scalar.QComplex := ((999999189681711572688585838156 : Int)/10^30,(-1273041994687879206003261811 : Int)/10^30)
theorem v2832_pa_checked : Scalar.distance (sourceCoefficient 35 68 1 0) v2832_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2832_pb : Scalar.QComplex := ((-549288978451789547021963 : Int)/10^30,(-431477151299755564651775227 : Int)/10^30)
theorem v2832_pb_checked : Scalar.distance (sourceCoefficient 35 68 1 1) v2832_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2832_pg : Scalar.QComplex := ((-93086352302749280180379 : Int)/10^30,(118502931638803340608 : Int)/10^30)
theorem v2832_pg_checked : Scalar.distance (sourceCoefficient 35 68 1 2) v2832_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2832_mb : Scalar.QComplex := ((-921634122488580856272811 : Int)/10^30,(-431476516629443309114421379 : Int)/10^30)
theorem v2832_mb_checked : Scalar.distance (sourceCoefficient 35 68 3 1) v2832_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2832_mg : Scalar.QComplex := ((-93086215379753231030573 : Int)/10^30,(198832217098342148906 : Int)/10^30)
theorem v2832_mg_checked : Scalar.distance (sourceCoefficient 35 68 3 2) v2832_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2832_upper : Scalar.QComplex := ((999995503145393334611510215707 : Int)/10^30,(-2998947980814176025017258889 : Int)/10^30)
theorem v2832_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 68 5) 1) 14) v2832_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2832 : Material (35 : Basis) (68 : Basis) where
  plus := ![v2832_pa,v2832_pb,v2832_pg]
  minus := ![(Primitive.Addresses.material2832 1).one,v2832_mb,v2832_mg]
  upper := v2832_upper
  lower := (Primitive.Addresses.material2832 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2832_pa_checked.trans (by decide +kernel)
    · exact v2832_pb_checked.trans (by decide +kernel)
    · exact v2832_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 68 Primitive.Addresses.material2832
    · exact v2832_mb_checked.trans (by decide +kernel)
    · exact v2832_mg_checked.trans (by decide +kernel)
  upper_error := v2832_upper_checked
  lower_error := reuse_lower_error 35 68 Primitive.Addresses.material2832

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
