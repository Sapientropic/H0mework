import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B127
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B128

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3057_pa : Scalar.QComplex := ((999999431368344062389106678690 : Int)/10^30,(-1066425331907143723159655227 : Int)/10^30)
theorem v3057_pa_checked : Scalar.distance (sourceCoefficient 39 55 1 0) v3057_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3057_pb : Scalar.QComplex := ((-460138555417023296068207 : Int)/10^30,(-431477272717055019874419523 : Int)/10^30)
theorem v3057_pb_checked : Scalar.distance (sourceCoefficient 39 55 1 1) v3057_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3057_pg : Scalar.QComplex := ((-93086376648831612440812 : Int)/10^30,(99269726561672644587 : Int)/10^30)
theorem v3057_pg_checked : Scalar.distance (sourceCoefficient 39 55 1 2) v3057_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3057_mb : Scalar.QComplex := ((-832483837426252474460880 : Int)/10^30,(-431476714979497448127933096 : Int)/10^30)
theorem v3057_mb_checked : Scalar.distance (sourceCoefficient 39 55 3 1) v3057_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3057_mg : Scalar.QComplex := ((-93086256323216248295020 : Int)/10^30,(179599040192185249893 : Int)/10^30)
theorem v3057_mg_checked : Scalar.distance (sourceCoefficient 39 55 3 2) v3057_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3057_upper : Scalar.QComplex := ((999996101433281702786427312626 : Int)/10^30,(-2792332042893890893128657750 : Int)/10^30)
theorem v3057_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 55 5) 1) 14) v3057_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3057 : Material (39 : Basis) (55 : Basis) where
  plus := ![v3057_pa,v3057_pb,v3057_pg]
  minus := ![(Primitive.Addresses.material3057 1).one,v3057_mb,v3057_mg]
  upper := v3057_upper
  lower := (Primitive.Addresses.material3057 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3057_pa_checked.trans (by decide +kernel)
    · exact v3057_pb_checked.trans (by decide +kernel)
    · exact v3057_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 55 Primitive.Addresses.material3057
    · exact v3057_mb_checked.trans (by decide +kernel)
    · exact v3057_mg_checked.trans (by decide +kernel)
  upper_error := v3057_upper_checked
  lower_error := reuse_lower_error 39 55 Primitive.Addresses.material3057

def v3058_pa : Scalar.QComplex := ((999999427478364562007075497918 : Int)/10^30,(-1070066793753998706154399064 : Int)/10^30)
theorem v3058_pa_checked : Scalar.distance (sourceCoefficient 39 56 1 0) v3058_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3058_pb : Scalar.QComplex := ((-461709764222667209787109 : Int)/10^30,(-431477270931913308441363877 : Int)/10^30)
theorem v3058_pb_checked : Scalar.distance (sourceCoefficient 39 56 1 1) v3058_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3058_pg : Scalar.QComplex := ((-93086376275217321467074 : Int)/10^30,(99608697231134334449 : Int)/10^30)
theorem v3058_pg_checked : Scalar.distance (sourceCoefficient 39 56 1 2) v3058_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3058_mb : Scalar.QComplex := ((-834055044106366644880133 : Int)/10^30,(-431476711838473966731724198 : Int)/10^30)
theorem v3058_mb_checked : Scalar.distance (sourceCoefficient 39 56 3 1) v3058_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3058_mg : Scalar.QComplex := ((-93086255657085675361747 : Int)/10^30,(179938010413020361642 : Int)/10^30)
theorem v3058_mg_checked : Scalar.distance (sourceCoefficient 39 56 3 2) v3058_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3058_upper : Scalar.QComplex := ((999996091258475199238399763993 : Int)/10^30,(-2795973492603464489913882275 : Int)/10^30)
theorem v3058_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 56 5) 1) 14) v3058_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3058 : Material (39 : Basis) (56 : Basis) where
  plus := ![v3058_pa,v3058_pb,v3058_pg]
  minus := ![(Primitive.Addresses.material3058 1).one,v3058_mb,v3058_mg]
  upper := v3058_upper
  lower := (Primitive.Addresses.material3058 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3058_pa_checked.trans (by decide +kernel)
    · exact v3058_pb_checked.trans (by decide +kernel)
    · exact v3058_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 56 Primitive.Addresses.material3058
    · exact v3058_mb_checked.trans (by decide +kernel)
    · exact v3058_mg_checked.trans (by decide +kernel)
  upper_error := v3058_upper_checked
  lower_error := reuse_lower_error 39 56 Primitive.Addresses.material3058

def v3059_pa : Scalar.QComplex := ((999999414805912665663272205646 : Int)/10^30,(-1081844643290594476529168739 : Int)/10^30)
theorem v3059_pa_checked : Scalar.distance (sourceCoefficient 39 57 1 0) v3059_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3059_pb : Scalar.QComplex := ((-466791641120156534073568 : Int)/10^30,(-431477265105857924443818460 : Int)/10^30)
theorem v3059_pb_checked : Scalar.distance (sourceCoefficient 39 57 1 1) v3059_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3059_pg : Scalar.QComplex := ((-93086375056947656408033 : Int)/10^30,(100705055150700867317 : Int)/10^30)
theorem v3059_pg_checked : Scalar.distance (sourceCoefficient 39 57 1 2) v3059_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3059_mb : Scalar.QComplex := ((-839136914084017546387582 : Int)/10^30,(-431476701626989868746641458 : Int)/10^30)
theorem v3059_mb_checked : Scalar.distance (sourceCoefficient 39 57 3 1) v3059_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3059_mg : Scalar.QComplex := ((-93086253492708957461957 : Int)/10^30,(181034366873050882906 : Int)/10^30)
theorem v3059_mg_checked : Scalar.distance (sourceCoefficient 39 57 3 2) v3059_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3059_upper : Scalar.QComplex := ((999996058258542355022252237432 : Int)/10^30,(-2807751302726834561689207553 : Int)/10^30)
theorem v3059_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 57 5) 1) 14) v3059_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3059 : Material (39 : Basis) (57 : Basis) where
  plus := ![v3059_pa,v3059_pb,v3059_pg]
  minus := ![(Primitive.Addresses.material3059 1).one,v3059_mb,v3059_mg]
  upper := v3059_upper
  lower := (Primitive.Addresses.material3059 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3059_pa_checked.trans (by decide +kernel)
    · exact v3059_pb_checked.trans (by decide +kernel)
    · exact v3059_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 57 Primitive.Addresses.material3059
    · exact v3059_mb_checked.trans (by decide +kernel)
    · exact v3059_mg_checked.trans (by decide +kernel)
  upper_error := v3059_upper_checked
  lower_error := reuse_lower_error 39 57 Primitive.Addresses.material3059

def v3060_pa : Scalar.QComplex := ((999999407871910512050053082549 : Int)/10^30,(-1088235189818922154664219169 : Int)/10^30)
theorem v3060_pa_checked : Scalar.distance (sourceCoefficient 39 58 1 0) v3060_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3060_pb : Scalar.QComplex := ((-469549018051754073517322 : Int)/10^30,(-431477261911298849366874137 : Int)/10^30)
theorem v3060_pb_checked : Scalar.distance (sourceCoefficient 39 58 1 1) v3060_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3060_pg : Scalar.QComplex := ((-93086374389621780247561 : Int)/10^30,(101299928285978313194 : Int)/10^30)
theorem v3060_pg_checked : Scalar.distance (sourceCoefficient 39 58 1 2) v3060_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3060_mb : Scalar.QComplex := ((-841894287232157031654717 : Int)/10^30,(-431476696052939878828299809 : Int)/10^30)
theorem v3060_mb_checked : Scalar.distance (sourceCoefficient 39 58 3 1) v3060_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3060_mg : Scalar.QComplex := ((-93086252312034606124415 : Int)/10^30,(181629239210957697589 : Int)/10^30)
theorem v3060_mg_checked : Scalar.distance (sourceCoefficient 39 58 3 2) v3060_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3060_upper : Scalar.QComplex := ((999996040295046966749467167704 : Int)/10^30,(-2814141827769735202833345323 : Int)/10^30)
theorem v3060_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 58 5) 1) 14) v3060_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3060 : Material (39 : Basis) (58 : Basis) where
  plus := ![v3060_pa,v3060_pb,v3060_pg]
  minus := ![(Primitive.Addresses.material3060 1).one,v3060_mb,v3060_mg]
  upper := v3060_upper
  lower := (Primitive.Addresses.material3060 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3060_pa_checked.trans (by decide +kernel)
    · exact v3060_pb_checked.trans (by decide +kernel)
    · exact v3060_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 58 Primitive.Addresses.material3060
    · exact v3060_mb_checked.trans (by decide +kernel)
    · exact v3060_mg_checked.trans (by decide +kernel)
  upper_error := v3060_upper_checked
  lower_error := reuse_lower_error 39 58 Primitive.Addresses.material3060

def v3061_pa : Scalar.QComplex := ((999999388601769780527219696342 : Int)/10^30,(-1105801106271444116746160991 : Int)/10^30)
theorem v3061_pa_checked : Scalar.distance (sourceCoefficient 39 59 1 0) v3061_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3061_pb : Scalar.QComplex := ((-477128315424005368806992 : Int)/10^30,(-431477253009254784677864943 : Int)/10^30)
theorem v3061_pb_checked : Scalar.distance (sourceCoefficient 39 59 1 1) v3061_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3061_pg : Scalar.QComplex := ((-93086372532469457657024 : Int)/10^30,(102935076659524192500 : Int)/10^30)
theorem v3061_pg_checked : Scalar.distance (sourceCoefficient 39 59 1 2) v3061_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3061_mb : Scalar.QComplex := ((-849473574100226429607974 : Int)/10^30,(-431476680610306855406080436 : Int)/10^30)
theorem v3061_mb_checked : Scalar.distance (sourceCoefficient 39 59 3 1) v3061_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3061_mg : Scalar.QComplex := ((-93086249043823573015408 : Int)/10^30,(183264385373024296092 : Int)/10^30)
theorem v3061_mg_checked : Scalar.distance (sourceCoefficient 39 59 3 2) v3061_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3061_upper : Scalar.QComplex := ((999995990707756706277023773001 : Int)/10^30,(-2831707684801373317281687449 : Int)/10^30)
theorem v3061_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 59 5) 1) 14) v3061_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3061 : Material (39 : Basis) (59 : Basis) where
  plus := ![v3061_pa,v3061_pb,v3061_pg]
  minus := ![(Primitive.Addresses.material3061 1).one,v3061_mb,v3061_mg]
  upper := v3061_upper
  lower := (Primitive.Addresses.material3061 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3061_pa_checked.trans (by decide +kernel)
    · exact v3061_pb_checked.trans (by decide +kernel)
    · exact v3061_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 59 Primitive.Addresses.material3061
    · exact v3061_mb_checked.trans (by decide +kernel)
    · exact v3061_mg_checked.trans (by decide +kernel)
  upper_error := v3061_upper_checked
  lower_error := reuse_lower_error 39 59 Primitive.Addresses.material3061

def v3062_pa : Scalar.QComplex := ((999999365988580041381331049640 : Int)/10^30,(-1126065023853754503938578096 : Int)/10^30)
theorem v3062_pa_checked : Scalar.distance (sourceCoefficient 39 60 1 0) v3062_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3062_pb : Scalar.QComplex := ((-485871739438204066840722 : Int)/10^30,(-431477242519410878383204590 : Int)/10^30)
theorem v3062_pb_checked : Scalar.distance (sourceCoefficient 39 60 1 1) v3062_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3062_pg : Scalar.QComplex := ((-93086370348445893767832 : Int)/10^30,(104821372304829248316 : Int)/10^30)
theorem v3062_pg_checked : Scalar.distance (sourceCoefficient 39 60 1 2) v3062_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3062_mb : Scalar.QComplex := ((-858216985806585926836989 : Int)/10^30,(-431476662575285719905696837 : Int)/10^30)
theorem v3062_mb_checked : Scalar.distance (sourceCoefficient 39 60 3 1) v3062_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3062_mg : Scalar.QComplex := ((-93086245232012636041904 : Int)/10^30,(185150678431261304324 : Int)/10^30)
theorem v3062_mg_checked : Scalar.distance (sourceCoefficient 39 60 3 2) v3062_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3062_upper : Scalar.QComplex := ((999995933120917227996026457830 : Int)/10^30,(-2851971533174644795375924377 : Int)/10^30)
theorem v3062_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 60 5) 1) 14) v3062_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3062 : Material (39 : Basis) (60 : Basis) where
  plus := ![v3062_pa,v3062_pb,v3062_pg]
  minus := ![(Primitive.Addresses.material3062 1).one,v3062_mb,v3062_mg]
  upper := v3062_upper
  lower := (Primitive.Addresses.material3062 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3062_pa_checked.trans (by decide +kernel)
    · exact v3062_pb_checked.trans (by decide +kernel)
    · exact v3062_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 60 Primitive.Addresses.material3062
    · exact v3062_mb_checked.trans (by decide +kernel)
    · exact v3062_mg_checked.trans (by decide +kernel)
  upper_error := v3062_upper_checked
  lower_error := reuse_lower_error 39 60 Primitive.Addresses.material3062

def v3063_pa : Scalar.QComplex := ((999999359373421278878589640924 : Int)/10^30,(-1131924355705728887373808248 : Int)/10^30)
theorem v3063_pa_checked : Scalar.distance (sourceCoefficient 39 61 1 0) v3063_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3063_pb : Scalar.QComplex := ((-488399909139298609167126 : Int)/10^30,(-431477239442232707708646042 : Int)/10^30)
theorem v3063_pb_checked : Scalar.distance (sourceCoefficient 39 61 1 1) v3063_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3063_pg : Scalar.QComplex := ((-93086369708621820094790 : Int)/10^30,(105366796558187421650 : Int)/10^30)
theorem v3063_pg_checked : Scalar.distance (sourceCoefficient 39 61 1 2) v3063_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3063_mb : Scalar.QComplex := ((-860745151910861176050537 : Int)/10^30,(-431476657316412107497102213 : Int)/10^30)
theorem v3063_mb_checked : Scalar.distance (sourceCoefficient 39 61 3 1) v3063_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3063_mg : Scalar.QComplex := ((-93086244121512234952978 : Int)/10^30,(185696101929393742040 : Int)/10^30)
theorem v3063_mg_checked : Scalar.distance (sourceCoefficient 39 61 3 2) v3063_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3063_upper : Scalar.QComplex := ((999995916393093095920740606265 : Int)/10^30,(-2857830844882668769199363198 : Int)/10^30)
theorem v3063_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 61 5) 1) 14) v3063_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3063 : Material (39 : Basis) (61 : Basis) where
  plus := ![v3063_pa,v3063_pb,v3063_pg]
  minus := ![(Primitive.Addresses.material3063 1).one,v3063_mb,v3063_mg]
  upper := v3063_upper
  lower := (Primitive.Addresses.material3063 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3063_pa_checked.trans (by decide +kernel)
    · exact v3063_pb_checked.trans (by decide +kernel)
    · exact v3063_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 61 Primitive.Addresses.material3063
    · exact v3063_mb_checked.trans (by decide +kernel)
    · exact v3063_mg_checked.trans (by decide +kernel)
  upper_error := v3063_upper_checked
  lower_error := reuse_lower_error 39 61 Primitive.Addresses.material3063

def v3064_pa : Scalar.QComplex := ((999999349700699421732577808604 : Int)/10^30,(-1140437713453634657464720121 : Int)/10^30)
theorem v3064_pa_checked : Scalar.distance (sourceCoefficient 39 62 1 0) v3064_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3064_pb : Scalar.QComplex := ((-492073231212618367245218 : Int)/10^30,(-431477234936027802789255876 : Int)/10^30)
theorem v3064_pb_checked : Scalar.distance (sourceCoefficient 39 62 1 1) v3064_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3064_pg : Scalar.QComplex := ((-93086368772340694808723 : Int)/10^30,(106159274591732059557 : Int)/10^30)
theorem v3064_pg_checked : Scalar.distance (sourceCoefficient 39 62 1 2) v3064_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3064_mb : Scalar.QComplex := ((-864418468727783366109089 : Int)/10^30,(-431476649640297371453540937 : Int)/10^30)
theorem v3064_mb_checked : Scalar.distance (sourceCoefficient 39 62 3 1) v3064_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3064_mg : Scalar.QComplex := ((-93086242501358607223828 : Int)/10^30,(186488578859894147437 : Int)/10^30)
theorem v3064_mg_checked : Scalar.distance (sourceCoefficient 39 62 3 2) v3064_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3064_upper : Scalar.QComplex := ((999995892027102498054150179885 : Int)/10^30,(-2866344173256687800073518598 : Int)/10^30)
theorem v3064_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 62 5) 1) 14) v3064_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3064 : Material (39 : Basis) (62 : Basis) where
  plus := ![v3064_pa,v3064_pb,v3064_pg]
  minus := ![(Primitive.Addresses.material3064 1).one,v3064_mb,v3064_mg]
  upper := v3064_upper
  lower := (Primitive.Addresses.material3064 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3064_pa_checked.trans (by decide +kernel)
    · exact v3064_pb_checked.trans (by decide +kernel)
    · exact v3064_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 62 Primitive.Addresses.material3064
    · exact v3064_mb_checked.trans (by decide +kernel)
    · exact v3064_mg_checked.trans (by decide +kernel)
  upper_error := v3064_upper_checked
  lower_error := reuse_lower_error 39 62 Primitive.Addresses.material3064

def v3065_pa : Scalar.QComplex := ((999999321115947957870562315726 : Int)/10^30,(-1165232870803386990611759573 : Int)/10^30)
theorem v3065_pa_checked : Scalar.distance (sourceCoefficient 39 63 1 0) v3065_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3065_pb : Scalar.QComplex := ((-502771782904844243547640 : Int)/10^30,(-431477221574135499716197649 : Int)/10^30)
theorem v3065_pb_checked : Scalar.distance (sourceCoefficient 39 63 1 1) v3065_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3065_pg : Scalar.QComplex := ((-93086366000575355115152 : Int)/10^30,(108467367124270925807 : Int)/10^30)
theorem v3065_pg_checked : Scalar.distance (sourceCoefficient 39 63 1 2) v3065_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3065_mb : Scalar.QComplex := ((-875117004905738239166479 : Int)/10^30,(-431476627046041778114019618 : Int)/10^30)
theorem v3065_mb_checked : Scalar.distance (sourceCoefficient 39 63 3 1) v3065_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3065_mg : Scalar.QComplex := ((-93086237737814396632890 : Int)/10^30,(188796668141116026304 : Int)/10^30)
theorem v3065_mg_checked : Scalar.distance (sourceCoefficient 39 63 3 2) v3065_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3065_upper : Scalar.QComplex := ((999995820648201421252540340741 : Int)/10^30,(-2891139244342278066318913025 : Int)/10^30)
theorem v3065_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 63 5) 1) 14) v3065_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3065 : Material (39 : Basis) (63 : Basis) where
  plus := ![v3065_pa,v3065_pb,v3065_pg]
  minus := ![(Primitive.Addresses.material3065 1).one,v3065_mb,v3065_mg]
  upper := v3065_upper
  lower := (Primitive.Addresses.material3065 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3065_pa_checked.trans (by decide +kernel)
    · exact v3065_pb_checked.trans (by decide +kernel)
    · exact v3065_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 63 Primitive.Addresses.material3065
    · exact v3065_mb_checked.trans (by decide +kernel)
    · exact v3065_mg_checked.trans (by decide +kernel)
  upper_error := v3065_upper_checked
  lower_error := reuse_lower_error 39 63 Primitive.Addresses.material3065

def v3066_pa : Scalar.QComplex := ((999999279195374736492304593384 : Int)/10^30,(-1200670117462622449165800557 : Int)/10^30)
theorem v3066_pa_checked : Scalar.distance (sourceCoefficient 39 64 1 0) v3066_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3066_pb : Scalar.QComplex := ((-518062156065286117815176 : Int)/10^30,(-431477201863329802591027209 : Int)/10^30)
theorem v3066_pb_checked : Scalar.distance (sourceCoefficient 39 64 1 1) v3066_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3066_pg : Scalar.QComplex := ((-93086361923264612204699 : Int)/10^30,(111766093666091569848 : Int)/10^30)
theorem v3066_pg_checked : Scalar.distance (sourceCoefficient 39 64 1 2) v3066_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3066_mb : Scalar.QComplex := ((-890407355363337806341481 : Int)/10^30,(-431476594140340035604452165 : Int)/10^30)
theorem v3066_mb_checked : Scalar.distance (sourceCoefficient 39 64 3 1) v3066_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3066_mg : Scalar.QComplex := ((-93086230813852735428651 : Int)/10^30,(192095389936134483703 : Int)/10^30)
theorem v3066_mg_checked : Scalar.distance (sourceCoefficient 39 64 3 2) v3066_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3066_upper : Scalar.QComplex := ((999995717566217743707316996975 : Int)/10^30,(-2926576365870791001947998186 : Int)/10^30)
theorem v3066_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 64 5) 1) 14) v3066_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3066 : Material (39 : Basis) (64 : Basis) where
  plus := ![v3066_pa,v3066_pb,v3066_pg]
  minus := ![(Primitive.Addresses.material3066 1).one,v3066_mb,v3066_mg]
  upper := v3066_upper
  lower := (Primitive.Addresses.material3066 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3066_pa_checked.trans (by decide +kernel)
    · exact v3066_pb_checked.trans (by decide +kernel)
    · exact v3066_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 64 Primitive.Addresses.material3066
    · exact v3066_mb_checked.trans (by decide +kernel)
    · exact v3066_mg_checked.trans (by decide +kernel)
  upper_error := v3066_upper_checked
  lower_error := reuse_lower_error 39 64 Primitive.Addresses.material3066

def v3067_pa : Scalar.QComplex := ((999999235364531865990220350047 : Int)/10^30,(-1236636709628426173215233499 : Int)/10^30)
theorem v3067_pa_checked : Scalar.distance (sourceCoefficient 39 65 1 0) v3067_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3067_pb : Scalar.QComplex := ((-533580929534095627590709 : Int)/10^30,(-431477181119358338688035164 : Int)/10^30)
theorem v3067_pb_checked : Scalar.distance (sourceCoefficient 39 65 1 1) v3067_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3067_pg : Scalar.QComplex := ((-93086357645596822235536 : Int)/10^30,(115114095050465703840 : Int)/10^30)
theorem v3067_pg_checked : Scalar.distance (sourceCoefficient 39 65 1 2) v3067_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3067_mb : Scalar.QComplex := ((-905926105152685611138972 : Int)/10^30,(-431476560004373731658652743 : Int)/10^30)
theorem v3067_mb_checked : Scalar.distance (sourceCoefficient 39 65 3 1) v3067_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3067_mg : Scalar.QComplex := ((-93086223647012131900652 : Int)/10^30,(195443386382460047332 : Int)/10^30)
theorem v3067_mg_checked : Scalar.distance (sourceCoefficient 39 65 3 2) v3067_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3067_upper : Scalar.QComplex := ((999995611660364939672916994340 : Int)/10^30,(-2962542828820522136251354668 : Int)/10^30)
theorem v3067_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 65 5) 1) 14) v3067_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3067 : Material (39 : Basis) (65 : Basis) where
  plus := ![v3067_pa,v3067_pb,v3067_pg]
  minus := ![(Primitive.Addresses.material3067 1).one,v3067_mb,v3067_mg]
  upper := v3067_upper
  lower := (Primitive.Addresses.material3067 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3067_pa_checked.trans (by decide +kernel)
    · exact v3067_pb_checked.trans (by decide +kernel)
    · exact v3067_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 65 Primitive.Addresses.material3067
    · exact v3067_mb_checked.trans (by decide +kernel)
    · exact v3067_mg_checked.trans (by decide +kernel)
  upper_error := v3067_upper_checked
  lower_error := reuse_lower_error 39 65 Primitive.Addresses.material3067

def v3068_pa : Scalar.QComplex := ((999999213460440345777950143317 : Int)/10^30,(-1254224262508091173569437058 : Int)/10^30)
theorem v3068_pa_checked : Scalar.distance (sourceCoefficient 39 66 1 0) v3068_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3068_pb : Scalar.QComplex := ((-541169561867429523238404 : Int)/10^30,(-431477170704684463941861628 : Int)/10^30)
theorem v3068_pb_checked : Scalar.distance (sourceCoefficient 39 66 1 1) v3068_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3068_pg : Scalar.QComplex := ((-93086355502685514159262 : Int)/10^30,(116751257409404325495 : Int)/10^30)
theorem v3068_pg_checked : Scalar.distance (sourceCoefficient 39 66 1 2) v3068_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3068_mb : Scalar.QComplex := ((-913514725673030377048750 : Int)/10^30,(-431476543041055810417233827 : Int)/10^30)
theorem v3068_mb_checked : Scalar.distance (sourceCoefficient 39 66 3 1) v3068_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3068_mg : Scalar.QComplex := ((-93086220091304241019636 : Int)/10^30,(197080546282572355011 : Int)/10^30)
theorem v3068_mg_checked : Scalar.distance (sourceCoefficient 39 66 3 2) v3068_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3068_upper : Scalar.QComplex := ((999995559401785303063784421257 : Int)/10^30,(-2980130317701118261206678260 : Int)/10^30)
theorem v3068_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 66 5) 1) 14) v3068_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3068 : Material (39 : Basis) (66 : Basis) where
  plus := ![v3068_pa,v3068_pb,v3068_pg]
  minus := ![(Primitive.Addresses.material3068 1).one,v3068_mb,v3068_mg]
  upper := v3068_upper
  lower := (Primitive.Addresses.material3068 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3068_pa_checked.trans (by decide +kernel)
    · exact v3068_pb_checked.trans (by decide +kernel)
    · exact v3068_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 66 Primitive.Addresses.material3068
    · exact v3068_mb_checked.trans (by decide +kernel)
    · exact v3068_mg_checked.trans (by decide +kernel)
  upper_error := v3068_upper_checked
  lower_error := reuse_lower_error 39 66 Primitive.Addresses.material3068

def v3069_pa : Scalar.QComplex := ((999999176003677515962074260521 : Int)/10^30,(-1283741393738683018657901647 : Int)/10^30)
theorem v3069_pa_checked : Scalar.distance (sourceCoefficient 39 67 1 0) v3069_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3069_pb : Scalar.QComplex := ((-553905537951145574041495 : Int)/10^30,(-431477152825821869423465933 : Int)/10^30)
theorem v3069_pb_checked : Scalar.distance (sourceCoefficient 39 67 1 1) v3069_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3069_pg : Scalar.QComplex := ((-93086351830745433798448 : Int)/10^30,(119498901503905930880 : Int)/10^30)
theorem v3069_pg_checked : Scalar.distance (sourceCoefficient 39 67 1 2) v3069_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3069_mb : Scalar.QComplex := ((-926250681585907284033029 : Int)/10^30,(-431476514171626119839049866 : Int)/10^30)
theorem v3069_mb_checked : Scalar.distance (sourceCoefficient 39 67 3 1) v3069_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3069_mg : Scalar.QComplex := ((-93086214048272423631271 : Int)/10^30,(199828186185281579165 : Int)/10^30)
theorem v3069_mg_checked : Scalar.distance (sourceCoefficient 39 67 3 2) v3069_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3069_upper : Scalar.QComplex := ((999995471001187529922261245901 : Int)/10^30,(-3009647340322435870846889503 : Int)/10^30)
theorem v3069_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 67 5) 1) 14) v3069_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3069 : Material (39 : Basis) (67 : Basis) where
  plus := ![v3069_pa,v3069_pb,v3069_pg]
  minus := ![(Primitive.Addresses.material3069 1).one,v3069_mb,v3069_mg]
  upper := v3069_upper
  lower := (Primitive.Addresses.material3069 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3069_pa_checked.trans (by decide +kernel)
    · exact v3069_pb_checked.trans (by decide +kernel)
    · exact v3069_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 67 Primitive.Addresses.material3069
    · exact v3069_mb_checked.trans (by decide +kernel)
    · exact v3069_mg_checked.trans (by decide +kernel)
  upper_error := v3069_upper_checked
  lower_error := reuse_lower_error 39 67 Primitive.Addresses.material3069

def v3070_pa : Scalar.QComplex := ((999999111689287192901994395088 : Int)/10^30,(-1332899334727973192469659600 : Int)/10^30)
theorem v3070_pa_checked : Scalar.distance (sourceCoefficient 39 68 1 0) v3070_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3070_pb : Scalar.QComplex := ((-575116079663009896921528 : Int)/10^30,(-431477121937800778220483098 : Int)/10^30)
theorem v3070_pb_checked : Scalar.distance (sourceCoefficient 39 68 1 1) v3070_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3070_pg : Scalar.QComplex := ((-93086345505475094294894 : Int)/10^30,(124074838213513985524 : Int)/10^30)
theorem v3070_pg_checked : Scalar.distance (sourceCoefficient 39 68 1 2) v3070_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3070_mb : Scalar.QComplex := ((-947461188745146501061959 : Int)/10^30,(-431476464979874319655830466 : Int)/10^30)
theorem v3070_mb_checked : Scalar.distance (sourceCoefficient 39 68 3 1) v3070_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3070_mg : Scalar.QComplex := ((-93086203774177151462079 : Int)/10^30,(204404115732635842793 : Int)/10^30)
theorem v3070_mg_checked : Scalar.distance (sourceCoefficient 39 68 3 2) v3070_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3070_upper : Scalar.QComplex := ((999995321844746421647100021750 : Int)/10^30,(-3058805097095944296807213436 : Int)/10^30)
theorem v3070_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 68 5) 1) 14) v3070_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3070 : Material (39 : Basis) (68 : Basis) where
  plus := ![v3070_pa,v3070_pb,v3070_pg]
  minus := ![(Primitive.Addresses.material3070 1).one,v3070_mb,v3070_mg]
  upper := v3070_upper
  lower := (Primitive.Addresses.material3070 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3070_pa_checked.trans (by decide +kernel)
    · exact v3070_pb_checked.trans (by decide +kernel)
    · exact v3070_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 68 Primitive.Addresses.material3070
    · exact v3070_mb_checked.trans (by decide +kernel)
    · exact v3070_mg_checked.trans (by decide +kernel)
  upper_error := v3070_upper_checked
  lower_error := reuse_lower_error 39 68 Primitive.Addresses.material3070

def v3071_pa : Scalar.QComplex := ((999999082617448438112895961036 : Int)/10^30,(-1354534702963725583809631578 : Int)/10^30)
theorem v3071_pa_checked : Scalar.distance (sourceCoefficient 39 69 1 0) v3071_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3071_pb : Scalar.QComplex := ((-584451252354149052948270 : Int)/10^30,(-431477107902800984898293453 : Int)/10^30)
theorem v3071_pb_checked : Scalar.distance (sourceCoefficient 39 69 1 1) v3071_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3071_pg : Scalar.QComplex := ((-93086342638431454467603 : Int)/10^30,(126088797147389784270 : Int)/10^30)
theorem v3071_pg_checked : Scalar.distance (sourceCoefficient 39 69 1 2) v3071_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3071_mb : Scalar.QComplex := ((-956796345848801516997748 : Int)/10^30,(-431476442889046160322924696 : Int)/10^30)
theorem v3071_mb_checked : Scalar.distance (sourceCoefficient 39 69 3 1) v3071_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3071_mg : Scalar.QComplex := ((-93086199169178724574592 : Int)/10^30,(206418071442493153668 : Int)/10^30)
theorem v3071_mg_checked : Scalar.distance (sourceCoefficient 39 69 3 2) v3071_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3071_upper : Scalar.QComplex := ((999995255432268136312404098246 : Int)/10^30,(-3080440382933000855719216803 : Int)/10^30)
theorem v3071_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 69 5) 1) 14) v3071_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3071 : Material (39 : Basis) (69 : Basis) where
  plus := ![v3071_pa,v3071_pb,v3071_pg]
  minus := ![(Primitive.Addresses.material3071 1).one,v3071_mb,v3071_mg]
  upper := v3071_upper
  lower := (Primitive.Addresses.material3071 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3071_pa_checked.trans (by decide +kernel)
    · exact v3071_pb_checked.trans (by decide +kernel)
    · exact v3071_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 69 Primitive.Addresses.material3071
    · exact v3071_mb_checked.trans (by decide +kernel)
    · exact v3071_mg_checked.trans (by decide +kernel)
  upper_error := v3071_upper_checked
  lower_error := reuse_lower_error 39 69 Primitive.Addresses.material3071

def v3072_pa : Scalar.QComplex := ((999999063238482040000023960831 : Int)/10^30,(-1368766655934406674117095460 : Int)/10^30)
theorem v3072_pa_checked : Scalar.distance (sourceCoefficient 39 70 1 0) v3072_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3072_pb : Scalar.QComplex := ((-590592018502314901085315 : Int)/10^30,(-431477098523607789968610469 : Int)/10^30)
theorem v3072_pb_checked : Scalar.distance (sourceCoefficient 39 70 1 1) v3072_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3072_pg : Scalar.QComplex := ((-93086340724744251765342 : Int)/10^30,(127413598663135055686 : Int)/10^30)
theorem v3072_pg_checked : Scalar.distance (sourceCoefficient 39 70 1 2) v3072_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3072_mb : Scalar.QComplex := ((-962937101616658177251537 : Int)/10^30,(-431476428210651841668949862 : Int)/10^30)
theorem v3072_mb_checked : Scalar.distance (sourceCoefficient 39 70 3 1) v3072_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3072_mg : Scalar.QComplex := ((-93086196112248193182699 : Int)/10^30,(207742870813528407691 : Int)/10^30)
theorem v3072_mg_checked : Scalar.distance (sourceCoefficient 39 70 3 2) v3072_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3072_upper : Scalar.QComplex := ((999995211490270886185888267366 : Int)/10^30,(-3094672281260521841786579916 : Int)/10^30)
theorem v3072_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 70 5) 1) 14) v3072_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3072 : Material (39 : Basis) (70 : Basis) where
  plus := ![v3072_pa,v3072_pb,v3072_pg]
  minus := ![(Primitive.Addresses.material3072 1).one,v3072_mb,v3072_mg]
  upper := v3072_upper
  lower := (Primitive.Addresses.material3072 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3072_pa_checked.trans (by decide +kernel)
    · exact v3072_pb_checked.trans (by decide +kernel)
    · exact v3072_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 70 Primitive.Addresses.material3072
    · exact v3072_mb_checked.trans (by decide +kernel)
    · exact v3072_mg_checked.trans (by decide +kernel)
  upper_error := v3072_upper_checked
  lower_error := reuse_lower_error 39 70 Primitive.Addresses.material3072

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
