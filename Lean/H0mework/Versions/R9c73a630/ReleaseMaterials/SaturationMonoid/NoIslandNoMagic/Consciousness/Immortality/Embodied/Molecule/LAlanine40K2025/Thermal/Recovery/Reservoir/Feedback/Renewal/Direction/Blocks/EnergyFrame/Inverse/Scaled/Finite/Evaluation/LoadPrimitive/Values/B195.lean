import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B130

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3121_pa : Scalar.QComplex := ((999999323513828050027116137010 : Int)/10^30,(-1163173197020291096510406344 : Int)/10^30)
theorem v3121_pa_checked : Scalar.distance (sourceCoefficient 40 62 1 0) v3121_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3121_pb : Scalar.QComplex := ((-501883082182483848868052 : Int)/10^30,(-431477224502073589975867477 : Int)/10^30)
theorem v3121_pb_checked : Scalar.distance (sourceCoefficient 40 62 1 1) v3121_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3121_pg : Scalar.QComplex := ((-93086366428015284197143 : Int)/10^30,(108275639684049838227 : Int)/10^30)
theorem v3121_pg_checked : Scalar.distance (sourceCoefficient 40 62 1 2) v3121_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3121_mb : Scalar.QComplex := ((-874228307040960441508863 : Int)/10^30,(-431476630740887475970830475 : Int)/10^30)
theorem v3121_mb_checked : Scalar.distance (sourceCoefficient 40 62 3 1) v3121_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3121_mg : Scalar.QComplex := ((-93086238330706312386900 : Int)/10^30,(188604941141145234714 : Int)/10^30)
theorem v3121_mg_checked : Scalar.distance (sourceCoefficient 40 62 3 2) v3121_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3121_upper : Scalar.QComplex := ((999995826600888039525891299975 : Int)/10^30,(-2889079577765347830940066210 : Int)/10^30)
theorem v3121_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 62 5) 1) 14) v3121_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3121 : Material (40 : Basis) (62 : Basis) where
  plus := ![v3121_pa,v3121_pb,v3121_pg]
  minus := ![(Primitive.Addresses.material3121 1).one,v3121_mb,v3121_mg]
  upper := v3121_upper
  lower := (Primitive.Addresses.material3121 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3121_pa_checked.trans (by decide +kernel)
    · exact v3121_pb_checked.trans (by decide +kernel)
    · exact v3121_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 62 Primitive.Addresses.material3121
    · exact v3121_mb_checked.trans (by decide +kernel)
    · exact v3121_mg_checked.trans (by decide +kernel)
  upper_error := v3121_upper_checked
  lower_error := reuse_lower_error 40 62 Primitive.Addresses.material3121

def v3122_pa : Scalar.QComplex := ((999999294365346327193200784938 : Int)/10^30,(-1187968353713746507091799786 : Int)/10^30)
theorem v3122_pa_checked : Scalar.distance (sourceCoefficient 40 63 1 0) v3122_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3122_pb : Scalar.QComplex := ((-512581633685924814999292 : Int)/10^30,(-431477210978023332718309077 : Int)/10^30)
theorem v3122_pb_checked : Scalar.distance (sourceCoefficient 40 63 1 1) v3122_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3122_pg : Scalar.QComplex := ((-93086363612520247038386 : Int)/10^30,(110583732165678423515 : Int)/10^30)
theorem v3122_pg_checked : Scalar.distance (sourceCoefficient 40 63 1 2) v3122_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3122_mb : Scalar.QComplex := ((-884926842890195463550242 : Int)/10^30,(-431476607984474151738501231 : Int)/10^30)
theorem v3122_mb_checked : Scalar.distance (sourceCoefficient 40 63 3 1) v3122_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3122_mg : Scalar.QComplex := ((-93086233523432464546621 : Int)/10^30,(190913030333720092175 : Int)/10^30)
theorem v3122_mg_checked : Scalar.distance (sourceCoefficient 40 63 3 2) v3122_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3122_upper : Scalar.QComplex := ((999995754658258676071331488914 : Int)/10^30,(-2913874647221694866321088304 : Int)/10^30)
theorem v3122_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 63 5) 1) 14) v3122_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3122 : Material (40 : Basis) (63 : Basis) where
  plus := ![v3122_pa,v3122_pb,v3122_pg]
  minus := ![(Primitive.Addresses.material3122 1).one,v3122_mb,v3122_mg]
  upper := v3122_upper
  lower := (Primitive.Addresses.material3122 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3122_pa_checked.trans (by decide +kernel)
    · exact v3122_pb_checked.trans (by decide +kernel)
    · exact v3122_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 63 Primitive.Addresses.material3122
    · exact v3122_mb_checked.trans (by decide +kernel)
    · exact v3122_mg_checked.trans (by decide +kernel)
  upper_error := v3122_upper_checked
  lower_error := reuse_lower_error 40 63 Primitive.Addresses.material3122

def v3123_pa : Scalar.QComplex := ((999999251639089643200328355611 : Int)/10^30,(-1223405599410738022158634072 : Int)/10^30)
theorem v3123_pa_checked : Scalar.distance (sourceCoefficient 40 64 1 0) v3123_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3123_pb : Scalar.QComplex := ((-527872006569575606043610 : Int)/10^30,(-431477191035461437113305546 : Int)/10^30)
theorem v3123_pb_checked : Scalar.distance (sourceCoefficient 40 64 1 1) v3123_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3123_pg : Scalar.QComplex := ((-93086359472711006886006 : Int)/10^30,(113882458632855856868 : Int)/10^30)
theorem v3123_pg_checked : Scalar.distance (sourceCoefficient 40 64 1 2) v3123_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3123_mb : Scalar.QComplex := ((-900217192871008889187606 : Int)/10^30,(-431476574847016535900763778 : Int)/10^30)
theorem v3123_mb_checked : Scalar.distance (sourceCoefficient 40 64 3 1) v3123_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3123_mg : Scalar.QComplex := ((-93086226536972393785232 : Int)/10^30,(194211752000161978386 : Int)/10^30)
theorem v3123_mg_checked : Scalar.distance (sourceCoefficient 40 64 3 2) v3123_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3123_upper : Scalar.QComplex := ((999995650770594396628121145130 : Int)/10^30,(-2949311766397428726172235076 : Int)/10^30)
theorem v3123_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 64 5) 1) 14) v3123_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3123 : Material (40 : Basis) (64 : Basis) where
  plus := ![v3123_pa,v3123_pb,v3123_pg]
  minus := ![(Primitive.Addresses.material3123 1).one,v3123_mb,v3123_mg]
  upper := v3123_upper
  lower := (Primitive.Addresses.material3123 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3123_pa_checked.trans (by decide +kernel)
    · exact v3123_pb_checked.trans (by decide +kernel)
    · exact v3123_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 64 Primitive.Addresses.material3123
    · exact v3123_mb_checked.trans (by decide +kernel)
    · exact v3123_mg_checked.trans (by decide +kernel)
  upper_error := v3123_upper_checked
  lower_error := reuse_lower_error 40 64 Primitive.Addresses.material3123

def v3124_pa : Scalar.QComplex := ((999999206990528376529342529710 : Int)/10^30,(-1259372190570730059585774019 : Int)/10^30)
theorem v3124_pa_checked : Scalar.distance (sourceCoefficient 40 65 1 0) v3124_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3124_pb : Scalar.QComplex := ((-543390779749061698927885 : Int)/10^30,(-431477170056271906466848593 : Int)/10^30)
theorem v3124_pb_checked : Scalar.distance (sourceCoefficient 40 65 1 1) v3124_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3124_pg : Scalar.QComplex := ((-93086355131611145603585 : Int)/10^30,(117230459939207142245 : Int)/10^30)
theorem v3124_pg_checked : Scalar.distance (sourceCoefficient 40 65 1 2) v3124_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3124_mb : Scalar.QComplex := ((-915735942168050787051025 : Int)/10^30,(-431476540475832502467013827 : Int)/10^30)
theorem v3124_mb_checked : Scalar.distance (sourceCoefficient 40 65 3 1) v3124_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3124_mg : Scalar.QComplex := ((-93086219306699809892838 : Int)/10^30,(197559748313725701784 : Int)/10^30)
theorem v3124_mg_checked : Scalar.distance (sourceCoefficient 40 65 3 2) v3124_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3124_upper : Scalar.QComplex := ((999995544047026150260039289778 : Int)/10^30,(-2985278226930041902937546665 : Int)/10^30)
theorem v3124_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 65 5) 1) 14) v3124_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3124 : Material (40 : Basis) (65 : Basis) where
  plus := ![v3124_pa,v3124_pb,v3124_pg]
  minus := ![(Primitive.Addresses.material3124 1).one,v3124_mb,v3124_mg]
  upper := v3124_upper
  lower := (Primitive.Addresses.material3124 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3124_pa_checked.trans (by decide +kernel)
    · exact v3124_pb_checked.trans (by decide +kernel)
    · exact v3124_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 65 Primitive.Addresses.material3124
    · exact v3124_mb_checked.trans (by decide +kernel)
    · exact v3124_mg_checked.trans (by decide +kernel)
  upper_error := v3124_upper_checked
  lower_error := reuse_lower_error 40 65 Primitive.Addresses.material3124

def v3125_pa : Scalar.QComplex := ((999999184686575077291160699815 : Int)/10^30,(-1276959742947849088301316817 : Int)/10^30)
theorem v3125_pa_checked : Scalar.distance (sourceCoefficient 40 66 1 0) v3125_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3125_pb : Scalar.QComplex := ((-550979411937837404093382 : Int)/10^30,(-431477159526577121234735754 : Int)/10^30)
theorem v3125_pb_checked : Scalar.distance (sourceCoefficient 40 66 1 1) v3125_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3125_pg : Scalar.QComplex := ((-93086352957681749916040 : Int)/10^30,(118867622259162255612 : Int)/10^30)
theorem v3125_pg_checked : Scalar.distance (sourceCoefficient 40 66 1 2) v3125_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3125_mb : Scalar.QComplex := ((-923324562444579550904365 : Int)/10^30,(-431476523397493838314405025 : Int)/10^30)
theorem v3125_mb_checked : Scalar.distance (sourceCoefficient 40 66 3 1) v3125_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3125_mg : Scalar.QComplex := ((-93086215719973876591015 : Int)/10^30,(199196908148087303083 : Int)/10^30)
theorem v3125_mg_checked : Scalar.distance (sourceCoefficient 40 66 3 2) v3125_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3125_upper : Scalar.QComplex := ((999995491388586197520900322440 : Int)/10^30,(-3002865714617967649315904690 : Int)/10^30)
theorem v3125_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 66 5) 1) 14) v3125_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3125 : Material (40 : Basis) (66 : Basis) where
  plus := ![v3125_pa,v3125_pb,v3125_pg]
  minus := ![(Primitive.Addresses.material3125 1).one,v3125_mb,v3125_mg]
  upper := v3125_upper
  lower := (Primitive.Addresses.material3125 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3125_pa_checked.trans (by decide +kernel)
    · exact v3125_pb_checked.trans (by decide +kernel)
    · exact v3125_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 66 Primitive.Addresses.material3125
    · exact v3125_mb_checked.trans (by decide +kernel)
    · exact v3125_mg_checked.trans (by decide +kernel)
  upper_error := v3125_upper_checked
  lower_error := reuse_lower_error 40 66 Primitive.Addresses.material3125

def v3126_pa : Scalar.QComplex := ((999999146558725560020758335808 : Int)/10^30,(-1306476873319214007430241193 : Int)/10^30)
theorem v3126_pa_checked : Scalar.distance (sourceCoefficient 40 67 1 0) v3126_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3126_pb : Scalar.QComplex := ((-563715387774395390926235 : Int)/10^30,(-431477141454675317379956091 : Int)/10^30)
theorem v3126_pb_checked : Scalar.distance (sourceCoefficient 40 67 1 1) v3126_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3126_pg : Scalar.QComplex := ((-93086349233684116831787 : Int)/10^30,(121615266287011889149 : Int)/10^30)
theorem v3126_pg_checked : Scalar.distance (sourceCoefficient 40 67 1 2) v3126_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3126_mb : Scalar.QComplex := ((-936060517943714342452595 : Int)/10^30,(-431476494335025223563434679 : Int)/10^30)
theorem v3126_mb_checked : Scalar.distance (sourceCoefficient 40 67 3 1) v3126_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3126_mg : Scalar.QComplex := ((-93086209624884583380266 : Int)/10^30,(201944547939221256792 : Int)/10^30)
theorem v3126_mg_checked : Scalar.distance (sourceCoefficient 40 67 3 2) v3126_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3126_upper : Scalar.QComplex := ((999995402316904219377365997822 : Int)/10^30,(-3032382735221824870676350784 : Int)/10^30)
theorem v3126_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 67 5) 1) 14) v3126_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3126 : Material (40 : Basis) (67 : Basis) where
  plus := ![v3126_pa,v3126_pb,v3126_pg]
  minus := ![(Primitive.Addresses.material3126 1).one,v3126_mb,v3126_mg]
  upper := v3126_upper
  lower := (Primitive.Addresses.material3126 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3126_pa_checked.trans (by decide +kernel)
    · exact v3126_pb_checked.trans (by decide +kernel)
    · exact v3126_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 67 Primitive.Addresses.material3126
    · exact v3126_mb_checked.trans (by decide +kernel)
    · exact v3126_mg_checked.trans (by decide +kernel)
  upper_error := v3126_upper_checked
  lower_error := reuse_lower_error 40 67 Primitive.Addresses.material3126

def v3127_pa : Scalar.QComplex := ((999999081126704952766755244551 : Int)/10^30,(-1355634812833579506018278459 : Int)/10^30)
theorem v3127_pa_checked : Scalar.distance (sourceCoefficient 40 68 1 0) v3127_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3127_pb : Scalar.QComplex := ((-584925929061995162702409 : Int)/10^30,(-431477110245166004579075097 : Int)/10^30)
theorem v3127_pb_checked : Scalar.distance (sourceCoefficient 40 68 1 1) v3127_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3127_pg : Scalar.QComplex := ((-93086342821716934105776 : Int)/10^30,(126191202882207051498 : Int)/10^30)
theorem v3127_pg_checked : Scalar.distance (sourceCoefficient 40 68 1 2) v3127_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3127_mb : Scalar.QComplex := ((-957271024401259310403768 : Int)/10^30,(-431476444821785687608274195 : Int)/10^30)
theorem v3127_mb_checked : Scalar.distance (sourceCoefficient 40 68 3 1) v3127_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3127_mg : Scalar.QComplex := ((-93086199264092599002986 : Int)/10^30,(206520477297347199705 : Int)/10^30)
theorem v3127_mg_checked : Scalar.distance (sourceCoefficient 40 68 3 2) v3127_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3127_upper : Scalar.QComplex := ((999995252042837037073489093998 : Int)/10^30,(-3081540488591482338248651421 : Int)/10^30)
theorem v3127_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 68 5) 1) 14) v3127_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3127 : Material (40 : Basis) (68 : Basis) where
  plus := ![v3127_pa,v3127_pb,v3127_pg]
  minus := ![(Primitive.Addresses.material3127 1).one,v3127_mb,v3127_mg]
  upper := v3127_upper
  lower := (Primitive.Addresses.material3127 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3127_pa_checked.trans (by decide +kernel)
    · exact v3127_pb_checked.trans (by decide +kernel)
    · exact v3127_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 68 Primitive.Addresses.material3127
    · exact v3127_mb_checked.trans (by decide +kernel)
    · exact v3127_mg_checked.trans (by decide +kernel)
  upper_error := v3127_upper_checked
  lower_error := reuse_lower_error 40 68 Primitive.Addresses.material3127

def v3128_pa : Scalar.QComplex := ((999999051562975320255531079416 : Int)/10^30,(-1377270180402777454425361528 : Int)/10^30)
theorem v3128_pa_checked : Scalar.distance (sourceCoefficient 40 69 1 0) v3128_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3128_pb : Scalar.QComplex := ((-594261101561398818351322 : Int)/10^30,(-431477096068672977551426416 : Int)/10^30)
theorem v3128_pb_checked : Scalar.distance (sourceCoefficient 40 69 1 1) v3128_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3128_pg : Scalar.QComplex := ((-93086339916516323381739 : Int)/10^30,(128205161764376873101 : Int)/10^30)
theorem v3128_pg_checked : Scalar.distance (sourceCoefficient 40 69 1 2) v3128_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3128_mb : Scalar.QComplex := ((-966606181191076609284488 : Int)/10^30,(-431476422589464512713408237 : Int)/10^30)
theorem v3128_mb_checked : Scalar.distance (sourceCoefficient 40 69 3 1) v3128_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3128_mg : Scalar.QComplex := ((-93086194620937260046268 : Int)/10^30,(208534432922570805333 : Int)/10^30)
theorem v3128_mg_checked : Scalar.distance (sourceCoefficient 40 69 3 2) v3128_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3128_upper : Scalar.QComplex := ((999995185138469757042847400550 : Int)/10^30,(-3103175772913026416025764088 : Int)/10^30)
theorem v3128_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 69 5) 1) 14) v3128_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3128 : Material (40 : Basis) (69 : Basis) where
  plus := ![v3128_pa,v3128_pb,v3128_pg]
  minus := ![(Primitive.Addresses.material3128 1).one,v3128_mb,v3128_mg]
  upper := v3128_upper
  lower := (Primitive.Addresses.material3128 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3128_pa_checked.trans (by decide +kernel)
    · exact v3128_pb_checked.trans (by decide +kernel)
    · exact v3128_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 69 Primitive.Addresses.material3128
    · exact v3128_mb_checked.trans (by decide +kernel)
    · exact v3128_mg_checked.trans (by decide +kernel)
  upper_error := v3128_upper_checked
  lower_error := reuse_lower_error 40 69 Primitive.Addresses.material3128

def v3129_pa : Scalar.QComplex := ((999999031860438379652296545162 : Int)/10^30,(-1391502132929189811549370469 : Int)/10^30)
theorem v3129_pa_checked : Scalar.distance (sourceCoefficient 40 70 1 0) v3129_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3129_pb : Scalar.QComplex := ((-600401867581770022529512 : Int)/10^30,(-431477086596404175034528118 : Int)/10^30)
theorem v3129_pb_checked : Scalar.distance (sourceCoefficient 40 70 1 1) v3129_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3129_pg : Scalar.QComplex := ((-93086337977729098866976 : Int)/10^30,(129529963245659319788 : Int)/10^30)
theorem v3129_pg_checked : Scalar.distance (sourceCoefficient 40 70 1 2) v3129_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3129_mb : Scalar.QComplex := ((-972746936750818615785195 : Int)/10^30,(-431476407817994731409542639 : Int)/10^30)
theorem v3129_mb_checked : Scalar.distance (sourceCoefficient 40 70 3 1) v3129_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3129_mg : Scalar.QComplex := ((-93086191538906745927623 : Int)/10^30,(209859232237483059098 : Int)/10^30)
theorem v3129_mg_checked : Scalar.distance (sourceCoefficient 40 70 3 2) v3129_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3129_upper : Scalar.QComplex := ((999995140872903213113812539094 : Int)/10^30,(-3117407670237825928347710287 : Int)/10^30)
theorem v3129_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 70 5) 1) 14) v3129_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3129 : Material (40 : Basis) (70 : Basis) where
  plus := ![v3129_pa,v3129_pb,v3129_pg]
  minus := ![(Primitive.Addresses.material3129 1).one,v3129_mb,v3129_mg]
  upper := v3129_upper
  lower := (Primitive.Addresses.material3129 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3129_pa_checked.trans (by decide +kernel)
    · exact v3129_pb_checked.trans (by decide +kernel)
    · exact v3129_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 70 Primitive.Addresses.material3129
    · exact v3129_mb_checked.trans (by decide +kernel)
    · exact v3129_mg_checked.trans (by decide +kernel)
  upper_error := v3129_upper_checked
  lower_error := reuse_lower_error 40 70 Primitive.Addresses.material3129

def v3130_pa : Scalar.QComplex := ((999998997761862216850426167662 : Int)/10^30,(-1415794925504754844835451577 : Int)/10^30)
theorem v3130_pa_checked : Scalar.distance (sourceCoefficient 40 71 1 0) v3130_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3130_pb : Scalar.QComplex := ((-610883658653389654691752 : Int)/10^30,(-431477070158800761461436709 : Int)/10^30)
theorem v3130_pb_checked : Scalar.distance (sourceCoefficient 40 71 1 1) v3130_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3130_pg : Scalar.QComplex := ((-93086334617557563757350 : Int)/10^30,(131791292271634935407 : Int)/10^30)
theorem v3130_pg_checked : Scalar.distance (sourceCoefficient 40 71 1 2) v3130_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3130_mb : Scalar.QComplex := ((-983228709734676966728460 : Int)/10^30,(-431476382335083825845040477 : Int)/10^30)
theorem v3130_mb_checked : Scalar.distance (sourceCoefficient 40 71 3 1) v3130_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3130_mg : Scalar.QComplex := ((-93086186227311359025082 : Int)/10^30,(212120557521785832213 : Int)/10^30)
theorem v3130_mg_checked : Scalar.distance (sourceCoefficient 40 71 3 2) v3130_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3130_upper : Scalar.QComplex := ((999995064847221675637508755165 : Int)/10^30,(-3141700367781080993871462870 : Int)/10^30)
theorem v3130_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 71 5) 1) 14) v3130_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3130 : Material (40 : Basis) (71 : Basis) where
  plus := ![v3130_pa,v3130_pb,v3130_pg]
  minus := ![(Primitive.Addresses.material3130 1).one,v3130_mb,v3130_mg]
  upper := v3130_upper
  lower := (Primitive.Addresses.material3130 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3130_pa_checked.trans (by decide +kernel)
    · exact v3130_pb_checked.trans (by decide +kernel)
    · exact v3130_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 71 Primitive.Addresses.material3130
    · exact v3130_mb_checked.trans (by decide +kernel)
    · exact v3130_mg_checked.trans (by decide +kernel)
  upper_error := v3130_upper_checked
  lower_error := reuse_lower_error 40 71 Primitive.Addresses.material3130

def v3131_pa : Scalar.QComplex := ((999998960090296182313871885411 : Int)/10^30,(-1442157524760447298218724260 : Int)/10^30)
theorem v3131_pa_checked : Scalar.distance (sourceCoefficient 40 72 1 0) v3131_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3131_pb : Scalar.QComplex := ((-622258524304412124946109 : Int)/10^30,(-431477051936539256391197206 : Int)/10^30)
theorem v3131_pb_checked : Scalar.distance (sourceCoefficient 40 72 1 1) v3131_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3131_pg : Scalar.QComplex := ((-93086330898577621639808 : Int)/10^30,(134245292160706656538 : Int)/10^30)
theorem v3131_pg_checked : Scalar.distance (sourceCoefficient 40 72 1 2) v3131_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3131_mb : Scalar.QComplex := ((-994603555425326119382190 : Int)/10^30,(-431476354296832353854435044 : Int)/10^30)
theorem v3131_mb_checked : Scalar.distance (sourceCoefficient 40 72 3 1) v3131_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3131_mg : Scalar.QComplex := ((-93086180390641421437001 : Int)/10^30,(214574553287809047899 : Int)/10^30)
theorem v3131_mg_checked : Scalar.distance (sourceCoefficient 40 72 3 2) v3131_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3131_upper : Scalar.QComplex := ((999994981676257029470526569048 : Int)/10^30,(-3168062862755073186509738795 : Int)/10^30)
theorem v3131_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 72 5) 1) 14) v3131_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3131 : Material (40 : Basis) (72 : Basis) where
  plus := ![v3131_pa,v3131_pb,v3131_pg]
  minus := ![(Primitive.Addresses.material3131 1).one,v3131_mb,v3131_mg]
  upper := v3131_upper
  lower := (Primitive.Addresses.material3131 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3131_pa_checked.trans (by decide +kernel)
    · exact v3131_pb_checked.trans (by decide +kernel)
    · exact v3131_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 72 Primitive.Addresses.material3131
    · exact v3131_mb_checked.trans (by decide +kernel)
    · exact v3131_mg_checked.trans (by decide +kernel)
  upper_error := v3131_upper_checked
  lower_error := reuse_lower_error 40 72 Primitive.Addresses.material3131

def v3132_pa : Scalar.QComplex := ((999998946417775130547128466367 : Int)/10^30,(-1451607157499370138112214931 : Int)/10^30)
theorem v3132_pa_checked : Scalar.distance (sourceCoefficient 40 73 1 0) v3132_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3132_pb : Scalar.QComplex := ((-626335827161272798203258 : Int)/10^30,(-431477045307452800381129231 : Int)/10^30)
theorem v3132_pb_checked : Scalar.distance (sourceCoefficient 40 73 1 1) v3132_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3132_pg : Scalar.QComplex := ((-93086329547139054499555 : Int)/10^30,(135124924601190850268 : Int)/10^30)
theorem v3132_pg_checked : Scalar.distance (sourceCoefficient 40 73 1 2) v3132_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3132_mb : Scalar.QComplex := ((-998680851043417548518183 : Int)/10^30,(-431476344149219635589282785 : Int)/10^30)
theorem v3132_mb_checked : Scalar.distance (sourceCoefficient 40 73 3 1) v3132_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3132_mg : Scalar.QComplex := ((-93086178280120178535692 : Int)/10^30,(215454184234535265939 : Int)/10^30)
theorem v3132_mg_checked : Scalar.distance (sourceCoefficient 40 73 3 2) v3132_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3132_upper : Scalar.QComplex := ((999994951694547497922477279000 : Int)/10^30,(-3177512457822347119685902418 : Int)/10^30)
theorem v3132_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 73 5) 1) 14) v3132_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3132 : Material (40 : Basis) (73 : Basis) where
  plus := ![v3132_pa,v3132_pb,v3132_pg]
  minus := ![(Primitive.Addresses.material3132 1).one,v3132_mb,v3132_mg]
  upper := v3132_upper
  lower := (Primitive.Addresses.material3132 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3132_pa_checked.trans (by decide +kernel)
    · exact v3132_pb_checked.trans (by decide +kernel)
    · exact v3132_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 73 Primitive.Addresses.material3132
    · exact v3132_mb_checked.trans (by decide +kernel)
    · exact v3132_mg_checked.trans (by decide +kernel)
  upper_error := v3132_upper_checked
  lower_error := reuse_lower_error 40 73 Primitive.Addresses.material3132

def v3133_pa : Scalar.QComplex := ((999998930926056277498210053132 : Int)/10^30,(-1462240316954058832214753147 : Int)/10^30)
theorem v3133_pa_checked : Scalar.distance (sourceCoefficient 40 74 1 0) v3133_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3133_pb : Scalar.QComplex := ((-630923794995775590665403 : Int)/10^30,(-431477037786674873329177552 : Int)/10^30)
theorem v3133_pb_checked : Scalar.distance (sourceCoefficient 40 74 1 1) v3133_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3133_pg : Scalar.QComplex := ((-93086328014842962191734 : Int)/10^30,(136114727297221769480 : Int)/10^30)
theorem v3133_pg_checked : Scalar.distance (sourceCoefficient 40 74 1 2) v3133_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3133_mb : Scalar.QComplex := ((-1003268810679517607924477 : Int)/10^30,(-431476332669234902091396477 : Int)/10^30)
theorem v3133_mb_checked : Scalar.distance (sourceCoefficient 40 74 3 1) v3133_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3133_mg : Scalar.QComplex := ((-93086175893669509155629 : Int)/10^30,(216443985239714889594 : Int)/10^30)
theorem v3133_mg_checked : Scalar.distance (sourceCoefficient 40 74 3 2) v3133_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3133_upper : Scalar.QComplex := ((999994917850983131866751637388 : Int)/10^30,(-3188145574702892522074313810 : Int)/10^30)
theorem v3133_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 74 5) 1) 14) v3133_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3133 : Material (40 : Basis) (74 : Basis) where
  plus := ![v3133_pa,v3133_pb,v3133_pg]
  minus := ![(Primitive.Addresses.material3133 1).one,v3133_mb,v3133_mg]
  upper := v3133_upper
  lower := (Primitive.Addresses.material3133 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3133_pa_checked.trans (by decide +kernel)
    · exact v3133_pb_checked.trans (by decide +kernel)
    · exact v3133_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 74 Primitive.Addresses.material3133
    · exact v3133_mb_checked.trans (by decide +kernel)
    · exact v3133_mg_checked.trans (by decide +kernel)
  upper_error := v3133_upper_checked
  lower_error := reuse_lower_error 40 74 Primitive.Addresses.material3133

def v3134_pa : Scalar.QComplex := ((999998909153033534032141932568 : Int)/10^30,(-1477055429895855827197904813 : Int)/10^30)
theorem v3134_pa_checked : Scalar.distance (sourceCoefficient 40 75 1 0) v3134_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3134_pb : Scalar.QComplex := ((-637316181114873659780474 : Int)/10^30,(-431477027199572753356991750 : Int)/10^30)
theorem v3134_pb_checked : Scalar.distance (sourceCoefficient 40 75 1 1) v3134_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3134_pg : Scalar.QComplex := ((-93086325859432286938329 : Int)/10^30,(137493813044438345098 : Int)/10^30)
theorem v3134_pg_checked : Scalar.distance (sourceCoefficient 40 75 1 2) v3134_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3134_mb : Scalar.QComplex := ((-1009661185282245874264263 : Int)/10^30,(-431476316565795405782916103 : Int)/10^30)
theorem v3134_mb_checked : Scalar.distance (sourceCoefficient 40 75 3 1) v3134_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3134_mg : Scalar.QComplex := ((-93086172548170748328580 : Int)/10^30,(217823068613412477540 : Int)/10^30)
theorem v3134_mg_checked : Scalar.distance (sourceCoefficient 40 75 3 2) v3134_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3134_upper : Scalar.QComplex := ((999994870508451895766006371203 : Int)/10^30,(-3202960628001057073637951421 : Int)/10^30)
theorem v3134_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 75 5) 1) 14) v3134_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3134 : Material (40 : Basis) (75 : Basis) where
  plus := ![v3134_pa,v3134_pb,v3134_pg]
  minus := ![(Primitive.Addresses.material3134 1).one,v3134_mb,v3134_mg]
  upper := v3134_upper
  lower := (Primitive.Addresses.material3134 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3134_pa_checked.trans (by decide +kernel)
    · exact v3134_pb_checked.trans (by decide +kernel)
    · exact v3134_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 75 Primitive.Addresses.material3134
    · exact v3134_mb_checked.trans (by decide +kernel)
    · exact v3134_mg_checked.trans (by decide +kernel)
  upper_error := v3134_upper_checked
  lower_error := reuse_lower_error 40 75 Primitive.Addresses.material3134

def v3135_pa : Scalar.QComplex := ((999998890715706667627425356789 : Int)/10^30,(-1489485601190257131041920415 : Int)/10^30)
theorem v3135_pa_checked : Scalar.distance (sourceCoefficient 40 76 1 0) v3135_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3135_pb : Scalar.QComplex := ((-642679518796551258712964 : Int)/10^30,(-431477018219368360107029990 : Int)/10^30)
theorem v3135_pb_checked : Scalar.distance (sourceCoefficient 40 76 1 1) v3135_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3135_pg : Scalar.QComplex := ((-93086324032610691831957 : Int)/10^30,(138650893117562208689 : Int)/10^30)
theorem v3135_pg_checked : Scalar.distance (sourceCoefficient 40 76 1 2) v3135_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3135_mb : Scalar.QComplex := ((-1015024513217395799684261 : Int)/10^30,(-431476302957275492747909057 : Int)/10^30)
theorem v3135_mb_checked : Scalar.distance (sourceCoefficient 40 76 3 1) v3135_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3135_mg : Scalar.QComplex := ((-93086169722841843277453 : Int)/10^30,(218980146679237789149 : Int)/10^30)
theorem v3135_mg_checked : Scalar.distance (sourceCoefficient 40 76 3 2) v3135_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3135_upper : Scalar.QComplex := ((999994830617804491788266556610 : Int)/10^30,(-3215390748961024834774422369 : Int)/10^30)
theorem v3135_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 76 5) 1) 14) v3135_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3135 : Material (40 : Basis) (76 : Basis) where
  plus := ![v3135_pa,v3135_pb,v3135_pg]
  minus := ![(Primitive.Addresses.material3135 1).one,v3135_mb,v3135_mg]
  upper := v3135_upper
  lower := (Primitive.Addresses.material3135 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3135_pa_checked.trans (by decide +kernel)
    · exact v3135_pb_checked.trans (by decide +kernel)
    · exact v3135_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 76 Primitive.Addresses.material3135
    · exact v3135_mb_checked.trans (by decide +kernel)
    · exact v3135_mg_checked.trans (by decide +kernel)
  upper_error := v3135_upper_checked
  lower_error := reuse_lower_error 40 76 Primitive.Addresses.material3135

def v3136_pa : Scalar.QComplex := ((999998886425283180917062019626 : Int)/10^30,(-1492363291423879783062928679 : Int)/10^30)
theorem v3136_pa_checked : Scalar.distance (sourceCoefficient 40 77 1 0) v3136_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3136_pb : Scalar.QComplex := ((-643921177016436121969780 : Int)/10^30,(-431477016127703310070562729 : Int)/10^30)
theorem v3136_pb_checked : Scalar.distance (sourceCoefficient 40 77 1 1) v3136_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3136_pg : Scalar.QComplex := ((-93086323607293966079858 : Int)/10^30,(138918766981556227823 : Int)/10^30)
theorem v3136_pg_checked : Scalar.distance (sourceCoefficient 40 77 1 2) v3136_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3136_mb : Scalar.QComplex := ((-1016266169169941828009281 : Int)/10^30,(-431476299794116099983590336 : Int)/10^30)
theorem v3136_mb_checked : Scalar.distance (sourceCoefficient 40 77 3 1) v3136_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3136_mg : Scalar.QComplex := ((-93086169066362195854347 : Int)/10^30,(219248020076460947508 : Int)/10^30)
theorem v3136_mg_checked : Scalar.distance (sourceCoefficient 40 77 3 2) v3136_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3136_upper : Scalar.QComplex := ((999994821360755113945690411002 : Int)/10^30,(-3218268427503784207171327608 : Int)/10^30)
theorem v3136_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 40 77 5) 1) 14) v3136_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3136 : Material (40 : Basis) (77 : Basis) where
  plus := ![v3136_pa,v3136_pb,v3136_pg]
  minus := ![(Primitive.Addresses.material3136 1).one,v3136_mb,v3136_mg]
  upper := v3136_upper
  lower := (Primitive.Addresses.material3136 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3136_pa_checked.trans (by decide +kernel)
    · exact v3136_pb_checked.trans (by decide +kernel)
    · exact v3136_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 40 77 Primitive.Addresses.material3136
    · exact v3136_mb_checked.trans (by decide +kernel)
    · exact v3136_mg_checked.trans (by decide +kernel)
  upper_error := v3136_upper_checked
  lower_error := reuse_lower_error 40 77 Primitive.Addresses.material3136

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
