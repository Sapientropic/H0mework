import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B166

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3985_pa : Scalar.QComplex := ((999998693006226255913943946669 : Int)/10^30,(-1616782557815195972155365401 : Int)/10^30)
theorem v3985_pa_checked : Scalar.distance (sourceCoefficient 58 71 1 0) v3985_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3985_pb : Scalar.QComplex := ((-697605319239849558294888 : Int)/10^30,(-431476950380225130687250273 : Int)/10^30)
theorem v3985_pb_checked : Scalar.distance (sourceCoefficient 58 71 1 1) v3985_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3985_pg : Scalar.QComplex := ((-93086307512809166148171 : Int)/10^30,(150500515061367627331 : Int)/10^30)
theorem v3985_pg_checked : Scalar.distance (sourceCoefficient 58 71 1 2) v3985_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3985_mb : Scalar.QComplex := ((-1069950234667183115739369 : Int)/10^30,(-431476187719665506596570606 : Int)/10^30)
theorem v3985_mb_checked : Scalar.distance (sourceCoefficient 58 71 3 1) v3985_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3985_mg : Scalar.QComplex := ((-93086142977356418327642 : Int)/10^30,(230829749955042711212 : Int)/10^30)
theorem v3985_mg_checked : Scalar.distance (sourceCoefficient 58 71 3 2) v3985_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3985_upper : Scalar.QComplex := ((999994413205619700171557576468 : Int)/10^30,(-3342687174763473007318880267 : Int)/10^30)
theorem v3985_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 71 5) 1) 14) v3985_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3985 : Material (58 : Basis) (71 : Basis) where
  plus := ![v3985_pa,v3985_pb,v3985_pg]
  minus := ![(Primitive.Addresses.material3985 1).one,v3985_mb,v3985_mg]
  upper := v3985_upper
  lower := (Primitive.Addresses.material3985 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3985_pa_checked.trans (by decide +kernel)
    · exact v3985_pb_checked.trans (by decide +kernel)
    · exact v3985_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 71 Primitive.Addresses.material3985
    · exact v3985_mb_checked.trans (by decide +kernel)
    · exact v3985_mg_checked.trans (by decide +kernel)
  upper_error := v3985_upper_checked
  lower_error := reuse_lower_error 58 71 Primitive.Addresses.material3985

def v3986_pa : Scalar.QComplex := ((999998650036098512024850861695 : Int)/10^30,(-1643145148966887519515185528 : Int)/10^30)
theorem v3986_pa_checked : Scalar.distance (sourceCoefficient 58 72 1 0) v3986_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3986_pb : Scalar.QComplex := ((-708980182559742603474377 : Int)/10^30,(-431476930633823481477859409 : Int)/10^30)
theorem v3986_pb_checked : Scalar.distance (sourceCoefficient 58 72 1 1) v3986_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3986_pg : Scalar.QComplex := ((-93086303382809067762321 : Int)/10^30,(152954514321795595332 : Int)/10^30)
theorem v3986_pg_checked : Scalar.distance (sourceCoefficient 58 72 1 2) v3986_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3986_mb : Scalar.QComplex := ((-1081325076711439411636045 : Int)/10^30,(-431476158157276469633549789 : Int)/10^30)
theorem v3986_mb_checked : Scalar.distance (sourceCoefficient 58 72 3 1) v3986_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3986_mg : Scalar.QComplex := ((-93086136729667020004087 : Int)/10^30,(233283744737730524642 : Int)/10^30)
theorem v3986_mg_checked : Scalar.distance (sourceCoefficient 58 72 3 2) v3986_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3986_upper : Scalar.QComplex := ((999994324736115223007664465009 : Int)/10^30,(-3369049652488639535312000955 : Int)/10^30)
theorem v3986_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 72 5) 1) 14) v3986_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3986 : Material (58 : Basis) (72 : Basis) where
  plus := ![v3986_pa,v3986_pb,v3986_pg]
  minus := ![(Primitive.Addresses.material3986 1).one,v3986_mb,v3986_mg]
  upper := v3986_upper
  lower := (Primitive.Addresses.material3986 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3986_pa_checked.trans (by decide +kernel)
    · exact v3986_pb_checked.trans (by decide +kernel)
    · exact v3986_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 72 Primitive.Addresses.material3986
    · exact v3986_mb_checked.trans (by decide +kernel)
    · exact v3986_mg_checked.trans (by decide +kernel)
  upper_error := v3986_upper_checked
  lower_error := reuse_lower_error 58 72 Primitive.Addresses.material3986

def v3987_pa : Scalar.QComplex := ((999998634464316252280249441936 : Int)/10^30,(-1652594778766935325562141110 : Int)/10^30)
theorem v3987_pa_checked : Scalar.distance (sourceCoefficient 58 73 1 0) v3987_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3987_pb : Scalar.QComplex := ((-713057484571230955446331 : Int)/10^30,(-431476923458411360946593945 : Int)/10^30)
theorem v3987_pb_checked : Scalar.distance (sourceCoefficient 58 73 1 1) v3987_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3987_pg : Scalar.QComplex := ((-93086301884040964683125 : Int)/10^30,(153834146534305304484 : Int)/10^30)
theorem v3987_pg_checked : Scalar.distance (sourceCoefficient 58 73 1 2) v3987_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3987_mb : Scalar.QComplex := ((-1085402371012704391370330 : Int)/10^30,(-431476147463339019787452371 : Int)/10^30)
theorem v3987_mb_checked : Scalar.distance (sourceCoefficient 58 73 3 1) v3987_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3987_mg : Scalar.QComplex := ((-93086134471816492753067 : Int)/10^30,(234163375329343588950 : Int)/10^30)
theorem v3987_mg_checked : Scalar.distance (sourceCoefficient 58 73 3 2) v3987_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3987_upper : Scalar.QComplex := ((999994292855152384439919322366 : Int)/10^30,(-3378499241339090266411841879 : Int)/10^30)
theorem v3987_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 73 5) 1) 14) v3987_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3987 : Material (58 : Basis) (73 : Basis) where
  plus := ![v3987_pa,v3987_pb,v3987_pg]
  minus := ![(Primitive.Addresses.material3987 1).one,v3987_mb,v3987_mg]
  upper := v3987_upper
  lower := (Primitive.Addresses.material3987 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3987_pa_checked.trans (by decide +kernel)
    · exact v3987_pb_checked.trans (by decide +kernel)
    · exact v3987_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 73 Primitive.Addresses.material3987
    · exact v3987_mb_checked.trans (by decide +kernel)
    · exact v3987_mg_checked.trans (by decide +kernel)
  upper_error := v3987_upper_checked
  lower_error := reuse_lower_error 58 73 Primitive.Addresses.material3987

def v3988_pa : Scalar.QComplex := ((999998616835461723368409573069 : Int)/10^30,(-1663227934893207364219445289 : Int)/10^30)
theorem v3988_pa_checked : Scalar.distance (sourceCoefficient 58 74 1 0) v3988_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3988_pb : Scalar.QComplex := ((-717645451448309128172697 : Int)/10^30,(-431476915322882781194486270 : Int)/10^30)
theorem v3988_pb_checked : Scalar.distance (sourceCoefficient 58 74 1 1) v3988_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3988_pg : Scalar.QComplex := ((-93086300185962932601384 : Int)/10^30,(154823948972144207246 : Int)/10^30)
theorem v3988_pg_checked : Scalar.distance (sourceCoefficient 58 74 1 2) v3988_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3988_mb : Scalar.QComplex := ((-1089990329160878061595147 : Int)/10^30,(-431476135368604688703499588 : Int)/10^30)
theorem v3988_mb_checked : Scalar.distance (sourceCoefficient 58 74 3 1) v3988_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3988_mg : Scalar.QComplex := ((-93086131919584168135359 : Int)/10^30,(235153175933268944808 : Int)/10^30)
theorem v3988_mg_checked : Scalar.distance (sourceCoefficient 58 74 3 2) v3988_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3988_upper : Scalar.QComplex := ((999994256874461270079011529673 : Int)/10^30,(-3389132351202721673535253060 : Int)/10^30)
theorem v3988_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 74 5) 1) 14) v3988_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3988 : Material (58 : Basis) (74 : Basis) where
  plus := ![v3988_pa,v3988_pb,v3988_pg]
  minus := ![(Primitive.Addresses.material3988 1).one,v3988_mb,v3988_mg]
  upper := v3988_upper
  lower := (Primitive.Addresses.material3988 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3988_pa_checked.trans (by decide +kernel)
    · exact v3988_pb_checked.trans (by decide +kernel)
    · exact v3988_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 74 Primitive.Addresses.material3988
    · exact v3988_mb_checked.trans (by decide +kernel)
    · exact v3988_mg_checked.trans (by decide +kernel)
  upper_error := v3988_upper_checked
  lower_error := reuse_lower_error 58 74 Primitive.Addresses.material3988

def v3989_pa : Scalar.QComplex := ((999998592084781539111745305051 : Int)/10^30,(-1678043043159654512090399743 : Int)/10^30)
theorem v3989_pa_checked : Scalar.distance (sourceCoefficient 58 75 1 0) v3989_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3989_pb : Scalar.QComplex := ((-724037836222534992952133 : Int)/10^30,(-431476903879252517592201388 : Int)/10^30)
theorem v3989_pb_checked : Scalar.distance (sourceCoefficient 58 75 1 1) v3989_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3989_pg : Scalar.QComplex := ((-93086297799569343277431 : Int)/10^30,(156203034356684432885 : Int)/10^30)
theorem v3989_pg_checked : Scalar.distance (sourceCoefficient 58 75 1 2) v3989_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3989_mb : Scalar.QComplex := ((-1096382701679589412999466 : Int)/10^30,(-431476118408638528253634824 : Int)/10^30)
theorem v3989_mb_checked : Scalar.distance (sourceCoefficient 58 75 3 1) v3989_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3989_mg : Scalar.QComplex := ((-93086128343102892216613 : Int)/10^30,(236532258744962466058 : Int)/10^30)
theorem v3989_mg_checked : Scalar.distance (sourceCoefficient 58 75 3 2) v3989_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3989_upper : Scalar.QComplex := ((999994206554285097288339650670 : Int)/10^30,(-3403947394686376729539397774 : Int)/10^30)
theorem v3989_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 75 5) 1) 14) v3989_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3989 : Material (58 : Basis) (75 : Basis) where
  plus := ![v3989_pa,v3989_pb,v3989_pg]
  minus := ![(Primitive.Addresses.material3989 1).one,v3989_mb,v3989_mg]
  upper := v3989_upper
  lower := (Primitive.Addresses.material3989 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3989_pa_checked.trans (by decide +kernel)
    · exact v3989_pb_checked.trans (by decide +kernel)
    · exact v3989_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 75 Primitive.Addresses.material3989
    · exact v3989_mb_checked.trans (by decide +kernel)
    · exact v3989_mg_checked.trans (by decide +kernel)
  upper_error := v3989_upper_checked
  lower_error := reuse_lower_error 58 75 Primitive.Addresses.material3989

def v3990_pa : Scalar.QComplex := ((999998571149141488068164925980 : Int)/10^30,(-1690473210497311548526720858 : Int)/10^30)
theorem v3990_pa_checked : Scalar.distance (sourceCoefficient 58 76 1 0) v3990_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3990_pb : Scalar.QComplex := ((-729401172766048486056650 : Int)/10^30,(-431476894180404158714825048 : Int)/10^30)
theorem v3990_pb_checked : Scalar.distance (sourceCoefficient 58 76 1 1) v3990_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3990_pg : Scalar.QComplex := ((-93086295778948538327718 : Int)/10^30,(157360114122875635919 : Int)/10^30)
theorem v3990_pg_checked : Scalar.distance (sourceCoefficient 58 76 1 2) v3990_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3990_mb : Scalar.QComplex := ((-1101746027856418280568257 : Int)/10^30,(-431476104081475899359567574 : Int)/10^30)
theorem v3990_mb_checked : Scalar.distance (sourceCoefficient 58 76 3 1) v3990_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3990_mg : Scalar.QComplex := ((-93086125323975114351510 : Int)/10^30,(237689336336615241692 : Int)/10^30)
theorem v3990_mg_checked : Scalar.distance (sourceCoefficient 58 76 3 2) v3990_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3990_upper : Scalar.QComplex := ((999994164165335058597404580116 : Int)/10^30,(-3416377507377744204888945066 : Int)/10^30)
theorem v3990_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 76 5) 1) 14) v3990_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3990 : Material (58 : Basis) (76 : Basis) where
  plus := ![v3990_pa,v3990_pb,v3990_pg]
  minus := ![(Primitive.Addresses.material3990 1).one,v3990_mb,v3990_mg]
  upper := v3990_upper
  lower := (Primitive.Addresses.material3990 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3990_pa_checked.trans (by decide +kernel)
    · exact v3990_pb_checked.trans (by decide +kernel)
    · exact v3990_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 76 Primitive.Addresses.material3990
    · exact v3990_mb_checked.trans (by decide +kernel)
    · exact v3990_mg_checked.trans (by decide +kernel)
  upper_error := v3990_upper_checked
  lower_error := reuse_lower_error 58 76 Primitive.Addresses.material3990

def v3991_pa : Scalar.QComplex := ((999998566280337279470706773563 : Int)/10^30,(-1693350899810487393649090683 : Int)/10^30)
theorem v3991_pa_checked : Scalar.distance (sourceCoefficient 58 77 1 0) v3991_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3991_pb : Scalar.QComplex := ((-730642830721165286134486 : Int)/10^30,(-431476891922366926890942043 : Int)/10^30)
theorem v3991_pb_checked : Scalar.distance (sourceCoefficient 58 77 1 1) v3991_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3991_pg : Scalar.QComplex := ((-93086295308765649465826 : Int)/10^30,(157627987915468733454 : Int)/10^30)
theorem v3991_pg_checked : Scalar.distance (sourceCoefficient 58 77 1 2) v3991_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3991_mb : Scalar.QComplex := ((-1102987683400624644541917 : Int)/10^30,(-431476100751944615238713786 : Int)/10^30)
theorem v3991_mb_checked : Scalar.distance (sourceCoefficient 58 77 3 1) v3991_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3991_mg : Scalar.QComplex := ((-93086124622629382140113 : Int)/10^30,(237957209623720026971 : Int)/10^30)
theorem v3991_mg_checked : Scalar.distance (sourceCoefficient 58 77 3 2) v3991_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3991_upper : Scalar.QComplex := ((999994154329907408905563922879 : Int)/10^30,(-3419255184001825485596696004 : Int)/10^30)
theorem v3991_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 77 5) 1) 14) v3991_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3991 : Material (58 : Basis) (77 : Basis) where
  plus := ![v3991_pa,v3991_pb,v3991_pg]
  minus := ![(Primitive.Addresses.material3991 1).one,v3991_mb,v3991_mg]
  upper := v3991_upper
  lower := (Primitive.Addresses.material3991 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3991_pa_checked.trans (by decide +kernel)
    · exact v3991_pb_checked.trans (by decide +kernel)
    · exact v3991_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 77 Primitive.Addresses.material3991
    · exact v3991_mb_checked.trans (by decide +kernel)
    · exact v3991_mg_checked.trans (by decide +kernel)
  upper_error := v3991_upper_checked
  lower_error := reuse_lower_error 58 77 Primitive.Addresses.material3991

def v3992_pa : Scalar.QComplex := ((999998536836424573581202205890 : Int)/10^30,(-1710650464006364200467854863 : Int)/10^30)
theorem v3992_pa_checked : Scalar.distance (sourceCoefficient 58 78 1 0) v3992_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3992_pb : Scalar.QComplex := ((-738107201953686232870018 : Int)/10^30,(-431476878247505955123213481 : Int)/10^30)
theorem v3992_pb_checked : Scalar.distance (sourceCoefficient 58 78 1 1) v3992_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3992_pg : Scalar.QComplex := ((-93086292463252445226864 : Int)/10^30,(159238342386637309611 : Int)/10^30)
theorem v3992_pg_checked : Scalar.distance (sourceCoefficient 58 78 1 2) v3992_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3992_mb : Scalar.QComplex := ((-1110452040053029917031585 : Int)/10^30,(-431476080635672544381740572 : Int)/10^30)
theorem v3992_mb_checked : Scalar.distance (sourceCoefficient 58 78 3 1) v3992_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3992_mg : Scalar.QComplex := ((-93086120387453856470310 : Int)/10^30,(239567561039730298576 : Int)/10^30)
theorem v3992_mg_checked : Scalar.distance (sourceCoefficient 58 78 3 2) v3992_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3992_upper : Scalar.QComplex := ((999994095028560158386278341802 : Int)/10^30,(-3436554671614511372747788891 : Int)/10^30)
theorem v3992_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 78 5) 1) 14) v3992_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3992 : Material (58 : Basis) (78 : Basis) where
  plus := ![v3992_pa,v3992_pb,v3992_pg]
  minus := ![(Primitive.Addresses.material3992 1).one,v3992_mb,v3992_mg]
  upper := v3992_upper
  lower := (Primitive.Addresses.material3992 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3992_pa_checked.trans (by decide +kernel)
    · exact v3992_pb_checked.trans (by decide +kernel)
    · exact v3992_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 78 Primitive.Addresses.material3992
    · exact v3992_mb_checked.trans (by decide +kernel)
    · exact v3992_mg_checked.trans (by decide +kernel)
  upper_error := v3992_upper_checked
  lower_error := reuse_lower_error 58 78 Primitive.Addresses.material3992

def v3993_pa : Scalar.QComplex := ((999998527280436359713977736760 : Int)/10^30,(-1716227536889458872690197981 : Int)/10^30)
theorem v3993_pa_checked : Scalar.distance (sourceCoefficient 58 79 1 0) v3993_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3993_pb : Scalar.QComplex := ((-740513582919279713121753 : Int)/10^30,(-431476873802273076203173184 : Int)/10^30)
theorem v3993_pb_checked : Scalar.distance (sourceCoefficient 58 79 1 1) v3993_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3993_pg : Scalar.QComplex := ((-93086291538981493845899 : Int)/10^30,(159757492124104374345 : Int)/10^30)
theorem v3993_pg_checked : Scalar.distance (sourceCoefficient 58 79 1 2) v3993_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3993_mb : Scalar.QComplex := ((-1112858416286582018098644 : Int)/10^30,(-431476074113842926693343619 : Int)/10^30)
theorem v3993_mb_checked : Scalar.distance (sourceCoefficient 58 79 3 1) v3993_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3993_mg : Scalar.QComplex := ((-93086119015180407439793 : Int)/10^30,(240086709786289986313 : Int)/10^30)
theorem v3993_mg_checked : Scalar.distance (sourceCoefficient 58 79 3 2) v3993_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3993_upper : Scalar.QComplex := ((999994075847064328919273630315 : Int)/10^30,(-3442131719698442369945752299 : Int)/10^30)
theorem v3993_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 79 5) 1) 14) v3993_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3993 : Material (58 : Basis) (79 : Basis) where
  plus := ![v3993_pa,v3993_pb,v3993_pg]
  minus := ![(Primitive.Addresses.material3993 1).one,v3993_mb,v3993_mg]
  upper := v3993_upper
  lower := (Primitive.Addresses.material3993 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3993_pa_checked.trans (by decide +kernel)
    · exact v3993_pb_checked.trans (by decide +kernel)
    · exact v3993_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 79 Primitive.Addresses.material3993
    · exact v3993_mb_checked.trans (by decide +kernel)
    · exact v3993_mg_checked.trans (by decide +kernel)
  upper_error := v3993_upper_checked
  lower_error := reuse_lower_error 58 79 Primitive.Addresses.material3993

def v3994_pa : Scalar.QComplex := ((999998512290795648714207110664 : Int)/10^30,(-1724939475872673879899838806 : Int)/10^30)
theorem v3994_pa_checked : Scalar.distance (sourceCoefficient 58 80 1 0) v3994_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3994_pb : Scalar.QComplex := ((-744272587769289512993116 : Int)/10^30,(-431476866822571586642953562 : Int)/10^30)
theorem v3994_pb_checked : Scalar.distance (sourceCoefficient 58 80 1 1) v3994_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3994_pg : Scalar.QComplex := ((-93086290088419315387704 : Int)/10^30,(160568455315218592321 : Int)/10^30)
theorem v3994_pg_checked : Scalar.distance (sourceCoefficient 58 80 1 2) v3994_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3994_mb : Scalar.QComplex := ((-1116617413713774485898116 : Int)/10^30,(-431476063890292149730278630 : Int)/10^30)
theorem v3994_mb_checked : Scalar.distance (sourceCoefficient 58 80 3 1) v3994_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3994_mg : Scalar.QComplex := ((-93086116864794059586897 : Int)/10^30,(240897671423675716273 : Int)/10^30)
theorem v3994_mg_checked : Scalar.distance (sourceCoefficient 58 80 3 2) v3994_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3994_upper : Scalar.QComplex := ((999994045821429599130185429561 : Int)/10^30,(-3450843619835487620295004182 : Int)/10^30)
theorem v3994_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 80 5) 1) 14) v3994_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3994 : Material (58 : Basis) (80 : Basis) where
  plus := ![v3994_pa,v3994_pb,v3994_pg]
  minus := ![(Primitive.Addresses.material3994 1).one,v3994_mb,v3994_mg]
  upper := v3994_upper
  lower := (Primitive.Addresses.material3994 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3994_pa_checked.trans (by decide +kernel)
    · exact v3994_pb_checked.trans (by decide +kernel)
    · exact v3994_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 80 Primitive.Addresses.material3994
    · exact v3994_mb_checked.trans (by decide +kernel)
    · exact v3994_mg_checked.trans (by decide +kernel)
  upper_error := v3994_upper_checked
  lower_error := reuse_lower_error 58 80 Primitive.Addresses.material3994

def v3995_pa : Scalar.QComplex := ((999998466697880749567899008006 : Int)/10^30,(-1751171575684540199508745610 : Int)/10^30)
theorem v3995_pa_checked : Scalar.distance (sourceCoefficient 58 81 1 0) v3995_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3995_pb : Scalar.QComplex := ((-755591146029823253266131 : Int)/10^30,(-431476845542650218579667798 : Int)/10^30)
theorem v3995_pb_checked : Scalar.distance (sourceCoefficient 58 81 1 1) v3995_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3995_pg : Scalar.QComplex := ((-93086285670926441089455 : Int)/10^30,(163010307497027436973 : Int)/10^30)
theorem v3995_pg_checked : Scalar.distance (sourceCoefficient 58 81 1 2) v3995_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3995_mb : Scalar.QComplex := ((-1127935949396277973549454 : Int)/10^30,(-431476032842972695254182651 : Int)/10^30)
theorem v3995_mb_checked : Scalar.distance (sourceCoefficient 58 81 3 1) v3995_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3995_mg : Scalar.QComplex := ((-93086110340094374161835 : Int)/10^30,(243339518884174001455 : Int)/10^30)
theorem v3995_mg_checked : Scalar.distance (sourceCoefficient 58 81 3 2) v3995_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3995_upper : Scalar.QComplex := ((999993954954358087498919008540 : Int)/10^30,(-3477075601888487750035444630 : Int)/10^30)
theorem v3995_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 81 5) 1) 14) v3995_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3995 : Material (58 : Basis) (81 : Basis) where
  plus := ![v3995_pa,v3995_pb,v3995_pg]
  minus := ![(Primitive.Addresses.material3995 1).one,v3995_mb,v3995_mg]
  upper := v3995_upper
  lower := (Primitive.Addresses.material3995 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3995_pa_checked.trans (by decide +kernel)
    · exact v3995_pb_checked.trans (by decide +kernel)
    · exact v3995_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 81 Primitive.Addresses.material3995
    · exact v3995_mb_checked.trans (by decide +kernel)
    · exact v3995_mg_checked.trans (by decide +kernel)
  upper_error := v3995_upper_checked
  lower_error := reuse_lower_error 58 81 Primitive.Addresses.material3995

def v3996_pa : Scalar.QComplex := ((999998449241377604193244104704 : Int)/10^30,(-1761111819260579653682492275 : Int)/10^30)
theorem v3996_pa_checked : Scalar.distance (sourceCoefficient 58 82 1 0) v3996_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3996_pb : Scalar.QComplex := ((-759880136429891266326291 : Int)/10^30,(-431476837375528183605408884 : Int)/10^30)
theorem v3996_pb_checked : Scalar.distance (sourceCoefficient 58 82 1 1) v3996_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3996_pg : Scalar.QComplex := ((-93086283977462229788533 : Int)/10^30,(163935609148314858606 : Int)/10^30)
theorem v3996_pg_checked : Scalar.distance (sourceCoefficient 58 82 1 2) v3996_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3996_mb : Scalar.QComplex := ((-1132224931151500361458644 : Int)/10^30,(-431476020974648154970868323 : Int)/10^30)
theorem v3996_mb_checked : Scalar.distance (sourceCoefficient 58 82 3 1) v3996_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3996_mg : Scalar.QComplex := ((-93086107848137142393350 : Int)/10^30,(244264818729545986383 : Int)/10^30)
theorem v3996_mg_checked : Scalar.distance (sourceCoefficient 58 82 3 2) v3996_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3996_upper : Scalar.QComplex := ((999993920341922301143979493034 : Int)/10^30,(-3487015800531361273410685128 : Int)/10^30)
theorem v3996_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 82 5) 1) 14) v3996_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3996 : Material (58 : Basis) (82 : Basis) where
  plus := ![v3996_pa,v3996_pb,v3996_pg]
  minus := ![(Primitive.Addresses.material3996 1).one,v3996_mb,v3996_mg]
  upper := v3996_upper
  lower := (Primitive.Addresses.material3996 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3996_pa_checked.trans (by decide +kernel)
    · exact v3996_pb_checked.trans (by decide +kernel)
    · exact v3996_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 82 Primitive.Addresses.material3996
    · exact v3996_mb_checked.trans (by decide +kernel)
    · exact v3996_mg_checked.trans (by decide +kernel)
  upper_error := v3996_upper_checked
  lower_error := reuse_lower_error 58 82 Primitive.Addresses.material3996

def v3997_pa : Scalar.QComplex := ((999998425253465517259601197609 : Int)/10^30,(-1774680418875137341893581502 : Int)/10^30)
theorem v3997_pa_checked : Scalar.distance (sourceCoefficient 58 83 1 0) v3997_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3997_pb : Scalar.QComplex := ((-765734680379121667715472 : Int)/10^30,(-431476826135513219333805154 : Int)/10^30)
theorem v3997_pb_checked : Scalar.distance (sourceCoefficient 58 83 1 1) v3997_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3997_pg : Scalar.QComplex := ((-93086281648534176959141 : Int)/10^30,(165198661453569268537 : Int)/10^30)
theorem v3997_pg_checked : Scalar.distance (sourceCoefficient 58 83 1 2) v3997_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3997_mb : Scalar.QComplex := ((-1138079463221189801988245 : Int)/10^30,(-431476004682429626555946990 : Int)/10^30)
theorem v3997_mb_checked : Scalar.distance (sourceCoefficient 58 83 3 1) v3997_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3997_mg : Scalar.QComplex := ((-93086104429252703059884 : Int)/10^30,(245527868554748280160 : Int)/10^30)
theorem v3997_mg_checked : Scalar.distance (sourceCoefficient 58 83 3 2) v3997_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3997_upper : Scalar.QComplex := ((999993872935873940402508096070 : Int)/10^30,(-3500584338536123619750544231 : Int)/10^30)
theorem v3997_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 83 5) 1) 14) v3997_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3997 : Material (58 : Basis) (83 : Basis) where
  plus := ![v3997_pa,v3997_pb,v3997_pg]
  minus := ![(Primitive.Addresses.material3997 1).one,v3997_mb,v3997_mg]
  upper := v3997_upper
  lower := (Primitive.Addresses.material3997 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3997_pa_checked.trans (by decide +kernel)
    · exact v3997_pb_checked.trans (by decide +kernel)
    · exact v3997_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 83 Primitive.Addresses.material3997
    · exact v3997_mb_checked.trans (by decide +kernel)
    · exact v3997_mg_checked.trans (by decide +kernel)
  upper_error := v3997_upper_checked
  lower_error := reuse_lower_error 58 83 Primitive.Addresses.material3997

def v3998_pa : Scalar.QComplex := ((999998362275493105786031129930 : Int)/10^30,(-1809819419623645063909801255 : Int)/10^30)
theorem v3998_pa_checked : Scalar.distance (sourceCoefficient 58 84 1 0) v3998_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3998_pb : Scalar.QComplex := ((-780896364378411552429403 : Int)/10^30,(-431476796534588344452115218 : Int)/10^30)
theorem v3998_pb_checked : Scalar.distance (sourceCoefficient 58 84 1 1) v3998_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3998_pg : Scalar.QComplex := ((-93086275524303300714099 : Int)/10^30,(168469625051154929882 : Int)/10^30)
theorem v3998_pg_checked : Scalar.distance (sourceCoefficient 58 84 1 2) v3998_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3998_mb : Scalar.QComplex := ((-1153241116030826819720324 : Int)/10^30,(-431475961997665338962734975 : Int)/10^30)
theorem v3998_mb_checked : Scalar.distance (sourceCoefficient 58 84 3 1) v3998_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3998_mg : Scalar.QComplex := ((-93086095482329841161169 : Int)/10^30,(248798825649469282623 : Int)/10^30)
theorem v3998_mg_checked : Scalar.distance (sourceCoefficient 58 84 3 2) v3998_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3998_upper : Scalar.QComplex := ((999993749311267820542897240726 : Int)/10^30,(-3535723178254950378672538803 : Int)/10^30)
theorem v3998_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 84 5) 1) 14) v3998_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3998 : Material (58 : Basis) (84 : Basis) where
  plus := ![v3998_pa,v3998_pb,v3998_pg]
  minus := ![(Primitive.Addresses.material3998 1).one,v3998_mb,v3998_mg]
  upper := v3998_upper
  lower := (Primitive.Addresses.material3998 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3998_pa_checked.trans (by decide +kernel)
    · exact v3998_pb_checked.trans (by decide +kernel)
    · exact v3998_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 84 Primitive.Addresses.material3998
    · exact v3998_mb_checked.trans (by decide +kernel)
    · exact v3998_mg_checked.trans (by decide +kernel)
  upper_error := v3998_upper_checked
  lower_error := reuse_lower_error 58 84 Primitive.Addresses.material3998

def v3999_pa : Scalar.QComplex := ((999998216071944715097647879485 : Int)/10^30,(-1888876101858059474683125659 : Int)/10^30)
theorem v3999_pa_checked : Scalar.distance (sourceCoefficient 58 85 1 0) v3999_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3999_pb : Scalar.QComplex := ((-815007532696596733964610 : Int)/10^30,(-431476727340710418559298378 : Int)/10^30)
theorem v3999_pb_checked : Scalar.distance (sourceCoefficient 58 85 1 1) v3999_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3999_pg : Scalar.QComplex := ((-93086261255619045125480 : Int)/10^30,(175828727962855352726 : Int)/10^30)
theorem v3999_pg_checked : Scalar.distance (sourceCoefficient 58 85 1 2) v3999_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3999_mb : Scalar.QComplex := ((-1187352211936664805519934 : Int)/10^30,(-431475863367411228509718192 : Int)/10^30)
theorem v3999_mb_checked : Scalar.distance (sourceCoefficient 58 85 3 1) v3999_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3999_mg : Scalar.QComplex := ((-93086074863076527349793 : Int)/10^30,(256157913507807488932 : Int)/10^30)
theorem v3999_mg_checked : Scalar.distance (sourceCoefficient 58 85 3 2) v3999_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3999_upper : Scalar.QComplex := ((999993466663275612454274444548 : Int)/10^30,(-3614779490409662211505668190 : Int)/10^30)
theorem v3999_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 85 5) 1) 14) v3999_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3999 : Material (58 : Basis) (85 : Basis) where
  plus := ![v3999_pa,v3999_pb,v3999_pg]
  minus := ![(Primitive.Addresses.material3999 1).one,v3999_mb,v3999_mg]
  upper := v3999_upper
  lower := (Primitive.Addresses.material3999 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3999_pa_checked.trans (by decide +kernel)
    · exact v3999_pb_checked.trans (by decide +kernel)
    · exact v3999_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 85 Primitive.Addresses.material3999
    · exact v3999_mb_checked.trans (by decide +kernel)
    · exact v3999_mg_checked.trans (by decide +kernel)
  upper_error := v3999_upper_checked
  lower_error := reuse_lower_error 58 85 Primitive.Addresses.material3999

def v4000_pa : Scalar.QComplex := ((999998188417003288304817968357 : Int)/10^30,(-1903460719739295379068689623 : Int)/10^30)
theorem v4000_pa_checked : Scalar.distance (sourceCoefficient 58 86 1 0) v4000_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4000_pb : Scalar.QComplex := ((-821300464783017452421895 : Int)/10^30,(-431476714182758777027333709 : Int)/10^30)
theorem v4000_pb_checked : Scalar.distance (sourceCoefficient 58 86 1 1) v4000_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4000_pg : Scalar.QComplex := ((-93086258549129006642474 : Int)/10^30,(177186357683556065414 : Int)/10^30)
theorem v4000_pg_checked : Scalar.distance (sourceCoefficient 58 86 1 2) v4000_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4000_mb : Scalar.QComplex := ((-1193645130325219652499701 : Int)/10^30,(-431475844778947518843428614 : Int)/10^30)
theorem v4000_mb_checked : Scalar.distance (sourceCoefficient 58 86 3 1) v4000_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4000_mg : Scalar.QComplex := ((-93086070985014193024804 : Int)/10^30,(257515540387421602436 : Int)/10^30)
theorem v4000_mg_checked : Scalar.distance (sourceCoefficient 58 86 3 2) v4000_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4000_upper : Scalar.QComplex := ((999993413836648017633598446869 : Int)/10^30,(-3629364038838902945398352987 : Int)/10^30)
theorem v4000_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 58 86 5) 1) 14) v4000_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4000 : Material (58 : Basis) (86 : Basis) where
  plus := ![v4000_pa,v4000_pb,v4000_pg]
  minus := ![(Primitive.Addresses.material4000 1).one,v4000_mb,v4000_mg]
  upper := v4000_upper
  lower := (Primitive.Addresses.material4000 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4000_pa_checked.trans (by decide +kernel)
    · exact v4000_pb_checked.trans (by decide +kernel)
    · exact v4000_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 58 86 Primitive.Addresses.material4000
    · exact v4000_mb_checked.trans (by decide +kernel)
    · exact v4000_mg_checked.trans (by decide +kernel)
  upper_error := v4000_upper_checked
  lower_error := reuse_lower_error 58 86 Primitive.Addresses.material4000

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
