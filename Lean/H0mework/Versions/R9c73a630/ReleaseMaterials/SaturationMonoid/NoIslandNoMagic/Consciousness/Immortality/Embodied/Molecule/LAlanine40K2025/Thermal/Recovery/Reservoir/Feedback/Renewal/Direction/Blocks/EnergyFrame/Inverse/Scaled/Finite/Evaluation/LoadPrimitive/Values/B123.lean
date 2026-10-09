import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B082

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1969_pa : Scalar.QComplex := ((999998968617364004282018996011 : Int)/10^30,(-1436232644191495227041926153 : Int)/10^30)
theorem v1969_pa_checked : Scalar.distance (sourceCoefficient 22 89 1 0) v1969_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1969_pb : Scalar.QComplex := ((-619701972177331565790069 : Int)/10^30,(-431476986359914672934001996 : Int)/10^30)
theorem v1969_pb_checked : Scalar.distance (sourceCoefficient 22 89 1 1) v1969_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1969_pg : Scalar.QComplex := ((-93086324221744469316291 : Int)/10^30,(133693755464480815373 : Int)/10^30)
theorem v1969_pg_checked : Scalar.distance (sourceCoefficient 22 89 1 2) v1969_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1969_mb : Scalar.QComplex := ((-992046947660493203352506 : Int)/10^30,(-431476290926421530408593792 : Int)/10^30)
theorem v1969_mb_checked : Scalar.distance (sourceCoefficient 22 89 3 1) v1969_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1969_mg : Scalar.QComplex := ((-93086174189762083755830 : Int)/10^30,(214023011035139228158 : Int)/10^30)
theorem v1969_mg_checked : Scalar.distance (sourceCoefficient 22 89 3 2) v1969_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1969_upper : Scalar.QComplex := ((999995000429118512417599257293 : Int)/10^30,(-3162138005727480228592123139 : Int)/10^30)
theorem v1969_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 89 5) 1) 14) v1969_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1969 : Material (22 : Basis) (89 : Basis) where
  plus := ![v1969_pa,v1969_pb,v1969_pg]
  minus := ![(Primitive.Addresses.material1969 1).one,v1969_mb,v1969_mg]
  upper := v1969_upper
  lower := (Primitive.Addresses.material1969 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1969_pa_checked.trans (by decide +kernel)
    · exact v1969_pb_checked.trans (by decide +kernel)
    · exact v1969_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 89 Primitive.Addresses.material1969
    · exact v1969_mb_checked.trans (by decide +kernel)
    · exact v1969_mg_checked.trans (by decide +kernel)
  upper_error := v1969_upper_checked
  lower_error := reuse_lower_error 22 89 Primitive.Addresses.material1969

def v1970_pa : Scalar.QComplex := ((999998930640547069515175474834 : Int)/10^30,(-1462435558351659499632078108 : Int)/10^30)
theorem v1970_pa_checked : Scalar.distance (sourceCoefficient 22 90 1 0) v1970_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1970_pb : Scalar.QComplex := ((-631007932048836915423478 : Int)/10^30,(-431476965717218242730807550 : Int)/10^30)
theorem v1970_pb_checked : Scalar.distance (sourceCoefficient 22 90 1 1) v1970_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1970_pg : Scalar.QComplex := ((-93086320227466326152293 : Int)/10^30,(136132890271749159250 : Int)/10^30)
theorem v1970_pg_checked : Scalar.distance (sourceCoefficient 22 90 1 2) v1970_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1970_mb : Scalar.QComplex := ((-1003352885508555678201766 : Int)/10^30,(-431476260527198618845744694 : Int)/10^30)
theorem v1970_mb_checked : Scalar.distance (sourceCoefficient 22 90 3 1) v1970_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1970_mg : Scalar.QComplex := ((-93086168090621943725279 : Int)/10^30,(216462141487324067380 : Int)/10^30)
theorem v1970_mg_checked : Scalar.distance (sourceCoefficient 22 90 3 2) v1970_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1970_upper : Scalar.QComplex := ((999994917228505409018622641992 : Int)/10^30,(-3188340815316941070645380740 : Int)/10^30)
theorem v1970_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 90 5) 1) 14) v1970_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1970 : Material (22 : Basis) (90 : Basis) where
  plus := ![v1970_pa,v1970_pb,v1970_pg]
  minus := ![(Primitive.Addresses.material1970 1).one,v1970_mb,v1970_mg]
  upper := v1970_upper
  lower := (Primitive.Addresses.material1970 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1970_pa_checked.trans (by decide +kernel)
    · exact v1970_pb_checked.trans (by decide +kernel)
    · exact v1970_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 90 Primitive.Addresses.material1970
    · exact v1970_mb_checked.trans (by decide +kernel)
    · exact v1970_mg_checked.trans (by decide +kernel)
  upper_error := v1970_upper_checked
  lower_error := reuse_lower_error 22 90 Primitive.Addresses.material1970

def v1971_pa : Scalar.QComplex := ((999998908944487486428163586639 : Int)/10^30,(-1477196613394781746435658234 : Int)/10^30)
theorem v1971_pa_checked : Scalar.distance (sourceCoefficient 22 91 1 0) v1971_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1971_pb : Scalar.QComplex := ((-637376990494076349050730 : Int)/10^30,(-431476953914501085960146342 : Int)/10^30)
theorem v1971_pb_checked : Scalar.distance (sourceCoefficient 22 91 1 1) v1971_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1971_pg : Scalar.QComplex := ((-93086317944510108058871 : Int)/10^30,(137506943648729109575 : Int)/10^30)
theorem v1971_pg_checked : Scalar.distance (sourceCoefficient 22 91 1 2) v1971_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1971_mb : Scalar.QComplex := ((-1009721931397090240670450 : Int)/10^30,(-431476243228275270268396868 : Int)/10^30)
theorem v1971_mb_checked : Scalar.distance (sourceCoefficient 22 91 3 1) v1971_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1971_mg : Scalar.QComplex := ((-93086164621920396413914 : Int)/10^30,(217836192382592752431 : Int)/10^30)
theorem v1971_mg_checked : Scalar.distance (sourceCoefficient 22 91 3 2) v1971_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1971_upper : Scalar.QComplex := ((999994870056236247687703218286 : Int)/10^30,(-3203101810929775196789518816 : Int)/10^30)
theorem v1971_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 91 5) 1) 14) v1971_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1971 : Material (22 : Basis) (91 : Basis) where
  plus := ![v1971_pa,v1971_pb,v1971_pg]
  minus := ![(Primitive.Addresses.material1971 1).one,v1971_mb,v1971_mg]
  upper := v1971_upper
  lower := (Primitive.Addresses.material1971 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1971_pa_checked.trans (by decide +kernel)
    · exact v1971_pb_checked.trans (by decide +kernel)
    · exact v1971_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 91 Primitive.Addresses.material1971
    · exact v1971_mb_checked.trans (by decide +kernel)
    · exact v1971_mg_checked.trans (by decide +kernel)
  upper_error := v1971_upper_checked
  lower_error := reuse_lower_error 22 91 Primitive.Addresses.material1971

def v1972_pa : Scalar.QComplex := ((999998861228442190024624577163 : Int)/10^30,(-1509152682408009330139173662 : Int)/10^30)
theorem v1972_pa_checked : Scalar.distance (sourceCoefficient 22 92 1 0) v1972_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1972_pb : Scalar.QComplex := ((-651165304716499682788971 : Int)/10^30,(-431476927933475074748384765 : Int)/10^30)
theorem v1972_pb_checked : Scalar.distance (sourceCoefficient 22 92 1 1) v1972_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1972_pg : Scalar.QComplex := ((-93086312921094629520593 : Int)/10^30,(140481618816813202386 : Int)/10^30)
theorem v1972_pg_checked : Scalar.distance (sourceCoefficient 22 92 1 2) v1972_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1972_mb : Scalar.QComplex := ((-1023510218065038726608209 : Int)/10^30,(-431476205348564761648550891 : Int)/10^30)
theorem v1972_mb_checked : Scalar.distance (sourceCoefficient 22 92 3 1) v1972_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1972_mg : Scalar.QComplex := ((-93086157031496092662435 : Int)/10^30,(220810862108088019049 : Int)/10^30)
theorem v1972_mg_checked : Scalar.distance (sourceCoefficient 22 92 3 2) v1972_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1972_upper : Scalar.QComplex := ((999994767186985933832588617689 : Int)/10^30,(-3235057749994626393070883378 : Int)/10^30)
theorem v1972_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 92 5) 1) 14) v1972_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1972 : Material (22 : Basis) (92 : Basis) where
  plus := ![v1972_pa,v1972_pb,v1972_pg]
  minus := ![(Primitive.Addresses.material1972 1).one,v1972_mb,v1972_mg]
  upper := v1972_upper
  lower := (Primitive.Addresses.material1972 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1972_pa_checked.trans (by decide +kernel)
    · exact v1972_pb_checked.trans (by decide +kernel)
    · exact v1972_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 92 Primitive.Addresses.material1972
    · exact v1972_mb_checked.trans (by decide +kernel)
    · exact v1972_mg_checked.trans (by decide +kernel)
  upper_error := v1972_upper_checked
  lower_error := reuse_lower_error 22 92 Primitive.Addresses.material1972

def v1973_pa : Scalar.QComplex := ((999998803273728382388394556321 : Int)/10^30,(-1547078249824957635810344283 : Int)/10^30)
theorem v1973_pa_checked : Scalar.distance (sourceCoefficient 22 93 1 0) v1973_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1973_pb : Scalar.QComplex := ((-667529320474428227652408 : Int)/10^30,(-431476896336743197624365160 : Int)/10^30)
theorem v1973_pb_checked : Scalar.distance (sourceCoefficient 22 93 1 1) v1973_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1973_pg : Scalar.QComplex := ((-93086306815375855358005 : Int)/10^30,(144011972973512189068 : Int)/10^30)
theorem v1973_pg_checked : Scalar.distance (sourceCoefficient 22 93 1 2) v1973_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1973_mb : Scalar.QComplex := ((-1039874200463339786348161 : Int)/10^30,(-431476159630436058250234340 : Int)/10^30)
theorem v1973_mb_checked : Scalar.distance (sourceCoefficient 22 93 3 1) v1973_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1973_mg : Scalar.QComplex := ((-93086147879242955955580 : Int)/10^30,(224341209681314497299 : Int)/10^30)
theorem v1973_mg_checked : Scalar.distance (sourceCoefficient 22 93 3 2) v1973_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1973_upper : Scalar.QComplex := ((999994643776269661881685409706 : Int)/10^30,(-3272983160901318659882843999 : Int)/10^30)
theorem v1973_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 93 5) 1) 14) v1973_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1973 : Material (22 : Basis) (93 : Basis) where
  plus := ![v1973_pa,v1973_pb,v1973_pg]
  minus := ![(Primitive.Addresses.material1973 1).one,v1973_mb,v1973_mg]
  upper := v1973_upper
  lower := (Primitive.Addresses.material1973 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1973_pa_checked.trans (by decide +kernel)
    · exact v1973_pb_checked.trans (by decide +kernel)
    · exact v1973_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 93 Primitive.Addresses.material1973
    · exact v1973_mb_checked.trans (by decide +kernel)
    · exact v1973_mg_checked.trans (by decide +kernel)
  upper_error := v1973_upper_checked
  lower_error := reuse_lower_error 22 93 Primitive.Addresses.material1973

def v1974_pa : Scalar.QComplex := ((999998732963400302826065723530 : Int)/10^30,(-1591876752142766514990845996 : Int)/10^30)
theorem v1974_pa_checked : Scalar.distance (sourceCoefficient 22 94 1 0) v1974_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1974_pb : Scalar.QComplex := ((-686858849530303334902421 : Int)/10^30,(-431476857947983718532008455 : Int)/10^30)
theorem v1974_pb_checked : Scalar.distance (sourceCoefficient 22 94 1 1) v1974_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1974_pg : Scalar.QComplex := ((-93086299401935218999778 : Int)/10^30,(148182103713090610103 : Int)/10^30)
theorem v1974_pg_checked : Scalar.distance (sourceCoefficient 22 94 1 2) v1974_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1974_mb : Scalar.QComplex := ((-1059203689194177358065036 : Int)/10^30,(-431476104561177867498878452 : Int)/10^30)
theorem v1974_mb_checked : Scalar.distance (sourceCoefficient 22 94 3 1) v1974_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1974_mg : Scalar.QComplex := ((-93086136867170067420399 : Int)/10^30,(228511332470697279394 : Int)/10^30)
theorem v1974_mg_checked : Scalar.distance (sourceCoefficient 22 94 3 2) v1974_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1974_upper : Scalar.QComplex := ((999994496147895389139029694312 : Int)/10^30,(-3317781475147772976245496847 : Int)/10^30)
theorem v1974_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 94 5) 1) 14) v1974_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1974 : Material (22 : Basis) (94 : Basis) where
  plus := ![v1974_pa,v1974_pb,v1974_pg]
  minus := ![(Primitive.Addresses.material1974 1).one,v1974_mb,v1974_mg]
  upper := v1974_upper
  lower := (Primitive.Addresses.material1974 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1974_pa_checked.trans (by decide +kernel)
    · exact v1974_pb_checked.trans (by decide +kernel)
    · exact v1974_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 94 Primitive.Addresses.material1974
    · exact v1974_mb_checked.trans (by decide +kernel)
    · exact v1974_mg_checked.trans (by decide +kernel)
  upper_error := v1974_upper_checked
  lower_error := reuse_lower_error 22 94 Primitive.Addresses.material1974

def v1975_pa : Scalar.QComplex := ((999998661504190741082290562223 : Int)/10^30,(-1636150918145023691258749251 : Int)/10^30)
theorem v1975_pa_checked : Scalar.distance (sourceCoefficient 22 95 1 0) v1975_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1975_pb : Scalar.QComplex := ((-705962138286594600672017 : Int)/10^30,(-431476818874147798898152366 : Int)/10^30)
theorem v1975_pb_checked : Scalar.distance (sourceCoefficient 22 95 1 1) v1975_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1975_pg : Scalar.QComplex := ((-93086291861123166131429 : Int)/10^30,(152303425752789420314 : Int)/10^30)
theorem v1975_pg_checked : Scalar.distance (sourceCoefficient 22 95 1 2) v1975_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1975_mb : Scalar.QComplex := ((-1078306937118480578039227 : Int)/10^30,(-431476049002078680347304932 : Int)/10^30)
theorem v1975_mb_checked : Scalar.distance (sourceCoefficient 22 95 3 1) v1975_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1975_mg : Scalar.QComplex := ((-93086125769845519535160 : Int)/10^30,(232632646468458364444 : Int)/10^30)
theorem v1975_mg_checked : Scalar.distance (sourceCoefficient 22 95 3 2) v1975_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1975_upper : Scalar.QComplex := ((999994348275598258562206922696 : Int)/10^30,(-3362055451876747726308245406 : Int)/10^30)
theorem v1975_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 95 5) 1) 14) v1975_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1975 : Material (22 : Basis) (95 : Basis) where
  plus := ![v1975_pa,v1975_pb,v1975_pg]
  minus := ![(Primitive.Addresses.material1975 1).one,v1975_mb,v1975_mg]
  upper := v1975_upper
  lower := (Primitive.Addresses.material1975 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1975_pa_checked.trans (by decide +kernel)
    · exact v1975_pb_checked.trans (by decide +kernel)
    · exact v1975_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 95 Primitive.Addresses.material1975
    · exact v1975_mb_checked.trans (by decide +kernel)
    · exact v1975_mg_checked.trans (by decide +kernel)
  upper_error := v1975_upper_checked
  lower_error := reuse_lower_error 22 95 Primitive.Addresses.material1975

def v1976_pa : Scalar.QComplex := ((999998626486838887518510577609 : Int)/10^30,(-1657414985960534637533949389 : Int)/10^30)
theorem v1976_pa_checked : Scalar.distance (sourceCoefficient 22 96 1 0) v1976_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1976_pb : Scalar.QComplex := ((-715137096178602046216937 : Int)/10^30,(-431476799706827818824039174 : Int)/10^30)
theorem v1976_pb_checked : Scalar.distance (sourceCoefficient 22 96 1 1) v1976_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1976_pg : Scalar.QComplex := ((-93086288163735986727657 : Int)/10^30,(154282820899501801072 : Int)/10^30)
theorem v1976_pg_checked : Scalar.distance (sourceCoefficient 22 96 1 2) v1976_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1976_mb : Scalar.QComplex := ((-1087481875053698005341540 : Int)/10^30,(-431476021917190401103816351 : Int)/10^30)
theorem v1976_mb_checked : Scalar.distance (sourceCoefficient 22 96 3 1) v1976_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1976_mg : Scalar.QComplex := ((-93086120364330853872884 : Int)/10^30,(234612037687472857566 : Int)/10^30)
theorem v1976_mg_checked : Scalar.distance (sourceCoefficient 22 96 3 2) v1976_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1976_upper : Scalar.QComplex := ((999994276558446570821916757475 : Int)/10^30,(-3383319427585154964343762016 : Int)/10^30)
theorem v1976_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 96 5) 1) 14) v1976_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1976 : Material (22 : Basis) (96 : Basis) where
  plus := ![v1976_pa,v1976_pb,v1976_pg]
  minus := ![(Primitive.Addresses.material1976 1).one,v1976_mb,v1976_mg]
  upper := v1976_upper
  lower := (Primitive.Addresses.material1976 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1976_pa_checked.trans (by decide +kernel)
    · exact v1976_pb_checked.trans (by decide +kernel)
    · exact v1976_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 96 Primitive.Addresses.material1976
    · exact v1976_mb_checked.trans (by decide +kernel)
    · exact v1976_mg_checked.trans (by decide +kernel)
  upper_error := v1976_upper_checked
  lower_error := reuse_lower_error 22 96 Primitive.Addresses.material1976

def v1977_pa : Scalar.QComplex := ((999998502550321905676730673567 : Int)/10^30,(-1730577104272764875833606070 : Int)/10^30)
theorem v1977_pa_checked : Scalar.distance (sourceCoefficient 22 97 1 0) v1977_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1977_pb : Scalar.QComplex := ((-746704871183430533077979 : Int)/10^30,(-431476731771651736136697668 : Int)/10^30)
theorem v1977_pb_checked : Scalar.distance (sourceCoefficient 22 97 1 1) v1977_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1977_pg : Scalar.QComplex := ((-93086275067206270854461 : Int)/10^30,(161093217582330711686 : Int)/10^30)
theorem v1977_pg_checked : Scalar.distance (sourceCoefficient 22 97 1 2) v1977_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1977_mb : Scalar.QComplex := ((-1119049579679403866706149 : Int)/10^30,(-431475926740471544428349736 : Int)/10^30)
theorem v1977_mb_checked : Scalar.distance (sourceCoefficient 22 97 3 1) v1977_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1977_mg : Scalar.QComplex := ((-93086101390740406035176 : Int)/10^30,(241422420532764533662 : Int)/10^30)
theorem v1977_mg_checked : Scalar.distance (sourceCoefficient 22 97 3 2) v1977_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1977_upper : Scalar.QComplex := ((999994026350935186480387151570 : Int)/10^30,(-3456481223027819325037693464 : Int)/10^30)
theorem v1977_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 97 5) 1) 14) v1977_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1977 : Material (22 : Basis) (97 : Basis) where
  plus := ![v1977_pa,v1977_pb,v1977_pg]
  minus := ![(Primitive.Addresses.material1977 1).one,v1977_mb,v1977_mg]
  upper := v1977_upper
  lower := (Primitive.Addresses.material1977 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1977_pa_checked.trans (by decide +kernel)
    · exact v1977_pb_checked.trans (by decide +kernel)
    · exact v1977_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 97 Primitive.Addresses.material1977
    · exact v1977_mb_checked.trans (by decide +kernel)
    · exact v1977_mg_checked.trans (by decide +kernel)
  upper_error := v1977_upper_checked
  lower_error := reuse_lower_error 22 97 Primitive.Addresses.material1977

def v1978_pa : Scalar.QComplex := ((999999923389279996696507313509 : Int)/10^30,(-391435095689444492033963031 : Int)/10^30)
theorem v1978_pa_checked : Scalar.distance (sourceCoefficient 23 24 1 0) v1978_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1978_pb : Scalar.QComplex := ((-168895444647673630527478 : Int)/10^30,(-431477487758199691878848308 : Int)/10^30)
theorem v1978_pb_checked : Scalar.distance (sourceCoefficient 23 24 1 1) v1978_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1978_pg : Scalar.QComplex := ((-93086422745423873932863 : Int)/10^30,(36437295586230526187 : Int)/10^30)
theorem v1978_pg_checked : Scalar.distance (sourceCoefficient 23 24 1 2) v1978_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1978_mb : Scalar.QComplex := ((-541241020670846174373007 : Int)/10^30,(-431477181350249541655788029 : Int)/10^30)
theorem v1978_mb_checked : Scalar.distance (sourceCoefficient 23 24 3 1) v1978_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1978_mg : Scalar.QComplex := ((-93086356641349410084093 : Int)/10^30,(116766672391411775826 : Int)/10^30)
theorem v1978_mg_checked : Scalar.distance (sourceCoefficient 23 24 3 2) v1978_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1978_upper : Scalar.QComplex := ((999997758425397905564521306995 : Int)/10^30,(-2117343661178358217288812145 : Int)/10^30)
theorem v1978_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 24 5) 1) 14) v1978_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1978 : Material (23 : Basis) (24 : Basis) where
  plus := ![v1978_pa,v1978_pb,v1978_pg]
  minus := ![(Primitive.Addresses.material1978 1).one,v1978_mb,v1978_mg]
  upper := v1978_upper
  lower := (Primitive.Addresses.material1978 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1978_pa_checked.trans (by decide +kernel)
    · exact v1978_pb_checked.trans (by decide +kernel)
    · exact v1978_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 24 Primitive.Addresses.material1978
    · exact v1978_mb_checked.trans (by decide +kernel)
    · exact v1978_mg_checked.trans (by decide +kernel)
  upper_error := v1978_upper_checked
  lower_error := reuse_lower_error 23 24 Primitive.Addresses.material1978

def v1979_pa : Scalar.QComplex := ((999999914128263116299289537789 : Int)/10^30,(-414419432934130425414387451 : Int)/10^30)
theorem v1979_pa_checked : Scalar.distance (sourceCoefficient 23 25 1 0) v1979_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1979_pb : Scalar.QComplex := ((-178812669414025681845981 : Int)/10^30,(-431477483555874709035920802 : Int)/10^30)
theorem v1979_pb_checked : Scalar.distance (sourceCoefficient 23 25 1 1) v1979_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1979_pg : Scalar.QComplex := ((-93086421861084162224036 : Int)/10^30,(38576825474196747195 : Int)/10^30)
theorem v1979_pg_checked : Scalar.distance (sourceCoefficient 23 25 1 2) v1979_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1979_mb : Scalar.QComplex := ((-551158238118145011114239 : Int)/10^30,(-431477168589807805391542332 : Int)/10^30)
theorem v1979_mb_checked : Scalar.distance (sourceCoefficient 23 25 3 1) v1979_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1979_mg : Scalar.QComplex := ((-93086353910692095189579 : Int)/10^30,(118906200719587896175 : Int)/10^30)
theorem v1979_mg_checked : Scalar.distance (sourceCoefficient 23 25 3 2) v1979_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1979_upper : Scalar.QComplex := ((999997709495513856822902968148 : Int)/10^30,(-2140327948206898771944909185 : Int)/10^30)
theorem v1979_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 25 5) 1) 14) v1979_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1979 : Material (23 : Basis) (25 : Basis) where
  plus := ![v1979_pa,v1979_pb,v1979_pg]
  minus := ![(Primitive.Addresses.material1979 1).one,v1979_mb,v1979_mg]
  upper := v1979_upper
  lower := (Primitive.Addresses.material1979 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1979_pa_checked.trans (by decide +kernel)
    · exact v1979_pb_checked.trans (by decide +kernel)
    · exact v1979_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 25 Primitive.Addresses.material1979
    · exact v1979_mb_checked.trans (by decide +kernel)
    · exact v1979_mg_checked.trans (by decide +kernel)
  upper_error := v1979_upper_checked
  lower_error := reuse_lower_error 23 25 Primitive.Addresses.material1979

def v1980_pa : Scalar.QComplex := ((999999911057828791683558023488 : Int)/10^30,(-421763363162239430546777815 : Int)/10^30)
theorem v1980_pa_checked : Scalar.distance (sourceCoefficient 23 26 1 0) v1980_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1980_pb : Scalar.QComplex := ((-181981410185794599746339 : Int)/10^30,(-431477482149084147152223638 : Int)/10^30)
theorem v1980_pb_checked : Scalar.distance (sourceCoefficient 23 26 1 1) v1980_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1980_pg : Scalar.QComplex := ((-93086421566426644433667 : Int)/10^30,(39260445716503402108 : Int)/10^30)
theorem v1980_pg_checked : Scalar.distance (sourceCoefficient 23 26 1 2) v1980_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1980_mb : Scalar.QComplex := ((-554326976496050025666835 : Int)/10^30,(-431477164448537196070227284 : Int)/10^30)
theorem v1980_mb_checked : Scalar.distance (sourceCoefficient 23 26 3 1) v1980_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1980_mg : Scalar.QComplex := ((-93086353026101207115796 : Int)/10^30,(119589820453075324917 : Int)/10^30)
theorem v1980_mg_checked : Scalar.distance (sourceCoefficient 23 26 3 2) v1980_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1980_upper : Scalar.QComplex := ((999997693750126767688219441677 : Int)/10^30,(-2147671862197795284292681555 : Int)/10^30)
theorem v1980_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 26 5) 1) 14) v1980_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1980 : Material (23 : Basis) (26 : Basis) where
  plus := ![v1980_pa,v1980_pb,v1980_pg]
  minus := ![(Primitive.Addresses.material1980 1).one,v1980_mb,v1980_mg]
  upper := v1980_upper
  lower := (Primitive.Addresses.material1980 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1980_pa_checked.trans (by decide +kernel)
    · exact v1980_pb_checked.trans (by decide +kernel)
    · exact v1980_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 26 Primitive.Addresses.material1980
    · exact v1980_mb_checked.trans (by decide +kernel)
    · exact v1980_mg_checked.trans (by decide +kernel)
  upper_error := v1980_upper_checked
  lower_error := reuse_lower_error 23 26 Primitive.Addresses.material1980

def v1981_pa : Scalar.QComplex := ((999999908917206961767250667149 : Int)/10^30,(-426808596188490926017611118 : Int)/10^30)
theorem v1981_pa_checked : Scalar.distance (sourceCoefficient 23 27 1 0) v1981_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1981_pb : Scalar.QComplex := ((-184158314796483129231826 : Int)/10^30,(-431477481164648020288622880 : Int)/10^30)
theorem v1981_pb_checked : Scalar.distance (sourceCoefficient 23 27 1 1) v1981_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1981_pg : Scalar.QComplex := ((-93086421360604702696870 : Int)/10^30,(39730088443857471754 : Int)/10^30)
theorem v1981_pg_checked : Scalar.distance (sourceCoefficient 23 27 1 2) v1981_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1981_mb : Scalar.QComplex := ((-556503879446653439011382 : Int)/10^30,(-431477161585530800877082268 : Int)/10^30)
theorem v1981_mb_checked : Scalar.distance (sourceCoefficient 23 27 3 1) v1981_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1981_mg : Scalar.QComplex := ((-93086352414998820232596 : Int)/10^30,(120059462827944877593 : Int)/10^30)
theorem v1981_mg_checked : Scalar.distance (sourceCoefficient 23 27 3 2) v1981_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1981_upper : Scalar.QComplex := ((999997682901893622631377079664 : Int)/10^30,(-2152717084015245759124788071 : Int)/10^30)
theorem v1981_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 27 5) 1) 14) v1981_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1981 : Material (23 : Basis) (27 : Basis) where
  plus := ![v1981_pa,v1981_pb,v1981_pg]
  minus := ![(Primitive.Addresses.material1981 1).one,v1981_mb,v1981_mg]
  upper := v1981_upper
  lower := (Primitive.Addresses.material1981 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1981_pa_checked.trans (by decide +kernel)
    · exact v1981_pb_checked.trans (by decide +kernel)
    · exact v1981_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 27 Primitive.Addresses.material1981
    · exact v1981_mb_checked.trans (by decide +kernel)
    · exact v1981_mg_checked.trans (by decide +kernel)
  upper_error := v1981_upper_checked
  lower_error := reuse_lower_error 23 27 Primitive.Addresses.material1981

def v1982_pa : Scalar.QComplex := ((999999905993269471363214019533 : Int)/10^30,(-433605180112055611587304836 : Int)/10^30)
theorem v1982_pa_checked : Scalar.distance (sourceCoefficient 23 28 1 0) v1982_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1982_pb : Scalar.QComplex := ((-187090887937426169683942 : Int)/10^30,(-431477479815333410223747099 : Int)/10^30)
theorem v1982_pb_checked : Scalar.distance (sourceCoefficient 23 28 1 1) v1982_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1982_pg : Scalar.QComplex := ((-93086421078965514146032 : Int)/10^30,(40362758172302422716 : Int)/10^30)
theorem v1982_pg_checked : Scalar.distance (sourceCoefficient 23 28 1 2) v1982_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1982_mb : Scalar.QComplex := ((-559436450331267736265012 : Int)/10^30,(-431477157705538150781153775 : Int)/10^30)
theorem v1982_mb_checked : Scalar.distance (sourceCoefficient 23 28 3 1) v1982_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1982_mg : Scalar.QComplex := ((-93086351587394255287714 : Int)/10^30,(120692132077776039059 : Int)/10^30)
theorem v1982_mg_checked : Scalar.distance (sourceCoefficient 23 28 3 2) v1982_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1982_upper : Scalar.QComplex := ((999997668247673216293192442304 : Int)/10^30,(-2159513652769646222475563583 : Int)/10^30)
theorem v1982_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 28 5) 1) 14) v1982_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1982 : Material (23 : Basis) (28 : Basis) where
  plus := ![v1982_pa,v1982_pb,v1982_pg]
  minus := ![(Primitive.Addresses.material1982 1).one,v1982_mb,v1982_mg]
  upper := v1982_upper
  lower := (Primitive.Addresses.material1982 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1982_pa_checked.trans (by decide +kernel)
    · exact v1982_pb_checked.trans (by decide +kernel)
    · exact v1982_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 28 Primitive.Addresses.material1982
    · exact v1982_mb_checked.trans (by decide +kernel)
    · exact v1982_mg_checked.trans (by decide +kernel)
  upper_error := v1982_upper_checked
  lower_error := reuse_lower_error 23 28 Primitive.Addresses.material1982

def v1983_pa : Scalar.QComplex := ((999999899929796781783932154168 : Int)/10^30,(-447370535934572431869229717 : Int)/10^30)
theorem v1983_pa_checked : Scalar.distance (sourceCoefficient 23 29 1 0) v1983_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1983_pb : Scalar.QComplex := ((-193030329446264603604137 : Int)/10^30,(-431477477001102349441770183 : Int)/10^30)
theorem v1983_pb_checked : Scalar.distance (sourceCoefficient 23 29 1 1) v1983_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1983_pg : Scalar.QComplex := ((-93086420493182627075893 : Int)/10^30,(41644125991602228927 : Int)/10^30)
theorem v1983_pg_checked : Scalar.distance (sourceCoefficient 23 29 1 2) v1983_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1983_mb : Scalar.QComplex := ((-565375887200025993365021 : Int)/10^30,(-431477149765837618253846969 : Int)/10^30)
theorem v1983_mb_checked : Scalar.distance (sourceCoefficient 23 29 3 1) v1983_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1983_mg : Scalar.QComplex := ((-93086349895848868939843 : Int)/10^30,(121973498914459795883 : Int)/10^30)
theorem v1983_mg_checked : Scalar.distance (sourceCoefficient 23 29 3 2) v1983_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1983_upper : Scalar.QComplex := ((999997638426454191205443088160 : Int)/10^30,(-2173278977625278749132726369 : Int)/10^30)
theorem v1983_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 29 5) 1) 14) v1983_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1983 : Material (23 : Basis) (29 : Basis) where
  plus := ![v1983_pa,v1983_pb,v1983_pg]
  minus := ![(Primitive.Addresses.material1983 1).one,v1983_mb,v1983_mg]
  upper := v1983_upper
  lower := (Primitive.Addresses.material1983 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1983_pa_checked.trans (by decide +kernel)
    · exact v1983_pb_checked.trans (by decide +kernel)
    · exact v1983_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 29 Primitive.Addresses.material1983
    · exact v1983_mb_checked.trans (by decide +kernel)
    · exact v1983_mg_checked.trans (by decide +kernel)
  upper_error := v1983_upper_checked
  lower_error := reuse_lower_error 23 29 Primitive.Addresses.material1983

def v1984_pa : Scalar.QComplex := ((999999897582574044203974775515 : Int)/10^30,(-452586833019104645536212106 : Int)/10^30)
theorem v1984_pa_checked : Scalar.distance (sourceCoefficient 23 30 1 0) v1984_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1984_pb : Scalar.QComplex := ((-195281044339639302769947 : Int)/10^30,(-431477475906185232106323771 : Int)/10^30)
theorem v1984_pb_checked : Scalar.distance (sourceCoefficient 23 30 1 1) v1984_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1984_pg : Scalar.QComplex := ((-93086420265827298378271 : Int)/10^30,(42129692460010836225 : Int)/10^30)
theorem v1984_pg_checked : Scalar.distance (sourceCoefficient 23 30 1 2) v1984_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1984_mb : Scalar.QComplex := ((-567626600310492515951160 : Int)/10^30,(-431477146728655324059542524 : Int)/10^30)
theorem v1984_mb_checked : Scalar.distance (sourceCoefficient 23 30 3 1) v1984_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1984_mg : Scalar.QComplex := ((-93086349249471631762291 : Int)/10^30,(122459065005872406547 : Int)/10^30)
theorem v1984_mg_checked : Scalar.distance (sourceCoefficient 23 30 3 2) v1984_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1984_upper : Scalar.QComplex := ((999997627076379400410354949503 : Int)/10^30,(-2178495262889655698008179704 : Int)/10^30)
theorem v1984_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 30 5) 1) 14) v1984_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1984 : Material (23 : Basis) (30 : Basis) where
  plus := ![v1984_pa,v1984_pb,v1984_pg]
  minus := ![(Primitive.Addresses.material1984 1).one,v1984_mb,v1984_mg]
  upper := v1984_upper
  lower := (Primitive.Addresses.material1984 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1984_pa_checked.trans (by decide +kernel)
    · exact v1984_pb_checked.trans (by decide +kernel)
    · exact v1984_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 30 Primitive.Addresses.material1984
    · exact v1984_mb_checked.trans (by decide +kernel)
    · exact v1984_mg_checked.trans (by decide +kernel)
  upper_error := v1984_upper_checked
  lower_error := reuse_lower_error 23 30 Primitive.Addresses.material1984

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
