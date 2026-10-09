import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B042

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1009_pa : Scalar.QComplex := ((999998987664259085357274240039 : Int)/10^30,(-1422909152759104687291040854 : Int)/10^30)
theorem v1009_pa_checked : Scalar.distance (sourceCoefficient 10 95 1 0) v1009_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1009_pb : Scalar.QComplex := ((-613953074457414568296389 : Int)/10^30,(-431476915964932876656300425 : Int)/10^30)
theorem v1009_pb_checked : Scalar.distance (sourceCoefficient 10 95 1 1) v1009_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1009_pg : Scalar.QComplex := ((-93086317514784360825776 : Int)/10^30,(132453507275846247110 : Int)/10^30)
theorem v1009_pg_checked : Scalar.distance (sourceCoefficient 10 95 1 2) v1009_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1009_mb : Scalar.QComplex := ((-986297991333454746688210 : Int)/10^30,(-431476225492505756946478081 : Int)/10^30)
theorem v1009_mb_checked : Scalar.distance (sourceCoefficient 10 95 3 1) v1009_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1009_mg : Scalar.QComplex := ((-93086168553082800659877 : Int)/10^30,(212782757520501239309 : Int)/10^30)
theorem v1009_mg_checked : Scalar.distance (sourceCoefficient 10 95 3 2) v1009_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1009_upper : Scalar.QComplex := ((999995042471122739985190132601 : Int)/10^30,(-3148814567012078079253827754 : Int)/10^30)
theorem v1009_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 95 5) 1) 14) v1009_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1009 : Material (10 : Basis) (95 : Basis) where
  plus := ![v1009_pa,v1009_pb,v1009_pg]
  minus := ![(Primitive.Addresses.material1009 1).one,v1009_mb,v1009_mg]
  upper := v1009_upper
  lower := (Primitive.Addresses.material1009 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1009_pa_checked.trans (by decide +kernel)
    · exact v1009_pb_checked.trans (by decide +kernel)
    · exact v1009_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 95 Primitive.Addresses.material1009
    · exact v1009_mb_checked.trans (by decide +kernel)
    · exact v1009_mg_checked.trans (by decide +kernel)
  upper_error := v1009_upper_checked
  lower_error := reuse_lower_error 10 95 Primitive.Addresses.material1009

def v1010_pa : Scalar.QComplex := ((999998957181300666465753675749 : Int)/10^30,(-1444173227558324740240000430 : Int)/10^30)
theorem v1010_pa_checked : Scalar.distance (sourceCoefficient 10 96 1 0) v1010_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1010_pb : Scalar.QComplex := ((-623128034358297251006375 : Int)/10^30,(-431476898101938512236850212 : Int)/10^30)
theorem v1010_pb_checked : Scalar.distance (sourceCoefficient 10 96 1 1) v1010_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1010_pg : Scalar.QComplex := ((-93086314169139218237737 : Int)/10^30,(134432902964299017655 : Int)/10^30)
theorem v1010_pg_checked : Scalar.distance (sourceCoefficient 10 96 1 2) v1010_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1010_mb : Scalar.QComplex := ((-995472932403120924824477 : Int)/10^30,(-431476199711940874128761854 : Int)/10^30)
theorem v1010_mb_checked : Scalar.distance (sourceCoefficient 10 96 3 1) v1010_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1010_mg : Scalar.QComplex := ((-93086163499309573346140 : Int)/10^30,(214762149584793456400 : Int)/10^30)
theorem v1010_mg_checked : Scalar.distance (sourceCoefficient 10 96 3 2) v1010_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1010_upper : Scalar.QComplex := ((999994975288345680222424734812 : Int)/10^30,(-3170078557530135733834024023 : Int)/10^30)
theorem v1010_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 96 5) 1) 14) v1010_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1010 : Material (10 : Basis) (96 : Basis) where
  plus := ![v1010_pa,v1010_pb,v1010_pg]
  minus := ![(Primitive.Addresses.material1010 1).one,v1010_mb,v1010_mg]
  upper := v1010_upper
  lower := (Primitive.Addresses.material1010 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1010_pa_checked.trans (by decide +kernel)
    · exact v1010_pb_checked.trans (by decide +kernel)
    · exact v1010_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 96 Primitive.Addresses.material1010
    · exact v1010_mb_checked.trans (by decide +kernel)
    · exact v1010_mg_checked.trans (by decide +kernel)
  upper_error := v1010_upper_checked
  lower_error := reuse_lower_error 10 96 Primitive.Addresses.material1010

def v1011_pa : Scalar.QComplex := ((999998848846023931313106920605 : Int)/10^30,(-1517335370635607758556316259 : Int)/10^30)
theorem v1011_pa_checked : Scalar.distance (sourceCoefficient 10 97 1 0) v1011_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1011_pb : Scalar.QComplex := ((-654695816486833187115792 : Int)/10^30,(-431476834654484393268104134 : Int)/10^30)
theorem v1011_pb_checked : Scalar.distance (sourceCoefficient 10 97 1 1) v1011_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1011_pg : Scalar.QComplex := ((-93086302282829139201369 : Int)/10^30,(141243301568202965829 : Int)/10^30)
theorem v1011_pg_checked : Scalar.distance (sourceCoefficient 10 97 1 2) v1011_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1011_mb : Scalar.QComplex := ((-1027040648025233518150538 : Int)/10^30,(-431476109022936162749215720 : Int)/10^30)
theorem v1011_mb_checked : Scalar.distance (sourceCoefficient 10 97 3 1) v1011_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1011_mg : Scalar.QComplex := ((-93086145735936653923944 : Int)/10^30,(221572535395524495073 : Int)/10^30)
theorem v1011_mg_checked : Scalar.distance (sourceCoefficient 10 97 3 2) v1011_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1011_upper : Scalar.QComplex := ((999994740682008564120900979829 : Int)/10^30,(-3243240404664141322233848662 : Int)/10^30)
theorem v1011_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 97 5) 1) 14) v1011_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1011 : Material (10 : Basis) (97 : Basis) where
  plus := ![v1011_pa,v1011_pb,v1011_pg]
  minus := ![(Primitive.Addresses.material1011 1).one,v1011_mb,v1011_mg]
  upper := v1011_upper
  lower := (Primitive.Addresses.material1011 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1011_pa_checked.trans (by decide +kernel)
    · exact v1011_pb_checked.trans (by decide +kernel)
    · exact v1011_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 97 Primitive.Addresses.material1011
    · exact v1011_mb_checked.trans (by decide +kernel)
    · exact v1011_mg_checked.trans (by decide +kernel)
  upper_error := v1011_upper_checked
  lower_error := reuse_lower_error 10 97 Primitive.Addresses.material1011

def v1012_pa : Scalar.QComplex := ((999999996500076551652510706846 : Int)/10^30,(83665087607947405065245112 : Int)/10^30)
theorem v1012_pa_checked : Scalar.distance (sourceCoefficient 11 12 1 0) v1012_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1012_pb : Scalar.QComplex := ((36099604595233855207170 : Int)/10^30,(-431477519488772709828779347 : Int)/10^30)
theorem v1012_pb_checked : Scalar.distance (sourceCoefficient 11 12 1 1) v1012_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1012_pg : Scalar.QComplex := ((-93086429570992798595502 : Int)/10^30,(-7788084312425837378 : Int)/10^30)
theorem v1012_pg_checked : Scalar.distance (sourceCoefficient 11 12 1 2) v1012_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1012_mb : Scalar.QComplex := ((-336246075139019680880643 : Int)/10^30,(-431477389982305607205980241 : Int)/10^30)
theorem v1012_mb_checked : Scalar.distance (sourceCoefficient 11 12 3 1) v1012_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1012_mg : Scalar.QComplex := ((-93086401631426808645755 : Int)/10^30,(72541314850044118012 : Int)/10^30)
theorem v1012_mg_checked : Scalar.distance (sourceCoefficient 11 12 3 2) v1012_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1012_upper : Scalar.QComplex := ((999998651515901189931526023587 : Int)/10^30,(-1642244311669482447944404683 : Int)/10^30)
theorem v1012_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 12 5) 1) 14) v1012_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1012 : Material (11 : Basis) (12 : Basis) where
  plus := ![v1012_pa,v1012_pb,v1012_pg]
  minus := ![(Primitive.Addresses.material1012 1).one,v1012_mb,v1012_mg]
  upper := v1012_upper
  lower := (Primitive.Addresses.material1012 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1012_pa_checked.trans (by decide +kernel)
    · exact v1012_pb_checked.trans (by decide +kernel)
    · exact v1012_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 12 Primitive.Addresses.material1012
    · exact v1012_mb_checked.trans (by decide +kernel)
    · exact v1012_mg_checked.trans (by decide +kernel)
  upper_error := v1012_upper_checked
  lower_error := reuse_lower_error 11 12 Primitive.Addresses.material1012

def v1013_pa : Scalar.QComplex := ((999999999483191859779130513586 : Int)/10^30,(32149903268511529364956562 : Int)/10^30)
theorem v1013_pa_checked : Scalar.distance (sourceCoefficient 11 13 1 0) v1013_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1013_pb : Scalar.QComplex := ((13871960555344259368455 : Int)/10^30,(-431477520548613422053646147 : Int)/10^30)
theorem v1013_pb_checked : Scalar.distance (sourceCoefficient 11 13 1 1) v1013_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1013_pg : Scalar.QComplex := ((-93086429824160941937307 : Int)/10^30,(-2992719716004522886 : Int)/10^30)
theorem v1013_pg_checked : Scalar.distance (sourceCoefficient 11 13 1 2) v1013_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1013_mb : Scalar.QComplex := ((-358473711817136348347987 : Int)/10^30,(-431477371860690214304120609 : Int)/10^30)
theorem v1013_mb_checked : Scalar.distance (sourceCoefficient 11 13 3 1) v1013_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1013_mg : Scalar.QComplex := ((-93086397746411186213942 : Int)/10^30,(77336677879404739703 : Int)/10^30)
theorem v1013_mg_checked : Scalar.distance (sourceCoefficient 11 13 3 2) v1013_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1013_upper : Scalar.QComplex := ((999998565588477306208506330871 : Int)/10^30,(-1693759424431689044414843746 : Int)/10^30)
theorem v1013_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 13 5) 1) 14) v1013_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1013 : Material (11 : Basis) (13 : Basis) where
  plus := ![v1013_pa,v1013_pb,v1013_pg]
  minus := ![(Primitive.Addresses.material1013 1).one,v1013_mb,v1013_mg]
  upper := v1013_upper
  lower := (Primitive.Addresses.material1013 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1013_pa_checked.trans (by decide +kernel)
    · exact v1013_pb_checked.trans (by decide +kernel)
    · exact v1013_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 13 Primitive.Addresses.material1013
    · exact v1013_mb_checked.trans (by decide +kernel)
    · exact v1013_mg_checked.trans (by decide +kernel)
  upper_error := v1013_upper_checked
  lower_error := reuse_lower_error 11 13 Primitive.Addresses.material1013

def v1014_pa : Scalar.QComplex := ((999999999874554000388387805572 : Int)/10^30,(15839570676236388763788840 : Int)/10^30)
theorem v1014_pa_checked : Scalar.distance (sourceCoefficient 11 14 1 0) v1014_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1014_pb : Scalar.QComplex := ((6834418683069038503624 : Int)/10^30,(-431477520565955242464730302 : Int)/10^30)
theorem v1014_pb_checked : Scalar.distance (sourceCoefficient 11 14 1 1) v1014_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1014_pg : Scalar.QComplex := ((-93086429844246845827440 : Int)/10^30,(-1474449084701431912 : Int)/10^30)
theorem v1014_pg_checked : Scalar.distance (sourceCoefficient 11 14 1 2) v1014_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1014_mb : Scalar.QComplex := ((-365511251083978308580438 : Int)/10^30,(-431477365804950351604388536 : Int)/10^30)
theorem v1014_mb_checked : Scalar.distance (sourceCoefficient 11 14 3 1) v1014_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1014_mg : Scalar.QComplex := ((-93086396456297908181443 : Int)/10^30,(78854947962719516668 : Int)/10^30)
theorem v1014_mg_checked : Scalar.distance (sourceCoefficient 11 14 3 2) v1014_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1014_upper : Scalar.QComplex := ((999998537829684471477222552726 : Int)/10^30,(-1710069733407095285671886705 : Int)/10^30)
theorem v1014_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 14 5) 1) 14) v1014_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1014 : Material (11 : Basis) (14 : Basis) where
  plus := ![v1014_pa,v1014_pb,v1014_pg]
  minus := ![(Primitive.Addresses.material1014 1).one,v1014_mb,v1014_mg]
  upper := v1014_upper
  lower := (Primitive.Addresses.material1014 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1014_pa_checked.trans (by decide +kernel)
    · exact v1014_pb_checked.trans (by decide +kernel)
    · exact v1014_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 14 Primitive.Addresses.material1014
    · exact v1014_mb_checked.trans (by decide +kernel)
    · exact v1014_mg_checked.trans (by decide +kernel)
  upper_error := v1014_upper_checked
  lower_error := reuse_lower_error 11 14 Primitive.Addresses.material1014

def v1015_pa : Scalar.QComplex := ((999999999945517720768439020103 : Int)/10^30,(-10438609028992016091577303 : Int)/10^30)
theorem v1015_pa_checked : Scalar.distance (sourceCoefficient 11 15 1 0) v1015_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1015_pb : Scalar.QComplex := ((-4504025139163464593302 : Int)/10^30,(-431477520271970319716463510 : Int)/10^30)
theorem v1015_pb_checked : Scalar.distance (sourceCoefficient 11 15 1 1) v1015_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1015_pg : Scalar.QComplex := ((-93086429815837752940038 : Int)/10^30,(971692846805175623 : Int)/10^30)
theorem v1015_pg_checked : Scalar.distance (sourceCoefficient 11 15 1 2) v1015_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1015_mb : Scalar.QComplex := ((-376849690430694236435951 : Int)/10^30,(-431477355726399184286488159 : Int)/10^30)
theorem v1015_mb_checked : Scalar.distance (sourceCoefficient 11 15 3 1) v1015_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1015_mg : Scalar.QComplex := ((-93086394316978509124730 : Int)/10^30,(81301088958899921230 : Int)/10^30)
theorem v1015_mg_checked : Scalar.distance (sourceCoefficient 11 15 3 2) v1015_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1015_upper : Scalar.QComplex := ((999998492546893852781479337315 : Int)/10^30,(-1736347874096538815014778773 : Int)/10^30)
theorem v1015_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 15 5) 1) 14) v1015_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1015 : Material (11 : Basis) (15 : Basis) where
  plus := ![v1015_pa,v1015_pb,v1015_pg]
  minus := ![(Primitive.Addresses.material1015 1).one,v1015_mb,v1015_mg]
  upper := v1015_upper
  lower := (Primitive.Addresses.material1015 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1015_pa_checked.trans (by decide +kernel)
    · exact v1015_pb_checked.trans (by decide +kernel)
    · exact v1015_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 15 Primitive.Addresses.material1015
    · exact v1015_mb_checked.trans (by decide +kernel)
    · exact v1015_mg_checked.trans (by decide +kernel)
  upper_error := v1015_upper_checked
  lower_error := reuse_lower_error 11 15 Primitive.Addresses.material1015

def v1016_pa : Scalar.QComplex := ((999999999905178857908303867503 : Int)/10^30,(-13771066922152445048237852 : Int)/10^30)
theorem v1016_pa_checked : Scalar.distance (sourceCoefficient 11 16 1 0) v1016_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1016_pb : Scalar.QComplex := ((-5941905806728819383442 : Int)/10^30,(-431477520206304351969005835 : Int)/10^30)
theorem v1016_pb_checked : Scalar.distance (sourceCoefficient 11 16 1 1) v1016_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1016_pg : Scalar.QComplex := ((-93086429806876905047734 : Int)/10^30,(1281899454536299131 : Int)/10^30)
theorem v1016_pg_checked : Scalar.distance (sourceCoefficient 11 16 1 2) v1016_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1016_mb : Scalar.QComplex := ((-378287570506204131617989 : Int)/10^30,(-431477354419906984621842723 : Int)/10^30)
theorem v1016_mb_checked : Scalar.distance (sourceCoefficient 11 16 3 1) v1016_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1016_mg : Scalar.QComplex := ((-93086394040323333283976 : Int)/10^30,(81611295443394139388 : Int)/10^30)
theorem v1016_mg_checked : Scalar.distance (sourceCoefficient 11 16 3 2) v1016_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1016_upper : Scalar.QComplex := ((999998486755035044624928691017 : Int)/10^30,(-1739680326956773452327994741 : Int)/10^30)
theorem v1016_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 16 5) 1) 14) v1016_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1016 : Material (11 : Basis) (16 : Basis) where
  plus := ![v1016_pa,v1016_pb,v1016_pg]
  minus := ![(Primitive.Addresses.material1016 1).one,v1016_mb,v1016_mg]
  upper := v1016_upper
  lower := (Primitive.Addresses.material1016 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1016_pa_checked.trans (by decide +kernel)
    · exact v1016_pb_checked.trans (by decide +kernel)
    · exact v1016_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 16 Primitive.Addresses.material1016
    · exact v1016_mb_checked.trans (by decide +kernel)
    · exact v1016_mg_checked.trans (by decide +kernel)
  upper_error := v1016_upper_checked
  lower_error := reuse_lower_error 11 16 Primitive.Addresses.material1016

def v1017_pa : Scalar.QComplex := ((999999999790642837752480283312 : Int)/10^30,(-20462510218719721191436375 : Int)/10^30)
theorem v1017_pa_checked : Scalar.distance (sourceCoefficient 11 17 1 0) v1017_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1017_pb : Scalar.QComplex := ((-8829113165124903769698 : Int)/10^30,(-431477520055155638553076823 : Int)/10^30)
theorem v1017_pb_checked : Scalar.distance (sourceCoefficient 11 17 1 1) v1017_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1017_pg : Scalar.QComplex := ((-93086429785241711739693 : Int)/10^30,(1904782021103424107 : Int)/10^30)
theorem v1017_pg_checked : Scalar.distance (sourceCoefficient 11 17 1 2) v1017_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1017_mb : Scalar.QComplex := ((-381174776659126432385948 : Int)/10^30,(-431477351777228412181963072 : Int)/10^30)
theorem v1017_mb_checked : Scalar.distance (sourceCoefficient 11 17 3 1) v1017_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1017_mg : Scalar.QComplex := ((-93086393481168546673677 : Int)/10^30,(82234177759363420280 : Int)/10^30)
theorem v1017_mg_checked : Scalar.distance (sourceCoefficient 11 17 3 2) v1017_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1017_upper : Scalar.QComplex := ((999998475091675108175839105743 : Int)/10^30,(-1746371760089543190217226813 : Int)/10^30)
theorem v1017_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 17 5) 1) 14) v1017_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1017 : Material (11 : Basis) (17 : Basis) where
  plus := ![v1017_pa,v1017_pb,v1017_pg]
  minus := ![(Primitive.Addresses.material1017 1).one,v1017_mb,v1017_mg]
  upper := v1017_upper
  lower := (Primitive.Addresses.material1017 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1017_pa_checked.trans (by decide +kernel)
    · exact v1017_pb_checked.trans (by decide +kernel)
    · exact v1017_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 17 Primitive.Addresses.material1017
    · exact v1017_mb_checked.trans (by decide +kernel)
    · exact v1017_mg_checked.trans (by decide +kernel)
  upper_error := v1017_upper_checked
  lower_error := reuse_lower_error 11 17 Primitive.Addresses.material1017

def v1018_pa : Scalar.QComplex := ((999999999084823741087362248273 : Int)/10^30,(-42782619332945568476357840 : Int)/10^30)
theorem v1018_pa_checked : Scalar.distance (sourceCoefficient 11 18 1 0) v1018_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1018_pb : Scalar.QComplex := ((-18459738478598156539883 : Int)/10^30,(-431477519364714772811822550 : Int)/10^30)
theorem v1018_pb_checked : Scalar.distance (sourceCoefficient 11 18 1 1) v1018_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1018_pg : Scalar.QComplex := ((-93086429677913190422808 : Int)/10^30,(3982481289617839315 : Int)/10^30)
theorem v1018_pg_checked : Scalar.distance (sourceCoefficient 11 18 1 2) v1018_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1018_mb : Scalar.QComplex := ((-390805397790858368797334 : Int)/10^30,(-431477342775991905258644270 : Int)/10^30)
theorem v1018_mb_checked : Scalar.distance (sourceCoefficient 11 18 3 1) v1018_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1018_mg : Scalar.QComplex := ((-93086391580879172693511 : Int)/10^30,(84311876161635762273 : Int)/10^30)
theorem v1018_mg_checked : Scalar.distance (sourceCoefficient 11 18 3 2) v1018_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1018_upper : Scalar.QComplex := ((999998435863373596073011075952 : Int)/10^30,(-1768691834742408686622299872 : Int)/10^30)
theorem v1018_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 18 5) 1) 14) v1018_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1018 : Material (11 : Basis) (18 : Basis) where
  plus := ![v1018_pa,v1018_pb,v1018_pg]
  minus := ![(Primitive.Addresses.material1018 1).one,v1018_mb,v1018_mg]
  upper := v1018_upper
  lower := (Primitive.Addresses.material1018 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1018_pa_checked.trans (by decide +kernel)
    · exact v1018_pb_checked.trans (by decide +kernel)
    · exact v1018_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 18 Primitive.Addresses.material1018
    · exact v1018_mb_checked.trans (by decide +kernel)
    · exact v1018_mg_checked.trans (by decide +kernel)
  upper_error := v1018_upper_checked
  lower_error := reuse_lower_error 11 18 Primitive.Addresses.material1018

def v1019_pa : Scalar.QComplex := ((999999998292717982008013535575 : Int)/10^30,(-58434271049352203242650453 : Int)/10^30)
theorem v1019_pa_checked : Scalar.distance (sourceCoefficient 11 19 1 0) v1019_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1019_pb : Scalar.QComplex := ((-25213074323024285470095 : Int)/10^30,(-431477518709595792888547972 : Int)/10^30)
theorem v1019_pb_checked : Scalar.distance (sourceCoefficient 11 19 1 1) v1019_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1019_pg : Scalar.QComplex := ((-93086429570378760465252 : Int)/10^30,(5439437665818600568 : Int)/10^30)
theorem v1019_pg_checked : Scalar.distance (sourceCoefficient 11 19 1 2) v1019_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1019_mb : Scalar.QComplex := ((-397558730555370745942125 : Int)/10^30,(-431477336293048494481878858 : Int)/10^30)
theorem v1019_mb_checked : Scalar.distance (sourceCoefficient 11 19 3 1) v1019_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1019_mg : Scalar.QComplex := ((-93086390216057048993978 : Int)/10^30,(85768831902547708588 : Int)/10^30)
theorem v1019_mg_checked : Scalar.distance (sourceCoefficient 11 19 3 2) v1019_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1019_upper : Scalar.QComplex := ((999998408057938060976301184662 : Int)/10^30,(-1784343461780415981066343379 : Int)/10^30)
theorem v1019_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 19 5) 1) 14) v1019_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1019 : Material (11 : Basis) (19 : Basis) where
  plus := ![v1019_pa,v1019_pb,v1019_pg]
  minus := ![(Primitive.Addresses.material1019 1).one,v1019_mb,v1019_mg]
  upper := v1019_upper
  lower := (Primitive.Addresses.material1019 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1019_pa_checked.trans (by decide +kernel)
    · exact v1019_pb_checked.trans (by decide +kernel)
    · exact v1019_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 19 Primitive.Addresses.material1019
    · exact v1019_mb_checked.trans (by decide +kernel)
    · exact v1019_mg_checked.trans (by decide +kernel)
  upper_error := v1019_upper_checked
  lower_error := reuse_lower_error 11 19 Primitive.Addresses.material1019

def v1020_pa : Scalar.QComplex := ((999999998124849316279622440730 : Int)/10^30,(-61239704146285398525792323 : Int)/10^30)
theorem v1020_pa_checked : Scalar.distance (sourceCoefficient 11 20 1 0) v1020_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1020_pb : Scalar.QComplex := ((-26423555632993912746538 : Int)/10^30,(-431477518577276329993516536 : Int)/10^30)
theorem v1020_pb_checked : Scalar.distance (sourceCoefficient 11 20 1 1) v1020_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1020_pg : Scalar.QComplex := ((-93086429548292394006687 : Int)/10^30,(5700585416260921999 : Int)/10^30)
theorem v1020_pg_checked : Scalar.distance (sourceCoefficient 11 20 1 2) v1020_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1020_mb : Scalar.QComplex := ((-398769211300437122757034 : Int)/10^30,(-431477335116138228406038138 : Int)/10^30)
theorem v1020_mb_checked : Scalar.distance (sourceCoefficient 11 20 3 1) v1020_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1020_mg : Scalar.QComplex := ((-93086389968611943785520 : Int)/10^30,(86029979536693247967 : Int)/10^30)
theorem v1020_mg_checked : Scalar.distance (sourceCoefficient 11 20 3 2) v1020_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1020_upper : Scalar.QComplex := ((999998403048146626864328356039 : Int)/10^30,(-1787148890409260039667823851 : Int)/10^30)
theorem v1020_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 20 5) 1) 14) v1020_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1020 : Material (11 : Basis) (20 : Basis) where
  plus := ![v1020_pa,v1020_pb,v1020_pg]
  minus := ![(Primitive.Addresses.material1020 1).one,v1020_mb,v1020_mg]
  upper := v1020_upper
  lower := (Primitive.Addresses.material1020 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1020_pa_checked.trans (by decide +kernel)
    · exact v1020_pb_checked.trans (by decide +kernel)
    · exact v1020_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 20 Primitive.Addresses.material1020
    · exact v1020_mb_checked.trans (by decide +kernel)
    · exact v1020_mg_checked.trans (by decide +kernel)
  upper_error := v1020_upper_checked
  lower_error := reuse_lower_error 11 20 Primitive.Addresses.material1020

def v1021_pa : Scalar.QComplex := ((999999993473637060491780144471 : Int)/10^30,(-114248526626924281280606777 : Int)/10^30)
theorem v1021_pa_checked : Scalar.distance (sourceCoefficient 11 21 1 0) v1021_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1021_pb : Scalar.QComplex := ((-49295670708941913931098 : Int)/10^30,(-431477515226032276479755465 : Int)/10^30)
theorem v1021_pb_checked : Scalar.distance (sourceCoefficient 11 21 1 1) v1021_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1021_pg : Scalar.QComplex := ((-93086428970313387465917 : Int)/10^30,(10634987428227932669 : Int)/10^30)
theorem v1021_pg_checked : Scalar.distance (sourceCoefficient 11 21 1 2) v1021_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1021_mb : Scalar.QComplex := ((-421641314968078690114799 : Int)/10^30,(-431477312027290233993573730 : Int)/10^30)
theorem v1021_mb_checked : Scalar.distance (sourceCoefficient 11 21 3 1) v1021_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1021_mg : Scalar.QComplex := ((-93086385132466453342005 : Int)/10^30,(90964379212587024833 : Int)/10^30)
theorem v1021_mg_checked : Scalar.distance (sourceCoefficient 11 21 3 2) v1021_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1021_upper : Scalar.QComplex := ((999998306908522619738259735301 : Int)/10^30,(-1840157625911914292402113858 : Int)/10^30)
theorem v1021_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 21 5) 1) 14) v1021_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1021 : Material (11 : Basis) (21 : Basis) where
  plus := ![v1021_pa,v1021_pb,v1021_pg]
  minus := ![(Primitive.Addresses.material1021 1).one,v1021_mb,v1021_mg]
  upper := v1021_upper
  lower := (Primitive.Addresses.material1021 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1021_pa_checked.trans (by decide +kernel)
    · exact v1021_pb_checked.trans (by decide +kernel)
    · exact v1021_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 21 Primitive.Addresses.material1021
    · exact v1021_mb_checked.trans (by decide +kernel)
    · exact v1021_mg_checked.trans (by decide +kernel)
  upper_error := v1021_upper_checked
  lower_error := reuse_lower_error 11 21 Primitive.Addresses.material1021

def v1022_pa : Scalar.QComplex := ((999999993313391653389832942945 : Int)/10^30,(-115642624704343350238460229 : Int)/10^30)
theorem v1022_pa_checked : Scalar.distance (sourceCoefficient 11 22 1 0) v1022_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1022_pb : Scalar.QComplex := ((-49897192682574498257592 : Int)/10^30,(-431477515116080335953358157 : Int)/10^30)
theorem v1022_pb_checked : Scalar.distance (sourceCoefficient 11 22 1 1) v1022_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1022_pg : Scalar.QComplex := ((-93086428950994602839654 : Int)/10^30,(10764759040227118159 : Int)/10^30)
theorem v1022_pg_checked : Scalar.distance (sourceCoefficient 11 22 1 2) v1022_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1022_mb : Scalar.QComplex := ((-422242836622853580122900 : Int)/10^30,(-431477311398251962706395683 : Int)/10^30)
theorem v1022_mb_checked : Scalar.distance (sourceCoefficient 11 22 3 1) v1022_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1022_mg : Scalar.QComplex := ((-93086385001160619450150 : Int)/10^30,(91094150759595067273 : Int)/10^30)
theorem v1022_mg_checked : Scalar.distance (sourceCoefficient 11 22 3 2) v1022_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1022_upper : Scalar.QComplex := ((999998304342190641267351259370 : Int)/10^30,(-1841551721636419001999921224 : Int)/10^30)
theorem v1022_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 22 5) 1) 14) v1022_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1022 : Material (11 : Basis) (22 : Basis) where
  plus := ![v1022_pa,v1022_pb,v1022_pg]
  minus := ![(Primitive.Addresses.material1022 1).one,v1022_mb,v1022_mg]
  upper := v1022_upper
  lower := (Primitive.Addresses.material1022 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1022_pa_checked.trans (by decide +kernel)
    · exact v1022_pb_checked.trans (by decide +kernel)
    · exact v1022_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 22 Primitive.Addresses.material1022
    · exact v1022_mb_checked.trans (by decide +kernel)
    · exact v1022_mg_checked.trans (by decide +kernel)
  upper_error := v1022_upper_checked
  lower_error := reuse_lower_error 11 22 Primitive.Addresses.material1022

def v1023_pa : Scalar.QComplex := ((999999992068125972007608655614 : Int)/10^30,(-125951371541044193159683692 : Int)/10^30)
theorem v1023_pa_checked : Scalar.distance (sourceCoefficient 11 23 1 0) v1023_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1023_pb : Scalar.QComplex := ((-54345185142275910628812 : Int)/10^30,(-431477514268330945587729093 : Int)/10^30)
theorem v1023_pb_checked : Scalar.distance (sourceCoefficient 11 23 1 1) v1023_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1023_pg : Scalar.QComplex := ((-93086428801589729223467 : Int)/10^30,(11724363472414159262 : Int)/10^30)
theorem v1023_pg_checked : Scalar.distance (sourceCoefficient 11 23 1 2) v1023_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1023_mb : Scalar.QComplex := ((-426690826694794573779128 : Int)/10^30,(-431477306712085725418070291 : Int)/10^30)
theorem v1023_mb_checked : Scalar.distance (sourceCoefficient 11 23 3 1) v1023_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1023_mg : Scalar.QComplex := ((-93086384023660395466071 : Int)/10^30,(92053754705547845198 : Int)/10^30)
theorem v1023_mg_checked : Scalar.distance (sourceCoefficient 11 23 3 2) v1023_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1023_upper : Scalar.QComplex := ((999998285304964976624052089363 : Int)/10^30,(-1851860450970236785677734498 : Int)/10^30)
theorem v1023_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 23 5) 1) 14) v1023_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1023 : Material (11 : Basis) (23 : Basis) where
  plus := ![v1023_pa,v1023_pb,v1023_pg]
  minus := ![(Primitive.Addresses.material1023 1).one,v1023_mb,v1023_mg]
  upper := v1023_upper
  lower := (Primitive.Addresses.material1023 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1023_pa_checked.trans (by decide +kernel)
    · exact v1023_pb_checked.trans (by decide +kernel)
    · exact v1023_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 23 Primitive.Addresses.material1023
    · exact v1023_mb_checked.trans (by decide +kernel)
    · exact v1023_mg_checked.trans (by decide +kernel)
  upper_error := v1023_upper_checked
  lower_error := reuse_lower_error 11 23 Primitive.Addresses.material1023

def v1024_pa : Scalar.QComplex := ((999999984353664134155112473354 : Int)/10^30,(-176897347314429644689925611 : Int)/10^30)
theorem v1024_pa_checked : Scalar.distance (sourceCoefficient 11 24 1 0) v1024_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1024_pb : Scalar.QComplex := ((-76327227994210525395421 : Int)/10^30,(-431477509181071893551835587 : Int)/10^30)
theorem v1024_pb_checked : Scalar.distance (sourceCoefficient 11 24 1 1) v1024_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1024_pg : Scalar.QComplex := ((-93086427893774368433731 : Int)/10^30,(16466742423028798608 : Int)/10^30)
theorem v1024_pg_checked : Scalar.distance (sourceCoefficient 11 24 1 2) v1024_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1024_mb : Scalar.QComplex := ((-448672856971734565517799 : Int)/10^30,(-431477282655315620839893050 : Int)/10^30)
theorem v1024_mb_checked : Scalar.distance (sourceCoefficient 11 24 3 1) v1024_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1024_mg : Scalar.QComplex := ((-93086379023385927136195 : Int)/10^30,(96796131106954293930 : Int)/10^30)
theorem v1024_mg_checked : Scalar.distance (sourceCoefficient 11 24 3 2) v1024_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1024_upper : Scalar.QComplex := ((999998189662382226511745145976 : Int)/10^30,(-1902806337551114575832911905 : Int)/10^30)
theorem v1024_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 24 5) 1) 14) v1024_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1024 : Material (11 : Basis) (24 : Basis) where
  plus := ![v1024_pa,v1024_pb,v1024_pg]
  minus := ![(Primitive.Addresses.material1024 1).one,v1024_mb,v1024_mg]
  upper := v1024_upper
  lower := (Primitive.Addresses.material1024 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1024_pa_checked.trans (by decide +kernel)
    · exact v1024_pb_checked.trans (by decide +kernel)
    · exact v1024_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 24 Primitive.Addresses.material1024
    · exact v1024_mb_checked.trans (by decide +kernel)
    · exact v1024_mg_checked.trans (by decide +kernel)
  upper_error := v1024_upper_checked
  lower_error := reuse_lower_error 11 24 Primitive.Addresses.material1024

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
