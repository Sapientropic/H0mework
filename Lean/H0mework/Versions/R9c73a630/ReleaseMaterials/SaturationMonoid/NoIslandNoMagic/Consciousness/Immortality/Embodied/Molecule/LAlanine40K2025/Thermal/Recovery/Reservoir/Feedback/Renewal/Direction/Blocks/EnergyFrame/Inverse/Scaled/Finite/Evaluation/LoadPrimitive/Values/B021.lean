import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B014

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v337_pa : Scalar.QComplex := ((999994007451487717013255475760 : Int)/10^30,(3461944701165560417913696848 : Int)/10^30)
theorem v337_pa_checked : Scalar.distance (sourceCoefficient 3 53 1 0) v337_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v337_pb : Scalar.QComplex := ((1493745827746262151432947 : Int)/10^30,(-431473349617345448629636638 : Int)/10^30)
theorem v337_pb_checked : Scalar.distance (sourceCoefficient 3 53 1 1) v337_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v337_pg : Scalar.QComplex := ((-93085701019888202828769 : Int)/10^30,(-322259480555654339833 : Int)/10^30)
theorem v337_pg_checked : Scalar.distance (sourceCoefficient 3 53 1 2) v337_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v337_mb : Scalar.QComplex := ((1121403203674939701781581 : Int)/10^30,(-431474477995471610199098314 : Int)/10^30)
theorem v337_mb_checked : Scalar.distance (sourceCoefficient 3 53 3 1) v337_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v337_mg : Scalar.QComplex := ((-93085944455245177736241 : Int)/10^30,(-241930593007902052747 : Int)/10^30)
theorem v337_mg_checked : Scalar.distance (sourceCoefficient 3 53 3 2) v337_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v337_upper : Scalar.QComplex := ((999998493080370207592739734113 : Int)/10^30,(1736040606892028855588389550 : Int)/10^30)
theorem v337_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 53 5) 1) 14) v337_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material337 : Material (3 : Basis) (53 : Basis) where
  plus := ![v337_pa,v337_pb,v337_pg]
  minus := ![(Primitive.Addresses.material337 1).one,v337_mb,v337_mg]
  upper := v337_upper
  lower := (Primitive.Addresses.material337 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v337_pa_checked.trans (by decide +kernel)
    · exact v337_pb_checked.trans (by decide +kernel)
    · exact v337_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 53 Primitive.Addresses.material337
    · exact v337_mb_checked.trans (by decide +kernel)
    · exact v337_mg_checked.trans (by decide +kernel)
  upper_error := v337_upper_checked
  lower_error := reuse_lower_error 3 53 Primitive.Addresses.material337

def v338_pa : Scalar.QComplex := ((999994013966722928414308973096 : Int)/10^30,(3460062242438534106791092320 : Int)/10^30)
theorem v338_pa_checked : Scalar.distance (sourceCoefficient 3 54 1 0) v338_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v338_pb : Scalar.QComplex := ((1492933587706480215825349 : Int)/10^30,(-431473351156880132883529831 : Int)/10^30)
theorem v338_pb_checked : Scalar.distance (sourceCoefficient 3 54 1 1) v338_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v338_pg : Scalar.QComplex := ((-93085701489196756118150 : Int)/10^30,(-322084249040706899994 : Int)/10^30)
theorem v338_pg_checked : Scalar.distance (sourceCoefficient 3 54 1 2) v338_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v338_mb : Scalar.QComplex := ((1120590962609042759745560 : Int)/10^30,(-431474478834079148815464497 : Int)/10^30)
theorem v338_mb_checked : Scalar.distance (sourceCoefficient 3 54 3 1) v338_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v338_mg : Scalar.QComplex := ((-93085944773336651015422 : Int)/10^30,(-241755361153209169784 : Int)/10^30)
theorem v338_mg_checked : Scalar.distance (sourceCoefficient 3 54 3 2) v338_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v338_upper : Scalar.QComplex := ((999998496346642727790558364582 : Int)/10^30,(1734158139723998771878996363 : Int)/10^30)
theorem v338_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 54 5) 1) 14) v338_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material338 : Material (3 : Basis) (54 : Basis) where
  plus := ![v338_pa,v338_pb,v338_pg]
  minus := ![(Primitive.Addresses.material338 1).one,v338_mb,v338_mg]
  upper := v338_upper
  lower := (Primitive.Addresses.material338 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v338_pa_checked.trans (by decide +kernel)
    · exact v338_pb_checked.trans (by decide +kernel)
    · exact v338_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 54 Primitive.Addresses.material338
    · exact v338_mb_checked.trans (by decide +kernel)
    · exact v338_mg_checked.trans (by decide +kernel)
  upper_error := v338_upper_checked
  lower_error := reuse_lower_error 3 54 Primitive.Addresses.material338

def v339_pa : Scalar.QComplex := ((999994066938807948797676709550 : Int)/10^30,(3444718737848896716879671280 : Int)/10^30)
theorem v339_pa_checked : Scalar.distance (sourceCoefficient 3 55 1 0) v339_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v339_pb : Scalar.QComplex := ((1486313198963553485349744 : Int)/10^30,(-431473363629257362908855518 : Int)/10^30)
theorem v339_pb_checked : Scalar.distance (sourceCoefficient 3 55 1 1) v339_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v339_pg : Scalar.QComplex := ((-93085705300074743922842 : Int)/10^30,(-320655975744573516950 : Int)/10^30)
theorem v339_pg_checked : Scalar.distance (sourceCoefficient 3 55 1 2) v339_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v339_mb : Scalar.QComplex := ((1113970565568089510480227 : Int)/10^30,(-431474485593354420899307939 : Int)/10^30)
theorem v339_mb_checked : Scalar.distance (sourceCoefficient 3 55 3 1) v339_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v339_mg : Scalar.QComplex := ((-93085947351677692334290 : Int)/10^30,(-240327085100271142302 : Int)/10^30)
theorem v339_mg_checked : Scalar.distance (sourceCoefficient 3 55 3 2) v339_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v339_upper : Scalar.QComplex := ((999998522837151882624732129725 : Int)/10^30,(1718814566561695938405601855 : Int)/10^30)
theorem v339_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 55 5) 1) 14) v339_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material339 : Material (3 : Basis) (55 : Basis) where
  plus := ![v339_pa,v339_pb,v339_pg]
  minus := ![(Primitive.Addresses.material339 1).one,v339_mb,v339_mg]
  upper := v339_upper
  lower := (Primitive.Addresses.material339 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v339_pa_checked.trans (by decide +kernel)
    · exact v339_pb_checked.trans (by decide +kernel)
    · exact v339_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 55 Primitive.Addresses.material339
    · exact v339_mb_checked.trans (by decide +kernel)
    · exact v339_mg_checked.trans (by decide +kernel)
  upper_error := v339_upper_checked
  lower_error := reuse_lower_error 3 55 Primitive.Addresses.material339

def v340_pa : Scalar.QComplex := ((999994079475996872569424893231 : Int)/10^30,(3441077295506508895043786088 : Int)/10^30)
theorem v340_pa_checked : Scalar.distance (sourceCoefficient 3 56 1 0) v340_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v340_pb : Scalar.QComplex := ((1484741995768394009889706 : Int)/10^30,(-431473366569414568656214450 : Int)/10^30)
theorem v340_pb_checked : Scalar.distance (sourceCoefficient 3 56 1 1) v340_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v340_pg : Scalar.QComplex := ((-93085706200748578335127 : Int)/10^30,(-320317006588111497946 : Int)/10^30)
theorem v340_pg_checked : Scalar.distance (sourceCoefficient 3 56 1 2) v340_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v340_mb : Scalar.QComplex := ((1112399360420737543316368 : Int)/10^30,(-431474487177632938834153302 : Int)/10^30)
theorem v340_mb_checked : Scalar.distance (sourceCoefficient 3 56 3 1) v340_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v340_mg : Scalar.QComplex := ((-93085947959836075961905 : Int)/10^30,(-239988115292781877650 : Int)/10^30)
theorem v340_mg_checked : Scalar.distance (sourceCoefficient 3 56 3 2) v340_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v340_upper : Scalar.QComplex := ((999998529089522999833675644938 : Int)/10^30,(1715173108004758014155290447 : Int)/10^30)
theorem v340_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 56 5) 1) 14) v340_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material340 : Material (3 : Basis) (56 : Basis) where
  plus := ![v340_pa,v340_pb,v340_pg]
  minus := ![(Primitive.Addresses.material340 1).one,v340_mb,v340_mg]
  upper := v340_upper
  lower := (Primitive.Addresses.material340 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v340_pa_checked.trans (by decide +kernel)
    · exact v340_pb_checked.trans (by decide +kernel)
    · exact v340_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 56 Primitive.Addresses.material340
    · exact v340_mb_checked.trans (by decide +kernel)
    · exact v340_mg_checked.trans (by decide +kernel)
  upper_error := v340_upper_checked
  lower_error := reuse_lower_error 3 56 Primitive.Addresses.material340

def v341_pa : Scalar.QComplex := ((999994119935152422176937535236 : Int)/10^30,(3429299508645028573588490261 : Int)/10^30)
theorem v341_pa_checked : Scalar.distance (sourceCoefficient 3 57 1 0) v341_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v341_pb : Scalar.QComplex := ((1479660136899480050331689 : Int)/10^30,(-431473376026743374562598953 : Int)/10^30)
theorem v341_pb_checked : Scalar.distance (sourceCoefficient 3 57 1 1) v341_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v341_pg : Scalar.QComplex := ((-93085709104003362807323 : Int)/10^30,(-319220653530376239855 : Int)/10^30)
theorem v341_pg_checked : Scalar.distance (sourceCoefficient 3 57 1 2) v341_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v341_mb : Scalar.QComplex := ((1107317495282783075859318 : Int)/10^30,(-431474492249542897899144285 : Int)/10^30)
theorem v341_mb_checked : Scalar.distance (sourceCoefficient 3 57 3 1) v341_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v341_mg : Scalar.QComplex := ((-93085949916986468502858 : Int)/10^30,(-238891760137890847506 : Int)/10^30)
theorem v341_mg_checked : Scalar.distance (sourceCoefficient 3 57 3 2) v341_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v341_upper : Scalar.QComplex := ((999998549221226639844253121416 : Int)/10^30,(1703395268856075654140583196 : Int)/10^30)
theorem v341_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 57 5) 1) 14) v341_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material341 : Material (3 : Basis) (57 : Basis) where
  plus := ![v341_pa,v341_pb,v341_pg]
  minus := ![(Primitive.Addresses.material341 1).one,v341_mb,v341_mg]
  upper := v341_upper
  lower := (Primitive.Addresses.material341 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v341_pa_checked.trans (by decide +kernel)
    · exact v341_pb_checked.trans (by decide +kernel)
    · exact v341_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 57 Primitive.Addresses.material341
    · exact v341_mb_checked.trans (by decide +kernel)
    · exact v341_mg_checked.trans (by decide +kernel)
  upper_error := v341_upper_checked
  lower_error := reuse_lower_error 3 57 Primitive.Addresses.material341

def v342_pa : Scalar.QComplex := ((999994141829843945656386948185 : Int)/10^30,(3422908995861723160505536922 : Int)/10^30)
theorem v342_pa_checked : Scalar.distance (sourceCoefficient 3 58 1 0) v342_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v342_pb : Scalar.QComplex := ((1476902769674680257464601 : Int)/10^30,(-431473381124799945081152304 : Int)/10^30)
theorem v342_pb_checked : Scalar.distance (sourceCoefficient 3 58 1 1) v342_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v342_pg : Scalar.QComplex := ((-93085710672976579215881 : Int)/10^30,(-318625783012766144055 : Int)/10^30)
theorem v342_pg_checked : Scalar.distance (sourceCoefficient 3 58 1 2) v342_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v342_mb : Scalar.QComplex := ((1104560124685283906279754 : Int)/10^30,(-431474494968113842385781551 : Int)/10^30)
theorem v342_mb_checked : Scalar.distance (sourceCoefficient 3 58 3 1) v342_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v342_mg : Scalar.QComplex := ((-93085950972612635987018 : Int)/10^30,(-238296888487825010508 : Int)/10^30)
theorem v342_mg_checked : Scalar.distance (sourceCoefficient 3 58 3 2) v342_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v342_upper : Scalar.QComplex := ((999998560086440232558465776882 : Int)/10^30,(1697004727802437050800539219 : Int)/10^30)
theorem v342_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 58 5) 1) 14) v342_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material342 : Material (3 : Basis) (58 : Basis) where
  plus := ![v342_pa,v342_pb,v342_pg]
  minus := ![(Primitive.Addresses.material342 1).one,v342_mb,v342_mg]
  upper := v342_upper
  lower := (Primitive.Addresses.material342 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v342_pa_checked.trans (by decide +kernel)
    · exact v342_pb_checked.trans (by decide +kernel)
    · exact v342_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 58 Primitive.Addresses.material342
    · exact v342_mb_checked.trans (by decide +kernel)
    · exact v342_mg_checked.trans (by decide +kernel)
  upper_error := v342_upper_checked
  lower_error := reuse_lower_error 3 58 Primitive.Addresses.material342

def v343_pa : Scalar.QComplex := ((999994201802133576591686602274 : Int)/10^30,(3405343171216128465600747195 : Int)/10^30)
theorem v343_pa_checked : Scalar.distance (sourceCoefficient 3 59 1 0) v343_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v343_pb : Scalar.QComplex := ((1469323498710805661103567 : Int)/10^30,(-431473395016956036328970580 : Int)/10^30)
theorem v343_pb_checked : Scalar.distance (sourceCoefficient 3 59 1 1) v343_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v343_pg : Scalar.QComplex := ((-93085714962817126471064 : Int)/10^30,(-316990641760863027317 : Int)/10^30)
theorem v343_pg_checked : Scalar.distance (sourceCoefficient 3 59 1 2) v343_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v343_mb : Scalar.QComplex := ((1096980844555213252301454 : Int)/10^30,(-431474502319695276817627224 : Int)/10^30)
theorem v343_mb_checked : Scalar.distance (sourceCoefficient 3 59 3 1) v343_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v343_mg : Scalar.QComplex := ((-93085953851398329574311 : Int)/10^30,(-236661744142820526466 : Int)/10^30)
theorem v343_mg_checked : Scalar.distance (sourceCoefficient 3 59 3 2) v343_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v343_upper : Scalar.QComplex := ((999998589741620762680404061800 : Int)/10^30,(1679438825812343479419370897 : Int)/10^30)
theorem v343_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 59 5) 1) 14) v343_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material343 : Material (3 : Basis) (59 : Basis) where
  plus := ![v343_pa,v343_pb,v343_pg]
  minus := ![(Primitive.Addresses.material343 1).one,v343_mb,v343_mg]
  upper := v343_upper
  lower := (Primitive.Addresses.material343 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v343_pa_checked.trans (by decide +kernel)
    · exact v343_pb_checked.trans (by decide +kernel)
    · exact v343_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 59 Primitive.Addresses.material343
    · exact v343_mb_checked.trans (by decide +kernel)
    · exact v343_mg_checked.trans (by decide +kernel)
  upper_error := v343_upper_checked
  lower_error := reuse_lower_error 3 59 Primitive.Addresses.material343

def v344_pa : Scalar.QComplex := ((999994270602457657536016483648 : Int)/10^30,(3385079357812565340031120923 : Int)/10^30)
theorem v344_pa_checked : Scalar.distance (sourceCoefficient 3 60 1 0) v344_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v344_pb : Scalar.QComplex := ((1460580104663752241420418 : Int)/10^30,(-431473410822341866840986175 : Int)/10^30)
theorem v344_pb_checked : Scalar.distance (sourceCoefficient 3 60 1 1) v344_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v344_pg : Scalar.QComplex := ((-93085719869921534094822 : Int)/10^30,(-315104354196906857060 : Int)/10^30)
theorem v344_pg_checked : Scalar.distance (sourceCoefficient 3 60 1 2) v344_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v344_mb : Scalar.QComplex := ((1088237440124388905605421 : Int)/10^30,(-431474510579919947504842289 : Int)/10^30)
theorem v344_mb_checked : Scalar.distance (sourceCoefficient 3 60 3 1) v344_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v344_mg : Scalar.QComplex := ((-93085957130719697602850 : Int)/10^30,(-234775453046605327868 : Int)/10^30)
theorem v344_mg_checked : Scalar.distance (sourceCoefficient 3 60 3 2) v344_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v344_upper : Scalar.QComplex := ((999998623568338757865727336728 : Int)/10^30,(1659174923846232216658495077 : Int)/10^30)
theorem v344_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 60 5) 1) 14) v344_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material344 : Material (3 : Basis) (60 : Basis) where
  plus := ![v344_pa,v344_pb,v344_pg]
  minus := ![(Primitive.Addresses.material344 1).one,v344_mb,v344_mg]
  upper := v344_upper
  lower := (Primitive.Addresses.material344 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v344_pa_checked.trans (by decide +kernel)
    · exact v344_pb_checked.trans (by decide +kernel)
    · exact v344_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 60 Primitive.Addresses.material344
    · exact v344_mb_checked.trans (by decide +kernel)
    · exact v344_mg_checked.trans (by decide +kernel)
  upper_error := v344_upper_checked
  lower_error := reuse_lower_error 3 60 Primitive.Addresses.material344

def v345_pa : Scalar.QComplex := ((999994290419607792438684675279 : Int)/10^30,(3379220055738730305039874552 : Int)/10^30)
theorem v345_pa_checked : Scalar.distance (sourceCoefficient 3 61 1 0) v345_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v345_pb : Scalar.QComplex := ((1458051943528376085352507 : Int)/10^30,(-431473415348455609196180201 : Int)/10^30)
theorem v345_pb_checked : Scalar.distance (sourceCoefficient 3 61 1 1) v345_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v345_pg : Scalar.QComplex := ((-93085721280504193553891 : Int)/10^30,(-314558932253497082959 : Int)/10^30)
theorem v345_pg_checked : Scalar.distance (sourceCoefficient 3 61 1 2) v345_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v345_mb : Scalar.QComplex := ((1085709276024530371853072 : Int)/10^30,(-431474512924342808902115116 : Int)/10^30)
theorem v345_mb_checked : Scalar.distance (sourceCoefficient 3 61 3 1) v345_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v345_mg : Scalar.QComplex := ((-93085958070627259567333 : Int)/10^30,(-234230030089011765485 : Int)/10^30)
theorem v345_mg_checked : Scalar.distance (sourceCoefficient 3 61 3 2) v345_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v345_upper : Scalar.QComplex := ((999998633272835549743769229790 : Int)/10^30,(1653315596296536003648376471 : Int)/10^30)
theorem v345_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 61 5) 1) 14) v345_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material345 : Material (3 : Basis) (61 : Basis) where
  plus := ![v345_pa,v345_pb,v345_pg]
  minus := ![(Primitive.Addresses.material345 1).one,v345_mb,v345_mg]
  upper := v345_upper
  lower := (Primitive.Addresses.material345 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v345_pa_checked.trans (by decide +kernel)
    · exact v345_pb_checked.trans (by decide +kernel)
    · exact v345_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 61 Primitive.Addresses.material345
    · exact v345_mb_checked.trans (by decide +kernel)
    · exact v345_mg_checked.trans (by decide +kernel)
  upper_error := v345_upper_checked
  lower_error := reuse_lower_error 3 61 Primitive.Addresses.material345

def v346_pa : Scalar.QComplex := ((999994319151897134392788222118 : Int)/10^30,(3370706740981191705633882872 : Int)/10^30)
theorem v346_pa_checked : Scalar.distance (sourceCoefficient 3 62 1 0) v346_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v346_pb : Scalar.QComplex := ((1454378633821288154799713 : Int)/10^30,(-431473421889507723861436677 : Int)/10^30)
theorem v346_pb_checked : Scalar.distance (sourceCoefficient 3 62 1 1) v346_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v346_pg : Scalar.QComplex := ((-93085723323376107183344 : Int)/10^30,(-313766457554799126718 : Int)/10^30)
theorem v346_pg_checked : Scalar.distance (sourceCoefficient 3 62 1 2) v346_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v346_mb : Scalar.QComplex := ((1082035962040550146891231 : Int)/10^30,(-431474516295491650545640250 : Int)/10^30)
theorem v346_mb_checked : Scalar.distance (sourceCoefficient 3 62 3 1) v346_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v346_mg : Scalar.QComplex := ((-93085959429628439301363 : Int)/10^30,(-233437553922481903526 : Int)/10^30)
theorem v346_mg_checked : Scalar.distance (sourceCoefficient 3 62 3 2) v346_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v346_upper : Scalar.QComplex := ((999998647311873148698163602829 : Int)/10^30,(1644802244629254860110323569 : Int)/10^30)
theorem v346_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 62 5) 1) 14) v346_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material346 : Material (3 : Basis) (62 : Basis) where
  plus := ![v346_pa,v346_pb,v346_pg]
  minus := ![(Primitive.Addresses.material346 1).one,v346_mb,v346_mg]
  upper := v346_upper
  lower := (Primitive.Addresses.material346 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v346_pa_checked.trans (by decide +kernel)
    · exact v346_pb_checked.trans (by decide +kernel)
    · exact v346_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 62 Primitive.Addresses.material346
    · exact v346_mb_checked.trans (by decide +kernel)
    · exact v346_mg_checked.trans (by decide +kernel)
  upper_error := v346_upper_checked
  lower_error := reuse_lower_error 3 62 Primitive.Addresses.material346

def v347_pa : Scalar.QComplex := ((999994402421758112548559003977 : Int)/10^30,(3345911706978044098038676910 : Int)/10^30)
theorem v347_pa_checked : Scalar.distance (sourceCoefficient 3 63 1 0) v347_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v347_pb : Scalar.QComplex := ((1443680117609863473034422 : Int)/10^30,(-431473440702756201901385716 : Int)/10^30)
theorem v347_pb_checked : Scalar.distance (sourceCoefficient 3 63 1 1) v347_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v347_pg : Scalar.QComplex := ((-93085729228395293245822 : Int)/10^30,(-311458374590496968747 : Int)/10^30)
theorem v347_pg_checked : Scalar.distance (sourceCoefficient 3 63 1 2) v347_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v347_mb : Scalar.QComplex := ((1071337433577685877693730 : Int)/10^30,(-431474525876395476377171734 : Int)/10^30)
theorem v347_mb_checked : Scalar.distance (sourceCoefficient 3 63 3 1) v347_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v347_mg : Scalar.QComplex := ((-93085963342873780660388 : Int)/10^30,(-231129466721818912386 : Int)/10^30)
theorem v347_mg_checked : Scalar.distance (sourceCoefficient 3 63 3 2) v347_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v347_upper : Scalar.QComplex := ((999998687787630804658313153066 : Int)/10^30,(1620007103839171905389461107 : Int)/10^30)
theorem v347_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 63 5) 1) 14) v347_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material347 : Material (3 : Basis) (63 : Basis) where
  plus := ![v347_pa,v347_pb,v347_pg]
  minus := ![(Primitive.Addresses.material347 1).one,v347_mb,v347_mg]
  upper := v347_upper
  lower := (Primitive.Addresses.material347 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v347_pa_checked.trans (by decide +kernel)
    · exact v347_pb_checked.trans (by decide +kernel)
    · exact v347_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 63 Primitive.Addresses.material347
    · exact v347_mb_checked.trans (by decide +kernel)
    · exact v347_mg_checked.trans (by decide +kernel)
  upper_error := v347_upper_checked
  lower_error := reuse_lower_error 3 63 Primitive.Addresses.material347

def v348_pa : Scalar.QComplex := ((999994520363842926717239993561 : Int)/10^30,(3310474631791361668273761836 : Int)/10^30)
theorem v348_pa_checked : Scalar.distance (sourceCoefficient 3 64 1 0) v348_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v348_pb : Scalar.QComplex := ((1428389793773708170183116 : Int)/10^30,(-431473466976674212936893855 : Int)/10^30)
theorem v348_pb_checked : Scalar.distance (sourceCoefficient 3 64 1 1) v348_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v348_pg : Scalar.QComplex := ((-93085737551948442969961 : Int)/10^30,(-308159661350136335299 : Int)/10^30)
theorem v348_pg_checked : Scalar.distance (sourceCoefficient 3 64 1 2) v348_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v348_mb : Scalar.QComplex := ((1056047092761609031180066 : Int)/10^30,(-431474538955442884451868346 : Int)/10^30)
theorem v348_mb_checked : Scalar.distance (sourceCoefficient 3 64 3 1) v348_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v348_mg : Scalar.QComplex := ((-93085968819782873243280 : Int)/10^30,(-227830747526868487673 : Int)/10^30)
theorem v348_mg_checked : Scalar.distance (sourceCoefficient 3 64 3 2) v348_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v348_upper : Scalar.QComplex := ((999998744568363012080330719788 : Int)/10^30,(1584569877874511468019009669 : Int)/10^30)
theorem v348_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 64 5) 1) 14) v348_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material348 : Material (3 : Basis) (64 : Basis) where
  plus := ![v348_pa,v348_pb,v348_pg]
  minus := ![(Primitive.Addresses.material348 1).one,v348_mb,v348_mg]
  upper := v348_upper
  lower := (Primitive.Addresses.material348 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v348_pa_checked.trans (by decide +kernel)
    · exact v348_pb_checked.trans (by decide +kernel)
    · exact v348_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 64 Primitive.Addresses.material348
    · exact v348_mb_checked.trans (by decide +kernel)
    · exact v348_mg_checked.trans (by decide +kernel)
  upper_error := v348_upper_checked
  lower_error := reuse_lower_error 3 64 Primitive.Addresses.material348

def v349_pa : Scalar.QComplex := ((999994638783626985866009873173 : Int)/10^30,(3274508207866834727050107578 : Int)/10^30)
theorem v349_pa_checked : Scalar.distance (sourceCoefficient 3 65 1 0) v349_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v349_pb : Scalar.QComplex := ((1412871068699701907855005 : Int)/10^30,(-431473492904328283329518712 : Int)/10^30)
theorem v349_pb_checked : Scalar.distance (sourceCoefficient 3 65 1 1) v349_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v349_pg : Scalar.QComplex := ((-93085745860383895818975 : Int)/10^30,(-304811673016565362376 : Int)/10^30)
theorem v349_pg_checked : Scalar.distance (sourceCoefficient 3 65 1 2) v349_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v349_mb : Scalar.QComplex := ((1040528351091535630119589 : Int)/10^30,(-431474551491126499358082269 : Int)/10^30)
theorem v349_mb_checked : Scalar.distance (sourceCoefficient 3 65 3 1) v349_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v349_mg : Scalar.QComplex := ((-93085974239052088407349 : Int)/10^30,(-224482753270100984197 : Int)/10^30)
theorem v349_mg_checked : Scalar.distance (sourceCoefficient 3 65 3 2) v349_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v349_upper : Scalar.QComplex := ((999998800913185853628268360391 : Int)/10^30,(1548603303135943722239792237 : Int)/10^30)
theorem v349_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 65 5) 1) 14) v349_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material349 : Material (3 : Basis) (65 : Basis) where
  plus := ![v349_pa,v349_pb,v349_pg]
  minus := ![(Primitive.Addresses.material349 1).one,v349_mb,v349_mg]
  upper := v349_upper
  lower := (Primitive.Addresses.material349 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v349_pa_checked.trans (by decide +kernel)
    · exact v349_pb_checked.trans (by decide +kernel)
    · exact v349_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 65 Primitive.Addresses.material349
    · exact v349_mb_checked.trans (by decide +kernel)
    · exact v349_mg_checked.trans (by decide +kernel)
  upper_error := v349_upper_checked
  lower_error := reuse_lower_error 3 65 Primitive.Addresses.material349

def v350_pa : Scalar.QComplex := ((999994696219597489872079925203 : Int)/10^30,(3256920735132142848210519578 : Int)/10^30)
theorem v350_pa_checked : Scalar.distance (sourceCoefficient 3 66 1 0) v350_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v350_pb : Scalar.QComplex := ((1405282459420163741799729 : Int)/10^30,(-431473505311936718036792172 : Int)/10^30)
theorem v350_pb_checked : Scalar.distance (sourceCoefficient 3 66 1 1) v350_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v350_pg : Scalar.QComplex := ((-93085749872038658846620 : Int)/10^30,(-303174516874628060963 : Int)/10^30)
theorem v350_pg_checked : Scalar.distance (sourceCoefficient 3 66 1 2) v350_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v350_mb : Scalar.QComplex := ((1032939733930376254200759 : Int)/10^30,(-431474557350102284178786935 : Int)/10^30)
theorem v350_mb_checked : Scalar.distance (sourceCoefficient 3 66 3 1) v350_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v350_mg : Scalar.QComplex := ((-93085976837913341996162 : Int)/10^30,(-222845594275874353891 : Int)/10^30)
theorem v350_mg_checked : Scalar.distance (sourceCoefficient 3 66 3 2) v350_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v350_upper : Scalar.QComplex := ((999998827994688396487941916375 : Int)/10^30,(1531015757466451972676946066 : Int)/10^30)
theorem v350_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 66 5) 1) 14) v350_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material350 : Material (3 : Basis) (66 : Basis) where
  plus := ![v350_pa,v350_pb,v350_pg]
  minus := ![(Primitive.Addresses.material350 1).one,v350_mb,v350_mg]
  upper := v350_upper
  lower := (Primitive.Addresses.material350 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v350_pa_checked.trans (by decide +kernel)
    · exact v350_pb_checked.trans (by decide +kernel)
    · exact v350_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 66 Primitive.Addresses.material350
    · exact v350_mb_checked.trans (by decide +kernel)
    · exact v350_mg_checked.trans (by decide +kernel)
  upper_error := v350_upper_checked
  lower_error := reuse_lower_error 3 66 Primitive.Addresses.material350

def v351_pa : Scalar.QComplex := ((999994791919002720870310536164 : Int)/10^30,(3227403735272453507258423034 : Int)/10^30)
theorem v351_pa_checked : Scalar.distance (sourceCoefficient 3 67 1 0) v351_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v351_pb : Scalar.QComplex := ((1392546521125440648889969 : Int)/10^30,(-431473525735635821511671847 : Int)/10^30)
theorem v351_pb_checked : Scalar.distance (sourceCoefficient 3 67 1 1) v351_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v351_pg : Scalar.QComplex := ((-93085756529286722035940 : Int)/10^30,(-300426882970822416568 : Int)/10^30)
theorem v351_pg_checked : Scalar.distance (sourceCoefficient 3 67 1 2) v351_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v351_mb : Scalar.QComplex := ((1020203782753092572513269 : Int)/10^30,(-431474566783252639998614232 : Int)/10^30)
theorem v351_mb_checked : Scalar.distance (sourceCoefficient 3 67 3 1) v351_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v351_mg : Scalar.QComplex := ((-93085981124074616240761 : Int)/10^30,(-220097955650233137745 : Int)/10^30)
theorem v351_mg_checked : Scalar.distance (sourceCoefficient 3 67 3 2) v351_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v351_upper : Scalar.QComplex := ((999998872750287097949667878151 : Int)/10^30,(1501498636400374965884583916 : Int)/10^30)
theorem v351_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 67 5) 1) 14) v351_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material351 : Material (3 : Basis) (67 : Basis) where
  plus := ![v351_pa,v351_pb,v351_pg]
  minus := ![(Primitive.Addresses.material351 1).one,v351_mb,v351_mg]
  upper := v351_upper
  lower := (Primitive.Addresses.material351 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v351_pa_checked.trans (by decide +kernel)
    · exact v351_pb_checked.trans (by decide +kernel)
    · exact v351_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 67 Primitive.Addresses.material351
    · exact v351_mb_checked.trans (by decide +kernel)
    · exact v351_mg_checked.trans (by decide +kernel)
  upper_error := v351_upper_checked
  lower_error := reuse_lower_error 3 67 Primitive.Addresses.material351

def v352_pa : Scalar.QComplex := ((999994949363413466552541614521 : Int)/10^30,(3178246004345315886129533784 : Int)/10^30)
theorem v352_pa_checked : Scalar.distance (sourceCoefficient 3 68 1 0) v352_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v352_pb : Scalar.QComplex := ((1371336039838194503211647 : Int)/10^30,(-431473558636848864357164794 : Int)/10^30)
theorem v352_pb_checked : Scalar.distance (sourceCoefficient 3 68 1 1) v352_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v352_pg : Scalar.QComplex := ((-93085767406286341879736 : Int)/10^30,(-295850962556142652008 : Int)/10^30)
theorem v352_pg_checked : Scalar.distance (sourceCoefficient 3 68 1 2) v352_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v352_mb : Scalar.QComplex := ((998993280971212936611417 : Int)/10^30,(-431474581380763365940753635 : Int)/10^30)
theorem v352_mb_checked : Scalar.distance (sourceCoefficient 3 68 3 1) v352_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v352_mg : Scalar.QComplex := ((-93085988052256960016847 : Int)/10^30,(-215522027553016883417 : Int)/10^30)
theorem v352_mg_checked : Scalar.distance (sourceCoefficient 3 68 3 2) v352_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v352_upper : Scalar.QComplex := ((999998945352679322950860679301 : Int)/10^30,(1452340706953133386338623507 : Int)/10^30)
theorem v352_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 68 5) 1) 14) v352_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material352 : Material (3 : Basis) (68 : Basis) where
  plus := ![v352_pa,v352_pb,v352_pg]
  minus := ![(Primitive.Addresses.material352 1).one,v352_mb,v352_mg]
  upper := v352_upper
  lower := (Primitive.Addresses.material352 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v352_pa_checked.trans (by decide +kernel)
    · exact v352_pb_checked.trans (by decide +kernel)
    · exact v352_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 68 Primitive.Addresses.material352
    · exact v352_mb_checked.trans (by decide +kernel)
    · exact v352_mg_checked.trans (by decide +kernel)
  upper_error := v352_upper_checked
  lower_error := reuse_lower_error 3 68 Primitive.Addresses.material352

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
