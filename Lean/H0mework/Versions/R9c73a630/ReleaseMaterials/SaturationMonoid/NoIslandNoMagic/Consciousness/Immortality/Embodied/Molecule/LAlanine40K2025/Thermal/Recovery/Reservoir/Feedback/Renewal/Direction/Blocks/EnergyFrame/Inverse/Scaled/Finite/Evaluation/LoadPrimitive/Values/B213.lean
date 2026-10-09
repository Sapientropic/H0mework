import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B142

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3409_pa : Scalar.QComplex := ((999998760684525530953096934511 : Int)/10^30,(-1574366352865573835302252679 : Int)/10^30)
theorem v3409_pa_checked : Scalar.distance (sourceCoefficient 45 80 1 0) v3409_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3409_pb : Scalar.QComplex := ((-679303655124134095635085 : Int)/10^30,(-431476963424792037752383719 : Int)/10^30)
theorem v3409_pb_checked : Scalar.distance (sourceCoefficient 45 80 1 1) v3409_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3409_pg : Scalar.QComplex := ((-93086312069884214341954 : Int)/10^30,(146552139259504256595 : Int)/10^30)
theorem v3409_pg_checked : Scalar.distance (sourceCoefficient 45 80 1 2) v3409_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3409_mb : Scalar.QComplex := ((-1051648588622887366043816 : Int)/10^30,(-431476216557739412082527373 : Int)/10^30)
theorem v3409_mb_checked : Scalar.distance (sourceCoefficient 45 80 3 1) v3409_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3409_mg : Scalar.QComplex := ((-93086150941700258477383 : Int)/10^30,(226881379555890624748 : Int)/10^30)
theorem v3409_mg_checked : Scalar.distance (sourceCoefficient 45 80 3 2) v3409_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3409_upper : Scalar.QComplex := ((999994554090339951327447243990 : Int)/10^30,(-3300271149794410406857252048 : Int)/10^30)
theorem v3409_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 80 5) 1) 14) v3409_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3409 : Material (45 : Basis) (80 : Basis) where
  plus := ![v3409_pa,v3409_pb,v3409_pg]
  minus := ![(Primitive.Addresses.material3409 1).one,v3409_mb,v3409_mg]
  upper := v3409_upper
  lower := (Primitive.Addresses.material3409 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3409_pa_checked.trans (by decide +kernel)
    · exact v3409_pb_checked.trans (by decide +kernel)
    · exact v3409_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 80 Primitive.Addresses.material3409
    · exact v3409_mb_checked.trans (by decide +kernel)
    · exact v3409_mg_checked.trans (by decide +kernel)
  upper_error := v3409_upper_checked
  lower_error := reuse_lower_error 45 80 Primitive.Addresses.material3409

def v3410_pa : Scalar.QComplex := ((999998719041465703649557902362 : Int)/10^30,(-1600598459245145686623695333 : Int)/10^30)
theorem v3410_pa_checked : Scalar.distance (sourceCoefficient 45 81 1 0) v3410_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3410_pb : Scalar.QComplex := ((-690622215273879310856614 : Int)/10^30,(-431476943281053083662026613 : Int)/10^30)
theorem v3410_pb_checked : Scalar.distance (sourceCoefficient 45 81 1 1) v3410_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3410_pg : Scalar.QComplex := ((-93086307958789591236571 : Int)/10^30,(148993991950783310356 : Int)/10^30)
theorem v3410_pg_checked : Scalar.distance (sourceCoefficient 45 81 1 2) v3410_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3410_mb : Scalar.QComplex := ((-1062967127175075876706193 : Int)/10^30,(-431476186646600318222305274 : Int)/10^30)
theorem v3410_mb_checked : Scalar.distance (sourceCoefficient 45 81 3 1) v3410_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3410_mg : Scalar.QComplex := ((-93086144723398270509270 : Int)/10^30,(229323227790266820454 : Int)/10^30)
theorem v3410_mg_checked : Scalar.distance (sourceCoefficient 45 81 3 2) v3410_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3410_upper : Scalar.QComplex := ((999994467173106293429872809138 : Int)/10^30,(-3326503145232197812431942728 : Int)/10^30)
theorem v3410_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 81 5) 1) 14) v3410_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3410 : Material (45 : Basis) (81 : Basis) where
  plus := ![v3410_pa,v3410_pb,v3410_pg]
  minus := ![(Primitive.Addresses.material3410 1).one,v3410_mb,v3410_mg]
  upper := v3410_upper
  lower := (Primitive.Addresses.material3410 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3410_pa_checked.trans (by decide +kernel)
    · exact v3410_pb_checked.trans (by decide +kernel)
    · exact v3410_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 81 Primitive.Addresses.material3410
    · exact v3410_mb_checked.trans (by decide +kernel)
    · exact v3410_mg_checked.trans (by decide +kernel)
  upper_error := v3410_upper_checked
  lower_error := reuse_lower_error 45 81 Primitive.Addresses.material3410

def v3411_pa : Scalar.QComplex := ((999998703081698307193986870341 : Int)/10^30,(-1610538705336984678487923254 : Int)/10^30)
theorem v3411_pa_checked : Scalar.distance (sourceCoefficient 45 82 1 0) v3411_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3411_pb : Scalar.QComplex := ((-694911206397621265082518 : Int)/10^30,(-431476935544469588007291180 : Int)/10^30)
theorem v3411_pb_checked : Scalar.distance (sourceCoefficient 45 82 1 1) v3411_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3411_pg : Scalar.QComplex := ((-93086306381430200775573 : Int)/10^30,(149919293797226393116 : Int)/10^30)
theorem v3411_pg_checked : Scalar.distance (sourceCoefficient 45 82 1 2) v3411_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3411_mb : Scalar.QComplex := ((-1067256110025507305020999 : Int)/10^30,(-431476175208813532451321493 : Int)/10^30)
theorem v3411_mb_checked : Scalar.distance (sourceCoefficient 45 82 3 1) v3411_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3411_mg : Scalar.QComplex := ((-93086142347545647939032 : Int)/10^30,(230248527930987625062 : Int)/10^30)
theorem v3411_mg_checked : Scalar.distance (sourceCoefficient 45 82 3 2) v3411_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3411_upper : Scalar.QComplex := ((999994434057399684740167579054 : Int)/10^30,(-3336443348974097246337653564 : Int)/10^30)
theorem v3411_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 82 5) 1) 14) v3411_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3411 : Material (45 : Basis) (82 : Basis) where
  plus := ![v3411_pa,v3411_pb,v3411_pg]
  minus := ![(Primitive.Addresses.material3411 1).one,v3411_mb,v3411_mg]
  upper := v3411_upper
  lower := (Primitive.Addresses.material3411 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3411_pa_checked.trans (by decide +kernel)
    · exact v3411_pb_checked.trans (by decide +kernel)
    · exact v3411_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 82 Primitive.Addresses.material3411
    · exact v3411_mb_checked.trans (by decide +kernel)
    · exact v3411_mg_checked.trans (by decide +kernel)
  upper_error := v3411_upper_checked
  lower_error := reuse_lower_error 45 82 Primitive.Addresses.material3411

def v3412_pa : Scalar.QComplex := ((999998681136855685157910662449 : Int)/10^30,(-1624107308409666244317916487 : Int)/10^30)
theorem v3412_pa_checked : Scalar.distance (sourceCoefficient 45 83 1 0) v3412_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3412_pb : Scalar.QComplex := ((-700765751341586777506848 : Int)/10^30,(-431476924892146968689417067 : Int)/10^30)
theorem v3412_pb_checked : Scalar.distance (sourceCoefficient 45 83 1 1) v3412_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3412_pg : Scalar.QComplex := ((-93086304210987180578616 : Int)/10^30,(151182346370734469918 : Int)/10^30)
theorem v3412_pg_checked : Scalar.distance (sourceCoefficient 45 83 1 2) v3412_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3412_mb : Scalar.QComplex := ((-1073110643597083511214822 : Int)/10^30,(-431476159504286271753811268 : Int)/10^30)
theorem v3412_mb_checked : Scalar.distance (sourceCoefficient 45 83 3 1) v3412_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3412_mg : Scalar.QComplex := ((-93086139087145950735947 : Int)/10^30,(231511578161208931087 : Int)/10^30)
theorem v3412_mg_checked : Scalar.distance (sourceCoefficient 45 83 3 2) v3412_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3412_upper : Scalar.QComplex := ((999994388694411777576196491814 : Int)/10^30,(-3350011893963130870426307384 : Int)/10^30)
theorem v3412_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 83 5) 1) 14) v3412_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3412 : Material (45 : Basis) (83 : Basis) where
  plus := ![v3412_pa,v3412_pb,v3412_pg]
  minus := ![(Primitive.Addresses.material3412 1).one,v3412_mb,v3412_mg]
  upper := v3412_upper
  lower := (Primitive.Addresses.material3412 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3412_pa_checked.trans (by decide +kernel)
    · exact v3412_pb_checked.trans (by decide +kernel)
    · exact v3412_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 83 Primitive.Addresses.material3412
    · exact v3412_mb_checked.trans (by decide +kernel)
    · exact v3412_mg_checked.trans (by decide +kernel)
  upper_error := v3412_upper_checked
  lower_error := reuse_lower_error 45 83 Primitive.Addresses.material3412

def v3413_pa : Scalar.QComplex := ((999998623449880254013507029210 : Int)/10^30,(-1659246318242635370185270940 : Int)/10^30)
theorem v3413_pa_checked : Scalar.distance (sourceCoefficient 45 84 1 0) v3413_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3413_pb : Scalar.QComplex := ((-715927437954037155898984 : Int)/10^30,(-431476896813186210877680333 : Int)/10^30)
theorem v3413_pb_checked : Scalar.distance (sourceCoefficient 45 84 1 1) v3413_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3413_pg : Scalar.QComplex := ((-93086298497189646007323 : Int)/10^30,(154453310673020184090 : Int)/10^30)
theorem v3413_pg_checked : Scalar.distance (sourceCoefficient 45 84 1 2) v3413_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3413_mb : Scalar.QComplex := ((-1088272300333266535938139 : Int)/10^30,(-431476118341483279493940807 : Int)/10^30)
theorem v3413_mb_checked : Scalar.distance (sourceCoefficient 45 84 3 1) v3413_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3413_mg : Scalar.QComplex := ((-93086130550655669563483 : Int)/10^30,(234782536314815212618 : Int)/10^30)
theorem v3413_mg_checked : Scalar.distance (sourceCoefficient 45 84 3 2) v3413_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3413_upper : Scalar.QComplex := ((999994270360779078771026889319 : Int)/10^30,(-3385150751898186295512916273 : Int)/10^30)
theorem v3413_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 84 5) 1) 14) v3413_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3413 : Material (45 : Basis) (84 : Basis) where
  plus := ![v3413_pa,v3413_pb,v3413_pg]
  minus := ![(Primitive.Addresses.material3413 1).one,v3413_mb,v3413_mg]
  upper := v3413_upper
  lower := (Primitive.Addresses.material3413 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3413_pa_checked.trans (by decide +kernel)
    · exact v3413_pb_checked.trans (by decide +kernel)
    · exact v3413_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 84 Primitive.Addresses.material3413
    · exact v3413_mb_checked.trans (by decide +kernel)
    · exact v3413_mg_checked.trans (by decide +kernel)
  upper_error := v3413_upper_checked
  lower_error := reuse_lower_error 45 84 Primitive.Addresses.material3413

def v3414_pa : Scalar.QComplex := ((999998489150161222872340679762 : Int)/10^30,(-1738303021595205070524227930 : Int)/10^30)
theorem v3414_pa_checked : Scalar.distance (sourceCoefficient 45 85 1 0) v3414_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3414_pb : Scalar.QComplex := ((-750038612346894932452043 : Int)/10^30,(-431476831043464656024715031 : Int)/10^30)
theorem v3414_pb_checked : Scalar.distance (sourceCoefficient 45 85 1 1) v3414_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3414_pg : Scalar.QComplex := ((-93086285151909516567429 : Int)/10^30,(161812415222898637141 : Int)/10^30)
theorem v3414_pg_checked : Scalar.distance (sourceCoefficient 45 85 1 2) v3414_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3414_mb : Scalar.QComplex := ((-1122383405268667584806659 : Int)/10^30,(-431476023135379022942010544 : Int)/10^30)
theorem v3414_mb_checked : Scalar.distance (sourceCoefficient 45 85 3 1) v3414_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3414_mg : Scalar.QComplex := ((-93086110854804724401415 : Int)/10^30,(242141626608187011454 : Int)/10^30)
theorem v3414_mg_checked : Scalar.distance (sourceCoefficient 45 85 3 2) v3414_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3414_upper : Scalar.QComplex := ((999993999616562052853906263887 : Int)/10^30,(-3464207105715951532514855726 : Int)/10^30)
theorem v3414_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 85 5) 1) 14) v3414_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3414 : Material (45 : Basis) (85 : Basis) where
  plus := ![v3414_pa,v3414_pb,v3414_pg]
  minus := ![(Primitive.Addresses.material3414 1).one,v3414_mb,v3414_mg]
  upper := v3414_upper
  lower := (Primitive.Addresses.material3414 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3414_pa_checked.trans (by decide +kernel)
    · exact v3414_pb_checked.trans (by decide +kernel)
    · exact v3414_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 85 Primitive.Addresses.material3414
    · exact v3414_mb_checked.trans (by decide +kernel)
    · exact v3414_mg_checked.trans (by decide +kernel)
  upper_error := v3414_upper_checked
  lower_error := reuse_lower_error 45 85 Primitive.Addresses.material3414

def v3415_pa : Scalar.QComplex := ((999998463691274553723267366364 : Int)/10^30,(-1752887643475203912906513499 : Int)/10^30)
theorem v3415_pa_checked : Scalar.distance (sourceCoefficient 45 86 1 0) v3415_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3415_pb : Scalar.QComplex := ((-756331545583566473383151 : Int)/10^30,(-431476818517211824850406365 : Int)/10^30)
theorem v3415_pb_checked : Scalar.distance (sourceCoefficient 45 86 1 1) v3415_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3415_pg : Scalar.QComplex := ((-93086282615771887886432 : Int)/10^30,(163170045253791479784 : Int)/10^30)
theorem v3415_pg_checked : Scalar.distance (sourceCoefficient 45 86 1 2) v3415_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3415_mb : Scalar.QComplex := ((-1128676325352600448649674 : Int)/10^30,(-431476005178612895808385391 : Int)/10^30)
theorem v3415_mb_checked : Scalar.distance (sourceCoefficient 45 86 3 1) v3415_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3415_mg : Scalar.QComplex := ((-93086107147094468766610 : Int)/10^30,(243499253944999596685 : Int)/10^30)
theorem v3415_mg_checked : Scalar.distance (sourceCoefficient 45 86 3 2) v3415_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3415_upper : Scalar.QComplex := ((999993948985979043409326024198 : Int)/10^30,(-3478791661934140535878360755 : Int)/10^30)
theorem v3415_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 86 5) 1) 14) v3415_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3415 : Material (45 : Basis) (86 : Basis) where
  plus := ![v3415_pa,v3415_pb,v3415_pg]
  minus := ![(Primitive.Addresses.material3415 1).one,v3415_mb,v3415_mg]
  upper := v3415_upper
  lower := (Primitive.Addresses.material3415 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3415_pa_checked.trans (by decide +kernel)
    · exact v3415_pb_checked.trans (by decide +kernel)
    · exact v3415_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 86 Primitive.Addresses.material3415
    · exact v3415_mb_checked.trans (by decide +kernel)
    · exact v3415_mg_checked.trans (by decide +kernel)
  upper_error := v3415_upper_checked
  lower_error := reuse_lower_error 45 86 Primitive.Addresses.material3415

def v3416_pa : Scalar.QComplex := ((999998461997945680677566962509 : Int)/10^30,(-1753853398431101987531429204 : Int)/10^30)
theorem v3416_pa_checked : Scalar.distance (sourceCoefficient 45 87 1 0) v3416_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3416_pb : Scalar.QComplex := ((-756748246918690785591293 : Int)/10^30,(-431476817683436679364883110 : Int)/10^30)
theorem v3416_pb_checked : Scalar.distance (sourceCoefficient 45 87 1 1) v3416_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3416_pg : Scalar.QComplex := ((-93086282447020105671306 : Int)/10^30,(163259943911152772091 : Int)/10^30)
theorem v3416_pg_checked : Scalar.distance (sourceCoefficient 45 87 1 2) v3416_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3416_mb : Scalar.QComplex := ((-1129093025813057410883774 : Int)/10^30,(-431476003985243576094623255 : Int)/10^30)
theorem v3416_mb_checked : Scalar.distance (sourceCoefficient 45 87 3 1) v3416_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3416_mg : Scalar.QComplex := ((-93086106900764256967916 : Int)/10^30,(243589152423262322532 : Int)/10^30)
theorem v3416_mg_checked : Scalar.distance (sourceCoefficient 45 87 3 2) v3416_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3416_upper : Scalar.QComplex := ((999993945625847251103199796839 : Int)/10^30,(-3479757412529128031957818077 : Int)/10^30)
theorem v3416_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 87 5) 1) 14) v3416_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3416 : Material (45 : Basis) (87 : Basis) where
  plus := ![v3416_pa,v3416_pb,v3416_pg]
  minus := ![(Primitive.Addresses.material3416 1).one,v3416_mb,v3416_mg]
  upper := v3416_upper
  lower := (Primitive.Addresses.material3416 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3416_pa_checked.trans (by decide +kernel)
    · exact v3416_pb_checked.trans (by decide +kernel)
    · exact v3416_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 87 Primitive.Addresses.material3416
    · exact v3416_mb_checked.trans (by decide +kernel)
    · exact v3416_mg_checked.trans (by decide +kernel)
  upper_error := v3416_upper_checked
  lower_error := reuse_lower_error 45 87 Primitive.Addresses.material3416

def v3417_pa : Scalar.QComplex := ((999998441304198645820652239235 : Int)/10^30,(-1765612973778726382513896135 : Int)/10^30)
theorem v3417_pa_checked : Scalar.distance (sourceCoefficient 45 88 1 0) v3417_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3417_pb : Scalar.QComplex := ((-761822236634341534439170 : Int)/10^30,(-431476807487876076456120546 : Int)/10^30)
theorem v3417_pb_checked : Scalar.distance (sourceCoefficient 45 88 1 1) v3417_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3417_pg : Scalar.QComplex := ((-93086280384077733329045 : Int)/10^30,(164354600505757552559 : Int)/10^30)
theorem v3417_pg_checked : Scalar.distance (sourceCoefficient 45 88 1 2) v3417_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3417_mb : Scalar.QComplex := ((-1134167004841120286502457 : Int)/10^30,(-431475989411062168866019805 : Int)/10^30)
theorem v3417_mb_checked : Scalar.distance (sourceCoefficient 45 88 3 1) v3417_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3417_mg : Scalar.QComplex := ((-93086103893183313112318 : Int)/10^30,(244683806830050068694 : Int)/10^30)
theorem v3417_mg_checked : Scalar.distance (sourceCoefficient 45 88 3 2) v3417_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3417_upper : Scalar.QComplex := ((999993904636170807493922772910 : Int)/10^30,(-3491516934646716263313637502 : Int)/10^30)
theorem v3417_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 88 5) 1) 14) v3417_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3417 : Material (45 : Basis) (88 : Basis) where
  plus := ![v3417_pa,v3417_pb,v3417_pg]
  minus := ![(Primitive.Addresses.material3417 1).one,v3417_mb,v3417_mg]
  upper := v3417_upper
  lower := (Primitive.Addresses.material3417 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3417_pa_checked.trans (by decide +kernel)
    · exact v3417_pb_checked.trans (by decide +kernel)
    · exact v3417_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 88 Primitive.Addresses.material3417
    · exact v3417_mb_checked.trans (by decide +kernel)
    · exact v3417_mg_checked.trans (by decide +kernel)
  upper_error := v3417_upper_checked
  lower_error := reuse_lower_error 45 88 Primitive.Addresses.material3417

def v3418_pa : Scalar.QComplex := ((999998412766960469646089086725 : Int)/10^30,(-1781702432998278768714159831 : Int)/10^30)
theorem v3418_pa_checked : Scalar.distance (sourceCoefficient 45 89 1 0) v3418_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3418_pb : Scalar.QComplex := ((-768764472808217145369144 : Int)/10^30,(-431476793409412691972490588 : Int)/10^30)
theorem v3418_pb_checked : Scalar.distance (sourceCoefficient 45 89 1 1) v3418_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3418_pg : Scalar.QComplex := ((-93086277537227730096528 : Int)/10^30,(165852310413098441889 : Int)/10^30)
theorem v3418_pg_checked : Scalar.distance (sourceCoefficient 45 89 1 2) v3418_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3418_mb : Scalar.QComplex := ((-1141109226281004263675313 : Int)/10^30,(-431475969341766875093610703 : Int)/10^30)
theorem v3418_mb_checked : Scalar.distance (sourceCoefficient 45 89 3 1) v3418_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3418_mg : Scalar.QComplex := ((-93086099753878174207181 : Int)/10^30,(246181513723021775372 : Int)/10^30)
theorem v3418_mg_checked : Scalar.distance (sourceCoefficient 45 89 3 2) v3418_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3418_upper : Scalar.QComplex := ((999993848330028145574423155806 : Int)/10^30,(-3507606320650224928582695935 : Int)/10^30)
theorem v3418_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 89 5) 1) 14) v3418_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3418 : Material (45 : Basis) (89 : Basis) where
  plus := ![v3418_pa,v3418_pb,v3418_pg]
  minus := ![(Primitive.Addresses.material3418 1).one,v3418_mb,v3418_mg]
  upper := v3418_upper
  lower := (Primitive.Addresses.material3418 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3418_pa_checked.trans (by decide +kernel)
    · exact v3418_pb_checked.trans (by decide +kernel)
    · exact v3418_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 89 Primitive.Addresses.material3418
    · exact v3418_mb_checked.trans (by decide +kernel)
    · exact v3418_mg_checked.trans (by decide +kernel)
  upper_error := v3418_upper_checked
  lower_error := reuse_lower_error 45 89 Primitive.Addresses.material3418

def v3419_pa : Scalar.QComplex := ((999998365737818997920872345544 : Int)/10^30,(-1807905332474928567059205715 : Int)/10^30)
theorem v3419_pa_checked : Scalar.distance (sourceCoefficient 45 90 1 0) v3419_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3419_pb : Scalar.QComplex := ((-780070428455985290506388 : Int)/10^30,(-431476770162800151876971123 : Int)/10^30)
theorem v3419_pb_checked : Scalar.distance (sourceCoefficient 45 90 1 1) v3419_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3419_pg : Scalar.QComplex := ((-93086272840742481842878 : Int)/10^30,(168291444081336898291 : Int)/10^30)
theorem v3419_pg_checked : Scalar.distance (sourceCoefficient 45 90 1 2) v3419_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3419_mb : Scalar.QComplex := ((-1152415157658268779909825 : Int)/10^30,(-431475936338632468090386561 : Int)/10^30)
theorem v3419_mb_checked : Scalar.distance (sourceCoefficient 45 90 3 1) v3419_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3419_mg : Scalar.QComplex := ((-93086092952532173482268 : Int)/10^30,(248620642430204045774 : Int)/10^30)
theorem v3419_mg_checked : Scalar.distance (sourceCoefficient 45 90 3 2) v3419_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3419_upper : Scalar.QComplex := ((999993756077129330005014902441 : Int)/10^30,(-3533809099932702235437628524 : Int)/10^30)
theorem v3419_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 90 5) 1) 14) v3419_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3419 : Material (45 : Basis) (90 : Basis) where
  plus := ![v3419_pa,v3419_pb,v3419_pg]
  minus := ![(Primitive.Addresses.material3419 1).one,v3419_mb,v3419_mg]
  upper := v3419_upper
  lower := (Primitive.Addresses.material3419 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3419_pa_checked.trans (by decide +kernel)
    · exact v3419_pb_checked.trans (by decide +kernel)
    · exact v3419_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 90 Primitive.Addresses.material3419
    · exact v3419_mb_checked.trans (by decide +kernel)
    · exact v3419_mg_checked.trans (by decide +kernel)
  upper_error := v3419_upper_checked
  lower_error := reuse_lower_error 45 90 Primitive.Addresses.material3419

def v3420_pa : Scalar.QComplex := ((999998338942255616563936462833 : Int)/10^30,(-1822666379141844474617862402 : Int)/10^30)
theorem v3420_pa_checked : Scalar.distance (sourceCoefficient 45 91 1 0) v3420_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3420_pb : Scalar.QComplex := ((-786439484491795137628214 : Int)/10^30,(-431476756893202307608594349 : Int)/10^30)
theorem v3420_pb_checked : Scalar.distance (sourceCoefficient 45 91 1 1) v3420_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3420_pg : Scalar.QComplex := ((-93086270162207451207478 : Int)/10^30,(169665496808557599342 : Int)/10^30)
theorem v3420_pg_checked : Scalar.distance (sourceCoefficient 45 91 1 2) v3420_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3420_mb : Scalar.QComplex := ((-1158784199871522685556991 : Int)/10^30,(-431475917572831057431259358 : Int)/10^30)
theorem v3420_mb_checked : Scalar.distance (sourceCoefficient 45 91 3 1) v3420_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3420_mg : Scalar.QComplex := ((-93086089088252521633962 : Int)/10^30,(249994692334347024470 : Int)/10^30)
theorem v3420_mg_checked : Scalar.distance (sourceCoefficient 45 91 3 2) v3420_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3420_upper : Scalar.QComplex := ((999993703805378422088307245103 : Int)/10^30,(-3548570078368061565269121932 : Int)/10^30)
theorem v3420_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 91 5) 1) 14) v3420_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3420 : Material (45 : Basis) (91 : Basis) where
  plus := ![v3420_pa,v3420_pb,v3420_pg]
  minus := ![(Primitive.Addresses.material3420 1).one,v3420_mb,v3420_mg]
  upper := v3420_upper
  lower := (Primitive.Addresses.material3420 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3420_pa_checked.trans (by decide +kernel)
    · exact v3420_pb_checked.trans (by decide +kernel)
    · exact v3420_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 91 Primitive.Addresses.material3420
    · exact v3420_mb_checked.trans (by decide +kernel)
    · exact v3420_mg_checked.trans (by decide +kernel)
  upper_error := v3420_upper_checked
  lower_error := reuse_lower_error 45 91 Primitive.Addresses.material3420

def v3421_pa : Scalar.QComplex := ((999998280186342629324946833403 : Int)/10^30,(-1854622429763625507208934744 : Int)/10^30)
theorem v3421_pa_checked : Scalar.distance (sourceCoefficient 45 92 1 0) v3421_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3421_pb : Scalar.QComplex := ((-800227793423888522545298 : Int)/10^30,(-431476727736540141603064770 : Int)/10^30)
theorem v3421_pb_checked : Scalar.distance (sourceCoefficient 45 92 1 1) v3421_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3421_pg : Scalar.QComplex := ((-93086264282407133595227 : Int)/10^30,(172640170549980028510 : Int)/10^30)
theorem v3421_pg_checked : Scalar.distance (sourceCoefficient 45 92 1 2) v3421_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3421_mb : Scalar.QComplex := ((-1172572478508712216261254 : Int)/10^30,(-431475876517490141768597769 : Int)/10^30)
theorem v3421_mb_checked : Scalar.distance (sourceCoefficient 45 92 3 1) v3421_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3421_mg : Scalar.QComplex := ((-93086080641444928824487 : Int)/10^30,(252969359894159612677 : Int)/10^30)
theorem v3421_mg_checked : Scalar.distance (sourceCoefficient 45 92 3 2) v3421_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3421_upper : Scalar.QComplex := ((999993589896308601952121789621 : Int)/10^30,(-3580525979987683496928680042 : Int)/10^30)
theorem v3421_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 92 5) 1) 14) v3421_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3421 : Material (45 : Basis) (92 : Basis) where
  plus := ![v3421_pa,v3421_pb,v3421_pg]
  minus := ![(Primitive.Addresses.material3421 1).one,v3421_mb,v3421_mg]
  upper := v3421_upper
  lower := (Primitive.Addresses.material3421 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3421_pa_checked.trans (by decide +kernel)
    · exact v3421_pb_checked.trans (by decide +kernel)
    · exact v3421_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 92 Primitive.Addresses.material3421
    · exact v3421_mb_checked.trans (by decide +kernel)
    · exact v3421_mg_checked.trans (by decide +kernel)
  upper_error := v3421_upper_checked
  lower_error := reuse_lower_error 45 92 Primitive.Addresses.material3421

def v3422_pa : Scalar.QComplex := ((999998209129477750396925552813 : Int)/10^30,(-1892547974895743213938194591 : Int)/10^30)
theorem v3422_pa_checked : Scalar.distance (sourceCoefficient 45 93 1 0) v3422_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3422_pb : Scalar.QComplex := ((-816591802771548818164887 : Int)/10^30,(-431476692370952919776608166 : Int)/10^30)
theorem v3422_pb_checked : Scalar.distance (sourceCoefficient 45 93 1 1) v3422_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3422_pg : Scalar.QComplex := ((-93086257160328036735375 : Int)/10^30,(176170522977999692857 : Int)/10^30)
theorem v3422_pg_checked : Scalar.distance (sourceCoefficient 45 93 1 2) v3422_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3422_mb : Scalar.QComplex := ((-1188936451244394994058558 : Int)/10^30,(-431475827030513028757725582 : Int)/10^30)
theorem v3422_mb_checked : Scalar.distance (sourceCoefficient 45 93 3 1) v3422_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3422_mg : Scalar.QComplex := ((-93086070472833339630164 : Int)/10^30,(256499704861634228941 : Int)/10^30)
theorem v3422_mg_checked : Scalar.distance (sourceCoefficient 45 93 3 2) v3422_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3422_upper : Scalar.QComplex := ((999993453383499234420310965404 : Int)/10^30,(-3618451345996454224246729621 : Int)/10^30)
theorem v3422_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 93 5) 1) 14) v3422_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3422 : Material (45 : Basis) (93 : Basis) where
  plus := ![v3422_pa,v3422_pb,v3422_pg]
  minus := ![(Primitive.Addresses.material3422 1).one,v3422_mb,v3422_mg]
  upper := v3422_upper
  lower := (Primitive.Addresses.material3422 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3422_pa_checked.trans (by decide +kernel)
    · exact v3422_pb_checked.trans (by decide +kernel)
    · exact v3422_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 93 Primitive.Addresses.material3422
    · exact v3422_mb_checked.trans (by decide +kernel)
    · exact v3422_mg_checked.trans (by decide +kernel)
  upper_error := v3422_upper_checked
  lower_error := reuse_lower_error 45 93 Primitive.Addresses.material3422

def v3423_pa : Scalar.QComplex := ((999998123342604930211568806485 : Int)/10^30,(-1937346450250083275554692800 : Int)/10^30)
theorem v3423_pa_checked : Scalar.distance (sourceCoefficient 45 94 1 0) v3423_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3423_pb : Scalar.QComplex := ((-835921324071337749464146 : Int)/10^30,(-431476649530339883513917708 : Int)/10^30)
theorem v3423_pb_checked : Scalar.distance (sourceCoefficient 45 94 1 1) v3423_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3423_pg : Scalar.QComplex := ((-93086248546340571179132 : Int)/10^30,(180340651625967385587 : Int)/10^30)
theorem v3423_pg_checked : Scalar.distance (sourceCoefficient 45 94 1 2) v3423_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3423_mb : Scalar.QComplex := ((-1208265928377400161973190 : Int)/10^30,(-431475767509409631617623726 : Int)/10^30)
theorem v3423_mb_checked : Scalar.distance (sourceCoefficient 45 94 3 1) v3423_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3423_mg : Scalar.QComplex := ((-93086058260215873881275 : Int)/10^30,(260669824523389218556 : Int)/10^30)
theorem v3423_mg_checked : Scalar.distance (sourceCoefficient 45 94 3 2) v3423_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3423_upper : Scalar.QComplex := ((999993290278649808051088173797 : Int)/10^30,(-3663249606568367680820742821 : Int)/10^30)
theorem v3423_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 94 5) 1) 14) v3423_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3423 : Material (45 : Basis) (94 : Basis) where
  plus := ![v3423_pa,v3423_pb,v3423_pg]
  minus := ![(Primitive.Addresses.material3423 1).one,v3423_mb,v3423_mg]
  upper := v3423_upper
  lower := (Primitive.Addresses.material3423 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3423_pa_checked.trans (by decide +kernel)
    · exact v3423_pb_checked.trans (by decide +kernel)
    · exact v3423_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 94 Primitive.Addresses.material3423
    · exact v3423_mb_checked.trans (by decide +kernel)
    · exact v3423_mg_checked.trans (by decide +kernel)
  upper_error := v3423_upper_checked
  lower_error := reuse_lower_error 45 94 Primitive.Addresses.material3423

def v3424_pa : Scalar.QComplex := ((999998036587993284368049879010 : Int)/10^30,(-1981620588923256970189697924 : Int)/10^30)
theorem v3424_pa_checked : Scalar.distance (sourceCoefficient 45 95 1 0) v3424_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3424_pb : Scalar.QComplex := ((-855024604966373256326075 : Int)/10^30,(-431476606056756432953944070 : Int)/10^30)
theorem v3424_pb_checked : Scalar.distance (sourceCoefficient 45 95 1 1) v3424_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3424_pg : Scalar.QComplex := ((-93086239819033297752101 : Int)/10^30,(184461971545694012078 : Int)/10^30)
theorem v3424_pg_checked : Scalar.distance (sourceCoefficient 45 95 1 2) v3424_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3424_mb : Scalar.QComplex := ((-1227369164643666588228120 : Int)/10^30,(-431475707550571335676678938 : Int)/10^30)
theorem v3424_mb_checked : Scalar.distance (sourceCoefficient 45 95 3 1) v3424_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3424_mg : Scalar.QComplex := ((-93086045976398376664265 : Int)/10^30,(264791135377286971669 : Int)/10^30)
theorem v3424_mg_checked : Scalar.distance (sourceCoefficient 45 95 3 2) v3424_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3424_upper : Scalar.QComplex := ((999993127111020541598015972758 : Int)/10^30,(-3707523529569823243591808362 : Int)/10^30)
theorem v3424_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 95 5) 1) 14) v3424_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3424 : Material (45 : Basis) (95 : Basis) where
  plus := ![v3424_pa,v3424_pb,v3424_pg]
  minus := ![(Primitive.Addresses.material3424 1).one,v3424_mb,v3424_mg]
  upper := v3424_upper
  lower := (Primitive.Addresses.material3424 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3424_pa_checked.trans (by decide +kernel)
    · exact v3424_pb_checked.trans (by decide +kernel)
    · exact v3424_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 95 Primitive.Addresses.material3424
    · exact v3424_mb_checked.trans (by decide +kernel)
    · exact v3424_mg_checked.trans (by decide +kernel)
  upper_error := v3424_upper_checked
  lower_error := reuse_lower_error 45 95 Primitive.Addresses.material3424

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
