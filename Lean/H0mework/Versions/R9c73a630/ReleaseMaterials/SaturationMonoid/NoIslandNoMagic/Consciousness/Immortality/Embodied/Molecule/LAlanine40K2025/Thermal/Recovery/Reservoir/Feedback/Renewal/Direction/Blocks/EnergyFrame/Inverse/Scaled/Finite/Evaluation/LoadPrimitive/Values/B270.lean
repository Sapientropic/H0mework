import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B180

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4321_pa : Scalar.QComplex := ((999998218086828753334204942628 : Int)/10^30,(-1887809091851922861632111963 : Int)/10^30)
theorem v4321_pa_checked : Scalar.distance (sourceCoefficient 68 72 1 0) v4321_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4321_pb : Scalar.QComplex := ((-814547186058451331909114 : Int)/10^30,(-431476751606821763890726513 : Int)/10^30)
theorem v4321_pb_checked : Scalar.distance (sourceCoefficient 68 72 1 1) v4321_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4321_pg : Scalar.QComplex := ((-93086263966968730567820 : Int)/10^30,(175729408577919330037 : Int)/10^30)
theorem v4321_pg_checked : Scalar.distance (sourceCoefficient 68 72 1 2) v4321_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4321_mb : Scalar.QComplex := ((-1186891886410488681663249 : Int)/10^30,(-431475888030771953935430445 : Int)/10^30)
theorem v4321_mb_checked : Scalar.distance (sourceCoefficient 68 72 3 1) v4321_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4321_mg : Scalar.QComplex := ((-93086077660133359253474 : Int)/10^30,(256058596499625276255 : Int)/10^30)
theorem v4321_mg_checked : Scalar.distance (sourceCoefficient 68 72 3 2) v4321_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4321_upper : Scalar.QComplex := ((999993470519719121957926411282 : Int)/10^30,(-3613712485470218723939394922 : Int)/10^30)
theorem v4321_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 72 5) 1) 14) v4321_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4321 : Material (68 : Basis) (72 : Basis) where
  plus := ![v4321_pa,v4321_pb,v4321_pg]
  minus := ![(Primitive.Addresses.material4321 1).one,v4321_mb,v4321_mg]
  upper := v4321_upper
  lower := (Primitive.Addresses.material4321 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4321_pa_checked.trans (by decide +kernel)
    · exact v4321_pb_checked.trans (by decide +kernel)
    · exact v4321_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 72 Primitive.Addresses.material4321
    · exact v4321_mb_checked.trans (by decide +kernel)
    · exact v4321_mg_checked.trans (by decide +kernel)
  upper_error := v4321_upper_checked
  lower_error := reuse_lower_error 68 72 Primitive.Addresses.material4321

def v4322_pa : Scalar.QComplex := ((999998200203059688143576030033 : Int)/10^30,(-1897258717559280709502483803 : Int)/10^30)
theorem v4322_pa_checked : Scalar.distance (sourceCoefficient 68 73 1 0) v4322_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4322_pb : Scalar.QComplex := ((-818624486892670552084969 : Int)/10^30,(-431476743766362760585815967 : Int)/10^30)
theorem v4322_pb_checked : Scalar.distance (sourceCoefficient 68 73 1 1) v4322_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4322_pg : Scalar.QComplex := ((-93086262288855130071308 : Int)/10^30,(176609040472950792925 : Int)/10^30)
theorem v4322_pg_checked : Scalar.distance (sourceCoefficient 68 73 1 2) v4322_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4322_mb : Scalar.QComplex := ((-1190969178960579460718588 : Int)/10^30,(-431475876671788884873275053 : Int)/10^30)
theorem v4322_mb_checked : Scalar.distance (sourceCoefficient 68 73 3 1) v4322_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4322_mg : Scalar.QComplex := ((-93086075222937675333090 : Int)/10^30,(256938226618993125662 : Int)/10^30)
theorem v4322_mg_checked : Scalar.distance (sourceCoefficient 68 73 3 2) v4322_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4322_upper : Scalar.QComplex := ((999993436326779984988497319790 : Int)/10^30,(-3623162066237706108048317221 : Int)/10^30)
theorem v4322_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 73 5) 1) 14) v4322_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4322 : Material (68 : Basis) (73 : Basis) where
  plus := ![v4322_pa,v4322_pb,v4322_pg]
  minus := ![(Primitive.Addresses.material4322 1).one,v4322_mb,v4322_mg]
  upper := v4322_upper
  lower := (Primitive.Addresses.material4322 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4322_pa_checked.trans (by decide +kernel)
    · exact v4322_pb_checked.trans (by decide +kernel)
    · exact v4322_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 73 Primitive.Addresses.material4322
    · exact v4322_mb_checked.trans (by decide +kernel)
    · exact v4322_mg_checked.trans (by decide +kernel)
  upper_error := v4322_upper_checked
  lower_error := reuse_lower_error 68 73 Primitive.Addresses.material4322

def v4323_pa : Scalar.QComplex := ((999998179972651748762071978069 : Int)/10^30,(-1907891869054147280557446297 : Int)/10^30)
theorem v4323_pa_checked : Scalar.distance (sourceCoefficient 68 74 1 0) v4323_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4323_pb : Scalar.QComplex := ((-823212452437517173633427 : Int)/10^30,(-431476734882492978727100988 : Int)/10^30)
theorem v4323_pb_checked : Scalar.distance (sourceCoefficient 68 74 1 1) v4323_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4323_pg : Scalar.QComplex := ((-93086260388969332808385 : Int)/10^30,(177598842551522196749 : Int)/10^30)
theorem v4323_pg_checked : Scalar.distance (sourceCoefficient 68 74 1 2) v4323_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4323_mb : Scalar.QComplex := ((-1195557135130737322434778 : Int)/10^30,(-431475863828714779980172577 : Int)/10^30)
theorem v4323_mb_checked : Scalar.distance (sourceCoefficient 68 74 3 1) v4323_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4323_mg : Scalar.QComplex := ((-93086072468897970708125 : Int)/10^30,(257928026689500104086 : Int)/10^30)
theorem v4323_mg_checked : Scalar.distance (sourceCoefficient 68 74 3 2) v4323_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4323_upper : Scalar.QComplex := ((999993397744547328251809567460 : Int)/10^30,(-3633795166979893770114927640 : Int)/10^30)
theorem v4323_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 74 5) 1) 14) v4323_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4323 : Material (68 : Basis) (74 : Basis) where
  plus := ![v4323_pa,v4323_pb,v4323_pg]
  minus := ![(Primitive.Addresses.material4323 1).one,v4323_mb,v4323_mg]
  upper := v4323_upper
  lower := (Primitive.Addresses.material4323 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4323_pa_checked.trans (by decide +kernel)
    · exact v4323_pb_checked.trans (by decide +kernel)
    · exact v4323_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 74 Primitive.Addresses.material4323
    · exact v4323_mb_checked.trans (by decide +kernel)
    · exact v4323_mg_checked.trans (by decide +kernel)
  upper_error := v4323_upper_checked
  lower_error := reuse_lower_error 68 74 Primitive.Addresses.material4323

def v4324_pa : Scalar.QComplex := ((999998151597243880706066137853 : Int)/10^30,(-1922706970821565164879835182 : Int)/10^30)
theorem v4324_pa_checked : Scalar.distance (sourceCoefficient 68 75 1 0) v4324_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4324_pb : Scalar.QComplex := ((-829604835342286370783488 : Int)/10^30,(-431476722396203717736085687 : Int)/10^30)
theorem v4324_pb_checked : Scalar.distance (sourceCoefficient 68 75 1 1) v4324_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4324_pg : Scalar.QComplex := ((-93086257721398278491090 : Int)/10^30,(178977927431919564553 : Int)/10^30)
theorem v4324_pg_checked : Scalar.distance (sourceCoefficient 68 75 1 2) v4324_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4324_mb : Scalar.QComplex := ((-1201949504880224947165422 : Int)/10^30,(-431475845826091623628080953 : Int)/10^30)
theorem v4324_mb_checked : Scalar.distance (sourceCoefficient 68 75 3 1) v4324_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4324_mg : Scalar.QComplex := ((-93086068611239769543838 : Int)/10^30,(259307108754407466690 : Int)/10^30)
theorem v4324_mg_checked : Scalar.distance (sourceCoefficient 68 75 3 2) v4324_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4324_upper : Scalar.QComplex := ((999993343799660087002812267131 : Int)/10^30,(-3648610197708578092600275662 : Int)/10^30)
theorem v4324_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 75 5) 1) 14) v4324_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4324 : Material (68 : Basis) (75 : Basis) where
  plus := ![v4324_pa,v4324_pb,v4324_pg]
  minus := ![(Primitive.Addresses.material4324 1).one,v4324_mb,v4324_mg]
  upper := v4324_upper
  lower := (Primitive.Addresses.material4324 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4324_pa_checked.trans (by decide +kernel)
    · exact v4324_pb_checked.trans (by decide +kernel)
    · exact v4324_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 75 Primitive.Addresses.material4324
    · exact v4324_mb_checked.trans (by decide +kernel)
    · exact v4324_mg_checked.trans (by decide +kernel)
  upper_error := v4324_upper_checked
  lower_error := reuse_lower_error 68 75 Primitive.Addresses.material4324

def v4325_pa : Scalar.QComplex := ((999998127620385987871896993574 : Int)/10^30,(-1935137132664979181786697375 : Int)/10^30)
theorem v4325_pa_checked : Scalar.distance (sourceCoefficient 68 76 1 0) v4325_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4325_pb : Scalar.QComplex := ((-834968170305371645582583 : Int)/10^30,(-431476711822543946725430110 : Int)/10^30)
theorem v4325_pb_checked : Scalar.distance (sourceCoefficient 68 76 1 1) v4325_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4325_pg : Scalar.QComplex := ((-93086255464864048450293 : Int)/10^30,(180135006771911213146 : Int)/10^30)
theorem v4325_pg_checked : Scalar.distance (sourceCoefficient 68 76 1 2) v4325_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4325_mb : Scalar.QComplex := ((-1207312828721703336266830 : Int)/10^30,(-431475830624119272171376612 : Int)/10^30)
theorem v4325_mb_checked : Scalar.distance (sourceCoefficient 68 76 3 1) v4325_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4325_mg : Scalar.QComplex := ((-93086065356199022220022 : Int)/10^30,(260464185716278185869 : Int)/10^30)
theorem v4325_mg_checked : Scalar.distance (sourceCoefficient 68 76 3 2) v4325_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4325_upper : Scalar.QComplex := ((999993298369506218623035110220 : Int)/10^30,(-3661040299656844633646803446 : Int)/10^30)
theorem v4325_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 76 5) 1) 14) v4325_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4325 : Material (68 : Basis) (76 : Basis) where
  plus := ![v4325_pa,v4325_pb,v4325_pg]
  minus := ![(Primitive.Addresses.material4325 1).one,v4325_mb,v4325_mg]
  upper := v4325_upper
  lower := (Primitive.Addresses.material4325 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4325_pa_checked.trans (by decide +kernel)
    · exact v4325_pb_checked.trans (by decide +kernel)
    · exact v4325_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 76 Primitive.Addresses.material4325
    · exact v4325_mb_checked.trans (by decide +kernel)
    · exact v4325_mg_checked.trans (by decide +kernel)
  upper_error := v4325_upper_checked
  lower_error := reuse_lower_error 68 76 Primitive.Addresses.material4325

def v4326_pa : Scalar.QComplex := ((999998122047514019248959839062 : Int)/10^30,(-1938014820700802194729300269 : Int)/10^30)
theorem v4326_pa_checked : Scalar.distance (sourceCoefficient 68 77 1 0) v4326_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4326_pb : Scalar.QComplex := ((-836209827893055761529111 : Int)/10^30,(-431476709361980443128716116 : Int)/10^30)
theorem v4326_pb_checked : Scalar.distance (sourceCoefficient 68 77 1 1) v4326_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4326_pg : Scalar.QComplex := ((-93086254940065198034188 : Int)/10^30,(180402880465417465437 : Int)/10^30)
theorem v4326_pg_checked : Scalar.distance (sourceCoefficient 68 77 1 2) v4326_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4326_mb : Scalar.QComplex := ((-1208554483723706101825886 : Int)/10^30,(-431475827092062108765336576 : Int)/10^30)
theorem v4326_mb_checked : Scalar.distance (sourceCoefficient 68 77 3 1) v4326_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4326_mg : Scalar.QComplex := ((-93086064600237434297915 : Int)/10^30,(260732058857165047789 : Int)/10^30)
theorem v4326_mg_checked : Scalar.distance (sourceCoefficient 68 77 3 2) v4326_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4326_upper : Scalar.QComplex := ((999993287830014062127046198546 : Int)/10^30,(-3663917973788417903366050525 : Int)/10^30)
theorem v4326_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 77 5) 1) 14) v4326_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4326 : Material (68 : Basis) (77 : Basis) where
  plus := ![v4326_pa,v4326_pb,v4326_pg]
  minus := ![(Primitive.Addresses.material4326 1).one,v4326_mb,v4326_mg]
  upper := v4326_upper
  lower := (Primitive.Addresses.material4326 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4326_pa_checked.trans (by decide +kernel)
    · exact v4326_pb_checked.trans (by decide +kernel)
    · exact v4326_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 77 Primitive.Addresses.material4326
    · exact v4326_mb_checked.trans (by decide +kernel)
    · exact v4326_mg_checked.trans (by decide +kernel)
  upper_error := v4326_upper_checked
  lower_error := reuse_lower_error 68 77 Primitive.Addresses.material4326

def v4327_pa : Scalar.QComplex := ((999998088371016043640513907234 : Int)/10^30,(-1955314377175022632979797673 : Int)/10^30)
theorem v4327_pa_checked : Scalar.distance (sourceCoefficient 68 78 1 0) v4327_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4327_pb : Scalar.QComplex := ((-843674196904429306804771 : Int)/10^30,(-431476694469609221851241530 : Int)/10^30)
theorem v4327_pb_checked : Scalar.distance (sourceCoefficient 68 78 1 1) v4327_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4327_pg : Scalar.QComplex := ((-93086251766221785515719 : Int)/10^30,(182013234337601524468 : Int)/10^30)
theorem v4327_pg_checked : Scalar.distance (sourceCoefficient 68 78 1 2) v4327_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4327_mb : Scalar.QComplex := ((-1216018837104308289189541 : Int)/10^30,(-431475805758282158483496893 : Int)/10^30)
theorem v4327_mb_checked : Scalar.distance (sourceCoefficient 68 78 3 1) v4327_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4327_mg : Scalar.QComplex := ((-93086060036732339497607 : Int)/10^30,(262342409390856842996 : Int)/10^30)
theorem v4327_mg_checked : Scalar.distance (sourceCoefficient 68 78 3 2) v4327_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4327_upper : Scalar.QComplex := ((999993224296101172705773062997 : Int)/10^30,(-3681217446374400724050299471 : Int)/10^30)
theorem v4327_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 78 5) 1) 14) v4327_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4327 : Material (68 : Basis) (78 : Basis) where
  plus := ![v4327_pa,v4327_pb,v4327_pg]
  minus := ![(Primitive.Addresses.material4327 1).one,v4327_mb,v4327_mg]
  upper := v4327_upper
  lower := (Primitive.Addresses.material4327 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4327_pa_checked.trans (by decide +kernel)
    · exact v4327_pb_checked.trans (by decide +kernel)
    · exact v4327_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 78 Primitive.Addresses.material4327
    · exact v4327_mb_checked.trans (by decide +kernel)
    · exact v4327_mg_checked.trans (by decide +kernel)
  upper_error := v4327_upper_checked
  lower_error := reuse_lower_error 68 78 Primitive.Addresses.material4327

def v4328_pa : Scalar.QComplex := ((999998077450517358131988394268 : Int)/10^30,(-1960891447553184372013608237 : Int)/10^30)
theorem v4328_pa_checked : Scalar.distance (sourceCoefficient 68 79 1 0) v4328_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4328_pb : Scalar.QComplex := ((-846080577149474629203178 : Int)/10^30,(-431476689631872618165954557 : Int)/10^30)
theorem v4328_pb_checked : Scalar.distance (sourceCoefficient 68 79 1 1) v4328_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4328_pg : Scalar.QComplex := ((-93086250736102994425250 : Int)/10^30,(182532383880755870370 : Int)/10^30)
theorem v4328_pg_checked : Scalar.distance (sourceCoefficient 68 79 1 2) v4328_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4328_mb : Scalar.QComplex := ((-1218425212278599463935410 : Int)/10^30,(-431475798843949583977536243 : Int)/10^30)
theorem v4328_mb_checked : Scalar.distance (sourceCoefficient 68 79 3 1) v4328_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4328_mg : Scalar.QComplex := ((-93086058558611257852700 : Int)/10^30,(262861557851761965793 : Int)/10^30)
theorem v4328_mg_checked : Scalar.distance (sourceCoefficient 68 79 3 2) v4328_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4328_upper : Scalar.QComplex := ((999993203750101227162525100724 : Int)/10^30,(-3686794489598381232233211631 : Int)/10^30)
theorem v4328_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 79 5) 1) 14) v4328_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4328 : Material (68 : Basis) (79 : Basis) where
  plus := ![v4328_pa,v4328_pb,v4328_pg]
  minus := ![(Primitive.Addresses.material4328 1).one,v4328_mb,v4328_mg]
  upper := v4328_upper
  lower := (Primitive.Addresses.material4328 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4328_pa_checked.trans (by decide +kernel)
    · exact v4328_pb_checked.trans (by decide +kernel)
    · exact v4328_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 79 Primitive.Addresses.material4328
    · exact v4328_mb_checked.trans (by decide +kernel)
    · exact v4328_mg_checked.trans (by decide +kernel)
  upper_error := v4328_upper_checked
  lower_error := reuse_lower_error 68 79 Primitive.Addresses.material4328

def v4329_pa : Scalar.QComplex := ((999998060329376448068857750403 : Int)/10^30,(-1969603382608218007667873377 : Int)/10^30)
theorem v4329_pa_checked : Scalar.distance (sourceCoefficient 68 80 1 0) v4329_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4329_pb : Scalar.QComplex := ((-849839580869536472244593 : Int)/10^30,(-431476682039041523139525861 : Int)/10^30)
theorem v4329_pb_checked : Scalar.distance (sourceCoefficient 68 80 1 1) v4329_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4329_pg : Scalar.QComplex := ((-93086249120196030386102 : Int)/10^30,(183343346767153106874 : Int)/10^30)
theorem v4329_pg_checked : Scalar.distance (sourceCoefficient 68 80 1 2) v4329_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4329_mb : Scalar.QComplex := ((-1222184208046741160451199 : Int)/10^30,(-431475788007270404938631480 : Int)/10^30)
theorem v4329_mb_checked : Scalar.distance (sourceCoefficient 68 80 3 1) v4329_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4329_mg : Scalar.QComplex := ((-93086056242880448941303 : Int)/10^30,(263672519041745724638 : Int)/10^30)
theorem v4329_mg_checked : Scalar.distance (sourceCoefficient 68 80 3 2) v4329_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4329_upper : Scalar.QComplex := ((999993171592976252613925259501 : Int)/10^30,(-3695506382128474986195994413 : Int)/10^30)
theorem v4329_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 80 5) 1) 14) v4329_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4329 : Material (68 : Basis) (80 : Basis) where
  plus := ![v4329_pa,v4329_pb,v4329_pg]
  minus := ![(Primitive.Addresses.material4329 1).one,v4329_mb,v4329_mg]
  upper := v4329_upper
  lower := (Primitive.Addresses.material4329 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4329_pa_checked.trans (by decide +kernel)
    · exact v4329_pb_checked.trans (by decide +kernel)
    · exact v4329_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 80 Primitive.Addresses.material4329
    · exact v4329_mb_checked.trans (by decide +kernel)
    · exact v4329_mg_checked.trans (by decide +kernel)
  upper_error := v4329_upper_checked
  lower_error := reuse_lower_error 68 80 Primitive.Addresses.material4329

def v4330_pa : Scalar.QComplex := ((999998008318403989169199416873 : Int)/10^30,(-1995835470479989668859235988 : Int)/10^30)
theorem v4330_pa_checked : Scalar.distance (sourceCoefficient 68 81 1 0) v4330_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4330_pb : Scalar.QComplex := ((-861158135695481970885824 : Int)/10^30,(-431476658912955140818582094 : Int)/10^30)
theorem v4330_pb_checked : Scalar.distance (sourceCoefficient 68 81 1 1) v4330_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4330_pg : Scalar.QComplex := ((-93086244204841438378290 : Int)/10^30,(185785198022744637101 : Int)/10^30)
theorem v4330_pg_checked : Scalar.distance (sourceCoefficient 68 81 1 2) v4330_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4330_mb : Scalar.QComplex := ((-1233502738701500426206202 : Int)/10^30,(-431475755113789587511450631 : Int)/10^30)
theorem v4330_mb_checked : Scalar.distance (sourceCoefficient 68 81 3 1) v4330_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4330_mg : Scalar.QComplex := ((-93086049220320030467175 : Int)/10^30,(266114365146394800743 : Int)/10^30)
theorem v4330_mg_checked : Scalar.distance (sourceCoefficient 68 81 3 2) v4330_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4330_upper : Scalar.QComplex := ((999993074307877347692309362144 : Int)/10^30,(-3721738341164413134386618620 : Int)/10^30)
theorem v4330_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 81 5) 1) 14) v4330_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4330 : Material (68 : Basis) (81 : Basis) where
  plus := ![v4330_pa,v4330_pb,v4330_pg]
  minus := ![(Primitive.Addresses.material4330 1).one,v4330_mb,v4330_mg]
  upper := v4330_upper
  lower := (Primitive.Addresses.material4330 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4330_pa_checked.trans (by decide +kernel)
    · exact v4330_pb_checked.trans (by decide +kernel)
    · exact v4330_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 81 Primitive.Addresses.material4330
    · exact v4330_mb_checked.trans (by decide +kernel)
    · exact v4330_mg_checked.trans (by decide +kernel)
  upper_error := v4330_upper_checked
  lower_error := reuse_lower_error 68 81 Primitive.Addresses.material4330

def v4331_pa : Scalar.QComplex := ((999997988429878407718818280690 : Int)/10^30,(-2005775709487530981315726847 : Int)/10^30)
theorem v4331_pa_checked : Scalar.distance (sourceCoefficient 68 82 1 0) v4331_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4331_pb : Scalar.QComplex := ((-865447124781413837556998 : Int)/10^30,(-431476650046257776624787146 : Int)/10^30)
theorem v4331_pb_checked : Scalar.distance (sourceCoefficient 68 82 1 1) v4331_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4331_pg : Scalar.QComplex := ((-93086242322720323420533 : Int)/10^30,(186710499319644409557 : Int)/10^30)
theorem v4331_pg_checked : Scalar.distance (sourceCoefficient 68 82 1 2) v4331_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4331_mb : Scalar.QComplex := ((-1237791718538885155626100 : Int)/10^30,(-431475742545891112532775349 : Int)/10^30)
theorem v4331_mb_checked : Scalar.distance (sourceCoefficient 68 82 3 1) v4331_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4331_mg : Scalar.QComplex := ((-93086046539706271108023 : Int)/10^30,(267039664474576857384 : Int)/10^30)
theorem v4331_mg_checked : Scalar.distance (sourceCoefficient 68 82 3 2) v4331_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4331_upper : Scalar.QComplex := ((999993037263430632286718414983 : Int)/10^30,(-3731678531041345226971151683 : Int)/10^30)
theorem v4331_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 82 5) 1) 14) v4331_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4331 : Material (68 : Basis) (82 : Basis) where
  plus := ![v4331_pa,v4331_pb,v4331_pg]
  minus := ![(Primitive.Addresses.material4331 1).one,v4331_mb,v4331_mg]
  upper := v4331_upper
  lower := (Primitive.Addresses.material4331 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4331_pa_checked.trans (by decide +kernel)
    · exact v4331_pb_checked.trans (by decide +kernel)
    · exact v4331_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 82 Primitive.Addresses.material4331
    · exact v4331_mb_checked.trans (by decide +kernel)
    · exact v4331_mg_checked.trans (by decide +kernel)
  upper_error := v4331_upper_checked
  lower_error := reuse_lower_error 68 82 Primitive.Addresses.material4331

def v4332_pa : Scalar.QComplex := ((999997961122214808777494961974 : Int)/10^30,(-2019344302826989943175940805 : Int)/10^30)
theorem v4332_pa_checked : Scalar.distance (sourceCoefficient 68 83 1 0) v4332_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4332_pb : Scalar.QComplex := ((-871301666925601575836235 : Int)/10^30,(-431476637851310727558655412 : Int)/10^30)
theorem v4332_pb_checked : Scalar.distance (sourceCoefficient 68 83 1 1) v4332_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4332_pg : Scalar.QComplex := ((-93086239736272425549641 : Int)/10^30,(187973551138126708396 : Int)/10^30)
theorem v4332_pg_checked : Scalar.distance (sourceCoefficient 68 83 1 2) v4332_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4332_mb : Scalar.QComplex := ((-1243646247979469224512504 : Int)/10^30,(-431475725298742412558705893 : Int)/10^30)
theorem v4332_mb_checked : Scalar.distance (sourceCoefficient 68 83 3 1) v4332_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4332_mg : Scalar.QComplex := ((-93086042863302502681872 : Int)/10^30,(268302713590779193309 : Int)/10^30)
theorem v4332_mg_checked : Scalar.distance (sourceCoefficient 68 83 3 2) v4332_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4332_upper : Scalar.QComplex := ((999992986537646534168607507731 : Int)/10^30,(-3745247057041428248761900670 : Int)/10^30)
theorem v4332_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 83 5) 1) 14) v4332_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4332 : Material (68 : Basis) (83 : Basis) where
  plus := ![v4332_pa,v4332_pb,v4332_pg]
  minus := ![(Primitive.Addresses.material4332 1).one,v4332_mb,v4332_mg]
  upper := v4332_upper
  lower := (Primitive.Addresses.material4332 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4332_pa_checked.trans (by decide +kernel)
    · exact v4332_pb_checked.trans (by decide +kernel)
    · exact v4332_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 83 Primitive.Addresses.material4332
    · exact v4332_mb_checked.trans (by decide +kernel)
    · exact v4332_mg_checked.trans (by decide +kernel)
  upper_error := v4332_upper_checked
  lower_error := reuse_lower_error 68 83 Primitive.Addresses.material4332

def v4333_pa : Scalar.QComplex := ((999997889546984475963130891620 : Int)/10^30,(-2054483287115313333941678657 : Int)/10^30)
theorem v4333_pa_checked : Scalar.distance (sourceCoefficient 68 84 1 0) v4333_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4333_pb : Scalar.QComplex := ((-886463346190091865173873 : Int)/10^30,(-431476605777370210768830161 : Int)/10^30)
theorem v4333_pb_checked : Scalar.distance (sourceCoefficient 68 84 1 1) v4333_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4333_pg : Scalar.QComplex := ((-93086232945134849381855 : Int)/10^30,(191244513458862551565 : Int)/10^30)
theorem v4333_pg_checked : Scalar.distance (sourceCoefficient 68 84 1 2) v4333_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4333_mb : Scalar.QComplex := ((-1258807893920207291373724 : Int)/10^30,(-431475680140967489792907795 : Int)/10^30)
theorem v4333_mb_checked : Scalar.distance (sourceCoefficient 68 84 3 1) v4333_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4333_mg : Scalar.QComplex := ((-93086033249474291044143 : Int)/10^30,(271573668833140407355 : Int)/10^30)
theorem v4333_mg_checked : Scalar.distance (sourceCoefficient 68 84 3 2) v4333_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4333_upper : Scalar.QComplex := ((999992854315823706358871109914 : Int)/10^30,(-3780385865462007956856304614 : Int)/10^30)
theorem v4333_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 84 5) 1) 14) v4333_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4333 : Material (68 : Basis) (84 : Basis) where
  plus := ![v4333_pa,v4333_pb,v4333_pg]
  minus := ![(Primitive.Addresses.material4333 1).one,v4333_mb,v4333_mg]
  upper := v4333_upper
  lower := (Primitive.Addresses.material4333 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4333_pa_checked.trans (by decide +kernel)
    · exact v4333_pb_checked.trans (by decide +kernel)
    · exact v4333_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 84 Primitive.Addresses.material4333
    · exact v4333_mb_checked.trans (by decide +kernel)
    · exact v4333_mg_checked.trans (by decide +kernel)
  upper_error := v4333_upper_checked
  lower_error := reuse_lower_error 68 84 Primitive.Addresses.material4333

def v4334_pa : Scalar.QComplex := ((999997724001090874842226466194 : Int)/10^30,(-2133539931212744189579960228 : Int)/10^30)
theorem v4334_pa_checked : Scalar.distance (sourceCoefficient 68 85 1 0) v4334_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4334_pb : Scalar.QComplex := ((-920574503538109892545831 : Int)/10^30,(-431476531019634310495347129 : Int)/10^30)
theorem v4334_pb_checked : Scalar.distance (sourceCoefficient 68 85 1 1) v4334_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4334_pg : Scalar.QComplex := ((-93086217176025726167602 : Int)/10^30,(198603613412199968978 : Int)/10^30)
theorem v4334_pg_checked : Scalar.distance (sourceCoefficient 68 85 1 2) v4334_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4334_mb : Scalar.QComplex := ((-1292918974054523362675106 : Int)/10^30,(-431475575946866943398005608 : Int)/10^30)
theorem v4334_mb_checked : Scalar.distance (sourceCoefficient 68 85 3 1) v4334_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4334_mg : Scalar.QComplex := ((-93086011129799221217919 : Int)/10^30,(278932752438317625634 : Int)/10^30)
theorem v4334_mg_checked : Scalar.distance (sourceCoefficient 68 85 3 2) v4334_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4334_upper : Scalar.QComplex := ((999992552325580916962662643578 : Int)/10^30,(-3859442106096659925755320156 : Int)/10^30)
theorem v4334_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 85 5) 1) 14) v4334_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4334 : Material (68 : Basis) (85 : Basis) where
  plus := ![v4334_pa,v4334_pb,v4334_pg]
  minus := ![(Primitive.Addresses.material4334 1).one,v4334_mb,v4334_mg]
  upper := v4334_upper
  lower := (Primitive.Addresses.material4334 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4334_pa_checked.trans (by decide +kernel)
    · exact v4334_pb_checked.trans (by decide +kernel)
    · exact v4334_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 85 Primitive.Addresses.material4334
    · exact v4334_mb_checked.trans (by decide +kernel)
    · exact v4334_mg_checked.trans (by decide +kernel)
  upper_error := v4334_upper_checked
  lower_error := reuse_lower_error 68 85 Primitive.Addresses.material4334

def v4335_pa : Scalar.QComplex := ((999997692777814625082076881165 : Int)/10^30,(-2148124541891280371586044805 : Int)/10^30)
theorem v4335_pa_checked : Scalar.distance (sourceCoefficient 68 86 1 0) v4335_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4335_pb : Scalar.QComplex := ((-926867433552661988143168 : Int)/10^30,(-431476516835245188734743956 : Int)/10^30)
theorem v4335_pb_checked : Scalar.distance (sourceCoefficient 68 86 1 1) v4335_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4335_pg : Scalar.QComplex := ((-93086214192732733693331 : Int)/10^30,(199961242574172686943 : Int)/10^30)
theorem v4335_pg_checked : Scalar.distance (sourceCoefficient 68 86 1 2) v4335_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4335_mb : Scalar.QComplex := ((-1299211889485441041836995 : Int)/10^30,(-431475556331967923621969956 : Int)/10^30)
theorem v4335_mb_checked : Scalar.distance (sourceCoefficient 68 86 3 1) v4335_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4335_mg : Scalar.QComplex := ((-93086006974934518125150 : Int)/10^30,(280290378520335469902 : Int)/10^30)
theorem v4335_mg_checked : Scalar.distance (sourceCoefficient 68 86 3 2) v4335_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4335_upper : Scalar.QComplex := ((999992495930636244996516741139 : Int)/10^30,(-3874026641164589477208482426 : Int)/10^30)
theorem v4335_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 86 5) 1) 14) v4335_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4335 : Material (68 : Basis) (86 : Basis) where
  plus := ![v4335_pa,v4335_pb,v4335_pg]
  minus := ![(Primitive.Addresses.material4335 1).one,v4335_mb,v4335_mg]
  upper := v4335_upper
  lower := (Primitive.Addresses.material4335 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4335_pa_checked.trans (by decide +kernel)
    · exact v4335_pb_checked.trans (by decide +kernel)
    · exact v4335_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 86 Primitive.Addresses.material4335
    · exact v4335_mb_checked.trans (by decide +kernel)
    · exact v4335_mg_checked.trans (by decide +kernel)
  upper_error := v4335_upper_checked
  lower_error := reuse_lower_error 68 86 Primitive.Addresses.material4335

def v4336_pa : Scalar.QComplex := ((999997690702783172260687275135 : Int)/10^30,(-2149090296102479491419282593 : Int)/10^30)
theorem v4336_pa_checked : Scalar.distance (sourceCoefficient 68 87 1 0) v4336_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4336_pb : Scalar.QComplex := ((-927284134673572402228192 : Int)/10^30,(-431476515891672658746628801 : Int)/10^30)
theorem v4336_pb_checked : Scalar.distance (sourceCoefficient 68 87 1 1) v4336_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4336_pg : Scalar.QComplex := ((-93086213994371510019123 : Int)/10^30,(200051141173766174461 : Int)/10^30)
theorem v4336_pg_checked : Scalar.distance (sourceCoefficient 68 87 1 2) v4336_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4336_mb : Scalar.QComplex := ((-1299628589636933987974491 : Int)/10^30,(-431475555028801445145146403 : Int)/10^30)
theorem v4336_mb_checked : Scalar.distance (sourceCoefficient 68 87 3 1) v4336_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4336_mg : Scalar.QComplex := ((-93086006698994925743335 : Int)/10^30,(280380276915278798049 : Int)/10^30)
theorem v4336_mg_checked : Scalar.distance (sourceCoefficient 68 87 3 2) v4336_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4336_upper : Scalar.QComplex := ((999992492188803726698693361777 : Int)/10^30,(-3874992390356095102732576765 : Int)/10^30)
theorem v4336_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 87 5) 1) 14) v4336_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4336 : Material (68 : Basis) (87 : Basis) where
  plus := ![v4336_pa,v4336_pb,v4336_pg]
  minus := ![(Primitive.Addresses.material4336 1).one,v4336_mb,v4336_mg]
  upper := v4336_upper
  lower := (Primitive.Addresses.material4336 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4336_pa_checked.trans (by decide +kernel)
    · exact v4336_pb_checked.trans (by decide +kernel)
    · exact v4336_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 87 Primitive.Addresses.material4336
    · exact v4336_mb_checked.trans (by decide +kernel)
    · exact v4336_mg_checked.trans (by decide +kernel)
  upper_error := v4336_upper_checked
  lower_error := reuse_lower_error 68 87 Primitive.Addresses.material4336

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
