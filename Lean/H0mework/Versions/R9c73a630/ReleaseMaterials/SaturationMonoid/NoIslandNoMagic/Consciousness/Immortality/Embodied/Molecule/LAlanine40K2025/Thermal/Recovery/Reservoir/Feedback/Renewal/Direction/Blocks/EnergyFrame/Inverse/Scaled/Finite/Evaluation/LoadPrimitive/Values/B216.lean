import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B144

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3457_pa : Scalar.QComplex := ((999998784537384801652033326618 : Int)/10^30,(-1559141992586732617549565354 : Int)/10^30)
theorem v3457_pa_checked : Scalar.distance (sourceCoefficient 46 77 1 0) v3457_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3457_pb : Scalar.QComplex := ((-672734692042097244757682 : Int)/10^30,(-431476977438157219634587254 : Int)/10^30)
theorem v3457_pb_checked : Scalar.distance (sourceCoefficient 46 77 1 1) v3457_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3457_pg : Scalar.QComplex := ((-93086314691686058425043 : Int)/10^30,(145134958577067352835 : Int)/10^30)
theorem v3457_pg_checked : Scalar.distance (sourceCoefficient 46 77 1 2) v3457_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3457_mb : Scalar.QComplex := ((-1045079640079678700478089 : Int)/10^30,(-431476236239818660831676730 : Int)/10^30)
theorem v3457_mb_checked : Scalar.distance (sourceCoefficient 46 77 3 1) v3457_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3457_mg : Scalar.QComplex := ((-93086154786464227838320 : Int)/10^30,(225464201663631767288 : Int)/10^30)
theorem v3457_mg_checked : Scalar.distance (sourceCoefficient 46 77 3 2) v3457_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3457_upper : Scalar.QComplex := ((999994604219028394098797382726 : Int)/10^30,(-3285046853358336632190332799 : Int)/10^30)
theorem v3457_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 77 5) 1) 14) v3457_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3457 : Material (46 : Basis) (77 : Basis) where
  plus := ![v3457_pa,v3457_pb,v3457_pg]
  minus := ![(Primitive.Addresses.material3457 1).one,v3457_mb,v3457_mg]
  upper := v3457_upper
  lower := (Primitive.Addresses.material3457 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3457_pa_checked.trans (by decide +kernel)
    · exact v3457_pb_checked.trans (by decide +kernel)
    · exact v3457_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 77 Primitive.Addresses.material3457
    · exact v3457_mb_checked.trans (by decide +kernel)
    · exact v3457_mg_checked.trans (by decide +kernel)
  upper_error := v3457_upper_checked
  lower_error := reuse_lower_error 46 77 Primitive.Addresses.material3457

def v3458_pa : Scalar.QComplex := ((999998757415231032037432798082 : Int)/10^30,(-1576441560578449436116211882 : Int)/10^30)
theorem v3458_pa_checked : Scalar.distance (sourceCoefficient 46 78 1 0) v3458_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3458_pb : Scalar.QComplex := ((-680199064366497920744994 : Int)/10^30,(-431476964431154089786582312 : Int)/10^30)
theorem v3458_pb_checked : Scalar.distance (sourceCoefficient 46 78 1 1) v3458_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3458_pg : Scalar.QComplex := ((-93086312026276393848861 : Int)/10^30,(146745313342686921066 : Int)/10^30)
theorem v3458_pg_checked : Scalar.distance (sourceCoefficient 46 78 1 2) v3458_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3458_mb : Scalar.QComplex := ((-1052543998400294534038926 : Int)/10^30,(-431476216791403240977400072 : Int)/10^30)
theorem v3458_mb_checked : Scalar.distance (sourceCoefficient 46 78 3 1) v3458_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3458_mg : Scalar.QComplex := ((-93086150731391920672574 : Int)/10^30,(227074553529514164497 : Int)/10^30)
theorem v3458_mg_checked : Scalar.distance (sourceCoefficient 46 78 3 2) v3458_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3458_upper : Scalar.QComplex := ((999994547239430070591708861478 : Int)/10^30,(-3302346348774002173316624922 : Int)/10^30)
theorem v3458_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 78 5) 1) 14) v3458_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3458 : Material (46 : Basis) (78 : Basis) where
  plus := ![v3458_pa,v3458_pb,v3458_pg]
  minus := ![(Primitive.Addresses.material3458 1).one,v3458_mb,v3458_mg]
  upper := v3458_upper
  lower := (Primitive.Addresses.material3458 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3458_pa_checked.trans (by decide +kernel)
    · exact v3458_pb_checked.trans (by decide +kernel)
    · exact v3458_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 78 Primitive.Addresses.material3458
    · exact v3458_mb_checked.trans (by decide +kernel)
    · exact v3458_mg_checked.trans (by decide +kernel)
  upper_error := v3458_upper_checked
  lower_error := reuse_lower_error 46 78 Primitive.Addresses.material3458

def v3459_pa : Scalar.QComplex := ((999998748607736749457021219106 : Int)/10^30,(-1582018634693817199931965668 : Int)/10^30)
theorem v3459_pa_checked : Scalar.distance (sourceCoefficient 46 79 1 0) v3459_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3459_pb : Scalar.QComplex := ((-682605445686556816828543 : Int)/10^30,(-431476960201226742074294602 : Int)/10^30)
theorem v3459_pb_checked : Scalar.distance (sourceCoefficient 46 79 1 1) v3459_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3459_pg : Scalar.QComplex := ((-93086311160067631547562 : Int)/10^30,(147264463175743903440 : Int)/10^30)
theorem v3459_pg_checked : Scalar.distance (sourceCoefficient 46 79 1 2) v3459_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3459_mb : Scalar.QComplex := ((-1054950375174110895385259 : Int)/10^30,(-431476210484878768440977154 : Int)/10^30)
theorem v3459_mb_checked : Scalar.distance (sourceCoefficient 46 79 3 1) v3459_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3459_mg : Scalar.QComplex := ((-93086149417180556612723 : Int)/10^30,(227593702421768788432 : Int)/10^30)
theorem v3459_mg_checked : Scalar.distance (sourceCoefficient 46 79 3 2) v3459_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3459_upper : Scalar.QComplex := ((999994528806424930826165513329 : Int)/10^30,(-3307923399382037049344002614 : Int)/10^30)
theorem v3459_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 79 5) 1) 14) v3459_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3459 : Material (46 : Basis) (79 : Basis) where
  plus := ![v3459_pa,v3459_pb,v3459_pg]
  minus := ![(Primitive.Addresses.material3459 1).one,v3459_mb,v3459_mg]
  upper := v3459_upper
  lower := (Primitive.Addresses.material3459 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3459_pa_checked.trans (by decide +kernel)
    · exact v3459_pb_checked.trans (by decide +kernel)
    · exact v3459_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 79 Primitive.Addresses.material3459
    · exact v3459_mb_checked.trans (by decide +kernel)
    · exact v3459_mg_checked.trans (by decide +kernel)
  upper_error := v3459_upper_checked
  lower_error := reuse_lower_error 46 79 Primitive.Addresses.material3459

def v3460_pa : Scalar.QComplex := ((999998734787317527667083501238 : Int)/10^30,(-1590730575610318098270261322 : Int)/10^30)
theorem v3460_pa_checked : Scalar.distance (sourceCoefficient 46 80 1 0) v3460_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3460_pb : Scalar.QComplex := ((-686364451092679536420059 : Int)/10^30,(-431476953557853769207745400 : Int)/10^30)
theorem v3460_pb_checked : Scalar.distance (sourceCoefficient 46 80 1 1) v3460_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3460_pg : Scalar.QComplex := ((-93086309800204330284406 : Int)/10^30,(148075426516827020593 : Int)/10^30)
theorem v3460_pg_checked : Scalar.distance (sourceCoefficient 46 80 1 2) v3460_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3460_mb : Scalar.QComplex := ((-1058709373447652438071183 : Int)/10^30,(-431476200597655903040701526 : Int)/10^30)
theorem v3460_mb_checked : Scalar.distance (sourceCoefficient 46 80 3 1) v3460_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3460_mg : Scalar.QComplex := ((-93086147357492922767124 : Int)/10^30,(228404664287392407824 : Int)/10^30)
theorem v3460_mg_checked : Scalar.distance (sourceCoefficient 46 80 3 2) v3460_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3460_upper : Scalar.QComplex := ((999994499950006612152786684880 : Int)/10^30,(-3316635303470335530850925436 : Int)/10^30)
theorem v3460_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 80 5) 1) 14) v3460_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3460 : Material (46 : Basis) (80 : Basis) where
  plus := ![v3460_pa,v3460_pb,v3460_pg]
  minus := ![(Primitive.Addresses.material3460 1).one,v3460_mb,v3460_mg]
  upper := v3460_upper
  lower := (Primitive.Addresses.material3460 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3460_pa_checked.trans (by decide +kernel)
    · exact v3460_pb_checked.trans (by decide +kernel)
    · exact v3460_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 80 Primitive.Addresses.material3460
    · exact v3460_mb_checked.trans (by decide +kernel)
    · exact v3460_mg_checked.trans (by decide +kernel)
  upper_error := v3460_upper_checked
  lower_error := reuse_lower_error 46 80 Primitive.Addresses.material3460

def v3461_pa : Scalar.QComplex := ((999998692714989136551297854006 : Int)/10^30,(-1616962681304920461844542914 : Int)/10^30)
theorem v3461_pa_checked : Scalar.distance (sourceCoefficient 46 81 1 0) v3461_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3461_pb : Scalar.QComplex := ((-697683011045392134877924 : Int)/10^30,(-431476933290634996037128089 : Int)/10^30)
theorem v3461_pb_checked : Scalar.distance (sourceCoefficient 46 81 1 1) v3461_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3461_pg : Scalar.QComplex := ((-93086305655810476118642 : Int)/10^30,(150517279154971605248 : Int)/10^30)
theorem v3461_pg_checked : Scalar.distance (sourceCoefficient 46 81 1 2) v3461_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3461_mb : Scalar.QComplex := ((-1070027911696250882792484 : Int)/10^30,(-431476170563037206107673419 : Int)/10^30)
theorem v3461_mb_checked : Scalar.distance (sourceCoefficient 46 81 3 1) v3461_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3461_mg : Scalar.QComplex := ((-93086141105891761990109 : Int)/10^30,(230846512439898417545 : Int)/10^30)
theorem v3461_mg_checked : Scalar.distance (sourceCoefficient 46 81 3 2) v3461_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3461_upper : Scalar.QComplex := ((999994412603506211983261910670 : Int)/10^30,(-3342867297482275870660010721 : Int)/10^30)
theorem v3461_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 81 5) 1) 14) v3461_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3461 : Material (46 : Basis) (81 : Basis) where
  plus := ![v3461_pa,v3461_pb,v3461_pg]
  minus := ![(Primitive.Addresses.material3461 1).one,v3461_mb,v3461_mg]
  upper := v3461_upper
  lower := (Primitive.Addresses.material3461 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3461_pa_checked.trans (by decide +kernel)
    · exact v3461_pb_checked.trans (by decide +kernel)
    · exact v3461_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 81 Primitive.Addresses.material3461
    · exact v3461_mb_checked.trans (by decide +kernel)
    · exact v3461_mg_checked.trans (by decide +kernel)
  upper_error := v3461_upper_checked
  lower_error := reuse_lower_error 46 81 Primitive.Addresses.material3461

def v3462_pa : Scalar.QComplex := ((999998676592557137360069053389 : Int)/10^30,(-1626902927134258996463045639 : Int)/10^30)
theorem v3462_pa_checked : Scalar.distance (sourceCoefficient 46 82 1 0) v3462_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3462_pb : Scalar.QComplex := ((-701972002093625394467984 : Int)/10^30,(-431476925507260755920879940 : Int)/10^30)
theorem v3462_pb_checked : Scalar.distance (sourceCoefficient 46 82 1 1) v3462_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3462_pg : Scalar.QComplex := ((-93086304065832863309930 : Int)/10^30,(151442580981051996432 : Int)/10^30)
theorem v3462_pg_checked : Scalar.distance (sourceCoefficient 46 82 1 2) v3462_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3462_mb : Scalar.QComplex := ((-1074316894430795339493401 : Int)/10^30,(-431476159078459758458112213 : Int)/10^30)
theorem v3462_mb_checked : Scalar.distance (sourceCoefficient 46 82 3 1) v3462_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3462_mg : Scalar.QComplex := ((-93086138717420939342584 : Int)/10^30,(231771812549367580576 : Int)/10^30)
theorem v3462_mg_checked : Scalar.distance (sourceCoefficient 46 82 3 2) v3462_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3462_upper : Scalar.QComplex := ((999994379325135695879692110920 : Int)/10^30,(-3352807500680930890779332898 : Int)/10^30)
theorem v3462_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 82 5) 1) 14) v3462_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3462 : Material (46 : Basis) (82 : Basis) where
  plus := ![v3462_pa,v3462_pb,v3462_pg]
  minus := ![(Primitive.Addresses.material3462 1).one,v3462_mb,v3462_mg]
  upper := v3462_upper
  lower := (Primitive.Addresses.material3462 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3462_pa_checked.trans (by decide +kernel)
    · exact v3462_pb_checked.trans (by decide +kernel)
    · exact v3462_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 82 Primitive.Addresses.material3462
    · exact v3462_mb_checked.trans (by decide +kernel)
    · exact v3462_mg_checked.trans (by decide +kernel)
  upper_error := v3462_upper_checked
  lower_error := reuse_lower_error 46 82 Primitive.Addresses.material3462

def v3463_pa : Scalar.QComplex := ((999998654425674597208145832044 : Int)/10^30,(-1640471529846013062212003252 : Int)/10^30)
theorem v3463_pa_checked : Scalar.distance (sourceCoefficient 46 83 1 0) v3463_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3463_pb : Scalar.QComplex := ((-707826546933769509256445 : Int)/10^30,(-431476914791067983664940132 : Int)/10^30)
theorem v3463_pb_checked : Scalar.distance (sourceCoefficient 46 83 1 1) v3463_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3463_pg : Scalar.QComplex := ((-93086301878165757433655 : Int)/10^30,(152705633526562196824 : Int)/10^30)
theorem v3463_pg_checked : Scalar.distance (sourceCoefficient 46 83 1 2) v3463_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3463_mb : Scalar.QComplex := ((-1080171427843433121328158 : Int)/10^30,(-431476143310062458197503459 : Int)/10^30)
theorem v3463_mb_checked : Scalar.distance (sourceCoefficient 46 83 3 1) v3463_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3463_mg : Scalar.QComplex := ((-93086135439797187034401 : Int)/10^30,(233034862736727410419 : Int)/10^30)
theorem v3463_mg_checked : Scalar.distance (sourceCoefficient 46 83 3 2) v3463_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3463_upper : Scalar.QComplex := ((999994333740108824230371455629 : Int)/10^30,(-3366376044925816796982133615 : Int)/10^30)
theorem v3463_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 83 5) 1) 14) v3463_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3463 : Material (46 : Basis) (83 : Basis) where
  plus := ![v3463_pa,v3463_pb,v3463_pg]
  minus := ![(Primitive.Addresses.material3463 1).one,v3463_mb,v3463_mg]
  upper := v3463_upper
  lower := (Primitive.Addresses.material3463 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3463_pa_checked.trans (by decide +kernel)
    · exact v3463_pb_checked.trans (by decide +kernel)
    · exact v3463_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 83 Primitive.Addresses.material3463
    · exact v3463_mb_checked.trans (by decide +kernel)
    · exact v3463_mg_checked.trans (by decide +kernel)
  upper_error := v3463_upper_checked
  lower_error := reuse_lower_error 46 83 Primitive.Addresses.material3463

def v3464_pa : Scalar.QComplex := ((999998596163675869808697831977 : Int)/10^30,(-1675610538730273579968142788 : Int)/10^30)
theorem v3464_pa_checked : Scalar.distance (sourceCoefficient 46 84 1 0) v3464_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3464_pb : Scalar.QComplex := ((-722988233273322274341841 : Int)/10^30,(-431476886546700815704624737 : Int)/10^30)
theorem v3464_pb_checked : Scalar.distance (sourceCoefficient 46 84 1 1) v3464_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3464_pg : Scalar.QComplex := ((-93086296119762502464778 : Int)/10^30,(155976597755254664971 : Int)/10^30)
theorem v3464_pg_checked : Scalar.distance (sourceCoefficient 46 84 1 2) v3464_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3464_mb : Scalar.QComplex := ((-1095333084163980352026934 : Int)/10^30,(-431476101981853352875769714 : Int)/10^30)
theorem v3464_mb_checked : Scalar.distance (sourceCoefficient 46 84 3 1) v3464_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3464_mg : Scalar.QComplex := ((-93086126858701265580759 : Int)/10^30,(236305820778247745590 : Int)/10^30)
theorem v3464_mg_checked : Scalar.distance (sourceCoefficient 46 84 3 2) v3464_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3464_upper : Scalar.QComplex := ((999994214831455322984801704241 : Int)/10^30,(-3401514900919726983317289776 : Int)/10^30)
theorem v3464_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 84 5) 1) 14) v3464_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3464 : Material (46 : Basis) (84 : Basis) where
  plus := ![v3464_pa,v3464_pb,v3464_pg]
  minus := ![(Primitive.Addresses.material3464 1).one,v3464_mb,v3464_mg]
  upper := v3464_upper
  lower := (Primitive.Addresses.material3464 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3464_pa_checked.trans (by decide +kernel)
    · exact v3464_pb_checked.trans (by decide +kernel)
    · exact v3464_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 84 Primitive.Addresses.material3464
    · exact v3464_mb_checked.trans (by decide +kernel)
    · exact v3464_mg_checked.trans (by decide +kernel)
  upper_error := v3464_upper_checked
  lower_error := reuse_lower_error 46 84 Primitive.Addresses.material3464

def v3465_pa : Scalar.QComplex := ((999998460570253733551527933669 : Int)/10^30,(-1754667239874544775263200354 : Int)/10^30)
theorem v3465_pa_checked : Scalar.distance (sourceCoefficient 46 85 1 0) v3465_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3465_pb : Scalar.QComplex := ((-757099407030959307859841 : Int)/10^30,(-431476820404843407906885488 : Int)/10^30)
theorem v3465_pb_checked : Scalar.distance (sourceCoefficient 46 85 1 1) v3465_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3465_pg : Scalar.QComplex := ((-93086282674127206371327 : Int)/10^30,(163335702133830936235 : Int)/10^30)
theorem v3465_pg_checked : Scalar.distance (sourceCoefficient 46 85 1 2) v3465_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3465_mb : Scalar.QComplex := ((-1129444188143024413667411 : Int)/10^30,(-431476006403613930109142963 : Int)/10^30)
theorem v3465_mb_checked : Scalar.distance (sourceCoefficient 46 85 3 1) v3465_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3465_mg : Scalar.QComplex := ((-93086107062495338958017 : Int)/10^30,(243664910813715437431 : Int)/10^30)
theorem v3465_mg_checked : Scalar.distance (sourceCoefficient 46 85 3 2) v3465_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3465_upper : Scalar.QComplex := ((999993942793540930093367988592 : Int)/10^30,(-3480571250296382808675226182 : Int)/10^30)
theorem v3465_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 85 5) 1) 14) v3465_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3465 : Material (46 : Basis) (85 : Basis) where
  plus := ![v3465_pa,v3465_pb,v3465_pg]
  minus := ![(Primitive.Addresses.material3465 1).one,v3465_mb,v3465_mg]
  upper := v3465_upper
  lower := (Primitive.Addresses.material3465 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3465_pa_checked.trans (by decide +kernel)
    · exact v3465_pb_checked.trans (by decide +kernel)
    · exact v3465_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 85 Primitive.Addresses.material3465
    · exact v3465_mb_checked.trans (by decide +kernel)
    · exact v3465_mg_checked.trans (by decide +kernel)
  upper_error := v3465_upper_checked
  lower_error := reuse_lower_error 46 85 Primitive.Addresses.material3465

def v3466_pa : Scalar.QComplex := ((999998434872700767861824548222 : Int)/10^30,(-1769251861335975406981268514 : Int)/10^30)
theorem v3466_pa_checked : Scalar.distance (sourceCoefficient 46 86 1 0) v3466_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3466_pb : Scalar.QComplex := ((-763392340147229006623808 : Int)/10^30,(-431476807809937819464914839 : Int)/10^30)
theorem v3466_pb_checked : Scalar.distance (sourceCoefficient 46 86 1 1) v3466_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3466_pg : Scalar.QComplex := ((-93086280119475750386911 : Int)/10^30,(164693332132254596261 : Int)/10^30)
theorem v3466_pg_checked : Scalar.distance (sourceCoefficient 46 86 1 2) v3466_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3466_mb : Scalar.QComplex := ((-1135737108047311242657808 : Int)/10^30,(-431475988378195175171782036 : Int)/10^30)
theorem v3466_mb_checked : Scalar.distance (sourceCoefficient 46 86 3 1) v3466_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3466_mg : Scalar.QComplex := ((-93086103336271290932778 : Int)/10^30,(245022538102082253003 : Int)/10^30)
theorem v3466_mg_checked : Scalar.distance (sourceCoefficient 46 86 3 2) v3466_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3466_upper : Scalar.QComplex := ((999993891924292701984330056520 : Int)/10^30,(-3495155805684087848590856463 : Int)/10^30)
theorem v3466_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 86 5) 1) 14) v3466_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3466 : Material (46 : Basis) (86 : Basis) where
  plus := ![v3466_pa,v3466_pb,v3466_pg]
  minus := ![(Primitive.Addresses.material3466 1).one,v3466_mb,v3466_mg]
  upper := v3466_upper
  lower := (Primitive.Addresses.material3466 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3466_pa_checked.trans (by decide +kernel)
    · exact v3466_pb_checked.trans (by decide +kernel)
    · exact v3466_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 86 Primitive.Addresses.material3466
    · exact v3466_mb_checked.trans (by decide +kernel)
    · exact v3466_mg_checked.trans (by decide +kernel)
  upper_error := v3466_upper_checked
  lower_error := reuse_lower_error 46 86 Primitive.Addresses.material3466

def v3467_pa : Scalar.QComplex := ((999998433163568046038159952407 : Int)/10^30,(-1770217616264034127034520470 : Int)/10^30)
theorem v3467_pa_checked : Scalar.distance (sourceCoefficient 46 87 1 0) v3467_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3467_pb : Scalar.QComplex := ((-763809041474345282182304 : Int)/10^30,(-431476806971616670590793513 : Int)/10^30)
theorem v3467_pb_checked : Scalar.distance (sourceCoefficient 46 87 1 1) v3467_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3467_pg : Scalar.QComplex := ((-93086279949498031661073 : Int)/10^30,(164783230787456333533 : Int)/10^30)
theorem v3467_pg_checked : Scalar.distance (sourceCoefficient 46 87 1 2) v3467_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3467_mb : Scalar.QComplex := ((-1136153808495837175044052 : Int)/10^30,(-431475987180279860672681613 : Int)/10^30)
theorem v3467_mb_checked : Scalar.distance (sourceCoefficient 46 87 3 1) v3467_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3467_mg : Scalar.QComplex := ((-93086103088715144943443 : Int)/10^30,(245112436577127496624 : Int)/10^30)
theorem v3467_mg_checked : Scalar.distance (sourceCoefficient 46 87 3 2) v3467_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3467_upper : Scalar.QComplex := ((999993888548357132486416365667 : Int)/10^30,(-3496121556223960022285293813 : Int)/10^30)
theorem v3467_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 87 5) 1) 14) v3467_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3467 : Material (46 : Basis) (87 : Basis) where
  plus := ![v3467_pa,v3467_pb,v3467_pg]
  minus := ![(Primitive.Addresses.material3467 1).one,v3467_mb,v3467_mg]
  upper := v3467_upper
  lower := (Primitive.Addresses.material3467 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3467_pa_checked.trans (by decide +kernel)
    · exact v3467_pb_checked.trans (by decide +kernel)
    · exact v3467_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 87 Primitive.Addresses.material3467
    · exact v3467_mb_checked.trans (by decide +kernel)
    · exact v3467_mg_checked.trans (by decide +kernel)
  upper_error := v3467_upper_checked
  lower_error := reuse_lower_error 46 87 Primitive.Addresses.material3467

def v3468_pa : Scalar.QComplex := ((999998412277384462611391899890 : Int)/10^30,(-1781977191271446472807355999 : Int)/10^30)
theorem v3468_pa_checked : Scalar.distance (sourceCoefficient 46 88 1 0) v3468_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3468_pb : Scalar.QComplex := ((-768883031092133469269061 : Int)/10^30,(-431476796720701374445129164 : Int)/10^30)
theorem v3468_pb_checked : Scalar.distance (sourceCoefficient 46 88 1 1) v3468_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3468_pg : Scalar.QComplex := ((-93086277871627967079498 : Int)/10^30,(165877887355670177329 : Int)/10^30)
theorem v3468_pg_checked : Scalar.distance (sourceCoefficient 46 88 1 2) v3468_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3468_mb : Scalar.QComplex := ((-1141227787378268918159710 : Int)/10^30,(-431475972550743865269241739 : Int)/10^30)
theorem v3468_mb_checked : Scalar.distance (sourceCoefficient 46 88 3 1) v3468_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3468_mg : Scalar.QComplex := ((-93086100066206537180984 : Int)/10^30,(246207090944642389858 : Int)/10^30)
theorem v3468_mg_checked : Scalar.distance (sourceCoefficient 46 88 3 2) v3468_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3468_upper : Scalar.QComplex := ((999993847366245014094053062183 : Int)/10^30,(-3507881077669208686013112305 : Int)/10^30)
theorem v3468_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 88 5) 1) 14) v3468_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3468 : Material (46 : Basis) (88 : Basis) where
  plus := ![v3468_pa,v3468_pb,v3468_pg]
  minus := ![(Primitive.Addresses.material3468 1).one,v3468_mb,v3468_mg]
  upper := v3468_upper
  lower := (Primitive.Addresses.material3468 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3468_pa_checked.trans (by decide +kernel)
    · exact v3468_pb_checked.trans (by decide +kernel)
    · exact v3468_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 88 Primitive.Addresses.material3468
    · exact v3468_mb_checked.trans (by decide +kernel)
    · exact v3468_mg_checked.trans (by decide +kernel)
  upper_error := v3468_upper_checked
  lower_error := reuse_lower_error 46 88 Primitive.Addresses.material3468

def v3469_pa : Scalar.QComplex := ((999998383476854466053298795288 : Int)/10^30,(-1798066650021854266482146151 : Int)/10^30)
theorem v3469_pa_checked : Scalar.distance (sourceCoefficient 46 89 1 0) v3469_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3469_pb : Scalar.QComplex := ((-775825267131058858206916 : Int)/10^30,(-431476782566501660105933430 : Int)/10^30)
theorem v3469_pb_checked : Scalar.distance (sourceCoefficient 46 89 1 1) v3469_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3469_pg : Scalar.QComplex := ((-93086275004353884907141 : Int)/10^30,(167375597226618571906 : Int)/10^30)
theorem v3469_pg_checked : Scalar.distance (sourceCoefficient 46 89 1 2) v3469_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3469_mb : Scalar.QComplex := ((-1148170008617845681960901 : Int)/10^30,(-431475952405712386297327434 : Int)/10^30)
theorem v3469_mb_checked : Scalar.distance (sourceCoefficient 46 89 3 1) v3469_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3469_mg : Scalar.QComplex := ((-93086095906477358345907 : Int)/10^30,(247704797783596555073 : Int)/10^30)
theorem v3469_mg_checked : Scalar.distance (sourceCoefficient 46 89 3 2) v3469_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3469_upper : Scalar.QComplex := ((999993790796811733634267758426 : Int)/10^30,(-3523970462749155661157846224 : Int)/10^30)
theorem v3469_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 89 5) 1) 14) v3469_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3469 : Material (46 : Basis) (89 : Basis) where
  plus := ![v3469_pa,v3469_pb,v3469_pg]
  minus := ![(Primitive.Addresses.material3469 1).one,v3469_mb,v3469_mg]
  upper := v3469_upper
  lower := (Primitive.Addresses.material3469 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3469_pa_checked.trans (by decide +kernel)
    · exact v3469_pb_checked.trans (by decide +kernel)
    · exact v3469_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 89 Primitive.Addresses.material3469
    · exact v3469_mb_checked.trans (by decide +kernel)
    · exact v3469_mg_checked.trans (by decide +kernel)
  upper_error := v3469_upper_checked
  lower_error := reuse_lower_error 46 89 Primitive.Addresses.material3469

def v3470_pa : Scalar.QComplex := ((999998336018922380100587477597 : Int)/10^30,(-1824269548725399337597474541 : Int)/10^30)
theorem v3470_pa_checked : Scalar.distance (sourceCoefficient 46 90 1 0) v3470_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3470_pb : Scalar.QComplex := ((-787131222556442143992303 : Int)/10^30,(-431476759196546787363765158 : Int)/10^30)
theorem v3470_pb_checked : Scalar.distance (sourceCoefficient 46 90 1 1) v3470_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3470_pg : Scalar.QComplex := ((-93086270274606481665677 : Int)/10^30,(169814730834885731349 : Int)/10^30)
theorem v3470_pg_checked : Scalar.distance (sourceCoefficient 46 90 1 2) v3470_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3470_mb : Scalar.QComplex := ((-1159475939666286543705991 : Int)/10^30,(-431475919279235884481559732 : Int)/10^30)
theorem v3470_mb_checked : Scalar.distance (sourceCoefficient 46 90 3 1) v3470_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3470_mg : Scalar.QComplex := ((-93086089071869266770730 : Int)/10^30,(250143926402103809164 : Int)/10^30)
theorem v3470_mg_checked : Scalar.distance (sourceCoefficient 46 90 3 2) v3470_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3470_upper : Scalar.QComplex := ((999993698115124276779239222115 : Int)/10^30,(-3550173240518475691655737498 : Int)/10^30)
theorem v3470_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 90 5) 1) 14) v3470_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3470 : Material (46 : Basis) (90 : Basis) where
  plus := ![v3470_pa,v3470_pb,v3470_pg]
  minus := ![(Primitive.Addresses.material3470 1).one,v3470_mb,v3470_mg]
  upper := v3470_upper
  lower := (Primitive.Addresses.material3470 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3470_pa_checked.trans (by decide +kernel)
    · exact v3470_pb_checked.trans (by decide +kernel)
    · exact v3470_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 90 Primitive.Addresses.material3470
    · exact v3470_mb_checked.trans (by decide +kernel)
    · exact v3470_mg_checked.trans (by decide +kernel)
  upper_error := v3470_upper_checked
  lower_error := reuse_lower_error 46 90 Primitive.Addresses.material3470

def v3471_pa : Scalar.QComplex := ((999998308981805644256024018096 : Int)/10^30,(-1839030594951849709384737462 : Int)/10^30)
theorem v3471_pa_checked : Scalar.distance (sourceCoefficient 46 91 1 0) v3471_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3471_pb : Scalar.QComplex := ((-793500278465551348294152 : Int)/10^30,(-431476745857465719543529638 : Int)/10^30)
theorem v3471_pb_checked : Scalar.distance (sourceCoefficient 46 91 1 1) v3471_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3471_pg : Scalar.QComplex := ((-93086267577333668922418 : Int)/10^30,(171188783527938630207 : Int)/10^30)
theorem v3471_pg_checked : Scalar.distance (sourceCoefficient 46 91 1 2) v3471_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3471_mb : Scalar.QComplex := ((-1165844981692878961192586 : Int)/10^30,(-431475900443951385479301819 : Int)/10^30)
theorem v3471_mb_checked : Scalar.distance (sourceCoefficient 46 91 3 1) v3471_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3471_mg : Scalar.QComplex := ((-93086085188851869276773 : Int)/10^30,(251517976255909136348 : Int)/10^30)
theorem v3471_mg_checked : Scalar.distance (sourceCoefficient 46 91 3 2) v3471_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3471_upper : Scalar.QComplex := ((999993645601821134343806667227 : Int)/10^30,(-3564934218096470965441006623 : Int)/10^30)
theorem v3471_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 91 5) 1) 14) v3471_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3471 : Material (46 : Basis) (91 : Basis) where
  plus := ![v3471_pa,v3471_pb,v3471_pg]
  minus := ![(Primitive.Addresses.material3471 1).one,v3471_mb,v3471_mg]
  upper := v3471_upper
  lower := (Primitive.Addresses.material3471 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3471_pa_checked.trans (by decide +kernel)
    · exact v3471_pb_checked.trans (by decide +kernel)
    · exact v3471_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 91 Primitive.Addresses.material3471
    · exact v3471_mb_checked.trans (by decide +kernel)
    · exact v3471_mg_checked.trans (by decide +kernel)
  upper_error := v3471_upper_checked
  lower_error := reuse_lower_error 46 91 Primitive.Addresses.material3471

def v3472_pa : Scalar.QComplex := ((999998249702956079647271840062 : Int)/10^30,(-1870986644607855959560024293 : Int)/10^30)
theorem v3472_pa_checked : Scalar.distance (sourceCoefficient 46 92 1 0) v3472_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3472_pb : Scalar.QComplex := ((-807288587119838014295802 : Int)/10^30,(-431476716550379979216273733 : Int)/10^30)
theorem v3472_pb_checked : Scalar.distance (sourceCoefficient 46 92 1 1) v3472_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3472_pg : Scalar.QComplex := ((-93086261656968103762529 : Int)/10^30,(174163457194443956959 : Int)/10^30)
theorem v3472_pg_checked : Scalar.distance (sourceCoefficient 46 92 1 2) v3472_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3472_mb : Scalar.QComplex := ((-1179633259922453106608197 : Int)/10^30,(-431475859238187191239171794 : Int)/10^30)
theorem v3472_mb_checked : Scalar.distance (sourceCoefficient 46 92 3 1) v3472_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3472_mg : Scalar.QComplex := ((-93086076701479108674040 : Int)/10^30,(254492643705798668392 : Int)/10^30)
theorem v3472_mg_checked : Scalar.distance (sourceCoefficient 46 92 3 2) v3472_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3472_upper : Scalar.QComplex := ((999993531169817182530122255702 : Int)/10^30,(-3596890117847778460988374233 : Int)/10^30)
theorem v3472_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 92 5) 1) 14) v3472_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3472 : Material (46 : Basis) (92 : Basis) where
  plus := ![v3472_pa,v3472_pb,v3472_pg]
  minus := ![(Primitive.Addresses.material3472 1).one,v3472_mb,v3472_mg]
  upper := v3472_upper
  lower := (Primitive.Addresses.material3472 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3472_pa_checked.trans (by decide +kernel)
    · exact v3472_pb_checked.trans (by decide +kernel)
    · exact v3472_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 92 Primitive.Addresses.material3472
    · exact v3472_mb_checked.trans (by decide +kernel)
    · exact v3472_mg_checked.trans (by decide +kernel)
  upper_error := v3472_upper_checked
  lower_error := reuse_lower_error 46 92 Primitive.Addresses.material3472

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
