import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B099
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B100

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2385_pa : Scalar.QComplex := ((999999157785978705472000914012 : Int)/10^30,(-1297854896845020318958004521 : Int)/10^30)
theorem v2385_pa_checked : Scalar.distance (sourceCoefficient 28 76 1 0) v2385_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2385_pb : Scalar.QComplex := ((-559995158009275099826088 : Int)/10^30,(-431477114841422332750146943 : Int)/10^30)
theorem v2385_pb_checked : Scalar.distance (sourceCoefficient 28 76 1 1) v2385_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2385_pg : Scalar.QComplex := ((-93086346885481322820428 : Int)/10^30,(120812672884863194376 : Int)/10^30)
theorem v2385_pg_checked : Scalar.distance (sourceCoefficient 28 76 1 2) v2385_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2385_mb : Scalar.QComplex := ((-932340266597766906490469 : Int)/10^30,(-431476470932172882634044740 : Int)/10^30)
theorem v2385_mb_checked : Scalar.distance (sourceCoefficient 28 76 3 1) v2385_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2385_mg : Scalar.QComplex := ((-93086207969284622301473 : Int)/10^30,(201141952809521513866 : Int)/10^30)
theorem v2385_mg_checked : Scalar.distance (sourceCoefficient 28 76 3 2) v2385_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2385_upper : Scalar.QComplex := ((999995428424889858016513368092 : Int)/10^30,(-3023760790966272732612834367 : Int)/10^30)
theorem v2385_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 76 5) 1) 14) v2385_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2385 : Material (28 : Basis) (76 : Basis) where
  plus := ![v2385_pa,v2385_pb,v2385_pg]
  minus := ![(Primitive.Addresses.material2385 1).one,v2385_mb,v2385_mg]
  upper := v2385_upper
  lower := (Primitive.Addresses.material2385 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2385_pa_checked.trans (by decide +kernel)
    · exact v2385_pb_checked.trans (by decide +kernel)
    · exact v2385_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 76 Primitive.Addresses.material2385
    · exact v2385_mb_checked.trans (by decide +kernel)
    · exact v2385_mg_checked.trans (by decide +kernel)
  upper_error := v2385_upper_checked
  lower_error := reuse_lower_error 28 76 Primitive.Addresses.material2385

def v2386_pa : Scalar.QComplex := ((999999154047009636913905643251 : Int)/10^30,(-1300732587847982797076947548 : Int)/10^30)
theorem v2386_pa_checked : Scalar.distance (sourceCoefficient 28 77 1 0) v2386_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2386_pb : Scalar.QComplex := ((-561236816450461845553076 : Int)/10^30,(-431477112908384064608407996 : Int)/10^30)
theorem v2386_pb_checked : Scalar.distance (sourceCoefficient 28 77 1 1) v2386_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2386_pg : Scalar.QComplex := ((-93086346502942031722325 : Int)/10^30,(121080546808536459989 : Int)/10^30)
theorem v2386_pg_checked : Scalar.distance (sourceCoefficient 28 77 1 2) v2386_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2386_mb : Scalar.QComplex := ((-933581922908502503374958 : Int)/10^30,(-431476467927640021726896328 : Int)/10^30)
theorem v2386_mb_checked : Scalar.distance (sourceCoefficient 28 77 3 1) v2386_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2386_mg : Scalar.QComplex := ((-93086207355582342103866 : Int)/10^30,(201409826303338895965 : Int)/10^30)
theorem v2386_mg_checked : Scalar.distance (sourceCoefficient 28 77 3 2) v2386_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2386_upper : Scalar.QComplex := ((999995419719292749188881956260 : Int)/10^30,(-3026638471230131083443170114 : Int)/10^30)
theorem v2386_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 77 5) 1) 14) v2386_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2386 : Material (28 : Basis) (77 : Basis) where
  plus := ![v2386_pa,v2386_pb,v2386_pg]
  minus := ![(Primitive.Addresses.material2386 1).one,v2386_mb,v2386_mg]
  upper := v2386_upper
  lower := (Primitive.Addresses.material2386 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2386_pa_checked.trans (by decide +kernel)
    · exact v2386_pb_checked.trans (by decide +kernel)
    · exact v2386_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 77 Primitive.Addresses.material2386
    · exact v2386_mb_checked.trans (by decide +kernel)
    · exact v2386_mg_checked.trans (by decide +kernel)
  upper_error := v2386_upper_checked
  lower_error := reuse_lower_error 28 77 Primitive.Addresses.material2386

def v2387_pa : Scalar.QComplex := ((999999131395232372847973105755 : Int)/10^30,(-1318032162270732189119534041 : Int)/10^30)
theorem v2387_pa_checked : Scalar.distance (sourceCoefficient 28 78 1 0) v2387_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2387_pb : Scalar.QComplex := ((-568701190624759759150918 : Int)/10^30,(-431477101187292186188239805 : Int)/10^30)
theorem v2387_pb_checked : Scalar.distance (sourceCoefficient 28 78 1 1) v2387_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2387_pg : Scalar.QComplex := ((-93086344184308515594158 : Int)/10^30,(122690902073024234127 : Int)/10^30)
theorem v2387_pg_checked : Scalar.distance (sourceCoefficient 28 78 1 2) v2387_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2387_mb : Scalar.QComplex := ((-941046284188698380434415 : Int)/10^30,(-431476449765133778118928687 : Int)/10^30)
theorem v2387_mb_checked : Scalar.distance (sourceCoefficient 28 78 3 1) v2387_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2387_mg : Scalar.QComplex := ((-93086203647285623764733 : Int)/10^30,(203020178967341511221 : Int)/10^30)
theorem v2387_mg_checked : Scalar.distance (sourceCoefficient 28 78 3 2) v2387_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2387_upper : Scalar.QComplex := ((999995367210053173750980622010 : Int)/10^30,(-3043937980792283918966221710 : Int)/10^30)
theorem v2387_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 78 5) 1) 14) v2387_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2387 : Material (28 : Basis) (78 : Basis) where
  plus := ![v2387_pa,v2387_pb,v2387_pg]
  minus := ![(Primitive.Addresses.material2387 1).one,v2387_mb,v2387_mg]
  upper := v2387_upper
  lower := (Primitive.Addresses.material2387 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2387_pa_checked.trans (by decide +kernel)
    · exact v2387_pb_checked.trans (by decide +kernel)
    · exact v2387_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 78 Primitive.Addresses.material2387
    · exact v2387_mb_checked.trans (by decide +kernel)
    · exact v2387_mg_checked.trans (by decide +kernel)
  upper_error := v2387_upper_checked
  lower_error := reuse_lower_error 28 78 Primitive.Addresses.material2387

def v2388_pa : Scalar.QComplex := ((999999124028908248032621293767 : Int)/10^30,(-1323609238475835500345909219 : Int)/10^30)
theorem v2388_pa_checked : Scalar.distance (sourceCoefficient 28 79 1 0) v2388_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2388_pb : Scalar.QComplex := ((-571107572545934567264045 : Int)/10^30,(-431477097371919835354051704 : Int)/10^30)
theorem v2388_pb_checked : Scalar.distance (sourceCoefficient 28 79 1 1) v2388_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2388_pg : Scalar.QComplex := ((-93086343429894237604453 : Int)/10^30,(123210052068186230043 : Int)/10^30)
theorem v2388_pg_checked : Scalar.distance (sourceCoefficient 28 79 1 2) v2388_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2388_mb : Scalar.QComplex := ((-943452661921372721429236 : Int)/10^30,(-431476443873163629366875116 : Int)/10^30)
theorem v2388_mb_checked : Scalar.distance (sourceCoefficient 28 79 3 1) v2388_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2388_mg : Scalar.QComplex := ((-93086202444868562500954 : Int)/10^30,(203539328118174693264 : Int)/10^30)
theorem v2388_mg_checked : Scalar.distance (sourceCoefficient 28 79 3 2) v2388_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2388_upper : Scalar.QComplex := ((999995350218212438602863285836 : Int)/10^30,(-3049515035977380180355681171 : Int)/10^30)
theorem v2388_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 79 5) 1) 14) v2388_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2388 : Material (28 : Basis) (79 : Basis) where
  plus := ![v2388_pa,v2388_pb,v2388_pg]
  minus := ![(Primitive.Addresses.material2388 1).one,v2388_mb,v2388_mg]
  upper := v2388_upper
  lower := (Primitive.Addresses.material2388 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2388_pa_checked.trans (by decide +kernel)
    · exact v2388_pb_checked.trans (by decide +kernel)
    · exact v2388_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 79 Primitive.Addresses.material2388
    · exact v2388_mb_checked.trans (by decide +kernel)
    · exact v2388_mg_checked.trans (by decide +kernel)
  upper_error := v2388_upper_checked
  lower_error := reuse_lower_error 28 79 Primitive.Addresses.material2388

def v2389_pa : Scalar.QComplex := ((999999112459739236826541570437 : Int)/10^30,(-1332321182672793970802655021 : Int)/10^30)
theorem v2389_pa_checked : Scalar.distance (sourceCoefficient 28 80 1 0) v2389_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2389_pb : Scalar.QComplex := ((-574866578895686372316923 : Int)/10^30,(-431477091376122735537721582 : Int)/10^30)
theorem v2389_pb_checked : Scalar.distance (sourceCoefficient 28 80 1 1) v2389_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2389_pg : Scalar.QComplex := ((-93086342244664968865666 : Int)/10^30,(124021015663741076650 : Int)/10^30)
theorem v2389_pg_checked : Scalar.distance (sourceCoefficient 28 80 1 2) v2389_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2389_mb : Scalar.QComplex := ((-947211661697371810927986 : Int)/10^30,(-431476434633515581585324074 : Int)/10^30)
theorem v2389_mb_checked : Scalar.distance (sourceCoefficient 28 80 3 1) v2389_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2389_mg : Scalar.QComplex := ((-93086200559814676557852 : Int)/10^30,(204350290388971252202 : Int)/10^30)
theorem v2389_mg_checked : Scalar.distance (sourceCoefficient 28 80 3 2) v2389_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2389_upper : Scalar.QComplex := ((999995323613035315768435523401 : Int)/10^30,(-3058226947231584979768856273 : Int)/10^30)
theorem v2389_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 80 5) 1) 14) v2389_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2389 : Material (28 : Basis) (80 : Basis) where
  plus := ![v2389_pa,v2389_pb,v2389_pg]
  minus := ![(Primitive.Addresses.material2389 1).one,v2389_mb,v2389_mg]
  upper := v2389_upper
  lower := (Primitive.Addresses.material2389 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2389_pa_checked.trans (by decide +kernel)
    · exact v2389_pb_checked.trans (by decide +kernel)
    · exact v2389_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 80 Primitive.Addresses.material2389
    · exact v2389_mb_checked.trans (by decide +kernel)
    · exact v2389_mg_checked.trans (by decide +kernel)
  upper_error := v2389_upper_checked
  lower_error := reuse_lower_error 28 80 Primitive.Addresses.material2389

def v2390_pa : Scalar.QComplex := ((999999077166041941623439593170 : Int)/10^30,(-1358553298363460959700989180 : Int)/10^30)
theorem v2390_pa_checked : Scalar.distance (sourceCoefficient 28 81 1 0) v2390_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2390_pb : Scalar.QComplex := ((-586185141723783605623282 : Int)/10^30,(-431477073058788483829304054 : Int)/10^30)
theorem v2390_pb_checked : Scalar.distance (sourceCoefficient 28 81 1 1) v2390_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2390_pg : Scalar.QComplex := ((-93086338626103239452496 : Int)/10^30,(126462869077300612842 : Int)/10^30)
theorem v2390_pg_checked : Scalar.distance (sourceCoefficient 28 81 1 2) v2390_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2390_mb : Scalar.QComplex := ((-958530204504016342343716 : Int)/10^30,(-431476406548778198755936928 : Int)/10^30)
theorem v2390_mb_checked : Scalar.distance (sourceCoefficient 28 81 3 1) v2390_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2390_mg : Scalar.QComplex := ((-93086194834044775593919 : Int)/10^30,(206792139770661365799 : Int)/10^30)
theorem v2390_mg_checked : Scalar.distance (sourceCoefficient 28 81 3 2) v2390_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2390_upper : Scalar.QComplex := ((999995243045138663236143590615 : Int)/10^30,(-3084458962938877375873971919 : Int)/10^30)
theorem v2390_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 81 5) 1) 14) v2390_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2390 : Material (28 : Basis) (81 : Basis) where
  plus := ![v2390_pa,v2390_pb,v2390_pg]
  minus := ![(Primitive.Addresses.material2390 1).one,v2390_mb,v2390_mg]
  upper := v2390_upper
  lower := (Primitive.Addresses.material2390 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2390_pa_checked.trans (by decide +kernel)
    · exact v2390_pb_checked.trans (by decide +kernel)
    · exact v2390_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 81 Primitive.Addresses.material2390
    · exact v2390_mb_checked.trans (by decide +kernel)
    · exact v2390_mg_checked.trans (by decide +kernel)
  upper_error := v2390_upper_checked
  lower_error := reuse_lower_error 28 81 Primitive.Addresses.material2390

def v2391_pa : Scalar.QComplex := ((999999063612266093093183983639 : Int)/10^30,(-1368493548027109048788830356 : Int)/10^30)
theorem v2391_pa_checked : Scalar.distance (sourceCoefficient 28 82 1 0) v2391_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2391_pb : Scalar.QComplex := ((-590474133874962390652220 : Int)/10^30,(-431477066014292460514269233 : Int)/10^30)
theorem v2391_pb_checked : Scalar.distance (sourceCoefficient 28 82 1 1) v2391_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2391_pg : Scalar.QComplex := ((-93086337235381479382475 : Int)/10^30,(127388171200816151189 : Int)/10^30)
theorem v2391_pg_checked : Scalar.distance (sourceCoefficient 28 82 1 2) v2391_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2391_mb : Scalar.QComplex := ((-962819188979124537066379 : Int)/10^30,(-431476395803077740997146901 : Int)/10^30)
theorem v2391_mb_checked : Scalar.distance (sourceCoefficient 28 82 3 1) v2391_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2391_mg : Scalar.QComplex := ((-93086192644829474819888 : Int)/10^30,(207717440349514392007 : Int)/10^30)
theorem v2391_mg_checked : Scalar.distance (sourceCoefficient 28 82 3 2) v2391_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2391_upper : Scalar.QComplex := ((999995212335413854411500951135 : Int)/10^30,(-3094399174405103729084116985 : Int)/10^30)
theorem v2391_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 82 5) 1) 14) v2391_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2391 : Material (28 : Basis) (82 : Basis) where
  plus := ![v2391_pa,v2391_pb,v2391_pg]
  minus := ![(Primitive.Addresses.material2391 1).one,v2391_mb,v2391_mg]
  upper := v2391_upper
  lower := (Primitive.Addresses.material2391 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2391_pa_checked.trans (by decide +kernel)
    · exact v2391_pb_checked.trans (by decide +kernel)
    · exact v2391_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 82 Primitive.Addresses.material2391
    · exact v2391_mb_checked.trans (by decide +kernel)
    · exact v2391_mg_checked.trans (by decide +kernel)
  upper_error := v2391_upper_checked
  lower_error := reuse_lower_error 28 82 Primitive.Addresses.material2391

def v2392_pa : Scalar.QComplex := ((999999044951642398319742270031 : Int)/10^30,(-1382062156013974343203422110 : Int)/10^30)
theorem v2392_pa_checked : Scalar.distance (sourceCoefficient 28 83 1 0) v2392_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2392_pb : Scalar.QComplex := ((-596328680232501028093938 : Int)/10^30,(-431477056306680878972730499 : Int)/10^30)
theorem v2392_pb_checked : Scalar.distance (sourceCoefficient 28 83 1 1) v2392_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2392_pg : Scalar.QComplex := ((-93086335319701963310811 : Int)/10^30,(128651224155527398270 : Int)/10^30)
theorem v2392_pg_checked : Scalar.distance (sourceCoefficient 28 83 1 2) v2392_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2392_mb : Scalar.QComplex := ((-968673724779516419335010 : Int)/10^30,(-431476381043259946466935344 : Int)/10^30)
theorem v2392_mb_checked : Scalar.distance (sourceCoefficient 28 83 3 1) v2392_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2392_mg : Scalar.QComplex := ((-93086189639192857920833 : Int)/10^30,(208980491180788156310 : Int)/10^30)
theorem v2392_mg_checked : Scalar.distance (sourceCoefficient 28 83 3 2) v2392_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2392_upper : Scalar.QComplex := ((999995170256631501616559384406 : Int)/10^30,(-3107967729976577689099587328 : Int)/10^30)
theorem v2392_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 83 5) 1) 14) v2392_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2392 : Material (28 : Basis) (83 : Basis) where
  plus := ![v2392_pa,v2392_pb,v2392_pg]
  minus := ![(Primitive.Addresses.material2392 1).one,v2392_mb,v2392_mg]
  upper := v2392_upper
  lower := (Primitive.Addresses.material2392 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2392_pa_checked.trans (by decide +kernel)
    · exact v2392_pb_checked.trans (by decide +kernel)
    · exact v2392_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 83 Primitive.Addresses.material2392
    · exact v2392_mb_checked.trans (by decide +kernel)
    · exact v2392_mg_checked.trans (by decide +kernel)
  upper_error := v2392_upper_checked
  lower_error := reuse_lower_error 28 83 Primitive.Addresses.material2392

def v2393_pa : Scalar.QComplex := ((999998995769905192560107137255 : Int)/10^30,(-1417201178780485092200726711 : Int)/10^30)
theorem v2393_pa_checked : Scalar.distance (sourceCoefficient 28 84 1 0) v2393_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2393_pb : Scalar.QComplex := ((-611490370565306157848402 : Int)/10^30,(-431477030674266036452692077 : Int)/10^30)
theorem v2393_pb_checked : Scalar.distance (sourceCoefficient 28 84 1 1) v2393_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2393_pg : Scalar.QComplex := ((-93086330265672957273596 : Int)/10^30,(131922189461094090790 : Int)/10^30)
theorem v2393_pg_checked : Scalar.distance (sourceCoefficient 28 84 1 2) v2393_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2393_mb : Scalar.QComplex := ((-983835387347311746721647 : Int)/10^30,(-431476342326998748039314392 : Int)/10^30)
theorem v2393_mb_checked : Scalar.distance (sourceCoefficient 28 84 3 1) v2393_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2393_mg : Scalar.QComplex := ((-93086181762469993834172 : Int)/10^30,(212251450907025567875 : Int)/10^30)
theorem v2393_mg_checked : Scalar.distance (sourceCoefficient 28 84 3 2) v2393_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2393_upper : Scalar.QComplex := ((999995060428202038523397244615 : Int)/10^30,(-3143106615524425062154806702 : Int)/10^30)
theorem v2393_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 84 5) 1) 14) v2393_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2393 : Material (28 : Basis) (84 : Basis) where
  plus := ![v2393_pa,v2393_pb,v2393_pg]
  minus := ![(Primitive.Addresses.material2393 1).one,v2393_mb,v2393_mg]
  upper := v2393_upper
  lower := (Primitive.Addresses.material2393 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2393_pa_checked.trans (by decide +kernel)
    · exact v2393_pb_checked.trans (by decide +kernel)
    · exact v2393_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 84 Primitive.Addresses.material2393
    · exact v2393_mb_checked.trans (by decide +kernel)
    · exact v2393_mg_checked.trans (by decide +kernel)
  upper_error := v2393_upper_checked
  lower_error := reuse_lower_error 28 84 Primitive.Addresses.material2393

def v2394_pa : Scalar.QComplex := ((999998880605503382073047968561 : Int)/10^30,(-1496257912323879691356280590 : Int)/10^30)
theorem v2394_pa_checked : Scalar.distance (sourceCoefficient 28 85 1 0) v2394_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2394_pb : Scalar.QComplex := ((-645601553642604834209939 : Int)/10^30,(-431476970408850242852634102 : Int)/10^30)
theorem v2394_pb_checked : Scalar.distance (sourceCoefficient 28 85 1 1) v2394_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2394_pg : Scalar.QComplex := ((-93086318404758072324690 : Int)/10^30,(139281296352935871523 : Int)/10^30)
theorem v2394_pg_checked : Scalar.distance (sourceCoefficient 28 85 1 2) v2394_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2394_mb : Scalar.QComplex := ((-1017946505717118429016828 : Int)/10^30,(-431476252625190708954333505 : Int)/10^30)
theorem v2394_mb_checked : Scalar.distance (sourceCoefficient 28 85 3 1) v2394_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2394_mg : Scalar.QComplex := ((-93086163550981719457200 : Int)/10^30,(219610544823300175040 : Int)/10^30)
theorem v2394_mg_checked : Scalar.distance (sourceCoefficient 28 85 3 2) v2394_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2394_upper : Scalar.QComplex := ((999994808819221626828290777514 : Int)/10^30,(-3222163032558791812717288920 : Int)/10^30)
theorem v2394_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 85 5) 1) 14) v2394_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2394 : Material (28 : Basis) (85 : Basis) where
  plus := ![v2394_pa,v2394_pb,v2394_pg]
  minus := ![(Primitive.Addresses.material2394 1).one,v2394_mb,v2394_mg]
  upper := v2394_upper
  lower := (Primitive.Addresses.material2394 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2394_pa_checked.trans (by decide +kernel)
    · exact v2394_pb_checked.trans (by decide +kernel)
    · exact v2394_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 85 Primitive.Addresses.material2394
    · exact v2394_mb_checked.trans (by decide +kernel)
    · exact v2394_mg_checked.trans (by decide +kernel)
  upper_error := v2394_upper_checked
  lower_error := reuse_lower_error 28 85 Primitive.Addresses.material2394

def v2395_pa : Scalar.QComplex := ((999998858676758446178809376262 : Int)/10^30,(-1510842539938858310913612665 : Int)/10^30)
theorem v2395_pa_checked : Scalar.distance (sourceCoefficient 28 86 1 0) v2395_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2395_pb : Scalar.QComplex := ((-651894488528952815613748 : Int)/10^30,(-431476958898048533070760053 : Int)/10^30)
theorem v2395_pb_checked : Scalar.distance (sourceCoefficient 28 86 1 1) v2395_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2395_pg : Scalar.QComplex := ((-93086316142460673842038 : Int)/10^30,(140638926828702688503 : Int)/10^30)
theorem v2395_pg_checked : Scalar.distance (sourceCoefficient 28 86 1 2) v2395_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2395_mb : Scalar.QComplex := ((-1024239428327015702623510 : Int)/10^30,(-431476235683873901517812606 : Int)/10^30)
theorem v2395_mb_checked : Scalar.distance (sourceCoefficient 28 86 3 1) v2395_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2395_mg : Scalar.QComplex := ((-93086160117111208151303 : Int)/10^30,(220968172841298354317 : Int)/10^30)
theorem v2395_mg_checked : Scalar.distance (sourceCoefficient 28 86 3 2) v2395_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2395_upper : Scalar.QComplex := ((999994761718765194852291050590 : Int)/10^30,(-3236747600604656431318615246 : Int)/10^30)
theorem v2395_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 86 5) 1) 14) v2395_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2395 : Material (28 : Basis) (86 : Basis) where
  plus := ![v2395_pa,v2395_pb,v2395_pg]
  minus := ![(Primitive.Addresses.material2395 1).one,v2395_mb,v2395_mg]
  upper := v2395_upper
  lower := (Primitive.Addresses.material2395 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2395_pa_checked.trans (by decide +kernel)
    · exact v2395_pb_checked.trans (by decide +kernel)
    · exact v2395_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 86 Primitive.Addresses.material2395
    · exact v2395_mb_checked.trans (by decide +kernel)
    · exact v2395_mg_checked.trans (by decide +kernel)
  upper_error := v2395_upper_checked
  lower_error := reuse_lower_error 28 86 Primitive.Addresses.material2395

def v2396_pa : Scalar.QComplex := ((999998857217186190560188885172 : Int)/10^30,(-1511808295276329036457800516 : Int)/10^30)
theorem v2396_pa_checked : Scalar.distance (sourceCoefficient 28 87 1 0) v2396_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2396_pb : Scalar.QComplex := ((-652311189973837133291771 : Int)/10^30,(-431476958131513865990466355 : Int)/10^30)
theorem v2396_pb_checked : Scalar.distance (sourceCoefficient 28 87 1 1) v2396_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2396_pg : Scalar.QComplex := ((-93086315991841864949861 : Int)/10^30,(140728825515663342652 : Int)/10^30)
theorem v2396_pg_checked : Scalar.distance (sourceCoefficient 28 87 1 2) v2396_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2396_mb : Scalar.QComplex := ((-1024656128955258133923809 : Int)/10^30,(-431476234557744940454635561 : Int)/10^30)
theorem v2396_mb_checked : Scalar.distance (sourceCoefficient 28 87 3 1) v2396_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2396_mg : Scalar.QComplex := ((-93086159888913937380907 : Int)/10^30,(221058071364808370283 : Int)/10^30)
theorem v2396_mg_checked : Scalar.distance (sourceCoefficient 28 87 3 2) v2396_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2396_upper : Scalar.QComplex := ((999994758592389013260442573355 : Int)/10^30,(-3237713351984658725454164801 : Int)/10^30)
theorem v2396_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 87 5) 1) 14) v2396_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2396 : Material (28 : Basis) (87 : Basis) where
  plus := ![v2396_pa,v2396_pb,v2396_pg]
  minus := ![(Primitive.Addresses.material2396 1).one,v2396_mb,v2396_mg]
  upper := v2396_upper
  lower := (Primitive.Addresses.material2396 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2396_pa_checked.trans (by decide +kernel)
    · exact v2396_pb_checked.trans (by decide +kernel)
    · exact v2396_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 87 Primitive.Addresses.material2396
    · exact v2396_mb_checked.trans (by decide +kernel)
    · exact v2396_mg_checked.trans (by decide +kernel)
  upper_error := v2396_upper_checked
  lower_error := reuse_lower_error 28 87 Primitive.Addresses.material2396

def v2397_pa : Scalar.QComplex := ((999998839369791163496016508947 : Int)/10^30,(-1523567875288307036544773629 : Int)/10^30)
theorem v2397_pa_checked : Scalar.distance (sourceCoefficient 28 88 1 0) v2397_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2397_pb : Scalar.QComplex := ((-657385181031196926043489 : Int)/10^30,(-431476948754711134447864337 : Int)/10^30)
theorem v2397_pb_checked : Scalar.distance (sourceCoefficient 28 88 1 1) v2397_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2397_pg : Scalar.QComplex := ((-93086314149696771242664 : Int)/10^30,(141823482472091460536 : Int)/10^30)
theorem v2397_pg_checked : Scalar.distance (sourceCoefficient 28 88 1 2) v2397_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2397_mb : Scalar.QComplex := ((-1029730110031580721370090 : Int)/10^30,(-431476220802319941896741508 : Int)/10^30)
theorem v2397_mb_checked : Scalar.distance (sourceCoefficient 28 88 3 1) v2397_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2397_mg : Scalar.QComplex := ((-93086157102129877710212 : Int)/10^30,(222152726323957426259 : Int)/10^30)
theorem v2397_mg_checked : Scalar.distance (sourceCoefficient 28 88 3 2) v2397_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2397_upper : Scalar.QComplex := ((999994720449052287885772726484 : Int)/10^30,(-3249472883679138961320931825 : Int)/10^30)
theorem v2397_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 88 5) 1) 14) v2397_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2397 : Material (28 : Basis) (88 : Basis) where
  plus := ![v2397_pa,v2397_pb,v2397_pg]
  minus := ![(Primitive.Addresses.material2397 1).one,v2397_mb,v2397_mg]
  upper := v2397_upper
  lower := (Primitive.Addresses.material2397 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2397_pa_checked.trans (by decide +kernel)
    · exact v2397_pb_checked.trans (by decide +kernel)
    · exact v2397_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 88 Primitive.Addresses.material2397
    · exact v2397_mb_checked.trans (by decide +kernel)
    · exact v2397_mg_checked.trans (by decide +kernel)
  upper_error := v2397_upper_checked
  lower_error := reuse_lower_error 28 88 Primitive.Addresses.material2397

def v2398_pa : Scalar.QComplex := ((999998814726933802722182936609 : Int)/10^30,(-1539657340943858904520725998 : Int)/10^30)
theorem v2398_pa_checked : Scalar.distance (sourceCoefficient 28 89 1 0) v2398_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2398_pb : Scalar.QComplex := ((-664327419056398448614447 : Int)/10^30,(-431476935796472841656020181 : Int)/10^30)
theorem v2398_pb_checked : Scalar.distance (sourceCoefficient 28 89 1 1) v2398_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2398_pg : Scalar.QComplex := ((-93086311604941759210984 : Int)/10^30,(143321192878685838310 : Int)/10^30)
theorem v2398_pg_checked : Scalar.distance (sourceCoefficient 28 89 1 2) v2398_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2398_mb : Scalar.QComplex := ((-1036672334289493721915469 : Int)/10^30,(-431476201853247725094238633 : Int)/10^30)
theorem v2398_mb_checked : Scalar.distance (sourceCoefficient 28 89 3 1) v2398_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2398_mg : Scalar.QComplex := ((-93086153264919186688864 : Int)/10^30,(223650433976876807040 : Int)/10^30)
theorem v2398_mg_checked : Scalar.distance (sourceCoefficient 28 89 3 2) v2398_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2398_upper : Scalar.QComplex := ((999994668037273533193008023194 : Int)/10^30,(-3265562282839985514614355275 : Int)/10^30)
theorem v2398_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 89 5) 1) 14) v2398_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2398 : Material (28 : Basis) (89 : Basis) where
  plus := ![v2398_pa,v2398_pb,v2398_pg]
  minus := ![(Primitive.Addresses.material2398 1).one,v2398_mb,v2398_mg]
  upper := v2398_upper
  lower := (Primitive.Addresses.material2398 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2398_pa_checked.trans (by decide +kernel)
    · exact v2398_pb_checked.trans (by decide +kernel)
    · exact v2398_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 89 Primitive.Addresses.material2398
    · exact v2398_mb_checked.trans (by decide +kernel)
    · exact v2398_mg_checked.trans (by decide +kernel)
  upper_error := v2398_upper_checked
  lower_error := reuse_lower_error 28 89 Primitive.Addresses.material2398

def v2399_pa : Scalar.QComplex := ((999998774040085623669036464949 : Int)/10^30,(-1565860251036135813644856783 : Int)/10^30)
theorem v2399_pa_checked : Scalar.distance (sourceCoefficient 28 90 1 0) v2399_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2399_pb : Scalar.QComplex := ((-675633377757769304531349 : Int)/10^30,(-431476914374231464832894653 : Int)/10^30)
theorem v2399_pb_checked : Scalar.distance (sourceCoefficient 28 90 1 1) v2399_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2399_pg : Scalar.QComplex := ((-93086307400441019640514 : Int)/10^30,(145760327370399944464 : Int)/10^30)
theorem v2399_pg_checked : Scalar.distance (sourceCoefficient 28 90 1 2) v2399_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2399_mb : Scalar.QComplex := ((-1047978270294709959210844 : Int)/10^30,(-431476170674481166945036220 : Int)/10^30)
theorem v2399_mb_checked : Scalar.distance (sourceCoefficient 28 90 3 1) v2399_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2399_mg : Scalar.QComplex := ((-93086146955556800836416 : Int)/10^30,(226089563932094893409 : Int)/10^30)
theorem v2399_mg_checked : Scalar.distance (sourceCoefficient 28 90 3 2) v2399_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2399_upper : Scalar.QComplex := ((999994582126640242585477673043 : Int)/10^30,(-3291765083684296976317803412 : Int)/10^30)
theorem v2399_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 90 5) 1) 14) v2399_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2399 : Material (28 : Basis) (90 : Basis) where
  plus := ![v2399_pa,v2399_pb,v2399_pg]
  minus := ![(Primitive.Addresses.material2399 1).one,v2399_mb,v2399_mg]
  upper := v2399_upper
  lower := (Primitive.Addresses.material2399 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2399_pa_checked.trans (by decide +kernel)
    · exact v2399_pb_checked.trans (by decide +kernel)
    · exact v2399_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 90 Primitive.Addresses.material2399
    · exact v2399_mb_checked.trans (by decide +kernel)
    · exact v2399_mg_checked.trans (by decide +kernel)
  upper_error := v2399_upper_checked
  lower_error := reuse_lower_error 28 90 Primitive.Addresses.material2399

def v2400_pa : Scalar.QComplex := ((999998750817366827083679015472 : Int)/10^30,(-1580621303756399969757998519 : Int)/10^30)
theorem v2400_pa_checked : Scalar.distance (sourceCoefficient 28 91 1 0) v2400_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2400_pb : Scalar.QComplex := ((-682002435534834789132849 : Int)/10^30,(-431476902132368275224754403 : Int)/10^30)
theorem v2400_pb_checked : Scalar.distance (sourceCoefficient 28 91 1 1) v2400_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2400_pg : Scalar.QComplex := ((-93086304999058763652267 : Int)/10^30,(147134380567191102254 : Int)/10^30)
theorem v2400_pg_checked : Scalar.distance (sourceCoefficient 28 91 1 2) v2400_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2400_mb : Scalar.QComplex := ((-1054347315136107573509841 : Int)/10^30,(-431476152936412525648371914 : Int)/10^30)
theorem v2400_mb_checked : Scalar.distance (sourceCoefficient 28 91 3 1) v2400_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2400_mg : Scalar.QComplex := ((-93086143368429415220464 : Int)/10^30,(227463614544978516024 : Int)/10^30)
theorem v2400_mg_checked : Scalar.distance (sourceCoefficient 28 91 3 2) v2400_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2400_upper : Scalar.QComplex := ((999994533427718150578113696923 : Int)/10^30,(-3306526074339401166339588588 : Int)/10^30)
theorem v2400_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 91 5) 1) 14) v2400_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2400 : Material (28 : Basis) (91 : Basis) where
  plus := ![v2400_pa,v2400_pb,v2400_pg]
  minus := ![(Primitive.Addresses.material2400 1).one,v2400_mb,v2400_mg]
  upper := v2400_upper
  lower := (Primitive.Addresses.material2400 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2400_pa_checked.trans (by decide +kernel)
    · exact v2400_pb_checked.trans (by decide +kernel)
    · exact v2400_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 91 Primitive.Addresses.material2400
    · exact v2400_mb_checked.trans (by decide +kernel)
    · exact v2400_mg_checked.trans (by decide +kernel)
  upper_error := v2400_upper_checked
  lower_error := reuse_lower_error 28 91 Primitive.Addresses.material2400

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
