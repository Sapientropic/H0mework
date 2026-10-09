import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B106

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2545_pa : Scalar.QComplex := ((999999778331229681463305825026 : Int)/10^30,(-665835934371245582008458024 : Int)/10^30)
theorem v2545_pa_checked : Scalar.distance (sourceCoefficient 31 35 1 0) v2545_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2545_pb : Scalar.QComplex := ((-287293238057118340743244 : Int)/10^30,(-431477424907192605886019867 : Int)/10^30)
theorem v2545_pb_checked : Scalar.distance (sourceCoefficient 31 35 1 1) v2545_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2545_pg : Scalar.QComplex := ((-93086409214256360347344 : Int)/10^30,(61980289995533175269 : Int)/10^30)
theorem v2545_pg_checked : Scalar.distance (sourceCoefficient 31 35 1 2) v2545_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2545_mb : Scalar.QComplex := ((-659638715757792940849237 : Int)/10^30,(-431477016327302584280279136 : Int)/10^30)
theorem v2545_mb_checked : Scalar.distance (sourceCoefficient 31 35 3 1) v2545_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2545_mg : Scalar.QComplex := ((-93086321067733173305287 : Int)/10^30,(142309645613102090749 : Int)/10^30)
theorem v2545_mg_checked : Scalar.distance (sourceCoefficient 31 35 3 2) v2545_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2545_upper : Scalar.QComplex := ((999997139776609522097123481533 : Int)/10^30,(-2391743840815308196939295997 : Int)/10^30)
theorem v2545_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 35 5) 1) 14) v2545_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2545 : Material (31 : Basis) (35 : Basis) where
  plus := ![v2545_pa,v2545_pb,v2545_pg]
  minus := ![(Primitive.Addresses.material2545 1).one,v2545_mb,v2545_mg]
  upper := v2545_upper
  lower := (Primitive.Addresses.material2545 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2545_pa_checked.trans (by decide +kernel)
    · exact v2545_pb_checked.trans (by decide +kernel)
    · exact v2545_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 35 Primitive.Addresses.material2545
    · exact v2545_mb_checked.trans (by decide +kernel)
    · exact v2545_mg_checked.trans (by decide +kernel)
  upper_error := v2545_upper_checked
  lower_error := reuse_lower_error 31 35 Primitive.Addresses.material2545

def v2546_pa : Scalar.QComplex := ((999999767451029644328615186980 : Int)/10^30,(-681980855033569953471776311 : Int)/10^30)
theorem v2546_pa_checked : Scalar.distance (sourceCoefficient 31 36 1 0) v2546_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2546_pb : Scalar.QComplex := ((-294259408256184887883531 : Int)/10^30,(-431477420010533585322879071 : Int)/10^30)
theorem v2546_pb_checked : Scalar.distance (sourceCoefficient 31 36 1 1) v2546_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2546_pg : Scalar.QComplex := ((-93086408179657273105190 : Int)/10^30,(63483163005310758917 : Int)/10^30)
theorem v2546_pg_checked : Scalar.distance (sourceCoefficient 31 36 1 2) v2546_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2546_mb : Scalar.QComplex := ((-666604879137439755760733 : Int)/10^30,(-431477005419154249831666640 : Int)/10^30)
theorem v2546_mb_checked : Scalar.distance (sourceCoefficient 31 36 3 1) v2546_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2546_mg : Scalar.QComplex := ((-93086318736222750741307 : Int)/10^30,(143812517170478952490 : Int)/10^30)
theorem v2546_mg_checked : Scalar.distance (sourceCoefficient 31 36 3 2) v2546_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2546_upper : Scalar.QComplex := ((999997101031757282331668071878 : Int)/10^30,(-2407888718653431537416942543 : Int)/10^30)
theorem v2546_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 36 5) 1) 14) v2546_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2546 : Material (31 : Basis) (36 : Basis) where
  plus := ![v2546_pa,v2546_pb,v2546_pg]
  minus := ![(Primitive.Addresses.material2546 1).one,v2546_mb,v2546_mg]
  upper := v2546_upper
  lower := (Primitive.Addresses.material2546 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2546_pa_checked.trans (by decide +kernel)
    · exact v2546_pb_checked.trans (by decide +kernel)
    · exact v2546_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 36 Primitive.Addresses.material2546
    · exact v2546_mb_checked.trans (by decide +kernel)
    · exact v2546_mg_checked.trans (by decide +kernel)
  upper_error := v2546_upper_checked
  lower_error := reuse_lower_error 31 36 Primitive.Addresses.material2546

def v2547_pa : Scalar.QComplex := ((999999762725650869325630900174 : Int)/10^30,(-688874910242949683532148642 : Int)/10^30)
theorem v2547_pa_checked : Scalar.distance (sourceCoefficient 31 37 1 0) v2547_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2547_pb : Scalar.QComplex := ((-297234038035768610583833 : Int)/10^30,(-431477417873919074859308884 : Int)/10^30)
theorem v2547_pb_checked : Scalar.distance (sourceCoefficient 31 37 1 1) v2547_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2547_pg : Scalar.QComplex := ((-93086407729247659357636 : Int)/10^30,(64124905984519429549 : Int)/10^30)
theorem v2547_pg_checked : Scalar.distance (sourceCoefficient 31 37 1 2) v2547_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2547_mb : Scalar.QComplex := ((-669579505965630771240437 : Int)/10^30,(-431477000715569007498559089 : Int)/10^30)
theorem v2547_mb_checked : Scalar.distance (sourceCoefficient 31 37 3 1) v2547_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2547_mg : Scalar.QComplex := ((-93086317732018016675607 : Int)/10^30,(144454259522054171891 : Int)/10^30)
theorem v2547_mg_checked : Scalar.distance (sourceCoefficient 31 37 3 2) v2547_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2547_upper : Scalar.QComplex := ((999997084407871677638925374907 : Int)/10^30,(-2414782755439350783077368444 : Int)/10^30)
theorem v2547_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 37 5) 1) 14) v2547_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2547 : Material (31 : Basis) (37 : Basis) where
  plus := ![v2547_pa,v2547_pb,v2547_pg]
  minus := ![(Primitive.Addresses.material2547 1).one,v2547_mb,v2547_mg]
  upper := v2547_upper
  lower := (Primitive.Addresses.material2547 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2547_pa_checked.trans (by decide +kernel)
    · exact v2547_pb_checked.trans (by decide +kernel)
    · exact v2547_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 37 Primitive.Addresses.material2547
    · exact v2547_mb_checked.trans (by decide +kernel)
    · exact v2547_mg_checked.trans (by decide +kernel)
  upper_error := v2547_upper_checked
  lower_error := reuse_lower_error 31 37 Primitive.Addresses.material2547

def v2548_pa : Scalar.QComplex := ((999999746402696949100908995918 : Int)/10^30,(-712175920535232690142160380 : Int)/10^30)
theorem v2548_pa_checked : Scalar.distance (sourceCoefficient 31 38 1 0) v2548_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2548_pb : Scalar.QComplex := ((-307287899904809034885951 : Int)/10^30,(-431477410450055014105211377 : Int)/10^30)
theorem v2548_pb_checked : Scalar.distance (sourceCoefficient 31 38 1 1) v2548_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2548_pg : Scalar.QComplex := ((-93086406168717254251754 : Int)/10^30,(66293913814480525397 : Int)/10^30)
theorem v2548_pg_checked : Scalar.distance (sourceCoefficient 31 38 1 2) v2548_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2548_mb : Scalar.QComplex := ((-679633357684698611506952 : Int)/10^30,(-431476984615677727135969153 : Int)/10^30)
theorem v2548_mb_checked : Scalar.distance (sourceCoefficient 31 38 3 1) v2548_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2548_mg : Scalar.QComplex := ((-93086314299732123856383 : Int)/10^30,(146623265197727068164 : Int)/10^30)
theorem v2548_mg_checked : Scalar.distance (sourceCoefficient 31 38 3 2) v2548_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2548_upper : Scalar.QComplex := ((999997027869512155197386355542 : Int)/10^30,(-2438083702855578428777939477 : Int)/10^30)
theorem v2548_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 38 5) 1) 14) v2548_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2548 : Material (31 : Basis) (38 : Basis) where
  plus := ![v2548_pa,v2548_pb,v2548_pg]
  minus := ![(Primitive.Addresses.material2548 1).one,v2548_mb,v2548_mg]
  upper := v2548_upper
  lower := (Primitive.Addresses.material2548 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2548_pa_checked.trans (by decide +kernel)
    · exact v2548_pb_checked.trans (by decide +kernel)
    · exact v2548_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 38 Primitive.Addresses.material2548
    · exact v2548_mb_checked.trans (by decide +kernel)
    · exact v2548_mg_checked.trans (by decide +kernel)
  upper_error := v2548_upper_checked
  lower_error := reuse_lower_error 31 38 Primitive.Addresses.material2548

def v2549_pa : Scalar.QComplex := ((999999736684574710350999557863 : Int)/10^30,(-725693310734145327091812131 : Int)/10^30)
theorem v2549_pa_checked : Scalar.distance (sourceCoefficient 31 39 1 0) v2549_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2549_pb : Scalar.QComplex := ((-313120349716654664398708 : Int)/10^30,(-431477406000159338045221267 : Int)/10^30)
theorem v2549_pb_checked : Scalar.distance (sourceCoefficient 31 39 1 1) v2549_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2549_pg : Scalar.QComplex := ((-93086405236397091144030 : Int)/10^30,(67552199387877398037 : Int)/10^30)
theorem v2549_pg_checked : Scalar.distance (sourceCoefficient 31 39 1 2) v2549_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2549_mb : Scalar.QComplex := ((-685465801484797067366733 : Int)/10^30,(-431476975132642204140976194 : Int)/10^30)
theorem v2549_mb_checked : Scalar.distance (sourceCoefficient 31 39 3 1) v2549_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2549_mg : Scalar.QComplex := ((-93086312281568529131061 : Int)/10^30,(147881549498056404716 : Int)/10^30)
theorem v2549_mg_checked : Scalar.distance (sourceCoefficient 31 39 3 2) v2549_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2549_upper : Scalar.QComplex := ((999996994821615195185378057094 : Int)/10^30,(-2451601056149328865721667894 : Int)/10^30)
theorem v2549_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 39 5) 1) 14) v2549_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2549 : Material (31 : Basis) (39 : Basis) where
  plus := ![v2549_pa,v2549_pb,v2549_pg]
  minus := ![(Primitive.Addresses.material2549 1).one,v2549_mb,v2549_mg]
  upper := v2549_upper
  lower := (Primitive.Addresses.material2549 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2549_pa_checked.trans (by decide +kernel)
    · exact v2549_pb_checked.trans (by decide +kernel)
    · exact v2549_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 39 Primitive.Addresses.material2549
    · exact v2549_mb_checked.trans (by decide +kernel)
    · exact v2549_mg_checked.trans (by decide +kernel)
  upper_error := v2549_upper_checked
  lower_error := reuse_lower_error 31 39 Primitive.Addresses.material2549

def v2550_pa : Scalar.QComplex := ((999999719927124045211431565002 : Int)/10^30,(-748428803206264430900761602 : Int)/10^30)
theorem v2550_pa_checked : Scalar.distance (sourceCoefficient 31 40 1 0) v2550_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2550_pb : Scalar.QComplex := ((-322930203248191427797585 : Int)/10^30,(-431477398278593817573495376 : Int)/10^30)
theorem v2550_pb_checked : Scalar.distance (sourceCoefficient 31 40 1 1) v2550_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2550_pg : Scalar.QComplex := ((-93086403623530937279709 : Int)/10^30,(69668565171009947178 : Int)/10^30)
theorem v2550_pg_checked : Scalar.distance (sourceCoefficient 31 40 1 2) v2550_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2550_mb : Scalar.QComplex := ((-695275644700313750754256 : Int)/10^30,(-431476958945617780446713014 : Int)/10^30)
theorem v2550_mb_checked : Scalar.distance (sourceCoefficient 31 40 3 1) v2550_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2550_mg : Scalar.QComplex := ((-93086308842374622543648 : Int)/10^30,(149997913101338400112 : Int)/10^30)
theorem v2550_mg_checked : Scalar.distance (sourceCoefficient 31 40 3 2) v2550_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2550_upper : Scalar.QComplex := ((999996938824792029187865871519 : Int)/10^30,(-2474336485837763006879436843 : Int)/10^30)
theorem v2550_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 40 5) 1) 14) v2550_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2550 : Material (31 : Basis) (40 : Basis) where
  plus := ![v2550_pa,v2550_pb,v2550_pg]
  minus := ![(Primitive.Addresses.material2550 1).one,v2550_mb,v2550_mg]
  upper := v2550_upper
  lower := (Primitive.Addresses.material2550 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2550_pa_checked.trans (by decide +kernel)
    · exact v2550_pb_checked.trans (by decide +kernel)
    · exact v2550_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 40 Primitive.Addresses.material2550
    · exact v2550_mb_checked.trans (by decide +kernel)
    · exact v2550_mg_checked.trans (by decide +kernel)
  upper_error := v2550_upper_checked
  lower_error := reuse_lower_error 31 40 Primitive.Addresses.material2550

def v2551_pa : Scalar.QComplex := ((999999708981992465872467271937 : Int)/10^30,(-762912793428432655171808834 : Int)/10^30)
theorem v2551_pa_checked : Scalar.distance (sourceCoefficient 31 41 1 0) v2551_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2551_pb : Scalar.QComplex := ((-329179719148000918672140 : Int)/10^30,(-431477393204384142972496979 : Int)/10^30)
theorem v2551_pb_checked : Scalar.distance (sourceCoefficient 31 41 1 1) v2551_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2551_pg : Scalar.QComplex := ((-93086402566757447525933 : Int)/10^30,(71016828079584356972 : Int)/10^30)
theorem v2551_pg_checked : Scalar.distance (sourceCoefficient 31 41 1 2) v2551_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2551_mb : Scalar.QComplex := ((-701525153894328439882855 : Int)/10^30,(-431476948478359241417842175 : Int)/10^30)
theorem v2551_mb_checked : Scalar.distance (sourceCoefficient 31 41 3 1) v2551_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2551_mg : Scalar.QComplex := ((-93086306622111359682463 : Int)/10^30,(151346174595944984039 : Int)/10^30)
theorem v2551_mg_checked : Scalar.distance (sourceCoefficient 31 41 3 2) v2551_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2551_upper : Scalar.QComplex := ((999996902881623605203055934407 : Int)/10^30,(-2488820435597425032881320099 : Int)/10^30)
theorem v2551_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 41 5) 1) 14) v2551_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2551 : Material (31 : Basis) (41 : Basis) where
  plus := ![v2551_pa,v2551_pb,v2551_pg]
  minus := ![(Primitive.Addresses.material2551 1).one,v2551_mb,v2551_mg]
  upper := v2551_upper
  lower := (Primitive.Addresses.material2551 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2551_pa_checked.trans (by decide +kernel)
    · exact v2551_pb_checked.trans (by decide +kernel)
    · exact v2551_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 41 Primitive.Addresses.material2551
    · exact v2551_mb_checked.trans (by decide +kernel)
    · exact v2551_mg_checked.trans (by decide +kernel)
  upper_error := v2551_upper_checked
  lower_error := reuse_lower_error 31 41 Primitive.Addresses.material2551

def v2552_pa : Scalar.QComplex := ((999999700000132631096406923737 : Int)/10^30,(-774596439920741415224227589 : Int)/10^30)
theorem v2552_pa_checked : Scalar.distance (sourceCoefficient 31 42 1 0) v2552_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2552_pb : Scalar.QComplex := ((-334220949709970488165873 : Int)/10^30,(-431477389023280549136605375 : Int)/10^30)
theorem v2552_pb_checked : Scalar.distance (sourceCoefficient 31 42 1 1) v2552_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2552_pg : Scalar.QComplex := ((-93086401697699740448854 : Int)/10^30,(72104416991385812808 : Int)/10^30)
theorem v2552_pg_checked : Scalar.distance (sourceCoefficient 31 42 1 2) v2552_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2552_mb : Scalar.QComplex := ((-706566378971113383971960 : Int)/10^30,(-431476939946902278014236999 : Int)/10^30)
theorem v2552_mb_checked : Scalar.distance (sourceCoefficient 31 42 3 1) v2552_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2552_mg : Scalar.QComplex := ((-93086304814513728496876 : Int)/10^30,(152433762352829722441 : Int)/10^30)
theorem v2552_mg_checked : Scalar.distance (sourceCoefficient 31 42 3 2) v2552_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2552_upper : Scalar.QComplex := ((999996873734863234257263092262 : Int)/10^30,(-2500504049186439553302354279 : Int)/10^30)
theorem v2552_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 42 5) 1) 14) v2552_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2552 : Material (31 : Basis) (42 : Basis) where
  plus := ![v2552_pa,v2552_pb,v2552_pg]
  minus := ![(Primitive.Addresses.material2552 1).one,v2552_mb,v2552_mg]
  upper := v2552_upper
  lower := (Primitive.Addresses.material2552 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2552_pa_checked.trans (by decide +kernel)
    · exact v2552_pb_checked.trans (by decide +kernel)
    · exact v2552_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 42 Primitive.Addresses.material2552
    · exact v2552_mb_checked.trans (by decide +kernel)
    · exact v2552_mg_checked.trans (by decide +kernel)
  upper_error := v2552_upper_checked
  lower_error := reuse_lower_error 31 42 Primitive.Addresses.material2552

def v2553_pa : Scalar.QComplex := ((999999687891311831757357135291 : Int)/10^30,(-790074223680694480880911135 : Int)/10^30)
theorem v2553_pa_checked : Scalar.distance (sourceCoefficient 31 43 1 0) v2553_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2553_pb : Scalar.QComplex := ((-340899265094301678414150 : Int)/10^30,(-431477383363480495215707903 : Int)/10^30)
theorem v2553_pb_checked : Scalar.distance (sourceCoefficient 31 43 1 1) v2553_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2553_pg : Scalar.QComplex := ((-93086400523597139017724 : Int)/10^30,(73545188583003531583 : Int)/10^30)
theorem v2553_pg_checked : Scalar.distance (sourceCoefficient 31 43 1 2) v2553_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2553_mb : Scalar.QComplex := ((-713244686984650003940856 : Int)/10^30,(-431476928524018934977173978 : Int)/10^30)
theorem v2553_mb_checked : Scalar.distance (sourceCoefficient 31 43 3 1) v2553_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2553_mg : Scalar.QComplex := ((-93086302397090570615371 : Int)/10^30,(153874532394784665725 : Int)/10^30)
theorem v2553_mg_checked : Scalar.distance (sourceCoefficient 31 43 3 2) v2553_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2553_upper : Scalar.QComplex := ((999996834912809833479613979935 : Int)/10^30,(-2515981788995325660690012194 : Int)/10^30)
theorem v2553_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 43 5) 1) 14) v2553_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2553 : Material (31 : Basis) (43 : Basis) where
  plus := ![v2553_pa,v2553_pb,v2553_pg]
  minus := ![(Primitive.Addresses.material2553 1).one,v2553_mb,v2553_mg]
  upper := v2553_upper
  lower := (Primitive.Addresses.material2553 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2553_pa_checked.trans (by decide +kernel)
    · exact v2553_pb_checked.trans (by decide +kernel)
    · exact v2553_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 43 Primitive.Addresses.material2553
    · exact v2553_mb_checked.trans (by decide +kernel)
    · exact v2553_mg_checked.trans (by decide +kernel)
  upper_error := v2553_upper_checked
  lower_error := reuse_lower_error 31 43 Primitive.Addresses.material2553

def v2554_pa : Scalar.QComplex := ((999999683247666377176440731412 : Int)/10^30,(-795930001264939292043637441 : Int)/10^30)
theorem v2554_pa_checked : Scalar.distance (sourceCoefficient 31 44 1 0) v2554_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2554_pb : Scalar.QComplex := ((-343425901334319380134055 : Int)/10^30,(-431477381186248806900431445 : Int)/10^30)
theorem v2554_pb_checked : Scalar.distance (sourceCoefficient 31 44 1 1) v2554_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2554_pg : Scalar.QComplex := ((-93086400072610306817817 : Int)/10^30,(74090281995811087458 : Int)/10^30)
theorem v2554_pg_checked : Scalar.distance (sourceCoefficient 31 44 1 2) v2554_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2554_mb : Scalar.QComplex := ((-715771320405032672380563 : Int)/10^30,(-431476924166414777681446813 : Int)/10^30)
theorem v2554_mb_checked : Scalar.distance (sourceCoefficient 31 44 3 1) v2554_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2554_mg : Scalar.QComplex := ((-93086301475712841181522 : Int)/10^30,(154419625215447707517 : Int)/10^30)
theorem v2554_mg_checked : Scalar.distance (sourceCoefficient 31 44 3 2) v2554_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2554_upper : Scalar.QComplex := ((999996820162630416649263288796 : Int)/10^30,(-2521837549843566841693437155 : Int)/10^30)
theorem v2554_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 44 5) 1) 14) v2554_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2554 : Material (31 : Basis) (44 : Basis) where
  plus := ![v2554_pa,v2554_pb,v2554_pg]
  minus := ![(Primitive.Addresses.material2554 1).one,v2554_mb,v2554_mg]
  upper := v2554_upper
  lower := (Primitive.Addresses.material2554 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2554_pa_checked.trans (by decide +kernel)
    · exact v2554_pb_checked.trans (by decide +kernel)
    · exact v2554_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 44 Primitive.Addresses.material2554
    · exact v2554_mb_checked.trans (by decide +kernel)
    · exact v2554_mg_checked.trans (by decide +kernel)
  upper_error := v2554_upper_checked
  lower_error := reuse_lower_error 31 44 Primitive.Addresses.material2554

def v2555_pa : Scalar.QComplex := ((999999680924621121120911643903 : Int)/10^30,(-798843323780489993782416561 : Int)/10^30)
theorem v2555_pa_checked : Scalar.distance (sourceCoefficient 31 45 1 0) v2555_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2555_pb : Scalar.QComplex := ((-344682934431584826296470 : Int)/10^30,(-431477380095700132360694577 : Int)/10^30)
theorem v2555_pb_checked : Scalar.distance (sourceCoefficient 31 45 1 1) v2555_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2555_pg : Scalar.QComplex := ((-93086399846851497074239 : Int)/10^30,(74361472779333645705 : Int)/10^30)
theorem v2555_pg_checked : Scalar.distance (sourceCoefficient 31 45 1 2) v2555_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2555_mb : Scalar.QComplex := ((-717028352093152857541675 : Int)/10^30,(-431476921991103560931807507 : Int)/10^30)
theorem v2555_mb_checked : Scalar.distance (sourceCoefficient 31 45 3 1) v2555_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2555_mg : Scalar.QComplex := ((-93086301015928683297785 : Int)/10^30,(154690815703173858018 : Int)/10^30)
theorem v2555_mg_checked : Scalar.distance (sourceCoefficient 31 45 3 2) v2555_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2555_upper : Scalar.QComplex := ((999996812811458253210302832912 : Int)/10^30,(-2524750864010700512489506758 : Int)/10^30)
theorem v2555_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 45 5) 1) 14) v2555_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2555 : Material (31 : Basis) (45 : Basis) where
  plus := ![v2555_pa,v2555_pb,v2555_pg]
  minus := ![(Primitive.Addresses.material2555 1).one,v2555_mb,v2555_mg]
  upper := v2555_upper
  lower := (Primitive.Addresses.material2555 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2555_pa_checked.trans (by decide +kernel)
    · exact v2555_pb_checked.trans (by decide +kernel)
    · exact v2555_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 45 Primitive.Addresses.material2555
    · exact v2555_mb_checked.trans (by decide +kernel)
    · exact v2555_mg_checked.trans (by decide +kernel)
  upper_error := v2555_upper_checked
  lower_error := reuse_lower_error 31 45 Primitive.Addresses.material2555

def v2556_pa : Scalar.QComplex := ((999999667718260477689970141549 : Int)/10^30,(-815207561688105074059244116 : Int)/10^30)
theorem v2556_pa_checked : Scalar.distance (sourceCoefficient 31 46 1 0) v2556_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2556_pb : Scalar.QComplex := ((-351743734761755474097246 : Int)/10^30,(-431477373879305384753414615 : Int)/10^30)
theorem v2556_pb_checked : Scalar.distance (sourceCoefficient 31 46 1 1) v2556_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2556_pg : Scalar.QComplex := ((-93086398561626335364916 : Int)/10^30,(75884761212870995270 : Int)/10^30)
theorem v2556_pg_checked : Scalar.distance (sourceCoefficient 31 46 1 2) v2556_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2556_mb : Scalar.QComplex := ((-724089144429796156744548 : Int)/10^30,(-431476909681558449677035743 : Int)/10^30)
theorem v2556_mb_checked : Scalar.distance (sourceCoefficient 31 46 3 1) v2556_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2556_mg : Scalar.QComplex := ((-93086298416174688358053 : Int)/10^30,(156214102460429875894 : Int)/10^30)
theorem v2556_mg_checked : Scalar.distance (sourceCoefficient 31 46 3 2) v2556_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2556_upper : Scalar.QComplex := ((999996771361927202624877572678 : Int)/10^30,(-2541115054752725108907939306 : Int)/10^30)
theorem v2556_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 46 5) 1) 14) v2556_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2556 : Material (31 : Basis) (46 : Basis) where
  plus := ![v2556_pa,v2556_pb,v2556_pg]
  minus := ![(Primitive.Addresses.material2556 1).one,v2556_mb,v2556_mg]
  upper := v2556_upper
  lower := (Primitive.Addresses.material2556 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2556_pa_checked.trans (by decide +kernel)
    · exact v2556_pb_checked.trans (by decide +kernel)
    · exact v2556_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 46 Primitive.Addresses.material2556
    · exact v2556_mb_checked.trans (by decide +kernel)
    · exact v2556_mg_checked.trans (by decide +kernel)
  upper_error := v2556_upper_checked
  lower_error := reuse_lower_error 31 46 Primitive.Addresses.material2556

def v2557_pa : Scalar.QComplex := ((999999664500184199950327684012 : Int)/10^30,(-819145603076750295245634435 : Int)/10^30)
theorem v2557_pa_checked : Scalar.distance (sourceCoefficient 31 47 1 0) v2557_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2557_pb : Scalar.QComplex := ((-353442910976111004850898 : Int)/10^30,(-431477372360336604055279996 : Int)/10^30)
theorem v2557_pb_checked : Scalar.distance (sourceCoefficient 31 47 1 1) v2557_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2557_pg : Scalar.QComplex := ((-93086398247996490936180 : Int)/10^30,(76251339413407965364 : Int)/10^30)
theorem v2557_pg_checked : Scalar.distance (sourceCoefficient 31 47 1 2) v2557_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2557_mb : Scalar.QComplex := ((-725788318700669080776173 : Int)/10^30,(-431476906696277689627415045 : Int)/10^30)
theorem v2557_mb_checked : Scalar.distance (sourceCoefficient 31 47 3 1) v2557_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2557_mg : Scalar.QComplex := ((-93086297786204483713906 : Int)/10^30,(156580680253824598098 : Int)/10^30)
theorem v2557_mg_checked : Scalar.distance (sourceCoefficient 31 47 3 2) v2557_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2557_upper : Scalar.QComplex := ((999996761347153537354221888443 : Int)/10^30,(-2545053084722012562765068918 : Int)/10^30)
theorem v2557_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 47 5) 1) 14) v2557_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2557 : Material (31 : Basis) (47 : Basis) where
  plus := ![v2557_pa,v2557_pb,v2557_pg]
  minus := ![(Primitive.Addresses.material2557 1).one,v2557_mb,v2557_mg]
  upper := v2557_upper
  lower := (Primitive.Addresses.material2557 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2557_pa_checked.trans (by decide +kernel)
    · exact v2557_pb_checked.trans (by decide +kernel)
    · exact v2557_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 47 Primitive.Addresses.material2557
    · exact v2557_mb_checked.trans (by decide +kernel)
    · exact v2557_mg_checked.trans (by decide +kernel)
  upper_error := v2557_upper_checked
  lower_error := reuse_lower_error 31 47 Primitive.Addresses.material2557

def v2558_pa : Scalar.QComplex := ((999999641654337281205711473957 : Int)/10^30,(-846576161385362059900778523 : Int)/10^30)
theorem v2558_pa_checked : Scalar.distance (sourceCoefficient 31 48 1 0) v2558_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2558_pb : Scalar.QComplex := ((-365278579346774972976628 : Int)/10^30,(-431477361532396581547716514 : Int)/10^30)
theorem v2558_pb_checked : Scalar.distance (sourceCoefficient 31 48 1 1) v2558_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2558_pg : Scalar.QComplex := ((-93086396016674093903007 : Int)/10^30,(78804752056334712740 : Int)/10^30)
theorem v2558_pg_checked : Scalar.distance (sourceCoefficient 31 48 1 2) v2558_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2558_mb : Scalar.QComplex := ((-737623973320348230628677 : Int)/10^30,(-431476885654692953689123800 : Int)/10^30)
theorem v2558_mb_checked : Scalar.distance (sourceCoefficient 31 48 3 1) v2558_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2558_mg : Scalar.QComplex := ((-93086293351402808094639 : Int)/10^30,(159134090020468388180 : Int)/10^30)
theorem v2558_mg_checked : Scalar.distance (sourceCoefficient 31 48 3 2) v2558_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2558_upper : Scalar.QComplex := ((999996691158685484961835600960 : Int)/10^30,(-2572483562746170723759827731 : Int)/10^30)
theorem v2558_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 48 5) 1) 14) v2558_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2558 : Material (31 : Basis) (48 : Basis) where
  plus := ![v2558_pa,v2558_pb,v2558_pg]
  minus := ![(Primitive.Addresses.material2558 1).one,v2558_mb,v2558_mg]
  upper := v2558_upper
  lower := (Primitive.Addresses.material2558 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2558_pa_checked.trans (by decide +kernel)
    · exact v2558_pb_checked.trans (by decide +kernel)
    · exact v2558_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 48 Primitive.Addresses.material2558
    · exact v2558_mb_checked.trans (by decide +kernel)
    · exact v2558_mg_checked.trans (by decide +kernel)
  upper_error := v2558_upper_checked
  lower_error := reuse_lower_error 31 48 Primitive.Addresses.material2558

def v2559_pa : Scalar.QComplex := ((999999622754321598267611765340 : Int)/10^30,(-868614537346205657945466032 : Int)/10^30)
theorem v2559_pa_checked : Scalar.distance (sourceCoefficient 31 49 1 0) v2559_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2559_pb : Scalar.QComplex := ((-374787642320991839766198 : Int)/10^30,(-431477352519364472805581205 : Int)/10^30)
theorem v2559_pb_checked : Scalar.distance (sourceCoefficient 31 49 1 1) v2559_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2559_pg : Scalar.QComplex := ((-93086394164776369081797 : Int)/10^30,(80856225703325482331 : Int)/10^30)
theorem v2559_pg_checked : Scalar.distance (sourceCoefficient 31 49 1 2) v2559_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2559_mb : Scalar.QComplex := ((-747133024976065588523234 : Int)/10^30,(-431476868435771126459746172 : Int)/10^30)
theorem v2559_mb_checked : Scalar.distance (sourceCoefficient 31 49 3 1) v2559_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2559_mg : Scalar.QComplex := ((-93086289729176410409752 : Int)/10^30,(161185561305497431876 : Int)/10^30)
theorem v2559_mg_checked : Scalar.distance (sourceCoefficient 31 49 3 2) v2559_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2559_upper : Scalar.QComplex := ((999996634222460348810341114927 : Int)/10^30,(-2594521873263729664900191925 : Int)/10^30)
theorem v2559_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 49 5) 1) 14) v2559_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2559 : Material (31 : Basis) (49 : Basis) where
  plus := ![v2559_pa,v2559_pb,v2559_pg]
  minus := ![(Primitive.Addresses.material2559 1).one,v2559_mb,v2559_mg]
  upper := v2559_upper
  lower := (Primitive.Addresses.material2559 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2559_pa_checked.trans (by decide +kernel)
    · exact v2559_pb_checked.trans (by decide +kernel)
    · exact v2559_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 49 Primitive.Addresses.material2559
    · exact v2559_mb_checked.trans (by decide +kernel)
    · exact v2559_mg_checked.trans (by decide +kernel)
  upper_error := v2559_upper_checked
  lower_error := reuse_lower_error 31 49 Primitive.Addresses.material2559

def v2560_pa : Scalar.QComplex := ((999999620514078961735963069128 : Int)/10^30,(-871189817472038528418288582 : Int)/10^30)
theorem v2560_pa_checked : Scalar.distance (sourceCoefficient 31 50 1 0) v2560_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2560_pb : Scalar.QComplex := ((-375898817699540262045556 : Int)/10^30,(-431477351447919043018056101 : Int)/10^30)
theorem v2560_pb_checked : Scalar.distance (sourceCoefficient 31 50 1 1) v2560_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2560_pg : Scalar.QComplex := ((-93086393944932114725669 : Int)/10^30,(81095949324786703508 : Int)/10^30)
theorem v2560_pg_checked : Scalar.distance (sourceCoefficient 31 50 1 2) v2560_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2560_mb : Scalar.QComplex := ((-748244199016263484349645 : Int)/10^30,(-431476866405431789414307857 : Int)/10^30)
theorem v2560_mb_checked : Scalar.distance (sourceCoefficient 31 50 3 1) v2560_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2560_mg : Scalar.QComplex := ((-93086289302461549341770 : Int)/10^30,(161425284647982902780 : Int)/10^30)
theorem v2560_mg_checked : Scalar.distance (sourceCoefficient 31 50 3 2) v2560_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2560_upper : Scalar.QComplex := ((999996627537521179257424704034 : Int)/10^30,(-2597097145687529744169749074 : Int)/10^30)
theorem v2560_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 50 5) 1) 14) v2560_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2560 : Material (31 : Basis) (50 : Basis) where
  plus := ![v2560_pa,v2560_pb,v2560_pg]
  minus := ![(Primitive.Addresses.material2560 1).one,v2560_mb,v2560_mg]
  upper := v2560_upper
  lower := (Primitive.Addresses.material2560 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2560_pa_checked.trans (by decide +kernel)
    · exact v2560_pb_checked.trans (by decide +kernel)
    · exact v2560_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 50 Primitive.Addresses.material2560
    · exact v2560_mb_checked.trans (by decide +kernel)
    · exact v2560_mg_checked.trans (by decide +kernel)
  upper_error := v2560_upper_checked
  lower_error := reuse_lower_error 31 50 Primitive.Addresses.material2560

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
