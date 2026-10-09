import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B108
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B109

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2609_pa : Scalar.QComplex := ((999999808264743739050156974522 : Int)/10^30,(-619249929963250938597198384 : Int)/10^30)
theorem v2609_pa_checked : Scalar.distance (sourceCoefficient 32 34 1 0) v2609_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2609_pb : Scalar.QComplex := ((-267192424637174855615576 : Int)/10^30,(-431477438233740676714976419 : Int)/10^30)
theorem v2609_pb_checked : Scalar.distance (sourceCoefficient 32 34 1 1) v2609_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2609_pg : Scalar.QComplex := ((-93086412044984887067020 : Int)/10^30,(57643765191729300778 : Int)/10^30)
theorem v2609_pg_checked : Scalar.distance (sourceCoefficient 32 34 1 2) v2609_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2609_mb : Scalar.QComplex := ((-639537921322511724203129 : Int)/10^30,(-431477046999942367407705633 : Int)/10^30)
theorem v2609_mb_checked : Scalar.distance (sourceCoefficient 32 34 3 1) v2609_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2609_mg : Scalar.QComplex := ((-93086327640686241871184 : Int)/10^30,(137973124866775816966 : Int)/10^30)
theorem v2609_mg_checked : Scalar.distance (sourceCoefficient 32 34 3 2) v2609_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2609_upper : Scalar.QComplex := ((999997250113296356123532517127 : Int)/10^30,(-2345157957454224458957103917 : Int)/10^30)
theorem v2609_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 34 5) 1) 14) v2609_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2609 : Material (32 : Basis) (34 : Basis) where
  plus := ![v2609_pa,v2609_pb,v2609_pg]
  minus := ![(Primitive.Addresses.material2609 1).one,v2609_mb,v2609_mg]
  upper := v2609_upper
  lower := (Primitive.Addresses.material2609 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2609_pa_checked.trans (by decide +kernel)
    · exact v2609_pb_checked.trans (by decide +kernel)
    · exact v2609_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 34 Primitive.Addresses.material2609
    · exact v2609_mb_checked.trans (by decide +kernel)
    · exact v2609_mg_checked.trans (by decide +kernel)
  upper_error := v2609_upper_checked
  lower_error := reuse_lower_error 32 34 Primitive.Addresses.material2609

def v2610_pa : Scalar.QComplex := ((999999775139731773497783736594 : Int)/10^30,(-670612023371833235454854270 : Int)/10^30)
theorem v2610_pa_checked : Scalar.distance (sourceCoefficient 32 35 1 0) v2610_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2610_pb : Scalar.QComplex := ((-289354013132303184173421 : Int)/10^30,(-431477423582733070672056336 : Int)/10^30)
theorem v2610_pb_checked : Scalar.distance (sourceCoefficient 32 35 1 1) v2610_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2610_pg : Scalar.QComplex := ((-93086408922845151278033 : Int)/10^30,(62424879073042110792 : Int)/10^30)
theorem v2610_pg_checked : Scalar.distance (sourceCoefficient 32 35 1 2) v2610_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2610_mb : Scalar.QComplex := ((-661699488922708114267921 : Int)/10^30,(-431477013224487466202585217 : Int)/10^30)
theorem v2610_mb_checked : Scalar.distance (sourceCoefficient 32 35 3 1) v2610_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2610_mg : Scalar.QComplex := ((-93086320392661722400218 : Int)/10^30,(142754234273595445237 : Int)/10^30)
theorem v2610_mg_checked : Scalar.distance (sourceCoefficient 32 35 3 2) v2610_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2610_upper : Scalar.QComplex := ((999997128342020035888054839300 : Int)/10^30,(-2396519917194236464115251298 : Int)/10^30)
theorem v2610_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 35 5) 1) 14) v2610_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2610 : Material (32 : Basis) (35 : Basis) where
  plus := ![v2610_pa,v2610_pb,v2610_pg]
  minus := ![(Primitive.Addresses.material2610 1).one,v2610_mb,v2610_mg]
  upper := v2610_upper
  lower := (Primitive.Addresses.material2610 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2610_pa_checked.trans (by decide +kernel)
    · exact v2610_pb_checked.trans (by decide +kernel)
    · exact v2610_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 35 Primitive.Addresses.material2610
    · exact v2610_mb_checked.trans (by decide +kernel)
    · exact v2610_mg_checked.trans (by decide +kernel)
  upper_error := v2610_upper_checked
  lower_error := reuse_lower_error 32 35 Primitive.Addresses.material2610

def v2611_pa : Scalar.QComplex := ((999999764182422141281102686809 : Int)/10^30,(-686756943982008650409153045 : Int)/10^30)
theorem v2611_pa_checked : Scalar.distance (sourceCoefficient 32 36 1 0) v2611_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2611_pb : Scalar.QComplex := ((-296320183316368996432735 : Int)/10^30,(-431477418663893345641614125 : Int)/10^30)
theorem v2611_pb_checked : Scalar.distance (sourceCoefficient 32 36 1 1) v2611_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2611_pg : Scalar.QComplex := ((-93086407882264516611351 : Int)/10^30,(63927752078774394291 : Int)/10^30)
theorem v2611_pg_checked : Scalar.distance (sourceCoefficient 32 36 1 2) v2611_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2611_mb : Scalar.QComplex := ((-668665652268213250910468 : Int)/10^30,(-431477002294158448490519883 : Int)/10^30)
theorem v2611_mb_checked : Scalar.distance (sourceCoefficient 32 36 3 1) v2611_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2611_mg : Scalar.QComplex := ((-93086318055169758129825 : Int)/10^30,(144257105821765202307 : Int)/10^30)
theorem v2611_mg_checked : Scalar.distance (sourceCoefficient 32 36 3 2) v2611_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2611_upper : Scalar.QComplex := ((999997089520058405890660981397 : Int)/10^30,(-2412664794847126759969929091 : Int)/10^30)
theorem v2611_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 36 5) 1) 14) v2611_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2611 : Material (32 : Basis) (36 : Basis) where
  plus := ![v2611_pa,v2611_pb,v2611_pg]
  minus := ![(Primitive.Addresses.material2611 1).one,v2611_mb,v2611_mg]
  upper := v2611_upper
  lower := (Primitive.Addresses.material2611 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2611_pa_checked.trans (by decide +kernel)
    · exact v2611_pb_checked.trans (by decide +kernel)
    · exact v2611_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 36 Primitive.Addresses.material2611
    · exact v2611_mb_checked.trans (by decide +kernel)
    · exact v2611_mg_checked.trans (by decide +kernel)
  upper_error := v2611_upper_checked
  lower_error := reuse_lower_error 32 36 Primitive.Addresses.material2611

def v2612_pa : Scalar.QComplex := ((999999759424116737725891118161 : Int)/10^30,(-693650999168740915568020534 : Int)/10^30)
theorem v2612_pa_checked : Scalar.distance (sourceCoefficient 32 37 1 0) v2612_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2612_pb : Scalar.QComplex := ((-299294813089438137837726 : Int)/10^30,(-431477416517807435203836096 : Int)/10^30)
theorem v2612_pb_checked : Scalar.distance (sourceCoefficient 32 37 1 1) v2612_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2612_pg : Scalar.QComplex := ((-93086407429300717616408 : Int)/10^30,(64569495056226255213 : Int)/10^30)
theorem v2612_pg_checked : Scalar.distance (sourceCoefficient 32 37 1 2) v2612_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2612_mb : Scalar.QComplex := ((-671640279081716295918816 : Int)/10^30,(-431476997581101815331629816 : Int)/10^30)
theorem v2612_mb_checked : Scalar.distance (sourceCoefficient 32 37 3 1) v2612_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2612_mg : Scalar.QComplex := ((-93086317048410841283824 : Int)/10^30,(144898848169379465821 : Int)/10^30)
theorem v2612_mg_checked : Scalar.distance (sourceCoefficient 32 37 3 2) v2612_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2612_upper : Scalar.QComplex := ((999997072863246260773506255667 : Int)/10^30,(-2419558831553570200658852942 : Int)/10^30)
theorem v2612_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 37 5) 1) 14) v2612_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2612 : Material (32 : Basis) (37 : Basis) where
  plus := ![v2612_pa,v2612_pb,v2612_pg]
  minus := ![(Primitive.Addresses.material2612 1).one,v2612_mb,v2612_mg]
  upper := v2612_upper
  lower := (Primitive.Addresses.material2612 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2612_pa_checked.trans (by decide +kernel)
    · exact v2612_pb_checked.trans (by decide +kernel)
    · exact v2612_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 37 Primitive.Addresses.material2612
    · exact v2612_mb_checked.trans (by decide +kernel)
    · exact v2612_mg_checked.trans (by decide +kernel)
  upper_error := v2612_upper_checked
  lower_error := reuse_lower_error 32 37 Primitive.Addresses.material2612

def v2613_pa : Scalar.QComplex := ((999999742989875093881822880131 : Int)/10^30,(-716952009382798264001194494 : Int)/10^30)
theorem v2613_pa_checked : Scalar.distance (sourceCoefficient 32 38 1 0) v2613_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2613_pb : Scalar.QComplex := ((-309348674935976820261619 : Int)/10^30,(-431477409061931273951457143 : Int)/10^30)
theorem v2613_pb_checked : Scalar.distance (sourceCoefficient 32 38 1 1) v2613_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2613_pg : Scalar.QComplex := ((-93086405860137498453081 : Int)/10^30,(66738502880119228364 : Int)/10^30)
theorem v2613_pg_checked : Scalar.distance (sourceCoefficient 32 38 1 2) v2613_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2613_mb : Scalar.QComplex := ((-681694130750657401727002 : Int)/10^30,(-431476981449198465808316275 : Int)/10^30)
theorem v2613_mb_checked : Scalar.distance (sourceCoefficient 32 38 3 1) v2613_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2613_mg : Scalar.QComplex := ((-93086313607492142858063 : Int)/10^30,(147067853831534511932 : Int)/10^30)
theorem v2613_mg_checked : Scalar.distance (sourceCoefficient 32 38 3 2) v2613_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2613_upper : Scalar.QComplex := ((999997016213599315473001896163 : Int)/10^30,(-2442859778699499789666944811 : Int)/10^30)
theorem v2613_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 38 5) 1) 14) v2613_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2613 : Material (32 : Basis) (38 : Basis) where
  plus := ![v2613_pa,v2613_pb,v2613_pg]
  minus := ![(Primitive.Addresses.material2613 1).one,v2613_mb,v2613_mg]
  upper := v2613_upper
  lower := (Primitive.Addresses.material2613 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2613_pa_checked.trans (by decide +kernel)
    · exact v2613_pb_checked.trans (by decide +kernel)
    · exact v2613_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 38 Primitive.Addresses.material2613
    · exact v2613_mb_checked.trans (by decide +kernel)
    · exact v2613_mg_checked.trans (by decide +kernel)
  upper_error := v2613_upper_checked
  lower_error := reuse_lower_error 32 38 Primitive.Addresses.material2613

def v2614_pa : Scalar.QComplex := ((999999733207192582183425506461 : Int)/10^30,(-730469399535142101018073706 : Int)/10^30)
theorem v2614_pa_checked : Scalar.distance (sourceCoefficient 32 39 1 0) v2614_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2614_pb : Scalar.QComplex := ((-315181124734426856312748 : Int)/10^30,(-431477404593464727020012432 : Int)/10^30)
theorem v2614_pb_checked : Scalar.distance (sourceCoefficient 32 39 1 1) v2614_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2614_pg : Scalar.QComplex := ((-93086404922809264251899 : Int)/10^30,(67996788449903664901 : Int)/10^30)
theorem v2614_pg_checked : Scalar.distance (sourceCoefficient 32 39 1 2) v2614_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2614_mb : Scalar.QComplex := ((-687526574521334443951855 : Int)/10^30,(-431476971947592090416446514 : Int)/10^30)
theorem v2614_mb_checked : Scalar.distance (sourceCoefficient 32 39 3 1) v2614_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2614_mg : Scalar.QComplex := ((-93086311584320482021385 : Int)/10^30,(148326138123929673928 : Int)/10^30)
theorem v2614_mg_checked : Scalar.distance (sourceCoefficient 32 39 3 2) v2614_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2614_upper : Scalar.QComplex := ((999996983101142259040972431917 : Int)/10^30,(-2456377131835256321789778246 : Int)/10^30)
theorem v2614_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 39 5) 1) 14) v2614_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2614 : Material (32 : Basis) (39 : Basis) where
  plus := ![v2614_pa,v2614_pb,v2614_pg]
  minus := ![(Primitive.Addresses.material2614 1).one,v2614_mb,v2614_mg]
  upper := v2614_upper
  lower := (Primitive.Addresses.material2614 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2614_pa_checked.trans (by decide +kernel)
    · exact v2614_pb_checked.trans (by decide +kernel)
    · exact v2614_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 39 Primitive.Addresses.material2614
    · exact v2614_mb_checked.trans (by decide +kernel)
    · exact v2614_mg_checked.trans (by decide +kernel)
  upper_error := v2614_upper_checked
  lower_error := reuse_lower_error 32 39 Primitive.Addresses.material2614

def v2615_pa : Scalar.QComplex := ((999999716341155157473001999010 : Int)/10^30,(-753204891926966801086470468 : Int)/10^30)
theorem v2615_pa_checked : Scalar.distance (sourceCoefficient 32 40 1 0) v2615_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2615_pb : Scalar.QComplex := ((-324990978242866799721421 : Int)/10^30,(-431477396840664042921745148 : Int)/10^30)
theorem v2615_pb_checked : Scalar.distance (sourceCoefficient 32 40 1 1) v2615_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2615_pg : Scalar.QComplex := ((-93086403301519815585091 : Int)/10^30,(70113154226807614567 : Int)/10^30)
theorem v2615_pg_checked : Scalar.distance (sourceCoefficient 32 40 1 2) v2615_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2615_mb : Scalar.QComplex := ((-697336417686799776519019 : Int)/10^30,(-431476955729332534657436285 : Int)/10^30)
theorem v2615_mb_checked : Scalar.distance (sourceCoefficient 32 40 3 1) v2615_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2615_mg : Scalar.QComplex := ((-93086308136703289142864 : Int)/10^30,(150442501713714148125 : Int)/10^30)
theorem v2615_mg_checked : Scalar.distance (sourceCoefficient 32 40 3 2) v2615_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2615_upper : Scalar.QComplex := ((999996926995732633780684220527 : Int)/10^30,(-2479112561255985282690657349 : Int)/10^30)
theorem v2615_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 40 5) 1) 14) v2615_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2615 : Material (32 : Basis) (40 : Basis) where
  plus := ![v2615_pa,v2615_pb,v2615_pg]
  minus := ![(Primitive.Addresses.material2615 1).one,v2615_mb,v2615_mg]
  upper := v2615_upper
  lower := (Primitive.Addresses.material2615 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2615_pa_checked.trans (by decide +kernel)
    · exact v2615_pb_checked.trans (by decide +kernel)
    · exact v2615_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 40 Primitive.Addresses.material2615
    · exact v2615_mb_checked.trans (by decide +kernel)
    · exact v2615_mg_checked.trans (by decide +kernel)
  upper_error := v2615_upper_checked
  lower_error := reuse_lower_error 32 40 Primitive.Addresses.material2615

def v2616_pa : Scalar.QComplex := ((999999705326846736429815987134 : Int)/10^30,(-767688882096694893727052059 : Int)/10^30)
theorem v2616_pa_checked : Scalar.distance (sourceCoefficient 32 41 1 0) v2616_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2616_pb : Scalar.QComplex := ((-331240494127591798733491 : Int)/10^30,(-431477391746555533719914504 : Int)/10^30)
theorem v2616_pb_checked : Scalar.distance (sourceCoefficient 32 41 1 1) v2616_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2616_pg : Scalar.QComplex := ((-93086402239380138155405 : Int)/10^30,(71461417131314137173 : Int)/10^30)
theorem v2616_pg_checked : Scalar.distance (sourceCoefficient 32 41 1 2) v2616_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2616_mb : Scalar.QComplex := ((-703585926848558181351502 : Int)/10^30,(-431476945242175181454215840 : Int)/10^30)
theorem v2616_mb_checked : Scalar.distance (sourceCoefficient 32 41 3 1) v2616_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2616_mg : Scalar.QComplex := ((-93086305911073844114250 : Int)/10^30,(151790763199622068097 : Int)/10^30)
theorem v2616_mg_checked : Scalar.distance (sourceCoefficient 32 41 3 2) v2616_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2616_upper : Scalar.QComplex := ((999996890983387561629342062993 : Int)/10^30,(-2493596510843814302058060821 : Int)/10^30)
theorem v2616_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 41 5) 1) 14) v2616_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2616 : Material (32 : Basis) (41 : Basis) where
  plus := ![v2616_pa,v2616_pb,v2616_pg]
  minus := ![(Primitive.Addresses.material2616 1).one,v2616_mb,v2616_mg]
  upper := v2616_upper
  lower := (Primitive.Addresses.material2616 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2616_pa_checked.trans (by decide +kernel)
    · exact v2616_pb_checked.trans (by decide +kernel)
    · exact v2616_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 41 Primitive.Addresses.material2616
    · exact v2616_mb_checked.trans (by decide +kernel)
    · exact v2616_mg_checked.trans (by decide +kernel)
  upper_error := v2616_upper_checked
  lower_error := reuse_lower_error 32 41 Primitive.Addresses.material2616

def v2617_pa : Scalar.QComplex := ((999999696289184753799206503948 : Int)/10^30,(-779372528545972224198096756 : Int)/10^30)
theorem v2617_pa_checked : Scalar.distance (sourceCoefficient 32 42 1 0) v2617_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2617_pb : Scalar.QComplex := ((-336281724677183305303349 : Int)/10^30,(-431477387549400358420175296 : Int)/10^30)
theorem v2617_pb_checked : Scalar.distance (sourceCoefficient 32 42 1 1) v2617_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2617_pg : Scalar.QComplex := ((-93086401365993745485748 : Int)/10^30,(72549006039777557890 : Int)/10^30)
theorem v2617_pg_checked : Scalar.distance (sourceCoefficient 32 42 1 2) v2617_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2617_mb : Scalar.QComplex := ((-708627151899113275258743 : Int)/10^30,(-431476936694666653245211248 : Int)/10^30)
theorem v2617_mb_checked : Scalar.distance (sourceCoefficient 32 42 3 1) v2617_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2617_mg : Scalar.QComplex := ((-93086304099147531828426 : Int)/10^30,(152878350949433311914 : Int)/10^30)
theorem v2617_mg_checked : Scalar.distance (sourceCoefficient 32 42 3 2) v2617_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2617_upper : Scalar.QComplex := ((999996861780825200208088011118 : Int)/10^30,(-2505280124293488012122337274 : Int)/10^30)
theorem v2617_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 42 5) 1) 14) v2617_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2617 : Material (32 : Basis) (42 : Basis) where
  plus := ![v2617_pa,v2617_pb,v2617_pg]
  minus := ![(Primitive.Addresses.material2617 1).one,v2617_mb,v2617_mg]
  upper := v2617_upper
  lower := (Primitive.Addresses.material2617 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2617_pa_checked.trans (by decide +kernel)
    · exact v2617_pb_checked.trans (by decide +kernel)
    · exact v2617_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 42 Primitive.Addresses.material2617
    · exact v2617_mb_checked.trans (by decide +kernel)
    · exact v2617_mg_checked.trans (by decide +kernel)
  upper_error := v2617_upper_checked
  lower_error := reuse_lower_error 32 42 Primitive.Addresses.material2617

def v2618_pa : Scalar.QComplex := ((999999684106440665324851964643 : Int)/10^30,(-794850312247915938969477034 : Int)/10^30)
theorem v2618_pa_checked : Scalar.distance (sourceCoefficient 32 43 1 0) v2618_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2618_pb : Scalar.QComplex := ((-342960040044828008440867 : Int)/10^30,(-431477381868336146350340624 : Int)/10^30)
theorem v2618_pb_checked : Scalar.distance (sourceCoefficient 32 43 1 1) v2618_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2618_pg : Scalar.QComplex := ((-93086400186156764844470 : Int)/10^30,(73989777626895373866 : Int)/10^30)
theorem v2618_pg_checked : Scalar.distance (sourceCoefficient 32 43 1 2) v2618_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2618_mb : Scalar.QComplex := ((-715305459877613403549620 : Int)/10^30,(-431476925250519174376515772 : Int)/10^30)
theorem v2618_mb_checked : Scalar.distance (sourceCoefficient 32 43 3 1) v2618_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2618_mg : Scalar.QComplex := ((-93086301675990000755158 : Int)/10^30,(154319120981939843083 : Int)/10^30)
theorem v2618_mg_checked : Scalar.distance (sourceCoefficient 32 43 3 2) v2618_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2618_upper : Scalar.QComplex := ((999996822884848720514066736264 : Int)/10^30,(-2520757863916779964243673669 : Int)/10^30)
theorem v2618_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 43 5) 1) 14) v2618_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2618 : Material (32 : Basis) (43 : Basis) where
  plus := ![v2618_pa,v2618_pb,v2618_pg]
  minus := ![(Primitive.Addresses.material2618 1).one,v2618_mb,v2618_mg]
  upper := v2618_upper
  lower := (Primitive.Addresses.material2618 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2618_pa_checked.trans (by decide +kernel)
    · exact v2618_pb_checked.trans (by decide +kernel)
    · exact v2618_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 43 Primitive.Addresses.material2618
    · exact v2618_mb_checked.trans (by decide +kernel)
    · exact v2618_mg_checked.trans (by decide +kernel)
  upper_error := v2618_upper_checked
  lower_error := reuse_lower_error 32 43 Primitive.Addresses.material2618

def v2619_pa : Scalar.QComplex := ((999999679434827489642859034097 : Int)/10^30,(-800706089809915493024812761 : Int)/10^30)
theorem v2619_pa_checked : Scalar.distance (sourceCoefficient 32 44 1 0) v2619_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2619_pb : Scalar.QComplex := ((-345486676278446824633235 : Int)/10^30,(-431477379683059496139234131 : Int)/10^30)
theorem v2619_pb_checked : Scalar.distance (sourceCoefficient 32 44 1 1) v2619_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2619_pg : Scalar.QComplex := ((-93086399733000419893269 : Int)/10^30,(74534871037977320108 : Int)/10^30)
theorem v2619_pg_checked : Scalar.distance (sourceCoefficient 32 44 1 2) v2619_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2619_mb : Scalar.QComplex := ((-717832093284654749059919 : Int)/10^30,(-431476920884870063702415574 : Int)/10^30)
theorem v2619_mb_checked : Scalar.distance (sourceCoefficient 32 44 3 1) v2619_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2619_mg : Scalar.QComplex := ((-93086300752442760866947 : Int)/10^30,(154864213799005084091 : Int)/10^30)
theorem v2619_mg_checked : Scalar.distance (sourceCoefficient 32 44 3 2) v2619_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2619_upper : Scalar.QComplex := ((999996808106701662630570472607 : Int)/10^30,(-2526613624694506171862785993 : Int)/10^30)
theorem v2619_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 44 5) 1) 14) v2619_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2619 : Material (32 : Basis) (44 : Basis) where
  plus := ![v2619_pa,v2619_pb,v2619_pg]
  minus := ![(Primitive.Addresses.material2619 1).one,v2619_mb,v2619_mg]
  upper := v2619_upper
  lower := (Primitive.Addresses.material2619 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2619_pa_checked.trans (by decide +kernel)
    · exact v2619_pb_checked.trans (by decide +kernel)
    · exact v2619_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 44 Primitive.Addresses.material2619
    · exact v2619_mb_checked.trans (by decide +kernel)
    · exact v2619_mg_checked.trans (by decide +kernel)
  upper_error := v2619_upper_checked
  lower_error := reuse_lower_error 32 44 Primitive.Addresses.material2619

def v2620_pa : Scalar.QComplex := ((999999677097867942885651341304 : Int)/10^30,(-803619412314337893438337260 : Int)/10^30)
theorem v2620_pa_checked : Scalar.distance (sourceCoefficient 32 45 1 0) v2620_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2620_pb : Scalar.QComplex := ((-346743709372511196250202 : Int)/10^30,(-431477378588508352536045135 : Int)/10^30)
theorem v2620_pb_checked : Scalar.distance (sourceCoefficient 32 45 1 1) v2620_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2620_pg : Scalar.QComplex := ((-93086399506162250448193 : Int)/10^30,(74806061820636633490 : Int)/10^30)
theorem v2620_pg_checked : Scalar.distance (sourceCoefficient 32 45 1 2) v2620_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2620_mb : Scalar.QComplex := ((-719089124966119910330245 : Int)/10^30,(-431476918705556382142009455 : Int)/10^30)
theorem v2620_mb_checked : Scalar.distance (sourceCoefficient 32 45 3 1) v2620_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2620_mg : Scalar.QComplex := ((-93086300291579244428548 : Int)/10^30,(155135404284936551239 : Int)/10^30)
theorem v2620_mg_checked : Scalar.distance (sourceCoefficient 32 45 3 2) v2620_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2620_upper : Scalar.QComplex := ((999996800741615248420071459965 : Int)/10^30,(-2529526938826496754451393257 : Int)/10^30)
theorem v2620_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 45 5) 1) 14) v2620_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2620 : Material (32 : Basis) (45 : Basis) where
  plus := ![v2620_pa,v2620_pb,v2620_pg]
  minus := ![(Primitive.Addresses.material2620 1).one,v2620_mb,v2620_mg]
  upper := v2620_upper
  lower := (Primitive.Addresses.material2620 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2620_pa_checked.trans (by decide +kernel)
    · exact v2620_pb_checked.trans (by decide +kernel)
    · exact v2620_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 45 Primitive.Addresses.material2620
    · exact v2620_mb_checked.trans (by decide +kernel)
    · exact v2620_mg_checked.trans (by decide +kernel)
  upper_error := v2620_upper_checked
  lower_error := reuse_lower_error 32 45 Primitive.Addresses.material2620

def v2621_pa : Scalar.QComplex := ((999999663813350225482519452283 : Int)/10^30,(-819983650158691563213593859 : Int)/10^30)
theorem v2621_pa_checked : Scalar.distance (sourceCoefficient 32 46 1 0) v2621_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2621_pb : Scalar.QComplex := ((-353804509684484593198113 : Int)/10^30,(-431477372349631591490825206 : Int)/10^30)
theorem v2621_pb_checked : Scalar.distance (sourceCoefficient 32 46 1 1) v2621_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2621_pg : Scalar.QComplex := ((-93086398214874286270504 : Int)/10^30,(76329350249266667361 : Int)/10^30)
theorem v2621_pg_checked : Scalar.distance (sourceCoefficient 32 46 1 2) v2621_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2621_mb : Scalar.QComplex := ((-726149917265165000411277 : Int)/10^30,(-431476906373529281523786718 : Int)/10^30)
theorem v2621_mb_checked : Scalar.distance (sourceCoefficient 32 46 3 1) v2621_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2621_mg : Scalar.QComplex := ((-93086297685762453512701 : Int)/10^30,(156658691032053329775 : Int)/10^30)
theorem v2621_mg_checked : Scalar.distance (sourceCoefficient 32 46 3 2) v2621_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2621_upper : Scalar.QComplex := ((999996759213927349451692015187 : Int)/10^30,(-2545891129370368015267057925 : Int)/10^30)
theorem v2621_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 46 5) 1) 14) v2621_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2621 : Material (32 : Basis) (46 : Basis) where
  plus := ![v2621_pa,v2621_pb,v2621_pg]
  minus := ![(Primitive.Addresses.material2621 1).one,v2621_mb,v2621_mg]
  upper := v2621_upper
  lower := (Primitive.Addresses.material2621 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2621_pa_checked.trans (by decide +kernel)
    · exact v2621_pb_checked.trans (by decide +kernel)
    · exact v2621_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 46 Primitive.Addresses.material2621
    · exact v2621_mb_checked.trans (by decide +kernel)
    · exact v2621_mg_checked.trans (by decide +kernel)
  upper_error := v2621_upper_checked
  lower_error := reuse_lower_error 32 46 Primitive.Addresses.material2621

def v2622_pa : Scalar.QComplex := ((999999660576465507420263317669 : Int)/10^30,(-823921691531922046852784322 : Int)/10^30)
theorem v2622_pa_checked : Scalar.distance (sourceCoefficient 32 47 1 0) v2622_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2622_pb : Scalar.QComplex := ((-355503685894406048839821 : Int)/10^30,(-431477370825252531384844078 : Int)/10^30)
theorem v2622_pb_checked : Scalar.distance (sourceCoefficient 32 47 1 1) v2622_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2622_pg : Scalar.QComplex := ((-93086397899785433045918 : Int)/10^30,(76695928448607885054 : Int)/10^30)
theorem v2622_pg_checked : Scalar.distance (sourceCoefficient 32 47 1 2) v2622_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2622_mb : Scalar.QComplex := ((-727849091526935023522935 : Int)/10^30,(-431476903382838247907220914 : Int)/10^30)
theorem v2622_mb_checked : Scalar.distance (sourceCoefficient 32 47 3 1) v2622_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2622_mg : Scalar.QComplex := ((-93086297054333241647841 : Int)/10^30,(157025268822993241145 : Int)/10^30)
theorem v2622_mg_checked : Scalar.distance (sourceCoefficient 32 47 3 2) v2622_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2622_upper : Scalar.QComplex := ((999996749180345298475823712207 : Int)/10^30,(-2549829159291779092826974583 : Int)/10^30)
theorem v2622_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 47 5) 1) 14) v2622_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2622 : Material (32 : Basis) (47 : Basis) where
  plus := ![v2622_pa,v2622_pb,v2622_pg]
  minus := ![(Primitive.Addresses.material2622 1).one,v2622_mb,v2622_mg]
  upper := v2622_upper
  lower := (Primitive.Addresses.material2622 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2622_pa_checked.trans (by decide +kernel)
    · exact v2622_pb_checked.trans (by decide +kernel)
    · exact v2622_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 47 Primitive.Addresses.material2622
    · exact v2622_mb_checked.trans (by decide +kernel)
    · exact v2622_mg_checked.trans (by decide +kernel)
  upper_error := v2622_upper_checked
  lower_error := reuse_lower_error 32 47 Primitive.Addresses.material2622

def v2623_pa : Scalar.QComplex := ((999999637599607771869156944026 : Int)/10^30,(-851352249731107129238553561 : Int)/10^30)
theorem v2623_pa_checked : Scalar.distance (sourceCoefficient 32 48 1 0) v2623_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2623_pb : Scalar.QComplex := ((-367339354233593248283377 : Int)/10^30,(-431477359959627027695060526 : Int)/10^30)
theorem v2623_pb_checked : Scalar.distance (sourceCoefficient 32 48 1 1) v2623_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2623_pg : Scalar.QComplex := ((-93086395658300261709940 : Int)/10^30,(79249341083046183142 : Int)/10^30)
theorem v2623_pg_checked : Scalar.distance (sourceCoefficient 32 48 1 2) v2623_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2623_mb : Scalar.QComplex := ((-739684746082616543444314 : Int)/10^30,(-431476882303568071981770268 : Int)/10^30)
theorem v2623_mb_checked : Scalar.distance (sourceCoefficient 32 48 3 1) v2623_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2623_mg : Scalar.QComplex := ((-93086292609368802834982 : Int)/10^30,(159578678572378568591 : Int)/10^30)
theorem v2623_mg_checked : Scalar.distance (sourceCoefficient 32 48 3 2) v2623_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2623_upper : Scalar.QComplex := ((999996678860866813262695768671 : Int)/10^30,(-2577259636980397949931004135 : Int)/10^30)
theorem v2623_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 48 5) 1) 14) v2623_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2623 : Material (32 : Basis) (48 : Basis) where
  plus := ![v2623_pa,v2623_pb,v2623_pg]
  minus := ![(Primitive.Addresses.material2623 1).one,v2623_mb,v2623_mg]
  upper := v2623_upper
  lower := (Primitive.Addresses.material2623 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2623_pa_checked.trans (by decide +kernel)
    · exact v2623_pb_checked.trans (by decide +kernel)
    · exact v2623_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 48 Primitive.Addresses.material2623
    · exact v2623_mb_checked.trans (by decide +kernel)
    · exact v2623_mg_checked.trans (by decide +kernel)
  upper_error := v2623_upper_checked
  lower_error := reuse_lower_error 32 48 Primitive.Addresses.material2623

def v2624_pa : Scalar.QComplex := ((999999618594334820629608041965 : Int)/10^30,(-873390625601431191018542288 : Int)/10^30)
theorem v2624_pa_checked : Scalar.distance (sourceCoefficient 32 49 1 0) v2624_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2624_pb : Scalar.QComplex := ((-376848417181772018682440 : Int)/10^30,(-431477350916317489229613015 : Int)/10^30)
theorem v2624_pb_checked : Scalar.distance (sourceCoefficient 32 49 1 1) v2624_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2624_pg : Scalar.QComplex := ((-93086393798237517490017 : Int)/10^30,(81300814723015169045 : Int)/10^30)
theorem v2624_pg_checked : Scalar.distance (sourceCoefficient 32 49 1 2) v2624_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2624_mb : Scalar.QComplex := ((-749193797686167756437132 : Int)/10^30,(-431476865054368848772455743 : Int)/10^30)
theorem v2624_mb_checked : Scalar.distance (sourceCoefficient 32 49 3 1) v2624_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2624_mg : Scalar.QComplex := ((-93086288978977394851076 : Int)/10^30,(161630149843339787211 : Int)/10^30)
theorem v2624_mg_checked : Scalar.distance (sourceCoefficient 32 49 3 2) v2624_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2624_upper : Scalar.QComplex := ((999996621819384721806596561605 : Int)/10^30,(-2599297947225772993401373003 : Int)/10^30)
theorem v2624_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 49 5) 1) 14) v2624_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2624 : Material (32 : Basis) (49 : Basis) where
  plus := ![v2624_pa,v2624_pb,v2624_pg]
  minus := ![(Primitive.Addresses.material2624 1).one,v2624_mb,v2624_mg]
  upper := v2624_upper
  lower := (Primitive.Addresses.material2624 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2624_pa_checked.trans (by decide +kernel)
    · exact v2624_pb_checked.trans (by decide +kernel)
    · exact v2624_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 49 Primitive.Addresses.material2624
    · exact v2624_mb_checked.trans (by decide +kernel)
    · exact v2624_mg_checked.trans (by decide +kernel)
  upper_error := v2624_upper_checked
  lower_error := reuse_lower_error 32 49 Primitive.Addresses.material2624

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
