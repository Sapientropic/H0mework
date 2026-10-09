import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B024

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v577_pa : Scalar.QComplex := ((999999988843605222589384051897 : Int)/10^30,(149374661272774397768728539 : Int)/10^30)
theorem v577_pa_checked : Scalar.distance (sourceCoefficient 6 17 1 0) v577_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v577_pb : Scalar.QComplex := ((64451807710806121658290 : Int)/10^30,(-431477510593716377477356794 : Int)/10^30)
theorem v577_pb_checked : Scalar.distance (sourceCoefficient 6 17 1 1) v577_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v577_pg : Scalar.QComplex := ((-93086428255131754092918 : Int)/10^30,(-13904753844829644861 : Int)/10^30)
theorem v577_pg_checked : Scalar.distance (sourceCoefficient 6 17 1 2) v577_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v577_mb : Scalar.QComplex := ((-307893874904235397697562 : Int)/10^30,(-431477405553926939803180976 : Int)/10^30)
theorem v577_mb_checked : Scalar.distance (sourceCoefficient 6 17 3 1) v577_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v577_mg : Scalar.QComplex := ((-93086405593976575993590 : Int)/10^30,(66424646459627105826 : Int)/10^30)
theorem v577_mg_checked : Scalar.distance (sourceCoefficient 6 17 3 2) v577_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v577_upper : Scalar.QComplex := ((999998757268204283817328531365 : Int)/10^30,(-1576534822656971715952900086 : Int)/10^30)
theorem v577_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 17 5) 1) 14) v577_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material577 : Material (6 : Basis) (17 : Basis) where
  plus := ![v577_pa,v577_pb,v577_pg]
  minus := ![(Primitive.Addresses.material577 1).one,v577_mb,v577_mg]
  upper := v577_upper
  lower := (Primitive.Addresses.material577 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v577_pa_checked.trans (by decide +kernel)
    · exact v577_pb_checked.trans (by decide +kernel)
    · exact v577_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 17 Primitive.Addresses.material577
    · exact v577_mb_checked.trans (by decide +kernel)
    · exact v577_mg_checked.trans (by decide +kernel)
  upper_error := v577_upper_checked
  lower_error := reuse_lower_error 6 17 Primitive.Addresses.material577

def v578_pa : Scalar.QComplex := ((999999991928570329652041192595 : Int)/10^30,(127054552360582266117535071 : Int)/10^30)
theorem v578_pa_checked : Scalar.distance (sourceCoefficient 6 18 1 0) v578_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v578_pb : Scalar.QComplex := ((54821182455448206016498 : Int)/10^30,(-431477510993700947362925704 : Int)/10^30)
theorem v578_pb_checked : Scalar.distance (sourceCoefficient 6 18 1 1) v578_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v578_pg : Scalar.QComplex := ((-93086428441862038503737 : Int)/10^30,(-11827054591987394007 : Int)/10^30)
theorem v578_pg_checked : Scalar.distance (sourceCoefficient 6 18 1 2) v578_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v578_mb : Scalar.QComplex := ((-317524496918840058626963 : Int)/10^30,(-431477397643115512642379293 : Int)/10^30)
theorem v578_mb_checked : Scalar.distance (sourceCoefficient 6 18 3 1) v578_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v578_mg : Scalar.QComplex := ((-93086403987745911773968 : Int)/10^30,(68502345099986794727 : Int)/10^30)
theorem v578_mg_checked : Scalar.distance (sourceCoefficient 6 18 3 2) v578_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v578_upper : Scalar.QComplex := ((999998721830681678206365846059 : Int)/10^30,(-1598854903650353436007287750 : Int)/10^30)
theorem v578_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 18 5) 1) 14) v578_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material578 : Material (6 : Basis) (18 : Basis) where
  plus := ![v578_pa,v578_pb,v578_pg]
  minus := ![(Primitive.Addresses.material578 1).one,v578_mb,v578_mg]
  upper := v578_upper
  lower := (Primitive.Addresses.material578 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v578_pa_checked.trans (by decide +kernel)
    · exact v578_pb_checked.trans (by decide +kernel)
    · exact v578_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 18 Primitive.Addresses.material578
    · exact v578_mb_checked.trans (by decide +kernel)
    · exact v578_mg_checked.trans (by decide +kernel)
  upper_error := v578_upper_checked
  lower_error := reuse_lower_error 6 18 Primitive.Addresses.material578

def v579_pa : Scalar.QComplex := ((999999993794696834618646490146 : Int)/10^30,(111402900735379954671883527 : Int)/10^30)
theorem v579_pa_checked : Scalar.distance (sourceCoefficient 6 19 1 0) v579_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v579_pb : Scalar.QComplex := ((48067846637257153590951 : Int)/10^30,(-431477511103226937024850738 : Int)/10^30)
theorem v579_pb_checked : Scalar.distance (sourceCoefficient 6 19 1 1) v579_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v579_pg : Scalar.QComplex := ((-93086428540532067180965 : Int)/10^30,(-10370098222861536755 : Int)/10^30)
theorem v579_pg_checked : Scalar.distance (sourceCoefficient 6 19 1 2) v579_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v579_mb : Scalar.QComplex := ((-324277830316971539456615 : Int)/10^30,(-431477391924816809378234753 : Int)/10^30)
theorem v579_mb_checked : Scalar.distance (sourceCoefficient 6 19 3 1) v579_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v579_mg : Scalar.QComplex := ((-93086402829128176035198 : Int)/10^30,(69959301011769000373 : Int)/10^30)
theorem v579_mg_checked : Scalar.distance (sourceCoefficient 6 19 3 2) v579_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v579_upper : Scalar.QComplex := ((999998696683474605441298625073 : Int)/10^30,(-1614506535185024277764921979 : Int)/10^30)
theorem v579_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 19 5) 1) 14) v579_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material579 : Material (6 : Basis) (19 : Basis) where
  plus := ![v579_pa,v579_pb,v579_pg]
  minus := ![(Primitive.Addresses.material579 1).one,v579_mb,v579_mg]
  upper := v579_upper
  lower := (Primitive.Addresses.material579 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v579_pa_checked.trans (by decide +kernel)
    · exact v579_pb_checked.trans (by decide +kernel)
    · exact v579_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 19 Primitive.Addresses.material579
    · exact v579_mb_checked.trans (by decide +kernel)
    · exact v579_mg_checked.trans (by decide +kernel)
  upper_error := v579_upper_checked
  lower_error := reuse_lower_error 6 19 Primitive.Addresses.material579

def v580_pa : Scalar.QComplex := ((999999994103294992574890025022 : Int)/10^30,(108597467650397308909361480 : Int)/10^30)
theorem v580_pa_checked : Scalar.distance (sourceCoefficient 6 20 1 0) v580_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v580_pb : Scalar.QComplex := ((46857365330725121912762 : Int)/10^30,(-431477511107963955115075034 : Int)/10^30)
theorem v580_pb_checked : Scalar.distance (sourceCoefficient 6 20 1 1) v580_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v580_pg : Scalar.QComplex := ((-93086428555406196891014 : Int)/10^30,(-10108950473346243643 : Int)/10^30)
theorem v580_pg_checked : Scalar.distance (sourceCoefficient 6 20 1 2) v580_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v580_mb : Scalar.QComplex := ((-325488311176873892248760 : Int)/10^30,(-431477390884962976221748283 : Int)/10^30)
theorem v580_mb_checked : Scalar.distance (sourceCoefficient 6 20 3 1) v580_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v580_mg : Scalar.QComplex := ((-93086402618643554033255 : Int)/10^30,(70220448676882755333 : Int)/10^30)
theorem v580_mg_checked : Scalar.distance (sourceCoefficient 6 20 3 2) v580_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v580_upper : Scalar.QComplex := ((999998692150149305998160599882 : Int)/10^30,(-1617311964624256317591810112 : Int)/10^30)
theorem v580_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 20 5) 1) 14) v580_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material580 : Material (6 : Basis) (20 : Basis) where
  plus := ![v580_pa,v580_pb,v580_pg]
  minus := ![(Primitive.Addresses.material580 1).one,v580_mb,v580_mg]
  upper := v580_upper
  lower := (Primitive.Addresses.material580 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v580_pa_checked.trans (by decide +kernel)
    · exact v580_pb_checked.trans (by decide +kernel)
    · exact v580_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 20 Primitive.Addresses.material580
    · exact v580_mb_checked.trans (by decide +kernel)
    · exact v580_mg_checked.trans (by decide +kernel)
  upper_error := v580_upper_checked
  lower_error := reuse_lower_error 6 20 Primitive.Addresses.material580

def v581_pa : Scalar.QComplex := ((999999998454951264315815566260 : Int)/10^30,(55588645144320555493047023 : Int)/10^30)
theorem v581_pa_checked : Scalar.distance (sourceCoefficient 6 21 1 0) v581_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v581_pb : Scalar.QComplex := ((23985250247459874283544 : Int)/10^30,(-431477510346410129940870712 : Int)/10^30)
theorem v581_pb_checked : Scalar.distance (sourceCoefficient 6 21 1 1) v581_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v581_pg : Scalar.QComplex := ((-93086428675797928662694 : Int)/10^30,(-5174548459405965798 : Int)/10^30)
theorem v581_pg_checked : Scalar.distance (sourceCoefficient 6 21 1 2) v581_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v581_mb : Scalar.QComplex := ((-348360417086618735065497 : Int)/10^30,(-431477370385804239574359797 : Int)/10^30)
theorem v581_mb_checked : Scalar.distance (sourceCoefficient 6 21 3 1) v581_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v581_mg : Scalar.QComplex := ((-93086398480868540164006 : Int)/10^30,(75154848957412292352 : Int)/10^30)
theorem v581_mg_checked : Scalar.distance (sourceCoefficient 6 21 3 2) v581_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v581_upper : Scalar.QComplex := ((999998605013380373782282232557 : Int)/10^30,(-1670320715690482747762690526 : Int)/10^30)
theorem v581_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 21 5) 1) 14) v581_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material581 : Material (6 : Basis) (21 : Basis) where
  plus := ![v581_pa,v581_pb,v581_pg]
  minus := ![(Primitive.Addresses.material581 1).one,v581_mb,v581_mg]
  upper := v581_upper
  lower := (Primitive.Addresses.material581 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v581_pa_checked.trans (by decide +kernel)
    · exact v581_pb_checked.trans (by decide +kernel)
    · exact v581_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 21 Primitive.Addresses.material581
    · exact v581_mb_checked.trans (by decide +kernel)
    · exact v581_mg_checked.trans (by decide +kernel)
  upper_error := v581_upper_checked
  lower_error := reuse_lower_error 6 21 Primitive.Addresses.material581

def v582_pa : Scalar.QComplex := ((999999998531475533413712772010 : Int)/10^30,(54194547059792005858462831 : Int)/10^30)
theorem v582_pa_checked : Scalar.distance (sourceCoefficient 6 22 1 0) v582_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v582_pb : Scalar.QComplex := ((23383728271782235912473 : Int)/10^30,(-431477510304565383698657708 : Int)/10^30)
theorem v582_pb_checked : Scalar.distance (sourceCoefficient 6 22 1 1) v582_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v582_pg : Scalar.QComplex := ((-93086428674845847151781 : Int)/10^30,(-5044776846855283498 : Int)/10^30)
theorem v582_pg_checked : Scalar.distance (sourceCoefficient 6 22 1 2) v582_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v582_mb : Scalar.QComplex := ((-348961938802212119589797 : Int)/10^30,(-431477369824873135447155435 : Int)/10^30)
theorem v582_mb_checked : Scalar.distance (sourceCoefficient 6 22 3 1) v582_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v582_mg : Scalar.QComplex := ((-93086398367929402072822 : Int)/10^30,(75284620520821468980 : Int)/10^30)
theorem v582_mg_checked : Scalar.distance (sourceCoefficient 6 22 3 2) v582_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v582_upper : Scalar.QComplex := ((999998602683817706600279703164 : Int)/10^30,(-1671714811830739908992188148 : Int)/10^30)
theorem v582_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 22 5) 1) 14) v582_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material582 : Material (6 : Basis) (22 : Basis) where
  plus := ![v582_pa,v582_pb,v582_pg]
  minus := ![(Primitive.Addresses.material582 1).one,v582_mb,v582_mg]
  upper := v582_upper
  lower := (Primitive.Addresses.material582 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v582_pa_checked.trans (by decide +kernel)
    · exact v582_pb_checked.trans (by decide +kernel)
    · exact v582_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 22 Primitive.Addresses.material582
    · exact v582_mb_checked.trans (by decide +kernel)
    · exact v582_mg_checked.trans (by decide +kernel)
  upper_error := v582_upper_checked
  lower_error := reuse_lower_error 6 22 Primitive.Addresses.material582

def v583_pa : Scalar.QComplex := ((999999999037018271682539278432 : Int)/10^30,(43885800160274936407391101 : Int)/10^30)
theorem v583_pa_checked : Scalar.distance (sourceCoefficient 6 23 1 0) v583_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v583_pb : Scalar.QComplex := ((18935735794011630608781 : Int)/10^30,(-431477509960438970162835912 : Int)/10^30)
theorem v583_pb_checked : Scalar.distance (sourceCoefficient 6 23 1 1) v583_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v583_pg : Scalar.QComplex := ((-93086428661254727074921 : Int)/10^30,(-4085172409795460523 : Int)/10^30)
theorem v583_pg_checked : Scalar.distance (sourceCoefficient 6 23 1 2) v583_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v583_mb : Scalar.QComplex := ((-353409929326826246117766 : Int)/10^30,(-431477365642329671873886636 : Int)/10^30)
theorem v583_mb_checked : Scalar.distance (sourceCoefficient 6 23 3 1) v583_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v583_mg : Scalar.QComplex := ((-93086397526242876853412 : Int)/10^30,(76244224588848179443 : Int)/10^30)
theorem v583_mg_checked : Scalar.distance (sourceCoefficient 6 23 3 2) v583_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v583_upper : Scalar.QComplex := ((999998585397397745569446313814 : Int)/10^30,(-1682023544249110325861070382 : Int)/10^30)
theorem v583_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 23 5) 1) 14) v583_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material583 : Material (6 : Basis) (23 : Basis) where
  plus := ![v583_pa,v583_pb,v583_pg]
  minus := ![(Primitive.Addresses.material583 1).one,v583_mb,v583_mg]
  upper := v583_upper
  lower := (Primitive.Addresses.material583 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v583_pa_checked.trans (by decide +kernel)
    · exact v583_pb_checked.trans (by decide +kernel)
    · exact v583_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 23 Primitive.Addresses.material583
    · exact v583_mb_checked.trans (by decide +kernel)
    · exact v583_mg_checked.trans (by decide +kernel)
  upper_error := v583_upper_checked
  lower_error := reuse_lower_error 6 23 Primitive.Addresses.material583

def v584_pa : Scalar.QComplex := ((999999999975076956092983397999 : Int)/10^30,(-7060176188553090626339268 : Int)/10^30)
theorem v584_pa_checked : Scalar.distance (sourceCoefficient 6 24 1 0) v584_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v584_pb : Scalar.QComplex := ((-3046307223450005664407 : Int)/10^30,(-431477507362091945987069442 : Int)/10^30)
theorem v584_pb_checked : Scalar.distance (sourceCoefficient 6 24 1 1) v584_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v584_pg : Scalar.QComplex := ((-93086428424632899034454 : Int)/10^30,(657206585457424366 : Int)/10^30)
theorem v584_pg_checked : Scalar.distance (sourceCoefficient 6 24 1 2) v584_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v584_mb : Scalar.QComplex := ((-375391961917112181336512 : Int)/10^30,(-431477344074470525577775059 : Int)/10^30)
theorem v584_mb_checked : Scalar.distance (sourceCoefficient 6 24 3 1) v584_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v584_mg : Scalar.QComplex := ((-93086393197161652835982 : Int)/10^30,(80986601614102646425 : Int)/10^30)
theorem v584_mg_checked : Scalar.distance (sourceCoefficient 6 24 3 2) v584_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v584_upper : Scalar.QComplex := ((999998498407321637645476643742 : Int)/10^30,(-1732969446338895305361368571 : Int)/10^30)
theorem v584_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 24 5) 1) 14) v584_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material584 : Material (6 : Basis) (24 : Basis) where
  plus := ![v584_pa,v584_pb,v584_pg]
  minus := ![(Primitive.Addresses.material584 1).one,v584_mb,v584_mg]
  upper := v584_upper
  lower := (Primitive.Addresses.material584 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v584_pa_checked.trans (by decide +kernel)
    · exact v584_pb_checked.trans (by decide +kernel)
    · exact v584_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 24 Primitive.Addresses.material584
    · exact v584_mb_checked.trans (by decide +kernel)
    · exact v584_mg_checked.trans (by decide +kernel)
  upper_error := v584_upper_checked
  lower_error := reuse_lower_error 6 24 Primitive.Addresses.material584

def v585_pa : Scalar.QComplex := ((999999999548663550241149972033 : Int)/10^30,(-30044515295041713570725060 : Int)/10^30)
theorem v585_pa_checked : Scalar.distance (sourceCoefficient 6 25 1 0) v585_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v585_pb : Scalar.QComplex := ((-12963532525352723836752 : Int)/10^30,(-431477505701055465237640832 : Int)/10^30)
theorem v585_pb_checked : Scalar.distance (sourceCoefficient 6 25 1 1) v585_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v585_pg : Scalar.QComplex := ((-93086428225611264560384 : Int)/10^30,(2796736617847449492 : Int)/10^30)
theorem v585_pg_checked : Scalar.distance (sourceCoefficient 6 25 1 2) v585_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v585_mb : Scalar.QComplex := ((-385309182092979007442935 : Int)/10^30,(-431477333855315883013071119 : Int)/10^30)
theorem v585_mb_checked : Scalar.distance (sourceCoefficient 6 25 3 1) v585_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v585_mg : Scalar.QComplex := ((-93086391151822035369746 : Int)/10^30,(83126130678101152190 : Int)/10^30)
theorem v585_mg_checked : Scalar.distance (sourceCoefficient 6 25 3 2) v585_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v585_upper : Scalar.QComplex := ((999998458312024692042611977084 : Int)/10^30,(-1755953750476959904743878203 : Int)/10^30)
theorem v585_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 25 5) 1) 14) v585_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material585 : Material (6 : Basis) (25 : Basis) where
  plus := ![v585_pa,v585_pb,v585_pg]
  minus := ![(Primitive.Addresses.material585 1).one,v585_mb,v585_mg]
  upper := v585_upper
  lower := (Primitive.Addresses.material585 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v585_pa_checked.trans (by decide +kernel)
    · exact v585_pb_checked.trans (by decide +kernel)
    · exact v585_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 25 Primitive.Addresses.material585
    · exact v585_mb_checked.trans (by decide +kernel)
    · exact v585_mg_checked.trans (by decide +kernel)
  upper_error := v585_upper_checked
  lower_error := reuse_lower_error 6 25 Primitive.Addresses.material585

def v586_pa : Scalar.QComplex := ((999999999301052046594812104697 : Int)/10^30,(-37388446160837542207136042 : Int)/10^30)
theorem v586_pa_checked : Scalar.distance (sourceCoefficient 6 26 1 0) v586_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v586_pb : Scalar.QComplex := ((-16132273480553326097147 : Int)/10^30,(-431477505106254620081946957 : Int)/10^30)
theorem v586_pb_checked : Scalar.distance (sourceCoefficient 6 26 1 1) v586_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v586_pg : Scalar.QComplex := ((-93086428149925827712475 : Int)/10^30,(3480356909620762369 : Int)/10^30)
theorem v586_pg_checked : Scalar.distance (sourceCoefficient 6 26 1 2) v586_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v586_mb : Scalar.QComplex := ((-388477921355026192932562 : Int)/10^30,(-431477330526034529785595912 : Int)/10^30)
theorem v586_mb_checked : Scalar.distance (sourceCoefficient 6 26 3 1) v586_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v586_mg : Scalar.QComplex := ((-93086390486203104017611 : Int)/10^30,(83809750650018264195 : Int)/10^30)
theorem v586_mg_checked : Scalar.distance (sourceCoefficient 6 26 3 2) v586_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v586_upper : Scalar.QComplex := ((999998445389455119024715454074 : Int)/10^30,(-1763297669977478395343332853 : Int)/10^30)
theorem v586_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 26 5) 1) 14) v586_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material586 : Material (6 : Basis) (26 : Basis) where
  plus := ![v586_pa,v586_pb,v586_pg]
  minus := ![(Primitive.Addresses.material586 1).one,v586_mb,v586_mg]
  upper := v586_upper
  lower := (Primitive.Addresses.material586 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v586_pa_checked.trans (by decide +kernel)
    · exact v586_pb_checked.trans (by decide +kernel)
    · exact v586_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 26 Primitive.Addresses.material586
    · exact v586_mb_checked.trans (by decide +kernel)
    · exact v586_mg_checked.trans (by decide +kernel)
  upper_error := v586_upper_checked
  lower_error := reuse_lower_error 6 26 Primitive.Addresses.material586

def v587_pa : Scalar.QComplex := ((999999999099691415818940136299 : Int)/10^30,(-42433679637188714825336436 : Int)/10^30)
theorem v587_pa_checked : Scalar.distance (sourceCoefficient 6 27 1 0) v587_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v587_pb : Scalar.QComplex := ((-18309178220713782611764 : Int)/10^30,(-431477504679650228006042680 : Int)/10^30)
theorem v587_pb_checked : Scalar.distance (sourceCoefficient 6 27 1 1) v587_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v587_pg : Scalar.QComplex := ((-93086428094536303138455 : Int)/10^30,(3949999671889975239 : Int)/10^30)
theorem v587_pg_checked : Scalar.distance (sourceCoefficient 6 27 1 2) v587_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v587_mb : Scalar.QComplex := ((-390654824916485148411010 : Int)/10^30,(-431477328220859549945456519 : Int)/10^30)
theorem v587_mb_checked : Scalar.distance (sourceCoefficient 6 27 3 1) v587_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v587_mg : Scalar.QComplex := ((-93086390025533048154128 : Int)/10^30,(84279393189619347881 : Int)/10^30)
theorem v587_mg_checked : Scalar.distance (sourceCoefficient 6 27 3 2) v587_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v587_upper : Scalar.QComplex := ((999998436480479507975343950354 : Int)/10^30,(-1768342895592016778266892485 : Int)/10^30)
theorem v587_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 27 5) 1) 14) v587_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material587 : Material (6 : Basis) (27 : Basis) where
  plus := ![v587_pa,v587_pb,v587_pg]
  minus := ![(Primitive.Addresses.material587 1).one,v587_mb,v587_mg]
  upper := v587_upper
  lower := (Primitive.Addresses.material587 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v587_pa_checked.trans (by decide +kernel)
    · exact v587_pb_checked.trans (by decide +kernel)
    · exact v587_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 27 Primitive.Addresses.material587
    · exact v587_mb_checked.trans (by decide +kernel)
    · exact v587_mg_checked.trans (by decide +kernel)
  upper_error := v587_upper_checked
  lower_error := reuse_lower_error 6 27 Primitive.Addresses.material587

def v588_pa : Scalar.QComplex := ((999999998788190543523231850947 : Int)/10^30,(-49230264182564104327866896 : Int)/10^30)
theorem v588_pa_checked : Scalar.distance (sourceCoefficient 6 28 1 0) v588_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v588_pb : Scalar.QComplex := ((-21241751540521714876706 : Int)/10^30,(-431477504081807390215361375 : Int)/10^30)
theorem v588_pb_checked : Scalar.distance (sourceCoefficient 6 28 1 1) v588_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v588_pg : Scalar.QComplex := ((-93086428015549111772341 : Int)/10^30,(4582669448570041407 : Int)/10^30)
theorem v588_pg_checked : Scalar.distance (sourceCoefficient 6 28 1 2) v588_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v588_mb : Scalar.QComplex := ((-393587396628450565318285 : Int)/10^30,(-431477325092338237964091869 : Int)/10^30)
theorem v588_mb_checked : Scalar.distance (sourceCoefficient 6 28 3 1) v588_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v588_mg : Scalar.QComplex := ((-93086389400580363312639 : Int)/10^30,(84912062662565153056 : Int)/10^30)
theorem v588_mg_checked : Scalar.distance (sourceCoefficient 6 28 3 2) v588_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v588_upper : Scalar.QComplex := ((999998424438690755639158603428 : Int)/10^30,(-1775139469477055623892814106 : Int)/10^30)
theorem v588_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 28 5) 1) 14) v588_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material588 : Material (6 : Basis) (28 : Basis) where
  plus := ![v588_pa,v588_pb,v588_pg]
  minus := ![(Primitive.Addresses.material588 1).one,v588_mb,v588_mg]
  upper := v588_upper
  lower := (Primitive.Addresses.material588 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v588_pa_checked.trans (by decide +kernel)
    · exact v588_pb_checked.trans (by decide +kernel)
    · exact v588_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 28 Primitive.Addresses.material588
    · exact v588_mb_checked.trans (by decide +kernel)
    · exact v588_mg_checked.trans (by decide +kernel)
  upper_error := v588_upper_checked
  lower_error := reuse_lower_error 6 28 Primitive.Addresses.material588

def v589_pa : Scalar.QComplex := ((999999998015775845357276107758 : Int)/10^30,(-62995621318852807141535551 : Int)/10^30)
theorem v589_pa_checked : Scalar.distance (sourceCoefficient 6 29 1 0) v589_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v589_pb : Scalar.QComplex := ((-27181193427268833876569 : Int)/10^30,(-431477502789558028855621260 : Int)/10^30)
theorem v589_pb_checked : Scalar.distance (sourceCoefficient 6 29 1 1) v589_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v589_pg : Scalar.QComplex := ((-93086427840204304373601 : Int)/10^30,(5864037369781792337 : Int)/10^30)
theorem v589_pg_checked : Scalar.distance (sourceCoefficient 6 29 1 2) v589_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v589_mb : Scalar.QComplex := ((-399526835188519025875538 : Int)/10^30,(-431477318674618512037502320 : Int)/10^30)
theorem v589_mb_checked : Scalar.distance (sourceCoefficient 6 29 3 1) v589_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v589_mg : Scalar.QComplex := ((-93086388119472815865894 : Int)/10^30,(86193429955350393965 : Int)/10^30)
theorem v589_mg_checked : Scalar.distance (sourceCoefficient 6 29 3 2) v589_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v589_upper : Scalar.QComplex := ((999998399908519574104303697552 : Int)/10^30,(-1788904804778344168520810279 : Int)/10^30)
theorem v589_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 29 5) 1) 14) v589_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material589 : Material (6 : Basis) (29 : Basis) where
  plus := ![v589_pa,v589_pb,v589_pg]
  minus := ![(Primitive.Addresses.material589 1).one,v589_mb,v589_mg]
  upper := v589_upper
  lower := (Primitive.Addresses.material589 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v589_pa_checked.trans (by decide +kernel)
    · exact v589_pb_checked.trans (by decide +kernel)
    · exact v589_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 29 Primitive.Addresses.material589
    · exact v589_mb_checked.trans (by decide +kernel)
    · exact v589_mg_checked.trans (by decide +kernel)
  upper_error := v589_upper_checked
  lower_error := reuse_lower_error 6 29 Primitive.Addresses.material589

def v590_pa : Scalar.QComplex := ((999999997673567055901789114944 : Int)/10^30,(-68211918920260053967747394 : Int)/10^30)
theorem v590_pa_checked : Scalar.distance (sourceCoefficient 6 30 1 0) v590_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v590_pb : Scalar.QComplex := ((-29431908469323502994968 : Int)/10^30,(-431477502271386533920886973 : Int)/10^30)
theorem v590_pb_checked : Scalar.distance (sourceCoefficient 6 30 1 1) v590_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v590_pg : Scalar.QComplex := ((-93086427768381966552372 : Int)/10^30,(6349603878285442381 : Int)/10^30)
theorem v590_pg_checked : Scalar.distance (sourceCoefficient 6 30 1 2) v590_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v590_mb : Scalar.QComplex := ((-401777548945370959527163 : Int)/10^30,(-431477316214181497191038431 : Int)/10^30)
theorem v590_mb_checked : Scalar.distance (sourceCoefficient 6 30 3 1) v590_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v590_mg : Scalar.QComplex := ((-93086387628628477052477 : Int)/10^30,(86678996221075998625 : Int)/10^30)
theorem v590_mg_checked : Scalar.distance (sourceCoefficient 6 30 3 2) v590_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v590_upper : Scalar.QComplex := ((999998390563454853121519000334 : Int)/10^30,(-1794121094020067561749183231 : Int)/10^30)
theorem v590_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 30 5) 1) 14) v590_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material590 : Material (6 : Basis) (30 : Basis) where
  plus := ![v590_pa,v590_pb,v590_pg]
  minus := ![(Primitive.Addresses.material590 1).one,v590_mb,v590_mg]
  upper := v590_upper
  lower := (Primitive.Addresses.material590 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v590_pa_checked.trans (by decide +kernel)
    · exact v590_pb_checked.trans (by decide +kernel)
    · exact v590_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 30 Primitive.Addresses.material590
    · exact v590_mb_checked.trans (by decide +kernel)
    · exact v590_mg_checked.trans (by decide +kernel)
  upper_error := v590_upper_checked
  lower_error := reuse_lower_error 6 30 Primitive.Addresses.material590

def v591_pa : Scalar.QComplex := ((999999996855200792221518093363 : Int)/10^30,(-79306988378497904956179999 : Int)/10^30)
theorem v591_pa_checked : Scalar.distance (sourceCoefficient 6 31 1 0) v591_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v591_pb : Scalar.QComplex := ((-34219181274295754658202 : Int)/10^30,(-431477501117177344919329824 : Int)/10^30)
theorem v591_pb_checked : Scalar.distance (sourceCoefficient 6 31 1 1) v591_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v591_pg : Scalar.QComplex := ((-93086427605788734022221 : Int)/10^30,(7382404255544352743 : Int)/10^30)
theorem v591_pg_checked : Scalar.distance (sourceCoefficient 6 31 1 2) v591_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v591_mb : Scalar.QComplex := ((-406564818971792210267441 : Int)/10^30,(-431477310928771918026547321 : Int)/10^30)
theorem v591_mb_checked : Scalar.distance (sourceCoefficient 6 31 3 1) v591_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v591_mg : Scalar.QComplex := ((-93086386574775095091030 : Int)/10^30,(87711796073465490478 : Int)/10^30)
theorem v591_mg_checked : Scalar.distance (sourceCoefficient 6 31 3 2) v591_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v591_upper : Scalar.QComplex := ((999998370596006460221751913527 : Int)/10^30,(-1805216145541076843599376064 : Int)/10^30)
theorem v591_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 31 5) 1) 14) v591_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material591 : Material (6 : Basis) (31 : Basis) where
  plus := ![v591_pa,v591_pb,v591_pg]
  minus := ![(Primitive.Addresses.material591 1).one,v591_mb,v591_mg]
  upper := v591_upper
  lower := (Primitive.Addresses.material591 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v591_pa_checked.trans (by decide +kernel)
    · exact v591_pb_checked.trans (by decide +kernel)
    · exact v591_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 31 Primitive.Addresses.material591
    · exact v591_mb_checked.trans (by decide +kernel)
    · exact v591_mg_checked.trans (by decide +kernel)
  upper_error := v591_upper_checked
  lower_error := reuse_lower_error 6 31 Primitive.Addresses.material591

def v592_pa : Scalar.QComplex := ((999999996465017954664136760505 : Int)/10^30,(-84083078429465392749429832 : Int)/10^30)
theorem v592_pa_checked : Scalar.distance (sourceCoefficient 6 32 1 0) v592_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v592_pb : Scalar.QComplex := ((-36279956651624119618172 : Int)/10^30,(-431477500598520786691839178 : Int)/10^30)
theorem v592_pb_checked : Scalar.distance (sourceCoefficient 6 32 1 1) v592_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v592_pg : Scalar.QComplex := ((-93086427531681206266116 : Int)/10^30,(7826993414533378686 : Int)/10^30)
theorem v592_pg_checked : Scalar.distance (sourceCoefficient 6 32 1 2) v592_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v592_mb : Scalar.QComplex := ((-408625593134222469834543 : Int)/10^30,(-431477308631759216161799899 : Int)/10^30)
theorem v592_mb_checked : Scalar.distance (sourceCoefficient 6 32 3 1) v592_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v592_mg : Scalar.QComplex := ((-93086386117007174273426 : Int)/10^30,(88156385002962195027 : Int)/10^30)
theorem v592_mg_checked : Scalar.distance (sourceCoefficient 6 32 3 2) v592_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v592_upper : Scalar.QComplex := ((999998361962726059330787869250 : Int)/10^30,(-1809992227805199058911252029 : Int)/10^30)
theorem v592_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 6 32 5) 1) 14) v592_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material592 : Material (6 : Basis) (32 : Basis) where
  plus := ![v592_pa,v592_pb,v592_pg]
  minus := ![(Primitive.Addresses.material592 1).one,v592_mb,v592_mg]
  upper := v592_upper
  lower := (Primitive.Addresses.material592 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v592_pa_checked.trans (by decide +kernel)
    · exact v592_pb_checked.trans (by decide +kernel)
    · exact v592_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 6 32 Primitive.Addresses.material592
    · exact v592_mb_checked.trans (by decide +kernel)
    · exact v592_mg_checked.trans (by decide +kernel)
  upper_error := v592_upper_checked
  lower_error := reuse_lower_error 6 32 Primitive.Addresses.material592

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
