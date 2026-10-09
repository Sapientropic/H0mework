import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B064

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1537_pa : Scalar.QComplex := ((999999850988482645542068630518 : Int)/10^30,(-545914839974591237032868181 : Int)/10^30)
theorem v1537_pa_checked : Scalar.distance (sourceCoefficient 17 42 1 0) v1537_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1537_pb : Scalar.QComplex := ((-235549975022630388185694 : Int)/10^30,(-431477444236420657414517008 : Int)/10^30)
theorem v1537_pb_checked : Scalar.distance (sourceCoefficient 17 42 1 1) v1537_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1537_pg : Scalar.QComplex := ((-93086414680990458485965 : Int)/10^30,(50817262746738776232 : Int)/10^30)
theorem v1537_pg_checked : Scalar.distance (sourceCoefficient 17 42 1 2) v1537_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1537_mb : Scalar.QComplex := ((-607895488669939852329139 : Int)/10^30,(-431477080308629007359443202 : Int)/10^30)
theorem v1537_mb_checked : Scalar.distance (sourceCoefficient 17 42 3 1) v1537_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1537_mg : Scalar.QComplex := ((-93086336167654987554722 : Int)/10^30,(131146627238358226115 : Int)/10^30)
theorem v1537_mg_checked : Scalar.distance (sourceCoefficient 17 42 3 2) v1537_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1537_upper : Scalar.QComplex := ((999997419406684043657560111961 : Int)/10^30,(-2271823050426864235980620093 : Int)/10^30)
theorem v1537_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 42 5) 1) 14) v1537_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1537 : Material (17 : Basis) (42 : Basis) where
  plus := ![v1537_pa,v1537_pb,v1537_pg]
  minus := ![(Primitive.Addresses.material1537 1).one,v1537_mb,v1537_mg]
  upper := v1537_upper
  lower := (Primitive.Addresses.material1537 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1537_pa_checked.trans (by decide +kernel)
    · exact v1537_pb_checked.trans (by decide +kernel)
    · exact v1537_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 42 Primitive.Addresses.material1537
    · exact v1537_mb_checked.trans (by decide +kernel)
    · exact v1537_mg_checked.trans (by decide +kernel)
  upper_error := v1537_upper_checked
  lower_error := reuse_lower_error 17 42 Primitive.Addresses.material1537

def v1538_pa : Scalar.QComplex := ((999999842419147265026772780239 : Int)/10^30,(-561392626098901753073990367 : Int)/10^30)
theorem v1538_pa_checked : Scalar.distance (sourceCoefficient 17 43 1 0) v1538_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1538_pb : Scalar.QComplex := ((-242228291087072961962636 : Int)/10^30,(-431477439594759516379122411 : Int)/10^30)
theorem v1538_pb_checked : Scalar.distance (sourceCoefficient 17 43 1 1) v1538_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1538_pg : Scalar.QComplex := ((-93086413781452906323465 : Int)/10^30,(52258034521764488880 : Int)/10^30)
theorem v1538_pg_checked : Scalar.distance (sourceCoefficient 17 43 1 2) v1538_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1538_mb : Scalar.QComplex := ((-614573798242195629135930 : Int)/10^30,(-431477069903883611202741638 : Int)/10^30)
theorem v1538_mb_checked : Scalar.distance (sourceCoefficient 17 43 3 1) v1538_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1538_mg : Scalar.QComplex := ((-93086334024796618435892 : Int)/10^30,(132587397700658366550 : Int)/10^30)
theorem v1538_mg_checked : Scalar.distance (sourceCoefficient 17 43 3 2) v1538_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1538_upper : Scalar.QComplex := ((999997384124106709389444232698 : Int)/10^30,(-2287300798708935005600927336 : Int)/10^30)
theorem v1538_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 43 5) 1) 14) v1538_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1538 : Material (17 : Basis) (43 : Basis) where
  plus := ![v1538_pa,v1538_pb,v1538_pg]
  minus := ![(Primitive.Addresses.material1538 1).one,v1538_mb,v1538_mg]
  upper := v1538_upper
  lower := (Primitive.Addresses.material1538 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1538_pa_checked.trans (by decide +kernel)
    · exact v1538_pb_checked.trans (by decide +kernel)
    · exact v1538_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 43 Primitive.Addresses.material1538
    · exact v1538_mb_checked.trans (by decide +kernel)
    · exact v1538_mg_checked.trans (by decide +kernel)
  upper_error := v1538_upper_checked
  lower_error := reuse_lower_error 17 43 Primitive.Addresses.material1538

def v1539_pa : Scalar.QComplex := ((999999839114610801890464709481 : Int)/10^30,(-567248404591948247071185228 : Int)/10^30)
theorem v1539_pa_checked : Scalar.distance (sourceCoefficient 17 44 1 0) v1539_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1539_pb : Scalar.QComplex := ((-244754927588508990829424 : Int)/10^30,(-431477437802724773534927361 : Int)/10^30)
theorem v1539_pb_checked : Scalar.distance (sourceCoefficient 17 44 1 1) v1539_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1539_pg : Scalar.QComplex := ((-93086413434343469438922 : Int)/10^30,(52803128005069631059 : Int)/10^30)
theorem v1539_pg_checked : Scalar.distance (sourceCoefficient 17 44 1 2) v1539_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1539_mb : Scalar.QComplex := ((-617100432256404142699659 : Int)/10^30,(-431477065931476030359426229 : Int)/10^30)
theorem v1539_mb_checked : Scalar.distance (sourceCoefficient 17 44 3 1) v1539_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1539_mg : Scalar.QComplex := ((-93086333207296184802864 : Int)/10^30,(133132490681460482089 : Int)/10^30)
theorem v1539_mg_checked : Scalar.distance (sourceCoefficient 17 44 3 2) v1539_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1539_upper : Scalar.QComplex := ((999997370713032721048903182333 : Int)/10^30,(-2293156562777157152100133006 : Int)/10^30)
theorem v1539_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 44 5) 1) 14) v1539_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1539 : Material (17 : Basis) (44 : Basis) where
  plus := ![v1539_pa,v1539_pb,v1539_pg]
  minus := ![(Primitive.Addresses.material1539 1).one,v1539_mb,v1539_mg]
  upper := v1539_upper
  lower := (Primitive.Addresses.material1539 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1539_pa_checked.trans (by decide +kernel)
    · exact v1539_pb_checked.trans (by decide +kernel)
    · exact v1539_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 44 Primitive.Addresses.material1539
    · exact v1539_mb_checked.trans (by decide +kernel)
    · exact v1539_mg_checked.trans (by decide +kernel)
  upper_error := v1539_upper_checked
  lower_error := reuse_lower_error 17 44 Primitive.Addresses.material1539

def v1540_pa : Scalar.QComplex := ((999999837457789001453242634933 : Int)/10^30,(-570161727562560233999682042 : Int)/10^30)
theorem v1540_pa_checked : Scalar.distance (sourceCoefficient 17 45 1 0) v1540_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1540_pb : Scalar.QComplex := ((-246011960816673578286690 : Int)/10^30,(-431477436903816392408469128 : Int)/10^30)
theorem v1540_pb_checked : Scalar.distance (sourceCoefficient 17 45 1 1) v1540_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1540_pg : Scalar.QComplex := ((-93086413260264961820142 : Int)/10^30,(53074318823892214412 : Int)/10^30)
theorem v1540_pg_checked : Scalar.distance (sourceCoefficient 17 45 1 2) v1540_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1540_mb : Scalar.QComplex := ((-618357464240800362473138 : Int)/10^30,(-431477063947804922706562466 : Int)/10^30)
theorem v1540_mb_checked : Scalar.distance (sourceCoefficient 17 45 3 1) v1540_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1540_mg : Scalar.QComplex := ((-93086332799192279338655 : Int)/10^30,(133403681249084417691 : Int)/10^30)
theorem v1540_mg_checked : Scalar.distance (sourceCoefficient 17 45 3 2) v1540_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1540_upper : Scalar.QComplex := ((999997364028082235572177300366 : Int)/10^30,(-2296069878549192675403021535 : Int)/10^30)
theorem v1540_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 45 5) 1) 14) v1540_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1540 : Material (17 : Basis) (45 : Basis) where
  plus := ![v1540_pa,v1540_pb,v1540_pg]
  minus := ![(Primitive.Addresses.material1540 1).one,v1540_mb,v1540_mg]
  upper := v1540_upper
  lower := (Primitive.Addresses.material1540 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1540_pa_checked.trans (by decide +kernel)
    · exact v1540_pb_checked.trans (by decide +kernel)
    · exact v1540_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 45 Primitive.Addresses.material1540
    · exact v1540_mb_checked.trans (by decide +kernel)
    · exact v1540_mg_checked.trans (by decide +kernel)
  upper_error := v1540_upper_checked
  lower_error := reuse_lower_error 17 45 Primitive.Addresses.material1540

def v1541_pa : Scalar.QComplex := ((999999827993629601170971394748 : Int)/10^30,(-586525968062341293836329538 : Int)/10^30)
theorem v1541_pa_checked : Scalar.distance (sourceCoefficient 17 46 1 0) v1541_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1541_pb : Scalar.QComplex := ((-253072761892485113691694 : Int)/10^30,(-431477431763872102591882993 : Int)/10^30)
theorem v1541_pb_checked : Scalar.distance (sourceCoefficient 17 46 1 1) v1541_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1541_pg : Scalar.QComplex := ((-93086412265329925972918 : Int)/10^30,(54597607458509126448 : Int)/10^30)
theorem v1541_pg_checked : Scalar.distance (sourceCoefficient 17 46 1 2) v1541_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1541_mb : Scalar.QComplex := ((-625418258252012535188528 : Int)/10^30,(-431477052714709224976279294 : Int)/10^30)
theorem v1541_mb_checked : Scalar.distance (sourceCoefficient 17 46 3 1) v1541_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1541_mg : Scalar.QComplex := ((-93086330489728128650135 : Int)/10^30,(134926968457927227604 : Int)/10^30)
theorem v1541_mg_checked : Scalar.distance (sourceCoefficient 17 46 3 2) v1541_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1541_upper : Scalar.QComplex := ((999997326320742380722939210331 : Int)/10^30,(-2312434078342079246484320234 : Int)/10^30)
theorem v1541_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 46 5) 1) 14) v1541_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1541 : Material (17 : Basis) (46 : Basis) where
  plus := ![v1541_pa,v1541_pb,v1541_pg]
  minus := ![(Primitive.Addresses.material1541 1).one,v1541_mb,v1541_mg]
  upper := v1541_upper
  lower := (Primitive.Addresses.material1541 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1541_pa_checked.trans (by decide +kernel)
    · exact v1541_pb_checked.trans (by decide +kernel)
    · exact v1541_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 46 Primitive.Addresses.material1541
    · exact v1541_mb_checked.trans (by decide +kernel)
    · exact v1541_mg_checked.trans (by decide +kernel)
  upper_error := v1541_upper_checked
  lower_error := reuse_lower_error 17 46 Primitive.Addresses.material1541

def v1542_pa : Scalar.QComplex := ((999999825676111203392624013991 : Int)/10^30,(-590464010083930980647777317 : Int)/10^30)
theorem v1542_pa_checked : Scalar.distance (sourceCoefficient 17 47 1 0) v1542_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1542_pb : Scalar.QComplex := ((-254771938288908180457317 : Int)/10^30,(-431477430503950304805183058 : Int)/10^30)
theorem v1542_pb_checked : Scalar.distance (sourceCoefficient 17 47 1 1) v1542_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1542_pg : Scalar.QComplex := ((-93086412021558179285687 : Int)/10^30,(54964185708144880018 : Int)/10^30)
theorem v1542_pg_checked : Scalar.distance (sourceCoefficient 17 47 1 2) v1542_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1542_mb : Scalar.QComplex := ((-627117432928498806649617 : Int)/10^30,(-431477049988475194266978950 : Int)/10^30)
theorem v1542_mb_checked : Scalar.distance (sourceCoefficient 17 47 3 1) v1542_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1542_mg : Scalar.QComplex := ((-93086329929615953366092 : Int)/10^30,(135293546360705107062 : Int)/10^30)
theorem v1542_mg_checked : Scalar.distance (sourceCoefficient 17 47 3 2) v1542_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1542_upper : Scalar.QComplex := ((999997317206524161733675964766 : Int)/10^30,(-2316372110498591426110591392 : Int)/10^30)
theorem v1542_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 47 5) 1) 14) v1542_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1542 : Material (17 : Basis) (47 : Basis) where
  plus := ![v1542_pa,v1542_pb,v1542_pg]
  minus := ![(Primitive.Addresses.material1542 1).one,v1542_mb,v1542_mg]
  upper := v1542_upper
  lower := (Primitive.Addresses.material1542 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1542_pa_checked.trans (by decide +kernel)
    · exact v1542_pb_checked.trans (by decide +kernel)
    · exact v1542_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 47 Primitive.Addresses.material1542
    · exact v1542_mb_checked.trans (by decide +kernel)
    · exact v1542_mg_checked.trans (by decide +kernel)
  upper_error := v1542_upper_checked
  lower_error := reuse_lower_error 17 47 Primitive.Addresses.material1542

def v1543_pa : Scalar.QComplex := ((999999809103130169726327218105 : Int)/10^30,(-617894572899724079270464679 : Int)/10^30)
theorem v1543_pa_checked : Scalar.distance (sourceCoefficient 17 48 1 0) v1543_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1543_pb : Scalar.QComplex := ((-266607607956070409476671 : Int)/10^30,(-431477421480410661316839476 : Int)/10^30)
theorem v1543_pb_checked : Scalar.distance (sourceCoefficient 17 48 1 1) v1543_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1543_pg : Scalar.QComplex := ((-93086410276834686751202 : Int)/10^30,(57517598700702807182 : Int)/10^30)
theorem v1543_pg_checked : Scalar.distance (sourceCoefficient 17 48 1 2) v1543_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1543_mb : Scalar.QComplex := ((-638953090401791994567485 : Int)/10^30,(-431477030751289046667574288 : Int)/10^30)
theorem v1543_mb_checked : Scalar.distance (sourceCoefficient 17 48 3 1) v1543_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1543_mg : Scalar.QComplex := ((-93086325981412699346540 : Int)/10^30,(137846956896892885729 : Int)/10^30)
theorem v1543_mg_checked : Scalar.distance (sourceCoefficient 17 48 3 2) v1543_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1543_upper : Scalar.QComplex := ((999997253290904872736641724507 : Int)/10^30,(-2343802603856321655853162728 : Int)/10^30)
theorem v1543_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 48 5) 1) 14) v1543_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1543 : Material (17 : Basis) (48 : Basis) where
  plus := ![v1543_pa,v1543_pb,v1543_pg]
  minus := ![(Primitive.Addresses.material1543 1).one,v1543_mb,v1543_mg]
  upper := v1543_upper
  lower := (Primitive.Addresses.material1543 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1543_pa_checked.trans (by decide +kernel)
    · exact v1543_pb_checked.trans (by decide +kernel)
    · exact v1543_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 48 Primitive.Addresses.material1543
    · exact v1543_mb_checked.trans (by decide +kernel)
    · exact v1543_mg_checked.trans (by decide +kernel)
  upper_error := v1543_upper_checked
  lower_error := reuse_lower_error 17 48 Primitive.Addresses.material1543

def v1544_pa : Scalar.QComplex := ((999999795242887121488135021746 : Int)/10^30,(-639932952606402708924054542 : Int)/10^30)
theorem v1544_pa_checked : Scalar.distance (sourceCoefficient 17 49 1 0) v1544_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1544_pb : Scalar.QComplex := ((-276116672007782995955371 : Int)/10^30,(-431477413917077589997036062 : Int)/10^30)
theorem v1544_pb_checked : Scalar.distance (sourceCoefficient 17 49 1 1) v1544_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1544_pg : Scalar.QComplex := ((-93086408815882326486799 : Int)/10^30,(59569072638265582405 : Int)/10^30)
theorem v1544_pg_checked : Scalar.distance (sourceCoefficient 17 49 1 2) v1544_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1544_mb : Scalar.QComplex := ((-648462144386029648224852 : Int)/10^30,(-431477014982064787241044917 : Int)/10^30)
theorem v1544_mb_checked : Scalar.distance (sourceCoefficient 17 49 3 1) v1544_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1544_mg : Scalar.QComplex := ((-93086322750131269901081 : Int)/10^30,(139898428809862068951 : Int)/10^30)
theorem v1544_mg_checked : Scalar.distance (sourceCoefficient 17 49 3 2) v1544_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1544_upper : Scalar.QComplex := ((999997201394438400164283588135 : Int)/10^30,(-2365840926817900412511273129 : Int)/10^30)
theorem v1544_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 49 5) 1) 14) v1544_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1544 : Material (17 : Basis) (49 : Basis) where
  plus := ![v1544_pa,v1544_pb,v1544_pg]
  minus := ![(Primitive.Addresses.material1544 1).one,v1544_mb,v1544_mg]
  upper := v1544_upper
  lower := (Primitive.Addresses.material1544 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1544_pa_checked.trans (by decide +kernel)
    · exact v1544_pb_checked.trans (by decide +kernel)
    · exact v1544_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 49 Primitive.Addresses.material1544
    · exact v1544_mb_checked.trans (by decide +kernel)
    · exact v1544_mg_checked.trans (by decide +kernel)
  upper_error := v1544_upper_checked
  lower_error := reuse_lower_error 17 49 Primitive.Addresses.material1544

def v1545_pa : Scalar.QComplex := ((999999793591563847534857309370 : Int)/10^30,(-642508233177200438646815702 : Int)/10^30)
theorem v1545_pa_checked : Scalar.distance (sourceCoefficient 17 50 1 0) v1545_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1545_pb : Scalar.QComplex := ((-277227847514326305023285 : Int)/10^30,(-431477413015035800832552916 : Int)/10^30)
theorem v1545_pb_checked : Scalar.distance (sourceCoefficient 17 50 1 1) v1545_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1545_pg : Scalar.QComplex := ((-93086408641721739123915 : Int)/10^30,(59808796294243628382 : Int)/10^30)
theorem v1545_pg_checked : Scalar.distance (sourceCoefficient 17 50 1 2) v1545_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1545_mb : Scalar.QComplex := ((-649573318700410095382411 : Int)/10^30,(-431477013121128917288108403 : Int)/10^30)
theorem v1545_mb_checked : Scalar.distance (sourceCoefficient 17 50 3 1) v1545_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1545_mg : Scalar.QComplex := ((-93086322369100029029760 : Int)/10^30,(140138152226287298902 : Int)/10^30)
theorem v1545_mg_checked : Scalar.distance (sourceCoefficient 17 50 3 2) v1545_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1545_upper : Scalar.QComplex := ((999997195298416948094546759814 : Int)/10^30,(-2368416200703086081770919210 : Int)/10^30)
theorem v1545_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 50 5) 1) 14) v1545_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1545 : Material (17 : Basis) (50 : Basis) where
  plus := ![v1545_pa,v1545_pb,v1545_pg]
  minus := ![(Primitive.Addresses.material1545 1).one,v1545_mb,v1545_mg]
  upper := v1545_upper
  lower := (Primitive.Addresses.material1545 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1545_pa_checked.trans (by decide +kernel)
    · exact v1545_pb_checked.trans (by decide +kernel)
    · exact v1545_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 50 Primitive.Addresses.material1545
    · exact v1545_mb_checked.trans (by decide +kernel)
    · exact v1545_mg_checked.trans (by decide +kernel)
  upper_error := v1545_upper_checked
  lower_error := reuse_lower_error 17 50 Primitive.Addresses.material1545

def v1546_pa : Scalar.QComplex := ((999999786267865847612037420756 : Int)/10^30,(-653807481314913339699880836 : Int)/10^30)
theorem v1546_pa_checked : Scalar.distance (sourceCoefficient 17 51 1 0) v1546_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1546_pb : Scalar.QComplex := ((-282103218325047989988338 : Int)/10^30,(-431477409012160101364334386 : Int)/10^30)
theorem v1546_pb_checked : Scalar.distance (sourceCoefficient 17 51 1 1) v1546_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1546_pg : Scalar.QComplex := ((-93086407869065547909844 : Int)/10^30,(60860602881393014927 : Int)/10^30)
theorem v1546_pg_checked : Scalar.distance (sourceCoefficient 17 51 1 2) v1546_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1546_mb : Scalar.QComplex := ((-654448684241506966250442 : Int)/10^30,(-431477004911029277170815093 : Int)/10^30)
theorem v1546_mb_checked : Scalar.distance (sourceCoefficient 17 51 3 1) v1546_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1546_mg : Scalar.QComplex := ((-93086320688782412411149 : Int)/10^30,(141189957755033529241 : Int)/10^30)
theorem v1546_mg_checked : Scalar.distance (sourceCoefficient 17 51 3 2) v1546_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1546_upper : Scalar.QComplex := ((999997168473252630050854251834 : Int)/10^30,(-2379715419371857837450571552 : Int)/10^30)
theorem v1546_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 51 5) 1) 14) v1546_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1546 : Material (17 : Basis) (51 : Basis) where
  plus := ![v1546_pa,v1546_pb,v1546_pg]
  minus := ![(Primitive.Addresses.material1546 1).one,v1546_mb,v1546_mg]
  upper := v1546_upper
  lower := (Primitive.Addresses.material1546 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1546_pa_checked.trans (by decide +kernel)
    · exact v1546_pb_checked.trans (by decide +kernel)
    · exact v1546_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 51 Primitive.Addresses.material1546
    · exact v1546_mb_checked.trans (by decide +kernel)
    · exact v1546_mg_checked.trans (by decide +kernel)
  upper_error := v1546_upper_checked
  lower_error := reuse_lower_error 17 51 Primitive.Addresses.material1546

def v1547_pa : Scalar.QComplex := ((999999770160408913394540622868 : Int)/10^30,(-677996408063474395200798374 : Int)/10^30)
theorem v1547_pa_checked : Scalar.distance (sourceCoefficient 17 52 1 0) v1547_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1547_pb : Scalar.QComplex := ((-292540194730810916169092 : Int)/10^30,(-431477400196055929286457691 : Int)/10^30)
theorem v1547_pb_checked : Scalar.distance (sourceCoefficient 17 52 1 1) v1547_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1547_pg : Scalar.QComplex := ((-93086406168384979964383 : Int)/10^30,(63112263527399504598 : Int)/10^30)
theorem v1547_pg_checked : Scalar.distance (sourceCoefficient 17 52 1 2) v1547_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1547_mb : Scalar.QComplex := ((-664885649153205745269011 : Int)/10^30,(-431476987088287813525753089 : Int)/10^30)
theorem v1547_mb_checked : Scalar.distance (sourceCoefficient 17 52 3 1) v1547_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1547_mg : Scalar.QComplex := ((-93086317045020751234129 : Int)/10^30,(143441616095033120101 : Int)/10^30)
theorem v1547_mg_checked : Scalar.distance (sourceCoefficient 17 52 3 2) v1547_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1547_upper : Scalar.QComplex := ((999997110617926520274863828405 : Int)/10^30,(-2403904282293844520524278526 : Int)/10^30)
theorem v1547_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 52 5) 1) 14) v1547_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1547 : Material (17 : Basis) (52 : Basis) where
  plus := ![v1547_pa,v1547_pb,v1547_pg]
  minus := ![(Primitive.Addresses.material1547 1).one,v1547_mb,v1547_mg]
  upper := v1547_upper
  lower := (Primitive.Addresses.material1547 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1547_pa_checked.trans (by decide +kernel)
    · exact v1547_pb_checked.trans (by decide +kernel)
    · exact v1547_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 52 Primitive.Addresses.material1547
    · exact v1547_mb_checked.trans (by decide +kernel)
    · exact v1547_mg_checked.trans (by decide +kernel)
  upper_error := v1547_upper_checked
  lower_error := reuse_lower_error 17 52 Primitive.Addresses.material1547

def v1548_pa : Scalar.QComplex := ((999999767643143521512380593946 : Int)/10^30,(-681699097085559066862232929 : Int)/10^30)
theorem v1548_pa_checked : Scalar.distance (sourceCoefficient 17 53 1 0) v1548_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1548_pb : Scalar.QComplex := ((-294137821531201751394864 : Int)/10^30,(-431477398816835113630055257 : Int)/10^30)
theorem v1548_pb_checked : Scalar.distance (sourceCoefficient 17 53 1 1) v1548_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1548_pg : Scalar.QComplex := ((-93086405902447654185256 : Int)/10^30,(63456933599292034870 : Int)/10^30)
theorem v1548_pg_checked : Scalar.distance (sourceCoefficient 17 53 1 2) v1548_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1548_mb : Scalar.QComplex := ((-666483274168521661445616 : Int)/10^30,(-431476984330387537119018264 : Int)/10^30)
theorem v1548_mb_checked : Scalar.distance (sourceCoefficient 17 53 3 1) v1548_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1548_mg : Scalar.QComplex := ((-93086316481648775796153 : Int)/10^30,(143786285809097295633 : Int)/10^30)
theorem v1548_mg_checked : Scalar.distance (sourceCoefficient 17 53 3 2) v1548_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1548_upper : Scalar.QComplex := ((999997101710159530769798083024 : Int)/10^30,(-2407606961456637140340445306 : Int)/10^30)
theorem v1548_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 53 5) 1) 14) v1548_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1548 : Material (17 : Basis) (53 : Basis) where
  plus := ![v1548_pa,v1548_pb,v1548_pg]
  minus := ![(Primitive.Addresses.material1548 1).one,v1548_mb,v1548_mg]
  upper := v1548_upper
  lower := (Primitive.Addresses.material1548 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1548_pa_checked.trans (by decide +kernel)
    · exact v1548_pb_checked.trans (by decide +kernel)
    · exact v1548_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 53 Primitive.Addresses.material1548
    · exact v1548_mb_checked.trans (by decide +kernel)
    · exact v1548_mg_checked.trans (by decide +kernel)
  upper_error := v1548_upper_checked
  lower_error := reuse_lower_error 17 53 Primitive.Addresses.material1548

def v1549_pa : Scalar.QComplex := ((999999766358093574831085002022 : Int)/10^30,(-683581566648631472595799944 : Int)/10^30)
theorem v1549_pa_checked : Scalar.distance (sourceCoefficient 17 54 1 0) v1549_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1549_pb : Scalar.QComplex := ((-294950064687986259393502 : Int)/10^30,(-431477398112606543482937309 : Int)/10^30)
theorem v1549_pb_checked : Scalar.distance (sourceCoefficient 17 54 1 1) v1549_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1549_pg : Scalar.QComplex := ((-93086405766672595331082 : Int)/10^30,(63632165954812819422 : Int)/10^30)
theorem v1549_pg_checked : Scalar.distance (sourceCoefficient 17 54 1 2) v1549_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1549_mb : Scalar.QComplex := ((-667295516415153382067720 : Int)/10^30,(-431476982925229966957142577 : Int)/10^30)
theorem v1549_mb_checked : Scalar.distance (sourceCoefficient 17 54 3 1) v1549_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1549_mg : Scalar.QComplex := ((-93086316194656136855123 : Int)/10^30,(143961517982203305000 : Int)/10^30)
theorem v1549_mg_checked : Scalar.distance (sourceCoefficient 17 54 3 2) v1549_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1549_upper : Scalar.QComplex := ((999997097176139808461203851759 : Int)/10^30,(-2409489425998112633134689400 : Int)/10^30)
theorem v1549_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 54 5) 1) 14) v1549_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1549 : Material (17 : Basis) (54 : Basis) where
  plus := ![v1549_pa,v1549_pb,v1549_pg]
  minus := ![(Primitive.Addresses.material1549 1).one,v1549_mb,v1549_mg]
  upper := v1549_upper
  lower := (Primitive.Addresses.material1549 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1549_pa_checked.trans (by decide +kernel)
    · exact v1549_pb_checked.trans (by decide +kernel)
    · exact v1549_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 54 Primitive.Addresses.material1549
    · exact v1549_mb_checked.trans (by decide +kernel)
    · exact v1549_mg_checked.trans (by decide +kernel)
  upper_error := v1549_upper_checked
  lower_error := reuse_lower_error 17 54 Primitive.Addresses.material1549

def v1550_pa : Scalar.QComplex := ((999999755751781220815664247562 : Int)/10^30,(-698925159012877640380100994 : Int)/10^30)
theorem v1550_pa_checked : Scalar.distance (sourceCoefficient 17 55 1 0) v1550_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1550_pb : Scalar.QComplex := ((-301570478679391661276905 : Int)/10^30,(-431477392296566329155946267 : Int)/10^30)
theorem v1550_pb_checked : Scalar.distance (sourceCoefficient 17 55 1 1) v1550_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1550_pg : Scalar.QComplex := ((-93086404645648036835877 : Int)/10^30,(65060446059794689131 : Int)/10^30)
theorem v1550_pg_checked : Scalar.distance (sourceCoefficient 17 55 1 2) v1550_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1550_mb : Scalar.QComplex := ((-673915922922495326847544 : Int)/10^30,(-431476971396072816002361630 : Int)/10^30)
theorem v1550_mb_checked : Scalar.distance (sourceCoefficient 17 55 3 1) v1550_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1550_mg : Scalar.QComplex := ((-93086313841090592517225 : Int)/10^30,(145389796587977511090 : Int)/10^30)
theorem v1550_mg_checked : Scalar.distance (sourceCoefficient 17 55 3 2) v1550_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1550_upper : Scalar.QComplex := ((999997060088194790439134805233 : Int)/10^30,(-2424832977204347433453934959 : Int)/10^30)
theorem v1550_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 55 5) 1) 14) v1550_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1550 : Material (17 : Basis) (55 : Basis) where
  plus := ![v1550_pa,v1550_pb,v1550_pg]
  minus := ![(Primitive.Addresses.material1550 1).one,v1550_mb,v1550_mg]
  upper := v1550_upper
  lower := (Primitive.Addresses.material1550 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1550_pa_checked.trans (by decide +kernel)
    · exact v1550_pb_checked.trans (by decide +kernel)
    · exact v1550_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 55 Primitive.Addresses.material1550
    · exact v1550_mb_checked.trans (by decide +kernel)
    · exact v1550_mg_checked.trans (by decide +kernel)
  upper_error := v1550_upper_checked
  lower_error := reuse_lower_error 17 55 Primitive.Addresses.material1550

def v1551_pa : Scalar.QComplex := ((999999753200040340153276169731 : Int)/10^30,(-702566622043399781349621206 : Int)/10^30)
theorem v1551_pa_checked : Scalar.distance (sourceCoefficient 17 56 1 0) v1551_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1551_pb : Scalar.QComplex := ((-303141687825519415065053 : Int)/10^30,(-431477390896371197216944844 : Int)/10^30)
theorem v1551_pb_checked : Scalar.distance (sourceCoefficient 17 56 1 1) v1551_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1551_pg : Scalar.QComplex := ((-93086404375843624342389 : Int)/10^30,(65399416821075836370 : Int)/10^30)
theorem v1551_pg_checked : Scalar.distance (sourceCoefficient 17 56 1 2) v1551_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1551_mb : Scalar.QComplex := ((-675487130275284771311370 : Int)/10^30,(-431476968639995476944783325 : Int)/10^30)
theorem v1551_mb_checked : Scalar.distance (sourceCoefficient 17 56 3 1) v1551_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1551_mg : Scalar.QComplex := ((-93086313278769780174983 : Int)/10^30,(145728766990215295732 : Int)/10^30)
theorem v1551_mg_checked : Scalar.distance (sourceCoefficient 17 56 3 2) v1551_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1551_upper : Scalar.QComplex := ((999997051251622870559393619431 : Int)/10^30,(-2428474430407264878857626863 : Int)/10^30)
theorem v1551_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 56 5) 1) 14) v1551_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1551 : Material (17 : Basis) (56 : Basis) where
  plus := ![v1551_pa,v1551_pb,v1551_pg]
  minus := ![(Primitive.Addresses.material1551 1).one,v1551_mb,v1551_mg]
  upper := v1551_upper
  lower := (Primitive.Addresses.material1551 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1551_pa_checked.trans (by decide +kernel)
    · exact v1551_pb_checked.trans (by decide +kernel)
    · exact v1551_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 56 Primitive.Addresses.material1551
    · exact v1551_mb_checked.trans (by decide +kernel)
    · exact v1551_mg_checked.trans (by decide +kernel)
  upper_error := v1551_upper_checked
  lower_error := reuse_lower_error 17 56 Primitive.Addresses.material1551

def v1552_pa : Scalar.QComplex := ((999999744855952653655860569442 : Int)/10^30,(-714344475441788086477774157 : Int)/10^30)
theorem v1552_pa_checked : Scalar.distance (sourceCoefficient 17 57 1 0) v1552_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1552_pb : Scalar.QComplex := ((-308223565833859827973127 : Int)/10^30,(-431477386315377024146612057 : Int)/10^30)
theorem v1552_pb_checked : Scalar.distance (sourceCoefficient 17 57 1 1) v1552_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1552_pg : Scalar.QComplex := ((-93086403493333932025416 : Int)/10^30,(66495775040209432940 : Int)/10^30)
theorem v1552_pg_checked : Scalar.distance (sourceCoefficient 17 57 1 2) v1552_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1552_mb : Scalar.QComplex := ((-680569002438218097374670 : Int)/10^30,(-431476959673571167679263673 : Int)/10^30)
theorem v1552_mb_checked : Scalar.distance (sourceCoefficient 17 57 3 1) v1552_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1552_mg : Scalar.QComplex := ((-93086311450152651485594 : Int)/10^30,(146825124039558503564 : Int)/10^30)
theorem v1552_mg_checked : Scalar.distance (sourceCoefficient 17 57 3 2) v1552_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1552_upper : Scalar.QComplex := ((999997022580041124496012692800 : Int)/10^30,(-2440252251862785693761080316 : Int)/10^30)
theorem v1552_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 57 5) 1) 14) v1552_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1552 : Material (17 : Basis) (57 : Basis) where
  plus := ![v1552_pa,v1552_pb,v1552_pg]
  minus := ![(Primitive.Addresses.material1552 1).one,v1552_mb,v1552_mg]
  upper := v1552_upper
  lower := (Primitive.Addresses.material1552 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1552_pa_checked.trans (by decide +kernel)
    · exact v1552_pb_checked.trans (by decide +kernel)
    · exact v1552_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 57 Primitive.Addresses.material1552
    · exact v1552_mb_checked.trans (by decide +kernel)
    · exact v1552_mg_checked.trans (by decide +kernel)
  upper_error := v1552_upper_checked
  lower_error := reuse_lower_error 17 57 Primitive.Addresses.material1552

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
