import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B066

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1585_pa : Scalar.QComplex := ((999999065305708832037997507301 : Int)/10^30,(-1367255538910889204303500345 : Int)/10^30)
theorem v1585_pa_checked : Scalar.distance (sourceCoefficient 17 90 1 0) v1585_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1585_pb : Scalar.QComplex := ((-589939879871197232916048 : Int)/10^30,(-431477007529759690708714369 : Int)/10^30)
theorem v1585_pb_checked : Scalar.distance (sourceCoefficient 17 90 1 1) v1585_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1585_pg : Scalar.QComplex := ((-93086331005508971987026 : Int)/10^30,(127272920625446913317 : Int)/10^30)
theorem v1585_pg_checked : Scalar.distance (sourceCoefficient 17 90 1 2) v1585_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1585_mb : Scalar.QComplex := ((-962284884704768826779542 : Int)/10^30,(-431476337779603890998238948 : Int)/10^30)
theorem v1585_mb_checked : Scalar.distance (sourceCoefficient 17 90 3 1) v1585_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1585_mg : Scalar.QComplex := ((-93086186514415342941118 : Int)/10^30,(207602184440958819717 : Int)/10^30)
theorem v1585_mg_checked : Scalar.distance (sourceCoefficient 17 90 3 2) v1585_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1585_upper : Scalar.QComplex := ((999995216165545494458036496778 : Int)/10^30,(-3093161170055481575935327547 : Int)/10^30)
theorem v1585_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 90 5) 1) 14) v1585_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1585 : Material (17 : Basis) (90 : Basis) where
  plus := ![v1585_pa,v1585_pb,v1585_pg]
  minus := ![(Primitive.Addresses.material1585 1).one,v1585_mb,v1585_mg]
  upper := v1585_upper
  lower := (Primitive.Addresses.material1585 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1585_pa_checked.trans (by decide +kernel)
    · exact v1585_pb_checked.trans (by decide +kernel)
    · exact v1585_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 90 Primitive.Addresses.material1585
    · exact v1585_mb_checked.trans (by decide +kernel)
    · exact v1585_mg_checked.trans (by decide +kernel)
  upper_error := v1585_upper_checked
  lower_error := reuse_lower_error 17 90 Primitive.Addresses.material1585

def v1586_pa : Scalar.QComplex := ((999999045014608257821317047569 : Int)/10^30,(-1382016595952182813345931098 : Int)/10^30)
theorem v1586_pa_checked : Scalar.distance (sourceCoefficient 17 91 1 0) v1586_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1586_pb : Scalar.QComplex := ((-596308938891213931183875 : Int)/10^30,(-431476996131181293611608258 : Int)/10^30)
theorem v1586_pb_checked : Scalar.distance (sourceCoefficient 17 91 1 1) v1586_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1586_pg : Scalar.QComplex := ((-93086328831538259682657 : Int)/10^30,(128646974157429048908 : Int)/10^30)
theorem v1586_pg_checked : Scalar.distance (sourceCoefficient 17 91 1 2) v1586_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1586_mb : Scalar.QComplex := ((-968653931516833987737180 : Int)/10^30,(-431476320884818655608223561 : Int)/10^30)
theorem v1586_mb_checked : Scalar.distance (sourceCoefficient 17 91 3 1) v1586_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1586_mg : Scalar.QComplex := ((-93086183154699127078615 : Int)/10^30,(208976235585279215289 : Int)/10^30)
theorem v1586_mg_checked : Scalar.distance (sourceCoefficient 17 91 3 2) v1586_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1586_upper : Scalar.QComplex := ((999995170398229800813544333353 : Int)/10^30,(-3107922170091315880701339772 : Int)/10^30)
theorem v1586_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 91 5) 1) 14) v1586_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1586 : Material (17 : Basis) (91 : Basis) where
  plus := ![v1586_pa,v1586_pb,v1586_pg]
  minus := ![(Primitive.Addresses.material1586 1).one,v1586_mb,v1586_mg]
  upper := v1586_upper
  lower := (Primitive.Addresses.material1586 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1586_pa_checked.trans (by decide +kernel)
    · exact v1586_pb_checked.trans (by decide +kernel)
    · exact v1586_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 91 Primitive.Addresses.material1586
    · exact v1586_mb_checked.trans (by decide +kernel)
    · exact v1586_mg_checked.trans (by decide +kernel)
  upper_error := v1586_upper_checked
  lower_error := reuse_lower_error 17 91 Primitive.Addresses.material1586

def v1587_pa : Scalar.QComplex := ((999999000340145488341868396484 : Int)/10^30,(-1413972669362279979757615067 : Int)/10^30)
theorem v1587_pa_checked : Scalar.distance (sourceCoefficient 17 92 1 0) v1587_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1587_pb : Scalar.QComplex := ((-610097254378403993726416 : Int)/10^30,(-431476971025071472240852473 : Int)/10^30)
theorem v1587_pb_checked : Scalar.distance (sourceCoefficient 17 92 1 1) v1587_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1587_pg : Scalar.QComplex := ((-93086324044064475441638 : Int)/10^30,(131621649666587187824 : Int)/10^30)
theorem v1587_pg_checked : Scalar.distance (sourceCoefficient 17 92 1 2) v1587_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1587_mb : Scalar.QComplex := ((-982442220204561998619155 : Int)/10^30,(-431476283880022919621376274 : Int)/10^30)
theorem v1587_mb_checked : Scalar.distance (sourceCoefficient 17 92 3 1) v1587_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1587_mg : Scalar.QComplex := ((-93086175800216135440980 : Int)/10^30,(211950905855455456773 : Int)/10^30)
theorem v1587_mg_checked : Scalar.distance (sourceCoefficient 17 92 3 2) v1587_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1587_upper : Scalar.QComplex := ((999995070570549895204616757896 : Int)/10^30,(-3139878118802525622329707944 : Int)/10^30)
theorem v1587_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 92 5) 1) 14) v1587_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1587 : Material (17 : Basis) (92 : Basis) where
  plus := ![v1587_pa,v1587_pb,v1587_pg]
  minus := ![(Primitive.Addresses.material1587 1).one,v1587_mb,v1587_mg]
  upper := v1587_upper
  lower := (Primitive.Addresses.material1587 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1587_pa_checked.trans (by decide +kernel)
    · exact v1587_pb_checked.trans (by decide +kernel)
    · exact v1587_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 92 Primitive.Addresses.material1587
    · exact v1587_mb_checked.trans (by decide +kernel)
    · exact v1587_mg_checked.trans (by decide +kernel)
  upper_error := v1587_upper_checked
  lower_error := reuse_lower_error 17 92 Primitive.Addresses.material1587

def v1588_pa : Scalar.QComplex := ((999998945995191796167215258386 : Int)/10^30,(-1451898242123575908520737581 : Int)/10^30)
theorem v1588_pa_checked : Scalar.distance (sourceCoefficient 17 93 1 0) v1588_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1588_pb : Scalar.QComplex := ((-626461271673642862480092 : Int)/10^30,(-431476940466692988838981495 : Int)/10^30)
theorem v1588_pb_checked : Scalar.distance (sourceCoefficient 17 93 1 1) v1588_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1588_pg : Scalar.QComplex := ((-93086318218362076204089 : Int)/10^30,(135152004237858001992 : Int)/10^30)
theorem v1588_pg_checked : Scalar.distance (sourceCoefficient 17 93 1 2) v1588_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1588_mb : Scalar.QComplex := ((-998806205036225022919840 : Int)/10^30,(-431476239200245896689213143 : Int)/10^30)
theorem v1588_mb_checked : Scalar.distance (sourceCoefficient 17 93 3 1) v1588_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1588_mg : Scalar.QComplex := ((-93086166927978911639454 : Int)/10^30,(215481254084895128237 : Int)/10^30)
theorem v1588_mg_checked : Scalar.distance (sourceCoefficient 17 93 3 2) v1588_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1588_upper : Scalar.QComplex := ((999994950769579138542468634769 : Int)/10^30,(-3177803541283676036862727435 : Int)/10^30)
theorem v1588_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 93 5) 1) 14) v1588_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1588 : Material (17 : Basis) (93 : Basis) where
  plus := ![v1588_pa,v1588_pb,v1588_pg]
  minus := ![(Primitive.Addresses.material1588 1).one,v1588_mb,v1588_mg]
  upper := v1588_upper
  lower := (Primitive.Addresses.material1588 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1588_pa_checked.trans (by decide +kernel)
    · exact v1588_pb_checked.trans (by decide +kernel)
    · exact v1588_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 93 Primitive.Addresses.material1588
    · exact v1588_mb_checked.trans (by decide +kernel)
    · exact v1588_mg_checked.trans (by decide +kernel)
  upper_error := v1588_upper_checked
  lower_error := reuse_lower_error 17 93 Primitive.Addresses.material1588

def v1589_pa : Scalar.QComplex := ((999998879948790619522926371311 : Int)/10^30,(-1496696750930609360821439106 : Int)/10^30)
theorem v1589_pa_checked : Scalar.distance (sourceCoefficient 17 94 1 0) v1589_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1589_pb : Scalar.QComplex := ((-645790802596153998742942 : Int)/10^30,(-431476903304459035498236823 : Int)/10^30)
theorem v1589_pb_checked : Scalar.distance (sourceCoefficient 17 94 1 1) v1589_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1589_pg : Scalar.QComplex := ((-93086311135682850172845 : Int)/10^30,(139322135480818662153 : Int)/10^30)
theorem v1589_pg_checked : Scalar.distance (sourceCoefficient 17 94 1 2) v1589_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1589_mb : Scalar.QComplex := ((-1018135696692134216680239 : Int)/10^30,(-431476185357511164175138192 : Int)/10^30)
theorem v1589_mb_checked : Scalar.distance (sourceCoefficient 17 94 3 1) v1589_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1589_mg : Scalar.QComplex := ((-93086156246666875877466 : Int)/10^30,(219651377663092162197 : Int)/10^30)
theorem v1589_mg_checked : Scalar.distance (sourceCoefficient 17 94 3 2) v1589_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1589_upper : Scalar.QComplex := ((999994807405114218286691656463 : Int)/10^30,(-3222601869378496275417435869 : Int)/10^30)
theorem v1589_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 94 5) 1) 14) v1589_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1589 : Material (17 : Basis) (94 : Basis) where
  plus := ![v1589_pa,v1589_pb,v1589_pg]
  minus := ![(Primitive.Addresses.material1589 1).one,v1589_mb,v1589_mg]
  upper := v1589_upper
  lower := (Primitive.Addresses.material1589 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1589_pa_checked.trans (by decide +kernel)
    · exact v1589_pb_checked.trans (by decide +kernel)
    · exact v1589_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 94 Primitive.Addresses.material1589
    · exact v1589_mb_checked.trans (by decide +kernel)
    · exact v1589_mg_checked.trans (by decide +kernel)
  upper_error := v1589_upper_checked
  lower_error := reuse_lower_error 17 94 Primitive.Addresses.material1589

def v1590_pa : Scalar.QComplex := ((999998812703601575298967007791 : Int)/10^30,(-1540970923533816829337096865 : Int)/10^30)
theorem v1590_pa_checked : Scalar.distance (sourceCoefficient 17 95 1 0) v1590_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1590_pb : Scalar.QComplex := ((-664894093251219356485986 : Int)/10^30,(-431476865442792974240271231 : Int)/10^30)
theorem v1590_pb_checked : Scalar.distance (sourceCoefficient 17 95 1 1) v1590_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1590_pg : Scalar.QComplex := ((-93086303921760866348417 : Int)/10^30,(143443458032566497267 : Int)/10^30)
theorem v1590_pg_checked : Scalar.distance (sourceCoefficient 17 95 1 2) v1590_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1590_mb : Scalar.QComplex := ((-1037238947561258815302106 : Int)/10^30,(-431476131010579745496694234 : Int)/10^30)
theorem v1590_mb_checked : Scalar.distance (sourceCoefficient 17 95 3 1) v1590_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1590_mg : Scalar.QComplex := ((-93086145476231833444789 : Int)/10^30,(223772692454993488495 : Int)/10^30)
theorem v1590_mg_checked : Scalar.distance (sourceCoefficient 17 95 3 2) v1590_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1590_upper : Scalar.QComplex := ((999994663746819936299766572725 : Int)/10^30,(-3266875859981428606672042071 : Int)/10^30)
theorem v1590_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 95 5) 1) 14) v1590_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1590 : Material (17 : Basis) (95 : Basis) where
  plus := ![v1590_pa,v1590_pb,v1590_pg]
  minus := ![(Primitive.Addresses.material1590 1).one,v1590_mb,v1590_mg]
  upper := v1590_upper
  lower := (Primitive.Addresses.material1590 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1590_pa_checked.trans (by decide +kernel)
    · exact v1590_pb_checked.trans (by decide +kernel)
    · exact v1590_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 95 Primitive.Addresses.material1590
    · exact v1590_mb_checked.trans (by decide +kernel)
    · exact v1590_mg_checked.trans (by decide +kernel)
  upper_error := v1590_upper_checked
  lower_error := reuse_lower_error 17 95 Primitive.Addresses.material1590

def v1591_pa : Scalar.QComplex := ((999998779710166291855765743527 : Int)/10^30,(-1562234994585965039751018151 : Int)/10^30)
theorem v1591_pa_checked : Scalar.distance (sourceCoefficient 17 96 1 0) v1591_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1591_pb : Scalar.QComplex := ((-674069052074250769139170 : Int)/10^30,(-431476846857655883443033880 : Int)/10^30)
theorem v1591_pb_checked : Scalar.distance (sourceCoefficient 17 96 1 1) v1591_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1591_pg : Scalar.QComplex := ((-93086300381372975644583 : Int)/10^30,(145422853430351355908 : Int)/10^30)
theorem v1591_pg_checked : Scalar.distance (sourceCoefficient 17 96 1 2) v1591_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1591_mb : Scalar.QComplex := ((-1046413886929897475951874 : Int)/10^30,(-431476104507873335325032892 : Int)/10^30)
theorem v1591_mb_checked : Scalar.distance (sourceCoefficient 17 96 3 1) v1591_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1591_mg : Scalar.QComplex := ((-93086140227716181360200 : Int)/10^30,(225752084060563681176 : Int)/10^30)
theorem v1591_mg_checked : Scalar.distance (sourceCoefficient 17 96 3 2) v1591_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1591_upper : Scalar.QComplex := ((999994594053576218151777409813 : Int)/10^30,(-3288139842419564680006423697 : Int)/10^30)
theorem v1591_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 96 5) 1) 14) v1591_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1591 : Material (17 : Basis) (96 : Basis) where
  plus := ![v1591_pa,v1591_pb,v1591_pg]
  minus := ![(Primitive.Addresses.material1591 1).one,v1591_mb,v1591_mg]
  upper := v1591_upper
  lower := (Primitive.Addresses.material1591 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1591_pa_checked.trans (by decide +kernel)
    · exact v1591_pb_checked.trans (by decide +kernel)
    · exact v1591_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 96 Primitive.Addresses.material1591
    · exact v1591_mb_checked.trans (by decide +kernel)
    · exact v1591_mg_checked.trans (by decide +kernel)
  upper_error := v1591_upper_checked
  lower_error := reuse_lower_error 17 96 Primitive.Addresses.material1591

def v1592_pa : Scalar.QComplex := ((999998662737228676608101067935 : Int)/10^30,(-1635397124363090052191494804 : Int)/10^30)
theorem v1592_pa_checked : Scalar.distance (sourceCoefficient 17 97 1 0) v1592_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1592_pb : Scalar.QComplex := ((-705636830376974819171922 : Int)/10^30,(-431476780925564691465535947 : Int)/10^30)
theorem v1592_pb_checked : Scalar.distance (sourceCoefficient 17 97 1 1) v1592_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1592_pg : Scalar.QComplex := ((-93086287825022146003329 : Int)/10^30,(152233251002535261135 : Int)/10^30)
theorem v1592_pg_checked : Scalar.distance (sourceCoefficient 17 97 1 2) v1592_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1592_mb : Scalar.QComplex := ((-1077981596582069717619031 : Int)/10^30,(-431476011334235777584020222 : Int)/10^30)
theorem v1592_mb_checked : Scalar.distance (sourceCoefficient 17 97 3 1) v1592_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1592_mg : Scalar.QComplex := ((-93086121794303651147842 : Int)/10^30,(232562468261360070801 : Int)/10^30)
theorem v1592_mg_checked : Scalar.distance (sourceCoefficient 17 97 3 2) v1592_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1592_upper : Scalar.QComplex := ((999994350809614041602602946294 : Int)/10^30,(-3361301661345612994983287287 : Int)/10^30)
theorem v1592_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 97 5) 1) 14) v1592_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1592 : Material (17 : Basis) (97 : Basis) where
  plus := ![v1592_pa,v1592_pb,v1592_pg]
  minus := ![(Primitive.Addresses.material1592 1).one,v1592_mb,v1592_mg]
  upper := v1592_upper
  lower := (Primitive.Addresses.material1592 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1592_pa_checked.trans (by decide +kernel)
    · exact v1592_pb_checked.trans (by decide +kernel)
    · exact v1592_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 97 Primitive.Addresses.material1592
    · exact v1592_mb_checked.trans (by decide +kernel)
    · exact v1592_mg_checked.trans (by decide +kernel)
  upper_error := v1592_upper_checked
  lower_error := reuse_lower_error 17 97 Primitive.Addresses.material1592

def v1593_pa : Scalar.QComplex := ((999999981987358263338963129362 : Int)/10^30,(-189803274863387990510993512 : Int)/10^30)
theorem v1593_pa_checked : Scalar.distance (sourceCoefficient 18 19 1 0) v1593_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1593_pb : Scalar.QComplex := ((-81895846512516415240228 : Int)/10^30,(-431477513210985861117310698 : Int)/10^30)
theorem v1593_pb_checked : Scalar.distance (sourceCoefficient 18 19 1 1) v1593_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1593_pg : Scalar.QComplex := ((-93086428218343223600292 : Int)/10^30,(17668109239426556792 : Int)/10^30)
theorem v1593_pg_checked : Scalar.distance (sourceCoefficient 18 19 1 2) v1593_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1593_mb : Scalar.QComplex := ((-454241476894223535980084 : Int)/10^30,(-431477281879761107854122737 : Int)/10^30)
theorem v1593_mb_checked : Scalar.distance (sourceCoefficient 18 19 3 1) v1593_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1593_mg : Scalar.QComplex := ((-93086378311229206452517 : Int)/10^30,(97997497756116585164 : Int)/10^30)
theorem v1593_mg_checked : Scalar.distance (sourceCoefficient 18 19 3 2) v1593_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1593_upper : Scalar.QComplex := ((999998165021619747129443806675 : Int)/10^30,(-1915712241794180610789217148 : Int)/10^30)
theorem v1593_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 19 5) 1) 14) v1593_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1593 : Material (18 : Basis) (19 : Basis) where
  plus := ![v1593_pa,v1593_pb,v1593_pg]
  minus := ![(Primitive.Addresses.material1593 1).one,v1593_mb,v1593_mg]
  upper := v1593_upper
  lower := (Primitive.Addresses.material1593 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1593_pa_checked.trans (by decide +kernel)
    · exact v1593_pb_checked.trans (by decide +kernel)
    · exact v1593_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 19 Primitive.Addresses.material1593
    · exact v1593_mb_checked.trans (by decide +kernel)
    · exact v1593_mg_checked.trans (by decide +kernel)
  upper_error := v1593_upper_checked
  lower_error := reuse_lower_error 18 19 Primitive.Addresses.material1593

def v1594_pa : Scalar.QComplex := ((999999981450942645804276003728 : Int)/10^30,(-192608707914060622990931605 : Int)/10^30)
theorem v1594_pa_checked : Scalar.distance (sourceCoefficient 18 20 1 0) v1594_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1594_pb : Scalar.QComplex := ((-83106327809179113968806 : Int)/10^30,(-431477512972653248876180134 : Int)/10^30)
theorem v1594_pb_checked : Scalar.distance (sourceCoefficient 18 20 1 1) v1594_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1594_pg : Scalar.QComplex := ((-93086428167667923846129 : Int)/10^30,(17929256986280352697 : Int)/10^30)
theorem v1594_pg_checked : Scalar.distance (sourceCoefficient 18 20 1 2) v1594_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1594_mb : Scalar.QComplex := ((-455451957534498415971224 : Int)/10^30,(-431477280596837743389003449 : Int)/10^30)
theorem v1594_mb_checked : Scalar.distance (sourceCoefficient 18 20 3 1) v1594_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1594_mg : Scalar.QComplex := ((-93086378035195181690163 : Int)/10^30,(98258645362002638516 : Int)/10^30)
theorem v1594_mg_checked : Scalar.distance (sourceCoefficient 18 20 3 2) v1594_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1594_upper : Scalar.QComplex := ((999998159643281989960101769499 : Int)/10^30,(-1918517669740685570987794348 : Int)/10^30)
theorem v1594_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 20 5) 1) 14) v1594_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1594 : Material (18 : Basis) (20 : Basis) where
  plus := ![v1594_pa,v1594_pb,v1594_pg]
  minus := ![(Primitive.Addresses.material1594 1).one,v1594_mb,v1594_mg]
  upper := v1594_upper
  lower := (Primitive.Addresses.material1594 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1594_pa_checked.trans (by decide +kernel)
    · exact v1594_pb_checked.trans (by decide +kernel)
    · exact v1594_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 20 Primitive.Addresses.material1594
    · exact v1594_mb_checked.trans (by decide +kernel)
    · exact v1594_mg_checked.trans (by decide +kernel)
  upper_error := v1594_upper_checked
  lower_error := reuse_lower_error 18 20 Primitive.Addresses.material1594

def v1595_pa : Scalar.QComplex := ((999999969836014188897375220286 : Int)/10^30,(-245617529326266144548214598 : Int)/10^30)
theorem v1595_pa_checked : Scalar.distance (sourceCoefficient 18 21 1 0) v1595_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1595_pb : Scalar.QComplex := ((-105978442577790465405638 : Int)/10^30,(-431477507618284541640029731 : Int)/10^30)
theorem v1595_pb_checked : Scalar.distance (sourceCoefficient 18 21 1 1) v1595_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1595_pg : Scalar.QComplex := ((-93086427049499351443332 : Int)/10^30,(22863658915366824165 : Int)/10^30)
theorem v1595_pg_checked : Scalar.distance (sourceCoefficient 18 21 1 2) v1595_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1595_mb : Scalar.QComplex := ((-478324059166197089239697 : Int)/10^30,(-431477255504866106326692411 : Int)/10^30)
theorem v1595_mb_checked : Scalar.distance (sourceCoefficient 18 21 3 1) v1595_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1595_mg : Scalar.QComplex := ((-93086372658860398044057 : Int)/10^30,(103193044488856640936 : Int)/10^30)
theorem v1595_mg_checked : Scalar.distance (sourceCoefficient 18 21 3 2) v1595_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1595_upper : Scalar.QComplex := ((999998056539953997371294570540 : Int)/10^30,(-1971526392156165634097899358 : Int)/10^30)
theorem v1595_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 21 5) 1) 14) v1595_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1595 : Material (18 : Basis) (21 : Basis) where
  plus := ![v1595_pa,v1595_pb,v1595_pg]
  minus := ![(Primitive.Addresses.material1595 1).one,v1595_mb,v1595_mg]
  upper := v1595_upper
  lower := (Primitive.Addresses.material1595 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1595_pa_checked.trans (by decide +kernel)
    · exact v1595_pb_checked.trans (by decide +kernel)
    · exact v1595_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 21 Primitive.Addresses.material1595
    · exact v1595_mb_checked.trans (by decide +kernel)
    · exact v1595_mg_checked.trans (by decide +kernel)
  upper_error := v1595_upper_checked
  lower_error := reuse_lower_error 18 21 Primitive.Addresses.material1595

def v1596_pa : Scalar.QComplex := ((999999969492627506512953797211 : Int)/10^30,(-247011627370604390237589608 : Int)/10^30)
theorem v1596_pa_checked : Scalar.distance (sourceCoefficient 18 22 1 0) v1596_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1596_pb : Scalar.QComplex := ((-106579964541907295397517 : Int)/10^30,(-431477507455651705913718469 : Int)/10^30)
theorem v1596_pb_checked : Scalar.distance (sourceCoefficient 18 22 1 1) v1596_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1596_pg : Scalar.QComplex := ((-93086427015973927274288 : Int)/10^30,(22993430524799863212 : Int)/10^30)
theorem v1596_pg_checked : Scalar.distance (sourceCoefficient 18 22 1 2) v1596_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1596_mb : Scalar.QComplex := ((-478925580765994988558250 : Int)/10^30,(-431477254823146967666772746 : Int)/10^30)
theorem v1596_mb_checked : Scalar.distance (sourceCoefficient 18 22 3 1) v1596_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1596_mg : Scalar.QComplex := ((-93086372513347932113670 : Int)/10^30,(103322816021038847807 : Int)/10^30)
theorem v1596_mg_checked : Scalar.distance (sourceCoefficient 18 22 3 2) v1596_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1596_upper : Scalar.QComplex := ((999998053790481073479828013436 : Int)/10^30,(-1972920487531504343006386777 : Int)/10^30)
theorem v1596_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 22 5) 1) 14) v1596_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1596 : Material (18 : Basis) (22 : Basis) where
  plus := ![v1596_pa,v1596_pb,v1596_pg]
  minus := ![(Primitive.Addresses.material1596 1).one,v1596_mb,v1596_mg]
  upper := v1596_upper
  lower := (Primitive.Addresses.material1596 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1596_pa_checked.trans (by decide +kernel)
    · exact v1596_pb_checked.trans (by decide +kernel)
    · exact v1596_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 22 Primitive.Addresses.material1596
    · exact v1596_mb_checked.trans (by decide +kernel)
    · exact v1596_mg_checked.trans (by decide +kernel)
  upper_error := v1596_upper_checked
  lower_error := reuse_lower_error 18 22 Primitive.Addresses.material1596

def v1597_pa : Scalar.QComplex := ((999999966893112025857526548689 : Int)/10^30,(-257320373954762695098824677 : Int)/10^30)
theorem v1597_pa_checked : Scalar.distance (sourceCoefficient 18 23 1 0) v1597_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1597_pb : Scalar.QComplex := ((-111027956928964422851175 : Int)/10^30,(-431477506218350088022305098 : Int)/10^30)
theorem v1597_pb_checked : Scalar.distance (sourceCoefficient 18 23 1 1) v1597_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1597_pg : Scalar.QComplex := ((-93086426761517154693370 : Int)/10^30,(23953034937396668297 : Int)/10^30)
theorem v1597_pg_checked : Scalar.distance (sourceCoefficient 18 23 1 2) v1597_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1597_mb : Scalar.QComplex := ((-483373570429125696771986 : Int)/10^30,(-431477249747428710589506877 : Int)/10^30)
theorem v1597_mb_checked : Scalar.distance (sourceCoefficient 18 23 3 1) v1597_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1597_mg : Scalar.QComplex := ((-93086371430795865185976 : Int)/10^30,(104282419856746339564 : Int)/10^30)
theorem v1597_mg_checked : Scalar.distance (sourceCoefficient 18 23 3 2) v1597_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1597_upper : Scalar.QComplex := ((999998033399008062424830754849 : Int)/10^30,(-1983229214275467667793195170 : Int)/10^30)
theorem v1597_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 23 5) 1) 14) v1597_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1597 : Material (18 : Basis) (23 : Basis) where
  plus := ![v1597_pa,v1597_pb,v1597_pg]
  minus := ![(Primitive.Addresses.material1597 1).one,v1597_mb,v1597_mg]
  upper := v1597_upper
  lower := (Primitive.Addresses.material1597 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1597_pa_checked.trans (by decide +kernel)
    · exact v1597_pb_checked.trans (by decide +kernel)
    · exact v1597_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 23 Primitive.Addresses.material1597
    · exact v1597_mb_checked.trans (by decide +kernel)
    · exact v1597_mg_checked.trans (by decide +kernel)
  upper_error := v1597_upper_checked
  lower_error := reuse_lower_error 18 23 Primitive.Addresses.material1597

def v1598_pa : Scalar.QComplex := ((999999952485928131774217064728 : Int)/10^30,(-308266348275098851036344261 : Int)/10^30)
theorem v1598_pa_checked : Scalar.distance (sourceCoefficient 18 24 1 0) v1598_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1598_pb : Scalar.QComplex := ((-133009999362926969499564 : Int)/10^30,(-431477499205918306390040384 : Int)/10^30)
theorem v1598_pb_checked : Scalar.distance (sourceCoefficient 18 24 1 1) v1598_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1598_pg : Scalar.QComplex := ((-93086425334533793134598 : Int)/10^30,(28695413775295331757 : Int)/10^30)
theorem v1598_pg_checked : Scalar.distance (sourceCoefficient 18 24 1 2) v1598_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1598_mb : Scalar.QComplex := ((-505355598626756416941914 : Int)/10^30,(-431477223765486953935820420 : Int)/10^30)
theorem v1598_mb_checked : Scalar.distance (sourceCoefficient 18 24 3 1) v1598_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1598_mg : Scalar.QComplex := ((-93086365911353686665848 : Int)/10^30,(109024795697418252174 : Int)/10^30)
theorem v1598_mg_checked : Scalar.distance (sourceCoefficient 18 24 3 2) v1598_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1598_upper : Scalar.QComplex := ((999997931063715731936295497194 : Int)/10^30,(-2034175087852267216449580524 : Int)/10^30)
theorem v1598_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 24 5) 1) 14) v1598_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1598 : Material (18 : Basis) (24 : Basis) where
  plus := ![v1598_pa,v1598_pb,v1598_pg]
  minus := ![(Primitive.Addresses.material1598 1).one,v1598_mb,v1598_mg]
  upper := v1598_upper
  lower := (Primitive.Addresses.material1598 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1598_pa_checked.trans (by decide +kernel)
    · exact v1598_pb_checked.trans (by decide +kernel)
    · exact v1598_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 24 Primitive.Addresses.material1598
    · exact v1598_mb_checked.trans (by decide +kernel)
    · exact v1598_mg_checked.trans (by decide +kernel)
  upper_error := v1598_upper_checked
  lower_error := reuse_lower_error 18 24 Primitive.Addresses.material1598

def v1599_pa : Scalar.QComplex := ((999999945136489937527373601902 : Int)/10^30,(-331250686210520198555667290 : Int)/10^30)
theorem v1599_pa_checked : Scalar.distance (sourceCoefficient 18 25 1 0) v1599_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1599_pb : Scalar.QComplex := ((-142927224327970222137142 : Int)/10^30,(-431477495553462141304211190 : Int)/10^30)
theorem v1599_pb_checked : Scalar.distance (sourceCoefficient 18 25 1 1) v1599_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1599_pg : Scalar.QComplex := ((-93086424598479110699364 : Int)/10^30,(30834943716843297450 : Int)/10^30)
theorem v1599_pg_checked : Scalar.distance (sourceCoefficient 18 25 1 2) v1599_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1599_mb : Scalar.QComplex := ((-515272816747258405572557 : Int)/10^30,(-431477211554913659225823919 : Int)/10^30)
theorem v1599_mb_checked : Scalar.distance (sourceCoefficient 18 25 3 1) v1599_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1599_mg : Scalar.QComplex := ((-93086363328981299593002 : Int)/10^30,(111164324207139399010 : Int)/10^30)
theorem v1599_mg_checked : Scalar.distance (sourceCoefficient 18 25 3 2) v1599_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1599_upper : Scalar.QComplex := ((999997884045406330126486480033 : Int)/10^30,(-2057159378870753551707114558 : Int)/10^30)
theorem v1599_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 25 5) 1) 14) v1599_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1599 : Material (18 : Basis) (25 : Basis) where
  plus := ![v1599_pa,v1599_pb,v1599_pg]
  minus := ![(Primitive.Addresses.material1599 1).one,v1599_mb,v1599_mg]
  upper := v1599_upper
  lower := (Primitive.Addresses.material1599 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1599_pa_checked.trans (by decide +kernel)
    · exact v1599_pb_checked.trans (by decide +kernel)
    · exact v1599_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 25 Primitive.Addresses.material1599
    · exact v1599_mb_checked.trans (by decide +kernel)
    · exact v1599_mg_checked.trans (by decide +kernel)
  upper_error := v1599_upper_checked
  lower_error := reuse_lower_error 18 25 Primitive.Addresses.material1599

def v1600_pa : Scalar.QComplex := ((999999942676841138551583717096 : Int)/10^30,(-338594616668594261203399510 : Int)/10^30)
theorem v1600_pa_checked : Scalar.distance (sourceCoefficient 18 26 1 0) v1600_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1600_pb : Scalar.QComplex := ((-146095965165888974820568 : Int)/10^30,(-431477494322365061047883495 : Int)/10^30)
theorem v1600_pb_checked : Scalar.distance (sourceCoefficient 18 26 1 1) v1600_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1600_pg : Scalar.QComplex := ((-93086424351201462849700 : Int)/10^30,(31518563976988807507 : Int)/10^30)
theorem v1600_pg_checked : Scalar.distance (sourceCoefficient 18 26 1 2) v1600_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1600_mb : Scalar.QComplex := ((-518441555342928791981365 : Int)/10^30,(-431477207589336409028837401 : Int)/10^30)
theorem v1600_mb_checked : Scalar.distance (sourceCoefficient 18 26 3 1) v1600_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1600_mg : Scalar.QComplex := ((-93086362491770248424103 : Int)/10^30,(111847943999352370104 : Int)/10^30)
theorem v1600_mg_checked : Scalar.distance (sourceCoefficient 18 26 3 2) v1600_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1600_upper : Scalar.QComplex := ((999997868910803460039625045792 : Int)/10^30,(-2064503294145775186288781807 : Int)/10^30)
theorem v1600_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 26 5) 1) 14) v1600_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1600 : Material (18 : Basis) (26 : Basis) where
  plus := ![v1600_pa,v1600_pb,v1600_pg]
  minus := ![(Primitive.Addresses.material1600 1).one,v1600_mb,v1600_mg]
  upper := v1600_upper
  lower := (Primitive.Addresses.material1600 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1600_pa_checked.trans (by decide +kernel)
    · exact v1600_pb_checked.trans (by decide +kernel)
    · exact v1600_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 26 Primitive.Addresses.material1600
    · exact v1600_mb_checked.trans (by decide +kernel)
    · exact v1600_mg_checked.trans (by decide +kernel)
  upper_error := v1600_upper_checked
  lower_error := reuse_lower_error 18 26 Primitive.Addresses.material1600

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
