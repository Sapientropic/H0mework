import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B104

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2497_pa : Scalar.QComplex := ((999999595642614542964133140827 : Int)/10^30,(-899285609475197017659965803 : Int)/10^30)
theorem v2497_pa_checked : Scalar.distance (sourceCoefficient 30 53 1 0) v2497_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2497_pb : Scalar.QComplex := ((-388021518207570675654220 : Int)/10^30,(-431477338478311318933326745 : Int)/10^30)
theorem v2497_pb_checked : Scalar.distance (sourceCoefficient 30 53 1 1) v2497_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2497_pg : Scalar.QComplex := ((-93086391388310589270887 : Int)/10^30,(83711286062760384910 : Int)/10^30)
theorem v2497_pg_checked : Scalar.distance (sourceCoefficient 30 53 1 2) v2497_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2497_mb : Scalar.QComplex := ((-760366883818271127598362 : Int)/10^30,(-431476842974484342239950206 : Int)/10^30)
theorem v2497_mb_checked : Scalar.distance (sourceCoefficient 30 53 3 1) v2497_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2497_mg : Scalar.QComplex := ((-93086284488923161356831 : Int)/10^30,(164040618205897959333 : Int)/10^30)
theorem v2497_mg_checked : Scalar.distance (sourceCoefficient 30 53 3 2) v2497_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2497_upper : Scalar.QComplex := ((999996554175305636498843232794 : Int)/10^30,(-2625192852919415143099918567 : Int)/10^30)
theorem v2497_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 53 5) 1) 14) v2497_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2497 : Material (30 : Basis) (53 : Basis) where
  plus := ![v2497_pa,v2497_pb,v2497_pg]
  minus := ![(Primitive.Addresses.material2497 1).one,v2497_mb,v2497_mg]
  upper := v2497_upper
  lower := (Primitive.Addresses.material2497 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2497_pa_checked.trans (by decide +kernel)
    · exact v2497_pb_checked.trans (by decide +kernel)
    · exact v2497_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 53 Primitive.Addresses.material2497
    · exact v2497_mb_checked.trans (by decide +kernel)
    · exact v2497_mg_checked.trans (by decide +kernel)
  upper_error := v2497_upper_checked
  lower_error := reuse_lower_error 30 53 Primitive.Addresses.material2497

def v2498_pa : Scalar.QComplex := ((999999593947964514242822805818 : Int)/10^30,(-901168078714098057383598529 : Int)/10^30)
theorem v2498_pa_checked : Scalar.distance (sourceCoefficient 30 54 1 0) v2498_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2498_pb : Scalar.QComplex := ((-388833761271106747811156 : Int)/10^30,(-431477337656260599889892513 : Int)/10^30)
theorem v2498_pb_checked : Scalar.distance (sourceCoefficient 30 54 1 1) v2498_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2498_pg : Scalar.QComplex := ((-93086391220762023051498 : Int)/10^30,(83886518393134540494 : Int)/10^30)
theorem v2498_pg_checked : Scalar.distance (sourceCoefficient 30 54 1 2) v2498_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2498_mb : Scalar.QComplex := ((-761179125869979239114498 : Int)/10^30,(-431476841451504747521529385 : Int)/10^30)
theorem v2498_mb_checked : Scalar.distance (sourceCoefficient 30 54 3 1) v2498_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2498_mg : Scalar.QComplex := ((-93086284170157048581724 : Int)/10^30,(164215850326438243265 : Int)/10^30)
theorem v2498_mg_checked : Scalar.distance (sourceCoefficient 30 54 3 2) v2498_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2498_upper : Scalar.QComplex := ((999996549231687001691810588064 : Int)/10^30,(-2627075316429787169727508143 : Int)/10^30)
theorem v2498_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 54 5) 1) 14) v2498_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2498 : Material (30 : Basis) (54 : Basis) where
  plus := ![v2498_pa,v2498_pb,v2498_pg]
  minus := ![(Primitive.Addresses.material2498 1).one,v2498_mb,v2498_mg]
  upper := v2498_upper
  lower := (Primitive.Addresses.material2498 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2498_pa_checked.trans (by decide +kernel)
    · exact v2498_pb_checked.trans (by decide +kernel)
    · exact v2498_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 54 Primitive.Addresses.material2498
    · exact v2498_mb_checked.trans (by decide +kernel)
    · exact v2498_mg_checked.trans (by decide +kernel)
  upper_error := v2498_upper_checked
  lower_error := reuse_lower_error 30 54 Primitive.Addresses.material2498

def v2499_pa : Scalar.QComplex := ((999999580003092637895837496498 : Int)/10^30,(-916511668407340098974699099 : Int)/10^30)
theorem v2499_pa_checked : Scalar.distance (sourceCoefficient 30 55 1 0) v2499_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2499_pb : Scalar.QComplex := ((-395454174494193344220459 : Int)/10^30,(-431477330879878154000122849 : Int)/10^30)
theorem v2499_pb_checked : Scalar.distance (sourceCoefficient 30 55 1 1) v2499_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2499_pg : Scalar.QComplex := ((-93086389840758645522919 : Int)/10^30,(85314798290921214253 : Int)/10^30)
theorem v2499_pg_checked : Scalar.distance (sourceCoefficient 30 55 1 2) v2499_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2499_mb : Scalar.QComplex := ((-767799530780270570870260 : Int)/10^30,(-431476828962006385607797766 : Int)/10^30)
theorem v2499_mb_checked : Scalar.distance (sourceCoefficient 30 55 3 1) v2499_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2499_mg : Scalar.QComplex := ((-93086281557612960440225 : Int)/10^30,(165644128501530273700 : Int)/10^30)
theorem v2499_mg_checked : Scalar.distance (sourceCoefficient 30 55 3 2) v2499_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2499_upper : Scalar.QComplex := ((999996508805192043641220957246 : Int)/10^30,(-2642418859202970958210122193 : Int)/10^30)
theorem v2499_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 55 5) 1) 14) v2499_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2499 : Material (30 : Basis) (55 : Basis) where
  plus := ![v2499_pa,v2499_pb,v2499_pg]
  minus := ![(Primitive.Addresses.material2499 1).one,v2499_mb,v2499_mg]
  upper := v2499_upper
  lower := (Primitive.Addresses.material2499 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2499_pa_checked.trans (by decide +kernel)
    · exact v2499_pb_checked.trans (by decide +kernel)
    · exact v2499_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 55 Primitive.Addresses.material2499
    · exact v2499_mb_checked.trans (by decide +kernel)
    · exact v2499_mg_checked.trans (by decide +kernel)
  upper_error := v2499_upper_checked
  lower_error := reuse_lower_error 30 55 Primitive.Addresses.material2499

def v2500_pa : Scalar.QComplex := ((999999576659018333964076711508 : Int)/10^30,(-920153130796437103887104512 : Int)/10^30)
theorem v2500_pa_checked : Scalar.distance (sourceCoefficient 30 56 1 0) v2500_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2500_pb : Scalar.QComplex := ((-397025383455814084680050 : Int)/10^30,(-431477329251766987587334633 : Int)/10^30)
theorem v2500_pb_checked : Scalar.distance (sourceCoefficient 30 56 1 1) v2500_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2500_pg : Scalar.QComplex := ((-93086389509491325820601 : Int)/10^30,(85653769002445715525 : Int)/10^30)
theorem v2500_pg_checked : Scalar.distance (sourceCoefficient 30 56 1 2) v2500_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2500_mb : Scalar.QComplex := ((-769370737751871797912184 : Int)/10^30,(-431476825978013256161231194 : Int)/10^30)
theorem v2500_mb_checked : Scalar.distance (sourceCoefficient 30 56 3 1) v2500_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2500_mg : Scalar.QComplex := ((-93086280933829306712347 : Int)/10^30,(165983098800971710168 : Int)/10^30)
theorem v2500_mg_checked : Scalar.distance (sourceCoefficient 30 56 3 2) v2500_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2500_upper : Scalar.QComplex := ((999996499176288987621262202815 : Int)/10^30,(-2646060310396968614247818899 : Int)/10^30)
theorem v2500_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 56 5) 1) 14) v2500_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2500 : Material (30 : Basis) (56 : Basis) where
  plus := ![v2500_pa,v2500_pb,v2500_pg]
  minus := ![(Primitive.Addresses.material2500 1).one,v2500_mb,v2500_mg]
  upper := v2500_upper
  lower := (Primitive.Addresses.material2500 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2500_pa_checked.trans (by decide +kernel)
    · exact v2500_pb_checked.trans (by decide +kernel)
    · exact v2500_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 56 Primitive.Addresses.material2500
    · exact v2500_mb_checked.trans (by decide +kernel)
    · exact v2500_mg_checked.trans (by decide +kernel)
  upper_error := v2500_upper_checked
  lower_error := reuse_lower_error 30 56 Primitive.Addresses.material2500

def v2501_pa : Scalar.QComplex := ((999999565752228015073209779208 : Int)/10^30,(-931930982100459039443396666 : Int)/10^30)
theorem v2501_pa_checked : Scalar.distance (sourceCoefficient 30 57 1 0) v2501_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2501_pb : Scalar.QComplex := ((-402107260861706508469105 : Int)/10^30,(-431477323933607116419832693 : Int)/10^30)
theorem v2501_pb_checked : Scalar.distance (sourceCoefficient 30 57 1 1) v2501_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2501_pg : Scalar.QComplex := ((-93086388428187603863125 : Int)/10^30,(86750127059115074145 : Int)/10^30)
theorem v2501_pg_checked : Scalar.distance (sourceCoefficient 30 57 1 2) v2501_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2501_mb : Scalar.QComplex := ((-774452608676216562428101 : Int)/10^30,(-431476816274424043164503287 : Int)/10^30)
theorem v2501_mb_checked : Scalar.distance (sourceCoefficient 30 57 3 1) v2501_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2501_mg : Scalar.QComplex := ((-93086278906418362601878 : Int)/10^30,(167079455516300446314 : Int)/10^30)
theorem v2501_mg_checked : Scalar.distance (sourceCoefficient 30 57 3 2) v2501_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2501_upper : Scalar.QComplex := ((999996467942012040695319144558 : Int)/10^30,(-2657838125335133921947725815 : Int)/10^30)
theorem v2501_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 57 5) 1) 14) v2501_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2501 : Material (30 : Basis) (57 : Basis) where
  plus := ![v2501_pa,v2501_pb,v2501_pg]
  minus := ![(Primitive.Addresses.material2501 1).one,v2501_mb,v2501_mg]
  upper := v2501_upper
  lower := (Primitive.Addresses.material2501 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2501_pa_checked.trans (by decide +kernel)
    · exact v2501_pb_checked.trans (by decide +kernel)
    · exact v2501_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 57 Primitive.Addresses.material2501
    · exact v2501_mb_checked.trans (by decide +kernel)
    · exact v2501_mg_checked.trans (by decide +kernel)
  upper_error := v2501_upper_checked
  lower_error := reuse_lower_error 30 57 Primitive.Addresses.material2501

def v2502_pa : Scalar.QComplex := ((999999559776256649390911013540 : Int)/10^30,(-938321529596477908903545103 : Int)/10^30)
theorem v2502_pa_checked : Scalar.distance (sourceCoefficient 30 58 1 0) v2502_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2502_pb : Scalar.QComplex := ((-404864638071662041284687 : Int)/10^30,(-431477321014627203454041951 : Int)/10^30)
theorem v2502_pb_checked : Scalar.distance (sourceCoefficient 30 58 1 1) v2502_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2502_pg : Scalar.QComplex := ((-93086387835178115408745 : Int)/10^30,(87345000269458284782 : Int)/10^30)
theorem v2502_pg_checked : Scalar.distance (sourceCoefficient 30 58 1 2) v2502_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2502_mb : Scalar.QComplex := ((-777209982340526342698866 : Int)/10^30,(-431476810975952872536187075 : Int)/10^30)
theorem v2502_mb_checked : Scalar.distance (sourceCoefficient 30 58 3 1) v2502_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2502_mg : Scalar.QComplex := ((-93086277800060306520666 : Int)/10^30,(167674327993404693311 : Int)/10^30)
theorem v2502_mg_checked : Scalar.distance (sourceCoefficient 30 58 3 2) v2502_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2502_upper : Scalar.QComplex := ((999996450936544343331926042874 : Int)/10^30,(-2664228652999198541249210855 : Int)/10^30)
theorem v2502_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 58 5) 1) 14) v2502_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2502 : Material (30 : Basis) (58 : Basis) where
  plus := ![v2502_pa,v2502_pb,v2502_pg]
  minus := ![(Primitive.Addresses.material2502 1).one,v2502_mb,v2502_mg]
  upper := v2502_upper
  lower := (Primitive.Addresses.material2502 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2502_pa_checked.trans (by decide +kernel)
    · exact v2502_pb_checked.trans (by decide +kernel)
    · exact v2502_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 58 Primitive.Addresses.material2502
    · exact v2502_mb_checked.trans (by decide +kernel)
    · exact v2502_mg_checked.trans (by decide +kernel)
  upper_error := v2502_upper_checked
  lower_error := reuse_lower_error 30 58 Primitive.Addresses.material2502

def v2503_pa : Scalar.QComplex := ((999999543139488309454725719504 : Int)/10^30,(-955887448740469343345662503 : Int)/10^30)
theorem v2503_pa_checked : Scalar.distance (sourceCoefficient 30 59 1 0) v2503_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2503_pb : Scalar.QComplex := ((-412443936218119041578628 : Int)/10^30,(-431477312870077121021770446 : Int)/10^30)
theorem v2503_pb_checked : Scalar.distance (sourceCoefficient 30 59 1 1) v2503_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2503_pg : Scalar.QComplex := ((-93086386182301820277899 : Int)/10^30,(88980148851786899730 : Int)/10^30)
theorem v2503_pg_checked : Scalar.distance (sourceCoefficient 30 59 1 2) v2503_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2503_mb : Scalar.QComplex := ((-784789270636484347809287 : Int)/10^30,(-431476796290812881216422124 : Int)/10^30)
theorem v2503_mb_checked : Scalar.distance (sourceCoefficient 30 59 3 1) v2503_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2503_mg : Scalar.QComplex := ((-93086274736125044639951 : Int)/10^30,(169309474540534961163 : Int)/10^30)
theorem v2503_mg_checked : Scalar.distance (sourceCoefficient 30 59 3 2) v2503_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2503_upper : Scalar.QComplex := ((999996403982617907115150032463 : Int)/10^30,(-2681794517267263969631467800 : Int)/10^30)
theorem v2503_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 59 5) 1) 14) v2503_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2503 : Material (30 : Basis) (59 : Basis) where
  plus := ![v2503_pa,v2503_pb,v2503_pg]
  minus := ![(Primitive.Addresses.material2503 1).one,v2503_mb,v2503_mg]
  upper := v2503_upper
  lower := (Primitive.Addresses.material2503 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2503_pa_checked.trans (by decide +kernel)
    · exact v2503_pb_checked.trans (by decide +kernel)
    · exact v2503_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 59 Primitive.Addresses.material2503
    · exact v2503_mb_checked.trans (by decide +kernel)
    · exact v2503_mg_checked.trans (by decide +kernel)
  upper_error := v2503_upper_checked
  lower_error := reuse_lower_error 30 59 Primitive.Addresses.material2503

def v2504_pa : Scalar.QComplex := ((999999523564138430616249308785 : Int)/10^30,(-976151369485100559637749513 : Int)/10^30)
theorem v2504_pa_checked : Scalar.distance (sourceCoefficient 30 60 1 0) v2504_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2504_pb : Scalar.QComplex := ((-421187361141964625508007 : Int)/10^30,(-431477303254072941244187389 : Int)/10^30)
theorem v2504_pb_checked : Scalar.distance (sourceCoefficient 30 60 1 1) v2504_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2504_pg : Scalar.QComplex := ((-93086384233929644038324 : Int)/10^30,(90866444742399583956 : Int)/10^30)
theorem v2504_pg_checked : Scalar.distance (sourceCoefficient 30 60 1 2) v2504_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2504_mb : Scalar.QComplex := ((-793532684006574719934771 : Int)/10^30,(-431476779129630361878355637 : Int)/10^30)
theorem v2504_mb_checked : Scalar.distance (sourceCoefficient 30 60 3 1) v2504_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2504_mg : Scalar.QComplex := ((-93086271159965195882848 : Int)/10^30,(171195768047436040664 : Int)/10^30)
theorem v2504_mg_checked : Scalar.distance (sourceCoefficient 30 60 3 2) v2504_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2504_upper : Scalar.QComplex := ((999996349433608306757075241278 : Int)/10^30,(-2702058374045887575131234663 : Int)/10^30)
theorem v2504_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 60 5) 1) 14) v2504_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2504 : Material (30 : Basis) (60 : Basis) where
  plus := ![v2504_pa,v2504_pb,v2504_pg]
  minus := ![(Primitive.Addresses.material2504 1).one,v2504_mb,v2504_mg]
  upper := v2504_upper
  lower := (Primitive.Addresses.material2504 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2504_pa_checked.trans (by decide +kernel)
    · exact v2504_pb_checked.trans (by decide +kernel)
    · exact v2504_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 60 Primitive.Addresses.material2504
    · exact v2504_mb_checked.trans (by decide +kernel)
    · exact v2504_mg_checked.trans (by decide +kernel)
  upper_error := v2504_upper_checked
  lower_error := reuse_lower_error 30 60 Primitive.Addresses.material2504

def v2505_pa : Scalar.QComplex := ((999999517827374075306620419606 : Int)/10^30,(-982010702262936423669116812 : Int)/10^30)
theorem v2505_pa_checked : Scalar.distance (sourceCoefficient 30 61 1 0) v2505_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2505_pb : Scalar.QComplex := ((-423715531109384774053603 : Int)/10^30,(-431477300429566393560630387 : Int)/10^30)
theorem v2505_pb_checked : Scalar.distance (sourceCoefficient 30 61 1 1) v2505_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2505_pg : Scalar.QComplex := ((-93086383662244402683505 : Int)/10^30,(91411869067578706586 : Int)/10^30)
theorem v2505_pg_checked : Scalar.distance (sourceCoefficient 30 61 1 2) v2505_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2505_mb : Scalar.QComplex := ((-796060850595219706936093 : Int)/10^30,(-431476774123428048552566348 : Int)/10^30)
theorem v2505_mb_checked : Scalar.distance (sourceCoefficient 30 61 3 1) v2505_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2505_mg : Scalar.QComplex := ((-93086270117603539762699 : Int)/10^30,(171741191676190144365 : Int)/10^30)
theorem v2505_mg_checked : Scalar.distance (sourceCoefficient 30 61 3 2) v2505_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2505_upper : Scalar.QComplex := ((999996333584175675656693838885 : Int)/10^30,(-2707917688195800710086069430 : Int)/10^30)
theorem v2505_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 61 5) 1) 14) v2505_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2505 : Material (30 : Basis) (61 : Basis) where
  plus := ![v2505_pa,v2505_pb,v2505_pg]
  minus := ![(Primitive.Addresses.material2505 1).one,v2505_mb,v2505_mg]
  upper := v2505_upper
  lower := (Primitive.Addresses.material2505 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2505_pa_checked.trans (by decide +kernel)
    · exact v2505_pb_checked.trans (by decide +kernel)
    · exact v2505_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 61 Primitive.Addresses.material2505
    · exact v2505_mb_checked.trans (by decide +kernel)
    · exact v2505_mg_checked.trans (by decide +kernel)
  upper_error := v2505_upper_checked
  lower_error := reuse_lower_error 30 61 Primitive.Addresses.material2505

def v2506_pa : Scalar.QComplex := ((999999509430921599233969798410 : Int)/10^30,(-990524061365250923618322588 : Int)/10^30)
theorem v2506_pa_checked : Scalar.distance (sourceCoefficient 30 62 1 0) v2506_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2506_pb : Scalar.QComplex := ((-427388853572302472461180 : Int)/10^30,(-431477296290482514332764092 : Int)/10^30)
theorem v2506_pb_checked : Scalar.distance (sourceCoefficient 30 62 1 1) v2506_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2506_pg : Scalar.QComplex := ((-93086382824966076836914 : Int)/10^30,(92204347206187571403 : Int)/10^30)
theorem v2506_pg_checked : Scalar.distance (sourceCoefficient 30 62 1 2) v2506_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2506_mb : Scalar.QComplex := ((-799734168118548602913590 : Int)/10^30,(-431476766814433865299117153 : Int)/10^30)
theorem v2506_mb_checked : Scalar.distance (sourceCoefficient 30 62 3 1) v2506_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2506_mg : Scalar.QComplex := ((-93086268596452583944062 : Int)/10^30,(172533668797189694547 : Int)/10^30)
theorem v2506_mg_checked : Scalar.distance (sourceCoefficient 30 62 3 2) v2506_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2506_upper : Scalar.QComplex := ((999996310494450220423545912486 : Int)/10^30,(-2716431020126951623064627444 : Int)/10^30)
theorem v2506_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 62 5) 1) 14) v2506_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2506 : Material (30 : Basis) (62 : Basis) where
  plus := ![v2506_pa,v2506_pb,v2506_pg]
  minus := ![(Primitive.Addresses.material2506 1).one,v2506_mb,v2506_mg]
  upper := v2506_upper
  lower := (Primitive.Addresses.material2506 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2506_pa_checked.trans (by decide +kernel)
    · exact v2506_pb_checked.trans (by decide +kernel)
    · exact v2506_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 62 Primitive.Addresses.material2506
    · exact v2506_mb_checked.trans (by decide +kernel)
    · exact v2506_mg_checked.trans (by decide +kernel)
  upper_error := v2506_upper_checked
  lower_error := reuse_lower_error 30 62 Primitive.Addresses.material2506

def v2507_pa : Scalar.QComplex := ((999999484563305148484032822460 : Int)/10^30,(-1015319222721625385705319661 : Int)/10^30)
theorem v2507_pa_checked : Scalar.distance (sourceCoefficient 30 63 1 0) v2507_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2507_pb : Scalar.QComplex := ((-438087406417039915508734 : Int)/10^30,(-431477283997830324095701175 : Int)/10^30)
theorem v2507_pb_checked : Scalar.distance (sourceCoefficient 30 63 1 1) v2507_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2507_pg : Scalar.QComplex := ((-93086380341546424494268 : Int)/10^30,(94512440049528226593 : Int)/10^30)
theorem v2507_pg_checked : Scalar.distance (sourceCoefficient 30 63 1 2) v2507_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2507_mb : Scalar.QComplex := ((-810432706371720674173829 : Int)/10^30,(-431476745289416992103055542 : Int)/10^30)
theorem v2507_mb_checked : Scalar.distance (sourceCoefficient 30 63 3 1) v2507_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2507_mg : Scalar.QComplex := ((-93086264121253685131826 : Int)/10^30,(174841758638042588206 : Int)/10^30)
theorem v2507_mg_checked : Scalar.distance (sourceCoefficient 30 63 3 2) v2507_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2507_upper : Scalar.QComplex := ((999996242832671705431741280969 : Int)/10^30,(-2741226101634595867634213017 : Int)/10^30)
theorem v2507_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 63 5) 1) 14) v2507_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2507 : Material (30 : Basis) (63 : Basis) where
  plus := ![v2507_pa,v2507_pb,v2507_pg]
  minus := ![(Primitive.Addresses.material2507 1).one,v2507_mb,v2507_mg]
  upper := v2507_upper
  lower := (Primitive.Addresses.material2507 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2507_pa_checked.trans (by decide +kernel)
    · exact v2507_pb_checked.trans (by decide +kernel)
    · exact v2507_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 63 Primitive.Addresses.material2507
    · exact v2507_mb_checked.trans (by decide +kernel)
    · exact v2507_mg_checked.trans (by decide +kernel)
  upper_error := v2507_upper_checked
  lower_error := reuse_lower_error 30 63 Primitive.Addresses.material2507

def v2508_pa : Scalar.QComplex := ((999999447955262465412994028915 : Int)/10^30,(-1050756475267120003823798145 : Int)/10^30)
theorem v2508_pa_checked : Scalar.distance (sourceCoefficient 30 64 1 0) v2508_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2508_pb : Scalar.QComplex := ((-453377781270674093033330 : Int)/10^30,(-431477265815182931474412100 : Int)/10^30)
theorem v2508_pb_checked : Scalar.distance (sourceCoefficient 30 64 1 1) v2508_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2508_pg : Scalar.QComplex := ((-93086376676339428727257 : Int)/10^30,(97811167047957908268 : Int)/10^30)
theorem v2508_pg_checked : Scalar.distance (sourceCoefficient 30 64 1 2) v2508_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2508_mb : Scalar.QComplex := ((-825723059841243705244757 : Int)/10^30,(-431476713911871523945493242 : Int)/10^30)
theorem v2508_mb_checked : Scalar.distance (sourceCoefficient 30 64 3 1) v2508_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2508_mg : Scalar.QComplex := ((-93086257609395223592936 : Int)/10^30,(178140481245296886542 : Int)/10^30)
theorem v2508_mg_checked : Scalar.distance (sourceCoefficient 30 64 3 2) v2508_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2508_upper : Scalar.QComplex := ((999996145063200494654241583186 : Int)/10^30,(-2776663238218304956048769747 : Int)/10^30)
theorem v2508_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 64 5) 1) 14) v2508_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2508 : Material (30 : Basis) (64 : Basis) where
  plus := ![v2508_pa,v2508_pb,v2508_pg]
  minus := ![(Primitive.Addresses.material2508 1).one,v2508_mb,v2508_mg]
  upper := v2508_upper
  lower := (Primitive.Addresses.material2508 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2508_pa_checked.trans (by decide +kernel)
    · exact v2508_pb_checked.trans (by decide +kernel)
    · exact v2508_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 64 Primitive.Addresses.material2508
    · exact v2508_mb_checked.trans (by decide +kernel)
    · exact v2508_mg_checked.trans (by decide +kernel)
  upper_error := v2508_upper_checked
  lower_error := reuse_lower_error 30 64 Primitive.Addresses.material2508

def v2509_pa : Scalar.QComplex := ((999999409516306317611779368323 : Int)/10^30,(-1086723073599610259267651660 : Int)/10^30)
theorem v2509_pa_checked : Scalar.distance (sourceCoefficient 30 65 1 0) v2509_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2509_pb : Scalar.QComplex := ((-468896556513341303925852 : Int)/10^30,(-431477246622196706833112564 : Int)/10^30)
theorem v2509_pb_checked : Scalar.distance (sourceCoefficient 30 65 1 1) v2509_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2509_pg : Scalar.QComplex := ((-93086372816931205015699 : Int)/10^30,(101159168910694397911 : Int)/10^30)
theorem v2509_pg_checked : Scalar.distance (sourceCoefficient 30 65 1 2) v2509_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2509_mb : Scalar.QComplex := ((-841241812742878958371706 : Int)/10^30,(-431476681326888350999393747 : Int)/10^30)
theorem v2509_mb_checked : Scalar.distance (sourceCoefficient 30 65 3 1) v2509_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2509_mg : Scalar.QComplex := ((-93086250860813617780221 : Int)/10^30,(181488478530923795674 : Int)/10^30)
theorem v2509_mg_checked : Scalar.distance (sourceCoefficient 30 65 3 2) v2509_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2509_upper : Scalar.QComplex := ((999996044549215739597297452274 : Int)/10^30,(-2812629716640620772430581250 : Int)/10^30)
theorem v2509_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 65 5) 1) 14) v2509_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2509 : Material (30 : Basis) (65 : Basis) where
  plus := ![v2509_pa,v2509_pb,v2509_pg]
  minus := ![(Primitive.Addresses.material2509 1).one,v2509_mb,v2509_mg]
  upper := v2509_upper
  lower := (Primitive.Addresses.material2509 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2509_pa_checked.trans (by decide +kernel)
    · exact v2509_pb_checked.trans (by decide +kernel)
    · exact v2509_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 65 Primitive.Addresses.material2509
    · exact v2509_mb_checked.trans (by decide +kernel)
    · exact v2509_mg_checked.trans (by decide +kernel)
  upper_error := v2509_upper_checked
  lower_error := reuse_lower_error 30 65 Primitive.Addresses.material2509

def v2510_pa : Scalar.QComplex := ((999999390248830816227223471596 : Int)/10^30,(-1104310629565367007238719909 : Int)/10^30)
theorem v2510_pa_checked : Scalar.distance (sourceCoefficient 30 66 1 0) v2510_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2510_pb : Scalar.QComplex := ((-476485189734394653469799 : Int)/10^30,(-431477236965949840564092236 : Int)/10^30)
theorem v2510_pb_checked : Scalar.distance (sourceCoefficient 30 66 1 1) v2510_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2510_pg : Scalar.QComplex := ((-93086370878547537740415 : Int)/10^30,(102796331509027402359 : Int)/10^30)
theorem v2510_pg_checked : Scalar.distance (sourceCoefficient 30 66 1 2) v2510_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2510_mb : Scalar.QComplex := ((-848830434805431197670549 : Int)/10^30,(-431476665121996389776183644 : Int)/10^30)
theorem v2510_mb_checked : Scalar.distance (sourceCoefficient 30 66 3 1) v2510_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2510_mg : Scalar.QComplex := ((-93086247509633084958637 : Int)/10^30,(183125638846928539437 : Int)/10^30)
theorem v2510_mg_checked : Scalar.distance (sourceCoefficient 30 66 3 2) v2510_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2510_upper : Scalar.QComplex := ((999995994927242868571649489080 : Int)/10^30,(-2830217213157864105191500979 : Int)/10^30)
theorem v2510_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 66 5) 1) 14) v2510_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2510 : Material (30 : Basis) (66 : Basis) where
  plus := ![v2510_pa,v2510_pb,v2510_pg]
  minus := ![(Primitive.Addresses.material2510 1).one,v2510_mb,v2510_mg]
  upper := v2510_upper
  lower := (Primitive.Addresses.material2510 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2510_pa_checked.trans (by decide +kernel)
    · exact v2510_pb_checked.trans (by decide +kernel)
    · exact v2510_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 66 Primitive.Addresses.material2510
    · exact v2510_mb_checked.trans (by decide +kernel)
    · exact v2510_mg_checked.trans (by decide +kernel)
  upper_error := v2510_upper_checked
  lower_error := reuse_lower_error 30 66 Primitive.Addresses.material2510

def v2511_pa : Scalar.QComplex := ((999999357217091848588049567624 : Int)/10^30,(-1133827766079556233619318185 : Int)/10^30)
theorem v2511_pa_checked : Scalar.distance (sourceCoefficient 30 67 1 0) v2511_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2511_pb : Scalar.QComplex := ((-489221167337946326528568 : Int)/10^30,(-431477220359952759589156270 : Int)/10^30)
theorem v2511_pb_checked : Scalar.distance (sourceCoefficient 30 67 1 1) v2511_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2511_pg : Scalar.QComplex := ((-93086367549865513675084 : Int)/10^30,(105543976013388349523 : Int)/10^30)
theorem v2511_pg_checked : Scalar.distance (sourceCoefficient 30 67 1 2) v2511_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2511_mb : Scalar.QComplex := ((-861566393336568771459624 : Int)/10^30,(-431476637525430427245764740 : Int)/10^30)
theorem v2511_mb_checked : Scalar.distance (sourceCoefficient 30 67 3 1) v2511_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2511_mg : Scalar.QComplex := ((-93086241809858842364940 : Int)/10^30,(185873279455713195575 : Int)/10^30)
theorem v2511_mg_checked : Scalar.distance (sourceCoefficient 30 67 3 2) v2511_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2511_upper : Scalar.QComplex := ((999995910951653248043829497079 : Int)/10^30,(-2859734248699960977914250723 : Int)/10^30)
theorem v2511_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 67 5) 1) 14) v2511_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2511 : Material (30 : Basis) (67 : Basis) where
  plus := ![v2511_pa,v2511_pb,v2511_pg]
  minus := ![(Primitive.Addresses.material2511 1).one,v2511_mb,v2511_mg]
  upper := v2511_upper
  lower := (Primitive.Addresses.material2511 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2511_pa_checked.trans (by decide +kernel)
    · exact v2511_pb_checked.trans (by decide +kernel)
    · exact v2511_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 67 Primitive.Addresses.material2511
    · exact v2511_mb_checked.trans (by decide +kernel)
    · exact v2511_mg_checked.trans (by decide +kernel)
  upper_error := v2511_upper_checked
  lower_error := reuse_lower_error 30 67 Primitive.Addresses.material2511

def v2512_pa : Scalar.QComplex := ((999999300272152873463776787177 : Int)/10^30,(-1182985716158066044672095780 : Int)/10^30)
theorem v2512_pa_checked : Scalar.distance (sourceCoefficient 30 68 1 0) v2512_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2512_pb : Scalar.QComplex := ((-510431711664339867251955 : Int)/10^30,(-431477191591766663570938205 : Int)/10^30)
theorem v2512_pb_checked : Scalar.distance (sourceCoefficient 30 68 1 1) v2512_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2512_pg : Scalar.QComplex := ((-93086361796258428080610 : Int)/10^30,(110119913428065564467 : Int)/10^30)
theorem v2512_pg_checked : Scalar.distance (sourceCoefficient 30 68 1 2) v2512_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2512_mb : Scalar.QComplex := ((-882776904939658359843616 : Int)/10^30,(-431476590453510576714899184 : Int)/10^30)
theorem v2512_mb_checked : Scalar.distance (sourceCoefficient 30 68 3 1) v2512_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2512_mg : Scalar.QComplex := ((-93086232107426002805541 : Int)/10^30,(190449210201455998339 : Int)/10^30)
theorem v2512_mg_checked : Scalar.distance (sourceCoefficient 30 68 3 2) v2512_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2512_upper : Scalar.QComplex := ((999995769164636824603842859644 : Int)/10^30,(-2908892027281679978923994628 : Int)/10^30)
theorem v2512_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 68 5) 1) 14) v2512_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2512 : Material (30 : Basis) (68 : Basis) where
  plus := ![v2512_pa,v2512_pb,v2512_pg]
  minus := ![(Primitive.Addresses.material2512 1).one,v2512_mb,v2512_mg]
  upper := v2512_upper
  lower := (Primitive.Addresses.material2512 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2512_pa_checked.trans (by decide +kernel)
    · exact v2512_pb_checked.trans (by decide +kernel)
    · exact v2512_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 68 Primitive.Addresses.material2512
    · exact v2512_mb_checked.trans (by decide +kernel)
    · exact v2512_mg_checked.trans (by decide +kernel)
  upper_error := v2512_upper_checked
  lower_error := reuse_lower_error 30 68 Primitive.Addresses.material2512

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
