import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B041
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B042

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v993_pa : Scalar.QComplex := ((999999493033143168355813437909 : Int)/10^30,(-1006942628280228509349015156 : Int)/10^30)
theorem v993_pa_checked : Scalar.distance (sourceCoefficient 10 79 1 0) v993_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v993_pb : Scalar.QComplex := ((-434473019248755667622320 : Int)/10^30,(-431477213083506982768991003 : Int)/10^30)
theorem v993_pb_checked : Scalar.distance (sourceCoefficient 10 79 1 1) v993_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v993_pg : Scalar.QComplex := ((-93086373086275331726505 : Int)/10^30,(93732684691932549492 : Int)/10^30)
theorem v993_pg_checked : Scalar.distance (sourceCoefficient 10 79 1 2) v993_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v993_mb : Scalar.QComplex := ((-806818259353370773690159 : Int)/10^30,(-431476677494173395694015137 : Int)/10^30)
theorem v993_mb_checked : Scalar.distance (sourceCoefficient 10 79 3 1) v993_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v993_mg : Scalar.QComplex := ((-93086257538879048560511 : Int)/10^30,(174061997309813279538 : Int)/10^30)
theorem v993_mg_checked : Scalar.distance (sourceCoefficient 10 79 3 2) v993_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v993_upper : Scalar.QComplex := ((999996265759739197614172635963 : Int)/10^30,(-2732849534287324472430137863 : Int)/10^30)
theorem v993_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 79 5) 1) 14) v993_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material993 : Material (10 : Basis) (79 : Basis) where
  plus := ![v993_pa,v993_pb,v993_pg]
  minus := ![(Primitive.Addresses.material993 1).one,v993_mb,v993_mg]
  upper := v993_upper
  lower := (Primitive.Addresses.material993 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v993_pa_checked.trans (by decide +kernel)
    · exact v993_pb_checked.trans (by decide +kernel)
    · exact v993_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 79 Primitive.Addresses.material993
    · exact v993_mb_checked.trans (by decide +kernel)
    · exact v993_mg_checked.trans (by decide +kernel)
  upper_error := v993_upper_checked
  lower_error := reuse_lower_error 10 79 Primitive.Addresses.material993

def v994_pa : Scalar.QComplex := ((999999484222758412731843570616 : Int)/10^30,(-1015654575703951315333779047 : Int)/10^30)
theorem v994_pa_checked : Scalar.distance (sourceCoefficient 10 80 1 0) v994_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v994_pb : Scalar.QComplex := ((-438232026526691566175679 : Int)/10^30,(-431477207881278732009456496 : Int)/10^30)
theorem v994_pb_checked : Scalar.distance (sourceCoefficient 10 80 1 1) v994_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v994_pg : Scalar.QComplex := ((-93086372115050531931119 : Int)/10^30,(94543648537794025622 : Int)/10^30)
theorem v994_pg_checked : Scalar.distance (sourceCoefficient 10 80 1 2) v994_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v994_mb : Scalar.QComplex := ((-810577260742367786805854 : Int)/10^30,(-431476669048093100506240487 : Int)/10^30)
theorem v994_mb_checked : Scalar.distance (sourceCoefficient 10 80 3 1) v994_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v994_mg : Scalar.QComplex := ((-93086255867829335873816 : Int)/10^30,(174872960015592593093 : Int)/10^30)
theorem v994_mg_checked : Scalar.distance (sourceCoefficient 10 80 3 2) v994_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v994_upper : Scalar.QComplex := ((999996241913336652374262255798 : Int)/10^30,(-2741561453529700151666991494 : Int)/10^30)
theorem v994_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 80 5) 1) 14) v994_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material994 : Material (10 : Basis) (80 : Basis) where
  plus := ![v994_pa,v994_pb,v994_pg]
  minus := ![(Primitive.Addresses.material994 1).one,v994_mb,v994_mg]
  upper := v994_upper
  lower := (Primitive.Addresses.material994 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v994_pa_checked.trans (by decide +kernel)
    · exact v994_pb_checked.trans (by decide +kernel)
    · exact v994_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 80 Primitive.Addresses.material994
    · exact v994_mb_checked.trans (by decide +kernel)
    · exact v994_mg_checked.trans (by decide +kernel)
  upper_error := v994_upper_checked
  lower_error := reuse_lower_error 10 80 Primitive.Addresses.material994

def v995_pa : Scalar.QComplex := ((999999457235903576814450122509 : Int)/10^30,(-1041886701255710785107973448 : Int)/10^30)
theorem v995_pa_checked : Scalar.distance (sourceCoefficient 10 81 1 0) v995_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v995_pb : Scalar.QComplex := ((-449550592191348337919693 : Int)/10^30,(-431477191953421429806642091 : Int)/10^30)
theorem v995_pb_checked : Scalar.distance (sourceCoefficient 10 81 1 1) v995_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v995_pg : Scalar.QComplex := ((-93086369140867355093919 : Int)/10^30,(96985502716298429373 : Int)/10^30)
theorem v995_pg_checked : Scalar.distance (sourceCoefficient 10 81 1 2) v995_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v995_mb : Scalar.QComplex := ((-821895808447581789854984 : Int)/10^30,(-431476643352829329647855898 : Int)/10^30)
theorem v995_mb_checked : Scalar.distance (sourceCoefficient 10 81 3 1) v995_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v995_mg : Scalar.QComplex := ((-93086250786437087441300 : Int)/10^30,(177314810718296958566 : Int)/10^30)
theorem v995_mg_checked : Scalar.distance (sourceCoefficient 10 81 3 2) v995_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v995_upper : Scalar.QComplex := ((999996169652253067710595336871 : Int)/10^30,(-2767793493434926835575037686 : Int)/10^30)
theorem v995_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 81 5) 1) 14) v995_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material995 : Material (10 : Basis) (81 : Basis) where
  plus := ![v995_pa,v995_pb,v995_pg]
  minus := ![(Primitive.Addresses.material995 1).one,v995_mb,v995_mg]
  upper := v995_upper
  lower := (Primitive.Addresses.material995 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v995_pa_checked.trans (by decide +kernel)
    · exact v995_pb_checked.trans (by decide +kernel)
    · exact v995_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 81 Primitive.Addresses.material995
    · exact v995_mb_checked.trans (by decide +kernel)
    · exact v995_mg_checked.trans (by decide +kernel)
  upper_error := v995_upper_checked
  lower_error := reuse_lower_error 10 81 Primitive.Addresses.material995

def v996_pa : Scalar.QComplex := ((999999446829875670998868947866 : Int)/10^30,(-1051826954712996415298811015 : Int)/10^30)
theorem v996_pa_checked : Scalar.distance (sourceCoefficient 10 82 1 0) v996_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v996_pb : Scalar.QComplex := ((-453839585433773223242713 : Int)/10^30,(-431477185814380296486655761 : Int)/10^30)
theorem v996_pb_checked : Scalar.distance (sourceCoefficient 10 82 1 1) v996_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v996_pg : Scalar.QComplex := ((-93086367994322762077079 : Int)/10^30,(97910805134094096001 : Int)/10^30)
theorem v996_pg_checked : Scalar.distance (sourceCoefficient 10 82 1 2) v996_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v996_mb : Scalar.QComplex := ((-826184794795302468442246 : Int)/10^30,(-431476633512582483045640832 : Int)/10^30)
theorem v996_mb_checked : Scalar.distance (sourceCoefficient 10 82 3 1) v996_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v996_mg : Scalar.QComplex := ((-93086248841398608851635 : Int)/10^30,(178240111802143901317 : Int)/10^30)
theorem v996_mg_checked : Scalar.distance (sourceCoefficient 10 82 3 2) v996_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v996_upper : Scalar.QComplex := ((999996142090264965925587071935 : Int)/10^30,(-2777733714127512467373542368 : Int)/10^30)
theorem v996_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 82 5) 1) 14) v996_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material996 : Material (10 : Basis) (82 : Basis) where
  plus := ![v996_pa,v996_pb,v996_pg]
  minus := ![(Primitive.Addresses.material996 1).one,v996_mb,v996_mg]
  upper := v996_upper
  lower := (Primitive.Addresses.material996 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v996_pa_checked.trans (by decide +kernel)
    · exact v996_pb_checked.trans (by decide +kernel)
    · exact v996_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 82 Primitive.Addresses.material996
    · exact v996_mb_checked.trans (by decide +kernel)
    · exact v996_mg_checked.trans (by decide +kernel)
  upper_error := v996_upper_checked
  lower_error := reuse_lower_error 10 82 Primitive.Addresses.material996

def v997_pa : Scalar.QComplex := ((999999432465980871460430010544 : Int)/10^30,(-1065395567928746487792934068 : Int)/10^30)
theorem v997_pa_checked : Scalar.distance (sourceCoefficient 10 83 1 0) v997_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v997_pb : Scalar.QComplex := ((-459694133295409194106766 : Int)/10^30,(-431477177342729869020298329 : Int)/10^30)
theorem v997_pb_checked : Scalar.distance (sourceCoefficient 10 83 1 1) v997_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v997_pg : Scalar.QComplex := ((-93086366411949186266752 : Int)/10^30,(99173858494420498568 : Int)/10^30)
theorem v997_pg_checked : Scalar.distance (sourceCoefficient 10 83 1 2) v997_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v997_mb : Scalar.QComplex := ((-832039333166369934431943 : Int)/10^30,(-431476619988724084417529983 : Int)/10^30)
theorem v997_mb_checked : Scalar.distance (sourceCoefficient 10 83 3 1) v997_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v997_mg : Scalar.QComplex := ((-93086246169067458081271 : Int)/10^30,(179503163326660684980 : Int)/10^30)
theorem v997_mg_checked : Scalar.distance (sourceCoefficient 10 83 3 2) v997_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v997_upper : Scalar.QComplex := ((999996104308196084311921816578 : Int)/10^30,(-2791302282343627694634054905 : Int)/10^30)
theorem v997_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 83 5) 1) 14) v997_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material997 : Material (10 : Basis) (83 : Basis) where
  plus := ![v997_pa,v997_pb,v997_pg]
  minus := ![(Primitive.Addresses.material997 1).one,v997_mb,v997_mg]
  upper := v997_upper
  lower := (Primitive.Addresses.material997 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v997_pa_checked.trans (by decide +kernel)
    · exact v997_pb_checked.trans (by decide +kernel)
    · exact v997_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 83 Primitive.Addresses.material997
    · exact v997_mb_checked.trans (by decide +kernel)
    · exact v997_mg_checked.trans (by decide +kernel)
  upper_error := v997_upper_checked
  lower_error := reuse_lower_error 10 83 Primitive.Addresses.material997

def v998_pa : Scalar.QComplex := ((999999394411608771947278382095 : Int)/10^30,(-1100534604507648297807208826 : Int)/10^30)
theorem v998_pa_checked : Scalar.distance (sourceCoefficient 10 84 1 0) v998_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v998_pb : Scalar.QComplex := ((-474855827601371381493923 : Int)/10^30,(-431477154911119937743045902 : Int)/10^30)
theorem v998_pb_checked : Scalar.distance (sourceCoefficient 10 84 1 1) v998_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v998_pg : Scalar.QComplex := ((-93086362221092367429121 : Int)/10^30,(102444824871442265903 : Int)/10^30)
theorem v998_pg_checked : Scalar.distance (sourceCoefficient 10 84 1 2) v998_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v998_mb : Scalar.QComplex := ((-847201002469471319564069 : Int)/10^30,(-431476584473263176771146175 : Int)/10^30)
theorem v998_mb_checked : Scalar.distance (sourceCoefficient 10 84 3 1) v998_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v998_mg : Scalar.QComplex := ((-93086239155515535178269 : Int)/10^30,(182774124869231494129 : Int)/10^30)
theorem v998_mg_checked : Scalar.distance (sourceCoefficient 10 84 3 2) v998_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v998_upper : Scalar.QComplex := ((999996005607091315628108565447 : Int)/10^30,(-2826441200908668263476789263 : Int)/10^30)
theorem v998_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 84 5) 1) 14) v998_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material998 : Material (10 : Basis) (84 : Basis) where
  plus := ![v998_pa,v998_pb,v998_pg]
  minus := ![(Primitive.Addresses.material998 1).one,v998_mb,v998_mg]
  upper := v998_upper
  lower := (Primitive.Addresses.material998 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v998_pa_checked.trans (by decide +kernel)
    · exact v998_pb_checked.trans (by decide +kernel)
    · exact v998_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 84 Primitive.Addresses.material998
    · exact v998_mb_checked.trans (by decide +kernel)
    · exact v998_mg_checked.trans (by decide +kernel)
  upper_error := v998_upper_checked
  lower_error := reuse_lower_error 10 84 Primitive.Addresses.material998

def v999_pa : Scalar.QComplex := ((999999304281857243080371619085 : Int)/10^30,(-1179591370555967188584607858 : Int)/10^30)
theorem v999_pa_checked : Scalar.distance (sourceCoefficient 10 85 1 0) v999_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v999_pb : Scalar.QComplex := ((-508967020028764998746474 : Int)/10^30,(-431477101846962468501007102 : Int)/10^30)
theorem v999_pb_checked : Scalar.distance (sourceCoefficient 10 85 1 1) v999_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v999_pg : Scalar.QComplex := ((-93086352302165857587658 : Int)/10^30,(109803934284756663498 : Int)/10^30)
theorem v999_pg_checked : Scalar.distance (sourceCoefficient 10 85 1 2) v999_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v999_mb : Scalar.QComplex := ((-881312136403731062568431 : Int)/10^30,(-431476501972702711975775195 : Int)/10^30)
theorem v999_mb_checked : Scalar.distance (sourceCoefficient 10 85 3 1) v999_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v999_mg : Scalar.QComplex := ((-93086222886012736900408 : Int)/10^30,(190133222982826283105 : Int)/10^30)
theorem v999_mg_checked : Scalar.distance (sourceCoefficient 10 85 3 2) v999_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v999_upper : Scalar.QComplex := ((999995779032667798831832988666 : Int)/10^30,(-2905497693655446153738575984 : Int)/10^30)
theorem v999_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 85 5) 1) 14) v999_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material999 : Material (10 : Basis) (85 : Basis) where
  plus := ![v999_pa,v999_pb,v999_pg]
  minus := ![(Primitive.Addresses.material999 1).one,v999_mb,v999_mg]
  upper := v999_upper
  lower := (Primitive.Addresses.material999 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v999_pa_checked.trans (by decide +kernel)
    · exact v999_pb_checked.trans (by decide +kernel)
    · exact v999_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 85 Primitive.Addresses.material999
    · exact v999_mb_checked.trans (by decide +kernel)
    · exact v999_mg_checked.trans (by decide +kernel)
  upper_error := v999_upper_checked
  lower_error := reuse_lower_error 10 85 Primitive.Addresses.material999

def v1000_pa : Scalar.QComplex := ((999999286971581072215301623475 : Int)/10^30,(-1194176004383794004769382479 : Int)/10^30)
theorem v1000_pa_checked : Scalar.distance (sourceCoefficient 10 86 1 0) v1000_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1000_pb : Scalar.QComplex := ((-515259956702248965278252 : Int)/10^30,(-431477091664670880540186773 : Int)/10^30)
theorem v1000_pb_checked : Scalar.distance (sourceCoefficient 10 86 1 1) v1000_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1000_pg : Scalar.QComplex := ((-93086350398132405109288 : Int)/10^30,(111161565242466658179 : Int)/10^30)
theorem v1000_pg_checked : Scalar.distance (sourceCoefficient 10 86 1 2) v1000_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1000_mb : Scalar.QComplex := ((-887605061947208057127499 : Int)/10^30,(-431476486359893989477408202 : Int)/10^30)
theorem v1000_mb_checked : Scalar.distance (sourceCoefficient 10 86 3 1) v1000_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1000_mg : Scalar.QComplex := ((-93086219810405622305496 : Int)/10^30,(191490851791933110425 : Int)/10^30)
theorem v1000_mg_checked : Scalar.distance (sourceCoefficient 10 86 3 2) v1000_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1000_upper : Scalar.QComplex := ((999995736550662530405937605453 : Int)/10^30,(-2920082275885207819886675009 : Int)/10^30)
theorem v1000_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 86 5) 1) 14) v1000_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1000 : Material (10 : Basis) (86 : Basis) where
  plus := ![v1000_pa,v1000_pb,v1000_pg]
  minus := ![(Primitive.Addresses.material1000 1).one,v1000_mb,v1000_mg]
  upper := v1000_upper
  lower := (Primitive.Addresses.material1000 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1000_pa_checked.trans (by decide +kernel)
    · exact v1000_pb_checked.trans (by decide +kernel)
    · exact v1000_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 86 Primitive.Addresses.material1000
    · exact v1000_mb_checked.trans (by decide +kernel)
    · exact v1000_mg_checked.trans (by decide +kernel)
  upper_error := v1000_upper_checked
  lower_error := reuse_lower_error 10 86 Primitive.Addresses.material1000

def v1001_pa : Scalar.QComplex := ((999999285817831562573337480457 : Int)/10^30,(-1195141760135040888804680782 : Int)/10^30)
theorem v1001_pa_checked : Scalar.distance (sourceCoefficient 10 87 1 0) v1001_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1001_pb : Scalar.QComplex := ((-515676658266156674148047 : Int)/10^30,(-431477090986106628215226249 : Int)/10^30)
theorem v1001_pb_checked : Scalar.distance (sourceCoefficient 10 87 1 1) v1001_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1001_pg : Scalar.QComplex := ((-93086350271236884001313 : Int)/10^30,(111251463961524764278 : Int)/10^30)
theorem v1001_pg_checked : Scalar.distance (sourceCoefficient 10 87 1 2) v1001_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1001_mb : Scalar.QComplex := ((-888021762770388341195172 : Int)/10^30,(-431476485321735307702332487 : Int)/10^30)
theorem v1001_mb_checked : Scalar.distance (sourceCoefficient 10 87 3 1) v1001_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1001_mg : Scalar.QComplex := ((-93086219605931602787382 : Int)/10^30,(191580750368012695291 : Int)/10^30)
theorem v1001_mg_checked : Scalar.distance (sourceCoefficient 10 87 3 2) v1001_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1001_upper : Scalar.QComplex := ((999995733730107925163577731574 : Int)/10^30,(-2921048028206807971775270774 : Int)/10^30)
theorem v1001_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 87 5) 1) 14) v1001_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1001 : Material (10 : Basis) (87 : Basis) where
  plus := ![v1001_pa,v1001_pb,v1001_pg]
  minus := ![(Primitive.Addresses.material1001 1).one,v1001_mb,v1001_mg]
  upper := v1001_upper
  lower := (Primitive.Addresses.material1001 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1001_pa_checked.trans (by decide +kernel)
    · exact v1001_pb_checked.trans (by decide +kernel)
    · exact v1001_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 87 Primitive.Addresses.material1001
    · exact v1001_mb_checked.trans (by decide +kernel)
    · exact v1001_mg_checked.trans (by decide +kernel)
  upper_error := v1001_upper_checked
  lower_error := reuse_lower_error 10 87 Primitive.Addresses.material1001

def v1002_pa : Scalar.QComplex := ((999999271694306251660106469649 : Int)/10^30,(-1206901345209083873283083508 : Int)/10^30)
theorem v1002_pa_checked : Scalar.distance (sourceCoefficient 10 88 1 0) v1002_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1002_pb : Scalar.QComplex := ((-520750650779627766769344 : Int)/10^30,(-431477082680481130073930022 : Int)/10^30)
theorem v1002_pb_checked : Scalar.distance (sourceCoefficient 10 88 1 1) v1002_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1002_pg : Scalar.QComplex := ((-93086348717959881474293 : Int)/10^30,(112346121310627482019 : Int)/10^30)
theorem v1002_pg_checked : Scalar.distance (sourceCoefficient 10 88 1 2) v1002_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1002_mb : Scalar.QComplex := ((-893095746227199394727884 : Int)/10^30,(-431476472637485887139034043 : Int)/10^30)
theorem v1002_mb_checked : Scalar.distance (sourceCoefficient 10 88 3 1) v1002_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1002_mg : Scalar.QComplex := ((-93086217108015187877577 : Int)/10^30,(192675405969116357467 : Int)/10^30)
theorem v1002_mg_checked : Scalar.distance (sourceCoefficient 10 88 3 2) v1002_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1002_upper : Scalar.QComplex := ((999995699310626633008407396880 : Int)/10^30,(-2932807571390406955937138976 : Int)/10^30)
theorem v1002_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 88 5) 1) 14) v1002_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1002 : Material (10 : Basis) (88 : Basis) where
  plus := ![v1002_pa,v1002_pb,v1002_pg]
  minus := ![(Primitive.Addresses.material1002 1).one,v1002_mb,v1002_mg]
  upper := v1002_upper
  lower := (Primitive.Addresses.material1002 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1002_pa_checked.trans (by decide +kernel)
    · exact v1002_pb_checked.trans (by decide +kernel)
    · exact v1002_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 88 Primitive.Addresses.material1002
    · exact v1002_mb_checked.trans (by decide +kernel)
    · exact v1002_mg_checked.trans (by decide +kernel)
  upper_error := v1002_upper_checked
  lower_error := reuse_lower_error 10 88 Primitive.Addresses.material1002

def v1003_pa : Scalar.QComplex := ((999999252146450070760771443437 : Int)/10^30,(-1222990817861502309058559037 : Int)/10^30)
theorem v1003_pa_checked : Scalar.distance (sourceCoefficient 10 89 1 0) v1003_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1003_pb : Scalar.QComplex := ((-527692890817489433305153 : Int)/10^30,(-431477071187828281043499866 : Int)/10^30)
theorem v1003_pb_checked : Scalar.distance (sourceCoefficient 10 89 1 1) v1003_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1003_pg : Scalar.QComplex := ((-93086346568434395374552 : Int)/10^30,(113843832259982923298 : Int)/10^30)
theorem v1003_pg_checked : Scalar.distance (sourceCoefficient 10 89 1 2) v1003_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1003_mb : Scalar.QComplex := ((-900037973762506020280787 : Int)/10^30,(-431476455153996831558446498 : Int)/10^30)
theorem v1003_mb_checked : Scalar.distance (sourceCoefficient 10 89 3 1) v1003_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1003_mg : Scalar.QComplex := ((-93086213666033407247801 : Int)/10^30,(194173114505861880059 : Int)/10^30)
theorem v1003_mg_checked : Scalar.distance (sourceCoefficient 10 89 3 2) v1003_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1003_upper : Scalar.QComplex := ((999995651993829393827439452285 : Int)/10^30,(-2948896986341619477586213433 : Int)/10^30)
theorem v1003_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 89 5) 1) 14) v1003_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1003 : Material (10 : Basis) (89 : Basis) where
  plus := ![v1003_pa,v1003_pb,v1003_pg]
  minus := ![(Primitive.Addresses.material1003 1).one,v1003_mb,v1003_mg]
  upper := v1003_upper
  lower := (Primitive.Addresses.material1003 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1003_pa_checked.trans (by decide +kernel)
    · exact v1003_pb_checked.trans (by decide +kernel)
    · exact v1003_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 89 Primitive.Addresses.material1003
    · exact v1003_mb_checked.trans (by decide +kernel)
    · exact v1003_mg_checked.trans (by decide +kernel)
  upper_error := v1003_upper_checked
  lower_error := reuse_lower_error 10 89 Primitive.Addresses.material1003

def v1004_pa : Scalar.QComplex := ((999999219757196177396117663661 : Int)/10^30,(-1249193739524167983537899434 : Int)/10^30)
theorem v1004_pa_checked : Scalar.distance (sourceCoefficient 10 90 1 0) v1004_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1004_pb : Scalar.QComplex := ((-538998852847101577921435 : Int)/10^30,(-431477052152403494364790809 : Int)/10^30)
theorem v1004_pb_checked : Scalar.distance (sourceCoefficient 10 90 1 1) v1004_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1004_pg : Scalar.QComplex := ((-93086343007594791563412 : Int)/10^30,(116282967649235439232 : Int)/10^30)
theorem v1004_pg_checked : Scalar.distance (sourceCoefficient 10 90 1 2) v1004_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1004_mb : Scalar.QComplex := ((-911343915155677526085137 : Int)/10^30,(-431476426362043102710427413 : Int)/10^30)
theorem v1004_mb_checked : Scalar.distance (sourceCoefficient 10 90 3 1) v1004_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1004_mg : Scalar.QComplex := ((-93086208000331142955002 : Int)/10^30,(196612245914068612753 : Int)/10^30)
theorem v1004_mg_checked : Scalar.distance (sourceCoefficient 10 90 3 2) v1004_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1004_upper : Scalar.QComplex := ((999995574380758061175065621246 : Int)/10^30,(-2975099813077197457134874192 : Int)/10^30)
theorem v1004_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 90 5) 1) 14) v1004_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1004 : Material (10 : Basis) (90 : Basis) where
  plus := ![v1004_pa,v1004_pb,v1004_pg]
  minus := ![(Primitive.Addresses.material1004 1).one,v1004_mb,v1004_mg]
  upper := v1004_upper
  lower := (Primitive.Addresses.material1004 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1004_pa_checked.trans (by decide +kernel)
    · exact v1004_pb_checked.trans (by decide +kernel)
    · exact v1004_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 90 Primitive.Addresses.material1004
    · exact v1004_mb_checked.trans (by decide +kernel)
    · exact v1004_mg_checked.trans (by decide +kernel)
  upper_error := v1004_upper_checked
  lower_error := reuse_lower_error 10 90 Primitive.Addresses.material1004

def v1005_pa : Scalar.QComplex := ((999999201208814187992972641621 : Int)/10^30,(-1263954798858193157880605612 : Int)/10^30)
theorem v1005_pa_checked : Scalar.distance (sourceCoefficient 10 91 1 0) v1005_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1005_pb : Scalar.QComplex := ((-545367912526626248074707 : Int)/10^30,(-431477041255120938687470153 : Int)/10^30)
theorem v1005_pb_checked : Scalar.distance (sourceCoefficient 10 91 1 1) v1005_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1005_pg : Scalar.QComplex := ((-93086340968810274849415 : Int)/10^30,(117657021359069386679 : Int)/10^30)
theorem v1005_pg_checked : Scalar.distance (sourceCoefficient 10 91 1 2) v1005_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1005_mb : Scalar.QComplex := ((-917712963059846146981954 : Int)/10^30,(-431476409968552952959168768 : Int)/10^30)
theorem v1005_mb_checked : Scalar.distance (sourceCoefficient 10 91 3 1) v1005_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1005_mg : Scalar.QComplex := ((-93086204775800918868769 : Int)/10^30,(197986297352900352194 : Int)/10^30)
theorem v1005_mg_checked : Scalar.distance (sourceCoefficient 10 91 3 2) v1005_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1005_upper : Scalar.QComplex := ((999995530356154399722804195666 : Int)/10^30,(-2989860818413534091639961702 : Int)/10^30)
theorem v1005_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 91 5) 1) 14) v1005_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1005 : Material (10 : Basis) (91 : Basis) where
  plus := ![v1005_pa,v1005_pb,v1005_pg]
  minus := ![(Primitive.Addresses.material1005 1).one,v1005_mb,v1005_mg]
  upper := v1005_upper
  lower := (Primitive.Addresses.material1005 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1005_pa_checked.trans (by decide +kernel)
    · exact v1005_pb_checked.trans (by decide +kernel)
    · exact v1005_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 91 Primitive.Addresses.material1005
    · exact v1005_mb_checked.trans (by decide +kernel)
    · exact v1005_mg_checked.trans (by decide +kernel)
  upper_error := v1005_upper_checked
  lower_error := reuse_lower_error 10 91 Primitive.Addresses.material1005

def v1006_pa : Scalar.QComplex := ((999999160307146479899725415978 : Int)/10^30,(-1295910877319930630282498865 : Int)/10^30)
theorem v1006_pa_checked : Scalar.distance (sourceCoefficient 10 92 1 0) v1006_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1006_pb : Scalar.QComplex := ((-559156229466928869790998 : Int)/10^30,(-431477017234261759413682265 : Int)/10^30)
theorem v1006_pb_checked : Scalar.distance (sourceCoefficient 10 92 1 1) v1006_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1006_pg : Scalar.QComplex := ((-93086336473999811957155 : Int)/10^30,(120631697260093451611 : Int)/10^30)
theorem v1006_pg_checked : Scalar.distance (sourceCoefficient 10 92 1 2) v1006_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1006_mb : Scalar.QComplex := ((-931501254137208602232659 : Int)/10^30,(-431476374049006201010184115 : Int)/10^30)
theorem v1006_mb_checked : Scalar.distance (sourceCoefficient 10 92 3 1) v1006_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1006_mg : Scalar.QComplex := ((-93086197713980801445317 : Int)/10^30,(200960968267497639042 : Int)/10^30)
theorem v1006_mg_checked : Scalar.distance (sourceCoefficient 10 92 3 2) v1006_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1006_upper : Scalar.QComplex := ((999995434301255217692130840329 : Int)/10^30,(-3021816778687878626091955199 : Int)/10^30)
theorem v1006_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 92 5) 1) 14) v1006_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1006 : Material (10 : Basis) (92 : Basis) where
  plus := ![v1006_pa,v1006_pb,v1006_pg]
  minus := ![(Primitive.Addresses.material1006 1).one,v1006_mb,v1006_mg]
  upper := v1006_upper
  lower := (Primitive.Addresses.material1006 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1006_pa_checked.trans (by decide +kernel)
    · exact v1006_pb_checked.trans (by decide +kernel)
    · exact v1006_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 92 Primitive.Addresses.material1006
    · exact v1006_mb_checked.trans (by decide +kernel)
    · exact v1006_mg_checked.trans (by decide +kernel)
  upper_error := v1006_upper_checked
  lower_error := reuse_lower_error 10 92 Primitive.Addresses.material1006

def v1007_pa : Scalar.QComplex := ((999999110439758353210880774148 : Int)/10^30,(-1333836456232980130700361379 : Int)/10^30)
theorem v1007_pa_checked : Scalar.distance (sourceCoefficient 10 93 1 0) v1007_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1007_pb : Scalar.QComplex := ((-575520248531729653157204 : Int)/10^30,(-431476987963862288977370559 : Int)/10^30)
theorem v1007_pb_checked : Scalar.distance (sourceCoefficient 10 93 1 1) v1007_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1007_pg : Scalar.QComplex := ((-93086330995631201392913 : Int)/10^30,(124162052308568193682 : Int)/10^30)
theorem v1007_pg_checked : Scalar.distance (sourceCoefficient 10 93 1 2) v1007_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1007_mb : Scalar.QComplex := ((-947865241849900762025007 : Int)/10^30,(-431476330657206184417895978 : Int)/10^30)
theorem v1007_mb_checked : Scalar.distance (sourceCoefficient 10 93 3 1) v1007_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1007_mg : Scalar.QComplex := ((-93086189189076825183357 : Int)/10^30,(204491317273874477016 : Int)/10^30)
theorem v1007_mg_checked : Scalar.distance (sourceCoefficient 10 93 3 2) v1007_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1007_upper : Scalar.QComplex := ((999995318977832740339271269620 : Int)/10^30,(-3059742215048645414418882611 : Int)/10^30)
theorem v1007_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 93 5) 1) 14) v1007_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1007 : Material (10 : Basis) (93 : Basis) where
  plus := ![v1007_pa,v1007_pb,v1007_pg]
  minus := ![(Primitive.Addresses.material1007 1).one,v1007_mb,v1007_mg]
  upper := v1007_upper
  lower := (Primitive.Addresses.material1007 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1007_pa_checked.trans (by decide +kernel)
    · exact v1007_pb_checked.trans (by decide +kernel)
    · exact v1007_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 93 Primitive.Addresses.material1007
    · exact v1007_mb_checked.trans (by decide +kernel)
    · exact v1007_mg_checked.trans (by decide +kernel)
  upper_error := v1007_upper_checked
  lower_error := reuse_lower_error 10 93 Primitive.Addresses.material1007

def v1008_pa : Scalar.QComplex := ((999999049682354713182766531470 : Int)/10^30,(-1378634972525362684321949961 : Int)/10^30)
theorem v1008_pa_checked : Scalar.distance (sourceCoefficient 10 94 1 0) v1008_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1008_pb : Scalar.QComplex := ((-594849781607413601244874 : Int)/10^30,(-431476952323017056624197254 : Int)/10^30)
theorem v1008_pb_checked : Scalar.distance (sourceCoefficient 10 94 1 1) v1008_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1008_pg : Scalar.QComplex := ((-93086324323230175243389 : Int)/10^30,(128332184132182471826 : Int)/10^30)
theorem v1008_pg_checked : Scalar.distance (sourceCoefficient 10 94 1 2) v1008_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1008_mb : Scalar.QComplex := ((-967194736971871911293475 : Int)/10^30,(-431476278335857748317679370 : Int)/10^30)
theorem v1008_mb_checked : Scalar.distance (sourceCoefficient 10 94 3 1) v1008_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1008_mg : Scalar.QComplex := ((-93086178918042335459844 : Int)/10^30,(208661441786776521009 : Int)/10^30)
theorem v1008_mg_checked : Scalar.distance (sourceCoefficient 10 94 3 2) v1008_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1008_upper : Scalar.QComplex := ((999995180902344560325644125815 : Int)/10^30,(-3104540559757133539837380299 : Int)/10^30)
theorem v1008_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 94 5) 1) 14) v1008_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1008 : Material (10 : Basis) (94 : Basis) where
  plus := ![v1008_pa,v1008_pb,v1008_pg]
  minus := ![(Primitive.Addresses.material1008 1).one,v1008_mb,v1008_mg]
  upper := v1008_upper
  lower := (Primitive.Addresses.material1008 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1008_pa_checked.trans (by decide +kernel)
    · exact v1008_pb_checked.trans (by decide +kernel)
    · exact v1008_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 94 Primitive.Addresses.material1008
    · exact v1008_mb_checked.trans (by decide +kernel)
    · exact v1008_mg_checked.trans (by decide +kernel)
  upper_error := v1008_upper_checked
  lower_error := reuse_lower_error 10 94 Primitive.Addresses.material1008

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
