import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B140

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3361_pa : Scalar.QComplex := ((999998628279557727658278155112 : Int)/10^30,(-1656332998804199304859306049 : Int)/10^30)
theorem v3361_pa_checked : Scalar.distance (sourceCoefficient 44 84 1 0) v3361_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3361_pb : Scalar.QComplex := ((-714670405741908889326120 : Int)/10^30,(-431476898624771843218486135 : Int)/10^30)
theorem v3361_pb_checked : Scalar.distance (sourceCoefficient 44 84 1 1) v3361_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3361_pg : Scalar.QComplex := ((-93086298917392991180854 : Int)/10^30,(154182120128195637044 : Int)/10^30)
theorem v3361_pg_checked : Scalar.distance (sourceCoefficient 44 84 1 2) v3361_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3361_mb : Scalar.QComplex := ((-1087015270152505621072798 : Int)/10^30,(-431476121237830421736115755 : Int)/10^30)
theorem v3361_mb_checked : Scalar.distance (sourceCoefficient 44 84 3 1) v3361_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3361_mg : Scalar.QComplex := ((-93086131204884084490954 : Int)/10^30,(234511346233583861058 : Int)/10^30)
theorem v3361_mg_checked : Scalar.distance (sourceCoefficient 44 84 3 2) v3361_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3361_upper : Scalar.QComplex := ((999994280218574415644282199332 : Int)/10^30,(-3382237445134382485789475824 : Int)/10^30)
theorem v3361_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 84 5) 1) 14) v3361_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3361 : Material (44 : Basis) (84 : Basis) where
  plus := ![v3361_pa,v3361_pb,v3361_pg]
  minus := ![(Primitive.Addresses.material3361 1).one,v3361_mb,v3361_mg]
  upper := v3361_upper
  lower := (Primitive.Addresses.material3361 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3361_pa_checked.trans (by decide +kernel)
    · exact v3361_pb_checked.trans (by decide +kernel)
    · exact v3361_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 84 Primitive.Addresses.material3361
    · exact v3361_mb_checked.trans (by decide +kernel)
    · exact v3361_mg_checked.trans (by decide +kernel)
  upper_error := v3361_upper_checked
  lower_error := reuse_lower_error 44 84 Primitive.Addresses.material3361

def v3362_pa : Scalar.QComplex := ((999998494210156444190011511213 : Int)/10^30,(-1735389702547692029823652738 : Int)/10^30)
theorem v3362_pa_checked : Scalar.distance (sourceCoefficient 44 85 1 0) v3362_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3362_pb : Scalar.QComplex := ((-748781580247216324870955 : Int)/10^30,(-431476832921301572007573338 : Int)/10^30)
theorem v3362_pb_checked : Scalar.distance (sourceCoefficient 44 85 1 1) v3362_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3362_pg : Scalar.QComplex := ((-93086285589979075280457 : Int)/10^30,(161541224708398779814 : Int)/10^30)
theorem v3362_pg_checked : Scalar.distance (sourceCoefficient 44 85 1 2) v3362_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3362_mb : Scalar.QComplex := ((-1121126375257528160998989 : Int)/10^30,(-431476026097977327118866099 : Int)/10^30)
theorem v3362_mb_checked : Scalar.distance (sourceCoefficient 44 85 3 1) v3362_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3362_mg : Scalar.QComplex := ((-93086111526899320047133 : Int)/10^30,(241870436572698075944 : Int)/10^30)
theorem v3362_mg_checked : Scalar.distance (sourceCoefficient 44 85 3 2) v3362_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3362_upper : Scalar.QComplex := ((999994009704674119671154900158 : Int)/10^30,(-3461293799740577703403453871 : Int)/10^30)
theorem v3362_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 85 5) 1) 14) v3362_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3362 : Material (44 : Basis) (85 : Basis) where
  plus := ![v3362_pa,v3362_pb,v3362_pg]
  minus := ![(Primitive.Addresses.material3362 1).one,v3362_mb,v3362_mg]
  upper := v3362_upper
  lower := (Primitive.Addresses.material3362 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3362_pa_checked.trans (by decide +kernel)
    · exact v3362_pb_checked.trans (by decide +kernel)
    · exact v3362_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 85 Primitive.Addresses.material3362
    · exact v3362_mb_checked.trans (by decide +kernel)
    · exact v3362_mg_checked.trans (by decide +kernel)
  upper_error := v3362_upper_checked
  lower_error := reuse_lower_error 44 85 Primitive.Addresses.material3362

def v3363_pa : Scalar.QComplex := ((999998468793759495960753625150 : Int)/10^30,(-1749974324501798950389691245 : Int)/10^30)
theorem v3363_pa_checked : Scalar.distance (sourceCoefficient 44 86 1 0) v3363_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3363_pb : Scalar.QComplex := ((-755074513505205177754762 : Int)/10^30,(-431476820407270979728547786 : Int)/10^30)
theorem v3363_pb_checked : Scalar.distance (sourceCoefficient 44 86 1 1) v3363_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3363_pg : Scalar.QComplex := ((-93086283057137460180002 : Int)/10^30,(162898854745040335954 : Int)/10^30)
theorem v3363_pg_checked : Scalar.distance (sourceCoefficient 44 86 1 2) v3363_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3363_mb : Scalar.QComplex := ((-1127419295373325570554718 : Int)/10^30,(-431476008153433415933745815 : Int)/10^30)
theorem v3363_mb_checked : Scalar.distance (sourceCoefficient 44 86 3 1) v3363_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3363_mg : Scalar.QComplex := ((-93086107822485071804733 : Int)/10^30,(243228063918103683804 : Int)/10^30)
theorem v3363_mg_checked : Scalar.distance (sourceCoefficient 44 86 3 2) v3363_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3363_upper : Scalar.QComplex := ((999993959116580639959122058148 : Int)/10^30,(-3475878356106208078245665086 : Int)/10^30)
theorem v3363_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 86 5) 1) 14) v3363_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3363 : Material (44 : Basis) (86 : Basis) where
  plus := ![v3363_pa,v3363_pb,v3363_pg]
  minus := ![(Primitive.Addresses.material3363 1).one,v3363_mb,v3363_mg]
  upper := v3363_upper
  lower := (Primitive.Addresses.material3363 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3363_pa_checked.trans (by decide +kernel)
    · exact v3363_pb_checked.trans (by decide +kernel)
    · exact v3363_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 86 Primitive.Addresses.material3363
    · exact v3363_mb_checked.trans (by decide +kernel)
    · exact v3363_mg_checked.trans (by decide +kernel)
  upper_error := v3363_upper_checked
  lower_error := reuse_lower_error 44 86 Primitive.Addresses.material3363

def v3364_pa : Scalar.QComplex := ((999998467103244179474224425334 : Int)/10^30,(-1750940079462626141314881151 : Int)/10^30)
theorem v3364_pa_checked : Scalar.distance (sourceCoefficient 44 87 1 0) v3364_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3364_pb : Scalar.QComplex := ((-755491214841747358463596 : Int)/10^30,(-431476819574305158466098604 : Int)/10^30)
theorem v3364_pb_checked : Scalar.distance (sourceCoefficient 44 87 1 1) v3364_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3364_pg : Scalar.QComplex := ((-93086282888603931236997 : Int)/10^30,(162988753402783989781 : Int)/10^30)
theorem v3364_pg_checked : Scalar.distance (sourceCoefficient 44 87 1 2) v3364_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3364_mb : Scalar.QComplex := ((-1127835995835898811115475 : Int)/10^30,(-431476006960873418918152698 : Int)/10^30)
theorem v3364_mb_checked : Scalar.distance (sourceCoefficient 44 87 3 1) v3364_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3364_mg : Scalar.QComplex := ((-93086107576373112866933 : Int)/10^30,(243317962396937113772 : Int)/10^30)
theorem v3364_mg_checked : Scalar.distance (sourceCoefficient 44 87 3 2) v3364_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3364_upper : Scalar.QComplex := ((999993955759262391514497475177 : Int)/10^30,(-3476844106710980626661329200 : Int)/10^30)
theorem v3364_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 87 5) 1) 14) v3364_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3364 : Material (44 : Basis) (87 : Basis) where
  plus := ![v3364_pa,v3364_pb,v3364_pg]
  minus := ![(Primitive.Addresses.material3364 1).one,v3364_mb,v3364_mg]
  upper := v3364_upper
  lower := (Primitive.Addresses.material3364 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3364_pa_checked.trans (by decide +kernel)
    · exact v3364_pb_checked.trans (by decide +kernel)
    · exact v3364_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 87 Primitive.Addresses.material3364
    · exact v3364_mb_checked.trans (by decide +kernel)
    · exact v3364_mg_checked.trans (by decide +kernel)
  upper_error := v3364_upper_checked
  lower_error := reuse_lower_error 44 87 Primitive.Addresses.material3364

def v3365_pa : Scalar.QComplex := ((999998446443756591230157493870 : Int)/10^30,(-1762699654870488210206904749 : Int)/10^30)
theorem v3365_pa_checked : Scalar.distance (sourceCoefficient 44 88 1 0) v3365_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3365_pb : Scalar.QComplex := ((-760565204574725574367811 : Int)/10^30,(-431476809388599342338186390 : Int)/10^30)
theorem v3365_pb_checked : Scalar.distance (sourceCoefficient 44 88 1 1) v3365_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3365_pg : Scalar.QComplex := ((-93086280828319133449498 : Int)/10^30,(164083410002061528430 : Int)/10^30)
theorem v3365_pg_checked : Scalar.distance (sourceCoefficient 44 88 1 2) v3365_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3365_mb : Scalar.QComplex := ((-1132909974889793384487442 : Int)/10^30,(-431475992396546779848188424 : Int)/10^30)
theorem v3365_mb_checked : Scalar.distance (sourceCoefficient 44 88 3 1) v3365_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3365_mg : Scalar.QComplex := ((-93086104571449738544181 : Int)/10^30,(244412616810690983523 : Int)/10^30)
theorem v3365_mg_checked : Scalar.distance (sourceCoefficient 44 88 3 2) v3365_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3365_upper : Scalar.QComplex := ((999993914803845239527886461713 : Int)/10^30,(-3488603628947935139070822897 : Int)/10^30)
theorem v3365_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 88 5) 1) 14) v3365_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3365 : Material (44 : Basis) (88 : Basis) where
  plus := ![v3365_pa,v3365_pb,v3365_pg]
  minus := ![(Primitive.Addresses.material3365 1).one,v3365_mb,v3365_mg]
  upper := v3365_upper
  lower := (Primitive.Addresses.material3365 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3365_pa_checked.trans (by decide +kernel)
    · exact v3365_pb_checked.trans (by decide +kernel)
    · exact v3365_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 88 Primitive.Addresses.material3365
    · exact v3365_mb_checked.trans (by decide +kernel)
    · exact v3365_mg_checked.trans (by decide +kernel)
  upper_error := v3365_upper_checked
  lower_error := reuse_lower_error 44 88 Primitive.Addresses.material3365

def v3366_pa : Scalar.QComplex := ((999998417953392213885786015114 : Int)/10^30,(-1778789114173110522079770557 : Int)/10^30)
theorem v3366_pa_checked : Scalar.distance (sourceCoefficient 44 89 1 0) v3366_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3366_pb : Scalar.QComplex := ((-767507440772496387486156 : Int)/10^30,(-431476795323619283995967183 : Int)/10^30)
theorem v3366_pb_checked : Scalar.distance (sourceCoefficient 44 89 1 1) v3366_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3366_pg : Scalar.QComplex := ((-93086277985105225577952 : Int)/10^30,(165581119915846319874 : Int)/10^30)
theorem v3366_pg_checked : Scalar.distance (sourceCoefficient 44 89 1 2) v3366_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3366_mb : Scalar.QComplex := ((-1139852196365208058144963 : Int)/10^30,(-431475972340734786576248244 : Int)/10^30)
theorem v3366_mb_checked : Scalar.distance (sourceCoefficient 44 89 3 1) v3366_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3366_mg : Scalar.QComplex := ((-93086100435780688085333 : Int)/10^30,(245910323713244376448 : Int)/10^30)
theorem v3366_mg_checked : Scalar.distance (sourceCoefficient 44 89 3 2) v3366_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3366_upper : Scalar.QComplex := ((999993858544576163254405677869 : Int)/10^30,(-3504693015115413530712685781 : Int)/10^30)
theorem v3366_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 89 5) 1) 14) v3366_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3366 : Material (44 : Basis) (89 : Basis) where
  plus := ![v3366_pa,v3366_pb,v3366_pg]
  minus := ![(Primitive.Addresses.material3366 1).one,v3366_mb,v3366_mg]
  upper := v3366_upper
  lower := (Primitive.Addresses.material3366 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3366_pa_checked.trans (by decide +kernel)
    · exact v3366_pb_checked.trans (by decide +kernel)
    · exact v3366_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 89 Primitive.Addresses.material3366
    · exact v3366_mb_checked.trans (by decide +kernel)
    · exact v3366_mg_checked.trans (by decide +kernel)
  upper_error := v3366_upper_checked
  lower_error := reuse_lower_error 44 89 Primitive.Addresses.material3366

def v3367_pa : Scalar.QComplex := ((999998371000588263646777446782 : Int)/10^30,(-1804992013786660222773725104 : Int)/10^30)
theorem v3367_pa_checked : Scalar.distance (sourceCoefficient 44 90 1 0) v3367_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3367_pb : Scalar.QComplex := ((-778813396459644016942981 : Int)/10^30,(-431476772098965358762824795 : Int)/10^30)
theorem v3367_pb_checked : Scalar.distance (sourceCoefficient 44 90 1 1) v3367_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3367_pg : Scalar.QComplex := ((-93086273294541633220024 : Int)/10^30,(168020253594704378511 : Int)/10^30)
theorem v3367_pg_checked : Scalar.distance (sourceCoefficient 44 90 1 2) v3367_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3367_mb : Scalar.QComplex := ((-1151158127800801339683206 : Int)/10^30,(-431475939359558952276483927 : Int)/10^30)
theorem v3367_mb_checked : Scalar.distance (sourceCoefficient 44 90 3 1) v3367_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3367_mg : Scalar.QComplex := ((-93086093640356331887000 : Int)/10^30,(248349452436156367469 : Int)/10^30)
theorem v3367_mg_checked : Scalar.distance (sourceCoefficient 44 90 3 2) v3367_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3367_upper : Scalar.QComplex := ((999993766368014519198622586743 : Int)/10^30,(-3530895794666542172819547318 : Int)/10^30)
theorem v3367_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 90 5) 1) 14) v3367_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3367 : Material (44 : Basis) (90 : Basis) where
  plus := ![v3367_pa,v3367_pb,v3367_pg]
  minus := ![(Primitive.Addresses.material3367 1).one,v3367_mb,v3367_mg]
  upper := v3367_upper
  lower := (Primitive.Addresses.material3367 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3367_pa_checked.trans (by decide +kernel)
    · exact v3367_pb_checked.trans (by decide +kernel)
    · exact v3367_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 90 Primitive.Addresses.material3367
    · exact v3367_mb_checked.trans (by decide +kernel)
    · exact v3367_mg_checked.trans (by decide +kernel)
  upper_error := v3367_upper_checked
  lower_error := reuse_lower_error 44 90 Primitive.Addresses.material3367

def v3368_pa : Scalar.QComplex := ((999998344248028585682757260627 : Int)/10^30,(-1819753060531577631417239528 : Int)/10^30)
theorem v3368_pa_checked : Scalar.distance (sourceCoefficient 44 91 1 0) v3368_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3368_pb : Scalar.QComplex := ((-785182452517891125349749 : Int)/10^30,(-431476758841737601170071986 : Int)/10^30)
theorem v3368_pb_checked : Scalar.distance (sourceCoefficient 44 91 1 1) v3368_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3368_pg : Scalar.QComplex := ((-93086270619342486803541 : Int)/10^30,(169394306327975813709 : Int)/10^30)
theorem v3368_pg_checked : Scalar.distance (sourceCoefficient 44 91 1 2) v3368_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3368_mb : Scalar.QComplex := ((-1157527170047167325933937 : Int)/10^30,(-431475920606127604324686126 : Int)/10^30)
theorem v3368_mb_checked : Scalar.distance (sourceCoefficient 44 91 3 1) v3368_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3368_mg : Scalar.QComplex := ((-93086089779412557793999 : Int)/10^30,(249723502349228795896 : Int)/10^30)
theorem v3368_mg_checked : Scalar.distance (sourceCoefficient 44 91 3 2) v3368_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3368_upper : Scalar.QComplex := ((999993714139267116002351360505 : Int)/10^30,(-3545656773254123378352500997 : Int)/10^30)
theorem v3368_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 91 5) 1) 14) v3368_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3368 : Material (44 : Basis) (91 : Basis) where
  plus := ![v3368_pa,v3368_pb,v3368_pg]
  minus := ![(Primitive.Addresses.material3368 1).one,v3368_mb,v3368_mg]
  upper := v3368_upper
  lower := (Primitive.Addresses.material3368 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3368_pa_checked.trans (by decide +kernel)
    · exact v3368_pb_checked.trans (by decide +kernel)
    · exact v3368_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 91 Primitive.Addresses.material3368
    · exact v3368_mb_checked.trans (by decide +kernel)
    · exact v3368_mg_checked.trans (by decide +kernel)
  upper_error := v3368_upper_checked
  lower_error := reuse_lower_error 44 91 Primitive.Addresses.material3368

def v3369_pa : Scalar.QComplex := ((999998285585213910074669994371 : Int)/10^30,(-1851709111324398029907840461 : Int)/10^30)
theorem v3369_pa_checked : Scalar.distance (sourceCoefficient 44 92 1 0) v3369_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3369_pb : Scalar.QComplex := ((-798970761499184267638373 : Int)/10^30,(-431476729711855318964310339 : Int)/10^30)
theorem v3369_pb_checked : Scalar.distance (sourceCoefficient 44 92 1 1) v3369_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3369_pg : Scalar.QComplex := ((-93086264746763993438072 : Int)/10^30,(172368980082666112274 : Int)/10^30)
theorem v3369_pg_checked : Scalar.distance (sourceCoefficient 44 92 1 2) v3369_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3369_mb : Scalar.QComplex := ((-1171315448756666429288429 : Int)/10^30,(-431475879577566520033243091 : Int)/10^30)
theorem v3369_mb_checked : Scalar.distance (sourceCoefficient 44 92 3 1) v3369_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3369_mg : Scalar.QComplex := ((-93086081339826775092716 : Int)/10^30,(252698169928541357626 : Int)/10^30)
theorem v3369_mg_checked : Scalar.distance (sourceCoefficient 44 92 3 2) v3369_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3369_upper : Scalar.QComplex := ((999993600323295173639640217349 : Int)/10^30,(-3577612675205463661230625279 : Int)/10^30)
theorem v3369_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 92 5) 1) 14) v3369_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3369 : Material (44 : Basis) (92 : Basis) where
  plus := ![v3369_pa,v3369_pb,v3369_pg]
  minus := ![(Primitive.Addresses.material3369 1).one,v3369_mb,v3369_mg]
  upper := v3369_upper
  lower := (Primitive.Addresses.material3369 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3369_pa_checked.trans (by decide +kernel)
    · exact v3369_pb_checked.trans (by decide +kernel)
    · exact v3369_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 92 Primitive.Addresses.material3369
    · exact v3369_mb_checked.trans (by decide +kernel)
    · exact v3369_mg_checked.trans (by decide +kernel)
  upper_error := v3369_upper_checked
  lower_error := reuse_lower_error 44 92 Primitive.Addresses.material3369

def v3370_pa : Scalar.QComplex := ((999998214638838411121997783055 : Int)/10^30,(-1889634656663366421134818266 : Int)/10^30)
theorem v3370_pa_checked : Scalar.distance (sourceCoefficient 44 93 1 0) v3370_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3370_pb : Scalar.QComplex := ((-815334770906345505486154 : Int)/10^30,(-431476694378050550412195792 : Int)/10^30)
theorem v3370_pb_checked : Scalar.distance (sourceCoefficient 44 93 1 1) v3370_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3370_pg : Scalar.QComplex := ((-93086257633255781124942 : Int)/10^30,(175899332526731602343 : Int)/10^30)
theorem v3370_pg_checked : Scalar.distance (sourceCoefficient 44 93 1 2) v3370_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3370_mb : Scalar.QComplex := ((-1187679421579276952906204 : Int)/10^30,(-431475830122371797116019758 : Int)/10^30)
theorem v3370_mb_checked : Scalar.distance (sourceCoefficient 44 93 3 1) v3370_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3370_mg : Scalar.QComplex := ((-93086071179786053406959 : Int)/10^30,(256228514919458080983 : Int)/10^30)
theorem v3370_mg_checked : Scalar.distance (sourceCoefficient 44 93 3 2) v3370_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3370_upper : Scalar.QComplex := ((999993463920974664516709887870 : Int)/10^30,(-3615538041611779411285797203 : Int)/10^30)
theorem v3370_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 93 5) 1) 14) v3370_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3370 : Material (44 : Basis) (93 : Basis) where
  plus := ![v3370_pa,v3370_pb,v3370_pg]
  minus := ![(Primitive.Addresses.material3370 1).one,v3370_mb,v3370_mg]
  upper := v3370_upper
  lower := (Primitive.Addresses.material3370 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3370_pa_checked.trans (by decide +kernel)
    · exact v3370_pb_checked.trans (by decide +kernel)
    · exact v3370_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 93 Primitive.Addresses.material3370
    · exact v3370_mb_checked.trans (by decide +kernel)
    · exact v3370_mg_checked.trans (by decide +kernel)
  upper_error := v3370_upper_checked
  lower_error := reuse_lower_error 44 93 Primitive.Addresses.material3370

def v3371_pa : Scalar.QComplex := ((999998128982478039704278016663 : Int)/10^30,(-1934433132267441277843421542 : Int)/10^30)
theorem v3371_pa_checked : Scalar.distance (sourceCoefficient 44 94 1 0) v3371_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3371_pb : Scalar.QComplex := ((-834664292277971063975261 : Int)/10^30,(-431476651574979636073062892 : Int)/10^30)
theorem v3371_pb_checked : Scalar.distance (sourceCoefficient 44 94 1 1) v3371_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3371_pg : Scalar.QComplex := ((-93086249029392429991558 : Int)/10^30,(180069461194071727853 : Int)/10^30)
theorem v3371_pg_checked : Scalar.distance (sourceCoefficient 44 94 1 2) v3371_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3371_mb : Scalar.QComplex := ((-1207008898816515881648249 : Int)/10^30,(-431475770638810445929053844 : Int)/10^30)
theorem v3371_mb_checked : Scalar.distance (sourceCoefficient 44 94 3 1) v3371_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3371_mg : Scalar.QComplex := ((-93086058977292681593721 : Int)/10^30,(260398634609322150940 : Int)/10^30)
theorem v3371_mg_checked : Scalar.distance (sourceCoefficient 44 94 3 2) v3371_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3371_upper : Scalar.QComplex := ((999993300946637061512562140646 : Int)/10^30,(-3660336302658679937577352298 : Int)/10^30)
theorem v3371_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 94 5) 1) 14) v3371_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3371 : Material (44 : Basis) (94 : Basis) where
  plus := ![v3371_pa,v3371_pb,v3371_pg]
  minus := ![(Primitive.Addresses.material3371 1).one,v3371_mb,v3371_mg]
  upper := v3371_upper
  lower := (Primitive.Addresses.material3371 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3371_pa_checked.trans (by decide +kernel)
    · exact v3371_pb_checked.trans (by decide +kernel)
    · exact v3371_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 94 Primitive.Addresses.material3371
    · exact v3371_mb_checked.trans (by decide +kernel)
    · exact v3371_mg_checked.trans (by decide +kernel)
  upper_error := v3371_upper_checked
  lower_error := reuse_lower_error 44 94 Primitive.Addresses.material3371

def v3372_pa : Scalar.QComplex := ((999998042356851280287901787386 : Int)/10^30,(-1978707271193171328918387936 : Int)/10^30)
theorem v3372_pa_checked : Scalar.distance (sourceCoefficient 44 95 1 0) v3372_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3372_pb : Scalar.QComplex := ((-853767573245654824218837 : Int)/10^30,(-431476608138498901294220677 : Int)/10^30)
theorem v3372_pb_checked : Scalar.distance (sourceCoefficient 44 95 1 1) v3372_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3372_pg : Scalar.QComplex := ((-93086240312090774839742 : Int)/10^30,(184190781133389661245 : Int)/10^30)
theorem v3372_pg_checked : Scalar.distance (sourceCoefficient 44 95 1 2) v3372_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3372_mb : Scalar.QComplex := ((-1226112135187448506909391 : Int)/10^30,(-431475710717074789262033004 : Int)/10^30)
theorem v3372_mb_checked : Scalar.distance (sourceCoefficient 44 95 3 1) v3372_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3372_mg : Scalar.QComplex := ((-93086046703480782019962 : Int)/10^30,(264519945491445601593 : Int)/10^30)
theorem v3372_mg_checked : Scalar.distance (sourceCoefficient 44 95 3 2) v3372_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3372_upper : Scalar.QComplex := ((999993137907992053489436451986 : Int)/10^30,(-3704610226135307693191111629 : Int)/10^30)
theorem v3372_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 95 5) 1) 14) v3372_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3372 : Material (44 : Basis) (95 : Basis) where
  plus := ![v3372_pa,v3372_pb,v3372_pg]
  minus := ![(Primitive.Addresses.material3372 1).one,v3372_mb,v3372_mg]
  upper := v3372_upper
  lower := (Primitive.Addresses.material3372 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3372_pa_checked.trans (by decide +kernel)
    · exact v3372_pb_checked.trans (by decide +kernel)
    · exact v3372_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 95 Primitive.Addresses.material3372
    · exact v3372_mb_checked.trans (by decide +kernel)
    · exact v3372_mg_checked.trans (by decide +kernel)
  upper_error := v3372_upper_checked
  lower_error := reuse_lower_error 44 95 Primitive.Addresses.material3372

def v3373_pa : Scalar.QComplex := ((999998000055348168333025951657 : Int)/10^30,(-1999971325765627960296597242 : Int)/10^30)
theorem v3373_pa_checked : Scalar.distance (sourceCoefficient 44 96 1 0) v3373_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3373_pb : Scalar.QComplex := ((-862942527328275970319537 : Int)/10^30,(-431476586875880864395078294 : Int)/10^30)
theorem v3373_pb_checked : Scalar.distance (sourceCoefficient 44 96 1 1) v3373_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3373_pg : Scalar.QComplex := ((-93086236049657278501894 : Int)/10^30,(186170175252811585544 : Int)/10^30)
theorem v3373_pg_checked : Scalar.distance (sourceCoefficient 44 96 1 2) v3373_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3373_mb : Scalar.QComplex := ((-1235287067505133198857449 : Int)/10^30,(-431475681536892520697549670 : Int)/10^30)
theorem v3373_mb_checked : Scalar.distance (sourceCoefficient 44 96 3 1) v3373_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3373_mg : Scalar.QComplex := ((-93086040732920896321575 : Int)/10^30,(266499335195560497990 : Int)/10^30)
theorem v3373_mg_checked : Scalar.distance (sourceCoefficient 44 96 3 2) v3373_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3373_upper : Scalar.QComplex := ((999993058906722812556040305369 : Int)/10^30,(-3725874176028896081360542622 : Int)/10^30)
theorem v3373_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 96 5) 1) 14) v3373_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3373 : Material (44 : Basis) (96 : Basis) where
  plus := ![v3373_pa,v3373_pb,v3373_pg]
  minus := ![(Primitive.Addresses.material3373 1).one,v3373_mb,v3373_mg]
  upper := v3373_upper
  lower := (Primitive.Addresses.material3373 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3373_pa_checked.trans (by decide +kernel)
    · exact v3373_pb_checked.trans (by decide +kernel)
    · exact v3373_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 96 Primitive.Addresses.material3373
    · exact v3373_mb_checked.trans (by decide +kernel)
    · exact v3373_mg_checked.trans (by decide +kernel)
  upper_error := v3373_upper_checked
  lower_error := reuse_lower_error 44 96 Primitive.Addresses.material3373

def v3374_pa : Scalar.QComplex := ((999997851056649458858799241622 : Int)/10^30,(-2073133397329935101957606781 : Int)/10^30)
theorem v3374_pa_checked : Scalar.distance (sourceCoefficient 44 97 1 0) v3374_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3374_pb : Scalar.QComplex := ((-894510288885987837332599 : Int)/10^30,(-431476511731527181732677715 : Int)/10^30)
theorem v3374_pb_checked : Scalar.distance (sourceCoefficient 44 97 1 1) v3374_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3374_pg : Scalar.QComplex := ((-93086221009003548419336 : Int)/10^30,(192980568309309757681 : Int)/10^30)
theorem v3374_pg_checked : Scalar.distance (sourceCoefficient 44 97 1 2) v3374_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3374_mb : Scalar.QComplex := ((-1266854752462531867877753 : Int)/10^30,(-431475579151010352609327423 : Int)/10^30)
theorem v3374_mb_checked : Scalar.distance (sourceCoefficient 44 97 3 1) v3374_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3374_mg : Scalar.QComplex := ((-93086019815210287520828 : Int)/10^30,(273309712736831321690 : Int)/10^30)
theorem v3374_mg_checked : Scalar.distance (sourceCoefficient 44 97 3 2) v3374_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3374_upper : Scalar.QComplex := ((999992783637147710432062874173 : Int)/10^30,(-3799035881468654932428039140 : Int)/10^30)
theorem v3374_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 97 5) 1) 14) v3374_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3374 : Material (44 : Basis) (97 : Basis) where
  plus := ![v3374_pa,v3374_pb,v3374_pg]
  minus := ![(Primitive.Addresses.material3374 1).one,v3374_mb,v3374_mg]
  upper := v3374_upper
  lower := (Primitive.Addresses.material3374 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3374_pa_checked.trans (by decide +kernel)
    · exact v3374_pb_checked.trans (by decide +kernel)
    · exact v3374_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 97 Primitive.Addresses.material3374
    · exact v3374_mb_checked.trans (by decide +kernel)
    · exact v3374_mg_checked.trans (by decide +kernel)
  upper_error := v3374_upper_checked
  lower_error := reuse_lower_error 44 97 Primitive.Addresses.material3374

def v3375_pa : Scalar.QComplex := ((999999472454415141421178056878 : Int)/10^30,(-1027176173503266936105700505 : Int)/10^30)
theorem v3375_pa_checked : Scalar.distance (sourceCoefficient 45 46 1 0) v3375_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3375_pb : Scalar.QComplex := ((-443203428954345120695575 : Int)/10^30,(-431477293357334064855557445 : Int)/10^30)
theorem v3375_pb_checked : Scalar.distance (sourceCoefficient 45 46 1 1) v3375_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3375_pg : Scalar.QComplex := ((-93086380787563659750265 : Int)/10^30,(95616162864522223966 : Int)/10^30)
theorem v3375_pg_checked : Scalar.distance (sourceCoefficient 45 46 1 2) v3375_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3375_mb : Scalar.QComplex := ((-815548735080927066816791 : Int)/10^30,(-431476750234020215299121954 : Int)/10^30)
theorem v3375_mb_checked : Scalar.distance (sourceCoefficient 45 46 3 1) v3375_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3375_mg : Scalar.QComplex := ((-93086263614807674805674 : Int)/10^30,(175945481426962925087 : Int)/10^30)
theorem v3375_mg_checked : Scalar.distance (sourceCoefficient 45 46 3 2) v3375_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3375_upper : Scalar.QComplex := ((999996210259778338197187150712 : Int)/10^30,(-2753083013857856401788117989 : Int)/10^30)
theorem v3375_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 46 5) 1) 14) v3375_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3375 : Material (45 : Basis) (46 : Basis) where
  plus := ![v3375_pa,v3375_pb,v3375_pg]
  minus := ![(Primitive.Addresses.material3375 1).one,v3375_mb,v3375_mg]
  upper := v3375_upper
  lower := (Primitive.Addresses.material3375 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3375_pa_checked.trans (by decide +kernel)
    · exact v3375_pb_checked.trans (by decide +kernel)
    · exact v3375_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 46 Primitive.Addresses.material3375
    · exact v3375_mb_checked.trans (by decide +kernel)
    · exact v3375_mg_checked.trans (by decide +kernel)
  upper_error := v3375_upper_checked
  lower_error := reuse_lower_error 45 46 Primitive.Addresses.material3375

def v3376_pa : Scalar.QComplex := ((999999468401597420064615272974 : Int)/10^30,(-1031114214121311172178392540 : Int)/10^30)
theorem v3376_pa_checked : Scalar.distance (sourceCoefficient 45 47 1 0) v3376_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3376_pb : Scalar.QComplex := ((-444902604947035984736405 : Int)/10^30,(-431477291598250506929657883 : Int)/10^30)
theorem v3376_pb_checked : Scalar.distance (sourceCoefficient 45 47 1 1) v3376_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3376_pg : Scalar.QComplex := ((-93086380409181231375186 : Int)/10^30,(95982741005282115346 : Int)/10^30)
theorem v3376_pg_checked : Scalar.distance (sourceCoefficient 45 47 1 2) v3376_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3376_mb : Scalar.QComplex := ((-817247908922927168292036 : Int)/10^30,(-431476747008624958714065629 : Int)/10^30)
theorem v3376_mb_checked : Scalar.distance (sourceCoefficient 45 47 3 1) v3376_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3376_mg : Scalar.QComplex := ((-93086262920084961910458 : Int)/10^30,(176312059104702027237 : Int)/10^30)
theorem v3376_mg_checked : Scalar.distance (sourceCoefficient 45 47 3 2) v3376_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3376_upper : Scalar.QComplex := ((999996199410265802546327720482 : Int)/10^30,(-2757021041615856013720607887 : Int)/10^30)
theorem v3376_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 47 5) 1) 14) v3376_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3376 : Material (45 : Basis) (47 : Basis) where
  plus := ![v3376_pa,v3376_pb,v3376_pg]
  minus := ![(Primitive.Addresses.material3376 1).one,v3376_mb,v3376_mg]
  upper := v3376_upper
  lower := (Primitive.Addresses.material3376 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3376_pa_checked.trans (by decide +kernel)
    · exact v3376_pb_checked.trans (by decide +kernel)
    · exact v3376_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 47 Primitive.Addresses.material3376
    · exact v3376_mb_checked.trans (by decide +kernel)
    · exact v3376_mg_checked.trans (by decide +kernel)
  upper_error := v3376_upper_checked
  lower_error := reuse_lower_error 45 47 Primitive.Addresses.material3376

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
