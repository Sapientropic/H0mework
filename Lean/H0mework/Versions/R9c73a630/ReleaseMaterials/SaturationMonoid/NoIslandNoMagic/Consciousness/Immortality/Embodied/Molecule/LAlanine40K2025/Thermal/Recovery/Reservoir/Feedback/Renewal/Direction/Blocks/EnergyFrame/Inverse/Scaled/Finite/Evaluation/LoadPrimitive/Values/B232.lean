import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B154
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B155

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3713_pa : Scalar.QComplex := ((999998047327545266264538656154 : Int)/10^30,(-1976193587819208426351508263 : Int)/10^30)
theorem v3713_pa_checked : Scalar.distance (sourceCoefficient 51 93 1 0) v3713_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3713_pb : Scalar.QComplex := ((-852683019770258079430855 : Int)/10^30,(-431476632661567007512304099 : Int)/10^30)
theorem v3713_pb_checked : Scalar.distance (sourceCoefficient 51 93 1 1) v3713_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3713_pg : Scalar.QComplex := ((-93086243188731176343869 : Int)/10^30,(183956796111118643407 : Int)/10^30)
theorem v3713_pg_checked : Scalar.distance (sourceCoefficient 51 93 1 2) v3713_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3713_mb : Scalar.QComplex := ((-1225027603278183885232932 : Int)/10^30,(-431475736176054567213226180 : Int)/10^30)
theorem v3713_mb_checked : Scalar.distance (sourceCoefficient 51 93 3 1) v3713_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3713_mg : Scalar.QComplex := ((-93086049782038648345083 : Int)/10^30,(264285963038709008614 : Int)/10^30)
theorem v3713_mg_checked : Scalar.distance (sourceCoefficient 51 93 3 2) v3713_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3713_upper : Scalar.QComplex := ((999993147217068100086911253962 : Int)/10^30,(-3702096555084147780110522567 : Int)/10^30)
theorem v3713_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 93 5) 1) 14) v3713_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3713 : Material (51 : Basis) (93 : Basis) where
  plus := ![v3713_pa,v3713_pb,v3713_pg]
  minus := ![(Primitive.Addresses.material3713 1).one,v3713_mb,v3713_mg]
  upper := v3713_upper
  lower := (Primitive.Addresses.material3713 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3713_pa_checked.trans (by decide +kernel)
    · exact v3713_pb_checked.trans (by decide +kernel)
    · exact v3713_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 93 Primitive.Addresses.material3713
    · exact v3713_mb_checked.trans (by decide +kernel)
    · exact v3713_mg_checked.trans (by decide +kernel)
  upper_error := v3713_upper_checked
  lower_error := reuse_lower_error 51 93 Primitive.Addresses.material3713

def v3714_pa : Scalar.QComplex := ((999997957793469809784310144910 : Int)/10^30,(-2020992055841120674876267034 : Int)/10^30)
theorem v3714_pa_checked : Scalar.distance (sourceCoefficient 51 94 1 0) v3714_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3714_pb : Scalar.QComplex := ((-872012538960861996929842 : Int)/10^30,(-431476588743064922039346986 : Int)/10^30)
theorem v3714_pb_checked : Scalar.distance (sourceCoefficient 51 94 1 1) v3714_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3714_pg : Scalar.QComplex := ((-93086234284065627688699 : Int)/10^30,(188126924190295088880 : Int)/10^30)
theorem v3714_pg_checked : Scalar.distance (sourceCoefficient 51 94 1 2) v3714_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3714_mb : Scalar.QComplex := ((-1244357077371835121545459 : Int)/10^30,(-431475675577064342341885395 : Int)/10^30)
theorem v3714_mb_checked : Scalar.distance (sourceCoefficient 51 94 3 1) v3714_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3714_mg : Scalar.QComplex := ((-93086037278743698571232 : Int)/10^30,(268456081880830868701 : Int)/10^30)
theorem v3714_mg_checked : Scalar.distance (sourceCoefficient 51 94 3 2) v3714_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3714_upper : Scalar.QComplex := ((999992980365034273546178857557 : Int)/10^30,(-3746894801856312537705419036 : Int)/10^30)
theorem v3714_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 94 5) 1) 14) v3714_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3714 : Material (51 : Basis) (94 : Basis) where
  plus := ![v3714_pa,v3714_pb,v3714_pg]
  minus := ![(Primitive.Addresses.material3714 1).one,v3714_mb,v3714_mg]
  upper := v3714_upper
  lower := (Primitive.Addresses.material3714 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3714_pa_checked.trans (by decide +kernel)
    · exact v3714_pb_checked.trans (by decide +kernel)
    · exact v3714_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 94 Primitive.Addresses.material3714
    · exact v3714_mb_checked.trans (by decide +kernel)
    · exact v3714_mg_checked.trans (by decide +kernel)
  upper_error := v3714_upper_checked
  lower_error := reuse_lower_error 51 94 Primitive.Addresses.material3714

def v3715_pa : Scalar.QComplex := ((999997867335514076122242679279 : Int)/10^30,(-2065266187102753588700741740 : Int)/10^30)
theorem v3715_pa_checked : Scalar.distance (sourceCoefficient 51 95 1 0) v3715_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3715_pb : Scalar.QComplex := ((-891115817723955530493136 : Int)/10^30,(-431476544204208414825697610 : Int)/10^30)
theorem v3715_pb_checked : Scalar.distance (sourceCoefficient 51 95 1 1) v3715_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3715_pg : Scalar.QComplex := ((-93086225269482468781828 : Int)/10^30,(192248243535093518008 : Int)/10^30)
theorem v3715_pg_checked : Scalar.distance (sourceCoefficient 51 95 1 2) v3715_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3715_mb : Scalar.QComplex := ((-1263460310586877698546503 : Int)/10^30,(-431475614552955226167013100 : Int)/10^30)
theorem v3715_mb_checked : Scalar.distance (sourceCoefficient 51 95 3 1) v3715_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3715_mg : Scalar.QComplex := ((-93086024707650918977464 : Int)/10^30,(272577391911894487779 : Int)/10^30)
theorem v3715_mg_checked : Scalar.distance (sourceCoefficient 51 95 3 2) v3715_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3715_upper : Scalar.QComplex := ((999992813494079226617569520276 : Int)/10^30,(-3791168711054602427461745948 : Int)/10^30)
theorem v3715_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 95 5) 1) 14) v3715_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3715 : Material (51 : Basis) (95 : Basis) where
  plus := ![v3715_pa,v3715_pb,v3715_pg]
  minus := ![(Primitive.Addresses.material3715 1).one,v3715_mb,v3715_mg]
  upper := v3715_upper
  lower := (Primitive.Addresses.material3715 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3715_pa_checked.trans (by decide +kernel)
    · exact v3715_pb_checked.trans (by decide +kernel)
    · exact v3715_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 95 Primitive.Addresses.material3715
    · exact v3715_mb_checked.trans (by decide +kernel)
    · exact v3715_mg_checked.trans (by decide +kernel)
  upper_error := v3715_upper_checked
  lower_error := reuse_lower_error 51 95 Primitive.Addresses.material3715

def v3716_pa : Scalar.QComplex := ((999997823193413850147948256611 : Int)/10^30,(-2086530237933970272543243131 : Int)/10^30)
theorem v3716_pa_checked : Scalar.distance (sourceCoefficient 51 96 1 0) v3716_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3716_pb : Scalar.QComplex := ((-900290770730402819906023 : Int)/10^30,(-431476522412139574857950108 : Int)/10^30)
theorem v3716_pb_checked : Scalar.distance (sourceCoefficient 51 96 1 1) v3716_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3716_pg : Scalar.QComplex := ((-93086220864270134939533 : Int)/10^30,(194227637364299899491 : Int)/10^30)
theorem v3716_pg_checked : Scalar.distance (sourceCoefficient 51 96 1 2) v3716_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3716_mb : Scalar.QComplex := ((-1272635241371496737046232 : Int)/10^30,(-431475584843323280362224976 : Int)/10^30)
theorem v3716_mb_checked : Scalar.distance (sourceCoefficient 51 96 3 1) v3716_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3716_mg : Scalar.QComplex := ((-93086018594312499380658 : Int)/10^30,(274556781202582243174 : Int)/10^30)
theorem v3716_mg_checked : Scalar.distance (sourceCoefficient 51 96 3 2) v3716_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3716_upper : Scalar.QComplex := ((999992732652222070058691203445 : Int)/10^30,(-3812432654030252799101203380 : Int)/10^30)
theorem v3716_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 96 5) 1) 14) v3716_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3716 : Material (51 : Basis) (96 : Basis) where
  plus := ![v3716_pa,v3716_pb,v3716_pg]
  minus := ![(Primitive.Addresses.material3716 1).one,v3716_mb,v3716_mg]
  upper := v3716_upper
  lower := (Primitive.Addresses.material3716 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3716_pa_checked.trans (by decide +kernel)
    · exact v3716_pb_checked.trans (by decide +kernel)
    · exact v3716_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 96 Primitive.Addresses.material3716
    · exact v3716_mb_checked.trans (by decide +kernel)
    · exact v3716_mg_checked.trans (by decide +kernel)
  upper_error := v3716_upper_checked
  lower_error := reuse_lower_error 51 96 Primitive.Addresses.material3716

def v3717_pa : Scalar.QComplex := ((999997667861873158777697709207 : Int)/10^30,(-2159692296327002676401076203 : Int)/10^30)
theorem v3717_pa_checked : Scalar.distance (sourceCoefficient 51 97 1 0) v3717_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3717_pb : Scalar.QComplex := ((-931858528499375765966948 : Int)/10^30,(-431476445446133442127198181 : Int)/10^30)
theorem v3717_pb_checked : Scalar.distance (sourceCoefficient 51 97 1 1) v3717_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3717_pg : Scalar.QComplex := ((-93086205332365057985136 : Int)/10^30,(201038029399075680081 : Int)/10^30)
theorem v3717_pg_checked : Scalar.distance (sourceCoefficient 51 97 1 2) v3717_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3717_mb : Scalar.QComplex := ((-1304202920968153875606794 : Int)/10^30,(-431475480635792610001162487 : Int)/10^30)
theorem v3717_mb_checked : Scalar.distance (sourceCoefficient 51 97 3 1) v3717_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3717_mg : Scalar.QComplex := ((-93085997185351608323809 : Int)/10^30,(281367157298203268550 : Int)/10^30)
theorem v3717_mg_checked : Scalar.distance (sourceCoefficient 51 97 3 2) v3717_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3717_upper : Scalar.QComplex := ((999992451049837150488222831164 : Int)/10^30,(-3885594335368845779616266084 : Int)/10^30)
theorem v3717_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 97 5) 1) 14) v3717_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3717 : Material (51 : Basis) (97 : Basis) where
  plus := ![v3717_pa,v3717_pb,v3717_pg]
  minus := ![(Primitive.Addresses.material3717 1).one,v3717_mb,v3717_mg]
  upper := v3717_upper
  lower := (Primitive.Addresses.material3717 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3717_pa_checked.trans (by decide +kernel)
    · exact v3717_pb_checked.trans (by decide +kernel)
    · exact v3717_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 97 Primitive.Addresses.material3717
    · exact v3717_mb_checked.trans (by decide +kernel)
    · exact v3717_mg_checked.trans (by decide +kernel)
  upper_error := v3717_upper_checked
  lower_error := reuse_lower_error 51 97 Primitive.Addresses.material3717

def v3718_pa : Scalar.QComplex := ((999999243323507692365182360594 : Int)/10^30,(-1230183893593130906381032815 : Int)/10^30)
theorem v3718_pa_checked : Scalar.distance (sourceCoefficient 52 53 1 0) v3718_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3718_pb : Scalar.QComplex := ((-530796696781281953014717 : Int)/10^30,(-431477194510769654998348205 : Int)/10^30)
theorem v3718_pb_checked : Scalar.distance (sourceCoefficient 52 53 1 1) v3718_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3718_pg : Scalar.QComplex := ((-93086359460556443971392 : Int)/10^30,(114513426771215194320 : Int)/10^30)
theorem v3718_pg_checked : Scalar.distance (sourceCoefficient 52 53 1 2) v3718_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3718_mb : Scalar.QComplex := ((-903141884992753875357614 : Int)/10^30,(-431476575798447530224491856 : Int)/10^30)
theorem v3718_mb_checked : Scalar.distance (sourceCoefficient 52 53 3 1) v3718_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3718_mg : Scalar.QComplex := ((-93086225980320749742243 : Int)/10^30,(194842719893094200885 : Int)/10^30)
theorem v3718_mg_checked : Scalar.distance (sourceCoefficient 52 53 3 2) v3718_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3718_upper : Scalar.QComplex := ((999995630756303994110075155482 : Int)/10^30,(-2956090036132408596647705982 : Int)/10^30)
theorem v3718_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 53 5) 1) 14) v3718_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3718 : Material (52 : Basis) (53 : Basis) where
  plus := ![v3718_pa,v3718_pb,v3718_pg]
  minus := ![(Primitive.Addresses.material3718 1).one,v3718_mb,v3718_mg]
  upper := v3718_upper
  lower := (Primitive.Addresses.material3718 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3718_pa_checked.trans (by decide +kernel)
    · exact v3718_pb_checked.trans (by decide +kernel)
    · exact v3718_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 53 Primitive.Addresses.material3718
    · exact v3718_mb_checked.trans (by decide +kernel)
    · exact v3718_mg_checked.trans (by decide +kernel)
  upper_error := v3718_upper_checked
  lower_error := reuse_lower_error 52 53 Primitive.Addresses.material3718

def v3719_pa : Scalar.QComplex := ((999999241005951570807049043008 : Int)/10^30,(-1232066362168215495420527061 : Int)/10^30)
theorem v3719_pa_checked : Scalar.distance (sourceCoefficient 52 54 1 0) v3719_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3719_pb : Scalar.QComplex := ((-531608939653870109333933 : Int)/10^30,(-431477193509538953246468176 : Int)/10^30)
theorem v3719_pb_checked : Scalar.distance (sourceCoefficient 52 54 1 1) v3719_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3719_pg : Scalar.QComplex := ((-93086359244687790939612 : Int)/10^30,(114688659050095763794 : Int)/10^30)
theorem v3719_pg_checked : Scalar.distance (sourceCoefficient 52 54 1 2) v3719_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3719_mb : Scalar.QComplex := ((-903954126698889887024126 : Int)/10^30,(-431476574096288184293973124 : Int)/10^30)
theorem v3719_mb_checked : Scalar.distance (sourceCoefficient 52 54 3 1) v3719_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3719_mg : Scalar.QComplex := ((-93086225613234612583167 : Int)/10^30,(195017951920442859217 : Int)/10^30)
theorem v3719_mg_checked : Scalar.distance (sourceCoefficient 52 54 3 2) v3719_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3719_upper : Scalar.QComplex := ((999995625189781339898646041766 : Int)/10^30,(-2957972497903885754630739937 : Int)/10^30)
theorem v3719_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 54 5) 1) 14) v3719_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3719 : Material (52 : Basis) (54 : Basis) where
  plus := ![v3719_pa,v3719_pb,v3719_pg]
  minus := ![(Primitive.Addresses.material3719 1).one,v3719_mb,v3719_mg]
  upper := v3719_upper
  lower := (Primitive.Addresses.material3719 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3719_pa_checked.trans (by decide +kernel)
    · exact v3719_pb_checked.trans (by decide +kernel)
    · exact v3719_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 54 Primitive.Addresses.material3719
    · exact v3719_mb_checked.trans (by decide +kernel)
    · exact v3719_mg_checked.trans (by decide +kernel)
  upper_error := v3719_upper_checked
  lower_error := reuse_lower_error 52 54 Primitive.Addresses.material3719

def v3720_pa : Scalar.QComplex := ((999999221983910147791374983763 : Int)/10^30,(-1247409946407106848956763328 : Int)/10^30)
theorem v3720_pa_checked : Scalar.distance (sourceCoefficient 52 55 1 0) v3720_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3720_pb : Scalar.QComplex := ((-538229351308003579083041 : Int)/10^30,(-431477185272700169288423866 : Int)/10^30)
theorem v3720_pb_checked : Scalar.distance (sourceCoefficient 52 55 1 1) v3720_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3720_pg : Scalar.QComplex := ((-93086357470838092058666 : Int)/10^30,(116116938524777411317 : Int)/10^30)
theorem v3720_pg_checked : Scalar.distance (sourceCoefficient 52 55 1 2) v3720_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3720_mb : Scalar.QComplex := ((-910574528779920633071454 : Int)/10^30,(-431476560146335382042492955 : Int)/10^30)
theorem v3720_mb_checked : Scalar.distance (sourceCoefficient 52 55 3 1) v3720_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3720_mg : Scalar.QComplex := ((-93086222606844714856868 : Int)/10^30,(196446229332558383810 : Int)/10^30)
theorem v3720_mg_checked : Scalar.distance (sourceCoefficient 52 55 3 2) v3720_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3720_upper : Scalar.QComplex := ((999995579686133810741473947387 : Int)/10^30,(-2973316026459992938346255449 : Int)/10^30)
theorem v3720_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 55 5) 1) 14) v3720_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3720 : Material (52 : Basis) (55 : Basis) where
  plus := ![v3720_pa,v3720_pb,v3720_pg]
  minus := ![(Primitive.Addresses.material3720 1).one,v3720_mb,v3720_mg]
  upper := v3720_upper
  lower := (Primitive.Addresses.material3720 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3720_pa_checked.trans (by decide +kernel)
    · exact v3720_pb_checked.trans (by decide +kernel)
    · exact v3720_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 55 Primitive.Addresses.material3720
    · exact v3720_mb_checked.trans (by decide +kernel)
    · exact v3720_mg_checked.trans (by decide +kernel)
  upper_error := v3720_upper_checked
  lower_error := reuse_lower_error 52 55 Primitive.Addresses.material3720

def v3721_pa : Scalar.QComplex := ((999999217434881704192465542125 : Int)/10^30,(-1251051407490296018005325246 : Int)/10^30)
theorem v3721_pa_checked : Scalar.distance (sourceCoefficient 52 56 1 0) v3721_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3721_pb : Scalar.QComplex := ((-539800559893977739645500 : Int)/10^30,(-431477183297981923168498571 : Int)/10^30)
theorem v3721_pb_checked : Scalar.distance (sourceCoefficient 52 56 1 1) v3721_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3721_pg : Scalar.QComplex := ((-93086357046100040121505 : Int)/10^30,(116455909134999997724 : Int)/10^30)
theorem v3721_pg_checked : Scalar.distance (sourceCoefficient 52 56 1 2) v3721_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3721_mb : Scalar.QComplex := ((-912145735076769120902754 : Int)/10^30,(-431476556815735626112525763 : Int)/10^30)
theorem v3721_mb_checked : Scalar.distance (sourceCoefficient 52 56 3 1) v3721_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3721_mg : Scalar.QComplex := ((-93086221889590451116562 : Int)/10^30,(196785199450036910979 : Int)/10^30)
theorem v3721_mg_checked : Scalar.distance (sourceCoefficient 52 56 3 2) v3721_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3721_upper : Scalar.QComplex := ((999995568852280663570467381936 : Int)/10^30,(-2976957474268443171036576431 : Int)/10^30)
theorem v3721_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 56 5) 1) 14) v3721_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3721 : Material (52 : Basis) (56 : Basis) where
  plus := ![v3721_pa,v3721_pb,v3721_pg]
  minus := ![(Primitive.Addresses.material3721 1).one,v3721_mb,v3721_mg]
  upper := v3721_upper
  lower := (Primitive.Addresses.material3721 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3721_pa_checked.trans (by decide +kernel)
    · exact v3721_pb_checked.trans (by decide +kernel)
    · exact v3721_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 56 Primitive.Addresses.material3721
    · exact v3721_mb_checked.trans (by decide +kernel)
    · exact v3721_mg_checked.trans (by decide +kernel)
  upper_error := v3721_upper_checked
  lower_error := reuse_lower_error 52 56 Primitive.Addresses.material3721

def v3722_pa : Scalar.QComplex := ((999999202630819039566307946138 : Int)/10^30,(-1262829254540476916407717730 : Int)/10^30)
theorem v3722_pa_checked : Scalar.distance (sourceCoefficient 52 57 1 0) v3722_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3722_pb : Scalar.QComplex := ((-544882436076245652813979 : Int)/10^30,(-431477176858765124016664990 : Int)/10^30)
theorem v3722_pb_checked : Scalar.distance (sourceCoefficient 52 57 1 1) v3722_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3722_pg : Scalar.QComplex := ((-93086355662477011712952 : Int)/10^30,(117552266861690294510 : Int)/10^30)
theorem v3722_pg_checked : Scalar.distance (sourceCoefficient 52 57 1 2) v3722_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3722_mb : Scalar.QComplex := ((-917227603810068192088683 : Int)/10^30,(-431476545991090958485038000 : Int)/10^30)
theorem v3722_mb_checked : Scalar.distance (sourceCoefficient 52 57 3 1) v3722_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3722_mg : Scalar.QComplex := ((-93086219559860597879379 : Int)/10^30,(197881555574498762646 : Int)/10^30)
theorem v3722_mg_checked : Scalar.distance (sourceCoefficient 52 57 3 2) v3722_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3722_upper : Scalar.QComplex := ((999995533720744517182311547143 : Int)/10^30,(-2988735278226435266225368816 : Int)/10^30)
theorem v3722_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 57 5) 1) 14) v3722_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3722 : Material (52 : Basis) (57 : Basis) where
  plus := ![v3722_pa,v3722_pb,v3722_pg]
  minus := ![(Primitive.Addresses.material3722 1).one,v3722_mb,v3722_mg]
  upper := v3722_upper
  lower := (Primitive.Addresses.material3722 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3722_pa_checked.trans (by decide +kernel)
    · exact v3722_pb_checked.trans (by decide +kernel)
    · exact v3722_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 57 Primitive.Addresses.material3722
    · exact v3722_mb_checked.trans (by decide +kernel)
    · exact v3722_mg_checked.trans (by decide +kernel)
  upper_error := v3722_upper_checked
  lower_error := reuse_lower_error 52 57 Primitive.Addresses.material3722

def v3723_pa : Scalar.QComplex := ((999999194540225630353480212360 : Int)/10^30,(-1269219799709193361106102530 : Int)/10^30)
theorem v3723_pa_checked : Scalar.distance (sourceCoefficient 52 58 1 0) v3723_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3723_pb : Scalar.QComplex := ((-547639812616748739077456 : Int)/10^30,(-431477173331510633139739238 : Int)/10^30)
theorem v3723_pb_checked : Scalar.distance (sourceCoefficient 52 58 1 1) v3723_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3723_pg : Scalar.QComplex := ((-93086354905432010019037 : Int)/10^30,(118147139891499944100 : Int)/10^30)
theorem v3723_pg_checked : Scalar.distance (sourceCoefficient 52 58 1 2) v3723_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3723_mb : Scalar.QComplex := ((-919984976280012210007789 : Int)/10^30,(-431476540084346014141322010 : Int)/10^30)
theorem v3723_mb_checked : Scalar.distance (sourceCoefficient 52 58 3 1) v3723_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3723_mg : Scalar.QComplex := ((-93086218289467245428884 : Int)/10^30,(198476427729514255777 : Int)/10^30)
theorem v3723_mg_checked : Scalar.distance (sourceCoefficient 52 58 3 2) v3723_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3723_upper : Scalar.QComplex := ((999995514600661942482376273721 : Int)/10^30,(-2995125799913555116888215335 : Int)/10^30)
theorem v3723_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 58 5) 1) 14) v3723_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3723 : Material (52 : Basis) (58 : Basis) where
  plus := ![v3723_pa,v3723_pb,v3723_pg]
  minus := ![(Primitive.Addresses.material3723 1).one,v3723_mb,v3723_mg]
  upper := v3723_upper
  lower := (Primitive.Addresses.material3723 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3723_pa_checked.trans (by decide +kernel)
    · exact v3723_pb_checked.trans (by decide +kernel)
    · exact v3723_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 58 Primitive.Addresses.material3723
    · exact v3723_mb_checked.trans (by decide +kernel)
    · exact v3723_mg_checked.trans (by decide +kernel)
  upper_error := v3723_upper_checked
  lower_error := reuse_lower_error 52 58 Primitive.Addresses.material3723

def v3724_pa : Scalar.QComplex := ((999999172090922482361266967266 : Int)/10^30,(-1286785712386424047350862804 : Int)/10^30)
theorem v3724_pa_checked : Scalar.distance (sourceCoefficient 52 59 1 0) v3724_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3724_pb : Scalar.QComplex := ((-555219108903031163023145 : Int)/10^30,(-431477163514975164011060825 : Int)/10^30)
theorem v3724_pb_checked : Scalar.distance (sourceCoefficient 52 59 1 1) v3724_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3724_pg : Scalar.QComplex := ((-93086352801665621744255 : Int)/10^30,(119782287972188835072 : Int)/10^30)
theorem v3724_pg_checked : Scalar.distance (sourceCoefficient 52 59 1 2) v3724_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3724_mb : Scalar.QComplex := ((-927564261272948246105390 : Int)/10^30,(-431476523727222863928603362 : Int)/10^30)
theorem v3724_mb_checked : Scalar.distance (sourceCoefficient 52 59 3 1) v3724_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3724_mg : Scalar.QComplex := ((-93086214774642491183710 : Int)/10^30,(200111573385907143389 : Int)/10^30)
theorem v3724_mg_checked : Scalar.distance (sourceCoefficient 52 59 3 2) v3724_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3724_upper : Scalar.QComplex := ((999995461834220516339772046187 : Int)/10^30,(-3012691647682961658887580954 : Int)/10^30)
theorem v3724_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 59 5) 1) 14) v3724_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3724 : Material (52 : Basis) (59 : Basis) where
  plus := ![v3724_pa,v3724_pb,v3724_pg]
  minus := ![(Primitive.Addresses.material3724 1).one,v3724_mb,v3724_mg]
  upper := v3724_upper
  lower := (Primitive.Addresses.material3724 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3724_pa_checked.trans (by decide +kernel)
    · exact v3724_pb_checked.trans (by decide +kernel)
    · exact v3724_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 59 Primitive.Addresses.material3724
    · exact v3724_mb_checked.trans (by decide +kernel)
    · exact v3724_mg_checked.trans (by decide +kernel)
  upper_error := v3724_upper_checked
  lower_error := reuse_lower_error 52 59 Primitive.Addresses.material3724

def v3725_pa : Scalar.QComplex := ((999999145810273362318911077264 : Int)/10^30,(-1307049625544215166732080159 : Int)/10^30)
theorem v3725_pa_checked : Scalar.distance (sourceCoefficient 52 60 1 0) v3725_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3725_pb : Scalar.QComplex := ((-563962531644509468981553 : Int)/10^30,(-431477151970180412593672014 : Int)/10^30)
theorem v3725_pb_checked : Scalar.distance (sourceCoefficient 52 60 1 1) v3725_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3725_pg : Scalar.QComplex := ((-93086350333149808054336 : Int)/10^30,(121668583274274972800 : Int)/10^30)
theorem v3725_pg_checked : Scalar.distance (sourceCoefficient 52 60 1 2) v3725_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3725_mb : Scalar.QComplex := ((-936307670796212759032427 : Int)/10^30,(-431476504637252374412281741 : Int)/10^30)
theorem v3725_mb_checked : Scalar.distance (sourceCoefficient 52 60 3 1) v3725_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3725_mg : Scalar.QComplex := ((-93086210678339706521414 : Int)/10^30,(201997865855421362807 : Int)/10^30)
theorem v3725_mg_checked : Scalar.distance (sourceCoefficient 52 60 3 2) v3725_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3725_upper : Scalar.QComplex := ((999995400579934755731112281005 : Int)/10^30,(-3032955485302018276861076909 : Int)/10^30)
theorem v3725_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 60 5) 1) 14) v3725_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3725 : Material (52 : Basis) (60 : Basis) where
  plus := ![v3725_pa,v3725_pb,v3725_pg]
  minus := ![(Primitive.Addresses.material3725 1).one,v3725_mb,v3725_mg]
  upper := v3725_upper
  lower := (Primitive.Addresses.material3725 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3725_pa_checked.trans (by decide +kernel)
    · exact v3725_pb_checked.trans (by decide +kernel)
    · exact v3725_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 60 Primitive.Addresses.material3725
    · exact v3725_mb_checked.trans (by decide +kernel)
    · exact v3725_mg_checked.trans (by decide +kernel)
  upper_error := v3725_upper_checked
  lower_error := reuse_lower_error 52 60 Primitive.Addresses.material3725

def v3726_pa : Scalar.QComplex := ((999999138134665086358393555214 : Int)/10^30,(-1312908956102984197738747650 : Int)/10^30)
theorem v3726_pa_checked : Scalar.distance (sourceCoefficient 52 61 1 0) v3726_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3726_pb : Scalar.QComplex := ((-566490700973611321741513 : Int)/10^30,(-431477148587962160010170497 : Int)/10^30)
theorem v3726_pb_checked : Scalar.distance (sourceCoefficient 52 61 1 1) v3726_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3726_pg : Scalar.QComplex := ((-93086349611064518517105 : Int)/10^30,(122214007427316588573 : Int)/10^30)
theorem v3726_pg_checked : Scalar.distance (sourceCoefficient 52 61 1 2) v3726_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3726_mb : Scalar.QComplex := ((-938835836265259604997284 : Int)/10^30,(-431476499073339114688044830 : Int)/10^30)
theorem v3726_mb_checked : Scalar.distance (sourceCoefficient 52 61 3 1) v3726_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3726_mg : Scalar.QComplex := ((-93086209485578206766580 : Int)/10^30,(202543289182249555931 : Int)/10^30)
theorem v3726_mg_checked : Scalar.distance (sourceCoefficient 52 61 3 2) v3726_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3726_upper : Scalar.QComplex := ((999995382791664921568151079676 : Int)/10^30,(-3038814793886599167333655879 : Int)/10^30)
theorem v3726_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 61 5) 1) 14) v3726_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3726 : Material (52 : Basis) (61 : Basis) where
  plus := ![v3726_pa,v3726_pb,v3726_pg]
  minus := ![(Primitive.Addresses.material3726 1).one,v3726_mb,v3726_mg]
  upper := v3726_upper
  lower := (Primitive.Addresses.material3726 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3726_pa_checked.trans (by decide +kernel)
    · exact v3726_pb_checked.trans (by decide +kernel)
    · exact v3726_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 61 Primitive.Addresses.material3726
    · exact v3726_mb_checked.trans (by decide +kernel)
    · exact v3726_mg_checked.trans (by decide +kernel)
  upper_error := v3726_upper_checked
  lower_error := reuse_lower_error 52 61 Primitive.Addresses.material3726

def v3727_pa : Scalar.QComplex := ((999999126921155592692773919827 : Int)/10^30,(-1321422311960845430525708112 : Int)/10^30)
theorem v3727_pa_checked : Scalar.distance (sourceCoefficient 52 62 1 0) v3727_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3727_pb : Scalar.QComplex := ((-570164022503256597391968 : Int)/10^30,(-431477143638547106221367724 : Int)/10^30)
theorem v3727_pb_checked : Scalar.distance (sourceCoefficient 52 62 1 1) v3727_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3727_pg : Scalar.QComplex := ((-93086348555261376632719 : Int)/10^30,(123006485314246644940 : Int)/10^30)
theorem v3727_pg_checked : Scalar.distance (sourceCoefficient 52 62 1 2) v3727_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3727_mb : Scalar.QComplex := ((-942509152156037118032855 : Int)/10^30,(-431476490954014863969057220 : Int)/10^30)
theorem v3727_mb_checked : Scalar.distance (sourceCoefficient 52 62 3 1) v3727_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3727_mg : Scalar.QComplex := ((-93086207745902733464401 : Int)/10^30,(203335765862993317127 : Int)/10^30)
theorem v3727_mg_checked : Scalar.distance (sourceCoefficient 52 62 3 2) v3727_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3727_upper : Scalar.QComplex := ((999995356884892244049551701886 : Int)/10^30,(-3047328117711316794432825050 : Int)/10^30)
theorem v3727_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 62 5) 1) 14) v3727_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3727 : Material (52 : Basis) (62 : Basis) where
  plus := ![v3727_pa,v3727_pb,v3727_pg]
  minus := ![(Primitive.Addresses.material3727 1).one,v3727_mb,v3727_mg]
  upper := v3727_upper
  lower := (Primitive.Addresses.material3727 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3727_pa_checked.trans (by decide +kernel)
    · exact v3727_pb_checked.trans (by decide +kernel)
    · exact v3727_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 62 Primitive.Addresses.material3727
    · exact v3727_mb_checked.trans (by decide +kernel)
    · exact v3727_mg_checked.trans (by decide +kernel)
  upper_error := v3727_upper_checked
  lower_error := reuse_lower_error 52 62 Primitive.Addresses.material3727

def v3728_pa : Scalar.QComplex := ((999999093848859617750180933106 : Int)/10^30,(-1346217463731105525908429819 : Int)/10^30)
theorem v3728_pa_checked : Scalar.distance (sourceCoefficient 52 63 1 0) v3728_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3728_pb : Scalar.QComplex := ((-580862572590532170783212 : Int)/10^30,(-431477128985805095889246226 : Int)/10^30)
theorem v3728_pb_checked : Scalar.distance (sourceCoefficient 52 63 1 1) v3728_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3728_pg : Scalar.QComplex := ((-93086345435388123413810 : Int)/10^30,(125314577413973001648 : Int)/10^30)
theorem v3728_pg_checked : Scalar.distance (sourceCoefficient 52 63 1 2) v3728_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3728_mb : Scalar.QComplex := ((-953207685615097126123485 : Int)/10^30,(-431476467068911429012640523 : Int)/10^30)
theorem v3728_mb_checked : Scalar.distance (sourceCoefficient 52 63 3 1) v3728_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3728_mg : Scalar.QComplex := ((-93086202634251112462314 : Int)/10^30,(205643854411001396435 : Int)/10^30)
theorem v3728_mg_checked : Scalar.distance (sourceCoefficient 52 63 3 2) v3728_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3728_upper : Scalar.QComplex := ((999995281018462969535204414667 : Int)/10^30,(-3072123175472328413645000907 : Int)/10^30)
theorem v3728_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 52 63 5) 1) 14) v3728_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3728 : Material (52 : Basis) (63 : Basis) where
  plus := ![v3728_pa,v3728_pb,v3728_pg]
  minus := ![(Primitive.Addresses.material3728 1).one,v3728_mb,v3728_mg]
  upper := v3728_upper
  lower := (Primitive.Addresses.material3728 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3728_pa_checked.trans (by decide +kernel)
    · exact v3728_pb_checked.trans (by decide +kernel)
    · exact v3728_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 52 63 Primitive.Addresses.material3728
    · exact v3728_mb_checked.trans (by decide +kernel)
    · exact v3728_mg_checked.trans (by decide +kernel)
  upper_error := v3728_upper_checked
  lower_error := reuse_lower_error 52 63 Primitive.Addresses.material3728

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
