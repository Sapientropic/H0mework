import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B164

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3937_pa : Scalar.QComplex := ((999999078229405986555636418889 : Int)/10^30,(-1357770355533608171898630693 : Int)/10^30)
theorem v3937_pa_checked : Scalar.distance (sourceCoefficient 57 62 1 0) v3937_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3937_pb : Scalar.QComplex := ((-585847386758598865196288 : Int)/10^30,(-431477123030474069130902864 : Int)/10^30)
theorem v3937_pb_checked : Scalar.distance (sourceCoefficient 57 62 1 1) v3937_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3937_pg : Scalar.QComplex := ((-93086344066010637976637 : Int)/10^30,(126389994980411791696 : Int)/10^30)
theorem v3937_pg_checked : Scalar.distance (sourceCoefficient 57 62 1 2) v3937_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3937_mb : Scalar.QComplex := ((-958192492787907230563718 : Int)/10^30,(-431476456811912500350665518 : Int)/10^30)
theorem v3937_mb_checked : Scalar.distance (sourceCoefficient 57 62 3 1) v3937_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3937_mg : Scalar.QComplex := ((-93086200336837212079486 : Int)/10^30,(206719270395301982026 : Int)/10^30)
theorem v3937_mg_checked : Scalar.distance (sourceCoefficient 57 62 3 2) v3937_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3937_upper : Scalar.QComplex := ((999995245459789420719734940269 : Int)/10^30,(-3083676023110395836132320481 : Int)/10^30)
theorem v3937_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 62 5) 1) 14) v3937_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3937 : Material (57 : Basis) (62 : Basis) where
  plus := ![v3937_pa,v3937_pb,v3937_pg]
  minus := ![(Primitive.Addresses.material3937 1).one,v3937_mb,v3937_mg]
  upper := v3937_upper
  lower := (Primitive.Addresses.material3937 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3937_pa_checked.trans (by decide +kernel)
    · exact v3937_pb_checked.trans (by decide +kernel)
    · exact v3937_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 62 Primitive.Addresses.material3937
    · exact v3937_mb_checked.trans (by decide +kernel)
    · exact v3937_mg_checked.trans (by decide +kernel)
  upper_error := v3937_upper_checked
  lower_error := reuse_lower_error 57 62 Primitive.Addresses.material3937

def v3938_pa : Scalar.QComplex := ((999999044255853968009845184354 : Int)/10^30,(-1382565506085374471654828399 : Int)/10^30)
theorem v3938_pa_checked : Scalar.distance (sourceCoefficient 57 63 1 0) v3938_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3938_pb : Scalar.QComplex := ((-596545936495372652852302 : Int)/10^30,(-431477108118484244964062483 : Int)/10^30)
theorem v3938_pb_checked : Scalar.distance (sourceCoefficient 57 63 1 1) v3938_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3938_pg : Scalar.QComplex := ((-93086340876225128566728 : Int)/10^30,(128698086985617117437 : Int)/10^30)
theorem v3938_pg_checked : Scalar.distance (sourceCoefficient 57 63 1 2) v3938_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3938_mb : Scalar.QComplex := ((-968891025672746396175686 : Int)/10^30,(-431476432667561650556594315 : Int)/10^30)
theorem v3938_mb_checked : Scalar.distance (sourceCoefficient 57 63 3 1) v3938_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3938_mg : Scalar.QComplex := ((-93086195155273442485319 : Int)/10^30,(209027358788457937200 : Int)/10^30)
theorem v3938_mg_checked : Scalar.distance (sourceCoefficient 57 63 3 2) v3938_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3938_upper : Scalar.QComplex := ((999995168692107547926947738168 : Int)/10^30,(-3108471078097429304571817791 : Int)/10^30)
theorem v3938_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 63 5) 1) 14) v3938_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3938 : Material (57 : Basis) (63 : Basis) where
  plus := ![v3938_pa,v3938_pb,v3938_pg]
  minus := ![(Primitive.Addresses.material3938 1).one,v3938_mb,v3938_mg]
  upper := v3938_upper
  lower := (Primitive.Addresses.material3938 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3938_pa_checked.trans (by decide +kernel)
    · exact v3938_pb_checked.trans (by decide +kernel)
    · exact v3938_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 63 Primitive.Addresses.material3938
    · exact v3938_mb_checked.trans (by decide +kernel)
    · exact v3938_mg_checked.trans (by decide +kernel)
  upper_error := v3938_upper_checked
  lower_error := reuse_lower_error 57 63 Primitive.Addresses.material3938

def v3939_pa : Scalar.QComplex := ((999998994633605329326499232366 : Int)/10^30,(-1418002742796980441872676902 : Int)/10^30)
theorem v3939_pa_checked : Scalar.distance (sourceCoefficient 57 64 1 0) v3939_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3939_pb : Scalar.QComplex := ((-611836306794362217295708 : Int)/10^30,(-431477086192278694490853608 : Int)/10^30)
theorem v3939_pb_checked : Scalar.distance (sourceCoefficient 57 64 1 1) v3939_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3939_pg : Scalar.QComplex := ((-93086336201479830397414 : Int)/10^30,(131996812755780001618 : Int)/10^30)
theorem v3939_pg_checked : Scalar.distance (sourceCoefficient 57 64 1 2) v3939_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3939_mb : Scalar.QComplex := ((-984181371357104423442135 : Int)/10^30,(-431476397546463348898070953 : Int)/10^30)
theorem v3939_mb_checked : Scalar.distance (sourceCoefficient 57 64 3 1) v3939_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3939_mg : Scalar.QComplex := ((-93086187633878114380301 : Int)/10^30,(212326079296259808326 : Int)/10^30)
theorem v3939_mg_checked : Scalar.distance (sourceCoefficient 57 64 3 2) v3939_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3939_upper : Scalar.QComplex := ((999995057908477092523522864871 : Int)/10^30,(-3143908176385934487957707389 : Int)/10^30)
theorem v3939_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 64 5) 1) 14) v3939_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3939 : Material (57 : Basis) (64 : Basis) where
  plus := ![v3939_pa,v3939_pb,v3939_pg]
  minus := ![(Primitive.Addresses.material3939 1).one,v3939_mb,v3939_mg]
  upper := v3939_upper
  lower := (Primitive.Addresses.material3939 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3939_pa_checked.trans (by decide +kernel)
    · exact v3939_pb_checked.trans (by decide +kernel)
    · exact v3939_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 64 Primitive.Addresses.material3939
    · exact v3939_mb_checked.trans (by decide +kernel)
    · exact v3939_mg_checked.trans (by decide +kernel)
  upper_error := v3939_upper_checked
  lower_error := reuse_lower_error 57 64 Primitive.Addresses.material3939

def v3940_pa : Scalar.QComplex := ((999998942986042940047858244337 : Int)/10^30,(-1453969324587488972232206605 : Int)/10^30)
theorem v3940_pa_checked : Scalar.distance (sourceCoefficient 57 65 1 0) v3940_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3940_pb : Scalar.QComplex := ((-627355077278700664478102 : Int)/10^30,(-431477063199814752120320903 : Int)/10^30)
theorem v3940_pb_checked : Scalar.distance (sourceCoefficient 57 65 1 1) v3940_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3940_pg : Scalar.QComplex := ((-93086331317453281886517 : Int)/10^30,(135344813335321481889 : Int)/10^30)
theorem v3940_pg_checked : Scalar.distance (sourceCoefficient 57 65 1 2) v3940_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3940_mb : Scalar.QComplex := ((-999700116221634536325948 : Int)/10^30,(-431476361162007979165353219 : Int)/10^30)
theorem v3940_mb_checked : Scalar.distance (sourceCoefficient 57 65 3 1) v3940_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3940_mg : Scalar.QComplex := ((-93086179860679672619977 : Int)/10^30,(215674074414492718674 : Int)/10^30)
theorem v3940_mg_checked : Scalar.distance (sourceCoefficient 57 65 3 2) v3940_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3940_upper : Scalar.QComplex := ((999994944185934318616337840727 : Int)/10^30,(-3179874615469437119201592188 : Int)/10^30)
theorem v3940_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 65 5) 1) 14) v3940_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3940 : Material (57 : Basis) (65 : Basis) where
  plus := ![v3940_pa,v3940_pb,v3940_pg]
  minus := ![(Primitive.Addresses.material3940 1).one,v3940_mb,v3940_mg]
  upper := v3940_upper
  lower := (Primitive.Addresses.material3940 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3940_pa_checked.trans (by decide +kernel)
    · exact v3940_pb_checked.trans (by decide +kernel)
    · exact v3940_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 65 Primitive.Addresses.material3940
    · exact v3940_mb_checked.trans (by decide +kernel)
    · exact v3940_mg_checked.trans (by decide +kernel)
  upper_error := v3940_upper_checked
  lower_error := reuse_lower_error 57 65 Primitive.Addresses.material3940

def v3941_pa : Scalar.QComplex := ((999998917259599642714057875845 : Int)/10^30,(-1471556872291314916406302059 : Int)/10^30)
theorem v3941_pa_checked : Scalar.distance (sourceCoefficient 57 66 1 0) v3941_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3941_pb : Scalar.QComplex := ((-634943708123195777383774 : Int)/10^30,(-431477051685634979992828420 : Int)/10^30)
theorem v3941_pb_checked : Scalar.distance (sourceCoefficient 57 66 1 1) v3941_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3941_pg : Scalar.QComplex := ((-93086328878034408097881 : Int)/10^30,(136981975292759789419 : Int)/10^30)
theorem v3941_pg_checked : Scalar.distance (sourceCoefficient 57 66 1 2) v3941_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3941_mb : Scalar.QComplex := ((-1007288734304317004323698 : Int)/10^30,(-431476343099185854739725550 : Int)/10^30)
theorem v3941_mb_checked : Scalar.distance (sourceCoefficient 57 66 3 1) v3941_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3941_mg : Scalar.QComplex := ((-93086176008464672906606 : Int)/10^30,(217311233657232186720 : Int)/10^30)
theorem v3941_mg_checked : Scalar.distance (sourceCoefficient 57 66 3 2) v3941_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3941_upper : Scalar.QComplex := ((999994888105017530858304663381 : Int)/10^30,(-3197462092577169490513795869 : Int)/10^30)
theorem v3941_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 66 5) 1) 14) v3941_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3941 : Material (57 : Basis) (66 : Basis) where
  plus := ![v3941_pa,v3941_pb,v3941_pg]
  minus := ![(Primitive.Addresses.material3941 1).one,v3941_mb,v3941_mg]
  upper := v3941_upper
  lower := (Primitive.Addresses.material3941 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3941_pa_checked.trans (by decide +kernel)
    · exact v3941_pb_checked.trans (by decide +kernel)
    · exact v3941_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 66 Primitive.Addresses.material3941
    · exact v3941_mb_checked.trans (by decide +kernel)
    · exact v3941_mg_checked.trans (by decide +kernel)
  upper_error := v3941_upper_checked
  lower_error := reuse_lower_error 57 66 Primitive.Addresses.material3941

def v3942_pa : Scalar.QComplex := ((999998873387796613845069073276 : Int)/10^30,(-1501073994684223767445524442 : Int)/10^30)
theorem v3942_pa_checked : Scalar.distance (sourceCoefficient 57 67 1 0) v3942_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3942_pb : Scalar.QComplex := ((-647679681664737500363113 : Int)/10^30,(-431477031961475319007421211 : Int)/10^30)
theorem v3942_pb_checked : Scalar.distance (sourceCoefficient 57 67 1 1) v3942_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3942_pg : Scalar.QComplex := ((-93086324708466672631932 : Int)/10^30,(139729618701704433528 : Int)/10^30)
theorem v3942_pg_checked : Scalar.distance (sourceCoefficient 57 67 1 2) v3942_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3942_mb : Scalar.QComplex := ((-1020024686082612270785598 : Int)/10^30,(-431476312384461978564911792 : Int)/10^30)
theorem v3942_mb_checked : Scalar.distance (sourceCoefficient 57 67 3 1) v3942_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3942_mg : Scalar.QComplex := ((-93086169467805977307405 : Int)/10^30,(220058872444954450824 : Int)/10^30)
theorem v3942_mg_checked : Scalar.distance (sourceCoefficient 57 67 3 2) v3942_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3942_upper : Scalar.QComplex := ((999994793289404366151580891817 : Int)/10^30,(-3226979095289039853130538811 : Int)/10^30)
theorem v3942_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 67 5) 1) 14) v3942_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3942 : Material (57 : Basis) (67 : Basis) where
  plus := ![v3942_pa,v3942_pb,v3942_pg]
  minus := ![(Primitive.Addresses.material3942 1).one,v3942_mb,v3942_mg]
  upper := v3942_upper
  lower := (Primitive.Addresses.material3942 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3942_pa_checked.trans (by decide +kernel)
    · exact v3942_pb_checked.trans (by decide +kernel)
    · exact v3942_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 67 Primitive.Addresses.material3942
    · exact v3942_mb_checked.trans (by decide +kernel)
    · exact v3942_mg_checked.trans (by decide +kernel)
  upper_error := v3942_upper_checked
  lower_error := reuse_lower_error 57 67 Primitive.Addresses.material3942

def v3943_pa : Scalar.QComplex := ((999998798389774343716767279064 : Int)/10^30,(-1550231920534934690098435861 : Int)/10^30)
theorem v3943_pa_checked : Scalar.distance (sourceCoefficient 57 68 1 0) v3943_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3943_pb : Scalar.QComplex := ((-668890219021964135702893 : Int)/10^30,(-431476998000289597462271658 : Int)/10^30)
theorem v3943_pb_checked : Scalar.distance (sourceCoefficient 57 68 1 1) v3943_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3943_pg : Scalar.QComplex := ((-93086317554445375862005 : Int)/10^30,(144305554236982250146 : Int)/10^30)
theorem v3943_pg_checked : Scalar.distance (sourceCoefficient 57 68 1 2) v3943_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3943_mb : Scalar.QComplex := ((-1041235186235212755916537 : Int)/10^30,(-431476260119550450175366860 : Int)/10^30)
theorem v3943_mb_checked : Scalar.distance (sourceCoefficient 57 68 3 1) v3943_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3943_mg : Scalar.QComplex := ((-93086158364961069847803 : Int)/10^30,(224634800102804163119 : Int)/10^30)
theorem v3943_mg_checked : Scalar.distance (sourceCoefficient 57 68 3 2) v3943_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3943_upper : Scalar.QComplex := ((999994633449373350637421649046 : Int)/10^30,(-3276136818485012045946930453 : Int)/10^30)
theorem v3943_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 68 5) 1) 14) v3943_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3943 : Material (57 : Basis) (68 : Basis) where
  plus := ![v3943_pa,v3943_pb,v3943_pg]
  minus := ![(Primitive.Addresses.material3943 1).one,v3943_mb,v3943_mg]
  upper := v3943_upper
  lower := (Primitive.Addresses.material3943 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3943_pa_checked.trans (by decide +kernel)
    · exact v3943_pb_checked.trans (by decide +kernel)
    · exact v3943_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 68 Primitive.Addresses.material3943
    · exact v3943_mb_checked.trans (by decide +kernel)
    · exact v3943_mg_checked.trans (by decide +kernel)
  upper_error := v3943_upper_checked
  lower_error := reuse_lower_error 57 68 Primitive.Addresses.material3943

def v3944_pa : Scalar.QComplex := ((999998764615860893989867398236 : Int)/10^30,(-1571867281941465028375820330 : Int)/10^30)
theorem v3944_pa_checked : Scalar.distance (sourceCoefficient 57 69 1 0) v3944_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3944_pb : Scalar.QComplex := ((-678225389748666130069991 : Int)/10^30,(-431476982612730143020825948 : Int)/10^30)
theorem v3944_pb_checked : Scalar.distance (sourceCoefficient 57 69 1 1) v3944_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3944_pg : Scalar.QComplex := ((-93086314322652283968958 : Int)/10^30,(146319512641101470404 : Int)/10^30)
theorem v3944_pg_checked : Scalar.distance (sourceCoefficient 57 69 1 2) v3944_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3944_mb : Scalar.QComplex := ((-1050570340207233271122288 : Int)/10^30,(-431476236676164828563777435 : Int)/10^30)
theorem v3944_mb_checked : Scalar.distance (sourceCoefficient 57 69 3 1) v3944_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3944_mg : Scalar.QComplex := ((-93086153395213783863518 : Int)/10^30,(226648754968142743331 : Int)/10^30)
theorem v3944_mg_checked : Scalar.distance (sourceCoefficient 57 69 3 2) v3944_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3944_upper : Scalar.QComplex := ((999994562334839160170559295840 : Int)/10^30,(-3297772089377502368541883775 : Int)/10^30)
theorem v3944_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 69 5) 1) 14) v3944_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3944 : Material (57 : Basis) (69 : Basis) where
  plus := ![v3944_pa,v3944_pb,v3944_pg]
  minus := ![(Primitive.Addresses.material3944 1).one,v3944_mb,v3944_mg]
  upper := v3944_upper
  lower := (Primitive.Addresses.material3944 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3944_pa_checked.trans (by decide +kernel)
    · exact v3944_pb_checked.trans (by decide +kernel)
    · exact v3944_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 69 Primitive.Addresses.material3944
    · exact v3944_mb_checked.trans (by decide +kernel)
    · exact v3944_mg_checked.trans (by decide +kernel)
  upper_error := v3944_upper_checked
  lower_error := reuse_lower_error 57 69 Primitive.Addresses.material3944

def v3945_pa : Scalar.QComplex := ((999998742143824617732412349910 : Int)/10^30,(-1586099230364348051496599844 : Int)/10^30)
theorem v3945_pa_checked : Scalar.distance (sourceCoefficient 57 70 1 0) v3945_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3945_pb : Scalar.QComplex := ((-684366154588650248952555 : Int)/10^30,(-431476972343810218522164121 : Int)/10^30)
theorem v3945_pb_checked : Scalar.distance (sourceCoefficient 57 70 1 1) v3945_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3945_pg : Scalar.QComplex := ((-93086312169029389996411 : Int)/10^30,(147644313804064840301 : Int)/10^30)
theorem v3945_pg_checked : Scalar.distance (sourceCoefficient 57 70 1 2) v3945_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3945_mb : Scalar.QComplex := ((-1056711093899114593403777 : Int)/10^30,(-431476221108045240528661726 : Int)/10^30)
theorem v3945_mb_checked : Scalar.distance (sourceCoefficient 57 70 3 1) v3945_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3945_mg : Scalar.QComplex := ((-93086150098347954975256 : Int)/10^30,(227973553779342531929 : Int)/10^30)
theorem v3945_mg_checked : Scalar.distance (sourceCoefficient 57 70 3 2) v3945_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3945_upper : Scalar.QComplex := ((999994515299784487750597348645 : Int)/10^30,(-3312003977818874052263421081 : Int)/10^30)
theorem v3945_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 70 5) 1) 14) v3945_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3945 : Material (57 : Basis) (70 : Basis) where
  plus := ![v3945_pa,v3945_pb,v3945_pg]
  minus := ![(Primitive.Addresses.material3945 1).one,v3945_mb,v3945_mg]
  upper := v3945_upper
  lower := (Primitive.Addresses.material3945 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3945_pa_checked.trans (by decide +kernel)
    · exact v3945_pb_checked.trans (by decide +kernel)
    · exact v3945_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 70 Primitive.Addresses.material3945
    · exact v3945_mb_checked.trans (by decide +kernel)
    · exact v3945_mg_checked.trans (by decide +kernel)
  upper_error := v3945_upper_checked
  lower_error := reuse_lower_error 57 70 Primitive.Addresses.material3945

def v3946_pa : Scalar.QComplex := ((999998703317936960020827253760 : Int)/10^30,(-1610392015844460691815727122 : Int)/10^30)
theorem v3946_pa_checked : Scalar.distance (sourceCoefficient 57 71 1 0) v3946_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3946_pb : Scalar.QComplex := ((-694847943619251120235603 : Int)/10^30,(-431476954546387738639614755 : Int)/10^30)
theorem v3946_pb_checked : Scalar.distance (sourceCoefficient 57 71 1 1) v3946_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3946_pg : Scalar.QComplex := ((-93086308442150733581538 : Int)/10^30,(149905642279631851698 : Int)/10^30)
theorem v3946_pg_checked : Scalar.distance (sourceCoefficient 57 71 1 2) v3946_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3946_mb : Scalar.QComplex := ((-1067192863668492333184615 : Int)/10^30,(-431476194265317536284753361 : Int)/10^30)
theorem v3946_mb_checked : Scalar.distance (sourceCoefficient 57 71 3 1) v3946_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3946_mg : Scalar.QComplex := ((-93086144420046058287123 : Int)/10^30,(230234878196785175953 : Int)/10^30)
theorem v3946_mg_checked : Scalar.distance (sourceCoefficient 57 71 3 2) v3946_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3946_upper : Scalar.QComplex := ((999994434546810742246877345700 : Int)/10^30,(-3336296660107776510797661801 : Int)/10^30)
theorem v3946_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 71 5) 1) 14) v3946_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3946 : Material (57 : Basis) (71 : Basis) where
  plus := ![v3946_pa,v3946_pb,v3946_pg]
  minus := ![(Primitive.Addresses.material3946 1).one,v3946_mb,v3946_mg]
  upper := v3946_upper
  lower := (Primitive.Addresses.material3946 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3946_pa_checked.trans (by decide +kernel)
    · exact v3946_pb_checked.trans (by decide +kernel)
    · exact v3946_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 71 Primitive.Addresses.material3946
    · exact v3946_mb_checked.trans (by decide +kernel)
    · exact v3946_mg_checked.trans (by decide +kernel)
  upper_error := v3946_upper_checked
  lower_error := reuse_lower_error 57 71 Primitive.Addresses.material3946

def v3947_pa : Scalar.QComplex := ((999998660516280681542205556130 : Int)/10^30,(-1636754607270216688812931173 : Int)/10^30)
theorem v3947_pa_checked : Scalar.distance (sourceCoefficient 57 72 1 0) v3947_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3947_pb : Scalar.QComplex := ((-706222807017979263661162 : Int)/10^30,(-431476934848447188798986439 : Int)/10^30)
theorem v3947_pb_checked : Scalar.distance (sourceCoefficient 57 72 1 1) v3947_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3947_pg : Scalar.QComplex := ((-93086304325219307818775 : Int)/10^30,(152359641561319553870 : Int)/10^30)
theorem v3947_pg_checked : Scalar.distance (sourceCoefficient 57 72 1 2) v3947_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3947_mb : Scalar.QComplex := ((-1078567705833403444121800 : Int)/10^30,(-431476164751389512615073831 : Int)/10^30)
theorem v3947_mb_checked : Scalar.distance (sourceCoefficient 57 72 3 1) v3947_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3947_mg : Scalar.QComplex := ((-93086138185425309374399 : Int)/10^30,(232688873012010391520 : Int)/10^30)
theorem v3947_mg_checked : Scalar.distance (sourceCoefficient 57 72 3 2) v3947_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3947_upper : Scalar.QComplex := ((999994346245777006564620799717 : Int)/10^30,(-3362659138397773545927883151 : Int)/10^30)
theorem v3947_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 72 5) 1) 14) v3947_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3947 : Material (57 : Basis) (72 : Basis) where
  plus := ![v3947_pa,v3947_pb,v3947_pg]
  minus := ![(Primitive.Addresses.material3947 1).one,v3947_mb,v3947_mg]
  upper := v3947_upper
  lower := (Primitive.Addresses.material3947 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3947_pa_checked.trans (by decide +kernel)
    · exact v3947_pb_checked.trans (by decide +kernel)
    · exact v3947_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 72 Primitive.Addresses.material3947
    · exact v3947_mb_checked.trans (by decide +kernel)
    · exact v3947_mg_checked.trans (by decide +kernel)
  upper_error := v3947_upper_checked
  lower_error := reuse_lower_error 57 72 Primitive.Addresses.material3947

def v3948_pa : Scalar.QComplex := ((999998645004886756575896597377 : Int)/10^30,(-1646204237169583795153595103 : Int)/10^30)
theorem v3948_pa_checked : Scalar.distance (sourceCoefficient 57 73 1 0) v3948_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3948_pb : Scalar.QComplex := ((-710300109058036978779422 : Int)/10^30,(-431476927690405873951813130 : Int)/10^30)
theorem v3948_pb_checked : Scalar.distance (sourceCoefficient 57 73 1 1) v3948_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3948_pg : Scalar.QComplex := ((-93086302831135650114293 : Int)/10^30,(153239273781533662200 : Int)/10^30)
theorem v3948_pg_checked : Scalar.distance (sourceCoefficient 57 73 1 2) v3948_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3948_mb : Scalar.QComplex := ((-1082645000178227999318036 : Int)/10^30,(-431476154074822837331050048 : Int)/10^30)
theorem v3948_mb_checked : Scalar.distance (sourceCoefficient 57 73 3 1) v3948_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3948_mg : Scalar.QComplex := ((-93086135932259219105311 : Int)/10^30,(233568503615370317517 : Int)/10^30)
theorem v3948_mg_checked : Scalar.distance (sourceCoefficient 57 73 3 2) v3948_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3948_upper : Scalar.QComplex := ((999994314425202241417735047523 : Int)/10^30,(-3372108727451768216837398011 : Int)/10^30)
theorem v3948_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 73 5) 1) 14) v3948_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3948 : Material (57 : Basis) (73 : Basis) where
  plus := ![v3948_pa,v3948_pb,v3948_pg]
  minus := ![(Primitive.Addresses.material3948 1).one,v3948_mb,v3948_mg]
  upper := v3948_upper
  lower := (Primitive.Addresses.material3948 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3948_pa_checked.trans (by decide +kernel)
    · exact v3948_pb_checked.trans (by decide +kernel)
    · exact v3948_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 73 Primitive.Addresses.material3948
    · exact v3948_mb_checked.trans (by decide +kernel)
    · exact v3948_mg_checked.trans (by decide +kernel)
  upper_error := v3948_upper_checked
  lower_error := reuse_lower_error 57 73 Primitive.Addresses.material3948

def v3949_pa : Scalar.QComplex := ((999998627443983946991783330026 : Int)/10^30,(-1656837393408296790796624776 : Int)/10^30)
theorem v3949_pa_checked : Scalar.distance (sourceCoefficient 57 74 1 0) v3949_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3949_pb : Scalar.QComplex := ((-714888075967458981163494 : Int)/10^30,(-431476919574423720108939410 : Int)/10^30)
theorem v3949_pb_checked : Scalar.distance (sourceCoefficient 57 74 1 1) v3949_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3949_pg : Scalar.QComplex := ((-93086301138328770455373 : Int)/10^30,(154229076228094837610 : Int)/10^30)
theorem v3949_pg_checked : Scalar.distance (sourceCoefficient 57 74 1 2) v3949_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3949_mb : Scalar.QComplex := ((-1087232958375613172378800 : Int)/10^30,(-431476141999634896967035256 : Int)/10^30)
theorem v3949_mb_checked : Scalar.distance (sourceCoefficient 57 74 3 1) v3949_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3949_mg : Scalar.QComplex := ((-93086133385298037420803 : Int)/10^30,(234558304232566709911 : Int)/10^30)
theorem v3949_mg_checked : Scalar.distance (sourceCoefficient 57 74 3 2) v3949_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3949_upper : Scalar.QComplex := ((999994278512462551115558893939 : Int)/10^30,(-3382741837545118916506770883 : Int)/10^30)
theorem v3949_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 74 5) 1) 14) v3949_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3949 : Material (57 : Basis) (74 : Basis) where
  plus := ![v3949_pa,v3949_pb,v3949_pg]
  minus := ![(Primitive.Addresses.material3949 1).one,v3949_mb,v3949_mg]
  upper := v3949_upper
  lower := (Primitive.Addresses.material3949 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3949_pa_checked.trans (by decide +kernel)
    · exact v3949_pb_checked.trans (by decide +kernel)
    · exact v3949_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 74 Primitive.Addresses.material3949
    · exact v3949_mb_checked.trans (by decide +kernel)
    · exact v3949_mg_checked.trans (by decide +kernel)
  upper_error := v3949_upper_checked
  lower_error := reuse_lower_error 57 74 Primitive.Addresses.material3949

def v3950_pa : Scalar.QComplex := ((999998602787980457670979091502 : Int)/10^30,(-1671652501832611887011479661 : Int)/10^30)
theorem v3950_pa_checked : Scalar.distance (sourceCoefficient 57 75 1 0) v3950_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3950_pb : Scalar.QComplex := ((-721280460787095825730917 : Int)/10^30,(-431476908158027366399261652 : Int)/10^30)
theorem v3950_pb_checked : Scalar.distance (sourceCoefficient 57 75 1 1) v3950_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3950_pg : Scalar.QComplex := ((-93086298759279444007501 : Int)/10^30,(155608161624881199567 : Int)/10^30)
theorem v3950_pg_checked : Scalar.distance (sourceCoefficient 57 75 1 2) v3950_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3950_mb : Scalar.QComplex := ((-1093625330963237124330073 : Int)/10^30,(-431476125066902597081717989 : Int)/10^30)
theorem v3950_mb_checked : Scalar.distance (sourceCoefficient 57 75 3 1) v3950_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3950_mg : Scalar.QComplex := ((-93086129816161011075670 : Int)/10^30,(235937387062844131009 : Int)/10^30)
theorem v3950_mg_checked : Scalar.distance (sourceCoefficient 57 75 3 2) v3950_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3950_upper : Scalar.QComplex := ((999994228286962659785174270123 : Int)/10^30,(-3397556881350045072185674877 : Int)/10^30)
theorem v3950_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 75 5) 1) 14) v3950_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3950 : Material (57 : Basis) (75 : Basis) where
  plus := ![v3950_pa,v3950_pb,v3950_pg]
  minus := ![(Primitive.Addresses.material3950 1).one,v3950_mb,v3950_mg]
  upper := v3950_upper
  lower := (Primitive.Addresses.material3950 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3950_pa_checked.trans (by decide +kernel)
    · exact v3950_pb_checked.trans (by decide +kernel)
    · exact v3950_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 75 Primitive.Addresses.material3950
    · exact v3950_mb_checked.trans (by decide +kernel)
    · exact v3950_mg_checked.trans (by decide +kernel)
  upper_error := v3950_upper_checked
  lower_error := reuse_lower_error 57 75 Primitive.Addresses.material3950

def v3951_pa : Scalar.QComplex := ((999998581931776016540932997470 : Int)/10^30,(-1684082669303805365421443234 : Int)/10^30)
theorem v3951_pa_checked : Scalar.distance (sourceCoefficient 57 76 1 0) v3951_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3951_pb : Scalar.QComplex := ((-726643797369021300019406 : Int)/10^30,(-431476898482028793754317478 : Int)/10^30)
theorem v3951_pb_checked : Scalar.distance (sourceCoefficient 57 76 1 1) v3951_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3951_pg : Scalar.QComplex := ((-93086296744820620113112 : Int)/10^30,(156765241401431094710 : Int)/10^30)
theorem v3951_pg_checked : Scalar.distance (sourceCoefficient 57 76 1 2) v3951_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3951_mb : Scalar.QComplex := ((-1098988657198196295182720 : Int)/10^30,(-431476110762589712764253452 : Int)/10^30)
theorem v3951_mb_checked : Scalar.distance (sourceCoefficient 57 76 3 1) v3951_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3951_mg : Scalar.QComplex := ((-93086126803195203032419 : Int)/10^30,(237094464670173107021 : Int)/10^30)
theorem v3951_mg_checked : Scalar.distance (sourceCoefficient 57 76 3 2) v3951_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3951_upper : Scalar.QComplex := ((999994185977447882225979165494 : Int)/10^30,(-3409986994312047446990542276 : Int)/10^30)
theorem v3951_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 76 5) 1) 14) v3951_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3951 : Material (57 : Basis) (76 : Basis) where
  plus := ![v3951_pa,v3951_pb,v3951_pg]
  minus := ![(Primitive.Addresses.material3951 1).one,v3951_mb,v3951_mg]
  upper := v3951_upper
  lower := (Primitive.Addresses.material3951 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3951_pa_checked.trans (by decide +kernel)
    · exact v3951_pb_checked.trans (by decide +kernel)
    · exact v3951_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 76 Primitive.Addresses.material3951
    · exact v3951_mb_checked.trans (by decide +kernel)
    · exact v3951_mg_checked.trans (by decide +kernel)
  upper_error := v3951_upper_checked
  lower_error := reuse_lower_error 57 76 Primitive.Addresses.material3951

def v3952_pa : Scalar.QComplex := ((999998577081361826318115689764 : Int)/10^30,(-1686960358648036787523342508 : Int)/10^30)
theorem v3952_pa_checked : Scalar.distance (sourceCoefficient 57 77 1 0) v3952_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3952_pb : Scalar.QComplex := ((-727885455333071288822909 : Int)/10^30,(-431476896229281481512910805 : Int)/10^30)
theorem v3952_pb_checked : Scalar.distance (sourceCoefficient 57 77 1 1) v3952_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3952_pg : Scalar.QComplex := ((-93086296276064282201299 : Int)/10^30,(157033115196433236214 : Int)/10^30)
theorem v3952_pg_checked : Scalar.distance (sourceCoefficient 57 77 1 2) v3952_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3952_mb : Scalar.QComplex := ((-1100230312755900806906355 : Int)/10^30,(-431476107438348338547257641 : Int)/10^30)
theorem v3952_mb_checked : Scalar.distance (sourceCoefficient 57 77 3 1) v3952_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3952_mg : Scalar.QComplex := ((-93086126103276019161034 : Int)/10^30,(237362337960917984592 : Int)/10^30)
theorem v3952_mg_checked : Scalar.distance (sourceCoefficient 57 77 3 2) v3952_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3952_upper : Scalar.QComplex := ((999994176160410169919898700516 : Int)/10^30,(-3412864670998923761809384221 : Int)/10^30)
theorem v3952_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 77 5) 1) 14) v3952_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3952 : Material (57 : Basis) (77 : Basis) where
  plus := ![v3952_pa,v3952_pb,v3952_pg]
  minus := ![(Primitive.Addresses.material3952 1).one,v3952_mb,v3952_mg]
  upper := v3952_upper
  lower := (Primitive.Addresses.material3952 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3952_pa_checked.trans (by decide +kernel)
    · exact v3952_pb_checked.trans (by decide +kernel)
    · exact v3952_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 77 Primitive.Addresses.material3952
    · exact v3952_mb_checked.trans (by decide +kernel)
    · exact v3952_mg_checked.trans (by decide +kernel)
  upper_error := v3952_upper_checked
  lower_error := reuse_lower_error 57 77 Primitive.Addresses.material3952

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
