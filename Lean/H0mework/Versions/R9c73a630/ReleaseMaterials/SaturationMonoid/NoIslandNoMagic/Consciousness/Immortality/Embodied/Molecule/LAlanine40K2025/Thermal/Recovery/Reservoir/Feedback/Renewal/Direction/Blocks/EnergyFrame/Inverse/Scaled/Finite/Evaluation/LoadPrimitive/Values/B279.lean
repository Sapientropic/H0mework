import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B186

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4465_pa : Scalar.QComplex := ((999997482011718940916946282662 : Int)/10^30,(-2244096749664145508977285090 : Int)/10^30)
theorem v4465_pa_checked : Scalar.distance (sourceCoefficient 73 86 1 0) v4465_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4465_pb : Scalar.QComplex := ((-968277292274460002510106 : Int)/10^30,(-431476430019560670274899057 : Int)/10^30)
theorem v4465_pb_checked : Scalar.distance (sourceCoefficient 73 86 1 1) v4465_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4465_pg : Scalar.QComplex := ((-93086195018246514762668 : Int)/10^30,(208894953674095101580 : Int)/10^30)
theorem v4465_pg_checked : Scalar.distance (sourceCoefficient 73 86 1 2) v4465_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4465_mb : Scalar.QComplex := ((-1340621657870430423894969 : Int)/10^30,(-431475433781472684501089687 : Int)/10^30)
theorem v4465_mb_checked : Scalar.distance (sourceCoefficient 73 86 3 1) v4465_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4465_mg : Scalar.QComplex := ((-93085980091065118910637 : Int)/10^30,(289224069747110931135 : Int)/10^30)
theorem v4465_mg_checked : Scalar.distance (sourceCoefficient 73 86 3 2) v4465_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4465_upper : Scalar.QComplex := ((999992119525530386884824837545 : Int)/10^30,(-3969998342234964224345357649 : Int)/10^30)
theorem v4465_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 86 5) 1) 14) v4465_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4465 : Material (73 : Basis) (86 : Basis) where
  plus := ![v4465_pa,v4465_pb,v4465_pg]
  minus := ![(Primitive.Addresses.material4465 1).one,v4465_mb,v4465_mg]
  upper := v4465_upper
  lower := (Primitive.Addresses.material4465 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4465_pa_checked.trans (by decide +kernel)
    · exact v4465_pb_checked.trans (by decide +kernel)
    · exact v4465_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 86 Primitive.Addresses.material4465
    · exact v4465_mb_checked.trans (by decide +kernel)
    · exact v4465_mg_checked.trans (by decide +kernel)
  upper_error := v4465_upper_checked
  lower_error := reuse_lower_error 73 86 Primitive.Addresses.material4465

def v4466_pa : Scalar.QComplex := ((999997479844001710436300458198 : Int)/10^30,(-2245062503671751158538894586 : Int)/10^30)
theorem v4466_pa_checked : Scalar.distance (sourceCoefficient 73 87 1 0) v4466_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4466_pb : Scalar.QComplex := ((-968693993336806413590097 : Int)/10^30,(-431476429049326920975550411 : Int)/10^30)
theorem v4466_pb_checked : Scalar.distance (sourceCoefficient 73 87 1 1) v4466_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4466_pg : Scalar.QComplex := ((-93086194812695467678135 : Int)/10^30,(208984852257895431445 : Int)/10^30)
theorem v4466_pg_checked : Scalar.distance (sourceCoefficient 73 87 1 2) v4466_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4466_mb : Scalar.QComplex := ((-1341038357940351957344635 : Int)/10^30,(-431475432451645047178320039 : Int)/10^30)
theorem v4466_mb_checked : Scalar.distance (sourceCoefficient 73 87 3 1) v4466_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4466_mg : Scalar.QComplex := ((-93085979807935719424381 : Int)/10^30,(289313968120056613725 : Int)/10^30)
theorem v4466_mg_checked : Scalar.distance (sourceCoefficient 73 87 3 2) v4466_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4466_upper : Scalar.QComplex := ((999992115691012580356183260439 : Int)/10^30,(-3970964091062909438974572189 : Int)/10^30)
theorem v4466_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 87 5) 1) 14) v4466_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4466 : Material (73 : Basis) (87 : Basis) where
  plus := ![v4466_pa,v4466_pb,v4466_pg]
  minus := ![(Primitive.Addresses.material4466 1).one,v4466_mb,v4466_mg]
  upper := v4466_upper
  lower := (Primitive.Addresses.material4466 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4466_pa_checked.trans (by decide +kernel)
    · exact v4466_pb_checked.trans (by decide +kernel)
    · exact v4466_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 87 Primitive.Addresses.material4466
    · exact v4466_mb_checked.trans (by decide +kernel)
    · exact v4466_mg_checked.trans (by decide +kernel)
  upper_error := v4466_upper_checked
  lower_error := reuse_lower_error 73 87 Primitive.Addresses.material4466

def v4467_pa : Scalar.QComplex := ((999997453373835315259756661187 : Int)/10^30,(-2256822067435680191480969326 : Int)/10^30)
theorem v4467_pa_checked : Scalar.distance (sourceCoefficient 73 88 1 0) v4467_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4467_pb : Scalar.QComplex := ((-973767979720387831642471 : Int)/10^30,(-431476417192169636580163729 : Int)/10^30)
theorem v4467_pb_checked : Scalar.distance (sourceCoefficient 73 88 1 1) v4467_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4467_pg : Scalar.QComplex := ((-93086192301664556432375 : Int)/10^30,(210079507953929521447 : Int)/10^30)
theorem v4467_pg_checked : Scalar.distance (sourceCoefficient 73 88 1 2) v4467_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4467_mb : Scalar.QComplex := ((-1346112332202463642263063 : Int)/10^30,(-431475416215870452577237353 : Int)/10^30)
theorem v4467_mb_checked : Scalar.distance (sourceCoefficient 73 88 3 1) v4467_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4467_mg : Scalar.QComplex := ((-93085976352267178935163 : Int)/10^30,(290408621241593776086 : Int)/10^30)
theorem v4467_mg_checked : Scalar.distance (sourceCoefficient 73 88 3 2) v4467_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4467_upper : Scalar.QComplex := ((999992068924945372132698722925 : Int)/10^30,(-3982723591627243777602694577 : Int)/10^30)
theorem v4467_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 88 5) 1) 14) v4467_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4467 : Material (73 : Basis) (88 : Basis) where
  plus := ![v4467_pa,v4467_pb,v4467_pg]
  minus := ![(Primitive.Addresses.material4467 1).one,v4467_mb,v4467_mg]
  upper := v4467_upper
  lower := (Primitive.Addresses.material4467 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4467_pa_checked.trans (by decide +kernel)
    · exact v4467_pb_checked.trans (by decide +kernel)
    · exact v4467_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 88 Primitive.Addresses.material4467
    · exact v4467_mb_checked.trans (by decide +kernel)
    · exact v4467_mg_checked.trans (by decide +kernel)
  upper_error := v4467_upper_checked
  lower_error := reuse_lower_error 73 88 Primitive.Addresses.material4467

def v4468_pa : Scalar.QComplex := ((999997416933296155191891347798 : Int)/10^30,(-2272911510696362262941306071 : Int)/10^30)
theorem v4468_pa_checked : Scalar.distance (sourceCoefficient 73 89 1 0) v4468_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4468_pb : Scalar.QComplex := ((-980710211303667730810160 : Int)/10^30,(-431476400840308520768129987 : Int)/10^30)
theorem v4468_pb_checked : Scalar.distance (sourceCoefficient 73 89 1 1) v4468_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4468_pg : Scalar.QComplex := ((-93086188841739503335458 : Int)/10^30,(211577216623308546492 : Int)/10^30)
theorem v4468_pg_checked : Scalar.distance (sourceCoefficient 73 89 1 2) v4468_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4468_mb : Scalar.QComplex := ((-1353054547089913764858727 : Int)/10^30,(-431475393873182235443645746 : Int)/10^30)
theorem v4468_mb_checked : Scalar.distance (sourceCoefficient 73 89 3 1) v4468_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4468_mg : Scalar.QComplex := ((-93085971599888286746817 : Int)/10^30,(291906326367547923270 : Int)/10^30)
theorem v4468_mg_checked : Scalar.distance (sourceCoefficient 73 89 3 2) v4468_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4468_upper : Scalar.QComplex := ((999992004715541040920711340398 : Int)/10^30,(-3998812948031525380659163575 : Int)/10^30)
theorem v4468_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 89 5) 1) 14) v4468_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4468 : Material (73 : Basis) (89 : Basis) where
  plus := ![v4468_pa,v4468_pb,v4468_pg]
  minus := ![(Primitive.Addresses.material4468 1).one,v4468_mb,v4468_mg]
  upper := v4468_upper
  lower := (Primitive.Addresses.material4468 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4468_pa_checked.trans (by decide +kernel)
    · exact v4468_pb_checked.trans (by decide +kernel)
    · exact v4468_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 89 Primitive.Addresses.material4468
    · exact v4468_mb_checked.trans (by decide +kernel)
    · exact v4468_mg_checked.trans (by decide +kernel)
  upper_error := v4468_upper_checked
  lower_error := reuse_lower_error 73 89 Primitive.Addresses.material4468

def v4469_pa : Scalar.QComplex := ((999997357033032210471708361672 : Int)/10^30,(-2299114383910609993533750978 : Int)/10^30)
theorem v4469_pa_checked : Scalar.distance (sourceCoefficient 73 90 1 0) v4469_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4469_pb : Scalar.QComplex := ((-992016159397012055897529 : Int)/10^30,(-431476373891296107003686862 : Int)/10^30)
theorem v4469_pb_checked : Scalar.distance (sourceCoefficient 73 90 1 1) v4469_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4469_pg : Scalar.QComplex := ((-93086183146815241125730 : Int)/10^30,(214016348254319333255 : Int)/10^30)
theorem v4469_pg_checked : Scalar.distance (sourceCoefficient 73 90 1 2) v4469_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4469_mb : Scalar.QComplex := ((-1364360467717752932824588 : Int)/10^30,(-431475357167655852471697028 : Int)/10^30)
theorem v4469_mb_checked : Scalar.distance (sourceCoefficient 73 90 3 1) v4469_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4469_mg : Scalar.QComplex := ((-93085963800105401866028 : Int)/10^30,(294345452175895381566 : Int)/10^30)
theorem v4469_mg_checked : Scalar.distance (sourceCoefficient 73 90 3 2) v4469_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4469_upper : Scalar.QComplex := ((999991899591584248904774550362 : Int)/10^30,(-4025015678837250005244562608 : Int)/10^30)
theorem v4469_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 90 5) 1) 14) v4469_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4469 : Material (73 : Basis) (90 : Basis) where
  plus := ![v4469_pa,v4469_pb,v4469_pg]
  minus := ![(Primitive.Addresses.material4469 1).one,v4469_mb,v4469_mg]
  upper := v4469_upper
  lower := (Primitive.Addresses.material4469 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4469_pa_checked.trans (by decide +kernel)
    · exact v4469_pb_checked.trans (by decide +kernel)
    · exact v4469_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 90 Primitive.Addresses.material4469
    · exact v4469_mb_checked.trans (by decide +kernel)
    · exact v4469_mg_checked.trans (by decide +kernel)
  upper_error := v4469_upper_checked
  lower_error := reuse_lower_error 73 90 Primitive.Addresses.material4469

def v4470_pa : Scalar.QComplex := ((999997322986697261142903847218 : Int)/10^30,(-2313875415634448360327836773 : Int)/10^30)
theorem v4470_pa_checked : Scalar.distance (sourceCoefficient 73 91 1 0) v4470_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4470_pb : Scalar.QComplex := ((-998385211134420698976136 : Int)/10^30,(-431476358536001717359542959 : Int)/10^30)
theorem v4470_pb_checked : Scalar.distance (sourceCoefficient 73 91 1 1) v4470_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4470_pg : Scalar.QComplex := ((-93086179905823189341572 : Int)/10^30,(215390399822375274105 : Int)/10^30)
theorem v4470_pg_checked : Scalar.distance (sourceCoefficient 73 91 1 2) v4470_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4470_mb : Scalar.QComplex := ((-1370729503832745052545789 : Int)/10^30,(-431475336316162382363593866 : Int)/10^30)
theorem v4470_mb_checked : Scalar.distance (sourceCoefficient 73 91 3 1) v4470_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4470_mg : Scalar.QComplex := ((-93085959373369938604401 : Int)/10^30,(295719500435498954543 : Int)/10^30)
theorem v4470_mg_checked : Scalar.distance (sourceCoefficient 73 91 3 2) v4470_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4470_upper : Scalar.QComplex := ((999991840069098362584923250569 : Int)/10^30,(-4039776629815380108809012719 : Int)/10^30)
theorem v4470_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 91 5) 1) 14) v4470_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4470 : Material (73 : Basis) (91 : Basis) where
  plus := ![v4470_pa,v4470_pb,v4470_pg]
  minus := ![(Primitive.Addresses.material4470 1).one,v4470_mb,v4470_mg]
  upper := v4470_upper
  lower := (Primitive.Addresses.material4470 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4470_pa_checked.trans (by decide +kernel)
    · exact v4470_pb_checked.trans (by decide +kernel)
    · exact v4470_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 91 Primitive.Addresses.material4470
    · exact v4470_mb_checked.trans (by decide +kernel)
    · exact v4470_mg_checked.trans (by decide +kernel)
  upper_error := v4470_upper_checked
  lower_error := reuse_lower_error 73 91 Primitive.Addresses.material4470

def v4471_pa : Scalar.QComplex := ((999997248533657425636077422728 : Int)/10^30,(-2345831433539437744910758162 : Int)/10^30)
theorem v4471_pa_checked : Scalar.distance (sourceCoefficient 73 92 1 0) v4471_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4471_pb : Scalar.QComplex := ((-1012173510655474366211300 : Int)/10^30,(-431476324864034822007706756 : Int)/10^30)
theorem v4471_pb_checked : Scalar.distance (sourceCoefficient 73 92 1 1) v4471_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4471_pg : Scalar.QComplex := ((-93086172808364983772280 : Int)/10^30,(218365071025889981008 : Int)/10^30)
theorem v4471_pg_checked : Scalar.distance (sourceCoefficient 73 92 1 2) v4471_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4471_mb : Scalar.QComplex := ((-1384517769162393750078327 : Int)/10^30,(-431475290745526539912354874 : Int)/10^30)
theorem v4471_mb_checked : Scalar.distance (sourceCoefficient 73 92 3 1) v4471_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4471_mg : Scalar.QComplex := ((-93085949708907101327627 : Int)/10^30,(298694164406620849433 : Int)/10^30)
theorem v4471_mg_checked : Scalar.distance (sourceCoefficient 73 92 3 2) v4471_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4471_upper : Scalar.QComplex := ((999991710462981539421767756324 : Int)/10^30,(-4071732471626442212391854550 : Int)/10^30)
theorem v4471_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 92 5) 1) 14) v4471_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4471 : Material (73 : Basis) (92 : Basis) where
  plus := ![v4471_pa,v4471_pb,v4471_pg]
  minus := ![(Primitive.Addresses.material4471 1).one,v4471_mb,v4471_mg]
  upper := v4471_upper
  lower := (Primitive.Addresses.material4471 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4471_pa_checked.trans (by decide +kernel)
    · exact v4471_pb_checked.trans (by decide +kernel)
    · exact v4471_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 92 Primitive.Addresses.material4471
    · exact v4471_mb_checked.trans (by decide +kernel)
    · exact v4471_mg_checked.trans (by decide +kernel)
  upper_error := v4471_upper_checked
  lower_error := reuse_lower_error 73 92 Primitive.Addresses.material4471

def v4472_pa : Scalar.QComplex := ((999997158847391352371346317325 : Int)/10^30,(-2383756939192230580666399209 : Int)/10^30)
theorem v4472_pa_checked : Scalar.distance (sourceCoefficient 73 93 1 0) v4472_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4472_pb : Scalar.QComplex := ((-1028537508646841023875730 : Int)/10^30,(-431476284139669285017860189 : Int)/10^30)
theorem v4472_pb_checked : Scalar.distance (sourceCoefficient 73 93 1 1) v4472_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4472_pg : Scalar.QComplex := ((-93086164241165549006943 : Int)/10^30,(221895420391418546338 : Int)/10^30)
theorem v4472_pg_checked : Scalar.distance (sourceCoefficient 73 93 1 2) v4472_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4472_mb : Scalar.QComplex := ((-1400881725917402782817563 : Int)/10^30,(-431475235899782907026108803 : Int)/10^30)
theorem v4472_mb_checked : Scalar.distance (sourceCoefficient 73 93 3 1) v4472_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4472_mg : Scalar.QComplex := ((-93085938095178355104055 : Int)/10^30,(302224505064531741176 : Int)/10^30)
theorem v4472_mg_checked : Scalar.distance (sourceCoefficient 73 93 3 2) v4472_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4472_upper : Scalar.QComplex := ((999991555320866861591153809005 : Int)/10^30,(-4109657766003290453202387008 : Int)/10^30)
theorem v4472_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 93 5) 1) 14) v4472_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4472 : Material (73 : Basis) (93 : Basis) where
  plus := ![v4472_pa,v4472_pb,v4472_pg]
  minus := ![(Primitive.Addresses.material4472 1).one,v4472_mb,v4472_mg]
  upper := v4472_upper
  lower := (Primitive.Addresses.material4472 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4472_pa_checked.trans (by decide +kernel)
    · exact v4472_pb_checked.trans (by decide +kernel)
    · exact v4472_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 93 Primitive.Addresses.material4472
    · exact v4472_mb_checked.trans (by decide +kernel)
    · exact v4472_mg_checked.trans (by decide +kernel)
  upper_error := v4472_upper_checked
  lower_error := reuse_lower_error 73 93 Primitive.Addresses.material4472

def v4473_pa : Scalar.QComplex := ((999997051055066563464177641623 : Int)/10^30,(-2428555367002541946308868048 : Int)/10^30)
theorem v4473_pa_checked : Scalar.distance (sourceCoefficient 73 94 1 0) v4473_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4473_pb : Scalar.QComplex := ((-1047867016270510884151018 : Int)/10^30,(-431476234969151332733463416 : Int)/10^30)
theorem v4473_pb_checked : Scalar.distance (sourceCoefficient 73 94 1 1) v4473_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4473_pg : Scalar.QComplex := ((-93086153920170662637810 : Int)/10^30,(226065545351299760593 : Int)/10^30)
theorem v4473_pg_checked : Scalar.distance (sourceCoefficient 73 94 1 2) v4473_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4473_mb : Scalar.QComplex := ((-1420211183911871117760092 : Int)/10^30,(-431475170048788752652000569 : Int)/10^30)
theorem v4473_mb_checked : Scalar.distance (sourceCoefficient 73 94 3 1) v4473_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4473_mg : Scalar.QComplex := ((-93085924175557286791678 : Int)/10^30,(306394619565131102159 : Int)/10^30)
theorem v4473_mg_checked : Scalar.distance (sourceCoefficient 73 94 3 2) v4473_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4473_upper : Scalar.QComplex := ((999991370210680297716253189085 : Int)/10^30,(-4154455941051832246042566318 : Int)/10^30)
theorem v4473_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 94 5) 1) 14) v4473_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4473 : Material (73 : Basis) (94 : Basis) where
  plus := ![v4473_pa,v4473_pb,v4473_pg]
  minus := ![(Primitive.Addresses.material4473 1).one,v4473_mb,v4473_mg]
  upper := v4473_upper
  lower := (Primitive.Addresses.material4473 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4473_pa_checked.trans (by decide +kernel)
    · exact v4473_pb_checked.trans (by decide +kernel)
    · exact v4473_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 94 Primitive.Addresses.material4473
    · exact v4473_mb_checked.trans (by decide +kernel)
    · exact v4473_mg_checked.trans (by decide +kernel)
  upper_error := v4473_upper_checked
  lower_error := reuse_lower_error 73 94 Primitive.Addresses.material4473

def v4474_pa : Scalar.QComplex := ((999996942552562524723064875660 : Int)/10^30,(-2472829457719581790511123484 : Int)/10^30)
theorem v4474_pa_checked : Scalar.distance (sourceCoefficient 73 95 1 0) v4474_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4474_pb : Scalar.QComplex := ((-1066970283370884668540568 : Int)/10^30,(-431476185239750445119929205 : Int)/10^30)
theorem v4474_pb_checked : Scalar.distance (sourceCoefficient 73 95 1 1) v4474_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4474_pg : Scalar.QComplex := ((-93086143505835391811797 : Int)/10^30,(230186861550972091577 : Int)/10^30)
theorem v4474_pg_checked : Scalar.distance (sourceCoefficient 73 95 1 2) v4474_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4474_mb : Scalar.QComplex := ((-1439314400984992261306682 : Int)/10^30,(-431475103834147253156009997 : Int)/10^30)
theorem v4474_mb_checked : Scalar.distance (sourceCoefficient 73 95 3 1) v4474_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4474_mg : Scalar.QComplex := ((-93085910204715630572623 : Int)/10^30,(310515925243146764076 : Int)/10^30)
theorem v4474_mg_checked : Scalar.distance (sourceCoefficient 73 95 3 2) v4474_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4474_upper : Scalar.QComplex := ((999991185295273797233098841707 : Int)/10^30,(-4198729778562336066653699821 : Int)/10^30)
theorem v4474_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 95 5) 1) 14) v4474_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4474 : Material (73 : Basis) (95 : Basis) where
  plus := ![v4474_pa,v4474_pb,v4474_pg]
  minus := ![(Primitive.Addresses.material4474 1).one,v4474_mb,v4474_mg]
  upper := v4474_upper
  lower := (Primitive.Addresses.material4474 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4474_pa_checked.trans (by decide +kernel)
    · exact v4474_pb_checked.trans (by decide +kernel)
    · exact v4474_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 95 Primitive.Addresses.material4474
    · exact v4474_mb_checked.trans (by decide +kernel)
    · exact v4474_mg_checked.trans (by decide +kernel)
  upper_error := v4474_upper_checked
  lower_error := reuse_lower_error 73 95 Primitive.Addresses.material4474

def v4475_pa : Scalar.QComplex := ((999996889743997731531413054711 : Int)/10^30,(-2494093488793982142465723560 : Int)/10^30)
theorem v4475_pa_checked : Scalar.distance (sourceCoefficient 73 96 1 0) v4475_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4475_pb : Scalar.QComplex := ((-1076145230694250847562508 : Int)/10^30,(-431476160954758645953871603 : Int)/10^30)
theorem v4475_pb_checked : Scalar.distance (sourceCoefficient 73 96 1 1) v4475_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4475_pg : Scalar.QComplex := ((-93086138428347873049114 : Int)/10^30,(232166253847602270084 : Int)/10^30)
theorem v4475_pg_checked : Scalar.distance (sourceCoefficient 73 96 1 2) v4475_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4475_mb : Scalar.QComplex := ((-1448489323935252068780312 : Int)/10^30,(-431475071631598180625103486 : Int)/10^30)
theorem v4475_mb_checked : Scalar.distance (sourceCoefficient 73 96 3 1) v4475_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4475_mg : Scalar.QComplex := ((-93085903419103598918444 : Int)/10^30,(312495312421115680707 : Int)/10^30)
theorem v4475_mg_checked : Scalar.distance (sourceCoefficient 73 96 3 2) v4475_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4475_upper : Scalar.QComplex := ((999991095786999079610466017523 : Int)/10^30,(-4219993686823667904369184068 : Int)/10^30)
theorem v4475_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 96 5) 1) 14) v4475_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4475 : Material (73 : Basis) (96 : Basis) where
  plus := ![v4475_pa,v4475_pb,v4475_pg]
  minus := ![(Primitive.Addresses.material4475 1).one,v4475_mb,v4475_mg]
  upper := v4475_upper
  lower := (Primitive.Addresses.material4475 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4475_pa_checked.trans (by decide +kernel)
    · exact v4475_pb_checked.trans (by decide +kernel)
    · exact v4475_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 96 Primitive.Addresses.material4475
    · exact v4475_mb_checked.trans (by decide +kernel)
    · exact v4475_mg_checked.trans (by decide +kernel)
  upper_error := v4475_upper_checked
  lower_error := reuse_lower_error 73 96 Primitive.Addresses.material4475

def v4476_pa : Scalar.QComplex := ((999996704594225995648064147136 : Int)/10^30,(-2567255477802995852531403728 : Int)/10^30)
theorem v4476_pa_checked : Scalar.distance (sourceCoefficient 73 97 1 0) v4476_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4476_pb : Scalar.QComplex := ((-1107712968504795436808426 : Int)/10^30,(-431476075411488775482997429 : Int)/10^30)
theorem v4476_pb_checked : Scalar.distance (sourceCoefficient 73 97 1 1) v4476_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4476_pg : Scalar.QComplex := ((-93086120583382314282567 : Int)/10^30,(238976640500119406539 : Int)/10^30)
theorem v4476_pg_checked : Scalar.distance (sourceCoefficient 73 97 1 2) v4476_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4476_mb : Scalar.QComplex := ((-1480056976171695981909572 : Int)/10^30,(-431474958846824189455986315 : Int)/10^30)
theorem v4476_mb_checked : Scalar.distance (sourceCoefficient 73 97 3 1) v4476_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4476_mg : Scalar.QComplex := ((-93085879697087731954375 : Int)/10^30,(319305681138413046583 : Int)/10^30)
theorem v4476_mg_checked : Scalar.distance (sourceCoefficient 73 97 3 2) v4476_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4476_upper : Scalar.QComplex := ((999990784366547276801141096954 : Int)/10^30,(-4293155247314783836397275371 : Int)/10^30)
theorem v4476_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 73 97 5) 1) 14) v4476_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4476 : Material (73 : Basis) (97 : Basis) where
  plus := ![v4476_pa,v4476_pb,v4476_pg]
  minus := ![(Primitive.Addresses.material4476 1).one,v4476_mb,v4476_mg]
  upper := v4476_upper
  lower := (Primitive.Addresses.material4476 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4476_pa_checked.trans (by decide +kernel)
    · exact v4476_pb_checked.trans (by decide +kernel)
    · exact v4476_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 73 97 Primitive.Addresses.material4476
    · exact v4476_mb_checked.trans (by decide +kernel)
    · exact v4476_mg_checked.trans (by decide +kernel)
  upper_error := v4476_upper_checked
  lower_error := reuse_lower_error 73 97 Primitive.Addresses.material4476

def v4477_pa : Scalar.QComplex := ((999997940943527295376478151124 : Int)/10^30,(-2029312372626671109779003604 : Int)/10^30)
theorem v4477_pa_checked : Scalar.distance (sourceCoefficient 74 75 1 0) v4477_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4477_pb : Scalar.QComplex := ((-875602671844878069041764 : Int)/10^30,(-431476632548286237531703223 : Int)/10^30)
theorem v4477_pb_checked : Scalar.distance (sourceCoefficient 74 75 1 1) v4477_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4477_pg : Scalar.QComplex := ((-93086238225057440294763 : Int)/10^30,(188901443910123626604 : Int)/10^30)
theorem v4477_pg_checked : Scalar.distance (sourceCoefficient 74 75 1 2) v4477_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4477_mb : Scalar.QComplex := ((-1247947246721013725099682 : Int)/10^30,(-431475716284146361825226276 : Int)/10^30)
theorem v4477_mb_checked : Scalar.distance (sourceCoefficient 74 75 3 1) v4477_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4477_mg : Scalar.QComplex := ((-93086040551358408627164 : Int)/10^30,(269230604713168756030 : Int)/10^30)
theorem v4477_mg_checked : Scalar.distance (sourceCoefficient 74 75 3 2) v4477_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4477_upper : Scalar.QComplex := ((999992949155004896530845806998 : Int)/10^30,(-3755215077168256328573232037 : Int)/10^30)
theorem v4477_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 75 5) 1) 14) v4477_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4477 : Material (74 : Basis) (75 : Basis) where
  plus := ![v4477_pa,v4477_pb,v4477_pg]
  minus := ![(Primitive.Addresses.material4477 1).one,v4477_mb,v4477_mg]
  upper := v4477_upper
  lower := (Primitive.Addresses.material4477 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4477_pa_checked.trans (by decide +kernel)
    · exact v4477_pb_checked.trans (by decide +kernel)
    · exact v4477_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 75 Primitive.Addresses.material4477
    · exact v4477_mb_checked.trans (by decide +kernel)
    · exact v4477_mg_checked.trans (by decide +kernel)
  upper_error := v4477_upper_checked
  lower_error := reuse_lower_error 74 75 Primitive.Addresses.material4477

def v4478_pa : Scalar.QComplex := ((999997915641544555797233093276 : Int)/10^30,(-2041742531843384691769331327 : Int)/10^30)
theorem v4478_pa_checked : Scalar.distance (sourceCoefficient 74 76 1 0) v4478_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4478_pb : Scalar.QComplex := ((-880966006052388554301751 : Int)/10^30,(-431476621593452079873772968 : Int)/10^30)
theorem v4478_pb_checked : Scalar.distance (sourceCoefficient 74 76 1 1) v4478_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4478_pg : Scalar.QComplex := ((-93086235865730592731691 : Int)/10^30,(190058523046356803822 : Int)/10^30)
theorem v4478_pg_checked : Scalar.distance (sourceCoefficient 74 76 1 2) v4478_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4478_mb : Scalar.QComplex := ((-1253310569477981277777497 : Int)/10^30,(-431475700701000417676905483 : Int)/10^30)
theorem v4478_mb_checked : Scalar.distance (sourceCoefficient 74 76 3 1) v4478_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4478_mg : Scalar.QComplex := ((-93086037193525257889846 : Int)/10^30,(270387681382575680389 : Int)/10^30)
theorem v4478_mg_checked : Scalar.distance (sourceCoefficient 74 76 3 2) v4478_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4478_upper : Scalar.QComplex := ((999992902399732688470450128204 : Int)/10^30,(-3767645174202781075770001681 : Int)/10^30)
theorem v4478_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 76 5) 1) 14) v4478_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4478 : Material (74 : Basis) (76 : Basis) where
  plus := ![v4478_pa,v4478_pb,v4478_pg]
  minus := ![(Primitive.Addresses.material4478 1).one,v4478_mb,v4478_mg]
  upper := v4478_upper
  lower := (Primitive.Addresses.material4478 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4478_pa_checked.trans (by decide +kernel)
    · exact v4478_pb_checked.trans (by decide +kernel)
    · exact v4478_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 76 Primitive.Addresses.material4478
    · exact v4478_mb_checked.trans (by decide +kernel)
    · exact v4478_mg_checked.trans (by decide +kernel)
  upper_error := v4478_upper_checked
  lower_error := reuse_lower_error 74 76 Primitive.Addresses.material4478

def v4479_pa : Scalar.QComplex := ((999997909761894931023760764091 : Int)/10^30,(-2044620219268756178981872037 : Int)/10^30)
theorem v4479_pa_checked : Scalar.distance (sourceCoefficient 74 77 1 0) v4479_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4479_pb : Scalar.QComplex := ((-882207663464475264129253 : Int)/10^30,(-431476619044643468509552043 : Int)/10^30)
theorem v4479_pb_checked : Scalar.distance (sourceCoefficient 74 77 1 1) v4479_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4479_pg : Scalar.QComplex := ((-93086235317134378355293 : Int)/10^30,(190326396692509095201 : Int)/10^30)
theorem v4479_pg_checked : Scalar.distance (sourceCoefficient 74 77 1 2) v4479_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4479_mb : Scalar.QComplex := ((-1254552224228235149009225 : Int)/10^30,(-431475697080698330893698007 : Int)/10^30)
theorem v4479_mb_checked : Scalar.distance (sourceCoefficient 74 77 3 1) v4479_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4479_mg : Scalar.QComplex := ((-93086036413766355732628 : Int)/10^30,(270655554455572545725 : Int)/10^30)
theorem v4479_mg_checked : Scalar.distance (sourceCoefficient 74 77 3 2) v4479_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4479_upper : Scalar.QComplex := ((999992891553464386317161923427 : Int)/10^30,(-3770522847194433325090766623 : Int)/10^30)
theorem v4479_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 77 5) 1) 14) v4479_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4479 : Material (74 : Basis) (77 : Basis) where
  plus := ![v4479_pa,v4479_pb,v4479_pg]
  minus := ![(Primitive.Addresses.material4479 1).one,v4479_mb,v4479_mg]
  upper := v4479_upper
  lower := (Primitive.Addresses.material4479 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4479_pa_checked.trans (by decide +kernel)
    · exact v4479_pb_checked.trans (by decide +kernel)
    · exact v4479_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 77 Primitive.Addresses.material4479
    · exact v4479_mb_checked.trans (by decide +kernel)
    · exact v4479_mg_checked.trans (by decide +kernel)
  upper_error := v4479_upper_checked
  lower_error := reuse_lower_error 74 77 Primitive.Addresses.material4479

def v4480_pa : Scalar.QComplex := ((999997874241167379906999285311 : Int)/10^30,(-2061919772054570395546366855 : Int)/10^30)
theorem v4480_pa_checked : Scalar.distance (sourceCoefficient 74 78 1 0) v4480_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4480_pb : Scalar.QComplex := ((-889672031414872568331711 : Int)/10^30,(-431476603621776514094579440 : Int)/10^30)
theorem v4480_pb_checked : Scalar.distance (sourceCoefficient 74 78 1 1) v4480_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4480_pg : Scalar.QComplex := ((-93086232000230343427981 : Int)/10^30,(191936750278576015249 : Int)/10^30)
theorem v4480_pg_checked : Scalar.distance (sourceCoefficient 74 78 1 2) v4480_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4480_mb : Scalar.QComplex := ((-1262016576090067565292845 : Int)/10^30,(-431475675216423760576878056 : Int)/10^30)
theorem v4480_mb_checked : Scalar.distance (sourceCoefficient 74 78 3 1) v4480_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4480_mg : Scalar.QComplex := ((-93086031707200938697690 : Int)/10^30,(272265904579692434555 : Int)/10^30)
theorem v4480_mg_checked : Scalar.distance (sourceCoefficient 74 78 3 2) v4480_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4480_upper : Scalar.QComplex := ((999992826175331034005416568041 : Int)/10^30,(-3787822312909042477409614909 : Int)/10^30)
theorem v4480_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 78 5) 1) 14) v4480_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4480 : Material (74 : Basis) (78 : Basis) where
  plus := ![v4480_pa,v4480_pb,v4480_pg]
  minus := ![(Primitive.Addresses.material4480 1).one,v4480_mb,v4480_mg]
  upper := v4480_upper
  lower := (Primitive.Addresses.material4480 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4480_pa_checked.trans (by decide +kernel)
    · exact v4480_pb_checked.trans (by decide +kernel)
    · exact v4480_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 78 Primitive.Addresses.material4480
    · exact v4480_mb_checked.trans (by decide +kernel)
    · exact v4480_mg_checked.trans (by decide +kernel)
  upper_error := v4480_upper_checked
  lower_error := reuse_lower_error 74 78 Primitive.Addresses.material4480

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
