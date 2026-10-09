import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B145
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B146

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3489_pa : Scalar.QComplex := ((999999280895425401845989185945 : Int)/10^30,(-1199253364425098793992356997 : Int)/10^30)
theorem v3489_pa_checked : Scalar.distance (sourceCoefficient 47 59 1 0) v3489_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3489_pb : Scalar.QComplex := ((-517450866848952771547118 : Int)/10^30,(-431477209151482396374931918 : Int)/10^30)
theorem v3489_pb_checked : Scalar.distance (sourceCoefficient 47 59 1 1) v3489_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3489_pg : Scalar.QComplex := ((-93086362788558970804043 : Int)/10^30,(111634214032948659770 : Int)/10^30)
theorem v3489_pg_checked : Scalar.distance (sourceCoefficient 47 59 1 2) v3489_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3489_mb : Scalar.QComplex := ((-889796072663962814839402 : Int)/10^30,(-431476601956004977927450608 : Int)/10^30)
theorem v3489_mb_checked : Scalar.distance (sourceCoefficient 47 59 3 1) v3489_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3489_mg : Scalar.QComplex := ((-93086231792952955603504 : Int)/10^30,(191963511098806448301 : Int)/10^30)
theorem v3489_mg_checked : Scalar.distance (sourceCoefficient 47 59 3 2) v3489_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3489_upper : Scalar.QComplex := ((999995721711453092969498718534 : Int)/10^30,(-2925159617877487793672495047 : Int)/10^30)
theorem v3489_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 59 5) 1) 14) v3489_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3489 : Material (47 : Basis) (59 : Basis) where
  plus := ![v3489_pa,v3489_pb,v3489_pg]
  minus := ![(Primitive.Addresses.material3489 1).one,v3489_mb,v3489_mg]
  upper := v3489_upper
  lower := (Primitive.Addresses.material3489 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3489_pa_checked.trans (by decide +kernel)
    · exact v3489_pb_checked.trans (by decide +kernel)
    · exact v3489_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 59 Primitive.Addresses.material3489
    · exact v3489_mb_checked.trans (by decide +kernel)
    · exact v3489_mg_checked.trans (by decide +kernel)
  upper_error := v3489_upper_checked
  lower_error := reuse_lower_error 47 59 Primitive.Addresses.material3489

def v3490_pa : Scalar.QComplex := ((999999256388525648679232778369 : Int)/10^30,(-1219517279805668332744130704 : Int)/10^30)
theorem v3490_pa_checked : Scalar.distance (sourceCoefficient 47 60 1 0) v3490_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3490_pb : Scalar.QComplex := ((-526194290229817020750279 : Int)/10^30,(-431477198116909627555432493 : Int)/10^30)
theorem v3490_pb_checked : Scalar.distance (sourceCoefficient 47 60 1 1) v3490_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3490_pg : Scalar.QComplex := ((-93086360457636486994237 : Int)/10^30,(113520509507460220177 : Int)/10^30)
theorem v3490_pg_checked : Scalar.distance (sourceCoefficient 47 60 1 2) v3490_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3490_mb : Scalar.QComplex := ((-898539483266911624375507 : Int)/10^30,(-431476583376255729268783810 : Int)/10^30)
theorem v3490_mb_checked : Scalar.distance (sourceCoefficient 47 60 3 1) v3490_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3490_mg : Scalar.QComplex := ((-93086227834243300793662 : Int)/10^30,(193849803859482872909 : Int)/10^30)
theorem v3490_mg_checked : Scalar.distance (sourceCoefficient 47 60 3 2) v3490_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3490_upper : Scalar.QComplex := ((999995662230910221131212761073 : Int)/10^30,(-2945423460780650014390904955 : Int)/10^30)
theorem v3490_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 60 5) 1) 14) v3490_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3490 : Material (47 : Basis) (60 : Basis) where
  plus := ![v3490_pa,v3490_pb,v3490_pg]
  minus := ![(Primitive.Addresses.material3490 1).one,v3490_mb,v3490_mg]
  upper := v3490_upper
  lower := (Primitive.Addresses.material3490 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3490_pa_checked.trans (by decide +kernel)
    · exact v3490_pb_checked.trans (by decide +kernel)
    · exact v3490_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 60 Primitive.Addresses.material3490
    · exact v3490_mb_checked.trans (by decide +kernel)
    · exact v3490_mg_checked.trans (by decide +kernel)
  upper_error := v3490_upper_checked
  lower_error := reuse_lower_error 47 60 Primitive.Addresses.material3490

def v3491_pa : Scalar.QComplex := ((999999249225798759149092094268 : Int)/10^30,(-1225376611013855024516040276 : Int)/10^30)
theorem v3491_pa_checked : Scalar.distance (sourceCoefficient 47 61 1 0) v3491_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3491_pb : Scalar.QComplex := ((-528722459745724953612835 : Int)/10^30,(-431477194882222566597551956 : Int)/10^30)
theorem v3491_pb_checked : Scalar.distance (sourceCoefficient 47 61 1 1) v3491_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3491_pg : Scalar.QComplex := ((-93086359775336445078302 : Int)/10^30,(114065933710878478828 : Int)/10^30)
theorem v3491_pg_checked : Scalar.distance (sourceCoefficient 47 61 1 2) v3491_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3491_mb : Scalar.QComplex := ((-901067649050077254701217 : Int)/10^30,(-431476577959873445032329033 : Int)/10^30)
theorem v3491_mb_checked : Scalar.distance (sourceCoefficient 47 61 3 1) v3491_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3491_mg : Scalar.QComplex := ((-93086226681266990373485 : Int)/10^30,(194395227271020566990 : Int)/10^30)
theorem v3491_mg_checked : Scalar.distance (sourceCoefficient 47 61 3 2) v3491_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3491_upper : Scalar.QComplex := ((999995644955519888686082818599 : Int)/10^30,(-2951282770899834343140318344 : Int)/10^30)
theorem v3491_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 61 5) 1) 14) v3491_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3491 : Material (47 : Basis) (61 : Basis) where
  plus := ![v3491_pa,v3491_pb,v3491_pg]
  minus := ![(Primitive.Addresses.material3491 1).one,v3491_mb,v3491_mg]
  upper := v3491_upper
  lower := (Primitive.Addresses.material3491 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3491_pa_checked.trans (by decide +kernel)
    · exact v3491_pb_checked.trans (by decide +kernel)
    · exact v3491_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 61 Primitive.Addresses.material3491
    · exact v3491_mb_checked.trans (by decide +kernel)
    · exact v3491_mg_checked.trans (by decide +kernel)
  upper_error := v3491_upper_checked
  lower_error := reuse_lower_error 47 61 Primitive.Addresses.material3491

def v3492_pa : Scalar.QComplex := ((999999238757483910696602680675 : Int)/10^30,(-1233889967820647487683092054 : Int)/10^30)
theorem v3492_pa_checked : Scalar.distance (sourceCoefficient 47 62 1 0) v3492_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3492_pb : Scalar.QComplex := ((-532395781548331890318308 : Int)/10^30,(-431477190147164003196877229 : Int)/10^30)
theorem v3492_pb_checked : Scalar.distance (sourceCoefficient 47 62 1 1) v3492_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3492_pg : Scalar.QComplex := ((-93086358777339560677472 : Int)/10^30,(114858411671419052112 : Int)/10^30)
theorem v3492_pg_checked : Scalar.distance (sourceCoefficient 47 62 1 2) v3492_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3492_mb : Scalar.QComplex := ((-904740965398796324102715 : Int)/10^30,(-431476570054905369333131768 : Int)/10^30)
theorem v3492_mb_checked : Scalar.distance (sourceCoefficient 47 62 3 1) v3492_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3492_mg : Scalar.QComplex := ((-93086224999397689508389 : Int)/10^30,(195187704075259014406 : Int)/10^30)
theorem v3492_mg_checked : Scalar.distance (sourceCoefficient 47 62 3 2) v3492_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3492_upper : Scalar.QComplex := ((999995619793939108731509062503 : Int)/10^30,(-2959796096959620141405719297 : Int)/10^30)
theorem v3492_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 62 5) 1) 14) v3492_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3492 : Material (47 : Basis) (62 : Basis) where
  plus := ![v3492_pa,v3492_pb,v3492_pg]
  minus := ![(Primitive.Addresses.material3492 1).one,v3492_mb,v3492_mg]
  upper := v3492_upper
  lower := (Primitive.Addresses.material3492 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3492_pa_checked.trans (by decide +kernel)
    · exact v3492_pb_checked.trans (by decide +kernel)
    · exact v3492_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 62 Primitive.Addresses.material3492
    · exact v3492_mb_checked.trans (by decide +kernel)
    · exact v3492_mg_checked.trans (by decide +kernel)
  upper_error := v3492_upper_checked
  lower_error := reuse_lower_error 47 62 Primitive.Addresses.material3492

def v3493_pa : Scalar.QComplex := ((999999207855567589607053634612 : Int)/10^30,(-1258685122390816254438272418 : Int)/10^30)
theorem v3493_pa_checked : Scalar.distance (sourceCoefficient 47 63 1 0) v3493_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3493_pb : Scalar.QComplex := ((-543094332441005891862708 : Int)/10^30,(-431477176118735342638388773 : Int)/10^30)
theorem v3493_pb_checked : Scalar.distance (sourceCoefficient 47 63 1 1) v3493_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3493_pg : Scalar.QComplex := ((-93086355825827051698313 : Int)/10^30,(117166503988339993595 : Int)/10^30)
theorem v3493_pg_checked : Scalar.distance (sourceCoefficient 47 63 1 2) v3493_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3493_mb : Scalar.QComplex := ((-915439500202008763285019 : Int)/10^30,(-431476546794114356667385765 : Int)/10^30)
theorem v3493_mb_checked : Scalar.distance (sourceCoefficient 47 63 3 1) v3493_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3493_mg : Scalar.QComplex := ((-93086220056106562628507 : Int)/10^30,(197495792985749337208 : Int)/10^30)
theorem v3493_mg_checked : Scalar.distance (sourceCoefficient 47 63 3 2) v3493_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3493_upper : Scalar.QComplex := ((999995546097881423156300946905 : Int)/10^30,(-2984591161266414649101506181 : Int)/10^30)
theorem v3493_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 63 5) 1) 14) v3493_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3493 : Material (47 : Basis) (63 : Basis) where
  plus := ![v3493_pa,v3493_pb,v3493_pg]
  minus := ![(Primitive.Addresses.material3493 1).one,v3493_mb,v3493_mg]
  upper := v3493_upper
  lower := (Primitive.Addresses.material3493 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3493_pa_checked.trans (by decide +kernel)
    · exact v3493_pb_checked.trans (by decide +kernel)
    · exact v3493_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 63 Primitive.Addresses.material3493
    · exact v3493_mb_checked.trans (by decide +kernel)
    · exact v3493_mg_checked.trans (by decide +kernel)
  upper_error := v3493_upper_checked
  lower_error := reuse_lower_error 47 63 Primitive.Addresses.material3493

def v3494_pa : Scalar.QComplex := ((999999162623301632350584342978 : Int)/10^30,(-1294122364977734191004509860 : Int)/10^30)
theorem v3494_pa_checked : Scalar.distance (sourceCoefficient 47 64 1 0) v3494_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3494_pb : Scalar.QComplex := ((-558384704430038802703413 : Int)/10^30,(-431477155455315677208796066 : Int)/10^30)
theorem v3494_pb_checked : Scalar.distance (sourceCoefficient 47 64 1 1) v3494_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3494_pg : Scalar.QComplex := ((-93086351491621598682535 : Int)/10^30,(120465230214262722968 : Int)/10^30)
theorem v3494_pg_checked : Scalar.distance (sourceCoefficient 47 64 1 2) v3494_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3494_mb : Scalar.QComplex := ((-930729848666136852696022 : Int)/10^30,(-431476512935800011428290190 : Int)/10^30)
theorem v3494_mb_checked : Scalar.distance (sourceCoefficient 47 64 3 1) v3494_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3494_mg : Scalar.QComplex := ((-93086212875250559578258 : Int)/10^30,(200794514243181432849 : Int)/10^30)
theorem v3494_mg_checked : Scalar.distance (sourceCoefficient 47 64 3 2) v3494_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3494_upper : Scalar.QComplex := ((999995439704216970560782559854 : Int)/10^30,(-3020028273006934900273709601 : Int)/10^30)
theorem v3494_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 64 5) 1) 14) v3494_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3494 : Material (47 : Basis) (64 : Basis) where
  plus := ![v3494_pa,v3494_pb,v3494_pg]
  minus := ![(Primitive.Addresses.material3494 1).one,v3494_mb,v3494_mg]
  upper := v3494_upper
  lower := (Primitive.Addresses.material3494 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3494_pa_checked.trans (by decide +kernel)
    · exact v3494_pb_checked.trans (by decide +kernel)
    · exact v3494_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 64 Primitive.Addresses.material3494
    · exact v3494_mb_checked.trans (by decide +kernel)
    · exact v3494_mg_checked.trans (by decide +kernel)
  upper_error := v3494_upper_checked
  lower_error := reuse_lower_error 47 64 Primitive.Addresses.material3494

def v3495_pa : Scalar.QComplex := ((999999115431297468578480974183 : Int)/10^30,(-1330088952890389786177379211 : Int)/10^30)
theorem v3495_pa_checked : Scalar.distance (sourceCoefficient 47 65 1 0) v3495_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3495_pb : Scalar.QComplex := ((-573903476675423124301015 : Int)/10^30,(-431477133744500533521351491 : Int)/10^30)
theorem v3495_pb_checked : Scalar.distance (sourceCoefficient 47 65 1 1) v3495_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3495_pg : Scalar.QComplex := ((-93086346953221722784659 : Int)/10^30,(123813231268711546429 : Int)/10^30)
theorem v3495_pg_checked : Scalar.distance (sourceCoefficient 47 65 1 2) v3495_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3495_mb : Scalar.QComplex := ((-946248596397717374221582 : Int)/10^30,(-431476477832991443458963533 : Int)/10^30)
theorem v3495_mb_checked : Scalar.distance (sourceCoefficient 47 65 3 1) v3495_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3495_mg : Scalar.QComplex := ((-93086205447678251914700 : Int)/10^30,(204142510134581761574 : Int)/10^30)
theorem v3495_mg_checked : Scalar.distance (sourceCoefficient 47 65 3 2) v3495_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3495_upper : Scalar.QComplex := ((999995330437215219859107873403 : Int)/10^30,(-3055994725902464770251581744 : Int)/10^30)
theorem v3495_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 65 5) 1) 14) v3495_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3495 : Material (47 : Basis) (65 : Basis) where
  plus := ![v3495_pa,v3495_pb,v3495_pg]
  minus := ![(Primitive.Addresses.material3495 1).one,v3495_mb,v3495_mg]
  upper := v3495_upper
  lower := (Primitive.Addresses.material3495 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3495_pa_checked.trans (by decide +kernel)
    · exact v3495_pb_checked.trans (by decide +kernel)
    · exact v3495_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 65 Primitive.Addresses.material3495
    · exact v3495_mb_checked.trans (by decide +kernel)
    · exact v3495_mg_checked.trans (by decide +kernel)
  upper_error := v3495_upper_checked
  lower_error := reuse_lower_error 47 65 Primitive.Addresses.material3495

def v3496_pa : Scalar.QComplex := ((999999091883608422195498987421 : Int)/10^30,(-1347676503646267608152821755 : Int)/10^30)
theorem v3496_pa_checked : Scalar.distance (sourceCoefficient 47 66 1 0) v3496_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3496_pb : Scalar.QComplex := ((-581492108397846079346779 : Int)/10^30,(-431477122857043076281760549 : Int)/10^30)
theorem v3496_pb_checked : Scalar.distance (sourceCoefficient 47 66 1 1) v3496_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3496_pg : Scalar.QComplex := ((-93086344682813227398696 : Int)/10^30,(125450393462903697381 : Int)/10^30)
theorem v3496_pg_checked : Scalar.distance (sourceCoefficient 47 66 1 2) v3496_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3496_mb : Scalar.QComplex := ((-953837215899160488689780 : Int)/10^30,(-431476460396890642951689584 : Int)/10^30)
theorem v3496_mb_checked : Scalar.distance (sourceCoefficient 47 66 3 1) v3496_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3496_mg : Scalar.QComplex := ((-93086201764473363365810 : Int)/10^30,(205779669759923329504 : Int)/10^30)
theorem v3496_mg_checked : Scalar.distance (sourceCoefficient 47 66 3 2) v3496_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3496_upper : Scalar.QComplex := ((999995276535044170488709637637 : Int)/10^30,(-3073582209822576655791842449 : Int)/10^30)
theorem v3496_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 66 5) 1) 14) v3496_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3496 : Material (47 : Basis) (66 : Basis) where
  plus := ![v3496_pa,v3496_pb,v3496_pg]
  minus := ![(Primitive.Addresses.material3496 1).one,v3496_mb,v3496_mg]
  upper := v3496_upper
  lower := (Primitive.Addresses.material3496 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3496_pa_checked.trans (by decide +kernel)
    · exact v3496_pb_checked.trans (by decide +kernel)
    · exact v3496_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 66 Primitive.Addresses.material3496
    · exact v3496_mb_checked.trans (by decide +kernel)
    · exact v3496_mg_checked.trans (by decide +kernel)
  upper_error := v3496_upper_checked
  lower_error := reuse_lower_error 47 66 Primitive.Addresses.material3496

def v3497_pa : Scalar.QComplex := ((999999051668401359187899906749 : Int)/10^30,(-1377193631247546547972269735 : Int)/10^30)
theorem v3497_pa_checked : Scalar.distance (sourceCoefficient 47 67 1 0) v3497_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3497_pb : Scalar.QComplex := ((-594228083437584193168460 : Int)/10^30,(-431477104184709377201851390 : Int)/10^30)
theorem v3497_pb_checked : Scalar.distance (sourceCoefficient 47 67 1 1) v3497_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3497_pg : Scalar.QComplex := ((-93086340796895044042629 : Int)/10^30,(128198037275872154001 : Int)/10^30)
theorem v3497_pg_checked : Scalar.distance (sourceCoefficient 47 67 1 2) v3497_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3497_mb : Scalar.QComplex := ((-966573170083330020788704 : Int)/10^30,(-431476430733991044163488401 : Int)/10^30)
theorem v3497_mb_checked : Scalar.distance (sourceCoefficient 47 67 3 1) v3497_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3497_mg : Scalar.QComplex := ((-93086195507463765606446 : Int)/10^30,(208527309196446044053 : Int)/10^30)
theorem v3497_mg_checked : Scalar.distance (sourceCoefficient 47 67 3 2) v3497_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3497_upper : Scalar.QComplex := ((999995185376012536398944781513 : Int)/10^30,(-3103099224053762263215401673 : Int)/10^30)
theorem v3497_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 67 5) 1) 14) v3497_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3497 : Material (47 : Basis) (67 : Basis) where
  plus := ![v3497_pa,v3497_pb,v3497_pg]
  minus := ![(Primitive.Addresses.material3497 1).one,v3497_mb,v3497_mg]
  upper := v3497_upper
  lower := (Primitive.Addresses.material3497 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3497_pa_checked.trans (by decide +kernel)
    · exact v3497_pb_checked.trans (by decide +kernel)
    · exact v3497_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 67 Primitive.Addresses.material3497
    · exact v3497_mb_checked.trans (by decide +kernel)
    · exact v3497_mg_checked.trans (by decide +kernel)
  upper_error := v3497_upper_checked
  lower_error := reuse_lower_error 47 67 Primitive.Addresses.material3497

def v3498_pa : Scalar.QComplex := ((999998982760087679250067709884 : Int)/10^30,(-1426351566011851317395714826 : Int)/10^30)
theorem v3498_pa_checked : Scalar.distance (sourceCoefficient 47 68 1 0) v3498_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3498_pb : Scalar.QComplex := ((-615438623358821041804994 : Int)/10^30,(-431477071975238540696413699 : Int)/10^30)
theorem v3498_pb_checked : Scalar.distance (sourceCoefficient 47 68 1 1) v3498_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3498_pg : Scalar.QComplex := ((-93086334115264771058022 : Int)/10^30,(132773973502595490652 : Int)/10^30)
theorem v3498_pg_checked : Scalar.distance (sourceCoefficient 47 68 1 2) v3498_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3498_mb : Scalar.QComplex := ((-987783674311590815997758 : Int)/10^30,(-431476380220791535944810963 : Int)/10^30)
theorem v3498_mb_checked : Scalar.distance (sourceCoefficient 47 68 3 1) v3498_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3498_mg : Scalar.QComplex := ((-93086184877009109353054 : Int)/10^30,(213103237953393196748 : Int)/10^30)
theorem v3498_mg_checked : Scalar.distance (sourceCoefficient 47 68 3 2) v3498_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3498_upper : Scalar.QComplex := ((999995031625665657115312859932 : Int)/10^30,(-3152256966673599599672339145 : Int)/10^30)
theorem v3498_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 68 5) 1) 14) v3498_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3498 : Material (47 : Basis) (68 : Basis) where
  plus := ![v3498_pa,v3498_pb,v3498_pg]
  minus := ![(Primitive.Addresses.material3498 1).one,v3498_mb,v3498_mg]
  upper := v3498_upper
  lower := (Primitive.Addresses.material3498 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3498_pa_checked.trans (by decide +kernel)
    · exact v3498_pb_checked.trans (by decide +kernel)
    · exact v3498_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 68 Primitive.Addresses.material3498
    · exact v3498_mb_checked.trans (by decide +kernel)
    · exact v3498_mg_checked.trans (by decide +kernel)
  upper_error := v3498_upper_checked
  lower_error := reuse_lower_error 47 68 Primitive.Addresses.material3498

def v3499_pa : Scalar.QComplex := ((999998951666373693150135480539 : Int)/10^30,(-1447986931436298455161480549 : Int)/10^30)
theorem v3499_pa_checked : Scalar.distance (sourceCoefficient 47 69 1 0) v3499_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3499_pb : Scalar.QComplex := ((-624773795241283536944027 : Int)/10^30,(-431477057358642953520386530 : Int)/10^30)
theorem v3499_pb_checked : Scalar.distance (sourceCoefficient 47 69 1 1) v3499_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3499_pg : Scalar.QComplex := ((-93086331091380177278854 : Int)/10^30,(134787932218392650814 : Int)/10^30)
theorem v3499_pg_checked : Scalar.distance (sourceCoefficient 47 69 1 2) v3499_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3499_mb : Scalar.QComplex := ((-997118830104678496159439 : Int)/10^30,(-431476357548368497164298863 : Int)/10^30)
theorem v3499_mb_checked : Scalar.distance (sourceCoefficient 47 69 3 1) v3499_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3499_mg : Scalar.QComplex := ((-93086180115169975104788 : Int)/10^30,(215117193309825270834 : Int)/10^30)
theorem v3499_mg_checked : Scalar.distance (sourceCoefficient 47 69 3 2) v3499_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3499_upper : Scalar.QComplex := ((999994963191320003873262078791 : Int)/10^30,(-3173892246209781865964735198 : Int)/10^30)
theorem v3499_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 69 5) 1) 14) v3499_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3499 : Material (47 : Basis) (69 : Basis) where
  plus := ![v3499_pa,v3499_pb,v3499_pg]
  minus := ![(Primitive.Addresses.material3499 1).one,v3499_mb,v3499_mg]
  upper := v3499_upper
  lower := (Primitive.Addresses.material3499 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3499_pa_checked.trans (by decide +kernel)
    · exact v3499_pb_checked.trans (by decide +kernel)
    · exact v3499_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 69 Primitive.Addresses.material3499
    · exact v3499_mb_checked.trans (by decide +kernel)
    · exact v3499_mg_checked.trans (by decide +kernel)
  upper_error := v3499_upper_checked
  lower_error := reuse_lower_error 47 69 Primitive.Addresses.material3499

def v3500_pa : Scalar.QComplex := ((999998930957398354725498592511 : Int)/10^30,(-1462218882533823959343778303 : Int)/10^30)
theorem v3500_pa_checked : Scalar.distance (sourceCoefficient 47 70 1 0) v3500_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3500_pb : Scalar.QComplex := ((-630914560850633046871650 : Int)/10^30,(-431477047596870461771893015 : Int)/10^30)
theorem v3500_pb_checked : Scalar.distance (sourceCoefficient 47 70 1 1) v3500_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3500_pg : Scalar.QComplex := ((-93086329074521489247161 : Int)/10^30,(136112733588833452296 : Int)/10^30)
theorem v3500_pg_checked : Scalar.distance (sourceCoefficient 47 70 1 2) v3500_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3500_mb : Scalar.QComplex := ((-1003259585003570316407014 : Int)/10^30,(-431476342487395489117502928 : Int)/10^30)
theorem v3500_mb_checked : Scalar.distance (sourceCoefficient 47 70 3 1) v3500_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3500_mg : Scalar.QComplex := ((-93086176955068122190136 : Int)/10^30,(216441992446523763859 : Int)/10^30)
theorem v3500_mg_checked : Scalar.distance (sourceCoefficient 47 70 3 2) v3500_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3500_upper : Scalar.QComplex := ((999994917919319027223674434199 : Int)/10^30,(-3188124140368675282242575872 : Int)/10^30)
theorem v3500_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 70 5) 1) 14) v3500_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3500 : Material (47 : Basis) (70 : Basis) where
  plus := ![v3500_pa,v3500_pb,v3500_pg]
  minus := ![(Primitive.Addresses.material3500 1).one,v3500_mb,v3500_mg]
  upper := v3500_upper
  lower := (Primitive.Addresses.material3500 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3500_pa_checked.trans (by decide +kernel)
    · exact v3500_pb_checked.trans (by decide +kernel)
    · exact v3500_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 70 Primitive.Addresses.material3500
    · exact v3500_mb_checked.trans (by decide +kernel)
    · exact v3500_mg_checked.trans (by decide +kernel)
  upper_error := v3500_upper_checked
  lower_error := reuse_lower_error 47 70 Primitive.Addresses.material3500

def v3501_pa : Scalar.QComplex := ((999998895140913199722226027124 : Int)/10^30,(-1486511672637303532183721845 : Int)/10^30)
theorem v3501_pa_checked : Scalar.distance (sourceCoefficient 47 71 1 0) v3501_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3501_pb : Scalar.QComplex := ((-641396351211153160949596 : Int)/10^30,(-431477030665107652828211628 : Int)/10^30)
theorem v3501_pb_checked : Scalar.distance (sourceCoefficient 47 71 1 1) v3501_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3501_pg : Scalar.QComplex := ((-93086325581088276760140 : Int)/10^30,(138374062423044395527 : Int)/10^30)
theorem v3501_pg_checked : Scalar.distance (sourceCoefficient 47 71 1 2) v3501_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3501_mb : Scalar.QComplex := ((-1013741356849892111948997 : Int)/10^30,(-431476316510325985827395259 : Int)/10^30)
theorem v3501_mb_checked : Scalar.distance (sourceCoefficient 47 71 3 1) v3501_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3501_mg : Scalar.QComplex := ((-93086171510211273013887 : Int)/10^30,(218703317424063110295 : Int)/10^30)
theorem v3501_mg_checked : Scalar.distance (sourceCoefficient 47 71 3 2) v3501_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3501_upper : Scalar.QComplex := ((999994840175735322764851469418 : Int)/10^30,(-3212416832474893496147831247 : Int)/10^30)
theorem v3501_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 71 5) 1) 14) v3501_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3501 : Material (47 : Basis) (71 : Basis) where
  plus := ![v3501_pa,v3501_pb,v3501_pg]
  minus := ![(Primitive.Addresses.material3501 1).one,v3501_mb,v3501_mg]
  upper := v3501_upper
  lower := (Primitive.Addresses.material3501 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3501_pa_checked.trans (by decide +kernel)
    · exact v3501_pb_checked.trans (by decide +kernel)
    · exact v3501_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 71 Primitive.Addresses.material3501
    · exact v3501_mb_checked.trans (by decide +kernel)
    · exact v3501_mg_checked.trans (by decide +kernel)
  upper_error := v3501_upper_checked
  lower_error := reuse_lower_error 47 71 Primitive.Addresses.material3501

def v3502_pa : Scalar.QComplex := ((999998855605068032281391847235 : Int)/10^30,(-1512874269163064622087123938 : Int)/10^30)
theorem v3502_pa_checked : Scalar.distance (sourceCoefficient 47 72 1 0) v3502_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3502_pb : Scalar.QComplex := ((-652771216076906309652683 : Int)/10^30,(-431477011906583137842180156 : Int)/10^30)
theorem v3502_pb_checked : Scalar.distance (sourceCoefficient 47 72 1 1) v3502_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3502_pg : Scalar.QComplex := ((-93086321717492429421453 : Int)/10^30,(140828062100349816022 : Int)/10^30)
theorem v3502_pg_checked : Scalar.distance (sourceCoefficient 47 72 1 2) v3502_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3502_mb : Scalar.QComplex := ((-1025116201292501410275172 : Int)/10^30,(-431476287935812381248282161 : Int)/10^30)
theorem v3502_mb_checked : Scalar.distance (sourceCoefficient 47 72 3 1) v3502_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3502_mg : Scalar.QComplex := ((-93086165528925666796553 : Int)/10^30,(221157312853523091248 : Int)/10^30)
theorem v3502_mg_checked : Scalar.distance (sourceCoefficient 47 72 3 2) v3502_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3502_upper : Scalar.QComplex := ((999994755140499031932240163730 : Int)/10^30,(-3238779321501381733907331745 : Int)/10^30)
theorem v3502_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 72 5) 1) 14) v3502_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3502 : Material (47 : Basis) (72 : Basis) where
  plus := ![v3502_pa,v3502_pb,v3502_pg]
  minus := ![(Primitive.Addresses.material3502 1).one,v3502_mb,v3502_mg]
  upper := v3502_upper
  lower := (Primitive.Addresses.material3502 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3502_pa_checked.trans (by decide +kernel)
    · exact v3502_pb_checked.trans (by decide +kernel)
    · exact v3502_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 72 Primitive.Addresses.material3502
    · exact v3502_mb_checked.trans (by decide +kernel)
    · exact v3502_mg_checked.trans (by decide +kernel)
  upper_error := v3502_upper_checked
  lower_error := reuse_lower_error 47 72 Primitive.Addresses.material3502

def v3503_pa : Scalar.QComplex := ((999998841264299022611740377804 : Int)/10^30,(-1522323900911482043622337221 : Int)/10^30)
theorem v3503_pa_checked : Scalar.distance (sourceCoefficient 47 73 1 0) v3503_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3503_pb : Scalar.QComplex := ((-656848518648846443548543 : Int)/10^30,(-431477005085274039675264731 : Int)/10^30)
theorem v3503_pb_checked : Scalar.distance (sourceCoefficient 47 73 1 1) v3503_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3503_pg : Scalar.QComplex := ((-93086320314216515857778 : Int)/10^30,(141707694463998499969 : Int)/10^30)
theorem v3503_pg_checked : Scalar.distance (sourceCoefficient 47 73 1 2) v3503_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3503_mb : Scalar.QComplex := ((-1029193496459792923343883 : Int)/10^30,(-431476277595977338273150258 : Int)/10^30)
theorem v3503_mb_checked : Scalar.distance (sourceCoefficient 47 73 3 1) v3503_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3503_mg : Scalar.QComplex := ((-93086163366567163078819 : Int)/10^30,(222036943678680532819 : Int)/10^30)
theorem v3503_mg_checked : Scalar.distance (sourceCoefficient 47 73 3 2) v3503_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3503_upper : Scalar.QComplex := ((999994724490544247280612337129 : Int)/10^30,(-3248228914424816371607446600 : Int)/10^30)
theorem v3503_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 73 5) 1) 14) v3503_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3503 : Material (47 : Basis) (73 : Basis) where
  plus := ![v3503_pa,v3503_pb,v3503_pg]
  minus := ![(Primitive.Addresses.material3503 1).one,v3503_mb,v3503_mg]
  upper := v3503_upper
  lower := (Primitive.Addresses.material3503 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3503_pa_checked.trans (by decide +kernel)
    · exact v3503_pb_checked.trans (by decide +kernel)
    · exact v3503_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 73 Primitive.Addresses.material3503
    · exact v3503_mb_checked.trans (by decide +kernel)
    · exact v3503_mg_checked.trans (by decide +kernel)
  upper_error := v3503_upper_checked
  lower_error := reuse_lower_error 47 73 Primitive.Addresses.material3503

def v3504_pa : Scalar.QComplex := ((999998825020636968652894203243 : Int)/10^30,(-1532957059244058102146674540 : Int)/10^30)
theorem v3504_pa_checked : Scalar.distance (sourceCoefficient 47 74 1 0) v3504_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3504_pb : Scalar.QComplex := ((-661436486160571660944287 : Int)/10^30,(-431476997348198394127760550 : Int)/10^30)
theorem v3504_pb_checked : Scalar.distance (sourceCoefficient 47 74 1 1) v3504_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3504_pg : Scalar.QComplex := ((-93086318723590667788592 : Int)/10^30,(142697497072984871280 : Int)/10^30)
theorem v3504_pg_checked : Scalar.distance (sourceCoefficient 47 74 1 2) v3504_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3504_mb : Scalar.QComplex := ((-1033781455586460338494569 : Int)/10^30,(-431476265899695245359747258 : Int)/10^30)
theorem v3504_mb_checked : Scalar.distance (sourceCoefficient 47 74 3 1) v3504_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3504_mg : Scalar.QComplex := ((-93086160921786834771749 : Int)/10^30,(223026744546479688835 : Int)/10^30)
theorem v3504_mg_checked : Scalar.distance (sourceCoefficient 47 74 3 2) v3504_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3504_upper : Scalar.QComplex := ((999994689895039736910638981215 : Int)/10^30,(-3258862028885465060656394182 : Int)/10^30)
theorem v3504_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 74 5) 1) 14) v3504_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3504 : Material (47 : Basis) (74 : Basis) where
  plus := ![v3504_pa,v3504_pb,v3504_pg]
  minus := ![(Primitive.Addresses.material3504 1).one,v3504_mb,v3504_mg]
  upper := v3504_upper
  lower := (Primitive.Addresses.material3504 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3504_pa_checked.trans (by decide +kernel)
    · exact v3504_pb_checked.trans (by decide +kernel)
    · exact v3504_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 74 Primitive.Addresses.material3504
    · exact v3504_mb_checked.trans (by decide +kernel)
    · exact v3504_mg_checked.trans (by decide +kernel)
  upper_error := v3504_upper_checked
  lower_error := reuse_lower_error 47 74 Primitive.Addresses.material3504

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
