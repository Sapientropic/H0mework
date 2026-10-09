import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B142
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B143

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3425_pa : Scalar.QComplex := ((999997994224541103940517449273 : Int)/10^30,(-2002884643372385402094468143 : Int)/10^30)
theorem v3425_pa_checked : Scalar.distance (sourceCoefficient 45 96 1 0) v3425_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3425_pb : Scalar.QComplex := ((-864199559013518842222268 : Int)/10^30,(-431476584776318644225081726 : Int)/10^30)
theorem v3425_pb_checked : Scalar.distance (sourceCoefficient 45 96 1 1) v3425_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3425_pg : Scalar.QComplex := ((-93086235551794287012831 : Int)/10^30,(186441365655549118776 : Int)/10^30)
theorem v3425_pg_checked : Scalar.distance (sourceCoefficient 45 96 1 2) v3425_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3425_mb : Scalar.QComplex := ((-1236544096910498089923624 : Int)/10^30,(-431475678352569352531394348 : Int)/10^30)
theorem v3425_mb_checked : Scalar.distance (sourceCoefficient 45 96 3 1) v3425_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3425_mg : Scalar.QComplex := ((-93086040001032986609501 : Int)/10^30,(266770525067688111530 : Int)/10^30)
theorem v3425_mg_checked : Scalar.distance (sourceCoefficient 45 96 3 2) v3425_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3425_upper : Scalar.QComplex := ((999993048047802537311107717685 : Int)/10^30,(-3728787479233165143762451954 : Int)/10^30)
theorem v3425_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 96 5) 1) 14) v3425_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3425 : Material (45 : Basis) (96 : Basis) where
  plus := ![v3425_pa,v3425_pb,v3425_pg]
  minus := ![(Primitive.Addresses.material3425 1).one,v3425_mb,v3425_mg]
  upper := v3425_upper
  lower := (Primitive.Addresses.material3425 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3425_pa_checked.trans (by decide +kernel)
    · exact v3425_pb_checked.trans (by decide +kernel)
    · exact v3425_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 96 Primitive.Addresses.material3425
    · exact v3425_mb_checked.trans (by decide +kernel)
    · exact v3425_mg_checked.trans (by decide +kernel)
  upper_error := v3425_upper_checked
  lower_error := reuse_lower_error 45 96 Primitive.Addresses.material3425

def v3426_pa : Scalar.QComplex := ((999997845012697616964746662378 : Int)/10^30,(-2076046714502300662178529289 : Int)/10^30)
theorem v3426_pa_checked : Scalar.distance (sourceCoefficient 45 97 1 0) v3426_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3426_pb : Scalar.QComplex := ((-895767320446277168477413 : Int)/10^30,(-431476509570653514978112060 : Int)/10^30)
theorem v3426_pb_checked : Scalar.distance (sourceCoefficient 45 97 1 1) v3426_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3426_pg : Scalar.QComplex := ((-93086220494606486002994 : Int)/10^30,(193251758678350635220 : Int)/10^30)
theorem v3426_pg_checked : Scalar.distance (sourceCoefficient 45 97 1 2) v3426_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3426_mb : Scalar.QComplex := ((-1268111781690034247674489 : Int)/10^30,(-431475575905375868516934625 : Int)/10^30)
theorem v3426_mb_checked : Scalar.distance (sourceCoefficient 45 97 3 1) v3426_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3426_mg : Scalar.QComplex := ((-93086019066788342116563 : Int)/10^30,(273580902560994133541 : Int)/10^30)
theorem v3426_mg_checked : Scalar.distance (sourceCoefficient 45 97 3 2) v3426_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3426_upper : Scalar.QComplex := ((999992772565083724860674431962 : Int)/10^30,(-3801949183870664210604183072 : Int)/10^30)
theorem v3426_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 45 97 5) 1) 14) v3426_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3426 : Material (45 : Basis) (97 : Basis) where
  plus := ![v3426_pa,v3426_pb,v3426_pg]
  minus := ![(Primitive.Addresses.material3426 1).one,v3426_mb,v3426_mg]
  upper := v3426_upper
  lower := (Primitive.Addresses.material3426 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3426_pa_checked.trans (by decide +kernel)
    · exact v3426_pb_checked.trans (by decide +kernel)
    · exact v3426_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 45 97 Primitive.Addresses.material3426
    · exact v3426_mb_checked.trans (by decide +kernel)
    · exact v3426_mg_checked.trans (by decide +kernel)
  upper_error := v3426_upper_checked
  lower_error := reuse_lower_error 45 97 Primitive.Addresses.material3426

def v3427_pa : Scalar.QComplex := ((999999451394299458909171903633 : Int)/10^30,(-1047478448520048067729436843 : Int)/10^30)
theorem v3427_pa_checked : Scalar.distance (sourceCoefficient 46 47 1 0) v3427_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3427_pb : Scalar.QComplex := ((-451963404267871933154670 : Int)/10^30,(-431477284288509760230564541 : Int)/10^30)
theorem v3427_pb_checked : Scalar.distance (sourceCoefficient 46 47 1 1) v3427_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3427_pg : Scalar.QComplex := ((-93086378829109665812532 : Int)/10^30,(97506029166628679347 : Int)/10^30)
theorem v3427_pg_checked : Scalar.distance (sourceCoefficient 46 47 1 2) v3427_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3427_mb : Scalar.QComplex := ((-824308699306727789193434 : Int)/10^30,(-431476733605735126480551148 : Int)/10^30)
theorem v3427_mb_checked : Scalar.distance (sourceCoefficient 46 47 3 1) v3427_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3427_mg : Scalar.QComplex := ((-93086260025484907790575 : Int)/10^30,(177835345335328193763 : Int)/10^30)
theorem v3427_mg_checked : Scalar.distance (sourceCoefficient 46 47 3 2) v3427_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3427_upper : Scalar.QComplex := ((999996154159809151291469776779 : Int)/10^30,(-2773385222288934659422532239 : Int)/10^30)
theorem v3427_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 47 5) 1) 14) v3427_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3427 : Material (46 : Basis) (47 : Basis) where
  plus := ![v3427_pa,v3427_pb,v3427_pg]
  minus := ![(Primitive.Addresses.material3427 1).one,v3427_mb,v3427_mg]
  upper := v3427_upper
  lower := (Primitive.Addresses.material3427 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3427_pa_checked.trans (by decide +kernel)
    · exact v3427_pb_checked.trans (by decide +kernel)
    · exact v3427_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 47 Primitive.Addresses.material3427
    · exact v3427_mb_checked.trans (by decide +kernel)
    · exact v3427_mg_checked.trans (by decide +kernel)
  upper_error := v3427_upper_checked
  lower_error := reuse_lower_error 46 47 Primitive.Addresses.material3427

def v3428_pa : Scalar.QComplex := ((999999422285153017932341085784 : Int)/10^30,(-1074909000897141475934111706 : Int)/10^30)
theorem v3428_pa_checked : Scalar.distance (sourceCoefficient 46 48 1 0) v3428_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3428_pb : Scalar.QComplex := ((-463799070932324691241393 : Int)/10^30,(-431477271658921118736731704 : Int)/10^30)
theorem v3428_pb_checked : Scalar.distance (sourceCoefficient 46 48 1 1) v3428_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3428_pg : Scalar.QComplex := ((-93086376111930443132539 : Int)/10^30,(100059441349435537852 : Int)/10^30)
theorem v3428_pg_checked : Scalar.distance (sourceCoefficient 46 48 1 2) v3428_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3428_mb : Scalar.QComplex := ((-836144350665454749363812 : Int)/10^30,(-431476710762503914775540171 : Int)/10^30)
theorem v3428_mb_checked : Scalar.distance (sourceCoefficient 46 48 3 1) v3428_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3428_mg : Scalar.QComplex := ((-93086255104826984493930 : Int)/10^30,(180388754222579707943 : Int)/10^30)
theorem v3428_mg_checked : Scalar.distance (sourceCoefficient 46 48 3 2) v3428_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3428_upper : Scalar.QComplex := ((999996077708061142378348493312 : Int)/10^30,(-2800815683571696524987951984 : Int)/10^30)
theorem v3428_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 48 5) 1) 14) v3428_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3428 : Material (46 : Basis) (48 : Basis) where
  plus := ![v3428_pa,v3428_pb,v3428_pg]
  minus := ![(Primitive.Addresses.material3428 1).one,v3428_mb,v3428_mg]
  upper := v3428_upper
  lower := (Primitive.Addresses.material3428 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3428_pa_checked.trans (by decide +kernel)
    · exact v3428_pb_checked.trans (by decide +kernel)
    · exact v3428_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 48 Primitive.Addresses.material3428
    · exact v3428_mb_checked.trans (by decide +kernel)
    · exact v3428_mg_checked.trans (by decide +kernel)
  upper_error := v3428_upper_checked
  lower_error := reuse_lower_error 46 48 Primitive.Addresses.material3428

def v3429_pa : Scalar.QComplex := ((999999398353050576730698636344 : Int)/10^30,(-1096947371967993208520271128 : Int)/10^30)
theorem v3429_pa_checked : Scalar.distance (sourceCoefficient 46 49 1 0) v3429_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3429_pb : Scalar.QComplex := ((-473308132499927192081725 : Int)/10^30,(-431477261198400809882615169 : Int)/10^30)
theorem v3429_pb_checked : Scalar.distance (sourceCoefficient 46 49 1 1) v3429_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3429_pg : Scalar.QComplex := ((-93086373869683559848137 : Int)/10^30,(102110914617099737487 : Int)/10^30)
theorem v3429_pg_checked : Scalar.distance (sourceCoefficient 46 49 1 2) v3429_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3429_mb : Scalar.QComplex := ((-845653399665441140807780 : Int)/10^30,(-431476692096095640245037951 : Int)/10^30)
theorem v3429_mb_checked : Scalar.distance (sourceCoefficient 46 49 3 1) v3429_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3429_mg : Scalar.QComplex := ((-93086251092251901032428 : Int)/10^30,(182440224791428579843 : Int)/10^30)
theorem v3429_mg_checked : Scalar.distance (sourceCoefficient 46 49 3 2) v3429_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3429_upper : Scalar.QComplex := ((999996015739765182347770450862 : Int)/10^30,(-2822853980514345646320048115 : Int)/10^30)
theorem v3429_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 49 5) 1) 14) v3429_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3429 : Material (46 : Basis) (49 : Basis) where
  plus := ![v3429_pa,v3429_pb,v3429_pg]
  minus := ![(Primitive.Addresses.material3429 1).one,v3429_mb,v3429_mg]
  upper := v3429_upper
  lower := (Primitive.Addresses.material3429 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3429_pa_checked.trans (by decide +kernel)
    · exact v3429_pb_checked.trans (by decide +kernel)
    · exact v3429_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 49 Primitive.Addresses.material3429
    · exact v3429_mb_checked.trans (by decide +kernel)
    · exact v3429_mg_checked.trans (by decide +kernel)
  upper_error := v3429_upper_checked
  lower_error := reuse_lower_error 46 49 Primitive.Addresses.material3429

def v3430_pa : Scalar.QComplex := ((999999395524786707380450330227 : Int)/10^30,(-1099522651515172566879772413 : Int)/10^30)
theorem v3430_pa_checked : Scalar.distance (sourceCoefficient 46 50 1 0) v3430_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3430_pb : Scalar.QComplex := ((-474419307712024960632847 : Int)/10^30,(-431477259957810085812353641 : Int)/10^30)
theorem v3430_pb_checked : Scalar.distance (sourceCoefficient 46 50 1 1) v3430_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3430_pg : Scalar.QComplex := ((-93086373604225307887995 : Int)/10^30,(102350638193673634118 : Int)/10^30)
theorem v3430_pg_checked : Scalar.distance (sourceCoefficient 46 50 1 2) v3430_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3430_mb : Scalar.QComplex := ((-846764573393223673938400 : Int)/10^30,(-431476689896611215536804103 : Int)/10^30)
theorem v3430_mb_checked : Scalar.distance (sourceCoefficient 46 50 3 1) v3430_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3430_mg : Scalar.QComplex := ((-93086250619923098080347 : Int)/10^30,(182679948049663917361 : Int)/10^30)
theorem v3430_mg_checked : Scalar.distance (sourceCoefficient 46 50 3 2) v3430_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3430_upper : Scalar.QComplex := ((999996008466806654468273758233 : Int)/10^30,(-2825429251344621772337347999 : Int)/10^30)
theorem v3430_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 50 5) 1) 14) v3430_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3430 : Material (46 : Basis) (50 : Basis) where
  plus := ![v3430_pa,v3430_pb,v3430_pg]
  minus := ![(Primitive.Addresses.material3430 1).one,v3430_mb,v3430_mg]
  upper := v3430_upper
  lower := (Primitive.Addresses.material3430 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3430_pa_checked.trans (by decide +kernel)
    · exact v3430_pb_checked.trans (by decide +kernel)
    · exact v3430_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 50 Primitive.Addresses.material3430
    · exact v3430_mb_checked.trans (by decide +kernel)
    · exact v3430_mg_checked.trans (by decide +kernel)
  upper_error := v3430_upper_checked
  lower_error := reuse_lower_error 46 50 Primitive.Addresses.material3430

def v3431_pa : Scalar.QComplex := ((999999383037168332934148786082 : Int)/10^30,(-1110821895125855017814427823 : Int)/10^30)
theorem v3431_pa_checked : Scalar.distance (sourceCoefficient 46 51 1 0) v3431_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3431_pb : Scalar.QComplex := ((-479294677220538748002048 : Int)/10^30,(-431477254469524036090733508 : Int)/10^30)
theorem v3431_pb_checked : Scalar.distance (sourceCoefficient 46 51 1 1) v3431_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3431_pg : Scalar.QComplex := ((-93086372430993359417134 : Int)/10^30,(103402444429652103915 : Int)/10^30)
theorem v3431_pg_checked : Scalar.distance (sourceCoefficient 46 51 1 2) v3431_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3431_mb : Scalar.QComplex := ((-851639936350270900212124 : Int)/10^30,(-431476680201102901999035554 : Int)/10^30)
theorem v3431_mb_checked : Scalar.distance (sourceCoefficient 46 51 3 1) v3431_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3431_mg : Scalar.QComplex := ((-93086248539030176402293 : Int)/10^30,(183731752881560524459 : Int)/10^30)
theorem v3431_mg_checked : Scalar.distance (sourceCoefficient 46 51 3 2) v3431_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3431_upper : Scalar.QComplex := ((999995976477737466197768659229 : Int)/10^30,(-2836728456573911721148046233 : Int)/10^30)
theorem v3431_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 51 5) 1) 14) v3431_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3431 : Material (46 : Basis) (51 : Basis) where
  plus := ![v3431_pa,v3431_pb,v3431_pg]
  minus := ![(Primitive.Addresses.material3431 1).one,v3431_mb,v3431_mg]
  upper := v3431_upper
  lower := (Primitive.Addresses.material3431 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3431_pa_checked.trans (by decide +kernel)
    · exact v3431_pb_checked.trans (by decide +kernel)
    · exact v3431_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 51 Primitive.Addresses.material3431
    · exact v3431_mb_checked.trans (by decide +kernel)
    · exact v3431_mg_checked.trans (by decide +kernel)
  upper_error := v3431_upper_checked
  lower_error := reuse_lower_error 46 51 Primitive.Addresses.material3431

def v3432_pa : Scalar.QComplex := ((999999355875020887816188488825 : Int)/10^30,(-1135010811986995525973434132 : Int)/10^30)
theorem v3432_pa_checked : Scalar.distance (sourceCoefficient 46 52 1 0) v3432_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3432_pb : Scalar.QComplex := ((-489731650782168582453235 : Int)/10^30,(-431477242473519614724516990 : Int)/10^30)
theorem v3432_pb_checked : Scalar.distance (sourceCoefficient 46 52 1 1) v3432_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3432_pg : Scalar.QComplex := ((-93086369872778070049382 : Int)/10^30,(105654104308671365643 : Int)/10^30)
theorem v3432_pg_checked : Scalar.distance (sourceCoefficient 46 52 1 2) v3432_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3432_mb : Scalar.QComplex := ((-862076895673726948756769 : Int)/10^30,(-431476659198464827446588320 : Int)/10^30)
theorem v3432_mb_checked : Scalar.distance (sourceCoefficient 46 52 3 1) v3432_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3432_mg : Scalar.QComplex := ((-93086244037734774977784 : Int)/10^30,(185983409714559330303 : Int)/10^30)
theorem v3432_mg_checked : Scalar.distance (sourceCoefficient 46 52 3 2) v3432_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3432_upper : Scalar.QComplex := ((999995907567754374975140482236 : Int)/10^30,(-2860917290529099634906218787 : Int)/10^30)
theorem v3432_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 52 5) 1) 14) v3432_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3432 : Material (46 : Basis) (52 : Basis) where
  plus := ![v3432_pa,v3432_pb,v3432_pg]
  minus := ![(Primitive.Addresses.material3432 1).one,v3432_mb,v3432_mg]
  upper := v3432_upper
  lower := (Primitive.Addresses.material3432 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3432_pa_checked.trans (by decide +kernel)
    · exact v3432_pb_checked.trans (by decide +kernel)
    · exact v3432_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 52 Primitive.Addresses.material3432
    · exact v3432_mb_checked.trans (by decide +kernel)
    · exact v3432_mg_checked.trans (by decide +kernel)
  upper_error := v3432_upper_checked
  lower_error := reuse_lower_error 46 52 Primitive.Addresses.material3432

def v3433_pa : Scalar.QComplex := ((999999351665572891377150079769 : Int)/10^30,(-1138713499471977071184041242 : Int)/10^30)
theorem v3433_pa_checked : Scalar.distance (sourceCoefficient 46 53 1 0) v3433_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3433_pb : Scalar.QComplex := ((-491329277140409127544517 : Int)/10^30,(-431477240607539637781234364 : Int)/10^30)
theorem v3433_pb_checked : Scalar.distance (sourceCoefficient 46 53 1 1) v3433_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3433_pg : Scalar.QComplex := ((-93086369475574714144580 : Int)/10^30,(105998774261327694746 : Int)/10^30)
theorem v3433_pg_checked : Scalar.distance (sourceCoefficient 46 53 1 2) v3433_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3433_mb : Scalar.QComplex := ((-863674519826841506059878 : Int)/10^30,(-431476655953805952551441719 : Int)/10^30)
theorem v3433_mb_checked : Scalar.distance (sourceCoefficient 46 53 3 1) v3433_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3433_mg : Scalar.QComplex := ((-93086243343096921185947 : Int)/10^30,(186328079196110677066 : Int)/10^30)
theorem v3433_mg_checked : Scalar.distance (sourceCoefficient 46 53 3 2) v3433_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3433_upper : Scalar.QComplex := ((999995896967809954120959459867 : Int)/10^30,(-2864619965234237755747634983 : Int)/10^30)
theorem v3433_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 53 5) 1) 14) v3433_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3433 : Material (46 : Basis) (53 : Basis) where
  plus := ![v3433_pa,v3433_pb,v3433_pg]
  minus := ![(Primitive.Addresses.material3433 1).one,v3433_mb,v3433_mg]
  upper := v3433_upper
  lower := (Primitive.Addresses.material3433 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3433_pa_checked.trans (by decide +kernel)
    · exact v3433_pb_checked.trans (by decide +kernel)
    · exact v3433_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 53 Primitive.Addresses.material3433
    · exact v3433_mb_checked.trans (by decide +kernel)
    · exact v3433_mg_checked.trans (by decide +kernel)
  upper_error := v3433_upper_checked
  lower_error := reuse_lower_error 46 53 Primitive.Addresses.material3433

def v3434_pa : Scalar.QComplex := ((999999349520207042602434994641 : Int)/10^30,(-1140595968251174419393014234 : Int)/10^30)
theorem v3434_pa_checked : Scalar.distance (sourceCoefficient 46 54 1 0) v3434_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3434_pb : Scalar.QComplex := ((-492141520071710661701421 : Int)/10^30,(-431477239655839757066628654 : Int)/10^30)
theorem v3434_pb_checked : Scalar.distance (sourceCoefficient 46 54 1 1) v3434_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3434_pg : Scalar.QComplex := ((-93086369273063209232247 : Int)/10^30,(106174006556041704246 : Int)/10^30)
theorem v3434_pg_checked : Scalar.distance (sourceCoefficient 46 54 1 2) v3434_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3434_mb : Scalar.QComplex := ((-864486761634433741472204 : Int)/10^30,(-431476654301177358548608241 : Int)/10^30)
theorem v3434_mb_checked : Scalar.distance (sourceCoefficient 46 54 3 1) v3434_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3434_mg : Scalar.QComplex := ((-93086242989367913509294 : Int)/10^30,(186503311250819386773 : Int)/10^30)
theorem v3434_mg_checked : Scalar.distance (sourceCoefficient 46 54 3 2) v3434_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3434_upper : Scalar.QComplex := ((999995891573476963955658796354 : Int)/10^30,(-2866502427507012158742827023 : Int)/10^30)
theorem v3434_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 54 5) 1) 14) v3434_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3434 : Material (46 : Basis) (54 : Basis) where
  plus := ![v3434_pa,v3434_pb,v3434_pg]
  minus := ![(Primitive.Addresses.material3434 1).one,v3434_mb,v3434_mg]
  upper := v3434_upper
  lower := (Primitive.Addresses.material3434 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3434_pa_checked.trans (by decide +kernel)
    · exact v3434_pb_checked.trans (by decide +kernel)
    · exact v3434_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 54 Primitive.Addresses.material3434
    · exact v3434_mb_checked.trans (by decide +kernel)
    · exact v3434_mg_checked.trans (by decide +kernel)
  upper_error := v3434_upper_checked
  lower_error := reuse_lower_error 46 54 Primitive.Addresses.material3434

def v3435_pa : Scalar.QComplex := ((999999331901650379746479020557 : Int)/10^30,(-1155939554165831924038857257 : Int)/10^30)
theorem v3435_pa_checked : Scalar.distance (sourceCoefficient 46 55 1 0) v3435_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3435_pb : Scalar.QComplex := ((-498761932207881078031762 : Int)/10^30,(-431477231822715720484397348 : Int)/10^30)
theorem v3435_pb_checked : Scalar.distance (sourceCoefficient 46 55 1 1) v3435_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3435_pg : Scalar.QComplex := ((-93086367608084665038058 : Int)/10^30,(107602286160715925281 : Int)/10^30)
theorem v3435_pg_checked : Scalar.distance (sourceCoefficient 46 55 1 2) v3435_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3435_mb : Scalar.QComplex := ((-871107164545888898964455 : Int)/10^30,(-431476640754938737375315193 : Int)/10^30)
theorem v3435_mb_checked : Scalar.distance (sourceCoefficient 46 55 3 1) v3435_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3435_mg : Scalar.QComplex := ((-93086240091849017754309 : Int)/10^30,(187931588886878339595 : Int)/10^30)
theorem v3435_mg_checked : Scalar.distance (sourceCoefficient 46 55 3 2) v3435_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3435_upper : Scalar.QComplex := ((999995847473309212412166932791 : Int)/10^30,(-2881845960161170370603942068 : Int)/10^30)
theorem v3435_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 55 5) 1) 14) v3435_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3435 : Material (46 : Basis) (55 : Basis) where
  plus := ![v3435_pa,v3435_pb,v3435_pg]
  minus := ![(Primitive.Addresses.material3435 1).one,v3435_mb,v3435_mg]
  upper := v3435_upper
  lower := (Primitive.Addresses.material3435 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3435_pa_checked.trans (by decide +kernel)
    · exact v3435_pb_checked.trans (by decide +kernel)
    · exact v3435_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 55 Primitive.Addresses.material3435
    · exact v3435_mb_checked.trans (by decide +kernel)
    · exact v3435_mg_checked.trans (by decide +kernel)
  upper_error := v3435_upper_checked
  lower_error := reuse_lower_error 46 55 Primitive.Addresses.material3435

def v3436_pa : Scalar.QComplex := ((999999327685708068932327977712 : Int)/10^30,(-1159581015649889039382614921 : Int)/10^30)
theorem v3436_pa_checked : Scalar.distance (sourceCoefficient 46 56 1 0) v3436_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3436_pb : Scalar.QComplex := ((-500333140909165576294794 : Int)/10^30,(-431477229943810259620693166 : Int)/10^30)
theorem v3436_pb_checked : Scalar.distance (sourceCoefficient 46 56 1 1) v3436_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3436_pg : Scalar.QComplex := ((-93086367209184778867445 : Int)/10^30,(107941256802034649976 : Int)/10^30)
theorem v3436_pg_checked : Scalar.distance (sourceCoefficient 46 56 1 2) v3436_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3436_mb : Scalar.QComplex := ((-872678371040729799989480 : Int)/10^30,(-431476637520151631518462251 : Int)/10^30)
theorem v3436_mb_checked : Scalar.distance (sourceCoefficient 46 56 3 1) v3436_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3436_mg : Scalar.QComplex := ((-93086239400432883325255 : Int)/10^30,(188270559057750166823 : Int)/10^30)
theorem v3436_mg_checked : Scalar.distance (sourceCoefficient 46 56 3 2) v3436_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3436_upper : Scalar.QComplex := ((999995836972541010071542179418 : Int)/10^30,(-2885487408945364400392313700 : Int)/10^30)
theorem v3436_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 56 5) 1) 14) v3436_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3436 : Material (46 : Basis) (56 : Basis) where
  plus := ![v3436_pa,v3436_pb,v3436_pg]
  minus := ![(Primitive.Addresses.material3436 1).one,v3436_mb,v3436_mg]
  upper := v3436_upper
  lower := (Primitive.Addresses.material3436 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3436_pa_checked.trans (by decide +kernel)
    · exact v3436_pb_checked.trans (by decide +kernel)
    · exact v3436_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 56 Primitive.Addresses.material3436
    · exact v3436_mb_checked.trans (by decide +kernel)
    · exact v3436_mg_checked.trans (by decide +kernel)
  upper_error := v3436_upper_checked
  lower_error := reuse_lower_error 46 56 Primitive.Addresses.material3436

def v3437_pa : Scalar.QComplex := ((999999313958970532389822718842 : Int)/10^30,(-1171358864004932623954564967 : Int)/10^30)
theorem v3437_pa_checked : Scalar.distance (sourceCoefficient 46 57 1 0) v3437_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3437_pb : Scalar.QComplex := ((-505415017466779431609150 : Int)/10^30,(-431477223814487842062015040 : Int)/10^30)
theorem v3437_pb_checked : Scalar.distance (sourceCoefficient 46 57 1 1) v3437_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3437_pg : Scalar.QComplex := ((-93086365909132042050706 : Int)/10^30,(109037614629945787461 : Int)/10^30)
theorem v3437_pg_checked : Scalar.distance (sourceCoefficient 46 57 1 2) v3437_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3437_mb : Scalar.QComplex := ((-877760240416799567752898 : Int)/10^30,(-431476627005400906189645684 : Int)/10^30)
theorem v3437_mb_checked : Scalar.distance (sourceCoefficient 46 57 3 1) v3437_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3437_mg : Scalar.QComplex := ((-93086237154273203213821 : Int)/10^30,(189366915355550219277 : Int)/10^30)
theorem v3437_mg_checked : Scalar.distance (sourceCoefficient 46 57 3 2) v3437_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3437_upper : Scalar.QComplex := ((999995802918326135143191789974 : Int)/10^30,(-2897265216067582675211194177 : Int)/10^30)
theorem v3437_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 57 5) 1) 14) v3437_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3437 : Material (46 : Basis) (57 : Basis) where
  plus := ![v3437_pa,v3437_pb,v3437_pg]
  minus := ![(Primitive.Addresses.material3437 1).one,v3437_mb,v3437_mg]
  upper := v3437_upper
  lower := (Primitive.Addresses.material3437 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3437_pa_checked.trans (by decide +kernel)
    · exact v3437_pb_checked.trans (by decide +kernel)
    · exact v3437_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 57 Primitive.Addresses.material3437
    · exact v3437_mb_checked.trans (by decide +kernel)
    · exact v3437_mg_checked.trans (by decide +kernel)
  upper_error := v3437_upper_checked
  lower_error := reuse_lower_error 46 57 Primitive.Addresses.material3437

def v3438_pa : Scalar.QComplex := ((999999306452923251679015360349 : Int)/10^30,(-1177749409886965005197959471 : Int)/10^30)
theorem v3438_pa_checked : Scalar.distance (sourceCoefficient 46 58 1 0) v3438_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3438_pb : Scalar.QComplex := ((-508172394212469044431481 : Int)/10^30,(-431477220455379026298607175 : Int)/10^30)
theorem v3438_pb_checked : Scalar.distance (sourceCoefficient 46 58 1 1) v3438_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3438_pg : Scalar.QComplex := ((-93086365197431467150587 : Int)/10^30,(109632487715088798592 : Int)/10^30)
theorem v3438_pg_checked : Scalar.distance (sourceCoefficient 46 58 1 2) v3438_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3438_mb : Scalar.QComplex := ((-880517613237032180453418 : Int)/10^30,(-431476621266801397284396938 : Int)/10^30)
theorem v3438_mb_checked : Scalar.distance (sourceCoefficient 46 58 3 1) v3438_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3438_mg : Scalar.QComplex := ((-93086235929224212923120 : Int)/10^30,(189961787605029251431 : Int)/10^30)
theorem v3438_mg_checked : Scalar.distance (sourceCoefficient 46 58 3 2) v3438_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3438_upper : Scalar.QComplex := ((999995784382787587213889139404 : Int)/10^30,(-2903655739476890988202708940 : Int)/10^30)
theorem v3438_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 58 5) 1) 14) v3438_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3438 : Material (46 : Basis) (58 : Basis) where
  plus := ![v3438_pa,v3438_pb,v3438_pg]
  minus := ![(Primitive.Addresses.material3438 1).one,v3438_mb,v3438_mg]
  upper := v3438_upper
  lower := (Primitive.Addresses.material3438 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3438_pa_checked.trans (by decide +kernel)
    · exact v3438_pb_checked.trans (by decide +kernel)
    · exact v3438_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 58 Primitive.Addresses.material3438
    · exact v3438_mb_checked.trans (by decide +kernel)
    · exact v3438_mg_checked.trans (by decide +kernel)
  upper_error := v3438_upper_checked
  lower_error := reuse_lower_error 46 58 Primitive.Addresses.material3438

def v3439_pa : Scalar.QComplex := ((999999285610382278684037020194 : Int)/10^30,(-1195315324544158104366252356 : Int)/10^30)
theorem v3439_pa_checked : Scalar.distance (sourceCoefficient 46 59 1 0) v3439_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3439_pb : Scalar.QComplex := ((-515751691068290980004029 : Int)/10^30,(-431477211101031393901391217 : Int)/10^30)
theorem v3439_pb_checked : Scalar.distance (sourceCoefficient 46 59 1 1) v3439_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3439_pg : Scalar.QComplex := ((-93086363218304874192306 : Int)/10^30,(111267635949367383000 : Int)/10^30)
theorem v3439_pg_checked : Scalar.distance (sourceCoefficient 46 59 1 2) v3439_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3439_mb : Scalar.QComplex := ((-888096899198354803044106 : Int)/10^30,(-431476605371865420222538675 : Int)/10^30)
theorem v3439_mb_checked : Scalar.distance (sourceCoefficient 46 59 3 1) v3439_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3439_mg : Scalar.QComplex := ((-93086232539039075044367 : Int)/10^30,(191596933522570305082 : Int)/10^30)
theorem v3439_mg_checked : Scalar.distance (sourceCoefficient 46 59 3 2) v3439_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3439_upper : Scalar.QComplex := ((999995733223102525749499782977 : Int)/10^30,(-2921221591999382743923535967 : Int)/10^30)
theorem v3439_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 59 5) 1) 14) v3439_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3439 : Material (46 : Basis) (59 : Basis) where
  plus := ![v3439_pa,v3439_pb,v3439_pg]
  minus := ![(Primitive.Addresses.material3439 1).one,v3439_mb,v3439_mg]
  upper := v3439_upper
  lower := (Primitive.Addresses.material3439 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3439_pa_checked.trans (by decide +kernel)
    · exact v3439_pb_checked.trans (by decide +kernel)
    · exact v3439_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 59 Primitive.Addresses.material3439
    · exact v3439_mb_checked.trans (by decide +kernel)
    · exact v3439_mg_checked.trans (by decide +kernel)
  upper_error := v3439_upper_checked
  lower_error := reuse_lower_error 46 59 Primitive.Addresses.material3439

def v3440_pa : Scalar.QComplex := ((999999261183282689816226108251 : Int)/10^30,(-1215579240021079732649535239 : Int)/10^30)
theorem v3440_pa_checked : Scalar.distance (sourceCoefficient 46 60 1 0) v3440_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3440_pb : Scalar.QComplex := ((-524495114476871069453698 : Int)/10^30,(-431477200089413276258743353 : Int)/10^30)
theorem v3440_pb_checked : Scalar.distance (sourceCoefficient 46 60 1 1) v3440_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3440_pg : Scalar.QComplex := ((-93086360893572650702296 : Int)/10^30,(113153931431353170080 : Int)/10^30)
theorem v3440_pg_checked : Scalar.distance (sourceCoefficient 46 60 1 2) v3440_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3440_mb : Scalar.QComplex := ((-896840309848828272633357 : Int)/10^30,(-431476586815070790276135868 : Int)/10^30)
theorem v3440_mb_checked : Scalar.distance (sourceCoefficient 46 60 3 1) v3440_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3440_mg : Scalar.QComplex := ((-93086228586519671799483 : Int)/10^30,(193483226296062869437 : Int)/10^30)
theorem v3440_mg_checked : Scalar.distance (sourceCoefficient 46 60 3 2) v3440_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3440_upper : Scalar.QComplex := ((999995673822359533062223045552 : Int)/10^30,(-2941485435136624754833961932 : Int)/10^30)
theorem v3440_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 46 60 5) 1) 14) v3440_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3440 : Material (46 : Basis) (60 : Basis) where
  plus := ![v3440_pa,v3440_pb,v3440_pg]
  minus := ![(Primitive.Addresses.material3440 1).one,v3440_mb,v3440_mg]
  upper := v3440_upper
  lower := (Primitive.Addresses.material3440 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3440_pa_checked.trans (by decide +kernel)
    · exact v3440_pb_checked.trans (by decide +kernel)
    · exact v3440_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 46 60 Primitive.Addresses.material3440
    · exact v3440_mb_checked.trans (by decide +kernel)
    · exact v3440_mg_checked.trans (by decide +kernel)
  upper_error := v3440_upper_checked
  lower_error := reuse_lower_error 46 60 Primitive.Addresses.material3440

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
