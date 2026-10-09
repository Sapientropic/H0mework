import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B124
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B125

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2993_pa : Scalar.QComplex := ((999999506065611935551431368869 : Int)/10^30,(-993915757072860488746472695 : Int)/10^30)
theorem v2993_pa_checked : Scalar.distance (sourceCoefficient 38 49 1 0) v2993_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2993_pb : Scalar.QComplex := ((-428852305196063644611447 : Int)/10^30,(-431477306119139290553336067 : Int)/10^30)
theorem v2993_pb_checked : Scalar.distance (sourceCoefficient 38 49 1 1) v2993_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2993_pg : Scalar.QComplex := ((-93086383728544903126894 : Int)/10^30,(92520069255575300747 : Int)/10^30)
theorem v2993_pg_checked : Scalar.distance (sourceCoefficient 38 49 1 2) v2993_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2993_mb : Scalar.QComplex := ((-801197627679087984103974 : Int)/10^30,(-431476775380194141970075461 : Int)/10^30)
theorem v2993_mb_checked : Scalar.distance (sourceCoefficient 38 49 3 1) v2993_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2993_mg : Scalar.QComplex := ((-93086269227577164761987 : Int)/10^30,(172849391508767507103 : Int)/10^30)
theorem v2993_mg_checked : Scalar.distance (sourceCoefficient 38 49 3 2) v2993_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2993_upper : Scalar.QComplex := ((999996301275386469871359618697 : Int)/10^30,(-2719822704974809667265150226 : Int)/10^30)
theorem v2993_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 49 5) 1) 14) v2993_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2993 : Material (38 : Basis) (49 : Basis) where
  plus := ![v2993_pa,v2993_pb,v2993_pg]
  minus := ![(Primitive.Addresses.material2993 1).one,v2993_mb,v2993_mg]
  upper := v2993_upper
  lower := (Primitive.Addresses.material2993 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2993_pa_checked.trans (by decide +kernel)
    · exact v2993_pb_checked.trans (by decide +kernel)
    · exact v2993_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 49 Primitive.Addresses.material2993
    · exact v2993_mb_checked.trans (by decide +kernel)
    · exact v2993_mg_checked.trans (by decide +kernel)
  upper_error := v2993_upper_checked
  lower_error := reuse_lower_error 38 49 Primitive.Addresses.material2993

def v2994_pa : Scalar.QComplex := ((999999503502683436409295281020 : Int)/10^30,(-996491036897771627212894435 : Int)/10^30)
theorem v2994_pa_checked : Scalar.distance (sourceCoefficient 38 50 1 0) v2994_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2994_pb : Scalar.QComplex := ((-429963480488051425893453 : Int)/10^30,(-431477304954872731097361257 : Int)/10^30)
theorem v2994_pb_checked : Scalar.distance (sourceCoefficient 38 50 1 1) v2994_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2994_pg : Scalar.QComplex := ((-93086383483669253087342 : Int)/10^30,(92759792853693413915 : Int)/10^30)
theorem v2994_pg_checked : Scalar.distance (sourceCoefficient 38 50 1 2) v2994_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2994_mb : Scalar.QComplex := ((-802308801552624816768136 : Int)/10^30,(-431476773257033784515670785 : Int)/10^30)
theorem v2994_mb_checked : Scalar.distance (sourceCoefficient 38 50 3 1) v2994_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2994_mg : Scalar.QComplex := ((-93086268775830937474965 : Int)/10^30,(173089114806308911588 : Int)/10^30)
theorem v2994_mg_checked : Scalar.distance (sourceCoefficient 38 50 3 2) v2994_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2994_upper : Scalar.QComplex := ((999996294267762437674252867132 : Int)/10^30,(-2722397976540761937682957793 : Int)/10^30)
theorem v2994_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 50 5) 1) 14) v2994_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2994 : Material (38 : Basis) (50 : Basis) where
  plus := ![v2994_pa,v2994_pb,v2994_pg]
  minus := ![(Primitive.Addresses.material2994 1).one,v2994_mb,v2994_mg]
  upper := v2994_upper
  lower := (Primitive.Addresses.material2994 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2994_pa_checked.trans (by decide +kernel)
    · exact v2994_pb_checked.trans (by decide +kernel)
    · exact v2994_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 50 Primitive.Addresses.material2994
    · exact v2994_mb_checked.trans (by decide +kernel)
    · exact v2994_mg_checked.trans (by decide +kernel)
  upper_error := v2994_upper_checked
  lower_error := reuse_lower_error 38 50 Primitive.Addresses.material2994

def v2995_pa : Scalar.QComplex := ((999999492179245079183751295720 : Int)/10^30,(-1007790281735100563804934104 : Int)/10^30)
theorem v2995_pa_checked : Scalar.distance (sourceCoefficient 38 51 1 0) v2995_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2995_pb : Scalar.QComplex := ((-434838850349412133780016 : Int)/10^30,(-431477299801465017391466663 : Int)/10^30)
theorem v2995_pb_checked : Scalar.distance (sourceCoefficient 38 51 1 1) v2995_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2995_pg : Scalar.QComplex := ((-93086382400745105786618 : Int)/10^30,(93811599184825335322 : Int)/10^30)
theorem v2995_pg_checked : Scalar.distance (sourceCoefficient 38 51 1 2) v2995_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2995_mb : Scalar.QComplex := ((-807184165151503753799388 : Int)/10^30,(-431476763896403377812117809 : Int)/10^30)
theorem v2995_mb_checked : Scalar.distance (sourceCoefficient 38 51 3 1) v2995_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2995_mg : Scalar.QComplex := ((-93086266785245701228183 : Int)/10^30,(174140919811290499963 : Int)/10^30)
theorem v2995_mg_checked : Scalar.distance (sourceCoefficient 38 51 3 2) v2995_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2995_upper : Scalar.QComplex := ((999996263442869415634570123195 : Int)/10^30,(-2733697185005965641342065255 : Int)/10^30)
theorem v2995_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 51 5) 1) 14) v2995_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2995 : Material (38 : Basis) (51 : Basis) where
  plus := ![v2995_pa,v2995_pb,v2995_pg]
  minus := ![(Primitive.Addresses.material2995 1).one,v2995_mb,v2995_mg]
  upper := v2995_upper
  lower := (Primitive.Addresses.material2995 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2995_pa_checked.trans (by decide +kernel)
    · exact v2995_pb_checked.trans (by decide +kernel)
    · exact v2995_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 51 Primitive.Addresses.material2995
    · exact v2995_mb_checked.trans (by decide +kernel)
    · exact v2995_mg_checked.trans (by decide +kernel)
  upper_error := v2995_upper_checked
  lower_error := reuse_lower_error 38 51 Primitive.Addresses.material2995

def v2996_pa : Scalar.QComplex := ((999999467509322303606708578686 : Int)/10^30,(-1031979201266413483757533707 : Int)/10^30)
theorem v2996_pa_checked : Scalar.distance (sourceCoefficient 38 52 1 0) v2996_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2996_pb : Scalar.QComplex := ((-445275824679121544016109 : Int)/10^30,(-431477288522353205074700083 : Int)/10^30)
theorem v2996_pb_checked : Scalar.distance (sourceCoefficient 38 52 1 1) v2996_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2996_pg : Scalar.QComplex := ((-93086380035856730246611 : Int)/10^30,(96063259270975277552 : Int)/10^30)
theorem v2996_pg_checked : Scalar.distance (sourceCoefficient 38 52 1 2) v2996_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2996_mb : Scalar.QComplex := ((-817621125861685126102948 : Int)/10^30,(-431476743610656982559157671 : Int)/10^30)
theorem v2996_mb_checked : Scalar.distance (sourceCoefficient 38 52 3 1) v2996_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2996_mg : Scalar.QComplex := ((-93086262477276962902525 : Int)/10^30,(176392577018252328697 : Int)/10^30)
theorem v2996_mg_checked : Scalar.distance (sourceCoefficient 38 52 3 2) v2996_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2996_upper : Scalar.QComplex := ((999996197025102673601624913199 : Int)/10^30,(-2757886025932675676757427680 : Int)/10^30)
theorem v2996_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 52 5) 1) 14) v2996_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2996 : Material (38 : Basis) (52 : Basis) where
  plus := ![v2996_pa,v2996_pb,v2996_pg]
  minus := ![(Primitive.Addresses.material2996 1).one,v2996_mb,v2996_mg]
  upper := v2996_upper
  lower := (Primitive.Addresses.material2996 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2996_pa_checked.trans (by decide +kernel)
    · exact v2996_pb_checked.trans (by decide +kernel)
    · exact v2996_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 52 Primitive.Addresses.material2996
    · exact v2996_mb_checked.trans (by decide +kernel)
    · exact v2996_mg_checked.trans (by decide +kernel)
  upper_error := v2996_upper_checked
  lower_error := reuse_lower_error 38 52 Primitive.Addresses.material2996

def v2997_pa : Scalar.QComplex := ((999999463681368408506524239092 : Int)/10^30,(-1035681889165448504006011043 : Int)/10^30)
theorem v2997_pa_checked : Scalar.distance (sourceCoefficient 38 53 1 0) v2997_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2997_pb : Scalar.QComplex := ((-446873451156465266091367 : Int)/10^30,(-431477286766110646625193416 : Int)/10^30)
theorem v2997_pb_checked : Scalar.distance (sourceCoefficient 38 53 1 1) v2997_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2997_pg : Scalar.QComplex := ((-93086379668246644218282 : Int)/10^30,(96407929255750573075 : Int)/10^30)
theorem v2997_pg_checked : Scalar.distance (sourceCoefficient 38 53 1 2) v2997_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2997_mb : Scalar.QComplex := ((-819218750228601265812747 : Int)/10^30,(-431476740475735382516853347 : Int)/10^30)
theorem v2997_mb_checked : Scalar.distance (sourceCoefficient 38 53 3 1) v2997_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2997_mg : Scalar.QComplex := ((-93086261812232340251012 : Int)/10^30,(176737246557460288993 : Int)/10^30)
theorem v2997_mg_checked : Scalar.distance (sourceCoefficient 38 53 3 2) v2997_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2997_upper : Scalar.QComplex := ((999996186806651071276912183654 : Int)/10^30,(-2761588701710290865989039525 : Int)/10^30)
theorem v2997_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 53 5) 1) 14) v2997_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2997 : Material (38 : Basis) (53 : Basis) where
  plus := ![v2997_pa,v2997_pb,v2997_pg]
  minus := ![(Primitive.Addresses.material2997 1).one,v2997_mb,v2997_mg]
  upper := v2997_upper
  lower := (Primitive.Addresses.material2997 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2997_pa_checked.trans (by decide +kernel)
    · exact v2997_pb_checked.trans (by decide +kernel)
    · exact v2997_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 53 Primitive.Addresses.material2997
    · exact v2997_mb_checked.trans (by decide +kernel)
    · exact v2997_mg_checked.trans (by decide +kernel)
  upper_error := v2997_upper_checked
  lower_error := reuse_lower_error 38 53 Primitive.Addresses.material2997

def v2998_pa : Scalar.QComplex := ((999999461729956475160682091825 : Int)/10^30,(-1037564358155694783204809675 : Int)/10^30)
theorem v2998_pa_checked : Scalar.distance (sourceCoefficient 38 54 1 0) v2998_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2998_pb : Scalar.QComplex := ((-447685694148475379437519 : Int)/10^30,(-431477285870201935182909032 : Int)/10^30)
theorem v2998_pb_checked : Scalar.distance (sourceCoefficient 38 54 1 1) v2998_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2998_pg : Scalar.QComplex := ((-93086379480780537235983 : Int)/10^30,(96583161566836075476 : Int)/10^30)
theorem v2998_pg_checked : Scalar.distance (sourceCoefficient 38 54 1 2) v2998_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2998_mb : Scalar.QComplex := ((-820030992145047324150768 : Int)/10^30,(-431476738878897884623969465 : Int)/10^30)
theorem v2998_mb_checked : Scalar.distance (sourceCoefficient 38 54 3 1) v2998_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2998_mg : Scalar.QComplex := ((-93086261473548710774444 : Int)/10^30,(176912478641523986299 : Int)/10^30)
theorem v2998_mg_checked : Scalar.distance (sourceCoefficient 38 54 3 2) v2998_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2998_upper : Scalar.QComplex := ((999996181606271343417602175069 : Int)/10^30,(-2763471164528860748309940452 : Int)/10^30)
theorem v2998_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 54 5) 1) 14) v2998_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2998 : Material (38 : Basis) (54 : Basis) where
  plus := ![v2998_pa,v2998_pb,v2998_pg]
  minus := ![(Primitive.Addresses.material2998 1).one,v2998_mb,v2998_mg]
  upper := v2998_upper
  lower := (Primitive.Addresses.material2998 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2998_pa_checked.trans (by decide +kernel)
    · exact v2998_pb_checked.trans (by decide +kernel)
    · exact v2998_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 54 Primitive.Addresses.material2998
    · exact v2998_mb_checked.trans (by decide +kernel)
    · exact v2998_mg_checked.trans (by decide +kernel)
  upper_error := v2998_upper_checked
  lower_error := reuse_lower_error 38 54 Primitive.Addresses.material2998

def v2999_pa : Scalar.QComplex := ((999999445692275202682500546835 : Int)/10^30,(-1052907945804181510512273878 : Int)/10^30)
theorem v2999_pa_checked : Scalar.distance (sourceCoefficient 38 55 1 0) v2999_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2999_pb : Scalar.QComplex := ((-454306106783384681310828 : Int)/10^30,(-431477278491819357594855201 : Int)/10^30)
theorem v2999_pb_checked : Scalar.distance (sourceCoefficient 38 55 1 1) v2999_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2999_pg : Scalar.QComplex := ((-93086377938433697947963 : Int)/10^30,(98011441306006939882 : Int)/10^30)
theorem v2999_pg_checked : Scalar.distance (sourceCoefficient 38 55 1 2) v2999_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2999_mb : Scalar.QComplex := ((-826651395947662579799653 : Int)/10^30,(-431476725787400122734630138 : Int)/10^30)
theorem v2999_mb_checked : Scalar.distance (sourceCoefficient 38 55 3 1) v2999_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2999_mg : Scalar.QComplex := ((-93086258698661358199694 : Int)/10^30,(178340756517905170620 : Int)/10^30)
theorem v2999_mg_checked : Scalar.distance (sourceCoefficient 38 55 3 2) v2999_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2999_upper : Scalar.QComplex := ((999996139086973635291746885585 : Int)/10^30,(-2778814701645293108394646495 : Int)/10^30)
theorem v2999_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 55 5) 1) 14) v2999_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2999 : Material (38 : Basis) (55 : Basis) where
  plus := ![v2999_pa,v2999_pb,v2999_pg]
  minus := ![(Primitive.Addresses.material2999 1).one,v2999_mb,v2999_mg]
  upper := v2999_upper
  lower := (Primitive.Addresses.material2999 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2999_pa_checked.trans (by decide +kernel)
    · exact v2999_pb_checked.trans (by decide +kernel)
    · exact v2999_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 55 Primitive.Addresses.material2999
    · exact v2999_mb_checked.trans (by decide +kernel)
    · exact v2999_mg_checked.trans (by decide +kernel)
  upper_error := v2999_upper_checked
  lower_error := reuse_lower_error 38 55 Primitive.Addresses.material2999

def v3000_pa : Scalar.QComplex := ((999999441851518776054017693498 : Int)/10^30,(-1056549407703286194036362203 : Int)/10^30)
theorem v3000_pa_checked : Scalar.distance (sourceCoefficient 38 56 1 0) v3000_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3000_pb : Scalar.QComplex := ((-455877315604058309041469 : Int)/10^30,(-431477276720836745903982200 : Int)/10^30)
theorem v3000_pb_checked : Scalar.distance (sourceCoefficient 38 56 1 1) v3000_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3000_pg : Scalar.QComplex := ((-93086377568637740465263 : Int)/10^30,(98350411979521744803 : Int)/10^30)
theorem v3000_pg_checked : Scalar.distance (sourceCoefficient 38 56 1 2) v3000_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3000_mb : Scalar.QComplex := ((-828222602655025124009720 : Int)/10^30,(-431476722660535722838557669 : Int)/10^30)
theorem v3000_mb_checked : Scalar.distance (sourceCoefficient 38 56 3 1) v3000_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3000_mg : Scalar.QComplex := ((-93086258036349113838063 : Int)/10^30,(178679726746088445750 : Int)/10^30)
theorem v3000_mg_checked : Scalar.distance (sourceCoefficient 38 56 3 2) v3000_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3000_upper : Scalar.QComplex := ((999996128961390042007038399051 : Int)/10^30,(-2782456151492070887705680176 : Int)/10^30)
theorem v3000_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 56 5) 1) 14) v3000_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3000 : Material (38 : Basis) (56 : Basis) where
  plus := ![v3000_pa,v3000_pb,v3000_pg]
  minus := ![(Primitive.Addresses.material3000 1).one,v3000_mb,v3000_mg]
  upper := v3000_upper
  lower := (Primitive.Addresses.material3000 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3000_pa_checked.trans (by decide +kernel)
    · exact v3000_pb_checked.trans (by decide +kernel)
    · exact v3000_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 56 Primitive.Addresses.material3000
    · exact v3000_mb_checked.trans (by decide +kernel)
    · exact v3000_mg_checked.trans (by decide +kernel)
  upper_error := v3000_upper_checked
  lower_error := reuse_lower_error 38 56 Primitive.Addresses.material3000

def v3001_pa : Scalar.QComplex := ((999999429338272709898703794812 : Int)/10^30,(-1068327257410104461801749423 : Int)/10^30)
theorem v3001_pa_checked : Scalar.distance (sourceCoefficient 38 57 1 0) v3001_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3001_pb : Scalar.QComplex := ((-460959192550512420252571 : Int)/10^30,(-431477270940577186029791542 : Int)/10^30)
theorem v3001_pb_checked : Scalar.distance (sourceCoefficient 38 57 1 1) v3001_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3001_pg : Scalar.QComplex := ((-93086376362717993989116 : Int)/10^30,(99446769912292781433 : Int)/10^30)
theorem v3001_pg_checked : Scalar.distance (sourceCoefficient 38 57 1 2) v3001_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3001_mb : Scalar.QComplex := ((-833304472721160527861086 : Int)/10^30,(-431476712494847389670545569 : Int)/10^30)
theorem v3001_mb_checked : Scalar.distance (sourceCoefficient 38 57 3 1) v3001_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3001_mg : Scalar.QComplex := ((-93086255884322298527836 : Int)/10^30,(179776083229980889377 : Int)/10^30)
theorem v3001_mg_checked : Scalar.distance (sourceCoefficient 38 57 3 2) v3001_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3001_upper : Scalar.QComplex := ((999996096120662497072409798979 : Int)/10^30,(-2794233962060438023210449704 : Int)/10^30)
theorem v3001_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 57 5) 1) 14) v3001_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3001 : Material (38 : Basis) (57 : Basis) where
  plus := ![v3001_pa,v3001_pb,v3001_pg]
  minus := ![(Primitive.Addresses.material3001 1).one,v3001_mb,v3001_mg]
  upper := v3001_upper
  lower := (Primitive.Addresses.material3001 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3001_pa_checked.trans (by decide +kernel)
    · exact v3001_pb_checked.trans (by decide +kernel)
    · exact v3001_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 57 Primitive.Addresses.material3001
    · exact v3001_mb_checked.trans (by decide +kernel)
    · exact v3001_mg_checked.trans (by decide +kernel)
  upper_error := v3001_upper_checked
  lower_error := reuse_lower_error 38 57 Primitive.Addresses.material3001

def v3002_pa : Scalar.QComplex := ((999999422490654090249114559531 : Int)/10^30,(-1074717804031577936793740587 : Int)/10^30)
theorem v3002_pa_checked : Scalar.distance (sourceCoefficient 38 58 1 0) v3002_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3002_pb : Scalar.QComplex := ((-463716569508903504404576 : Int)/10^30,(-431477267770866479396834774 : Int)/10^30)
theorem v3002_pb_checked : Scalar.distance (sourceCoefficient 38 58 1 1) v3002_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3002_pg : Scalar.QComplex := ((-93086375702093063452507 : Int)/10^30,(100041643054795735357 : Int)/10^30)
theorem v3002_pg_checked : Scalar.distance (sourceCoefficient 38 58 1 2) v3002_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3002_mb : Scalar.QComplex := ((-836061845917536570698201 : Int)/10^30,(-431476706945645735822385931 : Int)/10^30)
theorem v3002_mb_checked : Scalar.distance (sourceCoefficient 38 58 3 1) v3002_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3002_mg : Scalar.QComplex := ((-93086254710348884083800 : Int)/10^30,(180370955580895823692 : Int)/10^30)
theorem v3002_mg_checked : Scalar.distance (sourceCoefficient 38 58 3 2) v3002_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3002_upper : Scalar.QComplex := ((999996078243550353343932846552 : Int)/10^30,(-2800624487345574465450046045 : Int)/10^30)
theorem v3002_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 58 5) 1) 14) v3002_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3002 : Material (38 : Basis) (58 : Basis) where
  plus := ![v3002_pa,v3002_pb,v3002_pg]
  minus := ![(Primitive.Addresses.material3002 1).one,v3002_mb,v3002_mg]
  upper := v3002_upper
  lower := (Primitive.Addresses.material3002 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3002_pa_checked.trans (by decide +kernel)
    · exact v3002_pb_checked.trans (by decide +kernel)
    · exact v3002_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 58 Primitive.Addresses.material3002
    · exact v3002_mb_checked.trans (by decide +kernel)
    · exact v3002_mg_checked.trans (by decide +kernel)
  upper_error := v3002_upper_checked
  lower_error := reuse_lower_error 38 58 Primitive.Addresses.material3002

def v3003_pa : Scalar.QComplex := ((999999403457958768735469590091 : Int)/10^30,(-1092283720742977156111093522 : Int)/10^30)
theorem v3003_pa_checked : Scalar.distance (sourceCoefficient 38 59 1 0) v3003_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3003_pb : Scalar.QComplex := ((-471295866955621276935737 : Int)/10^30,(-431477258937123985148503628 : Int)/10^30)
theorem v3003_pb_checked : Scalar.distance (sourceCoefficient 38 59 1 1) v3003_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3003_pg : Scalar.QComplex := ((-93086373863359862048210 : Int)/10^30,(101676791448423247630 : Int)/10^30)
theorem v3003_pg_checked : Scalar.distance (sourceCoefficient 38 59 1 2) v3003_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3003_mb : Scalar.QComplex := ((-843641132919013597267442 : Int)/10^30,(-431476691571314193147832382 : Int)/10^30)
theorem v3003_mb_checked : Scalar.distance (sourceCoefficient 38 59 3 1) v3003_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3003_mg : Scalar.QComplex := ((-93086251460556947973208 : Int)/10^30,(182006101778938919701 : Int)/10^30)
theorem v3003_mg_checked : Scalar.distance (sourceCoefficient 38 59 3 2) v3003_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3003_upper : Scalar.QComplex := ((999996028893704702434971130119 : Int)/10^30,(-2818190345045898688363065779 : Int)/10^30)
theorem v3003_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 59 5) 1) 14) v3003_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3003 : Material (38 : Basis) (59 : Basis) where
  plus := ![v3003_pa,v3003_pb,v3003_pg]
  minus := ![(Primitive.Addresses.material3003 1).one,v3003_mb,v3003_mg]
  upper := v3003_upper
  lower := (Primitive.Addresses.material3003 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3003_pa_checked.trans (by decide +kernel)
    · exact v3003_pb_checked.trans (by decide +kernel)
    · exact v3003_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 59 Primitive.Addresses.material3003
    · exact v3003_mb_checked.trans (by decide +kernel)
    · exact v3003_mg_checked.trans (by decide +kernel)
  upper_error := v3003_upper_checked
  lower_error := reuse_lower_error 38 59 Primitive.Addresses.material3003

def v3004_pa : Scalar.QComplex := ((999999381118684383356870523447 : Int)/10^30,(-1112547638629107620814652844 : Int)/10^30)
theorem v3004_pa_checked : Scalar.distance (sourceCoefficient 38 60 1 0) v3004_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3004_pb : Scalar.QComplex := ((-480039291057214329760555 : Int)/10^30,(-431477248526072289710968190 : Int)/10^30)
theorem v3004_pb_checked : Scalar.distance (sourceCoefficient 38 60 1 1) v3004_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3004_pg : Scalar.QComplex := ((-93086371700584466707592 : Int)/10^30,(103563087117296241959 : Int)/10^30)
theorem v3004_pg_checked : Scalar.distance (sourceCoefficient 38 60 1 2) v3004_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3004_mb : Scalar.QComplex := ((-852384544780761546046887 : Int)/10^30,(-431476673615085163749240525 : Int)/10^30)
theorem v3004_mb_checked : Scalar.distance (sourceCoefficient 38 60 3 1) v3004_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3004_mg : Scalar.QComplex := ((-93086247669994151298544 : Int)/10^30,(183892394879080070146 : Int)/10^30)
theorem v3004_mg_checked : Scalar.distance (sourceCoefficient 38 60 3 2) v3004_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3004_upper : Scalar.QComplex := ((999995971580779645590628874242 : Int)/10^30,(-2838454194195742842659689644 : Int)/10^30)
theorem v3004_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 60 5) 1) 14) v3004_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3004 : Material (38 : Basis) (60 : Basis) where
  plus := ![v3004_pa,v3004_pb,v3004_pg]
  minus := ![(Primitive.Addresses.material3004 1).one,v3004_mb,v3004_mg]
  upper := v3004_upper
  lower := (Primitive.Addresses.material3004 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3004_pa_checked.trans (by decide +kernel)
    · exact v3004_pb_checked.trans (by decide +kernel)
    · exact v3004_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 60 Primitive.Addresses.material3004
    · exact v3004_mb_checked.trans (by decide +kernel)
    · exact v3004_mg_checked.trans (by decide +kernel)
  upper_error := v3004_upper_checked
  lower_error := reuse_lower_error 38 60 Primitive.Addresses.material3004

def v3005_pa : Scalar.QComplex := ((999999374582728516873419350182 : Int)/10^30,(-1118406970569966401217938347 : Int)/10^30)
theorem v3005_pa_checked : Scalar.distance (sourceCoefficient 38 61 1 0) v3005_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3005_pb : Scalar.QComplex := ((-482567460783876617913097 : Int)/10^30,(-431477245471676964881016101 : Int)/10^30)
theorem v3005_pb_checked : Scalar.distance (sourceCoefficient 38 61 1 1) v3005_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3005_pg : Scalar.QComplex := ((-93086371066904322026890 : Int)/10^30,(104108511377549357914 : Int)/10^30)
theorem v3005_pg_checked : Scalar.distance (sourceCoefficient 38 61 1 2) v3005_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3005_mb : Scalar.QComplex := ((-854912710930265101429142 : Int)/10^30,(-431476668378994366638344505 : Int)/10^30)
theorem v3005_mb_checked : Scalar.distance (sourceCoefficient 38 61 3 1) v3005_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3005_mg : Scalar.QComplex := ((-93086246565637670964268 : Int)/10^30,(184437818389409381924 : Int)/10^30)
theorem v3005_mg_checked : Scalar.distance (sourceCoefficient 38 61 3 2) v3005_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3005_upper : Scalar.QComplex := ((999995954932158138164817825760 : Int)/10^30,(-2844313506129348094367011644 : Int)/10^30)
theorem v3005_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 61 5) 1) 14) v3005_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3005 : Material (38 : Basis) (61 : Basis) where
  plus := ![v3005_pa,v3005_pb,v3005_pg]
  minus := ![(Primitive.Addresses.material3005 1).one,v3005_mb,v3005_mg]
  upper := v3005_upper
  lower := (Primitive.Addresses.material3005 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3005_pa_checked.trans (by decide +kernel)
    · exact v3005_pb_checked.trans (by decide +kernel)
    · exact v3005_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 61 Primitive.Addresses.material3005
    · exact v3005_mb_checked.trans (by decide +kernel)
    · exact v3005_mg_checked.trans (by decide +kernel)
  upper_error := v3005_upper_checked
  lower_error := reuse_lower_error 38 61 Primitive.Addresses.material3005

def v3006_pa : Scalar.QComplex := ((999999365025085068929975705692 : Int)/10^30,(-1126920328447844380649257803 : Int)/10^30)
theorem v3006_pa_checked : Scalar.distance (sourceCoefficient 38 62 1 0) v3006_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3006_pb : Scalar.QComplex := ((-486240782894583099926067 : Int)/10^30,(-431477240998574557315126958 : Int)/10^30)
theorem v3006_pb_checked : Scalar.distance (sourceCoefficient 38 62 1 1) v3006_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3006_pg : Scalar.QComplex := ((-93086370139550061919492 : Int)/10^30,(104900989421176203229 : Int)/10^30)
theorem v3006_pg_checked : Scalar.distance (sourceCoefficient 38 62 1 2) v3006_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3006_mb : Scalar.QComplex := ((-858586027813139965836722 : Int)/10^30,(-431476660735982083359652707 : Int)/10^30)
theorem v3006_mb_checked : Scalar.distance (sourceCoefficient 38 62 3 1) v3006_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3006_mg : Scalar.QComplex := ((-93086244954410896389416 : Int)/10^30,(185230295337695473574 : Int)/10^30)
theorem v3006_mg_checked : Scalar.distance (sourceCoefficient 38 62 3 2) v3006_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3006_upper : Scalar.QComplex := ((999995930681245553784780804704 : Int)/10^30,(-2852826834831954035455137749 : Int)/10^30)
theorem v3006_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 62 5) 1) 14) v3006_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3006 : Material (38 : Basis) (62 : Basis) where
  plus := ![v3006_pa,v3006_pb,v3006_pg]
  minus := ![(Primitive.Addresses.material3006 1).one,v3006_mb,v3006_mg]
  upper := v3006_upper
  lower := (Primitive.Addresses.material3006 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3006_pa_checked.trans (by decide +kernel)
    · exact v3006_pb_checked.trans (by decide +kernel)
    · exact v3006_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 62 Primitive.Addresses.material3006
    · exact v3006_mb_checked.trans (by decide +kernel)
    · exact v3006_mg_checked.trans (by decide +kernel)
  upper_error := v3006_upper_checked
  lower_error := reuse_lower_error 38 62 Primitive.Addresses.material3006

def v3007_pa : Scalar.QComplex := ((999999336775499511229951417224 : Int)/10^30,(-1151715486181722768184600828 : Int)/10^30)
theorem v3007_pa_checked : Scalar.distance (sourceCoefficient 38 63 1 0) v3007_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3007_pb : Scalar.QComplex := ((-496939334697303479712552 : Int)/10^30,(-431477227733093289013448218 : Int)/10^30)
theorem v3007_pb_checked : Scalar.distance (sourceCoefficient 38 63 1 1) v3007_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3007_pg : Scalar.QComplex := ((-93086367393784220097021 : Int)/10^30,(107209081983512505166 : Int)/10^30)
theorem v3007_pg_checked : Scalar.distance (sourceCoefficient 38 63 1 2) v3007_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3007_mb : Scalar.QComplex := ((-869284564184787682051904 : Int)/10^30,(-431476638238137393541496410 : Int)/10^30)
theorem v3007_mb_checked : Scalar.distance (sourceCoefficient 38 63 3 1) v3007_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3007_mg : Scalar.QComplex := ((-93086240216866148274932 : Int)/10^30,(187538384671151172721 : Int)/10^30)
theorem v3007_mg_checked : Scalar.distance (sourceCoefficient 38 63 3 2) v3007_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3007_upper : Scalar.QComplex := ((999995859637509220988194063936 : Int)/10^30,(-2877621906880135732000308900 : Int)/10^30)
theorem v3007_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 63 5) 1) 14) v3007_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3007 : Material (38 : Basis) (63 : Basis) where
  plus := ![v3007_pa,v3007_pb,v3007_pg]
  minus := ![(Primitive.Addresses.material3007 1).one,v3007_mb,v3007_mg]
  upper := v3007_upper
  lower := (Primitive.Addresses.material3007 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3007_pa_checked.trans (by decide +kernel)
    · exact v3007_pb_checked.trans (by decide +kernel)
    · exact v3007_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 63 Primitive.Addresses.material3007
    · exact v3007_mb_checked.trans (by decide +kernel)
    · exact v3007_mg_checked.trans (by decide +kernel)
  upper_error := v3007_upper_checked
  lower_error := reuse_lower_error 38 63 Primitive.Addresses.material3007

def v3008_pa : Scalar.QComplex := ((999999295333945508133237769206 : Int)/10^30,(-1187152733404377573110270719 : Int)/10^30)
theorem v3008_pa_checked : Scalar.distance (sourceCoefficient 38 64 1 0) v3008_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3008_pb : Scalar.QComplex := ((-512229708019813873161804 : Int)/10^30,(-431477208160078272784865412 : Int)/10^30)
theorem v3008_pb_checked : Scalar.distance (sourceCoefficient 38 64 1 1) v3008_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3008_pg : Scalar.QComplex := ((-93086363353631967662353 : Int)/10^30,(110507808569038728476 : Int)/10^30)
theorem v3008_pg_checked : Scalar.distance (sourceCoefficient 38 64 1 2) v3008_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3008_mb : Scalar.QComplex := ((-884574914923362859814966 : Int)/10^30,(-431476605470226140764915989 : Int)/10^30)
theorem v3008_mb_checked : Scalar.distance (sourceCoefficient 38 64 3 1) v3008_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3008_mg : Scalar.QComplex := ((-93086233330062925994727 : Int)/10^30,(190837106541941296839 : Int)/10^30)
theorem v3008_mg_checked : Scalar.distance (sourceCoefficient 38 64 3 2) v3008_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3008_upper : Scalar.QComplex := ((999995757034543075870979880632 : Int)/10^30,(-2913059029798810889324014865 : Int)/10^30)
theorem v3008_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 64 5) 1) 14) v3008_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3008 : Material (38 : Basis) (64 : Basis) where
  plus := ![v3008_pa,v3008_pb,v3008_pg]
  minus := ![(Primitive.Addresses.material3008 1).one,v3008_mb,v3008_mg]
  upper := v3008_upper
  lower := (Primitive.Addresses.material3008 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3008_pa_checked.trans (by decide +kernel)
    · exact v3008_pb_checked.trans (by decide +kernel)
    · exact v3008_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 64 Primitive.Addresses.material3008
    · exact v3008_mb_checked.trans (by decide +kernel)
    · exact v3008_mg_checked.trans (by decide +kernel)
  upper_error := v3008_upper_checked
  lower_error := reuse_lower_error 38 64 Primitive.Addresses.material3008

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
