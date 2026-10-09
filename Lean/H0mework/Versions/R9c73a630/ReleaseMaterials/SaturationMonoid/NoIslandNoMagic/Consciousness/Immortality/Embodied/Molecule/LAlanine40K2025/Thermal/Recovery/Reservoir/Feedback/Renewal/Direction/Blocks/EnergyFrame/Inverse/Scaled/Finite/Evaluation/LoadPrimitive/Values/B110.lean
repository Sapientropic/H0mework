import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B073
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B074

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1761_pa : Scalar.QComplex := ((999999918494447439865725950447 : Int)/10^30,(-403746329366736720015849800 : Int)/10^30)
theorem v1761_pa_checked : Scalar.distance (sourceCoefficient 20 32 1 0) v1761_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1761_pb : Scalar.QComplex := ((-174207464230340848555502 : Int)/10^30,(-431477483163014912330871616 : Int)/10^30)
theorem v1761_pb_checked : Scalar.distance (sourceCoefficient 20 32 1 1) v1761_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1761_pg : Scalar.QComplex := ((-93086422021922875044150 : Int)/10^30,(37583304268482308849 : Int)/10^30)
theorem v1761_pg_checked : Scalar.distance (sourceCoefficient 20 32 1 2) v1761_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1761_mb : Scalar.QComplex := ((-546553034310168225175824 : Int)/10^30,(-431477172171032817744136664 : Int)/10^30)
theorem v1761_mb_checked : Scalar.distance (sourceCoefficient 20 32 3 1) v1761_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1761_mg : Scalar.QComplex := ((-93086354928894802119614 : Int)/10^30,(117912680022603374136 : Int)/10^30)
theorem v1761_mg_checked : Scalar.distance (sourceCoefficient 20 32 3 2) v1761_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1761_upper : Scalar.QComplex := ((999997732282500178400182884714 : Int)/10^30,(-2129654868071477124691054772 : Int)/10^30)
theorem v1761_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 32 5) 1) 14) v1761_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1761 : Material (20 : Basis) (32 : Basis) where
  plus := ![v1761_pa,v1761_pb,v1761_pg]
  minus := ![(Primitive.Addresses.material1761 1).one,v1761_mb,v1761_mg]
  upper := v1761_upper
  lower := (Primitive.Addresses.material1761 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1761_pa_checked.trans (by decide +kernel)
    · exact v1761_pb_checked.trans (by decide +kernel)
    · exact v1761_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 32 Primitive.Addresses.material1761
    · exact v1761_mb_checked.trans (by decide +kernel)
    · exact v1761_mg_checked.trans (by decide +kernel)
  upper_error := v1761_upper_checked
  lower_error := reuse_lower_error 20 32 Primitive.Addresses.material1761

def v1762_pa : Scalar.QComplex := ((999999915784912446444411862370 : Int)/10^30,(-410402446404660464010094821 : Int)/10^30)
theorem v1762_pa_checked : Scalar.distance (sourceCoefficient 20 33 1 0) v1762_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1762_pb : Scalar.QComplex := ((-177079429014574463597208 : Int)/10^30,(-431477481806268199492056875 : Int)/10^30)
theorem v1762_pb_checked : Scalar.distance (sourceCoefficient 20 33 1 1) v1762_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1762_pg : Scalar.QComplex := ((-93086421749460971715343 : Int)/10^30,(38202898430295212699 : Int)/10^30)
theorem v1762_pg_checked : Scalar.distance (sourceCoefficient 20 33 1 2) v1762_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1762_mb : Scalar.QComplex := ((-549424996854226788196276 : Int)/10^30,(-431477168335910349782759866 : Int)/10^30)
theorem v1762_mb_checked : Scalar.distance (sourceCoefficient 20 33 3 1) v1762_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1762_mg : Scalar.QComplex := ((-93086354121751144081438 : Int)/10^30,(118532273718590703346 : Int)/10^30)
theorem v1762_mg_checked : Scalar.distance (sourceCoefficient 20 33 3 2) v1762_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1762_upper : Scalar.QComplex := ((999997718085115051277330143825 : Int)/10^30,(-2136310970519484831578678219 : Int)/10^30)
theorem v1762_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 33 5) 1) 14) v1762_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1762 : Material (20 : Basis) (33 : Basis) where
  plus := ![v1762_pa,v1762_pb,v1762_pg]
  minus := ![(Primitive.Addresses.material1762 1).one,v1762_mb,v1762_mg]
  upper := v1762_upper
  lower := (Primitive.Addresses.material1762 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1762_pa_checked.trans (by decide +kernel)
    · exact v1762_pb_checked.trans (by decide +kernel)
    · exact v1762_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 33 Primitive.Addresses.material1762
    · exact v1762_mb_checked.trans (by decide +kernel)
    · exact v1762_mg_checked.trans (by decide +kernel)
  upper_error := v1762_upper_checked
  lower_error := reuse_lower_error 20 33 Primitive.Addresses.material1762

def v1763_pa : Scalar.QComplex := ((999999909019264997085717972970 : Int)/10^30,(-426569410211672846323816315 : Int)/10^30)
theorem v1763_pa_checked : Scalar.distance (sourceCoefficient 20 34 1 0) v1763_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1763_pb : Scalar.QComplex := ((-184055110228200865246363 : Int)/10^30,(-431477478404744469753907124 : Int)/10^30)
theorem v1763_pb_checked : Scalar.distance (sourceCoefficient 20 34 1 1) v1763_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1763_pg : Scalar.QComplex := ((-93086421067645714912986 : Int)/10^30,(39707823346188023803 : Int)/10^30)
theorem v1763_pg_checked : Scalar.distance (sourceCoefficient 20 34 1 2) v1763_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1763_mb : Scalar.QComplex := ((-556400672535126489809356 : Int)/10^30,(-431477158914689172246978440 : Int)/10^30)
theorem v1763_mb_checked : Scalar.distance (sourceCoefficient 20 34 3 1) v1763_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1763_mg : Scalar.QComplex := ((-93086352141253718036692 : Int)/10^30,(120037197485755330996 : Int)/10^30)
theorem v1763_mg_checked : Scalar.distance (sourceCoefficient 20 34 3 2) v1763_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1763_upper : Scalar.QComplex := ((999997683416764803152079558382 : Int)/10^30,(-2152477898570810005470031229 : Int)/10^30)
theorem v1763_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 34 5) 1) 14) v1763_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1763 : Material (20 : Basis) (34 : Basis) where
  plus := ![v1763_pa,v1763_pb,v1763_pg]
  minus := ![(Primitive.Addresses.material1763 1).one,v1763_mb,v1763_mg]
  upper := v1763_upper
  lower := (Primitive.Addresses.material1763 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1763_pa_checked.trans (by decide +kernel)
    · exact v1763_pb_checked.trans (by decide +kernel)
    · exact v1763_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 34 Primitive.Addresses.material1763
    · exact v1763_mb_checked.trans (by decide +kernel)
    · exact v1763_mg_checked.trans (by decide +kernel)
  upper_error := v1763_upper_checked
  lower_error := reuse_lower_error 20 34 Primitive.Addresses.material1763

def v1764_pa : Scalar.QComplex := ((999999885790729807016666065555 : Int)/10^30,(-477931509049371288525549274 : Int)/10^30)
theorem v1764_pa_checked : Scalar.distance (sourceCoefficient 20 35 1 0) v1764_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1764_pb : Scalar.QComplex := ((-206216700285023564300922 : Int)/10^30,(-431477466600475016279784472 : Int)/10^30)
theorem v1764_pb_checked : Scalar.distance (sourceCoefficient 20 35 1 1) v1764_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1764_pg : Scalar.QComplex := ((-93086418713195720518661 : Int)/10^30,(44488937648648365869 : Int)/10^30)
theorem v1764_pg_checked : Scalar.distance (sourceCoefficient 20 35 1 2) v1764_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1764_mb : Scalar.QComplex := ((-578562244153623482220620 : Int)/10^30,(-431477127985970015968033258 : Int)/10^30)
theorem v1764_mb_checked : Scalar.distance (sourceCoefficient 20 35 3 1) v1764_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1764_mg : Scalar.QComplex := ((-93086345660918290683059 : Int)/10^30,(124818307976204005867 : Int)/10^30)
theorem v1764_mg_checked : Scalar.distance (sourceCoefficient 20 35 3 2) v1764_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1764_upper : Scalar.QComplex := ((999997571541941148598346658844 : Int)/10^30,(-2203839880820351183065886092 : Int)/10^30)
theorem v1764_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 35 5) 1) 14) v1764_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1764 : Material (20 : Basis) (35 : Basis) where
  plus := ![v1764_pa,v1764_pb,v1764_pg]
  minus := ![(Primitive.Addresses.material1764 1).one,v1764_mb,v1764_mg]
  upper := v1764_upper
  lower := (Primitive.Addresses.material1764 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1764_pa_checked.trans (by decide +kernel)
    · exact v1764_pb_checked.trans (by decide +kernel)
    · exact v1764_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 35 Primitive.Addresses.material1764
    · exact v1764_mb_checked.trans (by decide +kernel)
    · exact v1764_mg_checked.trans (by decide +kernel)
  upper_error := v1764_upper_checked
  lower_error := reuse_lower_error 20 35 Primitive.Addresses.material1764

def v1765_pa : Scalar.QComplex := ((999999877944232483581279412728 : Int)/10^30,(-494076431471110608320580471 : Int)/10^30)
theorem v1765_pa_checked : Scalar.distance (sourceCoefficient 20 36 1 0) v1765_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1765_pb : Scalar.QComplex := ((-213182870990188773463392 : Int)/10^30,(-431477462576465671424036358 : Int)/10^30)
theorem v1765_pb_checked : Scalar.distance (sourceCoefficient 20 36 1 1) v1765_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1765_pg : Scalar.QComplex := ((-93086417913927095115303 : Int)/10^30,(45991810794907329361 : Int)/10^30)
theorem v1765_pg_checked : Scalar.distance (sourceCoefficient 20 36 1 2) v1765_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1765_mb : Scalar.QComplex := ((-585528408792426138163708 : Int)/10^30,(-431477117950470595559105631 : Int)/10^30)
theorem v1765_mb_checked : Scalar.distance (sourceCoefficient 20 36 3 1) v1765_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1765_mg : Scalar.QComplex := ((-93086343564738124556306 : Int)/10^30,(126321179873141786310 : Int)/10^30)
theorem v1765_mg_checked : Scalar.distance (sourceCoefficient 20 36 3 2) v1765_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1765_upper : Scalar.QComplex := ((999997535830784067597778989983 : Int)/10^30,(-2219984765653782519918031697 : Int)/10^30)
theorem v1765_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 36 5) 1) 14) v1765_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1765 : Material (20 : Basis) (36 : Basis) where
  plus := ![v1765_pa,v1765_pb,v1765_pg]
  minus := ![(Primitive.Addresses.material1765 1).one,v1765_mb,v1765_mg]
  upper := v1765_upper
  lower := (Primitive.Addresses.material1765 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1765_pa_checked.trans (by decide +kernel)
    · exact v1765_pb_checked.trans (by decide +kernel)
    · exact v1765_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 36 Primitive.Addresses.material1765
    · exact v1765_mb_checked.trans (by decide +kernel)
    · exact v1765_mg_checked.trans (by decide +kernel)
  upper_error := v1765_upper_checked
  lower_error := reuse_lower_error 20 36 Primitive.Addresses.material1765

def v1766_pa : Scalar.QComplex := ((999999874514277480373558408468 : Int)/10^30,(-500970487446702120509185003 : Int)/10^30)
theorem v1766_pa_checked : Scalar.distance (sourceCoefficient 20 37 1 0) v1766_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1766_pb : Scalar.QComplex := ((-216157500990174600832497 : Int)/10^30,(-431477460812481982290334798 : Int)/10^30)
theorem v1766_pb_checked : Scalar.distance (sourceCoefficient 20 37 1 1) v1766_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1766_pg : Scalar.QComplex := ((-93086417564006126164268 : Int)/10^30,(46633553833552599273 : Int)/10^30)
theorem v1766_pg_checked : Scalar.distance (sourceCoefficient 20 37 1 2) v1766_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1766_mb : Scalar.QComplex := ((-588503036162582792384924 : Int)/10^30,(-431477113619515845611292069 : Int)/10^30)
theorem v1766_mb_checked : Scalar.distance (sourceCoefficient 20 37 3 1) v1766_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1766_mg : Scalar.QComplex := ((-93086342661021946579501 : Int)/10^30,(126962922370870757480 : Int)/10^30)
theorem v1766_mg_checked : Scalar.distance (sourceCoefficient 20 37 3 2) v1766_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1766_upper : Scalar.QComplex := ((999997520502318982906736888751 : Int)/10^30,(-2226878805441696316716308325 : Int)/10^30)
theorem v1766_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 37 5) 1) 14) v1766_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1766 : Material (20 : Basis) (37 : Basis) where
  plus := ![v1766_pa,v1766_pb,v1766_pg]
  minus := ![(Primitive.Addresses.material1766 1).one,v1766_mb,v1766_mg]
  upper := v1766_upper
  lower := (Primitive.Addresses.material1766 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1766_pa_checked.trans (by decide +kernel)
    · exact v1766_pb_checked.trans (by decide +kernel)
    · exact v1766_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 37 Primitive.Addresses.material1766
    · exact v1766_mb_checked.trans (by decide +kernel)
    · exact v1766_mg_checked.trans (by decide +kernel)
  upper_error := v1766_upper_checked
  lower_error := reuse_lower_error 20 37 Primitive.Addresses.material1766

def v1767_pa : Scalar.QComplex := ((999999862569687493355670537982 : Int)/10^30,(-524271500394783869707071392 : Int)/10^30)
theorem v1767_pa_checked : Scalar.distance (sourceCoefficient 20 38 1 0) v1767_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1767_pb : Scalar.QComplex := ((-226211363623159988843467 : Int)/10^30,(-431477454648061651875250246 : Int)/10^30)
theorem v1767_pb_checked : Scalar.distance (sourceCoefficient 20 38 1 1) v1767_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1767_pg : Scalar.QComplex := ((-93086416343114276018370 : Int)/10^30,(48802561869529380675 : Int)/10^30)
theorem v1767_pg_checked : Scalar.distance (sourceCoefficient 20 38 1 2) v1767_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1767_mb : Scalar.QComplex := ((-598556889732438527951287 : Int)/10^30,(-431477098779067167389157983 : Int)/10^30)
theorem v1767_mb_checked : Scalar.distance (sourceCoefficient 20 38 3 1) v1767_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1767_mg : Scalar.QComplex := ((-93086339568374304475046 : Int)/10^30,(129131928545652038775 : Int)/10^30)
theorem v1767_mg_checked : Scalar.distance (sourceCoefficient 20 38 3 2) v1767_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1767_upper : Scalar.QComplex := ((999997468342312288945574621290 : Int)/10^30,(-2250179763070377696146246298 : Int)/10^30)
theorem v1767_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 38 5) 1) 14) v1767_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1767 : Material (20 : Basis) (38 : Basis) where
  plus := ![v1767_pa,v1767_pb,v1767_pg]
  minus := ![(Primitive.Addresses.material1767 1).one,v1767_mb,v1767_mg]
  upper := v1767_upper
  lower := (Primitive.Addresses.material1767 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1767_pa_checked.trans (by decide +kernel)
    · exact v1767_pb_checked.trans (by decide +kernel)
    · exact v1767_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 38 Primitive.Addresses.material1767
    · exact v1767_mb_checked.trans (by decide +kernel)
    · exact v1767_mg_checked.trans (by decide +kernel)
  upper_error := v1767_upper_checked
  lower_error := reuse_lower_error 20 38 Primitive.Addresses.material1767

def v1768_pa : Scalar.QComplex := ((999999855391543267489072867685 : Int)/10^30,(-537788892181138393309669023 : Int)/10^30)
theorem v1768_pa_checked : Scalar.distance (sourceCoefficient 20 39 1 0) v1768_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1768_pb : Scalar.QComplex := ((-232043813891635939808643 : Int)/10^30,(-431477450928794911596269032 : Int)/10^30)
theorem v1768_pb_checked : Scalar.distance (sourceCoefficient 20 39 1 1) v1768_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1768_pg : Scalar.QComplex := ((-93086415607825349846299 : Int)/10^30,(50060847566067334436 : Int)/10^30)
theorem v1768_pg_checked : Scalar.distance (sourceCoefficient 20 39 1 2) v1768_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1768_mb : Scalar.QComplex := ((-604389334619667000512431 : Int)/10^30,(-431477090026659914077228191 : Int)/10^30)
theorem v1768_mb_checked : Scalar.distance (sourceCoefficient 20 39 3 1) v1768_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1768_mg : Scalar.QComplex := ((-93086337747241767056436 : Int)/10^30,(130390213139151494115 : Int)/10^30)
theorem v1768_mg_checked : Scalar.distance (sourceCoefficient 20 39 3 2) v1768_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1768_upper : Scalar.QComplex := ((999997437834386819037309917439 : Int)/10^30,(-2263697122335339280665953147 : Int)/10^30)
theorem v1768_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 39 5) 1) 14) v1768_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1768 : Material (20 : Basis) (39 : Basis) where
  plus := ![v1768_pa,v1768_pb,v1768_pg]
  minus := ![(Primitive.Addresses.material1768 1).one,v1768_mb,v1768_mg]
  upper := v1768_upper
  lower := (Primitive.Addresses.material1768 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1768_pa_checked.trans (by decide +kernel)
    · exact v1768_pb_checked.trans (by decide +kernel)
    · exact v1768_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 39 Primitive.Addresses.material1768
    · exact v1768_mb_checked.trans (by decide +kernel)
    · exact v1768_mg_checked.trans (by decide +kernel)
  upper_error := v1768_upper_checked
  lower_error := reuse_lower_error 20 39 Primitive.Addresses.material1768

def v1769_pa : Scalar.QComplex := ((999999842906193225312016518574 : Int)/10^30,(-560524387400683789373912943 : Int)/10^30)
theorem v1769_pa_checked : Scalar.distance (sourceCoefficient 20 40 1 0) v1769_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1769_pb : Scalar.QComplex := ((-241853668213474484006852 : Int)/10^30,(-431477444436106299981134741 : Int)/10^30)
theorem v1769_pb_checked : Scalar.distance (sourceCoefficient 20 40 1 1) v1769_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1769_pg : Scalar.QComplex := ((-93086414326354690492006 : Int)/10^30,(52177213562323303465 : Int)/10^30)
theorem v1769_pg_checked : Scalar.distance (sourceCoefficient 20 40 1 2) v1769_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1769_mb : Scalar.QComplex := ((-614199179685950596215640 : Int)/10^30,(-431477075068511259677678035 : Int)/10^30)
theorem v1769_mb_checked : Scalar.distance (sourceCoefficient 20 40 3 1) v1769_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1769_mg : Scalar.QComplex := ((-93086334639443047669451 : Int)/10^30,(132506577241536216307 : Int)/10^30)
theorem v1769_mg_checked : Scalar.distance (sourceCoefficient 20 40 3 2) v1769_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1769_upper : Scalar.QComplex := ((999997386109653171401731797801 : Int)/10^30,(-2286432562144453735402537274 : Int)/10^30)
theorem v1769_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 40 5) 1) 14) v1769_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1769 : Material (20 : Basis) (40 : Basis) where
  plus := ![v1769_pa,v1769_pb,v1769_pg]
  minus := ![(Primitive.Addresses.material1769 1).one,v1769_mb,v1769_mg]
  upper := v1769_upper
  lower := (Primitive.Addresses.material1769 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1769_pa_checked.trans (by decide +kernel)
    · exact v1769_pb_checked.trans (by decide +kernel)
    · exact v1769_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 40 Primitive.Addresses.material1769
    · exact v1769_mb_checked.trans (by decide +kernel)
    · exact v1769_mg_checked.trans (by decide +kernel)
  upper_error := v1769_upper_checked
  lower_error := reuse_lower_error 20 40 Primitive.Addresses.material1769

def v1770_pa : Scalar.QComplex := ((999999834682668131303256413519 : Int)/10^30,(-575008379423790024291582626 : Int)/10^30)
theorem v1770_pa_checked : Scalar.distance (sourceCoefficient 20 41 1 0) v1770_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1770_pb : Scalar.QComplex := ((-248103184631326813596924 : Int)/10^30,(-431477440144771294505092475 : Int)/10^30)
theorem v1770_pb_checked : Scalar.distance (sourceCoefficient 20 41 1 1) v1770_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1770_pg : Scalar.QComplex := ((-93086413480701725781755 : Int)/10^30,(53525476610600120819 : Int)/10^30)
theorem v1770_pg_checked : Scalar.distance (sourceCoefficient 20 41 1 2) v1770_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1770_mb : Scalar.QComplex := ((-620448690073593511257360 : Int)/10^30,(-431477065384126651226106844 : Int)/10^30)
theorem v1770_mb_checked : Scalar.distance (sourceCoefficient 20 41 3 1) v1770_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1770_mg : Scalar.QComplex := ((-93086332630300110685084 : Int)/10^30,(133854839058032660373 : Int)/10^30)
theorem v1770_mg_checked : Scalar.distance (sourceCoefficient 20 41 3 2) v1770_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1770_upper : Scalar.QComplex := ((999997352888084070978341948994 : Int)/10^30,(-2300916518402296981233706668 : Int)/10^30)
theorem v1770_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 41 5) 1) 14) v1770_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1770 : Material (20 : Basis) (41 : Basis) where
  plus := ![v1770_pa,v1770_pb,v1770_pg]
  minus := ![(Primitive.Addresses.material1770 1).one,v1770_mb,v1770_mg]
  upper := v1770_upper
  lower := (Primitive.Addresses.material1770 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1770_pa_checked.trans (by decide +kernel)
    · exact v1770_pb_checked.trans (by decide +kernel)
    · exact v1770_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 41 Primitive.Addresses.material1770
    · exact v1770_mb_checked.trans (by decide +kernel)
    · exact v1770_mg_checked.trans (by decide +kernel)
  upper_error := v1770_upper_checked
  lower_error := reuse_lower_error 20 41 Primitive.Addresses.material1770

def v1771_pa : Scalar.QComplex := ((999999827896217684210493856915 : Int)/10^30,(-586692027397566674046048731 : Int)/10^30)
theorem v1771_pa_checked : Scalar.distance (sourceCoefficient 20 42 1 0) v1771_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1771_pb : Scalar.QComplex := ((-253144415619443105507198 : Int)/10^30,(-431477436595180891878314630 : Int)/10^30)
theorem v1771_pb_checked : Scalar.distance (sourceCoefficient 20 42 1 1) v1771_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1771_pg : Scalar.QComplex := ((-93086412781946369509498 : Int)/10^30,(54613065637322040105 : Int)/10^30)
theorem v1771_pg_checked : Scalar.distance (sourceCoefficient 20 42 1 2) v1771_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1771_mb : Scalar.QComplex := ((-625489916121492460804267 : Int)/10^30,(-431477057484182276144964250 : Int)/10^30)
theorem v1771_mb_checked : Scalar.distance (sourceCoefficient 20 42 3 1) v1771_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1771_mg : Scalar.QComplex := ((-93086330993004667721787 : Int)/10^30,(134942427076801078046 : Int)/10^30)
theorem v1771_mg_checked : Scalar.distance (sourceCoefficient 20 42 3 2) v1771_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1771_upper : Scalar.QComplex := ((999997325936727261032274938061 : Int)/10^30,(-2312600137261854622041912575 : Int)/10^30)
theorem v1771_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 42 5) 1) 14) v1771_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1771 : Material (20 : Basis) (42 : Basis) where
  plus := ![v1771_pa,v1771_pb,v1771_pg]
  minus := ![(Primitive.Addresses.material1771 1).one,v1771_mb,v1771_mg]
  upper := v1771_upper
  lower := (Primitive.Addresses.material1771 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1771_pa_checked.trans (by decide +kernel)
    · exact v1771_pb_checked.trans (by decide +kernel)
    · exact v1771_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 42 Primitive.Addresses.material1771
    · exact v1771_mb_checked.trans (by decide +kernel)
    · exact v1771_mg_checked.trans (by decide +kernel)
  upper_error := v1771_upper_checked
  lower_error := reuse_lower_error 20 42 Primitive.Addresses.material1771

def v1772_pa : Scalar.QComplex := ((999999818695741624063813834224 : Int)/10^30,(-602169813159575666123486420 : Int)/10^30)
theorem v1772_pa_checked : Scalar.distance (sourceCoefficient 20 43 1 0) v1772_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1772_pb : Scalar.QComplex := ((-259822731579669039353301 : Int)/10^30,(-431477431771971077698655341 : Int)/10^30)
theorem v1772_pb_checked : Scalar.distance (sourceCoefficient 20 43 1 1) v1772_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1772_pg : Scalar.QComplex := ((-93086411833449957332017 : Int)/10^30,(56053837384243290202 : Int)/10^30)
theorem v1772_pg_checked : Scalar.distance (sourceCoefficient 20 43 1 2) v1772_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1772_mb : Scalar.QComplex := ((-632168225432863308210042 : Int)/10^30,(-431477046897888364377132707 : Int)/10^30)
theorem v1772_mb_checked : Scalar.distance (sourceCoefficient 20 43 3 1) v1772_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1772_mg : Scalar.QComplex := ((-93086328801187481070483 : Int)/10^30,(136383197468747475227 : Int)/10^30)
theorem v1772_mg_checked : Scalar.distance (sourceCoefficient 20 43 3 2) v1772_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1772_upper : Scalar.QComplex := ((999997290023010812442240828938 : Int)/10^30,(-2328077884092332850895519128 : Int)/10^30)
theorem v1772_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 43 5) 1) 14) v1772_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1772 : Material (20 : Basis) (43 : Basis) where
  plus := ![v1772_pa,v1772_pb,v1772_pg]
  minus := ![(Primitive.Addresses.material1772 1).one,v1772_mb,v1772_mg]
  upper := v1772_upper
  lower := (Primitive.Addresses.material1772 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1772_pa_checked.trans (by decide +kernel)
    · exact v1772_pb_checked.trans (by decide +kernel)
    · exact v1772_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 43 Primitive.Addresses.material1772
    · exact v1772_mb_checked.trans (by decide +kernel)
    · exact v1772_mg_checked.trans (by decide +kernel)
  upper_error := v1772_upper_checked
  lower_error := reuse_lower_error 20 43 Primitive.Addresses.material1772

def v1773_pa : Scalar.QComplex := ((999999815152422948317427243023 : Int)/10^30,(-608025591513004001482115290 : Int)/10^30)
theorem v1773_pa_checked : Scalar.distance (sourceCoefficient 20 44 1 0) v1773_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1773_pb : Scalar.QComplex := ((-262349368040943671174836 : Int)/10^30,(-431477429911250231690628275 : Int)/10^30)
theorem v1773_pb_checked : Scalar.distance (sourceCoefficient 20 44 1 1) v1773_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1773_pg : Scalar.QComplex := ((-93086411467817700904353 : Int)/10^30,(56598930856717969219 : Int)/10^30)
theorem v1773_pg_checked : Scalar.distance (sourceCoefficient 20 44 1 2) v1773_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1773_mb : Scalar.QComplex := ((-634694859347637426159306 : Int)/10^30,(-431477042856794740602437446 : Int)/10^30)
theorem v1773_mb_checked : Scalar.distance (sourceCoefficient 20 44 3 1) v1773_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1773_mg : Scalar.QComplex := ((-93086327965164244137428 : Int)/10^30,(136928290422734772607 : Int)/10^30)
theorem v1773_mg_checked : Scalar.distance (sourceCoefficient 20 44 3 2) v1773_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1773_upper : Scalar.QComplex := ((999997276373155208097953361545 : Int)/10^30,(-2333933647608820609889122405 : Int)/10^30)
theorem v1773_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 44 5) 1) 14) v1773_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1773 : Material (20 : Basis) (44 : Basis) where
  plus := ![v1773_pa,v1773_pb,v1773_pg]
  minus := ![(Primitive.Addresses.material1773 1).one,v1773_mb,v1773_mg]
  upper := v1773_upper
  lower := (Primitive.Addresses.material1773 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1773_pa_checked.trans (by decide +kernel)
    · exact v1773_pb_checked.trans (by decide +kernel)
    · exact v1773_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 44 Primitive.Addresses.material1773
    · exact v1773_mb_checked.trans (by decide +kernel)
    · exact v1773_mg_checked.trans (by decide +kernel)
  upper_error := v1773_upper_checked
  lower_error := reuse_lower_error 20 44 Primitive.Addresses.material1773

def v1774_pa : Scalar.QComplex := ((999999813376804013436959737613 : Int)/10^30,(-610938914413633337583209632 : Int)/10^30)
theorem v1774_pa_checked : Scalar.distance (sourceCoefficient 20 45 1 0) v1774_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1774_pb : Scalar.QComplex := ((-263606401248977631981959 : Int)/10^30,(-431477428978169655995047760 : Int)/10^30)
theorem v1774_pb_checked : Scalar.distance (sourceCoefficient 20 45 1 1) v1774_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1774_pg : Scalar.QComplex := ((-93086411284523859115590 : Int)/10^30,(56870121670111856699 : Int)/10^30)
theorem v1774_pg_checked : Scalar.distance (sourceCoefficient 20 45 1 2) v1774_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1774_mb : Scalar.QComplex := ((-635951891282413961923552 : Int)/10^30,(-431477040838951468476145336 : Int)/10^30)
theorem v1774_mb_checked : Scalar.distance (sourceCoefficient 20 45 3 1) v1774_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1774_mg : Scalar.QComplex := ((-93086327547845012619245 : Int)/10^30,(137199480976977596013 : Int)/10^30)
theorem v1774_mg_checked : Scalar.distance (sourceCoefficient 20 45 3 2) v1774_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1774_upper : Scalar.QComplex := ((999997269569407885896065461848 : Int)/10^30,(-2336846963105840509738354404 : Int)/10^30)
theorem v1774_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 45 5) 1) 14) v1774_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1774 : Material (20 : Basis) (45 : Basis) where
  plus := ![v1774_pa,v1774_pb,v1774_pg]
  minus := ![(Primitive.Addresses.material1774 1).one,v1774_mb,v1774_mg]
  upper := v1774_upper
  lower := (Primitive.Addresses.material1774 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1774_pa_checked.trans (by decide +kernel)
    · exact v1774_pb_checked.trans (by decide +kernel)
    · exact v1774_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 45 Primitive.Addresses.material1774
    · exact v1774_mb_checked.trans (by decide +kernel)
    · exact v1774_mg_checked.trans (by decide +kernel)
  upper_error := v1774_upper_checked
  lower_error := reuse_lower_error 20 45 Primitive.Addresses.material1774

def v1775_pa : Scalar.QComplex := ((999999803245356812268102075000 : Int)/10^30,(-627303154513887471745619186 : Int)/10^30)
theorem v1775_pa_checked : Scalar.distance (sourceCoefficient 20 46 1 0) v1775_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1775_pb : Scalar.QComplex := ((-270667202209864578567744 : Int)/10^30,(-431477423646278913482491721 : Int)/10^30)
theorem v1775_pb_checked : Scalar.distance (sourceCoefficient 20 46 1 1) v1775_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1775_pg : Scalar.QComplex := ((-93086410237825957955816 : Int)/10^30,(58393410273736656464 : Int)/10^30)
theorem v1775_pg_checked : Scalar.distance (sourceCoefficient 20 46 1 2) v1775_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1775_mb : Scalar.QComplex := ((-643012685013060444882091 : Int)/10^30,(-431477029413909488695073125 : Int)/10^30)
theorem v1775_mb_checked : Scalar.distance (sourceCoefficient 20 46 3 1) v1775_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1775_mg : Scalar.QComplex := ((-93086325186618042636653 : Int)/10^30,(138722768110159283742 : Int)/10^30)
theorem v1775_mg_checked : Scalar.distance (sourceCoefficient 20 46 3 2) v1775_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1775_upper : Scalar.QComplex := ((999997231194781913554264152774 : Int)/10^30,(-2353211161347522541740007173 : Int)/10^30)
theorem v1775_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 46 5) 1) 14) v1775_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1775 : Material (20 : Basis) (46 : Basis) where
  plus := ![v1775_pa,v1775_pb,v1775_pg]
  minus := ![(Primitive.Addresses.material1775 1).one,v1775_mb,v1775_mg]
  upper := v1775_upper
  lower := (Primitive.Addresses.material1775 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1775_pa_checked.trans (by decide +kernel)
    · exact v1775_pb_checked.trans (by decide +kernel)
    · exact v1775_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 46 Primitive.Addresses.material1775
    · exact v1775_mb_checked.trans (by decide +kernel)
    · exact v1775_mg_checked.trans (by decide +kernel)
  upper_error := v1775_upper_checked
  lower_error := reuse_lower_error 20 46 Primitive.Addresses.material1775

def v1776_pa : Scalar.QComplex := ((999999800767256113106636056225 : Int)/10^30,(-631241196437701213495833525 : Int)/10^30)
theorem v1776_pa_checked : Scalar.distance (sourceCoefficient 20 47 1 0) v1776_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1776_pb : Scalar.QComplex := ((-272366378578162231123101 : Int)/10^30,(-431477422340165347993418499 : Int)/10^30)
theorem v1776_pb_checked : Scalar.distance (sourceCoefficient 20 47 1 1) v1776_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1776_pg : Scalar.QComplex := ((-93086409981597517136532 : Int)/10^30,(58759988515787732080 : Int)/10^30)
theorem v1776_pg_checked : Scalar.distance (sourceCoefficient 20 47 1 2) v1776_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1776_mb : Scalar.QComplex := ((-644711859621559897478134 : Int)/10^30,(-431477026641483731753671419 : Int)/10^30)
theorem v1776_mb_checked : Scalar.distance (sourceCoefficient 20 47 3 1) v1776_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1776_mg : Scalar.QComplex := ((-93086324614049184403989 : Int)/10^30,(139089345994602922063 : Int)/10^30)
theorem v1776_mg_checked : Scalar.distance (sourceCoefficient 20 47 3 2) v1776_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1776_upper : Scalar.QComplex := ((999997221919981801102767868393 : Int)/10^30,(-2357149193129108437656149909 : Int)/10^30)
theorem v1776_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 47 5) 1) 14) v1776_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1776 : Material (20 : Basis) (47 : Basis) where
  plus := ![v1776_pa,v1776_pb,v1776_pg]
  minus := ![(Primitive.Addresses.material1776 1).one,v1776_mb,v1776_mg]
  upper := v1776_upper
  lower := (Primitive.Addresses.material1776 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1776_pa_checked.trans (by decide +kernel)
    · exact v1776_pb_checked.trans (by decide +kernel)
    · exact v1776_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 47 Primitive.Addresses.material1776
    · exact v1776_mb_checked.trans (by decide +kernel)
    · exact v1776_mg_checked.trans (by decide +kernel)
  upper_error := v1776_upper_checked
  lower_error := reuse_lower_error 20 47 Primitive.Addresses.material1776

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
