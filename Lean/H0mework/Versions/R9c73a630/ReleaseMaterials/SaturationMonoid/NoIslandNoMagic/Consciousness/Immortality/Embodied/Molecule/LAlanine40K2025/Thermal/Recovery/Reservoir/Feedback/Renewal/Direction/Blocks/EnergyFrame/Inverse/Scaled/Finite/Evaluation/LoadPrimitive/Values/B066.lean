import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B044

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1057_pa : Scalar.QComplex := ((999999816808599449060651848237 : Int)/10^30,(-605295603439170422402651243 : Int)/10^30)
theorem v1057_pa_checked : Scalar.distance (sourceCoefficient 11 57 1 0) v1057_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1057_pb : Scalar.QComplex := ((-261171425486726279100120 : Int)/10^30,(-431477407333611417404486615 : Int)/10^30)
theorem v1057_pb_checked : Scalar.distance (sourceCoefficient 11 57 1 1) v1057_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1057_pg : Scalar.QComplex := ((-93086409109465456636729 : Int)/10^30,(56344804495783033543 : Int)/10^30)
theorem v1057_pg_checked : Scalar.distance (sourceCoefficient 11 57 1 2) v1057_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1057_mb : Scalar.QComplex := ((-633516897748536444029608 : Int)/10^30,(-431477021295675704729446543 : Int)/10^30)
theorem v1057_mb_checked : Scalar.distance (sourceCoefficient 11 57 3 1) v1057_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1057_mg : Scalar.QComplex := ((-93086325826112482052554 : Int)/10^30,(136674162121270924694 : Int)/10^30)
theorem v1057_mg_checked : Scalar.distance (sourceCoefficient 11 57 3 2) v1057_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1057_upper : Scalar.QComplex := ((999997282741040995014161508739 : Int)/10^30,(-2331203666459393972982918634 : Int)/10^30)
theorem v1057_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 57 5) 1) 14) v1057_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1057 : Material (11 : Basis) (57 : Basis) where
  plus := ![v1057_pa,v1057_pb,v1057_pg]
  minus := ![(Primitive.Addresses.material1057 1).one,v1057_mb,v1057_mg]
  upper := v1057_upper
  lower := (Primitive.Addresses.material1057 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1057_pa_checked.trans (by decide +kernel)
    · exact v1057_pb_checked.trans (by decide +kernel)
    · exact v1057_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 57 Primitive.Addresses.material1057
    · exact v1057_mb_checked.trans (by decide +kernel)
    · exact v1057_mg_checked.trans (by decide +kernel)
  upper_error := v1057_upper_checked
  lower_error := reuse_lower_error 11 57 Primitive.Addresses.material1057

def v1058_pa : Scalar.QComplex := ((999999812920007892122746818533 : Int)/10^30,(-611686152546247412007075081 : Int)/10^30)
theorem v1058_pa_checked : Scalar.distance (sourceCoefficient 11 58 1 0) v1058_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1058_pb : Scalar.QComplex := ((-263928803160105371906271 : Int)/10^30,(-431477405015069793247925144 : Int)/10^30)
theorem v1058_pb_checked : Scalar.distance (sourceCoefficient 11 58 1 1) v1058_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1058_pg : Scalar.QComplex := ((-93086408678378243756767 : Int)/10^30,(56939677831099282625 : Int)/10^30)
theorem v1058_pg_checked : Scalar.distance (sourceCoefficient 11 58 1 2) v1058_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1058_mb : Scalar.QComplex := ((-636274272394420812242882 : Int)/10^30,(-431477016597642199426082842 : Int)/10^30)
theorem v1058_mb_checked : Scalar.distance (sourceCoefficient 11 58 3 1) v1058_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1058_mg : Scalar.QComplex := ((-93086324881676533408593 : Int)/10^30,(137269034863079794716 : Int)/10^30)
theorem v1058_mg_checked : Scalar.distance (sourceCoefficient 11 58 3 2) v1058_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1058_upper : Scalar.QComplex := ((999997267822947216947976556948 : Int)/10^30,(-2337594199337142497222674618 : Int)/10^30)
theorem v1058_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 58 5) 1) 14) v1058_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1058 : Material (11 : Basis) (58 : Basis) where
  plus := ![v1058_pa,v1058_pb,v1058_pg]
  minus := ![(Primitive.Addresses.material1058 1).one,v1058_mb,v1058_mg]
  upper := v1058_upper
  lower := (Primitive.Addresses.material1058 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1058_pa_checked.trans (by decide +kernel)
    · exact v1058_pb_checked.trans (by decide +kernel)
    · exact v1058_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 58 Primitive.Addresses.material1058
    · exact v1058_mb_checked.trans (by decide +kernel)
    · exact v1058_mg_checked.trans (by decide +kernel)
  upper_error := v1058_upper_checked
  lower_error := reuse_lower_error 11 58 Primitive.Addresses.material1058

def v1059_pa : Scalar.QComplex := ((999999802020892709099387622150 : Int)/10^30,(-629252076187337105439020816 : Int)/10^30)
theorem v1059_pa_checked : Scalar.distance (sourceCoefficient 11 59 1 0) v1059_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1059_pb : Scalar.QComplex := ((-271508102600160198412322 : Int)/10^30,(-431477398520965223617440174 : Int)/10^30)
theorem v1059_pb_checked : Scalar.distance (sourceCoefficient 11 59 1 1) v1059_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1059_pg : Scalar.QComplex := ((-93086407470583313794863 : Int)/10^30,(58574826762276909382 : Int)/10^30)
theorem v1059_pg_checked : Scalar.distance (sourceCoefficient 11 59 1 2) v1059_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1059_mb : Scalar.QComplex := ((-643853563408236306141249 : Int)/10^30,(-431477003562945990055148387 : Int)/10^30)
theorem v1059_mb_checked : Scalar.distance (sourceCoefficient 11 59 3 1) v1059_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1059_mg : Scalar.QComplex := ((-93086322262822169931701 : Int)/10^30,(138904182143144116905 : Int)/10^30)
theorem v1059_mg_checked : Scalar.distance (sourceCoefficient 11 59 3 2) v1059_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1059_upper : Scalar.QComplex := ((999997226606657630500020058406 : Int)/10^30,(-2355160078004968319698358629 : Int)/10^30)
theorem v1059_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 59 5) 1) 14) v1059_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1059 : Material (11 : Basis) (59 : Basis) where
  plus := ![v1059_pa,v1059_pb,v1059_pg]
  minus := ![(Primitive.Addresses.material1059 1).one,v1059_mb,v1059_mg]
  upper := v1059_upper
  lower := (Primitive.Addresses.material1059 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1059_pa_checked.trans (by decide +kernel)
    · exact v1059_pb_checked.trans (by decide +kernel)
    · exact v1059_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 59 Primitive.Addresses.material1059
    · exact v1059_mb_checked.trans (by decide +kernel)
    · exact v1059_mg_checked.trans (by decide +kernel)
  upper_error := v1059_upper_checked
  lower_error := reuse_lower_error 11 59 Primitive.Addresses.material1059

def v1060_pa : Scalar.QComplex := ((999999789064459166944698217358 : Int)/10^30,(-649516002244985660085189316 : Int)/10^30)
theorem v1060_pa_checked : Scalar.distance (sourceCoefficient 11 60 1 0) v1060_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1060_pb : Scalar.QComplex := ((-280251529052304091461577 : Int)/10^30,(-431477390808903378063269009 : Int)/10^30)
theorem v1060_pb_checked : Scalar.distance (sourceCoefficient 11 60 1 1) v1060_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1060_pg : Scalar.QComplex := ((-93086406035653870113452 : Int)/10^30,(60461123065031098896 : Int)/10^30)
theorem v1060_pg_checked : Scalar.distance (sourceCoefficient 11 60 1 2) v1060_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1060_mb : Scalar.QComplex := ((-652596979949640902386576 : Int)/10^30,(-431476988305703777163139528 : Int)/10^30)
theorem v1060_mb_checked : Scalar.distance (sourceCoefficient 11 60 3 1) v1060_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1060_mg : Scalar.QComplex := ((-93086319200104506895011 : Int)/10^30,(140790476505264501830 : Int)/10^30)
theorem v1060_mg_checked : Scalar.distance (sourceCoefficient 11 60 3 2) v1060_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1060_upper : Scalar.QComplex := ((999997178676545338941428481497 : Int)/10^30,(-2375423951520250484153707448 : Int)/10^30)
theorem v1060_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 60 5) 1) 14) v1060_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1060 : Material (11 : Basis) (60 : Basis) where
  plus := ![v1060_pa,v1060_pb,v1060_pg]
  minus := ![(Primitive.Addresses.material1060 1).one,v1060_mb,v1060_mg]
  upper := v1060_upper
  lower := (Primitive.Addresses.material1060 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1060_pa_checked.trans (by decide +kernel)
    · exact v1060_pb_checked.trans (by decide +kernel)
    · exact v1060_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 60 Primitive.Addresses.material1060
    · exact v1060_mb_checked.trans (by decide +kernel)
    · exact v1060_mg_checked.trans (by decide +kernel)
  upper_error := v1060_upper_checked
  lower_error := reuse_lower_error 11 60 Primitive.Addresses.material1060

def v1061_pa : Scalar.QComplex := ((999999785241561038055755449050 : Int)/10^30,(-655375336584083993809018047 : Int)/10^30)
theorem v1061_pa_checked : Scalar.distance (sourceCoefficient 11 61 1 0) v1061_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1061_pb : Scalar.QComplex := ((-282779699468823995766739 : Int)/10^30,(-431477388534923644701515236 : Int)/10^30)
theorem v1061_pb_checked : Scalar.distance (sourceCoefficient 11 61 1 1) v1061_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1061_pg : Scalar.QComplex := ((-93086405612431104212531 : Int)/10^30,(61006547511320510248 : Int)/10^30)
theorem v1061_pg_checked : Scalar.distance (sourceCoefficient 11 61 1 2) v1061_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1061_mb : Scalar.QComplex := ((-655125147462465323879526 : Int)/10^30,(-431476983850027685619997658 : Int)/10^30)
theorem v1061_mb_checked : Scalar.distance (sourceCoefficient 11 61 3 1) v1061_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1061_mg : Scalar.QComplex := ((-93086318306205166436671 : Int)/10^30,(141335900383245278973 : Int)/10^30)
theorem v1061_mg_checked : Scalar.distance (sourceCoefficient 11 61 3 2) v1061_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1061_upper : Scalar.QComplex := ((999997164740973389185421401616 : Int)/10^30,(-2381283270534583245698278021 : Int)/10^30)
theorem v1061_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 61 5) 1) 14) v1061_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1061 : Material (11 : Basis) (61 : Basis) where
  plus := ![v1061_pa,v1061_pb,v1061_pg]
  minus := ![(Primitive.Addresses.material1061 1).one,v1061_mb,v1061_mg]
  upper := v1061_upper
  lower := (Primitive.Addresses.material1061 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1061_pa_checked.trans (by decide +kernel)
    · exact v1061_pb_checked.trans (by decide +kernel)
    · exact v1061_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 61 Primitive.Addresses.material1061
    · exact v1061_mb_checked.trans (by decide +kernel)
    · exact v1061_mg_checked.trans (by decide +kernel)
  upper_error := v1061_upper_checked
  lower_error := reuse_lower_error 11 61 Primitive.Addresses.material1061

def v1062_pa : Scalar.QComplex := ((999999779625874068265160130722 : Int)/10^30,(-663888697974829437118837954 : Int)/10^30)
theorem v1062_pa_checked : Scalar.distance (sourceCoefficient 11 62 1 0) v1062_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1062_pb : Scalar.QComplex := ((-286453022590012674763201 : Int)/10^30,(-431477385195731603856180332 : Int)/10^30)
theorem v1062_pb_checked : Scalar.distance (sourceCoefficient 11 62 1 1) v1062_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1062_pg : Scalar.QComplex := ((-93086404990862384822868 : Int)/10^30,(61799025827447593503 : Int)/10^30)
theorem v1062_pg_checked : Scalar.distance (sourceCoefficient 11 62 1 2) v1062_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1062_mb : Scalar.QComplex := ((-658798466334335586074601 : Int)/10^30,(-431476977340924474854582738 : Int)/10^30)
theorem v1062_mb_checked : Scalar.distance (sourceCoefficient 11 62 3 1) v1062_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1062_mg : Scalar.QComplex := ((-93086317000763583566189 : Int)/10^30,(142128377867910656669 : Int)/10^30)
theorem v1062_mg_checked : Scalar.distance (sourceCoefficient 11 62 3 2) v1062_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1062_upper : Scalar.QComplex := ((999997144432005348986555426401 : Int)/10^30,(-2389796609553510688455093436 : Int)/10^30)
theorem v1062_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 62 5) 1) 14) v1062_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1062 : Material (11 : Basis) (62 : Basis) where
  plus := ![v1062_pa,v1062_pb,v1062_pg]
  minus := ![(Primitive.Addresses.material1062 1).one,v1062_mb,v1062_mg]
  upper := v1062_upper
  lower := (Primitive.Addresses.material1062 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1062_pa_checked.trans (by decide +kernel)
    · exact v1062_pb_checked.trans (by decide +kernel)
    · exact v1062_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 62 Primitive.Addresses.material1062
    · exact v1062_mb_checked.trans (by decide +kernel)
    · exact v1062_mg_checked.trans (by decide +kernel)
  upper_error := v1062_upper_checked
  lower_error := reuse_lower_error 11 62 Primitive.Addresses.material1062

def v1063_pa : Scalar.QComplex := ((999999762857238146986528989705 : Int)/10^30,(-688683866131142528267339100 : Int)/10^30)
theorem v1063_pa_checked : Scalar.distance (sourceCoefficient 11 63 1 0) v1063_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1063_pb : Scalar.QComplex := ((-297151577390763810701480 : Int)/10^30,(-431477375232764673767013130 : Int)/10^30)
theorem v1063_pb_checked : Scalar.distance (sourceCoefficient 11 63 1 1) v1063_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1063_pg : Scalar.QComplex := ((-93086403135697037523880 : Int)/10^30,(64107119198273245780 : Int)/10^30)
theorem v1063_pg_checked : Scalar.distance (sourceCoefficient 11 63 1 2) v1063_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1063_mb : Scalar.QComplex := ((-669497008553934076290794 : Int)/10^30,(-431476958145590306406401234 : Int)/10^30)
theorem v1063_mb_checked : Scalar.distance (sourceCoefficient 11 63 3 1) v1063_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1063_mg : Scalar.QComplex := ((-93086313153818300674025 : Int)/10^30,(144436468778403520735 : Int)/10^30)
theorem v1063_mg_checked : Scalar.distance (sourceCoefficient 11 63 3 2) v1063_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1063_upper : Scalar.QComplex := ((999997084869183564908742919039 : Int)/10^30,(-2414591711839189094469637506 : Int)/10^30)
theorem v1063_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 63 5) 1) 14) v1063_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1063 : Material (11 : Basis) (63 : Basis) where
  plus := ![v1063_pa,v1063_pb,v1063_pg]
  minus := ![(Primitive.Addresses.material1063 1).one,v1063_mb,v1063_mg]
  upper := v1063_upper
  lower := (Primitive.Addresses.material1063 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1063_pa_checked.trans (by decide +kernel)
    · exact v1063_pb_checked.trans (by decide +kernel)
    · exact v1063_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 63 Primitive.Addresses.material1063
    · exact v1063_mb_checked.trans (by decide +kernel)
    · exact v1063_mg_checked.trans (by decide +kernel)
  upper_error := v1063_upper_checked
  lower_error := reuse_lower_error 11 63 Primitive.Addresses.material1063

def v1064_pa : Scalar.QComplex := ((999999737824261085409249128296 : Int)/10^30,(-724121128743709166968712578 : Int)/10^30)
theorem v1064_pa_checked : Scalar.distance (sourceCoefficient 11 64 1 0) v1064_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1064_pb : Scalar.QComplex := ((-312441955140208041918417 : Int)/10^30,(-431477360379704204489264870 : Int)/10^30)
theorem v1064_pb_checked : Scalar.distance (sourceCoefficient 11 64 1 1) v1064_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1064_pg : Scalar.QComplex := ((-93086400368391297992209 : Int)/10^30,(67405846977626070045 : Int)/10^30)
theorem v1064_pg_checked : Scalar.distance (sourceCoefficient 11 64 1 2) v1064_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1064_mb : Scalar.QComplex := ((-684787367792549638628825 : Int)/10^30,(-431476930097628022881344656 : Int)/10^30)
theorem v1064_mb_checked : Scalar.distance (sourceCoefficient 11 64 3 1) v1064_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1064_mg : Scalar.QComplex := ((-93086307539860087139300 : Int)/10^30,(147735192941429015048 : Int)/10^30)
theorem v1064_mg_checked : Scalar.distance (sourceCoefficient 11 64 3 2) v1064_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1064_upper : Scalar.QComplex := ((999996998674743361071431773743 : Int)/10^30,(-2450028878467468390693710403 : Int)/10^30)
theorem v1064_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 64 5) 1) 14) v1064_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1064 : Material (11 : Basis) (64 : Basis) where
  plus := ![v1064_pa,v1064_pb,v1064_pg]
  minus := ![(Primitive.Addresses.material1064 1).one,v1064_mb,v1064_mg]
  upper := v1064_upper
  lower := (Primitive.Addresses.material1064 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1064_pa_checked.trans (by decide +kernel)
    · exact v1064_pb_checked.trans (by decide +kernel)
    · exact v1064_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 64 Primitive.Addresses.material1064
    · exact v1064_mb_checked.trans (by decide +kernel)
    · exact v1064_mg_checked.trans (by decide +kernel)
  upper_error := v1064_upper_checked
  lower_error := reuse_lower_error 11 64 Primitive.Addresses.material1064

def v1065_pa : Scalar.QComplex := ((999999711133273767117409669847 : Int)/10^30,(-760087737713074579342076303 : Int)/10^30)
theorem v1065_pa_checked : Scalar.distance (sourceCoefficient 11 65 1 0) v1065_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1065_pb : Scalar.QComplex := ((-327960733442590114692593 : Int)/10^30,(-431477344566040783558210629 : Int)/10^30)
theorem v1065_pb_checked : Scalar.distance (sourceCoefficient 11 65 1 1) v1065_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1065_pg : Scalar.QComplex := ((-93086397420296779603160 : Int)/10^30,(70753849665486482003 : Int)/10^30)
theorem v1065_pg_checked : Scalar.distance (sourceCoefficient 11 65 1 2) v1065_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1065_mb : Scalar.QComplex := ((-700306126670101994918505 : Int)/10^30,(-431476900891963754973046590 : Int)/10^30)
theorem v1065_mb_checked : Scalar.distance (sourceCoefficient 11 65 3 1) v1065_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1065_mg : Scalar.QComplex := ((-93086301702591135280570 : Int)/10^30,(151083191838602222912 : Int)/10^30)
theorem v1065_mg_checked : Scalar.distance (sourceCoefficient 11 65 3 2) v1065_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1065_upper : Scalar.QComplex := ((999996909908691580022753566097 : Int)/10^30,(-2485995387802571953955267608 : Int)/10^30)
theorem v1065_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 65 5) 1) 14) v1065_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1065 : Material (11 : Basis) (65 : Basis) where
  plus := ![v1065_pa,v1065_pb,v1065_pg]
  minus := ![(Primitive.Addresses.material1065 1).one,v1065_mb,v1065_mg]
  upper := v1065_upper
  lower := (Primitive.Addresses.material1065 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1065_pa_checked.trans (by decide +kernel)
    · exact v1065_pb_checked.trans (by decide +kernel)
    · exact v1065_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 65 Primitive.Addresses.material1065
    · exact v1065_mb_checked.trans (by decide +kernel)
    · exact v1065_mg_checked.trans (by decide +kernel)
  upper_error := v1065_upper_checked
  lower_error := reuse_lower_error 11 65 Primitive.Addresses.material1065

def v1066_pa : Scalar.QComplex := ((999999697610518916445383576012 : Int)/10^30,(-777675299034057634293834824 : Int)/10^30)
theorem v1066_pa_checked : Scalar.distance (sourceCoefficient 11 66 1 0) v1066_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1066_pb : Scalar.QComplex := ((-335549368204083228667575 : Int)/10^30,(-431477336562272376077526001 : Int)/10^30)
theorem v1066_pb_checked : Scalar.distance (sourceCoefficient 11 66 1 1) v1066_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1066_pg : Scalar.QComplex := ((-93086395927542712371350 : Int)/10^30,(72391012679235222796 : Int)/10^30)
theorem v1066_pg_checked : Scalar.distance (sourceCoefficient 11 66 1 2) v1066_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1066_mb : Scalar.QComplex := ((-707894751699107910139587 : Int)/10^30,(-431476886339548307914782112 : Int)/10^30)
theorem v1066_mb_checked : Scalar.distance (sourceCoefficient 11 66 3 1) v1066_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1066_mg : Scalar.QComplex := ((-93086298797039678089123 : Int)/10^30,(152720352954580822767 : Int)/10^30)
theorem v1066_mg_checked : Scalar.distance (sourceCoefficient 11 66 3 2) v1066_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1066_upper : Scalar.QComplex := ((999996866031421560988264947657 : Int)/10^30,(-2503582899589900303859811196 : Int)/10^30)
theorem v1066_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 66 5) 1) 14) v1066_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1066 : Material (11 : Basis) (66 : Basis) where
  plus := ![v1066_pa,v1066_pb,v1066_pg]
  minus := ![(Primitive.Addresses.material1066 1).one,v1066_mb,v1066_mg]
  upper := v1066_upper
  lower := (Primitive.Addresses.material1066 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1066_pa_checked.trans (by decide +kernel)
    · exact v1066_pb_checked.trans (by decide +kernel)
    · exact v1066_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 66 Primitive.Addresses.material1066
    · exact v1066_mb_checked.trans (by decide +kernel)
    · exact v1066_mg_checked.trans (by decide +kernel)
  upper_error := v1066_upper_checked
  lower_error := reuse_lower_error 11 66 Primitive.Addresses.material1066

def v1067_pa : Scalar.QComplex := ((999999674220125492516813589235 : Int)/10^30,(-807192444762981994742195227 : Int)/10^30)
theorem v1067_pa_checked : Scalar.distance (sourceCoefficient 11 67 1 0) v1067_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1067_pb : Scalar.QComplex := ((-348285348458268798095112 : Int)/10^30,(-431477322729624382092184104 : Int)/10^30)
theorem v1067_pb_checked : Scalar.distance (sourceCoefficient 11 67 1 1) v1067_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1067_pg : Scalar.QComplex := ((-93086393346759361047855 : Int)/10^30,(75138657898401811005 : Int)/10^30)
theorem v1067_pg_checked : Scalar.distance (sourceCoefficient 11 67 1 2) v1067_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1067_mb : Scalar.QComplex := ((-720630715274153748411200 : Int)/10^30,(-431476861516328112351671429 : Int)/10^30)
theorem v1067_mb_checked : Scalar.distance (sourceCoefficient 11 67 3 1) v1067_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1067_mg : Scalar.QComplex := ((-93086293845163212915331 : Int)/10^30,(155467994923573724266 : Int)/10^30)
theorem v1067_mg_checked : Scalar.distance (sourceCoefficient 11 67 3 2) v1067_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1067_upper : Scalar.QComplex := ((999996791697147220722526361199 : Int)/10^30,(-2533099960986806338793994629 : Int)/10^30)
theorem v1067_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 67 5) 1) 14) v1067_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1067 : Material (11 : Basis) (67 : Basis) where
  plus := ![v1067_pa,v1067_pb,v1067_pg]
  minus := ![(Primitive.Addresses.material1067 1).one,v1067_mb,v1067_mg]
  upper := v1067_upper
  lower := (Primitive.Addresses.material1067 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1067_pa_checked.trans (by decide +kernel)
    · exact v1067_pb_checked.trans (by decide +kernel)
    · exact v1067_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 67 Primitive.Addresses.material1067
    · exact v1067_mb_checked.trans (by decide +kernel)
    · exact v1067_mg_checked.trans (by decide +kernel)
  upper_error := v1067_upper_checked
  lower_error := reuse_lower_error 11 67 Primitive.Addresses.material1067

def v1068_pa : Scalar.QComplex := ((999999633331919721999107567080 : Int)/10^30,(-856350410819379878290681292 : Int)/10^30)
theorem v1068_pa_checked : Scalar.distance (sourceCoefficient 11 68 1 0) v1068_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1068_pb : Scalar.QComplex := ((-369495897380728406353408 : Int)/10^30,(-431477298580184280835086692 : Int)/10^30)
theorem v1068_pb_checked : Scalar.distance (sourceCoefficient 11 68 1 1) v1068_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1068_pg : Scalar.QComplex := ((-93086388838705539358143 : Int)/10^30,(79714596552516114502 : Int)/10^30)
theorem v1068_pg_checked : Scalar.distance (sourceCoefficient 11 68 1 2) v1068_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1068_mb : Scalar.QComplex := ((-741841235459077465885983 : Int)/10^30,(-431476819063148570613688405 : Int)/10^30)
theorem v1068_mb_checked : Scalar.distance (sourceCoefficient 11 68 3 1) v1068_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1068_mg : Scalar.QComplex := ((-93086285388282103905905 : Int)/10^30,(160043927983609523197 : Int)/10^30)
theorem v1068_mg_checked : Scalar.distance (sourceCoefficient 11 68 3 2) v1068_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1068_upper : Scalar.QComplex := ((999996665966812510885844153496 : Int)/10^30,(-2582257783258854470805437902 : Int)/10^30)
theorem v1068_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 68 5) 1) 14) v1068_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1068 : Material (11 : Basis) (68 : Basis) where
  plus := ![v1068_pa,v1068_pb,v1068_pg]
  minus := ![(Primitive.Addresses.material1068 1).one,v1068_mb,v1068_mg]
  upper := v1068_upper
  lower := (Primitive.Addresses.material1068 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1068_pa_checked.trans (by decide +kernel)
    · exact v1068_pb_checked.trans (by decide +kernel)
    · exact v1068_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 68 Primitive.Addresses.material1068
    · exact v1068_mb_checked.trans (by decide +kernel)
    · exact v1068_mg_checked.trans (by decide +kernel)
  upper_error := v1068_upper_checked
  lower_error := reuse_lower_error 11 68 Primitive.Addresses.material1068

def v1069_pa : Scalar.QComplex := ((999999614570401603667956473511 : Int)/10^30,(-877985790452606793835649978 : Int)/10^30)
theorem v1069_pa_checked : Scalar.distance (sourceCoefficient 11 69 1 0) v1069_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1069_pb : Scalar.QComplex := ((-378831073350370077332731 : Int)/10^30,(-431477287510965370105755772 : Int)/10^30)
theorem v1069_pb_checked : Scalar.distance (sourceCoefficient 11 69 1 1) v1069_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1069_pg : Scalar.QComplex := ((-93086386771454322705731 : Int)/10^30,(81728556370517063436 : Int)/10^30)
theorem v1069_pg_checked : Scalar.distance (sourceCoefficient 11 69 1 2) v1069_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1069_mb : Scalar.QComplex := ((-751176398400569103903209 : Int)/10^30,(-431476799938097360377863755 : Int)/10^30)
theorem v1069_mb_checked : Scalar.distance (sourceCoefficient 11 69 3 1) v1069_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1069_mg : Scalar.QComplex := ((-93086281583075039433841 : Int)/10^30,(162057885267776494946 : Int)/10^30)
theorem v1069_mg_checked : Scalar.distance (sourceCoefficient 11 69 3 2) v1069_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1069_upper : Scalar.QComplex := ((999996609864619834990584940013 : Int)/10^30,(-2603893098288046652267767252 : Int)/10^30)
theorem v1069_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 69 5) 1) 14) v1069_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1069 : Material (11 : Basis) (69 : Basis) where
  plus := ![v1069_pa,v1069_pb,v1069_pg]
  minus := ![(Primitive.Addresses.material1069 1).one,v1069_mb,v1069_mg]
  upper := v1069_upper
  lower := (Primitive.Addresses.material1069 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1069_pa_checked.trans (by decide +kernel)
    · exact v1069_pb_checked.trans (by decide +kernel)
    · exact v1069_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 69 Primitive.Addresses.material1069
    · exact v1069_mb_checked.trans (by decide +kernel)
    · exact v1069_mg_checked.trans (by decide +kernel)
  upper_error := v1069_upper_checked
  lower_error := reuse_lower_error 11 69 Primitive.Addresses.material1069

def v1070_pa : Scalar.QComplex := ((999999601973663150039790010378 : Int)/10^30,(-892217751042286534141968106 : Int)/10^30)
theorem v1070_pa_checked : Scalar.distance (sourceCoefficient 11 70 1 0) v1070_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1070_pb : Scalar.QComplex := ((-384971841690153561285970 : Int)/10^30,(-431477280082691320759939948 : Int)/10^30)
theorem v1070_pb_checked : Scalar.distance (sourceCoefficient 11 70 1 1) v1070_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1070_pg : Scalar.QComplex := ((-93086385383878257089733 : Int)/10^30,(83053358477283468612 : Int)/10^30)
theorem v1070_pg_checked : Scalar.distance (sourceCoefficient 11 70 1 2) v1070_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1070_mb : Scalar.QComplex := ((-757317158043597940436089 : Int)/10^30,(-431476787210619569624083856 : Int)/10^30)
theorem v1070_mb_checked : Scalar.distance (sourceCoefficient 11 70 3 1) v1070_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1070_mg : Scalar.QComplex := ((-93086279052254939208370 : Int)/10^30,(163382685683842878805 : Int)/10^30)
theorem v1070_mg_checked : Scalar.distance (sourceCoefficient 11 70 3 2) v1070_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1070_upper : Scalar.QComplex := ((999996572704827278316468055693 : Int)/10^30,(-2618125015940065093998259099 : Int)/10^30)
theorem v1070_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 70 5) 1) 14) v1070_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1070 : Material (11 : Basis) (70 : Basis) where
  plus := ![v1070_pa,v1070_pb,v1070_pg]
  minus := ![(Primitive.Addresses.material1070 1).one,v1070_mb,v1070_mg]
  upper := v1070_upper
  lower := (Primitive.Addresses.material1070 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1070_pa_checked.trans (by decide +kernel)
    · exact v1070_pb_checked.trans (by decide +kernel)
    · exact v1070_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 70 Primitive.Addresses.material1070
    · exact v1070_mb_checked.trans (by decide +kernel)
    · exact v1070_mg_checked.trans (by decide +kernel)
  upper_error := v1070_upper_checked
  lower_error := reuse_lower_error 11 70 Primitive.Addresses.material1070

def v1071_pa : Scalar.QComplex := ((999999580004110692001705754371 : Int)/10^30,(-916510557614831599532183670 : Int)/10^30)
theorem v1071_pa_checked : Scalar.distance (sourceCoefficient 11 71 1 0) v1071_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1071_pb : Scalar.QComplex := ((-395453636788027778872747 : Int)/10^30,(-431477267134021739030644248 : Int)/10^30)
theorem v1071_pb_checked : Scalar.distance (sourceCoefficient 11 71 1 1) v1071_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1071_pg : Scalar.QComplex := ((-93086382964579618040584 : Int)/10^30,(85314688589033131720 : Int)/10^30)
theorem v1071_pg_checked : Scalar.distance (sourceCoefficient 11 71 1 2) v1071_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1071_mb : Scalar.QComplex := ((-767798938064502138779863 : Int)/10^30,(-431476765216637722337488208 : Int)/10^30)
theorem v1071_mb_checked : Scalar.distance (sourceCoefficient 11 71 3 1) v1071_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1071_mg : Scalar.QComplex := ((-93086274681531161062225 : Int)/10^30,(165644012865850229083 : Int)/10^30)
theorem v1071_mg_checked : Scalar.distance (sourceCoefficient 11 71 3 2) v1071_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1071_upper : Scalar.QComplex := ((999996508808127223330178054632 : Int)/10^30,(-2642417748413873922755744298 : Int)/10^30)
theorem v1071_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 71 5) 1) 14) v1071_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1071 : Material (11 : Basis) (71 : Basis) where
  plus := ![v1071_pa,v1071_pb,v1071_pg]
  minus := ![(Primitive.Addresses.material1071 1).one,v1071_mb,v1071_mg]
  upper := v1071_upper
  lower := (Primitive.Addresses.material1071 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1071_pa_checked.trans (by decide +kernel)
    · exact v1071_pb_checked.trans (by decide +kernel)
    · exact v1071_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 71 Primitive.Addresses.material1071
    · exact v1071_mb_checked.trans (by decide +kernel)
    · exact v1071_mg_checked.trans (by decide +kernel)
  upper_error := v1071_upper_checked
  lower_error := reuse_lower_error 11 71 Primitive.Addresses.material1071

def v1072_pa : Scalar.QComplex := ((999999555494991597997792045415 : Int)/10^30,(-942873172393457126220104059 : Int)/10^30)
theorem v1072_pa_checked : Scalar.distance (sourceCoefficient 11 72 1 0) v1072_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1072_pb : Scalar.QComplex := ((-406828506904247747787427 : Int)/10^30,(-431477252697959963023408302 : Int)/10^30)
theorem v1072_pb_checked : Scalar.distance (sourceCoefficient 11 72 1 1) v1072_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1072_pg : Scalar.QComplex := ((-93086380266637299821520 : Int)/10^30,(87768689682250160968 : Int)/10^30)
theorem v1072_pg_checked : Scalar.distance (sourceCoefficient 11 72 1 2) v1072_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1072_mb : Scalar.QComplex := ((-779173791487666969572544 : Int)/10^30,(-431476740964580716370353012 : Int)/10^30)
theorem v1072_mb_checked : Scalar.distance (sourceCoefficient 11 72 3 1) v1072_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1072_mg : Scalar.QComplex := ((-93086269865897428070482 : Int)/10^30,(168098010717127788124 : Int)/10^30)
theorem v1072_mg_checked : Scalar.distance (sourceCoefficient 11 72 3 2) v1072_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1072_upper : Scalar.QComplex := ((999996438799563122603033112673 : Int)/10^30,(-2668780281627965400613902023 : Int)/10^30)
theorem v1072_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 11 72 5) 1) 14) v1072_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1072 : Material (11 : Basis) (72 : Basis) where
  plus := ![v1072_pa,v1072_pb,v1072_pg]
  minus := ![(Primitive.Addresses.material1072 1).one,v1072_mb,v1072_mg]
  upper := v1072_upper
  lower := (Primitive.Addresses.material1072 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1072_pa_checked.trans (by decide +kernel)
    · exact v1072_pb_checked.trans (by decide +kernel)
    · exact v1072_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 11 72 Primitive.Addresses.material1072
    · exact v1072_mb_checked.trans (by decide +kernel)
    · exact v1072_mg_checked.trans (by decide +kernel)
  upper_error := v1072_upper_checked
  lower_error := reuse_lower_error 11 72 Primitive.Addresses.material1072

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
