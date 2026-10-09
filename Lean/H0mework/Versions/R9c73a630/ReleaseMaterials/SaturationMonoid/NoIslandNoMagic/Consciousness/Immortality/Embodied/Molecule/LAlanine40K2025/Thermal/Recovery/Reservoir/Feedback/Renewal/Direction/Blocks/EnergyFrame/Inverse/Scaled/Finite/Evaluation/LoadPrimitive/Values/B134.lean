import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B089
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B090

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2145_pa : Scalar.QComplex := ((999999706664005863037312209547 : Int)/10^30,(-765945103925810024666724587 : Int)/10^30)
theorem v2145_pa_checked : Scalar.distance (sourceCoefficient 25 46 1 0) v2145_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2145_pb : Scalar.QComplex := ((-330488090419970153160651 : Int)/10^30,(-431477388891213405067990750 : Int)/10^30)
theorem v2145_pb_checked : Scalar.distance (sourceCoefficient 25 46 1 1) v2145_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2145_pg : Scalar.QComplex := ((-93086401993611825440002 : Int)/10^30,(71299094763667582670 : Int)/10^30)
theorem v2145_pg_checked : Scalar.distance (sourceCoefficient 25 46 1 2) v2145_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2145_mb : Scalar.QComplex := ((-702833520957059165483382 : Int)/10^30,(-431476943036124628649095773 : Int)/10^30)
theorem v2145_mb_checked : Scalar.distance (sourceCoefficient 25 46 3 1) v2145_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2145_mg : Scalar.QComplex := ((-93086305805382515460547 : Int)/10^30,(151628440680328564689 : Int)/10^30)
theorem v2145_mg_checked : Scalar.distance (sourceCoefficient 25 46 3 2) v2145_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2145_upper : Scalar.QComplex := ((999996895330147625322760482607 : Int)/10^30,(-2491852737577897526353832844 : Int)/10^30)
theorem v2145_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 46 5) 1) 14) v2145_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2145 : Material (25 : Basis) (46 : Basis) where
  plus := ![v2145_pa,v2145_pb,v2145_pg]
  minus := ![(Primitive.Addresses.material2145 1).one,v2145_mb,v2145_mg]
  upper := v2145_upper
  lower := (Primitive.Addresses.material2145 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2145_pa_checked.trans (by decide +kernel)
    · exact v2145_pb_checked.trans (by decide +kernel)
    · exact v2145_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 46 Primitive.Addresses.material2145
    · exact v2145_mb_checked.trans (by decide +kernel)
    · exact v2145_mg_checked.trans (by decide +kernel)
  upper_error := v2145_upper_checked
  lower_error := reuse_lower_error 25 46 Primitive.Addresses.material2145

def v2146_pa : Scalar.QComplex := ((999999703639927247343264090727 : Int)/10^30,(-769883145468207239839842186 : Int)/10^30)
theorem v2146_pa_checked : Scalar.distance (sourceCoefficient 25 47 1 0) v2146_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2146_pb : Scalar.QComplex := ((-332187266678552702828277 : Int)/10^30,(-431477387428048377192645365 : Int)/10^30)
theorem v2146_pb_checked : Scalar.distance (sourceCoefficient 25 47 1 1) v2146_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2146_pg : Scalar.QComplex := ((-93086401695030772416548 : Int)/10^30,(71665672976131406218 : Int)/10^30)
theorem v2146_pg_checked : Scalar.distance (sourceCoefficient 25 47 1 2) v2146_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2146_mb : Scalar.QComplex := ((-704532695320315217339579 : Int)/10^30,(-431476940106647562478051364 : Int)/10^30)
theorem v2146_mb_checked : Scalar.distance (sourceCoefficient 25 47 3 1) v2146_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2146_mg : Scalar.QComplex := ((-93086305190461086325991 : Int)/10^30,(151995018498636565117 : Int)/10^30)
theorem v2146_mg_checked : Scalar.distance (sourceCoefficient 25 47 3 2) v2146_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2146_upper : Scalar.QComplex := ((999996885509371067798976737216 : Int)/10^30,(-2495790768035759110562429148 : Int)/10^30)
theorem v2146_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 47 5) 1) 14) v2146_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2146 : Material (25 : Basis) (47 : Basis) where
  plus := ![v2146_pa,v2146_pb,v2146_pg]
  minus := ![(Primitive.Addresses.material2146 1).one,v2146_mb,v2146_mg]
  upper := v2146_upper
  lower := (Primitive.Addresses.material2146 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2146_pa_checked.trans (by decide +kernel)
    · exact v2146_pb_checked.trans (by decide +kernel)
    · exact v2146_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 47 Primitive.Addresses.material2146
    · exact v2146_mb_checked.trans (by decide +kernel)
    · exact v2146_mg_checked.trans (by decide +kernel)
  upper_error := v2146_upper_checked
  lower_error := reuse_lower_error 25 47 Primitive.Addresses.material2146

def v2147_pa : Scalar.QComplex := ((999999682145377498271756256151 : Int)/10^30,(-797313704868977805137793082 : Int)/10^30)
theorem v2147_pa_checked : Scalar.distance (sourceCoefficient 25 48 1 0) v2147_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2147_pb : Scalar.QComplex := ((-344022935363377981258555 : Int)/10^30,(-431477376988811251353132946 : Int)/10^30)
theorem v2147_pb_checked : Scalar.distance (sourceCoefficient 25 48 1 1) v2147_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2147_pg : Scalar.QComplex := ((-93086399568531232568362 : Int)/10^30,(74219085703779122862 : Int)/10^30)
theorem v2147_pg_checked : Scalar.distance (sourceCoefficient 25 48 1 2) v2147_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2147_mb : Scalar.QComplex := ((-716368350589588653815953 : Int)/10^30,(-431476919453765307368896661 : Int)/10^30)
theorem v2147_mb_checked : Scalar.distance (sourceCoefficient 25 48 3 1) v2147_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2147_mg : Scalar.QComplex := ((-93086300860482155750990 : Int)/10^30,(154548428440458697625 : Int)/10^30)
theorem v2147_mg_checked : Scalar.distance (sourceCoefficient 25 48 3 2) v2147_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2147_upper : Scalar.QComplex := ((999996816672196287514289076098 : Int)/10^30,(-2523221249484290771691918049 : Int)/10^30)
theorem v2147_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 48 5) 1) 14) v2147_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2147 : Material (25 : Basis) (48 : Basis) where
  plus := ![v2147_pa,v2147_pb,v2147_pg]
  minus := ![(Primitive.Addresses.material2147 1).one,v2147_mb,v2147_mg]
  upper := v2147_upper
  lower := (Primitive.Addresses.material2147 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2147_pa_checked.trans (by decide +kernel)
    · exact v2147_pb_checked.trans (by decide +kernel)
    · exact v2147_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 48 Primitive.Addresses.material2147
    · exact v2147_mb_checked.trans (by decide +kernel)
    · exact v2147_mg_checked.trans (by decide +kernel)
  upper_error := v2147_upper_checked
  lower_error := reuse_lower_error 25 48 Primitive.Addresses.material2147

def v2148_pa : Scalar.QComplex := ((999999664331026742134427338563 : Int)/10^30,(-819352081734141649049060052 : Int)/10^30)
theorem v2148_pa_checked : Scalar.distance (sourceCoefficient 25 49 1 0) v2148_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2148_pb : Scalar.QComplex := ((-353531998597724082746123 : Int)/10^30,(-431477368288072478776745511 : Int)/10^30)
theorem v2148_pb_checked : Scalar.distance (sourceCoefficient 25 49 1 1) v2148_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2148_pg : Scalar.QComplex := ((-93086397800850734003077 : Int)/10^30,(76270559420919844685 : Int)/10^30)
theorem v2148_pg_checked : Scalar.distance (sourceCoefficient 25 49 1 2) v2148_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2148_mb : Scalar.QComplex := ((-725877402774930233491809 : Int)/10^30,(-431476902547136475544371582 : Int)/10^30)
theorem v2148_mb_checked : Scalar.distance (sourceCoefficient 25 49 3 1) v2148_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2148_mg : Scalar.QComplex := ((-93086297322472892427857 : Int)/10^30,(156599899868313340688 : Int)/10^30)
theorem v2148_mg_checked : Scalar.distance (sourceCoefficient 25 49 3 2) v2148_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2148_upper : Scalar.QComplex := ((999996760821632900418482998356 : Int)/10^30,(-2545259562779927784725422962 : Int)/10^30)
theorem v2148_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 49 5) 1) 14) v2148_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2148 : Material (25 : Basis) (49 : Basis) where
  plus := ![v2148_pa,v2148_pb,v2148_pg]
  minus := ![(Primitive.Addresses.material2148 1).one,v2148_mb,v2148_mg]
  upper := v2148_upper
  lower := (Primitive.Addresses.material2148 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2148_pa_checked.trans (by decide +kernel)
    · exact v2148_pb_checked.trans (by decide +kernel)
    · exact v2148_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 49 Primitive.Addresses.material2148
    · exact v2148_mb_checked.trans (by decide +kernel)
    · exact v2148_mg_checked.trans (by decide +kernel)
  upper_error := v2148_upper_checked
  lower_error := reuse_lower_error 25 49 Primitive.Addresses.material2148

def v2149_pa : Scalar.QComplex := ((999999662217648776353423485972 : Int)/10^30,(-821927361967209578583202200 : Int)/10^30)
theorem v2149_pa_checked : Scalar.distance (sourceCoefficient 25 50 1 0) v2149_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2149_pb : Scalar.QComplex := ((-354643174007118849507335 : Int)/10^30,(-431477367253119884175296926 : Int)/10^30)
theorem v2149_pb_checked : Scalar.distance (sourceCoefficient 25 50 1 1) v2149_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2149_pg : Scalar.QComplex := ((-93086397590847628985026 : Int)/10^30,(76510283050699506482 : Int)/10^30)
theorem v2149_pg_checked : Scalar.distance (sourceCoefficient 25 50 1 2) v2149_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2149_mb : Scalar.QComplex := ((-726988576877466135503869 : Int)/10^30,(-431476900553289933478053421 : Int)/10^30)
theorem v2149_mb_checked : Scalar.distance (sourceCoefficient 25 50 3 1) v2149_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2149_mg : Scalar.QComplex := ((-93086296905599169855202 : Int)/10^30,(156839623227609717766 : Int)/10^30)
theorem v2149_mg_checked : Scalar.distance (sourceCoefficient 25 50 3 2) v2149_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2149_upper : Scalar.QComplex := ((999996754263558027588203267802 : Int)/10^30,(-2547834835529919675984862400 : Int)/10^30)
theorem v2149_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 50 5) 1) 14) v2149_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2149 : Material (25 : Basis) (50 : Basis) where
  plus := ![v2149_pa,v2149_pb,v2149_pg]
  minus := ![(Primitive.Addresses.material2149 1).one,v2149_mb,v2149_mg]
  upper := v2149_upper
  lower := (Primitive.Addresses.material2149 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2149_pa_checked.trans (by decide +kernel)
    · exact v2149_pb_checked.trans (by decide +kernel)
    · exact v2149_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 50 Primitive.Addresses.material2149
    · exact v2149_mb_checked.trans (by decide +kernel)
    · exact v2149_mg_checked.trans (by decide +kernel)
  upper_error := v2149_upper_checked
  lower_error := reuse_lower_error 25 50 Primitive.Addresses.material2149

def v2150_pa : Scalar.QComplex := ((999999652866649102155342055478 : Int)/10^30,(-833226608609042207850353948 : Int)/10^30)
theorem v2150_pa_checked : Scalar.distance (sourceCoefficient 25 51 1 0) v2150_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2150_pb : Scalar.QComplex := ((-359518544387548070785735 : Int)/10^30,(-431477362667087465387878707 : Int)/10^30)
theorem v2150_pb_checked : Scalar.distance (sourceCoefficient 25 51 1 1) v2150_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2150_pg : Scalar.QComplex := ((-93086396660929543644636 : Int)/10^30,(77562089521810432666 : Int)/10^30)
theorem v2150_pg_checked : Scalar.distance (sourceCoefficient 25 51 1 2) v2150_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2150_mb : Scalar.QComplex := ((-731863941485032718533985 : Int)/10^30,(-431476891760034162500475111 : Int)/10^30)
theorem v2150_mb_checked : Scalar.distance (sourceCoefficient 25 51 3 1) v2150_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2150_mg : Scalar.QComplex := ((-93086295068019817802027 : Int)/10^30,(157891428504607599132 : Int)/10^30)
theorem v2150_mg_checked : Scalar.distance (sourceCoefficient 25 51 3 2) v2150_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2150_upper : Scalar.QComplex := ((999996725411097636450593371910 : Int)/10^30,(-2559134049203874613388668533 : Int)/10^30)
theorem v2150_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 51 5) 1) 14) v2150_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2150 : Material (25 : Basis) (51 : Basis) where
  plus := ![v2150_pa,v2150_pb,v2150_pg]
  minus := ![(Primitive.Addresses.material2150 1).one,v2150_mb,v2150_mg]
  upper := v2150_upper
  lower := (Primitive.Addresses.material2150 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2150_pa_checked.trans (by decide +kernel)
    · exact v2150_pb_checked.trans (by decide +kernel)
    · exact v2150_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 51 Primitive.Addresses.material2150
    · exact v2150_mb_checked.trans (by decide +kernel)
    · exact v2150_mg_checked.trans (by decide +kernel)
  upper_error := v2150_upper_checked
  lower_error := reuse_lower_error 25 51 Primitive.Addresses.material2150

def v2151_pa : Scalar.QComplex := ((999999632419235117649937527426 : Int)/10^30,(-857415532078280824428489455 : Int)/10^30)
theorem v2151_pa_checked : Scalar.distance (sourceCoefficient 25 52 1 0) v2151_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2151_pb : Scalar.QComplex := ((-369955519850008410599971 : Int)/10^30,(-431477352602587386768362954 : Int)/10^30)
theorem v2151_pb_checked : Scalar.distance (sourceCoefficient 25 52 1 1) v2151_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2151_pg : Scalar.QComplex := ((-93086394623589723562304 : Int)/10^30,(79813749913433243601 : Int)/10^30)
theorem v2151_pg_checked : Scalar.distance (sourceCoefficient 25 52 1 2) v2151_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2151_mb : Scalar.QComplex := ((-742300904376119820739701 : Int)/10^30,(-431476872688898071176271828 : Int)/10^30)
theorem v2151_mb_checked : Scalar.distance (sourceCoefficient 25 52 3 1) v2151_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2151_mg : Scalar.QComplex := ((-93086291087599249363420 : Int)/10^30,(160143086299701833950 : Int)/10^30)
theorem v2151_mg_checked : Scalar.distance (sourceCoefficient 25 52 3 2) v2151_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2151_upper : Scalar.QComplex := ((999996663215826600055946228016 : Int)/10^30,(-2583322901356171590736268463 : Int)/10^30)
theorem v2151_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 52 5) 1) 14) v2151_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2151 : Material (25 : Basis) (52 : Basis) where
  plus := ![v2151_pa,v2151_pb,v2151_pg]
  minus := ![(Primitive.Addresses.material2151 1).one,v2151_mb,v2151_mg]
  upper := v2151_upper
  lower := (Primitive.Addresses.material2151 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2151_pa_checked.trans (by decide +kernel)
    · exact v2151_pb_checked.trans (by decide +kernel)
    · exact v2151_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 52 Primitive.Addresses.material2151
    · exact v2151_mb_checked.trans (by decide +kernel)
    · exact v2151_mg_checked.trans (by decide +kernel)
  upper_error := v2151_upper_checked
  lower_error := reuse_lower_error 25 52 Primitive.Addresses.material2151

def v2152_pa : Scalar.QComplex := ((999999629237636352346329332956 : Int)/10^30,(-861118220589122735895683785 : Int)/10^30)
theorem v2152_pa_checked : Scalar.distance (sourceCoefficient 25 53 1 0) v2152_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2152_pb : Scalar.QComplex := ((-371553146503339410652133 : Int)/10^30,(-431477351032269965015852941 : Int)/10^30)
theorem v2152_pb_checked : Scalar.distance (sourceCoefficient 25 53 1 1) v2152_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2152_pg : Scalar.QComplex := ((-93086394306118713485164 : Int)/10^30,(80158419945667638270 : Int)/10^30)
theorem v2152_pg_checked : Scalar.distance (sourceCoefficient 25 53 1 2) v2152_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2152_mb : Scalar.QComplex := ((-743898529079468192110497 : Int)/10^30,(-431476869739901386733443846 : Int)/10^30)
theorem v2152_mb_checked : Scalar.distance (sourceCoefficient 25 53 3 1) v2152_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2152_mg : Scalar.QComplex := ((-93086290472693643038962 : Int)/10^30,(160487755929636640087 : Int)/10^30)
theorem v2152_mg_checked : Scalar.distance (sourceCoefficient 25 53 3 2) v2152_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2152_upper : Scalar.QComplex := ((999996653643728108934578462768 : Int)/10^30,(-2587025578861143077121662163 : Int)/10^30)
theorem v2152_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 53 5) 1) 14) v2152_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2152 : Material (25 : Basis) (53 : Basis) where
  plus := ![v2152_pa,v2152_pb,v2152_pg]
  minus := ![(Primitive.Addresses.material2152 1).one,v2152_mb,v2152_mg]
  upper := v2152_upper
  lower := (Primitive.Addresses.material2152 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2152_pa_checked.trans (by decide +kernel)
    · exact v2152_pb_checked.trans (by decide +kernel)
    · exact v2152_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 53 Primitive.Addresses.material2152
    · exact v2152_mb_checked.trans (by decide +kernel)
    · exact v2152_mg_checked.trans (by decide +kernel)
  upper_error := v2152_upper_checked
  lower_error := reuse_lower_error 25 53 Primitive.Addresses.material2152

def v2153_pa : Scalar.QComplex := ((999999627614835288186177280659 : Int)/10^30,(-863000689891333023141709993 : Int)/10^30)
theorem v2153_pa_checked : Scalar.distance (sourceCoefficient 25 54 1 0) v2153_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2153_pb : Scalar.QComplex := ((-372365389585086493918577 : Int)/10^30,(-431477350230886720994204491 : Int)/10^30)
theorem v2153_pb_checked : Scalar.distance (sourceCoefficient 25 54 1 1) v2153_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2153_pg : Scalar.QComplex := ((-93086394144143616889216 : Int)/10^30,(80333652280952820340 : Int)/10^30)
theorem v2153_pg_checked : Scalar.distance (sourceCoefficient 25 54 1 2) v2153_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2153_mb : Scalar.QComplex := ((-744710771167222408070629 : Int)/10^30,(-431476868237589243626080912 : Int)/10^30)
theorem v2153_mb_checked : Scalar.distance (sourceCoefficient 25 54 3 1) v2153_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2153_mg : Scalar.QComplex := ((-93086290159500993574042 : Int)/10^30,(160662988059897601942 : Int)/10^30)
theorem v2153_mg_checked : Scalar.distance (sourceCoefficient 25 54 3 2) v2153_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2153_upper : Scalar.QComplex := ((999996648771958222412093505577 : Int)/10^30,(-2588908042558829051725368572 : Int)/10^30)
theorem v2153_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 54 5) 1) 14) v2153_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2153 : Material (25 : Basis) (54 : Basis) where
  plus := ![v2153_pa,v2153_pb,v2153_pg]
  minus := ![(Primitive.Addresses.material2153 1).one,v2153_mb,v2153_mg]
  upper := v2153_upper
  lower := (Primitive.Addresses.material2153 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2153_pa_checked.trans (by decide +kernel)
    · exact v2153_pb_checked.trans (by decide +kernel)
    · exact v2153_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 54 Primitive.Addresses.material2153
    · exact v2153_mb_checked.trans (by decide +kernel)
    · exact v2153_mg_checked.trans (by decide +kernel)
  upper_error := v2153_upper_checked
  lower_error := reuse_lower_error 25 54 Primitive.Addresses.material2153

def v2154_pa : Scalar.QComplex := ((999999614255588403478090161901 : Int)/10^30,(-878344280105638726148550644 : Int)/10^30)
theorem v2154_pa_checked : Scalar.distance (sourceCoefficient 25 55 1 0) v2154_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2154_pb : Scalar.QComplex := ((-378985802958057925360033 : Int)/10^30,(-431477343622960284919594309 : Int)/10^30)
theorem v2154_pb_checked : Scalar.distance (sourceCoefficient 25 55 1 1) v2154_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2154_pg : Scalar.QComplex := ((-93086392809568355414185 : Int)/10^30,(81761932219159457080 : Int)/10^30)
theorem v2154_pg_checked : Scalar.distance (sourceCoefficient 25 55 1 2) v2154_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2154_mb : Scalar.QComplex := ((-751331176372768468543013 : Int)/10^30,(-431476855916546699459775431 : Int)/10^30)
theorem v2154_mb_checked : Scalar.distance (sourceCoefficient 25 55 3 1) v2154_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2154_mg : Scalar.QComplex := ((-93086287592384969690521 : Int)/10^30,(162091266314611998455 : Int)/10^30)
theorem v2154_mg_checked : Scalar.distance (sourceCoefficient 25 55 3 2) v2154_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2154_upper : Scalar.QComplex := ((999996608931086484472160285638 : Int)/10^30,(-2604251586863811333645113391 : Int)/10^30)
theorem v2154_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 55 5) 1) 14) v2154_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2154 : Material (25 : Basis) (55 : Basis) where
  plus := ![v2154_pa,v2154_pb,v2154_pg]
  minus := ![(Primitive.Addresses.material2154 1).one,v2154_mb,v2154_mg]
  upper := v2154_upper
  lower := (Primitive.Addresses.material2154 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2154_pa_checked.trans (by decide +kernel)
    · exact v2154_pb_checked.trans (by decide +kernel)
    · exact v2154_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 55 Primitive.Addresses.material2154
    · exact v2154_mb_checked.trans (by decide +kernel)
    · exact v2154_mg_checked.trans (by decide +kernel)
  upper_error := v2154_upper_checked
  lower_error := reuse_lower_error 25 55 Primitive.Addresses.material2154

def v2155_pa : Scalar.QComplex := ((999999611050499266915205622151 : Int)/10^30,(-881985742619718013454983409 : Int)/10^30)
theorem v2155_pa_checked : Scalar.distance (sourceCoefficient 25 56 1 0) v2155_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2155_pb : Scalar.QComplex := ((-380557011955630028681220 : Int)/10^30,(-431477342034828434684241670 : Int)/10^30)
theorem v2155_pb_checked : Scalar.distance (sourceCoefficient 25 56 1 1) v2155_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2155_pg : Scalar.QComplex := ((-93086392489082396481062 : Int)/10^30,(82100902940379086988 : Int)/10^30)
theorem v2155_pg_checked : Scalar.distance (sourceCoefficient 25 56 1 2) v2155_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2155_mb : Scalar.QComplex := ((-752902383414821394319766 : Int)/10^30,(-431476852972532840280110918 : Int)/10^30)
theorem v2155_mb_checked : Scalar.distance (sourceCoefficient 25 56 3 1) v2155_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2155_mg : Scalar.QComplex := ((-93086286979382664350985 : Int)/10^30,(162430236633052388719 : Int)/10^30)
theorem v2155_mg_checked : Scalar.distance (sourceCoefficient 25 56 3 2) v2155_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2155_upper : Scalar.QComplex := ((999996599441168173110916217125 : Int)/10^30,(-2607893038422666876173199226 : Int)/10^30)
theorem v2155_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 56 5) 1) 14) v2155_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2155 : Material (25 : Basis) (56 : Basis) where
  plus := ![v2155_pa,v2155_pb,v2155_pg]
  minus := ![(Primitive.Addresses.material2155 1).one,v2155_mb,v2155_mg]
  upper := v2155_upper
  lower := (Primitive.Addresses.material2155 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2155_pa_checked.trans (by decide +kernel)
    · exact v2155_pb_checked.trans (by decide +kernel)
    · exact v2155_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 56 Primitive.Addresses.material2155
    · exact v2155_mb_checked.trans (by decide +kernel)
    · exact v2155_mg_checked.trans (by decide +kernel)
  upper_error := v2155_upper_checked
  lower_error := reuse_lower_error 25 56 Primitive.Addresses.material2155

def v2156_pa : Scalar.QComplex := ((999999600593238960987617360346 : Int)/10^30,(-893763594331445121211053065 : Int)/10^30)
theorem v2156_pa_checked : Scalar.distance (sourceCoefficient 25 57 1 0) v2156_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2156_pb : Scalar.QComplex := ((-385638889478799528044523 : Int)/10^30,(-431477336845976624580208550 : Int)/10^30)
theorem v2156_pb_checked : Scalar.distance (sourceCoefficient 25 57 1 1) v2156_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2156_pg : Scalar.QComplex := ((-93086391442649627564088 : Int)/10^30,(83197261028674961090 : Int)/10^30)
theorem v2156_pg_checked : Scalar.distance (sourceCoefficient 25 57 1 2) v2156_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2156_mb : Scalar.QComplex := ((-757984254568030223621208 : Int)/10^30,(-431476843398251538994716769 : Int)/10^30)
theorem v2156_mb_checked : Scalar.distance (sourceCoefficient 25 57 3 1) v2156_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2156_mg : Scalar.QComplex := ((-93086284986842633004710 : Int)/10^30,(163526593410099690515 : Int)/10^30)
theorem v2156_mg_checked : Scalar.distance (sourceCoefficient 25 57 3 2) v2156_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2156_upper : Scalar.QComplex := ((999996568656419865963962532748 : Int)/10^30,(-2619670854544384770174329059 : Int)/10^30)
theorem v2156_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 57 5) 1) 14) v2156_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2156 : Material (25 : Basis) (57 : Basis) where
  plus := ![v2156_pa,v2156_pb,v2156_pg]
  minus := ![(Primitive.Addresses.material2156 1).one,v2156_mb,v2156_mg]
  upper := v2156_upper
  lower := (Primitive.Addresses.material2156 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2156_pa_checked.trans (by decide +kernel)
    · exact v2156_pb_checked.trans (by decide +kernel)
    · exact v2156_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 57 Primitive.Addresses.material2156
    · exact v2156_mb_checked.trans (by decide +kernel)
    · exact v2156_mg_checked.trans (by decide +kernel)
  upper_error := v2156_upper_checked
  lower_error := reuse_lower_error 25 57 Primitive.Addresses.material2156

def v2157_pa : Scalar.QComplex := ((999999594861178205574683896115 : Int)/10^30,(-900154142050896584792955085 : Int)/10^30)
theorem v2157_pa_checked : Scalar.distance (sourceCoefficient 25 58 1 0) v2157_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2157_pb : Scalar.QComplex := ((-388396266753025820700850 : Int)/10^30,(-431477333997158007090100951 : Int)/10^30)
theorem v2157_pb_checked : Scalar.distance (sourceCoefficient 25 58 1 1) v2157_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2157_pg : Scalar.QComplex := ((-93086390868560778862215 : Int)/10^30,(83792134256350290316 : Int)/10^30)
theorem v2157_pg_checked : Scalar.distance (sourceCoefficient 25 58 1 2) v2157_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2157_mb : Scalar.QComplex := ((-760741628357156777849847 : Int)/10^30,(-431476838169941582255055769 : Int)/10^30)
theorem v2157_mb_checked : Scalar.distance (sourceCoefficient 25 58 3 1) v2157_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2157_mg : Scalar.QComplex := ((-93086283899405194674148 : Int)/10^30,(164121465920863709600 : Int)/10^30)
theorem v2157_mg_checked : Scalar.distance (sourceCoefficient 25 58 3 2) v2157_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2157_upper : Scalar.QComplex := ((999996551894862029969344681694 : Int)/10^30,(-2626061382852849236748175592 : Int)/10^30)
theorem v2157_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 58 5) 1) 14) v2157_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2157 : Material (25 : Basis) (58 : Basis) where
  plus := ![v2157_pa,v2157_pb,v2157_pg]
  minus := ![(Primitive.Addresses.material2157 1).one,v2157_mb,v2157_mg]
  upper := v2157_upper
  lower := (Primitive.Addresses.material2157 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2157_pa_checked.trans (by decide +kernel)
    · exact v2157_pb_checked.trans (by decide +kernel)
    · exact v2157_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 58 Primitive.Addresses.material2157
    · exact v2157_mb_checked.trans (by decide +kernel)
    · exact v2157_mg_checked.trans (by decide +kernel)
  upper_error := v2157_upper_checked
  lower_error := reuse_lower_error 25 58 Primitive.Addresses.material2157

def v2158_pa : Scalar.QComplex := ((999999578894855404459985045537 : Int)/10^30,(-917720061817075689604354156 : Int)/10^30)
theorem v2158_pa_checked : Scalar.distance (sourceCoefficient 25 59 1 0) v2158_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2158_pb : Scalar.QComplex := ((-395975565078456146069903 : Int)/10^30,(-431477326045462706387021793 : Int)/10^30)
theorem v2158_pb_checked : Scalar.distance (sourceCoefficient 25 59 1 1) v2158_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2158_pg : Scalar.QComplex := ((-93086389267692301236637 : Int)/10^30,(85427282886943262234 : Int)/10^30)
theorem v2158_pg_checked : Scalar.distance (sourceCoefficient 25 59 1 2) v2158_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2158_mb : Scalar.QComplex := ((-768320916998513032170788 : Int)/10^30,(-431476823677656146409915148 : Int)/10^30)
theorem v2158_mb_checked : Scalar.distance (sourceCoefficient 25 59 3 1) v2158_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2158_mg : Scalar.QComplex := ((-93086280887477689283848 : Int)/10^30,(165756612561138720613 : Int)/10^30)
theorem v2158_mg_checked : Scalar.distance (sourceCoefficient 25 59 3 2) v2158_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2158_upper : Scalar.QComplex := ((999996505611379060184706472595 : Int)/10^30,(-2643627248900229586485988285 : Int)/10^30)
theorem v2158_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 59 5) 1) 14) v2158_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2158 : Material (25 : Basis) (59 : Basis) where
  plus := ![v2158_pa,v2158_pb,v2158_pg]
  minus := ![(Primitive.Addresses.material2158 1).one,v2158_mb,v2158_mg]
  upper := v2158_upper
  lower := (Primitive.Addresses.material2158 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2158_pa_checked.trans (by decide +kernel)
    · exact v2158_pb_checked.trans (by decide +kernel)
    · exact v2158_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 59 Primitive.Addresses.material2158
    · exact v2158_mb_checked.trans (by decide +kernel)
    · exact v2158_mg_checked.trans (by decide +kernel)
  upper_error := v2158_upper_checked
  lower_error := reuse_lower_error 25 59 Primitive.Addresses.material2158

def v2159_pa : Scalar.QComplex := ((999999560092926782762008044095 : Int)/10^30,(-937983983294087446197327743 : Int)/10^30)
theorem v2159_pa_checked : Scalar.distance (sourceCoefficient 25 60 1 0) v2159_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2159_pb : Scalar.QComplex := ((-404718990212972218272052 : Int)/10^30,(-431477316651934445773167610 : Int)/10^30)
theorem v2159_pb_checked : Scalar.distance (sourceCoefficient 25 60 1 1) v2159_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2159_pg : Scalar.QComplex := ((-93086387379315977351041 : Int)/10^30,(87313578834368187341 : Int)/10^30)
theorem v2159_pg_checked : Scalar.distance (sourceCoefficient 25 60 1 2) v2159_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2159_mb : Scalar.QComplex := ((-777064330771260512421649 : Int)/10^30,(-431476806738949281598482046 : Int)/10^30)
theorem v2159_mb_checked : Scalar.distance (sourceCoefficient 25 60 3 1) v2159_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2159_mg : Scalar.QComplex := ((-93086277371313621515121 : Int)/10^30,(167642906176625738309 : Int)/10^30)
theorem v2159_mg_checked : Scalar.distance (sourceCoefficient 25 60 3 2) v2159_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2159_upper : Scalar.QComplex := ((999996451835788301024649507089 : Int)/10^30,(-2663891107746087567088005477 : Int)/10^30)
theorem v2159_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 60 5) 1) 14) v2159_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2159 : Material (25 : Basis) (60 : Basis) where
  plus := ![v2159_pa,v2159_pb,v2159_pg]
  minus := ![(Primitive.Addresses.material2159 1).one,v2159_mb,v2159_mg]
  upper := v2159_upper
  lower := (Primitive.Addresses.material2159 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2159_pa_checked.trans (by decide +kernel)
    · exact v2159_pb_checked.trans (by decide +kernel)
    · exact v2159_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 60 Primitive.Addresses.material2159
    · exact v2159_mb_checked.trans (by decide +kernel)
    · exact v2159_mg_checked.trans (by decide +kernel)
  upper_error := v2159_upper_checked
  lower_error := reuse_lower_error 25 60 Primitive.Addresses.material2159

def v2160_pa : Scalar.QComplex := ((999999554579797950966188764812 : Int)/10^30,(-943843316286612917533297949 : Int)/10^30)
theorem v2160_pa_checked : Scalar.distance (sourceCoefficient 25 61 1 0) v2160_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2160_pb : Scalar.QComplex := ((-407247160242148191636806 : Int)/10^30,(-431477313891757030676436621 : Int)/10^30)
theorem v2160_pb_checked : Scalar.distance (sourceCoefficient 25 61 1 1) v2160_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2160_pg : Scalar.QComplex := ((-93086386824978596191443 : Int)/10^30,(87859003176201217339 : Int)/10^30)
theorem v2160_pg_checked : Scalar.distance (sourceCoefficient 25 61 1 2) v2160_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2160_mb : Scalar.QComplex := ((-779592497477174445393463 : Int)/10^30,(-431476801797076023614347281 : Int)/10^30)
theorem v2160_mb_checked : Scalar.distance (sourceCoefficient 25 61 3 1) v2160_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2160_mg : Scalar.QComplex := ((-93086276346299804759220 : Int)/10^30,(168188329837004165207 : Int)/10^30)
theorem v2160_mg_checked : Scalar.distance (sourceCoefficient 25 61 3 2) v2160_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2160_upper : Scalar.QComplex := ((999996436209990489824449796026 : Int)/10^30,(-2669750422496664615121116095 : Int)/10^30)
theorem v2160_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 61 5) 1) 14) v2160_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2160 : Material (25 : Basis) (61 : Basis) where
  plus := ![v2160_pa,v2160_pb,v2160_pg]
  minus := ![(Primitive.Addresses.material2160 1).one,v2160_mb,v2160_mg]
  upper := v2160_upper
  lower := (Primitive.Addresses.material2160 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2160_pa_checked.trans (by decide +kernel)
    · exact v2160_pb_checked.trans (by decide +kernel)
    · exact v2160_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 61 Primitive.Addresses.material2160
    · exact v2160_mb_checked.trans (by decide +kernel)
    · exact v2160_mg_checked.trans (by decide +kernel)
  upper_error := v2160_upper_checked
  lower_error := reuse_lower_error 25 61 Primitive.Addresses.material2160

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
