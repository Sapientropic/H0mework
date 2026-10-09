import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B134

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3217_pa : Scalar.QComplex := ((999999493108956037047580979427 : Int)/10^30,(-1006867335346307869382541370 : Int)/10^30)
theorem v3217_pa_checked : Scalar.distance (sourceCoefficient 42 47 1 0) v3217_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3217_pb : Scalar.QComplex := ((-434440621688057160297133 : Int)/10^30,(-431477302145841197371566169 : Int)/10^30)
theorem v3217_pb_checked : Scalar.distance (sourceCoefficient 42 47 1 1) v3217_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3217_pg : Scalar.QComplex := ((-93086382696903258273326 : Int)/10^30,(93725685611768269163 : Int)/10^30)
theorem v3217_pg_checked : Scalar.distance (sourceCoefficient 42 47 1 2) v3217_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3217_mb : Scalar.QComplex := ((-806785938661518567427127 : Int)/10^30,(-431476766584432084070055939 : Int)/10^30)
theorem v3217_mb_checked : Scalar.distance (sourceCoefficient 42 47 3 1) v3217_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3217_mg : Scalar.QComplex := ((-93086267155543287586232 : Int)/10^30,(174055006525794130625 : Int)/10^30)
theorem v3217_mg_checked : Scalar.distance (sourceCoefficient 42 47 3 2) v3217_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3217_upper : Scalar.QComplex := ((999996265965500726816994274561 : Int)/10^30,(-2732774241596389946681413315 : Int)/10^30)
theorem v3217_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 47 5) 1) 14) v3217_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3217 : Material (42 : Basis) (47 : Basis) where
  plus := ![v3217_pa,v3217_pb,v3217_pg]
  minus := ![(Primitive.Addresses.material3217 1).one,v3217_mb,v3217_mg]
  upper := v3217_upper
  lower := (Primitive.Addresses.material3217 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3217_pa_checked.trans (by decide +kernel)
    · exact v3217_pb_checked.trans (by decide +kernel)
    · exact v3217_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 47 Primitive.Addresses.material3217
    · exact v3217_mb_checked.trans (by decide +kernel)
    · exact v3217_mg_checked.trans (by decide +kernel)
  upper_error := v3217_upper_checked
  lower_error := reuse_lower_error 42 47 Primitive.Addresses.material3217

def v3218_pa : Scalar.QComplex := ((999999465113795474524343496889 : Int)/10^30,(-1034297888882936626743682467 : Int)/10^30)
theorem v3218_pa_checked : Scalar.distance (sourceCoefficient 42 48 1 0) v3218_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3218_pb : Scalar.QComplex := ((-446276288686052208237191 : Int)/10^30,(-431477289836692464013168533 : Int)/10^30)
theorem v3218_pb_checked : Scalar.distance (sourceCoefficient 42 48 1 1) v3218_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3218_pg : Scalar.QComplex := ((-93086380066138175848608 : Int)/10^30,(96279097884522632597 : Int)/10^30)
theorem v3218_pg_checked : Scalar.distance (sourceCoefficient 42 48 1 2) v3218_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3218_mb : Scalar.QComplex := ((-818621590630312901900963 : Int)/10^30,(-431476744061640373354083580 : Int)/10^30)
theorem v3218_mb_checked : Scalar.distance (sourceCoefficient 42 48 3 1) v3218_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3218_mg : Scalar.QComplex := ((-93086262321299394748282 : Int)/10^30,(176608415577564627335 : Int)/10^30)
theorem v3218_mg_checked : Scalar.distance (sourceCoefficient 42 48 3 2) v3218_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3218_upper : Scalar.QComplex := ((999996190627734935953537924431 : Int)/10^30,(-2760204705961324000613051572 : Int)/10^30)
theorem v3218_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 48 5) 1) 14) v3218_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3218 : Material (42 : Basis) (48 : Basis) where
  plus := ![v3218_pa,v3218_pb,v3218_pg]
  minus := ![(Primitive.Addresses.material3218 1).one,v3218_mb,v3218_mg]
  upper := v3218_upper
  lower := (Primitive.Addresses.material3218 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3218_pa_checked.trans (by decide +kernel)
    · exact v3218_pb_checked.trans (by decide +kernel)
    · exact v3218_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 48 Primitive.Addresses.material3218
    · exact v3218_mb_checked.trans (by decide +kernel)
    · exact v3218_mg_checked.trans (by decide +kernel)
  upper_error := v3218_upper_checked
  lower_error := reuse_lower_error 42 48 Primitive.Addresses.material3218

def v3219_pa : Scalar.QComplex := ((999999442076696306748609530326 : Int)/10^30,(-1056336260907524643773813787 : Int)/10^30)
theorem v3219_pa_checked : Scalar.distance (sourceCoefficient 42 49 1 0) v3219_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3219_pb : Scalar.QComplex := ((-455785350527998552396118 : Int)/10^30,(-431477279633621349259134026 : Int)/10^30)
theorem v3219_pb_checked : Scalar.distance (sourceCoefficient 42 49 1 1) v3219_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3219_pg : Scalar.QComplex := ((-93086377893318508728445 : Int)/10^30,(98330571226170086986 : Int)/10^30)
theorem v3219_pg_checked : Scalar.distance (sourceCoefficient 42 49 1 2) v3219_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3219_mb : Scalar.QComplex := ((-828130640126810093939874 : Int)/10^30,(-431476725652680960317181619 : Int)/10^30)
theorem v3219_mb_checked : Scalar.distance (sourceCoefficient 42 49 3 1) v3219_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3219_mg : Scalar.QComplex := ((-93086258378151437755877 : Int)/10^30,(178659886280309287106 : Int)/10^30)
theorem v3219_mg_checked : Scalar.distance (sourceCoefficient 42 49 3 2) v3219_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3219_upper : Scalar.QComplex := ((999996129554439270284322396313 : Int)/10^30,(-2782243005402402441781363711 : Int)/10^30)
theorem v3219_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 49 5) 1) 14) v3219_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3219 : Material (42 : Basis) (49 : Basis) where
  plus := ![v3219_pa,v3219_pb,v3219_pg]
  minus := ![(Primitive.Addresses.material3219 1).one,v3219_mb,v3219_mg]
  upper := v3219_upper
  lower := (Primitive.Addresses.material3219 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3219_pa_checked.trans (by decide +kernel)
    · exact v3219_pb_checked.trans (by decide +kernel)
    · exact v3219_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 49 Primitive.Addresses.material3219
    · exact v3219_mb_checked.trans (by decide +kernel)
    · exact v3219_mg_checked.trans (by decide +kernel)
  upper_error := v3219_upper_checked
  lower_error := reuse_lower_error 42 49 Primitive.Addresses.material3219

def v3220_pa : Scalar.QComplex := ((999999439353017464026612077860 : Int)/10^30,(-1058911540567439348536254664 : Int)/10^30)
theorem v3220_pa_checked : Scalar.distance (sourceCoefficient 42 50 1 0) v3220_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3220_pb : Scalar.QComplex := ((-456896525772524832590764 : Int)/10^30,(-431477278423114683667070426 : Int)/10^30)
theorem v3220_pb_checked : Scalar.distance (sourceCoefficient 42 50 1 1) v3220_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3220_pg : Scalar.QComplex := ((-93086377635973129051716 : Int)/10^30,(98570294811489092709 : Int)/10^30)
theorem v3220_pg_checked : Scalar.distance (sourceCoefficient 42 50 1 2) v3220_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3220_mb : Scalar.QComplex := ((-829241813912982314170389 : Int)/10^30,(-431476723483280554901130796 : Int)/10^30)
theorem v3220_mb_checked : Scalar.distance (sourceCoefficient 42 50 3 1) v3220_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3220_mg : Scalar.QComplex := ((-93086257913935496519781 : Int)/10^30,(178899609554290773850 : Int)/10^30)
theorem v3220_mg_checked : Scalar.distance (sourceCoefficient 42 50 3 2) v3220_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3220_upper : Scalar.QComplex := ((999996122386065418694984194046 : Int)/10^30,(-2784818276525918014376408050 : Int)/10^30)
theorem v3220_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 50 5) 1) 14) v3220_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3220 : Material (42 : Basis) (50 : Basis) where
  plus := ![v3220_pa,v3220_pb,v3220_pg]
  minus := ![(Primitive.Addresses.material3220 1).one,v3220_mb,v3220_mg]
  upper := v3220_upper
  lower := (Primitive.Addresses.material3220 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3220_pa_checked.trans (by decide +kernel)
    · exact v3220_pb_checked.trans (by decide +kernel)
    · exact v3220_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 50 Primitive.Addresses.material3220
    · exact v3220_mb_checked.trans (by decide +kernel)
    · exact v3220_mg_checked.trans (by decide +kernel)
  upper_error := v3220_upper_checked
  lower_error := reuse_lower_error 42 50 Primitive.Addresses.material3220

def v3221_pa : Scalar.QComplex := ((999999427324274202910474894981 : Int)/10^30,(-1070210784675940430688966651 : Int)/10^30)
theorem v3221_pa_checked : Scalar.distance (sourceCoefficient 42 51 1 0) v3221_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3221_pb : Scalar.QComplex := ((-461771895424236984910594 : Int)/10^30,(-431477273066824830601468354 : Int)/10^30)
theorem v3221_pb_checked : Scalar.distance (sourceCoefficient 42 51 1 1) v3221_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3221_pg : Scalar.QComplex := ((-93086376498337052267839 : Int)/10^30,(99622101086084361730 : Int)/10^30)
theorem v3221_pg_checked : Scalar.distance (sourceCoefficient 42 51 1 2) v3221_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3221_mb : Scalar.QComplex := ((-834117177127134624901577 : Int)/10^30,(-431476713919768265297424231 : Int)/10^30)
theorem v3221_mb_checked : Scalar.distance (sourceCoefficient 42 51 3 1) v3221_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3221_mg : Scalar.QComplex := ((-93086255868638399950183 : Int)/10^30,(179951414455521799880 : Int)/10^30)
theorem v3221_mg_checked : Scalar.distance (sourceCoefficient 42 51 3 2) v3221_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3221_upper : Scalar.QComplex := ((999996090855869801124269679412 : Int)/10^30,(-2796117483045002669745558456 : Int)/10^30)
theorem v3221_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 51 5) 1) 14) v3221_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3221 : Material (42 : Basis) (51 : Basis) where
  plus := ![v3221_pa,v3221_pb,v3221_pg]
  minus := ![(Primitive.Addresses.material3221 1).one,v3221_mb,v3221_mg]
  upper := v3221_upper
  lower := (Primitive.Addresses.material3221 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3221_pa_checked.trans (by decide +kernel)
    · exact v3221_pb_checked.trans (by decide +kernel)
    · exact v3221_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 51 Primitive.Addresses.material3221
    · exact v3221_mb_checked.trans (by decide +kernel)
    · exact v3221_mg_checked.trans (by decide +kernel)
  upper_error := v3221_upper_checked
  lower_error := reuse_lower_error 42 51 Primitive.Addresses.material3221

def v3222_pa : Scalar.QComplex := ((999999401144466138412226925803 : Int)/10^30,(-1094399702620219606527460927 : Int)/10^30)
theorem v3222_pa_checked : Scalar.distance (sourceCoefficient 42 52 1 0) v3222_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3222_pb : Scalar.QComplex := ((-472208869297433475266915 : Int)/10^30,(-431477261353391981016383683 : Int)/10^30)
theorem v3222_pb_checked : Scalar.distance (sourceCoefficient 42 52 1 1) v3222_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3222_pg : Scalar.QComplex := ((-93086374016323817714095 : Int)/10^30,(101873761049124883069 : Int)/10^30)
theorem v3222_pg_checked : Scalar.distance (sourceCoefficient 42 52 1 2) v3222_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3222_mb : Scalar.QComplex := ((-844554137006003753236807 : Int)/10^30,(-431476693199701388443806907 : Int)/10^30)
theorem v3222_mb_checked : Scalar.distance (sourceCoefficient 42 52 3 1) v3222_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3222_mg : Scalar.QComplex := ((-93086251443544952459612 : Int)/10^30,(182203071438300775341 : Int)/10^30)
theorem v3222_mg_checked : Scalar.distance (sourceCoefficient 42 52 3 2) v3222_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3222_upper : Scalar.QComplex := ((999996022928222758043161244607 : Int)/10^30,(-2820306319778756291792566368 : Int)/10^30)
theorem v3222_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 52 5) 1) 14) v3222_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3222 : Material (42 : Basis) (52 : Basis) where
  plus := ![v3222_pa,v3222_pb,v3222_pg]
  minus := ![(Primitive.Addresses.material3222 1).one,v3222_mb,v3222_mg]
  upper := v3222_upper
  lower := (Primitive.Addresses.material3222 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3222_pa_checked.trans (by decide +kernel)
    · exact v3222_pb_checked.trans (by decide +kernel)
    · exact v3222_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 52 Primitive.Addresses.material3222
    · exact v3222_mb_checked.trans (by decide +kernel)
    · exact v3222_mg_checked.trans (by decide +kernel)
  upper_error := v3222_upper_checked
  lower_error := reuse_lower_error 42 52 Primitive.Addresses.material3222

def v3223_pa : Scalar.QComplex := ((999999397085388485239713551733 : Int)/10^30,(-1098102390273098255813665630 : Int)/10^30)
theorem v3223_pa_checked : Scalar.distance (sourceCoefficient 42 53 1 0) v3223_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3223_pb : Scalar.QComplex := ((-473806495703969904162078 : Int)/10^30,(-431477259530666285711334405 : Int)/10^30)
theorem v3223_pb_checked : Scalar.distance (sourceCoefficient 42 53 1 1) v3223_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3223_pg : Scalar.QComplex := ((-93086373630784993807142 : Int)/10^30,(102218431014805330494 : Int)/10^30)
theorem v3223_pg_checked : Scalar.distance (sourceCoefficient 42 53 1 2) v3223_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3223_mb : Scalar.QComplex := ((-846151761244740673314299 : Int)/10^30,(-431476689998296737404175225 : Int)/10^30)
theorem v3223_mb_checked : Scalar.distance (sourceCoefficient 42 53 3 1) v3223_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3223_mg : Scalar.QComplex := ((-93086250760571615083157 : Int)/10^30,(182547740942942201341 : Int)/10^30)
theorem v3223_mg_checked : Scalar.distance (sourceCoefficient 42 53 3 2) v3223_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3223_upper : Scalar.QComplex := ((999996012478648166721372574883 : Int)/10^30,(-2824008994911316837633608765 : Int)/10^30)
theorem v3223_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 53 5) 1) 14) v3223_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3223 : Material (42 : Basis) (53 : Basis) where
  plus := ![v3223_pa,v3223_pb,v3223_pg]
  minus := ![(Primitive.Addresses.material3223 1).one,v3223_mb,v3223_mg]
  upper := v3223_upper
  lower := (Primitive.Addresses.material3223 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3223_pa_checked.trans (by decide +kernel)
    · exact v3223_pb_checked.trans (by decide +kernel)
    · exact v3223_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 53 Primitive.Addresses.material3223
    · exact v3223_mb_checked.trans (by decide +kernel)
    · exact v3223_mg_checked.trans (by decide +kernel)
  upper_error := v3223_upper_checked
  lower_error := reuse_lower_error 42 53 Primitive.Addresses.material3223

def v3224_pa : Scalar.QComplex := ((999999395016471831186568052407 : Int)/10^30,(-1099984859137869001018087266 : Int)/10^30)
theorem v3224_pa_checked : Scalar.distance (sourceCoefficient 42 54 1 0) v3224_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3224_pb : Scalar.QComplex := ((-474618738659886769598728 : Int)/10^30,(-431477258600957144177457147 : Int)/10^30)
theorem v3224_pb_checked : Scalar.distance (sourceCoefficient 42 54 1 1) v3224_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3224_pg : Scalar.QComplex := ((-93086373434203807723865 : Int)/10^30,(102393663316157441669 : Int)/10^30)
theorem v3224_pg_checked : Scalar.distance (sourceCoefficient 42 54 1 2) v3224_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3224_mb : Scalar.QComplex := ((-846964003095925248327800 : Int)/10^30,(-431476688367658853151990714 : Int)/10^30)
theorem v3224_mb_checked : Scalar.distance (sourceCoefficient 42 54 3 1) v3224_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3224_mg : Scalar.QComplex := ((-93086250412772918299049 : Int)/10^30,(182722973009406608308 : Int)/10^30)
theorem v3224_mg_checked : Scalar.distance (sourceCoefficient 42 54 3 2) v3224_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3224_upper : Scalar.QComplex := ((999996007160764109723626256431 : Int)/10^30,(-2825891457401608884845387250 : Int)/10^30)
theorem v3224_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 54 5) 1) 14) v3224_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3224 : Material (42 : Basis) (54 : Basis) where
  plus := ![v3224_pa,v3224_pb,v3224_pg]
  minus := ![(Primitive.Addresses.material3224 1).one,v3224_mb,v3224_mg]
  upper := v3224_upper
  lower := (Primitive.Addresses.material3224 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3224_pa_checked.trans (by decide +kernel)
    · exact v3224_pb_checked.trans (by decide +kernel)
    · exact v3224_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 54 Primitive.Addresses.material3224
    · exact v3224_mb_checked.trans (by decide +kernel)
    · exact v3224_mg_checked.trans (by decide +kernel)
  upper_error := v3224_upper_checked
  lower_error := reuse_lower_error 42 54 Primitive.Addresses.material3224

def v3225_pa : Scalar.QComplex := ((999999378021035615524473493209 : Int)/10^30,(-1115328445755383267687709279 : Int)/10^30)
theorem v3225_pa_checked : Scalar.distance (sourceCoefficient 42 55 1 0) v3225_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3225_pb : Scalar.QComplex := ((-481239150998235113220060 : Int)/10^30,(-431477250947074750093217091 : Int)/10^30)
theorem v3225_pb_checked : Scalar.distance (sourceCoefficient 42 55 1 1) v3225_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3225_pg : Scalar.QComplex := ((-93086371817561978308120 : Int)/10^30,(103821942975353684873 : Int)/10^30)
theorem v3225_pg_checked : Scalar.distance (sourceCoefficient 42 55 1 2) v3225_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3225_mb : Scalar.QComplex := ((-853584406364235722562824 : Int)/10^30,(-431476675000661633266388169 : Int)/10^30)
theorem v3225_mb_checked : Scalar.distance (sourceCoefficient 42 55 3 1) v3225_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3225_mg : Scalar.QComplex := ((-93086247563590672274491 : Int)/10^30,(184151250741699970848 : Int)/10^30)
theorem v3225_mg_checked : Scalar.distance (sourceCoefficient 42 55 3 2) v3225_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3225_upper : Scalar.QComplex := ((999995963683714664242277996345 : Int)/10^30,(-2841234991834072174718913650 : Int)/10^30)
theorem v3225_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 55 5) 1) 14) v3225_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3225 : Material (42 : Basis) (55 : Basis) where
  plus := ![v3225_pa,v3225_pb,v3225_pg]
  minus := ![(Primitive.Addresses.material3225 1).one,v3225_mb,v3225_mg]
  upper := v3225_upper
  lower := (Primitive.Addresses.material3225 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3225_pa_checked.trans (by decide +kernel)
    · exact v3225_pb_checked.trans (by decide +kernel)
    · exact v3225_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 55 Primitive.Addresses.material3225
    · exact v3225_mb_checked.trans (by decide +kernel)
    · exact v3225_mg_checked.trans (by decide +kernel)
  upper_error := v3225_upper_checked
  lower_error := reuse_lower_error 42 55 Primitive.Addresses.material3225

def v3226_pa : Scalar.QComplex := ((999999373952977190618286741585 : Int)/10^30,(-1118969907407651717509567760 : Int)/10^30)
theorem v3226_pa_checked : Scalar.distance (sourceCoefficient 42 56 1 0) v3226_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3226_pb : Scalar.QComplex := ((-482810359747905884164621 : Int)/10^30,(-431477249110708337212960796 : Int)/10^30)
theorem v3226_pb_checked : Scalar.distance (sourceCoefficient 42 56 1 1) v3226_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3226_pg : Scalar.QComplex := ((-93086371430133744599890 : Int)/10^30,(104160913629720903375 : Int)/10^30)
theorem v3226_pg_checked : Scalar.distance (sourceCoefficient 42 56 1 2) v3226_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3226_mb : Scalar.QComplex := ((-855155612944172160775072 : Int)/10^30,(-431476671808413517798577333 : Int)/10^30)
theorem v3226_mb_checked : Scalar.distance (sourceCoefficient 42 56 3 1) v3226_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3226_mg : Scalar.QComplex := ((-93086246883646174776137 : Int)/10^30,(184490220935519806434 : Int)/10^30)
theorem v3226_mg_checked : Scalar.distance (sourceCoefficient 42 56 3 2) v3226_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3226_upper : Scalar.QComplex := ((999995953330829837236437839669 : Int)/10^30,(-2844876441041711459610179108 : Int)/10^30)
theorem v3226_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 56 5) 1) 14) v3226_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3226 : Material (42 : Basis) (56 : Basis) where
  plus := ![v3226_pa,v3226_pb,v3226_pg]
  minus := ![(Primitive.Addresses.material3226 1).one,v3226_mb,v3226_mg]
  upper := v3226_upper
  lower := (Primitive.Addresses.material3226 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3226_pa_checked.trans (by decide +kernel)
    · exact v3226_pb_checked.trans (by decide +kernel)
    · exact v3226_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 56 Primitive.Addresses.material3226
    · exact v3226_mb_checked.trans (by decide +kernel)
    · exact v3226_mg_checked.trans (by decide +kernel)
  upper_error := v3226_upper_checked
  lower_error := reuse_lower_error 42 56 Primitive.Addresses.material3226

def v3227_pa : Scalar.QComplex := ((999999360704551450116165379158 : Int)/10^30,(-1130747756310441295515664178 : Int)/10^30)
theorem v3227_pa_checked : Scalar.distance (sourceCoefficient 42 57 1 0) v3227_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3227_pb : Scalar.QComplex := ((-487892236463079793770588 : Int)/10^30,(-431477243118973110533965162 : Int)/10^30)
theorem v3227_pb_checked : Scalar.distance (sourceCoefficient 42 57 1 1) v3227_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3227_pg : Scalar.QComplex := ((-93086370167184622273931 : Int)/10^30,(105257271500121806631 : Int)/10^30)
theorem v3227_pg_checked : Scalar.distance (sourceCoefficient 42 57 1 2) v3227_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3227_mb : Scalar.QComplex := ((-860237482596533473195413 : Int)/10^30,(-431476661431249796152213436 : Int)/10^30)
theorem v3227_mb_checked : Scalar.distance (sourceCoefficient 42 57 3 1) v3227_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3227_mg : Scalar.QComplex := ((-93086244674590058673357 : Int)/10^30,(185586577307828357060 : Int)/10^30)
theorem v3227_mg_checked : Scalar.distance (sourceCoefficient 42 57 3 2) v3227_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3227_upper : Scalar.QComplex := ((999995919754925100599344055985 : Int)/10^30,(-2856654249537197679918417860 : Int)/10^30)
theorem v3227_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 57 5) 1) 14) v3227_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3227 : Material (42 : Basis) (57 : Basis) where
  plus := ![v3227_pa,v3227_pb,v3227_pg]
  minus := ![(Primitive.Addresses.material3227 1).one,v3227_mb,v3227_mg]
  upper := v3227_upper
  lower := (Primitive.Addresses.material3227 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3227_pa_checked.trans (by decide +kernel)
    · exact v3227_pb_checked.trans (by decide +kernel)
    · exact v3227_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 57 Primitive.Addresses.material3227
    · exact v3227_mb_checked.trans (by decide +kernel)
    · exact v3227_mg_checked.trans (by decide +kernel)
  upper_error := v3227_upper_checked
  lower_error := reuse_lower_error 42 57 Primitive.Addresses.material3227

def v3228_pa : Scalar.QComplex := ((999999353458031494510395052456 : Int)/10^30,(-1137138302492032923669595730 : Int)/10^30)
theorem v3228_pa_checked : Scalar.distance (sourceCoefficient 42 58 1 0) v3228_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3228_pb : Scalar.QComplex := ((-490649613294938126693148 : Int)/10^30,(-431477239834517765380787205 : Int)/10^30)
theorem v3228_pb_checked : Scalar.distance (sourceCoefficient 42 58 1 1) v3228_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3228_pg : Scalar.QComplex := ((-93086369475616107462440 : Int)/10^30,(105852144608502235079 : Int)/10^30)
theorem v3228_pg_checked : Scalar.distance (sourceCoefficient 42 58 1 2) v3228_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3228_mb : Scalar.QComplex := ((-862994855567357356780734 : Int)/10^30,(-431476655767303655700571106 : Int)/10^30)
theorem v3228_mb_checked : Scalar.distance (sourceCoefficient 42 58 3 1) v3228_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3228_mg : Scalar.QComplex := ((-93086243469673100922352 : Int)/10^30,(186181449597917859022 : Int)/10^30)
theorem v3228_mg_checked : Scalar.distance (sourceCoefficient 42 58 3 2) v3228_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3228_upper : Scalar.QComplex := ((999995901478912974227529549407 : Int)/10^30,(-2863044773693985412658437178 : Int)/10^30)
theorem v3228_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 58 5) 1) 14) v3228_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3228 : Material (42 : Basis) (58 : Basis) where
  plus := ![v3228_pa,v3228_pb,v3228_pg]
  minus := ![(Primitive.Addresses.material3228 1).one,v3228_mb,v3228_mg]
  upper := v3228_upper
  lower := (Primitive.Addresses.material3228 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3228_pa_checked.trans (by decide +kernel)
    · exact v3228_pb_checked.trans (by decide +kernel)
    · exact v3228_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 58 Primitive.Addresses.material3228
    · exact v3228_mb_checked.trans (by decide +kernel)
    · exact v3228_mg_checked.trans (by decide +kernel)
  upper_error := v3228_upper_checked
  lower_error := reuse_lower_error 42 58 Primitive.Addresses.material3228

def v3229_pa : Scalar.QComplex := ((999999333328862263033008169621 : Int)/10^30,(-1154704217981179841917919117 : Int)/10^30)
theorem v3229_pa_checked : Scalar.distance (sourceCoefficient 42 59 1 0) v3229_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3229_pb : Scalar.QComplex := ((-498228910390072974435051 : Int)/10^30,(-431477230685372711547541912 : Int)/10^30)
theorem v3229_pb_checked : Scalar.distance (sourceCoefficient 42 59 1 1) v3229_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3229_pg : Scalar.QComplex := ((-93086367551827204886788 : Int)/10^30,(107487292907317161725 : Int)/10^30)
theorem v3229_pg_checked : Scalar.distance (sourceCoefficient 42 59 1 2) v3229_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3229_mb : Scalar.QComplex := ((-870574141945073385753290 : Int)/10^30,(-431476640077569974280120338 : Int)/10^30)
theorem v3229_mb_checked : Scalar.distance (sourceCoefficient 42 59 3 1) v3229_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3229_mg : Scalar.QComplex := ((-93086240134825577129521 : Int)/10^30,(187816595627749165362 : Int)/10^30)
theorem v3229_mg_checked : Scalar.distance (sourceCoefficient 42 59 3 2) v3229_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3229_upper : Scalar.QComplex := ((999995851032597155920503719894 : Int)/10^30,(-2880610628279644657642319898 : Int)/10^30)
theorem v3229_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 59 5) 1) 14) v3229_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3229 : Material (42 : Basis) (59 : Basis) where
  plus := ![v3229_pa,v3229_pb,v3229_pg]
  minus := ![(Primitive.Addresses.material3229 1).one,v3229_mb,v3229_mg]
  upper := v3229_upper
  lower := (Primitive.Addresses.material3229 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3229_pa_checked.trans (by decide +kernel)
    · exact v3229_pb_checked.trans (by decide +kernel)
    · exact v3229_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 59 Primitive.Addresses.material3229
    · exact v3229_mb_checked.trans (by decide +kernel)
    · exact v3229_mg_checked.trans (by decide +kernel)
  upper_error := v3229_upper_checked
  lower_error := reuse_lower_error 42 59 Primitive.Addresses.material3229

def v3230_pa : Scalar.QComplex := ((999999309724703293051188169843 : Int)/10^30,(-1174968134433403423520530269 : Int)/10^30)
theorem v3230_pa_checked : Scalar.distance (sourceCoefficient 42 60 1 0) v3230_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3230_pb : Scalar.QComplex := ((-506972334079200307238541 : Int)/10^30,(-431477219910474843757636493 : Int)/10^30)
theorem v3230_pb_checked : Scalar.distance (sourceCoefficient 42 60 1 1) v3230_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3230_pg : Scalar.QComplex := ((-93086365290932151420423 : Int)/10^30,(109373588464959096029 : Int)/10^30)
theorem v3230_pg_checked : Scalar.distance (sourceCoefficient 42 60 1 2) v3230_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3230_mb : Scalar.QComplex := ((-879317553080372908374437 : Int)/10^30,(-431476621757495263945056670 : Int)/10^30)
theorem v3230_mb_checked : Scalar.distance (sourceCoefficient 42 60 3 1) v3230_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3230_mg : Scalar.QComplex := ((-93086236246143254850939 : Int)/10^30,(189702888531986451382 : Int)/10^30)
theorem v3230_mg_checked : Scalar.distance (sourceCoefficient 42 60 3 2) v3230_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3230_upper : Scalar.QComplex := ((999995792454791873163142732586 : Int)/10^30,(-2900874473812508020881841930 : Int)/10^30)
theorem v3230_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 60 5) 1) 14) v3230_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3230 : Material (42 : Basis) (60 : Basis) where
  plus := ![v3230_pa,v3230_pb,v3230_pg]
  minus := ![(Primitive.Addresses.material3230 1).one,v3230_mb,v3230_mg]
  upper := v3230_upper
  lower := (Primitive.Addresses.material3230 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3230_pa_checked.trans (by decide +kernel)
    · exact v3230_pb_checked.trans (by decide +kernel)
    · exact v3230_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 60 Primitive.Addresses.material3230
    · exact v3230_mb_checked.trans (by decide +kernel)
    · exact v3230_mg_checked.trans (by decide +kernel)
  upper_error := v3230_upper_checked
  lower_error := reuse_lower_error 42 60 Primitive.Addresses.material3230

def v3231_pa : Scalar.QComplex := ((999999302823004795419546331963 : Int)/10^30,(-1180827465954869405470976472 : Int)/10^30)
theorem v3231_pa_checked : Scalar.distance (sourceCoefficient 42 61 1 0) v3231_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3231_pb : Scalar.QComplex := ((-509500503685223553542138 : Int)/10^30,(-431477216750873037683395319 : Int)/10^30)
theorem v3231_pb_checked : Scalar.distance (sourceCoefficient 42 61 1 1) v3231_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3231_pg : Scalar.QComplex := ((-93086364628880610365971 : Int)/10^30,(109919012692679063513 : Int)/10^30)
theorem v3231_pg_checked : Scalar.distance (sourceCoefficient 42 61 1 2) v3231_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3231_mb : Scalar.QComplex := ((-881845719018449011837375 : Int)/10^30,(-431476616416198128869112441 : Int)/10^30)
theorem v3231_mb_checked : Scalar.distance (sourceCoefficient 42 61 3 1) v3231_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3231_mg : Scalar.QComplex := ((-93086235113415416781521 : Int)/10^30,(190248311985299389532 : Int)/10^30)
theorem v3231_mg_checked : Scalar.distance (sourceCoefficient 42 61 3 2) v3231_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3231_upper : Scalar.QComplex := ((999995775440429003153750079400 : Int)/10^30,(-2906733784695482497323166013 : Int)/10^30)
theorem v3231_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 61 5) 1) 14) v3231_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3231 : Material (42 : Basis) (61 : Basis) where
  plus := ![v3231_pa,v3231_pb,v3231_pg]
  minus := ![(Primitive.Addresses.material3231 1).one,v3231_mb,v3231_mg]
  upper := v3231_upper
  lower := (Primitive.Addresses.material3231 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3231_pa_checked.trans (by decide +kernel)
    · exact v3231_pb_checked.trans (by decide +kernel)
    · exact v3231_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 61 Primitive.Addresses.material3231
    · exact v3231_mb_checked.trans (by decide +kernel)
    · exact v3231_mg_checked.trans (by decide +kernel)
  upper_error := v3231_upper_checked
  lower_error := reuse_lower_error 42 61 Primitive.Addresses.material3231

def v3232_pa : Scalar.QComplex := ((999999292733952999068632136126 : Int)/10^30,(-1189340823219568754496489529 : Int)/10^30)
theorem v3232_pa_checked : Scalar.distance (sourceCoefficient 42 62 1 0) v3232_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3232_pb : Scalar.QComplex := ((-513173825619548174205403 : Int)/10^30,(-431477212124910127517251327 : Int)/10^30)
theorem v3232_pb_checked : Scalar.distance (sourceCoefficient 42 62 1 1) v3232_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3232_pg : Scalar.QComplex := ((-93086363660303928802263 : Int)/10^30,(110711490688740401047 : Int)/10^30)
theorem v3232_pg_checked : Scalar.distance (sourceCoefficient 42 62 1 2) v3232_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3232_mb : Scalar.QComplex := ((-885519035593030351407727 : Int)/10^30,(-431476608620325552116719384 : Int)/10^30)
theorem v3232_mb_checked : Scalar.distance (sourceCoefficient 42 62 3 1) v3232_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3232_mg : Scalar.QComplex := ((-93086233460966277146242 : Int)/10^30,(191040788850446897984 : Int)/10^30)
theorem v3232_mg_checked : Scalar.distance (sourceCoefficient 42 62 3 2) v3232_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3232_upper : Scalar.QComplex := ((999995750658109920127242799907 : Int)/10^30,(-2915247111867748120900512087 : Int)/10^30)
theorem v3232_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 62 5) 1) 14) v3232_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3232 : Material (42 : Basis) (62 : Basis) where
  plus := ![v3232_pa,v3232_pb,v3232_pg]
  minus := ![(Primitive.Addresses.material3232 1).one,v3232_mb,v3232_mg]
  upper := v3232_upper
  lower := (Primitive.Addresses.material3232 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3232_pa_checked.trans (by decide +kernel)
    · exact v3232_pb_checked.trans (by decide +kernel)
    · exact v3232_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 62 Primitive.Addresses.material3232
    · exact v3232_mb_checked.trans (by decide +kernel)
    · exact v3232_mg_checked.trans (by decide +kernel)
  upper_error := v3232_upper_checked
  lower_error := reuse_lower_error 42 62 Primitive.Addresses.material3232

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
