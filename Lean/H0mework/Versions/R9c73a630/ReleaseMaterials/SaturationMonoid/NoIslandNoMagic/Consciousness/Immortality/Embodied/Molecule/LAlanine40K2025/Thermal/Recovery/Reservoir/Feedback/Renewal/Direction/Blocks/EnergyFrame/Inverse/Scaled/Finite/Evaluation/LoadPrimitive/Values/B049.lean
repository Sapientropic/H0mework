import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B032
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B033

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v785_pa : Scalar.QComplex := ((999999917813214566060228802969 : Int)/10^30,(-405430097690356287181381526 : Int)/10^30)
theorem v785_pa_checked : Scalar.distance (sourceCoefficient 8 46 1 0) v785_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v785_pb : Scalar.QComplex := ((-174933961618739259613168 : Int)/10^30,(-431477456257042792362575896 : Int)/10^30)
theorem v785_pb_checked : Scalar.distance (sourceCoefficient 8 46 1 1) v785_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v785_pg : Scalar.QComplex := ((-93086419087885439739822 : Int)/10^30,(37740039086179334671 : Int)/10^30)
theorem v785_pg_checked : Scalar.distance (sourceCoefficient 8 46 1 2) v785_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v785_mb : Scalar.QComplex := ((-547279508209416316429385 : Int)/10^30,(-431477144638136190138837654 : Int)/10^30)
theorem v785_mb_checked : Scalar.distance (sourceCoefficient 8 46 3 1) v785_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v785_mg : Scalar.QComplex := ((-93086351859603370693127 : Int)/10^30,(118069412249998701668 : Int)/10^30)
theorem v785_mg_checked : Scalar.distance (sourceCoefficient 8 46 3 2) v785_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v785_upper : Scalar.QComplex := ((999997728695236942912754255039 : Int)/10^30,(-2131338632711575423921736505 : Int)/10^30)
theorem v785_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 46 5) 1) 14) v785_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material785 : Material (8 : Basis) (46 : Basis) where
  plus := ![v785_pa,v785_pb,v785_pg]
  minus := ![(Primitive.Addresses.material785 1).one,v785_mb,v785_mg]
  upper := v785_upper
  lower := (Primitive.Addresses.material785 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v785_pa_checked.trans (by decide +kernel)
    · exact v785_pb_checked.trans (by decide +kernel)
    · exact v785_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 46 Primitive.Addresses.material785
    · exact v785_mb_checked.trans (by decide +kernel)
    · exact v785_mg_checked.trans (by decide +kernel)
  upper_error := v785_upper_checked
  lower_error := reuse_lower_error 8 46 Primitive.Addresses.material785

def v786_pa : Scalar.QComplex := ((999999916208859438538893238674 : Int)/10^30,(-409368140067063568903555998 : Int)/10^30)
theorem v786_pa_checked : Scalar.distance (sourceCoefficient 8 47 1 0) v786_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v786_pb : Scalar.QComplex := ((-176633138117312495704278 : Int)/10^30,(-431477455202263600331196194 : Int)/10^30)
theorem v786_pb_checked : Scalar.distance (sourceCoefficient 8 47 1 1) v786_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v786_pg : Scalar.QComplex := ((-93086418899435210975040 : Int)/10^30,(38106617363362278651 : Int)/10^30)
theorem v786_pg_checked : Scalar.distance (sourceCoefficient 8 47 1 2) v786_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v786_mb : Scalar.QComplex := ((-548978683165081548667642 : Int)/10^30,(-431477142117044600649894484 : Int)/10^30)
theorem v786_mb_checked : Scalar.distance (sourceCoefficient 8 47 3 1) v786_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v786_mg : Scalar.QComplex := ((-93086351354812668960818 : Int)/10^30,(118435990228063739656 : Int)/10^30)
theorem v786_mg_checked : Scalar.distance (sourceCoefficient 8 47 3 2) v786_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v786_upper : Scalar.QComplex := ((999997720294180319106833021284 : Int)/10^30,(-2135276666454059776349906893 : Int)/10^30)
theorem v786_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 47 5) 1) 14) v786_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material786 : Material (8 : Basis) (47 : Basis) where
  plus := ![v786_pa,v786_pb,v786_pg]
  minus := ![(Primitive.Addresses.material786 1).one,v786_mb,v786_mg]
  upper := v786_upper
  lower := (Primitive.Addresses.material786 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v786_pa_checked.trans (by decide +kernel)
    · exact v786_pb_checked.trans (by decide +kernel)
    · exact v786_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 47 Primitive.Addresses.material786
    · exact v786_mb_checked.trans (by decide +kernel)
    · exact v786_mg_checked.trans (by decide +kernel)
  upper_error := v786_upper_checked
  lower_error := reuse_lower_error 8 47 Primitive.Addresses.material786

def v787_pa : Scalar.QComplex := ((999999904603440915184965564137 : Int)/10^30,(-436798705434352888546748770 : Int)/10^30)
theorem v787_pa_checked : Scalar.distance (sourceCoefficient 8 48 1 0) v787_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v787_pb : Scalar.QComplex := ((-188468808518416873140237 : Int)/10^30,(-431477447607651606836217474 : Int)/10^30)
theorem v787_pb_checked : Scalar.distance (sourceCoefficient 8 48 1 1) v787_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v787_pg : Scalar.QComplex := ((-93086417540055593562989 : Int)/10^30,(40660030553844930360 : Int)/10^30)
theorem v787_pg_checked : Scalar.distance (sourceCoefficient 8 48 1 2) v787_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v787_mb : Scalar.QComplex := ((-560814342605416817153855 : Int)/10^30,(-431477124308784937629766816 : Int)/10^30)
theorem v787_mb_checked : Scalar.distance (sourceCoefficient 8 48 3 1) v787_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v787_mg : Scalar.QComplex := ((-93086347791952975782441 : Int)/10^30,(120989401294710578159 : Int)/10^30)
theorem v787_mg_checked : Scalar.distance (sourceCoefficient 8 48 3 2) v787_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v787_upper : Scalar.QComplex := ((999997661346111738170332123005 : Int)/10^30,(-2162707170936844666007609706 : Int)/10^30)
theorem v787_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 48 5) 1) 14) v787_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material787 : Material (8 : Basis) (48 : Basis) where
  plus := ![v787_pa,v787_pb,v787_pg]
  minus := ![(Primitive.Addresses.material787 1).one,v787_mb,v787_mg]
  upper := v787_upper
  lower := (Primitive.Addresses.material787 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v787_pa_checked.trans (by decide +kernel)
    · exact v787_pb_checked.trans (by decide +kernel)
    · exact v787_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 48 Primitive.Addresses.material787
    · exact v787_mb_checked.trans (by decide +kernel)
    · exact v787_mg_checked.trans (by decide +kernel)
  upper_error := v787_upper_checked
  lower_error := reuse_lower_error 8 48 Primitive.Addresses.material787

def v788_pa : Scalar.QComplex := ((999999894734258123322024393710 : Int)/10^30,(-458837087289682304256793810 : Int)/10^30)
theorem v788_pa_checked : Scalar.distance (sourceCoefficient 8 49 1 0) v788_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v788_pb : Scalar.QComplex := ((-197977873188192444241363 : Int)/10^30,(-431477441192353678507215410 : Int)/10^30)
theorem v788_pb_checked : Scalar.distance (sourceCoefficient 8 49 1 1) v788_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v788_pg : Scalar.QComplex := ((-93086416388697852231237 : Int)/10^30,(42711504658082894338 : Int)/10^30)
theorem v788_pg_checked : Scalar.distance (sourceCoefficient 8 49 1 2) v788_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v788_mb : Scalar.QComplex := ((-570323398198419848118174 : Int)/10^30,(-431477109687594860367568056 : Int)/10^30)
theorem v788_mb_checked : Scalar.distance (sourceCoefficient 8 49 3 1) v788_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v788_mg : Scalar.QComplex := ((-93086344870265906160226 : Int)/10^30,(123040873641521100589 : Int)/10^30)
theorem v788_mg_checked : Scalar.distance (sourceCoefficient 8 49 3 2) v788_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v788_upper : Scalar.QComplex := ((999997613440695869381463355558 : Int)/10^30,(-2184745502935278944904758228 : Int)/10^30)
theorem v788_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 49 5) 1) 14) v788_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material788 : Material (8 : Basis) (49 : Basis) where
  plus := ![v788_pa,v788_pb,v788_pg]
  minus := ![(Primitive.Addresses.material788 1).one,v788_mb,v788_mg]
  upper := v788_upper
  lower := (Primitive.Addresses.material788 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v788_pa_checked.trans (by decide +kernel)
    · exact v788_pb_checked.trans (by decide +kernel)
    · exact v788_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 49 Primitive.Addresses.material788
    · exact v788_mb_checked.trans (by decide +kernel)
    · exact v788_mg_checked.trans (by decide +kernel)
  upper_error := v788_upper_checked
  lower_error := reuse_lower_error 8 49 Primitive.Addresses.material788

def v789_pa : Scalar.QComplex := ((999999893549307608318214741768 : Int)/10^30,(-461412368117298801832557236 : Int)/10^30)
theorem v789_pa_checked : Scalar.distance (sourceCoefficient 8 50 1 0) v789_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v789_pb : Scalar.QComplex := ((-199089048768610100395036 : Int)/10^30,(-431477440424464791536797905 : Int)/10^30)
theorem v789_pb_checked : Scalar.distance (sourceCoefficient 8 50 1 1) v789_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v789_pg : Scalar.QComplex := ((-93086416250714743329152 : Int)/10^30,(42951228333982891731 : Int)/10^30)
theorem v789_pg_checked : Scalar.distance (sourceCoefficient 8 50 1 2) v789_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v789_mb : Scalar.QComplex := ((-571434572702442527425750 : Int)/10^30,(-431477107960811778907206249 : Int)/10^30)
theorem v789_mb_checked : Scalar.distance (sourceCoefficient 8 50 3 1) v789_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v789_mg : Scalar.QComplex := ((-93086344525412113087429 : Int)/10^30,(123280597109087809078 : Int)/10^30)
theorem v789_mg_checked : Scalar.distance (sourceCoefficient 8 50 3 2) v789_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v789_upper : Scalar.QComplex := ((999997607811046038407859227412 : Int)/10^30,(-2187320777882200072456609704 : Int)/10^30)
theorem v789_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 50 5) 1) 14) v789_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material789 : Material (8 : Basis) (50 : Basis) where
  plus := ![v789_pa,v789_pb,v789_pg]
  minus := ![(Primitive.Addresses.material789 1).one,v789_mb,v789_mg]
  upper := v789_upper
  lower := (Primitive.Addresses.material789 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v789_pa_checked.trans (by decide +kernel)
    · exact v789_pb_checked.trans (by decide +kernel)
    · exact v789_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 50 Primitive.Addresses.material789
    · exact v789_mb_checked.trans (by decide +kernel)
    · exact v789_mg_checked.trans (by decide +kernel)
  upper_error := v789_upper_checked
  lower_error := reuse_lower_error 8 50 Primitive.Addresses.material789

def v790_pa : Scalar.QComplex := ((999999888271857147830532418511 : Int)/10^30,(-472711617396019821966169055 : Int)/10^30)
theorem v790_pa_checked : Scalar.distance (sourceCoefficient 8 51 1 0) v790_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v790_pb : Scalar.QComplex := ((-203964419907544674356222 : Int)/10^30,(-431477437010195610189534487 : Int)/10^30)
theorem v790_pb_checked : Scalar.distance (sourceCoefficient 8 51 1 1) v790_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v790_pg : Scalar.QComplex := ((-93086415636790113565533 : Int)/10^30,(44003035009642586507 : Int)/10^30)
theorem v790_pg_checked : Scalar.distance (sourceCoefficient 8 51 1 2) v790_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v790_mb : Scalar.QComplex := ((-576309939079693080366157 : Int)/10^30,(-431477100339318154512819662 : Int)/10^30)
theorem v790_mb_checked : Scalar.distance (sourceCoefficient 8 51 3 1) v790_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v790_mg : Scalar.QComplex := ((-93086343003825922435845 : Int)/10^30,(124332402863322503219 : Int)/10^30)
theorem v790_mg_checked : Scalar.distance (sourceCoefficient 8 51 3 2) v790_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v790_upper : Scalar.QComplex := ((999997583032124242877461332096 : Int)/10^30,(-2198620001223615866757611690 : Int)/10^30)
theorem v790_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 51 5) 1) 14) v790_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material790 : Material (8 : Basis) (51 : Basis) where
  plus := ![v790_pa,v790_pb,v790_pg]
  minus := ![(Primitive.Addresses.material790 1).one,v790_mb,v790_mg]
  upper := v790_upper
  lower := (Primitive.Addresses.material790 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v790_pa_checked.trans (by decide +kernel)
    · exact v790_pb_checked.trans (by decide +kernel)
    · exact v790_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 51 Primitive.Addresses.material790
    · exact v790_mb_checked.trans (by decide +kernel)
    · exact v790_mg_checked.trans (by decide +kernel)
  upper_error := v790_upper_checked
  lower_error := reuse_lower_error 8 51 Primitive.Addresses.material790

def v791_pa : Scalar.QComplex := ((999999876544915741468695081689 : Int)/10^30,(-496900546664928494678518736 : Int)/10^30)
theorem v791_pa_checked : Scalar.distance (sourceCoefficient 8 52 1 0) v791_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v791_pb : Scalar.QComplex := ((-214401397038289795720963 : Int)/10^30,(-431477429454154034190504435 : Int)/10^30)
theorem v791_pb_checked : Scalar.distance (sourceCoefficient 8 52 1 1) v791_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v791_pg : Scalar.QComplex := ((-93086414275914997002436 : Int)/10^30,(46254695851157539637 : Int)/10^30)
theorem v791_pg_checked : Scalar.distance (sourceCoefficient 8 52 1 2) v791_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v791_mb : Scalar.QComplex := ((-586746905803751053928124 : Int)/10^30,(-431477083776638192140729618 : Int)/10^30)
theorem v791_mb_checked : Scalar.distance (sourceCoefficient 8 52 3 1) v791_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v791_mg : Scalar.QComplex := ((-93086339699869417401092 : Int)/10^30,(126584061692067285015 : Int)/10^30)
theorem v791_mg_checked : Scalar.distance (sourceCoefficient 8 52 3 2) v791_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v791_upper : Scalar.QComplex := ((999997529557302786802479972138 : Int)/10^30,(-2222808874226318817095514034 : Int)/10^30)
theorem v791_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 52 5) 1) 14) v791_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material791 : Material (8 : Basis) (52 : Basis) where
  plus := ![v791_pa,v791_pb,v791_pg]
  minus := ![(Primitive.Addresses.material791 1).one,v791_mb,v791_mg]
  upper := v791_upper
  lower := (Primitive.Addresses.material791 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v791_pa_checked.trans (by decide +kernel)
    · exact v791_pb_checked.trans (by decide +kernel)
    · exact v791_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 52 Primitive.Addresses.material791
    · exact v791_mb_checked.trans (by decide +kernel)
    · exact v791_mg_checked.trans (by decide +kernel)
  upper_error := v791_upper_checked
  lower_error := reuse_lower_error 8 52 Primitive.Addresses.material791

def v792_pa : Scalar.QComplex := ((999999874698192161761360749096 : Int)/10^30,(-500603236082163407114068272 : Int)/10^30)
theorem v792_pa_checked : Scalar.distance (sourceCoefficient 8 53 1 0) v792_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v792_pb : Scalar.QComplex := ((-215999023952346256483879 : Int)/10^30,(-431477428267815688591720581 : Int)/10^30)
theorem v792_pb_checked : Scalar.distance (sourceCoefficient 8 53 1 1) v792_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v792_pg : Scalar.QComplex := ((-93086414061992956060637 : Int)/10^30,(46599365953702673463 : Int)/10^30)
theorem v792_pg_checked : Scalar.distance (sourceCoefficient 8 53 1 2) v792_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v792_mb : Scalar.QComplex := ((-588344531099181437874721 : Int)/10^30,(-431477081211620215884339077 : Int)/10^30)
theorem v792_mb_checked : Scalar.distance (sourceCoefficient 8 53 3 1) v792_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v792_mg : Scalar.QComplex := ((-93086339188512680980959 : Int)/10^30,(126928731481670900820 : Int)/10^30)
theorem v792_mg_checked : Scalar.distance (sourceCoefficient 8 53 3 2) v792_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v792_upper : Scalar.QComplex := ((999997521320075928785510236740 : Int)/10^30,(-2226511554941555425891664725 : Int)/10^30)
theorem v792_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 53 5) 1) 14) v792_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material792 : Material (8 : Basis) (53 : Basis) where
  plus := ![v792_pa,v792_pb,v792_pg]
  minus := ![(Primitive.Addresses.material792 1).one,v792_mb,v792_mg]
  upper := v792_upper
  lower := (Primitive.Addresses.material792 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v792_pa_checked.trans (by decide +kernel)
    · exact v792_pb_checked.trans (by decide +kernel)
    · exact v792_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 53 Primitive.Addresses.material792
    · exact v792_mb_checked.trans (by decide +kernel)
    · exact v792_mg_checked.trans (by decide +kernel)
  upper_error := v792_upper_checked
  lower_error := reuse_lower_error 8 53 Primitive.Addresses.material792

def v793_pa : Scalar.QComplex := ((999999873754049740658603993679 : Int)/10^30,(-502485705847084604537145502 : Int)/10^30)
theorem v793_pa_checked : Scalar.distance (sourceCoefficient 8 54 1 0) v793_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v793_pb : Scalar.QComplex := ((-216811267167192905905305 : Int)/10^30,(-431477427661649736431045414 : Int)/10^30)
theorem v793_pb_checked : Scalar.distance (sourceCoefficient 8 54 1 1) v793_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v793_pg : Scalar.QComplex := ((-93086413952662783595915 : Int)/10^30,(46774598324881277117 : Int)/10^30)
theorem v793_pg_checked : Scalar.distance (sourceCoefficient 8 54 1 2) v793_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v793_mb : Scalar.QComplex := ((-589156773488498901046362 : Int)/10^30,(-431477079904525177090698786 : Int)/10^30)
theorem v793_mb_checked : Scalar.distance (sourceCoefficient 8 54 3 1) v793_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v793_mg : Scalar.QComplex := ((-93086338927964905070749 : Int)/10^30,(127103963693255469380 : Int)/10^30)
theorem v793_mg_checked : Scalar.distance (sourceCoefficient 8 54 3 2) v793_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v793_upper : Scalar.QComplex := ((999997517126962875941038427014 : Int)/10^30,(-2228394020273254872004779784 : Int)/10^30)
theorem v793_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 54 5) 1) 14) v793_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material793 : Material (8 : Basis) (54 : Basis) where
  plus := ![v793_pa,v793_pb,v793_pg]
  minus := ![(Primitive.Addresses.material793 1).one,v793_mb,v793_mg]
  upper := v793_upper
  lower := (Primitive.Addresses.material793 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v793_pa_checked.trans (by decide +kernel)
    · exact v793_pb_checked.trans (by decide +kernel)
    · exact v793_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 54 Primitive.Addresses.material793
    · exact v793_mb_checked.trans (by decide +kernel)
    · exact v793_mg_checked.trans (by decide +kernel)
  upper_error := v793_upper_checked
  lower_error := reuse_lower_error 8 54 Primitive.Addresses.material793

def v794_pa : Scalar.QComplex := ((999999865926399104776446717920 : Int)/10^30,(-517829299880488270495883048 : Int)/10^30)
theorem v794_pa_checked : Scalar.distance (sourceCoefficient 8 55 1 0) v794_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v794_pb : Scalar.QComplex := ((-223431681638734244178910 : Int)/10^30,(-431477422644896196142003792 : Int)/10^30)
theorem v794_pb_checked : Scalar.distance (sourceCoefficient 8 55 1 1) v794_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v794_pg : Scalar.QComplex := ((-93086413047184635455697 : Int)/10^30,(48202878559343070498 : Int)/10^30)
theorem v794_pg_checked : Scalar.distance (sourceCoefficient 8 55 1 2) v794_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v794_mb : Scalar.QComplex := ((-595777181165725004599115 : Int)/10^30,(-431477069174653988227220724 : Int)/10^30)
theorem v794_mb_checked : Scalar.distance (sourceCoefficient 8 55 3 1) v794_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v794_mg : Scalar.QComplex := ((-93086336789945579094717 : Int)/10^30,(128532242614516395217 : Int)/10^30)
theorem v794_mg_checked : Scalar.distance (sourceCoefficient 8 55 3 2) v794_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v794_upper : Scalar.QComplex := ((999997482817672556747591170063 : Int)/10^30,(-2243737577944362731760512043 : Int)/10^30)
theorem v794_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 55 5) 1) 14) v794_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material794 : Material (8 : Basis) (55 : Basis) where
  plus := ![v794_pa,v794_pb,v794_pg]
  minus := ![(Primitive.Addresses.material794 1).one,v794_mb,v794_mg]
  upper := v794_upper
  lower := (Primitive.Addresses.material794 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v794_pa_checked.trans (by decide +kernel)
    · exact v794_pb_checked.trans (by decide +kernel)
    · exact v794_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 55 Primitive.Addresses.material794
    · exact v794_mb_checked.trans (by decide +kernel)
    · exact v794_mg_checked.trans (by decide +kernel)
  upper_error := v794_upper_checked
  lower_error := reuse_lower_error 8 55 Primitive.Addresses.material794

def v795_pa : Scalar.QComplex := ((999999864034112261304493871329 : Int)/10^30,(-521470763313407996938429410 : Int)/10^30)
theorem v795_pa_checked : Scalar.distance (sourceCoefficient 8 56 1 0) v795_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v795_pb : Scalar.QComplex := ((-225002890900612333974024 : Int)/10^30,(-431477421434394116786760248 : Int)/10^30)
theorem v795_pb_checked : Scalar.distance (sourceCoefficient 8 56 1 1) v795_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v795_pg : Scalar.QComplex := ((-93086412828535406580519 : Int)/10^30,(48541849351839012430 : Int)/10^30)
theorem v795_pg_checked : Scalar.distance (sourceCoefficient 8 56 1 2) v795_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v795_mb : Scalar.QComplex := ((-597348388797961302892610 : Int)/10^30,(-431477066608269531234680648 : Int)/10^30)
theorem v795_mb_checked : Scalar.distance (sourceCoefficient 8 56 3 1) v795_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v795_mg : Scalar.QComplex := ((-93086336278779904386410 : Int)/10^30,(128871213092113582448 : Int)/10^30)
theorem v795_mg_checked : Scalar.distance (sourceCoefficient 8 56 3 2) v795_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v795_upper : Scalar.QComplex := ((999997474640552997377234430517 : Int)/10^30,(-2247379032687835006301061608 : Int)/10^30)
theorem v795_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 56 5) 1) 14) v795_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material795 : Material (8 : Basis) (56 : Basis) where
  plus := ![v795_pa,v795_pb,v795_pg]
  minus := ![(Primitive.Addresses.material795 1).one,v795_mb,v795_mg]
  upper := v795_upper
  lower := (Primitive.Addresses.material795 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v795_pa_checked.trans (by decide +kernel)
    · exact v795_pb_checked.trans (by decide +kernel)
    · exact v795_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 56 Primitive.Addresses.material795
    · exact v795_mb_checked.trans (by decide +kernel)
    · exact v795_mg_checked.trans (by decide +kernel)
  upper_error := v795_upper_checked
  lower_error := reuse_lower_error 8 56 Primitive.Addresses.material795

def v796_pa : Scalar.QComplex := ((999999857822945577526316288166 : Int)/10^30,(-533248618029744698908662010 : Int)/10^30)
theorem v796_pa_checked : Scalar.distance (sourceCoefficient 8 57 1 0) v796_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v796_pb : Scalar.QComplex := ((-230084769288062799040628 : Int)/10^30,(-431477417466938223402917707 : Int)/10^30)
theorem v796_pb_checked : Scalar.distance (sourceCoefficient 8 57 1 1) v796_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v796_pg : Scalar.QComplex := ((-93086412111480710846854 : Int)/10^30,(49638207673208532081 : Int)/10^30)
theorem v796_pg_checked : Scalar.distance (sourceCoefficient 8 57 1 2) v796_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v796_mb : Scalar.QComplex := ((-602430261869460442585540 : Int)/10^30,(-431477058255382946052409101 : Int)/10^30)
theorem v796_mb_checked : Scalar.distance (sourceCoefficient 8 57 3 1) v796_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v796_mg : Scalar.QComplex := ((-93086334615617622448876 : Int)/10^30,(129967570386472885530 : Int)/10^30)
theorem v796_mg_checked : Scalar.distance (sourceCoefficient 8 57 3 2) v796_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v796_upper : Scalar.QComplex := ((999997448101886802638438867055 : Int)/10^30,(-2259156859142530408728829091 : Int)/10^30)
theorem v796_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 57 5) 1) 14) v796_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material796 : Material (8 : Basis) (57 : Basis) where
  plus := ![v796_pa,v796_pb,v796_pg]
  minus := ![(Primitive.Addresses.material796 1).one,v796_mb,v796_mg]
  upper := v796_upper
  lower := (Primitive.Addresses.material796 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v796_pa_checked.trans (by decide +kernel)
    · exact v796_pb_checked.trans (by decide +kernel)
    · exact v796_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 57 Primitive.Addresses.material796
    · exact v796_mb_checked.trans (by decide +kernel)
    · exact v796_mg_checked.trans (by decide +kernel)
  upper_error := v796_upper_checked
  lower_error := reuse_lower_error 8 57 Primitive.Addresses.material796

def v797_pa : Scalar.QComplex := ((999999854394773903262165496988 : Int)/10^30,(-539639167400397098273966333 : Int)/10^30)
theorem v797_pa_checked : Scalar.distance (sourceCoefficient 8 58 1 0) v797_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v797_pb : Scalar.QComplex := ((-232842147037259796906804 : Int)/10^30,(-431477415280837144364500535 : Int)/10^30)
theorem v797_pb_checked : Scalar.distance (sourceCoefficient 8 58 1 1) v797_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v797_pg : Scalar.QComplex := ((-93086411716109199401835 : Int)/10^30,(50233081028970858745 : Int)/10^30)
theorem v797_pg_checked : Scalar.distance (sourceCoefficient 8 58 1 2) v797_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v797_mb : Scalar.QComplex := ((-605187636705452913164601 : Int)/10^30,(-431477053689789871126084564 : Int)/10^30)
theorem v797_mb_checked : Scalar.distance (sourceCoefficient 8 58 3 1) v797_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v797_mg : Scalar.QComplex := ((-93086333706897344297225 : Int)/10^30,(130562443179548867282 : Int)/10^30)
theorem v797_mg_checked : Scalar.distance (sourceCoefficient 8 58 3 2) v797_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v797_upper : Scalar.QComplex := ((999997433644211766597431757005 : Int)/10^30,(-2265547393078496898694279368 : Int)/10^30)
theorem v797_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 58 5) 1) 14) v797_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material797 : Material (8 : Basis) (58 : Basis) where
  plus := ![v797_pa,v797_pb,v797_pg]
  minus := ![(Primitive.Addresses.material797 1).one,v797_mb,v797_mg]
  upper := v797_upper
  lower := (Primitive.Addresses.material797 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v797_pa_checked.trans (by decide +kernel)
    · exact v797_pb_checked.trans (by decide +kernel)
    · exact v797_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 58 Primitive.Addresses.material797
    · exact v797_mb_checked.trans (by decide +kernel)
    · exact v797_mg_checked.trans (by decide +kernel)
  upper_error := v797_upper_checked
  lower_error := reuse_lower_error 8 58 Primitive.Addresses.material797

def v798_pa : Scalar.QComplex := ((999999844761230797045168749072 : Int)/10^30,(-557205091781144978127444761 : Int)/10^30)
theorem v798_pa_checked : Scalar.distance (sourceCoefficient 8 59 1 0) v798_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v798_pb : Scalar.QComplex := ((-240421446690078530736713 : Int)/10^30,(-431477409150776487147231074 : Int)/10^30)
theorem v798_pb_checked : Scalar.distance (sourceCoefficient 8 59 1 1) v798_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v798_pg : Scalar.QComplex := ((-93086410606487254778977 : Int)/10^30,(51868230017525266823 : Int)/10^30)
theorem v798_pg_checked : Scalar.distance (sourceCoefficient 8 59 1 2) v798_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v798_mb : Scalar.QComplex := ((-612766928246185735648534 : Int)/10^30,(-431477041019137255012509907 : Int)/10^30)
theorem v798_mb_checked : Scalar.distance (sourceCoefficient 8 59 3 1) v798_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v798_mg : Scalar.QComplex := ((-93086331186215880091512 : Int)/10^30,(132197590601708814229 : Int)/10^30)
theorem v798_mg_checked : Scalar.distance (sourceCoefficient 8 59 3 2) v798_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v798_upper : Scalar.QComplex := ((999997393693491095451965346049 : Int)/10^30,(-2283113274670242398723348043 : Int)/10^30)
theorem v798_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 59 5) 1) 14) v798_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material798 : Material (8 : Basis) (59 : Basis) where
  plus := ![v798_pa,v798_pb,v798_pg]
  minus := ![(Primitive.Addresses.material798 1).one,v798_mb,v798_mg]
  upper := v798_upper
  lower := (Primitive.Addresses.material798 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v798_pa_checked.trans (by decide +kernel)
    · exact v798_pb_checked.trans (by decide +kernel)
    · exact v798_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 59 Primitive.Addresses.material798
    · exact v798_mb_checked.trans (by decide +kernel)
    · exact v798_mg_checked.trans (by decide +kernel)
  upper_error := v798_upper_checked
  lower_error := reuse_lower_error 8 59 Primitive.Addresses.material798

def v799_pa : Scalar.QComplex := ((999999833264752309147580782295 : Int)/10^30,(-577469018719672974202378287 : Int)/10^30)
theorem v799_pa_checked : Scalar.distance (sourceCoefficient 8 60 1 0) v799_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v799_pb : Scalar.QComplex := ((-249164873395608859229496 : Int)/10^30,(-431477401858673139510355620 : Int)/10^30)
theorem v799_pb_checked : Scalar.distance (sourceCoefficient 8 60 1 1) v799_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v799_pg : Scalar.QComplex := ((-93086409284809476900270 : Int)/10^30,(53754526388611055880 : Int)/10^30)
theorem v799_pg_checked : Scalar.distance (sourceCoefficient 8 60 1 2) v799_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v799_mb : Scalar.QComplex := ((-621510345403381942464049 : Int)/10^30,(-431477026181853165006973247 : Int)/10^30)
theorem v799_mb_checked : Scalar.distance (sourceCoefficient 8 60 3 1) v799_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v799_mg : Scalar.QComplex := ((-93086328236749781721661 : Int)/10^30,(134083885129891860176 : Int)/10^30)
theorem v799_mg_checked : Scalar.distance (sourceCoefficient 8 60 3 2) v799_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v799_upper : Scalar.QComplex := ((999997347223330163400917111613 : Int)/10^30,(-2303377151586152670200856186 : Int)/10^30)
theorem v799_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 60 5) 1) 14) v799_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material799 : Material (8 : Basis) (60 : Basis) where
  plus := ![v799_pa,v799_pb,v799_pg]
  minus := ![(Primitive.Addresses.material799 1).one,v799_mb,v799_mg]
  upper := v799_upper
  lower := (Primitive.Addresses.material799 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v799_pa_checked.trans (by decide +kernel)
    · exact v799_pb_checked.trans (by decide +kernel)
    · exact v799_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 60 Primitive.Addresses.material799
    · exact v799_mb_checked.trans (by decide +kernel)
    · exact v799_mg_checked.trans (by decide +kernel)
  upper_error := v799_upper_checked
  lower_error := reuse_lower_error 8 60 Primitive.Addresses.material799

def v800_pa : Scalar.QComplex := ((999999829864001633947408148504 : Int)/10^30,(-583328353318992410255588063 : Int)/10^30)
theorem v800_pa_checked : Scalar.distance (sourceCoefficient 8 61 1 0) v800_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v800_pb : Scalar.QComplex := ((-251693043886981795985338 : Int)/10^30,(-431477399706124822600435758 : Int)/10^30)
theorem v800_pb_checked : Scalar.distance (sourceCoefficient 8 61 1 1) v800_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v800_pg : Scalar.QComplex := ((-93086408894333542586777 : Int)/10^30,(54299950855086344323 : Int)/10^30)
theorem v800_pg_checked : Scalar.distance (sourceCoefficient 8 61 1 2) v800_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v800_mb : Scalar.QComplex := ((-624038513095849211866431 : Int)/10^30,(-431477021847608380106403504 : Int)/10^30)
theorem v800_mb_checked : Scalar.distance (sourceCoefficient 8 61 3 1) v800_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v800_mg : Scalar.QComplex := ((-93086327375597243238105 : Int)/10^30,(134629309056317547691 : Int)/10^30)
theorem v800_mg_checked : Scalar.distance (sourceCoefficient 8 61 3 2) v800_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v800_upper : Scalar.QComplex := ((999997333709904589476621273651 : Int)/10^30,(-2309236471589294354655021315 : Int)/10^30)
theorem v800_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 61 5) 1) 14) v800_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material800 : Material (8 : Basis) (61 : Basis) where
  plus := ![v800_pa,v800_pb,v800_pg]
  minus := ![(Primitive.Addresses.material800 1).one,v800_mb,v800_mg]
  upper := v800_upper
  lower := (Primitive.Addresses.material800 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v800_pa_checked.trans (by decide +kernel)
    · exact v800_pb_checked.trans (by decide +kernel)
    · exact v800_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 61 Primitive.Addresses.material800
    · exact v800_mb_checked.trans (by decide +kernel)
    · exact v800_mg_checked.trans (by decide +kernel)
  upper_error := v800_upper_checked
  lower_error := reuse_lower_error 8 61 Primitive.Addresses.material800

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
