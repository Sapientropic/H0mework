import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B148
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B149

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3569_pa : Scalar.QComplex := ((999998278302127375329942185507 : Int)/10^30,(-1855638106152645140628266999 : Int)/10^30)
theorem v3569_pa_checked : Scalar.distance (sourceCoefficient 48 90 1 0) v3569_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3569_pb : Scalar.QComplex := ((-800666054982422185779554 : Int)/10^30,(-431476737744636406192292637 : Int)/10^30)
theorem v3569_pb_checked : Scalar.distance (sourceCoefficient 48 90 1 1) v3569_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3569_pg : Scalar.QComplex := ((-93086265274276903721770 : Int)/10^30,(172734718399379126828 : Int)/10^30)
theorem v3569_pg_checked : Scalar.distance (sourceCoefficient 48 90 1 2) v3569_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3569_mb : Scalar.QComplex := ((-1173010748540597400128019 : Int)/10^30,(-431475886147382693439508637 : Int)/10^30)
theorem v3569_mb_checked : Scalar.distance (sourceCoefficient 48 90 3 1) v3569_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3569_mg : Scalar.QComplex := ((-93086081551723793878224 : Int)/10^30,(253063908564293165076 : Int)/10^30)
theorem v3569_mg_checked : Scalar.distance (sourceCoefficient 48 90 3 2) v3569_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3569_upper : Scalar.QComplex := ((999993586259130848268757627949 : Int)/10^30,(-3581541651611987864910169981 : Int)/10^30)
theorem v3569_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 90 5) 1) 14) v3569_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3569 : Material (48 : Basis) (90 : Basis) where
  plus := ![v3569_pa,v3569_pb,v3569_pg]
  minus := ![(Primitive.Addresses.material3569 1).one,v3569_mb,v3569_mg]
  upper := v3569_upper
  lower := (Primitive.Addresses.material3569 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3569_pa_checked.trans (by decide +kernel)
    · exact v3569_pb_checked.trans (by decide +kernel)
    · exact v3569_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 90 Primitive.Addresses.material3569
    · exact v3569_mb_checked.trans (by decide +kernel)
    · exact v3569_mg_checked.trans (by decide +kernel)
  upper_error := v3569_upper_checked
  lower_error := reuse_lower_error 48 90 Primitive.Addresses.material3569

def v3570_pa : Scalar.QComplex := ((999998250801977142819363713583 : Int)/10^30,(-1870399151523716368985007781 : Int)/10^30)
theorem v3570_pa_checked : Scalar.distance (sourceCoefficient 48 91 1 0) v3570_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3570_pb : Scalar.QComplex := ((-807035110645480158074570 : Int)/10^30,(-431476724272362983625625843 : Int)/10^30)
theorem v3570_pb_checked : Scalar.distance (sourceCoefficient 48 91 1 1) v3570_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3570_pg : Scalar.QComplex := ((-93086262541085646347384 : Int)/10^30,(174108771026078535877 : Int)/10^30)
theorem v3570_pg_checked : Scalar.distance (sourceCoefficient 48 91 1 2) v3570_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3570_mb : Scalar.QComplex := ((-1179379790206199673838702 : Int)/10^30,(-431475867178906101615551800 : Int)/10^30)
theorem v3570_mb_checked : Scalar.distance (sourceCoefficient 48 91 3 1) v3570_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3570_mg : Scalar.QComplex := ((-93086077632788022387292 : Int)/10^30,(254437958320749027148 : Int)/10^30)
theorem v3570_mg_checked : Scalar.distance (sourceCoefficient 48 91 3 2) v3570_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3570_upper : Scalar.QComplex := ((999993533282796375108113780701 : Int)/10^30,(-3596302627535451460076813427 : Int)/10^30)
theorem v3570_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 91 5) 1) 14) v3570_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3570 : Material (48 : Basis) (91 : Basis) where
  plus := ![v3570_pa,v3570_pb,v3570_pg]
  minus := ![(Primitive.Addresses.material3570 1).one,v3570_mb,v3570_mg]
  upper := v3570_upper
  lower := (Primitive.Addresses.material3570 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3570_pa_checked.trans (by decide +kernel)
    · exact v3570_pb_checked.trans (by decide +kernel)
    · exact v3570_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 91 Primitive.Addresses.material3570
    · exact v3570_mb_checked.trans (by decide +kernel)
    · exact v3570_mg_checked.trans (by decide +kernel)
  upper_error := v3570_upper_checked
  lower_error := reuse_lower_error 48 91 Primitive.Addresses.material3570

def v3571_pa : Scalar.QComplex := ((999998190520710731908884707398 : Int)/10^30,(-1902355199304505262725207520 : Int)/10^30)
theorem v3571_pa_checked : Scalar.distance (sourceCoefficient 48 92 1 0) v3571_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3571_pb : Scalar.QComplex := ((-820823418760357437397515 : Int)/10^30,(-431476694676930372785134597 : Int)/10^30)
theorem v3571_pb_checked : Scalar.distance (sourceCoefficient 48 92 1 1) v3571_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3571_pg : Scalar.QComplex := ((-93086256542960579615434 : Int)/10^30,(177083444547119460755 : Int)/10^30)
theorem v3571_pg_checked : Scalar.distance (sourceCoefficient 48 92 1 2) v3571_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3571_mb : Scalar.QComplex := ((-1193168067647534270830413 : Int)/10^30,(-431475825684795609712911036 : Int)/10^30)
theorem v3571_mb_checked : Scalar.distance (sourceCoefficient 48 92 3 1) v3571_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3571_mg : Scalar.QComplex := ((-93086069067655914695141 : Int)/10^30,(257412625558071263782 : Int)/10^30)
theorem v3571_mg_checked : Scalar.distance (sourceCoefficient 48 92 3 2) v3571_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3571_upper : Scalar.QComplex := ((999993417848380306429881770318 : Int)/10^30,(-3628258523681463853934210902 : Int)/10^30)
theorem v3571_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 92 5) 1) 14) v3571_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3571 : Material (48 : Basis) (92 : Basis) where
  plus := ![v3571_pa,v3571_pb,v3571_pg]
  minus := ![(Primitive.Addresses.material3571 1).one,v3571_mb,v3571_mg]
  upper := v3571_upper
  lower := (Primitive.Addresses.material3571 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3571_pa_checked.trans (by decide +kernel)
    · exact v3571_pb_checked.trans (by decide +kernel)
    · exact v3571_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 92 Primitive.Addresses.material3571
    · exact v3571_mb_checked.trans (by decide +kernel)
    · exact v3571_mg_checked.trans (by decide +kernel)
  upper_error := v3571_upper_checked
  lower_error := reuse_lower_error 48 92 Primitive.Addresses.material3571

def v3572_pa : Scalar.QComplex := ((999998117653551434927485261444 : Int)/10^30,(-1940280741001670769285835941 : Int)/10^30)
theorem v3572_pa_checked : Scalar.distance (sourceCoefficient 48 93 1 0) v3572_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3572_pb : Scalar.QComplex := ((-837187427119948035320664 : Int)/10^30,(-431476658790608958998548437 : Int)/10^30)
theorem v3572_pb_checked : Scalar.distance (sourceCoefficient 48 93 1 1) v3572_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3572_pg : Scalar.QComplex := ((-93086249280453285075878 : Int)/10^30,(180613796708682938872 : Int)/10^30)
theorem v3572_pg_checked : Scalar.distance (sourceCoefficient 48 93 1 2) v3572_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3572_mb : Scalar.QComplex := ((-1209532038945777564170581 : Int)/10^30,(-431475775677085351294695794 : Int)/10^30)
theorem v3572_mb_checked : Scalar.distance (sourceCoefficient 48 93 3 1) v3572_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3572_mg : Scalar.QComplex := ((-93086058758616410048639 : Int)/10^30,(260942970137906583084 : Int)/10^30)
theorem v3572_mg_checked : Scalar.distance (sourceCoefficient 48 93 3 2) v3572_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3572_upper : Scalar.QComplex := ((999993279525285145481457412576 : Int)/10^30,(-3666183883130883560108024837 : Int)/10^30)
theorem v3572_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 93 5) 1) 14) v3572_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3572 : Material (48 : Basis) (93 : Basis) where
  plus := ![v3572_pa,v3572_pb,v3572_pg]
  minus := ![(Primitive.Addresses.material3572 1).one,v3572_mb,v3572_mg]
  upper := v3572_upper
  lower := (Primitive.Addresses.material3572 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3572_pa_checked.trans (by decide +kernel)
    · exact v3572_pb_checked.trans (by decide +kernel)
    · exact v3572_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 93 Primitive.Addresses.material3572
    · exact v3572_mb_checked.trans (by decide +kernel)
    · exact v3572_mg_checked.trans (by decide +kernel)
  upper_error := v3572_upper_checked
  lower_error := reuse_lower_error 48 93 Primitive.Addresses.material3572

def v3573_pa : Scalar.QComplex := ((999998029728319640370350174565 : Int)/10^30,(-1985079212210123586858681153 : Int)/10^30)
theorem v3573_pa_checked : Scalar.distance (sourceCoefficient 48 94 1 0) v3573_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3573_pb : Scalar.QComplex := ((-856516947227165632864797 : Int)/10^30,(-431476615334893421390140119 : Int)/10^30)
theorem v3573_pb_checked : Scalar.distance (sourceCoefficient 48 94 1 1) v3573_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3573_pg : Scalar.QComplex := ((-93086240500588991702800 : Int)/10^30,(184783925035045778174 : Int)/10^30)
theorem v3573_pg_checked : Scalar.distance (sourceCoefficient 48 94 1 2) v3573_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3573_mb : Scalar.QComplex := ((-1228861514355406086905813 : Int)/10^30,(-431475715540880710974998513 : Int)/10^30)
theorem v3573_mb_checked : Scalar.distance (sourceCoefficient 48 94 3 1) v3573_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3573_mg : Scalar.QComplex := ((-93086046380122455776943 : Int)/10^30,(265113089334912607428 : Int)/10^30)
theorem v3573_mg_checked : Scalar.distance (sourceCoefficient 48 94 3 2) v3573_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3573_upper : Scalar.QComplex := ((999993114282087085000230583558 : Int)/10^30,(-3710982135866302348095520581 : Int)/10^30)
theorem v3573_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 94 5) 1) 14) v3573_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3573 : Material (48 : Basis) (94 : Basis) where
  plus := ![v3573_pa,v3573_pb,v3573_pg]
  minus := ![(Primitive.Addresses.material3573 1).one,v3573_mb,v3573_mg]
  upper := v3573_upper
  lower := (Primitive.Addresses.material3573 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3573_pa_checked.trans (by decide +kernel)
    · exact v3573_pb_checked.trans (by decide +kernel)
    · exact v3573_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 94 Primitive.Addresses.material3573
    · exact v3573_mb_checked.trans (by decide +kernel)
    · exact v3573_mg_checked.trans (by decide +kernel)
  upper_error := v3573_upper_checked
  lower_error := reuse_lower_error 48 94 Primitive.Addresses.material3573

def v3574_pa : Scalar.QComplex := ((999997940860377107372924940087 : Int)/10^30,(-2029353346691814432608617192 : Int)/10^30)
theorem v3574_pa_checked : Scalar.distance (sourceCoefficient 48 95 1 0) v3574_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3574_pb : Scalar.QComplex := ((-875620226916514164397801 : Int)/10^30,(-431476571253406845120548826 : Int)/10^30)
theorem v3574_pb_checked : Scalar.distance (sourceCoefficient 48 95 1 1) v3574_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3574_pg : Scalar.QComplex := ((-93086231609346370563345 : Int)/10^30,(188905244629630609577 : Int)/10^30)
theorem v3574_pg_checked : Scalar.distance (sourceCoefficient 48 95 1 2) v3574_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3574_mb : Scalar.QComplex := ((-1247964748891392968217209 : Int)/10^30,(-431475654974140556128109900 : Int)/10^30)
theorem v3574_mb_checked : Scalar.distance (sourceCoefficient 48 95 3 1) v3574_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3574_mg : Scalar.QComplex := ((-93086033932369952470856 : Int)/10^30,(269234399722199864816 : Int)/10^30)
theorem v3574_mg_checked : Scalar.distance (sourceCoefficient 48 95 3 2) v3574_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3574_upper : Scalar.QComplex := ((999992949001137313070508028609 : Int)/10^30,(-3755256051028863913355661088 : Int)/10^30)
theorem v3574_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 95 5) 1) 14) v3574_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3574 : Material (48 : Basis) (95 : Basis) where
  plus := ![v3574_pa,v3574_pb,v3574_pg]
  minus := ![(Primitive.Addresses.material3574 1).one,v3574_mb,v3574_mg]
  upper := v3574_upper
  lower := (Primitive.Addresses.material3574 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3574_pa_checked.trans (by decide +kernel)
    · exact v3574_pb_checked.trans (by decide +kernel)
    · exact v3574_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 95 Primitive.Addresses.material3574
    · exact v3574_mb_checked.trans (by decide +kernel)
    · exact v3574_mg_checked.trans (by decide +kernel)
  upper_error := v3574_upper_checked
  lower_error := reuse_lower_error 48 95 Primitive.Addresses.material3574

def v3575_pa : Scalar.QComplex := ((999997897481930974153969053790 : Int)/10^30,(-2050617399094590117322811728 : Int)/10^30)
theorem v3575_pa_checked : Scalar.distance (sourceCoefficient 48 96 1 0) v3575_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3575_pb : Scalar.QComplex := ((-884795180375023000959796 : Int)/10^30,(-431476549681004368594518392 : Int)/10^30)
theorem v3575_pb_checked : Scalar.distance (sourceCoefficient 48 96 1 1) v3575_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3575_pg : Scalar.QComplex := ((-93086227263372228012141 : Int)/10^30,(190884638580745998820 : Int)/10^30)
theorem v3575_pg_checked : Scalar.distance (sourceCoefficient 48 96 1 2) v3575_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3575_mb : Scalar.QComplex := ((-1257139680317635563787326 : Int)/10^30,(-431475625484174501864457393 : Int)/10^30)
theorem v3575_mb_checked : Scalar.distance (sourceCoefficient 48 96 3 1) v3575_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3575_mg : Scalar.QComplex := ((-93086027878269596906072 : Int)/10^30,(271213789185916473674 : Int)/10^30)
theorem v3575_mg_checked : Scalar.distance (sourceCoefficient 48 96 3 2) v3575_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3575_upper : Scalar.QComplex := ((999992868922930399525637414563 : Int)/10^30,(-3776519996894068631151878977 : Int)/10^30)
theorem v3575_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 96 5) 1) 14) v3575_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3575 : Material (48 : Basis) (96 : Basis) where
  plus := ![v3575_pa,v3575_pb,v3575_pg]
  minus := ![(Primitive.Addresses.material3575 1).one,v3575_mb,v3575_mg]
  upper := v3575_upper
  lower := (Primitive.Addresses.material3575 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3575_pa_checked.trans (by decide +kernel)
    · exact v3575_pb_checked.trans (by decide +kernel)
    · exact v3575_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 96 Primitive.Addresses.material3575
    · exact v3575_mb_checked.trans (by decide +kernel)
    · exact v3575_mg_checked.trans (by decide +kernel)
  upper_error := v3575_upper_checked
  lower_error := reuse_lower_error 48 96 Primitive.Addresses.material3575

def v3576_pa : Scalar.QComplex := ((999997744777853216214527857130 : Int)/10^30,(-2123779463018851117221524725 : Int)/10^30)
theorem v3576_pa_checked : Scalar.distance (sourceCoefficient 48 97 1 0) v3576_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3576_pb : Scalar.QComplex := ((-916362939735062991274558 : Int)/10^30,(-431476473470792289738532022 : Int)/10^30)
theorem v3576_pb_checked : Scalar.distance (sourceCoefficient 48 97 1 1) v3576_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3576_pg : Scalar.QComplex := ((-93086211935284759717543 : Int)/10^30,(197695031044590357706 : Int)/10^30)
theorem v3576_pg_checked : Scalar.distance (sourceCoefficient 48 97 1 2) v3576_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3576_mb : Scalar.QComplex := ((-1288707362157575382968097 : Int)/10^30,(-431475522032436230942292517 : Int)/10^30)
theorem v3576_mb_checked : Scalar.distance (sourceCoefficient 48 97 3 1) v3576_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3576_mg : Scalar.QComplex := ((-93086006673125868351552 : Int)/10^30,(278024165886491334254 : Int)/10^30)
theorem v3576_mg_checked : Scalar.distance (sourceCoefficient 48 97 3 2) v3576_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3576_upper : Scalar.QComplex := ((999992589947994953689814896930 : Int)/10^30,(-3849681688298644631118806097 : Int)/10^30)
theorem v3576_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 97 5) 1) 14) v3576_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3576 : Material (48 : Basis) (97 : Basis) where
  plus := ![v3576_pa,v3576_pb,v3576_pg]
  minus := ![(Primitive.Addresses.material3576 1).one,v3576_mb,v3576_mg]
  upper := v3576_upper
  lower := (Primitive.Addresses.material3576 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3576_pa_checked.trans (by decide +kernel)
    · exact v3576_pb_checked.trans (by decide +kernel)
    · exact v3576_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 97 Primitive.Addresses.material3576
    · exact v3576_mb_checked.trans (by decide +kernel)
    · exact v3576_mg_checked.trans (by decide +kernel)
  upper_error := v3576_upper_checked
  lower_error := reuse_lower_error 48 97 Primitive.Addresses.material3576

def v3577_pa : Scalar.QComplex := ((999999335376433758471360260768 : Int)/10^30,(-1152929612230760805464334259 : Int)/10^30)
theorem v3577_pa_checked : Scalar.distance (sourceCoefficient 49 50 1 0) v3577_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3577_pb : Scalar.QComplex := ((-497463210973022571294134 : Int)/10^30,(-431477234230046982548559216 : Int)/10^30)
theorem v3577_pb_checked : Scalar.distance (sourceCoefficient 49 50 1 1) v3577_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3577_pg : Scalar.QComplex := ((-93086368029489597224262 : Int)/10^30,(107322101525007183236 : Int)/10^30)
theorem v3577_pg_checked : Scalar.distance (sourceCoefficient 49 50 1 2) v3577_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3577_mb : Scalar.QComplex := ((-869808445872022119443403 : Int)/10^30,(-431476644283007036529834764 : Int)/10^30)
theorem v3577_mb_checked : Scalar.distance (sourceCoefficient 49 50 3 1) v3577_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3577_mg : Scalar.QComplex := ((-93086240755040514601291 : Int)/10^30,(187651404719148619598 : Int)/10^30)
theorem v3577_mg_checked : Scalar.distance (sourceCoefficient 49 50 3 2) v3577_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3577_upper : Scalar.QComplex := ((999995856142974135988809393833 : Int)/10^30,(-2878836028706215073494502887 : Int)/10^30)
theorem v3577_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 50 5) 1) 14) v3577_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3577 : Material (49 : Basis) (50 : Basis) where
  plus := ![v3577_pa,v3577_pb,v3577_pg]
  minus := ![(Primitive.Addresses.material3577 1).one,v3577_mb,v3577_mg]
  upper := v3577_upper
  lower := (Primitive.Addresses.material3577 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3577_pa_checked.trans (by decide +kernel)
    · exact v3577_pb_checked.trans (by decide +kernel)
    · exact v3577_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 50 Primitive.Addresses.material3577
    · exact v3577_mb_checked.trans (by decide +kernel)
    · exact v3577_mg_checked.trans (by decide +kernel)
  upper_error := v3577_upper_checked
  lower_error := reuse_lower_error 49 50 Primitive.Addresses.material3577

def v3578_pa : Scalar.QComplex := ((999999322285356759708739701722 : Int)/10^30,(-1164228855158402633499495452 : Int)/10^30)
theorem v3578_pa_checked : Scalar.distance (sourceCoefficient 49 51 1 0) v3578_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3578_pb : Scalar.QComplex := ((-502338580285058576770260 : Int)/10^30,(-431477228568175046432013533 : Int)/10^30)
theorem v3578_pb_checked : Scalar.distance (sourceCoefficient 49 51 1 1) v3578_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3578_pg : Scalar.QComplex := ((-93086366809446141346453 : Int)/10^30,(108373907708000808853 : Int)/10^30)
theorem v3578_pg_checked : Scalar.distance (sourceCoefficient 49 51 1 2) v3578_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3578_mb : Scalar.QComplex := ((-874683808482794835040993 : Int)/10^30,(-431476634413913070782576179 : Int)/10^30)
theorem v3578_mb_checked : Scalar.distance (sourceCoefficient 49 51 3 1) v3578_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3578_mg : Scalar.QComplex := ((-93086238627336148669887 : Int)/10^30,(188703209457664179665 : Int)/10^30)
theorem v3578_mg_checked : Scalar.distance (sourceCoefficient 49 51 3 2) v3578_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3578_upper : Scalar.QComplex := ((999995823550448401048869132778 : Int)/10^30,(-2890135232210950576483263363 : Int)/10^30)
theorem v3578_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 51 5) 1) 14) v3578_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3578 : Material (49 : Basis) (51 : Basis) where
  plus := ![v3578_pa,v3578_pb,v3578_pg]
  minus := ![(Primitive.Addresses.material3578 1).one,v3578_mb,v3578_mg]
  upper := v3578_upper
  lower := (Primitive.Addresses.material3578 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3578_pa_checked.trans (by decide +kernel)
    · exact v3578_pb_checked.trans (by decide +kernel)
    · exact v3578_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 51 Primitive.Addresses.material3578
    · exact v3578_mb_checked.trans (by decide +kernel)
    · exact v3578_mg_checked.trans (by decide +kernel)
  upper_error := v3578_upper_checked
  lower_error := reuse_lower_error 49 51 Primitive.Addresses.material3578

def v3579_pa : Scalar.QComplex := ((999999293831352001946509822661 : Int)/10^30,(-1188417770534397371334460190 : Int)/10^30)
theorem v3579_pa_checked : Scalar.distance (sourceCoefficient 49 52 1 0) v3579_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3579_pb : Scalar.QComplex := ((-512775553419483737133250 : Int)/10^30,(-431477216200565700321421545 : Int)/10^30)
theorem v3579_pb_checked : Scalar.distance (sourceCoefficient 49 52 1 1) v3579_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3579_pg : Scalar.QComplex := ((-93086364151018864417330 : Int)/10^30,(110625567471814305977 : Int)/10^30)
theorem v3579_pg_checked : Scalar.distance (sourceCoefficient 49 52 1 2) v3579_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3579_mb : Scalar.QComplex := ((-885120767058368054975394 : Int)/10^30,(-431476613039670578509643296 : Int)/10^30)
theorem v3579_mb_checked : Scalar.distance (sourceCoefficient 49 52 3 1) v3579_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3579_mg : Scalar.QComplex := ((-93086234025828896414896 : Int)/10^30,(190954866088978831916 : Int)/10^30)
theorem v3579_mg_checked : Scalar.distance (sourceCoefficient 49 52 3 2) v3579_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3579_upper : Scalar.QComplex := ((999995753348612484478554545140 : Int)/10^30,(-2914324062451366406623467677 : Int)/10^30)
theorem v3579_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 52 5) 1) 14) v3579_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3579 : Material (49 : Basis) (52 : Basis) where
  plus := ![v3579_pa,v3579_pb,v3579_pg]
  minus := ![(Primitive.Addresses.material3579 1).one,v3579_mb,v3579_mg]
  upper := v3579_upper
  lower := (Primitive.Addresses.material3579 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3579_pa_checked.trans (by decide +kernel)
    · exact v3579_pb_checked.trans (by decide +kernel)
    · exact v3579_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 52 Primitive.Addresses.material3579
    · exact v3579_mb_checked.trans (by decide +kernel)
    · exact v3579_mg_checked.trans (by decide +kernel)
  upper_error := v3579_upper_checked
  lower_error := reuse_lower_error 49 52 Primitive.Addresses.material3579

def v3580_pa : Scalar.QComplex := ((999999289424154601117523683541 : Int)/10^30,(-1192120457789284349422676344 : Int)/10^30)
theorem v3580_pa_checked : Scalar.distance (sourceCoefficient 49 53 1 0) v3580_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3580_pb : Scalar.QComplex := ((-514373179711537193720923 : Int)/10^30,(-431477214277702775234057358 : Int)/10^30)
theorem v3580_pb_checked : Scalar.distance (sourceCoefficient 49 53 1 1) v3580_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3580_pg : Scalar.QComplex := ((-93086363738475686802258 : Int)/10^30,(110970237406621733602 : Int)/10^30)
theorem v3580_pg_checked : Scalar.distance (sourceCoefficient 49 53 1 2) v3580_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3580_mb : Scalar.QComplex := ((-886718391096208126083912 : Int)/10^30,(-431476609738128833767012830 : Int)/10^30)
theorem v3580_mb_checked : Scalar.distance (sourceCoefficient 49 53 3 1) v3580_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3580_mg : Scalar.QComplex := ((-93086233315851242027303 : Int)/10^30,(191299535539443708591 : Int)/10^30)
theorem v3580_mg_checked : Scalar.distance (sourceCoefficient 49 53 3 2) v3580_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3580_upper : Scalar.QComplex := ((999995742550919350881283191904 : Int)/10^30,(-2918026736585112770750101178 : Int)/10^30)
theorem v3580_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 53 5) 1) 14) v3580_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3580 : Material (49 : Basis) (53 : Basis) where
  plus := ![v3580_pa,v3580_pb,v3580_pg]
  minus := ![(Primitive.Addresses.material3580 1).one,v3580_mb,v3580_mg]
  upper := v3580_upper
  lower := (Primitive.Addresses.material3580 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3580_pa_checked.trans (by decide +kernel)
    · exact v3580_pb_checked.trans (by decide +kernel)
    · exact v3580_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 53 Primitive.Addresses.material3580
    · exact v3580_mb_checked.trans (by decide +kernel)
    · exact v3580_mg_checked.trans (by decide +kernel)
  upper_error := v3580_upper_checked
  lower_error := reuse_lower_error 49 53 Primitive.Addresses.material3580

def v3581_pa : Scalar.QComplex := ((999999287178251755539514203893 : Int)/10^30,(-1194002926451219465897527538 : Int)/10^30)
theorem v3581_pa_checked : Scalar.distance (sourceCoefficient 49 54 1 0) v3581_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3581_pb : Scalar.QComplex := ((-515185422609108050067016 : Int)/10^30,(-431477213297083258613850720 : Int)/10^30)
theorem v3581_pb_checked : Scalar.distance (sourceCoefficient 49 54 1 1) v3581_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3581_pg : Scalar.QComplex := ((-93086363528165323476311 : Int)/10^30,(111145469692239474350 : Int)/10^30)
theorem v3581_pg_checked : Scalar.distance (sourceCoefficient 49 54 1 2) v3581_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3581_mb : Scalar.QComplex := ((-887530632845113352950416 : Int)/10^30,(-431476608056580643734736342 : Int)/10^30)
theorem v3581_mb_checked : Scalar.distance (sourceCoefficient 49 54 3 1) v3581_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3581_mg : Scalar.QComplex := ((-93086232954323386690579 : Int)/10^30,(191474767578326089369 : Int)/10^30)
theorem v3581_mg_checked : Scalar.distance (sourceCoefficient 49 54 3 2) v3581_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3581_upper : Scalar.QComplex := ((999995737056049716034708993662 : Int)/10^30,(-2919909198567107380822108300 : Int)/10^30)
theorem v3581_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 54 5) 1) 14) v3581_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3581 : Material (49 : Basis) (54 : Basis) where
  plus := ![v3581_pa,v3581_pb,v3581_pg]
  minus := ![(Primitive.Addresses.material3581 1).one,v3581_mb,v3581_mg]
  upper := v3581_upper
  lower := (Primitive.Addresses.material3581 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3581_pa_checked.trans (by decide +kernel)
    · exact v3581_pb_checked.trans (by decide +kernel)
    · exact v3581_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 54 Primitive.Addresses.material3581
    · exact v3581_mb_checked.trans (by decide +kernel)
    · exact v3581_mg_checked.trans (by decide +kernel)
  upper_error := v3581_upper_checked
  lower_error := reuse_lower_error 49 54 Primitive.Addresses.material3581

def v3582_pa : Scalar.QComplex := ((999999268740240308229743175198 : Int)/10^30,(-1209346511403040501276800224 : Int)/10^30)
theorem v3582_pa_checked : Scalar.distance (sourceCoefficient 49 55 1 0) v3582_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3582_pb : Scalar.QComplex := ((-521805834468316939698937 : Int)/10^30,(-431477205228241677665152719 : Int)/10^30)
theorem v3582_pb_checked : Scalar.distance (sourceCoefficient 49 55 1 1) v3582_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3582_pg : Scalar.QComplex := ((-93086361799620012390102 : Int)/10^30,(112573749222224520877 : Int)/10^30)
theorem v3582_pg_checked : Scalar.distance (sourceCoefficient 49 55 1 2) v3582_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3582_mb : Scalar.QComplex := ((-894151035276193462405523 : Int)/10^30,(-431476594274624804968714846 : Int)/10^30)
theorem v3582_mb_checked : Scalar.distance (sourceCoefficient 49 55 3 1) v3582_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3582_mg : Scalar.QComplex := ((-93086229993237812165781 : Int)/10^30,(192903045084840638607 : Int)/10^30)
theorem v3582_mg_checked : Scalar.distance (sourceCoefficient 49 55 3 2) v3582_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3582_upper : Scalar.QComplex := ((999995692136430062287441710505 : Int)/10^30,(-2935252728844125939838517126 : Int)/10^30)
theorem v3582_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 55 5) 1) 14) v3582_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3582 : Material (49 : Basis) (55 : Basis) where
  plus := ![v3582_pa,v3582_pb,v3582_pg]
  minus := ![(Primitive.Addresses.material3582 1).one,v3582_mb,v3582_mg]
  upper := v3582_upper
  lower := (Primitive.Addresses.material3582 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3582_pa_checked.trans (by decide +kernel)
    · exact v3582_pb_checked.trans (by decide +kernel)
    · exact v3582_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 55 Primitive.Addresses.material3582
    · exact v3582_mb_checked.trans (by decide +kernel)
    · exact v3582_mg_checked.trans (by decide +kernel)
  upper_error := v3582_upper_checked
  lower_error := reuse_lower_error 49 55 Primitive.Addresses.material3582

def v3583_pa : Scalar.QComplex := ((999999264329818489733629155658 : Int)/10^30,(-1212987972656743525363293416 : Int)/10^30)
theorem v3583_pa_checked : Scalar.distance (sourceCoefficient 49 56 1 0) v3583_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3583_pb : Scalar.QComplex := ((-523377043103339696926580 : Int)/10^30,(-431477203293393859952769181 : Int)/10^30)
theorem v3583_pb_checked : Scalar.distance (sourceCoefficient 49 56 1 1) v3583_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3583_pg : Scalar.QComplex := ((-93086361385633957020804 : Int)/10^30,(112912719845674212286 : Int)/10^30)
theorem v3583_pg_checked : Scalar.distance (sourceCoefficient 49 56 1 2) v3583_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3583_mb : Scalar.QComplex := ((-895722241656496912657245 : Int)/10^30,(-431476590983895420273976891 : Int)/10^30)
theorem v3583_mb_checked : Scalar.distance (sourceCoefficient 49 56 3 1) v3583_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3583_mg : Scalar.QComplex := ((-93086229286735529575482 : Int)/10^30,(193242015224824754639 : Int)/10^30)
theorem v3583_mg_checked : Scalar.distance (sourceCoefficient 49 56 3 2) v3583_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3583_upper : Scalar.QComplex := ((999995681441183039489499455086 : Int)/10^30,(-2938894177062312234239032843 : Int)/10^30)
theorem v3583_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 56 5) 1) 14) v3583_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3583 : Material (49 : Basis) (56 : Basis) where
  plus := ![v3583_pa,v3583_pb,v3583_pg]
  minus := ![(Primitive.Addresses.material3583 1).one,v3583_mb,v3583_mg]
  upper := v3583_upper
  lower := (Primitive.Addresses.material3583 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3583_pa_checked.trans (by decide +kernel)
    · exact v3583_pb_checked.trans (by decide +kernel)
    · exact v3583_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 56 Primitive.Addresses.material3583
    · exact v3583_mb_checked.trans (by decide +kernel)
    · exact v3583_mg_checked.trans (by decide +kernel)
  upper_error := v3583_upper_checked
  lower_error := reuse_lower_error 49 56 Primitive.Addresses.material3583

def v3584_pa : Scalar.QComplex := ((999999249974061489660200623306 : Int)/10^30,(-1224765820261886292829753327 : Int)/10^30)
theorem v3584_pa_checked : Scalar.distance (sourceCoefficient 49 57 1 0) v3584_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3584_pb : Scalar.QComplex := ((-528458919445243323405760 : Int)/10^30,(-431477196983132937828548761 : Int)/10^30)
theorem v3584_pb_checked : Scalar.distance (sourceCoefficient 49 57 1 1) v3584_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3584_pg : Scalar.QComplex := ((-93086360036786906765120 : Int)/10^30,(114009077615414024972 : Int)/10^30)
theorem v3584_pg_checked : Scalar.distance (sourceCoefficient 49 57 1 2) v3584_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3584_mb : Scalar.QComplex := ((-900804110660714751631934 : Int)/10^30,(-431476580288206443899504835 : Int)/10^30)
theorem v3584_mb_checked : Scalar.distance (sourceCoefficient 49 57 3 1) v3584_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3584_mg : Scalar.QComplex := ((-93086226991781604392689 : Int)/10^30,(194338371422346209070 : Int)/10^30)
theorem v3584_mg_checked : Scalar.distance (sourceCoefficient 49 57 3 2) v3584_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3584_upper : Scalar.QComplex := ((999995646757950932141606758181 : Int)/10^30,(-2950671982349000278987197611 : Int)/10^30)
theorem v3584_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 57 5) 1) 14) v3584_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3584 : Material (49 : Basis) (57 : Basis) where
  plus := ![v3584_pa,v3584_pb,v3584_pg]
  minus := ![(Primitive.Addresses.material3584 1).one,v3584_mb,v3584_mg]
  upper := v3584_upper
  lower := (Primitive.Addresses.material3584 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3584_pa_checked.trans (by decide +kernel)
    · exact v3584_pb_checked.trans (by decide +kernel)
    · exact v3584_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 57 Primitive.Addresses.material3584
    · exact v3584_mb_checked.trans (by decide +kernel)
    · exact v3584_mg_checked.trans (by decide +kernel)
  upper_error := v3584_upper_checked
  lower_error := reuse_lower_error 49 57 Primitive.Addresses.material3584

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
