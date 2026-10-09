import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B072

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1729_pa : Scalar.QComplex := ((999999350086305427709346884104 : Int)/10^30,(-1140099542477221992165027467 : Int)/10^30)
theorem v1729_pa_checked : Scalar.distance (sourceCoefficient 19 77 1 0) v1729_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1729_pb : Scalar.QComplex := ((-491927252660629970476216 : Int)/10^30,(-431477177757221951999038138 : Int)/10^30)
theorem v1729_pb_checked : Scalar.distance (sourceCoefficient 19 77 1 1) v1729_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1729_pg : Scalar.QComplex := ((-93086362622445360060921 : Int)/10^30,(106127788410621796073 : Int)/10^30)
theorem v1729_pg_checked : Scalar.distance (sourceCoefficient 19 77 1 2) v1729_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1729_mb : Scalar.QComplex := ((-864272440887415244381014 : Int)/10^30,(-431476592587485726682008558 : Int)/10^30)
theorem v1729_mb_checked : Scalar.distance (sourceCoefficient 19 77 3 1) v1729_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1729_mg : Scalar.QComplex := ((-93086236378636718576325 : Int)/10^30,(186457087383424935287 : Int)/10^30)
theorem v1729_mg_checked : Scalar.distance (sourceCoefficient 19 77 3 2) v1729_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1729_upper : Scalar.QComplex := ((999995892996360356372998283076 : Int)/10^30,(-2866006003449462064199422696 : Int)/10^30)
theorem v1729_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 77 5) 1) 14) v1729_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1729 : Material (19 : Basis) (77 : Basis) where
  plus := ![v1729_pa,v1729_pb,v1729_pg]
  minus := ![(Primitive.Addresses.material1729 1).one,v1729_mb,v1729_mg]
  upper := v1729_upper
  lower := (Primitive.Addresses.material1729 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1729_pa_checked.trans (by decide +kernel)
    · exact v1729_pb_checked.trans (by decide +kernel)
    · exact v1729_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 77 Primitive.Addresses.material1729
    · exact v1729_mb_checked.trans (by decide +kernel)
    · exact v1729_mg_checked.trans (by decide +kernel)
  upper_error := v1729_upper_checked
  lower_error := reuse_lower_error 19 77 Primitive.Addresses.material1729

def v1730_pa : Scalar.QComplex := ((999999330213413839524972305274 : Int)/10^30,(-1157399120315407469286192250 : Int)/10^30)
theorem v1730_pa_checked : Scalar.distance (sourceCoefficient 19 78 1 0) v1730_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1730_pb : Scalar.QComplex := ((-499391627817383734974052 : Int)/10^30,(-431477166835481143963309499 : Int)/10^30)
theorem v1730_pb_checked : Scalar.distance (sourceCoefficient 19 78 1 1) v1730_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1730_pg : Scalar.QComplex := ((-93086360519375623021672 : Int)/10^30,(107738143940051851304 : Int)/10^30)
theorem v1730_pg_checked : Scalar.distance (sourceCoefficient 19 78 1 2) v1730_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1730_mb : Scalar.QComplex := ((-871736803839870578833249 : Int)/10^30,(-431476575224329408008393659 : Int)/10^30)
theorem v1730_mb_checked : Scalar.distance (sourceCoefficient 19 78 3 1) v1730_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1730_mg : Scalar.QComplex := ((-93086232885903470428607 : Int)/10^30,(188067440498391565708 : Int)/10^30)
theorem v1730_mg_checked : Scalar.distance (sourceCoefficient 19 78 3 2) v1730_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1730_upper : Scalar.QComplex := ((999995843265996423260034619546 : Int)/10^30,(-2883305521223150475942547943 : Int)/10^30)
theorem v1730_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 78 5) 1) 14) v1730_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1730 : Material (19 : Basis) (78 : Basis) where
  plus := ![v1730_pa,v1730_pb,v1730_pg]
  minus := ![(Primitive.Addresses.material1730 1).one,v1730_mb,v1730_mg]
  upper := v1730_upper
  lower := (Primitive.Addresses.material1730 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1730_pa_checked.trans (by decide +kernel)
    · exact v1730_pb_checked.trans (by decide +kernel)
    · exact v1730_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 78 Primitive.Addresses.material1730
    · exact v1730_mb_checked.trans (by decide +kernel)
    · exact v1730_mg_checked.trans (by decide +kernel)
  upper_error := v1730_upper_checked
  lower_error := reuse_lower_error 19 78 Primitive.Addresses.material1730

def v1731_pa : Scalar.QComplex := ((999999323742953209103969390837 : Int)/10^30,(-1162976197631834048394960141 : Int)/10^30)
theorem v1731_pa_checked : Scalar.distance (sourceCoefficient 19 79 1 0) v1731_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1731_pb : Scalar.QComplex := ((-501798010058232522459747 : Int)/10^30,(-431477163277805411581687197 : Int)/10^30)
theorem v1731_pb_checked : Scalar.distance (sourceCoefficient 19 79 1 1) v1731_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1731_pg : Scalar.QComplex := ((-93086359834455287098576 : Int)/10^30,(108257294021421439441 : Int)/10^30)
theorem v1731_pg_checked : Scalar.distance (sourceCoefficient 19 79 1 2) v1731_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1731_mb : Scalar.QComplex := ((-874143182114599355671119 : Int)/10^30,(-431476569590055505892430903 : Int)/10^30)
theorem v1731_mb_checked : Scalar.distance (sourceCoefficient 19 79 3 1) v1731_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1731_mg : Scalar.QComplex := ((-93086231752980250962397 : Int)/10^30,(188586589795402449985 : Int)/10^30)
theorem v1731_mg_checked : Scalar.distance (sourceCoefficient 19 79 3 2) v1731_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1731_upper : Scalar.QComplex := ((999995827170015930179684893285 : Int)/10^30,(-2888882579065747469252235364 : Int)/10^30)
theorem v1731_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 79 5) 1) 14) v1731_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1731 : Material (19 : Basis) (79 : Basis) where
  plus := ![v1731_pa,v1731_pb,v1731_pg]
  minus := ![(Primitive.Addresses.material1731 1).one,v1731_mb,v1731_mg]
  upper := v1731_upper
  lower := (Primitive.Addresses.material1731 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1731_pa_checked.trans (by decide +kernel)
    · exact v1731_pb_checked.trans (by decide +kernel)
    · exact v1731_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 79 Primitive.Addresses.material1731
    · exact v1731_mb_checked.trans (by decide +kernel)
    · exact v1731_mg_checked.trans (by decide +kernel)
  upper_error := v1731_upper_checked
  lower_error := reuse_lower_error 19 79 Primitive.Addresses.material1731

def v1732_pa : Scalar.QComplex := ((999999313573211512266053441052 : Int)/10^30,(-1171688143574787539777672402 : Int)/10^30)
theorem v1732_pa_checked : Scalar.distance (sourceCoefficient 19 80 1 0) v1732_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1732_pb : Scalar.QComplex := ((-505557016910222687614011 : Int)/10^30,(-431477157684555896845906554 : Int)/10^30)
theorem v1732_pb_checked : Scalar.distance (sourceCoefficient 19 80 1 1) v1732_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1732_pg : Scalar.QComplex := ((-93086358757782423712205 : Int)/10^30,(109068257752416648918 : Int)/10^30)
theorem v1732_pg_checked : Scalar.distance (sourceCoefficient 19 80 1 2) v1732_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1732_mb : Scalar.QComplex := ((-877902182740217054119262 : Int)/10^30,(-431476560752954459895481290 : Int)/10^30)
theorem v1732_mb_checked : Scalar.distance (sourceCoefficient 19 80 3 1) v1732_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1732_mg : Scalar.QComplex := ((-93086229976482613072266 : Int)/10^30,(189397552295318609983 : Int)/10^30)
theorem v1732_mg_checked : Scalar.distance (sourceCoefficient 19 80 3 2) v1732_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1732_upper : Scalar.QComplex := ((999995801964261024001813745771 : Int)/10^30,(-2897594494481229278682101892 : Int)/10^30)
theorem v1732_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 80 5) 1) 14) v1732_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1732 : Material (19 : Basis) (80 : Basis) where
  plus := ![v1732_pa,v1732_pb,v1732_pg]
  minus := ![(Primitive.Addresses.material1732 1).one,v1732_mb,v1732_mg]
  upper := v1732_upper
  lower := (Primitive.Addresses.material1732 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1732_pa_checked.trans (by decide +kernel)
    · exact v1732_pb_checked.trans (by decide +kernel)
    · exact v1732_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 80 Primitive.Addresses.material1732
    · exact v1732_mb_checked.trans (by decide +kernel)
    · exact v1732_mg_checked.trans (by decide +kernel)
  upper_error := v1732_upper_checked
  lower_error := reuse_lower_error 19 80 Primitive.Addresses.material1732

def v1733_pa : Scalar.QComplex := ((999999282493262426735400265885 : Int)/10^30,(-1197920264596358991086818999 : Int)/10^30)
theorem v1733_pa_checked : Scalar.distance (sourceCoefficient 19 81 1 0) v1733_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1733_pb : Scalar.QComplex := ((-516875581271763415667862 : Int)/10^30,(-431477140579313293799665578 : Int)/10^30)
theorem v1733_pb_checked : Scalar.distance (sourceCoefficient 19 81 1 1) v1733_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1733_pg : Scalar.QComplex := ((-93086355466089659303832 : Int)/10^30,(111510111579505218592 : Int)/10^30)
theorem v1733_pg_checked : Scalar.distance (sourceCoefficient 19 81 1 2) v1733_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1733_mb : Scalar.QComplex := ((-889220728126285011525489 : Int)/10^30,(-431476533880306951118482337 : Int)/10^30)
theorem v1733_mb_checked : Scalar.distance (sourceCoefficient 19 81 3 1) v1733_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1733_mg : Scalar.QComplex := ((-93086224577581198547945 : Int)/10^30,(191839402372610798253 : Int)/10^30)
theorem v1733_mg_checked : Scalar.distance (sourceCoefficient 19 81 3 2) v1733_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1733_upper : Scalar.QComplex := ((999995725610097104601507697212 : Int)/10^30,(-2923826522791965339085226097 : Int)/10^30)
theorem v1733_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 81 5) 1) 14) v1733_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1733 : Material (19 : Basis) (81 : Basis) where
  plus := ![v1733_pa,v1733_pb,v1733_pg]
  minus := ![(Primitive.Addresses.material1733 1).one,v1733_mb,v1733_mg]
  upper := v1733_upper
  lower := (Primitive.Addresses.material1733 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1733_pa_checked.trans (by decide +kernel)
    · exact v1733_pb_checked.trans (by decide +kernel)
    · exact v1733_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 81 Primitive.Addresses.material1733
    · exact v1733_mb_checked.trans (by decide +kernel)
    · exact v1733_mg_checked.trans (by decide +kernel)
  upper_error := v1733_upper_checked
  lower_error := reuse_lower_error 19 81 Primitive.Addresses.material1733

def v1734_pa : Scalar.QComplex := ((999999270536220512237039309028 : Int)/10^30,(-1207860516308948786233372124 : Int)/10^30)
theorem v1734_pa_checked : Scalar.distance (sourceCoefficient 19 82 1 0) v1734_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1734_pb : Scalar.QComplex := ((-521164574012323672855863 : Int)/10^30,(-431477133994120428605292975 : Int)/10^30)
theorem v1734_pb_checked : Scalar.distance (sourceCoefficient 19 82 1 1) v1734_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1734_pg : Scalar.QComplex := ((-93086354199229777402020 : Int)/10^30,(112435413861961305897 : Int)/10^30)
theorem v1734_pg_checked : Scalar.distance (sourceCoefficient 19 82 1 2) v1734_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1734_mb : Scalar.QComplex := ((-893509713587132398165355 : Int)/10^30,(-431476523593908971851131853 : Int)/10^30)
theorem v1734_mb_checked : Scalar.distance (sourceCoefficient 19 82 3 1) v1734_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1734_mg : Scalar.QComplex := ((-93086222512227592664149 : Int)/10^30,(192764703217291536566 : Int)/10^30)
theorem v1734_mg_checked : Scalar.distance (sourceCoefficient 19 82 3 2) v1734_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1734_upper : Scalar.QComplex := ((999995696497100315373624395784 : Int)/10^30,(-2933766739062948262264194144 : Int)/10^30)
theorem v1734_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 82 5) 1) 14) v1734_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1734 : Material (19 : Basis) (82 : Basis) where
  plus := ![v1734_pa,v1734_pb,v1734_pg]
  minus := ![(Primitive.Addresses.material1734 1).one,v1734_mb,v1734_mg]
  upper := v1734_upper
  lower := (Primitive.Addresses.material1734 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1734_pa_checked.trans (by decide +kernel)
    · exact v1734_pb_checked.trans (by decide +kernel)
    · exact v1734_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 82 Primitive.Addresses.material1734
    · exact v1734_mb_checked.trans (by decide +kernel)
    · exact v1734_mg_checked.trans (by decide +kernel)
  upper_error := v1734_upper_checked
  lower_error := reuse_lower_error 19 82 Primitive.Addresses.material1734

def v1735_pa : Scalar.QComplex := ((999999254055165496698021441539 : Int)/10^30,(-1221429127118273626998726544 : Int)/10^30)
theorem v1735_pa_checked : Scalar.distance (sourceCoefficient 19 83 1 0) v1735_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1735_pb : Scalar.QComplex := ((-527019121181747467404795 : Int)/10^30,(-431477124913465382654193233 : Int)/10^30)
theorem v1735_pb_checked : Scalar.distance (sourceCoefficient 19 83 1 1) v1735_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1735_pg : Scalar.QComplex := ((-93086352452623808338468 : Int)/10^30,(113698467035616443769 : Int)/10^30)
theorem v1735_pg_checked : Scalar.distance (sourceCoefficient 19 83 1 2) v1735_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1735_mb : Scalar.QComplex := ((-899364250740444388379648 : Int)/10^30,(-431476509461046778846463124 : Int)/10^30)
theorem v1735_mb_checked : Scalar.distance (sourceCoefficient 19 83 3 1) v1735_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1735_mg : Scalar.QComplex := ((-93086219675664270880681 : Int)/10^30,(194027754413411966415 : Int)/10^30)
theorem v1735_mg_checked : Scalar.distance (sourceCoefficient 19 83 3 2) v1735_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1735_upper : Scalar.QComplex := ((999995656597878524292463606162 : Int)/10^30,(-2947335301218615376341091271 : Int)/10^30)
theorem v1735_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 83 5) 1) 14) v1735_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1735 : Material (19 : Basis) (83 : Basis) where
  plus := ![v1735_pa,v1735_pb,v1735_pg]
  minus := ![(Primitive.Addresses.material1735 1).one,v1735_mb,v1735_mg]
  upper := v1735_upper
  lower := (Primitive.Addresses.material1735 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1735_pa_checked.trans (by decide +kernel)
    · exact v1735_pb_checked.trans (by decide +kernel)
    · exact v1735_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 83 Primitive.Addresses.material1735
    · exact v1735_mb_checked.trans (by decide +kernel)
    · exact v1735_mg_checked.trans (by decide +kernel)
  upper_error := v1735_upper_checked
  lower_error := reuse_lower_error 19 83 Primitive.Addresses.material1735

def v1736_pa : Scalar.QComplex := ((999999210517921349086906787121 : Int)/10^30,(-1256568157331656114993066176 : Int)/10^30)
theorem v1736_pa_checked : Scalar.distance (sourceCoefficient 19 84 1 0) v1736_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1736_pb : Scalar.QComplex := ((-542180813656657560811008 : Int)/10^30,(-431477100904698296851003177 : Int)/10^30)
theorem v1736_pb_checked : Scalar.distance (sourceCoefficient 19 84 1 1) v1736_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1736_pg : Scalar.QComplex := ((-93086347836449534233555 : Int)/10^30,(116969432918852024532 : Int)/10^30)
theorem v1736_pg_checked : Scalar.distance (sourceCoefficient 19 84 1 2) v1736_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1736_mb : Scalar.QComplex := ((-914525916851478769480712 : Int)/10^30,(-431476472368430884037319540 : Int)/10^30)
theorem v1736_mb_checked : Scalar.distance (sourceCoefficient 19 84 3 1) v1736_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1736_mg : Scalar.QComplex := ((-93086212236795477190762 : Int)/10^30,(197298715095166964542 : Int)/10^30)
theorem v1736_mg_checked : Scalar.distance (sourceCoefficient 19 84 3 2) v1736_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1736_upper : Scalar.QComplex := ((999995552413920859913413981728 : Int)/10^30,(-2982474203955206351106800213 : Int)/10^30)
theorem v1736_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 84 5) 1) 14) v1736_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1736 : Material (19 : Basis) (84 : Basis) where
  plus := ![v1736_pa,v1736_pb,v1736_pg]
  minus := ![(Primitive.Addresses.material1736 1).one,v1736_mb,v1736_mg]
  upper := v1736_upper
  lower := (Primitive.Addresses.material1736 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1736_pa_checked.trans (by decide +kernel)
    · exact v1736_pb_checked.trans (by decide +kernel)
    · exact v1736_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 84 Primitive.Addresses.material1736
    · exact v1736_mb_checked.trans (by decide +kernel)
    · exact v1736_mg_checked.trans (by decide +kernel)
  upper_error := v1736_upper_checked
  lower_error := reuse_lower_error 19 84 Primitive.Addresses.material1736

def v1737_pa : Scalar.QComplex := ((999999108052654306720704041947 : Int)/10^30,(-1335624908354322022910447714 : Int)/10^30)
theorem v1737_pa_checked : Scalar.distance (sourceCoefficient 19 85 1 0) v1737_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1737_pb : Scalar.QComplex := ((-576292001761897461400789 : Int)/10^30,(-431477044292209565798751015 : Int)/10^30)
theorem v1737_pb_checked : Scalar.distance (sourceCoefficient 19 85 1 1) v1737_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1737_pg : Scalar.QComplex := ((-93086336960632186803484 : Int)/10^30,(124328541166596190802 : Int)/10^30)
theorem v1737_pg_checked : Scalar.distance (sourceCoefficient 19 85 1 2) v1737_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1737_mb : Scalar.QComplex := ((-948637043401536337123024 : Int)/10^30,(-431476386319544208461625622 : Int)/10^30)
theorem v1737_mb_checked : Scalar.distance (sourceCoefficient 19 85 3 1) v1737_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1737_mg : Scalar.QComplex := ((-93086195010403203453099 : Int)/10^30,(204657811217438260113 : Int)/10^30)
theorem v1737_mg_checked : Scalar.distance (sourceCoefficient 19 85 3 2) v1737_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1737_upper : Scalar.QComplex := ((999995313504026134833100164730 : Int)/10^30,(-3061530660386372930379560954 : Int)/10^30)
theorem v1737_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 85 5) 1) 14) v1737_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1737 : Material (19 : Basis) (85 : Basis) where
  plus := ![v1737_pa,v1737_pb,v1737_pg]
  minus := ![(Primitive.Addresses.material1737 1).one,v1737_mb,v1737_mg]
  upper := v1737_upper
  lower := (Primitive.Addresses.material1737 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1737_pa_checked.trans (by decide +kernel)
    · exact v1737_pb_checked.trans (by decide +kernel)
    · exact v1737_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 85 Primitive.Addresses.material1737
    · exact v1737_mb_checked.trans (by decide +kernel)
    · exact v1737_mg_checked.trans (by decide +kernel)
  upper_error := v1737_upper_checked
  lower_error := reuse_lower_error 19 85 Primitive.Addresses.material1737

def v1738_pa : Scalar.QComplex := ((999999088466684540259629565132 : Int)/10^30,(-1350209539303620661485712295 : Int)/10^30)
theorem v1738_pa_checked : Scalar.distance (sourceCoefficient 19 86 1 0) v1738_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1738_pb : Scalar.QComplex := ((-582584937607368087113375 : Int)/10^30,(-431477033455310991288712217 : Int)/10^30)
theorem v1738_pb_checked : Scalar.distance (sourceCoefficient 19 86 1 1) v1738_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1738_pg : Scalar.QComplex := ((-93086334880068589810043 : Int)/10^30,(125686171901012945881 : Int)/10^30)
theorem v1738_pg_checked : Scalar.distance (sourceCoefficient 19 86 1 2) v1738_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1738_mb : Scalar.QComplex := ((-954929967552103952182369 : Int)/10^30,(-431476370052129457692359059 : Int)/10^30)
theorem v1738_mb_checked : Scalar.distance (sourceCoefficient 19 86 3 1) v1738_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1738_mg : Scalar.QComplex := ((-93086191758266202765365 : Int)/10^30,(206015439650914366880 : Int)/10^30)
theorem v1738_mg_checked : Scalar.distance (sourceCoefficient 19 86 3 2) v1738_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1738_upper : Scalar.QComplex := ((999995268746335628267985710132 : Int)/10^30,(-3076115235809970009459330041 : Int)/10^30)
theorem v1738_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 86 5) 1) 14) v1738_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1738 : Material (19 : Basis) (86 : Basis) where
  plus := ![v1738_pa,v1738_pb,v1738_pg]
  minus := ![(Primitive.Addresses.material1738 1).one,v1738_mb,v1738_mg]
  upper := v1738_upper
  lower := (Primitive.Addresses.material1738 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1738_pa_checked.trans (by decide +kernel)
    · exact v1738_pb_checked.trans (by decide +kernel)
    · exact v1738_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 86 Primitive.Addresses.material1738
    · exact v1738_mb_checked.trans (by decide +kernel)
    · exact v1738_mg_checked.trans (by decide +kernel)
  upper_error := v1738_upper_checked
  lower_error := reuse_lower_error 19 86 Primitive.Addresses.material1738

def v1739_pa : Scalar.QComplex := ((999999087162244639440606854830 : Int)/10^30,(-1351175294863087398133309921 : Int)/10^30)
theorem v1739_pa_checked : Scalar.distance (sourceCoefficient 19 87 1 0) v1739_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1739_pb : Scalar.QComplex := ((-583001639116109922855297 : Int)/10^30,(-431477032733400401445218857 : Int)/10^30)
theorem v1739_pb_checked : Scalar.distance (sourceCoefficient 19 87 1 1) v1739_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1739_pg : Scalar.QComplex := ((-93086334741483710981520 : Int)/10^30,(125776070605194278952 : Int)/10^30)
theorem v1739_pg_checked : Scalar.distance (sourceCoefficient 19 87 1 2) v1739_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1739_mb : Scalar.QComplex := ((-955346668282712446631022 : Int)/10^30,(-431476368970624502144236924 : Int)/10^30)
theorem v1739_mb_checked : Scalar.distance (sourceCoefficient 19 87 3 1) v1739_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1739_mg : Scalar.QComplex := ((-93086191542102842717171 : Int)/10^30,(206105338202029795013 : Int)/10^30)
theorem v1739_mg_checked : Scalar.distance (sourceCoefficient 19 87 3 2) v1739_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1739_upper : Scalar.QComplex := ((999995265775091187279339822507 : Int)/10^30,(-3077080987679712354948122793 : Int)/10^30)
theorem v1739_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 87 5) 1) 14) v1739_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1739 : Material (19 : Basis) (87 : Basis) where
  plus := ![v1739_pa,v1739_pb,v1739_pg]
  minus := ![(Primitive.Addresses.material1739 1).one,v1739_mb,v1739_mg]
  upper := v1739_upper
  lower := (Primitive.Addresses.material1739 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1739_pa_checked.trans (by decide +kernel)
    · exact v1739_pb_checked.trans (by decide +kernel)
    · exact v1739_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 87 Primitive.Addresses.material1739
    · exact v1739_mb_checked.trans (by decide +kernel)
    · exact v1739_mg_checked.trans (by decide +kernel)
  upper_error := v1739_upper_checked
  lower_error := reuse_lower_error 19 87 Primitive.Addresses.material1739

def v1740_pa : Scalar.QComplex := ((999999071203828392884592743507 : Int)/10^30,(-1362934877590232637039795587 : Int)/10^30)
theorem v1740_pa_checked : Scalar.distance (sourceCoefficient 19 88 1 0) v1740_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1740_pb : Scalar.QComplex := ((-588075630954492040745027 : Int)/10^30,(-431477023899965525011220411 : Int)/10^30)
theorem v1740_pb_checked : Scalar.distance (sourceCoefficient 19 88 1 1) v1740_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1740_pg : Scalar.QComplex := ((-93086333045870516098221 : Int)/10^30,(126870727772243402910 : Int)/10^30)
theorem v1740_pg_checked : Scalar.distance (sourceCoefficient 19 88 1 2) v1740_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1740_mb : Scalar.QComplex := ((-960420650608959054983997 : Int)/10^30,(-431476355758566482387170193 : Int)/10^30)
theorem v1740_mb_checked : Scalar.distance (sourceCoefficient 19 88 3 1) v1740_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1740_mg : Scalar.QComplex := ((-93086188901850445553409 : Int)/10^30,(207199993498250207774 : Int)/10^30)
theorem v1740_mg_checked : Scalar.distance (sourceCoefficient 19 88 3 2) v1740_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1740_upper : Scalar.QComplex := ((999995229520725742868493553766 : Int)/10^30,(-3088840525349561794052503669 : Int)/10^30)
theorem v1740_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 88 5) 1) 14) v1740_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1740 : Material (19 : Basis) (88 : Basis) where
  plus := ![v1740_pa,v1740_pb,v1740_pg]
  minus := ![(Primitive.Addresses.material1740 1).one,v1740_mb,v1740_mg]
  upper := v1740_upper
  lower := (Primitive.Addresses.material1740 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1740_pa_checked.trans (by decide +kernel)
    · exact v1740_pb_checked.trans (by decide +kernel)
    · exact v1740_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 88 Primitive.Addresses.material1740
    · exact v1740_mb_checked.trans (by decide +kernel)
    · exact v1740_mg_checked.trans (by decide +kernel)
  upper_error := v1740_upper_checked
  lower_error := reuse_lower_error 19 88 Primitive.Addresses.material1740

def v1741_pa : Scalar.QComplex := ((999999049145473133043398927493 : Int)/10^30,(-1379024346996666313303716432 : Int)/10^30)
theorem v1741_pa_checked : Scalar.distance (sourceCoefficient 19 89 1 0) v1741_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1741_pb : Scalar.QComplex := ((-595017870058640885801917 : Int)/10^30,(-431477011685163512912424680 : Int)/10^30)
theorem v1741_pb_checked : Scalar.distance (sourceCoefficient 19 89 1 1) v1741_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1741_pg : Scalar.QComplex := ((-93086330701600551113805 : Int)/10^30,(128368438469801257045 : Int)/10^30)
theorem v1741_pg_checked : Scalar.distance (sourceCoefficient 19 89 1 2) v1741_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1741_mb : Scalar.QComplex := ((-967362876587371003384881 : Int)/10^30,(-431476337552929338379466402 : Int)/10^30)
theorem v1741_mb_checked : Scalar.distance (sourceCoefficient 19 89 3 1) v1741_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1741_mg : Scalar.QComplex := ((-93086185265124475841205 : Int)/10^30,(208697701615142522666 : Int)/10^30)
theorem v1741_mg_checked : Scalar.distance (sourceCoefficient 19 89 3 2) v1741_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1741_upper : Scalar.QComplex := ((999995179693438766114362445444 : Int)/10^30,(-3104929932721900731146725100 : Int)/10^30)
theorem v1741_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 89 5) 1) 14) v1741_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1741 : Material (19 : Basis) (89 : Basis) where
  plus := ![v1741_pa,v1741_pb,v1741_pg]
  minus := ![(Primitive.Addresses.material1741 1).one,v1741_mb,v1741_mg]
  upper := v1741_upper
  lower := (Primitive.Addresses.material1741 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1741_pa_checked.trans (by decide +kernel)
    · exact v1741_pb_checked.trans (by decide +kernel)
    · exact v1741_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 89 Primitive.Addresses.material1741
    · exact v1741_mb_checked.trans (by decide +kernel)
    · exact v1741_mg_checked.trans (by decide +kernel)
  upper_error := v1741_upper_checked
  lower_error := reuse_lower_error 19 89 Primitive.Addresses.material1741

def v1742_pa : Scalar.QComplex := ((999999012667681845552618103533 : Int)/10^30,(-1405227263286543374043519146 : Int)/10^30)
theorem v1742_pa_checked : Scalar.distance (sourceCoefficient 19 90 1 0) v1742_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1742_pb : Scalar.QComplex := ((-606323830542761612325306 : Int)/10^30,(-431476991473664268992442712 : Int)/10^30)
theorem v1742_pb_checked : Scalar.distance (sourceCoefficient 19 90 1 1) v1742_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1742_pg : Scalar.QComplex := ((-93086326823604853375867 : Int)/10^30,(130807573442275720988 : Int)/10^30)
theorem v1742_pg_checked : Scalar.distance (sourceCoefficient 19 90 1 2) v1742_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1742_mb : Scalar.QComplex := ((-978668815420152378381478 : Int)/10^30,(-431476307584902923885931560 : Int)/10^30)
theorem v1742_mb_checked : Scalar.distance (sourceCoefficient 19 90 3 1) v1742_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1742_mg : Scalar.QComplex := ((-93086179282266595374003 : Int)/10^30,(211136832332879933676 : Int)/10^30)
theorem v1742_mg_checked : Scalar.distance (sourceCoefficient 19 90 3 2) v1742_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1742_upper : Scalar.QComplex := ((999995097991845401677768520297 : Int)/10^30,(-3131132747028253466046672317 : Int)/10^30)
theorem v1742_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 90 5) 1) 14) v1742_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1742 : Material (19 : Basis) (90 : Basis) where
  plus := ![v1742_pa,v1742_pb,v1742_pg]
  minus := ![(Primitive.Addresses.material1742 1).one,v1742_mb,v1742_mg]
  upper := v1742_upper
  lower := (Primitive.Addresses.material1742 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1742_pa_checked.trans (by decide +kernel)
    · exact v1742_pb_checked.trans (by decide +kernel)
    · exact v1742_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 90 Primitive.Addresses.material1742
    · exact v1742_mb_checked.trans (by decide +kernel)
    · exact v1742_mg_checked.trans (by decide +kernel)
  upper_error := v1742_upper_checked
  lower_error := reuse_lower_error 19 90 Primitive.Addresses.material1742

def v1743_pa : Scalar.QComplex := ((999998991816077958049921525372 : Int)/10^30,(-1419988319546706515464475222 : Int)/10^30)
theorem v1743_pa_checked : Scalar.distance (sourceCoefficient 19 91 1 0) v1743_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1743_pb : Scalar.QComplex := ((-612692889338084853935814 : Int)/10^30,(-431476979913856177051473303 : Int)/10^30)
theorem v1743_pb_checked : Scalar.distance (sourceCoefficient 19 91 1 1) v1743_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1743_pg : Scalar.QComplex := ((-93086324606154768038215 : Int)/10^30,(132181626913663989987 : Int)/10^30)
theorem v1743_pg_checked : Scalar.distance (sourceCoefficient 19 91 1 2) v1743_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1743_mb : Scalar.QComplex := ((-985037861868390201211082 : Int)/10^30,(-431476290528888247585570104 : Int)/10^30)
theorem v1743_mb_checked : Scalar.distance (sourceCoefficient 19 91 3 1) v1743_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1743_mg : Scalar.QComplex := ((-93086175879071074957353 : Int)/10^30,(212510883379085744529 : Int)/10^30)
theorem v1743_mg_checked : Scalar.distance (sourceCoefficient 19 91 3 2) v1743_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1743_upper : Scalar.QComplex := ((999995051664028577711427545881 : Int)/10^30,(-3145893745315580596324994445 : Int)/10^30)
theorem v1743_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 91 5) 1) 14) v1743_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1743 : Material (19 : Basis) (91 : Basis) where
  plus := ![v1743_pa,v1743_pb,v1743_pg]
  minus := ![(Primitive.Addresses.material1743 1).one,v1743_mb,v1743_mg]
  upper := v1743_upper
  lower := (Primitive.Addresses.material1743 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1743_pa_checked.trans (by decide +kernel)
    · exact v1743_pb_checked.trans (by decide +kernel)
    · exact v1743_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 91 Primitive.Addresses.material1743
    · exact v1743_mb_checked.trans (by decide +kernel)
    · exact v1743_mg_checked.trans (by decide +kernel)
  upper_error := v1743_upper_checked
  lower_error := reuse_lower_error 19 91 Primitive.Addresses.material1743

def v1744_pa : Scalar.QComplex := ((999998945928186843437714097886 : Int)/10^30,(-1451944391237397659255504231 : Int)/10^30)
theorem v1744_pa_checked : Scalar.distance (sourceCoefficient 19 92 1 0) v1744_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1744_pb : Scalar.QComplex := ((-626481204330684964616394 : Int)/10^30,(-431476954458701709501850542 : Int)/10^30)
theorem v1744_pb_checked : Scalar.distance (sourceCoefficient 19 92 1 1) v1744_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1744_pg : Scalar.QComplex := ((-93086319724552898854018 : Int)/10^30,(135156302289444334656 : Int)/10^30)
theorem v1744_pg_checked : Scalar.distance (sourceCoefficient 19 92 1 2) v1744_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1744_mb : Scalar.QComplex := ((-998826149760318635124473 : Int)/10^30,(-431476253175048422193982695 : Int)/10^30)
theorem v1744_mb_checked : Scalar.distance (sourceCoefficient 19 92 3 1) v1744_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1744_mg : Scalar.QComplex := ((-93086168430460148523757 : Int)/10^30,(215485553434655943496 : Int)/10^30)
theorem v1744_mg_checked : Scalar.distance (sourceCoefficient 19 92 3 2) v1744_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1744_upper : Scalar.QComplex := ((999994950622925101767533710360 : Int)/10^30,(-3177849690213119633846423136 : Int)/10^30)
theorem v1744_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 92 5) 1) 14) v1744_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1744 : Material (19 : Basis) (92 : Basis) where
  plus := ![v1744_pa,v1744_pb,v1744_pg]
  minus := ![(Primitive.Addresses.material1744 1).one,v1744_mb,v1744_mg]
  upper := v1744_upper
  lower := (Primitive.Addresses.material1744 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1744_pa_checked.trans (by decide +kernel)
    · exact v1744_pb_checked.trans (by decide +kernel)
    · exact v1744_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 92 Primitive.Addresses.material1744
    · exact v1744_mb_checked.trans (by decide +kernel)
    · exact v1744_mg_checked.trans (by decide +kernel)
  upper_error := v1744_upper_checked
  lower_error := reuse_lower_error 19 92 Primitive.Addresses.material1744

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
