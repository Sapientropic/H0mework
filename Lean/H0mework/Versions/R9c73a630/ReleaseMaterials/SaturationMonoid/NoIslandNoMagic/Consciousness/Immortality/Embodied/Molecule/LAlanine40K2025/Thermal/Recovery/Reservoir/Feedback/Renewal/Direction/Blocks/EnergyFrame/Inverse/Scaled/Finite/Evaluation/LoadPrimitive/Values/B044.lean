import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B029
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B030

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v705_pa : Scalar.QComplex := ((999999885041180031454841942256 : Int)/10^30,(-479497264561081753367728869 : Int)/10^30)
theorem v705_pa_checked : Scalar.distance (sourceCoefficient 7 55 1 0) v705_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v705_pb : Scalar.QComplex := ((-206892269582221075630752 : Int)/10^30,(-431477426649166016433366770 : Int)/10^30)
theorem v705_pb_checked : Scalar.distance (sourceCoefficient 7 55 1 1) v705_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v705_pg : Scalar.QComplex := ((-93086414368786112009038 : Int)/10^30,(44634686188783170227 : Int)/10^30)
theorem v705_pg_checked : Scalar.distance (sourceCoefficient 7 55 1 2) v705_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v705_mb : Scalar.QComplex := ((-579237778723095342456925 : Int)/10^30,(-431477087451690014850029513 : Int)/10^30)
theorem v705_mb_checked : Scalar.distance (sourceCoefficient 7 55 3 1) v705_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v705_mg : Scalar.QComplex := ((-93086341190735873929917 : Int)/10^30,(124964052713040140497 : Int)/10^30)
theorem v705_mg_checked : Scalar.distance (sourceCoefficient 7 55 3 2) v705_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v705_upper : Scalar.QComplex := ((999997568090040520421036353248 : Int)/10^30,(-2205405632706397825782624578 : Int)/10^30)
theorem v705_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 55 5) 1) 14) v705_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material705 : Material (7 : Basis) (55 : Basis) where
  plus := ![v705_pa,v705_pb,v705_pg]
  minus := ![(Primitive.Addresses.material705 1).one,v705_mb,v705_mg]
  upper := v705_upper
  lower := (Primitive.Addresses.material705 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v705_pa_checked.trans (by decide +kernel)
    · exact v705_pb_checked.trans (by decide +kernel)
    · exact v705_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 55 Primitive.Addresses.material705
    · exact v705_mb_checked.trans (by decide +kernel)
    · exact v705_mg_checked.trans (by decide +kernel)
  upper_error := v705_upper_checked
  lower_error := reuse_lower_error 7 55 Primitive.Addresses.material705

def v706_pa : Scalar.QComplex := ((999999883288477911627392858182 : Int)/10^30,(-483138728063861411348988977 : Int)/10^30)
theorem v706_pa_checked : Scalar.distance (sourceCoefficient 7 56 1 0) v706_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v706_pb : Scalar.QComplex := ((-208463478864194490823976 : Int)/10^30,(-431477425478815714790388048 : Int)/10^30)
theorem v706_pb_checked : Scalar.distance (sourceCoefficient 7 56 1 1) v706_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v706_pg : Scalar.QComplex := ((-93086414160964752400556 : Int)/10^30,(44973656986698288311 : Int)/10^30)
theorem v706_pg_checked : Scalar.distance (sourceCoefficient 7 56 1 2) v706_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v706_mb : Scalar.QComplex := ((-580808986410076134462867 : Int)/10^30,(-431477084925457303278051630 : Int)/10^30)
theorem v706_mb_checked : Scalar.distance (sourceCoefficient 7 56 3 1) v706_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v706_mg : Scalar.QComplex := ((-93086340690398059780091 : Int)/10^30,(125303023205400465371 : Int)/10^30)
theorem v706_mg_checked : Scalar.distance (sourceCoefficient 7 56 3 2) v706_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v706_upper : Scalar.QComplex := ((999997560052505356228230088843 : Int)/10^30,(-2209047087760640497796928792 : Int)/10^30)
theorem v706_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 56 5) 1) 14) v706_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material706 : Material (7 : Basis) (56 : Basis) where
  plus := ![v706_pa,v706_pb,v706_pg]
  minus := ![(Primitive.Addresses.material706 1).one,v706_mb,v706_mg]
  upper := v706_upper
  lower := (Primitive.Addresses.material706 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v706_pa_checked.trans (by decide +kernel)
    · exact v706_pb_checked.trans (by decide +kernel)
    · exact v706_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 56 Primitive.Addresses.material706
    · exact v706_mb_checked.trans (by decide +kernel)
    · exact v706_mg_checked.trans (by decide +kernel)
  upper_error := v706_upper_checked
  lower_error := reuse_lower_error 7 56 Primitive.Addresses.material706

def v707_pa : Scalar.QComplex := ((999999877528780431435239412619 : Int)/10^30,(-494916583009631935856015954 : Int)/10^30)
theorem v707_pa_checked : Scalar.distance (sourceCoefficient 7 57 1 0) v707_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v707_pb : Scalar.QComplex := ((-213545357317641976129875 : Int)/10^30,(-431477421641225687894881758 : Int)/10^30)
theorem v707_pb_checked : Scalar.distance (sourceCoefficient 7 57 1 1) v707_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v707_pg : Scalar.QComplex := ((-93086413478931435677602 : Int)/10^30,(46070015325865453502 : Int)/10^30)
theorem v707_pg_checked : Scalar.distance (sourceCoefficient 7 57 1 2) v707_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v707_mb : Scalar.QComplex := ((-585890859659640663659316 : Int)/10^30,(-431477076702436479276663005 : Int)/10^30)
theorem v707_mb_checked : Scalar.distance (sourceCoefficient 7 57 3 1) v707_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v707_mg : Scalar.QComplex := ((-93086339062257128454641 : Int)/10^30,(126399380547779280147 : Int)/10^30)
theorem v707_mg_checked : Scalar.distance (sourceCoefficient 7 57 3 2) v707_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v707_upper : Scalar.QComplex := ((999997533965307296683149594919 : Int)/10^30,(-2220824915223964269470029771 : Int)/10^30)
theorem v707_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 57 5) 1) 14) v707_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material707 : Material (7 : Basis) (57 : Basis) where
  plus := ![v707_pa,v707_pb,v707_pg]
  minus := ![(Primitive.Addresses.material707 1).one,v707_mb,v707_mg]
  upper := v707_upper
  lower := (Primitive.Addresses.material707 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v707_pa_checked.trans (by decide +kernel)
    · exact v707_pb_checked.trans (by decide +kernel)
    · exact v707_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 57 Primitive.Addresses.material707
    · exact v707_mb_checked.trans (by decide +kernel)
    · exact v707_mg_checked.trans (by decide +kernel)
  upper_error := v707_upper_checked
  lower_error := reuse_lower_error 7 57 Primitive.Addresses.material707

def v708_pa : Scalar.QComplex := ((999999874345571554287786606164 : Int)/10^30,(-501307132506998187402622421 : Int)/10^30)
theorem v708_pa_checked : Scalar.distance (sourceCoefficient 7 58 1 0) v708_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v708_pb : Scalar.QComplex := ((-216302735103288424049497 : Int)/10^30,(-431477419525588564331185802 : Int)/10^30)
theorem v708_pb_checked : Scalar.distance (sourceCoefficient 7 58 1 1) v708_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v708_pg : Scalar.QComplex := ((-93086413102562183713140 : Int)/10^30,(46664888691457229892 : Int)/10^30)
theorem v708_pg_checked : Scalar.distance (sourceCoefficient 7 58 1 2) v708_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v708_mb : Scalar.QComplex := ((-588648234592889790715966 : Int)/10^30,(-431477072207307302133874927 : Int)/10^30)
theorem v708_mb_checked : Scalar.distance (sourceCoefficient 7 58 3 1) v708_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v708_mg : Scalar.QComplex := ((-93086338172539094225766 : Int)/10^30,(126994253367082802067 : Int)/10^30)
theorem v708_mg_checked : Scalar.distance (sourceCoefficient 7 58 3 2) v708_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v708_upper : Scalar.QComplex := ((999997519752594474218916041723 : Int)/10^30,(-2227215449709427987863445907 : Int)/10^30)
theorem v708_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 58 5) 1) 14) v708_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material708 : Material (7 : Basis) (58 : Basis) where
  plus := ![v708_pa,v708_pb,v708_pg]
  minus := ![(Primitive.Addresses.material708 1).one,v708_mb,v708_mg]
  upper := v708_upper
  lower := (Primitive.Addresses.material708 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v708_pa_checked.trans (by decide +kernel)
    · exact v708_pb_checked.trans (by decide +kernel)
    · exact v708_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 58 Primitive.Addresses.material708
    · exact v708_mb_checked.trans (by decide +kernel)
    · exact v708_mg_checked.trans (by decide +kernel)
  upper_error := v708_upper_checked
  lower_error := reuse_lower_error 7 58 Primitive.Addresses.material708

def v709_pa : Scalar.QComplex := ((999999865385366172523261807335 : Int)/10^30,(-518873057244114223510447788 : Int)/10^30)
theorem v709_pa_checked : Scalar.distance (sourceCoefficient 7 59 1 0) v709_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v709_pb : Scalar.QComplex := ((-223882034858617049762494 : Int)/10^30,(-431477413589214621600114044 : Int)/10^30)
theorem v709_pb_checked : Scalar.distance (sourceCoefficient 7 59 1 1) v709_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v709_pg : Scalar.QComplex := ((-93086412045172407787204 : Int)/10^30,(48300037707655836386 : Int)/10^30)
theorem v709_pg_checked : Scalar.distance (sourceCoefficient 7 59 1 2) v709_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v709_mb : Scalar.QComplex := ((-596227526403275378189663 : Int)/10^30,(-431477059730341239926662428 : Int)/10^30)
theorem v709_mb_checked : Scalar.distance (sourceCoefficient 7 59 3 1) v709_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v709_mg : Scalar.QComplex := ((-93086335704089755412853 : Int)/10^30,(128629400861960946273 : Int)/10^30)
theorem v709_mg_checked : Scalar.distance (sourceCoefficient 7 59 3 2) v709_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v709_upper : Scalar.QComplex := ((999997480475209909609368584777 : Int)/10^30,(-2244781332819660941062126637 : Int)/10^30)
theorem v709_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 59 5) 1) 14) v709_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material709 : Material (7 : Basis) (59 : Basis) where
  plus := ![v709_pa,v709_pb,v709_pg]
  minus := ![(Primitive.Addresses.material709 1).one,v709_mb,v709_mg]
  upper := v709_upper
  lower := (Primitive.Addresses.material709 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v709_pa_checked.trans (by decide +kernel)
    · exact v709_pb_checked.trans (by decide +kernel)
    · exact v709_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 59 Primitive.Addresses.material709
    · exact v709_mb_checked.trans (by decide +kernel)
    · exact v709_mg_checked.trans (by decide +kernel)
  upper_error := v709_upper_checked
  lower_error := reuse_lower_error 7 59 Primitive.Addresses.material709

def v710_pa : Scalar.QComplex := ((999999854665645352622939384232 : Int)/10^30,(-539136984608438340868642813 : Int)/10^30)
theorem v710_pa_checked : Scalar.distance (sourceCoefficient 7 60 1 0) v710_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v710_pb : Scalar.QComplex := ((-232625461686628339185936 : Int)/10^30,(-431477406520546906249714024 : Int)/10^30)
theorem v710_pb_checked : Scalar.distance (sourceCoefficient 7 60 1 1) v710_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v710_pg : Scalar.QComplex := ((-93086410783749292618600 : Int)/10^30,(50186334111771491421 : Int)/10^30)
theorem v710_pg_checked : Scalar.distance (sourceCoefficient 7 60 1 2) v710_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v710_mb : Scalar.QComplex := ((-604970943875767387826490 : Int)/10^30,(-431477045116492593316750844 : Int)/10^30)
theorem v710_mb_checked : Scalar.distance (sourceCoefficient 7 60 3 1) v710_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v710_mg : Scalar.QComplex := ((-93086332814878268814254 : Int)/10^30,(130515695475170906049 : Int)/10^30)
theorem v710_mg_checked : Scalar.distance (sourceCoefficient 7 60 3 2) v710_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v710_upper : Scalar.QComplex := ((999997434781804753780806364807 : Int)/10^30,(-2265045211501979967707688024 : Int)/10^30)
theorem v710_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 60 5) 1) 14) v710_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material710 : Material (7 : Basis) (60 : Basis) where
  plus := ![v710_pa,v710_pb,v710_pg]
  minus := ![(Primitive.Addresses.material710 1).one,v710_mb,v710_mg]
  upper := v710_upper
  lower := (Primitive.Addresses.material710 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v710_pa_checked.trans (by decide +kernel)
    · exact v710_pb_checked.trans (by decide +kernel)
    · exact v710_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 60 Primitive.Addresses.material710
    · exact v710_mb_checked.trans (by decide +kernel)
    · exact v710_mg_checked.trans (by decide +kernel)
  upper_error := v710_upper_checked
  lower_error := reuse_lower_error 7 60 Primitive.Addresses.material710

def v711_pa : Scalar.QComplex := ((999999851489494928614406521876 : Int)/10^30,(-544996319333810795231052564 : Int)/10^30)
theorem v711_pa_checked : Scalar.distance (sourceCoefficient 7 61 1 0) v711_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v711_pb : Scalar.QComplex := ((-235153632214260635775956 : Int)/10^30,(-431477404432605224196717454 : Int)/10^30)
theorem v711_pb_checked : Scalar.distance (sourceCoefficient 7 61 1 1) v711_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v711_pg : Scalar.QComplex := ((-93086410410696053851276 : Int)/10^30,(50731758588024967328 : Int)/10^30)
theorem v711_pg_checked : Scalar.distance (sourceCoefficient 7 61 1 2) v711_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v711_mb : Scalar.QComplex := ((-607499111660246619668739 : Int)/10^30,(-431477040846854387926907091 : Int)/10^30)
theorem v711_mb_checked : Scalar.distance (sourceCoefficient 7 61 3 1) v711_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v711_mg : Scalar.QComplex := ((-93086331971148410951465 : Int)/10^30,(131061119426409778955 : Int)/10^30)
theorem v711_mg_checked : Scalar.distance (sourceCoefficient 7 61 3 2) v711_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v711_upper : Scalar.QComplex := ((999997421492978878976385385983 : Int)/10^30,(-2270904532018814140711036987 : Int)/10^30)
theorem v711_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 61 5) 1) 14) v711_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material711 : Material (7 : Basis) (61 : Basis) where
  plus := ![v711_pa,v711_pb,v711_pg]
  minus := ![(Primitive.Addresses.material711 1).one,v711_mb,v711_mg]
  upper := v711_upper
  lower := (Primitive.Addresses.material711 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v711_pa_checked.trans (by decide +kernel)
    · exact v711_pb_checked.trans (by decide +kernel)
    · exact v711_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 61 Primitive.Addresses.material711
    · exact v711_mb_checked.trans (by decide +kernel)
    · exact v711_mg_checked.trans (by decide +kernel)
  upper_error := v711_upper_checked
  lower_error := reuse_lower_error 7 61 Primitive.Addresses.material711

def v712_pa : Scalar.QComplex := ((999999846813504624659258908391 : Int)/10^30,(-553509681292548953374442342 : Int)/10^30)
theorem v712_pa_checked : Scalar.distance (sourceCoefficient 7 62 1 0) v712_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v712_pb : Scalar.QComplex := ((-238826955498833362268331 : Int)/10^30,(-431477401363718489443918020 : Int)/10^30)
theorem v712_pb_checked : Scalar.distance (sourceCoefficient 7 62 1 1) v712_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v712_pg : Scalar.QComplex := ((-93086409862021504762802 : Int)/10^30,(51524236948212393880 : Int)/10^30)
theorem v712_pg_checked : Scalar.distance (sourceCoefficient 7 62 1 2) v712_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v712_mb : Scalar.QComplex := ((-611172430928762173583175 : Int)/10^30,(-431477034608056241613934175 : Int)/10^30)
theorem v712_mb_checked : Scalar.distance (sourceCoefficient 7 62 3 1) v712_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v712_mg : Scalar.QComplex := ((-93086330738600933218250 : Int)/10^30,(131853597018039869480 : Int)/10^30)
theorem v712_mg_checked : Scalar.distance (sourceCoefficient 7 62 3 2) v712_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v712_upper : Scalar.QComplex := ((999997402123705124741269972005 : Int)/10^30,(-2279417873227564648959378424 : Int)/10^30)
theorem v712_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 62 5) 1) 14) v712_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material712 : Material (7 : Basis) (62 : Basis) where
  plus := ![v712_pa,v712_pb,v712_pg]
  minus := ![(Primitive.Addresses.material712 1).one,v712_mb,v712_mg]
  upper := v712_upper
  lower := (Primitive.Addresses.material712 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v712_pa_checked.trans (by decide +kernel)
    · exact v712_pb_checked.trans (by decide +kernel)
    · exact v712_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 62 Primitive.Addresses.material712
    · exact v712_mb_checked.trans (by decide +kernel)
    · exact v712_mg_checked.trans (by decide +kernel)
  upper_error := v712_upper_checked
  lower_error := reuse_lower_error 7 62 Primitive.Addresses.material712

def v713_pa : Scalar.QComplex := ((999999832781735587953518568086 : Int)/10^30,(-578304851148721568362409148 : Int)/10^30)
theorem v713_pa_checked : Scalar.distance (sourceCoefficient 7 63 1 0) v713_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v713_pb : Scalar.QComplex := ((-249525510788551911291765 : Int)/10^30,(-431477392188015860551047942 : Int)/10^30)
theorem v713_pb_checked : Scalar.distance (sourceCoefficient 7 63 1 1) v713_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v713_pg : Scalar.QComplex := ((-93086408219160454908764 : Int)/10^30,(53832330450899586100 : Int)/10^30)
theorem v713_pg_checked : Scalar.distance (sourceCoefficient 7 63 1 2) v713_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v713_mb : Scalar.QComplex := ((-621870974316701529684115 : Int)/10^30,(-431477016199985659270715486 : Int)/10^30)
theorem v713_mb_checked : Scalar.distance (sourceCoefficient 7 63 3 1) v713_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v713_mg : Scalar.QComplex := ((-93086327103959754929872 : Int)/10^30,(134161688243603271256 : Int)/10^30)
theorem v713_mg_checked : Scalar.distance (sourceCoefficient 7 63 3 2) v713_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v713_upper : Scalar.QComplex := ((999997345297743215191290566548 : Int)/10^30,(-2304212981936684003220856664 : Int)/10^30)
theorem v713_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 63 5) 1) 14) v713_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material713 : Material (7 : Basis) (63 : Basis) where
  plus := ![v713_pa,v713_pb,v713_pg]
  minus := ![(Primitive.Addresses.material713 1).one,v713_mb,v713_mg]
  upper := v713_upper
  lower := (Primitive.Addresses.material713 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v713_pa_checked.trans (by decide +kernel)
    · exact v713_pb_checked.trans (by decide +kernel)
    · exact v713_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 63 Primitive.Addresses.material713
    · exact v713_mb_checked.trans (by decide +kernel)
    · exact v713_mg_checked.trans (by decide +kernel)
  upper_error := v713_upper_checked
  lower_error := reuse_lower_error 7 63 Primitive.Addresses.material713

def v714_pa : Scalar.QComplex := ((999999811660289598641019853251 : Int)/10^30,(-613742116308528598785731186 : Int)/10^30)
theorem v714_pa_checked : Scalar.distance (sourceCoefficient 7 64 1 0) v714_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v714_pb : Scalar.QComplex := ((-264815889270714064834631 : Int)/10^30,(-431477378460113789756539251 : Int)/10^30)
theorem v714_pb_checked : Scalar.distance (sourceCoefficient 7 64 1 1) v714_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v714_pg : Scalar.QComplex := ((-93086405755280087799573 : Int)/10^30,(57131058427846996816 : Int)/10^30)
theorem v714_pg_checked : Scalar.distance (sourceCoefficient 7 64 1 2) v714_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v714_mb : Scalar.QComplex := ((-637161335258995764161628 : Int)/10^30,(-431476989277180722978437865 : Int)/10^30)
theorem v714_mb_checked : Scalar.distance (sourceCoefficient 7 64 3 1) v714_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v714_mg : Scalar.QComplex := ((-93086321793426630323265 : Int)/10^30,(137460412866065709076 : Int)/10^30)
theorem v714_mg_checked : Scalar.distance (sourceCoefficient 7 64 3 2) v714_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v714_upper : Scalar.QComplex := ((999997263014823861546876877068 : Int)/10^30,(-2339650157863147676753617370 : Int)/10^30)
theorem v714_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 64 5) 1) 14) v714_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material714 : Material (7 : Basis) (64 : Basis) where
  plus := ![v714_pa,v714_pb,v714_pg]
  minus := ![(Primitive.Addresses.material714 1).one,v714_mb,v714_mg]
  upper := v714_upper
  lower := (Primitive.Addresses.material714 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v714_pa_checked.trans (by decide +kernel)
    · exact v714_pb_checked.trans (by decide +kernel)
    · exact v714_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 64 Primitive.Addresses.material714
    · exact v714_mb_checked.trans (by decide +kernel)
    · exact v714_mg_checked.trans (by decide +kernel)
  upper_error := v714_upper_checked
  lower_error := reuse_lower_error 7 64 Primitive.Addresses.material714

def v715_pa : Scalar.QComplex := ((999999788939262103797339489324 : Int)/10^30,(-649708728004919324195818002 : Int)/10^30)
theorem v715_pa_checked : Scalar.distance (sourceCoefficient 7 65 1 0) v715_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v715_pb : Scalar.QComplex := ((-280334668357529485791970 : Int)/10^30,(-431477363788415887386555135 : Int)/10^30)
theorem v715_pb_checked : Scalar.distance (sourceCoefficient 7 65 1 1) v715_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v715_pg : Scalar.QComplex := ((-93086403115143377030519 : Int)/10^30,(60479061327248274222 : Int)/10^30)
theorem v715_pg_checked : Scalar.distance (sourceCoefficient 7 65 1 2) v715_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v715_mb : Scalar.QComplex := ((-652680095906445986854587 : Int)/10^30,(-431476961213480871494607046 : Int)/10^30)
theorem v715_mb_checked : Scalar.distance (sourceCoefficient 7 65 3 1) v715_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v715_mg : Scalar.QComplex := ((-93086316264115188867525 : Int)/10^30,(140808412240533421692 : Int)/10^30)
theorem v715_mg_checked : Scalar.distance (sourceCoefficient 7 65 3 2) v715_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v715_upper : Scalar.QComplex := ((999997178218721284559248480150 : Int)/10^30,(-2375616676777062994797724751 : Int)/10^30)
theorem v715_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 65 5) 1) 14) v715_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material715 : Material (7 : Basis) (65 : Basis) where
  plus := ![v715_pa,v715_pb,v715_pg]
  minus := ![(Primitive.Addresses.material715 1).one,v715_mb,v715_mg]
  upper := v715_upper
  lower := (Primitive.Addresses.material715 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v715_pa_checked.trans (by decide +kernel)
    · exact v715_pb_checked.trans (by decide +kernel)
    · exact v715_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 65 Primitive.Addresses.material715
    · exact v715_mb_checked.trans (by decide +kernel)
    · exact v715_mg_checked.trans (by decide +kernel)
  upper_error := v715_upper_checked
  lower_error := reuse_lower_error 7 65 Primitive.Addresses.material715

def v716_pa : Scalar.QComplex := ((999999777357805416635483136415 : Int)/10^30,(-667296290711391729994740034 : Int)/10^30)
theorem v716_pa_checked : Scalar.distance (sourceCoefficient 7 66 1 0) v716_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v716_pb : Scalar.QComplex := ((-287923303517560904474646 : Int)/10^30,(-431477356343065109278938209 : Int)/10^30)
theorem v716_pb_checked : Scalar.distance (sourceCoefficient 7 66 1 1) v716_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v716_pg : Scalar.QComplex := ((-93086401772979731675447 : Int)/10^30,(62116224448472224029 : Int)/10^30)
theorem v716_pg_checked : Scalar.distance (sourceCoefficient 7 66 1 2) v716_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v716_mb : Scalar.QComplex := ((-660268721815879322341888 : Int)/10^30,(-431476947219482501964398444 : Int)/10^30)
theorem v716_mb_checked : Scalar.distance (sourceCoefficient 7 66 3 1) v716_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v716_mg : Scalar.QComplex := ((-93086313509154004734854 : Int)/10^30,(142445573593939942282 : Int)/10^30)
theorem v716_mg_checked : Scalar.distance (sourceCoefficient 7 66 3 2) v716_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v716_upper : Scalar.QComplex := ((999997136282744146470427005387 : Int)/10^30,(-2393204193300383149050674878 : Int)/10^30)
theorem v716_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 66 5) 1) 14) v716_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material716 : Material (7 : Basis) (66 : Basis) where
  plus := ![v716_pa,v716_pb,v716_pg]
  minus := ![(Primitive.Addresses.material716 1).one,v716_mb,v716_mg]
  upper := v716_upper
  lower := (Primitive.Addresses.material716 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v716_pa_checked.trans (by decide +kernel)
    · exact v716_pb_checked.trans (by decide +kernel)
    · exact v716_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 66 Primitive.Addresses.material716
    · exact v716_mb_checked.trans (by decide +kernel)
    · exact v716_mg_checked.trans (by decide +kernel)
  upper_error := v716_upper_checked
  lower_error := reuse_lower_error 7 66 Primitive.Addresses.material716

def v717_pa : Scalar.QComplex := ((999999757225486254642346296725 : Int)/10^30,(-696813438842313648378725922 : Int)/10^30)
theorem v717_pa_checked : Scalar.distance (sourceCoefficient 7 67 1 0) v717_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v717_pb : Scalar.QComplex := ((-300659284462685043643094 : Int)/10^30,(-431477343447607564415904112 : Int)/10^30)
theorem v717_pb_checked : Scalar.distance (sourceCoefficient 7 67 1 1) v717_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v717_pg : Scalar.QComplex := ((-93086399444931784706422 : Int)/10^30,(64863869853966616747 : Int)/10^30)
theorem v717_pg_checked : Scalar.distance (sourceCoefficient 7 67 1 2) v717_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v717_mb : Scalar.QComplex := ((-673004686890616621188017 : Int)/10^30,(-431476923333451810315892665 : Int)/10^30)
theorem v717_mb_checked : Scalar.distance (sourceCoefficient 7 67 3 1) v717_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v717_mg : Scalar.QComplex := ((-93086308810012689018088 : Int)/10^30,(145193215967359850089 : Int)/10^30)
theorem v717_mg_checked : Scalar.distance (sourceCoefficient 7 67 3 2) v717_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v717_upper : Scalar.QComplex := ((999997065206535069991351219995 : Int)/10^30,(-2422721262722423770339662137 : Int)/10^30)
theorem v717_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 67 5) 1) 14) v717_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material717 : Material (7 : Basis) (67 : Basis) where
  plus := ![v717_pa,v717_pb,v717_pg]
  minus := ![(Primitive.Addresses.material717 1).one,v717_mb,v717_mg]
  upper := v717_upper
  lower := (Primitive.Addresses.material717 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v717_pa_checked.trans (by decide +kernel)
    · exact v717_pb_checked.trans (by decide +kernel)
    · exact v717_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 67 Primitive.Addresses.material717
    · exact v717_mb_checked.trans (by decide +kernel)
    · exact v717_mg_checked.trans (by decide +kernel)
  upper_error := v717_upper_checked
  lower_error := reuse_lower_error 7 67 Primitive.Addresses.material717

def v718_pa : Scalar.QComplex := ((999999721763289685556790985920 : Int)/10^30,(-745971409112453485742190765 : Int)/10^30)
theorem v718_pa_checked : Scalar.distance (sourceCoefficient 7 68 1 0) v718_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v718_pb : Scalar.QComplex := ((-321869834597234484038470 : Int)/10^30,(-431477320858967970849799009 : Int)/10^30)
theorem v718_pb_checked : Scalar.distance (sourceCoefficient 7 68 1 1) v718_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v718_pg : Scalar.QComplex := ((-93086395357784459648242 : Int)/10^30,(69439808834949397215 : Int)/10^30)
theorem v718_pg_checked : Scalar.distance (sourceCoefficient 7 68 1 2) v718_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v718_mb : Scalar.QComplex := ((-694215209634530261775404 : Int)/10^30,(-431476882441071149132606195 : Int)/10^30)
theorem v718_mb_checked : Scalar.distance (sourceCoefficient 7 68 3 1) v718_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v718_mg : Scalar.QComplex := ((-93086300774037637844694 : Int)/10^30,(149769149717487353952 : Int)/10^30)
theorem v718_mg_checked : Scalar.distance (sourceCoefficient 7 68 3 2) v718_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v718_upper : Scalar.QComplex := ((999996944902194207647153404311 : Int)/10^30,(-2471879098573007218254759924 : Int)/10^30)
theorem v718_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 68 5) 1) 14) v718_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material718 : Material (7 : Basis) (68 : Basis) where
  plus := ![v718_pa,v718_pb,v718_pg]
  minus := ![(Primitive.Addresses.material718 1).one,v718_mb,v718_mg]
  upper := v718_upper
  lower := (Primitive.Addresses.material718 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v718_pa_checked.trans (by decide +kernel)
    · exact v718_pb_checked.trans (by decide +kernel)
    · exact v718_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 68 Primitive.Addresses.material718
    · exact v718_mb_checked.trans (by decide +kernel)
    · exact v718_mg_checked.trans (by decide +kernel)
  upper_error := v718_upper_checked
  lower_error := reuse_lower_error 7 68 Primitive.Addresses.material718

def v719_pa : Scalar.QComplex := ((999999705389864049754627573566 : Int)/10^30,(-767606790684761034853476375 : Int)/10^30)
theorem v719_pa_checked : Scalar.distance (sourceCoefficient 7 69 1 0) v719_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v719_pb : Scalar.QComplex := ((-331205011124655897821974 : Int)/10^30,(-431477310476687801767305317 : Int)/10^30)
theorem v719_pb_checked : Scalar.distance (sourceCoefficient 7 69 1 1) v719_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v719_pg : Scalar.QComplex := ((-93086393475782401061608 : Int)/10^30,(71453768803368748063 : Int)/10^30)
theorem v719_pg_checked : Scalar.distance (sourceCoefficient 7 69 1 2) v719_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v719_mb : Scalar.QComplex := ((-703550373726598630378712 : Int)/10^30,(-431476864002957943426134034 : Int)/10^30)
theorem v719_mb_checked : Scalar.distance (sourceCoefficient 7 69 3 1) v719_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v719_mg : Scalar.QComplex := ((-93086297154079532657374 : Int)/10^30,(151783107311934351705 : Int)/10^30)
theorem v719_mg_checked : Scalar.distance (sourceCoefficient 7 69 3 2) v719_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v719_upper : Scalar.QComplex := ((999996891188087110820392679388 : Int)/10^30,(-2493514419662908124037946750 : Int)/10^30)
theorem v719_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 69 5) 1) 14) v719_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material719 : Material (7 : Basis) (69 : Basis) where
  plus := ![v719_pa,v719_pb,v719_pg]
  minus := ![(Primitive.Addresses.material719 1).one,v719_mb,v719_mg]
  upper := v719_upper
  lower := (Primitive.Addresses.material719 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v719_pa_checked.trans (by decide +kernel)
    · exact v719_pb_checked.trans (by decide +kernel)
    · exact v719_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 69 Primitive.Addresses.material719
    · exact v719_mb_checked.trans (by decide +kernel)
    · exact v719_mg_checked.trans (by decide +kernel)
  upper_error := v719_upper_checked
  lower_error := reuse_lower_error 7 69 Primitive.Addresses.material719

def v720_pa : Scalar.QComplex := ((999999694364035776842931350959 : Int)/10^30,(-781838752578158862062177470 : Int)/10^30)
theorem v720_pa_checked : Scalar.distance (sourceCoefficient 7 70 1 0) v720_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v720_pb : Scalar.QComplex := ((-337345779839456038616774 : Int)/10^30,(-431477303500288655395765960 : Int)/10^30)
theorem v720_pb_checked : Scalar.distance (sourceCoefficient 7 70 1 1) v720_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v720_pg : Scalar.QComplex := ((-93086392210065011298966 : Int)/10^30,(72778571011267198679 : Int)/10^30)
theorem v720_pg_checked : Scalar.distance (sourceCoefficient 7 70 1 2) v720_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v720_mb : Scalar.QComplex := ((-709691134134591673693974 : Int)/10^30,(-431476851727354563770467789 : Int)/10^30)
theorem v720_mb_checked : Scalar.distance (sourceCoefficient 7 70 3 1) v720_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v720_mg : Scalar.QComplex := ((-93086294745117975639304 : Int)/10^30,(153107907934291292298 : Int)/10^30)
theorem v720_mg_checked : Scalar.distance (sourceCoefficient 7 70 3 2) v720_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v720_upper : Scalar.QComplex := ((999996855599200145077418318348 : Int)/10^30,(-2507746341329891170994151188 : Int)/10^30)
theorem v720_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 70 5) 1) 14) v720_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material720 : Material (7 : Basis) (70 : Basis) where
  plus := ![v720_pa,v720_pb,v720_pg]
  minus := ![(Primitive.Addresses.material720 1).one,v720_mb,v720_mg]
  upper := v720_upper
  lower := (Primitive.Addresses.material720 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v720_pa_checked.trans (by decide +kernel)
    · exact v720_pb_checked.trans (by decide +kernel)
    · exact v720_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 70 Primitive.Addresses.material720
    · exact v720_mb_checked.trans (by decide +kernel)
    · exact v720_mg_checked.trans (by decide +kernel)
  upper_error := v720_upper_checked
  lower_error := reuse_lower_error 7 70 Primitive.Addresses.material720

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
