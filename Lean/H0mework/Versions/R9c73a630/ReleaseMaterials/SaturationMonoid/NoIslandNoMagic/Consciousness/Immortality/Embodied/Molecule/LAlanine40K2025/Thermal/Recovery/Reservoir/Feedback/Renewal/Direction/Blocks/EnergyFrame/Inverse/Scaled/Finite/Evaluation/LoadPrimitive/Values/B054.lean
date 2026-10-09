import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B036

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v865_pa : Scalar.QComplex := ((999999947655298838486435531311 : Int)/10^30,(-323557413117145856020761739 : Int)/10^30)
theorem v865_pa_checked : Scalar.distance (sourceCoefficient 9 38 1 0) v865_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v865_pb : Scalar.QComplex := ((-139607744367785944024712 : Int)/10^30,(-431477479421911704367033633 : Int)/10^30)
theorem v865_pb_checked : Scalar.distance (sourceCoefficient 9 38 1 1) v865_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v865_pg : Scalar.QComplex := ((-93086422975612154043822 : Int)/10^30,(30118803790877303133 : Int)/10^30)
theorem v865_pg_checked : Scalar.distance (sourceCoefficient 9 38 1 2) v865_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v865_mb : Scalar.QComplex := ((-511953324102266735349963 : Int)/10^30,(-431477198287930930613590573 : Int)/10^30)
theorem v865_mb_checked : Scalar.distance (sourceCoefficient 9 38 3 1) v865_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v865_mg : Scalar.QComplex := ((-93086362324111449568699 : Int)/10^30,(110448183147363935963 : Int)/10^30)
theorem v865_mg_checked : Scalar.distance (sourceCoefficient 9 38 3 2) v865_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v865_upper : Scalar.QComplex := ((999997899842102910496571359039 : Int)/10^30,(-2049466121582841424910029792 : Int)/10^30)
theorem v865_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 38 5) 1) 14) v865_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material865 : Material (9 : Basis) (38 : Basis) where
  plus := ![v865_pa,v865_pb,v865_pg]
  minus := ![(Primitive.Addresses.material865 1).one,v865_mb,v865_mg]
  upper := v865_upper
  lower := (Primitive.Addresses.material865 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v865_pa_checked.trans (by decide +kernel)
    · exact v865_pb_checked.trans (by decide +kernel)
    · exact v865_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 38 Primitive.Addresses.material865
    · exact v865_mb_checked.trans (by decide +kernel)
    · exact v865_mg_checked.trans (by decide +kernel)
  upper_error := v865_upper_checked
  lower_error := reuse_lower_error 9 38 Primitive.Addresses.material865

def v866_pa : Scalar.QComplex := ((999999943190285942098984155981 : Int)/10^30,(-337074806071973317908519213 : Int)/10^30)
theorem v866_pa_checked : Scalar.distance (sourceCoefficient 9 39 1 0) v866_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v866_pb : Scalar.QComplex := ((-145440194972375091583590 : Int)/10^30,(-431477476483081731988908824 : Int)/10^30)
theorem v866_pb_checked : Scalar.distance (sourceCoefficient 9 39 1 1) v866_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v866_pg : Scalar.QComplex := ((-93086422450786316553312 : Int)/10^30,(31377089578056067774 : Int)/10^30)
theorem v866_pg_checked : Scalar.distance (sourceCoefficient 9 39 1 2) v866_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v866_mb : Scalar.QComplex := ((-517785769999090060485730 : Int)/10^30,(-431477190315959864559690088 : Int)/10^30)
theorem v866_mb_checked : Scalar.distance (sourceCoefficient 9 39 3 1) v866_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v866_mg : Scalar.QComplex := ((-93086360713441844247685 : Int)/10^30,(111706468013124335060 : Int)/10^30)
theorem v866_mg_checked : Scalar.distance (sourceCoefficient 9 39 3 2) v866_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v866_upper : Scalar.QComplex := ((999997872047302712498756041584 : Int)/10^30,(-2062983486698892748741197767 : Int)/10^30)
theorem v866_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 39 5) 1) 14) v866_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material866 : Material (9 : Basis) (39 : Basis) where
  plus := ![v866_pa,v866_pb,v866_pg]
  minus := ![(Primitive.Addresses.material866 1).one,v866_mb,v866_mg]
  upper := v866_upper
  lower := (Primitive.Addresses.material866 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v866_pa_checked.trans (by decide +kernel)
    · exact v866_pb_checked.trans (by decide +kernel)
    · exact v866_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 39 Primitive.Addresses.material866
    · exact v866_mb_checked.trans (by decide +kernel)
    · exact v866_mg_checked.trans (by decide +kernel)
  upper_error := v866_upper_checked
  lower_error := reuse_lower_error 9 39 Primitive.Addresses.material866

def v867_pa : Scalar.QComplex := ((999999935268270710255085035760 : Int)/10^30,(-359810303339541755662804126 : Int)/10^30)
theorem v867_pa_checked : Scalar.distance (sourceCoefficient 9 40 1 0) v867_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v867_pb : Scalar.QComplex := ((-155250049883330890969137 : Int)/10^30,(-431477471303044014186509980 : Int)/10^30)
theorem v867_pb_checked : Scalar.distance (sourceCoefficient 9 40 1 1) v867_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v867_pg : Scalar.QComplex := ((-93086421523302774422925 : Int)/10^30,(33493455733181329317 : Int)/10^30)
theorem v867_pg_checked : Scalar.distance (sourceCoefficient 9 40 1 2) v867_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v867_mb : Scalar.QComplex := ((-527595616787249293779754 : Int)/10^30,(-431477176670461106831298134 : Int)/10^30)
theorem v867_mb_checked : Scalar.distance (sourceCoefficient 9 40 3 1) v867_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v867_mg : Scalar.QComplex := ((-93086357959629973181980 : Int)/10^30,(113822832579853229787 : Int)/10^30)
theorem v867_mg_checked : Scalar.distance (sourceCoefficient 9 40 3 2) v867_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v867_upper : Scalar.QComplex := ((999997824885893543943207363644 : Int)/10^30,(-2085718936431929095012969751 : Int)/10^30)
theorem v867_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 40 5) 1) 14) v867_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material867 : Material (9 : Basis) (40 : Basis) where
  plus := ![v867_pa,v867_pb,v867_pg]
  minus := ![(Primitive.Addresses.material867 1).one,v867_mb,v867_mg]
  upper := v867_upper
  lower := (Primitive.Addresses.material867 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v867_pa_checked.trans (by decide +kernel)
    · exact v867_pb_checked.trans (by decide +kernel)
    · exact v867_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 40 Primitive.Addresses.material867
    · exact v867_mb_checked.trans (by decide +kernel)
    · exact v867_mg_checked.trans (by decide +kernel)
  upper_error := v867_upper_checked
  lower_error := reuse_lower_error 9 40 Primitive.Addresses.material867

def v868_pa : Scalar.QComplex := ((999999929951887267519797873989 : Int)/10^30,(-374294296721473311403661081 : Int)/10^30)
theorem v868_pa_checked : Scalar.distance (sourceCoefficient 9 41 1 0) v868_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v868_pb : Scalar.QComplex := ((-161499566692051597359457 : Int)/10^30,(-431477467847953167695594547 : Int)/10^30)
theorem v868_pb_checked : Scalar.distance (sourceCoefficient 9 41 1 1) v868_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v868_pg : Scalar.QComplex := ((-93086420903162671302002 : Int)/10^30,(34841718886864976945 : Int)/10^30)
theorem v868_pg_checked : Scalar.distance (sourceCoefficient 9 41 1 2) v868_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v868_mb : Scalar.QComplex := ((-533845128287401486248924 : Int)/10^30,(-431477167822320008691130018 : Int)/10^30)
theorem v868_mb_checked : Scalar.distance (sourceCoefficient 9 41 3 1) v868_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v868_mg : Scalar.QComplex := ((-93086356175999722856850 : Int)/10^30,(115171094696363907709 : Int)/10^30)
theorem v868_mg_checked : Scalar.distance (sourceCoefficient 9 41 3 2) v868_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v868_upper : Scalar.QComplex := ((999997794571459419738065662824 : Int)/10^30,(-2100202899066058394124216279 : Int)/10^30)
theorem v868_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 41 5) 1) 14) v868_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material868 : Material (9 : Basis) (41 : Basis) where
  plus := ![v868_pa,v868_pb,v868_pg]
  minus := ![(Primitive.Addresses.material868 1).one,v868_mb,v868_mg]
  upper := v868_upper
  lower := (Primitive.Addresses.material868 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v868_pa_checked.trans (by decide +kernel)
    · exact v868_pb_checked.trans (by decide +kernel)
    · exact v868_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 41 Primitive.Addresses.material868
    · exact v868_mb_checked.trans (by decide +kernel)
    · exact v868_mg_checked.trans (by decide +kernel)
  upper_error := v868_upper_checked
  lower_error := reuse_lower_error 9 41 Primitive.Addresses.material868

def v869_pa : Scalar.QComplex := ((999999925510509895156462885630 : Int)/10^30,(-385977945822041674522885222 : Int)/10^30)
theorem v869_pa_checked : Scalar.distance (sourceCoefficient 9 42 1 0) v869_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v869_pb : Scalar.QComplex := ((-166540798004291410308269 : Int)/10^30,(-431477464972926956978391893 : Int)/10^30)
theorem v869_pb_checked : Scalar.distance (sourceCoefficient 9 42 1 1) v869_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v869_pg : Scalar.QComplex := ((-93086420386319379445979 : Int)/10^30,(35929308000994409896 : Int)/10^30)
theorem v869_pg_checked : Scalar.distance (sourceCoefficient 9 42 1 2) v869_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v869_mb : Scalar.QComplex := ((-538886355241542352522933 : Int)/10^30,(-431477160596939294644484187 : Int)/10^30)
theorem v869_mb_checked : Scalar.distance (sourceCoefficient 9 42 3 1) v869_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v869_mg : Scalar.QComplex := ((-93086354720616201146864 : Int)/10^30,(116258682959521725078 : Int)/10^30)
theorem v869_mg_checked : Scalar.distance (sourceCoefficient 9 42 3 2) v869_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v869_upper : Scalar.QComplex := ((999997769965170247070277522990 : Int)/10^30,(-2111886523099789453688797935 : Int)/10^30)
theorem v869_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 42 5) 1) 14) v869_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material869 : Material (9 : Basis) (42 : Basis) where
  plus := ![v869_pa,v869_pb,v869_pg]
  minus := ![(Primitive.Addresses.material869 1).one,v869_mb,v869_mg]
  upper := v869_upper
  lower := (Primitive.Addresses.material869 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v869_pa_checked.trans (by decide +kernel)
    · exact v869_pb_checked.trans (by decide +kernel)
    · exact v869_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 42 Primitive.Addresses.material869
    · exact v869_mb_checked.trans (by decide +kernel)
    · exact v869_mg_checked.trans (by decide +kernel)
  upper_error := v869_upper_checked
  lower_error := reuse_lower_error 9 42 Primitive.Addresses.material869

def v870_pa : Scalar.QComplex := ((999999919416643926126259079875 : Int)/10^30,(-401455733118945762691820002 : Int)/10^30)
theorem v870_pa_checked : Scalar.distance (sourceCoefficient 9 43 1 0) v870_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v870_pb : Scalar.QComplex := ((-173219114406032485261363 : Int)/10^30,(-431477461043338729928772946 : Int)/10^30)
theorem v870_pb_checked : Scalar.distance (sourceCoefficient 9 43 1 1) v870_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v870_pg : Scalar.QComplex := ((-93086419678808999073486 : Int)/10^30,(37370079866980578905 : Int)/10^30)
theorem v870_pg_checked : Scalar.distance (sourceCoefficient 9 43 1 2) v870_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v870_mb : Scalar.QComplex := ((-545564665765583359110422 : Int)/10^30,(-431477150904266256262853901 : Int)/10^30)
theorem v870_mb_checked : Scalar.distance (sourceCoefficient 9 43 3 1) v870_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v870_mg : Scalar.QComplex := ((-93086352769784853822771 : Int)/10^30,(117699453678493088676 : Int)/10^30)
theorem v870_mg_checked : Scalar.distance (sourceCoefficient 9 43 3 2) v870_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v870_upper : Scalar.QComplex := ((999997737158056613576225710387 : Int)/10^30,(-2127364276826887680389060229 : Int)/10^30)
theorem v870_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 43 5) 1) 14) v870_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material870 : Material (9 : Basis) (43 : Basis) where
  plus := ![v870_pa,v870_pb,v870_pg]
  minus := ![(Primitive.Addresses.material870 1).one,v870_mb,v870_mg]
  upper := v870_upper
  lower := (Primitive.Addresses.material870 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v870_pa_checked.trans (by decide +kernel)
    · exact v870_pb_checked.trans (by decide +kernel)
    · exact v870_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 43 Primitive.Addresses.material870
    · exact v870_mb_checked.trans (by decide +kernel)
    · exact v870_mg_checked.trans (by decide +kernel)
  upper_error := v870_upper_checked
  lower_error := reuse_lower_error 9 43 Primitive.Addresses.material870

def v871_pa : Scalar.QComplex := ((999999917048662628949101714490 : Int)/10^30,(-407311512065614743686412403 : Int)/10^30)
theorem v871_pa_checked : Scalar.distance (sourceCoefficient 9 44 1 0) v871_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v871_pb : Scalar.QComplex := ((-175745751037953780664968 : Int)/10^30,(-431477459520705645741801644 : Int)/10^30)
theorem v871_pb_checked : Scalar.distance (sourceCoefficient 9 44 1 1) v871_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v871_pg : Scalar.QComplex := ((-93086419404350041646684 : Int)/10^30,(37915173385474135371 : Int)/10^30)
theorem v871_pg_checked : Scalar.distance (sourceCoefficient 9 44 1 2) v871_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v871_mb : Scalar.QComplex := ((-548091300142758588646231 : Int)/10^30,(-431477147201260121163304274 : Int)/10^30)
theorem v871_mb_checked : Scalar.distance (sourceCoefficient 9 44 3 1) v871_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v871_mg : Scalar.QComplex := ((-93086352024934842230374 : Int)/10^30,(118244546757177697115 : Int)/10^30)
theorem v871_mg_checked : Scalar.distance (sourceCoefficient 9 44 3 2) v871_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v871_upper : Scalar.QComplex := ((999997724683535613394670920248 : Int)/10^30,(-2133220042965140891092792985 : Int)/10^30)
theorem v871_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 44 5) 1) 14) v871_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material871 : Material (9 : Basis) (44 : Basis) where
  plus := ![v871_pa,v871_pb,v871_pg]
  minus := ![(Primitive.Addresses.material871 1).one,v871_mb,v871_mg]
  upper := v871_upper
  lower := (Primitive.Addresses.material871 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v871_pa_checked.trans (by decide +kernel)
    · exact v871_pb_checked.trans (by decide +kernel)
    · exact v871_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 44 Primitive.Addresses.material871
    · exact v871_mb_checked.trans (by decide +kernel)
    · exact v871_mg_checked.trans (by decide +kernel)
  upper_error := v871_upper_checked
  lower_error := reuse_lower_error 9 44 Primitive.Addresses.material871

def v872_pa : Scalar.QComplex := ((999999915857788726375633420540 : Int)/10^30,(-410224835263952559178930772 : Int)/10^30)
theorem v872_pa_checked : Scalar.distance (sourceCoefficient 9 45 1 0) v872_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v872_pb : Scalar.QComplex := ((-177002784331624083283587 : Int)/10^30,(-431477458755827956066292073 : Int)/10^30)
theorem v872_pb_checked : Scalar.distance (sourceCoefficient 9 45 1 1) v872_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v872_pg : Scalar.QComplex := ((-93086419266416055358110 : Int)/10^30,(38186364221961872077 : Int)/10^30)
theorem v872_pg_checked : Scalar.distance (sourceCoefficient 9 45 1 2) v872_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v872_mb : Scalar.QComplex := ((-549348332308322949394203 : Int)/10^30,(-431477145351619598527155325 : Int)/10^30)
theorem v872_mb_checked : Scalar.distance (sourceCoefficient 9 45 3 1) v872_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v872_mg : Scalar.QComplex := ((-93086351652975429393882 : Int)/10^30,(118515737373657873513 : Int)/10^30)
theorem v872_mg_checked : Scalar.distance (sourceCoefficient 9 45 3 2) v872_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v872_upper : Scalar.QComplex := ((999997718464531938772918060047 : Int)/10^30,(-2136133359769085705038575540 : Int)/10^30)
theorem v872_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 45 5) 1) 14) v872_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material872 : Material (9 : Basis) (45 : Basis) where
  plus := ![v872_pa,v872_pb,v872_pg]
  minus := ![(Primitive.Addresses.material872 1).one,v872_mb,v872_mg]
  upper := v872_upper
  lower := (Primitive.Addresses.material872 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v872_pa_checked.trans (by decide +kernel)
    · exact v872_pb_checked.trans (by decide +kernel)
    · exact v872_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 45 Primitive.Addresses.material872
    · exact v872_mb_checked.trans (by decide +kernel)
    · exact v872_mg_checked.trans (by decide +kernel)
  upper_error := v872_upper_checked
  lower_error := reuse_lower_error 9 45 Primitive.Addresses.material872

def v873_pa : Scalar.QComplex := ((999999909010875523580837884007 : Int)/10^30,(-426589077068104910996171144 : Int)/10^30)
theorem v873_pa_checked : Scalar.distance (sourceCoefficient 9 46 1 0) v873_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v873_pb : Scalar.QComplex := ((-184063585782640200307566 : Int)/10^30,(-431477454368738907790232725 : Int)/10^30)
theorem v873_pb_checked : Scalar.distance (sourceCoefficient 9 46 1 1) v873_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v873_pg : Scalar.QComplex := ((-93086418474506103190290 : Int)/10^30,(39709652957761504725 : Int)/10^30)
theorem v873_pg_checked : Scalar.distance (sourceCoefficient 9 46 1 2) v873_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v873_mb : Scalar.QComplex := ((-556409127344419730130851 : Int)/10^30,(-431477134871378538230329980 : Int)/10^30)
theorem v873_mb_checked : Scalar.distance (sourceCoefficient 9 46 3 1) v873_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v873_mg : Scalar.QComplex := ((-93086349546536199473117 : Int)/10^30,(120039024858884869668 : Int)/10^30)
theorem v873_mg_checked : Scalar.distance (sourceCoefficient 9 46 3 2) v873_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v873_upper : Scalar.QComplex := ((999997683374432132103869531890 : Int)/10^30,(-2152497565383471127535735175 : Int)/10^30)
theorem v873_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 46 5) 1) 14) v873_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material873 : Material (9 : Basis) (46 : Basis) where
  plus := ![v873_pa,v873_pb,v873_pg]
  minus := ![(Primitive.Addresses.material873 1).one,v873_mb,v873_mg]
  upper := v873_upper
  lower := (Primitive.Addresses.material873 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v873_pa_checked.trans (by decide +kernel)
    · exact v873_pb_checked.trans (by decide +kernel)
    · exact v873_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 46 Primitive.Addresses.material873
    · exact v873_mb_checked.trans (by decide +kernel)
    · exact v873_mg_checked.trans (by decide +kernel)
  upper_error := v873_upper_checked
  lower_error := reuse_lower_error 9 46 Primitive.Addresses.material873

def v874_pa : Scalar.QComplex := ((999999907323195431775577570107 : Int)/10^30,(-430527119409984137044378695 : Int)/10^30)
theorem v874_pa_checked : Scalar.distance (sourceCoefficient 9 47 1 0) v874_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v874_pb : Scalar.QComplex := ((-185762762271195088108792 : Int)/10^30,(-431477453289991150839694595 : Int)/10^30)
theorem v874_pb_checked : Scalar.distance (sourceCoefficient 9 47 1 1) v874_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v874_pg : Scalar.QComplex := ((-93086418279592188377812 : Int)/10^30,(40076231232242765968 : Int)/10^30)
theorem v874_pg_checked : Scalar.distance (sourceCoefficient 9 47 1 2) v874_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v874_mb : Scalar.QComplex := ((-558108302269382825788369 : Int)/10^30,(-431477132326318401392203884 : Int)/10^30)
theorem v874_mb_checked : Scalar.distance (sourceCoefficient 9 47 3 1) v874_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v874_mg : Scalar.QComplex := ((-93086349035281816431270 : Int)/10^30,(120405602828670355980 : Int)/10^30)
theorem v874_mg_checked : Scalar.distance (sourceCoefficient 9 47 3 2) v874_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v874_upper : Scalar.QComplex := ((999997674890050728226834328298 : Int)/10^30,(-2156435598947316146989893011 : Int)/10^30)
theorem v874_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 47 5) 1) 14) v874_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material874 : Material (9 : Basis) (47 : Basis) where
  plus := ![v874_pa,v874_pb,v874_pg]
  minus := ![(Primitive.Addresses.material874 1).one,v874_mb,v874_mg]
  upper := v874_upper
  lower := (Primitive.Addresses.material874 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v874_pa_checked.trans (by decide +kernel)
    · exact v874_pb_checked.trans (by decide +kernel)
    · exact v874_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 47 Primitive.Addresses.material874
    · exact v874_mb_checked.trans (by decide +kernel)
    · exact v874_mg_checked.trans (by decide +kernel)
  upper_error := v874_upper_checked
  lower_error := reuse_lower_error 9 47 Primitive.Addresses.material874

def v875_pa : Scalar.QComplex := ((999999895137374093902145893083 : Int)/10^30,(-457957684525574258096062233 : Int)/10^30)
theorem v875_pa_checked : Scalar.distance (sourceCoefficient 9 48 1 0) v875_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v875_pb : Scalar.QComplex := ((-197598432599897771511733 : Int)/10^30,(-431477445528425320271677636 : Int)/10^30)
theorem v875_pb_checked : Scalar.distance (sourceCoefficient 9 48 1 1) v875_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v875_pg : Scalar.QComplex := ((-93086416875189550530308 : Int)/10^30,(42629644403200601673 : Int)/10^30)
theorem v875_pg_checked : Scalar.distance (sourceCoefficient 9 48 1 2) v875_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v875_mb : Scalar.QComplex := ((-569943961493242785127683 : Int)/10^30,(-431477114351105025942982786 : Int)/10^30)
theorem v875_mb_checked : Scalar.distance (sourceCoefficient 9 48 3 1) v875_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v875_mg : Scalar.QComplex := ((-93086345427399136430605 : Int)/10^30,(122959013836939546875 : Int)/10^30)
theorem v875_mg_checked : Scalar.distance (sourceCoefficient 9 48 3 2) v875_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v875_upper : Scalar.QComplex := ((999997615361580631622625546451 : Int)/10^30,(-2183866102176679608803837146 : Int)/10^30)
theorem v875_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 48 5) 1) 14) v875_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material875 : Material (9 : Basis) (48 : Basis) where
  plus := ![v875_pa,v875_pb,v875_pg]
  minus := ![(Primitive.Addresses.material875 1).one,v875_mb,v875_mg]
  upper := v875_upper
  lower := (Primitive.Addresses.material875 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v875_pa_checked.trans (by decide +kernel)
    · exact v875_pb_checked.trans (by decide +kernel)
    · exact v875_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 48 Primitive.Addresses.material875
    · exact v875_mb_checked.trans (by decide +kernel)
    · exact v875_mg_checked.trans (by decide +kernel)
  upper_error := v875_upper_checked
  lower_error := reuse_lower_error 9 48 Primitive.Addresses.material875

def v876_pa : Scalar.QComplex := ((999999884801881596727957044263 : Int)/10^30,(-479996066167148501410062110 : Int)/10^30)
theorem v876_pa_checked : Scalar.distance (sourceCoefficient 9 49 1 0) v876_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v876_pb : Scalar.QComplex := ((-207107497208186311163443 : Int)/10^30,(-431477438978992628351816423 : Int)/10^30)
theorem v876_pb_checked : Scalar.distance (sourceCoefficient 9 49 1 1) v876_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v876_pg : Scalar.QComplex := ((-93086415687659222117097 : Int)/10^30,(44681118490857144549 : Int)/10^30)
theorem v876_pg_checked : Scalar.distance (sourceCoefficient 9 49 1 2) v876_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v876_mb : Scalar.QComplex := ((-579453016909006547763599 : Int)/10^30,(-431477099595780288094966491 : Int)/10^30)
theorem v876_mb_checked : Scalar.distance (sourceCoefficient 9 49 3 1) v876_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v876_mg : Scalar.QComplex := ((-93086342469539507504658 : Int)/10^30,(125010486135953340879 : Int)/10^30)
theorem v876_mg_checked : Scalar.distance (sourceCoefficient 9 49 3 2) v876_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v876_upper : Scalar.QComplex := ((999997566989856120958074413698 : Int)/10^30,(-2205904433156550785586957550 : Int)/10^30)
theorem v876_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 49 5) 1) 14) v876_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material876 : Material (9 : Basis) (49 : Basis) where
  plus := ![v876_pa,v876_pb,v876_pg]
  minus := ![(Primitive.Addresses.material876 1).one,v876_mb,v876_mg]
  upper := v876_upper
  lower := (Primitive.Addresses.material876 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v876_pa_checked.trans (by decide +kernel)
    · exact v876_pb_checked.trans (by decide +kernel)
    · exact v876_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 49 Primitive.Addresses.material876
    · exact v876_mb_checked.trans (by decide +kernel)
    · exact v876_mg_checked.trans (by decide +kernel)
  upper_error := v876_upper_checked
  lower_error := reuse_lower_error 9 49 Primitive.Addresses.material876

def v877_pa : Scalar.QComplex := ((999999883562440763353844763786 : Int)/10^30,(-482571346969116173492985874 : Int)/10^30)
theorem v877_pa_checked : Scalar.distance (sourceCoefficient 9 50 1 0) v877_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v877_pb : Scalar.QComplex := ((-208218672781226039946091 : Int)/10^30,(-431477438195429510548954415 : Int)/10^30)
theorem v877_pb_checked : Scalar.distance (sourceCoefficient 9 50 1 1) v877_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v877_pg : Scalar.QComplex := ((-93086415545449189001485 : Int)/10^30,(44920842164767510669 : Int)/10^30)
theorem v877_pg_checked : Scalar.distance (sourceCoefficient 9 50 1 2) v877_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v877_mb : Scalar.QComplex := ((-580564191392125147180041 : Int)/10^30,(-431477097853322988005211699 : Int)/10^30)
theorem v877_mb_checked : Scalar.distance (sourceCoefficient 9 50 3 1) v877_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v877_mg : Scalar.QComplex := ((-93086342120458793509172 : Int)/10^30,(125250209597882773612 : Int)/10^30)
theorem v877_mg_checked : Scalar.distance (sourceCoefficient 9 50 3 2) v877_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v877_upper : Scalar.QComplex := ((999997561305716097038641944517 : Int)/10^30,(-2208479707983777779662807110 : Int)/10^30)
theorem v877_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 50 5) 1) 14) v877_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material877 : Material (9 : Basis) (50 : Basis) where
  plus := ![v877_pa,v877_pb,v877_pg]
  minus := ![(Primitive.Addresses.material877 1).one,v877_mb,v877_mg]
  upper := v877_upper
  lower := (Primitive.Addresses.material877 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v877_pa_checked.trans (by decide +kernel)
    · exact v877_pb_checked.trans (by decide +kernel)
    · exact v877_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 50 Primitive.Addresses.material877
    · exact v877_mb_checked.trans (by decide +kernel)
    · exact v877_mg_checked.trans (by decide +kernel)
  upper_error := v877_upper_checked
  lower_error := reuse_lower_error 9 50 Primitive.Addresses.material877

def v878_pa : Scalar.QComplex := ((999999878045909700900285955179 : Int)/10^30,(-493870596133642367514844531 : Int)/10^30)
theorem v878_pa_checked : Scalar.distance (sourceCoefficient 9 51 1 0) v878_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v878_pb : Scalar.QComplex := ((-213094043887312282016615 : Int)/10^30,(-431477434712388395924708428 : Int)/10^30)
theorem v878_pb_checked : Scalar.distance (sourceCoefficient 9 51 1 1) v878_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v878_pg : Scalar.QComplex := ((-93086414912978593365741 : Int)/10^30,(45972648831568881807 : Int)/10^30)
theorem v878_pg_checked : Scalar.distance (sourceCoefficient 9 51 1 2) v878_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v878_mb : Scalar.QComplex := ((-585439557677180299415579 : Int)/10^30,(-431477090163057484287407323 : Int)/10^30)
theorem v878_mb_checked : Scalar.distance (sourceCoefficient 9 51 3 1) v878_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v878_mg : Scalar.QComplex := ((-93086340580326651535309 : Int)/10^30,(126302015327254814146 : Int)/10^30)
theorem v878_mg_checked : Scalar.distance (sourceCoefficient 9 51 3 2) v878_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v878_upper : Scalar.QComplex := ((999997536287714252714750006884 : Int)/10^30,(-2219778930798367488161515781 : Int)/10^30)
theorem v878_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 51 5) 1) 14) v878_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material878 : Material (9 : Basis) (51 : Basis) where
  plus := ![v878_pa,v878_pb,v878_pg]
  minus := ![(Primitive.Addresses.material878 1).one,v878_mb,v878_mg]
  upper := v878_upper
  lower := (Primitive.Addresses.material878 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v878_pa_checked.trans (by decide +kernel)
    · exact v878_pb_checked.trans (by decide +kernel)
    · exact v878_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 51 Primitive.Addresses.material878
    · exact v878_mb_checked.trans (by decide +kernel)
    · exact v878_mg_checked.trans (by decide +kernel)
  upper_error := v878_upper_checked
  lower_error := reuse_lower_error 9 51 Primitive.Addresses.material878

def v879_pa : Scalar.QComplex := ((999999865807155197333315686541 : Int)/10^30,(-518059525149006185507474662 : Int)/10^30)
theorem v879_pa_checked : Scalar.distance (sourceCoefficient 9 52 1 0) v879_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v879_pb : Scalar.QComplex := ((-223531020945124803894769 : Int)/10^30,(-431477427009122930599126368 : Int)/10^30)
theorem v879_pb_checked : Scalar.distance (sourceCoefficient 9 52 1 1) v879_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v879_pg : Scalar.QComplex := ((-93086413512401099690103 : Int)/10^30,(48224309653415847752 : Int)/10^30)
theorem v879_pg_checked : Scalar.distance (sourceCoefficient 9 52 1 2) v879_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v879_mb : Scalar.QComplex := ((-595876524201258114876118 : Int)/10^30,(-431477073453153750344496326 : Int)/10^30)
theorem v879_mb_checked : Scalar.distance (sourceCoefficient 9 52 3 1) v879_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v879_mg : Scalar.QComplex := ((-93086337236667801143611 : Int)/10^30,(128553674102070252760 : Int)/10^30)
theorem v879_mg_checked : Scalar.distance (sourceCoefficient 9 52 3 2) v879_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v879_upper : Scalar.QComplex := ((999997482301080899315540049124 : Int)/10^30,(-2243967802664182986950393639 : Int)/10^30)
theorem v879_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 52 5) 1) 14) v879_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material879 : Material (9 : Basis) (52 : Basis) where
  plus := ![v879_pa,v879_pb,v879_pg]
  minus := ![(Primitive.Addresses.material879 1).one,v879_mb,v879_mg]
  upper := v879_upper
  lower := (Primitive.Addresses.material879 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v879_pa_checked.trans (by decide +kernel)
    · exact v879_pb_checked.trans (by decide +kernel)
    · exact v879_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 52 Primitive.Addresses.material879
    · exact v879_mb_checked.trans (by decide +kernel)
    · exact v879_mg_checked.trans (by decide +kernel)
  upper_error := v879_upper_checked
  lower_error := reuse_lower_error 9 52 Primitive.Addresses.material879

def v880_pa : Scalar.QComplex := ((999999863882086482242914878435 : Int)/10^30,(-521762214526337456796461298 : Int)/10^30)
theorem v880_pa_checked : Scalar.distance (sourceCoefficient 9 53 1 0) v880_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v880_pb : Scalar.QComplex := ((-225128647847702915884747 : Int)/10^30,(-431477425800248476446293280 : Int)/10^30)
theorem v880_pb_checked : Scalar.distance (sourceCoefficient 9 53 1 1) v880_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v880_pg : Scalar.QComplex := ((-93086413292401668147731 : Int)/10^30,(48568979752865575431 : Int)/10^30)
theorem v880_pg_checked : Scalar.distance (sourceCoefficient 9 53 1 2) v880_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v880_mb : Scalar.QComplex := ((-597474149465762507630196 : Int)/10^30,(-431477070865599683830577742 : Int)/10^30)
theorem v880_mb_checked : Scalar.distance (sourceCoefficient 9 53 3 1) v880_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v880_mg : Scalar.QComplex := ((-93086336719233679056992 : Int)/10^30,(128898343883333949198 : Int)/10^30)
theorem v880_mg_checked : Scalar.distance (sourceCoefficient 9 53 3 2) v880_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v880_upper : Scalar.QComplex := ((999997473985509091471444514131 : Int)/10^30,(-2247670483204299417775756642 : Int)/10^30)
theorem v880_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 53 5) 1) 14) v880_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material880 : Material (9 : Basis) (53 : Basis) where
  plus := ![v880_pa,v880_pb,v880_pg]
  minus := ![(Primitive.Addresses.material880 1).one,v880_mb,v880_mg]
  upper := v880_upper
  lower := (Primitive.Addresses.material880 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v880_pa_checked.trans (by decide +kernel)
    · exact v880_pb_checked.trans (by decide +kernel)
    · exact v880_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 53 Primitive.Addresses.material880
    · exact v880_mb_checked.trans (by decide +kernel)
    · exact v880_mg_checked.trans (by decide +kernel)
  upper_error := v880_upper_checked
  lower_error := reuse_lower_error 9 53 Primitive.Addresses.material880

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
