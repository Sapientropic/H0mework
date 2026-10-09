import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B110

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2641_pa : Scalar.QComplex := ((999999372596193840405053732415 : Int)/10^30,(-1120181779303544067867060664 : Int)/10^30)
theorem v2641_pa_checked : Scalar.distance (sourceCoefficient 32 66 1 0) v2641_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2641_pb : Scalar.QComplex := ((-483333235106042607834710 : Int)/10^30,(-431477230562914650940900712 : Int)/10^30)
theorem v2641_pb_checked : Scalar.distance (sourceCoefficient 32 66 1 1) v2641_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2641_pg : Scalar.QComplex := ((-93086369366245590810723 : Int)/10^30,(104273720287316894369 : Int)/10^30)
theorem v2641_pg_checked : Scalar.distance (sourceCoefficient 32 66 1 2) v2641_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2641_mb : Scalar.QComplex := ((-855678472101707902391238 : Int)/10^30,(-431476652809408853077724641 : Int)/10^30)
theorem v2641_mb_checked : Scalar.distance (sourceCoefficient 32 66 3 1) v2641_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2641_mg : Scalar.QComplex := ((-93086244722411724584770 : Int)/10^30,(184603025770070200639 : Int)/10^30)
theorem v2641_mg_checked : Scalar.distance (sourceCoefficient 32 66 3 2) v2641_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2641_upper : Scalar.QComplex := ((999995949882467555642019245165 : Int)/10^30,(-2846088308790978001464897267 : Int)/10^30)
theorem v2641_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 66 5) 1) 14) v2641_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2641 : Material (32 : Basis) (66 : Basis) where
  plus := ![v2641_pa,v2641_pb,v2641_pg]
  minus := ![(Primitive.Addresses.material2641 1).one,v2641_mb,v2641_mg]
  upper := v2641_upper
  lower := (Primitive.Addresses.material2641 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2641_pa_checked.trans (by decide +kernel)
    · exact v2641_pb_checked.trans (by decide +kernel)
    · exact v2641_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 66 Primitive.Addresses.material2641
    · exact v2641_mb_checked.trans (by decide +kernel)
    · exact v2641_mg_checked.trans (by decide +kernel)
  upper_error := v2641_upper_checked
  lower_error := reuse_lower_error 32 66 Primitive.Addresses.material2641

def v2642_pa : Scalar.QComplex := ((999999339095983693710986155619 : Int)/10^30,(-1149698915289763704274376634 : Int)/10^30)
theorem v2642_pa_checked : Scalar.distance (sourceCoefficient 32 67 1 0) v2642_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2642_pb : Scalar.QComplex := ((-496069212557722946476185 : Int)/10^30,(-431477213822161052828175639 : Int)/10^30)
theorem v2642_pb_checked : Scalar.distance (sourceCoefficient 32 67 1 1) v2642_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2642_pg : Scalar.QComplex := ((-93086366001223309446029 : Int)/10^30,(107021364750722172105 : Int)/10^30)
theorem v2642_pg_checked : Scalar.distance (sourceCoefficient 32 67 1 2) v2642_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2642_mb : Scalar.QComplex := ((-868414430364685393229978 : Int)/10^30,(-431476625078086554643648208 : Int)/10^30)
theorem v2642_mb_checked : Scalar.distance (sourceCoefficient 32 67 3 1) v2642_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2642_mg : Scalar.QComplex := ((-93086238986297273565746 : Int)/10^30,(187350666306539197253 : Int)/10^30)
theorem v2642_mg_checked : Scalar.distance (sourceCoefficient 32 67 3 2) v2642_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2642_upper : Scalar.QComplex := ((999995865438408365019711559066 : Int)/10^30,(-2875605342996567314887679800 : Int)/10^30)
theorem v2642_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 67 5) 1) 14) v2642_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2642 : Material (32 : Basis) (67 : Basis) where
  plus := ![v2642_pa,v2642_pb,v2642_pg]
  minus := ![(Primitive.Addresses.material2642 1).one,v2642_mb,v2642_mg]
  upper := v2642_upper
  lower := (Primitive.Addresses.material2642 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2642_pa_checked.trans (by decide +kernel)
    · exact v2642_pb_checked.trans (by decide +kernel)
    · exact v2642_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 67 Primitive.Addresses.material2642
    · exact v2642_mb_checked.trans (by decide +kernel)
    · exact v2642_mg_checked.trans (by decide +kernel)
  upper_error := v2642_upper_checked
  lower_error := reuse_lower_error 32 67 Primitive.Addresses.material2642

def v2643_pa : Scalar.QComplex := ((999999281370851056679778940095 : Int)/10^30,(-1198856864458300013916028759 : Int)/10^30)
theorem v2643_pa_checked : Scalar.distance (sourceCoefficient 32 68 1 0) v2643_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2643_pb : Scalar.QComplex := ((-517279756622361090773128 : Int)/10^30,(-431477184829550947815345500 : Int)/10^30)
theorem v2643_pb_checked : Scalar.distance (sourceCoefficient 32 68 1 1) v2643_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2643_pg : Scalar.QComplex := ((-93086360187095022956673 : Int)/10^30,(111597302094810901426 : Int)/10^30)
theorem v2643_pg_checked : Scalar.distance (sourceCoefficient 32 68 1 2) v2643_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2643_mb : Scalar.QComplex := ((-889624941512351870570822 : Int)/10^30,(-431476577781743004564603902 : Int)/10^30)
theorem v2643_mb_checked : Scalar.distance (sourceCoefficient 32 68 3 1) v2643_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2643_mg : Scalar.QComplex := ((-93086229223343316560960 : Int)/10^30,(191926596929466470079 : Int)/10^30)
theorem v2643_mg_checked : Scalar.distance (sourceCoefficient 32 68 3 2) v2643_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2643_upper : Scalar.QComplex := ((999995722871201012211313195901 : Int)/10^30,(-2924763119321770687949682745 : Int)/10^30)
theorem v2643_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 68 5) 1) 14) v2643_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2643 : Material (32 : Basis) (68 : Basis) where
  plus := ![v2643_pa,v2643_pb,v2643_pg]
  minus := ![(Primitive.Addresses.material2643 1).one,v2643_mb,v2643_mg]
  upper := v2643_upper
  lower := (Primitive.Addresses.material2643 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2643_pa_checked.trans (by decide +kernel)
    · exact v2643_pb_checked.trans (by decide +kernel)
    · exact v2643_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 68 Primitive.Addresses.material2643
    · exact v2643_mb_checked.trans (by decide +kernel)
    · exact v2643_mg_checked.trans (by decide +kernel)
  upper_error := v2643_upper_checked
  lower_error := reuse_lower_error 32 68 Primitive.Addresses.material2643

def v2644_pa : Scalar.QComplex := ((999999255199073083662603672316 : Int)/10^30,(-1220492236396550806515231425 : Int)/10^30)
theorem v2644_pa_checked : Scalar.distance (sourceCoefficient 32 69 1 0) v2644_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2644_pb : Scalar.QComplex := ((-526614930378530096172689 : Int)/10^30,(-431477171628758482211838601 : Int)/10^30)
theorem v2644_pb_checked : Scalar.distance (sourceCoefficient 32 69 1 1) v2644_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2644_pg : Scalar.QComplex := ((-93086357545014966157933 : Int)/10^30,(113611261315896993074 : Int)/10^30)
theorem v2644_pg_checked : Scalar.distance (sourceCoefficient 32 69 1 2) v2644_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2644_mb : Scalar.QComplex := ((-898960100400919691838037 : Int)/10^30,(-431476556525120943264074764 : Int)/10^30)
theorem v2644_mb_checked : Scalar.distance (sourceCoefficient 32 69 3 1) v2644_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2644_mg : Scalar.QComplex := ((-93086224843308141088253 : Int)/10^30,(193940553120667407084 : Int)/10^30)
theorem v2644_mg_checked : Scalar.distance (sourceCoefficient 32 69 3 2) v2644_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2644_upper : Scalar.QComplex := ((999995659358772799172318516950 : Int)/10^30,(-2946398413866561951563848869 : Int)/10^30)
theorem v2644_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 69 5) 1) 14) v2644_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2644 : Material (32 : Basis) (69 : Basis) where
  plus := ![v2644_pa,v2644_pb,v2644_pg]
  minus := ![(Primitive.Addresses.material2644 1).one,v2644_mb,v2644_mg]
  upper := v2644_upper
  lower := (Primitive.Addresses.material2644 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2644_pa_checked.trans (by decide +kernel)
    · exact v2644_pb_checked.trans (by decide +kernel)
    · exact v2644_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 69 Primitive.Addresses.material2644
    · exact v2644_mb_checked.trans (by decide +kernel)
    · exact v2644_mg_checked.trans (by decide +kernel)
  upper_error := v2644_upper_checked
  lower_error := reuse_lower_error 32 69 Primitive.Addresses.material2644

def v2645_pa : Scalar.QComplex := ((999999237727794516797205426763 : Int)/10^30,(-1234724191836982813767430589 : Int)/10^30)
theorem v2645_pa_checked : Scalar.distance (sourceCoefficient 32 70 1 0) v2645_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2645_pb : Scalar.QComplex := ((-532755697237123919362064 : Int)/10^30,(-431477162798314877174738311 : Int)/10^30)
theorem v2645_pb_checked : Scalar.distance (sourceCoefficient 32 70 1 1) v2645_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2645_pg : Scalar.QComplex := ((-93086355779310968498359 : Int)/10^30,(114936063023225840371 : Int)/10^30)
theorem v2645_pg_checked : Scalar.distance (sourceCoefficient 32 70 1 2) v2645_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2645_mb : Scalar.QComplex := ((-905100857352750243932579 : Int)/10^30,(-431476542395475397110785230 : Int)/10^30)
theorem v2645_mb_checked : Scalar.distance (sourceCoefficient 32 70 3 1) v2645_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2645_mg : Scalar.QComplex := ((-93086221934360594310139 : Int)/10^30,(195265352810989006689 : Int)/10^30)
theorem v2645_mg_checked : Scalar.distance (sourceCoefficient 32 70 3 2) v2645_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2645_upper : Scalar.QComplex := ((999995617324456276450315958283 : Int)/10^30,(-2960630317956326308817065194 : Int)/10^30)
theorem v2645_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 70 5) 1) 14) v2645_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2645 : Material (32 : Basis) (70 : Basis) where
  plus := ![v2645_pa,v2645_pb,v2645_pg]
  minus := ![(Primitive.Addresses.material2645 1).one,v2645_mb,v2645_mg]
  upper := v2645_upper
  lower := (Primitive.Addresses.material2645 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2645_pa_checked.trans (by decide +kernel)
    · exact v2645_pb_checked.trans (by decide +kernel)
    · exact v2645_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 70 Primitive.Addresses.material2645
    · exact v2645_mb_checked.trans (by decide +kernel)
    · exact v2645_mg_checked.trans (by decide +kernel)
  upper_error := v2645_upper_checked
  lower_error := reuse_lower_error 32 70 Primitive.Addresses.material2645

def v2646_pa : Scalar.QComplex := ((999999207437796048233535029608 : Int)/10^30,(-1259016989459906294341437015 : Int)/10^30)
theorem v2646_pa_checked : Scalar.distance (sourceCoefficient 32 71 1 0) v2646_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2646_pb : Scalar.QComplex := ((-543237489760624635239624 : Int)/10^30,(-431477147456255195420698879 : Int)/10^30)
theorem v2646_pb_checked : Scalar.distance (sourceCoefficient 32 71 1 1) v2646_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2646_pg : Scalar.QComplex := ((-93086352714578511152228 : Int)/10^30,(117197392440735263275 : Int)/10^30)
theorem v2646_pg_checked : Scalar.distance (sourceCoefficient 32 71 1 2) v2646_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2646_mb : Scalar.QComplex := ((-915582632733894037091284 : Int)/10^30,(-431476518008106562536349917 : Int)/10^30)
theorem v2646_mb_checked : Scalar.distance (sourceCoefficient 32 71 3 1) v2646_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2646_mg : Scalar.QComplex := ((-93086216918203837289580 : Int)/10^30,(197526678741776059331 : Int)/10^30)
theorem v2646_mg_checked : Scalar.distance (sourceCoefficient 32 71 3 2) v2646_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2646_upper : Scalar.QComplex := ((999995545107338049500336312603 : Int)/10^30,(-2984923027120191892966939591 : Int)/10^30)
theorem v2646_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 71 5) 1) 14) v2646_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2646 : Material (32 : Basis) (71 : Basis) where
  plus := ![v2646_pa,v2646_pb,v2646_pg]
  minus := ![(Primitive.Addresses.material2646 1).one,v2646_mb,v2646_mg]
  upper := v2646_upper
  lower := (Primitive.Addresses.material2646 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2646_pa_checked.trans (by decide +kernel)
    · exact v2646_pb_checked.trans (by decide +kernel)
    · exact v2646_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 71 Primitive.Addresses.material2646
    · exact v2646_mb_checked.trans (by decide +kernel)
    · exact v2646_mg_checked.trans (by decide +kernel)
  upper_error := v2646_upper_checked
  lower_error := reuse_lower_error 32 71 Primitive.Addresses.material2646

def v2647_pa : Scalar.QComplex := ((999999173899308060380940349306 : Int)/10^30,(-1285379594297686404727295023 : Int)/10^30)
theorem v2647_pa_checked : Scalar.distance (sourceCoefficient 32 72 1 0) v2647_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2647_pb : Scalar.QComplex := ((-554612357017343934339936 : Int)/10^30,(-431477130422880486751709053 : Int)/10^30)
theorem v2647_pb_checked : Scalar.distance (sourceCoefficient 32 72 1 1) v2647_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2647_pg : Scalar.QComplex := ((-93086349316209795139770 : Int)/10^30,(119651392762820817658 : Int)/10^30)
theorem v2647_pg_checked : Scalar.distance (sourceCoefficient 32 72 1 2) v2647_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2647_mb : Scalar.QComplex := ((-926957481056195180537325 : Int)/10^30,(-431476491158740058626059657 : Int)/10^30)
theorem v2647_mb_checked : Scalar.distance (sourceCoefficient 32 72 3 1) v2647_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2647_mg : Scalar.QComplex := ((-93086211402144632756936 : Int)/10^30,(199980675217485995373 : Int)/10^30)
theorem v2647_mg_checked : Scalar.distance (sourceCoefficient 32 72 3 2) v2647_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2647_upper : Scalar.QComplex := ((999995466069435660106175694915 : Int)/10^30,(-3011285534809581187409020890 : Int)/10^30)
theorem v2647_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 72 5) 1) 14) v2647_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2647 : Material (32 : Basis) (72 : Basis) where
  plus := ![v2647_pa,v2647_pb,v2647_pg]
  minus := ![(Primitive.Addresses.material2647 1).one,v2647_mb,v2647_mg]
  upper := v2647_upper
  lower := (Primitive.Addresses.material2647 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2647_pa_checked.trans (by decide +kernel)
    · exact v2647_pb_checked.trans (by decide +kernel)
    · exact v2647_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 72 Primitive.Addresses.material2647
    · exact v2647_mb_checked.trans (by decide +kernel)
    · exact v2647_mg_checked.trans (by decide +kernel)
  upper_error := v2647_upper_checked
  lower_error := reuse_lower_error 32 72 Primitive.Addresses.material2647

def v2648_pa : Scalar.QComplex := ((999999161708282414225827331586 : Int)/10^30,(-1294829229064027799076416243 : Int)/10^30)
theorem v2648_pa_checked : Scalar.distance (sourceCoefficient 32 73 1 0) v2648_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2648_pb : Scalar.QComplex := ((-558689660457394936491468 : Int)/10^30,(-431477124219948655200818384 : Int)/10^30)
theorem v2648_pb_checked : Scalar.distance (sourceCoefficient 32 73 1 1) v2648_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2648_pg : Scalar.QComplex := ((-93086348079693823817877 : Int)/10^30,(120531025360575970334 : Int)/10^30)
theorem v2648_pg_checked : Scalar.distance (sourceCoefficient 32 73 1 2) v2648_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2648_mb : Scalar.QComplex := ((-931034777625228969035762 : Int)/10^30,(-431476481437281302876253870 : Int)/10^30)
theorem v2648_mb_checked : Scalar.distance (sourceCoefficient 32 73 3 1) v2648_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2648_mg : Scalar.QComplex := ((-93086209406545807165297 : Int)/10^30,(200860306420656138070 : Int)/10^30)
theorem v2648_mg_checked : Scalar.distance (sourceCoefficient 32 73 3 2) v2648_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2648_upper : Scalar.QComplex := ((999995437569215828515879806950 : Int)/10^30,(-3020735134461197325311389349 : Int)/10^30)
theorem v2648_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 73 5) 1) 14) v2648_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2648 : Material (32 : Basis) (73 : Basis) where
  plus := ![v2648_pa,v2648_pb,v2648_pg]
  minus := ![(Primitive.Addresses.material2648 1).one,v2648_mb,v2648_mg]
  upper := v2648_upper
  lower := (Primitive.Addresses.material2648 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2648_pa_checked.trans (by decide +kernel)
    · exact v2648_pb_checked.trans (by decide +kernel)
    · exact v2648_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 73 Primitive.Addresses.material2648
    · exact v2648_mb_checked.trans (by decide +kernel)
    · exact v2648_mg_checked.trans (by decide +kernel)
  upper_error := v2648_upper_checked
  lower_error := reuse_lower_error 32 73 Primitive.Addresses.material2648

def v2649_pa : Scalar.QComplex := ((999999147883610030270966944828 : Int)/10^30,(-1305462390816800210690043679 : Int)/10^30)
theorem v2649_pa_checked : Scalar.distance (sourceCoefficient 32 74 1 0) v2649_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2649_pb : Scalar.QComplex := ((-563277628952945342643857 : Int)/10^30,(-431477117178699424908024903 : Int)/10^30)
theorem v2649_pb_checked : Scalar.distance (sourceCoefficient 32 74 1 1) v2649_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2649_pg : Scalar.QComplex := ((-93086346676713898613393 : Int)/10^30,(121520828234873892640 : Int)/10^30)
theorem v2649_pg_checked : Scalar.distance (sourceCoefficient 32 74 1 2) v2649_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2649_mb : Scalar.QComplex := ((-935622738336188064126438 : Int)/10^30,(-431476470436824517132758277 : Int)/10^30)
theorem v2649_mb_checked : Scalar.distance (sourceCoefficient 32 74 3 1) v2649_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2649_mg : Scalar.QComplex := ((-93086207149411102901857 : Int)/10^30,(201850107715696726468 : Int)/10^30)
theorem v2649_mg_checked : Scalar.distance (sourceCoefficient 32 74 3 2) v2649_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2649_upper : Scalar.QComplex := ((999995405392691482400305612585 : Int)/10^30,(-3031368256516993994867182053 : Int)/10^30)
theorem v2649_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 74 5) 1) 14) v2649_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2649 : Material (32 : Basis) (74 : Basis) where
  plus := ![v2649_pa,v2649_pb,v2649_pg]
  minus := ![(Primitive.Addresses.material2649 1).one,v2649_mb,v2649_mg]
  upper := v2649_upper
  lower := (Primitive.Addresses.material2649 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2649_pa_checked.trans (by decide +kernel)
    · exact v2649_pb_checked.trans (by decide +kernel)
    · exact v2649_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 74 Primitive.Addresses.material2649
    · exact v2649_mb_checked.trans (by decide +kernel)
    · exact v2649_mg_checked.trans (by decide +kernel)
  upper_error := v2649_upper_checked
  lower_error := reuse_lower_error 32 74 Primitive.Addresses.material2649

def v2650_pa : Scalar.QComplex := ((999999128433272453780003081515 : Int)/10^30,(-1320277506990056779483554555 : Int)/10^30)
theorem v2650_pa_checked : Scalar.distance (sourceCoefficient 32 75 1 0) v2650_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2650_pb : Scalar.QComplex := ((-569670016001578145543176 : Int)/10^30,(-431477107259721565392246239 : Int)/10^30)
theorem v2650_pb_checked : Scalar.distance (sourceCoefficient 32 75 1 1) v2650_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2650_pg : Scalar.QComplex := ((-93086344701478610465037 : Int)/10^30,(122899914232761324545 : Int)/10^30)
theorem v2650_pg_checked : Scalar.distance (sourceCoefficient 32 75 1 2) v2650_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2650_mb : Scalar.QComplex := ((-942015114445011863716435 : Int)/10^30,(-431476455001508230360877521 : Int)/10^30)
theorem v2650_mb_checked : Scalar.distance (sourceCoefficient 32 75 3 1) v2650_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2650_mg : Scalar.QComplex := ((-93086203984087445774668 : Int)/10^30,(203229191495548321639 : Int)/10^30)
theorem v2650_mg_checked : Scalar.distance (sourceCoefficient 32 75 3 2) v2650_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2650_upper : Scalar.QComplex := ((999995360372836376701881485885 : Int)/10^30,(-3046183317055357193208414123 : Int)/10^30)
theorem v2650_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 75 5) 1) 14) v2650_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2650 : Material (32 : Basis) (75 : Basis) where
  plus := ![v2650_pa,v2650_pb,v2650_pg]
  minus := ![(Primitive.Addresses.material2650 1).one,v2650_mb,v2650_mg]
  upper := v2650_upper
  lower := (Primitive.Addresses.material2650 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2650_pa_checked.trans (by decide +kernel)
    · exact v2650_pb_checked.trans (by decide +kernel)
    · exact v2650_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 75 Primitive.Addresses.material2650
    · exact v2650_mb_checked.trans (by decide +kernel)
    · exact v2650_mg_checked.trans (by decide +kernel)
  upper_error := v2650_upper_checked
  lower_error := reuse_lower_error 32 75 Primitive.Addresses.material2650

def v2651_pa : Scalar.QComplex := ((999999111944724151043431315637 : Int)/10^30,(-1332707681022263852023933264 : Int)/10^30)
theorem v2651_pa_checked : Scalar.distance (sourceCoefficient 32 76 1 0) v2651_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2651_pb : Scalar.QComplex := ((-575033354470790136835151 : Int)/10^30,(-431477098840086573828714301 : Int)/10^30)
theorem v2651_pb_checked : Scalar.distance (sourceCoefficient 32 76 1 1) v2651_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2651_pg : Scalar.QComplex := ((-93086343025827710687200 : Int)/10^30,(124056994518262319890 : Int)/10^30)
theorem v2651_pg_checked : Scalar.distance (sourceCoefficient 32 76 1 2) v2651_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2651_mb : Scalar.QComplex := ((-947378443651442034807626 : Int)/10^30,(-431476441953556830679981388 : Int)/10^30)
theorem v2651_mb_checked : Scalar.distance (sourceCoefficient 32 76 3 1) v2651_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2651_mg : Scalar.QComplex := ((-93086201309928996492417 : Int)/10^30,(204386269904204187517 : Int)/10^30)
theorem v2651_mg_checked : Scalar.distance (sourceCoefficient 32 76 3 2) v2651_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2651_upper : Scalar.QComplex := ((999995322430959908711150537545 : Int)/10^30,(-3058613444116541654482104764 : Int)/10^30)
theorem v2651_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 76 5) 1) 14) v2651_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2651 : Material (32 : Basis) (76 : Basis) where
  plus := ![v2651_pa,v2651_pb,v2651_pg]
  minus := ![(Primitive.Addresses.material2651 1).one,v2651_mb,v2651_mg]
  upper := v2651_upper
  lower := (Primitive.Addresses.material2651 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2651_pa_checked.trans (by decide +kernel)
    · exact v2651_pb_checked.trans (by decide +kernel)
    · exact v2651_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 76 Primitive.Addresses.material2651
    · exact v2651_mb_checked.trans (by decide +kernel)
    · exact v2651_mg_checked.trans (by decide +kernel)
  upper_error := v2651_upper_checked
  lower_error := reuse_lower_error 32 76 Primitive.Addresses.material2651

def v2652_pa : Scalar.QComplex := ((999999108105459454562420010842 : Int)/10^30,(-1335585371893164942963190673 : Int)/10^30)
theorem v2652_pa_checked : Scalar.distance (sourceCoefficient 32 77 1 0) v2652_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2652_pb : Scalar.QComplex := ((-576275012873989204990598 : Int)/10^30,(-431477096878198101575889663 : Int)/10^30)
theorem v2652_pb_checked : Scalar.distance (sourceCoefficient 32 77 1 1) v2652_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2652_pg : Scalar.QComplex := ((-93086342635508284912152 : Int)/10^30,(124324868431691316644 : Int)/10^30)
theorem v2652_pg_checked : Scalar.distance (sourceCoefficient 32 77 1 2) v2652_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2652_mb : Scalar.QComplex := ((-948620099899293541482213 : Int)/10^30,(-431476438920173809185651637 : Int)/10^30)
theorem v2652_mb_checked : Scalar.distance (sourceCoefficient 32 77 3 1) v2652_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2652_mg : Scalar.QComplex := ((-93086200688446593355107 : Int)/10^30,(204654143381063398749 : Int)/10^30)
theorem v2652_mg_checked : Scalar.distance (sourceCoefficient 32 77 3 2) v2652_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2652_upper : Scalar.QComplex := ((999995313625067549265133087476 : Int)/10^30,(-3061491124075237659776014649 : Int)/10^30)
theorem v2652_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 77 5) 1) 14) v2652_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2652 : Material (32 : Basis) (77 : Basis) where
  plus := ![v2652_pa,v2652_pb,v2652_pg]
  minus := ![(Primitive.Addresses.material2652 1).one,v2652_mb,v2652_mg]
  upper := v2652_upper
  lower := (Primitive.Addresses.material2652 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2652_pa_checked.trans (by decide +kernel)
    · exact v2652_pb_checked.trans (by decide +kernel)
    · exact v2652_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 77 Primitive.Addresses.material2652
    · exact v2652_mb_checked.trans (by decide +kernel)
    · exact v2652_mg_checked.trans (by decide +kernel)
  upper_error := v2652_upper_checked
  lower_error := reuse_lower_error 32 77 Primitive.Addresses.material2652

def v2653_pa : Scalar.QComplex := ((999999084850743349099814417055 : Int)/10^30,(-1352884945515929090039703701 : Int)/10^30)
theorem v2653_pa_checked : Scalar.distance (sourceCoefficient 32 78 1 0) v2653_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2653_pb : Scalar.QComplex := ((-583739386818170033269302 : Int)/10^30,(-431477084983669863323155355 : Int)/10^30)
theorem v2653_pb_checked : Scalar.distance (sourceCoefficient 32 78 1 1) v2653_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2653_pg : Scalar.QComplex := ((-93086340270103583630144 : Int)/10^30,(125935223634122617647 : Int)/10^30)
theorem v2653_pg_checked : Scalar.distance (sourceCoefficient 32 78 1 2) v2653_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2653_mb : Scalar.QComplex := ((-956084460799704651653814 : Int)/10^30,(-431476420584231468904081620 : Int)/10^30)
theorem v2653_mb_checked : Scalar.distance (sourceCoefficient 32 78 3 1) v2653_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2653_mg : Scalar.QComplex := ((-93086196933378760829124 : Int)/10^30,(206264495942648137685 : Int)/10^30)
theorem v2653_mg_checked : Scalar.distance (sourceCoefficient 32 78 3 2) v2653_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2653_upper : Scalar.QComplex := ((999995260512891411139095502640 : Int)/10^30,(-3078790631796788699750797332 : Int)/10^30)
theorem v2653_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 78 5) 1) 14) v2653_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2653 : Material (32 : Basis) (78 : Basis) where
  plus := ![v2653_pa,v2653_pb,v2653_pg]
  minus := ![(Primitive.Addresses.material2653 1).one,v2653_mb,v2653_mg]
  upper := v2653_upper
  lower := (Primitive.Addresses.material2653 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2653_pa_checked.trans (by decide +kernel)
    · exact v2653_pb_checked.trans (by decide +kernel)
    · exact v2653_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 78 Primitive.Addresses.material2653
    · exact v2653_mb_checked.trans (by decide +kernel)
    · exact v2653_mg_checked.trans (by decide +kernel)
  upper_error := v2653_upper_checked
  lower_error := reuse_lower_error 32 78 Primitive.Addresses.material2653

def v2654_pa : Scalar.QComplex := ((999999077290042427338884663316 : Int)/10^30,(-1358462021460907985045117597 : Int)/10^30)
theorem v2654_pa_checked : Scalar.distance (sourceCoefficient 32 79 1 0) v2654_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2654_pb : Scalar.QComplex := ((-586145768664519620851807 : Int)/10^30,(-431477081112384703885227433 : Int)/10^30)
theorem v2654_pb_checked : Scalar.distance (sourceCoefficient 32 79 1 1) v2654_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2654_pg : Scalar.QComplex := ((-93086339500611104460225 : Int)/10^30,(126454373609106236610 : Int)/10^30)
theorem v2654_pg_checked : Scalar.distance (sourceCoefficient 32 79 1 2) v2654_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2654_mb : Scalar.QComplex := ((-958490838409303564373254 : Int)/10^30,(-431476414636348596937977527 : Int)/10^30)
theorem v2654_mb_checked : Scalar.distance (sourceCoefficient 32 79 3 1) v2654_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2654_mg : Scalar.QComplex := ((-93086195715883521412466 : Int)/10^30,(206783645060291141767 : Int)/10^30)
theorem v2654_mg_checked : Scalar.distance (sourceCoefficient 32 79 3 2) v2654_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2654_upper : Scalar.QComplex := ((999995243326674617497950267325 : Int)/10^30,(-3084367686386284214541261384 : Int)/10^30)
theorem v2654_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 79 5) 1) 14) v2654_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2654 : Material (32 : Basis) (79 : Basis) where
  plus := ![v2654_pa,v2654_pb,v2654_pg]
  minus := ![(Primitive.Addresses.material2654 1).one,v2654_mb,v2654_mg]
  upper := v2654_upper
  lower := (Primitive.Addresses.material2654 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2654_pa_checked.trans (by decide +kernel)
    · exact v2654_pb_checked.trans (by decide +kernel)
    · exact v2654_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 79 Primitive.Addresses.material2654
    · exact v2654_mb_checked.trans (by decide +kernel)
    · exact v2654_mg_checked.trans (by decide +kernel)
  upper_error := v2654_upper_checked
  lower_error := reuse_lower_error 32 79 Primitive.Addresses.material2654

def v2655_pa : Scalar.QComplex := ((999999065417237649705044688158 : Int)/10^30,(-1367173965249357075510725708 : Int)/10^30)
theorem v2655_pa_checked : Scalar.distance (sourceCoefficient 32 80 1 0) v2655_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2655_pb : Scalar.QComplex := ((-589904774896763024130523 : Int)/10^30,(-431477075029246271454262041 : Int)/10^30)
theorem v2655_pb_checked : Scalar.distance (sourceCoefficient 32 80 1 1) v2655_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2655_pg : Scalar.QComplex := ((-93086338291828195366287 : Int)/10^30,(127265337172972184602 : Int)/10^30)
theorem v2655_pg_checked : Scalar.distance (sourceCoefficient 32 80 1 2) v2655_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2655_mb : Scalar.QComplex := ((-962249837992422659512755 : Int)/10^30,(-431476405309359350467419394 : Int)/10^30)
theorem v2655_mb_checked : Scalar.distance (sourceCoefficient 32 80 3 1) v2655_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2655_mg : Scalar.QComplex := ((-93086193807276031230401 : Int)/10^30,(207594607279073083079 : Int)/10^30)
theorem v2655_mg_checked : Scalar.distance (sourceCoefficient 32 80 3 2) v2655_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2655_upper : Scalar.QComplex := ((999995216417862885515698967822 : Int)/10^30,(-3093079596707932455157274955 : Int)/10^30)
theorem v2655_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 80 5) 1) 14) v2655_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2655 : Material (32 : Basis) (80 : Basis) where
  plus := ![v2655_pa,v2655_pb,v2655_pg]
  minus := ![(Primitive.Addresses.material2655 1).one,v2655_mb,v2655_mg]
  upper := v2655_upper
  lower := (Primitive.Addresses.material2655 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2655_pa_checked.trans (by decide +kernel)
    · exact v2655_pb_checked.trans (by decide +kernel)
    · exact v2655_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 80 Primitive.Addresses.material2655
    · exact v2655_mb_checked.trans (by decide +kernel)
    · exact v2655_mg_checked.trans (by decide +kernel)
  upper_error := v2655_upper_checked
  lower_error := reuse_lower_error 32 80 Primitive.Addresses.material2655

def v2656_pa : Scalar.QComplex := ((999999029209277318575592947200 : Int)/10^30,(-1393406079694007065653717723 : Int)/10^30)
theorem v2656_pa_checked : Scalar.distance (sourceCoefficient 32 81 1 0) v2656_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2656_pb : Scalar.QComplex := ((-601223337366441398846070 : Int)/10^30,(-431477056448922739411681210 : Int)/10^30)
theorem v2656_pb_checked : Scalar.distance (sourceCoefficient 32 81 1 1) v2656_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2656_pg : Scalar.QComplex := ((-93086334602345233729007 : Int)/10^30,(129707190489875662908 : Int)/10^30)
theorem v2656_pg_checked : Scalar.distance (sourceCoefficient 32 81 1 2) v2656_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2656_mb : Scalar.QComplex := ((-973568380213700561462506 : Int)/10^30,(-431476376961633094526129594 : Int)/10^30)
theorem v2656_mb_checked : Scalar.distance (sourceCoefficient 32 81 3 1) v2656_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2656_mg : Scalar.QComplex := ((-93086188010585007859399 : Int)/10^30,(210036456502905345543 : Int)/10^30)
theorem v2656_mg_checked : Scalar.distance (sourceCoefficient 32 81 3 2) v2656_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2656_upper : Scalar.QComplex := ((999995134935706709256754475820 : Int)/10^30,(-3119311609591274649588838371 : Int)/10^30)
theorem v2656_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 32 81 5) 1) 14) v2656_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2656 : Material (32 : Basis) (81 : Basis) where
  plus := ![v2656_pa,v2656_pb,v2656_pg]
  minus := ![(Primitive.Addresses.material2656 1).one,v2656_mb,v2656_mg]
  upper := v2656_upper
  lower := (Primitive.Addresses.material2656 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2656_pa_checked.trans (by decide +kernel)
    · exact v2656_pb_checked.trans (by decide +kernel)
    · exact v2656_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 32 81 Primitive.Addresses.material2656
    · exact v2656_mb_checked.trans (by decide +kernel)
    · exact v2656_mg_checked.trans (by decide +kernel)
  upper_error := v2656_upper_checked
  lower_error := reuse_lower_error 32 81 Primitive.Addresses.material2656

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
