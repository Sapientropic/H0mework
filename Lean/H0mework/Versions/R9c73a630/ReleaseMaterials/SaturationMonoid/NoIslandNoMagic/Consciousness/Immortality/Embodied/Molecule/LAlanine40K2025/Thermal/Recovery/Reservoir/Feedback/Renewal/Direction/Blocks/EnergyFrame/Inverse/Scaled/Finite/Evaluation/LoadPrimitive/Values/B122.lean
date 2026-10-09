import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B081
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B082

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1953_pa : Scalar.QComplex := ((999999331193850372097323471201 : Int)/10^30,(-1156551707427791389604533207 : Int)/10^30)
theorem v1953_pa_checked : Scalar.distance (sourceCoefficient 22 73 1 0) v1953_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1953_pb : Scalar.QComplex := ((-499026005407483788881783 : Int)/10^30,(-431477182084380707072947809 : Int)/10^30)
theorem v1953_pb_checked : Scalar.distance (sourceCoefficient 22 73 1 1) v1953_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1953_pg : Scalar.QComplex := ((-93086362209897741154653 : Int)/10^30,(107659263155276331728 : Int)/10^30)
theorem v1953_pg_checked : Scalar.distance (sourceCoefficient 22 73 1 2) v1953_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1953_mb : Scalar.QComplex := ((-871371194725222103738293 : Int)/10^30,(-431476590788738965977411663 : Int)/10^30)
theorem v1953_mb_checked : Scalar.distance (sourceCoefficient 22 73 3 1) v1953_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1953_mg : Scalar.QComplex := ((-93086234644495523705550 : Int)/10^30,(187988561201831416993 : Int)/10^30)
theorem v1953_mg_checked : Scalar.distance (sourceCoefficient 22 73 3 2) v1953_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1953_upper : Scalar.QComplex := ((999995845708989262916057482256 : Int)/10^30,(-2882458111289800858967107345 : Int)/10^30)
theorem v1953_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 73 5) 1) 14) v1953_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1953 : Material (22 : Basis) (73 : Basis) where
  plus := ![v1953_pa,v1953_pb,v1953_pg]
  minus := ![(Primitive.Addresses.material1953 1).one,v1953_mb,v1953_mg]
  upper := v1953_upper
  lower := (Primitive.Addresses.material1953 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1953_pa_checked.trans (by decide +kernel)
    · exact v1953_pb_checked.trans (by decide +kernel)
    · exact v1953_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 73 Primitive.Addresses.material1953
    · exact v1953_mb_checked.trans (by decide +kernel)
    · exact v1953_mg_checked.trans (by decide +kernel)
  upper_error := v1953_upper_checked
  lower_error := reuse_lower_error 22 73 Primitive.Addresses.material1953

def v1954_pa : Scalar.QComplex := ((999999318839506475577712126126 : Int)/10^30,(-1167184870990549910200609899 : Int)/10^30)
theorem v1954_pa_checked : Scalar.distance (sourceCoefficient 22 74 1 0) v1954_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1954_pb : Scalar.QComplex := ((-503613974423679706957522 : Int)/10^30,(-431477175466073909368390380 : Int)/10^30)
theorem v1954_pb_checked : Scalar.distance (sourceCoefficient 22 74 1 1) v1954_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1954_pg : Scalar.QComplex := ((-93086360920974169840109 : Int)/10^30,(108649066169978536460 : Int)/10^30)
theorem v1954_pg_checked : Scalar.distance (sourceCoefficient 22 74 1 2) v1954_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1954_mb : Scalar.QComplex := ((-875959156321806787595801 : Int)/10^30,(-431476580211224006047727258 : Int)/10^30)
theorem v1954_mb_checked : Scalar.distance (sourceCoefficient 22 74 3 1) v1954_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1954_mg : Scalar.QComplex := ((-93086232501417009701085 : Int)/10^30,(188978362735701732036 : Int)/10^30)
theorem v1954_mg_checked : Scalar.distance (sourceCoefficient 22 74 3 2) v1954_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1954_upper : Scalar.QComplex := ((999995815002788090482343765041 : Int)/10^30,(-2893091237693234523898478899 : Int)/10^30)
theorem v1954_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 74 5) 1) 14) v1954_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1954 : Material (22 : Basis) (74 : Basis) where
  plus := ![v1954_pa,v1954_pb,v1954_pg]
  minus := ![(Primitive.Addresses.material1954 1).one,v1954_mb,v1954_mg]
  upper := v1954_upper
  lower := (Primitive.Addresses.material1954 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1954_pa_checked.trans (by decide +kernel)
    · exact v1954_pb_checked.trans (by decide +kernel)
    · exact v1954_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 74 Primitive.Addresses.material1954
    · exact v1954_mb_checked.trans (by decide +kernel)
    · exact v1954_mg_checked.trans (by decide +kernel)
  upper_error := v1954_upper_checked
  lower_error := reuse_lower_error 22 74 Primitive.Addresses.material1954

def v1955_pa : Scalar.QComplex := ((999999301437768166156638248419 : Int)/10^30,(-1181999989711715259295279021 : Int)/10^30)
theorem v1955_pa_checked : Scalar.distance (sourceCoefficient 22 75 1 0) v1955_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1955_pb : Scalar.QComplex := ((-510006362205222702945595 : Int)/10^30,(-431477166136379031919753438 : Int)/10^30)
theorem v1955_pb_checked : Scalar.distance (sourceCoefficient 22 75 1 1) v1955_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1955_pg : Scalar.QComplex := ((-93086359104652869077691 : Int)/10^30,(110028152365512404312 : Int)/10^30)
theorem v1955_pg_checked : Scalar.distance (sourceCoefficient 22 75 1 2) v1955_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1955_mb : Scalar.QComplex := ((-882351533672065180582246 : Int)/10^30,(-431476565365189849457514852 : Int)/10^30)
theorem v1955_mb_checked : Scalar.distance (sourceCoefficient 22 75 3 1) v1955_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1955_mg : Scalar.QComplex := ((-93086229495007110228920 : Int)/10^30,(190357446850335303456 : Int)/10^30)
theorem v1955_mg_checked : Scalar.distance (sourceCoefficient 22 75 3 2) v1955_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1955_upper : Scalar.QComplex := ((999995772031524803246436376819 : Int)/10^30,(-2907906304315199195218921676 : Int)/10^30)
theorem v1955_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 75 5) 1) 14) v1955_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1955 : Material (22 : Basis) (75 : Basis) where
  plus := ![v1955_pa,v1955_pb,v1955_pg]
  minus := ![(Primitive.Addresses.material1955 1).one,v1955_mb,v1955_mg]
  upper := v1955_upper
  lower := (Primitive.Addresses.material1955 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1955_pa_checked.trans (by decide +kernel)
    · exact v1955_pb_checked.trans (by decide +kernel)
    · exact v1955_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 75 Primitive.Addresses.material1955
    · exact v1955_mb_checked.trans (by decide +kernel)
    · exact v1955_mg_checked.trans (by decide +kernel)
  upper_error := v1955_upper_checked
  lower_error := reuse_lower_error 22 75 Primitive.Addresses.material1955

def v1956_pa : Scalar.QComplex := ((999999286668034966732009397698 : Int)/10^30,(-1194430165905082808739162330 : Int)/10^30)
theorem v1956_pa_checked : Scalar.distance (sourceCoefficient 22 76 1 0) v1956_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1956_pb : Scalar.QComplex := ((-515369701296096094070059 : Int)/10^30,(-431477158211164058852212886 : Int)/10^30)
theorem v1956_pb_checked : Scalar.distance (sourceCoefficient 22 76 1 1) v1956_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1956_pg : Scalar.QComplex := ((-93086357562333932111411 : Int)/10^30,(111185232818658987490 : Int)/10^30)
theorem v1956_pg_checked : Scalar.distance (sourceCoefficient 22 76 1 2) v1956_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1956_mb : Scalar.QComplex := ((-887714863926818728144004 : Int)/10^30,(-431476552811657747711651642 : Int)/10^30)
theorem v1956_mb_checked : Scalar.distance (sourceCoefficient 22 76 3 1) v1956_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1956_mg : Scalar.QComplex := ((-93086226954180429442052 : Int)/10^30,(191514525541696173602 : Int)/10^30)
theorem v1956_mg_checked : Scalar.distance (sourceCoefficient 22 76 3 2) v1956_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1956_upper : Scalar.QComplex := ((999995735808457148627533977156 : Int)/10^30,(-2920336436504059853229751204 : Int)/10^30)
theorem v1956_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 76 5) 1) 14) v1956_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1956 : Material (22 : Basis) (76 : Basis) where
  plus := ![v1956_pa,v1956_pb,v1956_pg]
  minus := ![(Primitive.Addresses.material1956 1).one,v1956_mb,v1956_mg]
  upper := v1956_upper
  lower := (Primitive.Addresses.material1956 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1956_pa_checked.trans (by decide +kernel)
    · exact v1956_pb_checked.trans (by decide +kernel)
    · exact v1956_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 76 Primitive.Addresses.material1956
    · exact v1956_mb_checked.trans (by decide +kernel)
    · exact v1956_mg_checked.trans (by decide +kernel)
  upper_error := v1956_upper_checked
  lower_error := reuse_lower_error 22 76 Primitive.Addresses.material1956

def v1957_pa : Scalar.QComplex := ((999999283226690566569401294115 : Int)/10^30,(-1197307857279356569937417471 : Int)/10^30)
theorem v1957_pa_checked : Scalar.distance (sourceCoefficient 22 77 1 0) v1957_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1957_pb : Scalar.QComplex := ((-516611359844091146508635 : Int)/10^30,(-431477156363738020426607595 : Int)/10^30)
theorem v1957_pb_checked : Scalar.distance (sourceCoefficient 22 77 1 1) v1957_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1957_pg : Scalar.QComplex := ((-93086357202881988248387 : Int)/10^30,(111453106771135620014 : Int)/10^30)
theorem v1957_pg_checked : Scalar.distance (sourceCoefficient 22 77 1 2) v1957_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1957_mb : Scalar.QComplex := ((-888956520418242090383799 : Int)/10^30,(-431476549892736992472532865 : Int)/10^30)
theorem v1957_mb_checked : Scalar.distance (sourceCoefficient 22 77 3 1) v1957_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1957_mg : Scalar.QComplex := ((-93086226363565463027041 : Int)/10^30,(191782399084240252736 : Int)/10^30)
theorem v1957_mg_checked : Scalar.distance (sourceCoefficient 22 77 3 2) v1957_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1957_upper : Scalar.QComplex := ((999995727400483624068818108456 : Int)/10^30,(-2923214117652902111466468979 : Int)/10^30)
theorem v1957_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 77 5) 1) 14) v1957_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1957 : Material (22 : Basis) (77 : Basis) where
  plus := ![v1957_pa,v1957_pb,v1957_pg]
  minus := ![(Primitive.Addresses.material1957 1).one,v1957_mb,v1957_mg]
  upper := v1957_upper
  lower := (Primitive.Addresses.material1957 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1957_pa_checked.trans (by decide +kernel)
    · exact v1957_pb_checked.trans (by decide +kernel)
    · exact v1957_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 77 Primitive.Addresses.material1957
    · exact v1957_mb_checked.trans (by decide +kernel)
    · exact v1957_mg_checked.trans (by decide +kernel)
  upper_error := v1957_upper_checked
  lower_error := reuse_lower_error 22 77 Primitive.Addresses.material1957

def v1958_pa : Scalar.QComplex := ((999999262364118640512143484725 : Int)/10^30,(-1214607433952337640656921333 : Int)/10^30)
theorem v1958_pa_checked : Scalar.distance (sourceCoefficient 22 78 1 0) v1958_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1958_pb : Scalar.QComplex := ((-524075734665671935303936 : Int)/10^30,(-431477145157314025471976801 : Int)/10^30)
theorem v1958_pb_checked : Scalar.distance (sourceCoefficient 22 78 1 1) v1958_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1958_pg : Scalar.QComplex := ((-93086355023040747285529 : Int)/10^30,(113063462210178414595 : Int)/10^30)
theorem v1958_pg_checked : Scalar.distance (sourceCoefficient 22 78 1 2) v1958_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1958_mb : Scalar.QComplex := ((-896420882789855805277480 : Int)/10^30,(-431476532244897882119759366 : Int)/10^30)
theorem v1958_mb_checked : Scalar.distance (sourceCoefficient 22 78 3 1) v1958_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1958_mg : Scalar.QComplex := ((-93086222794060817541388 : Int)/10^30,(193392752042569305936 : Int)/10^30)
theorem v1958_mg_checked : Scalar.distance (sourceCoefficient 22 78 3 2) v1958_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1958_upper : Scalar.QComplex := ((999995676680442838132677388250 : Int)/10^30,(-2940513632553289372173330407 : Int)/10^30)
theorem v1958_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 78 5) 1) 14) v1958_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1958 : Material (22 : Basis) (78 : Basis) where
  plus := ![v1958_pa,v1958_pb,v1958_pg]
  minus := ![(Primitive.Addresses.material1958 1).one,v1958_mb,v1958_mg]
  upper := v1958_upper
  lower := (Primitive.Addresses.material1958 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1958_pa_checked.trans (by decide +kernel)
    · exact v1958_pb_checked.trans (by decide +kernel)
    · exact v1958_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 78 Primitive.Addresses.material1958
    · exact v1958_mb_checked.trans (by decide +kernel)
    · exact v1958_mg_checked.trans (by decide +kernel)
  upper_error := v1958_upper_checked
  lower_error := reuse_lower_error 22 78 Primitive.Addresses.material1958

def v1959_pa : Scalar.QComplex := ((999999255574602608122020622606 : Int)/10^30,(-1220184510889473500982312780 : Int)/10^30)
theorem v1959_pa_checked : Scalar.distance (sourceCoefficient 22 79 1 0) v1959_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1959_pb : Scalar.QComplex := ((-526482116797417120103619 : Int)/10^30,(-431477141507861478931923087 : Int)/10^30)
theorem v1959_pb_checked : Scalar.distance (sourceCoefficient 22 79 1 1) v1959_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1959_pg : Scalar.QComplex := ((-93086354313370639061353 : Int)/10^30,(113582612262125655177 : Int)/10^30)
theorem v1959_pg_checked : Scalar.distance (sourceCoefficient 22 79 1 2) v1959_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1959_mb : Scalar.QComplex := ((-898827260876281762909136 : Int)/10^30,(-431476526518847294169562791 : Int)/10^30)
theorem v1959_mb_checked : Scalar.distance (sourceCoefficient 22 79 3 1) v1959_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1959_mg : Scalar.QComplex := ((-93086221636387860379731 : Int)/10^30,(193911901288799914806 : Int)/10^30)
theorem v1959_mg_checked : Scalar.distance (sourceCoefficient 22 79 3 2) v1959_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1959_upper : Scalar.QComplex := ((999995660265408072900121701937 : Int)/10^30,(-2946090689465935532289876134 : Int)/10^30)
theorem v1959_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 79 5) 1) 14) v1959_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1959 : Material (22 : Basis) (79 : Basis) where
  plus := ![v1959_pa,v1959_pb,v1959_pg]
  minus := ![(Primitive.Addresses.material1959 1).one,v1959_mb,v1959_mg]
  upper := v1959_upper
  lower := (Primitive.Addresses.material1959 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1959_pa_checked.trans (by decide +kernel)
    · exact v1959_pb_checked.trans (by decide +kernel)
    · exact v1959_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 79 Primitive.Addresses.material1959
    · exact v1959_mb_checked.trans (by decide +kernel)
    · exact v1959_mg_checked.trans (by decide +kernel)
  upper_error := v1959_upper_checked
  lower_error := reuse_lower_error 22 79 Primitive.Addresses.material1959

def v1960_pa : Scalar.QComplex := ((999999244906464841714245819500 : Int)/10^30,(-1228896456236376600986715935 : Int)/10^30)
theorem v1960_pa_checked : Scalar.distance (sourceCoefficient 22 80 1 0) v1960_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1960_pb : Scalar.QComplex := ((-530241123477952404410998 : Int)/10^30,(-431477135771247510527213250 : Int)/10^30)
theorem v1960_pb_checked : Scalar.distance (sourceCoefficient 22 80 1 1) v1960_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1960_pg : Scalar.QComplex := ((-93086353198036185394289 : Int)/10^30,(114393575946884031289 : Int)/10^30)
theorem v1960_pg_checked : Scalar.distance (sourceCoefficient 22 80 1 2) v1960_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1960_mb : Scalar.QComplex := ((-902586261206727577729899 : Int)/10^30,(-431476517538381995842662294 : Int)/10^30)
theorem v1960_mb_checked : Scalar.distance (sourceCoefficient 22 80 3 1) v1960_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1960_mg : Scalar.QComplex := ((-93086219821228686504689 : Int)/10^30,(194722863709116047495 : Int)/10^30)
theorem v1960_mg_checked : Scalar.distance (sourceCoefficient 22 80 3 2) v1960_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1960_upper : Scalar.QComplex := ((999995634561258868183693860315 : Int)/10^30,(-2954802603425181436149136049 : Int)/10^30)
theorem v1960_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 80 5) 1) 14) v1960_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1960 : Material (22 : Basis) (80 : Basis) where
  plus := ![v1960_pa,v1960_pb,v1960_pg]
  minus := ![(Primitive.Addresses.material1960 1).one,v1960_mb,v1960_mg]
  upper := v1960_upper
  lower := (Primitive.Addresses.material1960 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1960_pa_checked.trans (by decide +kernel)
    · exact v1960_pb_checked.trans (by decide +kernel)
    · exact v1960_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 80 Primitive.Addresses.material1960
    · exact v1960_mb_checked.trans (by decide +kernel)
    · exact v1960_mg_checked.trans (by decide +kernel)
  upper_error := v1960_upper_checked
  lower_error := reuse_lower_error 22 80 Primitive.Addresses.material1960

def v1961_pa : Scalar.QComplex := ((999999212325819345449695550495 : Int)/10^30,(-1255128575436989140292221181 : Int)/10^30)
theorem v1961_pa_checked : Scalar.distance (sourceCoefficient 22 81 1 0) v1961_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1961_pb : Scalar.QComplex := ((-541559687315691291598793 : Int)/10^30,(-431477118234327104475501521 : Int)/10^30)
theorem v1961_pb_checked : Scalar.distance (sourceCoefficient 22 81 1 1) v1961_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1961_pg : Scalar.QComplex := ((-93086349789931368012052 : Int)/10^30,(116835429632717138621 : Int)/10^30)
theorem v1961_pg_checked : Scalar.distance (sourceCoefficient 22 81 1 2) v1961_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1961_mb : Scalar.QComplex := ((-913904805696475387358238 : Int)/10^30,(-431476490234057296810964805 : Int)/10^30)
theorem v1961_mb_checked : Scalar.distance (sourceCoefficient 22 81 3 1) v1961_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1961_mg : Scalar.QComplex := ((-93086214305915384249134 : Int)/10^30,(197164713544694467308 : Int)/10^30)
theorem v1961_mg_checked : Scalar.distance (sourceCoefficient 22 81 3 2) v1961_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1961_upper : Scalar.QComplex := ((999995556706403915970396338594 : Int)/10^30,(-2981034627324895433841205028 : Int)/10^30)
theorem v1961_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 81 5) 1) 14) v1961_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1961 : Material (22 : Basis) (81 : Basis) where
  plus := ![v1961_pa,v1961_pb,v1961_pg]
  minus := ![(Primitive.Addresses.material1961 1).one,v1961_mb,v1961_mg]
  upper := v1961_upper
  lower := (Primitive.Addresses.material1961 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1961_pa_checked.trans (by decide +kernel)
    · exact v1961_pb_checked.trans (by decide +kernel)
    · exact v1961_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 81 Primitive.Addresses.material1961
    · exact v1961_mb_checked.trans (by decide +kernel)
    · exact v1961_mg_checked.trans (by decide +kernel)
  upper_error := v1961_upper_checked
  lower_error := reuse_lower_error 22 81 Primitive.Addresses.material1961

def v1962_pa : Scalar.QComplex := ((999999199800112013202967962339 : Int)/10^30,(-1265068826449270043822485708 : Int)/10^30)
theorem v1962_pa_checked : Scalar.distance (sourceCoefficient 22 82 1 0) v1962_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1962_pb : Scalar.QComplex := ((-545848679854806539282977 : Int)/10^30,(-431477111485556692502227159 : Int)/10^30)
theorem v1962_pb_checked : Scalar.distance (sourceCoefficient 22 82 1 1) v1962_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1962_pg : Scalar.QComplex := ((-93086348478958960669301 : Int)/10^30,(117760731860848850231 : Int)/10^30)
theorem v1962_pg_checked : Scalar.distance (sourceCoefficient 22 82 1 2) v1962_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1962_mb : Scalar.QComplex := ((-918193790814717783890501 : Int)/10^30,(-431476479784082005510079546 : Int)/10^30)
theorem v1962_mb_checked : Scalar.distance (sourceCoefficient 22 82 3 1) v1962_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1962_mg : Scalar.QComplex := ((-93086212196449316228998 : Int)/10^30,(198090014296983727452 : Int)/10^30)
theorem v1962_mg_checked : Scalar.distance (sourceCoefficient 22 82 3 2) v1962_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1962_upper : Scalar.QComplex := ((999995527024743764624101412985 : Int)/10^30,(-2990974841914105586321741250 : Int)/10^30)
theorem v1962_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 82 5) 1) 14) v1962_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1962 : Material (22 : Basis) (82 : Basis) where
  plus := ![v1962_pa,v1962_pb,v1962_pg]
  minus := ![(Primitive.Addresses.material1962 1).one,v1962_mb,v1962_mg]
  upper := v1962_upper
  lower := (Primitive.Addresses.material1962 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1962_pa_checked.trans (by decide +kernel)
    · exact v1962_pb_checked.trans (by decide +kernel)
    · exact v1962_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 82 Primitive.Addresses.material1962
    · exact v1962_mb_checked.trans (by decide +kernel)
    · exact v1962_mg_checked.trans (by decide +kernel)
  upper_error := v1962_upper_checked
  lower_error := reuse_lower_error 22 82 Primitive.Addresses.material1962

def v1963_pa : Scalar.QComplex := ((999999182542819136224011530885 : Int)/10^30,(-1278637436293537211552399219 : Int)/10^30)
theorem v1963_pa_checked : Scalar.distance (sourceCoefficient 22 83 1 0) v1963_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1963_pb : Scalar.QComplex := ((-551703226746629900654673 : Int)/10^30,(-431477102181615543972638092 : Int)/10^30)
theorem v1963_pb_checked : Scalar.distance (sourceCoefficient 22 83 1 1) v1963_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1963_pg : Scalar.QComplex := ((-93086346672138652391177 : Int)/10^30,(119023784959642514611 : Int)/10^30)
theorem v1963_pg_checked : Scalar.distance (sourceCoefficient 22 83 1 2) v1963_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1963_mb : Scalar.QComplex := ((-924048327497743594198397 : Int)/10^30,(-431476465427934032623213334 : Int)/10^30)
theorem v1963_mb_checked : Scalar.distance (sourceCoefficient 22 83 3 1) v1963_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1963_mg : Scalar.QComplex := ((-93086209299671742253588 : Int)/10^30,(199353065366280448895 : Int)/10^30)
theorem v1963_mg_checked : Scalar.distance (sourceCoefficient 22 83 3 2) v1963_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1963_upper : Scalar.QComplex := ((999995486349286933820107680675 : Int)/10^30,(-3004543401765000335606604796 : Int)/10^30)
theorem v1963_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 83 5) 1) 14) v1963_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1963 : Material (22 : Basis) (83 : Basis) where
  plus := ![v1963_pa,v1963_pb,v1963_pg]
  minus := ![(Primitive.Addresses.material1963 1).one,v1963_mb,v1963_mg]
  upper := v1963_upper
  lower := (Primitive.Addresses.material1963 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1963_pa_checked.trans (by decide +kernel)
    · exact v1963_pb_checked.trans (by decide +kernel)
    · exact v1963_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 83 Primitive.Addresses.material1963
    · exact v1963_mb_checked.trans (by decide +kernel)
    · exact v1963_mg_checked.trans (by decide +kernel)
  upper_error := v1963_upper_checked
  lower_error := reuse_lower_error 22 83 Primitive.Addresses.material1963

def v1964_pa : Scalar.QComplex := ((999999136995328985524434961972 : Int)/10^30,(-1313776463958724196352763198 : Int)/10^30)
theorem v1964_pa_checked : Scalar.distance (sourceCoefficient 22 84 1 0) v1964_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1964_pb : Scalar.QComplex := ((-566864918488547353480594 : Int)/10^30,(-431477077594597878834703031 : Int)/10^30)
theorem v1964_pb_checked : Scalar.distance (sourceCoefficient 22 84 1 1) v1964_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1964_pg : Scalar.QComplex := ((-93086341900025534800405 : Int)/10^30,(122294750645209422416 : Int)/10^30)
theorem v1964_pg_checked : Scalar.distance (sourceCoefficient 22 84 1 2) v1964_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1964_mb : Scalar.QComplex := ((-939209992376781401119259 : Int)/10^30,(-431476427757068406328078846 : Int)/10^30)
theorem v1964_mb_checked : Scalar.distance (sourceCoefficient 22 84 3 1) v1964_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1964_mg : Scalar.QComplex := ((-93086201704864333720130 : Int)/10^30,(202624025715798648961 : Int)/10^30)
theorem v1964_mg_checked : Scalar.distance (sourceCoefficient 22 84 3 2) v1964_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1964_upper : Scalar.QComplex := ((999995380155090658332145681108 : Int)/10^30,(-3039682298483897369178341579 : Int)/10^30)
theorem v1964_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 84 5) 1) 14) v1964_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1964 : Material (22 : Basis) (84 : Basis) where
  plus := ![v1964_pa,v1964_pb,v1964_pg]
  minus := ![(Primitive.Addresses.material1964 1).one,v1964_mb,v1964_mg]
  upper := v1964_upper
  lower := (Primitive.Addresses.material1964 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1964_pa_checked.trans (by decide +kernel)
    · exact v1964_pb_checked.trans (by decide +kernel)
    · exact v1964_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 84 Primitive.Addresses.material1964
    · exact v1964_mb_checked.trans (by decide +kernel)
    · exact v1964_mg_checked.trans (by decide +kernel)
  upper_error := v1964_upper_checked
  lower_error := reuse_lower_error 22 84 Primitive.Addresses.material1964

def v1965_pa : Scalar.QComplex := ((999999030007355524231845408429 : Int)/10^30,(-1392833208990152550666635039 : Int)/10^30)
theorem v1965_pa_checked : Scalar.distance (sourceCoefficient 22 85 1 0) v1965_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1965_pb : Scalar.QComplex := ((-600976104870397907786021 : Int)/10^30,(-431477019681145200129993578 : Int)/10^30)
theorem v1965_pb_checked : Scalar.distance (sourceCoefficient 22 85 1 1) v1965_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1965_pg : Scalar.QComplex := ((-93086330673372716339382 : Int)/10^30,(129653858428201191685 : Int)/10^30)
theorem v1965_pg_checked : Scalar.distance (sourceCoefficient 22 85 1 2) v1965_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1965_mb : Scalar.QComplex := ((-973321116080776970590881 : Int)/10^30,(-431476340407219754715649607 : Int)/10^30)
theorem v1965_mb_checked : Scalar.distance (sourceCoefficient 22 85 3 1) v1965_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1965_mg : Scalar.QComplex := ((-93086184127637120643982 : Int)/10^30,(209983121070562510123 : Int)/10^30)
theorem v1965_mg_checked : Scalar.distance (sourceCoefficient 22 85 3 2) v1965_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1965_upper : Scalar.QComplex := ((999995136722506590697878325181 : Int)/10^30,(-3118738741118054335746467788 : Int)/10^30)
theorem v1965_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 85 5) 1) 14) v1965_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1965 : Material (22 : Basis) (85 : Basis) where
  plus := ![v1965_pa,v1965_pb,v1965_pg]
  minus := ![(Primitive.Addresses.material1965 1).one,v1965_mb,v1965_mg]
  upper := v1965_upper
  lower := (Primitive.Addresses.material1965 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1965_pa_checked.trans (by decide +kernel)
    · exact v1965_pb_checked.trans (by decide +kernel)
    · exact v1965_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 85 Primitive.Addresses.material1965
    · exact v1965_mb_checked.trans (by decide +kernel)
    · exact v1965_mg_checked.trans (by decide +kernel)
  upper_error := v1965_upper_checked
  lower_error := reuse_lower_error 22 85 Primitive.Addresses.material1965

def v1966_pa : Scalar.QComplex := ((999999009587023061727104555670 : Int)/10^30,(-1407417838795103841267568045 : Int)/10^30)
theorem v1966_pa_checked : Scalar.distance (sourceCoefficient 22 86 1 0) v1966_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1966_pb : Scalar.QComplex := ((-607269040386695138099695 : Int)/10^30,(-431477008604240824823779534 : Int)/10^30)
theorem v1966_pb_checked : Scalar.distance (sourceCoefficient 22 86 1 1) v1966_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1966_pg : Scalar.QComplex := ((-93086328528085920317192 : Int)/10^30,(131011489073848612380 : Int)/10^30)
theorem v1966_pg_checked : Scalar.distance (sourceCoefficient 22 86 1 2) v1966_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1966_mb : Scalar.QComplex := ((-979614039695057116190516 : Int)/10^30,(-431476323899799576577151051 : Int)/10^30)
theorem v1966_mb_checked : Scalar.distance (sourceCoefficient 22 86 3 1) v1966_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1966_mg : Scalar.QComplex := ((-93086180810777021630842 : Int)/10^30,(211340749359416109821 : Int)/10^30)
theorem v1966_mg_checked : Scalar.distance (sourceCoefficient 22 86 3 2) v1966_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1966_upper : Scalar.QComplex := ((999995091130456605814030347739 : Int)/10^30,(-3133323313957271450643992895 : Int)/10^30)
theorem v1966_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 86 5) 1) 14) v1966_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1966 : Material (22 : Basis) (86 : Basis) where
  plus := ![v1966_pa,v1966_pb,v1966_pg]
  minus := ![(Primitive.Addresses.material1966 1).one,v1966_mb,v1966_mg]
  upper := v1966_upper
  lower := (Primitive.Addresses.material1966 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1966_pa_checked.trans (by decide +kernel)
    · exact v1966_pb_checked.trans (by decide +kernel)
    · exact v1966_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 86 Primitive.Addresses.material1966
    · exact v1966_mb_checked.trans (by decide +kernel)
    · exact v1966_mg_checked.trans (by decide +kernel)
  upper_error := v1966_upper_checked
  lower_error := reuse_lower_error 22 86 Primitive.Addresses.material1966

def v1967_pa : Scalar.QComplex := ((999999008227333877265744308432 : Int)/10^30,(-1408383594278365358148702432 : Int)/10^30)
theorem v1967_pa_checked : Scalar.distance (sourceCoefficient 22 87 1 0) v1967_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1967_pb : Scalar.QComplex := ((-607685741873516417169062 : Int)/10^30,(-431477007866437687765568915 : Int)/10^30)
theorem v1967_pb_checked : Scalar.distance (sourceCoefficient 22 87 1 1) v1967_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1967_pg : Scalar.QComplex := ((-93086328385215243004838 : Int)/10^30,(131101387772118552691 : Int)/10^30)
theorem v1967_pg_checked : Scalar.distance (sourceCoefficient 22 87 1 2) v1967_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1967_mb : Scalar.QComplex := ((-980030740390030509656094 : Int)/10^30,(-431476322802402098648286453 : Int)/10^30)
theorem v1967_mb_checked : Scalar.distance (sourceCoefficient 22 87 3 1) v1967_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1967_mg : Scalar.QComplex := ((-93086180590327869795880 : Int)/10^30,(211430647900921696329 : Int)/10^30)
theorem v1967_mg_checked : Scalar.distance (sourceCoefficient 22 87 3 2) v1967_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1967_upper : Scalar.QComplex := ((999995088103963094993660905063 : Int)/10^30,(-3134289065655453438474230032 : Int)/10^30)
theorem v1967_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 87 5) 1) 14) v1967_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1967 : Material (22 : Basis) (87 : Basis) where
  plus := ![v1967_pa,v1967_pb,v1967_pg]
  minus := ![(Primitive.Addresses.material1967 1).one,v1967_mb,v1967_mg]
  upper := v1967_upper
  lower := (Primitive.Addresses.material1967 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1967_pa_checked.trans (by decide +kernel)
    · exact v1967_pb_checked.trans (by decide +kernel)
    · exact v1967_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 87 Primitive.Addresses.material1967
    · exact v1967_mb_checked.trans (by decide +kernel)
    · exact v1967_mg_checked.trans (by decide +kernel)
  upper_error := v1967_upper_checked
  lower_error := reuse_lower_error 22 87 Primitive.Addresses.material1967

def v1968_pa : Scalar.QComplex := ((999998991596171287061359292727 : Int)/10^30,(-1420143176073312517362501902 : Int)/10^30)
theorem v1968_pa_checked : Scalar.distance (sourceCoefficient 22 88 1 0) v1968_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1968_pb : Scalar.QComplex := ((-612759733443750226197627 : Int)/10^30,(-431476998839486220529672077 : Int)/10^30)
theorem v1968_pb_checked : Scalar.distance (sourceCoefficient 22 88 1 1) v1968_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1968_pg : Scalar.QComplex := ((-93086326637415755973216 : Int)/10^30,(132196044866855189502 : Int)/10^30)
theorem v1968_pg_checked : Scalar.distance (sourceCoefficient 22 88 1 2) v1968_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1968_mb : Scalar.QComplex := ((-985104722281132806793445 : Int)/10^30,(-431476309396827791544305826 : Int)/10^30)
theorem v1968_mb_checked : Scalar.distance (sourceCoefficient 22 88 3 1) v1968_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1968_mg : Scalar.QComplex := ((-93086177897889262317556 : Int)/10^30,(212525303079795229128 : Int)/10^30)
theorem v1968_mg_checked : Scalar.distance (sourceCoefficient 22 88 3 2) v1968_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1968_upper : Scalar.QComplex := ((999995051176853917800413459766 : Int)/10^30,(-3146048601232007028219919767 : Int)/10^30)
theorem v1968_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 88 5) 1) 14) v1968_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1968 : Material (22 : Basis) (88 : Basis) where
  plus := ![v1968_pa,v1968_pb,v1968_pg]
  minus := ![(Primitive.Addresses.material1968 1).one,v1968_mb,v1968_mg]
  upper := v1968_upper
  lower := (Primitive.Addresses.material1968 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1968_pa_checked.trans (by decide +kernel)
    · exact v1968_pb_checked.trans (by decide +kernel)
    · exact v1968_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 88 Primitive.Addresses.material1968
    · exact v1968_mb_checked.trans (by decide +kernel)
    · exact v1968_mg_checked.trans (by decide +kernel)
  upper_error := v1968_upper_checked
  lower_error := reuse_lower_error 22 88 Primitive.Addresses.material1968

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
