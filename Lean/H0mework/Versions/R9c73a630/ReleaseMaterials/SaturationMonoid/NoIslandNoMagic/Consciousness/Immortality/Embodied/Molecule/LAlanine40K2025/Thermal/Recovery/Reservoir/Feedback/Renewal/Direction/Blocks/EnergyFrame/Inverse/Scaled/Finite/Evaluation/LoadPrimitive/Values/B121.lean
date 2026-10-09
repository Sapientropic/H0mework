import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B080
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B081

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1937_pa : Scalar.QComplex := ((999999672334937656470190170458 : Int)/10^30,(-809524562519672122561086761 : Int)/10^30)
theorem v1937_pa_checked : Scalar.distance (sourceCoefficient 22 57 1 0) v1937_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1937_pb : Scalar.QComplex := ((-349291637467427203428169 : Int)/10^30,(-431477362378702327559051753 : Int)/10^30)
theorem v1937_pb_checked : Scalar.distance (sourceCoefficient 22 57 1 1) v1937_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1937_pg : Scalar.QComplex := ((-93086397535938358089730 : Int)/10^30,(75355749933259284205 : Int)/10^30)
theorem v1937_pg_checked : Scalar.distance (sourceCoefficient 22 57 1 2) v1937_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1937_mb : Scalar.QComplex := ((-721637038123993304711516 : Int)/10^30,(-431476900297009201325620363 : Int)/10^30)
theorem v1937_mb_checked : Scalar.distance (sourceCoefficient 22 57 3 1) v1937_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1937_mg : Scalar.QComplex := ((-93086297847000001514705 : Int)/10^30,(155685090492670712121 : Int)/10^30)
theorem v1937_mg_checked : Scalar.distance (sourceCoefficient 22 57 3 2) v1937_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1937_upper : Scalar.QComplex := ((999996785786938512464782259545 : Int)/10^30,(-2535432072016417835706621664 : Int)/10^30)
theorem v1937_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 57 5) 1) 14) v1937_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1937 : Material (22 : Basis) (57 : Basis) where
  plus := ![v1937_pa,v1937_pb,v1937_pg]
  minus := ![(Primitive.Addresses.material1937 1).one,v1937_mb,v1937_mg]
  upper := v1937_upper
  lower := (Primitive.Addresses.material1937 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1937_pa_checked.trans (by decide +kernel)
    · exact v1937_pb_checked.trans (by decide +kernel)
    · exact v1937_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 57 Primitive.Addresses.material1937
    · exact v1937_mb_checked.trans (by decide +kernel)
    · exact v1937_mg_checked.trans (by decide +kernel)
  upper_error := v1937_upper_checked
  lower_error := reuse_lower_error 22 57 Primitive.Addresses.material1937

def v1938_pa : Scalar.QComplex := ((999999667141210668777379322466 : Int)/10^30,(-815915110699312644068319659 : Int)/10^30)
theorem v1938_pa_checked : Scalar.distance (sourceCoefficient 22 58 1 0) v1938_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1938_pb : Scalar.QComplex := ((-352049014874027648510914 : Int)/10^30,(-431477359684736318997372021 : Int)/10^30)
theorem v1938_pb_checked : Scalar.distance (sourceCoefficient 22 58 1 1) v1938_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1938_pg : Scalar.QComplex := ((-93086397003609149293139 : Int)/10^30,(75950623196632410041 : Int)/10^30)
theorem v1938_pg_checked : Scalar.distance (sourceCoefficient 22 58 1 2) v1938_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1938_mb : Scalar.QComplex := ((-724394412179124789280251 : Int)/10^30,(-431476895223551681622752178 : Int)/10^30)
theorem v1938_mb_checked : Scalar.distance (sourceCoefficient 22 58 3 1) v1938_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1938_mg : Scalar.QComplex := ((-93086296801322156734812 : Int)/10^30,(156279963075169202978 : Int)/10^30)
theorem v1938_mg_checked : Scalar.distance (sourceCoefficient 22 58 3 2) v1938_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1938_upper : Scalar.QComplex := ((999996769563712848160811178226 : Int)/10^30,(-2541822601714185920635274688 : Int)/10^30)
theorem v1938_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 58 5) 1) 14) v1938_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1938 : Material (22 : Basis) (58 : Basis) where
  plus := ![v1938_pa,v1938_pb,v1938_pg]
  minus := ![(Primitive.Addresses.material1938 1).one,v1938_mb,v1938_mg]
  upper := v1938_upper
  lower := (Primitive.Addresses.material1938 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1938_pa_checked.trans (by decide +kernel)
    · exact v1938_pb_checked.trans (by decide +kernel)
    · exact v1938_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 58 Primitive.Addresses.material1938
    · exact v1938_mb_checked.trans (by decide +kernel)
    · exact v1938_mg_checked.trans (by decide +kernel)
  upper_error := v1938_upper_checked
  lower_error := reuse_lower_error 22 58 Primitive.Addresses.material1938

def v1939_pa : Scalar.QComplex := ((999999652654624533611425097423 : Int)/10^30,(-833481031748153997495694755 : Int)/10^30)
theorem v1939_pa_checked : Scalar.distance (sourceCoefficient 22 59 1 0) v1939_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1939_pb : Scalar.QComplex := ((-359628313568417915233081 : Int)/10^30,(-431477352158689745418398463 : Int)/10^30)
theorem v1939_pb_checked : Scalar.distance (sourceCoefficient 22 59 1 1) v1939_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1939_pg : Scalar.QComplex := ((-93086395517526839634902 : Int)/10^30,(77585771926724088526 : Int)/10^30)
theorem v1939_pg_checked : Scalar.distance (sourceCoefficient 22 59 1 2) v1939_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1939_mb : Scalar.QComplex := ((-731973701556756528574735 : Int)/10^30,(-431476881156914496017430892 : Int)/10^30)
theorem v1939_mb_checked : Scalar.distance (sourceCoefficient 22 59 3 1) v1939_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1939_mg : Scalar.QComplex := ((-93086293904180690708814 : Int)/10^30,(157915109913998176688 : Int)/10^30)
theorem v1939_mg_checked : Scalar.distance (sourceCoefficient 22 59 3 2) v1939_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1939_upper : Scalar.QComplex := ((999996724759962126672296842172 : Int)/10^30,(-2559388471598117853380145040 : Int)/10^30)
theorem v1939_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 59 5) 1) 14) v1939_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1939 : Material (22 : Basis) (59 : Basis) where
  plus := ![v1939_pa,v1939_pb,v1939_pg]
  minus := ![(Primitive.Addresses.material1939 1).one,v1939_mb,v1939_mg]
  upper := v1939_upper
  lower := (Primitive.Addresses.material1939 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1939_pa_checked.trans (by decide +kernel)
    · exact v1939_pb_checked.trans (by decide +kernel)
    · exact v1939_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 59 Primitive.Addresses.material1939
    · exact v1939_mb_checked.trans (by decide +kernel)
    · exact v1939_mg_checked.trans (by decide +kernel)
  upper_error := v1939_upper_checked
  lower_error := reuse_lower_error 22 59 Primitive.Addresses.material1939

def v1940_pa : Scalar.QComplex := ((999999635559709722090481496643 : Int)/10^30,(-853744954737123971696359079 : Int)/10^30)
theorem v1940_pa_checked : Scalar.distance (sourceCoefficient 22 60 1 0) v1940_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1940_pb : Scalar.QComplex := ((-368371739137851297040341 : Int)/10^30,(-431477343256186861756207820 : Int)/10^30)
theorem v1940_pb_checked : Scalar.distance (sourceCoefficient 22 60 1 1) v1940_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1940_pg : Scalar.QComplex := ((-93086393761567031631089 : Int)/10^30,(79472067991434672452 : Int)/10^30)
theorem v1940_pg_checked : Scalar.distance (sourceCoefficient 22 60 1 2) v1940_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1940_mb : Scalar.QComplex := ((-740717116188153941838368 : Int)/10^30,(-431476864709232450012422282 : Int)/10^30)
theorem v1940_mb_checked : Scalar.distance (sourceCoefficient 22 60 3 1) v1940_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1940_mg : Scalar.QComplex := ((-93086290520432988304908 : Int)/10^30,(159801403761040298921 : Int)/10^30)
theorem v1940_mg_checked : Scalar.distance (sourceCoefficient 22 60 3 2) v1940_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1940_upper : Scalar.QComplex := ((999996672691380025790003133700 : Int)/10^30,(-2579652334902082776988088091 : Int)/10^30)
theorem v1940_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 60 5) 1) 14) v1940_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1940 : Material (22 : Basis) (60 : Basis) where
  plus := ![v1940_pa,v1940_pb,v1940_pg]
  minus := ![(Primitive.Addresses.material1940 1).one,v1940_mb,v1940_mg]
  upper := v1940_upper
  lower := (Primitive.Addresses.material1940 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1940_pa_checked.trans (by decide +kernel)
    · exact v1940_pb_checked.trans (by decide +kernel)
    · exact v1940_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 60 Primitive.Addresses.material1940
    · exact v1940_mb_checked.trans (by decide +kernel)
    · exact v1940_mg_checked.trans (by decide +kernel)
  upper_error := v1940_upper_checked
  lower_error := reuse_lower_error 22 60 Primitive.Addresses.material1940

def v1941_pa : Scalar.QComplex := ((999999630540165626769096979112 : Int)/10^30,(-859604288173280689193431990 : Int)/10^30)
theorem v1941_pa_checked : Scalar.distance (sourceCoefficient 22 61 1 0) v1941_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1941_pb : Scalar.QComplex := ((-370899909294638540045736 : Int)/10^30,(-431477340637989921294012584 : Int)/10^30)
theorem v1941_pb_checked : Scalar.distance (sourceCoefficient 22 61 1 1) v1941_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1941_pg : Scalar.QComplex := ((-93086393245518017359226 : Int)/10^30,(80017492367681076004 : Int)/10^30)
theorem v1941_pg_checked : Scalar.distance (sourceCoefficient 22 61 1 2) v1941_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1941_mb : Scalar.QComplex := ((-743245283144201851981720 : Int)/10^30,(-431476859909339503674225434 : Int)/10^30)
theorem v1941_mb_checked : Scalar.distance (sourceCoefficient 22 61 3 1) v1941_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1941_mg : Scalar.QComplex := ((-93086289533707494483042 : Int)/10^30,(160346827488873222739 : Int)/10^30)
theorem v1941_mg_checked : Scalar.distance (sourceCoefficient 22 61 3 2) v1941_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1941_upper : Scalar.QComplex := ((999996657559165450260468779979 : Int)/10^30,(-2585511650948172887943038148 : Int)/10^30)
theorem v1941_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 61 5) 1) 14) v1941_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1941 : Material (22 : Basis) (61 : Basis) where
  plus := ![v1941_pa,v1941_pb,v1941_pg]
  minus := ![(Primitive.Addresses.material1941 1).one,v1941_mb,v1941_mg]
  upper := v1941_upper
  lower := (Primitive.Addresses.material1941 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1941_pa_checked.trans (by decide +kernel)
    · exact v1941_pb_checked.trans (by decide +kernel)
    · exact v1941_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 61 Primitive.Addresses.material1941
    · exact v1941_mb_checked.trans (by decide +kernel)
    · exact v1941_mg_checked.trans (by decide +kernel)
  upper_error := v1941_upper_checked
  lower_error := reuse_lower_error 22 61 Primitive.Addresses.material1941

def v1942_pa : Scalar.QComplex := ((999999623185803413007181350019 : Int)/10^30,(-868117648239595972216478259 : Int)/10^30)
theorem v1942_pa_checked : Scalar.distance (sourceCoefficient 22 62 1 0) v1942_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1942_pb : Scalar.QComplex := ((-374573232034852675685948 : Int)/10^30,(-431477336798665048541948954 : Int)/10^30)
theorem v1942_pb_checked : Scalar.distance (sourceCoefficient 22 62 1 1) v1942_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1942_pg : Scalar.QComplex := ((-93086392489076742116640 : Int)/10^30,(80809970581069432491 : Int)/10^30)
theorem v1942_pg_checked : Scalar.distance (sourceCoefficient 22 62 1 2) v1942_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1942_mb : Scalar.QComplex := ((-746918601203505603885849 : Int)/10^30,(-431476852900103975988264766 : Int)/10^30)
theorem v1942_mb_checked : Scalar.distance (sourceCoefficient 22 62 3 1) v1942_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1942_mg : Scalar.QComplex := ((-93086288093393494637748 : Int)/10^30,(161139304754410970653 : Int)/10^30)
theorem v1942_mg_checked : Scalar.distance (sourceCoefficient 22 62 3 2) v1942_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1942_upper : Scalar.QComplex := ((999996635511527041489124537508 : Int)/10^30,(-2594024985641876403287729427 : Int)/10^30)
theorem v1942_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 62 5) 1) 14) v1942_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1942 : Material (22 : Basis) (62 : Basis) where
  plus := ![v1942_pa,v1942_pb,v1942_pg]
  minus := ![(Primitive.Addresses.material1942 1).one,v1942_mb,v1942_mg]
  upper := v1942_upper
  lower := (Primitive.Addresses.material1942 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1942_pa_checked.trans (by decide +kernel)
    · exact v1942_pb_checked.trans (by decide +kernel)
    · exact v1942_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 62 Primitive.Addresses.material1942
    · exact v1942_mb_checked.trans (by decide +kernel)
    · exact v1942_mg_checked.trans (by decide +kernel)
  upper_error := v1942_upper_checked
  lower_error := reuse_lower_error 22 62 Primitive.Addresses.material1942

def v1943_pa : Scalar.QComplex := ((999999601353275217986282458504 : Int)/10^30,(-892912812454170273149877748 : Int)/10^30)
theorem v1943_pa_checked : Scalar.distance (sourceCoefficient 22 63 1 0) v1943_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1943_pb : Scalar.QComplex := ((-385271785701756080447320 : Int)/10^30,(-431477325379061068729529639 : Int)/10^30)
theorem v1943_pb_checked : Scalar.distance (sourceCoefficient 22 63 1 1) v1943_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1943_pg : Scalar.QComplex := ((-93086390241095027875902 : Int)/10^30,(83118063646126433333 : Int)/10^30)
theorem v1943_pg_checked : Scalar.distance (sourceCoefficient 22 63 1 2) v1943_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1943_mb : Scalar.QComplex := ((-757617141032244615694664 : Int)/10^30,(-431476832248134278648901763 : Int)/10^30)
theorem v1943_mb_checked : Scalar.distance (sourceCoefficient 22 63 3 1) v1943_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1943_mg : Scalar.QComplex := ((-93086283853632254931895 : Int)/10^30,(163447395020152464260 : Int)/10^30)
theorem v1943_mg_checked : Scalar.distance (sourceCoefficient 22 63 3 2) v1943_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1943_upper : Scalar.QComplex := ((999996570884827328825299608160 : Int)/10^30,(-2618820075246003218083411481 : Int)/10^30)
theorem v1943_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 63 5) 1) 14) v1943_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1943 : Material (22 : Basis) (63 : Basis) where
  plus := ![v1943_pa,v1943_pb,v1943_pg]
  minus := ![(Primitive.Addresses.material1943 1).one,v1943_mb,v1943_mg]
  upper := v1943_upper
  lower := (Primitive.Addresses.material1943 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1943_pa_checked.trans (by decide +kernel)
    · exact v1943_pb_checked.trans (by decide +kernel)
    · exact v1943_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 63 Primitive.Addresses.material1943
    · exact v1943_mb_checked.trans (by decide +kernel)
    · exact v1943_mg_checked.trans (by decide +kernel)
  upper_error := v1943_upper_checked
  lower_error := reuse_lower_error 22 63 Primitive.Addresses.material1943

def v1944_pa : Scalar.QComplex := ((999999569082981649289563807150 : Int)/10^30,(-928350069215241760849621828 : Int)/10^30)
theorem v1944_pa_checked : Scalar.distance (sourceCoefficient 22 64 1 0) v1944_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1944_pb : Scalar.QComplex := ((-400562161768007987944711 : Int)/10^30,(-431477308444174456267090672 : Int)/10^30)
theorem v1944_pb_checked : Scalar.distance (sourceCoefficient 22 64 1 1) v1944_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1944_pg : Scalar.QComplex := ((-93086386912376008582631 : Int)/10^30,(86416790971566943256 : Int)/10^30)
theorem v1944_pg_checked : Scalar.distance (sourceCoefficient 22 64 1 2) v1944_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1944_mb : Scalar.QComplex := ((-772907496791146281443070 : Int)/10^30,(-431476802118348079617338942 : Int)/10^30)
theorem v1944_mb_checked : Scalar.distance (sourceCoefficient 22 64 3 1) v1944_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1944_mg : Scalar.QComplex := ((-93086277678261362381275 : Int)/10^30,(166746118244791437924 : Int)/10^30)
theorem v1944_mg_checked : Scalar.distance (sourceCoefficient 22 64 3 2) v1944_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1944_upper : Scalar.QComplex := ((999996477453091496151119245706 : Int)/10^30,(-2654257223531844351357093752 : Int)/10^30)
theorem v1944_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 64 5) 1) 14) v1944_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1944 : Material (22 : Basis) (64 : Basis) where
  plus := ![v1944_pa,v1944_pb,v1944_pg]
  minus := ![(Primitive.Addresses.material1944 1).one,v1944_mb,v1944_mg]
  upper := v1944_upper
  lower := (Primitive.Addresses.material1944 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1944_pa_checked.trans (by decide +kernel)
    · exact v1944_pb_checked.trans (by decide +kernel)
    · exact v1944_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 64 Primitive.Addresses.material1944
    · exact v1944_mb_checked.trans (by decide +kernel)
    · exact v1944_mg_checked.trans (by decide +kernel)
  upper_error := v1944_upper_checked
  lower_error := reuse_lower_error 22 64 Primitive.Addresses.material1944

def v1945_pa : Scalar.QComplex := ((999999535046569976527071862399 : Int)/10^30,(-964316671983458847469968124 : Int)/10^30)
theorem v1945_pa_checked : Scalar.distance (sourceCoefficient 22 65 1 0) v1945_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1945_pb : Scalar.QComplex := ((-416080938286619428108729 : Int)/10^30,(-431477290517587500587940916 : Int)/10^30)
theorem v1945_pb_checked : Scalar.distance (sourceCoefficient 22 65 1 1) v1945_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1945_pg : Scalar.QComplex := ((-93086383394482067787501 : Int)/10^30,(89764793178391738347 : Int)/10^30)
theorem v1945_pg_checked : Scalar.distance (sourceCoefficient 22 65 1 2) v1945_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1945_mb : Scalar.QComplex := ((-788426252061570821357720 : Int)/10^30,(-431476770799762603012660619 : Int)/10^30)
theorem v1945_mb_checked : Scalar.distance (sourceCoefficient 22 65 3 1) v1945_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1945_mg : Scalar.QComplex := ((-93086271271193615390904 : Int)/10^30,(170094116169217969310 : Int)/10^30)
theorem v1945_mg_checked : Scalar.distance (sourceCoefficient 22 65 3 2) v1945_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1945_upper : Scalar.QComplex := ((999996381341637003397956847023 : Int)/10^30,(-2690223713988272760623308079 : Int)/10^30)
theorem v1945_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 65 5) 1) 14) v1945_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1945 : Material (22 : Basis) (65 : Basis) where
  plus := ![v1945_pa,v1945_pb,v1945_pg]
  minus := ![(Primitive.Addresses.material1945 1).one,v1945_mb,v1945_mg]
  upper := v1945_upper
  lower := (Primitive.Addresses.material1945 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1945_pa_checked.trans (by decide +kernel)
    · exact v1945_pb_checked.trans (by decide +kernel)
    · exact v1945_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 65 Primitive.Addresses.material1945
    · exact v1945_mb_checked.trans (by decide +kernel)
    · exact v1945_mg_checked.trans (by decide +kernel)
  upper_error := v1945_upper_checked
  lower_error := reuse_lower_error 22 65 Primitive.Addresses.material1945

def v1946_pa : Scalar.QComplex := ((999999517931925186503577739506 : Int)/10^30,(-981904230175918984532359241 : Int)/10^30)
theorem v1946_pa_checked : Scalar.distance (sourceCoefficient 22 66 1 0) v1946_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1946_pb : Scalar.QComplex := ((-423669572148187723454628 : Int)/10^30,(-431477281480605981006108029 : Int)/10^30)
theorem v1946_pb_checked : Scalar.distance (sourceCoefficient 22 66 1 1) v1946_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1946_pg : Scalar.QComplex := ((-93086381623097834461391 : Int)/10^30,(91401955949454629832 : Int)/10^30)
theorem v1946_pg_checked : Scalar.distance (sourceCoefficient 22 66 1 2) v1946_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1946_mb : Scalar.QComplex := ((-796014875299035871480706 : Int)/10^30,(-431476755214135205160297056 : Int)/10^30)
theorem v1946_mb_checked : Scalar.distance (sourceCoefficient 22 66 3 1) v1946_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1946_mg : Scalar.QComplex := ((-93086268087012305278859 : Int)/10^30,(171731276802065525917 : Int)/10^30)
theorem v1946_mg_checked : Scalar.distance (sourceCoefficient 22 66 3 2) v1946_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1946_upper : Scalar.QComplex := ((999996333872487794256870727079 : Int)/10^30,(-2707811216447806670595102996 : Int)/10^30)
theorem v1946_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 66 5) 1) 14) v1946_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1946 : Material (22 : Basis) (66 : Basis) where
  plus := ![v1946_pa,v1946_pb,v1946_pg]
  minus := ![(Primitive.Addresses.material1946 1).one,v1946_mb,v1946_mg]
  upper := v1946_upper
  lower := (Primitive.Addresses.material1946 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1946_pa_checked.trans (by decide +kernel)
    · exact v1946_pb_checked.trans (by decide +kernel)
    · exact v1946_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 66 Primitive.Addresses.material1946
    · exact v1946_mb_checked.trans (by decide +kernel)
    · exact v1946_mg_checked.trans (by decide +kernel)
  upper_error := v1946_upper_checked
  lower_error := reuse_lower_error 22 66 Primitive.Addresses.material1946

def v1947_pa : Scalar.QComplex := ((999999488513274826201718554636 : Int)/10^30,(-1011421370512273946521245752 : Int)/10^30)
theorem v1947_pa_checked : Scalar.distance (sourceCoefficient 22 67 1 0) v1947_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1947_pb : Scalar.QComplex := ((-436405550851191745668002 : Int)/10^30,(-431477265913919864359320347 : Int)/10^30)
theorem v1947_pb_checked : Scalar.distance (sourceCoefficient 22 67 1 1) v1947_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1947_pg : Scalar.QComplex := ((-93086378574690403292718 : Int)/10^30,(94149600750308705740 : Int)/10^30)
theorem v1947_pg_checked : Scalar.distance (sourceCoefficient 22 67 1 2) v1947_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1947_mb : Scalar.QComplex := ((-808750835826503938435013 : Int)/10^30,(-431476728656878871197195734 : Int)/10^30)
theorem v1947_mb_checked : Scalar.distance (sourceCoefficient 22 67 3 1) v1947_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1947_mg : Scalar.QComplex := ((-93086262667512295362563 : Int)/10^30,(174478917949207550971 : Int)/10^30)
theorem v1947_mg_checked : Scalar.distance (sourceCoefficient 22 67 3 2) v1947_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1947_upper : Scalar.QComplex := ((999996253509974803083992534183 : Int)/10^30,(-2737328262047926745685460622 : Int)/10^30)
theorem v1947_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 67 5) 1) 14) v1947_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1947 : Material (22 : Basis) (67 : Basis) where
  plus := ![v1947_pa,v1947_pb,v1947_pg]
  minus := ![(Primitive.Addresses.material1947 1).one,v1947_mb,v1947_mg]
  upper := v1947_upper
  lower := (Primitive.Addresses.material1947 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1947_pa_checked.trans (by decide +kernel)
    · exact v1947_pb_checked.trans (by decide +kernel)
    · exact v1947_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 67 Primitive.Addresses.material1947
    · exact v1947_mb_checked.trans (by decide +kernel)
    · exact v1947_mg_checked.trans (by decide +kernel)
  upper_error := v1947_upper_checked
  lower_error := reuse_lower_error 22 67 Primitive.Addresses.material1947

def v1948_pa : Scalar.QComplex := ((999999437585587210502400333823 : Int)/10^30,(-1060579327192937268585722595 : Int)/10^30)
theorem v1948_pa_checked : Scalar.distance (sourceCoefficient 22 68 1 0) v1948_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1948_pb : Scalar.QComplex := ((-457616097076705746574152 : Int)/10^30,(-431477238876606149641834569 : Int)/10^30)
theorem v1948_pb_checked : Scalar.distance (sourceCoefficient 22 68 1 1) v1948_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1948_pg : Scalar.QComplex := ((-93086373287853677723322 : Int)/10^30,(98725538677128323823 : Int)/10^30)
theorem v1948_pg_checked : Scalar.distance (sourceCoefficient 22 68 1 2) v1948_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1948_mb : Scalar.QComplex := ((-829961350822378189336752 : Int)/10^30,(-431476683315829118628746205 : Int)/10^30)
theorem v1948_mb_checked : Scalar.distance (sourceCoefficient 22 68 3 1) v1948_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1948_mg : Scalar.QComplex := ((-93086253431849200072477 : Int)/10^30,(179054849609894364325 : Int)/10^30)
theorem v1948_mg_checked : Scalar.distance (sourceCoefficient 22 68 3 2) v1948_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1948_upper : Scalar.QComplex := ((999996117740189382361879271753 : Int)/10^30,(-2786486057617019390163123726 : Int)/10^30)
theorem v1948_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 68 5) 1) 14) v1948_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1948 : Material (22 : Basis) (68 : Basis) where
  plus := ![v1948_pa,v1948_pb,v1948_pg]
  minus := ![(Primitive.Addresses.material1948 1).one,v1948_mb,v1948_mg]
  upper := v1948_upper
  lower := (Primitive.Addresses.material1948 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1948_pa_checked.trans (by decide +kernel)
    · exact v1948_pb_checked.trans (by decide +kernel)
    · exact v1948_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 68 Primitive.Addresses.material1948
    · exact v1948_mb_checked.trans (by decide +kernel)
    · exact v1948_mg_checked.trans (by decide +kernel)
  upper_error := v1948_upper_checked
  lower_error := reuse_lower_error 22 68 Primitive.Addresses.material1948

def v1949_pa : Scalar.QComplex := ((999999414405497339078509135536 : Int)/10^30,(-1082214702543317619215704793 : Int)/10^30)
theorem v1949_pa_checked : Scalar.distance (sourceCoefficient 22 69 1 0) v1949_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1949_pb : Scalar.QComplex := ((-466951271814379502222576 : Int)/10^30,(-431477226536377748940157997 : Int)/10^30)
theorem v1949_pb_checked : Scalar.distance (sourceCoefficient 22 69 1 1) v1949_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1949_pg : Scalar.QComplex := ((-93086370877844918226121 : Int)/10^30,(100739498162900207001 : Int)/10^30)
theorem v1949_pg_checked : Scalar.distance (sourceCoefficient 22 69 1 2) v1949_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1949_mb : Scalar.QComplex := ((-839296511435078425037329 : Int)/10^30,(-431476662919769954808322179 : Int)/10^30)
theorem v1949_mb_checked : Scalar.distance (sourceCoefficient 22 69 3 1) v1949_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1949_mg : Scalar.QComplex := ((-93086249283885007078643 : Int)/10^30,(181068806266048071775 : Int)/10^30)
theorem v1949_mg_checked : Scalar.distance (sourceCoefficient 22 69 3 2) v1949_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1949_upper : Scalar.QComplex := ((999996057219438926122098524345 : Int)/10^30,(-2808121360737317389367431680 : Int)/10^30)
theorem v1949_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 69 5) 1) 14) v1949_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1949 : Material (22 : Basis) (69 : Basis) where
  plus := ![v1949_pa,v1949_pb,v1949_pg]
  minus := ![(Primitive.Addresses.material1949 1).one,v1949_mb,v1949_mg]
  upper := v1949_upper
  lower := (Primitive.Addresses.material1949 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1949_pa_checked.trans (by decide +kernel)
    · exact v1949_pb_checked.trans (by decide +kernel)
    · exact v1949_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 69 Primitive.Addresses.material1949
    · exact v1949_mb_checked.trans (by decide +kernel)
    · exact v1949_mg_checked.trans (by decide +kernel)
  upper_error := v1949_upper_checked
  lower_error := reuse_lower_error 22 69 Primitive.Addresses.material1949

def v1950_pa : Scalar.QComplex := ((999999398902179939132674354074 : Int)/10^30,(-1096446660263574048050612712 : Int)/10^30)
theorem v1950_pa_checked : Scalar.distance (sourceCoefficient 22 70 1 0) v1950_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1950_pb : Scalar.QComplex := ((-473092039328768615692411 : Int)/10^30,(-431477218272021449687220803 : Int)/10^30)
theorem v1950_pb_checked : Scalar.distance (sourceCoefficient 22 70 1 1) v1950_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1950_pg : Scalar.QComplex := ((-93086369264799648635141 : Int)/10^30,(102064300047079645818 : Int)/10^30)
theorem v1950_pg_checked : Scalar.distance (sourceCoefficient 22 70 1 2) v1950_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1950_mb : Scalar.QComplex := ((-845437269531211872495695 : Int)/10^30,(-431476649356210937737220741 : Int)/10^30)
theorem v1950_mb_checked : Scalar.distance (sourceCoefficient 22 70 3 1) v1950_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1950_mg : Scalar.QComplex := ((-93086246527595978913207 : Int)/10^30,(182393606264957803880 : Int)/10^30)
theorem v1950_mg_checked : Scalar.distance (sourceCoefficient 22 70 3 2) v1950_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1950_upper : Scalar.QComplex := ((999996017153076704502546664910 : Int)/10^30,(-2822353270503425214733407178 : Int)/10^30)
theorem v1950_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 70 5) 1) 14) v1950_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1950 : Material (22 : Basis) (70 : Basis) where
  plus := ![v1950_pa,v1950_pb,v1950_pg]
  minus := ![(Primitive.Addresses.material1950 1).one,v1950_mb,v1950_mg]
  upper := v1950_upper
  lower := (Primitive.Addresses.material1950 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1950_pa_checked.trans (by decide +kernel)
    · exact v1950_pb_checked.trans (by decide +kernel)
    · exact v1950_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 70 Primitive.Addresses.material1950
    · exact v1950_mb_checked.trans (by decide +kernel)
    · exact v1950_mg_checked.trans (by decide +kernel)
  upper_error := v1950_upper_checked
  lower_error := reuse_lower_error 22 70 Primitive.Addresses.material1950

def v1951_pa : Scalar.QComplex := ((999999371971332124287389505081 : Int)/10^30,(-1120739461842678914799803618 : Int)/10^30)
theorem v1951_pa_checked : Scalar.distance (sourceCoefficient 22 71 1 0) v1951_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1951_pb : Scalar.QComplex := ((-483573832990271490367119 : Int)/10^30,(-431477203896227042900973341 : Int)/10^30)
theorem v1951_pb_checked : Scalar.distance (sourceCoefficient 22 71 1 1) v1951_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1951_pg : Scalar.QComplex := ((-93086366460643301206667 : Int)/10^30,(104325629771478060055 : Int)/10^30)
theorem v1951_pg_checked : Scalar.distance (sourceCoefficient 22 71 1 2) v1951_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1951_mb : Scalar.QComplex := ((-855919046884200814046055 : Int)/10^30,(-431476625935106036301245695 : Int)/10^30)
theorem v1951_mb_checked : Scalar.distance (sourceCoefficient 22 71 3 1) v1951_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1951_mg : Scalar.QComplex := ((-93086241772014969954532 : Int)/10^30,(184654932727499180532 : Int)/10^30)
theorem v1951_mg_checked : Scalar.distance (sourceCoefficient 22 71 3 2) v1951_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1951_upper : Scalar.QComplex := ((999995948295097300200476841725 : Int)/10^30,(-2846645989421055581342141604 : Int)/10^30)
theorem v1951_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 71 5) 1) 14) v1951_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1951 : Material (22 : Basis) (71 : Basis) where
  plus := ![v1951_pa,v1951_pb,v1951_pg]
  minus := ![(Primitive.Addresses.material1951 1).one,v1951_mb,v1951_mg]
  upper := v1951_upper
  lower := (Primitive.Addresses.material1951 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1951_pa_checked.trans (by decide +kernel)
    · exact v1951_pb_checked.trans (by decide +kernel)
    · exact v1951_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 71 Primitive.Addresses.material1951
    · exact v1951_mb_checked.trans (by decide +kernel)
    · exact v1951_mg_checked.trans (by decide +kernel)
  upper_error := v1951_upper_checked
  lower_error := reuse_lower_error 22 71 Primitive.Addresses.material1951

def v1952_pa : Scalar.QComplex := ((999999342078202847448685197910 : Int)/10^30,(-1147102071066045744309766097 : Int)/10^30)
theorem v1952_pa_checked : Scalar.distance (sourceCoefficient 22 72 1 0) v1952_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1952_pb : Scalar.QComplex := ((-494948701508512102136878 : Int)/10^30,(-431477187911445829223521247 : Int)/10^30)
theorem v1952_pb_checked : Scalar.distance (sourceCoefficient 22 72 1 1) v1952_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1952_pg : Scalar.QComplex := ((-93086363345052432327812 : Int)/10^30,(106779630433762445145 : Int)/10^30)
theorem v1952_pg_checked : Scalar.distance (sourceCoefficient 22 72 1 2) v1952_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1952_mb : Scalar.QComplex := ((-867293897372911759719332 : Int)/10^30,(-431476600134331548307135869 : Int)/10^30)
theorem v1952_mb_checked : Scalar.distance (sourceCoefficient 22 72 3 1) v1952_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1952_mg : Scalar.QComplex := ((-93086236538733213688105 : Int)/10^30,(187108929787432366844 : Int)/10^30)
theorem v1952_mg_checked : Scalar.distance (sourceCoefficient 22 72 3 2) v1952_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1952_upper : Scalar.QComplex := ((999995872902540623361800567625 : Int)/10^30,(-2873008507787583493943108730 : Int)/10^30)
theorem v1952_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 72 5) 1) 14) v1952_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1952 : Material (22 : Basis) (72 : Basis) where
  plus := ![v1952_pa,v1952_pb,v1952_pg]
  minus := ![(Primitive.Addresses.material1952 1).one,v1952_mb,v1952_mg]
  upper := v1952_upper
  lower := (Primitive.Addresses.material1952 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1952_pa_checked.trans (by decide +kernel)
    · exact v1952_pb_checked.trans (by decide +kernel)
    · exact v1952_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 72 Primitive.Addresses.material1952
    · exact v1952_mb_checked.trans (by decide +kernel)
    · exact v1952_mg_checked.trans (by decide +kernel)
  upper_error := v1952_upper_checked
  lower_error := reuse_lower_error 22 72 Primitive.Addresses.material1952

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
