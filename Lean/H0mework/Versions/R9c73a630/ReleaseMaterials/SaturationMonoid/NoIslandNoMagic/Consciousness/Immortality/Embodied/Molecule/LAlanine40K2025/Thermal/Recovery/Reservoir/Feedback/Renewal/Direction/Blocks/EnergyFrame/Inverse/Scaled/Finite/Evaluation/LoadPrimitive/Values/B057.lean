import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B038

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v913_pa : Scalar.QComplex := ((999999336100956960528941568992 : Int)/10^30,(-1152301022006403831921850790 : Int)/10^30)
theorem v913_pa_checked : Scalar.distance (sourceCoefficient 9 86 1 0) v913_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v913_pb : Scalar.QComplex := ((-497191839036725424259904 : Int)/10^30,(-431477104902521013198617743 : Int)/10^30)
theorem v913_pb_checked : Scalar.distance (sourceCoefficient 9 86 1 1) v913_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v913_pg : Scalar.QComplex := ((-93086354112730221458270 : Int)/10^30,(107263572191131977450 : Int)/10^30)
theorem v913_pg_checked : Scalar.distance (sourceCoefficient 9 86 1 2) v913_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v913_mb : Scalar.QComplex := ((-869536962432938930600574 : Int)/10^30,(-431476515189710980614505772 : Int)/10^30)
theorem v913_mb_checked : Scalar.distance (sourceCoefficient 9 86 3 1) v913_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v913_mg : Scalar.QComplex := ((-93086226888794499751803 : Int)/10^30,(187592863397530006026 : Int)/10^30)
theorem v913_mg_checked : Scalar.distance (sourceCoefficient 9 86 3 2) v913_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v913_upper : Scalar.QComplex := ((999995857952385960934629263628 : Int)/10^30,(-2878207440668530718256979408 : Int)/10^30)
theorem v913_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 86 5) 1) 14) v913_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material913 : Material (9 : Basis) (86 : Basis) where
  plus := ![v913_pa,v913_pb,v913_pg]
  minus := ![(Primitive.Addresses.material913 1).one,v913_mb,v913_mg]
  upper := v913_upper
  lower := (Primitive.Addresses.material913 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v913_pa_checked.trans (by decide +kernel)
    · exact v913_pb_checked.trans (by decide +kernel)
    · exact v913_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 86 Primitive.Addresses.material913
    · exact v913_mb_checked.trans (by decide +kernel)
    · exact v913_mg_checked.trans (by decide +kernel)
  upper_error := v913_upper_checked
  lower_error := reuse_lower_error 9 86 Primitive.Addresses.material913

def v914_pa : Scalar.QComplex := ((999999334987648484787319234035 : Int)/10^30,(-1153266777805117255229369494 : Int)/10^30)
theorem v914_pa_checked : Scalar.distance (sourceCoefficient 9 87 1 0) v914_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v914_pb : Scalar.QComplex := ((-497608540614286960455310 : Int)/10^30,(-431477104235589690136932721 : Int)/10^30)
theorem v914_pb_checked : Scalar.distance (sourceCoefficient 9 87 1 1) v914_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v914_pg : Scalar.QComplex := ((-93086353988971792908530 : Int)/10^30,(107353470913872158729 : Int)/10^30)
theorem v914_pg_checked : Scalar.distance (sourceCoefficient 9 87 1 2) v914_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v914_mb : Scalar.QComplex := ((-869953663279811730936435 : Int)/10^30,(-431476514163185211988596308 : Int)/10^30)
theorem v914_mb_checked : Scalar.distance (sourceCoefficient 9 87 3 1) v914_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v914_mg : Scalar.QComplex := ((-93086226687457568446376 : Int)/10^30,(187682761979998834288 : Int)/10^30)
theorem v914_mg_checked : Scalar.distance (sourceCoefficient 9 87 3 2) v914_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v914_upper : Scalar.QComplex := ((999995855172272247437501087752 : Int)/10^30,(-2879173193107394894452014611 : Int)/10^30)
theorem v914_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 87 5) 1) 14) v914_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material914 : Material (9 : Basis) (87 : Basis) where
  plus := ![v914_pa,v914_pb,v914_pg]
  minus := ![(Primitive.Addresses.material914 1).one,v914_mb,v914_mg]
  upper := v914_upper
  lower := (Primitive.Addresses.material914 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v914_pa_checked.trans (by decide +kernel)
    · exact v914_pb_checked.trans (by decide +kernel)
    · exact v914_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 87 Primitive.Addresses.material914
    · exact v914_mb_checked.trans (by decide +kernel)
    · exact v914_mg_checked.trans (by decide +kernel)
  upper_error := v914_upper_checked
  lower_error := reuse_lower_error 9 87 Primitive.Addresses.material914

def v915_pa : Scalar.QComplex := ((999999321356555942804197219006 : Int)/10^30,(-1165026363460272706523245974 : Int)/10^30)
theorem v915_pa_checked : Scalar.distance (sourceCoefficient 9 88 1 0) v915_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v915_pb : Scalar.QComplex := ((-502682533294916000272670 : Int)/10^30,(-431477096071613279710138825 : Int)/10^30)
theorem v915_pb_checked : Scalar.distance (sourceCoefficient 9 88 1 1) v915_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v915_pg : Scalar.QComplex := ((-93086352473893793331921 : Int)/10^30,(108448128308052942421 : Int)/10^30)
theorem v915_pg_checked : Scalar.distance (sourceCoefficient 9 88 1 2) v915_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v915_mb : Scalar.QComplex := ((-875027647026017452484196 : Int)/10^30,(-431476501620584682147591238 : Int)/10^30)
theorem v915_mb_checked : Scalar.distance (sourceCoefficient 9 88 3 1) v915_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v915_mg : Scalar.QComplex := ((-93086224227740103363407 : Int)/10^30,(188777417659144564758 : Int)/10^30)
theorem v915_mg_checked : Scalar.distance (sourceCoefficient 9 88 3 2) v915_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v915_upper : Scalar.QComplex := ((999995821245221987844276031553 : Int)/10^30,(-2890932737721999765952137810 : Int)/10^30)
theorem v915_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 88 5) 1) 14) v915_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material915 : Material (9 : Basis) (88 : Basis) where
  plus := ![v915_pa,v915_pb,v915_pg]
  minus := ![(Primitive.Addresses.material915 1).one,v915_mb,v915_mg]
  upper := v915_upper
  lower := (Primitive.Addresses.material915 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v915_pa_checked.trans (by decide +kernel)
    · exact v915_pb_checked.trans (by decide +kernel)
    · exact v915_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 88 Primitive.Addresses.material915
    · exact v915_mb_checked.trans (by decide +kernel)
    · exact v915_mg_checked.trans (by decide +kernel)
  upper_error := v915_upper_checked
  lower_error := reuse_lower_error 9 88 Primitive.Addresses.material915

def v916_pa : Scalar.QComplex := ((999999302482446626380041997851 : Int)/10^30,(-1181115836917151260192892898 : Int)/10^30)
theorem v916_pa_checked : Scalar.distance (sourceCoefficient 9 89 1 0) v916_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v916_pb : Scalar.QComplex := ((-509624773564181928611044 : Int)/10^30,(-431477084772764812454934222 : Int)/10^30)
theorem v916_pb_checked : Scalar.distance (sourceCoefficient 9 89 1 1) v916_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v916_pg : Scalar.QComplex := ((-93086350376632210104415 : Int)/10^30,(109945839319811977221 : Int)/10^30)
theorem v916_pg_checked : Scalar.distance (sourceCoefficient 9 89 1 2) v916_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v916_mb : Scalar.QComplex := ((-881969874959972706523968 : Int)/10^30,(-431476484330899736488544740 : Int)/10^30)
theorem v916_mb_checked : Scalar.distance (sourceCoefficient 9 89 3 1) v916_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v916_mg : Scalar.QComplex := ((-93086220838022152294135 : Int)/10^30,(190275126303395051935 : Int)/10^30)
theorem v916_mg_checked : Scalar.distance (sourceCoefficient 9 89 3 2) v916_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v916_upper : Scalar.QComplex := ((999995774602169221246493688957 : Int)/10^30,(-2907022154640497173592609334 : Int)/10^30)
theorem v916_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 89 5) 1) 14) v916_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material916 : Material (9 : Basis) (89 : Basis) where
  plus := ![v916_pa,v916_pb,v916_pg]
  minus := ![(Primitive.Addresses.material916 1).one,v916_mb,v916_mg]
  upper := v916_upper
  lower := (Primitive.Addresses.material916 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v916_pa_checked.trans (by decide +kernel)
    · exact v916_pb_checked.trans (by decide +kernel)
    · exact v916_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 89 Primitive.Addresses.material916
    · exact v916_mb_checked.trans (by decide +kernel)
    · exact v916_mg_checked.trans (by decide +kernel)
  upper_error := v916_upper_checked
  lower_error := reuse_lower_error 9 89 Primitive.Addresses.material916

def v917_pa : Scalar.QComplex := ((999999271190440399207387507008 : Int)/10^30,(-1207318759913143675278085442 : Int)/10^30)
theorem v917_pa_checked : Scalar.distance (sourceCoefficient 9 90 1 0) v917_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v917_pb : Scalar.QComplex := ((-520930735977327677341842 : Int)/10^30,(-431477066052965100408147891 : Int)/10^30)
theorem v917_pb_checked : Scalar.distance (sourceCoefficient 9 90 1 1) v917_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v917_pg : Scalar.QComplex := ((-93086346900908320041784 : Int)/10^30,(112384974812493336692 : Int)/10^30)
theorem v917_pg_checked : Scalar.distance (sourceCoefficient 9 90 1 2) v917_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v917_mb : Scalar.QComplex := ((-893275817009047897817426 : Int)/10^30,(-431476455854570633778581678 : Int)/10^30)
theorem v917_mb_checked : Scalar.distance (sourceCoefficient 9 90 3 1) v917_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v917_mg : Scalar.QComplex := ((-93086215257435480802940 : Int)/10^30,(192714257888481617151 : Int)/10^30)
theorem v917_mg_checked : Scalar.distance (sourceCoefficient 9 90 3 2) v917_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v917_upper : Scalar.QComplex := ((999995698086341619363616290222 : Int)/10^30,(-2933224984603149838230255269 : Int)/10^30)
theorem v917_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 90 5) 1) 14) v917_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material917 : Material (9 : Basis) (90 : Basis) where
  plus := ![v917_pa,v917_pb,v917_pg]
  minus := ![(Primitive.Addresses.material917 1).one,v917_mb,v917_mg]
  upper := v917_upper
  lower := (Primitive.Addresses.material917 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v917_pa_checked.trans (by decide +kernel)
    · exact v917_pb_checked.trans (by decide +kernel)
    · exact v917_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 90 Primitive.Addresses.material917
    · exact v917_mb_checked.trans (by decide +kernel)
    · exact v917_mg_checked.trans (by decide +kernel)
  upper_error := v917_upper_checked
  lower_error := reuse_lower_error 9 90 Primitive.Addresses.material917

def v918_pa : Scalar.QComplex := ((999999253260177950832508591817 : Int)/10^30,(-1222079820010940671941508436 : Int)/10^30)
theorem v918_pa_checked : Scalar.distance (sourceCoefficient 9 91 1 0) v918_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v918_pb : Scalar.QComplex := ((-527299795876552552380939 : Int)/10^30,(-431477055333485634390928894 : Int)/10^30)
theorem v918_pb_checked : Scalar.distance (sourceCoefficient 9 91 1 1) v918_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v918_pg : Scalar.QComplex := ((-93086344910072582222505 : Int)/10^30,(113759028581574604122 : Int)/10^30)
theorem v918_pg_checked : Scalar.distance (sourceCoefficient 9 91 1 2) v918_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v918_mb : Scalar.QComplex := ((-899644865286352700218421 : Int)/10^30,(-431476439638883317891826522 : Int)/10^30)
theorem v918_mb_checked : Scalar.distance (sourceCoefficient 9 91 3 1) v918_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v918_mg : Scalar.QComplex := ((-93086212080853966630135 : Int)/10^30,(194088309427938291168 : Int)/10^30)
theorem v918_mg_checked : Scalar.distance (sourceCoefficient 9 91 3 2) v918_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v918_upper : Scalar.QComplex := ((999995654679855260122297544621 : Int)/10^30,(-2947985991770075409955711132 : Int)/10^30)
theorem v918_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 91 5) 1) 14) v918_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material918 : Material (9 : Basis) (91 : Basis) where
  plus := ![v918_pa,v918_pb,v918_pg]
  minus := ![(Primitive.Addresses.material918 1).one,v918_mb,v918_mg]
  upper := v918_upper
  lower := (Primitive.Addresses.material918 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v918_pa_checked.trans (by decide +kernel)
    · exact v918_pb_checked.trans (by decide +kernel)
    · exact v918_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 91 Primitive.Addresses.material918
    · exact v918_mb_checked.trans (by decide +kernel)
    · exact v918_mg_checked.trans (by decide +kernel)
  upper_error := v918_upper_checked
  lower_error := reuse_lower_error 9 91 Primitive.Addresses.material918

def v919_pa : Scalar.QComplex := ((999999213696671421724683296533 : Int)/10^30,(-1254035900157418180814025262 : Int)/10^30)
theorem v919_pa_checked : Scalar.distance (sourceCoefficient 9 92 1 0) v919_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v919_pb : Scalar.QComplex := ((-541088113301473378059843 : Int)/10^30,(-431477031697550688604284938 : Int)/10^30)
theorem v919_pb_checked : Scalar.distance (sourceCoefficient 9 92 1 1) v919_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v919_pg : Scalar.QComplex := ((-93086340519065979241607 : Int)/10^30,(116733704613287349522 : Int)/10^30)
theorem v919_pg_checked : Scalar.distance (sourceCoefficient 9 92 1 2) v919_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v919_mb : Scalar.QComplex := ((-913433157180505456141716 : Int)/10^30,(-431476404104260237901418141 : Int)/10^30)
theorem v919_mb_checked : Scalar.distance (sourceCoefficient 9 92 3 1) v919_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v919_mg : Scalar.QComplex := ((-93086205122837557688678 : Int)/10^30,(197062980562802265773 : Int)/10^30)
theorem v919_mg_checked : Scalar.distance (sourceCoefficient 9 92 3 2) v919_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v919_upper : Scalar.QComplex := ((999995559963112356334696948941 : Int)/10^30,(-2979941956038702269550929627 : Int)/10^30)
theorem v919_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 92 5) 1) 14) v919_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material919 : Material (9 : Basis) (92 : Basis) where
  plus := ![v919_pa,v919_pb,v919_pg]
  minus := ![(Primitive.Addresses.material919 1).one,v919_mb,v919_mg]
  upper := v919_upper
  lower := (Primitive.Addresses.material919 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v919_pa_checked.trans (by decide +kernel)
    · exact v919_pb_checked.trans (by decide +kernel)
    · exact v919_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 92 Primitive.Addresses.material919
    · exact v919_mb_checked.trans (by decide +kernel)
    · exact v919_mg_checked.trans (by decide +kernel)
  upper_error := v919_upper_checked
  lower_error := reuse_lower_error 9 92 Primitive.Addresses.material919

def v920_pa : Scalar.QComplex := ((999999165417417380070235370010 : Int)/10^30,(-1291961481125413551587285950 : Int)/10^30)
theorem v920_pa_checked : Scalar.distance (sourceCoefficient 9 93 1 0) v920_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v920_pb : Scalar.QComplex := ((-557452132957382668047882 : Int)/10^30,(-431477002883980558958376118 : Int)/10^30)
theorem v920_pb_checked : Scalar.distance (sourceCoefficient 9 93 1 1) v920_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v920_pg : Scalar.QComplex := ((-93086335163892130031195 : Int)/10^30,(120264059821168383845 : Int)/10^30)
theorem v920_pg_checked : Scalar.distance (sourceCoefficient 9 93 1 2) v920_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v920_mb : Scalar.QComplex := ((-929797145878529048731567 : Int)/10^30,(-431476361169288881901072506 : Int)/10^30)
theorem v920_mb_checked : Scalar.distance (sourceCoefficient 9 93 3 1) v920_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v920_mg : Scalar.QComplex := ((-93086196721128159349059 : Int)/10^30,(200593329834896867207 : Int)/10^30)
theorem v920_mg_checked : Scalar.distance (sourceCoefficient 9 93 3 2) v920_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v920_upper : Scalar.QComplex := ((999995446227818052026920768916 : Int)/10^30,(-3017867397195387224003394068 : Int)/10^30)
theorem v920_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 93 5) 1) 14) v920_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material920 : Material (9 : Basis) (93 : Basis) where
  plus := ![v920_pa,v920_pb,v920_pg]
  minus := ![(Primitive.Addresses.material920 1).one,v920_mb,v920_mg]
  upper := v920_upper
  lower := (Primitive.Addresses.material920 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v920_pa_checked.trans (by decide +kernel)
    · exact v920_pb_checked.trans (by decide +kernel)
    · exact v920_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 93 Primitive.Addresses.material920
    · exact v920_mb_checked.trans (by decide +kernel)
    · exact v920_mg_checked.trans (by decide +kernel)
  upper_error := v920_upper_checked
  lower_error := reuse_lower_error 9 93 Primitive.Addresses.material920

def v921_pa : Scalar.QComplex := ((999999106535952164281582190102 : Int)/10^30,(-1336759999922735592262970241 : Int)/10^30)
theorem v921_pa_checked : Scalar.distance (sourceCoefficient 9 94 1 0) v921_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v921_pb : Scalar.QComplex := ((-576781666753616506420726 : Int)/10^30,(-431476967782752044996867444 : Int)/10^30)
theorem v921_pb_checked : Scalar.distance (sourceCoefficient 9 94 1 1) v921_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v921_pg : Scalar.QComplex := ((-93086328637011426748299 : Int)/10^30,(124434191839095864494 : Int)/10^30)
theorem v921_pg_checked : Scalar.distance (sourceCoefficient 9 94 1 2) v921_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v921_mb : Scalar.QComplex := ((-949126642186714744528752 : Int)/10^30,(-431476309387556341466451616 : Int)/10^30)
theorem v921_mb_checked : Scalar.distance (sourceCoefficient 9 94 3 1) v921_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v921_mg : Scalar.QComplex := ((-93086186595613770624765 : Int)/10^30,(204763454667689525995 : Int)/10^30)
theorem v921_mg_checked : Scalar.distance (sourceCoefficient 9 94 3 2) v921_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v921_upper : Scalar.QComplex := ((999995310028261178964526669931 : Int)/10^30,(-3062665747646510642095738075 : Int)/10^30)
theorem v921_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 94 5) 1) 14) v921_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material921 : Material (9 : Basis) (94 : Basis) where
  plus := ![v921_pa,v921_pb,v921_pg]
  minus := ![(Primitive.Addresses.material921 1).one,v921_mb,v921_mg]
  upper := v921_upper
  lower := (Primitive.Addresses.material921 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v921_pa_checked.trans (by decide +kernel)
    · exact v921_pb_checked.trans (by decide +kernel)
    · exact v921_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 94 Primitive.Addresses.material921
    · exact v921_mb_checked.trans (by decide +kernel)
    · exact v921_mg_checked.trans (by decide +kernel)
  upper_error := v921_upper_checked
  lower_error := reuse_lower_error 9 94 Primitive.Addresses.material921

def v922_pa : Scalar.QComplex := ((999999046371838383478787291252 : Int)/10^30,(-1381034182714668289362023632 : Int)/10^30)
theorem v922_pa_checked : Scalar.distance (sourceCoefficient 9 95 1 0) v922_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v922_pb : Scalar.QComplex := ((-595884960339485149631714 : Int)/10^30,(-431476931957968731358497744 : Int)/10^30)
theorem v922_pb_checked : Scalar.distance (sourceCoefficient 9 95 1 1) v922_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v922_pg : Scalar.QComplex := ((-93086321972382718110970 : Int)/10^30,(128555515181203644100 : Int)/10^30)
theorem v922_pg_checked : Scalar.distance (sourceCoefficient 9 95 1 2) v922_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v922_mb : Scalar.QComplex := ((-968229897744379610748781 : Int)/10^30,(-431476257077504382831829592 : Int)/10^30)
theorem v922_mb_checked : Scalar.distance (sourceCoefficient 9 95 3 1) v922_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v922_mg : Scalar.QComplex := ((-93086176374471116807161 : Int)/10^30,(208884770723965859733 : Int)/10^30)
theorem v922_mg_checked : Scalar.distance (sourceCoefficient 9 95 3 2) v922_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v922_upper : Scalar.QComplex := ((999995173451014029153532113801 : Int)/10^30,(-3106939760659446541559472282 : Int)/10^30)
theorem v922_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 95 5) 1) 14) v922_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material922 : Material (9 : Basis) (95 : Basis) where
  plus := ![v922_pa,v922_pb,v922_pg]
  minus := ![(Primitive.Addresses.material922 1).one,v922_mb,v922_mg]
  upper := v922_upper
  lower := (Primitive.Addresses.material922 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v922_pa_checked.trans (by decide +kernel)
    · exact v922_pb_checked.trans (by decide +kernel)
    · exact v922_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 95 Primitive.Addresses.material922
    · exact v922_mb_checked.trans (by decide +kernel)
    · exact v922_mg_checked.trans (by decide +kernel)
  upper_error := v922_upper_checked
  lower_error := reuse_lower_error 9 95 Primitive.Addresses.material922

def v923_pa : Scalar.QComplex := ((999999016779313361443032202186 : Int)/10^30,(-1402298258771719113482861281 : Int)/10^30)
theorem v923_pa_checked : Scalar.distance (sourceCoefficient 9 96 1 0) v923_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v923_pb : Scalar.QComplex := ((-605059920602184877245679 : Int)/10^30,(-431476914351108966052316486 : Int)/10^30)
theorem v923_pb_checked : Scalar.distance (sourceCoefficient 9 96 1 1) v923_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v923_pg : Scalar.QComplex := ((-93086318695810287024746 : Int)/10^30,(130534910967228880236 : Int)/10^30)
theorem v923_pg_checked : Scalar.distance (sourceCoefficient 9 96 1 2) v923_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v923_mb : Scalar.QComplex := ((-977404839396895322228644 : Int)/10^30,(-431476231553073691524951023 : Int)/10^30)
theorem v923_mb_checked : Scalar.distance (sourceCoefficient 9 96 3 1) v923_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v923_mg : Scalar.QComplex := ((-93086171389770491075670 : Int)/10^30,(210864162945437145192 : Int)/10^30)
theorem v923_mg_checked : Scalar.distance (sourceCoefficient 9 96 3 2) v923_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v923_upper : Scalar.QComplex := ((999995107158666869148783702477 : Int)/10^30,(-3128203753972140357406671321 : Int)/10^30)
theorem v923_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 96 5) 1) 14) v923_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material923 : Material (9 : Basis) (96 : Basis) where
  plus := ![v923_pa,v923_pb,v923_pg]
  minus := ![(Primitive.Addresses.material923 1).one,v923_mb,v923_mg]
  upper := v923_upper
  lower := (Primitive.Addresses.material923 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v923_pa_checked.trans (by decide +kernel)
    · exact v923_pb_checked.trans (by decide +kernel)
    · exact v923_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 96 Primitive.Addresses.material923
    · exact v923_mb_checked.trans (by decide +kernel)
    · exact v923_mg_checked.trans (by decide +kernel)
  upper_error := v923_upper_checked
  lower_error := reuse_lower_error 9 96 Primitive.Addresses.material923

def v924_pa : Scalar.QComplex := ((999998911507702281207137041149 : Int)/10^30,(-1475460406321397542360485313 : Int)/10^30)
theorem v924_pa_checked : Scalar.distance (sourceCoefficient 9 97 1 0) v924_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v924_pb : Scalar.QComplex := ((-636627704017212528896334 : Int)/10^30,(-431476851784923188248520973 : Int)/10^30)
theorem v924_pb_checked : Scalar.distance (sourceCoefficient 9 97 1 1) v924_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v924_pg : Scalar.QComplex := ((-93086307047154919460575 : Int)/10^30,(137345309918065542539 : Int)/10^30)
theorem v924_pg_checked : Scalar.distance (sourceCoefficient 9 97 1 2) v924_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v924_mb : Scalar.QComplex := ((-1008972557065994039648942 : Int)/10^30,(-431476141745335882989467010 : Int)/10^30)
theorem v924_mb_checked : Scalar.distance (sourceCoefficient 9 97 3 1) v924_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v924_mg : Scalar.QComplex := ((-93086153864051895248653 : Int)/10^30,(217674549308186081245 : Int)/10^30)
theorem v924_mg_checked : Scalar.distance (sourceCoefficient 9 97 3 2) v924_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v924_upper : Scalar.QComplex := ((999994875615983126045155904779 : Int)/10^30,(-3201365610866143682069401765 : Int)/10^30)
theorem v924_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 97 5) 1) 14) v924_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material924 : Material (9 : Basis) (97 : Basis) where
  plus := ![v924_pa,v924_pb,v924_pg]
  minus := ![(Primitive.Addresses.material924 1).one,v924_mb,v924_mg]
  upper := v924_upper
  lower := (Primitive.Addresses.material924 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v924_pa_checked.trans (by decide +kernel)
    · exact v924_pb_checked.trans (by decide +kernel)
    · exact v924_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 97 Primitive.Addresses.material924
    · exact v924_mb_checked.trans (by decide +kernel)
    · exact v924_mg_checked.trans (by decide +kernel)
  upper_error := v924_upper_checked
  lower_error := reuse_lower_error 9 97 Primitive.Addresses.material924

def v925_pa : Scalar.QComplex := ((999999995237179513847483470175 : Int)/10^30,(97599390108855567972744969 : Int)/10^30)
theorem v925_pa_checked : Scalar.distance (sourceCoefficient 10 11 1 0) v925_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v925_pb : Scalar.QComplex := ((42111942894774465864094 : Int)/10^30,(-431477518939760905693347799 : Int)/10^30)
theorem v925_pb_checked : Scalar.distance (sourceCoefficient 10 11 1 1) v925_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v925_pg : Scalar.QComplex := ((-93086429452991944492775 : Int)/10^30,(-9085178785294099245 : Int)/10^30)
theorem v925_pg_checked : Scalar.distance (sourceCoefficient 10 11 1 2) v925_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v925_mb : Scalar.QComplex := ((-330233738604374936182146 : Int)/10^30,(-431477394621671174331306523 : Int)/10^30)
theorem v925_mb_checked : Scalar.distance (sourceCoefficient 10 11 3 1) v925_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v925_mg : Scalar.QComplex := ((-93086402632760109599005 : Int)/10^30,(71244220758313986011 : Int)/10^30)
theorem v925_mg_checked : Scalar.distance (sourceCoefficient 10 11 3 2) v925_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v925_upper : Scalar.QComplex := ((999998674302348039582578869850 : Int)/10^30,(-1628310027742435303859075574 : Int)/10^30)
theorem v925_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 11 5) 1) 14) v925_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material925 : Material (10 : Basis) (11 : Basis) where
  plus := ![v925_pa,v925_pb,v925_pg]
  minus := ![(Primitive.Addresses.material925 1).one,v925_mb,v925_mg]
  upper := v925_upper
  lower := (Primitive.Addresses.material925 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v925_pa_checked.trans (by decide +kernel)
    · exact v925_pb_checked.trans (by decide +kernel)
    · exact v925_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 11 Primitive.Addresses.material925
    · exact v925_mb_checked.trans (by decide +kernel)
    · exact v925_mg_checked.trans (by decide +kernel)
  upper_error := v925_upper_checked
  lower_error := reuse_lower_error 10 11 Primitive.Addresses.material925

def v926_pa : Scalar.QComplex := ((999999995705385598089981123162 : Int)/10^30,(92678092262283457582348378 : Int)/10^30)
theorem v926_pa_checked : Scalar.distance (sourceCoefficient 10 12 1 0) v926_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v926_pb : Scalar.QComplex := ((39988513499105776478738 : Int)/10^30,(-431477519133660141677003776 : Int)/10^30)
theorem v926_pb_checked : Scalar.distance (sourceCoefficient 10 12 1 1) v926_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v926_pg : Scalar.QComplex := ((-93086429495699552310039 : Int)/10^30,(-8627072738218938123 : Int)/10^30)
theorem v926_pg_checked : Scalar.distance (sourceCoefficient 10 12 1 2) v926_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v926_mb : Scalar.QComplex := ((-332357167376720123799008 : Int)/10^30,(-431477392983146405365152864 : Int)/10^30)
theorem v926_mb_checked : Scalar.distance (sourceCoefficient 10 12 3 1) v926_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v926_mg : Scalar.QComplex := ((-93086402280142815218864 : Int)/10^30,(71702326671670071393 : Int)/10^30)
theorem v926_mg_checked : Scalar.distance (sourceCoefficient 10 12 3 2) v926_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v926_upper : Scalar.QComplex := ((999998666276839799956763897622 : Int)/10^30,(-1633231319067393594112806566 : Int)/10^30)
theorem v926_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 12 5) 1) 14) v926_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material926 : Material (10 : Basis) (12 : Basis) where
  plus := ![v926_pa,v926_pb,v926_pg]
  minus := ![(Primitive.Addresses.material926 1).one,v926_mb,v926_mg]
  upper := v926_upper
  lower := (Primitive.Addresses.material926 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v926_pa_checked.trans (by decide +kernel)
    · exact v926_pb_checked.trans (by decide +kernel)
    · exact v926_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 12 Primitive.Addresses.material926
    · exact v926_mb_checked.trans (by decide +kernel)
    · exact v926_mg_checked.trans (by decide +kernel)
  upper_error := v926_upper_checked
  lower_error := reuse_lower_error 10 12 Primitive.Addresses.material926

def v927_pa : Scalar.QComplex := ((999999999152807504115848904324 : Int)/10^30,(41162907951826812915518466 : Int)/10^30)
theorem v927_pa_checked : Scalar.distance (sourceCoefficient 10 13 1 0) v927_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v927_pb : Scalar.QComplex := ((17760869467552105098486 : Int)/10^30,(-431477520327059426284001955 : Int)/10^30)
theorem v927_pb_checked : Scalar.distance (sourceCoefficient 10 13 1 1) v927_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v927_pg : Scalar.QComplex := ((-93086429784884898606368 : Int)/10^30,(-3831708144045601261 : Int)/10^30)
theorem v927_pg_checked : Scalar.distance (sourceCoefficient 10 13 1 2) v927_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v927_mb : Scalar.QComplex := ((-354584804161755902622710 : Int)/10^30,(-431477374995089542308991555 : Int)/10^30)
theorem v927_mb_checked : Scalar.distance (sourceCoefficient 10 13 3 1) v927_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v927_mg : Scalar.QComplex := ((-93086398431144384270627 : Int)/10^30,(76497689729863940285 : Int)/10^30)
theorem v927_mg_checked : Scalar.distance (sourceCoefficient 10 13 3 2) v927_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v927_upper : Scalar.QComplex := ((999998580813721872618379681150 : Int)/10^30,(-1684746432601972069119523672 : Int)/10^30)
theorem v927_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 13 5) 1) 14) v927_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material927 : Material (10 : Basis) (13 : Basis) where
  plus := ![v927_pa,v927_pb,v927_pg]
  minus := ![(Primitive.Addresses.material927 1).one,v927_mb,v927_mg]
  upper := v927_upper
  lower := (Primitive.Addresses.material927 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v927_pa_checked.trans (by decide +kernel)
    · exact v927_pb_checked.trans (by decide +kernel)
    · exact v927_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 13 Primitive.Addresses.material927
    · exact v927_mb_checked.trans (by decide +kernel)
    · exact v927_mg_checked.trans (by decide +kernel)
  upper_error := v927_upper_checked
  lower_error := reuse_lower_error 10 13 Primitive.Addresses.material927

def v928_pa : Scalar.QComplex := ((999999999691174748847088007370 : Int)/10^30,(24852575363741499969353075 : Int)/10^30)
theorem v928_pa_checked : Scalar.distance (sourceCoefficient 10 14 1 0) v928_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v928_pb : Scalar.QComplex := ((10723327596482095192272 : Int)/10^30,(-431477520386687511679685786 : Int)/10^30)
theorem v928_pb_checked : Scalar.distance (sourceCoefficient 10 14 1 1) v928_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v928_pg : Scalar.QComplex := ((-93086429816374286085595 : Int)/10^30,(-2313437513067523702 : Int)/10^30)
theorem v928_pg_checked : Scalar.distance (sourceCoefficient 10 14 1 2) v928_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v928_mb : Scalar.QComplex := ((-361622343463883794524331 : Int)/10^30,(-431477368981635929888792904 : Int)/10^30)
theorem v928_mb_checked : Scalar.distance (sourceCoefficient 10 14 3 1) v928_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v928_mg : Scalar.QComplex := ((-93086397152434585861655 : Int)/10^30,(78015959822694396700 : Int)/10^30)
theorem v928_mg_checked : Scalar.distance (sourceCoefficient 10 14 3 2) v928_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v928_upper : Scalar.QComplex := ((999998553201933930293505991284 : Int)/10^30,(-1701056741826905962477491749 : Int)/10^30)
theorem v928_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 14 5) 1) 14) v928_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material928 : Material (10 : Basis) (14 : Basis) where
  plus := ![v928_pa,v928_pb,v928_pg]
  minus := ![(Primitive.Addresses.material928 1).one,v928_mb,v928_mg]
  upper := v928_upper
  lower := (Primitive.Addresses.material928 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v928_pa_checked.trans (by decide +kernel)
    · exact v928_pb_checked.trans (by decide +kernel)
    · exact v928_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 14 Primitive.Addresses.material928
    · exact v928_mb_checked.trans (by decide +kernel)
    · exact v928_mg_checked.trans (by decide +kernel)
  upper_error := v928_upper_checked
  lower_error := reuse_lower_error 10 14 Primitive.Addresses.material928

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
