import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B125
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B126

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3009_pa : Scalar.QComplex := ((999999251989277227698568561289 : Int)/10^30,(-1223119326159374149448781940 : Int)/10^30)
theorem v3009_pa_checked : Scalar.distance (sourceCoefficient 38 65 1 0) v3009_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3009_pb : Scalar.QComplex := ((-527748481658105693873055 : Int)/10^30,(-431477187555955744121295279 : Int)/10^30)
theorem v3009_pb_checked : Scalar.distance (sourceCoefficient 38 65 1 1) v3009_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3009_pg : Scalar.QComplex := ((-93086359113677724788112 : Int)/10^30,(113855809999117744699 : Int)/10^30)
theorem v3009_pg_checked : Scalar.distance (sourceCoefficient 38 65 1 2) v3009_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3009_mb : Scalar.QComplex := ((-900093665002876244991558 : Int)/10^30,(-431476571474108573730787340 : Int)/10^30)
theorem v3009_mb_checked : Scalar.distance (sourceCoefficient 38 65 3 1) v3009_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3009_mg : Scalar.QComplex := ((-93086226200935816077918 : Int)/10^30,(194185103066516818269 : Int)/10^30)
theorem v3009_mg_checked : Scalar.distance (sourceCoefficient 38 65 3 2) v3009_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3009_upper : Scalar.QComplex := ((999995651614863120910641194188 : Int)/10^30,(-2949025494176827235424987620 : Int)/10^30)
theorem v3009_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 65 5) 1) 14) v3009_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3009 : Material (38 : Basis) (65 : Basis) where
  plus := ![v3009_pa,v3009_pb,v3009_pg]
  minus := ![(Primitive.Addresses.material3009 1).one,v3009_mb,v3009_mg]
  upper := v3009_upper
  lower := (Primitive.Addresses.material3009 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3009_pa_checked.trans (by decide +kernel)
    · exact v3009_pb_checked.trans (by decide +kernel)
    · exact v3009_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 65 Primitive.Addresses.material3009
    · exact v3009_mb_checked.trans (by decide +kernel)
    · exact v3009_mg_checked.trans (by decide +kernel)
  upper_error := v3009_upper_checked
  lower_error := reuse_lower_error 38 65 Primitive.Addresses.material3009

def v3010_pa : Scalar.QComplex := ((999999230322923585839904101824 : Int)/10^30,(-1240706879333518580111087466 : Int)/10^30)
theorem v3010_pa_checked : Scalar.distance (sourceCoefficient 38 66 1 0) v3010_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3010_pb : Scalar.QComplex := ((-535337114076147090771588 : Int)/10^30,(-431477177209667568189306855 : Int)/10^30)
theorem v3010_pb_checked : Scalar.distance (sourceCoefficient 38 66 1 1) v3010_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3010_pg : Scalar.QComplex := ((-93086356989208225156730 : Int)/10^30,(115492972380899731838 : Int)/10^30)
theorem v3010_pg_checked : Scalar.distance (sourceCoefficient 38 66 1 2) v3010_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3010_mb : Scalar.QComplex := ((-907682285666942258710800 : Int)/10^30,(-431476554579176252741673992 : Int)/10^30)
theorem v3010_mb_checked : Scalar.distance (sourceCoefficient 38 66 3 1) v3010_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3010_mg : Scalar.QComplex := ((-93086222663669707062270 : Int)/10^30,(195822263005386933026 : Int)/10^30)
theorem v3010_mg_checked : Scalar.distance (sourceCoefficient 38 66 3 2) v3010_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3010_upper : Scalar.QComplex := ((999995599594020500327689467054 : Int)/10^30,(-2966612983762216362722368375 : Int)/10^30)
theorem v3010_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 66 5) 1) 14) v3010_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3010 : Material (38 : Basis) (66 : Basis) where
  plus := ![v3010_pa,v3010_pb,v3010_pg]
  minus := ![(Primitive.Addresses.material3010 1).one,v3010_mb,v3010_mg]
  upper := v3010_upper
  lower := (Primitive.Addresses.material3010 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3010_pa_checked.trans (by decide +kernel)
    · exact v3010_pb_checked.trans (by decide +kernel)
    · exact v3010_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 66 Primitive.Addresses.material3010
    · exact v3010_mb_checked.trans (by decide +kernel)
    · exact v3010_mg_checked.trans (by decide +kernel)
  upper_error := v3010_upper_checked
  lower_error := reuse_lower_error 38 66 Primitive.Addresses.material3010

def v3011_pa : Scalar.QComplex := ((999999193265155442946986266355 : Int)/10^30,(-1270224011067731550687170052 : Int)/10^30)
theorem v3011_pa_checked : Scalar.distance (sourceCoefficient 38 67 1 0) v3011_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3011_pb : Scalar.QComplex := ((-548073090304730601389969 : Int)/10^30,(-431477159445576463287391163 : Int)/10^30)
theorem v3011_pb_checked : Scalar.distance (sourceCoefficient 38 67 1 1) v3011_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3011_pg : Scalar.QComplex := ((-93086353348218970257100 : Int)/10^30,(118240616514468247296 : Int)/10^30)
theorem v3011_pg_checked : Scalar.distance (sourceCoefficient 38 67 1 2) v3011_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3011_mb : Scalar.QComplex := ((-920418241823729197992609 : Int)/10^30,(-431476525824517884031205899 : Int)/10^30)
theorem v3011_mb_checked : Scalar.distance (sourceCoefficient 38 67 3 1) v3011_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3011_mg : Scalar.QComplex := ((-93086216651588669897698 : Int)/10^30,(198569902973872221106 : Int)/10^30)
theorem v3011_mg_checked : Scalar.distance (sourceCoefficient 38 67 3 2) v3011_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3011_upper : Scalar.QComplex := ((999995511592415950649032935566 : Int)/10^30,(-2996130007575782980879470293 : Int)/10^30)
theorem v3011_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 67 5) 1) 14) v3011_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3011 : Material (38 : Basis) (67 : Basis) where
  plus := ![v3011_pa,v3011_pb,v3011_pg]
  minus := ![(Primitive.Addresses.material3011 1).one,v3011_mb,v3011_mg]
  upper := v3011_upper
  lower := (Primitive.Addresses.material3011 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3011_pa_checked.trans (by decide +kernel)
    · exact v3011_pb_checked.trans (by decide +kernel)
    · exact v3011_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 67 Primitive.Addresses.material3011
    · exact v3011_mb_checked.trans (by decide +kernel)
    · exact v3011_mg_checked.trans (by decide +kernel)
  upper_error := v3011_upper_checked
  lower_error := reuse_lower_error 38 67 Primitive.Addresses.material3011

def v3012_pa : Scalar.QComplex := ((999999129615252367200626394873 : Int)/10^30,(-1319381952921893590730469632 : Int)/10^30)
theorem v3012_pa_checked : Scalar.distance (sourceCoefficient 38 68 1 0) v3012_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3012_pb : Scalar.QComplex := ((-569283632265376763550177 : Int)/10^30,(-431477128748696240485371539 : Int)/10^30)
theorem v3012_pb_checked : Scalar.distance (sourceCoefficient 38 68 1 1) v3012_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3012_pg : Scalar.QComplex := ((-93086347074494251396781 : Int)/10^30,(122816553291166163035 : Int)/10^30)
theorem v3012_pg_checked : Scalar.distance (sourceCoefficient 38 68 1 2) v3012_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3012_mb : Scalar.QComplex := ((-941628749396696122433754 : Int)/10^30,(-431476476823906666390946256 : Int)/10^30)
theorem v3012_mb_checked : Scalar.distance (sourceCoefficient 38 68 3 1) v3012_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3012_mg : Scalar.QComplex := ((-93086206429038941283422 : Int)/10^30,(203145832632797869935 : Int)/10^30)
theorem v3012_mg_checked : Scalar.distance (sourceCoefficient 38 68 3 2) v3012_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3012_upper : Scalar.QComplex := ((999995363100459607321512433959 : Int)/10^30,(-3045287766361006691997586170 : Int)/10^30)
theorem v3012_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 68 5) 1) 14) v3012_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3012 : Material (38 : Basis) (68 : Basis) where
  plus := ![v3012_pa,v3012_pb,v3012_pg]
  minus := ![(Primitive.Addresses.material3012 1).one,v3012_mb,v3012_mg]
  upper := v3012_upper
  lower := (Primitive.Addresses.material3012 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3012_pa_checked.trans (by decide +kernel)
    · exact v3012_pb_checked.trans (by decide +kernel)
    · exact v3012_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 68 Primitive.Addresses.material3012
    · exact v3012_mb_checked.trans (by decide +kernel)
    · exact v3012_mg_checked.trans (by decide +kernel)
  upper_error := v3012_upper_checked
  lower_error := reuse_lower_error 38 68 Primitive.Addresses.material3012

def v3013_pa : Scalar.QComplex := ((999999100835867405180539328406 : Int)/10^30,(-1341017321548644865358940767 : Int)/10^30)
theorem v3013_pa_checked : Scalar.distance (sourceCoefficient 38 69 1 0) v3013_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3013_pb : Scalar.QComplex := ((-578618805068987402138901 : Int)/10^30,(-431477114797821269661440424 : Int)/10^30)
theorem v3013_pb_checked : Scalar.distance (sourceCoefficient 38 69 1 1) v3013_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3013_pg : Scalar.QComplex := ((-93086344230136844132795 : Int)/10^30,(124830512255372536448 : Int)/10^30)
theorem v3013_pg_checked : Scalar.distance (sourceCoefficient 38 69 1 2) v3013_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3013_mb : Scalar.QComplex := ((-950963906685418512027891 : Int)/10^30,(-431476454817203201174958981 : Int)/10^30)
theorem v3013_mb_checked : Scalar.distance (sourceCoefficient 38 69 3 1) v3013_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3013_mg : Scalar.QComplex := ((-93086201846726712338199 : Int)/10^30,(205159788392562941136 : Int)/10^30)
theorem v3013_mg_checked : Scalar.distance (sourceCoefficient 38 69 3 2) v3013_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3013_upper : Scalar.QComplex := ((999995296980434004351656169993 : Int)/10^30,(-3066923053093810266969665975 : Int)/10^30)
theorem v3013_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 69 5) 1) 14) v3013_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3013 : Material (38 : Basis) (69 : Basis) where
  plus := ![v3013_pa,v3013_pb,v3013_pg]
  minus := ![(Primitive.Addresses.material3013 1).one,v3013_mb,v3013_mg]
  upper := v3013_upper
  lower := (Primitive.Addresses.material3013 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3013_pa_checked.trans (by decide +kernel)
    · exact v3013_pb_checked.trans (by decide +kernel)
    · exact v3013_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 69 Primitive.Addresses.material3013
    · exact v3013_mb_checked.trans (by decide +kernel)
    · exact v3013_mg_checked.trans (by decide +kernel)
  upper_error := v3013_upper_checked
  lower_error := reuse_lower_error 38 69 Primitive.Addresses.material3013

def v3014_pa : Scalar.QComplex := ((999999081649279920148165296434 : Int)/10^30,(-1355249274779978843071634607 : Int)/10^30)
theorem v3014_pa_checked : Scalar.distance (sourceCoefficient 38 70 1 0) v3014_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3014_pb : Scalar.QComplex := ((-584759571292130489039483 : Int)/10^30,(-431477105473966190655573656 : Int)/10^30)
theorem v3014_pb_checked : Scalar.distance (sourceCoefficient 38 70 1 1) v3014_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3014_pg : Scalar.QComplex := ((-93086342331372863032330 : Int)/10^30,(126155313791337179819 : Int)/10^30)
theorem v3014_pg_checked : Scalar.distance (sourceCoefficient 38 70 1 2) v3014_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3014_mb : Scalar.QComplex := ((-957104662576006684833797 : Int)/10^30,(-431476440194146913137910525 : Int)/10^30)
theorem v3014_mb_checked : Scalar.distance (sourceCoefficient 38 70 3 1) v3014_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3014_mg : Scalar.QComplex := ((-93086198804719379543097 : Int)/10^30,(206484587796695627711 : Int)/10^30)
theorem v3014_mg_checked : Scalar.distance (sourceCoefficient 38 70 3 2) v3014_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3014_upper : Scalar.QComplex := ((999995253230814930916608272331 : Int)/10^30,(-3081154952014012303728677807 : Int)/10^30)
theorem v3014_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 70 5) 1) 14) v3014_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3014 : Material (38 : Basis) (70 : Basis) where
  plus := ![v3014_pa,v3014_pb,v3014_pg]
  minus := ![(Primitive.Addresses.material3014 1).one,v3014_mb,v3014_mg]
  upper := v3014_upper
  lower := (Primitive.Addresses.material3014 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3014_pa_checked.trans (by decide +kernel)
    · exact v3014_pb_checked.trans (by decide +kernel)
    · exact v3014_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 70 Primitive.Addresses.material3014
    · exact v3014_mb_checked.trans (by decide +kernel)
    · exact v3014_mg_checked.trans (by decide +kernel)
  upper_error := v3014_upper_checked
  lower_error := reuse_lower_error 38 70 Primitive.Addresses.material3014

def v3015_pa : Scalar.QComplex := ((999999048431387773455398185847 : Int)/10^30,(-1379542068575752215678284891 : Int)/10^30)
theorem v3015_pa_checked : Scalar.distance (sourceCoefficient 38 71 1 0) v3015_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3015_pb : Scalar.QComplex := ((-595241362714745089395438 : Int)/10^30,(-431477089289693006241275354 : Int)/10^30)
theorem v3015_pb_checked : Scalar.distance (sourceCoefficient 38 71 1 1) v3015_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3015_pg : Scalar.QComplex := ((-93086339039517769245111 : Int)/10^30,(128416642911966825591 : Int)/10^30)
theorem v3015_pg_checked : Scalar.distance (sourceCoefficient 38 71 1 2) v3015_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3015_mb : Scalar.QComplex := ((-967586436129472451473369 : Int)/10^30,(-431476414964565839512930066 : Int)/10^30)
theorem v3015_mb_checked : Scalar.distance (sourceCoefficient 38 71 3 1) v3015_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3015_mg : Scalar.QComplex := ((-93086193561440326843464 : Int)/10^30,(208745913234606407737 : Int)/10^30)
theorem v3015_mg_checked : Scalar.distance (sourceCoefficient 38 71 3 2) v3015_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3015_upper : Scalar.QComplex := ((999995178085813991905120941001 : Int)/10^30,(-3105447652297454607990490432 : Int)/10^30)
theorem v3015_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 71 5) 1) 14) v3015_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3015 : Material (38 : Basis) (71 : Basis) where
  plus := ![v3015_pa,v3015_pb,v3015_pg]
  minus := ![(Primitive.Addresses.material3015 1).one,v3015_mb,v3015_mg]
  upper := v3015_upper
  lower := (Primitive.Addresses.material3015 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3015_pa_checked.trans (by decide +kernel)
    · exact v3015_pb_checked.trans (by decide +kernel)
    · exact v3015_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 71 Primitive.Addresses.material3015
    · exact v3015_mb_checked.trans (by decide +kernel)
    · exact v3015_mg_checked.trans (by decide +kernel)
  upper_error := v3015_upper_checked
  lower_error := reuse_lower_error 38 71 Primitive.Addresses.material3015

def v3016_pa : Scalar.QComplex := ((999999011715542236099975824061 : Int)/10^30,(-1405904669179824080815272905 : Int)/10^30)
theorem v3016_pa_checked : Scalar.distance (sourceCoefficient 38 72 1 0) v3016_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3016_pb : Scalar.QComplex := ((-606616228753631150015922 : Int)/10^30,(-431477071342346098791296778 : Int)/10^30)
theorem v3016_pb_checked : Scalar.distance (sourceCoefficient 38 72 1 1) v3016_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3016_pg : Scalar.QComplex := ((-93086335394675000015806 : Int)/10^30,(130870642905635066167 : Int)/10^30)
theorem v3016_pg_checked : Scalar.distance (sourceCoefficient 38 72 1 2) v3016_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3016_mb : Scalar.QComplex := ((-978961282445223966126323 : Int)/10^30,(-431476387201228528070506890 : Int)/10^30)
theorem v3016_mb_checked : Scalar.distance (sourceCoefficient 38 72 3 1) v3016_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3016_mg : Scalar.QComplex := ((-93086187798907444276878 : Int)/10^30,(211199909169203145110 : Int)/10^30)
theorem v3016_mg_checked : Scalar.distance (sourceCoefficient 38 72 3 2) v3016_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3016_upper : Scalar.QComplex := ((999995095870566092305316277744 : Int)/10^30,(-3131810150269311079978150167 : Int)/10^30)
theorem v3016_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 72 5) 1) 14) v3016_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3016 : Material (38 : Basis) (72 : Basis) where
  plus := ![v3016_pa,v3016_pb,v3016_pg]
  minus := ![(Primitive.Addresses.material3016 1).one,v3016_mb,v3016_mg]
  upper := v3016_upper
  lower := (Primitive.Addresses.material3016 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3016_pa_checked.trans (by decide +kernel)
    · exact v3016_pb_checked.trans (by decide +kernel)
    · exact v3016_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 72 Primitive.Addresses.material3016
    · exact v3016_mb_checked.trans (by decide +kernel)
    · exact v3016_mg_checked.trans (by decide +kernel)
  upper_error := v3016_upper_checked
  lower_error := reuse_lower_error 38 72 Primitive.Addresses.material3016

def v3017_pa : Scalar.QComplex := ((999998998385597711585325858782 : Int)/10^30,(-1415354302408205659496281365 : Int)/10^30)
theorem v3017_pa_checked : Scalar.distance (sourceCoefficient 38 73 1 0) v3017_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3017_pb : Scalar.QComplex := ((-610693531751285446891032 : Int)/10^30,(-431477064811802352954058350 : Int)/10^30)
theorem v3017_pb_checked : Scalar.distance (sourceCoefficient 38 73 1 1) v3017_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3017_pg : Scalar.QComplex := ((-93086334069810787274695 : Int)/10^30,(131750275384087564651 : Int)/10^30)
theorem v3017_pg_checked : Scalar.distance (sourceCoefficient 38 73 1 2) v3017_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3017_mb : Scalar.QComplex := ((-983038578289146887136617 : Int)/10^30,(-431476377152158361787673483 : Int)/10^30)
theorem v3017_mb_checked : Scalar.distance (sourceCoefficient 38 73 3 1) v3017_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3017_mg : Scalar.QComplex := ((-93086185714960513114928 : Int)/10^30,(212079540176830124750 : Int)/10^30)
theorem v3017_mg_checked : Scalar.distance (sourceCoefficient 38 73 3 2) v3017_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3017_upper : Scalar.QComplex := ((999995066231431733020485167864 : Int)/10^30,(-3141259746417299030687867364 : Int)/10^30)
theorem v3017_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 73 5) 1) 14) v3017_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3017 : Material (38 : Basis) (73 : Basis) where
  plus := ![v3017_pa,v3017_pb,v3017_pg]
  minus := ![(Primitive.Addresses.material3017 1).one,v3017_mb,v3017_mg]
  upper := v3017_upper
  lower := (Primitive.Addresses.material3017 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3017_pa_checked.trans (by decide +kernel)
    · exact v3017_pb_checked.trans (by decide +kernel)
    · exact v3017_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 73 Primitive.Addresses.material3017
    · exact v3017_mb_checked.trans (by decide +kernel)
    · exact v3017_mg_checked.trans (by decide +kernel)
  upper_error := v3017_upper_checked
  lower_error := reuse_lower_error 38 73 Primitive.Addresses.material3017

def v3018_pa : Scalar.QComplex := ((999998983279361653583452358497 : Int)/10^30,(-1425987462417526536276069588 : Int)/10^30)
theorem v3018_pa_checked : Scalar.distance (sourceCoefficient 38 74 1 0) v3018_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3018_pb : Scalar.QComplex := ((-615281499745329112767472 : Int)/10^30,(-431477057401909195535630634 : Int)/10^30)
theorem v3018_pb_checked : Scalar.distance (sourceCoefficient 38 74 1 1) v3018_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3018_pg : Scalar.QComplex := ((-93086332567417375356591 : Int)/10^30,(132740078123142424506 : Int)/10^30)
theorem v3018_pg_checked : Scalar.distance (sourceCoefficient 38 74 1 2) v3018_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3018_mb : Scalar.QComplex := ((-987626538180476322681942 : Int)/10^30,(-431476365783058218959255417 : Int)/10^30)
theorem v3018_mb_checked : Scalar.distance (sourceCoefficient 38 74 3 1) v3018_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3018_mg : Scalar.QComplex := ((-93086183358412475862723 : Int)/10^30,(213069341250838339436 : Int)/10^30)
theorem v3018_mg_checked : Scalar.distance (sourceCoefficient 38 74 3 2) v3018_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3018_upper : Scalar.QComplex := ((999995032773348630635631744253 : Int)/10^30,(-3151892864517784123219253510 : Int)/10^30)
theorem v3018_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 74 5) 1) 14) v3018_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3018 : Material (38 : Basis) (74 : Basis) where
  plus := ![v3018_pa,v3018_pb,v3018_pg]
  minus := ![(Primitive.Addresses.material3018 1).one,v3018_mb,v3018_mg]
  upper := v3018_upper
  lower := (Primitive.Addresses.material3018 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3018_pa_checked.trans (by decide +kernel)
    · exact v3018_pb_checked.trans (by decide +kernel)
    · exact v3018_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 74 Primitive.Addresses.material3018
    · exact v3018_mb_checked.trans (by decide +kernel)
    · exact v3018_mg_checked.trans (by decide +kernel)
  upper_error := v3018_upper_checked
  lower_error := reuse_lower_error 38 74 Primitive.Addresses.material3018

def v3019_pa : Scalar.QComplex := ((999998962043429618800446583746 : Int)/10^30,(-1440802576138923034973511423 : Int)/10^30)
theorem v3019_pa_checked : Scalar.distance (sourceCoefficient 38 75 1 0) v3019_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3019_pb : Scalar.QComplex := ((-621673886088680280493756 : Int)/10^30,(-431477046969302114468363626 : Int)/10^30)
theorem v3019_pb_checked : Scalar.distance (sourceCoefficient 38 75 1 1) v3019_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3019_pg : Scalar.QComplex := ((-93086330453669913077591 : Int)/10^30,(134119163930834111000 : Int)/10^30)
theorem v3019_pg_checked : Scalar.distance (sourceCoefficient 38 75 1 2) v3019_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3019_mb : Scalar.QComplex := ((-994018913140779864509957 : Int)/10^30,(-431476349834113510509805963 : Int)/10^30)
theorem v3019_mb_checked : Scalar.distance (sourceCoefficient 38 75 3 1) v3019_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3019_mg : Scalar.QComplex := ((-93086180054576860309665 : Int)/10^30,(214448424720964492097 : Int)/10^30)
theorem v3019_mg_checked : Scalar.distance (sourceCoefficient 38 75 3 2) v3019_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3019_upper : Scalar.QComplex := ((999994985967905957766410650652 : Int)/10^30,(-3166707919522516856073787395 : Int)/10^30)
theorem v3019_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 75 5) 1) 14) v3019_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3019 : Material (38 : Basis) (75 : Basis) where
  plus := ![v3019_pa,v3019_pb,v3019_pg]
  minus := ![(Primitive.Addresses.material3019 1).one,v3019_mb,v3019_mg]
  upper := v3019_upper
  lower := (Primitive.Addresses.material3019 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3019_pa_checked.trans (by decide +kernel)
    · exact v3019_pb_checked.trans (by decide +kernel)
    · exact v3019_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 75 Primitive.Addresses.material3019
    · exact v3019_mb_checked.trans (by decide +kernel)
    · exact v3019_mg_checked.trans (by decide +kernel)
  upper_error := v3019_upper_checked
  lower_error := reuse_lower_error 38 75 Primitive.Addresses.material3019

def v3020_pa : Scalar.QComplex := ((999998944056732426124063935723 : Int)/10^30,(-1453232748093562450302574790 : Int)/10^30)
theorem v3020_pa_checked : Scalar.distance (sourceCoefficient 38 76 1 0) v3020_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3020_pb : Scalar.QComplex := ((-627037223960276474013158 : Int)/10^30,(-431477038118722098884934275 : Int)/10^30)
theorem v3020_pb_checked : Scalar.distance (sourceCoefficient 38 76 1 1) v3020_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3020_pg : Scalar.QComplex := ((-93086328661804573493176 : Int)/10^30,(135276244055173980717 : Int)/10^30)
theorem v3020_pg_checked : Scalar.distance (sourceCoefficient 38 76 1 2) v3020_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3020_mb : Scalar.QComplex := ((-999382241377708313662462 : Int)/10^30,(-431476336355217762985057881 : Int)/10^30)
theorem v3020_mb_checked : Scalar.distance (sourceCoefficient 38 76 3 1) v3020_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3020_mg : Scalar.QComplex := ((-93086177264204153567577 : Int)/10^30,(215605502868171464906 : Int)/10^30)
theorem v3020_mg_checked : Scalar.distance (sourceCoefficient 38 76 3 2) v3020_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3020_upper : Scalar.QComplex := ((999994946527886416845956335793 : Int)/10^30,(-3179138041920467681398643114 : Int)/10^30)
theorem v3020_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 76 5) 1) 14) v3020_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3020 : Material (38 : Basis) (76 : Basis) where
  plus := ![v3020_pa,v3020_pb,v3020_pg]
  minus := ![(Primitive.Addresses.material3020 1).one,v3020_mb,v3020_mg]
  upper := v3020_upper
  lower := (Primitive.Addresses.material3020 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3020_pa_checked.trans (by decide +kernel)
    · exact v3020_pb_checked.trans (by decide +kernel)
    · exact v3020_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 76 Primitive.Addresses.material3020
    · exact v3020_mb_checked.trans (by decide +kernel)
    · exact v3020_mg_checked.trans (by decide +kernel)
  upper_error := v3020_upper_checked
  lower_error := reuse_lower_error 38 76 Primitive.Addresses.material3020

def v3021_pa : Scalar.QComplex := ((999998939870633536439373398251 : Int)/10^30,(-1456110438480834328907500701 : Int)/10^30)
theorem v3021_pa_checked : Scalar.distance (sourceCoefficient 38 77 1 0) v3021_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3021_pb : Scalar.QComplex := ((-628278882224358793669493 : Int)/10^30,(-431477036057066193254282484 : Int)/10^30)
theorem v3021_pb_checked : Scalar.distance (sourceCoefficient 38 77 1 1) v3021_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3021_pg : Scalar.QComplex := ((-93086328244580517801376 : Int)/10^30,(135544117931086881219 : Int)/10^30)
theorem v3021_pg_checked : Scalar.distance (sourceCoefficient 38 77 1 2) v3021_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3021_mb : Scalar.QComplex := ((-1000623897400348321990794 : Int)/10^30,(-431476333222067465312364391 : Int)/10^30)
theorem v3021_mb_checked : Scalar.distance (sourceCoefficient 38 77 3 1) v3021_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3021_mg : Scalar.QComplex := ((-93086176615817162906040 : Int)/10^30,(215873376284297109977 : Int)/10^30)
theorem v3021_mg_checked : Scalar.distance (sourceCoefficient 38 77 3 2) v3021_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3021_upper : Scalar.QComplex := ((999994937375161215465194413266 : Int)/10^30,(-3182015720796930841749791684 : Int)/10^30)
theorem v3021_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 77 5) 1) 14) v3021_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3021 : Material (38 : Basis) (77 : Basis) where
  plus := ![v3021_pa,v3021_pb,v3021_pg]
  minus := ![(Primitive.Addresses.material3021 1).one,v3021_mb,v3021_mg]
  upper := v3021_upper
  lower := (Primitive.Addresses.material3021 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3021_pa_checked.trans (by decide +kernel)
    · exact v3021_pb_checked.trans (by decide +kernel)
    · exact v3021_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 77 Primitive.Addresses.material3021
    · exact v3021_mb_checked.trans (by decide +kernel)
    · exact v3021_mg_checked.trans (by decide +kernel)
  upper_error := v3021_upper_checked
  lower_error := reuse_lower_error 38 77 Primitive.Addresses.material3021

def v3022_pa : Scalar.QComplex := ((999998914530883309611124336413 : Int)/10^30,(-1473410009175169972556982711 : Int)/10^30)
theorem v3022_pa_checked : Scalar.distance (sourceCoefficient 38 78 1 0) v3022_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3022_pb : Scalar.QComplex := ((-635743255326172286278148 : Int)/10^30,(-431477023562774417890556171 : Int)/10^30)
theorem v3022_pb_checked : Scalar.distance (sourceCoefficient 38 78 1 1) v3022_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3022_pg : Scalar.QComplex := ((-93086325717435502409778 : Int)/10^30,(137154472906354059980 : Int)/10^30)
theorem v3022_pg_checked : Scalar.distance (sourceCoefficient 38 78 1 2) v3022_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3022_mb : Scalar.QComplex := ((-1008088256940823489964383 : Int)/10^30,(-431476314286362538164249650 : Int)/10^30)
theorem v3022_mb_checked : Scalar.distance (sourceCoefficient 38 78 3 1) v3022_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3022_mg : Scalar.QComplex := ((-93086172699009272526183 : Int)/10^30,(217483728479143204691 : Int)/10^30)
theorem v3022_mg_checked : Scalar.distance (sourceCoefficient 38 78 3 2) v3022_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3022_upper : Scalar.QComplex := ((999994882177959115588843778029 : Int)/10^30,(-3199315221991477999188610766 : Int)/10^30)
theorem v3022_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 78 5) 1) 14) v3022_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3022 : Material (38 : Basis) (78 : Basis) where
  plus := ![v3022_pa,v3022_pb,v3022_pg]
  minus := ![(Primitive.Addresses.material3022 1).one,v3022_mb,v3022_mg]
  upper := v3022_upper
  lower := (Primitive.Addresses.material3022 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3022_pa_checked.trans (by decide +kernel)
    · exact v3022_pb_checked.trans (by decide +kernel)
    · exact v3022_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 78 Primitive.Addresses.material3022
    · exact v3022_mb_checked.trans (by decide +kernel)
    · exact v3022_mg_checked.trans (by decide +kernel)
  upper_error := v3022_upper_checked
  lower_error := reuse_lower_error 38 78 Primitive.Addresses.material3022

def v3023_pa : Scalar.QComplex := ((999998906298004339518907051839 : Int)/10^30,(-1478987084168386804569607832 : Int)/10^30)
theorem v3023_pa_checked : Scalar.distance (sourceCoefficient 38 79 1 0) v3023_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3023_pb : Scalar.QComplex := ((-638149636898745931921264 : Int)/10^30,(-431477019498136123812793491 : Int)/10^30)
theorem v3023_pb_checked : Scalar.distance (sourceCoefficient 38 79 1 1) v3023_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3023_pg : Scalar.QComplex := ((-93086324895800812492652 : Int)/10^30,(137673622807507570691 : Int)/10^30)
theorem v3023_pg_checked : Scalar.distance (sourceCoefficient 38 79 1 2) v3023_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3023_mb : Scalar.QComplex := ((-1010494634109791515791468 : Int)/10^30,(-431476308145126839808826984 : Int)/10^30)
theorem v3023_mb_checked : Scalar.distance (sourceCoefficient 38 79 3 1) v3023_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3023_mg : Scalar.QComplex := ((-93086171429371905489303 : Int)/10^30,(218002877477959748534 : Int)/10^30)
theorem v3023_mg_checked : Scalar.distance (sourceCoefficient 38 79 3 2) v3023_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3023_upper : Scalar.QComplex := ((999994864319566917401631966842 : Int)/10^30,(-3204892274469094536620473542 : Int)/10^30)
theorem v3023_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 79 5) 1) 14) v3023_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3023 : Material (38 : Basis) (79 : Basis) where
  plus := ![v3023_pa,v3023_pb,v3023_pg]
  minus := ![(Primitive.Addresses.material3023 1).one,v3023_mb,v3023_mg]
  upper := v3023_upper
  lower := (Primitive.Addresses.material3023 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3023_pa_checked.trans (by decide +kernel)
    · exact v3023_pb_checked.trans (by decide +kernel)
    · exact v3023_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 79 Primitive.Addresses.material3023
    · exact v3023_mb_checked.trans (by decide +kernel)
    · exact v3023_mg_checked.trans (by decide +kernel)
  upper_error := v3023_upper_checked
  lower_error := reuse_lower_error 38 79 Primitive.Addresses.material3023

def v3024_pa : Scalar.QComplex := ((999998893375191021900504518872 : Int)/10^30,(-1487699026462587675624744058 : Int)/10^30)
theorem v3024_pa_checked : Scalar.distance (sourceCoefficient 38 80 1 0) v3024_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3024_pb : Scalar.QComplex := ((-641908642701166347652803 : Int)/10^30,(-431477013112960987111677105 : Int)/10^30)
theorem v3024_pb_checked : Scalar.distance (sourceCoefficient 38 80 1 1) v3024_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3024_pg : Scalar.QComplex := ((-93086323605566617268243 : Int)/10^30,(138484586255461662119 : Int)/10^30)
theorem v3024_pg_checked : Scalar.distance (sourceCoefficient 38 80 1 2) v3024_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3024_mb : Scalar.QComplex := ((-1014253633002443710869579 : Int)/10^30,(-431476298516101372448066359 : Int)/10^30)
theorem v3024_mb_checked : Scalar.distance (sourceCoefficient 38 80 3 1) v3024_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3024_mg : Scalar.QComplex := ((-93086169439313259531516 : Int)/10^30,(218813839510541084940 : Int)/10^30)
theorem v3024_mg_checked : Scalar.distance (sourceCoefficient 38 80 3 2) v3024_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3024_upper : Scalar.QComplex := ((999994836360750788236065312003 : Int)/10^30,(-3213604181484277299350504461 : Int)/10^30)
theorem v3024_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 80 5) 1) 14) v3024_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3024 : Material (38 : Basis) (80 : Basis) where
  plus := ![v3024_pa,v3024_pb,v3024_pg]
  minus := ![(Primitive.Addresses.material3024 1).one,v3024_mb,v3024_mg]
  upper := v3024_upper
  lower := (Primitive.Addresses.material3024 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3024_pa_checked.trans (by decide +kernel)
    · exact v3024_pb_checked.trans (by decide +kernel)
    · exact v3024_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 80 Primitive.Addresses.material3024
    · exact v3024_mb_checked.trans (by decide +kernel)
    · exact v3024_mg_checked.trans (by decide +kernel)
  upper_error := v3024_upper_checked
  lower_error := reuse_lower_error 38 80 Primitive.Addresses.material3024

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
