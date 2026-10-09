import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B094

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2257_pa : Scalar.QComplex := ((999998875049630676399334959398 : Int)/10^30,(-1499966490670330904634517549 : Int)/10^30)
theorem v2257_pa_checked : Scalar.distance (sourceCoefficient 26 87 1 0) v2257_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2257_pb : Scalar.QComplex := ((-647201715772925409956554 : Int)/10^30,(-431476964137968095964949873 : Int)/10^30)
theorem v2257_pb_checked : Scalar.distance (sourceCoefficient 26 87 1 1) v2257_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2257_pg : Scalar.QComplex := ((-93086317469733682889841 : Int)/10^30,(139626514017399260198 : Int)/10^30)
theorem v2257_pg_checked : Scalar.distance (sourceCoefficient 26 87 1 2) v2257_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2257_mb : Scalar.QComplex := ((-1019546661840136649906519 : Int)/10^30,(-431476244973443047163045615 : Int)/10^30)
theorem v2257_mb_checked : Scalar.distance (sourceCoefficient 26 87 3 1) v2257_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2257_mg : Scalar.QComplex := ((-93086162318050381769197 : Int)/10^30,(219955761552339313862 : Int)/10^30)
theorem v2257_mg_checked : Scalar.distance (sourceCoefficient 26 87 3 2) v2257_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2257_upper : Scalar.QComplex := ((999994796862687409599008227863 : Int)/10^30,(-3225871595792818954012877983 : Int)/10^30)
theorem v2257_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 87 5) 1) 14) v2257_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2257 : Material (26 : Basis) (87 : Basis) where
  plus := ![v2257_pa,v2257_pb,v2257_pg]
  minus := ![(Primitive.Addresses.material2257 1).one,v2257_mb,v2257_mg]
  upper := v2257_upper
  lower := (Primitive.Addresses.material2257 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2257_pa_checked.trans (by decide +kernel)
    · exact v2257_pb_checked.trans (by decide +kernel)
    · exact v2257_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 87 Primitive.Addresses.material2257
    · exact v2257_mb_checked.trans (by decide +kernel)
    · exact v2257_mg_checked.trans (by decide +kernel)
  upper_error := v2257_upper_checked
  lower_error := reuse_lower_error 26 87 Primitive.Addresses.material2257

def v2258_pa : Scalar.QComplex := ((999998857341490457228456418052 : Int)/10^30,(-1511726070892829993948118129 : Int)/10^30)
theorem v2258_pa_checked : Scalar.distance (sourceCoefficient 26 88 1 0) v2258_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2258_pb : Scalar.QComplex := ((-652275706890841941446194 : Int)/10^30,(-431476954801222239724354011 : Int)/10^30)
theorem v2258_pb_checked : Scalar.distance (sourceCoefficient 26 88 1 1) v2258_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2258_pg : Scalar.QComplex := ((-93086315638390865959129 : Int)/10^30,(140721170990157924276 : Int)/10^30)
theorem v2258_pg_checked : Scalar.distance (sourceCoefficient 26 88 1 2) v2258_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2258_mb : Scalar.QComplex := ((-1024620643011583232833619 : Int)/10^30,(-431476231258074856734414196 : Int)/10^30)
theorem v2258_mb_checked : Scalar.distance (sourceCoefficient 26 88 3 1) v2258_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2258_mg : Scalar.QComplex := ((-93086159542068580760280 : Int)/10^30,(221050416537140788294 : Int)/10^30)
theorem v2258_mg_checked : Scalar.distance (sourceCoefficient 26 88 3 2) v2258_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2258_upper : Scalar.QComplex := ((999994758858604921373652196500 : Int)/10^30,(-3237631127938161130886177037 : Int)/10^30)
theorem v2258_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 88 5) 1) 14) v2258_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2258 : Material (26 : Basis) (88 : Basis) where
  plus := ![v2258_pa,v2258_pb,v2258_pg]
  minus := ![(Primitive.Addresses.material2258 1).one,v2258_mb,v2258_mg]
  upper := v2258_upper
  lower := (Primitive.Addresses.material2258 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2258_pa_checked.trans (by decide +kernel)
    · exact v2258_pb_checked.trans (by decide +kernel)
    · exact v2258_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 88 Primitive.Addresses.material2258
    · exact v2258_mb_checked.trans (by decide +kernel)
    · exact v2258_mg_checked.trans (by decide +kernel)
  upper_error := v2258_upper_checked
  lower_error := reuse_lower_error 26 88 Primitive.Addresses.material2258

def v2259_pa : Scalar.QComplex := ((999998832889161622717652399463 : Int)/10^30,(-1527815536839069992535459122 : Int)/10^30)
theorem v2259_pa_checked : Scalar.distance (sourceCoefficient 26 89 1 0) v2259_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2259_pb : Scalar.QComplex := ((-659217944999660384274703 : Int)/10^30,(-431476941897789791787054741 : Int)/10^30)
theorem v2259_pb_checked : Scalar.distance (sourceCoefficient 26 89 1 1) v2259_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2259_pg : Scalar.QComplex := ((-93086313108415536598316 : Int)/10^30,(142218881419301567564 : Int)/10^30)
theorem v2259_pg_checked : Scalar.distance (sourceCoefficient 26 89 1 2) v2259_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2259_mb : Scalar.QComplex := ((-1031562867400408098247999 : Int)/10^30,(-431476212363808392222099201 : Int)/10^30)
theorem v2259_mb_checked : Scalar.distance (sourceCoefficient 26 89 3 1) v2259_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2259_mg : Scalar.QComplex := ((-93086155719637547447648 : Int)/10^30,(222548124225363626684 : Int)/10^30)
theorem v2259_mg_checked : Scalar.distance (sourceCoefficient 26 89 3 2) v2259_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2259_upper : Scalar.QComplex := ((999994706637353907472715817009 : Int)/10^30,(-3253720527718530333562271605 : Int)/10^30)
theorem v2259_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 89 5) 1) 14) v2259_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2259 : Material (26 : Basis) (89 : Basis) where
  plus := ![v2259_pa,v2259_pb,v2259_pg]
  minus := ![(Primitive.Addresses.material2259 1).one,v2259_mb,v2259_mg]
  upper := v2259_upper
  lower := (Primitive.Addresses.material2259 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2259_pa_checked.trans (by decide +kernel)
    · exact v2259_pb_checked.trans (by decide +kernel)
    · exact v2259_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 89 Primitive.Addresses.material2259
    · exact v2259_mb_checked.trans (by decide +kernel)
    · exact v2259_mg_checked.trans (by decide +kernel)
  upper_error := v2259_upper_checked
  lower_error := reuse_lower_error 26 89 Primitive.Addresses.material2259

def v2260_pa : Scalar.QComplex := ((999998792512603539755209086395 : Int)/10^30,(-1554018447411315954706181149 : Int)/10^30)
theorem v2260_pa_checked : Scalar.distance (sourceCoefficient 26 90 1 0) v2260_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2260_pb : Scalar.QComplex := ((-670523903839095129407102 : Int)/10^30,(-431476920564803872539096089 : Int)/10^30)
theorem v2260_pb_checked : Scalar.distance (sourceCoefficient 26 90 1 1) v2260_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2260_pg : Scalar.QComplex := ((-93086308927984626539396 : Int)/10^30,(144658015948247842656 : Int)/10^30)
theorem v2260_pg_checked : Scalar.distance (sourceCoefficient 26 90 1 2) v2260_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2260_mb : Scalar.QComplex := ((-1042868803620711613322162 : Int)/10^30,(-431476181274297139271259405 : Int)/10^30)
theorem v2260_mb_checked : Scalar.distance (sourceCoefficient 26 90 3 1) v2260_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2260_mg : Scalar.QComplex := ((-93086149434344950014767 : Int)/10^30,(224987254238585046933 : Int)/10^30)
theorem v2260_mg_checked : Scalar.distance (sourceCoefficient 26 90 3 2) v2260_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2260_upper : Scalar.QComplex := ((999994621037009422432196627394 : Int)/10^30,(-3279923329578342690009714146 : Int)/10^30)
theorem v2260_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 90 5) 1) 14) v2260_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2260 : Material (26 : Basis) (90 : Basis) where
  plus := ![v2260_pa,v2260_pb,v2260_pg]
  minus := ![(Primitive.Addresses.material2260 1).one,v2260_mb,v2260_mg]
  upper := v2260_upper
  lower := (Primitive.Addresses.material2260 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2260_pa_checked.trans (by decide +kernel)
    · exact v2260_pb_checked.trans (by decide +kernel)
    · exact v2260_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 90 Primitive.Addresses.material2260
    · exact v2260_mb_checked.trans (by decide +kernel)
    · exact v2260_mg_checked.trans (by decide +kernel)
  upper_error := v2260_upper_checked
  lower_error := reuse_lower_error 26 90 Primitive.Addresses.material2260

def v2261_pa : Scalar.QComplex := ((999998769464682445081447006665 : Int)/10^30,(-1568779500405544359751628603 : Int)/10^30)
theorem v2261_pa_checked : Scalar.distance (sourceCoefficient 26 91 1 0) v2261_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2261_pb : Scalar.QComplex := ((-676892961694966881438487 : Int)/10^30,(-431476908373221529781123183 : Int)/10^30)
theorem v2261_pb_checked : Scalar.distance (sourceCoefficient 26 91 1 1) v2261_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2261_pg : Scalar.QComplex := ((-93086306540161781329201 : Int)/10^30,(146032069166290960564 : Int)/10^30)
theorem v2261_pg_checked : Scalar.distance (sourceCoefficient 26 91 1 2) v2261_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2261_mb : Scalar.QComplex := ((-1049237848584305571974285 : Int)/10^30,(-431476163586509258096645724 : Int)/10^30)
theorem v2261_mb_checked : Scalar.distance (sourceCoefficient 26 91 3 1) v2261_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2261_mg : Scalar.QComplex := ((-93086145860776951788595 : Int)/10^30,(226361304884421782561 : Int)/10^30)
theorem v2261_mg_checked : Scalar.distance (sourceCoefficient 26 91 3 2) v2261_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2261_upper : Scalar.QComplex := ((999994572512884299158344389500 : Int)/10^30,(-3294684320809095696902006722 : Int)/10^30)
theorem v2261_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 91 5) 1) 14) v2261_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2261 : Material (26 : Basis) (91 : Basis) where
  plus := ![v2261_pa,v2261_pb,v2261_pg]
  minus := ![(Primitive.Addresses.material2261 1).one,v2261_mb,v2261_mg]
  upper := v2261_upper
  lower := (Primitive.Addresses.material2261 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2261_pa_checked.trans (by decide +kernel)
    · exact v2261_pb_checked.trans (by decide +kernel)
    · exact v2261_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 91 Primitive.Addresses.material2261
    · exact v2261_mb_checked.trans (by decide +kernel)
    · exact v2261_mg_checked.trans (by decide +kernel)
  upper_error := v2261_upper_checked
  lower_error := reuse_lower_error 26 91 Primitive.Addresses.material2261

def v2262_pa : Scalar.QComplex := ((999998718822004899954404961235 : Int)/10^30,(-1600735564914778814981165646 : Int)/10^30)
theorem v2262_pa_checked : Scalar.distance (sourceCoefficient 26 92 1 0) v2262_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2262_pb : Scalar.QComplex := ((-690681274621809194788314 : Int)/10^30,(-431476881550344945842919008 : Int)/10^30)
theorem v2262_pb_checked : Scalar.distance (sourceCoefficient 26 92 1 1) v2262_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2262_pg : Scalar.QComplex := ((-93086301289721530546736 : Int)/10^30,(149006743984991213064 : Int)/10^30)
theorem v2262_pg_checked : Scalar.distance (sourceCoefficient 26 92 1 2) v2262_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2262_mb : Scalar.QComplex := ((-1063026133230194391207041 : Int)/10^30,(-431476124864949608237869639 : Int)/10^30)
theorem v2262_mb_checked : Scalar.distance (sourceCoefficient 26 92 3 1) v2262_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2262_mg : Scalar.QComplex := ((-93086138043328261827145 : Int)/10^30,(229335974064621185330 : Int)/10^30)
theorem v2262_mg_checked : Scalar.distance (sourceCoefficient 26 92 3 2) v2262_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2262_upper : Scalar.QComplex := ((999994466717013868938215534269 : Int)/10^30,(-3326640250318858713584931684 : Int)/10^30)
theorem v2262_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 92 5) 1) 14) v2262_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2262 : Material (26 : Basis) (92 : Basis) where
  plus := ![v2262_pa,v2262_pb,v2262_pg]
  minus := ![(Primitive.Addresses.material2262 1).one,v2262_mb,v2262_mg]
  upper := v2262_upper
  lower := (Primitive.Addresses.material2262 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2262_pa_checked.trans (by decide +kernel)
    · exact v2262_pb_checked.trans (by decide +kernel)
    · exact v2262_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 92 Primitive.Addresses.material2262
    · exact v2262_mb_checked.trans (by decide +kernel)
    · exact v2262_mg_checked.trans (by decide +kernel)
  upper_error := v2262_upper_checked
  lower_error := reuse_lower_error 26 92 Primitive.Addresses.material2262

def v2263_pa : Scalar.QComplex := ((999998657393954355248170821472 : Int)/10^30,(-1638661126865011665557561391 : Int)/10^30)
theorem v2263_pa_checked : Scalar.distance (sourceCoefficient 26 93 1 0) v2263_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2263_pb : Scalar.QComplex := ((-707045288807228073510538 : Int)/10^30,(-431476848954502060069545834 : Int)/10^30)
theorem v2263_pb_checked : Scalar.distance (sourceCoefficient 26 93 1 1) v2263_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2263_pg : Scalar.QComplex := ((-93086294914569014506472 : Int)/10^30,(152537097717626046910 : Int)/10^30)
theorem v2263_pg_checked : Scalar.distance (sourceCoefficient 26 93 1 2) v2263_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2263_mb : Scalar.QComplex := ((-1079390113193798568148018 : Int)/10^30,(-431476078147711625209908342 : Int)/10^30)
theorem v2263_mb_checked : Scalar.distance (sourceCoefficient 26 93 3 1) v2263_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2263_mg : Scalar.QComplex := ((-93086128621641849513376 : Int)/10^30,(232866320981274484247 : Int)/10^30)
theorem v2263_mg_checked : Scalar.distance (sourceCoefficient 26 93 3 2) v2263_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2263_upper : Scalar.QComplex := ((999994339832975468099310220625 : Int)/10^30,(-3364565649764179557797166613 : Int)/10^30)
theorem v2263_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 93 5) 1) 14) v2263_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2263 : Material (26 : Basis) (93 : Basis) where
  plus := ![v2263_pa,v2263_pb,v2263_pg]
  minus := ![(Primitive.Addresses.material2263 1).one,v2263_mb,v2263_mg]
  upper := v2263_upper
  lower := (Primitive.Addresses.material2263 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2263_pa_checked.trans (by decide +kernel)
    · exact v2263_pb_checked.trans (by decide +kernel)
    · exact v2263_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 93 Primitive.Addresses.material2263
    · exact v2263_mb_checked.trans (by decide +kernel)
    · exact v2263_mg_checked.trans (by decide +kernel)
  upper_error := v2263_upper_checked
  lower_error := reuse_lower_error 26 93 Primitive.Addresses.material2263

def v2264_pa : Scalar.QComplex := ((999998582980845640638216521689 : Int)/10^30,(-1683459622555717772162587311 : Int)/10^30)
theorem v2264_pa_checked : Scalar.distance (sourceCoefficient 26 94 1 0) v2264_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2264_pb : Scalar.QComplex := ((-726374815956806218374652 : Int)/10^30,(-431476809385571014350401920 : Int)/10^30)
theorem v2264_pb_checked : Scalar.distance (sourceCoefficient 26 94 1 1) v2264_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2264_pg : Scalar.QComplex := ((-93086287182867404395966 : Int)/10^30,(156707227943126731582 : Int)/10^30)
theorem v2264_pg_checked : Scalar.distance (sourceCoefficient 26 94 1 2) v2264_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2264_mb : Scalar.QComplex := ((-1098719598999904978235787 : Int)/10^30,(-431476021898283952311998116 : Int)/10^30)
theorem v2264_mb_checked : Scalar.distance (sourceCoefficient 26 94 3 1) v2264_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2264_mg : Scalar.QComplex := ((-93086117291308549354955 : Int)/10^30,(237036442981934834987 : Int)/10^30)
theorem v2264_mg_checked : Scalar.distance (sourceCoefficient 26 94 3 2) v2264_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2264_upper : Scalar.QComplex := ((999994188101838108697017871499 : Int)/10^30,(-3409363950302513797134981805 : Int)/10^30)
theorem v2264_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 94 5) 1) 14) v2264_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2264 : Material (26 : Basis) (94 : Basis) where
  plus := ![v2264_pa,v2264_pb,v2264_pg]
  minus := ![(Primitive.Addresses.material2264 1).one,v2264_mb,v2264_mg]
  upper := v2264_upper
  lower := (Primitive.Addresses.material2264 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2264_pa_checked.trans (by decide +kernel)
    · exact v2264_pb_checked.trans (by decide +kernel)
    · exact v2264_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 94 Primitive.Addresses.material2264
    · exact v2264_mb_checked.trans (by decide +kernel)
    · exact v2264_mg_checked.trans (by decide +kernel)
  upper_error := v2264_upper_checked
  lower_error := reuse_lower_error 26 94 Primitive.Addresses.material2264

def v2265_pa : Scalar.QComplex := ((999998507466875737848756742796 : Int)/10^30,(-1727733781827853091879455229 : Int)/10^30)
theorem v2265_pa_checked : Scalar.distance (sourceCoefficient 26 95 1 0) v2265_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2265_pb : Scalar.QComplex := ((-745478102777166934729656 : Int)/10^30,(-431476769145376657014293588 : Int)/10^30)
theorem v2265_pb_checked : Scalar.distance (sourceCoefficient 26 95 1 1) v2265_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2265_pg : Scalar.QComplex := ((-93086279327519410952610 : Int)/10^30,(160828549460756410602 : Int)/10^30)
theorem v2265_pg_checked : Scalar.distance (sourceCoefficient 26 95 1 2) v2265_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2265_mb : Scalar.QComplex := ((-1117822843981763568727760 : Int)/10^30,(-431475965172828432367596992 : Int)/10^30)
theorem v2265_mb_checked : Scalar.distance (sourceCoefficient 26 95 3 1) v2265_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2265_mg : Scalar.QComplex := ((-93086105879448628532962 : Int)/10^30,(241157756186196632694 : Int)/10^30)
theorem v2265_mg_checked : Scalar.distance (sourceCoefficient 26 95 3 2) v2265_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2265_upper : Scalar.QComplex := ((999994036174798291743505383171 : Int)/10^30,(-3453637913303228210712465396 : Int)/10^30)
theorem v2265_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 95 5) 1) 14) v2265_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2265 : Material (26 : Basis) (95 : Basis) where
  plus := ![v2265_pa,v2265_pb,v2265_pg]
  minus := ![(Primitive.Addresses.material2265 1).one,v2265_mb,v2265_mg]
  upper := v2265_upper
  lower := (Primitive.Addresses.material2265 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2265_pa_checked.trans (by decide +kernel)
    · exact v2265_pb_checked.trans (by decide +kernel)
    · exact v2265_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 95 Primitive.Addresses.material2265
    · exact v2265_mb_checked.trans (by decide +kernel)
    · exact v2265_mg_checked.trans (by decide +kernel)
  upper_error := v2265_upper_checked
  lower_error := reuse_lower_error 26 95 Primitive.Addresses.material2265

def v2266_pa : Scalar.QComplex := ((999998470502097054520067861031 : Int)/10^30,(-1748997846347194548099130063 : Int)/10^30)
theorem v2266_pa_checked : Scalar.distance (sourceCoefficient 26 96 1 0) v2266_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2266_pb : Scalar.QComplex := ((-754653059721025848172178 : Int)/10^30,(-431476749417876171840461843 : Int)/10^30)
theorem v2266_pb_checked : Scalar.distance (sourceCoefficient 26 96 1 1) v2266_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2266_pg : Scalar.QComplex := ((-93086275479066403968650 : Int)/10^30,(162807944351778274891 : Int)/10^30)
theorem v2266_pg_checked : Scalar.distance (sourceCoefficient 26 96 1 2) v2266_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2266_mb : Scalar.QComplex := ((-1126997780485422270659033 : Int)/10^30,(-431475937527760674814673601 : Int)/10^30)
theorem v2266_mb_checked : Scalar.distance (sourceCoefficient 26 96 3 1) v2266_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2266_mg : Scalar.QComplex := ((-93086100322868412188609 : Int)/10^30,(243137147019157699102 : Int)/10^30)
theorem v2266_mg_checked : Scalar.distance (sourceCoefficient 26 96 3 2) v2266_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2266_upper : Scalar.QComplex := ((999993962510228363591322106198 : Int)/10^30,(-3474901882354388828957416475 : Int)/10^30)
theorem v2266_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 96 5) 1) 14) v2266_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2266 : Material (26 : Basis) (96 : Basis) where
  plus := ![v2266_pa,v2266_pb,v2266_pg]
  minus := ![(Primitive.Addresses.material2266 1).one,v2266_mb,v2266_mg]
  upper := v2266_upper
  lower := (Primitive.Addresses.material2266 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2266_pa_checked.trans (by decide +kernel)
    · exact v2266_pb_checked.trans (by decide +kernel)
    · exact v2266_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 96 Primitive.Addresses.material2266
    · exact v2266_mb_checked.trans (by decide +kernel)
    · exact v2266_mg_checked.trans (by decide +kernel)
  upper_error := v2266_upper_checked
  lower_error := reuse_lower_error 26 96 Primitive.Addresses.material2266

def v2267_pa : Scalar.QComplex := ((999998339865174813826095442256 : Int)/10^30,(-1822159953002125994530429887 : Int)/10^30)
theorem v2267_pa_checked : Scalar.distance (sourceCoefficient 26 97 1 0) v2267_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2267_pb : Scalar.QComplex := ((-786220831372613358247136 : Int)/10^30,(-431476679555317607556159588 : Int)/10^30)
theorem v2267_pb_checked : Scalar.distance (sourceCoefficient 26 97 1 1) v2267_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2267_pg : Scalar.QComplex := ((-93086261862772739805645 : Int)/10^30,(169618340130327009527 : Int)/10^30)
theorem v2267_pg_checked : Scalar.distance (sourceCoefficient 26 97 1 2) v2267_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2267_mb : Scalar.QComplex := ((-1158565480094644128268825 : Int)/10^30,(-431475840423662947890768465 : Int)/10^30)
theorem v2267_mb_checked : Scalar.distance (sourceCoefficient 26 97 3 1) v2267_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2267_mg : Scalar.QComplex := ((-93086080829514989946029 : Int)/10^30,(249947528511636657850 : Int)/10^30)
theorem v2267_mg_checked : Scalar.distance (sourceCoefficient 26 97 3 2) v2267_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2267_upper : Scalar.QComplex := ((999993705602341819304321033948 : Int)/10^30,(-3548063654575480139198067212 : Int)/10^30)
theorem v2267_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 97 5) 1) 14) v2267_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2267 : Material (26 : Basis) (97 : Basis) where
  plus := ![v2267_pa,v2267_pb,v2267_pg]
  minus := ![(Primitive.Addresses.material2267 1).one,v2267_mb,v2267_mg]
  upper := v2267_upper
  lower := (Primitive.Addresses.material2267 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2267_pa_checked.trans (by decide +kernel)
    · exact v2267_pb_checked.trans (by decide +kernel)
    · exact v2267_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 97 Primitive.Addresses.material2267
    · exact v2267_mb_checked.trans (by decide +kernel)
    · exact v2267_mg_checked.trans (by decide +kernel)
  upper_error := v2267_upper_checked
  lower_error := reuse_lower_error 26 97 Primitive.Addresses.material2267

def v2268_pa : Scalar.QComplex := ((999999864839169975425675124281 : Int)/10^30,(-519924650099126072220022742 : Int)/10^30)
theorem v2268_pa_checked : Scalar.distance (sourceCoefficient 27 28 1 0) v2268_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2268_pb : Scalar.QComplex := ((-224335799130175518503157 : Int)/10^30,(-431477462678470885570971230 : Int)/10^30)
theorem v2268_pb_checked : Scalar.distance (sourceCoefficient 27 28 1 1) v2268_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2268_pg : Scalar.QComplex := ((-93086417314978588678440 : Int)/10^30,(48397929492975795143 : Int)/10^30)
theorem v2268_pg_checked : Scalar.distance (sourceCoefficient 27 28 1 2) v2268_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2268_mb : Scalar.QComplex := ((-596681332867693928354531 : Int)/10^30,(-431477108428001096153106079 : Int)/10^30)
theorem v2268_mb_checked : Scalar.distance (sourceCoefficient 27 28 3 1) v2268_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2268_mg : Scalar.QComplex := ((-93086340889417772265626 : Int)/10^30,(128727297158436710329 : Int)/10^30)
theorem v2268_mg_checked : Scalar.distance (sourceCoefficient 27 28 3 2) v2268_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2268_upper : Scalar.QComplex := ((999997478114060658014990550934 : Int)/10^30,(-2245832923165763675347224299 : Int)/10^30)
theorem v2268_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 28 5) 1) 14) v2268_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2268 : Material (27 : Basis) (28 : Basis) where
  plus := ![v2268_pa,v2268_pb,v2268_pg]
  minus := ![(Primitive.Addresses.material2268 1).one,v2268_mb,v2268_mg]
  upper := v2268_upper
  lower := (Primitive.Addresses.material2268 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2268_pa_checked.trans (by decide +kernel)
    · exact v2268_pb_checked.trans (by decide +kernel)
    · exact v2268_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 28 Primitive.Addresses.material2268
    · exact v2268_mb_checked.trans (by decide +kernel)
    · exact v2268_mg_checked.trans (by decide +kernel)
  upper_error := v2268_upper_checked
  lower_error := reuse_lower_error 27 28 Primitive.Addresses.material2268

def v2269_pa : Scalar.QComplex := ((999999857587478955715752388908 : Int)/10^30,(-533690005346963889564595379 : Int)/10^30)
theorem v2269_pa_checked : Scalar.distance (sourceCoefficient 27 29 1 0) v2269_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2269_pb : Scalar.QComplex := ((-230275240473706572471767 : Int)/10^30,(-431477459522446827380728830 : Int)/10^30)
theorem v2269_pb_checked : Scalar.distance (sourceCoefficient 27 29 1 1) v2269_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2269_pg : Scalar.QComplex := ((-93086416637023199778549 : Int)/10^30,(49679297267696587458 : Int)/10^30)
theorem v2269_pg_checked : Scalar.distance (sourceCoefficient 27 29 1 2) v2269_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2269_mb : Scalar.QComplex := ((-602620769276192904076272 : Int)/10^30,(-431477100146507836135511165 : Int)/10^30)
theorem v2269_mb_checked : Scalar.distance (sourceCoefficient 27 29 3 1) v2269_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2269_mg : Scalar.QComplex := ((-93086339105699956877720 : Int)/10^30,(130008663871000752072 : Int)/10^30)
theorem v2269_mg_checked : Scalar.distance (sourceCoefficient 27 29 3 2) v2269_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2269_upper : Scalar.QComplex := ((999997447104626064352049724475 : Int)/10^30,(-2259598245395961011503283433 : Int)/10^30)
theorem v2269_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 29 5) 1) 14) v2269_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2269 : Material (27 : Basis) (29 : Basis) where
  plus := ![v2269_pa,v2269_pb,v2269_pg]
  minus := ![(Primitive.Addresses.material2269 1).one,v2269_mb,v2269_mg]
  upper := v2269_upper
  lower := (Primitive.Addresses.material2269 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2269_pa_checked.trans (by decide +kernel)
    · exact v2269_pb_checked.trans (by decide +kernel)
    · exact v2269_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 29 Primitive.Addresses.material2269
    · exact v2269_mb_checked.trans (by decide +kernel)
    · exact v2269_mg_checked.trans (by decide +kernel)
  upper_error := v2269_upper_checked
  lower_error := reuse_lower_error 27 29 Primitive.Addresses.material2269

def v2270_pa : Scalar.QComplex := ((999999854789988176493840764542 : Int)/10^30,(-538906302209451605786052535 : Int)/10^30)
theorem v2270_pa_checked : Scalar.distance (sourceCoefficient 27 30 1 0) v2270_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2270_pb : Scalar.QComplex := ((-232525955303209799191879 : Int)/10^30,(-431477458298009351985118194 : Int)/10^30)
theorem v2270_pb_checked : Scalar.distance (sourceCoefficient 27 30 1 1) v2270_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2270_pg : Scalar.QComplex := ((-93086416374739667368836 : Int)/10^30,(50164863718880753484 : Int)/10^30)
theorem v2270_pg_checked : Scalar.distance (sourceCoefficient 27 30 1 2) v2270_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2270_mb : Scalar.QComplex := ((-604871482211017742373443 : Int)/10^30,(-431477096979805287225595231 : Int)/10^30)
theorem v2270_mb_checked : Scalar.distance (sourceCoefficient 27 30 3 1) v2270_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2270_mg : Scalar.QComplex := ((-93086338424394543857360 : Int)/10^30,(130494229915047461181 : Int)/10^30)
theorem v2270_mg_checked : Scalar.distance (sourceCoefficient 27 30 3 2) v2270_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2270_upper : Scalar.QComplex := ((999997435304284285765022037673 : Int)/10^30,(-2264814529661172001766044985 : Int)/10^30)
theorem v2270_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 30 5) 1) 14) v2270_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2270 : Material (27 : Basis) (30 : Basis) where
  plus := ![v2270_pa,v2270_pb,v2270_pg]
  minus := ![(Primitive.Addresses.material2270 1).one,v2270_mb,v2270_mg]
  upper := v2270_upper
  lower := (Primitive.Addresses.material2270 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2270_pa_checked.trans (by decide +kernel)
    · exact v2270_pb_checked.trans (by decide +kernel)
    · exact v2270_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 30 Primitive.Addresses.material2270
    · exact v2270_mb_checked.trans (by decide +kernel)
    · exact v2270_mg_checked.trans (by decide +kernel)
  upper_error := v2270_upper_checked
  lower_error := reuse_lower_error 27 30 Primitive.Addresses.material2270

def v2271_pa : Scalar.QComplex := ((999999848749235031286358799101 : Int)/10^30,(-550001370053414847655644288 : Int)/10^30)
theorem v2271_pa_checked : Scalar.distance (sourceCoefficient 27 31 1 0) v2271_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2271_pb : Scalar.QComplex := ((-237313227643833252047044 : Int)/10^30,(-431477455641571822198995753 : Int)/10^30)
theorem v2271_pb_checked : Scalar.distance (sourceCoefficient 27 31 1 1) v2271_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2271_pg : Scalar.QComplex := ((-93086415807035311982519 : Int)/10^30,(51197663970917114160 : Int)/10^30)
theorem v2271_pg_checked : Scalar.distance (sourceCoefficient 27 31 1 2) v2271_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2271_mb : Scalar.QComplex := ((-609658750476734966959743 : Int)/10^30,(-431477090192168327336905207 : Int)/10^30)
theorem v2271_mb_checked : Scalar.distance (sourceCoefficient 27 31 3 1) v2271_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2271_mg : Scalar.QComplex := ((-93086336965430297942553 : Int)/10^30,(131527029292621796477 : Int)/10^30)
theorem v2271_mg_checked : Scalar.distance (sourceCoefficient 27 31 3 2) v2271_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2271_upper : Scalar.QComplex := ((999997410114459575561368875694 : Int)/10^30,(-2275909570554543092490829488 : Int)/10^30)
theorem v2271_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 31 5) 1) 14) v2271_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2271 : Material (27 : Basis) (31 : Basis) where
  plus := ![v2271_pa,v2271_pb,v2271_pg]
  minus := ![(Primitive.Addresses.material2271 1).one,v2271_mb,v2271_mg]
  upper := v2271_upper
  lower := (Primitive.Addresses.material2271 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2271_pa_checked.trans (by decide +kernel)
    · exact v2271_pb_checked.trans (by decide +kernel)
    · exact v2271_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 31 Primitive.Addresses.material2271
    · exact v2271_mb_checked.trans (by decide +kernel)
    · exact v2271_mg_checked.trans (by decide +kernel)
  upper_error := v2271_upper_checked
  lower_error := reuse_lower_error 27 31 Primitive.Addresses.material2271

def v2272_pa : Scalar.QComplex := ((999999846110973434558821606013 : Int)/10^30,(-554777459391646390210968253 : Int)/10^30)
theorem v2272_pa_checked : Scalar.distance (sourceCoefficient 27 32 1 0) v2272_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2272_pb : Scalar.QComplex := ((-239374002816141927028731 : Int)/10^30,(-431477454476251640707762424 : Int)/10^30)
theorem v2272_pb_checked : Scalar.distance (sourceCoefficient 27 32 1 1) v2272_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2272_pg : Scalar.QComplex := ((-93086415558539763801560 : Int)/10^30,(51642253074617769843 : Int)/10^30)
theorem v2272_pg_checked : Scalar.distance (sourceCoefficient 27 32 1 2) v2272_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2272_mb : Scalar.QComplex := ((-611719523876104030658586 : Int)/10^30,(-431477087248492419913594738 : Int)/10^30)
theorem v2272_mb_checked : Scalar.distance (sourceCoefficient 27 32 3 1) v2272_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2272_mg : Scalar.QComplex := ((-93086336333274469344098 : Int)/10^30,(131971618016341143870 : Int)/10^30)
theorem v2272_mg_checked : Scalar.distance (sourceCoefficient 27 32 3 2) v2272_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2272_upper : Scalar.QComplex := ((999997399233104993867065454417 : Int)/10^30,(-2280685648225950429885465099 : Int)/10^30)
theorem v2272_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 32 5) 1) 14) v2272_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2272 : Material (27 : Basis) (32 : Basis) where
  plus := ![v2272_pa,v2272_pb,v2272_pg]
  minus := ![(Primitive.Addresses.material2272 1).one,v2272_mb,v2272_mg]
  upper := v2272_upper
  lower := (Primitive.Addresses.material2272 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2272_pa_checked.trans (by decide +kernel)
    · exact v2272_pb_checked.trans (by decide +kernel)
    · exact v2272_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 32 Primitive.Addresses.material2272
    · exact v2272_mb_checked.trans (by decide +kernel)
    · exact v2272_mg_checked.trans (by decide +kernel)
  upper_error := v2272_upper_checked
  lower_error := reuse_lower_error 27 32 Primitive.Addresses.material2272

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
