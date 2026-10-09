import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B190
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B191

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4577_pa : Scalar.QComplex := ((999997018771321915002955416819 : Int)/10^30,(-2441812537531405798795158109 : Int)/10^30)
theorem v4577_pa_checked : Scalar.distance (sourceCoefficient 78 93 1 0) v4577_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4577_pb : Scalar.QComplex := ((-1053587201032292553319627 : Int)/10^30,(-431476226718474336191686646 : Int)/10^30)
theorem v4577_pb_checked : Scalar.distance (sourceCoefficient 78 93 1 1) v4577_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4577_pg : Scalar.QComplex := ((-93086151527585937798904 : Int)/10^30,(227299609502721932007 : Int)/10^30)
theorem v4577_pg_checked : Scalar.distance (sourceCoefficient 78 93 1 2) v4577_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4577_mb : Scalar.QComplex := ((-1425931359423803923441151 : Int)/10^30,(-431475156861853006354849835 : Int)/10^30)
theorem v4577_mb_checked : Scalar.distance (sourceCoefficient 78 93 3 1) v4577_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4577_mg : Scalar.QComplex := ((-93085920718031670330225 : Int)/10^30,(307628681192361930961 : Int)/10^30)
theorem v4577_mg_checked : Scalar.distance (sourceCoefficient 78 93 3 2) v4577_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4577_upper : Scalar.QComplex := ((999991315046310080396909641069 : Int)/10^30,(-4167713036116883387622824660 : Int)/10^30)
theorem v4577_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 93 5) 1) 14) v4577_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4577 : Material (78 : Basis) (93 : Basis) where
  plus := ![v4577_pa,v4577_pb,v4577_pg]
  minus := ![(Primitive.Addresses.material4577 1).one,v4577_mb,v4577_mg]
  upper := v4577_upper
  lower := (Primitive.Addresses.material4577 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4577_pa_checked.trans (by decide +kernel)
    · exact v4577_pb_checked.trans (by decide +kernel)
    · exact v4577_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 93 Primitive.Addresses.material4577
    · exact v4577_mb_checked.trans (by decide +kernel)
    · exact v4577_mg_checked.trans (by decide +kernel)
  upper_error := v4577_upper_checked
  lower_error := reuse_lower_error 78 93 Primitive.Addresses.material4577

def v4578_pa : Scalar.QComplex := ((999996908378190207315510622156 : Int)/10^30,(-2486610959008255113614221952 : Int)/10^30)
theorem v4578_pa_checked : Scalar.distance (sourceCoefficient 78 94 1 0) v4578_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4578_pb : Scalar.QComplex := ((-1072916706834131448464979 : Int)/10^30,(-431476176799829918331467839 : Int)/10^30)
theorem v4578_pb_checked : Scalar.distance (sourceCoefficient 78 94 1 1) v4578_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4578_pg : Scalar.QComplex := ((-93086141004841194243896 : Int)/10^30,(231469733971303674925 : Int)/10^30)
theorem v4578_pg_checked : Scalar.distance (sourceCoefficient 78 94 1 2) v4578_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4578_mb : Scalar.QComplex := ((-1445260814950842526177955 : Int)/10^30,(-431475090262734237124664456 : Int)/10^30)
theorem v4578_mb_checked : Scalar.distance (sourceCoefficient 78 94 3 1) v4578_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4578_mg : Scalar.QComplex := ((-93085906596661243921982 : Int)/10^30,(311798795027560963264 : Int)/10^30)
theorem v4578_mg_checked : Scalar.distance (sourceCoefficient 78 94 3 2) v4578_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4578_upper : Scalar.QComplex := ((999991127335331402319058715883 : Int)/10^30,(-4212511200343215764133169738 : Int)/10^30)
theorem v4578_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 94 5) 1) 14) v4578_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4578 : Material (78 : Basis) (94 : Basis) where
  plus := ![v4578_pa,v4578_pb,v4578_pg]
  minus := ![(Primitive.Addresses.material4578 1).one,v4578_mb,v4578_mg]
  upper := v4578_upper
  lower := (Primitive.Addresses.material4578 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4578_pa_checked.trans (by decide +kernel)
    · exact v4578_pb_checked.trans (by decide +kernel)
    · exact v4578_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 94 Primitive.Addresses.material4578
    · exact v4578_mb_checked.trans (by decide +kernel)
    · exact v4578_mg_checked.trans (by decide +kernel)
  upper_error := v4578_upper_checked
  lower_error := reuse_lower_error 78 94 Primitive.Addresses.material4578

def v4579_pa : Scalar.QComplex := ((999996797305320043265543280329 : Int)/10^30,(-2530885043351486537499374118 : Int)/10^30)
theorem v4579_pa_checked : Scalar.distance (sourceCoefficient 78 95 1 0) v4579_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4579_pb : Scalar.QComplex := ((-1092019972101068573605944 : Int)/10^30,(-431476126331058913035858303 : Int)/10^30)
theorem v4579_pb_checked : Scalar.distance (sourceCoefficient 78 95 1 1) v4579_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4579_pg : Scalar.QComplex := ((-93086130391117420631937 : Int)/10^30,(235591049676546786094 : Int)/10^30)
theorem v4579_pg_checked : Scalar.distance (sourceCoefficient 78 95 1 2) v4579_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4579_mb : Scalar.QComplex := ((-1464364029552484581582535 : Int)/10^30,(-431475023308724477421146265 : Int)/10^30)
theorem v4579_mb_checked : Scalar.distance (sourceCoefficient 78 95 3 1) v4579_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4579_mg : Scalar.QComplex := ((-93085892426431585828582 : Int)/10^30,(315920100039084291685 : Int)/10^30)
theorem v4579_mg_checked : Scalar.distance (sourceCoefficient 78 95 3 2) v4579_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4579_upper : Scalar.QComplex := ((999990939849573605400563109519 : Int)/10^30,(-4256785027043701906976410716 : Int)/10^30)
theorem v4579_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 95 5) 1) 14) v4579_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4579 : Material (78 : Basis) (95 : Basis) where
  plus := ![v4579_pa,v4579_pb,v4579_pg]
  minus := ![(Primitive.Addresses.material4579 1).one,v4579_mb,v4579_mg]
  upper := v4579_upper
  lower := (Primitive.Addresses.material4579 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4579_pa_checked.trans (by decide +kernel)
    · exact v4579_pb_checked.trans (by decide +kernel)
    · exact v4579_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 95 Primitive.Addresses.material4579
    · exact v4579_mb_checked.trans (by decide +kernel)
    · exact v4579_mg_checked.trans (by decide +kernel)
  upper_error := v4579_upper_checked
  lower_error := reuse_lower_error 78 95 Primitive.Addresses.material4579

def v4580_pa : Scalar.QComplex := ((999996743262255699118069382599 : Int)/10^30,(-2552149071324210228339963765 : Int)/10^30)
theorem v4580_pa_checked : Scalar.distance (sourceCoefficient 78 96 1 0) v4580_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4580_pb : Scalar.QComplex := ((-1101194918532232272707715 : Int)/10^30,(-431476101690961253023011678 : Int)/10^30)
theorem v4580_pb_checked : Scalar.distance (sourceCoefficient 78 96 1 1) v4580_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4580_pg : Scalar.QComplex := ((-93086125217867273229439 : Int)/10^30,(237570441732573628592 : Int)/10^30)
theorem v4580_pg_checked : Scalar.distance (sourceCoefficient 78 96 1 2) v4580_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4580_mb : Scalar.QComplex := ((-1473538951304101876807247 : Int)/10^30,(-431474990751070446196148727 : Int)/10^30)
theorem v4580_mb_checked : Scalar.distance (sourceCoefficient 78 96 3 1) v4580_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4580_mg : Scalar.QComplex := ((-93085885545057168821233 : Int)/10^30,(317899486893811126368 : Int)/10^30)
theorem v4580_mg_checked : Scalar.distance (sourceCoefficient 78 96 3 2) v4580_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4580_upper : Scalar.QComplex := ((999990849106806528676710027403 : Int)/10^30,(-4278048930072727471135595820 : Int)/10^30)
theorem v4580_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 96 5) 1) 14) v4580_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4580 : Material (78 : Basis) (96 : Basis) where
  plus := ![v4580_pa,v4580_pb,v4580_pg]
  minus := ![(Primitive.Addresses.material4580 1).one,v4580_mb,v4580_mg]
  upper := v4580_upper
  lower := (Primitive.Addresses.material4580 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4580_pa_checked.trans (by decide +kernel)
    · exact v4580_pb_checked.trans (by decide +kernel)
    · exact v4580_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 96 Primitive.Addresses.material4580
    · exact v4580_mb_checked.trans (by decide +kernel)
    · exact v4580_mg_checked.trans (by decide +kernel)
  upper_error := v4580_upper_checked
  lower_error := reuse_lower_error 78 96 Primitive.Addresses.material4580

def v4581_pa : Scalar.QComplex := ((999996553865008866021660034540 : Int)/10^30,(-2625311049460916652458255860 : Int)/10^30)
theorem v4581_pa_checked : Scalar.distance (sourceCoefficient 78 97 1 0) v4581_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4581_pb : Scalar.QComplex := ((-1132762653215339498918149 : Int)/10^30,(-431476014925898071499988035 : Int)/10^30)
theorem v4581_pb_checked : Scalar.distance (sourceCoefficient 78 97 1 1) v4581_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4581_pg : Scalar.QComplex := ((-93086107043416475728580 : Int)/10^30,(244380827541703887032 : Int)/10^30)
theorem v4581_pg_checked : Scalar.distance (sourceCoefficient 78 97 1 2) v4581_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4581_mb : Scalar.QComplex := ((-1505106599358756991478891 : Int)/10^30,(-431474876744506297741960255 : Int)/10^30)
theorem v4581_mb_checked : Scalar.distance (sourceCoefficient 78 97 3 1) v4581_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4581_mg : Scalar.QComplex := ((-93085861493556913610156 : Int)/10^30,(324709854483391006696 : Int)/10^30)
theorem v4581_mg_checked : Scalar.distance (sourceCoefficient 78 97 3 2) v4581_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4581_upper : Scalar.QComplex := ((999990533438904719385586024400 : Int)/10^30,(-4351210472360795620381910778 : Int)/10^30)
theorem v4581_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 78 97 5) 1) 14) v4581_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4581 : Material (78 : Basis) (97 : Basis) where
  plus := ![v4581_pa,v4581_pb,v4581_pg]
  minus := ![(Primitive.Addresses.material4581 1).one,v4581_mb,v4581_mg]
  upper := v4581_upper
  lower := (Primitive.Addresses.material4581 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4581_pa_checked.trans (by decide +kernel)
    · exact v4581_pb_checked.trans (by decide +kernel)
    · exact v4581_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 78 97 Primitive.Addresses.material4581
    · exact v4581_mb_checked.trans (by decide +kernel)
    · exact v4581_mg_checked.trans (by decide +kernel)
  upper_error := v4581_upper_checked
  lower_error := reuse_lower_error 78 97 Primitive.Addresses.material4581

def v4582_pa : Scalar.QComplex := ((999997733233364161081314713567 : Int)/10^30,(-2129208334909211278067730174 : Int)/10^30)
theorem v4582_pa_checked : Scalar.distance (sourceCoefficient 79 80 1 0) v4582_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4582_pb : Scalar.QComplex := ((-918705534028932587158748 : Int)/10^30,(-431476542936345913597478402 : Int)/10^30)
theorem v4582_pb_checked : Scalar.distance (sourceCoefficient 79 80 1 1) v4582_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4582_pg : Scalar.QComplex := ((-93086218891173754877365 : Int)/10^30,(198200402402329813425 : Int)/10^30)
theorem v4582_pg_checked : Scalar.distance (sourceCoefficient 79 80 1 2) v4582_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4582_mb : Scalar.QComplex := ((-1291050015524834226391048 : Int)/10^30,(-431475589476410620521840228 : Int)/10^30)
theorem v4582_mb_checked : Scalar.distance (sourceCoefficient 79 80 3 1) v4582_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4582_mg : Scalar.QComplex := ((-93086013192899552867873 : Int)/10^30,(278529543058676858086 : Int)/10^30)
theorem v4582_mg_checked : Scalar.distance (sourceCoefficient 79 80 3 2) v4582_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4582_upper : Scalar.QComplex := ((999992569033782713365968766924 : Int)/10^30,(-3855110532178597030069222367 : Int)/10^30)
theorem v4582_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 80 5) 1) 14) v4582_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4582 : Material (79 : Basis) (80 : Basis) where
  plus := ![v4582_pa,v4582_pb,v4582_pg]
  minus := ![(Primitive.Addresses.material4582 1).one,v4582_mb,v4582_mg]
  upper := v4582_upper
  lower := (Primitive.Addresses.material4582 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4582_pa_checked.trans (by decide +kernel)
    · exact v4582_pb_checked.trans (by decide +kernel)
    · exact v4582_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 80 Primitive.Addresses.material4582
    · exact v4582_mb_checked.trans (by decide +kernel)
    · exact v4582_mg_checked.trans (by decide +kernel)
  upper_error := v4582_upper_checked
  lower_error := reuse_lower_error 79 80 Primitive.Addresses.material4582

def v4583_pa : Scalar.QComplex := ((999997677035612452061656332734 : Int)/10^30,(-2155440414145640647560260958 : Int)/10^30)
theorem v4583_pa_checked : Scalar.distance (sourceCoefficient 79 81 1 0) v4583_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4583_pb : Scalar.QComplex := ((-930024086370907380928665 : Int)/10^30,(-431476518605925452377675865 : Int)/10^30)
theorem v4583_pb_checked : Scalar.distance (sourceCoefficient 79 81 1 1) v4583_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4583_pg : Scalar.QComplex := ((-93086213651042219014518 : Int)/10^30,(200642252988060357167 : Int)/10^30)
theorem v4583_pg_checked : Scalar.distance (sourceCoefficient 79 81 1 2) v4583_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4583_mb : Scalar.QComplex := ((-1302368542656337643274224 : Int)/10^30,(-431475555378598316179263386 : Int)/10^30)
theorem v4583_mb_checked : Scalar.distance (sourceCoefficient 79 81 3 1) v4583_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4583_mg : Scalar.QComplex := ((-93086005845562889527872 : Int)/10^30,(280971388213197321990 : Int)/10^30)
theorem v4583_mg_checked : Scalar.distance (sourceCoefficient 79 81 3 2) v4583_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4583_upper : Scalar.QComplex := ((999992467561925697857635576265 : Int)/10^30,(-3881342475353204583828426598 : Int)/10^30)
theorem v4583_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 81 5) 1) 14) v4583_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4583 : Material (79 : Basis) (81 : Basis) where
  plus := ![v4583_pa,v4583_pb,v4583_pg]
  minus := ![(Primitive.Addresses.material4583 1).one,v4583_mb,v4583_mg]
  upper := v4583_upper
  lower := (Primitive.Addresses.material4583 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4583_pa_checked.trans (by decide +kernel)
    · exact v4583_pb_checked.trans (by decide +kernel)
    · exact v4583_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 81 Primitive.Addresses.material4583
    · exact v4583_mb_checked.trans (by decide +kernel)
    · exact v4583_mg_checked.trans (by decide +kernel)
  upper_error := v4583_upper_checked
  lower_error := reuse_lower_error 79 81 Primitive.Addresses.material4583

def v4584_pa : Scalar.QComplex := ((999997655560572424587173422256 : Int)/10^30,(-2165380649852260059450586084 : Int)/10^30)
theorem v4584_pa_checked : Scalar.distance (sourceCoefficient 79 82 1 0) v4584_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4584_pb : Scalar.QComplex := ((-934313074507323522583706 : Int)/10^30,(-431476509282864544965815434 : Int)/10^30)
theorem v4584_pb_checked : Scalar.distance (sourceCoefficient 79 82 1 1) v4584_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4584_pg : Scalar.QComplex := ((-93086211645851966121067 : Int)/10^30,(201567554028900934121 : Int)/10^30)
theorem v4584_pg_checked : Scalar.distance (sourceCoefficient 79 82 1 2) v4584_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4584_mb : Scalar.QComplex := ((-1306657521150385817279889 : Int)/10^30,(-431475542354337287296832694 : Int)/10^30)
theorem v4584_mb_checked : Scalar.distance (sourceCoefficient 79 82 3 1) v4584_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4584_mg : Scalar.QComplex := ((-93086003041880259024843 : Int)/10^30,(281896687179117155262 : Int)/10^30)
theorem v4584_mg_checked : Scalar.distance (sourceCoefficient 79 82 3 2) v4584_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4584_upper : Scalar.QComplex := ((999992428930972596446588211061 : Int)/10^30,(-3891282659191039685810855273 : Int)/10^30)
theorem v4584_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 82 5) 1) 14) v4584_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4584 : Material (79 : Basis) (82 : Basis) where
  plus := ![v4584_pa,v4584_pb,v4584_pg]
  minus := ![(Primitive.Addresses.material4584 1).one,v4584_mb,v4584_mg]
  upper := v4584_upper
  lower := (Primitive.Addresses.material4584 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4584_pa_checked.trans (by decide +kernel)
    · exact v4584_pb_checked.trans (by decide +kernel)
    · exact v4584_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 82 Primitive.Addresses.material4584
    · exact v4584_mb_checked.trans (by decide +kernel)
    · exact v4584_mg_checked.trans (by decide +kernel)
  upper_error := v4584_upper_checked
  lower_error := reuse_lower_error 79 82 Primitive.Addresses.material4584

def v4585_pa : Scalar.QComplex := ((999997626087289939746478114792 : Int)/10^30,(-2178949238660449395406456808 : Int)/10^30)
theorem v4585_pa_checked : Scalar.distance (sourceCoefficient 79 83 1 0) v4585_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4585_pb : Scalar.QComplex := ((-940167615348083948001638 : Int)/10^30,(-431476496464973588762090341 : Int)/10^30)
theorem v4585_pb_checked : Scalar.distance (sourceCoefficient 79 83 1 1) v4585_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4585_pg : Scalar.QComplex := ((-93086208891412626378665 : Int)/10^30,(202830605495883473269 : Int)/10^30)
theorem v4585_pg_checked : Scalar.distance (sourceCoefficient 79 83 1 2) v4585_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4585_mb : Scalar.QComplex := ((-1312512048749970523122880 : Int)/10^30,(-431475524484246036934723262 : Int)/10^30)
theorem v4585_mb_checked : Scalar.distance (sourceCoefficient 79 83 3 1) v4585_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4585_mg : Scalar.QComplex := ((-93085999197485414606536 : Int)/10^30,(283159735798850814094 : Int)/10^30)
theorem v4585_mg_checked : Scalar.distance (sourceCoefficient 79 83 3 2) v4585_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4585_upper : Scalar.QComplex := ((999992376039580658424345139377 : Int)/10^30,(-3904851176922198096839413285 : Int)/10^30)
theorem v4585_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 83 5) 1) 14) v4585_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4585 : Material (79 : Basis) (83 : Basis) where
  plus := ![v4585_pa,v4585_pb,v4585_pg]
  minus := ![(Primitive.Addresses.material4585 1).one,v4585_mb,v4585_mg]
  upper := v4585_upper
  lower := (Primitive.Addresses.material4585 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4585_pa_checked.trans (by decide +kernel)
    · exact v4585_pb_checked.trans (by decide +kernel)
    · exact v4585_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 83 Primitive.Addresses.material4585
    · exact v4585_mb_checked.trans (by decide +kernel)
    · exact v4585_mg_checked.trans (by decide +kernel)
  upper_error := v4585_upper_checked
  lower_error := reuse_lower_error 79 83 Primitive.Addresses.material4585

def v4586_pa : Scalar.QComplex := ((999997548903692847430401911981 : Int)/10^30,(-2214088211077425040362639340 : Int)/10^30)
theorem v4586_pa_checked : Scalar.distance (sourceCoefficient 79 84 1 0) v4586_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4586_pb : Scalar.QComplex := ((-955329291197761136615221 : Int)/10^30,(-431476462777776962091863267 : Int)/10^30)
theorem v4586_pb_checked : Scalar.distance (sourceCoefficient 79 84 1 1) v4586_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4586_pg : Scalar.QComplex := ((-93086201665222685177044 : Int)/10^30,(206101566895734835355 : Int)/10^30)
theorem v4586_pg_checked : Scalar.distance (sourceCoefficient 79 84 1 2) v4586_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4586_mb : Scalar.QComplex := ((-1327673689883729396282224 : Int)/10^30,(-431475477713218551807410948 : Int)/10^30)
theorem v4586_mb_checked : Scalar.distance (sourceCoefficient 79 84 3 1) v4586_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4586_mg : Scalar.QComplex := ((-93085989148605794606682 : Int)/10^30,(286430689744897292950 : Int)/10^30)
theorem v4586_mg_checked : Scalar.distance (sourceCoefficient 79 84 3 2) v4586_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4586_upper : Scalar.QComplex := ((999992238209419912985628861347 : Int)/10^30,(-3939989963791915500260263295 : Int)/10^30)
theorem v4586_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 84 5) 1) 14) v4586_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4586 : Material (79 : Basis) (84 : Basis) where
  plus := ![v4586_pa,v4586_pb,v4586_pg]
  minus := ![(Primitive.Addresses.material4586 1).one,v4586_mb,v4586_mg]
  upper := v4586_upper
  lower := (Primitive.Addresses.material4586 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4586_pa_checked.trans (by decide +kernel)
    · exact v4586_pb_checked.trans (by decide +kernel)
    · exact v4586_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 84 Primitive.Addresses.material4586
    · exact v4586_mb_checked.trans (by decide +kernel)
    · exact v4586_mg_checked.trans (by decide +kernel)
  upper_error := v4586_upper_checked
  lower_error := reuse_lower_error 79 84 Primitive.Addresses.material4586

def v4587_pa : Scalar.QComplex := ((999997370739942986849288524211 : Int)/10^30,(-2293144827745917581898688901 : Int)/10^30)
theorem v4587_pa_checked : Scalar.distance (sourceCoefficient 79 85 1 0) v4587_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4587_pb : Scalar.QComplex := ((-989440440655799045593182 : Int)/10^30,(-431476384390493542307379962 : Int)/10^30)
theorem v4587_pb_checked : Scalar.distance (sourceCoefficient 79 85 1 1) v4587_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4587_pg : Scalar.QComplex := ((-93086184917320905265980 : Int)/10^30,(213460664721353973904 : Int)/10^30)
theorem v4587_pg_checked : Scalar.distance (sourceCoefficient 79 85 1 2) v4587_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4587_mb : Scalar.QComplex := ((-1361784758995932246403838 : Int)/10^30,(-431475369889578646045419179 : Int)/10^30)
theorem v4587_mb_checked : Scalar.distance (sourceCoefficient 79 85 3 1) v4587_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4587_mg : Scalar.QComplex := ((-93085966050140268657932 : Int)/10^30,(293789770377703045067 : Int)/10^30)
theorem v4587_mg_checked : Scalar.distance (sourceCoefficient 79 85 3 2) v4587_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4587_upper : Scalar.QComplex := ((999991923601386996803108678110 : Int)/10^30,(-4019046155220394786388401100 : Int)/10^30)
theorem v4587_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 85 5) 1) 14) v4587_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4587 : Material (79 : Basis) (85 : Basis) where
  plus := ![v4587_pa,v4587_pb,v4587_pg]
  minus := ![(Primitive.Addresses.material4587 1).one,v4587_mb,v4587_mg]
  upper := v4587_upper
  lower := (Primitive.Addresses.material4587 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4587_pa_checked.trans (by decide +kernel)
    · exact v4587_pb_checked.trans (by decide +kernel)
    · exact v4587_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 85 Primitive.Addresses.material4587
    · exact v4587_mb_checked.trans (by decide +kernel)
    · exact v4587_mg_checked.trans (by decide +kernel)
  upper_error := v4587_upper_checked
  lower_error := reuse_lower_error 79 85 Primitive.Addresses.material4587

def v4588_pa : Scalar.QComplex := ((999997337188886162093353734995 : Int)/10^30,(-2307729433255290721681367931 : Int)/10^30)
theorem v4588_pa_checked : Scalar.distance (sourceCoefficient 79 86 1 0) v4588_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4588_pb : Scalar.QComplex := ((-995733369183432723956977 : Int)/10^30,(-431476369536514434741164534 : Int)/10^30)
theorem v4588_pb_checked : Scalar.distance (sourceCoefficient 79 86 1 1) v4588_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4588_pg : Scalar.QComplex := ((-93086181753457260899670 : Int)/10^30,(214818293482344249484 : Int)/10^30)
theorem v4588_pg_checked : Scalar.distance (sourceCoefficient 79 86 1 2) v4588_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4588_mb : Scalar.QComplex := ((-1368077672362106061443096 : Int)/10^30,(-431475349605091172926350514 : Int)/10^30)
theorem v4588_mb_checked : Scalar.distance (sourceCoefficient 79 86 3 1) v4588_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4588_mg : Scalar.QComplex := ((-93085961714705326937618 : Int)/10^30,(295147395902914256272 : Int)/10^30)
theorem v4588_mg_checked : Scalar.distance (sourceCoefficient 79 86 3 2) v4588_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4588_upper : Scalar.QComplex := ((999991864878674138303371782820 : Int)/10^30,(-4033630681101630896640729545 : Int)/10^30)
theorem v4588_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 86 5) 1) 14) v4588_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4588 : Material (79 : Basis) (86 : Basis) where
  plus := ![v4588_pa,v4588_pb,v4588_pg]
  minus := ![(Primitive.Addresses.material4588 1).one,v4588_mb,v4588_mg]
  upper := v4588_upper
  lower := (Primitive.Addresses.material4588 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4588_pa_checked.trans (by decide +kernel)
    · exact v4588_pb_checked.trans (by decide +kernel)
    · exact v4588_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 86 Primitive.Addresses.material4588
    · exact v4588_mb_checked.trans (by decide +kernel)
    · exact v4588_mg_checked.trans (by decide +kernel)
  upper_error := v4588_upper_checked
  lower_error := reuse_lower_error 79 86 Primitive.Addresses.material4588

def v4589_pa : Scalar.QComplex := ((999997334959715257681170520488 : Int)/10^30,(-2308695187123003113126875927 : Int)/10^30)
theorem v4589_pa_checked : Scalar.distance (sourceCoefficient 79 87 1 0) v4589_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4589_pb : Scalar.QComplex := ((-996150070205538604670632 : Int)/10^30,(-431476368548603433047733437 : Int)/10^30)
theorem v4589_pb_checked : Scalar.distance (sourceCoefficient 79 87 1 1) v4589_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4589_pg : Scalar.QComplex := ((-93086181543139127906694 : Int)/10^30,(214908192055292776083 : Int)/10^30)
theorem v4589_pg_checked : Scalar.distance (sourceCoefficient 79 87 1 2) v4589_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4589_mb : Scalar.QComplex := ((-1368494372376532406847615 : Int)/10^30,(-431475348257586324517312712 : Int)/10^30)
theorem v4589_mb_checked : Scalar.distance (sourceCoefficient 79 87 3 1) v4589_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4589_mg : Scalar.QComplex := ((-93085961426808852682540 : Int)/10^30,(295237294260894359199 : Int)/10^30)
theorem v4589_mg_checked : Scalar.distance (sourceCoefficient 79 87 3 2) v4589_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4589_upper : Scalar.QComplex := ((999991860982702990814293772210 : Int)/10^30,(-4034596429683619595336333293 : Int)/10^30)
theorem v4589_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 87 5) 1) 14) v4589_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4589 : Material (79 : Basis) (87 : Basis) where
  plus := ![v4589_pa,v4589_pb,v4589_pg]
  minus := ![(Primitive.Addresses.material4589 1).one,v4589_mb,v4589_mg]
  upper := v4589_upper
  lower := (Primitive.Addresses.material4589 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4589_pa_checked.trans (by decide +kernel)
    · exact v4589_pb_checked.trans (by decide +kernel)
    · exact v4589_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 87 Primitive.Addresses.material4589
    · exact v4589_mb_checked.trans (by decide +kernel)
    · exact v4589_mg_checked.trans (by decide +kernel)
  upper_error := v4589_upper_checked
  lower_error := reuse_lower_error 79 87 Primitive.Addresses.material4589

def v4590_pa : Scalar.QComplex := ((999997307741254378310871662553 : Int)/10^30,(-2320454749178752005297546727 : Int)/10^30)
theorem v4590_pa_checked : Scalar.distance (sourceCoefficient 79 88 1 0) v4590_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4590_pb : Scalar.QComplex := ((-1001224056097759139918544 : Int)/10^30,(-431476356476197985081765903 : Int)/10^30)
theorem v4590_pb_checked : Scalar.distance (sourceCoefficient 79 88 1 1) v4590_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4590_pg : Scalar.QComplex := ((-93086178974061498504899 : Int)/10^30,(216002847618819874138 : Int)/10^30)
theorem v4590_pg_checked : Scalar.distance (sourceCoefficient 79 88 1 2) v4590_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4590_mb : Scalar.QComplex := ((-1373568345961533921173696 : Int)/10^30,(-431475331806564070514689586 : Int)/10^30)
theorem v4590_mb_checked : Scalar.distance (sourceCoefficient 79 88 3 1) v4590_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4590_mg : Scalar.QComplex := ((-93085957913093729998299 : Int)/10^30,(296331947199832875509 : Int)/10^30)
theorem v4590_mg_checked : Scalar.distance (sourceCoefficient 79 88 3 2) v4590_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4590_upper : Scalar.QComplex := ((999991813468345361057745615152 : Int)/10^30,(-4046355927248287942353612778 : Int)/10^30)
theorem v4590_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 88 5) 1) 14) v4590_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4590 : Material (79 : Basis) (88 : Basis) where
  plus := ![v4590_pa,v4590_pb,v4590_pg]
  minus := ![(Primitive.Addresses.material4590 1).one,v4590_mb,v4590_mg]
  upper := v4590_upper
  lower := (Primitive.Addresses.material4590 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4590_pa_checked.trans (by decide +kernel)
    · exact v4590_pb_checked.trans (by decide +kernel)
    · exact v4590_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 88 Primitive.Addresses.material4590
    · exact v4590_mb_checked.trans (by decide +kernel)
    · exact v4590_mg_checked.trans (by decide +kernel)
  upper_error := v4590_upper_checked
  lower_error := reuse_lower_error 79 88 Primitive.Addresses.material4590

def v4591_pa : Scalar.QComplex := ((999997270276898188795629135702 : Int)/10^30,(-2336544190088044574910868722 : Int)/10^30)
theorem v4591_pa_checked : Scalar.distance (sourceCoefficient 79 89 1 0) v4591_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4591_pb : Scalar.QComplex := ((-1008166287004657905084356 : Int)/10^30,(-431476339829834183585572842 : Int)/10^30)
theorem v4591_pb_checked : Scalar.distance (sourceCoefficient 79 89 1 1) v4591_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4591_pg : Scalar.QComplex := ((-93086175434716885617220 : Int)/10^30,(217500556105796854908 : Int)/10^30)
theorem v4591_pg_checked : Scalar.distance (sourceCoefficient 79 89 1 2) v4591_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4591_mb : Scalar.QComplex := ((-1380510559918460607778245 : Int)/10^30,(-431475309169373861040203544 : Int)/10^30)
theorem v4591_mb_checked : Scalar.distance (sourceCoefficient 79 89 3 1) v4591_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4591_mg : Scalar.QComplex := ((-93085953081295464995474 : Int)/10^30,(297829652074849543160 : Int)/10^30)
theorem v4591_mg_checked : Scalar.distance (sourceCoefficient 79 89 3 2) v4591_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4591_upper : Scalar.QComplex := ((999991748235129583538544183203 : Int)/10^30,(-4062445279534168232810716413 : Int)/10^30)
theorem v4591_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 89 5) 1) 14) v4591_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4591 : Material (79 : Basis) (89 : Basis) where
  plus := ![v4591_pa,v4591_pb,v4591_pg]
  minus := ![(Primitive.Addresses.material4591 1).one,v4591_mb,v4591_mg]
  upper := v4591_upper
  lower := (Primitive.Addresses.material4591 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4591_pa_checked.trans (by decide +kernel)
    · exact v4591_pb_checked.trans (by decide +kernel)
    · exact v4591_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 89 Primitive.Addresses.material4591
    · exact v4591_mb_checked.trans (by decide +kernel)
    · exact v4591_mg_checked.trans (by decide +kernel)
  upper_error := v4591_upper_checked
  lower_error := reuse_lower_error 79 89 Primitive.Addresses.material4591

def v4592_pa : Scalar.QComplex := ((999997208709270907476630999509 : Int)/10^30,(-2362747059437618350017971126 : Int)/10^30)
theorem v4592_pa_checked : Scalar.distance (sourceCoefficient 79 90 1 0) v4592_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4592_pb : Scalar.QComplex := ((-1019472233986322286152583 : Int)/10^30,(-431476312401201910027481593 : Int)/10^30)
theorem v4592_pb_checked : Scalar.distance (sourceCoefficient 79 90 1 1) v4592_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4592_pg : Scalar.QComplex := ((-93086169610451873731756 : Int)/10^30,(219939687437017058728 : Int)/10^30)
theorem v4592_pg_checked : Scalar.distance (sourceCoefficient 79 90 1 2) v4592_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4592_mb : Scalar.QComplex := ((-1391816479020729907928904 : Int)/10^30,(-431475271984228756188723698 : Int)/10^30)
theorem v4592_mb_checked : Scalar.distance (sourceCoefficient 79 90 3 1) v4592_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4592_mg : Scalar.QComplex := ((-93085945152172137304191 : Int)/10^30,(300268777471791288460 : Int)/10^30)
theorem v4592_mg_checked : Scalar.distance (sourceCoefficient 79 90 3 2) v4592_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4592_upper : Scalar.QComplex := ((999991641443818608342266536145 : Int)/10^30,(-4088648003597506800939400383 : Int)/10^30)
theorem v4592_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 79 90 5) 1) 14) v4592_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4592 : Material (79 : Basis) (90 : Basis) where
  plus := ![v4592_pa,v4592_pb,v4592_pg]
  minus := ![(Primitive.Addresses.material4592 1).one,v4592_mb,v4592_mg]
  upper := v4592_upper
  lower := (Primitive.Addresses.material4592 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4592_pa_checked.trans (by decide +kernel)
    · exact v4592_pb_checked.trans (by decide +kernel)
    · exact v4592_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 79 90 Primitive.Addresses.material4592
    · exact v4592_mb_checked.trans (by decide +kernel)
    · exact v4592_mg_checked.trans (by decide +kernel)
  upper_error := v4592_upper_checked
  lower_error := reuse_lower_error 79 90 Primitive.Addresses.material4592

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
