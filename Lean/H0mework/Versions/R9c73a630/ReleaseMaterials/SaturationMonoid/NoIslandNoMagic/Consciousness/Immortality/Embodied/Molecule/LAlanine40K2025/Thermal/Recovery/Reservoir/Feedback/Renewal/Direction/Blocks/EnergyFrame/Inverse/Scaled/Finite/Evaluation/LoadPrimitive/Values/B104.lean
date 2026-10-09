import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B069
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B070

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1665_pa : Scalar.QComplex := ((999999013918753627191599299036 : Int)/10^30,(-1404336683416548922434277539 : Int)/10^30)
theorem v1665_pa_checked : Scalar.distance (sourceCoefficient 18 91 1 0) v1665_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1665_pb : Scalar.QComplex := ((-605939557977069125996540 : Int)/10^30,(-431476986698996095023292189 : Int)/10^30)
theorem v1665_pb_checked : Scalar.distance (sourceCoefficient 18 91 1 1) v1665_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1665_pg : Scalar.QComplex := ((-93086326366793212550559 : Int)/10^30,(130724671746520077886 : Int)/10^30)
theorem v1665_pg_checked : Scalar.distance (sourceCoefficient 18 91 1 2) v1665_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1665_mb : Scalar.QComplex := ((-978284538877218539320268 : Int)/10^30,(-431476303141846444942678046 : Int)/10^30)
theorem v1665_mb_checked : Scalar.distance (sourceCoefficient 18 91 3 1) v1665_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1665_mg : Scalar.QComplex := ((-93086178896995554323892 : Int)/10^30,(211053930273784508699 : Int)/10^30)
theorem v1665_mg_checked : Scalar.distance (sourceCoefficient 18 91 3 2) v1665_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1665_upper : Scalar.QComplex := ((999995100779975382828028281460 : Int)/10^30,(-3130242170643909514697279761 : Int)/10^30)
theorem v1665_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 91 5) 1) 14) v1665_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1665 : Material (18 : Basis) (91 : Basis) where
  plus := ![v1665_pa,v1665_pb,v1665_pg]
  minus := ![(Primitive.Addresses.material1665 1).one,v1665_mb,v1665_mg]
  upper := v1665_upper
  lower := (Primitive.Addresses.material1665 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1665_pa_checked.trans (by decide +kernel)
    · exact v1665_pb_checked.trans (by decide +kernel)
    · exact v1665_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 91 Primitive.Addresses.material1665
    · exact v1665_mb_checked.trans (by decide +kernel)
    · exact v1665_mg_checked.trans (by decide +kernel)
  upper_error := v1665_upper_checked
  lower_error := reuse_lower_error 18 91 Primitive.Addresses.material1665

def v1666_pa : Scalar.QComplex := ((999998968531027823152485561496 : Int)/10^30,(-1436292755821547150267368521 : Int)/10^30)
theorem v1666_pa_checked : Scalar.distance (sourceCoefficient 18 92 1 0) v1666_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1666_pb : Scalar.QComplex := ((-619727873175140837125984 : Int)/10^30,(-431476961387714996714339394 : Int)/10^30)
theorem v1666_pb_checked : Scalar.distance (sourceCoefficient 18 92 1 1) v1666_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1666_pg : Scalar.QComplex := ((-93086321523990175705172 : Int)/10^30,(133699347177710664342 : Int)/10^30)
theorem v1666_pg_checked : Scalar.distance (sourceCoefficient 18 92 1 2) v1666_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1666_mb : Scalar.QComplex := ((-992072827098774735014746 : Int)/10^30,(-431476265931879757908392807 : Int)/10^30)
theorem v1666_mb_checked : Scalar.distance (sourceCoefficient 18 92 3 1) v1666_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1666_mg : Scalar.QComplex := ((-93086171487183397965984 : Int)/10^30,(214028600418246573694 : Int)/10^30)
theorem v1666_mg_checked : Scalar.distance (sourceCoefficient 18 92 3 2) v1666_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1666_upper : Scalar.QComplex := ((999995000239035239690525957719 : Int)/10^30,(-3162198117118994523790908923 : Int)/10^30)
theorem v1666_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 92 5) 1) 14) v1666_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1666 : Material (18 : Basis) (92 : Basis) where
  plus := ![v1666_pa,v1666_pb,v1666_pg]
  minus := ![(Primitive.Addresses.material1666 1).one,v1666_mb,v1666_mg]
  upper := v1666_upper
  lower := (Primitive.Addresses.material1666 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1666_pa_checked.trans (by decide +kernel)
    · exact v1666_pb_checked.trans (by decide +kernel)
    · exact v1666_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 92 Primitive.Addresses.material1666
    · exact v1666_mb_checked.trans (by decide +kernel)
    · exact v1666_mg_checked.trans (by decide +kernel)
  upper_error := v1666_upper_checked
  lower_error := reuse_lower_error 18 92 Primitive.Addresses.material1666

def v1667_pa : Scalar.QComplex := ((999998913339571221892646557478 : Int)/10^30,(-1474218327360410763478123476 : Int)/10^30)
theorem v1667_pa_checked : Scalar.distance (sourceCoefficient 18 93 1 0) v1667_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1667_pb : Scalar.QComplex := ((-636091890118745056723159 : Int)/10^30,(-431476930585838571002426777 : Int)/10^30)
theorem v1667_pb_checked : Scalar.distance (sourceCoefficient 18 93 1 1) v1667_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1667_pg : Scalar.QComplex := ((-93086315632622838334975 : Int)/10^30,(137229701654154938034 : Int)/10^30)
theorem v1667_pg_checked : Scalar.distance (sourceCoefficient 18 93 1 2) v1667_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1667_mb : Scalar.QComplex := ((-1008436811368675483615231 : Int)/10^30,(-431476221008605186776465549 : Int)/10^30)
theorem v1667_mb_checked : Scalar.distance (sourceCoefficient 18 93 3 1) v1667_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1667_mg : Scalar.QComplex := ((-93086162549281342312902 : Int)/10^30,(217558948496193855821 : Int)/10^30)
theorem v1667_mg_checked : Scalar.distance (sourceCoefficient 18 93 3 2) v1667_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1667_upper : Scalar.QComplex := ((999994879591564944517116284281 : Int)/10^30,(-3200123536916727216503896354 : Int)/10^30)
theorem v1667_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 93 5) 1) 14) v1667_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1667 : Material (18 : Basis) (93 : Basis) where
  plus := ![v1667_pa,v1667_pb,v1667_pg]
  minus := ![(Primitive.Addresses.material1667 1).one,v1667_mb,v1667_mg]
  upper := v1667_upper
  lower := (Primitive.Addresses.material1667 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1667_pa_checked.trans (by decide +kernel)
    · exact v1667_pb_checked.trans (by decide +kernel)
    · exact v1667_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 93 Primitive.Addresses.material1667
    · exact v1667_mb_checked.trans (by decide +kernel)
    · exact v1667_mg_checked.trans (by decide +kernel)
  upper_error := v1667_upper_checked
  lower_error := reuse_lower_error 18 93 Primitive.Addresses.material1667

def v1668_pa : Scalar.QComplex := ((999998846293262456534822166058 : Int)/10^30,(-1519016834682122310836928736 : Int)/10^30)
theorem v1668_pa_checked : Scalar.distance (sourceCoefficient 18 94 1 0) v1668_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1668_pb : Scalar.QComplex := ((-655421420614000929357735 : Int)/10^30,(-431476893135979572203223367 : Int)/10^30)
theorem v1668_pb_checked : Scalar.distance (sourceCoefficient 18 94 1 1) v1668_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1668_pg : Scalar.QComplex := ((-93086308472378764246531 : Int)/10^30,(141399832781896182750 : Int)/10^30)
theorem v1668_pg_checked : Scalar.distance (sourceCoefficient 18 94 1 2) v1668_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1668_mb : Scalar.QComplex := ((-1027766302349122112754534 : Int)/10^30,(-431476166878245884601931048 : Int)/10^30)
theorem v1668_mb_checked : Scalar.distance (sourceCoefficient 18 94 3 1) v1668_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1668_mg : Scalar.QComplex := ((-93086151790404586803818 : Int)/10^30,(221729071892236546754 : Int)/10^30)
theorem v1668_mg_checked : Scalar.distance (sourceCoefficient 18 94 3 2) v1668_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1668_upper : Scalar.QComplex := ((999994735227196488323560373224 : Int)/10^30,(-3244921861800477975117498853 : Int)/10^30)
theorem v1668_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 94 5) 1) 14) v1668_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1668 : Material (18 : Basis) (94 : Basis) where
  plus := ![v1668_pa,v1668_pb,v1668_pg]
  minus := ![(Primitive.Addresses.material1668 1).one,v1668_mb,v1668_mg]
  upper := v1668_upper
  lower := (Primitive.Addresses.material1668 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1668_pa_checked.trans (by decide +kernel)
    · exact v1668_pb_checked.trans (by decide +kernel)
    · exact v1668_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 94 Primitive.Addresses.material1668
    · exact v1668_mb_checked.trans (by decide +kernel)
    · exact v1668_mg_checked.trans (by decide +kernel)
  upper_error := v1668_upper_checked
  lower_error := reuse_lower_error 18 94 Primitive.Addresses.material1668

def v1669_pa : Scalar.QComplex := ((999998778059869065182995390322 : Int)/10^30,(-1563291005773381407201121812 : Int)/10^30)
theorem v1669_pa_checked : Scalar.distance (sourceCoefficient 18 95 1 0) v1669_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1669_pb : Scalar.QComplex := ((-674524710834151882091699 : Int)/10^30,(-431476854990054925411438220 : Int)/10^30)
theorem v1669_pb_checked : Scalar.distance (sourceCoefficient 18 95 1 1) v1669_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1669_pg : Scalar.QComplex := ((-93086301181799776970777 : Int)/10^30,(145521155216359134512 : Int)/10^30)
theorem v1669_pg_checked : Scalar.distance (sourceCoefficient 18 95 1 2) v1669_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1669_mb : Scalar.QComplex := ((-1046869552538030111521585 : Int)/10^30,(-431476112247056361543673893 : Int)/10^30)
theorem v1669_mb_checked : Scalar.distance (sourceCoefficient 18 95 3 1) v1669_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1669_mg : Scalar.QComplex := ((-93086140943312670674293 : Int)/10^30,(225850386500701491895 : Int)/10^30)
theorem v1669_mg_checked : Scalar.distance (sourceCoefficient 18 95 3 2) v1669_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1669_upper : Scalar.QComplex := ((999994590580701940508787735818 : Int)/10^30,(-3289195849185913132145505941 : Int)/10^30)
theorem v1669_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 95 5) 1) 14) v1669_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1669 : Material (18 : Basis) (95 : Basis) where
  plus := ![v1669_pa,v1669_pb,v1669_pg]
  minus := ![(Primitive.Addresses.material1669 1).one,v1669_mb,v1669_mg]
  upper := v1669_upper
  lower := (Primitive.Addresses.material1669 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1669_pa_checked.trans (by decide +kernel)
    · exact v1669_pb_checked.trans (by decide +kernel)
    · exact v1669_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 95 Primitive.Addresses.material1669
    · exact v1669_mb_checked.trans (by decide +kernel)
    · exact v1669_mg_checked.trans (by decide +kernel)
  upper_error := v1669_upper_checked
  lower_error := reuse_lower_error 18 95 Primitive.Addresses.material1669

def v1670_pa : Scalar.QComplex := ((999998744591817403653900567551 : Int)/10^30,(-1584555076083815796945262953 : Int)/10^30)
theorem v1670_pa_checked : Scalar.distance (sourceCoefficient 18 96 1 0) v1670_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1670_pb : Scalar.QComplex := ((-683699669443828111454028 : Int)/10^30,(-431476836268393663812251417 : Int)/10^30)
theorem v1670_pb_checked : Scalar.distance (sourceCoefficient 18 96 1 1) v1670_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1670_pg : Scalar.QComplex := ((-93086297604594937181980 : Int)/10^30,(147500550556607757085 : Int)/10^30)
theorem v1670_pg_checked : Scalar.distance (sourceCoefficient 18 96 1 2) v1670_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1670_mb : Scalar.QComplex := ((-1056044491575499457740698 : Int)/10^30,(-431476085607826015520165370 : Int)/10^30)
theorem v1670_mb_checked : Scalar.distance (sourceCoefficient 18 96 3 1) v1670_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1670_mg : Scalar.QComplex := ((-93086135657980132864554 : Int)/10^30,(227829778016964101045 : Int)/10^30)
theorem v1670_mg_checked : Scalar.distance (sourceCoefficient 18 96 3 2) v1670_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1670_upper : Scalar.QComplex := ((999994520412843831291014541031 : Int)/10^30,(-3310459830063191677790941411 : Int)/10^30)
theorem v1670_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 96 5) 1) 14) v1670_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1670 : Material (18 : Basis) (96 : Basis) where
  plus := ![v1670_pa,v1670_pb,v1670_pg]
  minus := ![(Primitive.Addresses.material1670 1).one,v1670_mb,v1670_mg]
  upper := v1670_upper
  lower := (Primitive.Addresses.material1670 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1670_pa_checked.trans (by decide +kernel)
    · exact v1670_pb_checked.trans (by decide +kernel)
    · exact v1670_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 96 Primitive.Addresses.material1670
    · exact v1670_mb_checked.trans (by decide +kernel)
    · exact v1670_mg_checked.trans (by decide +kernel)
  upper_error := v1670_upper_checked
  lower_error := reuse_lower_error 18 96 Primitive.Addresses.material1670

def v1671_pa : Scalar.QComplex := ((999998625985893097174077179814 : Int)/10^30,(-1657717203231867856358448351 : Int)/10^30)
theorem v1671_pa_checked : Scalar.distance (sourceCoefficient 18 97 1 0) v1671_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1671_pb : Scalar.QComplex := ((-715267446990295073531975 : Int)/10^30,(-431476769866571208406453744 : Int)/10^30)
theorem v1671_pb_checked : Scalar.distance (sourceCoefficient 18 97 1 1) v1671_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1671_pg : Scalar.QComplex := ((-93086284921570039486283 : Int)/10^30,(154310947924849175857 : Int)/10^30)
theorem v1671_pg_checked : Scalar.distance (sourceCoefficient 18 97 1 2) v1671_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1671_mb : Scalar.QComplex := ((-1087612200066057968614265 : Int)/10^30,(-431475991964458021869076463 : Int)/10^30)
theorem v1671_mb_checked : Scalar.distance (sourceCoefficient 18 97 3 1) v1671_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1671_mg : Scalar.QComplex := ((-93086117097893757757478 : Int)/10^30,(234640161904504064610 : Int)/10^30)
theorem v1671_mg_checked : Scalar.distance (sourceCoefficient 18 97 3 2) v1671_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1671_upper : Scalar.QComplex := ((999994275535901933192943153933 : Int)/10^30,(-3383621643541784069764534623 : Int)/10^30)
theorem v1671_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 97 5) 1) 14) v1671_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1671 : Material (18 : Basis) (97 : Basis) where
  plus := ![v1671_pa,v1671_pb,v1671_pg]
  minus := ![(Primitive.Addresses.material1671 1).one,v1671_mb,v1671_mg]
  upper := v1671_upper
  lower := (Primitive.Addresses.material1671 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1671_pa_checked.trans (by decide +kernel)
    · exact v1671_pb_checked.trans (by decide +kernel)
    · exact v1671_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 97 Primitive.Addresses.material1671
    · exact v1671_mb_checked.trans (by decide +kernel)
    · exact v1671_mg_checked.trans (by decide +kernel)
  upper_error := v1671_upper_checked
  lower_error := reuse_lower_error 18 97 Primitive.Addresses.material1671

def v1672_pa : Scalar.QComplex := ((999999978313811129450499918963 : Int)/10^30,(-208260359336116128849933385 : Int)/10^30)
theorem v1672_pa_checked : Scalar.distance (sourceCoefficient 19 20 1 0) v1672_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1672_pb : Scalar.QComplex := ((-89859663568934646522976 : Int)/10^30,(-431477511642983673257670542 : Int)/10^30)
theorem v1672_pb_checked : Scalar.distance (sourceCoefficient 19 20 1 1) v1672_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1672_pg : Scalar.QComplex := ((-93086427878225097599594 : Int)/10^30,(19386213339647700864 : Int)/10^30)
theorem v1672_pg_checked : Scalar.distance (sourceCoefficient 19 20 1 2) v1672_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1672_mb : Scalar.QComplex := ((-462205289632233444812765 : Int)/10^30,(-431477273439344061149929535 : Int)/10^30)
theorem v1672_mb_checked : Scalar.distance (sourceCoefficient 19 20 3 1) v1672_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1672_mg : Scalar.QComplex := ((-93086376488464749138667 : Int)/10^30,(99715600923102427100 : Int)/10^30)
theorem v1672_mg_checked : Scalar.distance (sourceCoefficient 19 20 3 2) v1672_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1672_upper : Scalar.QComplex := ((999998129492824698252709058681 : Int)/10^30,(-1934169292437040456945188454 : Int)/10^30)
theorem v1672_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 20 5) 1) 14) v1672_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1672 : Material (19 : Basis) (20 : Basis) where
  plus := ![v1672_pa,v1672_pb,v1672_pg]
  minus := ![(Primitive.Addresses.material1672 1).one,v1672_mb,v1672_mg]
  upper := v1672_upper
  lower := (Primitive.Addresses.material1672 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1672_pa_checked.trans (by decide +kernel)
    · exact v1672_pb_checked.trans (by decide +kernel)
    · exact v1672_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 20 Primitive.Addresses.material1672
    · exact v1672_mb_checked.trans (by decide +kernel)
    · exact v1672_mg_checked.trans (by decide +kernel)
  upper_error := v1672_upper_checked
  lower_error := reuse_lower_error 19 20 Primitive.Addresses.material1672

def v1673_pa : Scalar.QComplex := ((999999965869207062288156169136 : Int)/10^30,(-261269180560035938397185844 : Int)/10^30)
theorem v1673_pa_checked : Scalar.distance (sourceCoefficient 19 21 1 0) v1673_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1673_pb : Scalar.QComplex := ((-112731778283385296799856 : Int)/10^30,(-431477506049957383843078783 : Int)/10^30)
theorem v1673_pb_checked : Scalar.distance (sourceCoefficient 19 21 1 1) v1673_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1673_pg : Scalar.QComplex := ((-93086426695696908133651 : Int)/10^30,(24320615254128468400 : Int)/10^30)
theorem v1673_pg_checked : Scalar.distance (sourceCoefficient 19 21 1 2) v1673_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1673_mb : Scalar.QComplex := ((-485077391003820692406285 : Int)/10^30,(-431477248108714977510547970 : Int)/10^30)
theorem v1673_mb_checked : Scalar.distance (sourceCoefficient 19 21 3 1) v1673_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1673_mg : Scalar.QComplex := ((-93086371047770384997506 : Int)/10^30,(104649999979811280150 : Int)/10^30)
theorem v1673_mg_checked : Scalar.distance (sourceCoefficient 19 21 3 2) v1673_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1673_upper : Scalar.QComplex := ((999998025559822656076877608359 : Int)/10^30,(-1987178013232290252757223094 : Int)/10^30)
theorem v1673_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 21 5) 1) 14) v1673_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1673 : Material (19 : Basis) (21 : Basis) where
  plus := ![v1673_pa,v1673_pb,v1673_pg]
  minus := ![(Primitive.Addresses.material1673 1).one,v1673_mb,v1673_mg]
  upper := v1673_upper
  lower := (Primitive.Addresses.material1673 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1673_pa_checked.trans (by decide +kernel)
    · exact v1673_pb_checked.trans (by decide +kernel)
    · exact v1673_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 21 Primitive.Addresses.material1673
    · exact v1673_mb_checked.trans (by decide +kernel)
    · exact v1673_mg_checked.trans (by decide +kernel)
  upper_error := v1673_upper_checked
  lower_error := reuse_lower_error 19 21 Primitive.Addresses.material1673

def v1674_pa : Scalar.QComplex := ((999999965504000442870014742486 : Int)/10^30,(-262663278598828856295093494 : Int)/10^30)
theorem v1674_pa_checked : Scalar.distance (sourceCoefficient 19 22 1 0) v1674_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1674_pb : Scalar.QComplex := ((-113333300245907003943230 : Int)/10^30,(-431477505881048006598529293 : Int)/10^30)
theorem v1674_pb_checked : Scalar.distance (sourceCoefficient 19 22 1 1) v1674_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1674_pg : Scalar.QComplex := ((-93086426660478867266874 : Int)/10^30,(24450386863131345142 : Int)/10^30)
theorem v1674_pg_checked : Scalar.distance (sourceCoefficient 19 22 1 2) v1674_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1674_mb : Scalar.QComplex := ((-485678912596607096824967 : Int)/10^30,(-431477247420719301045952513 : Int)/10^30)
theorem v1674_mb_checked : Scalar.distance (sourceCoefficient 19 22 3 1) v1674_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1674_mg : Scalar.QComplex := ((-93086370900565303370837 : Int)/10^30,(104779771510102672898 : Int)/10^30)
theorem v1674_mg_checked : Scalar.distance (sourceCoefficient 19 22 3 2) v1674_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1674_upper : Scalar.QComplex := ((999998022788529837220656809414 : Int)/10^30,(-1988572108564424410302381552 : Int)/10^30)
theorem v1674_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 22 5) 1) 14) v1674_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1674 : Material (19 : Basis) (22 : Basis) where
  plus := ![v1674_pa,v1674_pb,v1674_pg]
  minus := ![(Primitive.Addresses.material1674 1).one,v1674_mb,v1674_mg]
  upper := v1674_upper
  lower := (Primitive.Addresses.material1674 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1674_pa_checked.trans (by decide +kernel)
    · exact v1674_pb_checked.trans (by decide +kernel)
    · exact v1674_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 22 Primitive.Addresses.material1674
    · exact v1674_mb_checked.trans (by decide +kernel)
    · exact v1674_mg_checked.trans (by decide +kernel)
  upper_error := v1674_upper_checked
  lower_error := reuse_lower_error 19 22 Primitive.Addresses.material1674

def v1675_pa : Scalar.QComplex := ((999999962743136051163368429989 : Int)/10^30,(-272972025141037761686399576 : Int)/10^30)
theorem v1675_pa_checked : Scalar.distance (sourceCoefficient 19 23 1 0) v1675_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1675_pb : Scalar.QComplex := ((-117781292620897316217244 : Int)/10^30,(-431477504597334103580450204 : Int)/10^30)
theorem v1675_pb_checked : Scalar.distance (sourceCoefficient 19 23 1 1) v1675_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1675_pg : Scalar.QComplex := ((-93086426393505932949510 : Int)/10^30,(25409991272474050368 : Int)/10^30)
theorem v1675_pg_checked : Scalar.distance (sourceCoefficient 19 23 1 2) v1675_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1675_mb : Scalar.QComplex := ((-490126902207619282619498 : Int)/10^30,(-431477242298588786536553857 : Int)/10^30)
theorem v1675_mb_checked : Scalar.distance (sourceCoefficient 19 23 3 1) v1675_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1675_mg : Scalar.QComplex := ((-93086369805497082175176 : Int)/10^30,(105739375331755182137 : Int)/10^30)
theorem v1675_mg_checked : Scalar.distance (sourceCoefficient 19 23 3 2) v1675_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1675_upper : Scalar.QComplex := ((999998002235708227825547988455 : Int)/10^30,(-1998880834987964815082428653 : Int)/10^30)
theorem v1675_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 23 5) 1) 14) v1675_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1675 : Material (19 : Basis) (23 : Basis) where
  plus := ![v1675_pa,v1675_pb,v1675_pg]
  minus := ![(Primitive.Addresses.material1675 1).one,v1675_mb,v1675_mg]
  upper := v1675_upper
  lower := (Primitive.Addresses.material1675 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1675_pa_checked.trans (by decide +kernel)
    · exact v1675_pb_checked.trans (by decide +kernel)
    · exact v1675_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 23 Primitive.Addresses.material1675
    · exact v1675_mb_checked.trans (by decide +kernel)
    · exact v1675_mg_checked.trans (by decide +kernel)
  upper_error := v1675_upper_checked
  lower_error := reuse_lower_error 19 23 Primitive.Addresses.material1675

def v1676_pa : Scalar.QComplex := ((999999947538563511433131084913 : Int)/10^30,(-323917999229637468113503069 : Int)/10^30)
theorem v1676_pa_checked : Scalar.distance (sourceCoefficient 19 24 1 0) v1676_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1676_pb : Scalar.QComplex := ((-139763334988200484176042 : Int)/10^30,(-431477497355532139544957140 : Int)/10^30)
theorem v1676_pb_checked : Scalar.distance (sourceCoefficient 19 24 1 1) v1676_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1676_pg : Scalar.QComplex := ((-93086424904667519581342 : Int)/10^30,(30152370092396448216 : Int)/10^30)
theorem v1676_pg_checked : Scalar.distance (sourceCoefficient 19 24 1 2) v1676_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1676_mb : Scalar.QComplex := ((-512108930140654511955715 : Int)/10^30,(-431477216087276990408682275 : Int)/10^30)
theorem v1676_mb_checked : Scalar.distance (sourceCoefficient 19 24 3 1) v1676_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1676_mg : Scalar.QComplex := ((-93086364224199890389823 : Int)/10^30,(110481751101072711965 : Int)/10^30)
theorem v1676_mg_checked : Scalar.distance (sourceCoefficient 19 24 3 2) v1676_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1676_upper : Scalar.QComplex := ((999997899103028839262893599160 : Int)/10^30,(-2049826706956807795518875779 : Int)/10^30)
theorem v1676_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 24 5) 1) 14) v1676_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1676 : Material (19 : Basis) (24 : Basis) where
  plus := ![v1676_pa,v1676_pb,v1676_pg]
  minus := ![(Primitive.Addresses.material1676 1).one,v1676_mb,v1676_mg]
  upper := v1676_upper
  lower := (Primitive.Addresses.material1676 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1676_pa_checked.trans (by decide +kernel)
    · exact v1676_pb_checked.trans (by decide +kernel)
    · exact v1676_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 24 Primitive.Addresses.material1676
    · exact v1676_mb_checked.trans (by decide +kernel)
    · exact v1676_mg_checked.trans (by decide +kernel)
  upper_error := v1676_upper_checked
  lower_error := reuse_lower_error 19 24 Primitive.Addresses.material1676

def v1677_pa : Scalar.QComplex := ((999999939829382465339417957478 : Int)/10^30,(-346902337047212683638407692 : Int)/10^30)
theorem v1677_pa_checked : Scalar.distance (sourceCoefficient 19 25 1 0) v1677_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1677_pb : Scalar.QComplex := ((-149680559919345099160314 : Int)/10^30,(-431477493599595339356686461 : Int)/10^30)
theorem v1677_pb_checked : Scalar.distance (sourceCoefficient 19 25 1 1) v1677_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1677_pg : Scalar.QComplex := ((-93086424140706855729167 : Int)/10^30,(32291900024802850838 : Int)/10^30)
theorem v1677_pg_checked : Scalar.distance (sourceCoefficient 19 25 1 2) v1677_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1677_mb : Scalar.QComplex := ((-522026148137958748056451 : Int)/10^30,(-431477203773223128379811593 : Int)/10^30)
theorem v1677_mb_checked : Scalar.distance (sourceCoefficient 19 25 3 1) v1677_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1677_mg : Scalar.QComplex := ((-93086361613921540179466 : Int)/10^30,(112621279577570694010 : Int)/10^30)
theorem v1677_mg_checked : Scalar.distance (sourceCoefficient 19 25 3 2) v1677_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1677_upper : Scalar.QComplex := ((999997851724977324792667284221 : Int)/10^30,(-2072810997236564647628848895 : Int)/10^30)
theorem v1677_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 25 5) 1) 14) v1677_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1677 : Material (19 : Basis) (25 : Basis) where
  plus := ![v1677_pa,v1677_pb,v1677_pg]
  minus := ![(Primitive.Addresses.material1677 1).one,v1677_mb,v1677_mg]
  upper := v1677_upper
  lower := (Primitive.Addresses.material1677 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1677_pa_checked.trans (by decide +kernel)
    · exact v1677_pb_checked.trans (by decide +kernel)
    · exact v1677_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 25 Primitive.Addresses.material1677
    · exact v1677_mb_checked.trans (by decide +kernel)
    · exact v1677_mg_checked.trans (by decide +kernel)
  upper_error := v1677_upper_checked
  lower_error := reuse_lower_error 19 25 Primitive.Addresses.material1677

def v1678_pa : Scalar.QComplex := ((999999937254789024761938311696 : Int)/10^30,(-354246267465889643139725927 : Int)/10^30)
theorem v1678_pa_checked : Scalar.distance (sourceCoefficient 19 26 1 0) v1678_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1678_pb : Scalar.QComplex := ((-152849300745931209007107 : Int)/10^30,(-431477492335434240042568977 : Int)/10^30)
theorem v1678_pb_checked : Scalar.distance (sourceCoefficient 19 26 1 1) v1678_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1678_pg : Scalar.QComplex := ((-93086423884512719295490 : Int)/10^30,(32975520281892247835 : Int)/10^30)
theorem v1678_pg_checked : Scalar.distance (sourceCoefficient 19 26 1 2) v1678_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1678_mb : Scalar.QComplex := ((-525194886693763736549554 : Int)/10^30,(-431477199774581881215841046 : Int)/10^30)
theorem v1678_mb_checked : Scalar.distance (sourceCoefficient 19 26 3 1) v1678_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1678_mg : Scalar.QComplex := ((-93086360767794006383858 : Int)/10^30,(113304899359033025117 : Int)/10^30)
theorem v1678_mg_checked : Scalar.distance (sourceCoefficient 19 26 3 2) v1678_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1678_upper : Scalar.QComplex := ((999997836475430052296483362061 : Int)/10^30,(-2080154912273805214033372269 : Int)/10^30)
theorem v1678_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 26 5) 1) 14) v1678_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1678 : Material (19 : Basis) (26 : Basis) where
  plus := ![v1678_pa,v1678_pb,v1678_pg]
  minus := ![(Primitive.Addresses.material1678 1).one,v1678_mb,v1678_mg]
  upper := v1678_upper
  lower := (Primitive.Addresses.material1678 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1678_pa_checked.trans (by decide +kernel)
    · exact v1678_pb_checked.trans (by decide +kernel)
    · exact v1678_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 26 Primitive.Addresses.material1678
    · exact v1678_mb_checked.trans (by decide +kernel)
    · exact v1678_mg_checked.trans (by decide +kernel)
  upper_error := v1678_upper_checked
  lower_error := reuse_lower_error 19 26 Primitive.Addresses.material1678

def v1679_pa : Scalar.QComplex := ((999999935454806706215664178394 : Int)/10^30,(-359291500625170222396566506 : Int)/10^30)
theorem v1679_pa_checked : Scalar.distance (sourceCoefficient 19 27 1 0) v1679_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1679_pb : Scalar.QComplex := ((-155026205394885777730302 : Int)/10^30,(-431477491448983640378951761 : Int)/10^30)
theorem v1679_pb_checked : Scalar.distance (sourceCoefficient 19 27 1 1) v1679_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1679_pg : Scalar.QComplex := ((-93086423705114874182519 : Int)/10^30,(33445163019565652867 : Int)/10^30)
theorem v1679_pg_checked : Scalar.distance (sourceCoefficient 19 27 1 2) v1679_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1679_mb : Scalar.QComplex := ((-527371789767190271752876 : Int)/10^30,(-431477197009560943716321212 : Int)/10^30)
theorem v1679_mb_checked : Scalar.distance (sourceCoefficient 19 27 3 1) v1679_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1679_mg : Scalar.QComplex := ((-93086360183115697380463 : Int)/10^30,(113774541767024714626 : Int)/10^30)
theorem v1679_mg_checked : Scalar.distance (sourceCoefficient 19 27 3 2) v1679_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1679_upper : Scalar.QComplex := ((999997825967835681671006054840 : Int)/10^30,(-2085200134812197468569895978 : Int)/10^30)
theorem v1679_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 27 5) 1) 14) v1679_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1679 : Material (19 : Basis) (27 : Basis) where
  plus := ![v1679_pa,v1679_pb,v1679_pg]
  minus := ![(Primitive.Addresses.material1679 1).one,v1679_mb,v1679_mg]
  upper := v1679_upper
  lower := (Primitive.Addresses.material1679 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1679_pa_checked.trans (by decide +kernel)
    · exact v1679_pb_checked.trans (by decide +kernel)
    · exact v1679_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 27 Primitive.Addresses.material1679
    · exact v1679_mb_checked.trans (by decide +kernel)
    · exact v1679_mg_checked.trans (by decide +kernel)
  upper_error := v1679_upper_checked
  lower_error := reuse_lower_error 19 27 Primitive.Addresses.material1679

def v1680_pa : Scalar.QComplex := ((999999932989754863932304116851 : Int)/10^30,(-366088084730659376004914953 : Int)/10^30)
theorem v1680_pa_checked : Scalar.distance (sourceCoefficient 19 28 1 0) v1680_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1680_pb : Scalar.QComplex := ((-157958778588159696762885 : Int)/10^30,(-431477490231668257204528526 : Int)/10^30)
theorem v1680_pb_checked : Scalar.distance (sourceCoefficient 19 28 1 1) v1680_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1680_pg : Scalar.QComplex := ((-93086423459072374504969 : Int)/10^30,(34077832762122853175 : Int)/10^30)
theorem v1680_pg_checked : Scalar.distance (sourceCoefficient 19 28 1 2) v1680_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1680_mb : Scalar.QComplex := ((-530304360818044815883766 : Int)/10^30,(-431477193261567426202309112 : Int)/10^30)
theorem v1680_mb_checked : Scalar.distance (sourceCoefficient 19 28 3 1) v1680_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1680_mg : Scalar.QComplex := ((-93086359391107795876360 : Int)/10^30,(114407211061686459465 : Int)/10^30)
theorem v1680_mg_checked : Scalar.distance (sourceCoefficient 19 28 3 2) v1680_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1680_upper : Scalar.QComplex := ((999997811772499926012101846718 : Int)/10^30,(-2091996704540517127879685706 : Int)/10^30)
theorem v1680_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 28 5) 1) 14) v1680_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1680 : Material (19 : Basis) (28 : Basis) where
  plus := ![v1680_pa,v1680_pb,v1680_pg]
  minus := ![(Primitive.Addresses.material1680 1).one,v1680_mb,v1680_mg]
  upper := v1680_upper
  lower := (Primitive.Addresses.material1680 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1680_pa_checked.trans (by decide +kernel)
    · exact v1680_pb_checked.trans (by decide +kernel)
    · exact v1680_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 28 Primitive.Addresses.material1680
    · exact v1680_mb_checked.trans (by decide +kernel)
    · exact v1680_mg_checked.trans (by decide +kernel)
  upper_error := v1680_upper_checked
  lower_error := reuse_lower_error 19 28 Primitive.Addresses.material1680

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
